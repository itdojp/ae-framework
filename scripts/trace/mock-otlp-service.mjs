#!/usr/bin/env node
import fastify from "fastify";
import { BasicTracerProvider, SimpleSpanProcessor } from "@opentelemetry/sdk-trace-base";
import { Resource } from "@opentelemetry/resources";
import { SemanticResourceAttributes } from "@opentelemetry/semantic-conventions";
import { diag, DiagConsoleLogger, DiagLogLevel, trace } from "@opentelemetry/api";
import { fileURLToPath } from "node:url";
import path from "node:path";
import fs from "node:fs/promises";

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);
const projectRoot = path.resolve(__dirname, "..", "..");
const outputDir = path.join(projectRoot, "hermetic-reports", "trace");
const outputFile = path.join(outputDir, "collected-kvonce-otlp.json");

diag.setLogger(new DiagConsoleLogger(), DiagLogLevel.ERROR);

class CollectingExporter {
  constructor() {
    this.spans = [];
  }
  export(spans, resultCallback) {
    this.spans.push(...spans);
    resultCallback({ code: 0 });
  }
  shutdown() {
    return Promise.resolve();
  }
}

function toAttributeValue(value) {
  if (typeof value === "string") {
    return { stringValue: value };
  }
  if (typeof value === "number") {
    return Number.isInteger(value)
      ? { intValue: String(value) }
      : { doubleValue: value };
  }
  if (typeof value === "boolean") {
    return { boolValue: value };
  }
  if (Array.isArray(value)) {
    return {
      arrayValue: {
        values: value.map((v) => ({ stringValue: String(v) })),
      },
    };
  }
  if (value && typeof value === "object") {
    return { stringValue: JSON.stringify(value) };
  }
  return { stringValue: String(value) };
}

function spanToOtlp(span) {
  const attributes = Object.entries(span.attributes ?? {}).map(([key, val]) => ({
    key,
    value: toAttributeValue(val),
  }));
  const startNanos = BigInt(span.startTime[0]) * 1000000000n + BigInt(span.startTime[1]);
  const endNanos = BigInt(span.endTime[0]) * 1000000000n + BigInt(span.endTime[1]);

  return {
    name: span.name,
    startTimeUnixNano: startNanos.toString(),
    endTimeUnixNano: endNanos.toString(),
    attributes,
  };
}

async function main() {
  const provider = new BasicTracerProvider({
    resource: new Resource({
      [SemanticResourceAttributes.SERVICE_NAME]: "kvonce-mock-service",
    }),
  });
  const exporter = new CollectingExporter();
  provider.addSpanProcessor(new SimpleSpanProcessor(exporter));
  provider.register();

  const tracer = trace.getTracer("kvonce-mock-tracer");

  const app = fastify();

  app.post("/event", async (request, reply) => {
    const { type, key, value, reason } = request.body ?? {};
    if (!type || !key) {
      reply.code(400);
      return { error: "type and key are required" };
    }
    await tracer.startActiveSpan(`kvonce.${type}`, async (span) => {
      span.setAttribute("kvonce.event.type", type);
      span.setAttribute("kvonce.event.key", key);
      if (value !== undefined) {
        span.setAttribute("kvonce.event.value", value);
      }
      if (reason !== undefined) {
        span.setAttribute("kvonce.event.reason", reason);
      }
      span.end();
    });
    return { ok: true };
  });

  let url;
  try {
    await app.listen({ port: 0, host: "127.0.0.1" });
    const serverAddress = app.server.address();
    const port = typeof serverAddress === "object" && serverAddress ? serverAddress.port : 0;
    url = `http://127.0.0.1:${port}/event`;
  } catch (error) {
    console.error("[mock-otlp] failed to start server:", error.message);
    process.exitCode = 1;
    return;
  }

  const events = [
    { type: "success", key: "alpha", value: "v1" },
    { type: "retry", key: "beta" },
    { type: "failure", key: "beta", reason: "duplicate" },
    { type: "success", key: "beta", value: "v2" },
  ];

  for (const event of events) {
    await fetch(url, {
      method: "POST",
      headers: { "Content-Type": "application/json" },
      body: JSON.stringify(event),
    });
  }

  await app.close();
  await provider.forceFlush();
  await provider.shutdown();

  const spans = exporter.spans;
  if (!spans.length) {
    console.error("[mock-otlp] no spans captured");
    process.exitCode = 1;
    return;
  }

  const resourceAttributes = Object.entries(spans[0].resource.attributes ?? {}).map(([key, val]) => ({
    key,
    value: toAttributeValue(val),
  }));

  const scopeName = spans[0].instrumentationLibrary?.name ?? "kvonce-mock-tracer";
  const scopeVersion = spans[0].instrumentationLibrary?.version ?? "1.0.0";

  const payload = {
    resourceSpans: [
      {
        resource: {
          attributes: resourceAttributes,
        },
        scopeSpans: [
          {
            scope: {
              name: scopeName,
              version: scopeVersion,
            },
            spans: spans.map(spanToOtlp),
          },
        ],
      },
    ],
  };

  await fs.mkdir(outputDir, { recursive: true });
  await fs.writeFile(outputFile, JSON.stringify(payload, null, 2), "utf8");
  console.log(`[mock-otlp] wrote payload to ${outputFile}`);
}

main().catch((error) => {
  console.error("[mock-otlp] failed:", error.message);
  process.exitCode = 1;
});
