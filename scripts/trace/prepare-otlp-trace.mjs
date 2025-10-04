#!/usr/bin/env node
import { fileURLToPath } from "node:url";
import path from "node:path";
import fs from "node:fs/promises";
import { produceMockOtlp } from "./mock-otlp-service.mjs";

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);
const projectRoot = path.resolve(__dirname, "..", "..");
const targetPath = path.join(projectRoot, "hermetic-reports", "trace", "collected-kvonce-otlp.json");
const samplePath = path.join(projectRoot, "samples", "trace", "kvonce-otlp.json");

async function ensureDir() {
  await fs.mkdir(path.dirname(targetPath), { recursive: true });
}

async function copyPayload(src) {
  await ensureDir();
  await fs.copyFile(src, targetPath);
  console.log(`[prepare-otlp] copied payload from ${src} to ${targetPath}`);
}

async function main() {
  const provided = process.env.KVONCE_OTLP_PAYLOAD;
  if (provided) {
    try {
      await fs.access(provided);
      await copyPayload(provided);
      return;
    } catch (error) {
      console.warn(`[prepare-otlp] provided KVONCE_OTLP_PAYLOAD not usable (${error.message}), falling back.`);
    }
  }

  try {
    await fs.access(samplePath);
    await copyPayload(samplePath);
    return;
  } catch {
    // ignore, fall through to mock
  }

  const result = await produceMockOtlp(targetPath);
  console.log(`[prepare-otlp] generated mock payload at ${result}`);
}

main().catch((error) => {
  console.error("[prepare-otlp] failed:", error.message);
  process.exitCode = 1;
});
