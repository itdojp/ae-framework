#!/usr/bin/env node
import fs from "node:fs/promises";
import path from "node:path";
import { fileURLToPath } from "node:url";

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);
const projectRoot = path.resolve(__dirname, "..", "..");

const samplePath = path.join(projectRoot, "samples", "trace", "kvonce-otlp.json");
const outputDir = process.env.KVONCE_OTLP_OUTDIR || path.join(projectRoot, "hermetic-reports", "trace");
const outputPath = path.join(outputDir, "collected-kvonce-otlp.json");

async function main() {
  try {
    await fs.mkdir(outputDir, { recursive: true });
    const raw = await fs.readFile(samplePath, "utf8");
    const formatted = JSON.stringify(JSON.parse(raw), null, 2);
    await fs.writeFile(outputPath, formatted, "utf8");
    console.log(`[collect-otlp] wrote sample payload to ${outputPath}`);
  } catch (error) {
    console.error("[collect-otlp] failed:", error.message);
    process.exitCode = 1;
  }
}

main();
