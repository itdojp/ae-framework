#!/usr/bin/env node
import { fileURLToPath } from "node:url";
import fs from "node:fs/promises";
import path from "node:path";

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);
const projectRoot = path.resolve(__dirname, "..", "..");
const traceDir = path.join(projectRoot, "hermetic-reports", "trace");
const targetPath = path.join(traceDir, "fetched-kvonce-otlp.json");

const payloadFile = process.env.KVONCE_OTLP_PAYLOAD_FILE;
const payloadUrl = process.env.KVONCE_OTLP_PAYLOAD_URL;
const githubEnv = process.env.GITHUB_ENV;

async function ensureTraceDir() {
  await fs.mkdir(traceDir, { recursive: true });
}

async function setEnv(key, value) {
  if (githubEnv) {
    await fs.appendFile(githubEnv, `${key}=${value}\n`);
  }
  process.env[key] = value;
}

async function copyFromFile() {
  if (!payloadFile) return false;
  try {
    await fs.access(payloadFile);
  } catch (error) {
    console.warn(`[fetch-otlp] specified file not accessible (${error.message})`);
    return false;
  }
  await fs.copyFile(payloadFile, targetPath);
  console.log(`[fetch-otlp] copied payload from ${payloadFile} to ${targetPath}`);
  await setEnv("KVONCE_OTLP_PAYLOAD", targetPath);
  return true;
}

async function downloadFromUrl() {
  if (!payloadUrl) return false;
  try {
    const response = await fetch(payloadUrl);
    if (!response.ok) {
      throw new Error(`unexpected status ${response.status}`);
    }
    const buffer = Buffer.from(await response.arrayBuffer());
    await fs.writeFile(targetPath, buffer);
    console.log(`[fetch-otlp] downloaded payload from ${payloadUrl} to ${targetPath}`);
    await setEnv("KVONCE_OTLP_PAYLOAD", targetPath);
    return true;
  } catch (error) {
    console.warn(`[fetch-otlp] failed to download ${payloadUrl}: ${error.message}`);
    return false;
  }
}

async function main() {
  await ensureTraceDir();
  const copied = await copyFromFile();
  if (copied) return;
  const downloaded = await downloadFromUrl();
  if (downloaded) return;
  console.log("[fetch-otlp] no external payload configured; skipping");
}

main().catch((error) => {
  console.error("[fetch-otlp] fatal:", error.message);
  process.exitCode = 1;
});
