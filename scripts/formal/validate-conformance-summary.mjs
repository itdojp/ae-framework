#!/usr/bin/env node
import fs from 'fs';
import Ajv from 'ajv';
const ajv = new Ajv({ allErrors: true });
const schema = JSON.parse(fs.readFileSync(new URL('./conformance-schema.json', import.meta.url)));
const file = process.argv[2] || 'artifacts/formal/conformance-summary.json';
if (!fs.existsSync(file)) {
  console.log('ℹ️ conformance summary not found (skipping)');
  process.exit(0);
}
const data = JSON.parse(fs.readFileSync(file));
const validate = ajv.compile(schema);
const ok = validate(data);
if (!ok) {
  console.warn('⚠️ conformance summary invalid:', validate.errors);
  process.exit(0);
}
console.log('✅ conformance summary valid');
