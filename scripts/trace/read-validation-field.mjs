#!/usr/bin/env node
import fs from 'node:fs';

const [,, file, field] = process.argv;
if (!file || !field) {
  console.error('[read-validation-field] usage: read-validation-field.mjs <json-file> <field>');
  process.exitCode = 1;
  process.exit();
}

try {
  const json = JSON.parse(fs.readFileSync(file, 'utf8'));
  const value = json?.[field];
  if (value === true) {
    console.log('true');
  } else if (value === false) {
    console.log('false');
  } else {
    console.log('unknown');
  }
} catch (error) {
  console.log('unknown');
  console.warn(`[read-validation-field] failed to read ${field} from ${file}: ${error.message}`);
  process.exitCode = 1;
}
