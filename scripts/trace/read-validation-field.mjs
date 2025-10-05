#!/usr/bin/env node
import fs from 'node:fs';

const [,, file, field] = process.argv;
if (!file || !field) {
  console.error('[read-validation-field] usage: read-validation-field.mjs <json-file> <field>');
  process.exit(1);
}

try {
  const json = JSON.parse(fs.readFileSync(file, 'utf8'));
  const value = json?.[field];
  if (value === false) {
    console.log('false');
  } else if (value === true) {
    console.log('true');
  } else {
    console.log('unknown');
  }
} catch (error) {
  console.log('unknown');
  process.exitCode = 1;
}
