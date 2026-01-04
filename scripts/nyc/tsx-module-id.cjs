'use strict';

const path = require('path');
const Module = require('module');

const wrapExtension = (ext) => {
  const handler = Module._extensions[ext];
  if (!handler) return;
  Module._extensions[ext] = function patched(module, filename) {
    if (module && typeof module.id !== 'string') {
      module.id = filename;
    }
    if (module && typeof module.filename !== 'string') {
      module.filename = filename;
    }
    if (module && !module.paths) {
      module.paths = Module._nodeModulePaths(path.dirname(filename));
    }
    return handler(module, filename);
  };
};

[
  '.ts',
  '.tsx',
  '.cts',
  '.mts',
  '.js',
  '.jsx',
  '.cjs',
  '.mjs'
].forEach(wrapExtension);
