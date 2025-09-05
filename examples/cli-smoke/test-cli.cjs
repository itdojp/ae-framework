const { main } = require("tsx/cjs").require("./src/runner/main.ts", import.meta.url); main().then(() => process.exit(0)).catch(console.error);
