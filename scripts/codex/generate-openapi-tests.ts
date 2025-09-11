#!/usr/bin/env tsx
// Generate minimal API tests from OpenAPI (operationId-aware)
import { promises as fs } from 'fs'
import path from 'path'
import yaml from 'yaml'

async function exists(p: string) {
  try { await fs.stat(p); return true } catch { return false }
}

async function main() {
  const repo = process.cwd()
  const defaultYaml = path.join(repo, 'artifacts', 'codex', 'openapi.yaml')
  const defaultJson = path.join(repo, 'artifacts', 'codex', 'openapi.json')
  const openapiPath = process.env.CONTRACTS_OPENAPI_PATH || (await exists(defaultJson) ? defaultJson : defaultYaml)
  const useOpId = process.argv.includes('--use-operation-id') || process.argv.includes('--opid')

  const specTxt = await fs.readFile(openapiPath, 'utf8')
  let jsonSpecStr: string
  if (openapiPath.endsWith('.json')) {
    // Normalize JSON string
    jsonSpecStr = JSON.stringify(JSON.parse(specTxt))
  } else {
    // YAML → JSON string
    const obj = yaml.parse(specTxt)
    jsonSpecStr = JSON.stringify(obj)
  }

  // Lazy import to avoid build step
  const { CodeGenerationAgent } = await import(path.join(repo, 'src', 'agents', 'code-generation-agent.ts'))
  const agent = new (CodeGenerationAgent as any)()
  const files = await agent.generateTestsFromOpenAPI(jsonSpecStr, { useOperationIdForTestNames: useOpId })

  const outDir = path.join(repo, 'tests', 'api', 'generated')
  await fs.mkdir(outDir, { recursive: true })
  for (const f of files) {
    const abs = path.join(repo, f.path)
    await fs.mkdir(path.dirname(abs), { recursive: true })
    await fs.writeFile(abs, f.content, 'utf8')
  }
  console.log(`Generated ${files.length} test files under tests/api/generated/ (useOperationId=${useOpId})`)
}

main().catch((e) => { console.error('generate-openapi-tests failed:', e); process.exit(1) })

