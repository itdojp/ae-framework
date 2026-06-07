#!/usr/bin/env tsx
// Generate minimal API tests from OpenAPI (operationId-aware)
import { promises as fs } from 'fs'
import path from 'path'
import yaml from 'yaml'
import {
  assertWithinWorkspace,
  resolveWorkspacePath,
  toWorkspaceRelativePath,
} from '../../src/utils/workspace-path-policy.js'

const DEFAULT_REVIEW_OUTPUT_DIR = 'artifacts/codex/generated-tests'
const REVIEWED_TEST_OUTPUT_APPROVAL = 'reviewed-generated-tests'

async function exists(p: string) {
  try { await fs.stat(p); return true } catch { return false }
}

function normalizeWorkspacePath(repo: string, inputPath: string, label: string): { absolutePath: string; relativePath: string } {
  const raw = String(inputPath).trim()
  if (!raw) throw new Error(`${label} must be non-empty`)
  const absolutePath = path.isAbsolute(raw)
    ? assertWithinWorkspace(raw, { workspaceRoot: repo, label })
    : resolveWorkspacePath(raw, { workspaceRoot: repo, label })
  const relativePath = toWorkspaceRelativePath(absolutePath, { workspaceRoot: repo, label })
  const segments = relativePath.split('/').filter(Boolean)
  if (segments.length === 0) throw new Error(`${label} must not target the workspace root`)
  if (segments.some((segment) => segment.toLowerCase() === '.git')) {
    throw new Error(`${label} must not target Git metadata directories`)
  }
  return { absolutePath, relativePath }
}

function getArgValue(name: string): string | undefined {
  const inline = process.argv.find((arg) => arg.startsWith(`${name}=`))
  if (inline) return inline.slice(name.length + 1)
  const index = process.argv.indexOf(name)
  if (index < 0) return undefined
  const value = process.argv[index + 1]
  if (!value || value.startsWith('--')) {
    throw new Error(`${name} requires a value`)
  }
  return value
}

function hasReviewedTestsApproval(): boolean {
  return process.argv.includes('--approve-generated-tests') &&
    process.env.CODEX_GENERATE_TESTS_APPROVAL === REVIEWED_TEST_OUTPUT_APPROVAL
}

async function main() {
  const repo = process.cwd()
  const defaultYaml = path.join(repo, 'artifacts', 'codex', 'openapi.yaml')
  const defaultJson = path.join(repo, 'artifacts', 'codex', 'openapi.json')
  const openapiPath = normalizeWorkspacePath(
    repo,
    process.env.CONTRACTS_OPENAPI_PATH || (await exists(defaultJson) ? defaultJson : defaultYaml),
    'OpenAPI input path',
  )
  const useOpId = process.argv.includes('--use-operation-id') || process.argv.includes('--opid')
  const withInput = process.argv.includes('--with-input') || process.argv.includes('--sample')
  const requestedOutputDir = getArgValue('--output-dir') || process.env.CODEX_GENERATE_TESTS_OUTPUT_DIR || DEFAULT_REVIEW_OUTPUT_DIR
  const outputDir = normalizeWorkspacePath(repo, requestedOutputDir, 'generated test output directory')
  if ((outputDir.relativePath === 'tests' || outputDir.relativePath.startsWith('tests/')) && !hasReviewedTestsApproval()) {
    throw new Error(
      `Writing generated tests under tests/ requires --approve-generated-tests and CODEX_GENERATE_TESTS_APPROVAL=${REVIEWED_TEST_OUTPUT_APPROVAL}`
    )
  }

  const specTxt = await fs.readFile(openapiPath.absolutePath, 'utf8')
  let jsonSpecStr: string
  if (openapiPath.relativePath.endsWith('.json')) {
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
  const files = await agent.generateTestsFromOpenAPI(jsonSpecStr, {
    useOperationIdForTestNames: useOpId,
    includeSampleInput: withInput,
    outputRoot: outputDir.relativePath,
  })

  for (const f of files) {
    const safeFile = normalizeWorkspacePath(repo, f.path, 'generated test file path')
    if (safeFile.relativePath !== outputDir.relativePath && !safeFile.relativePath.startsWith(`${outputDir.relativePath}/`)) {
      throw new Error(`generated test file path escaped output directory: ${f.path}`)
    }
    const abs = safeFile.absolutePath
    await fs.mkdir(path.dirname(abs), { recursive: true })
    await fs.writeFile(abs, f.content, 'utf8')
  }
  console.log(`Generated ${files.length} test files under ${outputDir.relativePath}/ (useOperationId=${useOpId}, includeSampleInput=${withInput})`)
}

main().catch((e) => { console.error('generate-openapi-tests failed:', e); process.exit(1) })
