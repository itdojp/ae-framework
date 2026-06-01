import Fastify from 'fastify'
import fs from 'fs'
import path from 'path'
import { fileURLToPath, pathToFileURL } from 'url'
import yaml from 'yaml'
import {
  collectOpenApiRouteDescriptors,
  OpenApiRouteRegistrationError,
  resolveRouteModulePath,
  type OpenApiLikeSpec,
} from './server/openapi-route-security.js'
import { handler as postReservation } from './routes/reservations-post.js'
import { handler as deleteReservation } from './routes/reservations-id-delete.js'
import { handler as getInventory } from './routes/inventory-sku-get.js'

const server = Fastify({ logger: true })
const moduleDir = path.dirname(fileURLToPath(import.meta.url))
const routesDir = path.resolve(moduleDir, 'routes')

type PlainObject = Record<string, unknown>

interface RouteHandlerModule {
  handler: (input: unknown) => Promise<unknown>
}

function toPlainObject(value: unknown): PlainObject {
  return value !== null && typeof value === 'object' && !Array.isArray(value)
    ? (value as PlainObject)
    : {}
}

function getResponseStatus(result: unknown, fallback: number): number {
  if (result == null) return fallback
  const status = toPlainObject(result)['status']
  return typeof status === 'number' ? status : fallback
}

function getRouteParam(params: unknown, key: string): string {
  const value = toPlainObject(params)[key]
  if (typeof value === 'undefined') return ''
  if (typeof value === 'string') return value
  if (typeof value === 'number' || typeof value === 'boolean' || typeof value === 'bigint') {
    return String(value)
  }
  throw new TypeError(
    `Invalid route parameter "${key}": expected primitive or undefined, got ${value === null ? 'null' : typeof value}`
  )
}

function isRouteHandlerModule(value: unknown): value is RouteHandlerModule {
  return (
    value !== null &&
    typeof value === 'object' &&
    'handler' in value &&
    typeof value.handler === 'function'
  )
}

function isOpenApiLikeSpec(value: unknown): value is OpenApiLikeSpec {
  return value !== null && typeof value === 'object'
}

function isPathWithin(baseDir: string, candidatePath: string): boolean {
  const relative = path.relative(baseDir, candidatePath)
  return relative === '' || (!!relative && !relative.startsWith('..') && !path.isAbsolute(relative))
}

function resolveExistingRouteModulePath(key: string, extension: 'js' | 'ts'): string | null {
  const candidate = resolveRouteModulePath(key, extension, routesDir)
  if (!fs.existsSync(candidate)) return null

  const realBase = fs.realpathSync(routesDir)
  const realCandidate = fs.realpathSync(candidate)
  if (!isPathWithin(realBase, realCandidate)) {
    throw new OpenApiRouteRegistrationError(`Route module realpath escaped routes directory: ${key}.${extension}`)
  }
  return realCandidate
}

async function loadRouteModule(key: string): Promise<RouteHandlerModule | null> {
  try {
    const fileJs = resolveExistingRouteModulePath(key, 'js')
    if (fileJs) {
      const mod: unknown = await import(pathToFileURL(fileJs).href)
      return isRouteHandlerModule(mod) ? mod : null
    }

    const fileTs = resolveExistingRouteModulePath(key, 'ts')
    if (fileTs) {
      const mod: unknown = await import(pathToFileURL(fileTs).href)
      return isRouteHandlerModule(mod) ? mod : null
    }
  } catch (error) {
    if (error instanceof OpenApiRouteRegistrationError) throw error
    // Optional route module may not exist for every operation.
  }

  return null
}

async function tryAutoRegisterFromOpenAPI() {
  try {
    const root = process.cwd()
    const y = path.join(root, 'artifacts', 'codex', 'openapi.yaml')
    const j = path.join(root, 'artifacts', 'codex', 'openapi.json')
    let spec: OpenApiLikeSpec | null = null
    if (fs.existsSync(j)) {
      const parsed: unknown = JSON.parse(fs.readFileSync(j, 'utf8'))
      if (isOpenApiLikeSpec(parsed)) spec = parsed
    } else if (fs.existsSync(y)) {
      const parsed: unknown = yaml.parse(fs.readFileSync(y, 'utf8'))
      if (isOpenApiLikeSpec(parsed)) spec = parsed
    }
    if (!spec || !spec.paths) return false
    const routeDescriptors = collectOpenApiRouteDescriptors(spec)
    for (const descriptor of routeDescriptors) {
      const mod = await loadRouteModule(descriptor.moduleKey)
      if (mod?.handler) {
        switch (descriptor.method) {
          case 'get':
            server.get(descriptor.fastifyPath, async (req, rep) => {
              const r = await mod.handler({ ...toPlainObject(req.params), ...toPlainObject(req.query) })
              rep.code(getResponseStatus(r, 200)).send(r)
            })
            break
          case 'post':
            server.post(descriptor.fastifyPath, async (req, rep) => {
              const r = await mod.handler(req.body)
              rep.code(getResponseStatus(r, 200)).send(r)
            })
            break
          case 'delete':
            server.delete(descriptor.fastifyPath, async (req, rep) => {
              const r = await mod.handler(toPlainObject(req.params))
              rep.code(getResponseStatus(r, 204)).send(r)
            })
            break
          case 'put':
            server.put(descriptor.fastifyPath, async (req, rep) => {
              const r = await mod.handler(req.body)
              rep.code(getResponseStatus(r, 200)).send(r)
            })
            break
          case 'patch':
            server.patch(descriptor.fastifyPath, async (req, rep) => {
              const r = await mod.handler(req.body)
              rep.code(getResponseStatus(r, 200)).send(r)
            })
            break
        }
        server.log.info({ route: descriptor.fastifyPath, method: descriptor.method.toUpperCase() }, 'auto-registered route')
      }
    }
    return true
  } catch (e) {
    if (e instanceof OpenApiRouteRegistrationError) throw e
    server.log.warn({ err: e }, 'OpenAPI auto-register skipped')
    return false
  }
}

server.post('/reservations', async (request, reply) => {
  const res = await postReservation(request.body)
  reply.code(getResponseStatus(res, 200)).send(res)
})

server.delete('/reservations/:id', async (request, reply) => {
  const res = await deleteReservation({ id: getRouteParam(request.params, 'id') })
  reply.code(getResponseStatus(res, 204)).send(res)
})

server.get('/inventory/:sku', async (request, reply) => {
  const res = await getInventory({ sku: getRouteParam(request.params, 'sku') })
  reply.code(getResponseStatus(res, 200)).send(res)
})

export async function start() {
  try {
    // Try to auto-register from OpenAPI; fall back to static wiring
    const ok = await tryAutoRegisterFromOpenAPI()
    if (!ok) {
      server.post('/reservations', async (request, reply) => {
        const res = await postReservation(request.body)
        reply.code(getResponseStatus(res, 200)).send(res)
      })
      server.delete('/reservations/:id', async (request, reply) => {
        const res = await deleteReservation({ id: getRouteParam(request.params, 'id') })
        reply.code(getResponseStatus(res, 204)).send(res)
      })
      server.get('/inventory/:sku', async (request, reply) => {
        const res = await getInventory({ sku: getRouteParam(request.params, 'sku') })
        reply.code(getResponseStatus(res, 200)).send(res)
      })
    }
    await server.listen({ port: 3000, host: '0.0.0.0' })
    server.log.info('Server listening on 0.0.0.0:3000')
  } catch (err) {
    server.log.error(err)
    const { safeExit } = await import('./utils/safe-exit.js');
    safeExit(1)
  }
}

if (process.argv[1] && import.meta.url === pathToFileURL(process.argv[1]).href) {
  void start()
}
