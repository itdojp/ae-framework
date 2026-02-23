import Fastify from 'fastify'
import fs from 'fs'
import path from 'path'
import yaml from 'yaml'
import { handler as postReservation } from './routes/reservations-post.js'
import { handler as deleteReservation } from './routes/reservations-id-delete.js'
import { handler as getInventory } from './routes/inventory-sku-get.js'

const server = Fastify({ logger: true })

type PlainObject = Record<string, unknown>

interface RouteHandlerModule {
  handler: (input: unknown) => Promise<unknown>
}

interface OpenApiLikeSpec {
  paths?: Record<string, unknown>
}

function safeName(p: string) {
  return String(p).replace(/[^a-zA-Z0-9]/g, '-').replace(/-+/g, '-').replace(/^-|-$/g, '')
}

function toPlainObject(value: unknown): PlainObject {
  return value !== null && typeof value === 'object' ? (value as PlainObject) : {}
}

function getResponseStatus(result: unknown, fallback: number): number {
  const status = toPlainObject(result)['status']
  return typeof status === 'number' ? status : fallback
}

function getRouteParam(params: unknown, key: string): string {
  const value = toPlainObject(params)[key]
  if (typeof value === 'string') return value
  if (typeof value === 'number' || typeof value === 'boolean' || typeof value === 'bigint') {
    return String(value)
  }
  return ''
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

async function loadRouteModule(key: string): Promise<RouteHandlerModule | null> {
  const file = path.join(__dirname, 'routes', `${key}.ts`)
  const fileJs = path.join(__dirname, 'routes', `${key}.js`)

  try {
    if (fs.existsSync(fileJs)) {
      const mod: unknown = await import(`./routes/${key}.js`)
      return isRouteHandlerModule(mod) ? mod : null
    }
    if (fs.existsSync(file)) {
      const mod: unknown = await import(`./routes/${key}.ts`)
      return isRouteHandlerModule(mod) ? mod : null
    }
  } catch {
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
    for (const [p, methods] of Object.entries(spec.paths)) {
      const methodMap = toPlainObject(methods)
      for (const [m] of Object.entries(methodMap)) {
        const key = `${safeName(p)}-${String(m).toLowerCase()}`
        const mod = await loadRouteModule(key)
        if (mod?.handler) {
          const routePath = p.replace(/\{([^}]+)\}/g, ':$1')
          switch (String(m).toLowerCase()) {
            case 'get':
              server.get(routePath, async (req, rep) => {
                const r = await mod.handler({ ...toPlainObject(req.params), ...toPlainObject(req.query) })
                rep.code(getResponseStatus(r, 200)).send(r)
              })
              break
            case 'post':
              server.post(routePath, async (req, rep) => {
                const r = await mod.handler(req.body)
                rep.code(getResponseStatus(r, 200)).send(r)
              })
              break
            case 'delete':
              server.delete(routePath, async (req, rep) => {
                const r = await mod.handler(toPlainObject(req.params))
                rep.code(getResponseStatus(r, 204)).send(r)
              })
              break
            case 'put':
              server.put(routePath, async (req, rep) => {
                const r = await mod.handler(req.body)
                rep.code(getResponseStatus(r, 200)).send(r)
              })
              break
            case 'patch':
              server.patch(routePath, async (req, rep) => {
                const r = await mod.handler(req.body)
                rep.code(getResponseStatus(r, 200)).send(r)
              })
              break
          }
          server.log.info({ route: routePath, method: String(m).toUpperCase() }, 'auto-registered route')
        }
      }
    }
    return true
  } catch (e) {
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

if (require.main === module) {
  void start()
}
