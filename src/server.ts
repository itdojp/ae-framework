import Fastify from 'fastify'
import fs from 'fs'
import path from 'path'
import yaml from 'yaml'
import { handler as postReservation } from './routes/reservations-post.js'
import { handler as deleteReservation } from './routes/reservations-id-delete.js'
import { handler as getInventory } from './routes/inventory-sku-get.js'

const server = Fastify({ logger: true })

function safeName(p: string) {
  return String(p).replace(/[^a-zA-Z0-9]/g, '-').replace(/-+/g, '-').replace(/^-|-$/g, '')
}

async function tryAutoRegisterFromOpenAPI() {
  try {
    const root = process.cwd()
    const y = path.join(root, 'artifacts', 'codex', 'openapi.yaml')
    const j = path.join(root, 'artifacts', 'codex', 'openapi.json')
    let spec: any | null = null
    if (fs.existsSync(j)) spec = JSON.parse(fs.readFileSync(j, 'utf8'))
    else if (fs.existsSync(y)) spec = yaml.parse(fs.readFileSync(y, 'utf8'))
    if (!spec || !spec.paths) return false
    for (const [p, methods] of Object.entries<any>(spec.paths)) {
      for (const [m] of Object.entries<any>(methods)) {
        const key = `${safeName(p)}-${String(m).toLowerCase()}`
        let mod: any = null
        const file = path.join(__dirname, 'routes', `${key}.ts`)
        const fileJs = path.join(__dirname, 'routes', `${key}.js`)
        try {
          if (fs.existsSync(fileJs)) mod = await import(`./routes/${key}.js`)
          else if (fs.existsSync(file)) mod = await import(`./routes/${key}.ts`)
        } catch {}
        if (mod?.handler) {
          const routePath = p.replace(/\{([^}]+)\}/g, ':$1')
          switch (String(m).toLowerCase()) {
            case 'get': server.get(routePath, async (req, rep) => { const r = await mod.handler({ ...(req.params as any), ...(req.query as any) }); rep.code((r as any).status ?? 200).send(r) }); break
            case 'post': server.post(routePath, async (req, rep) => { const r = await mod.handler(req.body as unknown); rep.code((r as any).status ?? 200).send(r) }); break
            case 'delete': server.delete(routePath, async (req, rep) => { const r = await mod.handler({ ...(req.params as any) }); rep.code((r as any).status ?? 204).send(r) }); break
            case 'put': server.put(routePath, async (req, rep) => { const r = await mod.handler(req.body as unknown); rep.code((r as any).status ?? 200).send(r) }); break
            case 'patch': server.patch(routePath, async (req, rep) => { const r = await mod.handler(req.body as unknown); rep.code((r as any).status ?? 200).send(r) }); break
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
  const res = await postReservation(request.body as unknown)
  reply.code((res as any).status ?? 200).send(res)
})

server.delete('/reservations/:id', async (request, reply) => {
  const res = await deleteReservation({ id: (request.params as any).id })
  reply.code((res as any).status ?? 204).send(res)
})

server.get('/inventory/:sku', async (request, reply) => {
  const res = await getInventory({ sku: (request.params as any).sku })
  reply.code((res as any).status ?? 200).send(res)
})

export async function start() {
  try {
    // Try to auto-register from OpenAPI; fall back to static wiring
    const ok = await tryAutoRegisterFromOpenAPI()
    if (!ok) {
      server.post('/reservations', async (request, reply) => {
        const res = await postReservation(request.body as unknown)
        reply.code((res as any).status ?? 200).send(res)
      })
      server.delete('/reservations/:id', async (request, reply) => {
        const res = await deleteReservation({ id: (request.params as any).id })
        reply.code((res as any).status ?? 204).send(res)
      })
      server.get('/inventory/:sku', async (request, reply) => {
        const res = await getInventory({ sku: (request.params as any).sku })
        reply.code((res as any).status ?? 200).send(res)
      })
    }
    await server.listen({ port: 3000, host: '0.0.0.0' })
    server.log.info('Server listening on 0.0.0.0:3000')
  } catch (err) {
    server.log.error(err)
    process.exit(1)
  }
}

if (require.main === module) {
  start()
}
