import Fastify from 'fastify'
import { handler as postReservation } from './routes/reservations-post'
import { handler as deleteReservation } from './routes/reservations-id-delete'
import { handler as getInventory } from './routes/inventory-sku-get'

const server = Fastify({ logger: true })

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

