import path from 'path'
import { describe, expect, it } from 'vitest'
import {
  collectOpenApiRouteDescriptors,
  OpenApiRouteRegistrationError,
  resolveOpenApiRouteDescriptor,
  resolveRouteModulePath,
} from '../../../src/server/openapi-route-security.js'

describe('OpenAPI route registration security', () => {
  it('maps only explicit manifest routes to route modules', () => {
    expect(resolveOpenApiRouteDescriptor('/inventory/{sku}', 'get')).toEqual({
      method: 'get',
      openApiPath: '/inventory/{sku}',
      fastifyPath: '/inventory/:sku',
      moduleKey: 'inventory-sku-get',
    })
    expect(resolveOpenApiRouteDescriptor('/reservations/{id}', 'delete')).toMatchObject({
      method: 'delete',
      fastifyPath: '/reservations/:id',
      moduleKey: 'reservations-id-delete',
    })
  })

  it('rejects unsupported method names before route-key construction', () => {
    expect(() => resolveOpenApiRouteDescriptor('/inventory/{sku}', 'GET')).toThrow(OpenApiRouteRegistrationError)
    expect(() => resolveOpenApiRouteDescriptor('/inventory/{sku}', '../get')).toThrow(OpenApiRouteRegistrationError)
    expect(() => resolveOpenApiRouteDescriptor('/inventory/{sku}', 'get/../../secrets')).toThrow(OpenApiRouteRegistrationError)
  })

  it('rejects unsafe or unexpected OpenAPI paths instead of using lossy path-derived keys', () => {
    for (const unsafePath of [
      '/inventory/../{sku}',
      '/inventory//{sku}',
      '/inventory/{bad-name}',
      '/inventory\\{sku}',
      '/inventory/%2e%2e/{sku}',
    ]) {
      expect(() => resolveOpenApiRouteDescriptor(unsafePath, 'get')).toThrow(OpenApiRouteRegistrationError)
    }

    expect(() => resolveOpenApiRouteDescriptor('/inventory-sku', 'get')).toThrow(OpenApiRouteRegistrationError)
    expect(() => resolveOpenApiRouteDescriptor('/inventory/{sku}/details', 'get')).toThrow(OpenApiRouteRegistrationError)
  })

  it('collects valid descriptors from an OpenAPI-like spec', () => {
    expect(
      collectOpenApiRouteDescriptors({
        paths: {
          '/reservations': { description: 'Reservation collection', parameters: [], post: {} },
          '/reservations/{id}': { delete: {}, summary: 'Reservation by id' },
          '/inventory/{sku}': { get: {}, servers: [] },
        },
      }).map((descriptor) => descriptor.moduleKey),
    ).toEqual(['reservations-post', 'reservations-id-delete', 'inventory-sku-get'])
  })

  it('still rejects unsupported OpenAPI operation method keys', () => {
    expect(() =>
      collectOpenApiRouteDescriptors({
        paths: {
          '/inventory/{sku}': { head: {} },
        },
      }),
    ).toThrow(OpenApiRouteRegistrationError)
  })

  it('fails closed when a spec contains any unexpected public route', () => {
    expect(() =>
      collectOpenApiRouteDescriptors({
        paths: {
          '/reservations': { post: {} },
          '/admin/{id}': { get: {} },
        },
      }),
    ).toThrow(OpenApiRouteRegistrationError)
  })

  it('resolves route modules under the configured routes directory only', () => {
    const routesDir = path.join(process.cwd(), 'src', 'routes')
    expect(resolveRouteModulePath('inventory-sku-get', 'ts', routesDir)).toBe(
      path.resolve(routesDir, 'inventory-sku-get.ts'),
    )

    for (const unsafeKey of [
      '',
      '../inventory-sku-get',
      'inventory-sku-get/../../evil',
      'inventory.sku.get',
      'inventory_sku_get',
    ]) {
      expect(() => resolveRouteModulePath(unsafeKey, 'ts', routesDir)).toThrow(OpenApiRouteRegistrationError)
    }
  })
})
