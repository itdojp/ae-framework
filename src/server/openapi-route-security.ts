import path from 'path'

const OPENAPI_ALLOWED_METHODS = ['get', 'post', 'delete', 'put', 'patch'] as const
export type OpenApiMethod = (typeof OPENAPI_ALLOWED_METHODS)[number]

const OPENAPI_PATH_ITEM_METADATA_FIELDS = new Set(['$ref', 'summary', 'description', 'servers', 'parameters'])

export interface OpenApiLikeSpec {
  paths?: Record<string, unknown>
}

export interface OpenApiRouteDescriptor {
  method: OpenApiMethod
  openApiPath: string
  fastifyPath: string
  moduleKey: string
}

const OPENAPI_ROUTE_MANIFEST: ReadonlyArray<OpenApiRouteDescriptor> = [
  { method: 'post', openApiPath: '/reservations', fastifyPath: '/reservations', moduleKey: 'reservations-post' },
  { method: 'delete', openApiPath: '/reservations/{id}', fastifyPath: '/reservations/:id', moduleKey: 'reservations-id-delete' },
  { method: 'get', openApiPath: '/inventory/{sku}', fastifyPath: '/inventory/:sku', moduleKey: 'inventory-sku-get' },
]

const routeManifestBySpecKey = new Map(
  OPENAPI_ROUTE_MANIFEST.map((route) => [openApiRouteSpecKey(route.openApiPath, route.method), route] as const),
)

const routeModuleKeyPattern = /^[a-z0-9]+(?:-[a-z0-9]+)*$/

export class OpenApiRouteRegistrationError extends Error {
  constructor(message: string) {
    super(message)
    this.name = 'OpenApiRouteRegistrationError'
  }
}

function toPlainObject(value: unknown): Record<string, unknown> {
  return value !== null && typeof value === 'object' && !Array.isArray(value)
    ? (value as Record<string, unknown>)
    : {}
}

function openApiRouteSpecKey(openApiPath: string, method: OpenApiMethod): string {
  return `${method} ${openApiPath}`
}

function isAllowedOpenApiMethod(method: string): method is OpenApiMethod {
  return (OPENAPI_ALLOWED_METHODS as readonly string[]).includes(method)
}

function isOpenApiPathItemMetadataField(field: string): boolean {
  return OPENAPI_PATH_ITEM_METADATA_FIELDS.has(field)
}

function isSafeOpenApiPath(openApiPath: string): boolean {
  if (!openApiPath.startsWith('/') || openApiPath.includes('\\') || openApiPath.includes('\0')) {
    return false
  }
  const segments = openApiPath.split('/').slice(1)
  if (segments.length === 0) return false
  return segments.every((segment) => {
    if (!segment || segment === '.' || segment === '..') return false
    return /^[A-Za-z0-9_-]+$/.test(segment) || /^\{[A-Za-z][A-Za-z0-9_]*\}$/.test(segment)
  })
}

export function resolveOpenApiRouteDescriptor(openApiPath: string, rawMethod: string): OpenApiRouteDescriptor {
  if (!isAllowedOpenApiMethod(rawMethod)) {
    throw new OpenApiRouteRegistrationError(`Unsupported OpenAPI method for route registration: ${rawMethod}`)
  }
  if (!isSafeOpenApiPath(openApiPath)) {
    throw new OpenApiRouteRegistrationError(`Unsafe OpenAPI path for route registration: ${openApiPath}`)
  }

  const descriptor = routeManifestBySpecKey.get(openApiRouteSpecKey(openApiPath, rawMethod))
  if (!descriptor) {
    throw new OpenApiRouteRegistrationError(`Unexpected OpenAPI route: ${rawMethod.toUpperCase()} ${openApiPath}`)
  }
  assertSafeRouteModuleKey(descriptor.moduleKey)
  return descriptor
}

export function collectOpenApiRouteDescriptors(spec: OpenApiLikeSpec): OpenApiRouteDescriptor[] {
  const descriptors: OpenApiRouteDescriptor[] = []
  const seenRoutes = new Set<string>()
  const seenModuleKeys = new Set<string>()

  for (const [openApiPath, methods] of Object.entries(spec.paths ?? {})) {
    const methodMap = toPlainObject(methods)
    for (const [rawMethod] of Object.entries(methodMap)) {
      if (isOpenApiPathItemMetadataField(rawMethod)) continue
      const descriptor = resolveOpenApiRouteDescriptor(openApiPath, rawMethod)
      const routeKey = `${descriptor.method} ${descriptor.fastifyPath}`
      if (seenRoutes.has(routeKey)) {
        throw new OpenApiRouteRegistrationError(`Duplicate OpenAPI route registration: ${routeKey}`)
      }
      if (seenModuleKeys.has(descriptor.moduleKey)) {
        throw new OpenApiRouteRegistrationError(`Duplicate OpenAPI route module registration: ${descriptor.moduleKey}`)
      }
      seenRoutes.add(routeKey)
      seenModuleKeys.add(descriptor.moduleKey)
      descriptors.push(descriptor)
    }
  }

  return descriptors
}

function assertSafeRouteModuleKey(key: string): void {
  if (!routeModuleKeyPattern.test(key)) {
    throw new OpenApiRouteRegistrationError(`Unsafe route module key: ${key}`)
  }
}

function isPathWithin(baseDir: string, candidatePath: string): boolean {
  const relative = path.relative(baseDir, candidatePath)
  return relative === '' || (!!relative && !relative.startsWith('..') && !path.isAbsolute(relative))
}

export function resolveRouteModulePath(key: string, extension: 'js' | 'ts', baseRoutesDir: string): string {
  assertSafeRouteModuleKey(key)
  const resolvedBase = path.resolve(baseRoutesDir)
  const candidate = path.resolve(resolvedBase, `${key}.${extension}`)
  if (!isPathWithin(resolvedBase, candidate)) {
    throw new OpenApiRouteRegistrationError(`Route module path escaped routes directory: ${key}.${extension}`)
  }
  return candidate
}
