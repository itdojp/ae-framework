# syntax=docker/dockerfile:1
#
# Podman-friendly multi-stage build for ae-framework runtime
#

ARG NODE_IMAGE=docker.io/node:22-alpine
FROM ${NODE_IMAGE} AS deps
WORKDIR /app

COPY package*.json pnpm-lock.yaml* ./
COPY pnpm-workspace.yaml ./
COPY tsconfig*.json ./
COPY packages ./packages
RUN corepack enable pnpm && pnpm install --frozen-lockfile

FROM deps AS build
WORKDIR /app
RUN cp -a packages /tmp/packages-with-deps
COPY . .
RUN for dir in /tmp/packages-with-deps/*; do \
      pkg="$(basename "$dir")"; \
      if [ -d "$dir/node_modules" ]; then \
        rm -rf "packages/$pkg/node_modules"; \
        cp -a "$dir/node_modules" "packages/$pkg/node_modules"; \
      fi; \
    done
RUN pnpm run build && pnpm prune --prod

FROM ${NODE_IMAGE} AS runtime
WORKDIR /app

# Rootless user (matches tests期待)
RUN addgroup -g 1001 -S nodejs && adduser -S nextjs -u 1001

ENV NODE_ENV=production \
    PORT=3000

COPY --from=build --chown=nextjs:nodejs /app/node_modules ./node_modules
COPY --from=build --chown=nextjs:nodejs /app/dist ./dist
COPY --chown=nextjs:nodejs package*.json ./

RUN mkdir -p /app/.ae && chown -R nextjs:nodejs /app
USER nextjs

HEALTHCHECK --interval=30s --timeout=3s --start-period=5s --retries=3 \
    CMD node -e "require('http').get('http://localhost:3000/health', (res) => process.exit(res.statusCode === 200 ? 0 : 1))"

EXPOSE 3000
CMD ["node", "dist/index.js"]
