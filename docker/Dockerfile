# Stage 1: Install all dependencies (including dev dependencies)
FROM docker.io/node:22-alpine AS deps
WORKDIR /app

# Copy package files
COPY package*.json ./
COPY pnpm-lock.yaml* ./

# Install all dependencies first (needed for building)
RUN corepack enable pnpm && \
    pnpm install --frozen-lockfile

# Stage 2: Build the application
FROM deps AS build
WORKDIR /app

# Copy source code
COPY . .

# Build the application
RUN pnpm run build

# Remove dev dependencies after build
RUN pnpm prune --prod

# Stage 3: Production runtime with minimal dependencies
FROM docker.io/node:22-alpine AS runtime
WORKDIR /app

# Create non-root user for security
RUN addgroup -g 1001 -S nodejs && \
    adduser -S nextjs -u 1001

# Set production environment
ENV NODE_ENV=production

# Copy only production dependencies from build stage
COPY --from=build --chown=nextjs:nodejs /app/node_modules ./node_modules

# Copy built application
COPY --from=build --chown=nextjs:nodejs /app/dist ./dist

# Copy only necessary files for runtime
COPY --chown=nextjs:nodejs package*.json ./

# Create directory for application data
RUN mkdir -p /app/.ae && \
    chown -R nextjs:nodejs /app/.ae

# Switch to non-root user
USER nextjs

# Health check
HEALTHCHECK --interval=30s --timeout=3s --start-period=5s --retries=3 \
    CMD node -e "require('http').get('http://localhost:3000/health', (res) => process.exit(res.statusCode === 200 ? 0 : 1))"

# Expose port
EXPOSE 3000

# Start the application
CMD ["node", "dist/index.js"]