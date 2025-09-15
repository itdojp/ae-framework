# Container-Based Verification - Phase 3

> 🌍 Language / 言語: English | 日本語

This document describes the container-based verification system implemented in Phase 3 of the ae-framework, enabling isolated, reproducible verification environments using Podman and Docker.

## Overview

The container-based verification system provides:

- **Isolated Environments**: Run verification in clean, consistent container environments
- **Multi-Engine Support**: Works with both Podman (preferred) and Docker
- **Language Support**: Rust, Elixir, and multi-language project verification
- **Tool Integration**: Seamless integration with existing verification tools
- **Scalable Architecture**: Container engine abstraction for extensibility

## Architecture

### Core Components

```
src/services/container/
├── container-engine.ts       # Abstract engine interface
├── podman-engine.ts         # Podman implementation
├── docker-engine.ts         # Docker implementation  
└── container-manager.ts     # High-level orchestration

src/agents/
├── container-agent.ts       # Container agent with full lifecycle management

src/mcp-server/
└── container-server.ts      # MCP server exposing container tools
```

### Engine Abstraction

The system uses an abstract `ContainerEngine` base class that both Podman and Docker implementations extend:

```typescript
abstract class ContainerEngine {
  // Container lifecycle
  abstract createContainer(config: ContainerConfig): Promise<string>;
  abstract runContainer(config: ContainerConfig, options?: ContainerRunOptions): Promise<RunResult>;
  abstract getContainerStatus(containerId: string): Promise<ContainerStatus>;
  
  // Image management
  abstract buildImage(context: ImageBuildContext, tag: string): Promise<string>;
  abstract pullImage(image: string, tag?: string): Promise<void>;
  
  // Resource management
  abstract cleanup(options?: CleanupOptions): Promise<CleanupResult>;
}
```

## Usage

### Direct Agent Usage

```typescript
import { ContainerAgent } from './src/agents/container-agent.js';

const agent = new ContainerAgent({
  preferredEngine: 'podman',
  autoCleanup: true,
  maxConcurrentContainers: 5
});

await agent.initialize();

// Run verification
const result = await agent.runVerification({
  projectPath: '/path/to/project',
  language: 'rust',
  tools: ['cargo', 'miri', 'prusti']
});

console.log('Verification result:', result.success);
```

### MCP Server

Start the container MCP server:

```bash
npm run container:server
```

Available MCP tools:
- `initialize_container_system`
- `run_container_verification`  
- `build_verification_image`
- `get_verification_job_status`
- `list_verification_jobs`
- `cancel_verification_job`
- `get_container_system_status`
- `cleanup_container_resources`
- `list_container_engines`
- `shutdown_container_system`

### Integration with Verify Agent

The container system integrates with the existing `VerifyAgent`:

```typescript
import { VerifyAgent } from './src/agents/verify-agent.js';

const agent = new VerifyAgent({ 
  enableContainers: true,
  containerConfig: {
    preferredEngine: 'podman'
  }
});

// Run verification with container support
await agent.runFullVerification({
  codeFiles: [...],
  testFiles: [...],
  verificationTypes: ['tests', 'container-verification'],
  containerConfig: {
    enabled: true,
    buildImages: true,
    projectPath: '/path/to/project'
  }
});
```

## Container Images

### Supported Languages

**Rust Verification Environment (`Containerfile.rust`)**
- Base: `rust:1.75-slim`
- Tools: cargo, rustc, miri, prusti, kani
- Features: Formal verification, undefined behavior detection

**Elixir Verification Environment (`Containerfile.elixir`)**
- Base: `elixir:1.15-alpine`
- Tools: elixir, mix, exunit
- Features: Unit testing, integration testing

**Multi-Language Environment (`Containerfile.multi`)**
- Base: `ubuntu:22.04`
- Tools: Combined Rust and Elixir toolchains
- Features: Cross-language project verification

### Building Images

```bash
# Build individual language images
await agent.buildVerificationImage({
  language: 'rust',
  tools: ['cargo', 'miri', 'prusti'],
  tag: 'my-rust-verify:latest'
});

# Build and push to registry
await agent.buildVerificationImage({
  language: 'elixir',
  tools: ['mix', 'exunit'],
  tag: 'registry.example.com/elixir-verify:v1.0',
  push: true
});
```

## Engine Capabilities

### Podman Features (Preferred)
- ✅ Rootless by default
- ✅ SELinux compatibility
- ✅ systemd integration
- ✅ Pod support
- ✅ Compose support (via podman-compose)

### Docker Features  
- ✅ Wide compatibility
- ✅ BuildKit support
- ✅ Compose support
- ❌ Rootless (requires configuration)
- ❌ SELinux integration

### Engine Selection

The system automatically detects and prefers Podman for security, falling back to Docker if Podman is unavailable:

```typescript
// Auto-detect preferred engine
const engine = await ContainerEngineFactory.createPreferredEngine();

// Force specific engine
const podman = await ContainerEngineFactory.createEngine('podman');
const docker = await ContainerEngineFactory.createEngine('docker');
```

## Job Management

### Verification Jobs

Jobs track the complete verification lifecycle:

```typescript
interface VerificationJob {
  id: string;
  name: string;
  projectPath: string;
  language: 'rust' | 'elixir' | 'multi';
  tools: string[];
  status: 'pending' | 'running' | 'completed' | 'failed';
  results?: VerificationResults;
  logs?: ContainerLogs;
}
```

### Job Operations

```typescript
// List all jobs
const jobs = await agent.listJobs();

// Filter by status
const runningJobs = await agent.listJobs({ status: 'running' });

// Get specific job
const job = await agent.getJobStatus('job-id');

// Cancel running job
await agent.cancelJob('job-id');
```

## Resource Management

### Cleanup Operations

```typescript
// Automatic cleanup (default)
const agent = new ContainerAgent({ autoCleanup: true });

// Manual cleanup
await agent.cleanup({
  maxAge: 3600,      // Remove resources older than 1 hour
  keepCompleted: 10, // Keep 10 most recent completed jobs
  force: false       // Don't force removal of active resources
});
```

### Resource Limits

```typescript
const agent = new ContainerAgent({
  maxConcurrentContainers: 10,
  resourceLimits: {
    memory: '2g',
    cpus: '1.0'
  }
});
```

## Configuration

### Agent Configuration

```typescript
interface ContainerAgentConfig {
  preferredEngine?: 'docker' | 'podman';
  autoCleanup?: boolean;
  maxConcurrentContainers?: number;
  containerfilesPath?: string;
  resourceLimits?: {
    memory?: string;
    cpus?: string;
  };
  securityDefaults?: {
    rootless?: boolean;
    readOnlyRootFilesystem?: boolean;
    noNewPrivileges?: boolean;
  };
}
```

### Container Configuration

```typescript
interface ContainerConfig {
  name: string;
  image: string;
  command?: string[];
  environment?: Record<string, string>;
  volumes?: VolumeMount[];
  resources?: ResourceLimits;
  security?: SecurityContext;
}
```

## Security

### Default Security Settings

- **Rootless Operation**: Preferred with Podman
- **Read-only Root Filesystem**: For verification isolation  
- **No New Privileges**: Prevents privilege escalation
- **Capability Dropping**: Minimal required capabilities
- **SELinux Labels**: Enhanced isolation on supported systems

### Volume Mounts

Project code is mounted read-only, results written to separate output volumes:

```typescript
volumes: [
  {
    source: '/path/to/project',
    target: '/workspace',
    readonly: true  // Code mounted read-only
  },
  {
    source: 'verification-output',
    target: '/output',
    type: 'volume'  // Results in named volume
  }
]
```

## Monitoring

### Health Checks

```typescript
const status = await agent.getStatus();
console.log('System Health:', status.data.health);
console.log('Engine:', status.data.engine);
console.log('Active Jobs:', status.data.jobs.active);
```

### Event Monitoring

The system emits events for monitoring:

```typescript
agent.on('jobStarted', ({ jobId, name }) => {
  console.log(`Started: ${name} (${jobId})`);
});

agent.on('jobCompleted', ({ jobId, status, duration }) => {
  console.log(`Completed: ${jobId} - ${status} (${duration}ms)`);
});
```

## Testing

Run container system tests:

```bash
# Run all container tests
npm run test:container

# Test specific components
npx vitest tests/container/container-agent.test.ts
```

## Performance

### Optimization Features

- **Image Caching**: Reuse built verification images
- **Parallel Execution**: Multiple concurrent verification jobs
- **Resource Limits**: Prevent resource exhaustion
- **Cleanup Automation**: Automatic resource reclamation

### Benchmarks

| Operation | Average Time | Memory Usage |
|-----------|--------------|--------------|
| Container Creation | 2-5s | 50MB |
| Rust Verification | 30-120s | 500MB-2GB |
| Elixir Testing | 10-60s | 200MB-1GB |
| Image Build | 2-10min | 1-4GB |

## Troubleshooting

### Common Issues

**Container Engine Not Found**
```bash
# Install Podman (preferred)
sudo apt install podman

# Or install Docker
curl -fsSL https://get.docker.com -o get-docker.sh && sh get-docker.sh
```

**Permission Denied**
```bash
# For Podman (rootless)
podman system reset
loginctl enable-linger $USER

# For Docker
sudo usermod -aG docker $USER && newgrp docker
```

**Build Failures**
- Check Containerfile syntax
- Verify base image availability  
- Ensure sufficient disk space
- Check network connectivity

### Debug Mode

Enable detailed logging:

```typescript
const agent = new ContainerAgent({
  logLevel: 'debug',
  containerConfig: {
    logDriverOptions: { 'max-size': '10m' }
  }
});
```

## Future Enhancements

- **Kubernetes Support**: Run verification in K8s clusters
- **Multi-Architecture**: ARM64 and AMD64 image builds
- **Registry Integration**: Private registry authentication
- **GPU Support**: CUDA/OpenCL verification workloads
- **Distributed Execution**: Multi-node verification clusters

## Contributing

When contributing to container verification:

1. **Test Coverage**: Ensure tests work with both Podman and Docker
2. **Security**: Follow principle of least privilege
3. **Performance**: Consider resource usage and cleanup
4. **Documentation**: Update both code and user documentation
5. **Compatibility**: Test across different container engine versions
