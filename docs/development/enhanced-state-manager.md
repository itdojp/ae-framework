# Enhanced State Manager

The Enhanced State Manager is a comprehensive state management system for AE-Framework that provides SQLite-like storage with advanced features including versioning, compression, transactions, and EventBus integration for CEGIS (Counterexample-Guided Iterative Synthesis) workflows.

## Overview

The Enhanced State Manager builds upon the basic PhaseStateManager to provide:

- **SQLite-like Storage**: Logical key + ISO timestamp naming convention
- **SSOT Management**: Single Source of Truth for AE-IR specifications
- **Version Control**: Multi-version storage with automatic cleanup
- **Compression**: Automatic compression for large data with configurable thresholds
- **Transactions**: Atomic operations with rollback support
- **Garbage Collection**: TTL-based cleanup with configurable intervals
- **EventBus Integration**: CEGIS trigger notifications for failure artifacts
- **Snapshots**: Compressed state snapshots for backup and recovery

## Architecture

### Core Components

```typescript
┌─────────────────────┐    ┌─────────────────────┐    ┌─────────────────────┐
│  EnhancedStateCLI   │───▶│ EnhancedStateManager │───▶│   Storage Layer     │
├─────────────────────┤    ├─────────────────────┤    ├─────────────────────┤
│ - CLI Commands      │    │ - SSOT Management   │    │ - Memory Storage    │
│ - User Interface    │    │ - Version Control   │    │ - File Persistence  │
│ - Event Monitoring  │    │ - Transactions      │    │ - Compression       │
└─────────────────────┘    │ - EventBus          │    │ - Index Management  │
                           │ - Garbage Collection │    └─────────────────────┘
                           └─────────────────────┘
                                      │
                                      ▼
                           ┌─────────────────────┐
                           │    Event System     │
                           ├─────────────────────┤
                           │ - CEGIS Triggers    │
                           │ - Lifecycle Events  │
                           │ - Failure Tracking  │
                           └─────────────────────┘
```

### Storage Strategy

#### Key Naming Convention
```
{logicalKey}_{ISO_timestamp}
```

Examples:
- `user_spec_2025-01-20T10:00:00.000Z`
- `product_model_2025-01-20T10:15:30.123Z`
- `validation_rules_2025-01-20T10:30:45.456Z`

#### Data Structure
```typescript
interface StateEntry<T> {
  id: string;                    // Unique identifier
  logicalKey: string;           // Business identifier
  timestamp: string;            // ISO format timestamp
  version: number;              // Sequential version number
  checksum: string;             // Data integrity hash
  data: T;                      // Actual data (potentially compressed)
  compressed: boolean;          // Compression flag
  tags: Record<string, string>; // Metadata tags
  ttl?: number;                 // Time to live in seconds
  metadata: {
    size: number;               // Data size in bytes
    created: string;            // Creation timestamp
    accessed: string;           // Last access timestamp
    source: string;             // Data source identifier
    phase?: string;             // Development phase
  };
}
```

## Features

### 1. SSOT (Single Source of Truth) Management

The Enhanced State Manager specializes in managing AE-IR (AI-Enhanced Intermediate Representation) data as the single source of truth.

#### Save SSOT Data
```typescript
const key = await stateManager.saveSSOT('user_specification', aeir, {
  phase: 'phase-5',
  tags: { environment: 'production', version: '2.1.0' },
  ttl: 604800, // 7 days
  source: 'domain_modeling'
});
```

#### Load SSOT Data
```typescript
// Load latest version
const latestSpec = await stateManager.loadSSOT('user_specification');

// Load specific version
const version2 = await stateManager.loadSSOT('user_specification', 2);
```

#### Version Management
```typescript
// Get all versions
const versions = await stateManager.getVersions('user_specification');
console.log(versions);
// [
//   { version: 3, timestamp: '2025-01-20T12:00:00Z', key: '...' },
//   { version: 2, timestamp: '2025-01-20T11:00:00Z', key: '...' },
//   { version: 1, timestamp: '2025-01-20T10:00:00Z', key: '...' }
// ]
```

### 2. Transaction Support

Atomic operations ensure data consistency during complex workflows.

```typescript
// Begin transaction
const txId = await stateManager.beginTransaction();

try {
  // Multiple operations within transaction
  await stateManager.saveSSOT('spec1', aeir1, { phase: 'test' });
  await stateManager.saveSSOT('spec2', aeir2, { phase: 'test' });
  await stateManager.saveSSOT('spec3', aeir3, { phase: 'test' });
  
  // Commit all changes
  await stateManager.commitTransaction(txId);
  console.log('All changes committed successfully');
  
} catch (error) {
  // Rollback on error
  await stateManager.rollbackTransaction(txId);
  console.error('Transaction rolled back:', error);
}
```

### 3. Compressed Snapshots

Create compressed snapshots for backup, recovery, or phase transitions.

```typescript
// Create snapshot of entire phase
const snapshotId = await stateManager.createSnapshot('phase-5');

// Create snapshot of specific entities
const entitySnapshotId = await stateManager.createSnapshot('phase-5', ['User', 'Product']);

// Load snapshot
const snapshot = await stateManager.loadSnapshot(snapshotId);
console.log(`Snapshot contains ${Object.keys(snapshot).length} entries`);
```

### 4. Failure Artifact Management & CEGIS Integration

The system provides specialized handling for failure artifacts that trigger CEGIS workflows.

```typescript
// Define failure artifact
const failureArtifact: FailureArtifact = {
  id: `validation_failure_${Date.now()}`,
  timestamp: new Date().toISOString(),
  phase: 'phase-4',
  type: 'validation',
  error: new Error('Domain invariant violated'),
  context: {
    invariant: 'user.email.unique',
    violatingRecords: ['user123', 'user456']
  },
  artifacts: ['validation-report.json', 'error-log.txt'],
  retryable: true,
  severity: 'high'
};

// Persist and trigger CEGIS
await stateManager.persistFailureArtifact(failureArtifact);
```

#### Event Handling for CEGIS
```typescript
// Listen for CEGIS triggers
stateManager.on('failureArtifactPersisted', (event) => {
  if (event.cegis_trigger) {
    console.log(`CEGIS triggered for ${event.artifact.type} failure in ${event.artifact.phase}`);
    
    // Trigger counterexample-guided synthesis
    triggerCEGISWorkflow(event.artifact);
  }
});

// Specific failure type handling
stateManager.on('failure_validation', (artifact) => {
  console.log('Validation failure detected:', artifact.error.message);
  // Handle validation-specific CEGIS workflow
});

stateManager.on('failure_compilation', (artifact) => {
  console.log('Compilation failure detected:', artifact.error.message);
  // Handle compilation-specific CEGIS workflow
});
```

### 5. Automatic Compression

Large data is automatically compressed based on configurable thresholds.

```typescript
const stateManager = new EnhancedStateManager(projectRoot, {
  enableCompression: true,
  compressionThreshold: 1024, // 1KB threshold
  // Data larger than 1KB will be compressed
});
```

### 6. Garbage Collection with TTL

Automatic cleanup of expired entries based on TTL (Time To Live).

```typescript
const stateManager = new EnhancedStateManager(projectRoot, {
  defaultTTL: 604800,    // 7 days default TTL
  gcInterval: 3600,      // Run GC every hour
});

// Custom TTL for specific data
await stateManager.saveSSOT('temporary_spec', aeir, {
  ttl: 86400 // 24 hours
});
```

## CLI Interface

The Enhanced State Manager provides a comprehensive CLI for all operations.

### Basic Operations

```bash
# Save SSOT data
ae-framework enhanced-state save -k "user_spec" -i "user-spec.json" -p "phase-5" --source "domain_modeling"

# Load SSOT data
ae-framework enhanced-state load -k "user_spec" -o "loaded-spec.json"

# Load specific version
ae-framework enhanced-state load -k "user_spec" -v 2 -o "spec-v2.json"

# List all versions
ae-framework enhanced-state versions -k "user_spec"
```

### Advanced Operations

```bash
# Create snapshot
ae-framework enhanced-state snapshot -p "phase-5" -e "User,Product"

# Load snapshot
ae-framework enhanced-state load-snapshot -s "snapshot_phase-5_2025-01-20T10:00:00Z"

# Simulate failure for CEGIS testing
ae-framework enhanced-state simulate-failure -p "phase-4" -t "validation" -m "Invariant violation" -s "critical" --retryable

# View statistics
ae-framework enhanced-state stats

# Test transaction functionality
ae-framework enhanced-state test-tx

# Run garbage collection
ae-framework enhanced-state gc
```

### State Management

```bash
# Export state for backup
ae-framework enhanced-state export -o "state-backup.json"

# Import state from backup
ae-framework enhanced-state import -i "state-backup.json"
```

## Configuration Options

```typescript
interface StorageOptions {
  databasePath?: string;          // Default: '.ae/enhanced-state.db'
  enableCompression?: boolean;    // Default: true
  compressionThreshold?: number;  // Default: 1024 bytes
  defaultTTL?: number;           // Default: 604800 seconds (7 days)
  gcInterval?: number;           // Default: 3600 seconds (1 hour)
  maxVersions?: number;          // Default: 10
  enableTransactions?: boolean;   // Default: true
}

const stateManager = new EnhancedStateManager(projectRoot, {
  enableCompression: true,
  compressionThreshold: 2048,    // 2KB threshold
  defaultTTL: 1209600,          // 14 days
  gcInterval: 1800,             // 30 minutes
  maxVersions: 20,              // Keep 20 versions
  enableTransactions: true
});
```

## Integration with AE-Framework Phases

### Phase-Aware Storage

```typescript
// Phase 1: Intent
await stateManager.saveSSOT('intent_analysis', intentData, {
  phase: 'phase-1',
  source: 'intent_agent'
});

// Phase 2: Natural Language Requirements
await stateManager.saveSSOT('requirements', requirementsData, {
  phase: 'phase-2',
  source: 'natural_language_processor'
});

// Phase 5: Domain Modeling
await stateManager.saveSSOT('domain_model', domainModel, {
  phase: 'phase-5',
  source: 'domain_modeling_agent'
});
```

### Failure Handling Across Phases

```typescript
// Phase-specific failure handling
const phases = ['phase-1', 'phase-2', 'phase-3', 'phase-4', 'phase-5', 'phase-6'];

phases.forEach(phase => {
  stateManager.on(`failure_${phase}`, (artifact) => {
    console.log(`Failure in ${phase}:`, artifact.error.message);
    
    // Phase-specific CEGIS workflows
    switch (phase) {
      case 'phase-1':
        triggerIntentRefinement(artifact);
        break;
      case 'phase-2':
        triggerRequirementsRefinement(artifact);
        break;
      case 'phase-5':
        triggerDomainModelRefinement(artifact);
        break;
    }
  });
});
```

## Event System

### Core Events

```typescript
// Lifecycle events
stateManager.on('stateManagerInitialized', () => {
  console.log('Enhanced State Manager ready');
});

stateManager.on('stateManagerShutdown', () => {
  console.log('Enhanced State Manager shutdown complete');
});

// SSOT events
stateManager.on('ssotSaved', (event) => {
  console.log(`SSOT saved: ${event.logicalKey} v${event.version}`);
});

stateManager.on('ssotLoaded', (event) => {
  console.log(`SSOT loaded: ${event.logicalKey} v${event.version}`);
});

// Transaction events
stateManager.on('transactionCommitted', (event) => {
  console.log(`Transaction committed: ${event.txId} (${event.operationCount} operations)`);
});

stateManager.on('transactionRolledBack', (event) => {
  console.log(`Transaction rolled back: ${event.txId} (${event.operationCount} operations)`);
});

// Snapshot events
stateManager.on('snapshotCreated', (event) => {
  console.log(`Snapshot created: ${event.snapshotId}`);
});

stateManager.on('snapshotLoaded', (event) => {
  console.log(`Snapshot loaded: ${event.snapshotId}`);
});

// Maintenance events
stateManager.on('garbageCollectionCompleted', (event) => {
  console.log(`GC completed: ${event.expiredCount} entries removed`);
});

stateManager.on('versionsCleanedUp', (event) => {
  console.log(`Versions cleaned up: ${event.logicalKey} (${event.deletedCount} old versions removed)`);
});
```

### CEGIS-Specific Events

```typescript
// Main CEGIS trigger
stateManager.on('failureArtifactPersisted', (event) => {
  if (event.cegis_trigger) {
    // Route to appropriate CEGIS workflow
    routeToCEGISWorkflow(event.artifact);
  }
});

// Failure type-specific events
stateManager.on('failure_validation', handleValidationFailure);
stateManager.on('failure_compilation', handleCompilationFailure);
stateManager.on('failure_test', handleTestFailure);
stateManager.on('failure_verification', handleVerificationFailure);
stateManager.on('failure_generation', handleGenerationFailure);
```

## Best Practices

### 1. Logical Key Naming

```typescript
// Good: Use hierarchical naming
'domain.user.specification'
'api.authentication.definition'
'phase5.domain_model.final'

// Avoid: Generic or ambiguous names
'data1', 'temp', 'test'
```

### 2. Phase Management

```typescript
// Always specify phase for better organization
await stateManager.saveSSOT('specification', data, {
  phase: getCurrentPhase(),
  source: 'current_agent',
  tags: { environment: process.env.NODE_ENV }
});
```

### 3. Transaction Usage

```typescript
// Use transactions for related operations
const txId = await stateManager.beginTransaction();
try {
  // Save related specifications together
  await stateManager.saveSSOT('domain_model', domainData, { phase });
  await stateManager.saveSSOT('api_specification', apiData, { phase });
  await stateManager.saveSSOT('validation_rules', validationData, { phase });
  
  await stateManager.commitTransaction(txId);
} catch (error) {
  await stateManager.rollbackTransaction(txId);
  throw error;
}
```

### 4. Failure Artifact Design

```typescript
// Provide rich context for CEGIS
const failureArtifact: FailureArtifact = {
  id: `${type}_${phase}_${timestamp}`,
  timestamp: new Date().toISOString(),
  phase,
  type,
  error,
  context: {
    // Include as much context as possible
    inputs: inputData,
    expectedOutput: expectedResult,
    actualOutput: actualResult,
    configuration: currentConfig,
    environment: process.env.NODE_ENV
  },
  artifacts: [
    'error-log.txt',
    'input-data.json',
    'configuration.yaml'
  ],
  retryable: determineIfRetryable(error),
  severity: calculateSeverity(error, context)
};
```

### 5. Resource Management

```typescript
// Always shutdown properly
process.on('SIGINT', async () => {
  console.log('Shutting down Enhanced State Manager...');
  await stateManager.shutdown();
  process.exit(0);
});

process.on('SIGTERM', async () => {
  console.log('Terminating Enhanced State Manager...');
  await stateManager.shutdown();
  process.exit(0);
});
```

## Performance Considerations

### Memory Management
- The system uses in-memory storage with periodic disk persistence
- Large datasets are automatically compressed
- Garbage collection removes expired entries
- Version cleanup prevents unlimited growth

### Compression Strategy
- Automatic compression for data exceeding threshold
- Uses gzip compression for optimal balance of speed and size
- Compressed data is transparently decompressed on read

### Transaction Overhead
- Transactions add minimal overhead for small operations
- Rollback data is stored in memory during transaction
- Use transactions judiciously for related operations only

## Monitoring and Diagnostics

### Statistics Monitoring

```typescript
const stats = stateManager.getStatistics();
console.log('Enhanced State Manager Statistics:', {
  totalEntries: stats.totalEntries,
  totalSize: formatBytes(stats.totalSize),
  compressionRatio: stats.compressedEntries / stats.totalEntries,
  logicalKeys: stats.logicalKeys,
  averageVersionsPerKey: stats.averageVersions,
  activeTransactions: stats.activeTransactions
});
```

### Health Checks

```typescript
// Periodic health check
setInterval(async () => {
  const stats = stateManager.getStatistics();
  
  // Alert on high memory usage
  if (stats.totalSize > MAX_MEMORY_THRESHOLD) {
    console.warn('High memory usage detected');
    await stateManager.runGarbageCollection();
  }
  
  // Alert on too many active transactions
  if (stats.activeTransactions > MAX_TRANSACTIONS) {
    console.warn('High number of active transactions');
  }
}, 60000); // Check every minute
```

## Migration and Backup

### Regular Backups

```bash
# Automated backup script
#!/bin/bash
BACKUP_DIR="/backups/ae-framework"
TIMESTAMP=$(date +%Y%m%d_%H%M%S)

ae-framework enhanced-state export -o "$BACKUP_DIR/state_$TIMESTAMP.json"
```

### State Migration

```typescript
// Migrate between environments
async function migrateState(fromEnv: string, toEnv: string) {
  const sourceManager = new EnhancedStateManager(`/data/${fromEnv}`);
  const targetManager = new EnhancedStateManager(`/data/${toEnv}`);
  
  await sourceManager.initialize();
  await targetManager.initialize();
  
  const exportedState = await sourceManager.exportState();
  await targetManager.importState(exportedState);
  
  await sourceManager.shutdown();
  await targetManager.shutdown();
}
```

This Enhanced State Manager provides a robust foundation for managing complex state in AE-Framework with advanced features that support sophisticated workflows including CEGIS integration, making it ideal for AI-enhanced development processes.