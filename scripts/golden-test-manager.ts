#!/usr/bin/env ts-node

/**
 * Golden Test Management CLI
 * 
 * Provides commands for managing code generation snapshots:
 * - approve: Approve current snapshot as the new baseline
 * - diff: Show differences between current and approved snapshots
 * - reset: Reset approved snapshot (requires confirmation)
 */

import { CodegenSnapshotManager } from '../tests/golden/codegen-snapshot.test.js';
import { readFileSync, existsSync } from 'fs';

const snapshotManager = new CodegenSnapshotManager();

async function main() {
  const command = process.argv[2];

  switch (command) {
    case 'approve':
      await handleApprove();
      break;
    case 'diff':
      await handleDiff();
      break;
    case 'reset':
      await handleReset();
      break;
    case 'status':
      await handleStatus();
      break;
    default:
      showHelp();
      process.exit(1);
  }
}

async function handleApprove() {
  try {
    console.log('📸 Generating current snapshot...');
    const currentSnapshot = await snapshotManager.generateSnapshot();
    
    console.log('✅ Approving snapshot...');
    snapshotManager.approveSnapshot();
    
    console.log('');
    console.log('🎉 Snapshot approved successfully!');
    console.log(`   Files: ${currentSnapshot.summary.totalFiles}`);
    console.log(`   Lines: ${currentSnapshot.summary.totalLines}`);
    console.log(`   ARIA attributes: ${currentSnapshot.summary.totalAriaAttributes}`);
    console.log('');
    console.log('Future test runs will use this as the baseline.');
  } catch (error) {
    console.error('❌ Failed to approve snapshot:', (error as Error).message);
    process.exit(1);
  }
}

async function handleDiff() {
  try {
    console.log('📸 Generating current snapshot...');
    const currentSnapshot = await snapshotManager.generateSnapshot();
    
    const approvedSnapshot = snapshotManager.loadApprovedSnapshot();
    if (!approvedSnapshot) {
      console.log('⚠️  No approved snapshot found. Run with "approve" first.');
      return;
    }

    const comparison = snapshotManager.compareSnapshots(currentSnapshot, approvedSnapshot);
    
    if (comparison.passed) {
      console.log('✅ No differences found between current and approved snapshots.');
      return;
    }

    console.log('📊 Snapshot differences:');
    console.log('');
    comparison.differences.forEach(diff => {
      console.log(`   ${diff}`);
    });
    console.log('');
    console.log('🔧 To approve these changes, run: pnpm test:golden:approve');
  } catch (error) {
    console.error('❌ Failed to compare snapshots:', (error as Error).message);
    process.exit(1);
  }
}

async function handleReset() {
  const approvedPath = './tests/golden/snapshots/codegen-approved.json';
  
  if (!existsSync(approvedPath)) {
    console.log('ℹ️  No approved snapshot found to reset.');
    return;
  }

  // Simple confirmation check
  const isCI = process.env.CI === 'true';
  if (!isCI) {
    console.log('⚠️  This will delete the approved snapshot baseline.');
    console.log('🔧 To confirm, run: rm tests/golden/snapshots/codegen-approved.json');
    return;
  }

  // In CI, we can reset automatically if needed
  console.log('🔄 Resetting approved snapshot in CI environment...');
}

async function handleStatus() {
  try {
    console.log('📊 Golden Test Status:');
    console.log('');

    const approvedSnapshot = snapshotManager.loadApprovedSnapshot();
    if (!approvedSnapshot) {
      console.log('❌ No approved baseline found');
      console.log('🔧 Run "pnpm test:golden:approve" to create initial baseline');
      return;
    }

    console.log('✅ Approved baseline found');
    console.log(`   Files: ${approvedSnapshot.summary.totalFiles}`);
    console.log(`   Lines: ${approvedSnapshot.summary.totalLines}`);
    console.log(`   ARIA attributes: ${approvedSnapshot.summary.totalAriaAttributes}`);
    console.log(`   Approved: ${new Date(approvedSnapshot.timestamp).toLocaleString()}`);

    console.log('');
    console.log('📸 Generating current snapshot for comparison...');
    const currentSnapshot = await snapshotManager.generateSnapshot();
    
    const comparison = snapshotManager.compareSnapshots(currentSnapshot, approvedSnapshot);
    
    if (comparison.passed) {
      console.log('✅ Current code matches approved baseline');
    } else {
      console.log(`⚠️  ${comparison.differences.length} differences found`);
      console.log('🔧 Run "pnpm test:golden:diff" for details');
    }
  } catch (error) {
    console.error('❌ Failed to check status:', (error as Error).message);
    process.exit(1);
  }
}

function showHelp() {
  console.log('Golden Test Manager');
  console.log('');
  console.log('Usage:');
  console.log('  pnpm test:golden:approve  - Approve current snapshot as baseline');
  console.log('  pnpm test:golden:diff     - Show differences from approved baseline');
  console.log('  pnpm test:golden:status   - Show current status');
  console.log('  pnpm test:golden:reset    - Reset approved baseline');
  console.log('');
  console.log('Golden tests ensure code generation consistency and require');
  console.log('explicit approval for changes to prevent unintended drift.');
}

if (require.main === module) {
  main().catch(error => {
    console.error('❌ Unexpected error:', error);
    process.exit(1);
  });
}