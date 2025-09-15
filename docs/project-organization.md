# Project Organization and Maintenance

> 🌍 Language / 言語: English | 日本語

---

## 日本語（概要）

このドキュメントは、AE Framework のプロジェクト構成とメンテナンス手順をまとめたものです。目的は構造の最適化、パフォーマンス向上、開発体験の維持です。

主なポイント
- ディレクトリ構成の原則（関心の分離、アーカイブ戦略、レポート整理、ビルド成果物管理）
- クリーニングスクリプト（`pnpm run clean:*`）と自動化
- レポート/一時ファイルのカテゴリと保持方針
- 運用スケジュール（毎日/毎週/毎月）とベストプラクティス

以降の英語セクションに詳細な手順・例・コマンドを掲載しています。

## Overview

This document outlines the project organization strategy and maintenance procedures for the AE Framework, ensuring optimal project structure, performance, and developer experience.

## Project Structure

### Core Directories

```
ae-framework/
├── src/                    # Source code
├── tests/                  # Test suites
├── scripts/                # Utility scripts
├── docs/                   # Documentation
├── packages/               # Monorepo packages
├── reports/                # Organized reports
├── temp-reports/           # Temporary and archived reports
│   ├── cegis-archives/     # CEGIS conformance reports
│   ├── sample-data-archives/ # Sample data files
│   ├── conformance-archives/ # Conformance test results
│   └── build-artifacts/    # Build-related artifacts
└── config/                 # Configuration files
```

### File Organization Principles

1. **Separation of Concerns**: Source code, tests, documentation, and temporary files are clearly separated
2. **Archival Strategy**: Temporary files are automatically archived rather than deleted
3. **Report Organization**: Reports are categorized by type and purpose
4. **Build Artifact Management**: Build outputs are isolated and can be safely cleaned

## Cleanup and Maintenance

### Automated Cleanup

The project includes automated cleanup tools to maintain project hygiene:

```bash
# Full project cleanup
pnpm run clean:all

# Clean only temporary files and reports
pnpm run clean:project

# Clean archived reports
pnpm run clean:reports

# Clean frontend build artifacts
pnpm run clean:frontend
```

### Cleanup Script Features

The `scripts/project-cleanup.mjs` script provides:

- **File Analysis**: Identifies temporary files, large files, and organizational opportunities
- **Smart Archival**: Moves files to organized archive structure instead of deletion
- **Report Organization**: Categorizes reports by type (testing, performance, security, etc.)
- **Space Optimization**: Tracks and reports space savings
- **Retention Policies**: Keeps recent files while archiving older ones

### File Categories

#### Temporary Files (Auto-archived)
- `cegis-report-*.json` - CEGIS conformance test reports
- `sample-*.json` - Sample data files used in testing
- `conformance-results.json` - Conformance test results
- Build artifacts and coverage reports

#### Reports (Organized by Type)
- **Testing**: Test results, coverage reports
- **Performance**: Lighthouse reports, benchmarks
- **Security**: Security audit results
- **Stability**: Flake detection, CI stability reports
- **Conformance**: CEGIS and compliance reports

#### Build Artifacts (Cleanable)
- Coverage files (`.nyc_output/`, `coverage/`)
- Build outputs (`dist/`, temporary files)
- Test artifacts (`.stryker-tmp/`, mutation reports)

## Maintenance Schedule

### Daily (Automated)
- Temporary file monitoring
- Build artifact cleanup
- Log rotation

### Weekly (Manual/Scripted)
- Run project cleanup script
- Review archived files
- Update documentation

### Monthly (Team Review)
- Archive review and cleanup
- Project structure assessment
- Tool configuration updates

## Best Practices

### File Management

1. **Use .gitignore Effectively**
   - Exclude temporary files and build artifacts
   - Include patterns for generated reports
   - Maintain clear separation between tracked and untracked files

2. **Implement Retention Policies**
   - Keep recent reports for debugging
   - Archive older files for historical reference
   - Regularly review and purge very old archives

3. **Monitor Project Size**
   - Track project growth over time
   - Identify sources of file accumulation
   - Implement automated size monitoring

### Development Workflow

1. **Before Commits**
   ```bash
  pnpm run clean:project
  pnpm run lint
  pnpm run test
   ```

2. **Build Preparation**
   ```bash
  pnpm run clean:all
  pnpm run build
   ```

3. **CI/CD Integration**
   - Include cleanup steps in CI pipelines
   - Archive build artifacts
   - Generate cleanup reports

## Automation and Tools

### Cleanup Script Configuration

The cleanup script can be configured through environment variables:

```bash
# Retention period for reports (days)
export REPORT_RETENTION_DAYS=30

# Maximum archive size (MB)
export MAX_ARCHIVE_SIZE=1000

# Enable aggressive cleanup
export AGGRESSIVE_CLEANUP=true
```

### Integration with Build Tools

```json
{
  "scripts": {
    "prebuild": "pnpm run clean:project",
    "posttest": "pnpm run clean:reports",
    "precommit": "pnpm run clean:project && pnpm run lint"
  }
}
```

### Monitoring and Alerts

- Set up file size monitoring
- Alert on excessive temporary file accumulation
- Track cleanup script execution results

## Troubleshooting

### Common Issues

1. **Large Project Size**
  - Run `pnpm run clean:all`
   - Check `temp-reports/` directory size
   - Review git repository size

2. **Build Failures Due to Artifacts**
  - Clean build artifacts: `pnpm run clean:frontend`
   - Remove node_modules and reinstall
   - Check for permission issues

3. **Missing Reports**
   - Check `temp-reports/` archives
   - Verify cleanup script configuration
   - Review retention policies

### Recovery Procedures

1. **Restore Archived Files**
   ```bash
   # List archived files
   ls temp-reports/*/
   
   # Restore specific file
   cp temp-reports/cegis-archives/report.json ./
   ```

2. **Emergency Cleanup**
   ```bash
   # Remove all temporary files (use with caution)
   rm -rf temp-reports/
   rm -f *-report-*.json
  pnpm run clean:all
   ```

## Continuous Improvement

### Metrics and Monitoring

- Track cleanup effectiveness
- Monitor project size trends
- Measure developer productivity impact

### Tool Enhancement

- Regular review of cleanup script effectiveness
- Update file patterns and categories
- Improve automation and integration

### Team Training

- Onboard new team members on organization practices
- Regular training on cleanup tools
- Share best practices and lessons learned

---

This organization strategy ensures the AE Framework remains maintainable, performant, and developer-friendly while preserving important artifacts and maintaining project hygiene.
