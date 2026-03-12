---
docRole: narrative
lastVerified: '2026-03-12'
---

# Proposed Issues to Address in the req2run-benchmark Repository
# req2run-benchmark リポジトリ側で処理すべき問題の提案

> 🌍 Language / 言語: English | 日本語

## 概要
AE Framework の EPIC Phase 1 統合作業中に発見された、req2run-benchmark リポジトリ側で対応が必要な問題について提案します。

---

## 🔧 Issue 1: Integration API Documentation Missing

### 問題
AE Framework との統合に必要な API 仕様が不明確で、統合作業で推測に頼る必要があった。

### 具体的な問題
- リポジトリ構造の仕様が不明
- 問題定義ファイル（YAML）のスキーマが未定義
- 統合方法（Git submodule vs NPM vs Manual clone）が不明
- 環境変数の設定方法が文書化されていない

### 提案する解決策
```markdown no-doctest
## API Documentation Needed

### 1. Repository Structure Specification
```
req2run-benchmark/
├── problems/
│   ├── basic/           # Basic difficulty problems
│   ├── intermediate/    # Intermediate difficulty problems
│   └── advanced/        # Advanced difficulty problems
├── schemas/
│   └── problem.schema.yaml  # Problem definition schema
└── integration/
    ├── setup.md         # Integration setup guide
    └── examples/        # Integration examples
```

### 2. Problem Definition Schema
```yaml no-doctest
# problem.schema.yaml example
problemId: string
title: string
description: string
category: enum [cli-tool, web-api, data-processing, ...]
difficulty: enum [basic, intermediate, advanced, expert]
requirements:
  functional: string[]
  nonfunctional: string[]
expectedOutputs:
  - type: string
    description: string
testCases:
  - input: any
    expectedOutput: any
    description: string
```

### 3. Integration Guide
- Environment variable setup (`REQ2RUN_BENCHMARK_REPO`)
- Problem discovery API
- Validation methods
```

### 優先度: **High**
### 影響: AE Framework の統合テストが mock data に依存している

---

## 📊 Issue 2: Standardized Problem Categories Missing

### 問題
AE Framework が仮定している問題カテゴリが実際の req2run-benchmark の構造と一致しない可能性がある。

### 具体的な問題
```typescript no-doctest
// AE Framework側で仮定している問題ID
const knownBasicProblems = [
  'CLI-001', // File Processing Tool
  'WEB-001', // Simple REST API
  'DATA-001', // CSV Data Processor  
  'CRYPTO-001', // Password Hasher
  'NET-001' // Port Scanner
];
```

### 提案する解決策
1. **問題カテゴリの標準化**
   - CLI tools (CLI-XXX)
   - Web APIs (WEB-XXX)  
   - Data Processing (DATA-XXX)
   - Cryptography (CRYPTO-XXX)
   - Networking (NET-XXX)
   - Authentication (AUTH-XXX)
   - Machine Learning (ML-XXX)

2. **問題リストAPI**
   ```bash no-doctest
   # 問題一覧取得
   req2run list --category=basic --format=json
   
   # 特定問題の詳細取得  
   req2run describe CLI-001 --format=yaml
   ```

### 優先度: **Medium**
### 影響: カテゴリ不整合により適切な問題選択ができない

---

## 🧪 Issue 3: Integration Testing Support Missing

### 問題
AE Framework の CI/CD パイプラインで req2run-benchmark を使用するための仕組みが不足している。

### 具体的な問題
- CI/CD 用の軽量問題セットがない
- 統合テスト用の Docker 環境がない
- 問題の妥当性検証ツールがない

### 提案する解決策

1. **CI/CD サポート**
   ```yaml no-doctest
   # ci/smoke-test.yml
   problems:
     - CLI-001  # Quick execution test
     - WEB-001  # Basic API test
   
   execution:
     timeout: 60s
     parallel: true
   ```

2. **Docker Integration**
   ```dockerfile
   FROM node:18
   COPY problems/ /req2run/problems/
   WORKDIR /req2run
   CMD ["node", "integration-server.js"]
   ```

3. **Validation Tools**
   ```bash no-doctest
   # 問題定義の妥当性検証
   req2run validate problems/basic/CLI-001.yaml
   
   # 統合テスト実行
   req2run integration-test --framework=ae-framework
   ```

### 優先度: **Medium**  
### 影響: 統合テストの自動化が困難

---

## 🔄 Issue 4: Version Compatibility Management Missing

### 問題
req2run-benchmark のバージョン更新時の互換性管理が不明確。

### 具体的な問題
- 問題定義の breaking changes 検出方法なし
- AE Framework との互換性マトリックス不在
- バージョン間のマイグレーションガイドなし

### 提案する解決策

1. **Semantic Versioning**
   - 問題追加: PATCH version
   - 問題定義変更: MINOR version  
   - スキーマ変更: MAJOR version

2. **互換性マトリックス**
   ```markdown no-doctest
   | req2run-benchmark | AE Framework | Status |
   |-------------------|--------------|--------|
   | 1.0.x            | 1.0.x        | ✅ Full |
   | 1.1.x            | 1.0.x        | ⚠️ Limited |
   ```

3. **Migration Tools**
   ```bash no-doctest
   req2run migrate --from=1.0 --to=1.1 --dry-run
   ```

### 優先度: **Low (Future)**
### 影響: 将来的な統合保守性に関わる

---

## 📈 Summary and Recommendations

### Immediate Actions Needed (High Priority)
1. **Integration API Documentation** の作成
2. **Setup Guide** の整備
3. **Problem Schema** の定義

### Short-term Improvements (Medium Priority)  
1. **Standardized Categories** の実装
2. **CI/CD Support** の追加
3. **Integration Testing** の整備

### Long-term Considerations (Low Priority)
1. **Version Management** システム
2. **Advanced Integration** 機能

### 統合成功指標
- ✅ AE Framework が mock fallback なしで動作
- ✅ CI/CD パイプラインで自動テスト実行
- ✅ 新しい問題の追加が容易
- ✅ 複数フレームワークからの利用が可能

---

## 連絡先
これらの問題について議論や詳細確認が必要な場合は、AE Framework リポジトリの Issue #171 でコメントしてください。
