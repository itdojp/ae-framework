# AE Framework 基礎調査（Formal Methods × AI）

> 🌍 Language / 言語: 日本語 | English

---

## English (Overview)

Foundation survey for implementing a pipeline from NL → BDD → Formal Specs → TDD → Code → Operate. Strategy: generate → verify → repair with verifiers as final arbiters, integrating MBT, conformance checking, and runtime verification. See Japanese sections for detailed mappings, artifacts, and procedures.
**Repository:** [itdojp/ae-framework](https://github.com/itdojp/ae-framework)  
**Status:** Draft (v0.1) ― 2025-09-12  
**Audience:** プロダクトオーナー / アーキテクト / テックリード / 開発者 / QA

> 本ドキュメントは、`ae-framework` における **NL→BDD→形式仕様→TDD→コード→運用** の一貫パイプラインを実装・拡張するための“基礎調査（foundation survey）”です。  
> 研究サーベイの要点を **リポジトリ構成・開発フロー・ツール選定・CI/品質ゲート** に落とし込み、即時に利用できる運用指針・テンプレート・ロードマップをまとめました。

---

## 0. TL;DR

- **目的**: 自然言語要求から **BDD（Gherkin）** を経て **形式仕様**（TLA+/Alloy/Dafny など）を確立し、**TDD** と **モデルベーステスト（MBT）**、**適合性検査（Conformance Checking）** と **ランタイム検証** を統合する。
- **戦略**: 生成AI（LLM）は **候補生成** に特化、**検証器が最終裁定** を担う **“Generate → Verify → Repair”** の閉ループを全段に通す。
- **実装アプローチ（最小実用）**:  
  1) NL→BDD→形式仕様を半自動化（人間が on-the-loop で承認）、  
  2) 仕様から **テスト（反例・トレース）** を自動生成して TDD を駆動、  
  3) コードは必要範囲で LLM 補助＋静的/動的/形式検証で**継続的適合**を担保。

---

## 1. リポジトリ整合性（ae-framework へのフィット）

`ae-framework` の README/設計方針（**6-Phase Workflow**）に対して、本調査の成果を次のようにマッピングします。

### 1.1 6-Phase へのマッピング（提案）
| ae-framework の Phase | 本調査の主要アウトプット | 生成/検証の要点 |
|---|---|---|
| 1. Intent Analysis | NL 要求の整形・用語辞書・曖昧性指摘 | NL 正規化 → BDD 変換の前工程。用語辞書（`traceability.json`）更新 |
| 2. Natural Language Requirements | **BDD(Gherkin)** 草案/テンプレ、品質チェック | LLM で候補生成 → 人手承認 → Gherkin リンター & 交差レビュー |
| 3. User Stories Creation | 受入条件/例ベース仕様、**BDD→形式仕様(LTL/TLA+/Contracts)** | nl2spec/SpecGen系パターンでプロパティ候補生成 → 検証器で裁定 |
| 4. Validation | **モデル検査/定理証明/SMT**・**MBT**・**適合性検査** | TLC/Apalache/Alloy6/cvc5 などで性質検証・反例からテスト生成 |
| 5. Domain Modeling | DDD モデルと形式仕様の整合性管理 | Ubiquitous Language と型/制約を同期（Typescript 型, Dafny 契約） |
| 6. UI/UX & Frontend Delivery | 受入/E2E テストをオラクル化、A11y/Perf を品質ゲート | Playwright/Storybook/Vitest + Lighthouse/AXE を**仕様に紐づく**ゲートへ |

> **既存ディレクトリとの対応（推奨配置）**  
> `spec/` or `specs/`：TLA+/Alloy/Dafny 等の正式仕様、`tests/`：MBT/プロパティ/適合性テスト、`policies/`：Cedar/OPA 等、`observability/`：OpenTelemetry 設定、`hermetic-reports/`：モデル検査ログ・反例、`docs/quality/`：品質ゲート基準、`templates/`：シナリオ/仕様テンプレ。

---

## 2. 全体アーキテクチャ（Mermaid）

```mermaid
flowchart LR
  A[Natural Language\nRequirements] --> B[BDD\n(Gherkin)]
  B --> C[Formal Specs\n(TLA+, Alloy6, Dafny/Contracts)]
  C --> D[Verification\n(Model Checking / SMT / ITP)]
  D --> E[MBT/Test Oracle\n反例→テスト/トレース適合]
  E --> F[Implement\n(LLM補助+TDD)]
  F --> G[Conformance &\nRuntime Verification]
  G --> H[Operate\n(OTel/Policies)]
  D -. counterexamples .-> E
  G -. logs/traces .-> D
```

---

## 3. 成果物（Artifacts）定義

- **NL 正規化**: 用語辞書・曖昧性チケット・境界条件一覧（`docs/`）  
- **BDD（Gherkin）**: `features/*.feature`（日本語/英語対応、リンタ・重複チェック）  
- **形式仕様**: 
  - **TLA+**（`spec/*.tla` + `MC/*.cfg`）: 並行プロトコル/一貫性/安全性・ライブネス  
  - **Alloy 6**（`spec/*.als`）: 構造制約＋**時間演算子**による動的性質  
  - **Dafny/Contracts**（`*.dfy` / JML/ACSL）: 実装近傍の契約・不変量  
- **テスト**: MBT/プロパティベース/受入（Playwright/Vitest/Cucumber）  
- **適合性検査**: 仕様⇄実装の**トレース適合チェック**（反例→再現テスト）  
- **運用**: OTel 計測・ポリシー（Cedar/OPA）、SBOM/セキュリティ監査

---

## 4. 手順（サンプル）

### 4.1 NL→BDD（テンプレ）
```gherkin
# features/authentication.feature
Feature: User Authentication
  In order to protect accounts
  As a registered user
  I want to sign in with valid credentials

  Scenario: Successful sign-in
    Given a registered user "alice" with password "P@ssw0rd!"
    When she signs in with the same credentials
    Then she is authenticated within 2 seconds
    And she receives a session token valid for 15 minutes
```

### 4.2 BDD→形式仕様（LTL 例：要旨）
```text
# LTL sketches (Alloy6 style or TLC operators相当の概念スケッチ)
G( signInRequest -> F[<=2s] authenticated )
G( authenticated -> F[<=15m] tokenValid )
G( invalidPassword -> X not authenticated )
```
> 実際には Alloy6 の時間演算子（`always/eventually/until` 等）や TLA+ のアクション/不変量で厳密化。

### 4.3 TLA+ スケルトン（抜粋）
```tla
---- MODULE Auth ----
EXTENDS Naturals, Sequences

VARIABLES users, sessions

Init == /\ users = {...}
        /\ sessions = << >>

SignIn(u,p) ==
  /\ u \in DOMAIN users
  /\ users[u].pass = p
  /\ sessions' = Append(sessions, [user |-> u, exp |-> Now + 15*60])

Next == \/ \E u,p : SignIn(u,p)
        \/ UNCHANGED << users, sessions >>

Authenticated(u) == \E s \in sessions : s.user = u /\ s.exp > Now

Inv == \A u : Authenticated(u) => ...

Spec == Init /\ [][Next]_<<users,sessions>>

THEOREM InvIsInvariant == Spec => []Inv
====
```
- TLC/Apalache による安全性・ライブネス検証。**反例トレース**を `tests/` に自動落とし込み。

### 4.4 適合性検査（Conformance）
- 実装の実行トレース（ログ/イベント）を **仕様の許容振る舞い**と照合。  
- 差分が出た場合は **最小反例**として**再現テスト化**し、TDD の Red として投入。

---

## 5. ツール選定（推奨）

| 目的 | 推奨ツール | ノート |
|---|---|---|
| モデル検査（安全性/ライブネス） | **TLA+ (TLC/Apalache)** | 分散/一貫性設計に強い。有界検査＋帰納法でスケール |
| 構造＋時間プロパティ | **Alloy 6** | **LTL/過去演算**を統合。軽量で反例が得やすい |
| 契約/プログラム検証 | **Dafny / cvc5 / Z3** | 事前/事後条件・不変量の自動検証 |
| 適合性検査 | 仕様→テスト生成＋**トレース適合** | MongoDB 事例に学ぶ継続的適合性 |
| BDD/ATDD | Cucumber(Gherkin), Playwright/Storybook/Vitest | 受入→E2E→ユニットの三層連携 |
| 生成支援 | LLM（候補生成）＋検証器（裁定） | “Generate→Verify→Repair” を全段で反復 |
| 運用 | OpenTelemetry, Cedar/OPA, SBOM | 仕様に基づく運用ゲート・ポリシー化 |

---

## 6. CI/品質ゲート（サンプル）

### 6.1 GitHub Actions（抜粋）
```yaml
name: verify
on:
  pull_request:
  push:
    branches: [ main ]

jobs:
  verify:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: actions/setup-node@v4
        with: { node-version: '20' }
      - run: pnpm install --frozen-lockfile
      - name: Unit & PBT
        run: pnpm run test:fast
      - name: Model Checking (TLA+)
        run: pnpm run verify:tla   # TLC/Apalache ラッパー
      - name: Alloy 6
        run: pnpm run verify:alloy # LTL/過去演算の性質
      - name: Conformance
        run: pnpm run verify:conf  # トレース適合検査
      - name: Coverage/A11y/Perf gates
        run: pnpm run quality:gate # ≥80%/≥95%/≥75% を既定
```

### 6.2 既定ゲート（リポジトリ整合）
- ✅ **Coverage ≥ 80%** / **A11y ≥ 95% (WCAG 2.1 AA)** / **Performance ≥ 75%**  
- ✅ TypeScript: `--strict` / 型エラー 0  
- ✅ ESLint: 重大エラー 0  
- ✅ 仕様準拠: 主要シナリオの **適合性検査パス** 必須

---

## 7. 使い方（最小ワークフロー）
```bash
# Install
npm install ae-framework

# Initialize (TDD)
ae-framework init my-project --tdd

# From Intent to Tests
ae-framework feature "User Authentication"
ae-framework generate:tests   # Red: 仕様からの失敗テスト生成（MBT/反例）
ae-framework generate:code    # Green: 実装候補（人間がレビュー）
ae-framework verify           # 仕様・品質ゲートの一括検証
ae-framework ui-scaffold --components  # Phase 6: UI 自動生成
```

---

## 8. リスクと対策

- **意味論ドリフト**（NL→BDD→形式仕様の段階的翻訳で意図がずれる）  
  → 各段に **承認チェック**、反例の**ナレッジ化**、**用語辞書**の一元管理。  
- **LLM のハルシネーション**  
  → 生成物は **検証器が最終裁定**。未証明の仕様/コードは採択しない。  
- **スケーラビリティ**  
  → 前段で **軽量手法（Alloy/シミュレーション）**、クリティカル部位に **重量級（ITP/完全証明）** を重点配分。

---

## 9. ロードマップ（短中期）

- **Phase 2.x（検証強化）**: CEGIS（反例誘導）で自動修復、**ランタイム適合**、**統合テストの自動オーケストレーション**。  
- **Spec→Code の接着**: 「仕様→テスト→適合」の三点支持を先行し、必要部位のみ **検証済み合成（VeCoGen型）** を適用。  
- **教育/運用**: テンプレート/クックブック整備、CI での**継続的モデル検査**、OTel による**運用検証**。

---

## 10. 参考情報（抜粋）

- **Systems Correctness at AWS**（形式/半形式手法のポートフォリオ、決定的シミュレーション等）  
  https://cacm.acm.org/practice/systems-correctness-practices-at-amazon-web-services/  
- **Conformance Checking（MongoDB）**（TLA+ 仕様と実装の継続的適合）  
  https://www.mongodb.com/company/blog/engineering/conformance-checking-at-mongodb-testing-our-code-matches-our-tla-specs  
- **Alloy 6**（LTL/過去演算の統合）  
  https://alloytools.org/alloy6.html  
- **cvc5 (TACAS 2022)**（産業級 SMT ソルバー）  
  https://link.springer.com/chapter/10.1007/978-3-030-99524-9_24  

> 上記は最低限の“リード”となる出典です。詳細な研究サーベイと設計指針の背景は、社内のサーベイ文書（別紙）をご参照ください。
