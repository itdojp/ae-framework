---
docRole: derived
canonicalSource:
- docs/ci/pr-automation.md
- docs/integrations/CLAUDE-CODE-TASK-TOOL-INTEGRATION.md
lastVerified: '2026-03-26'
---
# Claude Code自動実行ガイド

> 🌍 Language / 言語: English | 日本語

---

## English

> Complete guide for driving ae-framework from requirements through the default six-phase flow and UI delivery in Claude Code

### Overview

This guide documents how to drive ae-framework inside Claude Code so that a requirements document can move through the default six-phase automation flow with explicit quality thresholds, traceability checks, and handoff expectations. The objective is operational consistency: the prompts, expected outputs, and escalation rules should be explicit enough that different operators drive the same workflow in the same way.

### Audience

- Developers using Claude Code with ae-framework integration available in the current workspace.
- Operators who need repeatable prompts from requirements analysis through domain modeling and UI delivery.
- Reviewers who need explicit checkpoints for quality scores, traceability, and next-phase readiness.

### Prerequisites

- Claude Code can invoke ae-framework in the current workspace.
- A requirements file such as `requirements.md` already exists.
- The operator understands the Phase 1-6 flow and basic delivery terminology.

### Basic workflow instructions

#### 1. Project initialization

```text
Start a new project with ae-framework.
The project name is "EC Site Development" and the requirements document is `requirements.md`.
Execute the workflow incrementally from Phase 1.
```

Expected result:
- the project context is initialized
- Phase 1 inputs are recognized
- the first execution plan is proposed

#### 2. Requirements analysis (Phase 1: Intent Analysis)

```text
Analyze the contents of `requirements.md` and extract the requirements and intent.
Evaluate the document from the following perspectives:
- identify functional requirements
- extract non-functional requirements
- clarify the business requirements
- identify technical requirements
Also provide recommendations for the next phase.
```

Expected result:
- classified requirements with priorities
- identified stakeholders and business goals
- clarified scope and recommended next actions
- readiness signal for Phase 2

#### 3. Structure requirements (Phase 2: Natural Language Requirements)

```text
Structure the extracted requirements.
Please do the following:
- classify and prioritize the requirements
- identify business entities
- analyze the relationships between requirements
- propose clarifications for ambiguous requirements
Evaluate completeness and recommend the next steps.
```

Expected result:
- structured functional and non-functional requirements
- extracted business entities
- dependency map between requirements
- completeness score, with `75%+` as the initial reference target

#### 4. Create user stories (Phase 3: User Stories Creation)

```text
Create user stories from the structured requirements.
Use the following format:
- "As a [user role], I want [functionality], So that [benefit]"
- write acceptance criteria in Given-When-Then form
- estimate story points
- organize stories by epic
Also make dependencies explicit.
```

Expected result:
- INVEST-oriented user stories
- epics and dependency structure
- detailed acceptance criteria
- initial effort estimates

#### 5. Validate consistency (Phase 4: Validation)

```text
Validate the consistency of the artifacts produced so far.
Check the following:
- requirement-to-story correspondence
- traceability coverage
- overall consistency
- completeness
If there are problems, propose concrete fixes.
```

Expected result:
- traceability matrix
- consistency findings
- gap analysis with repair proposals
- quality score, with `90%+` as the target reference

#### 6. Design the domain model (Phase 5: Domain Modeling)

```text
Design the domain model based on Domain-Driven Design (DDD).
Define the following:
- core domain entities
- aggregates and aggregate roots
- bounded contexts
- domain services
- ubiquitous language
- business rules
```

Expected result:
- DDD-aligned domain model
- bounded contexts with clear responsibilities
- ubiquitous language dictionary
- architecture ready for implementation handoff

#### 7. Deliver UI/UX and frontend scaffolding (Phase 6: UI Generation)

```text
Use the Phase 5 outputs to generate the UI and frontend delivery artifacts.
Please do the following:
- generate the required UI components and pages
- summarize Storybook / E2E / accessibility expectations
- report missing inputs that block generation
- provide the files created and the next operator actions
```

Expected result:
- Phase 6 delivery artifacts and generated file list
- explicit blockers if required inputs are missing
- next-step guidance for review, testing, and implementation hardening

### Full automation patterns

#### Fully automated run

```text
Use ae-framework to run the workflow from the attached `requirements.md` through the default delivery flow.

Execution phases:
Phase 1: Requirements Analysis
Phase 2: Requirements Structuring
Phase 3: User Story Creation
Phase 4: Consistency Validation
Phase 5: Domain Modeling
Phase 6: UI / UX Delivery

Report each phase result in detail and provide recommendations for the next phase.
If any quality score is below 80%, include an improvement plan.
Produce a final summary report for the whole project.
```

Use this pattern for:
- early PoC work
- small-project bootstrap
- broad initial analysis before deeper review

#### Staged execution

```text
Run ae-framework Phase 2.
Use the Phase 1 result as input and perform requirements structuring and analysis.

After execution, confirm the following:
- completeness score (target: 80% or higher)
- whether ambiguity remains
- cautions for the next phase

If the result is acceptable, continue to Phase 3 automatically.
```

Use this pattern for:
- large projects that require explicit review at each gate
- training or onboarding situations
- cases where each phase needs approval before moving on

### Quality control instructions

#### Quality criteria

```text
When running ae-framework, apply the following quality criteria:

Quality criteria:
- completeness: 85% or higher
- consistency: 90% or higher
- traceability coverage: 95% or higher
- user story quality: compliant with the INVEST principle

If a criterion is not met, block progress and propose an improvement plan.
Warning-level issues may continue, but report the corrective action.
```

Operational metrics:
- Completeness: coverage of required artifacts.
- Consistency: alignment across phases.
- Traceability: end-to-end linkability from requirements to design.
- Validity: fit against business intent and constraints.

#### Proactive guidance

```text
During ae-framework execution, use the following guidance settings:

Guidance settings:
- critical issues: block progress (stop on error)
- medium issues: show warnings (continue allowed)
- minor issues: show suggestions (reference information)
- automatic intervention: enabled

Always provide concrete recommendations for quality improvement.
Include alternative options for problem resolution when relevant.
```

Intervention levels:
- `Block`: stop progress until the issue is addressed.
- `Warning`: continue, but report and recommend a fix.
- `Suggestion`: optional improvement guidance.
- `Info`: reference-only context.

### Advanced execution patterns

#### Custom configuration run

```text
Run ae-framework with the following custom project settings:

Project settings:
- project type: web application
- architecture pattern: microservices
- delivery model: agile / scrum
- tech stack: React + Node.js + PostgreSQL
- quality focus: security and performance
- deployment environment: AWS
- team size: 5-8 people

Use this configuration to execute Phase 2 through Phase 5.
Generate artifacts that fit the selected settings at each phase.
```

Typical configurable dimensions:
- project type (`Web`, `Mobile`, `Desktop`, `API`)
- architecture pattern (`Monolith`, `Microservices`, `Serverless`)
- delivery model (`Waterfall`, `Agile`, `DevOps`)
- technical constraints (language, framework, infrastructure)
- quality priorities (security, performance, availability)

#### Parallel execution guidance

```text
To improve throughput, execute phases in parallel where safe.

Parallel execution strategy:
- start user-story generation from requirement subsets that are already stable during Phase 2
- run partial validation after each phase completes
- begin domain modeling from the core domain first, then handle supporting domains later

However, keep the following dependencies strict:
- start Phase 2 only after Phase 1 completes
- move to the next phase only after the relevant quality gate passes
- keep critical-path work sequential

Report progress regularly and adjust if a bottleneck appears.
```

Advantages:
- shorter end-to-end runtime
- earlier defect discovery
- better utilization of parallelizable work

Cautions:
- keep dependency management explicit
- use validation gates to rejoin split flows
- re-check consistency between parallel outputs

#### Continuous improvement pattern

```text
Apply a continuous improvement cycle while ae-framework is running:

Improvement cycle:
1. run a short retrospective after each phase
2. measure and analyze quality metrics
3. identify process improvement points
4. apply the improvements in the next phase
5. measure the effect of the change

Primary improvement targets:
- clearer requirements
- better user-story quality
- more efficient validation
- higher-precision domain models

Shorten the feedback loop and maximize learning value.
```

### Reporting instructions

#### Detailed project report

```text
After the ae-framework run completes, produce a detailed report that includes:

## Project Execution Summary
1. Overall overview
   - project name and time span
   - executed phases and produced artifacts
   - quality score summary

2. Detailed result by phase
   - Phase 1: requirements analysis results (requirement count, categories, quality score)
   - Phase 2: structuring results (entity count, relationships, completeness)
   - Phase 3: user stories (story count, epic count, effort estimate)
   - Phase 4: validation results (traceability, consistency, gaps)
   - Phase 5: domain model (entities, bounded contexts, services)
   - Phase 6: UI delivery (generated artifacts, blockers, follow-up work)

3. Quality analysis
   - quality metrics list
   - comparison against benchmarks
   - identified improvement areas

4. Issues and solutions
   - identified issue list
   - solutions already applied
   - unresolved issues and response options

5. Recommended next steps
   - preparation for Phase 6 or its hardening pass when only Phase 1-5 were run
   - preparation for Phase 7 (Code Generation)
   - handoff notes for the implementation team

6. Risk analysis
   - technical risks and mitigations
   - project risks and mitigations
   - quality risks and mitigations

7. Success probability assessment
   - rationale for the estimated probability of success
   - success factors and blockers
   - recommended actions to improve the probability

Write the report in Markdown and include diagrams or tables where useful.
Use actual measured data when presenting graphs or tables.
```

The detailed report should be Markdown-based, evidence-backed, and explicit about both solved and unsolved risks.

#### Executive summary

```text
Create an executive summary for management:

Scope (1-2 A4 pages):
- project overview (understandable in 30 seconds)
- key outcomes with numeric evidence
- projected business impact
- ROI analysis
- key risks and mitigations
- next steps and timeline
- recommended decisions

Keep business value explicit and minimize low-level technical detail.
```

Keep the executive summary short, numeric, and decision-oriented.

### Effective prompting practices

#### Be explicit

Good example:

```text
Read `requirements.md` and run Phase 2 requirements structuring for the EC site project.
Set the target completeness score to 80% or higher.
Write the result to `requirements_structured.md`.
```

Bad example:

```text
Analyze the requirements.
```

Key points:
- specify file names and paths
- state the expected output format
- use numeric quality thresholds
- tell the tool where the output should go

#### Use a staged approach

Recommended pattern:
1. do not run every phase at once unless the scope is intentionally narrow
2. review each phase result before advancing on high-risk work
3. fix issues immediately when they affect downstream artifacts
4. do not bypass quality gates for convenience

Example instruction:

```text
Run Phase 2 and then pause.
Review the result and confirm that the quality score is 80% or higher before proceeding to Phase 3.
```

#### Optimize for quality

```text
Always confirm the following quality checkpoints:

Required checkpoints:
- complete requirement coverage
- user stories comply with the INVEST principle
- traceability is preserved
- stakeholder agreements are reflected

Recommended checkpoints:
- business value is explicit
- technical feasibility is confirmed
- major risks are listed
```

#### Handle errors explicitly

```text
If an error or warning occurs during execution:

1. classify the severity (Critical / High / Medium / Low)
2. analyze the root cause
3. provide one or more repair options
4. assess the impact of the repair
5. re-validate after the fix

Stop progress on Critical or High issues.
Medium or Low issues may continue, but they must be recorded.
```

### Troubleshooting

#### Common problems and fixes

##### 1. The Task Adapter does not trigger

Symptom:

```text
Analyze the requirements.
```

The request is too vague, so the ae-framework Task Adapter may not activate.

Fix:

```text
Run ae-framework Phase 1 Intent Analysis against `requirements.md`.
Extract and analyze the requirements and provide next-phase recommendations.
```

Improvements:
- specify the exact phase
- name the input file
- explicitly call ae-framework behavior

##### 2. Quality scores are below target

Symptom: completeness or consistency is below the required threshold.

Fix:

```text
The quality score is 70%. Improve it by doing the following:
1. identify and add missing requirements
2. clarify ambiguous wording
3. list stakeholder confirmation points
4. reorganize requirement dependencies

Run the quality evaluation again after the fixes.
```

##### 3. Proactive guidance is too aggressive

Symptom: warnings or blocks interrupt progress too often.

Fix:

```text
Adjust the guidance sensitivity:
- Critical: only project-failure risks
- High: only major quality degradation
- Medium: show as recommended improvements
- Low: hide

Keep the important quality requirements in place.
```

##### 4. Memory or performance problems

Symptom: large requirement sets run slowly or fail.

Fix:

```text
Run in large-project mode with:
- batch size: 50 requirements per pass
- parallelism: up to 2 workers
- memory limit: 500 MB
- timeout: 300 seconds

Split the requirements into multiple files when necessary.
```

### Related documents

- [ae-framework README](../../README.md)
- [Claude Code Task Tool Integration](../integrations/CLAUDE-CODE-TASK-TOOL-INTEGRATION.md)
- [Phase 2: Natural Language Requirements](../phases/PHASE-2-NATURAL-LANGUAGE-REQUIREMENTS.md)
- [Phase 3: User Stories Creation](../phases/PHASE-3-USER-STORIES-CREATION.md)
- [Phase 4: Validation](../phases/PHASE-4-VALIDATION.md)
- [Phase 5: Domain Modeling](../phases/PHASE-5-DOMAIN-MODELING.md)
- [CLI Commands Reference](../reference/CLI-COMMANDS-REFERENCE.md)
- [TDD Framework Architecture](../architecture/TDD-FRAMEWORK-ARCHITECTURE.md)

### Feedback

Use [GitHub Issues](https://github.com/itdojp/ae-framework/issues) for follow-up proposals or corrections.


## 日本語

> ae-frameworkを使って要求ドキュメントから実装まで可能な限り自動で実行するための完全ガイド

### 📋 概要

このガイドでは、Claude Code環境でae-frameworkを活用し、要求ドキュメントからドメインモデル設計まで **自動実行** するための具体的な指示方法を説明します。

#### 対象読者
- Claude Codeを使用する開発者
- ae-frameworkでの自動化を検討している方
- 効率的なソフトウェア開発プロセスを求める方

#### 前提条件
- Claude Code環境でae-frameworkが利用可能
- 要求ドキュメント（requirements.md等）が準備済み
- 基本的なソフトウェア開発知識

### 🚀 基本的なワークフロー指示

#### 1. プロジェクト初期化

```
ae-frameworkを使って新しいプロジェクトを開始します。
プロジェクト名は「ECサイト開発」で、要件ドキュメントは requirements.md です。
Phase 1から段階的に実行してください。
```

**期待される結果**: プロジェクト構造の初期化とPhase 1の準備

#### 2. 要件分析（Phase 1: Intent Analysis）

```
requirements.mdの内容を分析して、要件と意図を抽出してください。
以下の観点で分析してください：
- 機能要件の特定
- 非機能要件の抽出
- ビジネス要件の明確化
- 技術要件の識別
次のフェーズへの推奨事項も提示してください。
```

**期待される結果**:
- 要件の分類と優先順位付け
- ステークホルダーの特定
- プロジェクトスコープの明確化
- Phase 2への準備完了

#### 3. 要件構造化（Phase 2: Natural Language Requirements）

```
抽出された要件を構造化してください。
以下を実行してください：
- 要件の分類と優先順位付け
- ビジネスエンティティの特定
- 要件間の関係性の分析
- 不明確な要件の明確化提案
完全性を評価して、次のステップを推奨してください。
```

**期待される結果**:
- 機能要件・非機能要件の構造化
- ビジネスエンティティの抽出
- 要件間の依存関係マップ
- 完全性スコア（目標: 75%以上）

#### 4. ユーザーストーリー作成（Phase 3: User Stories Creation）

```
構造化された要件からユーザーストーリーを作成してください。
以下の形式で生成してください：
- "As a [user role], I want [functionality], So that [benefit]"
- 受入基準をGiven-When-Then形式で記述
- ストーリーポイントによる見積もり
- エピック単位での組織化
依存関係も明確にしてください。
```

**期待される結果**:
- INVEST原則準拠のユーザーストーリー
- エピック階層の構造化
- 受入基準の詳細定義
- 開発工数見積もり

#### 5. 整合性検証（Phase 4: Validation）

```
これまでのフェーズの成果物の整合性を検証してください。
以下をチェックしてください：
- 要件とユーザーストーリーの対応関係
- トレーサビリティの確保
- 一貫性の評価
- 完全性の確認
問題があれば修正提案をしてください。
```

**期待される結果**:
- トレーサビリティマトリックス
- 一貫性チェック結果
- ギャップ分析と修正提案
- 品質スコア（目標: 90%以上）

#### 6. ドメインモデル設計（Phase 5: Domain Modeling）

```
ドメイン駆動設計（DDD）に基づいてドメインモデルを設計してください。
以下を定義してください：
- コアドメインエンティティ
- 集約（Aggregate）と集約ルート
- 境界コンテキスト（Bounded Context）
- ドメインサービス
- ユビキタス言語
- ビジネスルール
```

**期待される結果**:
- DDD原則に準拠したドメインモデル
- 明確な境界コンテキスト定義
- ユビキタス言語辞書
- 実装準備完了のアーキテクチャ設計

### 🎯 一括自動実行パターン

#### 完全自動実行指示

```
ae-frameworkを使って、添付のrequirements.mdから実装まで完全自動で実行してください。

実行フェーズ：
Phase 1: 要件分析
Phase 2: 要件構造化  
Phase 3: ユーザーストーリー作成
Phase 4: 整合性検証
Phase 5: ドメインモデル設計

各フェーズの結果を詳細に報告し、次フェーズへの推奨事項を提示してください。
品質スコアが80%未満の場合は、改善提案を含めてください。
最終的にプロジェクト全体のサマリーレポートを作成してください。
```

**使用場面**: 
- 初期の概念実証（PoC）
- 小規模プロジェクトの迅速な立ち上げ
- 全体像把握のための俯瞰分析

#### 段階的実行指示

```
ae-frameworkのPhase 2を実行してください。
Phase 1の結果を基に、要件の構造化と分析を行ってください。

実行後は以下を確認してください：
- 完全性スコア（目標：80%以上）
- 曖昧性の有無
- 次フェーズでの注意点

完了したら自動的にPhase 3に進んでください。
```

**使用場面**:
- 大規模プロジェクトでの慎重な進行
- 各フェーズでの詳細レビューが必要な場合
- 学習目的での段階的理解

### 📊 品質管理指示

#### 品質基準指定

```
ae-frameworkを実行する際、以下の品質基準を適用してください：

品質基準:
- 完全性: 85%以上
- 一貫性: 90%以上  
- トレーサビリティカバレッジ: 95%以上
- ユーザーストーリー品質: INVEST原則準拠

基準を満たさない場合は進行をブロックし、改善案を提示してください。
警告レベルの問題は継続可能ですが、解決策を含めて報告してください。
```

**品質メトリクス**:
- **完全性**: 必要な成果物の網羅度
- **一貫性**: フェーズ間の整合性
- **トレーサビリティ**: 要件から設計までの追跡可能性
- **妥当性**: ビジネス要件との適合性

#### プロアクティブガイダンス設定

```
ae-framework実行中は以下のガイダンス設定を使用してください：

ガイダンス設定:
- 重要な問題: 進行ブロック（エラー停止）
- 中程度の問題: 警告表示（継続可能）
- 軽微な問題: 提案表示（参考情報）
- 自動介入: 有効

品質向上のための具体的な推奨事項を随時提示してください。
問題解決のための代替案も含めて提案してください。
```

**介入レベル**:
- **Block**: 進行停止、必須修正
- **Warning**: 警告表示、推奨修正  
- **Suggestion**: 提案表示、任意修正
- **Info**: 情報提供のみ

### 🔧 高度な実行パターン

#### カスタム設定実行

```
ae-frameworkをカスタム設定で実行してください：

プロジェクト設定:
- プロジェクトタイプ: Webアプリケーション
- アーキテクチャパターン: マイクロサービス
- 開発手法: アジャイル/スクラム
- 技術スタック: React + Node.js + PostgreSQL
- 品質重視領域: セキュリティとパフォーマンス
- デプロイ環境: AWS
- チーム規模: 5-8名

この設定に基づいてPhase 2-5を実行してください。
各フェーズで設定に適した成果物を生成してください。
```

**設定可能項目**:
- プロジェクトタイプ（Web, Mobile, Desktop, API等）
- アーキテクチャパターン（モノリス, マイクロサービス, サーバーレス等）
- 開発手法（ウォーターフォール, アジャイル, DevOps等）
- 技術制約（言語, フレームワーク, インフラ等）
- 品質要件（セキュリティ, パフォーマンス, 可用性等）

#### 並列処理指示

```
効率化のため、可能な範囲でフェーズの並列実行を行ってください：

並列実行戦略:
- Phase 2とPhase 3: 要件確定部分から段階的にユーザーストーリー作成開始
- Phase 4: 各フェーズ完了後に部分的検証を実行
- Phase 5: コアドメインから設計開始、サポートドメインは後続実行

ただし、以下の依存関係は必ず守ってください：
- Phase 1完了後にPhase 2開始
- 各フェーズの品質ゲート通過後に次フェーズ移行
- クリティカルパス上の作業は順次実行

進行状況を定期的に報告し、ボトルネックがあれば調整してください。
```

**並列実行の利点**:
- 全体実行時間の短縮
- 早期の問題発見と修正
- リソースの効率的活用

**注意点**:
- 依存関係の厳密な管理
- 品質ゲートでの統合確認
- 並列作業間の整合性チェック

#### 継続的改善パターン

```
ae-framework実行中に継続的改善を適用してください：

改善サイクル:
1. 各フェーズ完了時に振り返り実施
2. 品質メトリクスの測定と分析
3. プロセス改善点の特定
4. 次フェーズでの改善実装
5. 改善効果の測定

改善対象:
- 要件の明確性向上
- ユーザーストーリーの品質向上
- 検証プロセスの効率化
- ドメインモデルの精度向上

フィードバックループを短縮し、学習効果を最大化してください。
```

### 📈 結果レポート指示

#### 詳細レポート要求

```
ae-framework実行完了後、以下を含む詳細レポートを作成してください：

## プロジェクト実行サマリー
1. **全体概要**
   - プロジェクト名と期間
   - 実行フェーズと成果物
   - 品質スコアサマリー

2. **フェーズ別詳細結果**
   - Phase 1: 要件分析結果（要件数、分類、品質スコア）
   - Phase 2: 構造化結果（エンティティ数、関係性、完全性）
   - Phase 3: ユーザーストーリー（ストーリー数、エピック数、工数見積）
   - Phase 4: 検証結果（トレーサビリティ、一貫性、ギャップ）
   - Phase 5: ドメインモデル（エンティティ、境界コンテキスト、サービス）

3. **品質分析**
   - 品質メトリクス一覧
   - ベンチマークとの比較
   - 改善領域の特定

4. **課題と解決策**
   - 特定された課題一覧
   - 実施済み解決策
   - 未解決課題と対策案

5. **次ステップ推奨事項**
   - Phase 6 (テスト生成) への準備
   - Phase 7 (コード生成) への準備
   - 実装チームへの引き継ぎ事項

6. **リスク分析**
   - 技術リスクとその対策
   - プロジェクトリスクとその対策
   - 品質リスクとその対策

7. **成功確率評価**
   - プロジェクト成功確率の算出根拠
   - 成功要因と阻害要因
   - 成功確率向上のための推奨アクション

レポートはMarkdown形式で作成し、図表を含めてください。
グラフや表は実際のデータに基づいて作成してください。
```

#### エグゼクティブサマリー要求

```
経営層向けのエグゼクティブサマリーを作成してください：

内容（A4 1-2ページ）:
- プロジェクト概要（30秒で理解可能）
- 主要成果（数値ベース）
- ビジネスインパクト予測
- 投資対効果（ROI）分析
- 主要リスクと対策
- 次ステップとタイムライン
- 推奨意思決定事項

ビジネス価値を明確に示し、技術詳細は最小限にしてください。
```

### 💡 効果的な指示のコツ

#### 明確性の確保

**Good例**:
```
requirements.mdファイルを読み込んで、ECサイトプロジェクトの
Phase 2要件構造化を実行してください。
完全性スコア80%以上を目標とし、
結果をrequirements_structured.mdに出力してください。
```

**Bad例**:
```
要件を分析してください。
```

**ポイント**:
- 具体的なファイル名やパスを指定
- 期待する出力形式を明記
- 品質基準を数値で指定
- 出力先を明確化

#### 段階的アプローチ

**推奨パターン**:
1. 一度に全フェーズではなく、段階的に実行
2. 各フェーズの結果を確認してから次へ進行  
3. 問題発見時は即座に修正
4. 品質ゲートでの停止を恐れない

**段階的実行の指示例**:
```
Phase 2を実行後、一時停止してください。
結果を確認し、品質スコアが80%以上であることを確認してから
Phase 3への進行許可を出します。
```

#### 品質重視

**品質確保の指示例**:
```
以下の品質チェックポイントを必ず確認してください：

必須チェック項目:
□ 要件の網羅性（漏れなし）
□ ユーザーストーリーのINVEST原則準拠
□ トレーサビリティの確保
□ ステークホルダーの合意事項反映

推奨チェック項目:
□ ビジネス価値の明確化
□ 技術的実現可能性の確認
□ リスク要因の洗い出し
```

#### エラーハンドリング

**エラー対応指示例**:
```
実行中にエラーや警告が発生した場合：

1. エラーレベルの判定（Critical/High/Medium/Low）
2. 根本原因の分析
3. 修正案の提示（複数案推奨）
4. 修正実施の影響範囲評価
5. 修正後の再検証

Critical/Highレベルは進行停止し、
Medium/Lowレベルは継続可能ですが記録してください。
```

### 🔧 トラブルシューティング

#### よくある問題と解決策

##### 1. Task Adapterが呼び出されない

**症状**:
```
要件分析を実行してください
```
と指示しても、ae-frameworkのTask Adapterが動作しない

**解決策**:
```
ae-frameworkのPhase 1 Intent Analysisを実行してください。
requirements.mdファイルを対象として、
要件の抽出と分析を行ってください。
```

**改善ポイント**:
- 具体的なフェーズ名を指定
- 対象ファイルを明記
- ae-frameworkの機能を明示的に呼び出し

##### 2. 品質スコアが低い

**症状**: 完全性や一貫性スコアが目標値を下回る

**解決策**:
```
品質スコアが70%でした。以下を実行して改善してください：

1. 不足している要件の特定と追加
2. 曖昧な表現の明確化
3. ステークホルダーへの確認事項の整理
4. 要件間の依存関係の再整理

改善後、再度品質評価を実行してください。
```

##### 3. プロアクティブガイダンスが過度に介入

**症状**: 警告やブロックが頻繁に発生し、進行が妨げられる

**解決策**:
```
ガイダンス感度を調整してください：

- Critical: プロジェクト失敗リスクのみ
- High: 品質大幅劣化のみ  
- Medium: 推奨改善事項として表示
- Low: 非表示

ただし、重要な品質要求は維持してください。
```

##### 4. メモリ不足やパフォーマンス問題

**症状**: 大規模要件での処理が遅い、または失敗する

**解決策**:
```
大規模プロジェクトモードで実行してください：

設定:
- バッチサイズ: 50要件/回
- 並列度: 2並列まで
- メモリ制限: 500MB
- タイムアウト: 300秒

必要に応じて要件を複数ファイルに分割してください。
```

### 📚 関連ドキュメント

- [ae-framework README](../README.md) - プロジェクト概要
- [Claude Code Task Tool Integration](../integrations/CLAUDE-CODE-TASK-TOOL-INTEGRATION.md) - 技術統合詳細
- [Phase 2: Natural Language Requirements](../phases/PHASE-2-NATURAL-LANGUAGE-REQUIREMENTS.md)
- [Phase 3: User Stories Creation](../phases/PHASE-3-USER-STORIES-CREATION.md)
- [Phase 4: Validation](../phases/PHASE-4-VALIDATION.md)
- [Phase 5: Domain Modeling](../phases/PHASE-5-DOMAIN-MODELING.md)
- [CLI Commands Reference](../reference/CLI-COMMANDS-REFERENCE.md)
- [TDD Framework Architecture](../architecture/TDD-FRAMEWORK-ARCHITECTURE.md)

### 🤝 フィードバック

このガイドの改善提案やご質問は、[GitHub Issues](https://github.com/itdojp/ae-framework/issues)でお気軽にお知らせください。

---

**ae-framework Claude Code自動実行ガイド** - 効率的なソフトウェア開発の実現 🚀

*最終更新: 2025年8月*
