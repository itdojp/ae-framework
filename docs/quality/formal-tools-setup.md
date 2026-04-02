---
docRole: derived
canonicalSource:
- docs/quality/formal-runbook.md
- README.md
lastVerified: '2026-03-27'
---
# Formal Tools Setup

> 🌍 Language / 言語: English | 日本語

---

## English

This guide outlines local setup for formal verification tools used alongside AE-Framework. All steps are optional; CI remains label-gated.

## Supported tools
- TLA+ (TLC)
- Apalache (SMT/BMC plus inductive invariants)
- Alloy (Alloy Analyzer / Alloy 6 CLI)
- SMT solvers: Z3, cvc5
- Kani (Rust bounded model checking)
- SPIN (Promela model checking)
- CSP (CSPM checks via `cspx` or a configured backend)
- Lean4 (theorem proving / typechecking via lake)

## Quick checks
- Run `pnpm run tools:formal:check` to confirm which tools are available on the local machine.

## TLA+ (TLC)
- Install Java 11 or later. OpenJDK is recommended.
- Download `tla2tools.jar` from the TLA+ releases.
- Usage:
  - `java -cp /path/to/tla2tools.jar tlc2.TLC DomainSpec.tla`
- Optional environment variable:
  - `TLA_TOOLS_JAR=/path/to/tla2tools.jar`

## Apalache
- Install from a package manager or releases: `https://github.com/apalache-mc/apalache`
- Verify:
  - `apalache-mc version`
- Example:
  - `apalache-mc check --inv=Invariant spec/tla/DomainSpec.tla`

## Alloy
- Download an Alloy 6 jar, for example:
  - `curl -L -o alloy.jar https://github.com/AlloyTools/org.alloytools.alloy/releases/download/v6.2.0/org.alloytools.alloy.dist.jar`
- Verify:
  - `java -jar alloy.jar help`
- Run with the CLI exec mode:
  - `ALLOY_JAR=$PWD/alloy.jar ALLOY_RUN_CMD='java -jar $ALLOY_JAR exec -q -o - -f {file}' pnpm run verify:model`

## Z3 / cvc5
- Install from a package manager or releases.
- Verify:
  - `z3 --version`
  - `cvc5 --version`

## Kani
- Install from releases or cargo. Reference: `https://github.com/model-checking/kani`
- Example for Linux x86_64 using a prebuilt package:
  - `curl -L -o kani.tar.gz https://github.com/model-checking/kani/releases/download/kani-0.67.0/kani-0.67.0-x86_64-unknown-linux-gnu.tar.gz`
  - `tar -xzf kani.tar.gz`
  - `export PATH="$PWD/kani-0.67.0/bin:$PATH"`
- Verify:
  - `kani-driver --version`
  - `cargo kani --version` if the cargo plugin is installed

## SPIN
- Install from a package manager. Linux example:
  - `sudo apt-get update && sudo apt-get install -y spin gcc`
- Verify:
  - `spin -V`
  - `gcc --version`

## CSP
- CI is wired as non-blocking and always emits `csp-summary.json` by default.
- Recommended backend: `cspx` (OSS, Apache-2.0) for CI-first CSPM checks with JSON output.
  - Install with an immutable commit pin:
    - `cargo install --git https://github.com/itdojp/cspx --rev 8a67639ea4d3f715e27feb8cd728f46866a905db --locked cspx`
  - Verify:
    - `cspx --version`
    - `cspx typecheck --help | grep -- --summary-json`
  - Run:
    - `pnpm run verify:csp -- --file spec/csp/cspx-smoke.cspm --mode typecheck`
- Fallback backend order: `CSP_RUN_CMD` -> `cspx` -> `refines` (FDR) -> `cspmchecker`
  - `CSP_RUN_CMD` supports the `{file}` placeholder
  - Example:
    - `CSP_RUN_CMD='echo Running CSP tool on {file}' pnpm run verify:csp -- --file spec/csp/sample.cspm`

## Lean4 (elan + lake)
- Install `elan`:
  - `curl -L -sS https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y`
  - `export PATH="$HOME/.elan/bin:$PATH"`
- Verify:
  - `elan --version`
  - `lake --version`
- Build the project under `spec/lean/`:
  - `pnpm run verify:lean`

## Notes
- None of these tools is required for ordinary AE-Framework use. They extend the formal workflow when present.
- Use the `Formal Verify` workflow with the `run-formal` label or manual dispatch to exercise CI stubs. Engines are wired incrementally.

## Upstream references (`cspx`)
- Integration contract: `https://github.com/itdojp/cspx/blob/main/docs/integrations/ae-framework.md`
- Result JSON contract: `https://github.com/itdojp/cspx/blob/main/docs/result-json.md`
- Explainability guide: `https://github.com/itdojp/cspx/blob/main/docs/explainability.md`
- Validation report: `https://github.com/itdojp/cspx/blob/main/docs/validation-report.md`

---

## 日本語

このガイドは、AE-Framework と併用する形式検証ツールのローカルセットアップを整理したものです。すべて任意であり、CI は label-gated のままです。

## 対応ツール
- TLA+ (TLC)
- Apalache（SMT / 有界モデル検査と帰納的不変条件）
- Alloy（Alloy Analyzer / Alloy 6 CLI）
- SMT ソルバー: Z3, cvc5
- Kani（Rust の有界モデル検査）
- SPIN（Promela のモデル検査）
- CSP（`cspx` または構成済み backend による CSPM check）
- Lean4（lake による定理証明 / 型検査）

## 簡易確認
- `pnpm run tools:formal:check` を実行し、ローカル環境で利用可能なツールを確認する。

## TLA+ (TLC)
- Java 11 以上を導入する。OpenJDK を推奨。
- TLA+ releases から `tla2tools.jar` を取得する。
- 実行例:
  - `java -cp /path/to/tla2tools.jar tlc2.TLC DomainSpec.tla`
- 任意の環境変数:
  - `TLA_TOOLS_JAR=/path/to/tla2tools.jar`

## Apalache
- package manager または release から導入する: `https://github.com/apalache-mc/apalache`
- 確認:
  - `apalache-mc version`
- 実行例:
  - `apalache-mc check --inv=Invariant spec/tla/DomainSpec.tla`

## Alloy
- Alloy 6 jar を取得する。例:
  - `curl -L -o alloy.jar https://github.com/AlloyTools/org.alloytools.alloy/releases/download/v6.2.0/org.alloytools.alloy.dist.jar`
- 確認:
  - `java -jar alloy.jar help`
- CLI exec モードでの実行例:
  - `ALLOY_JAR=$PWD/alloy.jar ALLOY_RUN_CMD='java -jar $ALLOY_JAR exec -q -o - -f {file}' pnpm run verify:model`

## Z3 / cvc5
- package manager または release から導入する。
- 確認:
  - `z3 --version`
  - `cvc5 --version`

## Kani
- release または cargo から導入する。参考: `https://github.com/model-checking/kani`
- Linux x86_64 の prebuilt 例:
  - `curl -L -o kani.tar.gz https://github.com/model-checking/kani/releases/download/kani-0.67.0/kani-0.67.0-x86_64-unknown-linux-gnu.tar.gz`
  - `tar -xzf kani.tar.gz`
  - `export PATH="$PWD/kani-0.67.0/bin:$PATH"`
- 確認:
  - `kani-driver --version`
  - cargo plugin を導入している場合は `cargo kani --version`

## SPIN
- package manager で導入する。Linux の例:
  - `sudo apt-get update && sudo apt-get install -y spin gcc`
- 確認:
  - `spin -V`
  - `gcc --version`

## CSP
- CI は non-blocking 構成で、既定では常に `csp-summary.json` を出力する。
- 推奨 backend は `cspx`（OSS, Apache-2.0）。CI-first な CSPM check と JSON 出力に対応する。
  - immutable commit pin で導入:
    - `cargo install --git https://github.com/itdojp/cspx --rev 8a67639ea4d3f715e27feb8cd728f46866a905db --locked cspx`
  - 確認:
    - `cspx --version`
    - `cspx typecheck --help | grep -- --summary-json`
  - 実行:
    - `pnpm run verify:csp -- --file spec/csp/cspx-smoke.cspm --mode typecheck`
- fallback backend 順序: `CSP_RUN_CMD` -> `cspx` -> `refines` (FDR) -> `cspmchecker`
  - `CSP_RUN_CMD` は `{file}` placeholder を受け付ける
  - 例:
    - `CSP_RUN_CMD='echo Running CSP tool on {file}' pnpm run verify:csp -- --file spec/csp/sample.cspm`

## Lean4 (elan + lake)
- `elan` を導入する:
  - `curl -L -sS https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y`
  - `export PATH="$HOME/.elan/bin:$PATH"`
- 確認:
  - `elan --version`
  - `lake --version`
- `spec/lean/` 配下の project を build:
  - `pnpm run verify:lean`

## 備考
- これらのツールは通常の AE-Framework 利用では必須ではありません。導入済みの場合に、formal workflow の検証レーンを拡張します。
- CI 上の stub を動かすには、`Formal Verify` workflow を `run-formal` label か manual dispatch で実行します。各 engine は段階的に接続されます。

## 上流参照 (`cspx`)
- AE-Framework 連携契約: `https://github.com/itdojp/cspx/blob/main/docs/integrations/ae-framework.md`
- 結果 JSON 契約: `https://github.com/itdojp/cspx/blob/main/docs/result-json.md`
- 説明可能性ガイド: `https://github.com/itdojp/cspx/blob/main/docs/explainability.md`
- 検証レポート: `https://github.com/itdojp/cspx/blob/main/docs/validation-report.md`
