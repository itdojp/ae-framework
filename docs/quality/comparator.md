---
docRole: narrative
lastVerified: '2026-03-29'
---
# Comparator Utilities

> Language / 言語: English | 日本語

---

## English

This document describes the shared comparator utility used for threshold parsing, comparisons, and strictest-merge decisions.

### Expression format

```text
[operator][number][unit?]
```

- Operators: `>`, `>=`, `<`, `<=`, `==`, `!=`
- Default operator: `>=` when omitted
- Examples: `>=0.9`, `<=200ms`, `90%`, `==0`

### Supported units

#### Percent

- `%`, `percent`, `pct`
- Normalization stores the comparator as a percent value, for example `90% -> 90`
- When the comparator uses percent, ratio-style actual values are treated as percent values too, for example `0.85 -> 85`
- Unitless comparator expressions are not mixed with percent actual values, for example `compare('90%', '>=0.9')` raises a unit mismatch

#### Time

- `ms`, `s`, `m`, `h`
- Common aliases such as `sec`, `min`, and `hour` are accepted
- Values are normalized to milliseconds (`ms`)

#### Throughput

- `rps`, `req/s`, `requests/s`, `ops/s`
- `rpm`, `req/min`, `requests/min`, `ops/min`
- Values are normalized to requests per second (`rps`)

#### Unitless

- No unit specified
- Use this for ratios or counts when the unit is implicit

### Strictest merge rules

When two threshold expressions are merged into one stricter threshold:

- `>=` and `>` use the larger normalized value as stricter
- `<=` and `<` use the smaller normalized value as stricter
- If the normalized values are equal, strict operators (`>` or `<`) are stricter than non-strict operators (`>=` or `<=`)
- `==` is allowed only when it satisfies the other comparator
- `!=` is not supported for strictest selection
- Unit mismatches are rejected

### Usage guidelines

- Prefer explicit units such as `ms`, `%`, and `rps`
- For accuracy and coverage, choose either ratio style (`>=0.9`) or percent style (`>=90%`) and keep it consistent
- Avoid `==` for normalized floating-point values when a range check is acceptable
- Prefer millisecond thresholds for latency
- Prefer explicit `rps` or `rpm` thresholds for throughput
- Use `strictest` when merging policy thresholds with AE-IR or configuration hints

## 日本語

この文書は、閾値の構文解析、比較、より厳しい条件への統合に使う共有 comparator utility を説明します。

### 式の形式

```text
[operator][number][unit?]
```

- 演算子: `>`, `>=`, `<`, `<=`, `==`, `!=`
- 演算子を省略した場合の既定値は `>=`
- 例: `>=0.9`, `<=200ms`, `90%`, `==0`

### 対応単位

#### パーセント

- `%`, `percent`, `pct`
- 正規化後は percent 値として保持します。例: `90% -> 90`
- comparator が percent の場合、実測値が ratio 形式でも percent として扱います。例: `0.85 -> 85`
- unit なし comparator と percent 実測値の混在はサポートしません。例: `compare('90%', '>=0.9')` は unit mismatch になります

#### 時間

- `ms`, `s`, `m`, `h`
- `sec`, `min`, `hour` などの一般的な alias も受け付けます
- 正規化後は milliseconds (`ms`) に変換します

#### スループット

- `rps`, `req/s`, `requests/s`, `ops/s`
- `rpm`, `req/min`, `requests/min`, `ops/min`
- 正規化後は requests per second (`rps`) に変換します

#### 単位なし

- 単位を指定しない形式です
- unit が暗黙な ratio や count に使います

### strictest merge ルール

2 つの閾値式を 1 つのより厳しい閾値に統合する場合:

- `>=` と `>` は、正規化後の値が大きい方をより厳しい条件とみなします
- `<=` と `<` は、正規化後の値が小さい方をより厳しい条件とみなします
- 正規化後の値が同じ場合は、strict operator (`>` または `<`) の方が non-strict (`>=` または `<=`) より厳しい条件です
- `==` は、もう一方の comparator を満たす場合に限って利用できます
- `!=` は strictest selection ではサポートしません
- unit mismatch は拒否されます

### 利用ガイドライン

- `ms`, `%`, `rps` のような明示的な単位を優先してください
- accuracy や coverage では、ratio 形式 (`>=0.9`) か percent 形式 (`>=90%`) のどちらかに統一してください
- 正規化後の浮動小数点値に対しては、許容できるなら `==` より範囲チェック (`>=`, `<=`) を優先してください
- latency では millisecond ベースの閾値を優先してください
- throughput では `rps` または `rpm` を明示してください
- policy threshold と AE-IR / configuration hint を統合する場合は `strictest` を使ってください
