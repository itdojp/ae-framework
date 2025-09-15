# AE Framework Minimal Specification

> 🌍 Language / 言語: English | 日本語

This is a minimal, valid AE-Spec used to satisfy fail-fast validation in CI.

## Glossary

- **User**: An actor who uses the system

## Domain

### User
- **id** (uuid, required) - Unique identifier
- **email** (string, required) - Email address
- **createdAt** (date) - Created timestamp

## Invariants

- User email must be unique

## Use Cases

### Register User
- User submits email
- System validates uniqueness
- System creates account

## API

- POST /users - Register user
- GET /users/{id} - Get user

---

## 日本語（概要）

これは CI の早期失敗（fail‑fast）チェックを満たす、最小限の妥当な AE-Spec サンプルです。用語集、ドメイン、最小の不変条件、ユースケース、簡単な API を含みます。CI での仕様コンパイル/検証が通ることを確認するために使用します。
