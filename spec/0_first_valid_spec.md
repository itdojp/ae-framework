# AE Framework Minimal Specification

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
