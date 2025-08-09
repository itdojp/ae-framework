SHELL := /usr/bin/env bash
COMPOSE := podman compose

.PHONY: up down spec:lint formal:check test:all test:acceptance test:property \
        test:mbt test:mutation test:contract test:api-fuzz policy:test sbom verify:trace

up:
	$(COMPOSE) up -d --build

down:
	$(COMPOSE) down -v

spec:lint:
	npx @stoplight/spectral lint specs/openapi/api.yaml
	npx gherkin-lint specs/bdd/features/*.feature
	@./scripts/verify/traceability.sh

formal:check:
	podman run --rm -v $$PWD/specs/formal/tla+:/work ghcr.io/apalache-mc/apalache:mcr \
	  check --init=Inventory.cfg Inventory.tla

test:acceptance:
	npx cucumber-js

test:property:
	npm run pbt

test:mbt:
	npm run mbt

test:mutation:
	npx stryker run

test:contract:
	npm run contract

test:api-fuzz:
	podman run --rm -v $$PWD/specs/openapi:/spec schemathesis/schemathesis:stable run /spec/api.yaml --base-url=http://localhost:3000

policy:test:
	opa test policy/opa -v

sbom:
	curl -sSfL https://raw.githubusercontent.com/anchore/syft/main/install.sh | sh -s -- -b . v1.0.0
	./syft packages dir:. -o cyclonedx-json > security/sbom/sbom.json

verify:trace:
	./scripts/verify/traceability.sh