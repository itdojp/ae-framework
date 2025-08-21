SHELL := /usr/bin/env bash
COMPOSE := podman compose

.PHONY: up down spec:lint formal:check test:all test:acceptance test:property \
        test:mbt test:mutation test:contract test:api-fuzz policy:test sbom verify:trace \
        test:docker test:docker:unit test:docker:integration test:docker:e2e test:docker:quality \
        test:docker:flake test:docker:clean test:env:build test:env:validate \
        test:docker:all test:docker:report test:docker:performance

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

# Docker-based standardized test execution
test:docker:all:
	$(COMPOSE) -f docker-compose.test.yml up --build --abort-on-container-exit
	$(COMPOSE) -f docker-compose.test.yml down -v

test:docker:unit:
	$(COMPOSE) -f docker-compose.test.yml up test-unit --build --abort-on-container-exit
	$(COMPOSE) -f docker-compose.test.yml down -v

test:docker:integration:
	$(COMPOSE) -f docker-compose.test.yml up test-integration --build --abort-on-container-exit
	$(COMPOSE) -f docker-compose.test.yml down -v

test:docker:e2e:
	$(COMPOSE) -f docker-compose.test.yml up test-e2e --build --abort-on-container-exit
	$(COMPOSE) -f docker-compose.test.yml down -v

test:docker:quality:
	$(COMPOSE) -f docker-compose.test.yml up test-quality --build --abort-on-container-exit
	$(COMPOSE) -f docker-compose.test.yml down -v

test:docker:flake:
	$(COMPOSE) -f docker-compose.test.yml up test-flake-detection --build --abort-on-container-exit
	$(COMPOSE) -f docker-compose.test.yml down -v

test:docker:performance:
	$(COMPOSE) -f docker-compose.test.yml up test-performance --build --abort-on-container-exit
	$(COMPOSE) -f docker-compose.test.yml down -v

test:docker:report:
	$(COMPOSE) -f docker-compose.test.yml up test-reporter --build
	$(COMPOSE) -f docker-compose.test.yml down -v

test:docker:clean:
	$(COMPOSE) -f docker-compose.test.yml down -v --remove-orphans
	docker volume prune -f
	docker system prune -f

test:env:build:
	docker build -f Dockerfile.test -t ae-framework:test .

test:env:validate:
	docker run --rm ae-framework:test node -e "console.log('Test environment validation successful')"