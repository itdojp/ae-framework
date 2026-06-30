# Tasks: Reservation Approval

**Input**: Design documents from `/specs/001-reservation-approval/`
**Prerequisites**: plan.md, spec.md, contracts/

## Format: `[ID] [P?] [Story] Description`

## Phase 1: Setup (Shared Infrastructure)

- [ ] T001 Create reservation approval fixture directory and schema references
- [ ] T002 [P] Add bridge report validation command to local verification

## Phase 2: Foundational (Blocking Prerequisites)

- [ ] T003 Define approval event contract in contracts/reservation-api.openapi.yaml

## Phase 3: User Story 1 - Approve available reservation (Priority: P1)

- [ ] T004 [US1] Implement approval state transition for sufficient stock
- [ ] T005 [P] [US1] Add automated approval scenario test

## Phase 4: User Story 2 - Reject unavailable reservation (Priority: P2)

- [ ] T006 [US2] Implement rejection path for insufficient stock
- [ ] T007 [P] [US2] Add automated rejection scenario test

## Phase 5: Polish & Cross-Cutting Concerns

- [ ] T008 Update assurance evidence documentation and rollback notes
