---
docRole: derived
canonicalSource:
- action.yml
- .github/actions/assurance-gate/action.yml
- docs/operate/ASSURANCE-GATE-ACTION-RELEASE.md
- docs/operate/publication-evidence.json
lastVerified: '2026-07-12'
owner: product-assurance
verificationCommand: pnpm -s exec vitest run tests/actions/assurance-gate-action.test.ts tests/unit/docs/publish-assets-quickstart.test.ts --reporter dot
---

# ae-framework Assurance Gate v1.0.2 release notes

Status: release-note source prepared. The GitHub Release, immutable tag, moving
major update, and external runtime evidence must follow the staged release
procedure below; this checked-in document does not claim that those owner
operations have already completed.

## Included patch

The root `itdojp/ae-framework` action and its compatibility subdirectory action
now run their filtered frozen install with explicit lockfile settings:

```text
pnpm install --frozen-lockfile --filter @ae-framework/core... --config.use-lockfile=true --config.package-lock=true
```

This preserves `pnpm-lock.yaml` as the authoritative lockfile when repository
npm configuration sets `package-lock=false`. Without the explicit overrides,
the hosted-runner path was reproduced failing before action execution with
`ERR_PNPM_LOCKFILE_CONFIG_MISMATCH`.

## Release refs

- Immutable release: `itdojp/ae-framework@v1.0.2` after candidate verification
  and tag creation.
- Normal major-line adoption: `itdojp/ae-framework@v1` only after immutable
  `v1.0.2` external smoke succeeds and the moving tag is updated to the same
  commit.
- Historical `v1.0.1` and `v1.0.0` tags remain immutable and are not rewritten.

The action ref remains the compatibility anchor for root action metadata,
profiles, policy, schemas, lockfile, and the `@ae-framework/core` source build.
This patch does not switch the action to an npm-published or prebuilt core.

## Staged verification evidence

Before creating the immutable tag and publishing this text as the initial
GitHub Release body, verify:

1. green required checks and full PR rollup for the reviewed release commit;
2. external consumer pass and block runs against that exact candidate commit
   SHA; and
3. the release owner has fixed that candidate SHA as the tag target rather than
   deriving it from a later `main` HEAD.

After the GitHub Release exists, complete the remaining staged operations:

1. confirm the immutable `v1.0.2` tag resolves to the candidate commit;
2. run external consumer pass and block cases against `@v1.0.2`;
3. move `v1` with lease protection only after immutable smoke succeeds;
4. confirm `v1` resolves to the same commit; and
5. run external consumer pass and block cases against `@v1`.

Record final run URLs and resolved commits in Issue #3651 and the reviewed
publication-evidence PR. The initial GitHub Release body intentionally describes
this staged status; it does not claim that post-release immutable/moving smoke
has completed before those public records exist.

Each runtime run must preserve `gate-result.json`, `assurance-summary.json`,
`policy-decision.json`, and `review-surface.md`. The block case uses
`fail-on-block=false` so the job succeeds while retaining `gateResult=block` and
the missing-evidence decision. Runtime smoke is compatibility evidence, not
approval, quality, safety, productivity, or adoption-effectiveness evidence.

## Publication boundary

This patch release does not by itself publish:

- the GitHub Marketplace listing;
- `@ae-framework/core` to npm; or
- a production adoption or external pilot outcome.

Keep `docs/operate/publication-evidence.json` Marketplace state `blocked` until
the listing URL and all required release-owner evidence exist. The final
evidence PR may record successful immutable and moving runtime smoke while the
listing blocker remains.

## Rollback

Do not rewrite or delete `v1.0.2` after publication to hide a failure. If the
post-move `@v1` smoke fails, stop new adoption and make an explicit
release-owner decision whether to return `v1` to its previous commit. Record
the rollback reason, public workflow run, and known limitation in the release
Issue and release note. Correct immutable-release defects with a subsequent
patch tag.
