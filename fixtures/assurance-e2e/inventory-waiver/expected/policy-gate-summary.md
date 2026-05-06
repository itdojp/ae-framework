### Policy Gate
- PR: #3245
- result: PASS
- selected risk label: risk:low
- inferred risk: risk:low
- review topology: solo
- approvals: 0/0 (source: topology, policy: 1)
- required labels (by diff): enforce-assurance
- missing required labels: enforce-assurance
- assurance: waived (report-only)
  - claim evidence manifest: present
  - claims: pass=1, waived=1, report-only=1, block=0
  - waivers: active=1, expiringSoon=0, expired=0, orphan=0
    - id=change-package-v2:waiver:0:manual-fraud-review, claim=manual-fraud-review, status=active, owner=@team-risk, expires=2099-12-31, reason=Manual fraud review is active while automated model validation evidence is being collected.
- required checks:
  - verify-lite: success

