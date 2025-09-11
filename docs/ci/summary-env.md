# PR Summary — Environment Variables

- ADAPTER_WARN_MAX — maximum allowed adapter warnings count (default 0)
- ADAPTER_ERROR_MAX — maximum allowed adapter errors count (default 0)
- SUMMARY_MODE — digest | detailed (usually set via label pr-summary:detailed)

Usage (in workflow step)
```yaml
env:
  ADAPTER_WARN_MAX: 0
  ADAPTER_ERROR_MAX: 0
  SUMMARY_MODE: ${{ steps.mode.outputs.mode }}
```
