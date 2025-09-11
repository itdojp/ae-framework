# Playwright Trace Adapter Notes

- Use normalized JSON to summarize trace artifacts (e.g., count of traces, files produced).
- Upload raw trace zips separately for manual inspection.
- Keep parsing/inspection outside core; PR summary shows high-level stats only.
