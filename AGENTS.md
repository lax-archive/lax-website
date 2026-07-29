# Repository guidance

This repository owns the Lax archive's website presentation: editorial
content, static assets, rendering code, tests, and deployment workflows.

Before changing it:

1. Read `README.md`.
2. Keep generated files out of git; `_site/` is build output.
3. Treat `lax-db` as read-only input. Never edit archive records here.
4. Run `npm run check` and a real database build before publishing changes.
5. Preserve deterministic output and the strict Content Security Policy.
