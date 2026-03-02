# Contributing

This repository now uses a mixed model:

- Existing conjecture projects remain as git submodules.
- New conjecture projects should be added as regular in-repo directories under
  `<field>/<slug>/`.

## Principles

- Prefer a single source of truth over duplicated accounting.
- Do not add hard-coded conjecture counts in index pages.
- Keep Lean toolchain and Mathlib versions pinned consistently.

## Add A New In-Repo Lean Project (Preferred)

1. Create the project under `<field>/<slug>/`.
   - Pin Lean in `lean-toolchain` (currently `leanprover/lean4:v4.28.0`).
   - Pin Mathlib in `lakefile.toml` (currently `v4.28.0`).
   - Add `.gitignore` with at least `/.lake`.
   - Ensure `lake build` succeeds in that directory.
2. Follow the standard module layout.
   - Top-level `<Project>.lean` importing `Defs`, `Basic`, `SmallCases`, `Conjecture`.
   - Keep conjecture statement explicit and documented in `README.md`.
3. Update documentation in this repo.
   - Add the project row to `README.md` in the formalizations table.
   - If the conjecture is in the open index, update:
     - `open-problems/<field>.md`
     - `open-problems/README.md` alphabetical index
   - Keep counts out of index pages; field pages are the accounting source.
4. Validate before opening PR.
   - `git status --short`
   - `git -C <field>/<slug> lake build`

## Legacy Submodule Maintenance

Only use submodule workflow for existing linked projects:

- `.gitmodules` entries must use `git@github.com:...`.
- Keep submodule remotes on SSH.
- Use `git submodule sync -- <field>/<slug>` after URL changes.

## Review Checklist

- [ ] New in-repo project(s) include `lean-toolchain`, `lakefile.toml`, and `/.lake` ignore.
- [ ] `.gitmodules` uses SSH URLs for any edited legacy submodules.
- [ ] `README.md` formalizations table is updated for added/removed projects.
- [ ] Open-problem entries are updated in the relevant field page and alphabetical index.
- [ ] No duplicated numeric counts were introduced in index files.
- [ ] Builds pass for all modified Lean project directories.
- [ ] No build artifacts are staged (`.lake`, `build`, etc.).

## CI

CI runs automatically on pull requests (`.github/workflows/ci.yml`):

1. **hygiene** — validates SSH submodule URLs, checks for build artifacts
2. **jekyll** — builds the Jekyll site to catch rendering errors
3. **lean-build** — matrix build across configured Lean projects

All required jobs must pass before merge.

## References

When adding a new conjecture, add references in two places:

1. **Project README** — cite the original paper(s) and key surveys
2. **Centralized `references.md`** — add an entry under the appropriate field
   section with a link back to the project
