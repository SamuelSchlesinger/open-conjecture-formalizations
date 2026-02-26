# Contributing

This repository is an index and submodule umbrella for Lean formalizations.
Each conjecture project is developed in its own repository and linked here.

## Principles

- Prefer a single source of truth over duplicated accounting.
- Do not add hard-coded conjecture counts in index pages.
- Use SSH submodule URLs to keep push workflows consistent.

## Add A New Lean Submodule

1. Prepare the standalone conjecture repo.
   - Pin Lean in `lean-toolchain` (currently `leanprover/lean4:v4.28.0`).
   - Pin Mathlib in `lakefile.toml` (currently `v4.28.0`).
   - Add `.gitignore` with at least `/.lake`.
   - Ensure `lake build` succeeds in that repo.
2. Add the submodule in this repo.
   - `git submodule add git@github.com:SamuelSchlesinger/<repo>.git <field>/<slug>`
   - `git submodule update --init --recursive <field>/<slug>`
3. Ensure SSH is configured everywhere.
   - `.gitmodules` entry must use `git@github.com:...`.
   - Run `git submodule sync -- <field>/<slug>`.
   - Run `git -C <field>/<slug> remote set-url origin git@github.com:SamuelSchlesinger/<repo>.git`.
4. Update documentation in this repo.
   - Add the project row to `README.md` in the formalizations table.
   - If the conjecture is in the open index, update:
     - `open-problems/<field>.md`
     - `open-problems/README.md` alphabetical index
   - Keep counts out of index pages; field pages are the accounting source.
5. Validate before opening PR.
   - `git submodule foreach --recursive 'git status --short'`
   - `git -C <field>/<slug> lake build`

## Review Checklist

- [ ] `.gitmodules` uses SSH URLs for all edited submodules.
- [ ] Edited submodule(s) have `.gitignore` including `/.lake`.
- [ ] `README.md` formalizations table is updated when adding/removing a submodule.
- [ ] Open-problem entries are updated in the relevant field page and alphabetical index.
- [ ] No duplicated numeric counts were introduced in index files.
- [ ] Builds pass for all modified Lean submodules.
- [ ] No build artifacts are staged (`.lake`, `build`, etc.).

## About Template Drift

YAML does not support native file imports, but GitHub Actions supports reusable
workflows (`workflow_call`). If CI centralization is desired, define one
reusable workflow in a canonical repo and have each submodule workflow call it
via `uses:`.
