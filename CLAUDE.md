# CLAUDE.md — Open Conjecture Formalizations

## Repository Structure

This is an umbrella repository containing:

- **Lean 4 submodules** — each conjecture formalization lives in its own repo
  under `<field>/<slug>/` (e.g. `number-theory/collatz/`)
- **Jekyll site** — GitHub Pages site with layout in `_layouts/`, styles in
  `assets/css/`, and content pages at the root and under `open-problems/`
- **Open-problems index** — curated tables of open conjectures organized by
  mathematical field in `open-problems/*.md`

### Key paths

| Path | Purpose |
|------|---------|
| `.gitmodules` | Submodule registry (SSH URLs) |
| `_config.yml` | Jekyll config; `exclude` list keeps Lean artifacts out of site |
| `_layouts/default.html` | Site layout with nav and sidebar |
| `open-problems/` | Field pages (number-theory, algebra, etc.) |
| `CONTRIBUTING.md` | Contributor workflow and review checklist |
| `references.md` | Centralized bibliography |

## Submodule Conventions

- **SSH URLs only** — `.gitmodules` entries must use `git@github.com:…`
- **Lean version** — pin `leanprover/lean4:v4.28.0` in `lean-toolchain`
- **Mathlib version** — pin `v4.28.0` in `lakefile.toml`
- **Lake TOML format** — use top-level `name` (not `[package]`); dependencies
  use `rev` (not `version = "git#..."`)
- **`.gitignore`** — every submodule must ignore `/.lake` at minimum

## Lean Coding Conventions

- `set_option autoImplicit false` in every Lean file
- Module names follow the pattern `<Project>.<Module>` (e.g. `Collatz.Defs`)
- No `sorry` in merged code — every `sorry` must be resolved before merge
- No `native_decide` on unbounded domains — only for finite, small computations
- No custom axioms beyond Lean's core (`Classical.choice`, `propext`,
  `Quot.sound`, function extensionality are fine)
- Mathlib-compatible style — follow Mathlib naming conventions and tactic style
- Prefer Mathlib API over hand-rolled definitions where available
- Keep individual files under ~300 lines; split logically
- Doc-comments should explain the mathematical idea so a mathematician can
  reconstruct a paper proof from the Lean source

## Workflow: Formalizing a Conjecture

### Phase 1: Statement
- Formalize the conjecture statement in Lean 4
- Verify it matches the canonical source (Wikipedia, original paper, etc.)
- Cross-reference with existing formalizations (Mathlib, google-deepmind/formal-conjectures) if available

### Phase 2: Known Territory
- Prove the "easy" cases that are well-known in the literature
- This builds infrastructure (helper lemmas, definitions) needed later
- Serves as a sanity check on the formalization

### Phase 3: Novel Attempt
- Identify the boundary of what's known
- Formalize the attack strategy as intermediate lemmas
- Attempt the proof, iterating on the mathematical ideas
- If stuck, consider: alternative parametrizations, reductions, computational search

### Phase 4: Assessment
- If something new is proved: clean up, document, prepare for review
- If stuck: document what was tried, what obstructions were hit, and either
  push further or move to a different problem

### Phase 5: Literature & References
1. **Cite sources in doc-comments** — use author names inline, matching
   the submodule's references. File-level headers use `Reference: URL`.
2. **Update submodule README** — document the result and its status
3. **Update centralized `references.md`** — add citations for new papers used
4. **Classify novelty** — is this a formalization of a known result, or
   potentially new? If uncertain, note what literature search was done.

### Quality Gate

Before marking any theorem as "done":
- [ ] No `sorry` anywhere in the file or its dependencies
- [ ] `lake build` succeeds with no warnings
- [ ] Doc-comments explain the mathematical content
- [ ] A human can follow the proof structure
- [ ] Sources are cited in doc-comments and references
- [ ] Result is classified (known formalization vs. potentially novel)

## Adding a New Conjecture

See `CONTRIBUTING.md` for the full workflow. In brief:

1. Create a standalone Lean repo with pinned toolchain and Mathlib
2. Add it as a submodule: `git submodule add git@github.com:SamuelSchlesinger/<repo>.git <field>/<slug>`
3. Update `README.md`, the relevant `open-problems/<field>.md`, and `references.md`
4. Ensure CI passes (hygiene + Jekyll + Lean build)

## Jekyll Site

- Uses the `default` layout in `_layouts/default.html`
- Plugin: `jekyll-relative-links` for `.md` cross-references
- Files listed in `_config.yml` `exclude` are not processed by Jekyll
- Add non-site files (like `CLAUDE.md`, `LICENSE`) to the exclude list

## CI

GitHub Actions workflow (`.github/workflows/ci.yml`) runs three jobs:

1. **hygiene** — validates submodule URLs are SSH, no build artifacts staged
2. **jekyll** — builds the Jekyll site to catch broken links/syntax
3. **lean-build** — matrix build across all submodules using `leanprover/lean-action@v1`
