---
title: "GitHub Repo Settings"
kind: architecture
tags:
  - aura
  - workflow
  - ci
---

# GitHub Repo Settings

Snapshot of **GitHub.com** configuration for [`nahharris/aura`](https://github.com/nahharris/aura) (not stored in git). Update this note when you change branch rules, checks, or org policy.

## Pull requests (repository)

| Setting | Value |
| --- | --- |
| **Allow auto-merge** | Enabled — PRs can use *Enable auto-merge* once required checks pass. |

UI: **Settings → General → Pull requests** (or repository **Settings** search for “auto-merge”).

## Default branch: `master` (branch protection)

Classic protection rule on **`master`**:

| Rule | Value |
| --- | --- |
| **Require a pull request before merging** | On — `required_approving_review_count` is **0** (no mandatory reviewers, but merges go through PRs, not direct pushes). |
| **Require status checks to pass before merging** | On, **strict** — branch must be up to date with the base before merge. |
| **Require branches to be up to date** | Implied by strict required checks. |
| **Status checks that are required** | See table below (names must match GitHub Actions job names from workflow `CI`). |
| **Do not allow bypassing the above settings** | On — **Enforce on administrators** (`enforce_admins`). |
| **Allow force pushes** | Off |
| **Allow deletions** | Off |

UI: **Settings → Branches → Branch protection rules → `master`**.

### Required GitHub Actions checks (workflow `CI`)

These job names are registered as required contexts (GitHub Actions app):

| Check name |
| --- |
| `fmt` |
| `docs` |
| `workspace (ubuntu-latest, true)` |
| `workspace (windows-latest, false)` |
| `llvm (ubuntu-latest)` |
| `llvm (windows-latest)` |

If `.github/workflows/ci.yml` **renames jobs** or changes the **matrix**, update the branch rule so required contexts still match; otherwise merges stay blocked with “Expected — Waiting for status to be reported”.

The **llvm** job caches only `toolchains/cache` (the LLVM tarball download), not the extracted `toolchains/llvm` tree, so the `toolchains/llvm/18` symlink is always recreated correctly on each runner.

### Submodule checkout in CI

The **CI** workflow checks out **git submodules** so Cargo `path` dependencies under `tool/` resolve. Submodule repositories maintain their **own** CI; Aura does not duplicate their gates beyond what this workspace already builds and tests. See `AGENTS.md` at the repository root (companion surfaces / submodule note) and comments in `.github/workflows/ci.yml`.

## Changing settings later

- **Web:** repository **Settings** as above.
- **CLI (authenticated):** e.g. `gh api repos/nahharris/aura/branches/master/protection` (GET) and `PUT` with a JSON body; `gh api repos/nahharris/aura -X PATCH -f allow_auto_merge=true` for the repo flag.

## Related

- [[Architecture/Build And Dev Workflow]]
- [[Architecture/Repo Map]]
- [[Subsystems/Xtask]]
