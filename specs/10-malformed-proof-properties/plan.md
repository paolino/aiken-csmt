# Plan: issue #10

Class: changes behaviour (on-chain verifier). Topology: OWNER, one commit
owner and one persistent mute auditor (operator staffing 2026-10-24).

## Strategy

1. Properties first. A generator draws each proof field over its whole domain,
   biased to stay near honest proofs: start from an honest proof of the held
   key, of its neighbours, or of the tree with the key inserted, then replace
   any subset of fields with domain values. A uniform random proof never hits
   a root and would pass vacuously; the bias is what makes the property able
   to fail, and the planted relaxations prove it does.
2. Fix with explicit range checks, one per finding, each with its failing case
   kept as a unit test. The expected set, to be confirmed by the generator, not
   assumed: `root_jump` equals the key's leading bits; the steps consume the
   key path exactly to its start; `consumed >= 1`; every jump byte is 0 or 1;
   sibling hashes are 32 bytes. A check the generator does not need is not
   added.
3. Relaxation check in CI: one planted relaxation per range check, each
   required to make the property suite fail; the unmodified tree is the
   control and must pass.
4. Completeness through haskell-mts byte vectors over seeded random trees.
5. Measurement through the same vectors at 1, 10, 1 000, 100 000 keys.
6. Release.

## Slices (each well under two hours)

| slice | content | depends on |
|---|---|---|
| inclusion-soundness | properties for has, delete, update, pop, pop_max; fixes on the including path; failing cases kept | none |
| exclusion-soundness | properties for miss, insert, push_min, push_max; fixes on the excluding path; failing cases kept | inclusion-soundness |
| relaxation-check | planted relaxations run in `just ci`; `--max-success` fixed in `just test` | exclusion-soundness |
| honest-completeness | seeded random-tree vectors from haskell-mts; completeness properties | ruling on the haskell-mts route (plan review question 1) |
| cost-measurement | vectors at the four sizes; cost table before and after the checks in the PR body | honest-completeness |
| release | version bump in this PR; tag after merge | all |

The two soundness slices may also run against the random-tree vectors once
honest-completeness lands; until then they use the trees of the existing
haskell-mts vectors.

## Gate (frozen per slice, v1)

Every command runs in
`systemd-run --user --scope --unit=csmt-<what>-<n> -p MemoryMax=16G timeout 3600 ...`.

| row | acceptance | command | expected |
|---|---|---|---|
| format | formatting | `nix develop --quiet -c just format-check` | 0 |
| vectors | committed vectors match haskell-mts | `nix develop --quiet -c just vectors-check` | 0 |
| tests | unit, vector and property tests at the recorded case count | `nix develop --quiet -c just test` (CI change in this ticket: fixed `--max-success`) | 0 |
| relaxations | every planted relaxation is killed, control passes | `nix develop --quiet -c just relaxation-check` (CI change in this ticket, part of `just ci`) | 0 |
| root | everything hosted CI runs | `nix develop --quiet -c just ci`, once on the final candidate; hosted `ci.yml` on the pushed head | 0 |

Red run on record: the probe above (a711011) is the subject failing; the
inclusion-soundness RED commit must reproduce it through the `tests` row.

## Open questions for plan review

1. Completeness route. The haskell-mts vector emitter (`csmt-test-vectors`)
   has hand-picked trees only; the `mts` CLI emits binary proofs and no
   exclusion proofs. Options: (a) add a seeded random-tree and measurement
   section to `csmt-test-vectors` in haskell-mts (a pull request there) and
   bump the pin here; (b) a test-only reference trie in Aiken checked against
   the existing vectors (not haskell-mts for random trees, so it misses the
   point of the requirement). Recommendation: (a), done by the same commit
   owner in a haskell-mts worktree, merged by the epic owner before
   honest-completeness. Needs a ruling because it is a second repository.
2. Release. Recommendation: `aiken.toml` 0.0.1 -> 0.1.0 in this PR; the epic
   owner or this ticket owner pushes annotated tag `v0.1.0` on the merge
   commit (existing tag: v0.0.1). Needs who tags.
3. Scope beyond the issue's three functions: every public function that
   verifies a proof, and `has` for an absent key (the probe shows it broken).
   Recommendation: include; same folds, same fixes.
