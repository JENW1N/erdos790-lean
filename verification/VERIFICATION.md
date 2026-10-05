# Verification report: Erdős Problem 790 / JSP-000649

**Selected proof commit (A):** `44a5c97f66dd67cef224af0f51d04e0875e87202`
(this report was added in a later commit and describes commit A; no proof file changed).

**Date:** 2026-10-05. **Toolchain:** `leanprover/lean4:v4.33.0`; Mathlib `v4.33.0`
(`db584cd6d46c92f209a44c0f1c829460d327499d`); all dependency revisions pinned in
`lake-manifest.json`.

## Checks performed and results

| Check | Result |
| --- | --- |
| Clean checkout of commit A in a fresh directory; every dependency fetched independently at the manifest revision; `lake exe cache get`; `LAKE_NO_CACHE=1 lake build` | **passed** — `Build completed successfully (8713 jobs)`, all 7 project modules rebuilt from source |
| Source scan for `sorry`, `admit`, `axiom`, `native_decide`, `ofReduceBool`, `implemented_by`, `extern`, `debug.skipKernelTC` | **none** |
| `#print axioms` (file `Erdos790/Check.lean`) for `Erdos790.korsky`, `Erdos790.erdos_790`, `Erdos790.erdos_790_part_i`, `Erdos790.erdos_790_part_ii`, `Erdos790.erdos_790_exponent` | each depends only on `[propext, Classical.choice, Quot.sound]` |
| `leanchecker` kernel replay of every project module (`Erdos790.Defs`, `.Bisection`, `.Average`, `.Positive`, `.Main`, `.Sanity`) | **exit 0** for all |
| Official `skills/lean-verify/scripts/audit.py` (TheJustinSunPrize/awards) `preflight` / `prepare` / `run` with [`targets.json`](targets.json) | targets `korsky`, `part_i`, `part_ii`, `exponent`: `standard_axioms_only` ([`audit-result.json`](audit-result.json), [`axiom-logs.txt`](axiom-logs.txt)) |
| Statement bridge [`AuditBridge.lean`](AuditBridge.lean): the problem restated with **all definitions written inline** (no project definitions), proved by `Erdos790.erdos_790` | **passed** (`lake env lean verification/AuditBridge.lean`), axioms `[propext, Classical.choice, Quot.sound]` |
| Non-vacuity checks (`Erdos790/Sanity.lean`): `{1,2,3}` and `{-1,0,1}` are not sum-free, `{1,2,4}` and `{-1,1}` are sum-free, `l n ≤ n` | **passed** |

The `audit.py` bridge target is reported as `incomplete` only because `AuditBridge.lean` is
not a Lake library module (`unknown module AuditBridge`); it was checked directly with
`lake env lean` as recorded above.

## Statement correspondence

Original problem (erdosproblems.com/790, from [Er65, p.188], [Er73, p.130]): *Let `l(n)` be
maximal such that if `A ⊂ ℤ` with `|A| = n` then there exists a sum-free `B ⊆ A` with
`|B| ≥ l(n)` — that is, there are no solutions to `a₁ = a₂ + ⋯ + aᵣ` with `aᵢ ∈ B` all distinct.
Estimate `l(n)`. In particular, is it true that `l(n) n^{-1/2} → ∞`? Is it true that
`l(n) < n^{1-c}` for some `c > 0`?*

* **Sum-free.** `IsSumFree B := ∀ b ∈ B, ∀ S ⊆ B.erase b, 2 ≤ S.card → ∑ x ∈ S, x ≠ b`.
  A solution of `a₁ = a₂ + ⋯ + aᵣ` with distinct entries is exactly an element `b = a₁` and a
  set `S = {a₂, …, aᵣ}` of other elements with `∑ S = b`; `r = 2` (one summand) is impossible
  for distinct entries, so requiring `|S| ≥ 2` loses nothing.
* **`l(n)`.** `l n := sSup {m | ∀ A : Finset ℤ, A.card = n → ∃ B ⊆ A, IsSumFree B ∧ m ≤ B.card}`.
  The set is nonempty (`0`) and bounded by `n`, so the supremum is a maximum (`l_spec`,
  `le_l`, `l_le`): this is literally "maximal such that …". Arbitrary integers (including `0`
  and negatives) are allowed, as in the problem.
* **Question 1** (`erdos_790_part_i`): `Tendsto (fun n => (l n : ℝ) / √n) atTop atTop` — **yes**.
* **Question 2** (`erdos_790_part_ii`):
  `¬ ∃ c > 0, ∀ᶠ n in atTop, (l n : ℝ) < n ^ (1 - c)` — **no** (the strongest reading:
  not even eventually; a fortiori not for all `n`).
* **Estimate** (`korsky`, `erdos_790_exponent`): `l n ≥ c n / (log n)²` for all `n ≥ 2`, and
  `log l(n) / log n → 1`, i.e. `l(n) = n^{1+o(1)}` (Choi–Komlós–Szemerédi conjecture).

## Trust scope

Trusted: the Lean 4 kernel (v4.33.0) and the official Mathlib build cache for Mathlib
`v4.33.0`. Project modules were rebuilt from source and replayed with `leanchecker`;
Mathlib itself was not re-replayed from scratch.
