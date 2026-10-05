# Erdős Problem 790 (JSP-000649): complete Lean 4 formalization

**Problem** ([Erdős #790](https://www.erdosproblems.com/790); Justin Sun Prize catalog
[JSP-000649](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0601-0700.md#JSP-000649)).
Let `l(n)` be maximal such that every set `A ⊂ ℤ` with `|A| = n` contains a *sum-free* subset
`B` with `|B| ≥ l(n)`, where sum-free means there is no solution of `a₁ = a₂ + ⋯ + aᵣ` with the
`aᵢ ∈ B` pairwise distinct. Estimate `l(n)`. In particular:

1. Is it true that `l(n) n^{-1/2} → ∞`?
2. Is it true that `l(n) < n^{1-c}` for some `c > 0`?

(Erdős, *Extremal problems in number theory*, 1965, p. 188; *Problems and results on
combinatorial number theory*, 1973, p. 130.)

**Answer.** (1) **Yes**; (2) **No**. In fact `l(n) ≥ c n / (log n)²`, so `l(n) = n^{1+o(1)}`
(the conjecture of Choi, Komlós and Szemerédi).

## Mathematical solution and credit

The mathematical solution formalized here is due to **Samuel Korsky**,
*Large Sum-Free Subsets of Sets of Integers* (13 September 2026), Theorem 1, posted as a full
proof claim on [erdosproblems.com/forum/thread/790](https://www.erdosproblems.com/forum/thread/790/proof-claims)
([PDF](https://drive.google.com/file/d/1S77Jwk5i9naiKJ_IQTK5_4Vh-X4LUfCf/view)). Korsky credits
GPT Astra with the main idea (the bisection lists of Lemma 2) and completed and verified the
proof himself. The first question was already answered positively by Choi, Komlós and Szemerédi
(Trans. AMS 212 (1975)); Korsky's theorem answers both questions.

This repository contributes only the Lean formalization; no mathematical discovery is claimed.

## Lean formalization authors

Jensen Kohlmeyer ([JENW1N](https://github.com/JENW1N), repository owner) and Liam Kruer
([lkruer](https://github.com/lkruer)). The formalization was prepared with the assistance of
Claude (Anthropic).

## Formal statements

All in [`Erdos790/Main.lean`](Erdos790/Main.lean), with definitions in
[`Erdos790/Defs.lean`](Erdos790/Defs.lean):

```lean
def IsSumFree (B : Finset ℤ) : Prop :=
  ∀ b ∈ B, ∀ S ⊆ B.erase b, 2 ≤ S.card → ∑ x ∈ S, x ≠ b

def admissible (n : ℕ) : Set ℕ :=
  {m | ∀ A : Finset ℤ, A.card = n → ∃ B ⊆ A, IsSumFree B ∧ m ≤ B.card}

noncomputable def l (n : ℕ) : ℕ := sSup (admissible n)

theorem Erdos790.korsky : ∃ c > 0, ∀ n : ℕ, 2 ≤ n → c * n / Real.log n ^ 2 ≤ l n
theorem Erdos790.erdos_790_part_i :
    Tendsto (fun n : ℕ => (l n : ℝ) / Real.sqrt n) atTop atTop
theorem Erdos790.erdos_790_part_ii :
    ¬ ∃ c > (0 : ℝ), ∀ᶠ n : ℕ in atTop, (l n : ℝ) < (n : ℝ) ^ (1 - c)
theorem Erdos790.erdos_790_exponent :
    Tendsto (fun n : ℕ => Real.log (l n) / Real.log n) atTop (𝓝 1)
theorem Erdos790.erdos_790 : (part i) ∧ (part ii)
```

### Correspondence with the original problem

* `IsSumFree B` is literally "no `a₁ = a₂ + ⋯ + aᵣ` with distinct `aᵢ ∈ B`": an element `b`
  and a set `S` of at least two *other* elements of `B` (so `r ≥ 3`; `r = 2` would force
  `a₁ = a₂`, impossible for distinct elements) with `∑ S = b`.
* `l n = sSup (admissible n)` is exactly "maximal such that every `A ⊂ ℤ`, `|A| = n`, contains
  a sum-free `B ⊆ A` with `|B| ≥ l(n)`"; the supremum is attained (`l_spec`) and maximal
  (`le_l`), and `l n ≤ n` (`l_le`).
* Sets are arbitrary finite sets of integers (negative numbers and `0` allowed).
* Part (i) is the literal statement `l(n)/√n → ∞`; part (ii) is the negation of
  "`∃ c > 0`, `l(n) < n^{1-c}` for all large `n`"; `erdos_790_exponent` records the
  resulting estimate `l(n) = n^{1+o(1)}`.

## Proof outline (following Korsky)

| Paper | Lean |
| --- | --- |
| Lemma 2 (bisection lists) | `Bisection.lean`: `bisection` (integer dividing points) |
| dyadic intervals, forbidden sets `F(a)`, `|F(a)| = O(log² n)` | `Positive.lean`: `jf`, `card_window`, `hFK` |
| random choice of intervals, `E|B| ≥ n/(4K)` | `Average.lean`: `exists_good_selection` (exact Bernoulli-weighted average over subsets) |
| every selection is sum-free (two cases) | `Positive.lean`: `positive_case` |
| reduction to positive sets | `Main.lean`: `korsky_finset`, `IsSumFree.image_neg` |
| `K(n) = O(log² n)`, asymptotics | `Main.lean`: `Kbound_le`, `korsky`, `eventually_rpow_le_l` |

## Reproduction

```sh
lake exe cache get
lake build
lake env lean Erdos790/Check.lean   # prints the axioms of the main theorems
```

Lean `v4.33.0`, Mathlib `v4.33.0` (see `lean-toolchain`, `lake-manifest.json`).
No `sorry`, `admit`, `native_decide` or custom axioms; the main theorems depend only on
`propext`, `Classical.choice` and `Quot.sound`.
