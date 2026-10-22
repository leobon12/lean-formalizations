import HigherDimLFPP.Exist.Discretize

/-!
# Discretization of continuous paths: statement shapes (packet L3a2)

Source: Ding–Gwynne–Zhuang, arXiv:2310.03996v5 ([2]), Lemma 5.12(1) (TeX l. 2641–2647, p. 52:
"each maximal segment of `P` in `B₂(0) \ 𝒰`", ill-defined when there are infinitely many) and the
discretizations of Lemmas 4.1, 4.9, 4.10; planning audit `planning/audits/MA7-ref2-sections-4-6.md`,
gap G13 and Details (a) D-DISC (closed and open boxes; generalizes HigherDimLFPP's
`exists_latticePath`).

* `DiscretizeLemma d` — copied **verbatim** (name, binders, body and docstring) from the
  type-checked statement surface `planning/audits/statements/MA7Statements.lean.txt` §B, with the
  namespace `MA7Scratch` replaced by `HigherDimLQGMetric.DGZ`: the closed variant;
* `DiscretizeLemmaOpen d` — the **open variant** of MA7 D-DISC: `DiscretizeLemma` with
  `cbox (latPt s x) s` replaced by `obox (latPt s x) s` in the three places of the conclusion.

Both are proved in `DGZ/Discretize.lean` (`discretize`, `discretizeOpen`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace HigherDimLQGMetric

namespace DGZ

open Set
open HigherDimLFPP HigherDimLFPP.Perc
open HigherDimLFPP.DGZ (latPt cbox obox)

variable {d : ℕ}

/-- **(DISC) lattice discretization** (MA7 D-DISC; generalizes HigherDimLFPP `exists_latticePath`):
for mesh `s > 0` and a continuous path `P` on `[0,1]` inside the open box `obox c ρ` whose faces lie
on lattice hyperplanes (`c` a lattice point, `ρ ∈ s ℤ`, `ρ ≥ s`), there is an L-path of lattice sites
`x` with `obox (latPt s x) s ⊆ obox c ρ`, each closed `s`-box meeting `P`, the first containing
`P 0` and the last containing `P 1` -/
def DiscretizeLemma (d : ℕ) : Prop :=
  ∀ {s : ℝ}, 0 < s → ∀ (c : Zd d) (N : ℕ), 1 ≤ N → ∀ {P : ℝ → Rd d},
    ContinuousOn P (Icc 0 1) → MapsTo P (Icc 0 1) (obox (latPt s c) (s * N)) →
    ∃ (l : List (Zd d)) (x₀ x₁ : Zd d), l.IsChain LAdj ∧ l.head? = some x₀ ∧
      l.getLast? = some x₁ ∧ P 0 ∈ cbox (latPt s x₀) s ∧ P 1 ∈ cbox (latPt s x₁) s ∧
      ∀ x ∈ l, obox (latPt s x) s ⊆ obox (latPt s c) (s * N) ∧
        ∃ t ∈ Icc (0 : ℝ) 1, P t ∈ cbox (latPt s x) s

/-- **(DISC) lattice discretization, open variant** (MA7 D-DISC, "the open variant replaces
`cbox (latPt s x) s` by `obox (latPt s x) s` in the conclusions"): for mesh `s > 0` and a continuous
path `P` on `[0,1]` inside the open box `obox (latPt s c) (s * N)` (`N ≥ 1`), there is an L-path of
lattice sites `x` with `obox (latPt s x) s ⊆ obox (latPt s c) (s * N)`, each open `s`-box meeting
`P`, the first containing `P 0` and the last containing `P 1` -/
def DiscretizeLemmaOpen (d : ℕ) : Prop :=
  ∀ {s : ℝ}, 0 < s → ∀ (c : Zd d) (N : ℕ), 1 ≤ N → ∀ {P : ℝ → Rd d},
    ContinuousOn P (Icc 0 1) → MapsTo P (Icc 0 1) (obox (latPt s c) (s * N)) →
    ∃ (l : List (Zd d)) (x₀ x₁ : Zd d), l.IsChain LAdj ∧ l.head? = some x₀ ∧
      l.getLast? = some x₁ ∧ P 0 ∈ obox (latPt s x₀) s ∧ P 1 ∈ obox (latPt s x₁) s ∧
      ∀ x ∈ l, obox (latPt s x) s ⊆ obox (latPt s c) (s * N) ∧
        ∃ t ∈ Icc (0 : ℝ) 1, P t ∈ obox (latPt s x) s

end DGZ

end HigherDimLQGMetric
