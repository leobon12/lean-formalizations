import HigherDimLFPP.Perc.Defs

/-!
# Free sites: definitions and statement shapes (packet L3a1)

Source: Ding–Gwynne–Zhuang, arXiv:2310.03996v5 ([2]), §4 (the "duality" steps at TeX l. 1348,
1355–1357, 1444, 1520, 1878, 1898); planning audit `planning/audits/MA7-ref2-sections-4-6.md`,
gap list §3 (G1–G3) and Details (a) D-F0–D-F3, D-FS. The six definitions below are copied
**verbatim** (names, binders, bodies and docstrings) from the type-checked statement surface
`planning/audits/statements/MA7Statements.lean.txt` §A, with the namespace `MA7Scratch` replaced by
`HigherDimLQGMetric.DGZ`.

Lattice language (HigherDimLFPP `Perc`): sites `Zd d = Fin d → ℤ`, `LAdj` (`|x - y|₁ = 1`), `SAdj`
(`*`-adjacency, `|x - y|_∞ = 1`), `WithinInf r x y` (`|x - y|_∞ ≤ r`), `StepIn`, `ConnIn`,
`Ext R F` (sites joined to `(R + 1, …, R + 1)` by an L-path avoiding `F`), `IsClosedCluster O C`
(a maximal `*`-connected set of sites outside the set `O` of open sites).

* `SmallClusters O D` — every closed cluster is bounded with `ℓ^∞`-diameter `≤ D`;
* `FreeSite O x` — `x` is open and in the exterior of every closed cluster;
* `FreeSiteLemma d` (D-F1), `HoleLemma d` (D-F3), `FreeSurgery d` (D-FS(i)),
  `FreeToInfinity d` (D-FS(ii)) — the statement shapes proved in `DGZ/FreeSites.lean`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace HigherDimLQGMetric

namespace DGZ

open HigherDimLFPP HigherDimLFPP.Perc

variable {d : ℕ}

/-- every closed cluster (maximal `*`-connected set of sites outside `O`) is bounded and has
`ℓ^∞`-diameter at most `D` -/
def SmallClusters (O : Set (Zd d)) (D : ℕ) : Prop :=
  ∀ C, IsClosedCluster O C → (∃ R : ℤ, ∀ y ∈ C, WithinInf R y 0) ∧
    ∀ y ∈ C, ∀ y' ∈ C, WithinInf (D : ℤ) y y'

/-- `x` is a *free* site: open, and in the exterior of every (bounded) closed cluster -/
def FreeSite (O : Set (Zd d)) (x : Zd d) : Prop :=
  x ∈ O ∧ ∀ C, IsClosedCluster O C → ∀ R : ℤ, (∀ y ∈ C, WithinInf R y 0) → x ∈ Ext R C

/-- **(F1) free-site lemma** (MA7 D-F1): if all closed clusters are bounded with diameter `≤ D`,
every `*`-connected set of diameter `> D` contains a free site -/
def FreeSiteLemma (d : ℕ) : Prop :=
  ∀ (O : Set (Zd d)) (D : ℕ), SmallClusters O D → ∀ S : Set (Zd d), ConnIn S SAdj →
    (∃ x ∈ S, ∃ y ∈ S, ¬ WithinInf (D : ℤ) x y) → ∃ x ∈ S, FreeSite O x

/-- **(F3) hole lemma** (MA7 D-F3): every site is within `D + 1` of a free site -/
def HoleLemma (d : ℕ) : Prop :=
  ∀ (O : Set (Zd d)) (D : ℕ), SmallClusters O D → ∀ x : Zd d,
    ∃ y, WithinInf ((D : ℤ) + 1) y x ∧ FreeSite O y

/-- **free surgery** (MA7 D-FS; corollary of HigherDimLFPP `surgeryLemma`): two free sites are
joined by an open L-path staying within `D + 1` of any reference L-path between them -/
def FreeSurgery (d : ℕ) : Prop :=
  ∀ (O : Set (Zd d)) (D : ℕ), SmallClusters O D → ∀ (γ : List (Zd d)) (u v : Zd d),
    γ.IsChain LAdj → γ.head? = some u → γ.getLast? = some v → FreeSite O u → FreeSite O v →
    Relation.ReflTransGen (StepIn {y | y ∈ O ∧ ∃ x ∈ γ, WithinInf ((D : ℤ) + 1) y x} LAdj) u v

/-- a free site is joined to every far-away site by an open L-path (it lies in the unbounded
open cluster) -/
def FreeToInfinity (d : ℕ) : Prop :=
  ∀ (O : Set (Zd d)) (D : ℕ), SmallClusters O D → ∀ R : ℤ, (∀ y, y ∉ O → WithinInf R y 0) →
    ∀ u v : Zd d, FreeSite O u → ¬ WithinInf R v 0 →
      Relation.ReflTransGen (StepIn O LAdj) u v

end DGZ

end HigherDimLQGMetric
