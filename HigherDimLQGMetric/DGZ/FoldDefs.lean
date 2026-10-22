import HigherDimLQGMetric.DGZ.FreeSitesDefs

/-!
# Folding a lattice box: definitions and statement shapes (packet L3a2)

Source: Ding–Gwynne–Zhuang, arXiv:2310.03996v5 ([2]), Lemma 4.9, around half (TeX l. 1898 and its
footnote: an enclosing open cluster "inside the box" is used without proof); planning audit
`planning/audits/MA7-ref2-sections-4-6.md`, gap G3(a) and Details (a) D-BOX (folding and box
surgery). The five definitions below are copied **verbatim** (names, binders, bodies and
docstrings) from the type-checked statement surface
`planning/audits/statements/MA7Statements.lean.txt` §A, with the namespace `MA7Scratch` replaced by
`HigherDimLQGMetric.DGZ`.

* `latBox a b` — the lattice box `[a, b] = ∏ᵢ [aᵢ, bᵢ]`;
* `foldZ a b` — the folding of `ℤ` onto `[a, b]` by reflections at `a - 1/2` and `b + 1/2`
  (a triangle wave of period `2(b - a + 1)`), `foldBox a b` its coordinatewise version;
* `FoldSmall d` (D-BOX (i)) and `BoxSurgery d` (D-BOX (ii)) — the statement shapes proved in
  `DGZ/Fold.lean` (`foldSmall`, `boxSurgery`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace HigherDimLQGMetric

namespace DGZ

open HigherDimLFPP HigherDimLFPP.Perc

variable {d : ℕ}

/-- the lattice box `[a, b] = ∏ [aᵢ, bᵢ]` -/
def latBox (a b : Zd d) : Set (Zd d) := {x | ∀ i, a i ≤ x i ∧ x i ≤ b i}

/-- fold `ℤ` onto `[a, b]` by reflections at `a - 1/2` and `b + 1/2` (period `2(b - a + 1)`) -/
def foldZ (a b t : ℤ) : ℤ :=
  if (t - a) % (2 * (b - a + 1)) ≤ b - a then a + (t - a) % (2 * (b - a + 1))
  else a + (2 * (b - a + 1) - 1 - (t - a) % (2 * (b - a + 1)))

/-- the folding map `ℤ^d → [a, b]` (coordinatewise; 1-Lipschitz for `L`- and `*`-adjacency) -/
def foldBox (a b : Zd d) (x : Zd d) : Zd d := fun i => foldZ (a i) (b i) (x i)

/-- **folding keeps clusters small** (MA7 D-BOX (i)): if the closed clusters of the configuration
restricted to the box (sites outside declared open) have diameter `≤ D` and the box sides exceed
`2D + 2`, the folded configuration has bounded closed clusters of diameter `≤ 2D + 1` -/
def FoldSmall (d : ℕ) : Prop :=
  ∀ (O : Set (Zd d)) (a b : Zd d) (D : ℕ), (∀ i, 2 * (D : ℤ) + 2 < b i - a i) →
    SmallClusters (O ∪ (latBox a b)ᶜ) D → SmallClusters (foldBox a b ⁻¹' O) (2 * D + 1)

/-- **box surgery** (MA7 D-BOX (ii)): rerouting inside a lattice box -/
def BoxSurgery (d : ℕ) : Prop :=
  ∀ (O : Set (Zd d)) (a b : Zd d) (D : ℕ), (∀ i, 2 * (D : ℤ) + 2 < b i - a i) →
    SmallClusters (O ∪ (latBox a b)ᶜ) D →
    ∀ (γ : List (Zd d)) (u v : Zd d), γ.IsChain LAdj → (∀ x ∈ γ, x ∈ latBox a b) →
      γ.head? = some u → γ.getLast? = some v →
      FreeSite (foldBox a b ⁻¹' O) u → FreeSite (foldBox a b ⁻¹' O) v →
      Relation.ReflTransGen
        (StepIn {y | y ∈ O ∩ latBox a b ∧ ∃ x ∈ γ, WithinInf (2 * (D : ℤ) + 2) y x} LAdj) u v

end DGZ

end HigherDimLQGMetric
