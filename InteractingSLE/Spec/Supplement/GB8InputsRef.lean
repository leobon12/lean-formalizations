/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB8Proof
import InteractingSLE.Spec.Sec5.Aux22StripAe
import InteractingSLE.Spec.Sec4.ZeroMarks
import InteractingSLE.Spec.Sec4.RepulsionNoncollision

/-!
# Lemma GB8, input 1: the two-mark reference swallows its far-left mark

Packet PROVE-T14-TIP4. Specification supplement §8.8, proof of **Lemma GB8** (`source/spec/p481-528.md` L1023–L1027,
p. 523): "This two-mark reference has an almost surely finite first real endpoint strictly to the left of `a₋`: the
strip calculation in the proof of Proposition 5.9 applies directly. More explicitly, `Φ(z) = (1/π) Log((z − a₋)/(−a₋))`
sends its attracting left ray to the upper strip boundary. The upper height is `λ(1 − κ/2) ∈ (−λ, λ)`, while every
remaining lower partial sum is at least `c_κ`. The full-span case of Aux. 22 gives a finite upper-strip endpoint, hence
the claimed finite first swallow of `a₋`."

This file proves PROVE-T14-TIP2's named input `Supp8.GB8.ReferenceSwallowStatement` (driver form), for every universe:

1. drop the passive (zero-weight) marks (`IsIntegratedSLEEvolution.compEmb`): the reference is an evolution of the
   two-mark word `(x₋; κ − 4)`, `(x₊; κ/2 − 2)`, with the same driver and lifetime;
2. reflect (`IsIntegratedSLEEvolution.reflect`): the far-left mark becomes the last right mark;
3. Aux. 22 in the strip (`Sec5.Aux22Strip.ae_exists_stripEnd_of_integrated`, built on Zhan's strip endpoint theorem
   `Strip.stripEndpointStatement_le_four`): the strip word has no lower left marks, the end charge `τ₋ = κ − 4` and one
   lower right mark of weight `κ/2 − 2` (prefix condition `κ/2 − 2 ≥ κ/2 − 2`), and `q₊ = −2`, `q₋ = κ − 4`, so
   `|q₊ − q₋| = |2 − κ| < 2` for `0 < κ < 4`. Its conclusion: almost surely the life before the last right mark is a
   bounded interval `[0, S)`;
4. so if `ζ = ∞`, at time `S` the far-left mark has met the driver.

## Main results

* `sum_Iic_fin_one`, `hasStripPrefixSums_two`, `abs_charge_two_lt`: the strip-word conditions;
* `referenceSwallowStatement`: **`ReferenceSwallowStatement.{u}`**.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Finset
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Supp8

namespace GB8

/-! ### The strip-word conditions of the two-mark reference -/

theorem sum_Iic_fin_one (f : Fin 1 → ℝ) (j : Fin 1) : ∑ i ∈ Finset.Iic j, f i = f 0 := by
  have : Finset.Iic j = {0} := by
    ext i
    simp only [Finset.mem_Iic, Finset.mem_singleton]
    exact ⟨fun _ => Subsingleton.elim _ _, fun h => h ▸ (Subsingleton.elim j 0) ▸ le_rfl⟩
  rw [this, Finset.sum_singleton]

/-- The prefix condition of Zhan's strip theorem for the reflected two-mark reference: no lower left marks, one lower
right mark of weight `κ/2 − 2`. -/
theorem hasStripPrefixSums_two (κ : ℝ) (ρ : Fin (0 + 1) → ℝ) :
    Strip.HasStripPrefixSums κ (Fin.init ρ) (fun _ : Fin 1 => κ / 2 - 2) := by
  refine ⟨fun j => j.elim0, fun j => ?_⟩
  rw [sum_Iic_fin_one]

/-- The charge condition `|q₊ − q₋| < 2` for the reflected two-mark reference: `q₋ = κ − 4`, `q₊ = −2`. -/
theorem abs_charge_two_lt {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) :
    |Strip.chargePlus κ (Fin.init (fun _ : Fin (0 + 1) => κ - 4)) (fun _ : Fin 1 => κ / 2 - 2)
        ((fun _ : Fin (0 + 1) => κ - 4) (Fin.last 0)) -
      Strip.chargeMinus (Fin.init (fun _ : Fin (0 + 1) => κ - 4)) ((fun _ : Fin (0 + 1) => κ - 4) (Fin.last 0))| <
      2 := by
  simp only [Strip.chargePlus, Strip.chargeMinus, Strip.tauPlus, Finset.univ_eq_empty, Finset.sum_empty,
    Fin.sum_univ_one]
  rw [abs_lt]
  constructor <;> linarith

/-! ### The reference swallows its far-left mark -/

/-- **Input 1 of GB8: the two-mark reference swallows its far-left mark** (Aux. 22's full-span endpoint, driver form;
GB8 proof, p. 523). For `0 < κ < 4` and an ordered word with marks off the seed, all left weight `κ − 4` on the
outermost left mark and all right weight `κ/2 − 2` on the outermost right mark (the other marks passive), almost surely
the lifetime is finite or the outermost left mark meets the driver before it. -/
theorem referenceSwallowStatement : ReferenceSwallowStatement.{u} := by
  intro κ hκ hκ4 nL nR hnL hnR xL xR hF hL0 hR0 Ω mΩ P 𝓕 W VL VR B ζ hE
  set iL : Fin nL := ⟨nL - 1, Nat.sub_lt hnL one_pos⟩ with hiL
  set iR : Fin nR := ⟨nR - 1, Nat.sub_lt hnR one_pos⟩ with hiR
  have : IsProbabilityMeasure P := hE.1.isProbabilityMeasure'
  -- 1. drop the passive marks
  let eL : Fin 1 ↪o Fin nL := OrderEmbedding.ofStrictMono (fun _ => iL) (Subsingleton.strictMono _)
  let eR : Fin 1 ↪o Fin nR := OrderEmbedding.ofStrictMono (fun _ => iR) (Subsingleton.strictMono _)
  have hzL : ∀ i, i ∉ Set.range eL → refW nL (κ - 4) i = 0 := by
    intro i hi
    simp only [refW]
    split_ifs with h
    · exact absurd ⟨0, Fin.ext (by simp [eL, iL]; omega)⟩ hi
    · rfl
  have hzR : ∀ i, i ∉ Set.range eR → refW nR (κ / 2 - 2) i = 0 := by
    intro i hi
    simp only [refW]
    split_ifs with h
    · exact absurd ⟨0, Fin.ext (by simp [eR, iR]; omega)⟩ hi
    · rfl
  have hwL : ∀ j : Fin 1, refW nL (κ - 4) (eL j) = κ - 4 := by
    intro j
    show refW nL (κ - 4) iL = κ - 4
    simp only [refW, iL]
    exact ite_eq_left (by omega)
  have hwR : ∀ j : Fin 1, refW nR (κ / 2 - 2) (eR j) = κ / 2 - 2 := by
    intro j
    show refW nR (κ / 2 - 2) iR = κ / 2 - 2
    simp only [refW, iR]
    exact ite_eq_left (by omega)
  have hE1 := hE.compEmb eL eR hzL hzR
  simp only [hwL, hwR] at hE1
  -- 2. reflect
  have hE2 := hE1.reflect
  -- 3. Aux. 22 in the strip
  have hsub : Subsingleton (Fin (0 + 1)) := inferInstanceAs (Subsingleton (Fin 1))
  have h := Sec5.Aux22Strip.ae_exists_stripEnd_of_integrated (n := 1) (j := 0) (XR := -fun j => xL (eL j))
    (XL := -fun j => xR (eR j)) (ρR := fun _ => κ - 4) (ρL := fun _ => κ / 2 - 2) hκ hκ4.le hE2
    (by simp [eL, hL0 iL]) (Subsingleton.strictMono _) (fun k => k.elim0) (Subsingleton.strictAnti _)
    (fun i => by simp [eR, hR0 iR]) (hasStripPrefixSums_two κ _) (abs_charge_two_lt hκ hκ4)
  -- 4. at the end of the life the far-left mark has met the driver
  filter_upwards [h, hE.ae_isIntegratedSLEPath] with ω hω hp
  obtain ⟨S, -, -, -, -, hlife, -⟩ := hω
  by_cases hζ : ζ ω = ⊤
  · right
    have hnot : ¬ (((S : ℝ≥0∞) < ζ ω) ∧ ∀ r ≤ S, (-W) r ω < (fun i => -(fun j => VL (eL j)) i) (Fin.last 0) r ω) :=
      fun hS => lt_irrefl S ((hlife S).1 hS)
    rw [hζ] at hnot
    push Not at hnot
    obtain ⟨r, hrS, hr⟩ := hnot ENNReal.coe_lt_top
    have hrζ : (r : ℝ≥0∞) < ζ ω := by rw [hζ]; exact ENNReal.coe_lt_top
    refine ⟨r, hrζ, le_antisymm (hp.isForcePath.vL_le_w hrζ iL) ?_⟩
    simpa [eL] using hr
  · left
    exact hζ

end GB8

end Supp8

end InteractingSLE
