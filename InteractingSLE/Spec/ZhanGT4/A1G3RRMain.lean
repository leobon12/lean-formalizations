/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1G3RRRow
import InteractingSLE.Spec.ZhanGT4.A1AsmG3

/-!
# Zhan's A.1 (G3): the row input `G3RectRow` is proved

Packet PROVE-A1-G3RECTROW. Source: Astra, *Follow-up proofs*, §A.1.3–A.1.4 (`ig1_followup_proofs.txt` L300–L407) and
follow-up 4 §2.5 (R71, R76, R80).

PROVE-A1-ASSEMBLE reduced A.1 (G3) to three named inputs (`a1DualCouplingG3SeedGStatement_of_rect`): the rows
`G3RectRow`, the measurability `G3RectMeas` and the law input (I2) `G3RectLaw`. This file proves the first one outright,
for every `κ`:

* **`g3RectRow`**: for every pair of regular G3 marginals (right-continuous filtrations, continuous Brownian paths at
  every sample, a `GoodSmallG3` small curve at every sample), every rectangle `m` of the segment family, every small
  sample `ω₁` and every own time `a ∈ [0, g3S₁ m ω₁]`, the row `t ↦ seedHeightField (g3Rec …) (ω₁, ·) a (t ∧ g3S₂ m)`
  is a martingale of the large filtration with continuous paths at every sample (`g3_row` on the rectangles of
  A1-COMMON's `g3_rect`; at `a = 0` the row is the constant `1`);
* **`a1DualCouplingG3SeedGStatement_of_meas_law`**: hence `G3RectMeas κ → G3RectLaw κ →
  A1DualCouplingG3SeedGStatement κ`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1G3RR

open QuantumZipper (H fwdMap fwdHull)
open A2X A1Marg A1SeedField A1EightSeed A1G3Calc A1Common A1Asm

/-- **The G3 row input `G3RectRow` holds for every `κ`.** -/
theorem g3RectRow (κ : ℝ) : G3RectRow κ := by
  intro hκ4 hκ8 y x hyx hx X Y mX mY hX hY P₁ hP₁ P₂ hP₂ 𝓖₁ 𝓖₂ h𝓖₁ h𝓖₂ W₂ VL₂ VR₂ B₂ ζ₂ W₁ VL₁ VR₁ B₁ ζ₁ h₂
    hB₂ h₁ hB₁ hg₁
  have hκ : 0 < κ := by linarith
  have hqlo : 0 < x - y := by linarith
  have hqlox : x - y < -y := by linarith
  have hne : (goodIdxG (-y) (x - y) ![x - y]).Nonempty :=
    goodIdxG_nonempty hqlo hqlox (fun m => by fin_cases m; simp; linarith) (fun m => by fin_cases m; simp; linarith)
  have hF := isEnclFamily_cofG hne
  obtain ⟨hU, hgood₁, hsep₁, hsepO, -, -, -, hgood₂, hS₂pos, hS₂ζ⟩ :=
    g3_rect hκ4 hκ8 hyx hx h₁.path hg₁ hB₁ h₂.path hB₂ hF
  have hs₂ : ∀ m, IsStoppingTime 𝓖₂ fun ω => (g3S₂ x y W₂ ζ₂ m ω : WithTop ℝ≥0) := fun m =>
    isStoppingTime_rect₂ (fun ω => (h₂.path ω).2.2.2.1) h₂.evol.2.1 (fun m => (hF.pp m).hull₂)
      (cofGN (-y) (x - y) ![x - y]) (-y) m
  have hK₂ : ∀ m ω, fwdHull (Strip.extPath (W₂ · ω)) (g3S₂ x y W₂ ζ₂ m ω) ⊆
      transl (-(-y)) (cofGH₂ (-y) (x - y) ![x - y] m) := fun m ω => by
    have he : g3S₂ x y W₂ ζ₂ m ω = lifeExit (W₂ · ω) (ζ₂ ω) (transl (-(-y)) (cofGH₂ (-y) (x - y) ![x - y] m))
        (cofGN (-y) (x - y) ![x - y] m) := by
      rw [g3S₂, lifeExit_add_const, ← transl_neg_eq_preimage]
    rw [he]
    exact fwdHull_lifeExit_subset (h₂.path ω).2.2.2.1 (h₂.path ω).1 (hF.hull₂ m) (by rw [← he]; exact hS₂ζ m ω)
  have hrow : ∀ m (ω₁ : X) (a : ℝ), 0 < a → a ≤ g3S₁ x y W₁ ζ₁ m ω₁ →
      Martingale (fun (t : ℝ≥0) ω₂ => seedHeightField (g3Rec κ (-y) W₁ VL₁ VR₁ W₂ (g3S₁ x y W₁ ζ₁) m)
        (ω₁, ω₂) a (min (t : ℝ) (g3S₂ x y W₂ ζ₂ m ω₂))) 𝓖₂ P₂ ∧
      ∀ ω₂, Continuous fun t : ℝ≥0 => seedHeightField (g3Rec κ (-y) W₁ VL₁ VR₁ W₂ (g3S₁ x y W₁ ζ₁) m)
        (ω₁, ω₂) a (min (t : ℝ) (g3S₂ x y W₂ ζ₂ m ω₂)) := by
    intro m ω₁ a ha haS
    obtain ⟨U, -, hU₂⟩ := hU m
    exact g3_row (S₁ := g3S₁ x y W₁ ζ₁) (S₂ := g3S₂ x y W₂ ζ₂) hκ (isProtectedPairG_cofG hne m) (h₁.path ω₁)
      (by simp) rfl (by simpa using hqlo) (by simpa using qlo_le_cofGq hne m) (hgood₁ m ω₁) (hsep₁ ω₁)
      (hsepO ω₁) h₂ hB₂ (by simp) (by simp) (hs₂ m) hU₂ (hS₂ζ m) (hS₂pos m) (hgood₂ m) (hK₂ m) ⟨ha, haS⟩
  refine ⟨fun m ω₁ a ha haS => ?_, fun m ω₁ ω₂ a ha haS => ?_⟩
  · rcases ha.eq_or_lt with rfl | hpos
    · simp only [seedHeightField_zero_left]
      exact martingale_const _ _ _
    · exact (hrow m ω₁ a hpos haS).1
  · rcases ha.eq_or_lt with rfl | hpos
    · simp only [seedHeightField_zero_left]
      exact continuous_const
    · exact (hrow m ω₁ a hpos haS).2 ω₂

/-- **A.1 (G3), rectangle-wise mixed-mark form, from the measurability and the law input**: with the rows proved
(`g3RectRow`), `G3RectMeas κ → G3RectLaw κ → A1DualCouplingG3SeedGStatement κ`. -/
theorem a1DualCouplingG3SeedGStatement_of_meas_law {κ : ℝ} (hM : G3RectMeas κ) (hL : G3RectLaw κ) :
    A1DualCouplingG3SeedGStatement κ :=
  a1DualCouplingG3SeedGStatement_of_rect (g3RectRow κ) hM hL

end InteractingSLE.ZhanGT4.A1G3RR
