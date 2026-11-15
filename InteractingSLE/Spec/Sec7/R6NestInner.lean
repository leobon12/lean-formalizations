/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R6NestCover

/-!
# R.6's inner pockets are R.7 configurations in the bounded sector

PROVE-R6-NESTED. Supplement p. 476: the inner pocket `U` of Lemma R.6 is bounded by `β_R` (instead of an outer right
arm) and `β_L` (instead of an outer left arm), "traversed by the same counterflow in the same field frame". Its seed
weights are `r_L' = min(r_L, d)`, `r_R' = min(r_R, d)` (`d = k/2 − 4`), in the retained sector of Aux. 131, and its
phase is zero by Aux. 122 since `d < k − 6`.

`IsR7OuterConfig.inner`: the **same** field, counterflow and frontiers, with the inner arms
`innerRight k r_L α_R β_R`, `innerLeft k r_R α_L β_L`, form an R.7 configuration for the weights
`(innerRight k r_L r_L d, innerLeft k r_R r_R d)`, with the boundary-value margins enlarged by the nonnegative
amounts `r7A k r_R − r7A k r_R'` and `r7B k r_L − r7B k r_L'` (the field's data are unchanged). So every landed R.7
result stated for arbitrary margins `c, c' ≥ 0` applies to the inner pockets. Note that the named R.7 inputs
(`OuterPhNext.R7OuterPhaseContRemaining`, …) fix the margins `(π χ, 0)`; for an outer right arm the inner margin
`c'` is positive, so those inputs do not apply to the inner pockets as stated.

Input: `Prop55HalfPlaneStatement` (R48-safe), which orders the inner arms of the mixed shapes.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open QuantumZipper (H chiC)
open LQGMetric (DistOn)
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Sec7.R6Nest

open WangWu R7Outer

section Weights

variable {k rL rR : ℝ}

/-- The inner right seed weight `min(r_L, d)` in the form of `innerRight`. -/
theorem innerRight_weight_le (k rL : ℝ) : innerRight k rL rL (k / 2 - 4) ≤ k / 2 - 4 := by
  by_cases hd : k / 2 - 4 < rL <;> simp only [innerRight, hd, ↓reduceIte, le_refl]
  exact not_lt.1 hd

theorem innerLeft_weight_le (k rR : ℝ) : innerLeft k rR rR (k / 2 - 4) ≤ k / 2 - 4 := by
  by_cases hd : k / 2 - 4 < rR <;> simp only [innerLeft, hd, ↓reduceIte, le_refl]
  exact not_lt.1 hd

theorem neg_two_lt_innerRight_weight (hk4 : 4 < k) (hL : -2 < rL) : -2 < innerRight k rL rL (k / 2 - 4) := by
  by_cases hd : k / 2 - 4 < rL <;> simp only [innerRight, hd, ↓reduceIte]
  · linarith
  · exact hL

theorem neg_two_lt_innerLeft_weight (hk4 : 4 < k) (hR : -2 < rR) : -2 < innerLeft k rR rR (k / 2 - 4) := by
  by_cases hd : k / 2 - 4 < rR <;> simp only [innerLeft, hd, ↓reduceIte]
  · linarith
  · exact hR

/-- **The inner weights are in Aux. 122's bounded sector**: `−2 < r' < k − 6`. -/
theorem innerRight_weight_lt (hk4 : 4 < k) : innerRight k rL rL (k / 2 - 4) < k - 6 :=
  lt_of_le_of_lt (innerRight_weight_le k rL) (by linarith)

theorem innerLeft_weight_lt (hk4 : 4 < k) : innerLeft k rR rR (k / 2 - 4) < k - 6 :=
  lt_of_le_of_lt (innerLeft_weight_le k rR) (by linarith)

/-- The right boundary value does not increase when the right arm is replaced by `β_R`. -/
theorem r7B_innerRight_le (hk4 : 4 < k) (rL : ℝ) : r7B k (innerRight k rL rL (k / 2 - 4)) ≤ r7B k rL := by
  by_cases hd : k / 2 - 4 < rL <;> simp only [innerRight, hd, ↓reduceIte, le_refl]
  have hθ : R7.thetaR k rL < -(π / 2) := (R7.d_lt_rL_iff hk4).1 hd
  have hθd : R7.thetaR k (k / 2 - 4) = -(π / 2) := (R7.rL_eq_d_iff hk4).1 rfl
  have hκ : 0 < 16 / k := R7.sixteen_div_pos (by linarith)
  have hχ := Sec4.chiC_pos hκ (R7.sixteen_div_lt_four hk4)
  simp only [r7B, r7ThetaLo, hθd, min_self, min_eq_left hθ.le]
  nlinarith

/-- The left boundary value does not increase when the left arm is replaced by `β_L`. -/
theorem r7A_innerLeft_le (hk4 : 4 < k) (rR : ℝ) : r7A k (innerLeft k rR rR (k / 2 - 4)) ≤ r7A k rR := by
  by_cases hd : k / 2 - 4 < rR <;> simp only [innerLeft, hd, ↓reduceIte, le_refl]
  have hθ : π / 2 < R7.thetaL k rR := (R7.d_lt_rR_iff hk4).1 hd
  have hθd : R7.thetaL k (k / 2 - 4) = π / 2 := (R7.rR_eq_d_iff hk4).1 rfl
  have hκ : 0 < 16 / k := R7.sixteen_div_pos (by linarith)
  have hχ := Sec4.chiC_pos hκ (R7.sixteen_div_lt_four hk4)
  simp only [r7A, r7ThetaHi, hθd, max_self, max_eq_left hθ.le]
  nlinarith

end Weights

section Config

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}

/-- **The inner R.7 configuration** (supplement p. 476): replacing each outer arm by its certified frontier gives an
R.7 configuration of the same field, counterflow and frontiers for the bounded-sector weights
`(innerRight k r_L r_L d, innerLeft k r_R r_R d)`, with the margins enlarged so that the field's data are unchanged. -/
theorem IsR7OuterConfig.inner (h55 : Lemma71H.Prop55HalfPlaneStatement.{u}) {k rL rR c c' : ℝ} (hk4 : 4 < k)
    (hL : -2 < rL) (hR : -2 < rR) (hc : 0 ≤ c) (hc' : 0 ≤ c') [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    {αR βR βL αL : Ω → ℝ≥0 → ℂ} {ζαR ζβR ζβL ζαL : Ω → ℝ≥0∞}
    (hcfg : IsR7OuterConfig k rL rR c c' P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL) :
    IsR7OuterConfig k (innerRight k rL rL (k / 2 - 4)) (innerLeft k rR rR (k / 2 - 4))
      (c + (r7A k rR - r7A k (innerLeft k rR rR (k / 2 - 4))))
      (c' + (r7B k rL - r7B k (innerRight k rL rL (k / 2 - 4)))) P h W' ζ'
      (innerRight k rL αR βR) βR βL (innerLeft k rR αL βL)
      (innerRight k rL ζαR ζβR) ζβR ζβL (innerLeft k rR ζαL ζβL) := by
  have he : prop74Data (r7A k (innerLeft k rR rR (k / 2 - 4)) + (c + (r7A k rR - r7A k
      (innerLeft k rR rR (k / 2 - 4))))) (r7B k (innerRight k rL rL (k / 2 - 4)) + (c' + (r7B k rL - r7B k
      (innerRight k rL rL (k / 2 - 4))))) = prop74Data (r7A k rR + c) (r7B k rL + c') := by
    congr 1 <;> ring
  have hRβL : ∀ᵐ ω ∂P, range (βL ω) ⊆ closedLeftSide (αR ω) :=
    ae_order_r7 h55 hk4 hc hc' (R7.thetaR_lt_pi_div_two hk4 hL) (thetaR_mem_r7 rR hk4 hL)
      (pi_div_two_mem_r7 k rL rR) hcfg.gff hcfg.flow_αR hcfg.flow_βL
  have hβRL : ∀ᵐ ω ∂P, range (αL ω) ⊆ closedLeftSide (βR ω) :=
    ae_order_r7 h55 hk4 hc hc' (R7.neg_pi_div_two_lt_thetaL hk4 hR) (neg_pi_div_two_mem_r7 k rL rR)
      (thetaL_mem_r7 rL hk4 hR) hcfg.gff hcfg.flow_βR hcfg.flow_αL
  obtain ⟨hgff, hcf, hfαR, hfβR, hfβL, hfαL, hborel, hreg, hord, hav⟩ := hcfg
  rw [← he] at hgff hfαR hfβR hfβL hfαL
  obtain ⟨ΦαR, ΦβR, ΦβL, ΦαL, hΦαR, hΦβR, hΦβL, hΦαL, hΦ⟩ := hborel
  have hθRd : R7.thetaR k (k / 2 - 4) = -(π / 2) := (R7.rL_eq_d_iff hk4).1 rfl
  have hθLd : R7.thetaL k (k / 2 - 4) = π / 2 := (R7.rR_eq_d_iff hk4).1 rfl
  by_cases hdL : k / 2 - 4 < rL <;> by_cases hdR : k / 2 - 4 < rR <;>
    simp only [innerRight, innerLeft, hdL, hdR, ↓reduceIte] at hgff hfαR hfβR hfβL hfαL ⊢
  · refine ⟨hgff, hcf, hθRd ▸ hfβR, hfβR, hfβL, hθLd ▸ hfβL,
      ⟨ΦβR, ΦβR, ΦβL, ΦβL, hΦβR, hΦβR, hΦβL, hΦβL, fun ω => ⟨(hΦ ω).2.1, (hΦ ω).2.1, (hΦ ω).2.2.1,
        (hΦ ω).2.2.1⟩⟩, ?_, ?_, hav⟩
    · filter_upwards [hreg] with ω hω
      exact ⟨hω.2.1, hω.2.1, hω.2.2.1, hω.2.2.1, hω.2.2.2.2.2.1, hω.2.2.2.2.2.1, hω.2.2.2.2.2.2.1,
        hω.2.2.2.2.2.2.1⟩
    · filter_upwards [hord] with ω hω
      refine ⟨hω.1, hω.1, fun h' => absurd (hθRd ▸ h') (lt_irrefl _), fun h' => absurd (hθLd ▸ h') (lt_irrefl _),
        fun h' => absurd (hθRd ▸ h') (lt_irrefl _), fun h' => absurd (hθLd ▸ h') (lt_irrefl _)⟩
  · have hθL : ¬ π / 2 < R7.thetaL k rR := fun h' => hdR ((R7.d_lt_rR_iff hk4).2 h')
    refine ⟨hgff, hcf, hθRd ▸ hfβR, hfβR, hfβL, hfαL,
      ⟨ΦβR, ΦβR, ΦβL, ΦαL, hΦβR, hΦβR, hΦβL, hΦαL, fun ω => ⟨(hΦ ω).2.1, (hΦ ω).2.1, (hΦ ω).2.2.1,
        (hΦ ω).2.2.2⟩⟩, ?_, ?_, hav⟩
    · filter_upwards [hreg] with ω hω
      exact ⟨hω.2.1, hω.2.1, hω.2.2.1, hω.2.2.2.1, hω.2.2.2.2.2.1, hω.2.2.2.2.2.1, hω.2.2.2.2.2.2.1,
        hω.2.2.2.2.2.2.2⟩
    · filter_upwards [hord, hβRL] with ω hω h2
      exact ⟨hω.1, h2, fun h' => absurd (hθRd ▸ h') (lt_irrefl _), fun h' => absurd h' hθL,
        fun h' => absurd (hθRd ▸ h') (lt_irrefl _), hω.2.2.2.2.2⟩
  · have hθR : ¬ R7.thetaR k rL < -(π / 2) := fun h' => hdL ((R7.d_lt_rL_iff hk4).2 h')
    refine ⟨hgff, hcf, hfαR, hfβR, hfβL, hθLd ▸ hfβL,
      ⟨ΦαR, ΦβR, ΦβL, ΦβL, hΦαR, hΦβR, hΦβL, hΦβL, fun ω => ⟨(hΦ ω).1, (hΦ ω).2.1, (hΦ ω).2.2.1,
        (hΦ ω).2.2.1⟩⟩, ?_, ?_, hav⟩
    · filter_upwards [hreg] with ω hω
      exact ⟨hω.1, hω.2.1, hω.2.2.1, hω.2.2.1, hω.2.2.2.2.1, hω.2.2.2.2.2.1, hω.2.2.2.2.2.2.1,
        hω.2.2.2.2.2.2.1⟩
    · filter_upwards [hord, hRβL] with ω hω h1
      exact ⟨hω.1, h1, fun h' => absurd h' hθR, fun h' => absurd (hθLd ▸ h') (lt_irrefl _),
        hω.2.2.2.2.1, fun h' => absurd (hθLd ▸ h') (lt_irrefl _)⟩
  · exact ⟨hgff, hcf, hfαR, hfβR, hfβL, hfαL, ⟨ΦαR, ΦβR, ΦβL, ΦαL, hΦαR, hΦβR, hΦβL, hΦαL, hΦ⟩, hreg, hord, hav⟩

end Config

end InteractingSLE.Sec7.R6Nest
