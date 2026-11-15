/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61R45Barrier
import InteractingSLE.Spec.Supplement.LPProbRetarget

/-!
# The stopped barrier after retargeting the first of two marks

For the word `(a,b; r,-r)`, retargeting at `a` gives the left word
`(-1, b/(a-b); κ-6,-r)`. Its outer cumulative weight is at least
`κ/2-2` when `r ≤ κ/2-4`. The announced local GB7a barrier therefore
excludes the entire ray to the left of the outer mark, through the stop.
This file proves the word calculation and this barrier; it does not assert
the stochastic transport through target separation.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology Finset
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.TwoMark

/-- The exact left positions in LP9's word when its target is the first mark. -/
theorem retargetXL_eq (xL : Fin 0 → ℝ) (a b : ℝ) :
    LP.retargetXL (j := 0) (m := 1) xL ![a, b] =
      ![-1, Sec7.targetChangeReal a b] := by
  rw [LP.retargetXL, Fin.append_left_nil _ _ rfl]
  funext i
  fin_cases i <;> simp [LP.retargetPos, LP.retargetIdx]

/-- Total original weight zero makes the old target's weight exactly `κ-6`. -/
theorem retargetRhoL_eq (ρL : Fin 0 → ℝ) (κ r : ℝ) :
    LP.retargetρL (j := 0) (m := 1) κ ρL ![r, -r] = ![κ - 6, -r] := by
  rw [LP.retargetρL, Fin.append_left_nil _ _ rfl]
  funext i
  fin_cases i <;> simp [Fin.sum_univ_two]

/-- The open interval to exclude becomes part of the outer left ray. -/
theorem targetChangeReal_lt_of_mem {a b y : ℝ} (ha : 0 < a) (hy : y ∈ Ioo a b) :
    Sec7.targetChangeReal a y < Sec7.targetChangeReal a b :=
  Sec7.strictMonoOn_targetChangeReal_Ioi ha hy.1 (hy.1.trans hy.2) hy.2

/-- The two transformed left marks have the required order. -/
theorem isOrderedForceWord_retarget {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (xR : Fin 0 → ℝ) :
    IsOrderedForceWord ![-1, Sec7.targetChangeReal a b] xR := by
  have hb := Sec7.targetChangeReal_lt_neg_one ha hab
  refine ⟨?_, ?_, (fun i => i.elim0), fun i => i.elim0⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
    exact hb.le
  · intro i
    fin_cases i
    · norm_num
    · change Sec7.targetChangeReal a b ≤ 0
      linarith only [hb]

/-- All left weights are counted at the outer mark. -/
theorem sum_retarget_left {a b : ℝ} (ha : 0 < a) (hab : a < b) (κ r : ℝ) :
    ∑ i ∈ univ.filter (fun i : Fin 2 =>
        (![-1, Sec7.targetChangeReal a b] : Fin 2 → ℝ) 1 ≤
          (![-1, Sec7.targetChangeReal a b] : Fin 2 → ℝ) i),
        (![κ - 6, -r] : Fin 2 → ℝ) i = κ - 6 - r := by
  have hb := (Sec7.targetChangeReal_lt_neg_one ha hab).le
  rw [Finset.sum_filter, Fin.sum_univ_two]
  norm_num [hb]
  ring

/-- GB7a's stopped interval barrier for the whole outer left ray of this word. -/
theorem ae_avoid_left_ray {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    {κ a b r : ℝ} (hκ : 0 < κ) (hκ4 : κ ≤ 4) (ha : 0 < a) (hab : a < b)
    (hr : r ≤ κ / 2 - 4)
    {xR ρR : Fin 0 → ℝ} {W B : ℝ≥0 → Ω → ℝ}
    {VL : Fin 2 → ℝ≥0 → Ω → ℝ} {VR : Fin 0 → ℝ≥0 → Ω → ℝ}
    {e : Ω → ℝ≥0∞} {T : ℕ → Ω → ℝ≥0} {η : Ω → ℝ≥0 → ℂ}
    (hE : Sec2.IsSLEEvolutionUpTo κ ![-1, Sec7.targetChangeReal a b] xR
      ![κ - 6, -r] ρR P 𝓕 W VL VR B e)
    (hW : ∀ ω, ContinuousOn (W · ω) {t | (t : ℝ≥0∞) < e ω})
    (hL : ∀ i ω, ContinuousOn (VL i · ω) {t | (t : ℝ≥0∞) < e ω})
    (hT : Coupling.IsAnnouncingSeq 𝓕 P e T)
    (hη : ∀ᵐ ω ∂P, IsGeneratingTrace (W · ω) (e ω) (η ω))
    (hinj : ∀ᵐ ω ∂P, InjOn (η ω) {t | (t : ℝ≥0∞) ≤ e ω})
    (hc : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, (s : ℝ≥0∞) = e ω →
      ContinuousOn (fun t => (W t ω, fun i => VL i t ω, fun j => VR j t ω)) (Iic s)) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ e ω →
      ∀ y < Sec7.targetChangeReal a b, η ω t ≠ (y : ℂ) := by
  have hsum : κ / 2 - 2 ≤ ∑ i ∈ univ.filter (fun i : Fin 2 =>
      (![-1, Sec7.targetChangeReal a b] : Fin 2 → ℝ) 1 ≤
        (![-1, Sec7.targetChangeReal a b] : Fin 2 → ℝ) i),
      (![κ - 6, -r] : Fin 2 → ℝ) i := by
    rw [sum_retarget_left ha hab]
    linarith only [hr]
  have hav : ∀ n : ℕ, ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ e ω →
      ∀ y ∈ Ioo (-(n : ℝ)) (Sec7.targetChangeReal a b), η ω t ≠ (y : ℂ) := by
    intro n
    exact Aux61R45.gb7aEvol_left_upTo hκ hκ4 (isOrderedForceWord_retarget ha hab xR)
      hE hW hL (fun i => i.elim0) hT hη hinj hc
      (k := 1) (a := -(n : ℝ)) (fun j hj =>
        (not_lt_of_ge ((isOrderedForceWord_retarget ha hab xR).1 (Fin.le_last j)) hj).elim) hsum
  filter_upwards [ae_all_iff.2 hav] with ω hω t ht y hy
  obtain ⟨n, hn⟩ := exists_nat_gt (-y)
  exact hω n t ht y ⟨by linarith only [hn], hy⟩

end InteractingSLE.Sec5.TwoMark
