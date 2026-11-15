/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FCK2BdrySeed
import InteractingSLE.Spec.Supplement.RLCGJump

/-!
# Incident boundary bounds at every live real visit

The countable rational-interval argument follows `Supp8.GB7aFlowStatement.ae_forall`,
now using the landed continuation-threshold exclusion. Original jumps are
excluded by `RLC.jumpVisitStatement`; the seed uses positive-lifetime weights.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal
open QuantumZipper (chiC)

namespace InteractingSLE.Restart.FCPlumb
open PiecewiseConstantBoundaryData
universe u

/-- Simultaneous threshold exclusion off the jumps, strictly before lifetime. -/
theorem thresholdVisit_ae_forall {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps) {x θ : ℝ}
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps)
    {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞} (hη : IsFlowLine κ b jumps x θ P h η ζ) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → ∀ y : ℝ, y ∉ jumps →
      (x < y → Sec4.cumWeightRight κ (b y + θ * QuantumZipper.chiC κ) ≤ -2 → η ω t ≠ y) ∧
      (y < x → Sec4.cumWeightLeft κ (b y + θ * QuantumZipper.chiC κ) ≤ -2 → η ω t ≠ y) := by
  -- one event per rational interval
  have hq : ∀ q : ℚ × ℚ, ∀ᵐ ω ∂P,
      ((∀ z ∈ Ioo (q.1 : ℝ) q.2, z ∉ jumps) → x ≤ q.1 →
        Sec4.cumWeightRight κ (b ((q.1 + q.2 : ℝ) / 2) + θ * QuantumZipper.chiC κ) ≤ -2 →
        ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → ∀ y ∈ Ioo (q.1 : ℝ) q.2, η ω t ≠ y) ∧
      ((∀ z ∈ Ioo (q.1 : ℝ) q.2, z ∉ jumps) → (q.2 : ℝ) ≤ x →
        Sec4.cumWeightLeft κ (b ((q.1 + q.2 : ℝ) / 2) + θ * QuantumZipper.chiC κ) ≤ -2 →
        ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → ∀ y ∈ Ioo (q.1 : ℝ) q.2, η ω t ≠ y) := by
    intro q
    by_cases hJ : ∀ z ∈ Ioo (q.1 : ℝ) q.2, z ∉ jumps
    · by_cases hne : (q.1 : ℝ) < q.2
      · have hmid : ((q.1 + q.2 : ℝ) / 2) ∈ Ioo (q.1 : ℝ) q.2 := ⟨by linarith, by linarith⟩
        have hconst : ∀ y ∈ Ioo (q.1 : ℝ) q.2, y ∉ jumps → b y = b ((q.1 + q.2 : ℝ) / 2) :=
          fun y hy _ => Sec4.eq_of_mem_Ioo_of_isPiecewiseConstant hb
            (fun z hzJ hz => hJ z hz hzJ) hmid hy
        obtain ⟨hR, hL⟩ := RLC.thresholdVisitStatement κ hκ hκ4 b jumps hb x θ q.1 q.2 _ hconst P h hh η ζ hη
        by_cases hxR : x ≤ q.1 ∧
            Sec4.cumWeightRight κ (b ((q.1 + q.2 : ℝ) / 2) + θ * QuantumZipper.chiC κ) ≤ -2
        · by_cases hxL : (q.2 : ℝ) ≤ x ∧
              Sec4.cumWeightLeft κ (b ((q.1 + q.2 : ℝ) / 2) + θ * QuantumZipper.chiC κ) ≤ -2
          · filter_upwards [hR hxR.1 hxR.2, hL hxL.1 hxL.2] with ω h1 h2
            exact ⟨fun _ _ _ => h1, fun _ _ _ => h2⟩
          · filter_upwards [hR hxR.1 hxR.2] with ω h1
            exact ⟨fun _ _ _ => h1, fun _ h2 h3 => absurd ⟨h2, h3⟩ hxL⟩
        · by_cases hxL : (q.2 : ℝ) ≤ x ∧
              Sec4.cumWeightLeft κ (b ((q.1 + q.2 : ℝ) / 2) + θ * QuantumZipper.chiC κ) ≤ -2
          · filter_upwards [hL hxL.1 hxL.2] with ω h2
            exact ⟨fun _ h1 h3 => absurd ⟨h1, h3⟩ hxR, fun _ _ _ => h2⟩
          · exact Eventually.of_forall fun ω =>
              ⟨fun _ h1 h3 => absurd ⟨h1, h3⟩ hxR, fun _ h2 h3 => absurd ⟨h2, h3⟩ hxL⟩
      · -- empty interval
        refine Eventually.of_forall fun ω => ⟨fun _ _ _ t _ y hy => ?_, fun _ _ _ t _ y hy => ?_⟩ <;>
          exact absurd (hy.1.trans hy.2) hne
    · exact Eventually.of_forall fun ω => ⟨fun h' => absurd h' hJ, fun h' => absurd h' hJ⟩
  filter_upwards [ae_all_iff.2 hq] with ω hω t ht y hyJ
  refine ⟨fun hxy hw => ?_, fun hxy hw => ?_⟩
  · obtain ⟨q₁, q₂, hy, hJ, hR, -⟩ := Supp8.exists_rat_Ioo_avoid jumps hyJ hxy.ne
    have hmid : ((q₁ + q₂ : ℝ) / 2) ∈ Ioo (q₁ : ℝ) q₂ := ⟨by linarith [hy.1, hy.2], by linarith [hy.1, hy.2]⟩
    have hby : b y = b ((q₁ + q₂ : ℝ) / 2) :=
      Sec4.eq_of_mem_Ioo_of_isPiecewiseConstant hb (fun z hzJ hz => hJ z hz hzJ) hmid hy
    rw [hby] at hw
    exact ((hω (q₁, q₂)).1 hJ (hR hxy) hw) t ht y hy
  · obtain ⟨q₁, q₂, hy, hJ, -, hL⟩ := Supp8.exists_rat_Ioo_avoid jumps hyJ hxy.ne'
    have hmid : ((q₁ + q₂ : ℝ) / 2) ∈ Ioo (q₁ : ℝ) q₂ := ⟨by linarith [hy.1, hy.2], by linarith [hy.1, hy.2]⟩
    have hby : b y = b ((q₁ + q₂ : ℝ) / 2) :=
      Sec4.eq_of_mem_Ioo_of_isPiecewiseConstant hb (fun z hzJ hz => hJ z hz hzJ) hmid hy
    rw [hby] at hw
    exact ((hω (q₁, q₂)).2 hJ (hL hxy) hw) t ht y hy

/-- The continuation-threshold left inequality in boundary-height units. -/
theorem cumWeightLeft_gt_iff {κ v : ℝ} (hκ : 0 < κ) :
    -2 < Sec4.cumWeightLeft κ v ↔ v < sleLambda κ := by
  rw [Sec4.cumWeightLeft, lt_sub_iff_add_lt, lt_div_iff₀ (Sec4.sleLambda_pos hκ)]
  constructor <;> intro h <;> linarith

/-- The continuation-threshold right inequality in boundary-height units. -/
theorem cumWeightRight_gt_iff {κ v : ℝ} (hκ : 0 < κ) :
    -2 < Sec4.cumWeightRight κ v ↔ -sleLambda κ < v := by
  rw [Sec4.cumWeightRight, lt_sub_iff_add_lt, lt_div_iff₀ (Sec4.sleLambda_pos hκ)]
  constructor <;> intro h <;> linarith

/-- Every real visit before lifetime has the admissible incident height on
the side facing the seed. At the seed, positive lifetime supplies both bounds.
The assertion holds simultaneously for every time and every real point. -/
theorem ae_live_real_incident_bounds {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps) {x θ : ℝ}
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps)
    {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞} (hη : IsFlowLine κ b jumps x θ P h η ζ) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → ∀ y : ℝ, η ω t = y →
      (y ≤ x → leftLim b y + θ * chiC κ < sleLambda κ) ∧
      (x ≤ y → -sleLambda κ < rightLim b y + θ * chiC κ) := by
  have htv := thresholdVisit_ae_forall hκ hκ4 hb hh hη
  have hj := RLC.jumpVisitStatement κ hκ hκ4 b jumps hb x θ P h hh η ζ hη
  have hs := Supp9.ae_seedWeights_of_isFlowLine hη
  have hp := ae_isPathGood_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη
  filter_upwards [htv, hj, hs, hp] with ω htvω hjω hsω hpω t ht y he
  by_cases hyx : y = x
  · subst y
    have hw := hsω (lt_of_le_of_lt (zero_le : (0 : ℝ≥0∞) ≤ t) ht)
    exact ⟨fun _ => (cumWeightLeft_gt_iff hκ).1 hw.1,
      fun _ => (cumWeightRight_gt_iff hκ).1 hw.2⟩
  have ht0 : 0 < t := by
    apply pos_iff_ne_zero.2
    intro ht0
    subst t
    exact hyx (Complex.ofReal_injective (he.symm.trans (Sec7.IsPathGood.zero hpω)))
  have hyJ : y ∉ jumps := fun hyJ => hjω t ht0 ht y hyJ hyx he
  have hw := htvω t ht y hyJ
  constructor
  · intro hy
    rw [Exist.StagedLaw.leftLim_eq_of_notMem hb hyJ]
    apply (cumWeightLeft_gt_iff hκ).1
    exact lt_of_not_ge (fun hbad => hw.2 (lt_of_le_of_ne hy hyx) hbad he)
  · intro hy
    rw [Exist.StagedLaw.rightLim_eq_of_notMem hb hyJ]
    apply (cumWeightRight_gt_iff hκ).1
    exact lt_of_not_ge (fun hbad => hw.1 (lt_of_le_of_ne hy (Ne.symm hyx)) hbad he)

end InteractingSLE.Restart.FCPlumb
