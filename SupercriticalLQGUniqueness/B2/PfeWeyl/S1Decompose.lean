import SupercriticalLQGUniqueness.B2.PfeWeyl.W3Circle
import SupercriticalLQGUniqueness.Uniqueness.TwoScale.GapChecks.Gapc2

 

















set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal
open LQGMetric (DistC addFun addConst ofCont IsGFFPlusBddCont IsGFFPlusCont)
open SupercriticalLQGUniqueness.B2.Iface

namespace SupercriticalLQGUniqueness.B2.PfeWeyl

 
theorem exists_normalized_bdd_decomposition
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistC} (hh : IsGFFPlusBddCont h P) :
    ∃ (k : Ω → DistC) (F' : Ω → C(ℂ, ℝ)),
      IsNormalizedWholePlaneGFF k P ∧ Measurable F' ∧
        (∀ ω, ∃ M : ℝ, ∀ z, |F' ω z| ≤ M) ∧
        ∀ ω, h ω = addFun (k ω) (F' ω) := by
  obtain ⟨-, F, hF, hFb, hg⟩ := hh
  let g : Ω → DistC := fun ω => h ω - ofCont (F ω)
  let a : Ω → ℝ := fun ω => LQGMetric.circleAvg (g ω) 1 0
  have ha : Measurable a := (LQGMetric.measurable_circleAvg_left 1 0).comp hg.measurable
  let k : Ω → DistC := fun ω => addConst (g ω) (-(a ω))
  have hk : LQGMetric.IsWholePlaneGFF k P := hg.addConst ha.neg
  refine ⟨k, fun ω => F ω + ContinuousMap.const ℂ (a ω), ?_, ?_, ?_, ?_⟩
  · refine isNormalizedWholePlaneGFF_iff_old.mpr ⟨hk, ?_⟩
    filter_upwards [LQGMetric.CircleAvg.ae_circleAvg_addConst_one_zero hg] with ω hω
    show LQGMetric.circleAvg (addConst (g ω) (-(a ω))) 1 0 = 0
    rw [hω (-(a ω))]
    exact add_neg_cancel _
  · rw [ContinuousMap.measurable_iff_eval]
    intro x
    simp only [ContinuousMap.add_apply, ContinuousMap.const_apply]
    exact ((ContinuousMap.measurable_eval x).comp hF).add ha
  · intro ω
    obtain ⟨M, hM⟩ := hFb ω
    refine ⟨M + |a ω|, fun z => ?_⟩
    simp only [ContinuousMap.add_apply, ContinuousMap.const_apply]
    exact (abs_add_le _ _).trans (add_le_add (hM z) le_rfl)
  · intro ω
    refine DFunLike.ext _ _ fun φ => ?_
    show h ω φ = (addConst (g ω) (-(a ω)) + ofCont (F ω + ContinuousMap.const ℂ (a ω))) φ
    rw [add_apply, LQGMetric.GFFInv.addConst_apply,
      Uniqueness.TwoScale.GapChecks.ofCont_add_const_apply]
    show h ω φ = (h ω - ofCont (F ω)) φ + (∫ x, φ x) * -(a ω) +
      (ofCont (F ω) φ + (∫ x, φ x) * a ω)
    rw [sub_apply]
    ring

 
theorem ae_heatVersion_shift_eq
    (ε : ℕ → Set.Ioi (0 : ℝ))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (k : Ω → DistC) (hk : IsNormalizedWholePlaneGFF k P)
    (F : Ω → C(ℂ, ℝ)) (Mf : Ω → ℝ) (hMf : ∀ ω z, |F ω z| ≤ Mf ω)
    (hb : IsGFFPlusBddCont (fun ω => addFun (k ω) (F ω)) P)
    (X Y : Set.Ioi (0 : ℝ) → Ω → C(ℂ, ℝ))
    (hX : ∀ δ, IsHeatSmoothing P k δ (X δ))
    (hY : ∀ δ, IsHeatSmoothing P (fun ω => addFun (k ω) (F ω)) δ (Y δ)) :
    ∀ᵐ ω ∂P, ∀ n, Y (ε n) ω = X (ε n) ω +
      LQGMetric.LFPP.mollCont (ε n : ℝ) (ε n).property.ne' (F ω) (Mf ω) (hMf ω) := by
  rw [ae_all_iff]
  intro n
  have hXe := PfeAxioms.ae_heat_smoothing_sequence_eq P k hk ε X hX
  have hYe := PfeAxioms.ae_heatVersion_eq_heatMollify_bdd hb (ε n) (Y (ε n)) (hY (ε n))
  have hconv := hk.1.ae_tendstoLocallyUniformly_heatMollify
    (ε n : ℝ) (ε n).property.ne'
  filter_upwards [hXe, hYe, hconv] with ω hXω hYω hc
  ext z
  change Y (ε n) ω z = X (ε n) ω z + LQGMetric.heatMollify (ε n : ℝ) (ofCont (F ω)) z
  rw [hYω z, hXω n z]
  exact congrFun
    (LQGMetric.LFPP.heatMollify_addFun (ε n).property.ne'
      (fun u => (tendstoLocallyUniformlyOn_univ.2 hc.1).tendsto_at (mem_univ u))
      (F ω) (Mf ω) (hMf ω)) z

end SupercriticalLQGUniqueness.B2.PfeWeyl
