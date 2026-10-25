import SupercriticalLQGUniqueness.B2.PfeAxioms.LocalObservableBddFactor
import LQGMetric.Papers.DFGPS.L2_17CoreG

 


set_option autoImplicit false
noncomputable section

open MeasureTheory Set Topology
open LQGMetric

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

 

def clampContinuous (C : ℝ) (f : C(ℂ, ℝ)) : C(ℂ, ℝ) :=
  ⟨fun z => max (-C) (min C (f z)), by fun_prop⟩

theorem clampContinuous_bound {C : ℝ} (hC : 0 ≤ C) (f : C(ℂ, ℝ)) (z : ℂ) :
    |clampContinuous C f z| ≤ C := by
  refine abs_le.2 ⟨le_max_left _ _, ?_⟩
  exact max_le (by linarith) (min_le_left _ _)

theorem clampContinuous_eq_of_bound {C : ℝ} (f : C(ℂ, ℝ))
    {z : ℂ} (hz : |f z| ≤ C) : clampContinuous C f z = f z := by
  rw [abs_le] at hz
  show max (-C) (min C (f z)) = f z
  rw [min_eq_right hz.2, max_eq_right hz.1]

 

theorem exists_nat_clampContinuous_eqOn (f : C(ℂ, ℝ))
    {U : Set ℂ} (hU : Bornology.IsBounded U) :
    ∃ N : ℕ, EqOn (clampContinuous N f) f U := by
  obtain ⟨C, hC⟩ := hU.isCompact_closure.exists_bound_of_continuousOn
    f.continuous.continuousOn
  obtain ⟨N, hN⟩ := exists_nat_ge C
  refine ⟨N, fun z hz => ?_⟩
  apply clampContinuous_eq_of_bound
  have hCz := hC z (subset_closure hz)
  rw [Real.norm_eq_abs] at hCz
  exact hCz.trans hN

theorem measurable_clampContinuous (C : ℝ) :
    Measurable (clampContinuous C) := by
  apply ContinuousMap.measurable_iff_eval.2
  intro z
  change Measurable fun f : C(ℂ, ℝ) => max (-C) (min C (f z))
  exact measurable_const.max (measurable_const.min (continuous_eval_const z).measurable)

 

theorem gffPlusCont_bounded_truncations
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    {h : Ω → DistC} (hh : IsGFFPlusCont h P) :
    ∃ f : Ω → C(ℂ, ℝ), Measurable f ∧
      IsWholePlaneGFF (fun ω => h ω - ofCont (f ω)) P ∧
      ∀ N : ℕ, IsGFFPlusBddCont
        (fun ω => (h ω - ofCont (f ω)) -
          ofCont (-(clampContinuous N (f ω)))) P := by
  obtain ⟨-, f, hf, hg⟩ := hh
  refine ⟨f, hf, hg, fun N => ?_⟩
  apply LQGMetric.DFGPS.L217.isGFFPlusBddCont_sub_ofCont hg
  · exact (measurable_clampContinuous N).comp hf |>.neg
  · intro ω
    exact ⟨N, fun z => by
      simpa using clampContinuous_bound (Nat.cast_nonneg N) (f ω) z⟩

end SupercriticalLQGUniqueness.B2.PfeAxioms
