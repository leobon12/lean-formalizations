import SupercriticalLQGUniqueness.Uniqueness.EndSaving.RadonNikodym.FiniteRNFactorV2




 







set_option autoImplicit false
noncomputable section
open Set Finset MeasureTheory
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.RadonNikodym
open LQGMetric (DistC TestC)
open SupercriticalLQGUniqueness.Uniqueness.EndSaving.InterfaceV2

 

theorem finiteBump_probability_window
    {Ω ι : Type} [MeasurableSpace Ω] [DecidableEq ι]
    (P : Measure Ω) (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (Z : Finset ι) (f : ι → TestC)
    (hdisj : ∀ i ∈ Z, ∀ j ∈ Z, i ≠ j →
      Disjoint (tsupport (⇑(f i) : ℂ → ℝ))
        (tsupport (⇑(f j) : ℂ → ℝ)))
    (E : Set DistC) (hE : MeasurableSet E)
    (hconst : ∀ (g : DistC) (c : ℝ),
      g ∈ E ↔ LQGMetric.addConst g c ∈ E)
    (C : ℝ) (hC : 0 < C)
    (hwindow : ∀ g ∈ E, ∀ i ∈ Z,
      C⁻¹ ≤ LQGMetric.cmDensity (f i) (LQGMetric.pair0 g) ∧
      LQGMetric.cmDensity (f i) (LQGMetric.pair0 g) ≤ C) :
    ENNReal.ofReal ((C⁻¹) ^ Z.card) * P (sampleEvent h E) ≤
      P (sampleEvent (fun ω => LQGMetric.addFun (h ω)
        (LQGMetric.testCont (∑ i ∈ Z, f i))) E) ∧
    P (sampleEvent (fun ω => LQGMetric.addFun (h ω)
        (LQGMetric.testCont (∑ i ∈ Z, f i))) E) ≤
      ENNReal.ofReal (C ^ Z.card) * P (sampleEvent h E) := by
  apply oneBump_probability_window P h hh (∑ i ∈ Z, f i) E hE hconst
    (ENNReal.ofReal ((C⁻¹) ^ Z.card)) (ENNReal.ofReal (C ^ Z.card))
  intro g hg
  rw [cmDensity_finset_sum_of_disjoint Z f hdisj g]
  have hLo : (C⁻¹) ^ Z.card ≤
      ∏ i ∈ Z, LQGMetric.cmDensity (f i) (LQGMetric.pair0 g) := by
    rw [← Finset.prod_const]
    exact Finset.prod_le_prod₀
      (fun i hi => inv_nonneg.mpr hC.le)
      (fun i hi => (hwindow g hg i hi).1)
  have hHi : (∏ i ∈ Z, LQGMetric.cmDensity (f i)
      (LQGMetric.pair0 g)) ≤ C ^ Z.card := by
    rw [← Finset.prod_const]
    exact Finset.prod_le_prod₀
      (fun i hi => (Real.exp_pos _).le)
      (fun i hi => (hwindow g hg i hi).2)
  exact ⟨ENNReal.ofReal_le_ofReal hLo, ENNReal.ofReal_le_ofReal hHi⟩

end SupercriticalLQGUniqueness.Uniqueness.EndSaving.RadonNikodym
