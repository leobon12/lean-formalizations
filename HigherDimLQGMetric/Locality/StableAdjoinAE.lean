import HigherDimLQGMetric.Locality.StableAdjoin

/-! The adjoined stable law for almost surely measurable LFPP metrics. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l7a_stable_adjoin_field_ae {d : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : Measurable h)
    (X : ℕ → Ω → C(Rd d × Rd d, ℝ))
    (Y : Ω → C(Rd d × Rd d, ℝ))
    (hX : ∀ n, AEMeasurable (X n) P) (hY : Measurable Y)
    (hstable : StablyTendstoLU P h X Y)
    {A : Type*} [TopologicalSpace A] [MeasurableSpace A]
    [OpensMeasurableSpace A] [SecondCountableTopology A]
    (Φ : (CoordJ → ℝ) → A) (hΦ : Measurable Φ) :
    Tendsto (β := ProbabilityMeasure (A × C(Rd d × Rd d, ℝ)))
      (fun n => (⟨P.map (fun ω => (Φ (pairJ ⊤ (h ω)), X n ω)),
        (Measure.isProbabilityMeasure_map_iff
          ((hΦ.comp ((measurable_pairJ ⊤).comp hh)).aemeasurable.prodMk (hX n))).2
            inferInstance⟩ : ProbabilityMeasure (A × C(Rd d × Rd d, ℝ))))
      atTop
      (𝓝 (⟨P.map (fun ω => (Φ (pairJ ⊤ (h ω)), Y ω)),
        (Measure.isProbabilityMeasure_map_iff
          ((hΦ.comp ((measurable_pairJ ⊤).comp hh)).prodMk hY).aemeasurable).2
            inferInstance⟩ : ProbabilityMeasure (A × C(Rd d × Rd d, ℝ)))) := by
  let Xm : ℕ → Ω → C(Rd d × Rd d, ℝ) := fun n => (hX n).mk (X n)
  have hXm (n : ℕ) : Measurable (Xm n) := (hX n).measurable_mk
  have hXe (n : ℕ) : X n =ᵐ[P] Xm n := (hX n).ae_eq_mk
  have hstable' : StablyTendstoLU P h Xm Y := by
    intro g hg hgb ψ hψ hψb
    have heq (n : ℕ) :
        ∫ ω, g (h ω) * ψ (Xm n ω) ∂P =
        ∫ ω, g (h ω) * ψ (X n ω) ∂P := by
      apply integral_congr_ae
      filter_upwards [hXe n] with ω he
      rw [he]
    simpa only [heq] using hstable g hg hgb ψ hψ hψb
  have hlim := l7a_stable_adjoin_field P h hh Xm Y hXm hY hstable' Φ hΦ
  let νn : ℕ → ProbabilityMeasure (A × C(Rd d × Rd d, ℝ)) := fun n =>
    ⟨P.map (fun ω => (Φ (pairJ ⊤ (h ω)), X n ω)),
      (Measure.isProbabilityMeasure_map_iff
        ((hΦ.comp ((measurable_pairJ ⊤).comp hh)).aemeasurable.prodMk (hX n))).2
          inferInstance⟩
  let νm : ℕ → ProbabilityMeasure (A × C(Rd d × Rd d, ℝ)) := fun n =>
    ⟨P.map (fun ω => (Φ (pairJ ⊤ (h ω)), Xm n ω)),
      (Measure.isProbabilityMeasure_map_iff
        ((hΦ.comp ((measurable_pairJ ⊤).comp hh)).prodMk (hXm n)).aemeasurable).2
          inferInstance⟩
  have hν (n : ℕ) : νn n = νm n := by
    apply Subtype.ext
    apply Measure.map_congr
    filter_upwards [hXe n] with ω he
    exact Prod.ext rfl he
  change Tendsto νn atTop _
  change Tendsto νm atTop _ at hlim
  have heq : νn = νm := funext hν
  rw [heq]
  exact hlim

end HigherDimLQGMetric
