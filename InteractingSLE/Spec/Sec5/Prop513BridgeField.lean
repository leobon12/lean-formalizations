/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop513FieldChart
import InteractingSLE.Spec.Restart.RetAux79
import InteractingSLE.Spec.Coupling.WholeField2Hull

/-!
# Field sigma-algebras for Proposition 5.13's consumers

PROVE-PROP513-BRIDGE. A signed conformal transport on all of the half-plane
preserves the field sigma-algebra. This uses the existing inverse test transport
`Chart.exists_pushTest_eq`, without choosing an inverse random field. Deterministic
changes of harmonic mean use `WholeField.comap_sub_dist`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open LQGMetric (DistOn TestOn)
open SupercriticalConformalCovariance.GM24 (smoothDist)

namespace InteractingSLE.Sec5.Prop513Bridge

universe u

/-- Recover measurability of a field from a signed full-domain chart transport.
The nonzero sign and the full chart domain are essential. -/
theorem measurable_of_signed_chart {Ω : Type u} {m : MeasurableSpace Ω}
    {c : Chart} (hc : c.IsConformal) (hdom : c.dom = upperHalfPlaneOpens)
    {σ a k : ℝ} (hσ : σ ≠ 0) {h h' : Ω → DistOn upperHalfPlaneOpens}
    (hT : ∀ ω, IsChartTransport c σ a k (h ω) (h' ω))
    (hh' : Measurable[m] h') : Measurable[m] h := by
  apply LQGMetric.measurable_distOn_iff.2
  intro ψ
  have hsupp : tsupport ψ ⊆ c.dom := by
    rw [hdom]
    exact ψ.tsupport_subset
  obtain ⟨φ, hφ⟩ := Chart.exists_pushTest_eq hc ψ hsupp
  have he : (fun ω => h ω ψ) = fun ω =>
      (h' ω φ - a * (∫ z, φ z) -
        k * (∫ z, c.2.2 (c.2.1 z) * φ z)) / σ := by
    funext ω
    have ht := (hT ω).apply_eq hc φ
    rw [hφ] at ht
    apply (eq_div_iff hσ).2
    linarith only [ht]
  rw [he]
  exact (((LQGMetric.measurable_distOn_apply φ).comp hh').sub_const _).sub_const
    _ |>.div_const σ

/-- A signed chart covering the whole half-plane preserves the exact cylinder
sigma-algebra of the field, including its deterministic lift and offset. -/
theorem comap_eq_of_signed_chart {Ω : Type u} {c : Chart}
    (hc : c.IsConformal) (hdom : c.dom = upperHalfPlaneOpens)
    {σ a k : ℝ} (hσ : σ ≠ 0)
    (hl : LocallyIntegrableOn (fun z => c.2.2 (c.2.1 z)) QuantumZipper.H)
    {h h' : Ω → DistOn upperHalfPlaneOpens}
    (hT : ∀ ω, IsChartTransport c σ a k (h ω) (h' ω)) :
    MeasurableSpace.comap h inferInstance = MeasurableSpace.comap h' inferInstance := by
  apply le_antisymm
  · exact (measurable_of_signed_chart hc hdom hσ hT (comap_measurable h')).comap_le
  · have he : h' = fun ω => Chart.chartTransport hc σ a k (h ω) :=
      funext fun ω => (hT ω).eq_chartTransport hc hl
    rw [he]
    exact ((Chart.measurable_chartTransport hc σ a k).comp
      (comap_measurable h)).comap_le

/-- In particular, the strip parameter field and the Fig. 5.1 field generate
identical sigma-algebras in their existing capacity chart. -/
theorem comap_eq_strip_parameter {Ω : Type u} {q : ℝ} (hq : 0 < q)
    {a k : ℝ} {h h' : Ω → DistOn upperHalfPlaneOpens}
    (hT : ∀ ω, IsChartTransport (Sec4.stripCounterflowChart q) (-1) a k
      (h ω) (h' ω)) :
    MeasurableSpace.comap h inferInstance = MeasurableSpace.comap h' inferInstance :=
  comap_eq_of_signed_chart (Prop513Field.isConformal hq) (Prop513Field.dom_eq hq)
    (by norm_num) (Chart.locallyIntegrableOn_of_continuousOn
      (Prop513Field.continuousOn_lift_inv hq)) hT

/-- Addition version of the existing deterministic distribution shift lemma. -/
theorem comap_add_dist {Ω : Type u} (h : Ω → DistOn upperHalfPlaneOpens)
    (T : DistOn upperHalfPlaneOpens) :
    MeasurableSpace.comap (fun ω => h ω + T) inferInstance =
      MeasurableSpace.comap h inferInstance := by
  simpa only [sub_neg_eq_add] using WholeField.comap_sub_dist h (-T)

/-- Changing the deterministic mean in the consumers does not change the field
sigma-algebra; neither harmonicity nor a boundary-mean identification is needed. -/
theorem comap_centredField_add {Ω : Type u}
    (h : Ω → DistOn upperHalfPlaneOpens) (u₀ u : ℂ → ℝ) :
    MeasurableSpace.comap
      (fun ω => WholeField.centredField h u₀ ω + smoothDist upperHalfPlaneOpens u)
      inferInstance = MeasurableSpace.comap h inferInstance := by
  have he : (fun ω => WholeField.centredField h u₀ ω + smoothDist upperHalfPlaneOpens u) =
      fun ω => h ω - (smoothDist upperHalfPlaneOpens u₀ - smoothDist upperHalfPlaneOpens u) := by
    funext ω
    dsimp only [WholeField.centredField]
    abel
  rw [he]
  exact WholeField.comap_sub_dist _ _

end InteractingSLE.Sec5.Prop513Bridge
