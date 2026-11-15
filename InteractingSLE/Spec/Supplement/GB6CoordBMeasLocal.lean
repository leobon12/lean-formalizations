/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB6CoordBLocal

/-!
# Measurable relative drivers on separated-prefix events

Boundary evaluations, rational prefix reconstruction, and the canonical
`segDriver` give an explicit measurable choice. All geometric assumptions
can be restricted to a measurable event; no positive-time `H` assumption is
used, and no assertion about a causal stopping rule is built into this choice.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Complex
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE.Supp8.GB6.CoordB

open Sec7.PocketTraversal Sec7.Lemma71C

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Measurable reconstruction remains valid on a measurable geometric event. -/
theorem measurable_indicator_drivenDriver {Γ : Ω → ℝ → ℂ} {E : Set Ω}
    (hE : MeasurableSet E) (hΓ : ∀ ω ∈ E, IsDrivenCurve (Γ ω))
    (hm : ∀ u, 0 ≤ u → Measurable (E.indicator fun ω => Γ ω u)) (t : ℝ≥0) :
    Measurable (E.indicator (drivenDriver Γ t)) := by
  have hsub : ∀ u, 0 ≤ u → Measurable fun ω : E => Γ ω.val u := by
    intro u hu
    have h : Measurable fun ω : E => (E.indicator fun ω => Γ ω u) ω.val :=
      (hm u hu).comp measurable_subtype_coe
    convert h using 1
    funext ω
    exact (indicator_of_mem ω.property (fun ω => Γ ω u)).symm
  apply measurable_of_restrict_of_restrict_compl hE
  · have h := measurable_drivenDriver (fun ω : E => hΓ ω.val ω.property) hsub t
    convert h using 1
    funext ω
    exact indicator_of_mem ω.property _
  · have he : (Eᶜ).domRestrict (E.indicator (drivenDriver Γ t)) =
        fun _ : ↥(Eᶜ) => (0 : ℝ) := by
      funext ω
      exact indicator_of_notMem ω.property _
    rw [he]
    exact measurable_const

/-- The lifetime of the reconstructed curve is measurable on the same event. -/
theorem measurable_indicator_capLife {Γ : Ω → ℝ → ℂ} {E : Set Ω}
    (hE : MeasurableSet E) (hΓ : ∀ ω ∈ E, IsDrivenCurve (Γ ω))
    (hm : ∀ u, 0 ≤ u → Measurable (E.indicator fun ω => Γ ω u)) :
    Measurable (E.indicator fun ω => capLife (Γ ω)) := by
  have hsub : ∀ u, 0 ≤ u → Measurable fun ω : E => Γ ω.val u := by
    intro u hu
    have h : Measurable fun ω : E => (E.indicator fun ω => Γ ω u) ω.val :=
      (hm u hu).comp measurable_subtype_coe
    convert h using 1
    funext ω
    exact (indicator_of_mem ω.property (fun ω => Γ ω u)).symm
  apply measurable_of_restrict_of_restrict_compl hE
  · have h := measurable_capLife (fun ω : E => hΓ ω.val ω.property) hsub
    convert h using 1
    funext ω
    exact indicator_of_mem ω.property _
  · have he : (Eᶜ).domRestrict (E.indicator fun ω => capLife (Γ ω)) =
        fun _ : ↥(Eᶜ) => (0 : ℝ≥0∞) := by
      funext ω
      exact indicator_of_notMem ω.property _
    rw [he]
    exact measurable_const

/-- A measurable prefix choice is already adapted before its lifetime in the
constant filtration. This is the input progressive regularization needs. -/
theorem adaptedBefore_indicator_drivenDriver {Γ : Ω → ℝ → ℂ} {E : Set Ω}
    (hE : MeasurableSet E) (hΓ : ∀ ω ∈ E, IsDrivenCurve (Γ ω))
    (hm : ∀ u, 0 ≤ u → Measurable (E.indicator fun ω => Γ ω u)) :
    AdaptedBefore (Filtration.const ℝ≥0 (inferInstance : MeasurableSpace Ω) le_rfl)
      (E.indicator fun ω => capLife (Γ ω))
      (fun t => E.indicator (drivenDriver Γ t)) := by
  intro t A hA
  exact (measurableSet_lt measurable_const (measurable_indicator_capLife hE hΓ hm)).inter
    (measurable_indicator_drivenDriver hE hΓ hm t hA)

section Relative

variable {V : ℝ≥0 → Ω → ℝ} (hVm : ∀ t, Measurable (V t))
  (hVc : ∀ ω, Continuous (V · ω)) (hV0 : ∀ ω, V 0 ω = 0)
  {γ : Ω → ℝ≥0 → ℂ} (hγm : ∀ t, Measurable fun ω => γ ω t)
  {E : Set Ω} (hE : MeasurableSet E) {s T : ℝ≥0}
  (hs : 0 < s) (hT : 0 < T)
  (hgeom : ∀ ω ∈ E, ∃ (w : ℝ≥0 → ℝ) (p : ℂ), Continuous w ∧ w 0 = 0 ∧
    IsGeneratingTrace w ⊤ (γ ω) ∧
    Tendsto (QuantumZipper.fwdMapInv (Ito.rpath (V · ω)) s) (𝓝[H] 0) (𝓝 p) ∧
    Disjoint (closure (QuantumZipper.fwdHull (Ito.rpath (V · ω)) s))
      (closure ((fun z : ℂ => -z⁻¹) '' QuantumZipper.fwdHull (Ito.rpath w) T)))

include hVc hV0 hs hT hgeom in
omit [MeasurableSpace Ω] in
theorem isDrivenCurve_localCurve_on : ∀ ω ∈ E,
    IsDrivenCurve (localCurve (Ito.rpath (V · ω)) s (γ ω) T) := by
  intro ω hω
  obtain ⟨w, p, hw, hw0, hγ, htip, hd⟩ := hgeom ω hω
  exact isDrivenCurve_localCurve (Chart.continuous_rpath_of_continuous (hVc ω))
    (Chart.rpath_zero_of (hV0 ω)) (by exact_mod_cast hs) htip hw hw0 hγ hT hd

include hVm hVc hV0 hγm hT hgeom hE in
/-- The extended mapped curve is measurable at fixed reparametrized times,
even when the physical trace visits the real axis. -/
theorem measurable_indicator_localCurve (u : ℝ) (hu : 0 ≤ u) :
    Measurable (E.indicator fun ω => localCurve (Ito.rpath (V · ω)) s (γ ω) T u) := by
  apply measurable_indicator_relBdry hVm hVc hV0 s hE (hγm _)
  intro ω hω
  obtain ⟨w, p, hw, hw0, hγ, htip, hd⟩ := hgeom ω hω
  have hd' := Q3Rel.disjoint_closure_invHull (Chart.continuous_rpath_of_continuous (hVc ω))
    s.coe_nonneg hd
  apply trace_mem_relSafe (Chart.continuous_rpath_of_continuous (hVc ω)) s.coe_nonneg hw hw0 hγ hd'
  exact Real.toNNReal_le_iff_le_coe.2 ((clockOf_lt (by exact_mod_cast hT) hu).le)

include hVm hVc hV0 hγm hs hT hgeom hE in
/-- Explicit measurable local relative driver on every separated-prefix event. -/
theorem measurable_indicator_localDriver (t : ℝ≥0) :
    Measurable (E.indicator
      (drivenDriver (fun ω => localCurve (Ito.rpath (V · ω)) s (γ ω) T) t)) :=
  measurable_indicator_drivenDriver hE (isDrivenCurve_localCurve_on hVc hV0 hs hT hgeom)
    (measurable_indicator_localCurve hVm hVc hV0 hγm hE hT hgeom) t

include hVm hVc hV0 hγm hs hT hgeom hE in
theorem measurable_indicator_localLife :
    Measurable (E.indicator fun ω => capLife (localCurve (Ito.rpath (V · ω)) s (γ ω) T)) :=
  measurable_indicator_capLife hE (isDrivenCurve_localCurve_on hVc hV0 hs hT hgeom)
    (measurable_indicator_localCurve hVm hVc hV0 hγm hE hT hgeom)

end Relative

end InteractingSLE.Supp8.GB6.CoordB
