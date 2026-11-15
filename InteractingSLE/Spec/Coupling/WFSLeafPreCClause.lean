/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.WFSLeafPreCFilt
import InteractingSLE.Spec.Exist.TransferHist

/-!
# The field clause under restriction of a stopped filtration

The conditional Gaussian functional and its avoidance event are Borel functions
of the closed stopped record. Localization and the tower property transfer the
clause to any smaller sigma algebra in which that record is measurable.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology QuantumZipper
open scoped NNReal ENNReal

namespace InteractingSLE.WFS

open LawUnique Sec4 LQGMetric Restart.Aux54

/-- The localized form of the existing tower adapter. -/
theorem condExp_eq_on_of_le_of_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {m₁ m₂ : MeasurableSpace Ω} (h12 : m₁ ≤ m₂) (h2 : m₂ ≤ mΩ)
    {E : Set Ω} (hE : MeasurableSet[m₁] E) {f g : Ω → ℂ} (hf : Integrable f P)
    (hg : StronglyMeasurable[m₁] g)
    (hfg : ∀ᵐ ω ∂P, ω ∈ E → P[f | m₂] ω = g ω) :
    ∀ᵐ ω ∂P, ω ∈ E → P[f | m₁] ω = g ω := by
  classical
  have he : E.indicator (P[f | m₂]) =ᵐ[P] E.indicator g := by
    filter_upwards [hfg] with ω hω
    by_cases h : ω ∈ E
    · simp only [indicator_of_mem h, hω h]
    · simp only [indicator_of_notMem h]
  have hb : P[E.indicator f | m₂] =ᵐ[P] E.indicator g :=
    (condExp_indicator hf (h12 _ hE)).trans he
  have hs := WholeField.condExp_ae_eq_of_le_of_ae_eq (mΩ := mΩ) h12 h2 (hg.indicator hE) hb
  filter_upwards [hs, condExp_indicator hf hE] with ω hsω hiω hω
  rw [hiω, indicator_of_mem hω] at hsω
  simpa only [indicator_of_mem hω] using hsω

/-- The endpoint reader agrees with the usual closed history of a longer
continuous evolution at every strictly earlier finite stop. -/
theorem closedPrefixHistory_killedHistory_eq
    {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {Ω : Type*}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {e ζ : Ω → ℝ≥0∞} {ω : Ω} {T : ℝ≥0}
    (hT : (T : ℝ≥0∞) = e ω) (hc : ContinuousOn (dState W VL VR ω) (Iic T))
    (h0 : dState W VL VR ω 0 = initVal xL xR) (hζ : (T : ℝ≥0∞) < ζ ω) :
    closedPrefixHistory xL xR (killedHistory W VL VR e ω) =
      stopHistory (fun _ => T) (killedHistory W VL VR ζ ω) := by
  have ht : (recH xL xR (killedHistory W VL VR e ω)).1.toNNReal = T := by
    simp only [recH, killedHistory, ← hT, ENNReal.toNNReal_coe]
  refine Prod.ext (by simp only [closedPrefixHistory, stopHistory, ht]) (funext fun p => ?_)
  dsimp only [closedPrefixHistory, stopHistory]
  simp only [ht]
  by_cases hp : dyadicTime p ≤ T
  · rw [ite_eq_left hp, ite_eq_left hp, recH_killedHistory_snd hT hc h0, min_eq_left hp]
    have hpζ : (dyadicTime p : ℝ≥0∞) < ζ ω :=
      lt_of_le_of_lt (ENNReal.coe_le_coe.2 hp) hζ
    simp only [killedHistory, hpζ, ↓reduceIte, dState]
  · rw [ite_eq_right hp, ite_eq_right hp]

/-- Transfer of the frozen field clause to a smaller sigma algebra carrying
the same closed record. The locality clause transfers directly elsewhere. -/
theorem clauseAt_of_measurable_closedRecord
    {κ : ℝ} {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : Measurable h)
    {τ : Ω → WithTop ℝ≥0} {m₁ m₂ : MeasurableSpace Ω}
    (h12 : m₁ ≤ m₂) (h2 : m₂ ≤ mΩ) {Z : Ω → HistorySpace nL nR}
    (hZ : Measurable[m₁] Z)
    (hz : ∀ᵐ ω ∂P, IsGoodStop (fun _ => (τ ω).untopD 0) W VL VR ζ ω ∧
      Z ω = stopHistory (fun _ => (τ ω).untopD 0) (killedHistory W VL VR ζ ω))
    (hcl : ClauseAt κ ρL ρR P W VL VR h τ m₂) :
    ClauseAt κ ρL ρR P W VL VR h τ m₁ := by
  intro u hu φ
  obtain ⟨A, hAm, -, hAe⟩ := hasMeasurableHistHull (nL := nL) (nR := nR)
  obtain ⟨G, hGm, hGe⟩ := hasMeasurableHistCharFun κ ρL ρR
  let E : Set Ω := {ω | Disjoint (tsupport φ) (A (Z ω))}
  have hE : MeasurableSet[m₁] E := hZ (hAm _ φ.hasCompactSupport.isCompact)
  have hc : ∀ᵐ ω ∂P, ω ∈ E →
      P[fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ)) | m₂] ω = G φ (Z ω) := by
    filter_upwards [hz, hcl u hu φ] with ω hz hc hd
    change Disjoint (tsupport φ) (A (Z ω)) at hd
    rw [hz.2] at hd ⊢
    have hcont := isContHist_stopHistory hz.1
    rw [hAe _ hcont] at hd
    rw [hGe _ _ hcont hd]
    rw [Exist.histHull_eq_fwdHull hz.1] at hd
    rw [Exist.histCharFun_eq_of_goodStop κ ρL ρR hz.1 (hu ω) hd]
    exact hc hd
  have hs := condExp_eq_on_of_le_of_measurable (mΩ := mΩ) h12 h2 hE
    (@LocalExt.integrable_cexp_field Ω mΩ P inferInstance h hh φ) ((hGm φ).comp hZ).stronglyMeasurable hc
  filter_upwards [hz, hs] with ω hz hs hd
  have hcont := isContHist_stopHistory hz.1
  have hd' : ω ∈ E := by
    change Disjoint (tsupport φ) (A (Z ω))
    rw [hz.2, hAe _ hcont, Exist.histHull_eq_fwdHull hz.1]
    exact hd
  rw [hs hd']
  change G φ (Z ω) = _
  rw [hz.2, hGe _ _ hcont (by rwa [Exist.histHull_eq_fwdHull hz.1]),
    Exist.histCharFun_eq_of_goodStop κ ρL ρR hz.1 (hu ω) hd]

end InteractingSLE.WFS
