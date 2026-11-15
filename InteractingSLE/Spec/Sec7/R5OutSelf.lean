import InteractingSLE.Spec.Sec7.R5OutCapacityWire
import InteractingSLE.Spec.Sec7.R5OLawRefInf

/-! # Deterministic relative references from the proved source phase word -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H)
open LQGMetric (DistOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R5Out
open LocalSets PocketTraversal Lemma71C PocketStop PocketStopSide PocketStopField R5Wall PhaseSel Aux119Heights

/-- A proved phase word supplies the deterministic relative cover by using
the current chart as a reference. This transfers the source rational-time
proof to the earlier relative-cover interface without changing either statement. -/
theorem r5Cover_self_of_phaseWord {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {κ : ℝ} {nL nR : ℕ} {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ}
    {A : Set Ω} {γ : Ω → ℝ → ℂ} {xL : Ω → Fin (nL + 1) → ℝ} {xR : Ω → Fin (nR + 1) → ℝ}
    {c : Ω → Chart} {a : ℝ} {h₀ : Ω → DistOn upperHalfPlaneOpens} {u : ℂ → ℝ} {C : Ω → Set ℂ}
    {δ : Ω → ℝ} {q : ℝ≥0} (hγ : ∀ ω ∈ A, IsDrivenCurve (γ ω)) (hc : ∀ ω ∈ A, (c ω).IsConformal)
    (hNorm : liveExt A γ C (activeCompl A γ c q) 0 = activeCompl A γ c q)
    (hWord : PocketStopPhaseSideLimit κ ρL ρR P A γ xL xR c a h₀ u (activeCompl A γ c q) δ q) :
    R5Cover κ ρL ρR P A γ xL xR c a h₀ u C (fun _ => activeCompl A γ c q) δ (fun _ => ∅)
      (fun _ ω => (relChart c γ q ω).2.2) (fun _ => {ω | ω ∈ A ∧ (q : ℝ≥0∞) < capLife (γ ω)})
      (fun _ => relChart c γ q) q (fun _ _ => True) := by
  intro gB hgB
  have hg : IsLocalSetMean (activeCompl A γ c q) h₀ P (gB 0) := by rw [← hNorm]; exact hgB 0
  filter_upwards [hWord.2 (gB 0) hg, hg.2.1] with ω hw hr hω hq ξ hξ _ _
  have hcur := isConformal_relChart_of_driven (c := c) (hγ ω hω) hq (hc ω hω)
  obtain ⟨hv, hPair⟩ := harmRep_spec hr
  have hHeight := hw hω hq _ hv hPair ξ hξ
  let b := phaseData κ ρL ρR
    (fun i => geomLW (fun t ω => segDriver (γ ω) t) xL i q ω - segDriver (γ ω) q)
    (fun j => geomRW (fun t ω => segDriver (γ ω) t) xR j q ω - segDriver (γ ω) q) (δ ω) ξ - a
  refine ⟨0, ξ, 1, b, 0, ⟨hω, hq⟩, zero_lt_one, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact hcur.inv_mem_dom hz.1
  · refine (tendsto_id.mono_left nhdsWithin_le_nhds).congr' ?_
    exact eventually_nhdsWithin_of_forall fun z hz => (hcur.2.2 z hz).symm
  · simpa only [hNorm] using hHeight
  · simpa only [sub_self] using (tendsto_const_nhds (x := (0 : ℝ)) :
      Tendsto (fun _ : ℂ => (0 : ℝ)) (𝓝[H] (ξ : ℂ)) (𝓝 0))
  · rw [mul_zero, add_zero]

end InteractingSLE.Sec7.R5Out
