/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.RetMatchMeyerRaw

/-!
# The Galmarino conclusion from a raw history version

The raw version supplied by predictable-time lifting lives on killed history
space, whereas the earlier Galmarino constructor takes a complete-state raw
stopping time. Infinite recording bridges the two without another stochastic
input. The equality is proved before each record's lifetime and transported
under the canonical image law.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Wire.RetMatchMeyer

open LawUnique Restart.FlowStopIdentG Restart.RetAux79 Restart.StoppedExtendWF
open RetMatchRaw RetMatchGal Sec7.PocketTraversal

variable {nL nR : ℕ}

/-- Reading an infinite record recovers each value of a continuous state path. -/
theorem histState_fullHistory {w : ℝ≥0 → DrivingValue nL nR} (hc : Continuous w)
    (t : ℝ≥0) : histState (fullHistory w) t = w t := by
  exact Tendsto.limUnder_eq ((hc.tendsto t).comp (tendsto_dyadicTime_lowerDyadic t))

/-- A raw history stopping time strictly before killing has the same value
on the infinite record of the original continuous path. -/
theorem rawStop_fullHistory_eq_killedHistory
    {τ : HistorySpace nL nR → ℝ≥0∞}
    (hτ : IsStoppingTime historyFiltration (fun γ => (τ γ : WithTop ℝ≥0)))
    {Ω : Type*} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞} {ω : Ω}
    (hc : Continuous (fun t => (W t ω, fun i => VL i t ω, fun j => VR j t ω)))
    (hpre : τ (killedHistory W VL VR V ω) < V ω) :
    τ (fullHistory (fun t => (W t ω, fun i => VL i t ω, fun j => VR j t ω))) =
      τ (killedHistory W VL VR V ω) := by
  apply eq_of_isStoppingTime_historyPrefix hτ _ _ hpre (hpre.trans_le le_top)
  intro r hr
  exact (histState_killedHistory hc.continuousOn (hr.trans_lt hpre)).trans
    (histState_fullHistory hc r).symm

/-- Every measurable raw history version of the canonical stop yields the
full global Galmarino witness. This conclusion has no predictability premise. -/
theorem exists_canonicalHistoryRule_of_rawHistoryStop
    {κ θ : ℝ} (M : StoppedTypeModel κ θ)
    {s : HistorySpace M.data.nL M.data.nR → ℝ≥0} (hsm : Measurable s)
    (hpre : ∀ᵐ γ ∂modelHistoryLaw M, 0 < (s γ : ℝ≥0∞) ∧ (s γ : ℝ≥0∞) < γ.1)
    {τ : HistorySpace M.data.nL M.data.nR → ℝ≥0∞} (hτm : Measurable τ)
    (hτ : IsStoppingTime historyFiltration (fun γ => (τ γ : WithTop ℝ≥0)))
    (he : ∀ᵐ γ ∂modelHistoryLaw M, (s γ : ℝ≥0∞) = τ γ) :
    ∃ Q : HistorySpace M.data.nL M.data.nR → ℝ≥0∞,
      Measurable Q ∧ IsHistGalmarino Q ∧
        ∀ᵐ γ ∂modelHistoryLaw M, (s γ : ℝ≥0∞) = Q γ := by
  apply exists_canonicalHistoryRule_of_rawStop M hsm hpre
    (hτm.comp measurable_fullHistory) (isStoppingTime_fullHistory hτ)
  have he' := ae_of_ae_map (measurable_modelHistory M).aemeasurable he
  have hp' := ae_of_ae_map (measurable_modelHistory M).aemeasurable hpre
  filter_upwards [he', hp'] with ω heω hpω
  have hτpre : τ (modelHistory M ω) < M.data.life ω := heω ▸ hpω.2
  exact heω.trans (rawStop_fullHistory_eq_killedHistory hτ
    (continuous_modelState M ω) hτpre).symm

end InteractingSLE.Wire.RetMatchMeyer
