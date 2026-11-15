/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.RetMatchLiftRules

/-!
# Increasing limits of measurable history rules

Galmarino rules are closed under suprema. Consequently an increasing sequence
of measurable history rules converging to the model's lifetime supplies the
exact lifetime representation used by the retained determination consumer.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Wire.RetMatchPredict

open RetMatchLift
open Restart Restart.RetAux79 Restart.StoppedExtendWF LawUnique Sec7.PocketTraversal

/-- A supremum of Galmarino rules is Galmarino: agreement before its value
implies agreement before every constituent rule's value. -/
theorem isHistGalmarino_iSup {nL nR : ℕ} {ι : Type*}
    {Q : ι → HistorySpace nL nR → ℝ≥0∞} (hQ : ∀ i, IsHistGalmarino (Q i)) :
    IsHistGalmarino (fun γ => ⨆ i, Q i γ) := by
  intro γ δ hγ hδ hγlife hδlife hag
  apply iSup_congr
  intro i
  have hQi : Q i γ ≤ ⨆ j, Q j γ := le_iSup (fun j => Q j γ) i
  exact hQ i γ δ hγ hδ (hQi.trans hγlife) (hQi.trans hδlife)
    (fun p hp => hag p (hp.trans_le hQi))

/-- An increasing measurable Galmarino-rule approximation to the lifetime
gives the full lifetime rule. This is a proved limit step, not a representation
assumption for the approximating rules. -/
theorem hasStoppedTypeHistoryRule_of_ruleSequence {κ θ : ℝ}
    (M : StoppedTypeModel κ θ)
    {Q : ℕ → HistorySpace M.data.nL M.data.nR → ℝ≥0∞}
    (hQm : ∀ n, Measurable (Q n)) (hQg : ∀ n, IsHistGalmarino (Q n))
    (hmono : ∀ᵐ ω ∂M.law, Monotone fun n => Q n (killedHistory M.data.driver
      (geomLW M.data.driver M.data.xL) (geomRW M.data.driver M.data.xR)
      M.data.life ω))
    (hlim : ∀ᵐ ω ∂M.law, Tendsto
      (fun n => Q n (killedHistory M.data.driver
        (geomLW M.data.driver M.data.xL) (geomRW M.data.driver M.data.xR)
        M.data.life ω)) atTop (𝓝 (M.data.life ω))) :
    HasStoppedTypeHistoryRule M := by
  refine ⟨fun γ => ⨆ n, Q n γ, Measurable.iSup hQm,
    isHistGalmarino_iSup hQg, ?_⟩
  filter_upwards [hmono, hlim] with ω hm hl
  exact (tendsto_nhds_unique (tendsto_atTop_iSup hm) hl).symm

end InteractingSLE.Wire.RetMatchPredict
