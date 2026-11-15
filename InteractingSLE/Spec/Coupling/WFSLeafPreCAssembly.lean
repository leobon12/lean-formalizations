/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.WFSLeafPreCApprox

/-!
# WFS from strict own-history announcing rules

The regular stopped prefix models, their field clauses at the closed endpoint,
and the reference cofinality are now proved. The remaining stochastic input is
an announcing sequence of Borel Galmarino rules for an arbitrary positive
own-history cutoff. The zero-cutoff case is proved separately.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.WFS

open LawUnique Restart.StoppedExtendWF LQGMetric

/-- Remaining announcing-rule construction for positive through cutoffs.
No field-law equality, kernel, or stopped-coupling realization is assumed.
This construction is not proved here. -/
def StrictRuleAnnounceStatement (κ : ℝ) : Prop :=
  ∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ)
    (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ), IsOrderedForceWord xL xR →
    ∀ R : HistorySpace nL nR → ℝ≥0∞, Measurable R → IsHistGalmarino R →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ)
      (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
      (B : ℝ≥0 → Ω → ℝ) (ζ V : Ω → ℝ≥0∞) (h : Ω → DistOn upperHalfPlaneOpens)
      (hC : IsCouplingThrough κ xL xR ρL ρR P 𝓕 W VL VR B ζ V h),
      (∀ᵐ ω ∂P, V ω = R (killedHistory W VL VR V ω)) →
      (∀ᵐ ω ∂P, 0 < V ω) →
      ∃ Q : ℕ → HistorySpace nL nR → ℝ≥0∞,
        (∀ n, Measurable (Q n) ∧ IsHistGalmarino (Q n)) ∧
        (∀ n, IsStoppingTime (drivingFiltration P hC.2.2.2.2.choose)
          fun ω => (Q n (killedHistory W VL VR V ω) : WithTop ℝ≥0)) ∧
        (∀ n, ∀ᵐ ω ∂P, Q n (killedHistory W VL VR V ω) < V ω) ∧
        (∀ᵐ ω ∂P, Tendsto (fun n => Q n (killedHistory W VL VR V ω)) atTop (𝓝 (V ω)))

/-- The unchanged WFS target from strict Galmarino announcing rules and the
permitted Theorem 1.2/1.3 inputs. The announcing construction remains open. -/
theorem throughKernelStatement_of_strictRuleAnnounce
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    {κ : ℝ} (hκ : 0 < κ) (hA : StrictRuleAnnounceStatement.{u} κ) :
    ThroughKernelStatement.{u, u} κ := by
  apply throughKernelStatement_of_jointLaw h12 h13 hκ
  intro nL nR xL xR ρL ρR hF R hRm hRg Ω mΩ P hP 𝓕 W VL VR B ζ V h hC hV
    Ω₀ mΩ₀ P₀ hP₀ 𝓕₀ W₀ VL₀ VR₀ B₀ ζ₀ h₀ hC₀
  have hc : ∀ᵐ ω ∂P, IsKilledContHist (killedHistory W VL VR V ω) := by
    filter_upwards [hC.1.isSLEEvolutionUpTo.ae_path] with ω hp
    exact isKilledContHist_killedHistory ((continuousOn_state_of_isSLEPathUpTo hp).mono
      (fun t ht => ht.trans_le (hC.2.1 ω)))
  rcases ae_zero_or_ae_pos_of_selfRule hRg hc hV with hz | hp
  · exact map_field_ruleHistory_eq_of_zero hRg hC hV hz hC₀
  · obtain ⟨Q, hQ, hs, hstrict, hconv⟩ :=
      hA xL xR ρL ρR hF R hRm hRg P 𝓕 W VL VR B ζ V h hC hV hp
    exact map_field_ruleHistory_eq_of_regularApprox hκ hF
      (Exist.Param12.hasFieldDeterminedHistories h12 h13 hκ hF) hRm hC hC₀
      (hasRegularRuleApprox_of_strictRules hκ hF hRm hRg hC hV hQ hs hstrict hconv hC₀)

end InteractingSLE.WFS
