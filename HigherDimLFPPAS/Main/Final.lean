import HigherDimLFPPAS.Main.Assembly
import HigherDimLFPPAS.Localize.Lemma24
import HigherDimLFPPAS.Annulus.Marginal
import HigherDimLFPPAS.Endpoint.Lemma61
import HigherDimLFPPAS.Endpoint.Lemma62

/-!
# Final composition of the almost-sure convergence theorem

This module replaces the three remaining rescaling interfaces by their producer hypotheses and
composes the landed deterministic, endpoint, localization, and annulus producers.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace HigherDimLFPPAS.Main

open HigherDimLQGMetric HigherDimLFPPAS.Core
open HigherDimLQGContinuity
open HigherDimLFPPAS
open HigherDimLFPP (Rd)

private theorem l24_adapter :
    ∀ {d : ℕ} {ξ Q : ℝ} {κ : Rd d → ℝ} {D : DistRd d → ContMetric d}
      {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
      {h : Ω → DistRd d}, Core.Setting d ξ Q κ D P h → Core.Lemma23i κ P h →
      Core.Lemma24Conv κ ξ D P h ∧ Core.Lemma24Confine κ ξ P h := by
  intro d ξ Q κ D Ω _ P _ h hS h23i
  exact Localize.lemma24_holds hS h23i

private theorem l32p_adapter
    (hP : ∀ {d : ℕ} {ξ Q : ℝ} {κ : Rd d → ℝ} {D : DistRd d → ContMetric d}
      {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
      {h : Ω → DistRd d}, Core.Setting d ξ Q κ D P h → Core.PairLaw κ ξ D P h)
    (hL : ∀ {d : ℕ} {ξ Q : ℝ} {κ : Rd d → ℝ} {D : DistRd d → ContMetric d}
      {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
      {h : Ω → DistRd d}, Core.Setting d ξ Q κ D P h → Core.RescaledLoc κ P h)
    (hC : ∀ {d : ℕ} {ξ Q : ℝ} {κ : Rd d → ℝ} {D : DistRd d → ContMetric d}
      {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
      {h : Ω → DistRd d}, Core.Setting d ξ Q κ D P h → Core.RescaledLoc κ P h →
      Core.RescaledConv κ ξ D P h) :
    ∀ {d : ℕ} {ξ Q : ℝ} {κ : Rd d → ℝ} {D : DistRd d → ContMetric d}
      {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
      {h : Ω → DistRd d}, Core.Setting d ξ Q κ D P h →
      Core.PairLaw κ ξ D P h ∧ Core.RescaledConv κ ξ D P h ∧
        (Core.LocFieldScaling κ → Core.CoordScaling ξ Q D P h →
          Core.AffineInternalScaling d → Core.PairLaw κ ξ D P h →
          Core.RescaledConv κ ξ D P h → Core.Lemma32Marginal κ ξ Q D P h) := by
  intro d ξ Q κ D Ω _ P _ h hS
  have hloc : Core.RescaledLoc κ P h := hL hS
  have hconv : Core.RescaledConv κ ξ D P h := hC hS hloc
  refine ⟨hP hS, hconv, ?_⟩
  intro hsc hcs hai hpl hrc
  exact Annulus.lemma32Marginal_holds hS hsc hcs hai hpl hrc

private theorem l61_adapter :
    ∀ {d : ℕ} {ξ Q : ℝ} {κ : Rd d → ℝ} {D : DistRd d → ContMetric d}
      {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
      {h : Ω → DistRd d}, Core.Setting d ξ Q κ D P h → Core.Lemma27Stmt κ ξ D P h →
      Core.Lemma23ii κ P h → Core.Lemma25Exponent κ ξ Q → Core.Lemma61Stmt κ ξ D P h := by
  intro d ξ Q κ D Ω _ P _ h hS h27 h23ii h25
  exact Endpoint.lemma61_holds hS h27 h23ii h25

private theorem l62_adapter :
    ∀ {d : ℕ} {ξ Q : ℝ} {κ : Rd d → ℝ} {D : DistRd d → ContMetric d}
      {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
      {h : Ω → DistRd d}, Core.Setting d ξ Q κ D P h → Core.Lemma61Stmt κ ξ D P h →
      Core.Lemma27Stmt κ ξ D P h → Core.Lemma23i κ P h → Core.Lemma23iii κ P h →
      Core.Lemma25Window κ ξ → Core.Lemma62Stmt κ ξ P h := by
  intro d ξ Q κ D Ω _ P _ h hS h61 h27 h23i h23iii _
  exact Endpoint.lemma62_holds hS h61 h27 h23i h23iii (Glue.lemma25_holds hS).2.1

/-- The frozen almost-sure convergence theorem from the three rescaling producers. -/
theorem asConvergence_of_rz
    (hP : ∀ {d : ℕ} {ξ Q : ℝ} {κ : Rd d → ℝ} {D : DistRd d → ContMetric d}
      {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
      {h : Ω → DistRd d}, Core.Setting d ξ Q κ D P h → Core.PairLaw κ ξ D P h)
    (hL : ∀ {d : ℕ} {ξ Q : ℝ} {κ : Rd d → ℝ} {D : DistRd d → ContMetric d}
      {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
      {h : Ω → DistRd d}, Core.Setting d ξ Q κ D P h → Core.RescaledLoc κ P h)
    (hC : ∀ {d : ℕ} {ξ Q : ℝ} {κ : Rd d → ℝ} {D : DistRd d → ContMetric d}
      {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
      {h : Ω → DistRd d}, Core.Setting d ξ Q κ D P h → Core.RescaledLoc κ P h →
      Core.RescaledConv κ ξ D P h) :
    ∀ (d : ℕ) (ξ : ℝ), 3 ≤ d → 0 < ξ →
      ∀ κ : Rd d → ℝ, IsAdmissibleSeed κ →
      ∀ D : DistRd d → ContMetric d,
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistRd d), IsNormalizedLGF h P → Assumption11 d ξ κ D P h →
        ∀ᵐ ω ∂P, ∀ F : Set (Rd d), IsCompact F →
          Tendsto (fun ε : ℝ => ⨆ p ∈ F ×ˢ F,
            edist (((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω)) p) ((D (h ω)).1 p))
            (𝓝[>] 0) (𝓝 0) := by
  exact HigherDimLFPPAS.asConvergence_of_remaining l24_adapter
    (l32p_adapter hP hL hC) l61_adapter l62_adapter

/-- The frozen unconditional theorem for nonnegative seeds from the three rescaling producers. -/
theorem asConvergence_nonneg_of_rz
    (hP : ∀ {d : ℕ} {ξ Q : ℝ} {κ : Rd d → ℝ} {D : DistRd d → ContMetric d}
      {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
      {h : Ω → DistRd d}, Core.Setting d ξ Q κ D P h → Core.PairLaw κ ξ D P h)
    (hL : ∀ {d : ℕ} {ξ Q : ℝ} {κ : Rd d → ℝ} {D : DistRd d → ContMetric d}
      {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
      {h : Ω → DistRd d}, Core.Setting d ξ Q κ D P h → Core.RescaledLoc κ P h)
    (hC : ∀ {d : ℕ} {ξ Q : ℝ} {κ : Rd d → ℝ} {D : DistRd d → ContMetric d}
      {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
      {h : Ω → DistRd d}, Core.Setting d ξ Q κ D P h → Core.RescaledLoc κ P h →
      Core.RescaledConv κ ξ D P h) :
    ∀ (d : ℕ) (ξ : ℝ), 3 ≤ d → 0 < ξ → Real.sqrt (2 * d) < distExp d ξ →
    ∃ D : DistRd d → ContMetric d, IsStrongExpMetric d ξ (distExp d ξ) D ∧
      HigherDimLQGContinuity.IsMedianOne d D ∧
      ∀ κ : Rd d → ℝ, HigherDimLFPP.IsLFPPKernel κ →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistRd d), IsNormalizedLGF h P →
        ∀ᵐ ω ∂P, ∀ F : Set (Rd d), IsCompact F →
          Tendsto (fun ε : ℝ => ⨆ p ∈ F ×ˢ F,
            edist (((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω)) p) ((D (h ω)).1 p))
            (𝓝[>] 0) (𝓝 0) := by
  exact HigherDimLFPPAS.asConvergence_nonneg_of_remaining l24_adapter
    (l32p_adapter hP hL hC) l61_adapter l62_adapter

/-- The frozen theorem for every median-one strong limit from the three rescaling producers. -/
theorem asConvergence_medianOne_of_rz
    (hP : ∀ {d : ℕ} {ξ Q : ℝ} {κ : Rd d → ℝ} {D : DistRd d → ContMetric d}
      {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
      {h : Ω → DistRd d}, Core.Setting d ξ Q κ D P h → Core.PairLaw κ ξ D P h)
    (hL : ∀ {d : ℕ} {ξ Q : ℝ} {κ : Rd d → ℝ} {D : DistRd d → ContMetric d}
      {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
      {h : Ω → DistRd d}, Core.Setting d ξ Q κ D P h → Core.RescaledLoc κ P h)
    (hC : ∀ {d : ℕ} {ξ Q : ℝ} {κ : Rd d → ℝ} {D : DistRd d → ContMetric d}
      {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
      {h : Ω → DistRd d}, Core.Setting d ξ Q κ D P h → Core.RescaledLoc κ P h →
      Core.RescaledConv κ ξ D P h) :
    ∀ (d : ℕ) (ξ : ℝ), 3 ≤ d → 0 < ξ → Real.sqrt (2 * d) < distExp d ξ →
    ∀ D : DistRd d → ContMetric d, IsStrongExpMetric d ξ (distExp d ξ) D →
      HigherDimLQGContinuity.IsMedianOne d D →
      ∀ κ : Rd d → ℝ, HigherDimLFPP.IsLFPPKernel κ →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistRd d), IsNormalizedLGF h P →
        ∀ᵐ ω ∂P, ∀ F : Set (Rd d), IsCompact F →
          Tendsto (fun ε : ℝ => ⨆ p ∈ F ×ˢ F,
            edist (((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω)) p) ((D (h ω)).1 p))
            (𝓝[>] 0) (𝓝 0) := by
  exact HigherDimLFPPAS.asConvergence_medianOne_of_remaining l24_adapter
    (l32p_adapter hP hL hC) l61_adapter l62_adapter

end HigherDimLFPPAS.Main
