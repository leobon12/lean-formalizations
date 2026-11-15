/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FlowStopIdentCMIConvWDriver

/-!
# Clock assembly after the two exit predictability constructions

The remaining statements concern the exit and its announcements only. Driver
regularization, path data, threshold locality and killed measurability are proved.
Neither remaining construction is asserted as an unconditional theorem here.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
universe u
namespace InteractingSLE.Restart.FlowStopIdentCMI
open Sec7.PocketTraversal

/-- Remaining source-filtration predictability construction for the raw trace exit. -/
def CMIWSourceAnnounceStatement : Prop :=
  ∀ {S : Type u} [MeasurableSpace S] (D : CMIVSetting S),
    ¬ FlowStopIdentG.SeedStop D.κ D.b D.J D.y D.θ D.V →
    ∃ e : S → ℝ≥0∞, Measurable e ∧
      (e =ᵐ[D.Q₀] fun ω => RLC.exitTime D.V (D.Γ ω) (D.U ω)) ∧
      IsStoppingTime D.driving (fun ω => (e ω : WithTop ℝ≥0)) ∧
      ∃ T : ℕ → S → ℝ≥0, Coupling.IsAnnouncingSeq D.driving D.Q₀ e T

/-- Remaining reference-filtration predictability construction. The conclusion
is an announcing sequence, not an evolution or a comparison coupling. -/
def CMIWReferenceAnnounceStatement : Prop :=
  ∀ {S : Type u} [MeasurableSpace S] (D : CMIVSetting S) (e : S → ℝ≥0∞) (W : ℝ≥0 → S → ℝ),
    (e =ᵐ[D.Q₀] fun ω => RLC.exitTime D.V (D.Γ ω) (D.U ω)) →
    (∀ ω, W 0 ω = 0) → (∀ ω, Continuous (W · ω)) →
    (∀ᵐ ω ∂D.Q₀, ∀ t : ℝ≥0, (t : ℝ≥0∞) < e ω → W t ω = D.W₀ t ω) →
    (∀ᵐ ω ∂D.Q₀, 0 < e ω) →
    ∀ hX : IsMeasurableKilledDriving W (geomLW W fun _ => flowLineXL D.bR D.JR D.y)
      (geomRW W fun _ => flowLineXR D.bR D.JR D.y) e,
    ∃ σ : ℕ → S → WithTop ℝ≥0,
      (∀ n, IsStoppingTime (drivingFiltration D.Q₀ hX) (σ n)) ∧
      (∀ ω, Monotone fun n => σ n ω) ∧
      (∀ᵐ ω ∂D.Q₀, ∀ n, (σ n ω : ℝ≥0∞) < e ω) ∧
      ∀ᵐ ω ∂D.Q₀, Tendsto (fun n => (σ n ω : ℝ≥0∞)) atTop (𝓝 (e ω))

namespace CMIVSetting
variable {S : Type u} [MeasurableSpace S] (D : CMIVSetting S)

/-- The landed deterministic theorem gives every path-data clause for any
continuous driver agreeing before the measurable exit. -/
theorem pathData_of_agree {e : S → ℝ≥0∞} {W : ℝ≥0 → S → ℝ}
    (he : e =ᵐ[D.Q₀] fun ω => RLC.exitTime D.V (D.Γ ω) (D.U ω))
    (hWc : ∀ ω, Continuous (W · ω))
    (hag : ∀ᵐ ω ∂D.Q₀, ∀ t : ℝ≥0, (t : ℝ≥0∞) < e ω → W t ω = D.W₀ t ω)
    (τ : S → WithTop ℝ≥0) (hlt : ∀ᵐ ω ∂D.Q₀, (τ ω : ℝ≥0∞) < e ω) :
    ∀ᵐ ω ∂D.Q₀, StopPathData D.b D.J D.y D.N D.W₀ W D.VL₀ D.VR₀ τ ω := by
  filter_upwards [he, hag, D.coupling.1.ae_isIntegratedSLEPath, D.trace, hlt]
    with ω heω hagω hp hg hτω
  have ht := FlowStopIdentCM.coe_untopD_lt hτω
  have hag' : ∀ t : ℝ≥0, (t : ℝ≥0∞) < RLC.exitTime D.V (D.Γ ω) (D.U ω) →
      W t ω = D.W₀ t ω := fun t ht => hagω t (heω ▸ ht)
  exact ⟨hWc ω, stopPathData_det D.V_bounded D.closureV_real D.hull_subset
    hp hg (hWc ω) hag' (heω ▸ ht)⟩

end CMIVSetting

/-- All other fields of the positive clock follow from the two precise exit
announcement constructions. In particular the threshold bound is no longer an input. -/
theorem cmiVPositiveClockStatement_of_announcements
    (hsource : CMIWSourceAnnounceStatement.{u}) (hreference : CMIWReferenceAnnounceStatement.{u}) :
    CMIVPositiveClockStatement.{u} := by
  intro S mS D hseed
  obtain ⟨e, hem, he, hes, T, hT⟩ := hsource D hseed
  obtain ⟨W, hW0, hWc, hWa, hag⟩ := D.exists_adapted_driver_of_announced_exit he hes hT
  have hXP : IsMeasurableKilledDriving W (geomLW W fun _ => flowLineXL D.bR D.JR D.y)
      (geomRW W fun _ => flowLineXR D.bR D.JR D.y) e := Coupling.isMeasurableKilledDriving_of_adaptedBefore
    (MartChar.adaptedBefore_of_stronglyAdapted hes hWa)
    (fun i => MartChar.adaptedBefore_of_stronglyAdapted hes
      (stronglyAdapted_geomLW hWa hWc measurable_const i))
    (fun j => MartChar.adaptedBefore_of_stronglyAdapted hes
      (stronglyAdapted_geomRW hWa hWc measurable_const j))
  have hpos : ∀ᵐ ω ∂D.Q₀, 0 < e ω :=
    (hT.2.2.1 0).mono fun _ h => lt_of_le_of_lt bot_le h
  obtain ⟨σ, hσ, hσm, hσlt, hσlim⟩ := hreference D e W he hW0 hWc hag hpos hXP
  exact ⟨{
    e := e
    measurable := hem
    ae_exit := he
    W := W
    zero := hW0
    continuous := hWc
    adapted := hWa
    stopping := hes
    announce := T
    announcing := hT
    pathData := fun τ _ hlt => D.pathData_of_agree he hWc hag τ hlt
    threshold := D.threshold_of_agree he hW0 hWc hag
    killed := hXP
    σ := σ
    σ_stopping := hσ
    σ_monotone := hσm
    σ_lt := hσlt
    σ_limit := hσlim }⟩

end InteractingSLE.Restart.FlowStopIdentCMI
