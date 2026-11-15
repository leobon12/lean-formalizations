/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SxTimeVer

/-!
# GW2's stage identity: exhausting announced versions up to a physical time, for any explored curve

Packet PROVE-GW2-RELDET, ruling R106.

* `exists_versionsA_uncapped`: `GW2SvVer.exists_versionsA_of_capGauge` with the constant gauge `1` and life `⊤`. It
  gives exhausting announced R-form GB6 versions up to the first contact, for ANY explored curve with a transient
  generating trace on `[0, ∞)`. No cap gauge is needed: the explored curve is defined after its program end (frozen
  extension), and its pieces' deaths do not enter the relative exploration.
* `exists_versionsA_timeCap`: the same versions stopped at the physical time `Δ > 0` (`GW2SxTimeVer`). The stops lie
  below `capClock Δ` (the relative clock of `Δ` if `Δ` precedes the contact). Every relative clock value of a
  physical time before both the contact and `Δ` is below some stop.

These are the versions of a stage `[T, Δ)` of the explored schedule for the stage chain
(`GW2SkStep.ae_isStopDrvMatch_stage_aug` at the stage start `T`). There is no hypothesis beyond the regularity of the
two curves. Conditional helpers with distinct names.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (DistOn)

namespace InteractingSLE.Theorem14.GW2Rd

open Supp8 Supp8.GB6 Supp8.GB6.RelDrv Supp8.GB6.HullId

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {κ θ : ℝ} {b : ℝ → ℝ}
  {J : Finset ℝ} {h : Ω → DistOn upperHalfPlaneOpens} {W Wα : ℝ≥0 → Ω → ℝ} {ζα : Ω → ℝ≥0∞} {γ α : Ω → ℝ≥0 → ℂ}

/-- **Exhausting announced GB6 versions for any transient explored curve, with no cap.** -/
theorem exists_versionsA_uncapped (hF : IsFlowLineDriver κ b J θ P h Wα ζα)
    (hα : ∀ᵐ ω ∂P, IsGeneratingTrace (Wα · ω) (ζα ω) (α ω))
    (hNR : ∀ᵐ ω ∂P, ∀ α' : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => Wα t ω) (ζα ω) α' →
      ∀ v : ℝ≥0, 0 < v → (v : ℝ≥0∞) < ζα ω → α' v ≠ 0)
    (hWm : ∀ t, Measurable (W t))
    (hW : ∀ᵐ ω ∂P, Continuous (W · ω) ∧ W 0 ω = 0 ∧ IsGeneratingTrace (W · ω) ⊤ (γ ω) ∧
      Tendsto (fun t => ‖γ ω t‖) atTop atTop)
    (s : ℝ≥0) (hs : 0 < s) :
    ∃ (R : ℕ → ℝ≥0 → Ω → ℝ) (V : ℕ → Ω → ℝ≥0∞),
      (∀ m, Q3Stop.IsGB6RelVersionA s P W Wα ζα γ α (R m) (V m)) ∧
      ∀ᵐ ω ∂P, (s : ℝ≥0∞) < ζα ω → α ω s ∈ H → ∀ t : ℝ≥0, (t : ℝ≥0∞) < gb6Tc s γ α ω →
        ∃ m, ENNReal.ofReal (gb6Clock s W Wα ω t) < V m ω := by
  obtain ⟨R, V, hRV, -, hex⟩ := exists_versionsA_of_capGauge hF hα hNR hWm hW s hs
    (Gζ := fun _ _ => 1) (fun _ => measurable_const) (fun _ _ _ _ _ => rfl) (fun _ _ => zero_le_one)
    (Lζ := fun _ => ⊤) fun _ _ _ => ae_of_all _ fun _ _ =>
      ⟨ENNReal.zero_lt_top, continuousOn_const, fun _ _ _ => zero_lt_one, fun _ _ ht => absurd ht ENNReal.coe_ne_top⟩
  exact ⟨R, V, hRV, hex.mono fun ω hω hs' hsH t ht => hω hs' hsH t ht ENNReal.ofReal_lt_top⟩

/-- **Exhausting announced GB6 versions stopped at the physical time `Δ`, for any transient explored curve.** -/
theorem exists_versionsA_timeCap (hF : IsFlowLineDriver κ b J θ P h Wα ζα)
    (hα : ∀ᵐ ω ∂P, IsGeneratingTrace (Wα · ω) (ζα ω) (α ω))
    (hNR : ∀ᵐ ω ∂P, ∀ α' : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => Wα t ω) (ζα ω) α' →
      ∀ v : ℝ≥0, 0 < v → (v : ℝ≥0∞) < ζα ω → α' v ≠ 0)
    (hWm : ∀ t, Measurable (W t))
    (hW : ∀ᵐ ω ∂P, Continuous (W · ω) ∧ W 0 ω = 0 ∧ IsGeneratingTrace (W · ω) ⊤ (γ ω) ∧
      Tendsto (fun t => ‖γ ω t‖) atTop atTop)
    (s : ℝ≥0) (hs : 0 < s) {Δ : ℝ≥0} (hΔ : 0 < Δ) :
    ∃ (R : ℕ → ℝ≥0 → Ω → ℝ) (V : ℕ → Ω → ℝ≥0∞),
      (∀ m, Q3Stop.IsGB6RelVersionA s P W Wα ζα γ α (R m) (V m)) ∧
      (∀ᵐ ω ∂P, (s : ℝ≥0∞) < ζα ω → α ω s ∈ H → ∀ m, V m ω ≤ capClock (gb6Tc s γ α ω) (gb6Clock s W Wα ω) Δ) ∧
      ∀ᵐ ω ∂P, (s : ℝ≥0∞) < ζα ω → α ω s ∈ H → ∀ t : ℝ≥0, (t : ℝ≥0∞) < gb6Tc s γ α ω → t < Δ →
        ∃ m, ENNReal.ofReal (gb6Clock s W Wα ω t) < V m ω := by
  obtain ⟨R₀, V₀, hRV, hex⟩ := exists_versionsA_uncapped hF hα hNR hWm hW s hs
  have hW' : ∀ᵐ ω ∂P, Continuous (W · ω) ∧ W 0 ω = 0 ∧ IsGeneratingTrace (W · ω) ⊤ (γ ω) :=
    hW.mono fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩
  have hcap := fun m => isGB6RelVersionA_timeCap hF hα hW' (hRV m) hΔ
  have hcapae : ∀ᵐ ω ∂P, ∀ m, (s : ℝ≥0∞) < ζα ω → α ω s ∈ H →
      ruleCapStop s Wα ζα (timeCapRule s Δ) (R₀ m) (V₀ m) ω =
        min (V₀ m ω) (capClock (gb6Tc s γ α ω) (gb6Clock s W Wα ω) Δ) := ae_all_iff.2 fun m => (hcap m).2
  refine ⟨fun m => ruleCapDrv (R₀ m) (ruleCapStop s Wα ζα (timeCapRule s Δ) (R₀ m) (V₀ m)),
    fun m => ruleCapStop s Wα ζα (timeCapRule s Δ) (R₀ m) (V₀ m), fun m => (hcap m).1, ?_, ?_⟩
  · filter_upwards [hcapae] with ω hω hs' hsH m
    rw [hω m hs' hsH]
    exact min_le_right _ _
  · filter_upwards [hcapae, hex, ae_timeCap_sample hF hα hW' (hRV 0).1.1] with ω hω hexω hsam hs' hsH t ht htΔ
    obtain ⟨-, ha0, ham, -, -, -⟩ := hsam hs' hsH
    obtain ⟨m, hm⟩ := hexω hs' hsH t ht
    refine ⟨m, ?_⟩
    rw [hω m hs' hsH]
    refine lt_min hm ?_
    unfold capClock
    split_ifs with hΔT
    · have h0T : ((0 : ℝ≥0) : ℝ≥0∞) < gb6Tc s γ α ω := (ENNReal.coe_le_coe.2 zero_le).trans_lt ht
      have hat : 0 ≤ gb6Clock s W Wα ω t := by
        rw [← ha0]
        exact ham.monotoneOn h0T ht zero_le
      have htΔ' := ham ht hΔT htΔ
      exact (ENNReal.ofReal_lt_ofReal_iff (hat.trans_lt htΔ')).2 htΔ'
    · exact ENNReal.ofReal_lt_top

end InteractingSLE.Theorem14.GW2Rd
