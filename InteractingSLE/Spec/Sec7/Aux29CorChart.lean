/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Aux29CorMob
import InteractingSLE.Spec.Sec7.PocketSideInSyncCharts
import InteractingSLE.Spec.Sec7.PocketStopSideEndGeometry

/-!
# The base chart of a late R.7 side target: conformality, lift, boundary extension, landing at `∞`

PROVE-AUX29-CORNER. For a late side test `j` with `j.Ready d`:

* **`SideTest.isConformal_baseChart_of_ready`**: the deterministic base-chart conformality, the
  `hChart` input of `lateSideCollar_of_incrementLaws` (PROVE-SIDE-LATCOL), at every sample, from
  `Ready` alone (no wall continuity);
* `SideTest.baseChart_aux29Facts`: the analytic lift `pLog`, the continuous extension of the inverse
  to `ℍ̄` (landed `exists_inverse_extension_of_jordan_cases`), and the landing at `∞` after `mob`;
* `Aux29Cor.tendsto_invFunOn_pole`, `Aux29Cor.tendsto_invFunOn_cobounded`: the inverse of a bounded
  Jordan coordinate tends to the pole (the outgoing corner), that of an unbounded one to `∞`.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology Metric Complex Bornology Function
open QuantumZipper (H Hbar)
open SupercriticalConformalCovariance (IsConformalBijection)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.Aux29Cor

/-! ### The inverse of a Jordan coordinate at `∞` -/

/-- **Bounded Jordan pocket**: the inverse of its coordinate tends to the pole (the outgoing corner)
as the half-plane point tends to `∞`. -/
theorem tendsto_invFunOn_pole {C : Set ℂ} {pole seed : ℂ} {ψ : ℂ → ℂ} (hCb : IsBounded C)
    (hψ : Sec6.IsJordanCoord C pole seed ψ) :
    Tendsto (invFunOn ψ C) (cobounded ℂ ⊓ 𝓟 H) (𝓝 pole) := by
  have hsurj := hψ.2.2.2.1.2.surjOn
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hS : IsCompact (closure C \ ball pole ε) :=
    hCb.isCompact_closure.diff isOpen_ball
  have hSsub : closure C \ ball pole ε ⊆ closure C \ {pole} := fun z hz =>
    ⟨hz.1, fun h => hz.2 (by rw [mem_singleton_iff.1 h]; exact mem_ball_self hε)⟩
  obtain ⟨R, hR⟩ := hS.exists_bound_of_continuousOn (hψ.1.mono hSsub)
  rw [(hasBasis_cobounded_norm.inf_principal H).eventually_iff]
  refine ⟨R + 1, trivial, fun w ⟨hwR, hwH⟩ => ?_⟩
  have hwR' : R + 1 ≤ ‖w‖ := hwR
  obtain ⟨hmem, hψw⟩ := invFunOn_pos (hsurj hwH)
  by_contra hfar
  have hz : invFunOn ψ C w ∈ closure C \ ball pole ε := ⟨subset_closure hmem, hfar⟩
  have := hR _ hz
  rw [hψw] at this
  linarith

/-- **Unbounded Jordan pocket**: the inverse of its coordinate tends to `∞`. -/
theorem tendsto_invFunOn_cobounded {C : Set ℂ} {seed : ℂ} {ψ : ℂ → ℂ}
    (hψ : Sec6.IsJordanCoordInf C seed ψ) :
    Tendsto (invFunOn ψ C) (cobounded ℂ ⊓ 𝓟 H) (cobounded ℂ) := by
  have hsurj := hψ.2.2.2.1.2.surjOn
  rw [← tendsto_norm_atTop_iff_cobounded, Filter.tendsto_atTop]
  intro R'
  have hS : IsCompact (closure C ∩ closedBall 0 R') :=
    (isCompact_closedBall 0 R').inter_left isClosed_closure
  obtain ⟨R, hR⟩ := hS.exists_bound_of_continuousOn (hψ.1.mono inter_subset_left)
  rw [(hasBasis_cobounded_norm.inf_principal H).eventually_iff]
  refine ⟨R + 1, trivial, fun w ⟨hwR, hwH⟩ => ?_⟩
  have hwR' : R + 1 ≤ ‖w‖ := hwR
  obtain ⟨hmem, hψw⟩ := invFunOn_pos (hsurj hwH)
  by_contra hnear
  have hz : invFunOn ψ C w ∈ closure C ∩ closedBall 0 R' :=
    ⟨subset_closure hmem, mem_closedBall_zero_iff.2 (le_of_lt (not_le.1 hnear))⟩
  have := hR _ hz
  rw [hψw] at this
  linarith

/-- `mob` tends to `0` at `∞`. -/
theorem tendsto_mob_cobounded : Tendsto mob (cobounded ℂ) (𝓝 0) := by
  have h1 : Tendsto (fun z : ℂ => z + I) (cobounded ℂ) (cobounded ℂ) := by
    rw [← tendsto_norm_atTop_iff_cobounded]
    have h := tendsto_atTop_add_const_right _ (-1 : ℝ)
      (tendsto_norm_cobounded_atTop (E := ℂ))
    refine tendsto_atTop_mono (fun z => ?_) h
    have := norm_sub_norm_le z (-I)
    rw [sub_neg_eq_add, norm_neg, Complex.norm_I] at this
    linarith
  exact tendsto_inv₀_cobounded.comp h1

/-- The landing at `∞` of a Jordan pocket coordinate's inverse, after `mob`. -/
theorem exists_tendsto_mob_invFunOn {C : Set ℂ} {seed : ℂ} {ψ : ℂ → ℂ} (hCH : C ⊆ H)
    (hJ : (∃ pole : ℂ, IsBounded C ∧ pole ∉ C ∧ Sec6.IsJordanCoord C pole seed ψ) ∨
      Sec6.IsJordanCoordInf C seed ψ) :
    ∃ p : ℂ, Tendsto (fun w => mob (invFunOn ψ C w)) (cobounded ℂ ⊓ 𝓟 H) (𝓝 p) := by
  rcases hJ with ⟨pole, hCb, -, hψ⟩ | hψ
  · have hlim := tendsto_invFunOn_pole hCb hψ
    have hpole : pole ∈ Hbar := by
      have := neBot_cobounded_inf_H
      have hcl : pole ∈ closure H := mem_closure_of_tendsto hlim
        (eventually_inf_principal.2 (Eventually.of_forall fun w hw =>
          hCH (invFunOn_pos (hψ.2.2.2.1.2.surjOn hw)).1))
      rwa [QuantumZipper.CA.Car.closure_H_eq_Hbar] at hcl
    exact ⟨mob pole, (continuousAt_mob hpole).tendsto.comp hlim⟩
  · exact ⟨0, tendsto_mob_cobounded.comp (tendsto_invFunOn_cobounded hψ)⟩

end InteractingSLE.Sec7.Aux29Cor

namespace InteractingSLE.Wire.Current.SideTest

open Sec7 Sec7.PocketStopField Sec7.PocketJordan Sec7.Aux29Cor

variable {Ω : Type} [MeasurableSpace Ω] {j : SideTest Ω} {i : BothLow} {d : WordObjects Ω}

/-- Every late side target's pocket lies in `ℍ`. -/
theorem domain_subset_H_of_ready (hj : j.Ready d) :
    ∀ ω ∈ (j.target i d).event, (j.target i d).domain ω ⊆ H := by
  rcases hj with ⟨-, -, -, hG, -, -, -, -, hAG, -⟩
  rw [target_event, target_domain]
  intro ω hω
  have hωG : ω ∈ j.outerEvent := by
    cases hI : j.infinite <;> simp only [hI, Bool.false_eq_true, ↓reduceIte] at hAG <;>
      exact (hAG hω).1
  exact image_negInv_subset_H (hG ω hωG).1.changePocket_subset_H

/-- The pocket coordinate is a conformal bijection of the pocket onto `ℍ`. -/
theorem isConformalBijection_chart_of_ready (hj : j.Ready d) :
    ∀ ω ∈ (j.target i d).event,
      IsConformalBijection ((j.target i d).chart ω) ((j.target i d).domain ω) H := by
  intro ω hω
  rcases jordan_cases hj ω hω with ⟨pole, -, -, hJ⟩ | hJ
  · exact hJ.2.2.2.1
  · exact hJ.2.2.2.1

/-- **The deterministic base-chart conformality** of the late side collar (`hChart` of
`lateSideCollar_of_incrementLaws`), at every sample, from `Ready` alone. -/
theorem isConformal_baseChart_of_ready (hj : j.Ready d) (ω : Ω) :
    ((j.target i d).baseChart ω).IsConformal :=
  (pChart_props (isOpen_domain (i := i) hj) (domain_subset_H_of_ready (i := i) hj)
    (isConformalBijection_chart_of_ready (i := i) hj) ω).2.2.1

/-- The base chart of a late side target: conformal with the analytic lift `pLog`, its inverse
extends continuously to `ℍ̄`, and its landing at `∞` (after `mob`) exists. -/
theorem baseChart_aux29Facts (hj : j.Ready d) {ω : Ω} (hω : ω ∈ (j.target i d).event) :
    (((j.target i d).baseChart ω).IsConformal ∧
      IsDerivLog ((j.target i d).baseChart ω).1
        (pLog (j.target i d).event (j.target i d).domain (j.target i d).chart ω)
        ((j.target i d).baseChart ω).dom ∧
      ∀ z ∈ ((j.target i d).baseChart ω).dom, ((j.target i d).baseChart ω).2.2 z =
        (pLog (j.target i d).event (j.target i d).domain (j.target i d).chart ω z).im) ∧
    (∃ E : ℂ → ℂ, EqOn E ((j.target i d).baseChart ω).2.1 H ∧ ContinuousOn E Hbar) ∧
    ∃ p : ℂ, Tendsto (fun w => mob (((j.target i d).baseChart ω).2.1 w))
      (Bornology.cobounded ℂ ⊓ 𝓟 H) (𝓝 p) := by
  have hprops := pChart_props (isOpen_domain (i := i) hj) (domain_subset_H_of_ready (i := i) hj)
    (isConformalBijection_chart_of_ready (i := i) hj) ω
  have hcc : ((j.target i d).baseChart ω).IsConformal := hprops.2.2.1
  have hdom : (((j.target i d).baseChart ω).dom : Set ℂ) = (j.target i d).domain ω := by
    change ((pChart (j.target i d).event (j.target i d).domain (j.target i d).chart ω).dom : Set ℂ) = _
    rw [hprops.2.2.2]
    ext z
    simp only [mem_ofPred_eq, hω, true_and, not_true_eq_false, false_and, or_false]
  have hfwd : EqOn ((j.target i d).baseChart ω).1 ((j.target i d).chart ω) ((j.target i d).domain ω) :=
    fun z _ => by
      change pFwd (j.target i d).event (j.target i d).chart ω z = _
      rw [pFwd_of_mem hω]
  have hinv : ((j.target i d).baseChart ω).2.1 =
      invFunOn ((j.target i d).chart ω) ((j.target i d).domain ω) := by
    change pInv (j.target i d).event (j.target i d).domain (j.target i d).chart ω = _
    rw [pInv_of_mem hω]
  have hlog := isDerivLog_pLog (isOpen_domain (i := i) hj) (isConformalBijection_chart_of_ready (i := i) hj) hω
  refine ⟨⟨hcc, hdom ▸ hlog, fun z _ => rfl⟩, ?_, ?_⟩
  · obtain ⟨E, hE, hEc, -⟩ := PocketStopSide.exists_inverse_extension_of_jordan_cases
      (jordan_cases hj ω hω) hcc hdom hfwd
    exact ⟨E, hE, hEc⟩
  · rw [hinv]
    exact exists_tendsto_mob_invFunOn (domain_subset_H_of_ready hj ω hω) (jordan_cases hj ω hω)

end InteractingSLE.Wire.Current.SideTest
