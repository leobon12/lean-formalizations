/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FlowStopIdentLL
import InteractingSLE.Foundations.Loewner.FiniteEndpointStatement
import InteractingSLE.Spec.Sec2.Assembly2Close
import InteractingSLE.Spec.Sec7.LocalExtFHist

/-!
# Continuous state versions at a finite lifetime

Packet PROVE-L1-LL. The frozen integrated paths specify values strictly before
their lifetime; arbitrary supplied endpoint values need not be continuous.
The existing measurable `LocalExt.stopVal` instead takes dyadic left limits.
Here it is identified with `Sec2.closeAt` when a terminal limit exists, and its
continuity and threshold state are proved from the existing terminal-limit API.
No endpoint continuity of the unmodified paths is asserted.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Restart.FlowStopIdentLL

open Sec2 Sec7 LocalExt

/-- The existing closed path is continuous when the one-sided limit exists. -/
theorem continuous_closeAt_of_tendsto {T : ℝ≥0} {f : ℝ≥0 → ℝ} {c : ℝ}
    (hc : ContinuousOn f (Iio T)) (hlim : Tendsto f (𝓝[<] T) (𝓝 c)) :
    Continuous (closeAt T f c) := by
  change Continuous (fun t => if t < T then f t else c)
  have h := (FiniteEndpoint.continuous_extDriver hc hlim).comp NNReal.continuous_coe
  simpa only [Function.comp_def, FiniteEndpoint.extDriver, Real.toNNReal_coe] using h

/-- At a finite positive stop with a left limit, the measurable stopped reader
equals the original path before the stop and its limit from the stop on. -/
theorem stopVal_eq_closeAt_of_tendsto {Ω : Type*} {X : ℝ≥0 → Ω → ℝ}
    {S : Ω → WithTop ℝ≥0} {ω : Ω} {T : ℝ≥0} {c : ℝ}
    (hT : 0 < T) (hS : S ω = T) (hlim : Tendsto (X · ω) (𝓝[<] T) (𝓝 c))
    (q : ℝ≥0) : stopVal X S q ω = closeAt T (X · ω) c q := by
  have hlow : ∀ n, lowVal X S n ω = X (lowApprox n T) ω := by
    intro n
    have hlt : (lowApprox n ((S ω).untopD 0) : WithTop ℝ≥0) < S ω := by
      rw [hS, WithTop.untopD_coe]
      exact WithTop.coe_lt_coe.2 (lowApprox_lt hT n)
    rw [lowVal, ite_eq_left hlt, hS, WithTop.untopD_coe]
  have hseq : Tendsto (fun n => lowApprox n T) atTop (𝓝[<] T) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_lowApprox T,
      Eventually.of_forall (lowApprox_lt hT)⟩
  have hval : (limUnder atTop fun n => lowVal X S n ω) = c := by
    simp_rw [hlow]
    exact (hlim.comp hseq).limUnder_eq
  unfold stopVal closeAt
  rw [hS]
  simp only [WithTop.coe_lt_coe, hval]

/-- The measurable stopped version is continuous through a finite positive
lifetime whenever the original coordinate has a left limit there. -/
theorem continuous_stopVal_of_tendsto {Ω : Type*} {X : ℝ≥0 → Ω → ℝ}
    {S : Ω → WithTop ℝ≥0} {ω : Ω} {T : ℝ≥0} {c : ℝ}
    (hT : 0 < T) (hS : S ω = T) (hc : ContinuousOn (X · ω) (Iio T))
    (hlim : Tendsto (X · ω) (𝓝[<] T) (𝓝 c)) :
    Continuous (stopVal X S · ω) := by
  have heq : (stopVal X S · ω) = closeAt T (X · ω) c :=
    funext (stopVal_eq_closeAt_of_tendsto hT hS hlim)
  rw [heq]
  exact continuous_closeAt_of_tendsto hc hlim

section State

variable {nL nR : ℕ} {Ω : Type*} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {ω : Ω} {T : ℝ≥0} {w₀ : ℝ}
  {vL₀ : Fin nL → ℝ} {vR₀ : Fin nR → ℝ}

/-- The dyadic stopped reader of a state is globally continuous, including the
terminal time, if the state is continuous before it and has a terminal limit. -/
theorem continuous_stopVal_state_of_tendsto (hT : 0 < T) (hζ : (T : ℝ≥0∞) = ζ ω)
    (hc : ContinuousOn (fun t => (W t ω, fun i => VL i t ω, fun j => VR j t ω))
      {t | (t : ℝ≥0∞) < ζ ω})
    (hlim : Tendsto (fun t => (W t ω, fun i => VL i t ω, fun j => VR j t ω))
      (𝓝[<] T) (𝓝 (w₀, vL₀, vR₀))) :
    Continuous (fun t => (stopVal W (fun x => (ζ x : WithTop ℝ≥0)) t ω,
      fun i => stopVal (VL i) (fun x => (ζ x : WithTop ℝ≥0)) t ω,
      fun j => stopVal (VR j) (fun x => (ζ x : WithTop ℝ≥0)) t ω)) := by
  have hset : {t : ℝ≥0 | (t : ℝ≥0∞) < ζ ω} = Iio T := by
    rw [← hζ]
    exact setOf_lt_coe_eq_Iio T
  rw [hset] at hc
  have hS : (fun x => (ζ x : WithTop ℝ≥0)) ω = T := hζ.symm
  have hwc := continuous_fst.comp_continuousOn hc
  have hLc := continuous_fst.comp_continuousOn (continuous_snd.comp_continuousOn hc)
  have hRc := continuous_snd.comp_continuousOn (continuous_snd.comp_continuousOn hc)
  have hwlim := (continuous_fst.tendsto _).comp hlim
  have hLlim := ((continuous_fst.comp continuous_snd).tendsto _).comp hlim
  have hRlim := ((continuous_snd.comp continuous_snd).tendsto _).comp hlim
  exact (continuous_stopVal_of_tendsto hT hS hwc hwlim).prodMk
    ((continuous_pi fun i => continuous_stopVal_of_tendsto hT hS
      ((continuousOn_pi.1 hLc) i) (((continuous_apply i).tendsto _).comp hLlim)).prodMk
    (continuous_pi fun j => continuous_stopVal_of_tendsto hT hS
      ((continuousOn_pi.1 hRc) j) (((continuous_apply j).tendsto _).comp hRlim)))

/-- The stopped reader takes the terminal limit as its terminal state. -/
theorem stopVal_state_at_lifetime (hT : 0 < T) (hζ : (T : ℝ≥0∞) = ζ ω)
    (hlim : Tendsto (fun t => (W t ω, fun i => VL i t ω, fun j => VR j t ω))
      (𝓝[<] T) (𝓝 (w₀, vL₀, vR₀))) :
    (stopVal W (fun x => (ζ x : WithTop ℝ≥0)) T ω,
      fun i => stopVal (VL i) (fun x => (ζ x : WithTop ℝ≥0)) T ω,
      fun j => stopVal (VR j) (fun x => (ζ x : WithTop ℝ≥0)) T ω) =
        (w₀, vL₀, vR₀) := by
  have hS : (fun x => (ζ x : WithTop ℝ≥0)) ω = T := hζ.symm
  have hwlim := (continuous_fst.tendsto _).comp hlim
  have hLlim := ((continuous_fst.comp continuous_snd).tendsto _).comp hlim
  have hRlim := ((continuous_snd.comp continuous_snd).tendsto _).comp hlim
  apply Prod.ext
  · change stopVal W (fun x => (ζ x : WithTop ℝ≥0)) T ω = w₀
    rw [stopVal_eq_closeAt_of_tendsto (S := fun x => (ζ x : WithTop ℝ≥0))
      hT hS hwlim, closeAt_self]
  · apply Prod.ext
    · funext i
      change stopVal (VL i) (fun x => (ζ x : WithTop ℝ≥0)) T ω = vL₀ i
      rw [stopVal_eq_closeAt_of_tendsto (S := fun x => (ζ x : WithTop ℝ≥0)) hT hS
        (((continuous_apply i).tendsto _).comp hLlim), closeAt_self]
      rfl
    · funext j
      change stopVal (VR j) (fun x => (ζ x : WithTop ℝ≥0)) T ω = vR₀ j
      rw [stopVal_eq_closeAt_of_tendsto (S := fun x => (ζ x : WithTop ℝ≥0)) hT hS
        (((continuous_apply j).tendsto _).comp hRlim), closeAt_self]
      rfl

end State

section Preservation

variable {Ω : Type*} {ζ : Ω → ℝ≥0∞} {ω : Ω}

/-- The stopped reader leaves every strictly pre-lifetime value unchanged. -/
theorem stopVal_of_lt {X : ℝ≥0 → Ω → ℝ} {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < ζ ω) :
    stopVal X (fun x => (ζ x : WithTop ℝ≥0)) t ω = X t ω := by
  have ht' : (t : WithTop ℝ≥0) < (ζ ω : WithTop ℝ≥0) := ht
  exact ite_eq_left ht'

/-- At a positive lifetime, replacing the coordinates by their measurable
stopped versions preserves the complete frozen integrated-path predicate. -/
theorem isIntegratedSLEPath_stopVal_of_pos {κ : ℝ} {nL nR : ℕ}
    {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {β : ℝ≥0 → ℝ}
    (hp : IsIntegratedSLEPath κ xL xR ρL ρR (W · ω)
      (fun i t => VL i t ω) (fun j t => VR j t ω) β (ζ ω)) (hpos : 0 < ζ ω) :
    IsIntegratedSLEPath κ xL xR ρL ρR
      (fun t => stopVal W (fun x => (ζ x : WithTop ℝ≥0)) t ω)
      (fun i t => stopVal (VL i) (fun x => (ζ x : WithTop ℝ≥0)) t ω)
      (fun j t => stopVal (VR j) (fun x => (ζ x : WithTop ℝ≥0)) t ω) β (ζ ω) := by
  have h0 : ((0 : ℝ≥0) : ℝ≥0∞) < ζ ω := hpos
  exact Sec2.Assembly.isIntegratedSLEPath_congr hp (stopVal_of_lt h0)
    (fun _ => stopVal_of_lt h0) (fun _ => stopVal_of_lt h0)
    (fun _ ht => stopVal_of_lt ht) (fun _ ht _ => stopVal_of_lt ht)
    (fun _ ht _ => stopVal_of_lt ht) (fun _ _ => rfl)

/-- Closing the driver by the stopped reader preserves every generating trace:
the filled hulls in the frozen predicate are only asserted before the lifetime. -/
theorem isGeneratingTrace_stopVal {W : ℝ≥0 → Ω → ℝ} {η : ℝ≥0 → ℂ}
    (hη : IsGeneratingTrace (W · ω) (ζ ω) η) :
    IsGeneratingTrace (fun t => stopVal W (fun x => (ζ x : WithTop ℝ≥0)) t ω)
      (ζ ω) η := by
  refine ⟨hη.1, hη.2.1, fun t ht => ?_⟩
  obtain ⟨p, htp, hpζ⟩ := FlowStopIdentG.exists_dyadicTime_btwn ht
  have hHull : QuantumZipper.fwdHull
      (fun s : ℝ => stopVal W (fun x => (ζ x : WithTop ℝ≥0)) s.toNNReal ω) t =
      QuantumZipper.fwdHull (fun s : ℝ => W s.toNNReal ω) t := by
    apply InteractingSLE.fwdHull_eq_of_eqOn t.coe_nonneg (by exact_mod_cast htp)
    intro s hs
    exact stopVal_of_lt (lt_of_le_of_lt
      (ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hs.2)) hpζ)
  rw [hHull]
  exact hη.2.2 t ht

end Preservation

section Evolution

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
  {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {P Q : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **Continuity at the lifetime, for the measurable stopped version.**
Auxiliary lemma 3 supplies the state limit almost surely. Its dyadic stopped
version is continuous through every finite positive lifetime and is a threshold
state there. This needs no new Loewner continuity theorem. -/
theorem ae_continuous_stopVal_state_at_lifetime (hκ : 0 < κ)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0, 0 < T → (T : ℝ≥0∞) = ζ ω →
      Continuous (fun t => (stopVal W (fun x => (ζ x : WithTop ℝ≥0)) t ω,
        fun i => stopVal (VL i) (fun x => (ζ x : WithTop ℝ≥0)) t ω,
        fun j => stopVal (VR j) (fun x => (ζ x : WithTop ℝ≥0)) t ω)) ∧
      ForceWord.ThresholdCondition ρL ρR
        (stopVal W (fun x => (ζ x : WithTop ℝ≥0)) T ω)
        (fun i => stopVal (VL i) (fun x => (ζ x : WithTop ℝ≥0)) T ω)
        (fun j => stopVal (VR j) (fun x => (ζ x : WithTop ℝ≥0)) T ω) := by
  filter_upwards [hE.ae_isIntegratedSLEPath, hE.ae_tendsto_threshold hκ]
    with ω hp hlim T hT hζ
  obtain ⟨w₀, vL₀, vR₀, hlim, hthr⟩ := hlim T hT hζ
  have hf := hp.isForcePath
  have hc := hf.continuousOn_w.prodMk
    ((continuousOn_pi.2 hf.continuousOn_vL).prodMk
      (continuousOn_pi.2 hf.continuousOn_vR))
  refine ⟨continuous_stopVal_state_of_tendsto hT hζ hc hlim, ?_⟩
  have hstate := stopVal_state_at_lifetime hT hζ hlim
  have h := congrArg (fun p : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) =>
    ForceWord.ThresholdCondition ρL ρR p.1 p.2.1 p.2.2) hstate
  exact h ▸ hthr

/-- The terminal continuity and threshold statements survive an absolutely
continuous change of measure, as required for the local field comparison. -/
theorem ae_continuous_stopVal_state_at_lifetime_of_ac (hκ : 0 < κ)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hQP : Q ≪ P) :
    ∀ᵐ ω ∂Q, ∀ T : ℝ≥0, 0 < T → (T : ℝ≥0∞) = ζ ω →
      Continuous (fun t => (stopVal W (fun x => (ζ x : WithTop ℝ≥0)) t ω,
        fun i => stopVal (VL i) (fun x => (ζ x : WithTop ℝ≥0)) t ω,
        fun j => stopVal (VR j) (fun x => (ζ x : WithTop ℝ≥0)) t ω)) ∧
      ForceWord.ThresholdCondition ρL ρR
        (stopVal W (fun x => (ζ x : WithTop ℝ≥0)) T ω)
        (fun i => stopVal (VL i) (fun x => (ζ x : WithTop ℝ≥0)) T ω)
        (fun j => stopVal (VR j) (fun x => (ζ x : WithTop ℝ≥0)) T ω) :=
  (ae_continuous_stopVal_state_at_lifetime hκ hE).filter_mono hQP.ae_le

end Evolution

end InteractingSLE.Restart.FlowStopIdentLL
