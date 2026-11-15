/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.MartingaleCoupling

/-!
# Theorem 2.4's localization below a killing time

Packet PROVE-LEMMA71B. Specification, Theorem 2.4 (`source/spec/p001-048.md`, anchors `thm-2.4`, `thm-2.4-proof`),
and the proof of Lemma 7.1 (p. 225), where the martingale characterization is applied to the mapped driver only up
to its terminal capacity time.

The converse of Theorem 2.4 (`MartChar.martingale_driftProc_quadProc_of_couplingMean`, `Spec/Sec2/MartingaleCoupling`)
uses the martingale property of the coupling means `𝔥_t(z)` only at points `z` far from the origin and only up to
the localizing times `locTime W V T N`. This file records the same statements when the coupling means are local
martingales only before `min (swallowTime z) θ` for a random time `θ` that comes after the localizing time:

* `continuousWithinAt_coupProc`: the coupling-mean process is right-continuous before `z` is swallowed;
* **`setIntegral_stoppedProcess_coupProc_eq_of_before`**, **`martingale_driftProc_quadProc_of_before`**: the
  statements of `setIntegral_stoppedProcess_coupProc_eq` and `martingale_driftProc_quadProc_of_couplingMean` with
  the extra time `θ` and the hypothesis `locTime W V T N < θ` almost surely.

The proofs are those of `Spec/Sec2/MartingaleCoupling.lean` (PROVE-SEC2-MART), with the one change that the localizing
time is compared with `min (swallowTime z) θ` instead of `swallowTime z`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Complex
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE

namespace MartChar

variable {nL nR : ℕ}

section Process

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}

/-- **The coupling-mean process is right-continuous before `z` is swallowed** (the right-continuity step of
`setIntegral_stoppedProcess_coupProc_eq`). -/
theorem continuousWithinAt_coupProc {κ : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    (hWc : ∀ ω, Continuous fun t => W t ω) (hVLc : ∀ i ω, Continuous fun t => VL i t ω)
    (hVRc : ∀ i ω, Continuous fun t => VR i t ω) (hordL : ∀ ω t i, VL i t ω ≤ W t ω)
    (hordR : ∀ ω t i, W t ω ≤ VR i t ω) {z : ℂ} (hzH : z ∈ H) (ω : Ω) (s : ℝ≥0)
    (hs : (s : WithTop ℝ≥0) < (QuantumZipper.swallowTime (wpath W ω) z : WithTop ℝ≥0)) :
    ContinuousWithinAt (coupProc κ ρL ρR W VL VR z · ω) (Ici s) s := by
  set V := jointV VL VR with hV
  set ρ := jointρ ρL ρR with hρ
  set c : ℝ := Real.pi / Real.sqrt κ * (1 + ∑ i, ρR i) with hc
  have hVc : ∀ j ω, Continuous fun t => V j t ω := fun j ω => by
    cases j with
    | inl i => exact hVLc i ω
    | inr i => exact hVRc i ω
  obtain ⟨T', hsT', hT'⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hs
  have hsT'' : s < T' := ENNReal.coe_lt_coe.1 hsT'
  have hzT' : z ∈ H \ QuantumZipper.fwdHull (wpath W ω) T' := by
    refine ⟨hzH, fun h => ?_⟩
    have h2 := h.2
    rw [ENNReal.ofReal_coe_nnreal] at h2
    exact absurd h2 (not_le.2 hT')
  set g : ℝ → ℝ := fun x => c + harmPart κ ρ (wpath W ω) x (fun j => V j x.toNNReal ω) z with hg_def
  have hg : ContinuousOn g (Icc 0 T') :=
    continuousOn_const.add (continuousOn_harmPart κ ρ (continuous_wpath hWc ω)
      (NNReal.coe_nonneg T') hzT' fun j => ((hVc j ω).comp continuous_real_toNNReal).continuousOn)
  have heq : ∀ t : ℝ≥0, t ≤ T' → coupProc κ ρL ρR W VL VR z t ω = g t := fun t ht => by
    rw [coupProc_eq hWc hordL hordR ht hzT', hg_def, jointV_apply_eq]
    simp only [Real.toNNReal_coe, hc, hρ, hV]
  have hgc : ContinuousOn (fun t : ℝ≥0 => g t) (Iic T') :=
    hg.comp NNReal.continuous_coe.continuousOn fun t ht =>
      ⟨NNReal.coe_nonneg t, by exact_mod_cast ht⟩
  have hca : ContinuousAt (fun t : ℝ≥0 => g t) s := hgc.continuousAt (Iic_mem_nhds hsT'')
  have heq' : (fun t : ℝ≥0 => g t) =ᶠ[𝓝 s] (coupProc κ ρL ρR W VL VR z · ω) := by
    filter_upwards [Iic_mem_nhds hsT''] with t ht
    exact (heq t ht).symm
  exact (hca.congr heq').continuousWithinAt

/-- **The coupling mean stopped at a localizing time has constant set integrals** (as
`setIntegral_stoppedProcess_coupProc_eq`), for every `z` far enough from the origin, when it is a local martingale
before `min (swallowTime z) θ` and the localizing time comes before `θ` almost surely. -/
theorem setIntegral_stoppedProcess_coupProc_eq_of_before [IsProbabilityMeasure P] {κ : ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    (hW0 : ∀ ω, W 0 ω = 0) (hVL0 : ∀ i ω, VL i 0 ω = xL i) (hVR0 : ∀ i ω, VR i 0 ω = xR i)
    (hWc : ∀ ω, Continuous fun t => W t ω) (hVLc : ∀ i ω, Continuous fun t => VL i t ω)
    (hVRc : ∀ i ω, Continuous fun t => VR i t ω) (hWa : StronglyAdapted 𝓕 W)
    (hVLa : ∀ i, StronglyAdapted 𝓕 (VL i)) (hVRa : ∀ i, StronglyAdapted 𝓕 (VR i))
    (hordL : ∀ ω t i, VL i t ω ≤ W t ω) (hordR : ∀ ω t i, W t ω ≤ VR i t ω) {z : ℂ}
    (hzH : z ∈ H)
    {θ : Ω → WithTop ℝ≥0}
    (hmart : IsLocalMartingaleBefore 𝓕 P
      (fun ω => min (QuantumZipper.swallowTime (wpath W ω) z : WithTop ℝ≥0) (θ ω))
      (coupProc κ ρL ρR W VL VR z))
    (T N : ℕ) (hzR : laurentRadius ((N : ℝ) + |(0 : ℝ)| + ∑ j, |jointV xL xR j|) T ≤ ‖z‖)
    (hτθ : ∀ᵐ ω ∂P, locTime W (jointV VL VR) T N ω < θ ω) :
    (∀ t, Integrable
      (stoppedProcess (coupProc κ ρL ρR W VL VR z) (locTime W (jointV VL VR) T N) t) P) ∧
      ∀ s t : ℝ≥0, s ≤ t → ∀ A, MeasurableSet[𝓕 s] A →
        ∫ ω in A, stoppedProcess (coupProc κ ρL ρR W VL VR z) (locTime W (jointV VL VR) T N) t ω ∂P
          = ∫ ω in A, stoppedProcess (coupProc κ ρL ρR W VL VR z)
              (locTime W (jointV VL VR) T N) s ω ∂P := by
  set V := jointV VL VR with hV
  set ρ := jointρ ρL ρR with hρ
  set K : ℝ := (N : ℝ) + |(0 : ℝ)| + ∑ j, |jointV xL xR j| with hK
  set τ := locTime W V T N with hτdef
  set c : ℝ := Real.pi / Real.sqrt κ * (1 + ∑ i, ρR i) with hc
  have hVc : ∀ j ω, Continuous fun t => V j t ω := fun j ω => by
    cases j with
    | inl i => exact hVLc i ω
    | inr i => exact hVRc i ω
  have hVa : ∀ j, StronglyAdapted 𝓕 (V j) := fun j => by
    cases j with
    | inl i => exact hVLa i
    | inr i => exact hVRa i
  have hV0 : ∀ j ω, V j 0 ω = jointV xL xR j := fun j ω => by
    cases j with
    | inl i => exact hVL0 i ω
    | inr i => exact hVR0 i ω
  have hτ : IsStoppingTime 𝓕 τ := isStoppingTime_locTime hWc hVc hWa hVa T N
  have hτT : ∀ ω, τ ω ≤ ((T : ℝ≥0) : WithTop ℝ≥0) := locTime_le T N
  have hbd : ∀ ω (t : ℝ≥0), (t : WithTop ℝ≥0) ≤ τ ω → |W t ω| ≤ K ∧ ∀ j, |V j t ω| ≤ K :=
    fun ω t ht => abs_le_of_le_locTime hW0 hV0 hWc hVc ht
  have hle_T : ∀ ω (t : ℝ≥0), (t : WithTop ℝ≥0) ≤ τ ω → (t : ℝ) ≤ T := fun ω t ht => by
    have := ht.trans (hτT ω)
    exact_mod_cast (WithTop.coe_le_coe.1 this)
  have hpb : ∀ ω (t : ℝ≥0), (t : WithTop ℝ≥0) ≤ τ ω → ∀ r ∈ Icc (0 : ℝ) t, |wpath W ω r| ≤ K :=
    fun ω t ht r hr => (hbd ω r.toNNReal ((WithTop.coe_le_coe.2
      (Real.toNNReal_le_iff_le_coe.2 hr.2)).trans ht)).1
  have hR1 : 1 ≤ ‖z‖ := (one_le_laurentRadius _ _).trans hzR
  have hR3 : 2 * dispConst K T + 1 ≤ ‖z‖ :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hzR))
  have hR4 : K + 3 * Real.sqrt T + 1 ≤ ‖z‖ :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hzR))
  have hns : ∀ ω (t : ℝ≥0), (t : WithTop ℝ≥0) ≤ τ ω →
      z ∈ H \ QuantumZipper.fwdHull (wpath W ω) t := fun ω t ht => by
    refine mem_diff_fwdHull_of_norm (continuous_wpath hWc ω) (NNReal.coe_nonneg t) (hpb ω t ht)
      hzH ?_
    have := Real.sqrt_le_sqrt (hle_T ω t ht)
    linarith
  -- `τ` comes before the swallowing time
  have hτζ : ∀ ω, τ ω < (QuantumZipper.swallowTime (wpath W ω) z : WithTop ℝ≥0) := fun ω => by
    have hne : τ ω ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top (hτT ω)
    obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 hne
    have hz := hns ω r (hr ▸ le_rfl)
    have hnot : ¬ QuantumZipper.swallowTime (wpath W ω) z ≤ ENNReal.ofReal r :=
      fun h => hz.2 ⟨hzH, h⟩
    rw [not_le, ENNReal.ofReal_coe_nnreal] at hnot
    rw [← hr]
    exact hnot
  -- right-continuity before swallowing
  have hrc : ∀ ω (s : ℝ≥0), (s : WithTop ℝ≥0) < (QuantumZipper.swallowTime (wpath W ω) z : WithTop ℝ≥0) →
      ContinuousWithinAt (coupProc κ ρL ρR W VL VR z · ω) (Ici s) s := by
    intro ω s hs
    obtain ⟨T', hsT', hT'⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hs
    have hsT'' : s < T' := ENNReal.coe_lt_coe.1 hsT'
    have hzT' : z ∈ H \ QuantumZipper.fwdHull (wpath W ω) T' := by
      refine ⟨hzH, fun h => ?_⟩
      have h2 := h.2
      rw [ENNReal.ofReal_coe_nnreal] at h2
      exact absurd h2 (not_le.2 hT')
    set g : ℝ → ℝ := fun x => c + harmPart κ ρ (wpath W ω) x (fun j => V j x.toNNReal ω) z with hg_def
    have hg : ContinuousOn g (Icc 0 T') :=
      continuousOn_const.add (continuousOn_harmPart κ ρ (continuous_wpath hWc ω)
        (NNReal.coe_nonneg T') hzT' fun j => ((hVc j ω).comp continuous_real_toNNReal).continuousOn)
    have heq : ∀ t : ℝ≥0, t ≤ T' → coupProc κ ρL ρR W VL VR z t ω = g t := fun t ht => by
      rw [coupProc_eq hWc hordL hordR ht hzT', hg_def, jointV_apply_eq]
      simp only [Real.toNNReal_coe, hc, hρ, hV]
    have hgc : ContinuousOn (fun t : ℝ≥0 => g t) (Iic T') :=
      hg.comp NNReal.continuous_coe.continuousOn fun t ht =>
        ⟨NNReal.coe_nonneg t, by exact_mod_cast ht⟩
    have hca : ContinuousAt (fun t : ℝ≥0 => g t) s := hgc.continuousAt (Iic_mem_nhds hsT'')
    have heq' : (fun t : ℝ≥0 => g t) =ᶠ[𝓝 s] (coupProc κ ρL ρR W VL VR z · ω) := by
      filter_upwards [Iic_mem_nhds hsT''] with t ht
      exact (heq t ht).symm
    exact (hca.congr heq').continuousWithinAt
  -- the bound
  have hC : ∀ ω (t : ℝ≥0), (t : WithTop ℝ≥0) ≤ τ ω →
      |coupProc κ ρL ρR W VL VR z t ω| ≤ |c| + harmBound κ ρ K T := fun ω t ht => by
    rw [coupProc_eq hWc hordL hordR le_rfl (hns ω t ht)]
    refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
    exact abs_harmPart_le κ ρ (continuous_wpath hWc ω) (by simp [wpath, hW0])
      (NNReal.coe_nonneg t) (hle_T ω t ht) (hpb ω t ht) _ (hns ω t ht) hR1 (by linarith)
  exact setIntegral_stoppedProcess_eq_of_isLocalMartingaleBefore hmart
    (fun ω s hs => hrc ω s (lt_of_lt_of_le hs (min_le_left _ _))) hτ hτT
    (by filter_upwards [hτθ] with ω hω; exact lt_min (hτζ ω) hω) hC

/-- **The Laurent-coefficient processes are martingales up to every localizing time** (as
`martingale_driftProc_quadProc_of_couplingMean`) when every coupling mean `𝔥_t(z)`, `z ∈ ℍ`, is a local martingale
before `min (swallowTime z) θ` and the localizing time `locTime W V T N` comes before `θ` almost surely. -/
theorem martingale_driftProc_quadProc_of_before [IsProbabilityMeasure P] {κ : ℝ}
    (hκ : 0 < κ) {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {xL : Fin nL → ℝ}
    {xR : Fin nR → ℝ} (hW0 : ∀ ω, W 0 ω = 0) (hVL0 : ∀ i ω, VL i 0 ω = xL i)
    (hVR0 : ∀ i ω, VR i 0 ω = xR i) (hWc : ∀ ω, Continuous fun t => W t ω)
    (hVLc : ∀ i ω, Continuous fun t => VL i t ω) (hVRc : ∀ i ω, Continuous fun t => VR i t ω)
    (hWa : StronglyAdapted 𝓕 W) (hVLa : ∀ i, StronglyAdapted 𝓕 (VL i))
    (hVRa : ∀ i, StronglyAdapted 𝓕 (VR i)) (hordL : ∀ ω t i, VL i t ω ≤ W t ω)
    (hordR : ∀ ω t i, W t ω ≤ VR i t ω)
    {θ : Ω → WithTop ℝ≥0}
    (hmart : ∀ z ∈ H, IsLocalMartingaleBefore 𝓕 P
      (fun ω => min (QuantumZipper.swallowTime (wpath W ω) z : WithTop ℝ≥0) (θ ω))
      (coupProc κ ρL ρR W VL VR z))
    (T N : ℕ) (hτθ : ∀ᵐ ω ∂P, locTime W (jointV VL VR) T N ω < θ ω) :
    Martingale (stoppedProcess (driftProc (jointρ ρL ρR) W (jointV VL VR))
        (locTime W (jointV VL VR) T N)) 𝓕 P ∧
      Martingale (stoppedProcess (quadProc κ (jointρ ρL ρR) W (jointV VL VR))
        (locTime W (jointV VL VR) T N)) 𝓕 P := by
  set V := jointV VL VR with hV
  set ρ := jointρ ρL ρR with hρ
  set K : ℝ := (N : ℝ) + |(0 : ℝ)| + ∑ j, |jointV xL xR j| with hK
  set τ := locTime W V T N with hτdef
  set c : ℝ := Real.pi / Real.sqrt κ * (1 + ∑ i, ρR i) with hc
  set R := laurentRadius K T with hR
  have hVc : ∀ j ω, Continuous fun t => V j t ω := fun j ω => by
    cases j with
    | inl i => exact hVLc i ω
    | inr i => exact hVRc i ω
  have hVa : ∀ j, StronglyAdapted 𝓕 (V j) := fun j => by
    cases j with
    | inl i => exact hVLa i
    | inr i => exact hVRa i
  have hV0 : ∀ j ω, V j 0 ω = jointV xL xR j := fun j ω => by
    cases j with
    | inl i => exact hVL0 i ω
    | inr i => exact hVR0 i ω
  have hτ : IsStoppingTime 𝓕 τ := isStoppingTime_locTime hWc hVc hWa hVa T N
  have hτT : ∀ ω, τ ω ≤ ((T : ℝ≥0) : WithTop ℝ≥0) := locTime_le T N
  have hK0 : 0 ≤ K := by
    have : 0 ≤ ∑ j, |jointV xL xR j| := Finset.sum_nonneg fun j _ => abs_nonneg _
    positivity
  have hsk : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  -- stopped times and bounds
  set θ : ℝ≥0 → Ω → ℝ≥0 := fun u ω => (min (u : WithTop ℝ≥0) (τ ω)).untopA with hθ
  have hθτ : ∀ u ω, ((θ u ω : ℝ≥0) : WithTop ℝ≥0) ≤ τ ω := fun u ω => by
    simp only [hθ]
    rw [coe_untopA_of_ne_top (ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _))]
    exact min_le_right _ _
  have hθT : ∀ u ω, (θ u ω : ℝ) ≤ T := fun u ω => by
    have := (hθτ u ω).trans (hτT ω)
    exact_mod_cast (WithTop.coe_le_coe.1 this)
  have hbd : ∀ u ω, |W (θ u ω) ω| ≤ K ∧ ∀ j, |V j (θ u ω) ω| ≤ K := fun u ω =>
    abs_le_of_le_locTime hW0 hV0 hWc hVc (hθτ u ω)
  have hpb : ∀ u ω, ∀ r ∈ Icc (0 : ℝ) (θ u ω), |wpath W ω r| ≤ K := fun u ω r hr =>
    (abs_le_of_le_locTime hW0 hV0 hWc hVc ((WithTop.coe_le_coe.2
      (Real.toNNReal_le_iff_le_coe.2 hr.2)).trans (hθτ u ω))).1
  have hw0 : ∀ ω, wpath W ω 0 = 0 := fun ω => by simp [wpath, hW0]
  -- the identity at stopped times
  have hstop : ∀ (z : ℂ), z ∈ H → R ≤ ‖z‖ → ∀ u ω,
      stoppedProcess (coupProc κ ρL ρR W VL VR z) τ u ω
        = c + harmPart κ ρ (wpath W ω) (θ u ω) (fun j => V j (θ u ω) ω) z := by
    intro z hzH hzR u ω
    have hR4 : K + 3 * Real.sqrt T + 1 ≤ ‖z‖ :=
      (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hzR))
    have hns : z ∈ H \ QuantumZipper.fwdHull (wpath W ω) (θ u ω) := by
      refine mem_diff_fwdHull_of_norm (continuous_wpath hWc ω) (NNReal.coe_nonneg _) (hpb u ω)
        hzH ?_
      have := Real.sqrt_le_sqrt (hθT u ω)
      linarith
    show coupProc κ ρL ρR W VL VR z (θ u ω) ω = _
    rw [coupProc_eq hWc hordL hordR le_rfl hns, jointV_apply_eq]
  -- the radii
  set Y : ℕ → ℝ := fun k => (k : ℝ) + R with hY
  have hR1 : 1 ≤ R := one_le_laurentRadius K T
  have hYR : ∀ k, R ≤ Y k := fun k => by simp only [hY]; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hYpos : ∀ k, 0 < Y k := fun k => by linarith [hYR k]
  have hYtop : Tendsto Y atTop atTop := tendsto_atTop_add_const_right _ R tendsto_natCast_atTop_atTop
  have hzI : ∀ k, ((Y k : ℂ) * Complex.I) ∈ H ∧ R ≤ ‖(Y k : ℂ) * Complex.I‖ := fun k => by
    refine ⟨?_, ?_⟩
    · show 0 < ((Y k : ℂ) * Complex.I).im
      simp [hYpos k]
    · rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (hYpos k)]
      exact hYR k
  have hzD : ∀ k, ((Y k : ℂ) * (1 + Complex.I)) ∈ H ∧ R ≤ ‖(Y k : ℂ) * (1 + Complex.I)‖ :=
    fun k => by
      refine ⟨?_, ?_⟩
      · show 0 < ((Y k : ℂ) * (1 + Complex.I)).im
        simp [hYpos k]
      · have h1I : (1 : ℝ) ≤ ‖(1 : ℂ) + Complex.I‖ := by
          have h := Complex.abs_re_le_norm ((1 : ℂ) + Complex.I)
          simp only [Complex.add_re, Complex.one_re, Complex.I_re, add_zero, abs_one] at h
          exact h
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hYpos k)]
        nlinarith [hYR k, hYpos k]
  -- the two coupling processes at the radii
  have hI := fun k => setIntegral_stoppedProcess_coupProc_eq_of_before hW0 hVL0 hVR0 hWc hVLc hVRc hWa hVLa
    hVRa hordL hordR (hzI k).1 (hmart _ (hzI k).1) T N (hzI k).2 hτθ
  have hD := fun k => setIntegral_stoppedProcess_coupProc_eq_of_before hW0 hVL0 hVR0 hWc hVLc hVRc hWa hVLa
    hVRa hordL hordR (hzD k).1 (hmart _ (hzD k).1) T N (hzD k).2 hτθ
  -- adaptedness and integrability of `N^τ`, `Q^τ`
  have hNc : ∀ ω, Continuous fun t => driftProc ρ W V t ω := fun ω => by
    simp only [driftProc, driftValue]
    exact (continuous_const.mul (hWc ω)).add (continuous_finsetSum _ fun j _ =>
      continuous_const.mul (hVc j ω))
  have hQc : ∀ ω, Continuous fun t => quadProc κ ρ W V t ω := fun ω => by
    simp only [quadProc, quadValue]
    exact (((hWc ω).pow 2).add (continuous_const.mul (continuous_finsetSum _ fun j _ =>
      continuous_const.mul ((hVc j ω).pow 2)))).sub
      (continuous_const.mul NNReal.continuous_coe)
  have hNa : StronglyAdapted 𝓕 (driftProc ρ W V) := fun t => by
    have h1 := (hWa t).measurable
    have h2 := fun j => ((hVa j) t).measurable
    have : Measurable[𝓕 t] (driftProc ρ W V t) := by
      show Measurable[𝓕 t] fun ω => 2 * W t ω + ∑ j, ρ j * V j t ω
      fun_prop
    exact this.stronglyMeasurable
  have hQa : StronglyAdapted 𝓕 (quadProc κ ρ W V) := fun t => by
    have h1 := (hWa t).measurable
    have h2 := fun j => ((hVa j) t).measurable
    have : Measurable[𝓕 t] (quadProc κ ρ W V t) := by
      show Measurable[𝓕 t] fun ω =>
        W t ω ^ 2 + 1 / 2 * (∑ j, ρ j * V j t ω ^ 2) - (2 * (∑ j, ρ j) + κ) * (t : ℝ)
      fun_prop
    exact this.stronglyMeasurable
  have hNsa := stronglyAdapted_stoppedProcess_of_continuous hNa hNc hτ
  have hQsa := stronglyAdapted_stoppedProcess_of_continuous hQa hQc hτ
  have hNval : ∀ u ω, stoppedProcess (driftProc ρ W V) τ u ω
      = driftValue ρ (wpath W ω (θ u ω)) (fun j => V j (θ u ω) ω) := fun u ω => by
    rw [wpath_coe]; rfl
  have hQval : ∀ u ω, stoppedProcess (quadProc κ ρ W V) τ u ω
      = quadValue κ ρ (wpath W ω (θ u ω)) (fun j => V j (θ u ω) ω) (θ u ω) := fun u ω => by
    rw [wpath_coe]; rfl
  set Rρ : ℝ := ∑ j, |ρ j| with hRρ
  have hRρ0 : 0 ≤ Rρ := Finset.sum_nonneg fun j _ => abs_nonneg _
  have hNb : ∀ u ω, |stoppedProcess (driftProc ρ W V) τ u ω| ≤ 2 * K + Rρ * K := fun u ω => by
    rw [hNval, wpath_coe]
    simp only [driftValue]
    have h1 : |∑ j, ρ j * V j (θ u ω) ω| ≤ Rρ * K := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      rw [hRρ, Finset.sum_mul]
      exact Finset.sum_le_sum fun j _ => by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left ((hbd u ω).2 j) (abs_nonneg _)
    have h2 : |2 * W (θ u ω) ω| ≤ 2 * K := by
      rw [abs_mul, abs_two]; linarith [(hbd u ω).1]
    exact (abs_add_le _ _).trans (by linarith)
  have hQb : ∀ u ω, |stoppedProcess (quadProc κ ρ W V) τ u ω|
      ≤ K ^ 2 + Rρ * K ^ 2 + |2 * (∑ j, ρ j) + κ| * T := fun u ω => by
    rw [hQval, wpath_coe]
    simp only [quadValue]
    have h1 : |∑ j, ρ j * V j (θ u ω) ω ^ 2| ≤ Rρ * K ^ 2 := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      rw [hRρ, Finset.sum_mul]
      exact Finset.sum_le_sum fun j _ => by
        rw [abs_mul, abs_pow]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) ((hbd u ω).2 j) 2)
          (abs_nonneg _)
    have h2 : |W (θ u ω) ω ^ 2| ≤ K ^ 2 := by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hbd u ω).1 2
    have h3 : |(2 * (∑ j, ρ j) + κ) * (θ u ω : ℝ)| ≤ |2 * (∑ j, ρ j) + κ| * T := by
      rw [abs_mul, NNReal.abs_eq]
      exact mul_le_mul_of_nonneg_left (hθT u ω) (abs_nonneg _)
    have h4 : |1 / 2 * ∑ j, ρ j * V j (θ u ω) ω ^ 2| ≤ Rρ * K ^ 2 := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      have : 0 ≤ Rρ * K ^ 2 := by positivity
      linarith
    calc _ ≤ |W (θ u ω) ω ^ 2 + 1 / 2 * ∑ j, ρ j * V j (θ u ω) ω ^ 2|
          + |(2 * (∑ j, ρ j) + κ) * (θ u ω : ℝ)| := abs_sub _ _
      _ ≤ _ := by linarith [abs_add_le (W (θ u ω) ω ^ 2) (1 / 2 * ∑ j, ρ j * V j (θ u ω) ω ^ 2)]
  have hNint : ∀ u, Integrable (stoppedProcess (driftProc ρ W V) τ u) P := fun u =>
    Integrable.of_bound ((hNsa u).mono (𝓕.le u)).aestronglyMeasurable _
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hNb u ω)
  have hQint : ∀ u, Integrable (stoppedProcess (quadProc κ ρ W V) τ u) P := fun u =>
    Integrable.of_bound ((hQsa u).mono (𝓕.le u)).aestronglyMeasurable _
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hQb u ω)
  set C := harmConst κ ρ K T with hCdef
  -- set integrals of an affine function of a process
  have haff : ∀ (X : ℝ≥0 → Ω → ℝ), (∀ u, Integrable (X u) P) → ∀ (a b : ℝ) (u : ℝ≥0) (A : Set Ω),
      ∫ ω in A, (a * X u ω + b) ∂P = a * ∫ ω in A, X u ω ∂P + b * (P A).toReal := by
    intro X hX a b u A
    rw [integral_add ((hX u).integrableOn.const_mul a) (integrable_const b),
      integral_const_mul, setIntegral_const, smul_eq_mul, mul_comm (P.real A)]
    rfl
  -- the first coefficient
  have hNmart : Martingale (stoppedProcess (driftProc ρ W V) τ) 𝓕 P := by
    refine martingale_of_forall_abs_sub_le hNsa hNint
      (G := fun k t ω => -(Real.sqrt κ * Y k)
        * stoppedProcess (coupProc κ ρL ρR W VL VR ((Y k : ℂ) * Complex.I)) τ t ω
        + Real.sqrt κ * Y k * (c + phiI κ ρ))
      (fun k t => (((hI k).1 t).aestronglyMeasurable.const_mul _).add aestronglyMeasurable_const)
      (ε := fun k => Real.sqrt κ * C / Y k ^ 2) ?_ ?_ ?_
    · exact tendsto_const_nhds.div_atTop ((tendsto_pow_atTop two_ne_zero).comp hYtop)
    · intro k t ω
      rw [hstop _ (hzI k).1 (hzI k).2, hNval]
      have hl := abs_laurent_one_le κ ρ (continuous_wpath hWc ω) (hw0 ω) (NNReal.coe_nonneg _)
        (hθT t ω) (hpb t ω) (hbd t ω).2 (hYR k)
      have hid : -(Real.sqrt κ * Y k) * (c + harmPart κ ρ (wpath W ω) (θ t ω)
          (fun j => V j (θ t ω) ω) ((Y k : ℂ) * Complex.I)) + Real.sqrt κ * Y k * (c + phiI κ ρ)
          - driftValue ρ (wpath W ω (θ t ω)) (fun j => V j (θ t ω) ω)
          = -(Real.sqrt κ * (Y k * (harmPart κ ρ (wpath W ω) (θ t ω) (fun j => V j (θ t ω) ω)
              ((Y k : ℂ) * Complex.I) - phiI κ ρ)
            + driftValue ρ (wpath W ω (θ t ω)) (fun j => V j (θ t ω) ω) / Real.sqrt κ)) := by
        field_simp; ring
      rw [hid, abs_neg, abs_mul, abs_of_pos hsk]
      calc _ ≤ Real.sqrt κ * (C / Y k ^ 2) := mul_le_mul_of_nonneg_left hl hsk.le
        _ = Real.sqrt κ * C / Y k ^ 2 := by ring
    · intro k s t hst A hA
      rw [haff _ (hI k).1, haff _ (hI k).1, (hI k).2 s t hst A hA]
  refine ⟨hNmart, ?_⟩
  -- the second coefficient
  refine martingale_of_forall_abs_sub_le hQsa hQint
    (G := fun k t ω => -(2 * Y k ^ 2 * Real.sqrt κ)
      * stoppedProcess (coupProc κ ρL ρR W VL VR ((Y k : ℂ) * (1 + Complex.I))) τ t ω
      + 2 * Y k ^ 2 * Real.sqrt κ * (c + phiD κ ρ)
      - Y k * stoppedProcess (driftProc ρ W V) τ t ω)
    (fun k t => ((((hD k).1 t).aestronglyMeasurable.const_mul _).add
      aestronglyMeasurable_const).sub ((hNint t).aestronglyMeasurable.const_mul _))
    (ε := fun k => 2 * Real.sqrt κ * C / Y k) ?_ ?_ ?_
  · exact tendsto_const_nhds.div_atTop hYtop
  · intro k t ω
    rw [hstop _ (hzD k).1 (hzD k).2, hNval, hQval]
    have hl := abs_laurent_two_le hκ ρ (continuous_wpath hWc ω) (hw0 ω) (NNReal.coe_nonneg _)
      (hθT t ω) (hpb t ω) (hbd t ω).2 (hYR k)
    have hid : -(2 * Y k ^ 2 * Real.sqrt κ) * (c + harmPart κ ρ (wpath W ω) (θ t ω)
        (fun j => V j (θ t ω) ω) ((Y k : ℂ) * (1 + Complex.I)))
        + 2 * Y k ^ 2 * Real.sqrt κ * (c + phiD κ ρ)
        - Y k * driftValue ρ (wpath W ω (θ t ω)) (fun j => V j (θ t ω) ω)
        - quadValue κ ρ (wpath W ω (θ t ω)) (fun j => V j (θ t ω) ω) (θ t ω)
        = -(2 * Y k ^ 2 * Real.sqrt κ * (harmPart κ ρ (wpath W ω) (θ t ω) (fun j => V j (θ t ω) ω)
            ((Y k : ℂ) * (1 + Complex.I)) - phiD κ ρ)
          + Y k * driftValue ρ (wpath W ω (θ t ω)) (fun j => V j (θ t ω) ω)
          + quadValue κ ρ (wpath W ω (θ t ω)) (fun j => V j (θ t ω) ω) (θ t ω)) := by ring
    rw [hid, abs_neg]
    exact hl
  · intro k s t hst A hA
    have hX := (hD k).1
    have h1 : ∀ u, ∫ ω in A, (-(2 * Y k ^ 2 * Real.sqrt κ)
        * stoppedProcess (coupProc κ ρL ρR W VL VR ((Y k : ℂ) * (1 + Complex.I))) τ u ω
        + 2 * Y k ^ 2 * Real.sqrt κ * (c + phiD κ ρ)
        - Y k * stoppedProcess (driftProc ρ W V) τ u ω) ∂P
        = (-(2 * Y k ^ 2 * Real.sqrt κ) * ∫ ω in A,
            stoppedProcess (coupProc κ ρL ρR W VL VR ((Y k : ℂ) * (1 + Complex.I))) τ u ω ∂P
          + 2 * Y k ^ 2 * Real.sqrt κ * (c + phiD κ ρ) * (P A).toReal)
          - Y k * ∫ ω in A, stoppedProcess (driftProc ρ W V) τ u ω ∂P := fun u => by
      have hI1 : IntegrableOn (fun ω => -(2 * Y k ^ 2 * Real.sqrt κ)
          * stoppedProcess (coupProc κ ρL ρR W VL VR ((Y k : ℂ) * (1 + Complex.I))) τ u ω
          + 2 * Y k ^ 2 * Real.sqrt κ * (c + phiD κ ρ)) A P :=
        ((hX u).integrableOn.const_mul _).add (integrable_const _)
      have hI2 : IntegrableOn (fun ω => Y k * stoppedProcess (driftProc ρ W V) τ u ω) A P :=
        (hNint u).integrableOn.const_mul _
      rw [integral_sub hI1 hI2, integral_const_mul, haff _ hX]
    rw [h1, h1, (hD k).2 s t hst A hA, hNmart.setIntegral_eq hst hA]

end Process

end MartChar

end InteractingSLE
