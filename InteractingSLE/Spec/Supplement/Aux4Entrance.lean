/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.Aux4EntranceRestart
import InteractingSLE.Spec.Supplement.Aux4EntranceConv
import InteractingSLE.Spec.Supplement.Aux4EntranceGirsanov
import InteractingSLE.Spec.Sec2.TwoSeedLawBridge
import InteractingSLE.Spec.Sec2.JacobiExists
import InteractingSLE.Spec.Sec2.Assembly2Entr

/-!
# Aux. lemma 4 at the restart: the entrance law of Lemma DS3 (`EntranceStatement`)

Packet PROVE-T14-DS3. Aux. lemma 4 (spec pp. 28–30) in the form used by the proof of Lemma DS3: the laws of the restart
state at the hitting time `τ_r` of the cross-gap level `r` are, up to a tolerance that vanishes with `r` uniformly in the
weights, the images `ν(ρ) = restartMap_*(law of vPath U)` of the stationary Jacobi law with the seed weights, and these
converge as the weights converge.

* `vLaw_eq`: entrance-path laws depend only on the Jacobi parameters (landed `Sec2.TwoSeed.map_toCPathR_eq`);
* `restartLaw`: `ν(ρ)` (with the landed stationary Jacobi law `Sec2.JacobiExists.pathMeasure`);
* `lintegral_restartLaw_eq`: under the Girsanov measure `Q` removing the separated weights up to the localization time,
  `∫ g dν(ρ) = ∫_{τ_r<ζ} g(S) dQ`, and `Q`-almost surely the restart state is in the carrier (two-seed cover
  `exists_twoSeed_cover_path`, angle `exists_isJacobiMP_logAngle`, pathwise `restartState_eq_restartMap`);
* `lintegral_le_girsanov_restart`: `|∫_{τ_r<ζ} g(S) dP − ∫_{τ_r<ζ} g(S) dQ| ≤ e` (`lintegral_le_girsanov_add`, the
  restart state being `𝓖_{r²/16}`-measurable);
* **`entranceStatement`**: `DS3Reach.EntranceStatement`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Supp12

namespace Aux4

open Sec2 Sec2.Assembly Sec2.Assembly2 Sec2.Assembly3 Sec2.TwoSeed Sec2.Jacobi DS2 DS3Reach Girsanov

/-! ### The law of the entrance path depends only on the parameters -/

section Law

open scoped DSReach.PathMeas

variable {R : ℝ≥0}

/-- The entrance path as a function of a continuous path in `CPathR`. -/
def vPathC (f : CPathR) : C(Icc (0 : ℝ≥0) R, ℝ) := vPath f.1 f.2

theorem measurable_vPathC : Measurable (vPathC (R := R)) :=
  DSReach.measurable_to_pathSpace _ fun _ => measurable_const.mul
    (continuous_clamp01.measurable.comp ((measurable_pi_apply _).comp measurable_subtype_coe))

theorem vLaw_eq {κ a b : ℝ} (hκ : 0 ≤ κ) (hab : 0 < a + b) {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁]
    [MeasurableSpace Ω₂] {P₁ : Measure Ω₁} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂]
    {U₁ : ℝ → Ω₁ → ℝ} {U₂ : ℝ → Ω₂ → ℝ} (h₁ : IsJacobiMP κ a b P₁ U₁) (h₂ : IsJacobiMP κ a b P₂ U₂) :
    vLaw (R := R) h₁ = vLaw (R := R) h₂ := by
  apply Subtype.ext
  change P₁.map _ = P₂.map _
  have e₁ : (fun ω => vPath (R := R) (U₁ · ω) (h₁.continuous ω)) = vPathC ∘ toCPathR U₁ h₁.continuous := rfl
  have e₂ : (fun ω => vPath (R := R) (U₂ · ω) (h₂.continuous ω)) = vPathC ∘ toCPathR U₂ h₂.continuous := rfl
  rw [e₁, e₂, ← Measure.map_map measurable_vPathC (measurable_toCPathR h₁.measurable h₁.continuous),
    ← Measure.map_map measurable_vPathC (measurable_toCPathR h₂.measurable h₂.continuous),
    map_toCPathR_eq h₁ h₂ hκ hab]

end Law

/-! ### The identification under the Girsanov measure -/

section Ident

open scoped DSReach.PathMeas

variable {nL nR : ℕ} (hnL : 0 < nL) (hnR : 0 < nR) {κ : ℝ} {mL mR : ℕ} {Rw ε η : ℝ}
  {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}

/-- The seed initial state is not a threshold state. -/
theorem not_thr_seed (hε : 0 < ε) (hη : 0 < η) (hw : IsDS1Word mL mR Rw ε xL xR ρL ρR)
    (hfarL : ∀ i : Fin nL, mL ≤ (i : ℕ) → xL i ≤ -η) (hfarR : ∀ j : Fin nR, mR ≤ (j : ℕ) → η ≤ xR j) :
    ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR := by
  have hord : DSReach.IsOrderedState (((0 : ℝ), xL, xR) : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)) :=
    ⟨hw.1.1, hw.1.2.1, hw.1.2.2.2, hw.1.2.2.1⟩
  have hbuf : DSReach.InCBuffer mL mR ‖((xL, xR) : (Fin nL → ℝ) × (Fin nR → ℝ))‖ η
      (((0 : ℝ), xL, xR) : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)) := by
    refine ⟨⟨by simp, fun i => ?_, fun j => ?_⟩, fun j hj => ?_, fun i hi => ?_⟩
    · rw [← Real.norm_eq_abs]
      exact (norm_le_pi_norm xL i).trans (norm_fst_le ((xL, xR) : (Fin nL → ℝ) × (Fin nR → ℝ)))
    · rw [← Real.norm_eq_abs]
      exact (norm_le_pi_norm xR j).trans (norm_snd_le ((xL, xR) : (Fin nL → ℝ) × (Fin nR → ℝ)))
    · simp only [sub_zero]; exact hfarR j hj
    · simp only [zero_sub]; linarith [hfarL i hi]
  exact DSReach.not_threshold_of_inCBuffer hε hη hw hord hbuf

/-- The law `ν(ρ)` of the restart functional of the entrance path. -/
def restartLaw (R : ℝ≥0) (δ : ℝ) (xL : Fin nL → ℝ)
    (xR : Fin nR → ℝ) {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P'] {κ' a' b' : ℝ}
    {U' : ℝ → Ω' → ℝ} (hU : IsJacobiMP κ' a' b' P' U') : ProbabilityMeasure (ℝ × ((Fin nL → ℝ) × (Fin nR → ℝ))) :=
  (vLaw (R := R) hU).map (restartMap δ xL xR)

/-- **The identification under the Girsanov measure**: with `Q` the Girsanov measure removing the separated weights up
to the localization time, `∫ g dν(ρ) = ∫_{τ_r < ζ} g(S) dQ`, and the restart state is `Q`-almost surely in the carrier on
`{τ_r < ζ}`. -/
theorem lintegral_restartLaw_eq (hκ : 0 < κ) (hε : 0 < ε) (hη : 0 < η) (hL0 : xL ⟨0, hnL⟩ = 0)
    (hR0 : xR ⟨0, hnR⟩ = 0) (hLη : ∀ i, xL i ≠ 0 → xL i ≤ -η) (hRη : ∀ j, xR j ≠ 0 → η ≤ xR j)
    (hfarL : ∀ i : Fin nL, mL ≤ (i : ℕ) → xL i ≤ -η) (hfarR : ∀ j : Fin nR, mR ≤ (j : ℕ) → η ≤ xR j)
    (hw : IsDS1Word mL mR Rw ε xL xR ρL ρR) {r : ℝ} (hr0 : 0 < r) (hrη : r ≤ η / 4) (hr1 : r ≤ 1)
    (hk : (r.toNNReal : ℝ) ^ 2 / (8 * (η / 2) ^ 2) < 1)
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓖 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {N : Set Ω}
    (hG : IsGoodEvolution κ xL xR ρL ρR P 𝓖 W VL VR B ζ N)
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P'] {U' : ℝ → Ω' → ℝ}
    (hU : IsJacobiMP κ (seedSum xL ρL + 2) (seedSum xR ρR + 2) P' U') :
    (∀ g : ℝ × ((Fin nL → ℝ) × (Fin nR → ℝ)) → ℝ≥0∞, Measurable g →
      ∫⁻ x, g x ∂((restartLaw r.toNNReal (η / 2) xL xR hU :
        ProbabilityMeasure _) : Measure (ℝ × ((Fin nL → ℝ) × (Fin nR → ℝ)))) =
      ∫⁻ ω in {ω | tauR hnL hnR r ζ VL VR ω < ζ ω} ∩ Nᶜ, g (restartState hnL hnR r ζ W VL VR ω)
        ∂(girsanovMeasure P 𝓖 B (weightDrift κ (η / 2) ρL (seedW xL ρL) ρR (seedW xR ρR)
          (entT (η / 2) xL xR ζ W VL VR) ζ W VL VR) (1 + 1))) ∧
    girsanovMeasure P 𝓖 B (weightDrift κ (η / 2) ρL (seedW xL ρL) ρR (seedW xR ρR)
          (entT (η / 2) xL xR ζ W VL VR) ζ W VL VR) (1 + 1)
      (({ω | tauR hnL hnR r ζ VL VR ω < ζ ω} ∩ Nᶜ) ∩
        restartState hnL hnR r ζ W VL VR ⁻¹' (RestartCarrier hnL hnR mL mR η r)ᶜ) = 0 := by
  obtain ⟨hE, h𝓖rc, hWc, hVLc, hVRc, hBc, hW0, hVL0, hVR0, hζ0, hNm, hN0, hnull, hNp⟩ := hG
  have : 𝓖.IsRightContinuous := h𝓖rc
  have : IsProbabilityMeasure P := hE.1.isProbabilityMeasure'
  have hthr := not_thr_seed hε hη hw hfarL hfarR
  obtain ⟨hsL, hsR⟩ := (not_thr_iff_seedSum xL xR ρL ρR).1 hthr
  have hδ : 0 < η / 2 := by linarith
  have hδL : ∀ i, xL i ≠ 0 → η / 2 < -xL i := fun i hi => by linarith [hLη i hi]
  have hδR : ∀ j, xR j ≠ 0 → η / 2 < xR j := fun j hj => by linarith [hRη j hj]
  obtain ⟨Gw, Gl, Gr, ζG, hQp, hGev, hcov⟩ := exists_twoSeed_cover_path hκ hw.1 hδ hδL hδR
    (pL := ⟨0, hnL⟩) (pR := ⟨0, hnR⟩) hL0 hR0 hthr hE hWc hVLc hVRc hBc hW0 hVL0 hVR0 hζ0 hnull
  obtain ⟨Ug, hUg, hUgeq⟩ := exists_isJacobiMP_logAngle hGev hκ hsL hsR
  set Q := girsanovMeasure P 𝓖 B (weightDrift κ (η / 2) ρL (seedW xL ρL) ρR (seedW xR ρR)
    (entT (η / 2) xL xR ζ W VL VR) ζ W VL VR) (1 + 1) with hQdef
  have hQP : Q ≪ P := by
    obtain ⟨hTle, -, -, hTζ, -⟩ := entT_good hδ hδL hδR ⟨0, hnL⟩ hE.2.1 hE.2.2.1 hE.2.2.2.1 hWc hVLc hVRc
      hW0 hVL0 hVR0 hζ0
    obtain ⟨hθp, hθb, hθreg⟩ := hE.isSLEEvolutionUpTo.weightDrift_props (seedW xL ρL) (seedW xR ρR) hTle hTζ hδ
    have := isFilteredPreBrownian_of_isFilteredBrownianReal hE.1
    exact (isEquivProbMeasure_girsanovMeasure (B := B) hθp.stronglyAdapted hθb hθreg (1 + 1)).ac
  -- the identification, `Q`-almost surely
  have hid : ∀ᵐ ω ∂Q, (tauR hnL hnR r ζ VL VR ω < ζ ω ∧ ω ∉ N) ∧
      restartState hnL hnR r ζ W VL VR ω =
        restartMap (R := r.toNNReal) (η / 2) xL xR (vPath (Ug · ω) (hUg.continuous ω)) ∧
      restartState hnL hnR r ζ W VL VR ω ∈ RestartCarrier hnL hnR mL mR η r := by
    filter_upwards [hcov, hUgeq, hQP.ae_le (measure_eq_zero_iff_ae_notMem.1 hN0)] with ω hc hUω hωN
    obtain ⟨hζG, hlt, hp, hpG, hpQ, hag⟩ := hc
    rw [hζG] at hpG hUω
    obtain ⟨hτζ, hS⟩ := restartState_eq_restartMap hnL hnR hp.isForcePath hpQ hpG hag hlt
      (hUg.continuous ω) (fun v => hUg.mem_Icc v ω) hUω hL0 hR0 hLη hRη hr0 hrη hr1
    exact ⟨⟨hτζ, hωN⟩, hS, restartState_mem_carrier hnL hnR hp.isForcePath hL0 hR0 hfarL hfarR hr0.le hrη
      (by linarith) hτζ⟩
  -- measurability of the restart event
  have hT := isStoppingTime_TR hnL hnR (r := r) hE.2.2.1 hE.2.2.2.1 hVLc hVRc
  have hAm : MeasurableSet ({ω | tauR hnL hnR r ζ VL VR ω < ζ ω} ∩ Nᶜ) :=
    hT.measurableSpace_le _ (measurableSet_tauR_lt hnL hnR hE.2.2.1 hE.2.2.2.1 hVLc hVRc
      (hnull N hNm hN0) (fun ω hω => (hNp ω hω).isForcePath) hr0.le (by linarith))
  refine ⟨fun g hg => ?_, ?_⟩
  · have hR : 0 < r.toNNReal := Real.toNNReal_pos.2 hr0
    have hcont := continuous_restartMap hR hδ hk xL xR
    have hlaw : vLaw (R := r.toNNReal) hU = vLaw (R := r.toNNReal) hUg :=
      vLaw_eq hκ.le (by linarith) hU hUg
    change ∫⁻ x, g x ∂(((vLaw (R := r.toNNReal) hU : ProbabilityMeasure C(Icc (0 : ℝ≥0) r.toNNReal, ℝ)) :
      Measure C(Icc (0 : ℝ≥0) r.toNNReal, ℝ)).map (restartMap (η / 2) xL xR)) = _
    rw [lintegral_map hg hcont.measurable, hlaw]
    change ∫⁻ V, g (restartMap (η / 2) xL xR V) ∂(Q.map fun ω => vPath (R := r.toNNReal) (Ug · ω)
      (hUg.continuous ω)) = _
    rw [lintegral_map (f := fun V => g (restartMap (η / 2) xL xR V)) (hg.comp hcont.measurable)
      (measurable_vPath hUg.measurable hUg.continuous), ← lintegral_indicator hAm]
    refine lintegral_congr_ae ?_
    filter_upwards [hid] with ω hω
    have hmem : ω ∈ {ω | tauR hnL hnR r ζ VL VR ω < ζ ω} ∩ Nᶜ := ⟨hω.1.1, hω.1.2⟩
    rw [indicator_of_mem hmem, hω.2.1]
  · refine measure_mono_null (fun ω hω => ?_) (ae_iff.1 hid)
    intro h
    exact hω.2 h.2.2

/-! ### Measurability of the restart event at a deterministic time -/

/-- A function measurable for a stopping-time σ-algebra, vanishing off an event on which the stopping time is at most
`t`, is `𝓕_t`-measurable. -/
theorem measurable_of_stoppingTime_le {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime 𝓕 τ) {A : Set Ω} (hA : MeasurableSet[hτ.measurableSpace] A)
    {t : ℝ≥0} (hAτ : ∀ ω ∈ A, τ ω ≤ t) {f : Ω → ℝ≥0∞} (hf : Measurable[hτ.measurableSpace] f)
    (hf0 : ∀ ω, ω ∉ A → f ω = 0) : Measurable[𝓕 t] f := by
  have hsub : ∀ X : Set Ω, MeasurableSet[hτ.measurableSpace] X → X ⊆ A → MeasurableSet[𝓕 t] X := by
    intro X hX hXA
    have := (hτ.measurableSet X).1 hX |>.2 t
    convert this using 1
    ext ω
    exact ⟨fun h => ⟨h, hAτ ω (hXA h)⟩, fun h => h.1⟩
  have hAt : MeasurableSet[𝓕 t] A := hsub A hA subset_rfl
  intro B hB
  have e : f ⁻¹' B = (f ⁻¹' B ∩ A) ∪ (Aᶜ ∩ {_ω | (0 : ℝ≥0∞) ∈ B}) := by
    ext ω
    by_cases hω : ω ∈ A
    · simp [hω]
    · simp [hω, hf0 ω hω]
  rw [e]
  exact (hsub _ ((hf hB).inter hA) inter_subset_right).union (hAt.compl.inter (MeasurableSet.const _))

theorem measurable_restart_indicator {r : ℝ} (hr0 : 0 < r) (hr4 : r ≤ 4) {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {𝓖 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {N : Set Ω}
    (hG : IsGoodEvolution κ xL xR ρL ρR P 𝓖 W VL VR B ζ N) {g : ℝ × ((Fin nL → ℝ) × (Fin nR → ℝ)) → ℝ≥0∞}
    (hg : Measurable g) :
    Measurable[𝓖 ((r ^ 2 / 16).toNNReal)] (({ω | tauR hnL hnR r ζ VL VR ω < ζ ω} ∩ Nᶜ).indicator
      fun ω => g (restartState hnL hnR r ζ W VL VR ω)) := by
  obtain ⟨hE, -, hWc, hVLc, hVRc, -, -, -, -, -, hNm, hN0, hnull, hNp⟩ := hG
  have hT := isStoppingTime_TR hnL hnR (r := r) hE.2.2.1 hE.2.2.2.1 hVLc hVRc
  have hA := measurableSet_tauR_lt hnL hnR (r := r) hE.2.2.1 hE.2.2.2.1 hVLc hVRc (hnull N hNm hN0)
    (fun ω hω => (hNp ω hω).isForcePath) hr0.le hr4
  set A := {ω | tauR hnL hnR r ζ VL VR ω < ζ ω} ∩ Nᶜ
  -- the restart state through the progressive versions
  set Sp : Ω → ℝ × ((Fin nL → ℝ) × (Fin nR → ℝ)) := fun ω =>
    (Restart.progVersion ζ W (TR hnL hnR r ζ VL VR ω) ω,
      (fun i => Restart.progVersion ζ (VL i) (TR hnL hnR r ζ VL VR ω) ω -
        Restart.progVersion ζ W (TR hnL hnR r ζ VL VR ω) ω),
      fun j => Restart.progVersion ζ (VR j) (TR hnL hnR r ζ VL VR ω) ω -
        Restart.progVersion ζ W (TR hnL hnR r ζ VL VR ω) ω) with hSp
  have hSpm : Measurable[hT.measurableSpace] Sp := by
    have hw := Restart.measurable_eval_stop (Restart.isStronglyProgressive_progVersion hE.2.1) hT
    have hrel := @Restart.measurable_start_aux nL nR Ω hT.measurableSpace _ _ _ hw
      (fun i => Restart.measurable_eval_stop (Restart.isStronglyProgressive_progVersion (hE.2.2.1 i)) hT)
      (fun j => Restart.measurable_eval_stop (Restart.isStronglyProgressive_progVersion (hE.2.2.2.1 j)) hT)
    let _ : MeasurableSpace Ω := hT.measurableSpace
    exact hw.prodMk hrel
  have heq : A.indicator (fun ω => g (restartState hnL hnR r ζ W VL VR ω)) = A.indicator (fun ω => g (Sp ω)) := by
    refine indicator_congr fun ω hω => ?_
    have hp := (hNp ω hω.2).isForcePath
    have hTζ : (TR hnL hnR r ζ VL VR ω : ℝ≥0∞) < ζ ω := by rw [coe_TR_eq hnL hnR hp hr0.le hr4]; exact hω.1
    simp only [hSp, restartState, Restart.progVersion_eq hp.continuousOn_w hTζ,
      Restart.progVersion_eq (hp.continuousOn_vL _) hTζ, Restart.progVersion_eq (hp.continuousOn_vR _) hTζ]
  rw [heq]
  refine measurable_of_stoppingTime_le hT hA (fun ω hω => ?_) ?_ (fun ω hω => indicator_of_notMem hω _)
  · have hp := (hNp ω hω.2).isForcePath
    have h1 := tauR_le hnL hnR hp hr0.le
    rw [← coe_TR_eq hnL hnR hp hr0.le hr4] at h1
    exact WithTop.coe_le_coe.2 (ENNReal.coe_le_coe.1 h1)
  · let _ : MeasurableSpace Ω := hT.measurableSpace
    exact Measurable.indicator (hg.comp hSpm) hA

/-! ### The entrance bound for a good evolution -/

/-- The uniform bound on the separated drifts. -/
def driftC (κ : ℝ) (nL nR : ℕ) (Rw η : ℝ) : ℝ := |1 / Real.sqrt κ| * (((nL + nR : ℕ) : ℝ) * Rw * (η / 2)⁻¹)

theorem abs_weightDiff_le (hw : IsDS1Word mL mR Rw ε xL xR ρL ρR) (k : Fin (nL + nR)) :
    |weightDiff ρL (seedW xL ρL) ρR (seedW xR ρR) k| ≤ Rw := by
  cases k using Fin.addCases with
  | left i =>
    simp only [weightDiff, Fin.addCases_left, seedW]
    split_ifs
    · rw [sub_self, abs_zero]; exact (abs_nonneg _).trans (hw.2.1 i)
    · rw [zero_sub, abs_neg]; exact hw.2.1 i
  | right j =>
    simp only [weightDiff, Fin.addCases_right, seedW]
    split_ifs
    · rw [sub_self, abs_zero]; exact (abs_nonneg _).trans (hw.2.2.1 j)
    · rw [zero_sub, abs_neg]; exact hw.2.2.1 j

/-- **The entrance bound for a good evolution.** -/
theorem entranceBound_of_good (hκ : 0 < κ) (hε : 0 < ε) (hη : 0 < η) (hL0 : xL ⟨0, hnL⟩ = 0)
    (hR0 : xR ⟨0, hnR⟩ = 0) (hLη : ∀ i, xL i ≠ 0 → xL i ≤ -η) (hRη : ∀ j, xR j ≠ 0 → η ≤ xR j)
    (hfarL : ∀ i : Fin nL, mL ≤ (i : ℕ) → xL i ≤ -η) (hfarR : ∀ j : Fin nR, mR ≤ (j : ℕ) → η ≤ xR j)
    (hw : IsDS1Word mL mR Rw ε xL xR ρL ρR) {r : ℝ} (hr0 : 0 < r) (hrη : r ≤ η / 4) (hr1 : r ≤ 1)
    (hk : (r.toNNReal : ℝ) ^ 2 / (8 * (η / 2) ^ 2) < 1) {e : ℝ} (he : 0 < e)
    (hCe : Real.exp (driftC κ nL nR Rw η ^ 2 * ((r ^ 2 / 16).toNNReal : ℝ)) ≤ 1 + e ^ 2)
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓖 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {N : Set Ω}
    (hG : IsGoodEvolution κ xL xR ρL ρR P 𝓖 W VL VR B ζ N)
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P'] {U' : ℝ → Ω' → ℝ}
    (hU : IsJacobiMP κ (seedSum xL ρL + 2) (seedSum xR ρR + 2) P' U')
    (g : ℝ × ((Fin nL → ℝ) × (Fin nR → ℝ)) → ℝ≥0∞) (hg : Measurable g) (hg1 : ∀ x, g x ≤ 1) :
    (∫⁻ ω in {ω | tauR hnL hnR r ζ VL VR ω < ζ ω} ∩ Nᶜ, g (restartState hnL hnR r ζ W VL VR ω) ∂P ≤
        ∫⁻ x, g x ∂((restartLaw r.toNNReal (η / 2) xL xR hU : ProbabilityMeasure _) :
          Measure (ℝ × ((Fin nL → ℝ) × (Fin nR → ℝ)))) + ENNReal.ofReal e) ∧
      ∫⁻ x, g x ∂((restartLaw r.toNNReal (η / 2) xL xR hU : ProbabilityMeasure _) :
          Measure (ℝ × ((Fin nL → ℝ) × (Fin nR → ℝ)))) ≤
        ∫⁻ ω in {ω | tauR hnL hnR r ζ VL VR ω < ζ ω} ∩ Nᶜ, g (restartState hnL hnR r ζ W VL VR ω) ∂P +
          ENNReal.ofReal e := by
  have hI := (lintegral_restartLaw_eq hnL hnR hκ hε hη hL0 hR0 hLη hRη hfarL hfarR hw hr0 hrη hr1 hk hG hU).1
    g hg
  rw [hI]
  have hGm := measurable_restart_indicator hnL hnR hr0 (by linarith) hG hg
  obtain ⟨hE, -, hWc, hVLc, hVRc, -, hW0, hVL0, hVR0, hζ0, hNm, hN0, hnull, hNp⟩ := hG
  have : IsProbabilityMeasure P := hE.1.isProbabilityMeasure'
  have hδ : 0 < η / 2 := by linarith
  have hδL : ∀ i, xL i ≠ 0 → η / 2 < -xL i := fun i hi => by linarith [hLη i hi]
  have hδR : ∀ j, xR j ≠ 0 → η / 2 < xR j := fun j hj => by linarith [hRη j hj]
  obtain ⟨hTle, -, -, hTζ, -⟩ := entT_good hδ hδL hδR ⟨0, hnL⟩ hE.2.1 hE.2.2.1 hE.2.2.2.1 hWc hVLc hVRc
    hW0 hVL0 hVR0 hζ0
  obtain ⟨hθp, hθb, hθreg⟩ := hE.isSLEEvolutionUpTo.weightDrift_props (seedW xL ρL) (seedW xR ρR) hTle hTζ hδ
  have := isFilteredPreBrownian_of_isFilteredBrownianReal hE.1
  -- the drift constant is uniformly bounded
  have hRw : 0 ≤ Rw := (abs_nonneg _).trans (hw.2.2.1 ⟨0, hnR⟩)
  have hsum : (∑ j, |weightDiff ρL (seedW xL ρL) ρR (seedW xR ρR) j|) ≤ ((nL + nR : ℕ) : ℝ) * Rw := by
    calc (∑ j, |weightDiff ρL (seedW xL ρL) ρR (seedW xR ρR) j|) ≤ ∑ _j : Fin (nL + nR), Rw :=
          Finset.sum_le_sum fun j _ => abs_weightDiff_le hw j
      _ = ((nL + nR : ℕ) : ℝ) * Rw := by simp
  have hC0 : 0 ≤ |1 / Real.sqrt κ| * ((∑ j, |weightDiff ρL (seedW xL ρL) ρR (seedW xR ρR) j|) * (η / 2)⁻¹) := by
    positivity
  have hCle : |1 / Real.sqrt κ| * ((∑ j, |weightDiff ρL (seedW xL ρL) ρR (seedW xR ρR) j|) * (η / 2)⁻¹) ≤
      driftC κ nL nR Rw η := by
    unfold driftC
    gcongr
  have hCe' : Real.exp ((|1 / Real.sqrt κ| * ((∑ j, |weightDiff ρL (seedW xL ρL) ρR (seedW xR ρR) j|) *
      (η / 2)⁻¹)) ^ 2 * ((r ^ 2 / 16).toNNReal : ℝ)) ≤ 1 + e ^ 2 :=
    (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hC0 hCle 2) (NNReal.coe_nonneg _))).trans hCe
  have ht2 : (r ^ 2 / 16).toNNReal ≤ 1 + 1 := by
    rw [Real.toNNReal_le_iff_le_coe]; push_cast; nlinarith
  have hTV := lintegral_le_girsanov_add (B := B) hθp.stronglyAdapted hθb hθreg ht2 he hCe' hGm
    (fun ω => by
      by_cases hω : ω ∈ ({ω | tauR hnL hnR r ζ VL VR ω < ζ ω} ∩ Nᶜ)
      · rw [indicator_of_mem hω]; exact hg1 _
      · rw [indicator_of_notMem hω]; exact zero_le)
  have hAm : MeasurableSet ({ω | tauR hnL hnR r ζ VL VR ω < ζ ω} ∩ Nᶜ) :=
    (isStoppingTime_TR hnL hnR (r := r) hE.2.2.1 hE.2.2.2.1 hVLc hVRc).measurableSpace_le _
      (measurableSet_tauR_lt hnL hnR hE.2.2.1 hE.2.2.2.1 hVLc hVRc (hnull N hNm hN0)
        (fun ω hω => (hNp ω hω).isForcePath) hr0.le (by linarith))
  rw [lintegral_indicator hAm, lintegral_indicator hAm] at hTV
  exact hTV

/-! ### The carrier -/

theorem isClosed_restartCarrier {r : ℝ} : IsClosed (RestartCarrier hnL hnR mL mR η r) := by
  have hL : ∀ i, Continuous fun x : ℝ × ((Fin nL → ℝ) × (Fin nR → ℝ)) => x.2.1 i :=
    fun i => (continuous_apply i).comp (continuous_fst.comp continuous_snd)
  have hR : ∀ j, Continuous fun x : ℝ × ((Fin nL → ℝ) × (Fin nR → ℝ)) => x.2.2 j :=
    fun j => (continuous_apply j).comp (continuous_snd.comp continuous_snd)
  unfold RestartCarrier IsOrderedForceWord Antitone Monotone
  simp only [ofPred_and, ofPred_forall]
  refine ((isClosed_iInter fun a => isClosed_iInter fun b => isClosed_iInter fun _ =>
    isClosed_le (hL b) (hL a)).inter ((isClosed_iInter fun i => isClosed_le (hL i) continuous_const).inter
    ((isClosed_iInter fun a => isClosed_iInter fun b => isClosed_iInter fun _ =>
      isClosed_le (hR a) (hR b)).inter (isClosed_iInter fun j => isClosed_le continuous_const (hR j))))).inter
    ((isClosed_le continuous_const ((hR _).sub (hL _))).inter ((isClosed_iInter fun i => isClosed_iInter fun _ =>
      isClosed_le (hL i) continuous_const).inter (isClosed_iInter fun j => isClosed_iInter fun _ =>
        isClosed_le continuous_const (hR j))))

/-- **The law `ν(ρ)` is carried by the restart carrier** (through one good evolution with these weights). -/
theorem restartLaw_carrier (hκ : 0 < κ) (hε : 0 < ε) (hη : 0 < η) (hL0 : xL ⟨0, hnL⟩ = 0)
    (hR0 : xR ⟨0, hnR⟩ = 0) (hLη : ∀ i, xL i ≠ 0 → xL i ≤ -η) (hRη : ∀ j, xR j ≠ 0 → η ≤ xR j)
    (hfarL : ∀ i : Fin nL, mL ≤ (i : ℕ) → xL i ≤ -η) (hfarR : ∀ j : Fin nR, mR ≤ (j : ℕ) → η ≤ xR j)
    (hw : IsDS1Word mL mR Rw ε xL xR ρL ρR) {r : ℝ} (hr0 : 0 < r) (hrη : r ≤ η / 4) (hr1 : r ≤ 1)
    (hk : (r.toNNReal : ℝ) ^ 2 / (8 * (η / 2) ^ 2) < 1)
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P'] {U' : ℝ → Ω' → ℝ}
    (hU : IsJacobiMP κ (seedSum xL ρL + 2) (seedSum xR ρR + 2) P' U') :
    ((restartLaw r.toNNReal (η / 2) xL xR hU : ProbabilityMeasure _) :
      Measure (ℝ × ((Fin nL → ℝ) × (Fin nR → ℝ)))) (RestartCarrier hnL hnR mL mR η r)ᶜ = 0 := by
  obtain ⟨Ω, mΩ, P, -, 𝓕, W, VL, VR, B, ζ, hE⟩ := exists_isIntegratedSLEEvolution_assembled hκ hw.1
  obtain ⟨𝓖, h𝓖, W', VL', VR', B', ζ', hE', hWc, hVLc, hVRc, hBc, hW0, hVL0, hVR0, hζ0, hnull, N, hNm, hN0,
    hNp⟩ := exists_good_modification_eq (not_thr_seed hε hη hw hfarL hfarR) hE
  have hG : IsGoodEvolution κ xL xR ρL ρR P 𝓖 W' VL' VR' B' ζ' N :=
    ⟨hE', h𝓖, hWc, hVLc, hVRc, hBc, hW0, hVL0, hVR0, hζ0, hNm, hN0, hnull, fun ω hω => (hNp ω hω).2.2.2.2⟩
  obtain ⟨hI, h0⟩ := lintegral_restartLaw_eq hnL hnR hκ hε hη hL0 hR0 hLη hRη hfarL hfarR hw hr0 hrη hr1 hk hG hU
  have hCm : MeasurableSet (RestartCarrier hnL hnR mL mR η r)ᶜ := (isClosed_restartCarrier hnL hnR).measurableSet.compl
  have hAm : MeasurableSet ({ω | tauR hnL hnR r ζ' VL' VR' ω < ζ' ω} ∩ Nᶜ) :=
    (isStoppingTime_TR hnL hnR (r := r) hE'.2.2.1 hE'.2.2.2.1 hVLc hVRc).measurableSpace_le _
      (measurableSet_tauR_lt hnL hnR hE'.2.2.1 hE'.2.2.2.1 hVLc hVRc (hnull N hNm hN0)
        (fun ω hω => (hNp ω hω).2.2.2.2.isForcePath) hr0.le (by linarith))
  rw [← lintegral_indicator_one hCm, hI _ (measurable_one.indicator hCm)]
  calc _ = ∫⁻ _ω in {ω | tauR hnL hnR r ζ' VL' VR' ω < ζ' ω} ∩ Nᶜ, (0 : ℝ≥0∞) ∂(girsanovMeasure P 𝓖 B'
        (weightDrift κ (η / 2) ρL (seedW xL ρL) ρR (seedW xR ρR) (entT (η / 2) xL xR ζ' W' VL' VR') ζ' W' VL' VR')
        (1 + 1)) := by
        refine lintegral_congr_ae ?_
        rw [Filter.EventuallyEq, ae_iff, Measure.restrict_apply' hAm]
        refine measure_mono_null ?_ h0
        intro ω hω
        refine ⟨hω.2, fun hC => hω.1 ?_⟩
        simp [hC]
    _ = 0 := lintegral_zero

/-! ### Aux. lemma 4 at the restart -/

/-- **Aux. lemma 4 in the restart form** (`DS3Reach.EntranceStatement`): `ν(ρ)` with the seed weights, the convergence
coming from the weak continuity of the Jacobi entrance-path law (`tendsto_vLaw`) and the continuity of `restartMap`, the
bounds from `entranceBound_of_good` at levels `r` with `exp(C² r²/16) ≤ 1 + e²`. -/
theorem entranceStatement : EntranceStatement.{u} := by
  intro κ hκ nL nR hnL hnR mL mR Rw ε η hε hη xL xR ρL ρR ρL₀ ρR₀ hL0 hR0 hLη hRη hfarL' hfarR' hwm hw₀ hρL hρR
    e he
  have hfarL : ∀ i : Fin nL, mL ≤ (i : ℕ) → xL i ≤ -η := fun i hi => hLη i (hfarL' i hi)
  have hfarR : ∀ j : Fin nR, mR ≤ (j : ℕ) → η ≤ xR j := fun j hj => hRη j (hfarR' j hj)
  -- the time scale on which the Girsanov density is close to one
  set C := driftC κ nL nR Rw η with hC
  have hlog : 0 < Real.log (1 + e ^ 2) := Real.log_pos (by nlinarith)
  set t₀ := Real.log (1 + e ^ 2) / (C ^ 2 + 1) with ht₀
  have ht₀0 : 0 < t₀ := div_pos hlog (by positivity)
  have hCt₀ : C ^ 2 * t₀ ≤ Real.log (1 + e ^ 2) := by
    rw [ht₀, mul_div_assoc']
    rw [div_le_iff₀ (by positivity)]
    nlinarith [sq_nonneg C]
  refine ⟨min (η / 4) (min 1 (4 * Real.sqrt t₀)), lt_min (by linarith) (lt_min one_pos (by positivity)),
    fun r hr0 hr => ?_⟩
  have hrη : r ≤ η / 4 := hr.trans (min_le_left _ _)
  have hr1 : r ≤ 1 := hr.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hrt : r ≤ 4 * Real.sqrt t₀ := hr.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hrr : (r.toNNReal : ℝ) = r := Real.coe_toNNReal _ hr0.le
  have hk : (r.toNNReal : ℝ) ^ 2 / (8 * (η / 2) ^ 2) < 1 := by
    rw [hrr, div_lt_one (by positivity)]
    nlinarith
  have hCe : Real.exp (C ^ 2 * ((r ^ 2 / 16).toNNReal : ℝ)) ≤ 1 + e ^ 2 := by
    rw [Real.coe_toNNReal _ (by positivity)]
    have hr2 : r ^ 2 / 16 ≤ t₀ := by
      have h1 : r ^ 2 ≤ (4 * Real.sqrt t₀) ^ 2 := pow_le_pow_left₀ hr0.le hrt 2
      rw [mul_pow, Real.sq_sqrt ht₀0.le] at h1
      linarith
    calc Real.exp (C ^ 2 * (r ^ 2 / 16)) ≤ Real.exp (Real.log (1 + e ^ 2)) :=
          Real.exp_le_exp.2 ((mul_le_mul_of_nonneg_left hr2 (sq_nonneg C)).trans hCt₀)
      _ = 1 + e ^ 2 := Real.exp_log (by positivity)
  -- the Jacobi parameters
  have hpar : ∀ (ρL' : Fin nL → ℝ) (ρR' : Fin nR → ℝ), IsDS1Word mL mR Rw ε xL xR ρL' ρR' →
      0 < seedSum xL ρL' + 2 ∧ 0 < seedSum xR ρR' + 2 := fun ρL' ρR' hw => by
    obtain ⟨h1, h2⟩ := (not_thr_iff_seedSum xL xR ρL' ρR').1 (not_thr_seed hε hη hw hfarL hfarR)
    exact ⟨by linarith, by linarith⟩
  have hU := fun m => JacobiExists.isJacobiMP_jacU hκ (hpar _ _ (hwm m)).1 (hpar _ _ (hwm m)).2
  have hU₀ := JacobiExists.isJacobiMP_jacU hκ (hpar _ _ hw₀).1 (hpar _ _ hw₀).2
  refine ⟨fun m => restartLaw r.toNNReal (η / 2) xL xR (hU m), restartLaw r.toNNReal (η / 2) xL xR hU₀, ?_,
    fun m => restartLaw_carrier hnL hnR hκ hε hη hL0 hR0 hLη hRη hfarL hfarR (hwm m) hr0 hrη hr1 hk (hU m),
    restartLaw_carrier hnL hnR hκ hε hη hL0 hR0 hLη hRη hfarL hfarR hw₀ hr0 hrη hr1 hk hU₀,
    fun m Ω _ P 𝓖 W VL VR B ζ N hG g hg hg1 =>
      entranceBound_of_good hnL hnR hκ hε hη hL0 hR0 hLη hRη hfarL hfarR (hwm m) hr0 hrη hr1 hk he hCe hG (hU m)
        g hg hg1,
    fun Ω _ P 𝓖 W VL VR B ζ N hG g hg hg1 =>
      entranceBound_of_good hnL hnR hκ hε hη hL0 hR0 hLη hRη hfarL hfarR hw₀ hr0 hrη hr1 hk he hCe hG hU₀
        g hg hg1⟩
  -- the convergence
  have hseed : ∀ {n : ℕ} (x : Fin n → ℝ), Continuous fun ρ : Fin n → ℝ => seedSum x ρ + 2 := fun x => by
    unfold seedSum
    exact (continuous_finsetSum _ fun i _ => continuous_apply i).add continuous_const
  have hRpos : 0 < r.toNNReal := Real.toNNReal_pos.2 hr0
  have hv := tendsto_vLaw (R := r.toNNReal) hRpos hκ.le (hpar _ _ hw₀).1 (hpar _ _ hw₀).2
    (fun m => (hpar _ _ (hwm m)).1) (fun m => (hpar _ _ (hwm m)).2)
    (((hseed xL).tendsto ρL₀).comp hρL) (((hseed xR).tendsto ρR₀).comp hρR) hU hU₀
  exact ((ProbabilityMeasure.continuous_map
    (continuous_restartMap hRpos (by linarith) hk xL xR)).tendsto _).comp hv

end Ident

end Aux4

namespace DSReach

/-- **Lemma DS3 in reach form** (`DSReach.DS3ReachStatement`), from Aux. lemma 4 at the restart. -/
theorem ds3ReachStatement : DS3ReachStatement.{u} :=
  DS3Reach.ds3ReachStatement_of_entrance Aux4.entranceStatement

end DSReach

end Supp12

end InteractingSLE
