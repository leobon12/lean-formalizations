/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.LocalExtMBrack
import InteractingSLE.Spec.Sec7.LocalExtMSeed
import InteractingSLE.Spec.Sec7.LocalExtKMain

/-!
# Theorem 1.2's restart coupling: the driving law through the local stop (clause (a))

Packet PROVE-LOCEXT-M. PROVE-LOCEXT-K reduced `RestartSeedCouplingStatement κ` to `RestartDrivingLocalityInput κ`, two clauses
for the canonical restart objects. This file proves the first one, **the driving law through the local stop**
(Aux. lemma 55, proof, specification pp. 248–249, at a restart): under `Q = restartQ` (the Cameron–Martin measure of the
source of the restart word) there is an equivalent measure `Q'`, equal to `Q` on the stopped σ-algebra `𝓖'_{S₀}`, under
which the restarted driver and the chosen seed marks are a local evolution of the `1 + 1` seed word before `S₀`.

* `restartGood`, `restartW`, `restartVL`, `restartVR`: the restarted processes on a good event of time `0` (and `0`
  off it); `adaptedBefore_restartW` etc.: they are adapted before the restarted lifetime;
* `isIntegratedSLEEvolutionFrom_restart`: under `P[·|D]` they are an evolution from the random restart word in the
  usual augmentation of the restarted filtration, with the restart of a continuous version of `B`;
* **`restartDriving`**: clause (a) of `RestartDrivingLocalityInput` for every `κ > 0`: `Q'` is the Girsanov measure of the
  distant drift (`girsanov_shift_drift`), equal to `Q` on `𝓖'_{S₀}` because its density is the density martingale at the
  stop (`doleansDensity_srcThetaW_ae_eq`, LOCEXT-K's `wordMeasure_apply_of_measurableSet`), and the `1 + 1` seed path is
  `IsSLEPathUpTo.oneSeed`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal Classical

namespace InteractingSLE

namespace LocalExt

open QuantumZipper (H fwdMap fwdHull)
open LQGMetric (TestOn DistOn)
open Sec7 Sec5.Markov Sec2.Restart Sec2 Girsanov Coupling

/-! ### The restarted processes on a good event -/

section Processes

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {nL nR : ℕ} {κ : ℝ} {xL : Fin nL → ℝ}
  {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {T : Ω → ℝ≥0}

/-- A restarted process on the event `E`, `0` off it. -/
def onEvent (E : Set Ω) (X : ℝ≥0 → Ω → ℝ) : ℝ≥0 → Ω → ℝ := fun t ω => if ω ∈ E then X t ω else 0

theorem onEvent_of_mem {E : Set Ω} {X : ℝ≥0 → Ω → ℝ} {ω : Ω} (hω : ω ∈ E) : (fun t => onEvent E X t ω) = fun t => X t ω :=
  funext fun t => by simp [onEvent, hω]

/-- **A restarted process on a good event is adapted before the restarted lifetime** (the restart of the progressive
versions, `restart_values`). -/
theorem adaptedBefore_onEvent_restart (hX : IsMeasurableKilledDriving W VL VR ζ)
    (hT : IsStoppingTime (drivingFiltration P hX) fun ω => (T ω : WithTop ℝ≥0)) {E : Set Ω}
    (hE : MeasurableSet[restartFiltration (drivingFiltration P hX) T hT 0] E)
    (hEp : ∀ ω ∈ E, IsIntegratedSLEPath κ xL xR ρL ρR (fun t => W t ω) (fun i t => VL i t ω)
      (fun j t => VR j t ω) (fun t => B t ω) (ζ ω))
    {Y : ℝ≥0 → Ω → ℝ} (hY : AdaptedBefore (drivingFiltration P hX) ζ Y)
    (hYv : ∀ ω ∈ E, ∀ s : ℝ≥0, (s : ℝ≥0∞) < ζ ω → progVersion ζ Y s ω = Y s ω) :
    AdaptedBefore (restartFiltration (drivingFiltration P hX) T hT) (restartLife ζ T)
      (onEvent E (fun t ω => Y (T ω + t) ω - W (T ω) ω)) := by
  set 𝓓 := drivingFiltration P hX with h𝓓
  have hWad : AdaptedBefore 𝓓 ζ W := Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ P)
    (Coupling.adaptedBefore_killedDriving_W hX)
  have hζ : IsStoppingTime 𝓓 fun ω => (ζ ω : WithTop ℝ≥0) := Ito.isStoppingTime_lifetime hWad
  have hpv := adaptedBefore_restart hT hζ (isStronglyProgressive_progVersion hY) (isStronglyProgressive_progVersion hWad)
  intro t A hA
  have hEt : MeasurableSet[restartFiltration 𝓓 T hT t] E := (restartFiltration 𝓓 T hT).mono bot_le E hE
  have hlt : MeasurableSet[restartFiltration 𝓓 T hT t] {ω | (t : ℝ≥0∞) < restartLife ζ T ω} := by
    have h := measurableSet_add_lt hT hζ t
    convert h using 1
    ext ω
    simp only [mem_ofPred_eq, restartLife]
    exact (coe_lt_sub_iff _ _)
  have e : {ω | (t : ℝ≥0∞) < restartLife ζ T ω ∧ onEvent E (fun t ω => Y (T ω + t) ω - W (T ω) ω) t ω ∈ A} =
      (E ∩ {ω | (t : ℝ≥0∞) < ζ ω - T ω ∧ progVersion ζ Y (T ω + t) ω - progVersion ζ W (T ω) ω ∈ A}) ∪
      (Eᶜ ∩ ({ω | (t : ℝ≥0∞) < restartLife ζ T ω} ∩ {_ω | (0 : ℝ) ∈ A})) := by
    ext ω
    by_cases hω : ω ∈ E
    · have hp := hEp ω hω
      simp only [mem_ofPred_eq, mem_union, mem_inter_iff, hω, true_and, mem_compl_iff, not_true_eq_false,
        false_and, or_false, onEvent, ↓reduceIte, restartLife]
      constructor
      · rintro ⟨h1, h2⟩
        have hTt : ((T ω + t : ℝ≥0) : ℝ≥0∞) < ζ ω := (coe_lt_sub_iff _ _).1 h1
        have hT' : (T ω : ℝ≥0∞) < ζ ω := lt_of_le_of_lt (by exact_mod_cast le_self_add) hTt
        refine ⟨h1, ?_⟩
        rwa [hYv ω hω _ hTt, (restart_values hp hT').1]
      · rintro ⟨h1, h2⟩
        have hTt : ((T ω + t : ℝ≥0) : ℝ≥0∞) < ζ ω := (coe_lt_sub_iff _ _).1 h1
        have hT' : (T ω : ℝ≥0∞) < ζ ω := lt_of_le_of_lt (by exact_mod_cast le_self_add) hTt
        refine ⟨h1, ?_⟩
        rwa [hYv ω hω _ hTt, (restart_values hp hT').1] at h2
    · simp only [mem_ofPred_eq, mem_union, mem_inter_iff, hω, false_and, mem_compl_iff, not_false_eq_true,
        true_and, false_or, onEvent, ↓reduceIte]
  rw [e]
  exact (hEt.inter (hpv t A hA)).union (hEt.compl.inter (hlt.inter (MeasurableSet.const _)))

end Processes

/-! ### Clause (a): the driving law through the local stop -/

section Main

universe u

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens} {G : Set Ω} {T : Ω → ℝ≥0}
  {SL : Finset (Fin nL)} {SR : Finset (Fin nR)} {r : ℝ} {D : Set Ω}

/-- **Clause (a) of `RestartDrivingLocalityInput`: the driving law through the local stop at a restart** (Aux. lemma 55,
steps 3–4, specification pp. 248–249, conditionally on a cell event). Under `Q = restartQ` there is an equivalent measure
`Q'`, equal to `Q` on the stopped σ-algebra of the capped local stop `S₀` of the restarted path, a filtration containing
the restarted driving filtration, and a Brownian motion, under which the restarted driver and the restarted chosen seed
marks are a local evolution of the `1 + 1` seed word before `S₀`. -/
theorem restartDriving (hκ : 0 < κ) (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hX : IsMeasurableKilledDriving W VL VR ζ)
    (hT : IsStoppingTime (drivingFiltration P hX) fun ω => (T ω : WithTop ℝ≥0))
    (hGm : MeasurableSet G) (hG0 : P Gᶜ = 0) (hG : ∀ ω ∈ G, IsGoodPath κ xL xR ρL ρR W VL VR B ζ ω)
    (hSL : -2 < ∑ i ∈ SL, ρL i) (hSR : -2 < ∑ j ∈ SR, ρR j)
    (hD : MeasurableSet[hT.measurableSpace] D) (hPD : P D ≠ 0) (hDp : IsRestartCell W VL VR ζ G T SL SR r D)
    {K : Ω → DrivingHist nL nR} (hKm : Measurable[hT.measurableSpace] K)
    (hK : ∀ ω, IsIntegratedSLEPath κ xL xR ρL ρR (fun t => W t ω) (fun i t => VL i t ω) (fun j t => VR j t ω)
      (fun t => B t ω) (ζ ω) → (T ω : ℝ≥0∞) < ζ ω →
        K ω = stoppedHistory (completedState W VL VR ζ) (fun ω => (T ω : WithTop ℝ≥0)) ω) :
    ∃ (Q' : Measure Ω) (𝓕' : Filtration ℝ≥0 mΩ) (B' : ℝ≥0 → Ω → ℝ), IsProbabilityMeasure Q' ∧
      restartQ κ ρL ρR r P D K h ≪ Q' ∧ Q' ≪ restartQ κ ρL ρR r P D K h ∧
      restartFiltration (drivingFiltration P hX) T hT ≤ 𝓕' ∧
      Sec2.IsSLEEvolutionUpTo κ (oneSeedY SL) (oneSeedY SR) (seedWtL (oneSeedY SL) (oneSeedWts SL ρL))
        (seedWtR (oneSeedY SR) (oneSeedWts SR ρR)) Q' 𝓕' (r0W G W T) (r0VL G VL W T SL) (r0VR G VR W T SR) B'
        (fun ω => (capStop r G (restartLife ζ T) (restartDrv W T) ω : ℝ≥0∞)) ∧
      ∀ A, MeasurableSet[(isStoppingTime_capStop_restart hX hT hGm hG0 hG r).measurableSpace] A →
        restartQ κ ρL ρR r P D K h A = Q' A := by
  -- the conditioned measure and the basic objects
  set Pt := P[|D] with hPt
  have hPprob : IsProbabilityMeasure Pt := cond_isProbabilityMeasure hPD
  have hDm : MeasurableSet D := hT.measurableSpace_le _ hD
  have hr0 : 0 < r := pos_radius_of_isRestartCell hPD hDp
  set 𝓓 := drivingFiltration P hX with h𝓓
  set 𝓖' := restartFiltration 𝓓 T hT with h𝓖'
  set 𝓕u := usualAugmentation 𝓕 P with h𝓕u
  have h𝓓u : 𝓓 ≤ 𝓕u := Ito.drivingFiltration_le_usualAugmentation hC.1 hX
  have hTu : IsStoppingTime 𝓕u fun ω => (T ω : WithTop ℝ≥0) := fun t => h𝓓u t _ (hT t)
  have hDu : MeasurableSet[hTu.measurableSpace] D := Ito.measurableSpace_le_of_filtration_le h𝓓u hT hTu _ hD
  -- the restarted Brownian motion
  obtain ⟨Bv, -, hBvc, hBvF, hBvae⟩ := exists_continuous_version hC.1.1
  set Bs := QuantumZipper.StrongMarkov.smShift Bv T with hBs
  have hBsR := isFilteredBrownianReal_restart_cond hBvF hBvc hTu hDu hPD
  set 𝓕R := restartFiltration 𝓕u T hTu with h𝓕R
  set 𝓕M := usualAugmentation 𝓕R Pt with h𝓕M
  have hBsM : IsFilteredBrownianReal 𝓕M Bs Pt := Ito.isFilteredBrownianReal_usualAugmentation hBsR
  have hnullM : Ito.nullAugmented 𝓕M Pt = 𝓕M := Ito.nullAugmented_usualAugmentation 𝓕R Pt
  have h𝓖M : 𝓖' ≤ 𝓕M := (restartFiltration_mono h𝓓u hT hTu).trans (Ito.le_usualAugmentation 𝓕R Pt)
  -- the good event of the restart
  set Gb : Set Ω := (toMeasurable P {ω | ¬ ∀ t, Bv t ω = B t ω})ᶜ with hGbdef
  have hGbm : MeasurableSet Gb := (measurableSet_toMeasurable _ _).compl
  have hGb0 : P Gbᶜ = 0 := by rw [hGbdef, compl_compl, measure_toMeasurable]; exact ae_iff.1 hBvae
  have hGbB : ∀ ω ∈ Gb, ∀ t, Bv t ω = B t ω := fun ω hω => by
    by_contra hn; exact hω (subset_toMeasurable _ _ hn)
  set GM : Set Ω := D ∩ G ∩ Gb with hGMdef
  have hGM0 : MeasurableSet[𝓖' 0] GM := by
    rw [h𝓖', restartFiltration_zero]
    exact (hD.inter (measurableSet_stopped_of_zero hT (measurableSet_drivingFiltration_zero_of_null_compl hX hGm hG0))).inter
      (measurableSet_stopped_of_zero hT (measurableSet_drivingFiltration_zero_of_null_compl hX hGbm hGb0))
  have hGMc : Pt GMᶜ = 0 := by
    have hac : Pt ≪ P := cond_absolutelyContinuous
    have h1 : Pt Dᶜ = 0 := by rw [hPt, cond_apply hDm]; simp
    rw [hGMdef, compl_inter, compl_inter]
    exact measure_union_null (measure_union_null h1 (hac hG0)) (hac hGb0)
  have hGMae : ∀ᵐ ω ∂Pt, ω ∈ GM := by rw [ae_iff]; exact hGMc
  -- the processes on the good event
  set Ws := onEvent GM (restartDrv W T) with hWsdef
  set VLs : Fin nL → ℝ≥0 → Ω → ℝ := fun i => onEvent GM (restartMark (VL i) W T) with hVLsdef
  set VRs : Fin nR → ℝ≥0 → Ω → ℝ := fun j => onEvent GM (restartMark (VR j) W T) with hVRsdef
  set c := restartWord r K with hcdef
  set ζ' := restartLife ζ T with hζ'def
  have hc0 : Measurable[𝓖' 0] c := measurable_restartWord_zero hX hT hKm (r := r)
  have hadm : ∀ ω, IsAdmWord r (c ω) := isAdmWord_restartWord hPD hDp
  have hhm := measurable_restartField_word (κ := κ) hC hX hT hKm
  have hWs : ∀ ω ∈ GM, (fun t => Ws t ω) = fun t => restartDrv W T t ω := fun ω hω => onEvent_of_mem hω
  have hVLs : ∀ ω ∈ GM, (fun i t => VLs i t ω) = fun i t => restartMark (VL i) W T t ω := fun ω hω =>
    funext fun i => onEvent_of_mem hω
  have hVRs : ∀ ω ∈ GM, (fun j t => VRs j t ω) = fun j t => restartMark (VR j) W T t ω := fun ω hω =>
    funext fun j => onEvent_of_mem hω
  have hBsB : ∀ ω ∈ GM, (fun t => Bs t ω) = fun t => restartBM B T t ω := fun ω hω => funext fun t => by
    simp only [hBs, QuantumZipper.StrongMarkov.smShift, restartBM, hGbB ω hω.2]
  have hwp : ∀ ω ∈ GM, IsWordPath κ ρL ρR Ws VLs VRs Bs ζ' c ω := fun ω hω => by
    unfold IsWordPath
    rw [hWs ω hω, hVLs ω hω, hVRs ω hω, hBsB ω hω]
    exact (restartWord_eq_and_isWordPath hG hDp hK hω.1.1).2
  have hcur : ∀ ω ∈ GM, c ω = (curL VL W T ω, curR VR W T ω) := fun ω hω =>
    (restartWord_eq_and_isWordPath (ρL := ρL) (ρR := ρR) hG hDp hK hω.1.1).1
  -- the evolution from the restart word
  have hle := Ito.le_usualAugmentation (killedDrivingFiltration hX) P
  have hWad : AdaptedBefore 𝓓 ζ W := Ito.adaptedBefore_mono hle (Coupling.adaptedBefore_killedDriving_W hX)
  have hEp : ∀ ω ∈ GM, IsIntegratedSLEPath κ xL xR ρL ρR (fun t => W t ω) (fun i t => VL i t ω)
      (fun j t => VR j t ω) (fun t => B t ω) (ζ ω) := fun ω hω => (hG ω hω.1.2).1
  have hWa : AdaptedBefore 𝓖' ζ' Ws := adaptedBefore_onEvent_restart hX hT hGM0 hEp hWad
    fun ω hω s hs => (restart_values (hEp ω hω) hs).1
  have hVLa : ∀ i, AdaptedBefore 𝓖' ζ' (VLs i) := fun i => adaptedBefore_onEvent_restart hX hT hGM0 hEp
    (Ito.adaptedBefore_mono hle (Coupling.adaptedBefore_killedDriving_VL hX i))
    fun ω hω s hs => (restart_values (hEp ω hω) hs).2.1 i
  have hVRa : ∀ j, AdaptedBefore 𝓖' ζ' (VRs j) := fun j => adaptedBefore_onEvent_restart hX hT hGM0 hEp
    (Ito.adaptedBefore_mono hle (Coupling.adaptedBefore_killedDriving_VR hX j))
    fun ω hω s hs => (restart_values (hEp ω hω) hs).2.2 j
  have hEs : IsIntegratedSLEEvolutionFrom κ ρL ρR Pt 𝓕M (fun ω => (c ω).1) (fun ω => (c ω).2) Ws VLs VRs Bs ζ' :=
    ⟨hBsM, fun i => ((measurable_pi_apply i).comp (measurable_fst.comp hc0)).mono (h𝓖M 0) le_rfl,
      fun j => ((measurable_pi_apply j).comp (measurable_snd.comp hc0)).mono (h𝓖M 0) le_rfl,
      AdaptedBefore.mono_filtration h𝓖M hWa, fun i => AdaptedBefore.mono_filtration h𝓖M (hVLa i),
      fun j => AdaptedBefore.mono_filtration h𝓖M (hVRa j), by
        filter_upwards [hGMae] with ω hω using (hwp ω hω).1⟩
  -- the coupling clause for the processes on the good event
  have hcf : MartMeans.IsCouplingCharFun κ ρL ρR Pt 𝓖' Ws VLs VRs ζ' (fun ω => restartField κ (h ω, K ω)) :=
    (isCouplingCharFun_restartWord hC hκ hX hT hG hD hPD hDp hKm hK).congr_ae (by
      filter_upwards [hGMae] with ω hω
      exact ⟨fun t => congrFun (hWs ω hω) t, fun i t => congrFun (congrFun (hVLs ω hω) i) t,
        fun j t => congrFun (congrFun (hVRs ω hω) j) t⟩)
  have hgood : ∀ᵐ ω ∂Pt, IsWordPath κ ρL ρR Ws VLs VRs Bs ζ' c ω := by
    filter_upwards [hGMae] with ω hω using hwp ω hω
  -- the local stop
  set S₀ := capStop r G ζ' (restartDrv W T) with hS₀def
  have hS₀ := isStoppingTime_capStop_restart (B := B) (xL := xL) (xR := xR) (ρL := ρL) (ρR := ρR) (κ := κ)
    hX hT hGm hG0 hG r
  set S : Ω → ℝ≥0 := fun ω => (S₀ ω).untopD 0 with hSdef
  have hScoe : ∀ ω, (S ω : WithTop ℝ≥0) = S₀ ω := fun ω => by
    obtain ⟨a, ha⟩ : ∃ a : ℝ≥0, (a : WithTop ℝ≥0) = S₀ ω :=
      WithTop.ne_top_iff_exists.1 (capStop_restart_ne_top (G := G) (r := r) (ζ := ζ) (W := W) (T := T) ω)
    show (((S₀ ω).untopD 0 : ℝ≥0) : WithTop ℝ≥0) = S₀ ω
    rw [← ha, WithTop.untopD_coe]
  have hS𝓖 : IsStoppingTime 𝓖' fun ω => (S ω : WithTop ℝ≥0) := by simp_rw [hScoe]; exact hS₀
  have hSζ : ∀ ω, (S ω : ℝ≥0∞) ≤ ζ' ω := fun ω => by
    have h1 := capStop_le (G := G) (ζ := ζ') (W := restartDrv W T) r ω
    have h2 : ((S ω : WithTop ℝ≥0) : WithTop ℝ≥0) ≤ (ζ' ω : WithTop ℝ≥0) := (hScoe ω).symm ▸ h1
    exact h2
  have hGgood : ∀ ω ∈ GM, IsWordGood κ ρL ρR r Ws VLs VRs Bs c ζ' S ω := fun ω hω => by
    obtain ⟨hωG, hTζ, -, -, hrad⟩ := hDp ω hω.1.1
    refine ⟨hwp ω hω, ?_, by simp [hBs, QuantumZipper.StrongMarkov.smShift], ?_⟩
    · show Continuous fun t => Bv (T ω + t) ω - Bv (T ω) ω
      exact ((hBvc ω).comp (continuous_const.add continuous_id)).sub continuous_const
    · rw [hScoe, hS₀def, hWs ω hω]
      exact capStop_restart_eq_localStopPath (hG ω hωG) hTζ hωG hrad
  have hpat : ∀ ω ∈ GM, seedWtL (c ω).1 ρL = patWt SL ρL ∧ seedWtR (c ω).2 ρR = patWt SR ρR := fun ω hω => by
    obtain ⟨-, -, hpL, hpR, -⟩ := hDp ω hω.1.1
    rw [hcur ω hω]
    refine ⟨funext fun i => ?_, funext fun j => ?_⟩
    · simp only [seedWtL, patWt, curL, sub_eq_zero]
      by_cases hi : i ∈ SL
      · simp [hi, (hpL i).2 hi]
      · have : ¬ VL i (T ω) ω = W (T ω) ω := fun h0 => hi ((hpL i).1 h0)
        simp [hi, this]
    · simp only [seedWtR, patWt, curR, sub_eq_zero]
      by_cases hj : j ∈ SR
      · simp [hj, (hpR j).2 hj]
      · have : ¬ VR j (T ω) ω = W (T ω) ω := fun h0 => hj ((hpR j).1 h0)
        simp [hj, this]
  -- the Doléans density of the distant drift is the density martingale at the stop
  set 𝓔 := Ito.nullAugmented 𝓕M Pt with h𝓔
  have hBn : IsFilteredBrownianReal 𝓔 Bs Pt := by
    have e : 𝓔 = 𝓕M := hnullM
    rw [e]; exact hBsM
  have hdol := doleansDensity_srcThetaW_ae_eq (P := Pt) hκ hr0 hEs hBn h𝓖M hcf hhm hc0 hadm hGM0 hGMc hGgood
    hpat hS𝓖 hSζ
  -- Girsanov's theorem for the distant drift
  set σ := weightDiff ρL (patWt SL ρL) ρR (patWt SR ρR) with hσdef
  have h𝓖𝓔 : 𝓖' ≤ 𝓔 := fun t => (h𝓖M t).trans (Ito.le_nullAugmented 𝓕M Pt t)
  have hWa𝓔 : AdaptedBefore 𝓔 ζ' Ws := AdaptedBefore.mono_filtration h𝓖𝓔 hWa
  have hU : ∀ k, AdaptedBefore 𝓔 ζ' (allMarks VLs VRs k) :=
    allMarks_adaptedBefore (fun i => AdaptedBefore.mono_filtration h𝓖𝓔 (hVLa i))
      (fun j => AdaptedBefore.mono_filtration h𝓖𝓔 (hVRa j))
  have hτ : ∀ s : ℝ≥0, MeasurableSet[𝓔 s] {ω | (S ω : ℝ≥0∞) ≤ s} := fun s => h𝓖𝓔 s _ (hS𝓖 s)
  have hτT : ∀ ω, (S ω : ℝ≥0∞) ≤ (stopHorizon r : ℝ≥0∞) := fun ω => by
    have h1 : S₀ ω ≤ (stopHorizon r : WithTop ℝ≥0) :=
      (min_le_left _ _).trans (localStop_le_stopHorizon (r := r) (G := G) (ζ' := ζ') (W' := restartDrv W T))
    have h2 : ((S ω : WithTop ℝ≥0) : WithTop ℝ≥0) ≤ (stopHorizon r : WithTop ℝ≥0) := (hScoe ω).symm ▸ h1
    exact h2
  have hcont : ∀ᵐ ω ∂Pt, ContinuousOn (fun s => Ws s ω) {s | (s : ℝ≥0∞) < ζ' ω} ∧
      ∀ k, ContinuousOn (fun s => allMarks VLs VRs k s ω) {s | (s : ℝ≥0∞) < ζ' ω} := by
    filter_upwards [hgood] with ω hp
    refine ⟨hp.1.2.2.2.1, fun k => ?_⟩
    cases k using Fin.addCases with
    | left i => simpa [allMarks] using hp.1.2.2.2.2.1 i
    | right i => simpa [allMarks] using hp.1.2.2.2.2.2.1 i
  have hgap : ∀ᵐ ω ∂Pt, ∀ t : ℝ≥0, (t : ℝ≥0∞) < S ω → ∀ k, σ k ≠ 0 →
      7 * r ≤ |Ws t ω - allMarks VLs VRs k t ω| := by
    filter_upwards [hGMae] with ω hω t ht k hk
    have hg := (hGgood ω hω).gap (hadm ω) (hpat ω hω) ht
    cases k using Fin.addCases with
    | left i =>
      simp only [hσdef, weightDiff, allMarks, Fin.addCases_left] at hk ⊢
      exact hg.1 i (sub_ne_zero.1 hk)
    | right i =>
      simp only [hσdef, weightDiff, allMarks, Fin.addCases_right] at hk ⊢
      exact hg.2 i (sub_ne_zero.1 hk)
  obtain ⟨h1, h2, h3⟩ := girsanov_shift_drift (P := Pt) hκ 1 (δ := 7 * r) (by positivity) σ hBn hWa𝓔 hU hτ hSζ
    hτT hcont hgap
  set θ := shiftDrift κ 1 (7 * r) σ (fun ω => (S ω : ℝ≥0∞)) ζ' Ws (allMarks VLs VRs) with hθdef
  have hθ : θ = srcThetaW κ r ρL (patWt SL ρL) ρR (patWt SR ρR) S ζ' Ws VLs VRs := rfl
  have hcm : Measurable c := hc0.mono (𝓖'.le 0) le_rfl
  have hQeq : restartQ κ ρL ρR r P D K h = wordMeasure κ ρL ρR r Pt c (fun ω => restartField κ (h ω, K ω)) := rfl
  refine ⟨girsanovMeasure Pt 𝓔 Bs θ (stopHorizon r + 1), 𝓔, girsanovProcess Bs θ, h1.isProb, ?_, ?_, h𝓖𝓔,
    ⟨h2, AdaptedBefore.mono_filtration h𝓖𝓔 (adaptedBefore_r0W hX hT hGm hG0 hG r),
      fun k => AdaptedBefore.mono_filtration h𝓖𝓔 (adaptedBefore_r0VL hX hT hGm hG0 hG r k),
      fun k => AdaptedBefore.mono_filtration h𝓖𝓔 (adaptedBefore_r0VR hX hT hGm hG0 hG r k), h1.ac.ae_le ?_⟩, ?_⟩
  · rw [hQeq]; exact wordMeasure_absolutelyContinuous.trans h1.ac'
  · rw [hQeq]; exact h1.ac.trans (absolutelyContinuous_wordMeasure hhm hcm)
  · -- the `1 + 1` seed path
    filter_upwards [hGMae, h3] with ω hω h3ω
    have hg := hGgood ω hω
    have hpU := hg.1.1.isSLEPathUpTo (hSζ ω)
    obtain ⟨-, -, hpL, hpR, -⟩ := hDp ω hω.1.1
    have hxL : ∀ i, (c ω).1 i = 0 ↔ i ∈ SL := fun i => by
      rw [hcur ω hω]; simp only [curL, sub_eq_zero]; exact hpL i
    have hxR : ∀ j, (c ω).2 j = 0 ↔ j ∈ SR := fun j => by
      rw [hcur ω hω]; simp only [curR, sub_eq_zero]; exact hpR j
    have h7 : (0 : ℝ) < 7 * r := by positivity
    have hsepL : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < S ω → ∀ i, patWt SL ρL i ≠ ρL i → VLs i t ω ≠ Ws t ω :=
      fun ht i hi heq => by
        have := (hg.gap (hadm ω) (hpat ω hω) ht).1 i hi
        rw [heq, sub_self, abs_zero] at this; linarith
    have hsepR : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < S ω → ∀ j, patWt SR ρR j ≠ ρR j → VRs j t ω ≠ Ws t ω :=
      fun ht j hj heq => by
        have := (hg.gap (hadm ω) (hpat ω hω) ht).2 j hj
        rw [heq, sub_self, abs_zero] at this; linarith
    have hb' : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < S ω →
        Real.sqrt κ * girsanovProcess Bs θ t ω = Real.sqrt κ * Bs t ω
          + (∑ i, ∫ s in (0 : ℝ)..t, (ρL i - patWt SL ρL i) / (Ws s.toNNReal ω - VLs i s.toNNReal ω))
          + (∑ i, ∫ s in (0 : ℝ)..t, (ρR i - patWt SR ρR i) / (Ws s.toNNReal ω - VRs i s.toNNReal ω)) :=
      fun {t} ht => by
        have e := (h3ω t ht.le).2
        rw [hσdef, sum_weightDiff_integral] at e
        have eL : ∑ i, ∫ s in (0 : ℝ)..t, (ρL i - patWt SL ρL i) / (Ws s.toNNReal ω - VLs i s.toNNReal ω) =
            -∑ i, ∫ s in (0 : ℝ)..t, (patWt SL ρL i - ρL i) / (Ws s.toNNReal ω - VLs i s.toNNReal ω) := by
          rw [← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← intervalIntegral.integral_neg]
          refine intervalIntegral.integral_congr fun s _ => ?_
          show _ = -((patWt SL ρL i - ρL i) / (Ws s.toNNReal ω - VLs i s.toNNReal ω))
          ring
        have eR : ∑ i, ∫ s in (0 : ℝ)..t, (ρR i - patWt SR ρR i) / (Ws s.toNNReal ω - VRs i s.toNNReal ω) =
            -∑ i, ∫ s in (0 : ℝ)..t, (patWt SR ρR i - ρR i) / (Ws s.toNNReal ω - VRs i s.toNNReal ω) := by
          rw [← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← intervalIntegral.integral_neg]
          refine intervalIntegral.integral_congr fun s _ => ?_
          show _ = -((patWt SR ρR i - ρR i) / (Ws s.toNNReal ω - VRs i s.toNNReal ω))
          ring
        rw [eL, eR]
        linarith
    have hone := hpU.oneSeed hxL hxR hsepL hsepR hSL hSR hb'
    have hωG : ω ∈ G := hω.1.2
    have e1 : (fun t => r0W G W T t ω) = fun t => Ws t ω := funext fun t => by
      simp [r0W, hWsdef, onEvent, hω, hωG]
    have e2 : (fun k t => r0VL G VL W T SL k t ω) = fun k t => VLs (oneSeedIdx SL k) t ω :=
      funext fun k => funext fun t => by simp [r0VL, hVLsdef, onEvent, hω, hωG]
    have e3 : (fun k t => r0VR G VR W T SR k t ω) = fun k t => VRs (oneSeedIdx SR k) t ω :=
      funext fun k => funext fun t => by simp [r0VR, hVRsdef, onEvent, hω, hωG]
    have e4 : ((capStop r G (restartLife ζ T) (restartDrv W T) ω : WithTop ℝ≥0) : ℝ≥0∞) = (S ω : ℝ≥0∞) :=
      (hScoe ω).symm
    show IsSLEPathUpTo κ (oneSeedY SL) (oneSeedY SR) (seedWtL (oneSeedY SL) (oneSeedWts SL ρL))
      (seedWtR (oneSeedY SR) (oneSeedWts SR ρR)) (fun t => r0W G W T t ω) (fun k t => r0VL G VL W T SL k t ω)
      (fun k t => r0VR G VR W T SR k t ω) (fun t => girsanovProcess Bs θ t ω)
      ((capStop r G (restartLife ζ T) (restartDrv W T) ω : WithTop ℝ≥0) : ℝ≥0∞)
    rw [e1, e2, e3, e4]
    exact hone
  · -- `Q = Q'` on the stopped σ-algebra
    intro A hA
    have hAm : MeasurableSet A := hS₀.measurableSpace_le _ hA
    have hτS : ∀ᵐ ω ∂Pt, S₀ ω ≤ localStopPath r (ζ' ω) fun t => Ws t ω := by
      filter_upwards [hGMae] with ω hω
      rw [← hScoe ω]; exact le_of_eq (hGgood ω hω).2.2.2
    have hk := wordMeasure_apply_of_measurableSet hcf hhm hc0 hadm hgood hS₀ hτS hA
    rw [hQeq, hk, girsanovMeasure, withDensity_apply _ hAm]
    refine lintegral_congr_ae (ae_restrict_of_ae ?_)
    filter_upwards [hdol] with ω h1
    rw [hθ, h1]

end Main

end LocalExt

end InteractingSLE
