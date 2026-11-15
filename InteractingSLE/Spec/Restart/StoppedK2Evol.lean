/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.ConverseBeforeK2
import InteractingSLE.Spec.Restart.StoppedK2Kernel

/-!
# The stopped K2, part 7: (E-stop) on the enlargement

Packet PROVE-STOPPEDK2. The input (E-stop) of the stopped K2 (`IsRandomWordEvolutionUpTo`) for a continuation read in
a chart, from the coupling means as local martingales before the stop `T`, when the stop comes at or before the
continuation threshold:

* **`isRandomWordEvolutionUpTo_prod`**: PROVE-DOMAINMARKOV7's `ConverseBefore.isRandomWordEvolution_prod` (same
  construction: the driving Brownian motion `M/√κ` up to `T`, glued with an independent one on `Ω × (ℕ → ℝ)`) with the
  lifetime `T ≤ threshold` in place of the threshold: the force defects vanish before `T`
  (`ae_forceDefect_left_eq_zero_before`), so Aux. lemma 117's equations hold before `T`
  (`Aux117.isWordEntrance_of_forceDefect_eq_zero`), and no threshold condition holds before `T`;
* **`isRandomWordEvolutionUpTo_prod_of_isCouplingCharFun`**: the same from the conditional-law clause before `T`
  (`ConverseBefore.isRandomWordEvolution_prod_of_isCouplingCharFun` with the stop as lifetime).

Provenance: both proofs are copies of the landed ones with these changes.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H)
open LQGMetric (TestOn DistOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Restart.StoppedK2

open Sec7 MartChar Aux117 PhaseSelFull ConverseBefore PocketTraversal

section Evolution

variable {nL nR : ℕ} {Ω : Type*} {𝒢 : MeasurableSpace Ω} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {𝓕 : Filtration ℝ≥0 mΩ}

/-- **(E-stop) from local martingales before the stop** (`ConverseBefore.isRandomWordEvolution_prod`, with the stop
`T ≤ threshold` as lifetime). -/
theorem isRandomWordEvolutionUpTo_prod [IsProbabilityMeasure P] {κ : ℝ} (hκ : 0 < κ)
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (h𝒢 : 𝒢 ≤ 𝓕 0) {F : Set Ω}
    (hF : MeasurableSet[𝒢] F) {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ} (hxL : Measurable[𝒢] xL)
    (hxR : Measurable[𝒢] xR) (hxL0 : ∀ ω i, xL ω i ≤ 0) (hxR0 : ∀ ω j, 0 ≤ xR ω j)
    (hxLa : ∀ ω, Antitone (xL ω)) (hxRm : ∀ ω, Monotone (xR ω)) {W : ℝ≥0 → Ω → ℝ}
    (hW0 : ∀ ω, W 0 ω = 0) (hWc : ∀ ω, Continuous fun t => W t ω) (hWa : StronglyAdapted 𝓕 W)
    {T : Ω → WithTop ℝ≥0} (hT : IsStoppingTime 𝓕 T)
    (hmart : ∀ z ∈ H, IsLocalMartingaleBefore 𝓕 P
      (fun ω => min (QuantumZipper.swallowTime (wpath W ω) z : WithTop ℝ≥0) (T ω))
      (coupProc κ ρL ρR W (geomLW W xL) (geomRW W xR) z))
    (hTζ : ∀ᵐ ω ∂P, ω ∈ F → (T ω : ℝ≥0∞) ≤ thresholdTime ρL ρR (fun t => W t ω)
      (fun i t => geomLW W xL i t ω) (fun j t => geomRW W xR j t ω)) :
    ∃ (P₀ : Measure (ℕ → ℝ)) (_ : IsProbabilityMeasure P₀)
      (𝓦 : Filtration ℝ≥0 (inferInstance : MeasurableSpace (ℕ → ℝ))) (B : ℝ≥0 → Ω × (ℕ → ℝ) → ℝ),
      IsRandomWordEvolutionUpTo κ (P.prod P₀) (𝒢.comap Prod.fst) (Prod.fst ⁻¹' F)
        (fun p => xL p.1) (fun p => xR p.1) ρL ρR (WholeField.prodFiltration 𝓕 𝓦) (fun t p => W t p.1)
        (fun i t p => geomLW W xL i t p.1) (fun j t p => geomRW W xR j t p.1) B (fun p => (T p.1 : ℝ≥0∞)) ∧
      (∀ p, Continuous fun t => B t p) ∧
      ∀ (p : Ω × (ℕ → ℝ)) (t : ℝ≥0), (t : WithTop ℝ≥0) ≤ T p.1 →
        B t p = martProc (jointρ ρL ρR) W (jointV (geomLW W xL) (geomRW W xR)) t p.1 / Real.sqrt κ := by
  set VL := geomLW W xL with hVLdef
  set VR := geomRW W xR with hVRdef
  have hxL' : Measurable[𝓕 0] xL := hxL.mono h𝒢 le_rfl
  have hxR' : Measurable[𝓕 0] xR := hxR.mono h𝒢 le_rfl
  have hVLa : ∀ i, StronglyAdapted 𝓕 (VL i) := fun i => stronglyAdapted_geomLW hWa hWc hxL' i
  have hVRa : ∀ j, StronglyAdapted 𝓕 (VR j) := fun j => stronglyAdapted_geomRW hWa hWc hxR' j
  have hordL : ∀ ω t i, VL i t ω ≤ W t ω := fun ω t i => geomLW_le hWc xL ω t i
  have hordR : ∀ ω t j, W t ω ≤ VR j t ω := fun ω t j => le_geomRW hWc xR ω t j
  have hpathL : ∀ ω i, IsForcePath (fun t => W t ω) (fun t => VL i t ω) := fun ω i =>
    isForcePath_geomLW hWc xL ω i
  have hpathR : ∀ ω j, IsForcePath (fun t => W t ω) (fun t => VR j t ω) := fun ω j =>
    isForcePath_geomRW hWc xR ω j
  have hantiL : ∀ ω i, Antitone fun t => VL i t ω := fun ω i => antitone_geomLW hWc xL ω i
  have hmonoR : ∀ ω j, Monotone fun t => VR j t ω := fun ω j => monotone_geomRW hWc xR ω j
  have hidxL : ∀ ω t, Antitone fun i => VL i t ω := fun ω t => antitone_index_geomLW hWc (hxLa ω) t
  have hidxR : ∀ ω t, Monotone fun j => VR j t ω := fun ω t => monotone_index_geomRW hWc (hxRm ω) t
  have hmergeL : ∀ ω i j s t, s ≤ t → VL i s ω = VL j s ω → VL i t ω = VL j t ω :=
    fun ω i j s t hst h => geomLW_merge hWc xL ω i j s t hst h
  have hmergeR : ∀ ω i j s t, s ≤ t → VR i s ω = VR j s ω → VR i t ω = VR j t ω :=
    fun ω i j s t hst h => geomRW_merge hWc xR ω i j s t hst h
  have hsep : ∀ ω t, 0 < t → ∀ i j, VL i t ω = W t ω → VR j t ω ≠ W t ω :=
    fun ω t ht i j h => geom_sep hWc xL xR ω t ht i j h
  have hVL0 : ∀ ω i, VL i 0 ω = xL ω i := fun ω i => geomLW_zero hWc hW0 (hxL0 ω i)
  have hVR0 : ∀ ω j, VR j 0 ω = xR ω j := fun ω j => geomRW_zero hWc hW0 (hxR0 ω j)
  obtain ⟨P₀, hP₀, 𝓦, B, hB, hBc, hBeq⟩ := exists_brownian_continuation_std hκ hW0 hWc hWa hVLa hVRa hordL
    hordR hpathL hpathR hT hmart
  refine ⟨P₀, hP₀, 𝓦, B, ?_, hBc, hBeq⟩
  set 𝓖 := WholeField.prodFiltration 𝓕 𝓦 with h𝓖
  have hBpre := LocalTime.isFilteredPreBrownian_of_isFilteredBrownianReal hB
  have hsk : Real.sqrt κ ≠ 0 := (Real.sqrt_pos.2 hκ).ne'
  have hdec : ∀ (t : ℝ≥0) (ω : Ω), W t ω = Real.sqrt κ * (martProc (jointρ ρL ρR) W (jointV VL VR) t ω /
      Real.sqrt κ) - (1 / 2) * ((∑ i, ρL i * (VL i t ω - xL ω i)) + ∑ j, ρR j * (VR j t ω - xR ω j)) := by
    intro t ω
    have h := driver_eq_martProc (ρL := ρL) (ρR := ρR) (VL := VL) (VR := VR) hκ hW0 t ω
    simp only [hVL0, hVR0] at h
    exact h
  have hW' : ∀ (t : ℝ≥0) (p : Ω × (ℕ → ℝ)), (t : WithTop ℝ≥0) ≤ T p.1 → W t p.1 = Real.sqrt κ * B t p
      - (1 / 2) * ((∑ i, ρL i * (VL i t p.1 - xL p.1 i)) + ∑ j, ρR j * (VR j t p.1 - xR p.1 j)) :=
    fun t p ht => by rw [hBeq p t ht]; exact hdec t p.1
  have hL := ae_forceDefect_left_eq_zero_before (P := P.prod P₀) (𝓕 := 𝓖) (ρL := ρL) (ρR := ρR)
    (xL := fun p i => xL p.1 i) (xR := fun p j => xR p.1 j) (W := fun t p => W t p.1)
    (VL := fun i t p => VL i t p.1) (VR := fun j t p => VR j t p.1) hsk hBpre (isStoppingTime_fst hT) hW'
    (fun p => hWc p.1) (stronglyAdapted_fst hWa) (fun i => stronglyAdapted_fst (hVLa i))
    (fun j => stronglyAdapted_fst (hVRa j)) (fun p => hpathL p.1) (fun p => hpathR p.1)
    (fun p => hordL p.1) (fun p => hantiL p.1) (fun p => hmonoR p.1) (fun p => hmergeL p.1)
    (fun p => hidxL p.1) (fun p => hsep p.1)
  have hR := ae_forceDefect_right_eq_zero_before (P := P.prod P₀) (𝓕 := 𝓖) (ρL := ρL) (ρR := ρR)
    (xL := fun p i => xL p.1 i) (xR := fun p j => xR p.1 j) (W := fun t p => W t p.1)
    (VL := fun i t p => VL i t p.1) (VR := fun j t p => VR j t p.1) hsk hBpre (isStoppingTime_fst hT) hW'
    (fun p => hWc p.1) (stronglyAdapted_fst hWa) (fun i => stronglyAdapted_fst (hVLa i))
    (fun j => stronglyAdapted_fst (hVRa j)) (fun p => hpathL p.1) (fun p => hpathR p.1)
    (fun p => hordR p.1) (fun p => hantiL p.1) (fun p => hmonoR p.1) (fun p => hmergeR p.1)
    (fun p => hidxR p.1) (fun p => hsep p.1)
  have hζ : ∀ t : ℝ≥0, MeasurableSet[𝓖 t] {p : Ω × (ℕ → ℝ) | (T p.1 : ℝ≥0∞) ≤ t} := fun t =>
    isStoppingTime_fst (Ω₀ := ℕ → ℝ) (𝓦 := 𝓦) hT t
  have hfst : Measurable[𝒢.comap Prod.fst, 𝒢] (Prod.fst : Ω × (ℕ → ℝ) → Ω) := Measurable.of_comap_le le_rfl
  refine ⟨(MeasurableSpace.comap_mono h𝒢).trans (WholeField.comap_fst_le_prodFiltration 𝓕 𝓦 0),
    ⟨F, hF, rfl⟩, hxL.comp hfst, hxR.comp hfst, hB,
    MartChar.adaptedBefore_of_stronglyAdapted hζ (stronglyAdapted_fst hWa),
    fun i => MartChar.adaptedBefore_of_stronglyAdapted hζ (stronglyAdapted_fst (hVLa i)),
    fun j => MartChar.adaptedBefore_of_stronglyAdapted hζ (stronglyAdapted_fst (hVRa j)), ?_⟩
  have hTζ' : ∀ᵐ p ∂(P.prod P₀), p.1 ∈ F → (T p.1 : ℝ≥0∞) ≤ thresholdTime ρL ρR (fun t => W t p.1)
      (fun i t => VL i t p.1) (fun j t => VR j t p.1) :=
    Measure.quasiMeasurePreserving_fst.ae hTζ
  filter_upwards [hL, hR, hTζ'] with p hLp hRp hTp hpF
  have hle := hTp hpF
  set b' : ℝ≥0 → ℝ := fun t => (W t p.1 + (1 / 2) * ((∑ i, ρL i * (VL i t p.1 - xL p.1 i)) +
    ∑ j, ρR j * (VR j t p.1 - xR p.1 j))) / Real.sqrt κ with hb'
  have hw' : ∀ t, W t p.1 = Real.sqrt κ * b' t
      - (1 / 2) * ((∑ i, ρL i * (VL i t p.1 - xL p.1 i)) + ∑ j, ρR j * (VR j t p.1 - xR p.1 j)) :=
    fun t => by simp only [hb']; field_simp; ring
  have hlt : ∀ t : ℝ≥0, (t : ℝ≥0∞) < T p.1 → (t : WithTop ℝ≥0) ≤ T p.1 := fun t ht => ht.le
  have hnot : ∀ t : ℝ≥0, (t : ℝ≥0∞) < T p.1 → ∀ u : ℝ≥0, 0 < u → u ≤ t →
      ColliderNe ρL (fun t => W t p.1) (fun i t => VL i t p.1) u ∧
        ColliderNe ρR (fun t => W t p.1) (fun j t => VR j t p.1) u :=
    fun t ht u _ hu => colliderNe_of_not_thresholdCondition
      (notMem_thresholdSet_of_lt ((ENNReal.coe_le_coe.2 hu).trans_lt (ht.trans_le hle)))
  have hE := Aux117.isWordEntrance_of_forceDefect_eq_zero (a := κ) (b := b') (T := (T p.1 : ℝ≥0∞)) (hW0 p.1)
    (fun i => hVL0 p.1 i) (fun j => hVR0 p.1 j) (hWc p.1) (hpathL p.1) (hpathR p.1) (hordL p.1) (hordR p.1)
    (hidxL p.1) (hidxR p.1) hw'
    (fun t ht i => hLp t (hlt t ht) (fun u hu hut => (hnot t ht u hu hut).1) i)
    (fun t ht j => hRp t (hlt t ht) (fun u hu hut => (hnot t ht u hu hut).2) j)
  have hE' := PhaseSelFull.IsWordEntrance.congr_b (b' := fun t => B t p) hE fun t ht => by
    have h := hW' t p (hlt t ht)
    simp only [hb']
    rw [div_eq_iff hsk]
    linarith
  exact ⟨hE'.w_zero, hE'.vL_zero, hE'.vR_zero, hE'.continuousOn_w, hE'.continuousOn_vL, hE'.continuousOn_vR,
    fun {t} ht => hE'.antitone_vL t ht, fun {t} ht => hE'.vL_le_w t ht, fun {t} ht => hE'.w_le_vR t ht,
    fun {t} ht => hE'.monotone_vR t ht, fun {t} ht => hE'.integrable_gapL t ht,
    fun {t} ht => hE'.integrable_gapR t ht, fun {t} ht => hE'.w_eq t ht, fun {t} ht => hE'.vL_eq t ht,
    fun {t} ht => hE'.vR_eq t ht, hE'.volume_collisionL, hE'.volume_collisionR,
    fun {t} ht => notMem_thresholdSet_of_lt (ht.trans_le hle)⟩

end Evolution

section OneShot

variable {Ω : Type*} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓖 : Filtration ℝ≥0 mΩ}
  {nL nR : ℕ}

/-- **(E-stop) from the conditional-law clause before the stop, in one step**
(`ConverseBefore.isRandomWordEvolution_prod_of_isCouplingCharFun`, with the stop `ζ ≤ threshold` as lifetime and
`isRandomWordEvolutionUpTo_prod` in place of `isRandomWordEvolution_prod`). -/
theorem isRandomWordEvolutionUpTo_prod_of_isCouplingCharFun [IsProbabilityMeasure P] [𝓖.IsRightContinuous] {κ : ℝ}
    (hκ : 0 < κ) {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (hnull : ∀ s, MeasurableSet s → P s = 0 → MeasurableSet[𝓖 0] s) (h𝒢 : 𝒢 ≤ 𝓖 0) {F : Set Ω}
    (hF : MeasurableSet[𝒢] F) {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ} (hxL : Measurable[𝒢] xL)
    (hxR : Measurable[𝒢] xR) (hxL0 : ∀ ω i, xL ω i ≤ 0) (hxR0 : ∀ ω j, 0 ≤ xR ω j)
    (hxLa : ∀ ω, Antitone (xL ω)) (hxRm : ∀ ω, Monotone (xR ω)) {W : ℝ≥0 → Ω → ℝ}
    (hW0 : ∀ ω, W 0 ω = 0) (hWc : ∀ ω, Continuous fun t => W t ω) (hWa : StronglyAdapted 𝓖 W)
    {ζ : Ω → ℝ≥0∞} (hζ : IsStoppingTime 𝓖 fun ω => (ζ ω : WithTop ℝ≥0)) {T : ℕ → Ω → ℝ≥0}
    (hT : Coupling.IsAnnouncingSeq 𝓖 P ζ T) {h : Ω → DistOn upperHalfPlaneOpens}
    (hint : ∀ φ : TestOn upperHalfPlaneOpens, Integrable (fun ω => h ω φ) P)
    (hcf : Coupling.MartMeans.IsCouplingCharFun κ ρL ρR P 𝓖 W (geomLW W xL) (geomRW W xR) ζ h)
    (hTζ : ∀ᵐ ω ∂P, ω ∈ F → ζ ω ≤ MartChar.thresholdTime ρL ρR (fun t => W t ω) (fun i t => geomLW W xL i t ω)
      (fun j t => geomRW W xR j t ω)) :
    ∃ (P₀ : Measure (ℕ → ℝ)) (_ : IsProbabilityMeasure P₀)
      (𝓦 : Filtration ℝ≥0 (inferInstance : MeasurableSpace (ℕ → ℝ))) (B : ℝ≥0 → Ω × (ℕ → ℝ) → ℝ),
      IsRandomWordEvolutionUpTo κ (P.prod P₀) (𝒢.comap Prod.fst) (Prod.fst ⁻¹' F)
        (fun p => xL p.1) (fun p => xR p.1) ρL ρR (WholeField.prodFiltration 𝓖 𝓦) (fun t p => W t p.1)
        (fun i t p => geomLW W xL i t p.1) (fun j t p => geomRW W xR j t p.1) B (fun p => ζ p.1) ∧
      (∀ p, Continuous fun t => B t p) ∧
      ∀ (p : Ω × (ℕ → ℝ)) (t : ℝ≥0), (t : WithTop ℝ≥0) ≤ ζ p.1 →
        B t p = MartChar.martProc (MartChar.jointρ ρL ρR) W (MartChar.jointV (geomLW W xL) (geomRW W xR)) t p.1 /
          Real.sqrt κ := by
  have hxL' : Measurable[𝓖 0] xL := hxL.mono h𝒢 le_rfl
  have hxR' : Measurable[𝓖 0] xR := hxR.mono h𝒢 le_rfl
  have hVLa : ∀ i, StronglyAdapted 𝓖 (geomLW W xL i) := fun i => stronglyAdapted_geomLW hWa hWc hxL' i
  have hVRa : ∀ j, StronglyAdapted 𝓖 (geomRW W xR j) := fun j => stronglyAdapted_geomRW hWa hWc hxR' j
  have hζm : ∀ t : ℝ≥0, MeasurableSet[𝓖 t] {ω | ζ ω ≤ t} := fun t => hζ t
  have hmart : ∀ z ∈ H, MartChar.IsLocalMartingaleBefore 𝓖 P
      (fun ω => min (QuantumZipper.swallowTime (MartChar.wpath W ω) z : WithTop ℝ≥0) (ζ ω))
      (MartChar.coupProc κ ρL ρR W (geomLW W xL) (geomRW W xR) z) := by
    intro z hz
    obtain ⟨G, hG, hGae, hloc⟩ := Coupling.MartMeans2.exists_isLocalMartingaleBefore_meanProcOn hnull
      (MartChar.adaptedBefore_of_stronglyAdapted hζm hWa)
      (fun i => MartChar.adaptedBefore_of_stronglyAdapted hζm (hVLa i))
      (fun j => MartChar.adaptedBefore_of_stronglyAdapted hζm (hVRa j))
      (Eventually.of_forall fun ω => ⟨hW0 ω, (hWc ω).continuousOn,
        ⟨fun i => (isForcePath_geomLW hWc xL ω i).1.continuousOn,
          fun j => (isForcePath_geomRW hWc xR ω j).1.continuousOn⟩,
        fun t _ => ⟨fun i => geomLW_le hWc xL ω t i, fun j => le_geomRW hWc xR ω t j⟩⟩)
      hT hint hcf (fun ω t => MartChar.meanExt κ ρL ρR (W t ω) (fun i => geomLW W xL i t ω)
        (fun j => geomRW W xR j t ω))
      (fun ω t => MartChar.isBoundedHarmonicExtension_meanExt κ ρL ρR _ _ _) hz
    exact isLocalMartingaleBefore_coupProc_of_meanProcOn hnull hG hGae
      (ConverseBefore.measurable_coupProc_zero hW0 (fun i => ((hVLa i 0).measurable.mono (𝓖.le 0) le_rfl))
        (fun j => ((hVRa j 0).measurable.mono (𝓖.le 0) le_rfl)) hz) hloc
  exact isRandomWordEvolutionUpTo_prod hκ h𝒢 hF hxL hxR hxL0 hxR0 hxLa hxRm hW0 hWc hWa hζ hmart hTζ

end OneShot

end InteractingSLE.Restart.StoppedK2
