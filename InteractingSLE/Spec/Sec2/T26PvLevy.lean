/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.StoppedK2Evol
import InteractingSLE.Spec.Sec2.T2426Cert
import MathFin.Probability.Martingales.MartingaleSetIntegral

/-!
# Theorem 2.6, the provider, part 5: Lévy before the stop and the local evolution

Packet PROVE-T26-PROVIDER. Specification, proof of Theorem 2.6 (`source/spec/p001-048.md` L984–L986) with the end of
the proof of Theorem 2.4 (L927–L931): once `M = W − W₀ + ½ ∑ ρⱼ (Vʲ − Vʲ₀)` and `M² − κ t` are local martingales before
the stop `T`, `B = M/√κ` is a Brownian motion up to `T` (Lévy), "extended independently thereafter", and the
occupation-density and Tanaka argument eliminates every singular force-point motion, giving Definition 2.1's
equations before `T`.

* `martingale_stoppedProcess_lifeLoc`: a continuous adapted local martingale before `T` from `0` that is bounded up to
  the landed localizers `PhaseSelFull.lifeLoc` is a martingale when stopped there
  (`PhaseSelFull.setIntegral_indicator_stoppedProcess_eq`);
* `exists_brownian_continuation_of_martProc`: the landed `Restart.ConverseBefore.exists_brownian_continuation_std`
  (same proof) with the two local martingales as inputs in place of the coupling means at all points;
* `isRandomWordEvolutionUpTo_prod_of_brownian`: the landed `Restart.StoppedK2.isRandomWordEvolutionUpTo_prod` (same
  proof, after its Brownian motion is obtained) for any such continued Brownian motion;
* **`isRandomWordEvolutionUpTo_prod_of_martProc`**: the two combined.

Provenance: the last three proofs are copies of the landed ones with these changes.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec2.T26Pv

open Sec7 MartChar Aux117 PhaseSelFull Restart.ConverseBefore Restart.StoppedK2 PocketTraversal

section Lifeloc

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {ι : Type*} [Fintype ι] {W : ℝ≥0 → Ω → ℝ} {V : ι → ℝ≥0 → Ω → ℝ} {T : Ω → WithTop ℝ≥0}

/-- **A local martingale before `T`, bounded up to `lifeLoc n`, stopped at `lifeLoc n` is a martingale.** -/
theorem martingale_stoppedProcess_lifeLoc [IsProbabilityMeasure P] (hWc : ∀ ω, Continuous fun t => W t ω)
    (hVc : ∀ j ω, Continuous fun t => V j t ω) (hWa : StronglyAdapted 𝓕 W) (hVa : ∀ j, StronglyAdapted 𝓕 (V j))
    (hT : IsStoppingTime 𝓕 T) {X : ℝ≥0 → Ω → ℝ} (hX : MartChar.IsLocalMartingaleBefore 𝓕 P T X)
    (hXc : ∀ ω, Continuous fun t => X t ω) (hXa : StronglyAdapted 𝓕 X) (hX0 : ∀ ω, X 0 ω = 0) (n : ℕ) {C : ℝ}
    (hC : ∀ ω ∈ initEvent W V n, ∀ t : ℝ≥0, (t : WithTop ℝ≥0) ≤ lifeLoc W V T n ω → |X t ω| ≤ C) :
    Martingale (stoppedProcess X (lifeLoc W V T n)) 𝓕 P := by
  classical
  set E := initEvent W V n with hEdef
  set τ := lifeLoc W V T n with hτdef
  have hτ : IsStoppingTime 𝓕 τ := isStoppingTime_lifeLoc hWc hVc hWa hVa hT n
  have hE : MeasurableSet[𝓕 0] E := measurableSet_initEvent hWa hVa n
  obtain ⟨hint, hset⟩ := setIntegral_indicator_stoppedProcess_eq hX
    (fun ω s _ => (hXc ω).continuousWithinAt) hτ hE (fun ω _ => lifeLoc_le_T W V T n ω)
    (fun ω _ u _ => (hXc ω).continuousWithinAt) hC
  have heq : ∀ t, E.indicator (stoppedProcess X τ t) = stoppedProcess X τ t := by
    intro t
    funext ω
    by_cases h : ω ∈ E
    · rw [Set.indicator_of_mem h]
    · rw [Set.indicator_of_notMem h]
      have h0 : τ ω = ((0 : ℝ≥0) : WithTop ℝ≥0) := lifeLoc_of_notMem h
      have hmin : (min (t : WithTop ℝ≥0) (τ ω)).untopA = 0 := by
        rw [h0, ← WithTop.coe_min, min_eq_right (zero_le : (0 : ℝ≥0) ≤ t)]
        rfl
      simp only [stoppedProcess, hmin, hX0]
  refine (martingale_iff_setIntegral_eq (𝒢 := 𝓕)).2 ⟨stronglyAdapted_stoppedProcess_of_continuous hXa hXc hτ,
    fun t => by rw [← heq t]; exact hint t, fun s t hst A hA => ?_⟩
  rw [← heq s, ← heq t]
  exact (hset s t hst A hA).symm

end Lifeloc

section Continuation

variable {nL nR : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}

/-- **The driving Brownian motion continued after `T`, from the two local martingales** (the landed
`Restart.ConverseBefore.exists_brownian_continuation_std`, same proof, with `M` and `M² − κ t` local martingales before
`T` as inputs). -/
theorem exists_brownian_continuation_of_martProc [IsProbabilityMeasure P] {κ : ℝ} (hκ : 0 < κ)
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} (hWc : ∀ ω, Continuous fun t => W t ω)
    (hWa : StronglyAdapted 𝓕 W) (hVLa : ∀ i, StronglyAdapted 𝓕 (VL i))
    (hVRa : ∀ i, StronglyAdapted 𝓕 (VR i))
    (hVLc : ∀ i ω, Continuous fun t => VL i t ω) (hVRc : ∀ i ω, Continuous fun t => VR i t ω)
    {T : Ω → WithTop ℝ≥0} (hT : IsStoppingTime 𝓕 T)
    (hM : MartChar.IsLocalMartingaleBefore 𝓕 P T (martProc (jointρ ρL ρR) W (jointV VL VR)))
    (hM2 : MartChar.IsLocalMartingaleBefore 𝓕 P T
      (fun t ω => martProc (jointρ ρL ρR) W (jointV VL VR) t ω ^ 2 - κ * t)) :
    ∃ (P₀ : Measure (ℕ → ℝ)) (_ : IsProbabilityMeasure P₀)
      (𝓦 : Filtration ℝ≥0 (inferInstance : MeasurableSpace (ℕ → ℝ))) (B : ℝ≥0 → Ω × (ℕ → ℝ) → ℝ),
      IsFilteredBrownianReal (WholeField.prodFiltration 𝓕 𝓦) B (P.prod P₀) ∧
        (∀ p, Continuous fun t => B t p) ∧
        ∀ (p : Ω × (ℕ → ℝ)) (t : ℝ≥0), (t : WithTop ℝ≥0) ≤ T p.1 →
          B t p = martProc (jointρ ρL ρR) W (jointV VL VR) t p.1 / Real.sqrt κ := by
  set V := jointV VL VR with hV
  set ρ := jointρ ρL ρR with hρ
  have hVc : ∀ j ω, Continuous fun t => V j t ω := fun j ω => by
    cases j with
    | inl i => exact hVLc i ω
    | inr i => exact hVRc i ω
  have hVa : ∀ j, StronglyAdapted 𝓕 (V j) := fun j => by
    cases j with
    | inl i => exact hVLa i
    | inr i => exact hVRa i
  set S : ℕ → Ω → ℝ≥0 := lifeLocN W V T with hS
  set Bv : ℝ≥0 → Ω → ℝ := fun t ω => martProc ρ W V t ω / Real.sqrt κ with hBv
  have hSmono : ∀ ω, Monotone fun m => S m ω := fun ω m m' hmm' => by
    have h := lifeLoc_mono (T := T) hWc hVc ω hmm'
    simp only at h
    rw [← coe_lifeLocN, ← coe_lifeLocN] at h
    exact WithTop.coe_le_coe.1 h
  have hSm : ∀ (m : ℕ) (u : ℝ≥0), Measurable[𝓕 u] fun ω => min u (S m ω) := by
    intro m u
    have hσ := isStoppingTime_lifeLoc hWc hVc hWa hVa hT m
    refine measurable_of_Iic (mδ := 𝓕 u) fun x => ?_
    by_cases hx : u ≤ x
    · have : (fun ω => min u (S m ω)) ⁻¹' Iic x = univ := by
        ext ω; simp only [mem_preimage, mem_Iic, mem_univ, iff_true]; exact (min_le_left _ _).trans hx
      rw [this]; exact @MeasurableSet.univ _ (𝓕 u)
    · push Not at hx
      have : (fun ω => min u (S m ω)) ⁻¹' Iic x = {ω | lifeLoc W V T m ω ≤ x} := by
        ext ω
        simp only [mem_preimage, mem_Iic, min_le_iff, mem_ofPred_eq, hS, ← coe_lifeLocN W V T m ω,
          WithTop.coe_le_coe]
        exact ⟨fun h => h.resolve_left (not_le.2 hx), Or.inr⟩
      rw [this]
      exact 𝓕.mono hx.le _ (hσ x)
  have hBvc : ∀ ω, Continuous fun t => Bv t ω := fun ω => (continuous_martProc hWc hVc ω).div_const _
  have hBv0 : ∀ ω, Bv 0 ω = 0 := fun ω => by simp [hBv, martProc, martValue]
  have hMa : StronglyAdapted 𝓕 (martProc ρ W V) := stronglyAdapted_martProc hWa hVa
  have hMc : ∀ ω, Continuous fun t => martProc ρ W V t ω := continuous_martProc hWc hVc
  have hM0 : ∀ ω, martProc ρ W V 0 ω = 0 := fun ω => by simp [martProc, martValue]
  have hbound : ∀ (m : ℕ) ω, ω ∈ initEvent W V m → ∀ t : ℝ≥0, (t : WithTop ℝ≥0) ≤ lifeLoc W V T m ω →
      |martProc ρ W V t ω| ≤ 2 * m + (∑ j, |ρ j|) * m := by
    intro m ω _ t ht
    have hmin : min t (lifeLocN W V T m ω) = t := by
      refine min_eq_left ?_
      rw [← coe_lifeLocN] at ht
      exact WithTop.coe_le_coe.1 ht
    have h := abs_martProc_lifeLocN_le (ρ := ρ) (T := T) hWc hVc m t ω
    rwa [hmin] at h
  have hMM : ∀ m : ℕ, Martingale (stoppedProcess (martProc ρ W V) (lifeLoc W V T m)) 𝓕 P ∧
      Martingale (stoppedProcess (fun t ω => martProc ρ W V t ω ^ 2 - κ * t) (lifeLoc W V T m)) 𝓕 P := by
    intro m
    refine ⟨martingale_stoppedProcess_lifeLoc hWc hVc hWa hVa hT hM hMc hMa hM0 m (hbound m), ?_⟩
    have hQc : ∀ ω, Continuous fun t : ℝ≥0 => martProc ρ W V t ω ^ 2 - κ * t := fun ω =>
      ((hMc ω).pow 2).sub (continuous_const.mul NNReal.continuous_coe)
    have hQa : StronglyAdapted 𝓕 (fun t ω => martProc ρ W V t ω ^ 2 - κ * t) := fun t =>
      (((hMa t).measurable.pow_const 2).sub measurable_const).stronglyMeasurable
    refine martingale_stoppedProcess_lifeLoc hWc hVc hWa hVa hT hM2 hQc hQa (fun ω => by simp [hM0 ω]) m
      (C := (2 * m + (∑ j, |ρ j|) * m) ^ 2 + κ * m) fun ω hω t ht => ?_
    have h1 := hbound m ω hω t ht
    have ht' : (t : ℝ) ≤ m := by
      have := ht.trans (lifeLoc_le_n W V T m ω)
      exact_mod_cast WithTop.coe_le_coe.1 this
    have hsq : martProc ρ W V t ω ^ 2 ≤ (2 * m + (∑ j, |ρ j|) * m) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    have hk : κ * (t : ℝ) ≤ κ * m := mul_le_mul_of_nonneg_left ht' hκ.le
    have hk0 : 0 ≤ κ * (t : ℝ) := mul_nonneg hκ.le t.coe_nonneg
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (martProc ρ W V t ω)]
  have hexp : ∀ (m : ℕ) (a : ℝ), Martingale (fun t ω => Real.exp (a * Bv (min t (S m ω)) ω -
      a ^ 2 * ((min t (S m ω) : ℝ≥0) : ℝ) / 2)) ((fun _ : ℕ => 𝓕) m) P := by
    intro m a
    exact martingale_exp_lifeLoc hκ hWc hVc (hMM m).1 (hMM m).2 a
  have hTC := WholeField.isTCExpMartingale_annClock (𝒢 := fun _ : ℕ => 𝓕) (fun _ => monotone_const)
    hSmono hSm hBvc hBv0 hexp
  rw [iSupFiltration_const] at hTC
  obtain ⟨P₀, hP₀, 𝓦, β, hβ, hβc, hβ0⟩ := exists_noiseBM
  obtain ⟨hB, hBc⟩ := WholeField.IsTCExpMartingale.isFilteredBrownianReal_complNoise hTC
    (LocalTime.isFilteredPreBrownian_of_isFilteredBrownianReal hβ) hβc hβ0
  refine ⟨P₀, hP₀, 𝓦, _, hB, hBc, fun p t ht => ?_⟩
  have hc : WholeField.annClock S t p.1 = t := annClock_lifeLocN_eq hWc hVc ht
  rw [WholeField.complNoise_of_eq hc]
  simp only [hc, hBv]

end Continuation

section Evolution

variable {nL nR : ℕ} {Ω : Type*} {𝒢 : MeasurableSpace Ω} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {𝓕 : Filtration ℝ≥0 mΩ}

/-- **(E-stop) from the two local martingales before the stop** (the landed
`Restart.StoppedK2.isRandomWordEvolutionUpTo_prod`, same proof, with `M` and `M² − κ t` local martingales before the
stop `T ≤ threshold` in place of the coupling means at all points): on `Ω × (ℕ → ℝ)` the coordinates are a local
integrated `SLE_κ(ρ)` evolution of the random word before `T`, driven by `M/√κ` continued by an independent Brownian
motion. -/
theorem isRandomWordEvolutionUpTo_prod_of_martProc [IsProbabilityMeasure P] {κ : ℝ} (hκ : 0 < κ)
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (h𝒢 : 𝒢 ≤ 𝓕 0) {F : Set Ω}
    (hF : MeasurableSet[𝒢] F) {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ} (hxL : Measurable[𝒢] xL)
    (hxR : Measurable[𝒢] xR) (hxL0 : ∀ ω i, xL ω i ≤ 0) (hxR0 : ∀ ω j, 0 ≤ xR ω j)
    (hxLa : ∀ ω, Antitone (xL ω)) (hxRm : ∀ ω, Monotone (xR ω)) {W : ℝ≥0 → Ω → ℝ}
    (hW0 : ∀ ω, W 0 ω = 0) (hWc : ∀ ω, Continuous fun t => W t ω) (hWa : StronglyAdapted 𝓕 W)
    {T : Ω → WithTop ℝ≥0} (hT : IsStoppingTime 𝓕 T)
    (hM : MartChar.IsLocalMartingaleBefore 𝓕 P T
      (martProc (jointρ ρL ρR) W (jointV (geomLW W xL) (geomRW W xR))))
    (hM2 : MartChar.IsLocalMartingaleBefore 𝓕 P T
      (fun t ω => martProc (jointρ ρL ρR) W (jointV (geomLW W xL) (geomRW W xR)) t ω ^ 2 - κ * t))
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
  have hpathL : ∀ ω i, MartChar.IsForcePath (fun t => W t ω) (fun t => VL i t ω) := fun ω i =>
    isForcePath_geomLW hWc xL ω i
  have hpathR : ∀ ω j, MartChar.IsForcePath (fun t => W t ω) (fun t => VR j t ω) := fun ω j =>
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
  obtain ⟨P₀, hP₀, 𝓦, B, hB, hBc, hBeq⟩ := exists_brownian_continuation_of_martProc hκ hWc hWa hVLa hVRa
    (fun i ω => (hpathL ω i).1) (fun j ω => (hpathR ω j).1) hT hM hM2
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

end InteractingSLE.Sec2.T26Pv
