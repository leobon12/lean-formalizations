/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PhaseSelFullWord
import InteractingSLE.Spec.Sec7.PocketTraversalCoords
import InteractingSLE.Spec.Sec7.PocketWordEvol

/-!
# (E2) Theorem 2.4's converse before a stopping time, on a standard Borel enlargement

Packet PROVE-DOMAINMARKOV7 (item E2 of `planning/handoffs/PROVE-DOMAINMARKOV5.md`). Specification §2 (Theorem 2.4 and
its converse, pp. 22–35), used through Aux. lemma 122 (p. 391) and the domain Markov restarts of §7 (p. 295).

A continuation read in a chart is known to be a coupling only **before a stopping time** `T` (its stop, or its
lifetime): its explicit coupling means are local martingales before `min (swallowTime z) T` only, so its normalized
martingale part `M/√κ` is a Brownian motion only up to `T`. The landed PROVE-STRIPSYS5 construction
(`PhaseSelFull.exists_brownian_continuation`) glues an independent Brownian motion after `T` on an enlarged space
`Ω × Ω₀`, but hides `Ω₀`; the kernel assembly K2 (`DomainMarkov.K2.ae_isOptionalHullCoupling_k`) needs a standard
Borel space. Here `Ω₀ = ℕ → ℝ` (with QuantumZipper's Gaussian product measure and the natural filtration of a
continuous Brownian motion on it), so `Ω × Ω₀` is standard Borel whenever `Ω` is.

* `exists_noiseBM`: a filtered Brownian motion with continuous paths from `0` on `ℕ → ℝ`;
* `exists_brownian_continuation_std`: PROVE-STRIPSYS5's glued Brownian motion `B = M^T/√κ + β − β^T` on
  `Ω × (ℕ → ℝ)`;
* `exists_isWordEntrance_before_std`: Definition 2.1's equations before `T` with the glued Brownian motion;
* `IsIntegratedSLEPath.congr_b`: Definition 2.1's path conditions only see the noise before the lifetime;
* **`isRandomWordEvolution_prod`** (E2): for geometric force points of a random initial word measurable for an
  initial σ-algebra `𝒢`, coupling means that are local martingales before `min (swallowTime z) T`, and a threshold
  time at most `T` on a `𝒢`-event `F`, the coordinates read on `Ω × (ℕ → ℝ)` form K2's input (E)
  (`Aux122Disint.IsRandomWordEvolution`) with lifetime the threshold time;
* `isLocalMartingaleBefore_of_ae_eq_zero`: a local martingale before `ζ` modified on a null event of the initial
  σ-algebra stays one (to turn `MartMeans2.exists_isLocalMartingaleBefore_meanProcOn`'s output into `hmart`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Restart

namespace ConverseBefore

open Sec7 MartChar Aux117 PhaseSelFull

/-! ### The noise space `ℕ → ℝ` -/

/-- **A filtered Brownian motion with continuous paths from `0` on the standard Borel space `ℕ → ℝ`**
(`OneForce.exists_filteredBrownian` with the space made explicit). -/
theorem exists_noiseBM :
    ∃ (P₀ : Measure (ℕ → ℝ)) (_ : IsProbabilityMeasure P₀)
      (𝓦 : Filtration ℝ≥0 (inferInstance : MeasurableSpace (ℕ → ℝ))) (β : ℝ≥0 → (ℕ → ℝ) → ℝ),
      IsFilteredBrownianReal 𝓦 β P₀ ∧ (∀ w, Continuous (β · w)) ∧ ∀ w, β 0 w = 0 := by
  obtain ⟨B₀, hB₀⟩ := QuantumZipper.BMExist.exists_isBrownianReal_stdP
  obtain ⟨B, hBm, hBc, hB0, hB, -⟩ := QuantumZipper.RS.exists_good_version0 hB₀
  exact ⟨LQGDimension.ExistAsm.stdP, inferInstance, Bessel.natFilt hBm, B,
    OneForce.isFilteredBrownianReal_natFilt hB hBm, hBc, hB0⟩

section Continuation

variable {nL nR : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}

/-- **The driving Brownian motion continued after `T`, on `Ω × (ℕ → ℝ)`** (PROVE-STRIPSYS5's
`PhaseSelFull.exists_brownian_continuation`, same proof, with the noise space `ℕ → ℝ` of `exists_noiseBM`). The
coordinates are continuous adapted processes on all of `ℝ≥0` with the deterministic properties of force images, and
every explicit coupling mean is a local martingale before swallowing and before the stopping time `T`. -/
theorem exists_brownian_continuation_std [IsProbabilityMeasure P] {κ : ℝ} (hκ : 0 < κ)
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} (hW0 : ∀ ω, W 0 ω = 0) (hWc : ∀ ω, Continuous fun t => W t ω)
    (hWa : StronglyAdapted 𝓕 W) (hVLa : ∀ i, StronglyAdapted 𝓕 (VL i))
    (hVRa : ∀ i, StronglyAdapted 𝓕 (VR i)) (hordL : ∀ ω t i, VL i t ω ≤ W t ω)
    (hordR : ∀ ω t i, W t ω ≤ VR i t ω)
    (hpathL : ∀ ω i, IsForcePath (fun t => W t ω) (fun t => VL i t ω))
    (hpathR : ∀ ω i, IsForcePath (fun t => W t ω) (fun t => VR i t ω))
    {T : Ω → WithTop ℝ≥0} (hT : IsStoppingTime 𝓕 T)
    (hmart : ∀ z ∈ H, IsLocalMartingaleBefore 𝓕 P
      (fun ω => min (QuantumZipper.swallowTime (wpath W ω) z : WithTop ℝ≥0) (T ω))
      (coupProc κ ρL ρR W VL VR z)) :
    ∃ (P₀ : Measure (ℕ → ℝ)) (_ : IsProbabilityMeasure P₀)
      (𝓦 : Filtration ℝ≥0 (inferInstance : MeasurableSpace (ℕ → ℝ))) (B : ℝ≥0 → Ω × (ℕ → ℝ) → ℝ),
      IsFilteredBrownianReal (WholeField.prodFiltration 𝓕 𝓦) B (P.prod P₀) ∧
        (∀ p, Continuous fun t => B t p) ∧
        ∀ (p : Ω × (ℕ → ℝ)) (t : ℝ≥0), (t : WithTop ℝ≥0) ≤ T p.1 →
          B t p = martProc (jointρ ρL ρR) W (jointV VL VR) t p.1 / Real.sqrt κ := by
  set V := jointV VL VR with hV
  set ρ := jointρ ρL ρR with hρ
  have hVLc : ∀ i ω, Continuous fun t => VL i t ω := fun i ω => (hpathL ω i).1
  have hVRc : ∀ i ω, Continuous fun t => VR i t ω := fun i ω => (hpathR ω i).1
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
  have hexp : ∀ (m : ℕ) (a : ℝ), Martingale (fun t ω => Real.exp (a * Bv (min t (S m ω)) ω -
      a ^ 2 * ((min t (S m ω) : ℝ≥0) : ℝ) / 2)) ((fun _ : ℕ => 𝓕) m) P := by
    intro m a
    have hMM := martingale_martProc_lifeLoc hκ hW0 hWc hWa hVLa hVRa hordL hordR hpathL hpathR hT hmart m
    exact martingale_exp_lifeLoc hκ hWc hVc hMM.1 hMM.2 a
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

/-! ### Definition 2.1's path conditions only see the noise before the lifetime -/

section Path

variable {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {w b b' : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-- **`IsIntegratedSLEPath` depends on the noise path only before the lifetime.** -/
theorem IsIntegratedSLEPath.congr_b (h : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ)
    (hb : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → b t = b' t) : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b' ζ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, fun t ht => by rw [← hb t ht]; exact h13 t ht,
    h14, h15, h16, h17, h18, h19, h20⟩

end Path

/-! ### (E2): K2's input (E) on the enlargement -/

section Evolution

open PocketTraversal

variable {nL nR : ℕ} {Ω : Type*} {𝒢 : MeasurableSpace Ω} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {𝓕 : Filtration ℝ≥0 mΩ}

/-- **(E2) Theorem 2.4's converse before a stopping time, in K2's input form** (`Aux122Disint.IsRandomWordEvolution`,
the input (E) of `DomainMarkov.K2.ae_isOptionalHullCoupling_k`). Let `W` be a continuous adapted driver from `0`
(frozen after the stop, if any), `xL ≤ 0 ≤ xR` a sorted random initial word measurable for an initial σ-algebra
`𝒢 ≤ 𝓕₀`, and let the force points be the geometric images (`geomLW`, `geomRW`). If every explicit coupling mean is a
local martingale before `min (swallowTime z) T` for a stopping time `T`, and on a `𝒢`-event `F` the threshold time of
the word comes at or before `T` almost surely, then on `Ω × (ℕ → ℝ)` (with an independent Brownian motion on the
second factor, glued after `T`) the coordinates read through the first factor form an integrated `SLE_κ(ρ)` evolution
of the random word on `F`, with initial σ-algebra `𝒢` read through the first factor and lifetime the threshold time.
The Brownian motion is `M/√κ` up to `T`. -/
theorem isRandomWordEvolution_prod [IsProbabilityMeasure P] {κ : ℝ} (hκ : 0 < κ)
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (h𝒢 : 𝒢 ≤ 𝓕 0) {F : Set Ω}
    (hF : MeasurableSet[𝒢] F) {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ} (hxL : Measurable[𝒢] xL)
    (hxR : Measurable[𝒢] xR) (hxL0 : ∀ ω i, xL ω i ≤ 0) (hxR0 : ∀ ω j, 0 ≤ xR ω j)
    (hxLa : ∀ ω, Antitone (xL ω)) (hxRm : ∀ ω, Monotone (xR ω)) {W : ℝ≥0 → Ω → ℝ}
    (hW0 : ∀ ω, W 0 ω = 0) (hWc : ∀ ω, Continuous fun t => W t ω) (hWa : StronglyAdapted 𝓕 W)
    {T : Ω → WithTop ℝ≥0} (hT : IsStoppingTime 𝓕 T)
    (hmart : ∀ z ∈ H, IsLocalMartingaleBefore 𝓕 P
      (fun ω => min (QuantumZipper.swallowTime (wpath W ω) z : WithTop ℝ≥0) (T ω))
      (coupProc κ ρL ρR W (geomLW W xL) (geomRW W xR) z))
    (hTζ : ∀ᵐ ω ∂P, ω ∈ F → thresholdTime ρL ρR (fun t => W t ω) (fun i t => geomLW W xL i t ω)
      (fun j t => geomRW W xR j t ω) ≤ T ω) :
    ∃ (P₀ : Measure (ℕ → ℝ)) (_ : IsProbabilityMeasure P₀)
      (𝓦 : Filtration ℝ≥0 (inferInstance : MeasurableSpace (ℕ → ℝ))) (B : ℝ≥0 → Ω × (ℕ → ℝ) → ℝ),
      Aux122Disint.IsRandomWordEvolution κ (P.prod P₀) (𝒢.comap Prod.fst) (Prod.fst ⁻¹' F)
        (fun p => xL p.1) (fun p => xR p.1) ρL ρR (WholeField.prodFiltration 𝓕 𝓦) (fun t p => W t p.1)
        (fun i t p => geomLW W xL i t p.1) (fun j t p => geomRW W xR j t p.1) B
        (fun p => thresholdTime ρL ρR (fun t => W t p.1) (fun i t => geomLW W xL i t p.1)
          (fun j t => geomRW W xR j t p.1)) ∧
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
  have hζΩ := measurableSet_thresholdTime_le (𝓕 := 𝓕) (ρL := ρL) (ρR := ρR) hWc
    (fun i ω => (hpathL ω i).1) (fun j ω => (hpathR ω j).1) hWa hVLa hVRa hmergeL hmergeR
  have hζ : ∀ t : ℝ≥0, MeasurableSet[𝓖 t] {p : Ω × (ℕ → ℝ) | thresholdTime ρL ρR (fun s => W s p.1)
      (fun i s => VL i s p.1) (fun j s => VR j s p.1) ≤ t} := fun t =>
    WholeField.comap_fst_le_prodFiltration 𝓕 𝓦 t _ ⟨_, hζΩ t, rfl⟩
  have hfst : Measurable[𝒢.comap Prod.fst, 𝒢] (Prod.fst : Ω × (ℕ → ℝ) → Ω) := Measurable.of_comap_le le_rfl
  refine ⟨(MeasurableSpace.comap_mono h𝒢).trans (WholeField.comap_fst_le_prodFiltration 𝓕 𝓦 0),
    ⟨F, hF, rfl⟩, hxL.comp hfst, hxR.comp hfst, hB,
    MartChar.adaptedBefore_of_stronglyAdapted hζ (stronglyAdapted_fst hWa),
    fun i => MartChar.adaptedBefore_of_stronglyAdapted hζ (stronglyAdapted_fst (hVLa i)),
    fun j => MartChar.adaptedBefore_of_stronglyAdapted hζ (stronglyAdapted_fst (hVRa j)), ?_⟩
  have hTζ' : ∀ᵐ p ∂(P.prod P₀), p.1 ∈ F → thresholdTime ρL ρR (fun t => W t p.1)
      (fun i t => VL i t p.1) (fun j t => VR j t p.1) ≤ T p.1 :=
    Measure.quasiMeasurePreserving_fst.ae hTζ
  filter_upwards [hL, hR, hTζ'] with p hLp hRp hTp hpF
  have hle := hTp hpF
  set b' : ℝ≥0 → ℝ := fun t => (W t p.1 + (1 / 2) * ((∑ i, ρL i * (VL i t p.1 - xL p.1 i)) +
    ∑ j, ρR j * (VR j t p.1 - xR p.1 j))) / Real.sqrt κ with hb'
  have hw' : ∀ t, W t p.1 = Real.sqrt κ * b' t
      - (1 / 2) * ((∑ i, ρL i * (VL i t p.1 - xL p.1 i)) + ∑ j, ρR j * (VR j t p.1 - xR p.1 j)) :=
    fun t => by simp only [hb']; field_simp; ring
  have hlt : ∀ t : ℝ≥0, (t : ℝ≥0∞) < thresholdTime ρL ρR (fun t => W t p.1) (fun i t => VL i t p.1)
      (fun j t => VR j t p.1) → (t : WithTop ℝ≥0) ≤ T p.1 := fun t ht => ht.le.trans hle
  have hnot : ∀ t : ℝ≥0, (t : ℝ≥0∞) < thresholdTime ρL ρR (fun t => W t p.1) (fun i t => VL i t p.1)
      (fun j t => VR j t p.1) → ∀ u : ℝ≥0, 0 < u → u ≤ t →
        ColliderNe ρL (fun t => W t p.1) (fun i t => VL i t p.1) u ∧
          ColliderNe ρR (fun t => W t p.1) (fun j t => VR j t p.1) u :=
    fun t ht u _ hu => colliderNe_of_not_thresholdCondition
      (notMem_thresholdSet_of_lt ((ENNReal.coe_le_coe.2 hu).trans_lt ht))
  have hE := isIntegratedSLEPath_of_forceDefect_eq_zero (b := b') (hW0 p.1) (fun i => hVL0 p.1 i)
    (fun j => hVR0 p.1 j) (hWc p.1) (hpathL p.1) (hpathR p.1) (hordL p.1) (hordR p.1) (hidxL p.1) (hidxR p.1)
    (hmergeL p.1) (hmergeR p.1) hw'
    (fun t ht i => hLp t (hlt t ht) (fun u hu hut => (hnot t ht u hu hut).1) i)
    (fun t ht j => hRp t (hlt t ht) (fun u hu hut => (hnot t ht u hu hut).2) j)
  refine IsIntegratedSLEPath.congr_b hE fun t ht => ?_
  have h := hW' t p (hlt t ht)
  simp only [hb']
  rw [div_eq_iff hsk]
  linarith

end Evolution

/-! ### Local martingales before a lifetime, modified on a null initial event -/

section Null

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}

open scoped Classical in
/-- **A local martingale before `ζ`, modified on a null initial event, stays one.** If `Y` is a local martingale before
`ζ`, `Y = X` on an event `G ∈ 𝓕₀` of full measure, `X₀` is measurable, and `𝓕₀` contains the measurable null sets,
then `X` is a local martingale before `ζ` (localize by `σₙ` on `G` and by `0` off `G`). This turns the output of
`MartMeans2.exists_isLocalMartingaleBefore_meanProcOn` (the mean set to `0` off a full initial event) into the
hypothesis `hmart` of `isRandomWordEvolution_prod`. -/
theorem isLocalMartingaleBefore_of_eqOn (hnull : ∀ s, MeasurableSet s → P s = 0 → MeasurableSet[𝓕 0] s)
    {G : Set Ω} (hG : MeasurableSet[𝓕 0] G) (hGae : ∀ᵐ ω ∂P, ω ∈ G) {X Y : ℝ≥0 → Ω → ℝ}
    (hX0 : Measurable (X 0)) (hXY : ∀ ω ∈ G, ∀ t, Y t ω = X t ω) {ζ : Ω → WithTop ℝ≥0}
    (h : IsLocalMartingaleBefore 𝓕 P ζ Y) : IsLocalMartingaleBefore 𝓕 P ζ X := by
  obtain ⟨σ, hσ, hσζ, hσev, hσm⟩ := h
  set σ' : ℕ → Ω → WithTop ℝ≥0 := fun n ω => if ω ∈ G then σ n ω else 0 with hσ'
  have hGc0 : P Gᶜ = 0 := ae_iff.1 hGae
  have hGm : MeasurableSet G := 𝓕.le 0 _ hG
  have hst : ∀ n, IsStoppingTime 𝓕 (σ' n) := fun n t => by
    have e : {ω | σ' n ω ≤ t} = (G ∩ {ω | σ n ω ≤ t}) ∪ Gᶜ := by
      ext ω
      by_cases hω : ω ∈ G
      · simp [hσ', hω]
      · simp only [hσ', hω, ↓reduceIte, mem_ofPred_eq, mem_union, mem_inter_iff, mem_compl_iff,
          not_false_eq_true, or_true, iff_true]
        exact zero_le
    rw [e]
    exact ((𝓕.mono zero_le _ hG).inter (hσ n t)).union (𝓕.mono zero_le _ hG.compl)
  refine ⟨σ', hst, fun n ω => ?_, ?_, fun n => ?_⟩
  · by_cases hω : ω ∈ G
    · simp only [hσ', hω, ↓reduceIte]; exact hσζ n ω
    · simp only [hσ', hω, ↓reduceIte]; exact zero_le
  · filter_upwards [hσev, hGae] with ω h hω r hr
    simp only [hσ', hω, ↓reduceIte]
    exact h r hr
  · have hm := hσm n
    have hon : ∀ ω ∈ G, ∀ t, stoppedProcess X (σ' n) t ω = stoppedProcess Y (σ n) t ω := fun ω hω t => by
      simp only [stoppedProcess, hσ', hω, ↓reduceIte]
      exact (hXY ω hω _).symm
    have hoff : ∀ ω, ω ∉ G → ∀ t, stoppedProcess X (σ' n) t ω = X 0 ω := fun ω hω t => by
      simp only [stoppedProcess, hσ', hω, ↓reduceIte]
      congr 1
      rw [min_eq_right zero_le]
      rfl
    have hae : ∀ t, stoppedProcess X (σ' n) t =ᵐ[P] stoppedProcess Y (σ n) t := fun t => by
      filter_upwards [hGae] with ω hω using hon ω hω t
    have hadapt : StronglyAdapted 𝓕 (stoppedProcess X (σ' n)) := fun t => by
      have hYt : Measurable[𝓕 t] (stoppedProcess Y (σ n) t) := (hm.1 t).measurable
      refine Measurable.stronglyMeasurable fun A hA => ?_
      have e : stoppedProcess X (σ' n) t ⁻¹' A =
          (G ∩ stoppedProcess Y (σ n) t ⁻¹' A) ∪ (Gᶜ ∩ X 0 ⁻¹' A) := by
        ext ω
        by_cases hω : ω ∈ G
        · simp [hon ω hω t, hω]
        · simp [hoff ω hω t, hω]
      rw [e]
      refine ((𝓕.mono zero_le _ hG).inter (hYt hA)).union (𝓕.mono zero_le _ ?_)
      exact hnull _ (hGm.compl.inter (hX0 hA)) (measure_mono_null inter_subset_left hGc0)
    exact ⟨hadapt, fun i j hij =>
      (condExp_congr_ae (hae j)).trans ((hm.2 i j hij).trans (hae i).symm)⟩

end Null

end ConverseBefore

end Restart

end InteractingSLE
