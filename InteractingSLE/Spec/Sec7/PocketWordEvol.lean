/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PhaseSelAdaptCont
import InteractingSLE.Spec.Sec7.Aux122DisintEvol

/-!
# §7.4, Aux. lemma 122's SDE conclusion with a random initial word

Packet PROVE-STRIPSYS6 (specification §7.4, Aux. lemma 122 and its proof, `source/spec/p385-432.md` L104–L131,
pp. 389–391: "The trace consequently has the canonical `SLE_k(r)` driving law up to its continuation threshold and
lifetime, in the stated filtration. Conditional on initial information fixing the word and its marked positions, the
coordinates satisfy this SDE with Brownian noise independent of that initial information"; "Applying Theorem 2.4 now
uses the actual admissible seed data and gives the canonical integrated SDE up to the continuation threshold").

The landed converse of Theorem 2.4 (`Aux117.isIntegratedSLEEvolution_of_coupProc`) fixes the initial word
deterministically. Here the initial positions are random (`𝓕₀`-measurable), the form
`Aux122Disint.IsRandomWordEvolution` that `Lemma725Ref.PocketWordEvolution` consumes:

* `isFilteredBrownianReal_martProc_random`: Lévy's characterization along the localizations `lifeLoc` of
  PROVE-STRIPSYS5 (bounded on the time-zero events `{|W₀| + ∑|V₀| < n}`), so the normalized martingale part
  `M/√κ` is an `𝓕`-Brownian motion on `Ω` itself (no continuation is needed when the means are local martingales
  until swallowing, for all times);
* **`isRandomWordEvolution_of_coupProc`**: the coordinates form an integrated `SLE_κ(ρ)` evolution of the random
  initial word `(V₀)`, with initial σ-algebra `𝓕₀`, lifetime the continuation threshold;
* **`aux122_isRandomWordEvolution`**: Aux. lemma 122 with globally defined coordinates and a random initial word
  (seeds at `0`, other marks strictly away from `0`, no measurability of the phase assumed): there is a time-zero event
  `A` of probability one on which the phase vanishes, and conditionally on `A` the coordinates form an integrated
  evolution of their random initial word, with initial σ-algebra the time-zero σ-algebra.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec7

namespace PocketWord

open MartChar Aux117 PhaseSel PhaseSelFull

variable {nL nR : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}

theorem isStoppingTime_top : IsStoppingTime 𝓕 fun _ : Ω => (⊤ : WithTop ℝ≥0) := fun t => by
  have e : {ω : Ω | (⊤ : WithTop ℝ≥0) ≤ (t : WithTop ℝ≥0)} = ∅ := by
    ext ω
    simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_le]
    exact WithTop.coe_lt_top t
  rw [e]
  exact @MeasurableSet.empty _ (𝓕 t)

/-- **Lévy's characterization with a random initial word**: if the explicit coupling means are local martingales
until swallowing, the normalized martingale part `M/√κ` of the driver is an `𝓕`-Brownian motion (the localizations
`lifeLoc` of `PhaseSelFull` handle the random initial positions). -/
theorem isFilteredBrownianReal_martProc_random [IsProbabilityMeasure P] {κ : ℝ} (hκ : 0 < κ)
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} (hW0 : ∀ ω, W 0 ω = 0) (hWc : ∀ ω, Continuous fun t => W t ω)
    (hWa : StronglyAdapted 𝓕 W) (hVLa : ∀ i, StronglyAdapted 𝓕 (VL i))
    (hVRa : ∀ i, StronglyAdapted 𝓕 (VR i)) (hordL : ∀ ω t i, VL i t ω ≤ W t ω)
    (hordR : ∀ ω t i, W t ω ≤ VR i t ω)
    (hpathL : ∀ ω i, IsForcePath (fun t => W t ω) (fun t => VL i t ω))
    (hpathR : ∀ ω i, IsForcePath (fun t => W t ω) (fun t => VR i t ω))
    (hmart : ∀ z ∈ H, IsLocalMartingaleBefore 𝓕 P
      (fun ω => (QuantumZipper.swallowTime (wpath W ω) z : WithTop ℝ≥0)) (coupProc κ ρL ρR W VL VR z)) :
    IsFilteredBrownianReal 𝓕 (fun t ω => martProc (jointρ ρL ρR) W (jointV VL VR) t ω / Real.sqrt κ) P := by
  set V := jointV VL VR with hV
  set ρ := jointρ ρL ρR with hρ
  have hVc : ∀ j ω, Continuous fun t => V j t ω := fun j ω => by
    cases j with
    | inl i => exact (hpathL ω i).1
    | inr i => exact (hpathR ω i).1
  have hVa : ∀ j, StronglyAdapted 𝓕 (V j) := fun j => by
    cases j with
    | inl i => exact hVLa i
    | inr i => exact hVRa i
  have hmart' : ∀ z ∈ H, IsLocalMartingaleBefore 𝓕 P
      (fun ω => min (QuantumZipper.swallowTime (wpath W ω) z : WithTop ℝ≥0) ((fun _ => ⊤) ω))
      (coupProc κ ρL ρR W VL VR z) := fun z hz =>
    PhaseSelAdapt.isLocalMartingaleBefore_congr_life (fun ω => (min_top_right _).symm) (hmart z hz)
  set σ : ℕ → Ω → WithTop ℝ≥0 := fun n => lifeLoc W V (fun _ => ⊤) n with hσ_def
  have hσst : ∀ n, IsStoppingTime 𝓕 (σ n) := fun n =>
    isStoppingTime_lifeLoc hWc hVc hWa hVa isStoppingTime_top n
  have hσT : ∀ n ω, σ n ω ≤ ((n : ℝ≥0) : WithTop ℝ≥0) := fun n ω => lifeLoc_le_n W V _ n ω
  have hσ : IsLocalizingSequence 𝓕 σ P := {
    isStoppingTime := hσst
    mono := ae_of_all _ fun ω => PhaseSelFull.lifeLoc_mono hWc hVc ω
    tendsto_top := ae_of_all _ fun ω => by
      rw [WithTop.tendsto_nhds_top_iff _]
      intro c
      obtain ⟨u, hu⟩ := exists_nat_gt c
      filter_upwards [PhaseSelFull.eventually_le_lifeLoc (T := fun _ => ⊤) hWc hVc (u := (u : ℝ≥0) + 1)
        (ω := ω) le_top] with n hn
      refine lt_of_lt_of_le ?_ hn
      exact WithTop.coe_lt_coe.2 (lt_of_lt_of_le hu (by simp)) }
  have hmm := fun n => martingale_martProc_lifeLoc hκ hW0 hWc hWa hVLa hVRa hordL hordR hpathL hpathR
    isStoppingTime_top hmart' n
  have hM : ∀ n, Martingale (stoppedProcess (martProc ρ W V) (σ n)) 𝓕 P := fun n => (hmm n).1
  have hMsq : ∀ n, Martingale (stoppedProcess (fun t ω => martProc ρ W V t ω ^ 2 - κ * t) (σ n)) 𝓕 P :=
    fun n => (hmm n).2
  -- the normalized processes (as in `MartChar.isFilteredBrownianReal_martProc_div_sqrt`)
  set B : ℝ≥0 → Ω → ℝ := fun t ω => martProc ρ W V t ω / Real.sqrt κ with hB_def
  have hsq : Real.sqrt κ ^ 2 = κ := Real.sq_sqrt hκ.le
  have hB0 : ∀ ω, B 0 ω = 0 := fun ω => by simp [hB_def, martProc, martValue]
  have hBc : ∀ ω, Continuous fun t => B t ω := fun ω =>
    (continuous_martProc hWc hVc ω).div_const _
  have hBa : StronglyAdapted 𝓕 B := fun t =>
    ((stronglyAdapted_martProc (ρ := ρ) hWa hVa t).measurable.div_const _).stronglyMeasurable
  have hB2_0 : ∀ ω, B 0 ω ^ 2 - ((0 : ℝ≥0) : ℝ) = 0 := fun ω => by simp [hB0]
  have hBloc : IsLocalMartingale B 𝓕 P := by
    refine ⟨σ, hσ, fun n => ?_⟩
    rw [stoppedProcess_indicator_eq_of_zero hB0]
    refine ⟨?_, fun ω => (continuous_stoppedProcess hBc (hσT n) ω).isCadlag⟩
    have heq : stoppedProcess B (σ n) = (Real.sqrt κ)⁻¹ • stoppedProcess (martProc ρ W V) (σ n) := by
      funext t ω
      simp only [hB_def, stoppedProcess, Pi.smul_apply, smul_eq_mul]
      rw [div_eq_inv_mul]
    rw [heq]
    exact (hM n).smul _
  have hB2loc : IsLocalMartingale (fun t ω => B t ω ^ 2 - (t : ℝ)) 𝓕 P := by
    refine ⟨σ, hσ, fun n => ?_⟩
    rw [stoppedProcess_indicator_eq_of_zero hB2_0]
    refine ⟨?_, fun ω => (continuous_stoppedProcess (X := fun t ω => B t ω ^ 2 - (t : ℝ))
      (fun ω => ((hBc ω).pow 2).sub NNReal.continuous_coe) (hσT n) ω).isCadlag⟩
    have heq : stoppedProcess (fun t ω => B t ω ^ 2 - (t : ℝ)) (σ n)
        = κ⁻¹ • stoppedProcess (fun t ω => martProc ρ W V t ω ^ 2 - κ * t) (σ n) := by
      funext t ω
      simp only [hB_def, stoppedProcess, Pi.smul_apply, smul_eq_mul]
      rw [div_pow, hsq]
      field_simp
    rw [heq]
    exact (hMsq n).smul _
  have hpre := MathFin.LevyCharacterization.isFilteredPreBrownian_of_localMartingale hBa hBc hB0
    hBloc hB2loc
  have hbm := MathFin.LevyCharacterization.isBrownianReal_of_localMartingale hBa hBc hB0
    hBloc hB2loc
  exact ⟨hbm, hBa.adapted, fun s t hst => hpre.indep s t hst⟩

/-- **The converse of Theorem 2.4 with a random initial word** (`Aux117.isIntegratedSLEEvolution_of_coupProc` with the
initial positions `𝓕₀`-measurable instead of deterministic): continuous adapted coordinates with the deterministic
properties of geometric force images, whose explicit coupling means are local martingales until swallowing, form an
integrated `SLE_κ(ρ)` evolution of their random initial word `(V₀)`, with initial σ-algebra `𝓕₀`, Brownian motion
`M/√κ` and lifetime the continuation threshold (`Aux122Disint.IsRandomWordEvolution`). -/
theorem isRandomWordEvolution_of_coupProc [IsProbabilityMeasure P] {κ : ℝ} (hκ : 0 < κ)
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} (hW0 : ∀ ω, W 0 ω = 0) (hWc : ∀ ω, Continuous fun t => W t ω)
    (hWa : StronglyAdapted 𝓕 W) (hVLa : ∀ i, StronglyAdapted 𝓕 (VL i))
    (hVRa : ∀ i, StronglyAdapted 𝓕 (VR i)) (hordL : ∀ ω t i, VL i t ω ≤ W t ω)
    (hordR : ∀ ω t i, W t ω ≤ VR i t ω)
    (hpathL : ∀ ω i, IsForcePath (fun t => W t ω) (fun t => VL i t ω))
    (hpathR : ∀ ω i, IsForcePath (fun t => W t ω) (fun t => VR i t ω))
    (hantiL : ∀ ω i, Antitone fun t => VL i t ω) (hmonoR : ∀ ω j, Monotone fun t => VR j t ω)
    (hidxL : ∀ ω t, Antitone fun i => VL i t ω) (hidxR : ∀ ω t, Monotone fun j => VR j t ω)
    (hmergeL : ∀ ω i j s t, s ≤ t → VL i s ω = VL j s ω → VL i t ω = VL j t ω)
    (hmergeR : ∀ ω i j s t, s ≤ t → VR i s ω = VR j s ω → VR i t ω = VR j t ω)
    (hsep : ∀ ω t, 0 < t → ∀ i j, VL i t ω = W t ω → VR j t ω ≠ W t ω)
    (hmart : ∀ z ∈ H, IsLocalMartingaleBefore 𝓕 P
      (fun ω => (QuantumZipper.swallowTime (wpath W ω) z : WithTop ℝ≥0)) (coupProc κ ρL ρR W VL VR z)) :
    Aux122Disint.IsRandomWordEvolution κ P (𝓕 0) univ (fun ω i => VL i 0 ω) (fun ω j => VR j 0 ω) ρL ρR 𝓕
      W VL VR (fun t ω => martProc (jointρ ρL ρR) W (jointV VL VR) t ω / Real.sqrt κ)
      (fun ω => thresholdTime ρL ρR (fun t => W t ω) (fun i t => VL i t ω) (fun j t => VR j t ω)) := by
  have hVLc : ∀ i ω, Continuous fun t => VL i t ω := fun i ω => (hpathL ω i).1
  have hVRc : ∀ i ω, Continuous fun t => VR i t ω := fun i ω => (hpathR ω i).1
  have hB := isFilteredBrownianReal_martProc_random hκ hW0 hWc hWa hVLa hVRa hordL hordR hpathL hpathR hmart
  have hBpre := LocalTime.isFilteredPreBrownian_of_isFilteredBrownianReal hB
  have hsk : Real.sqrt κ ≠ 0 := (Real.sqrt_pos.2 hκ).ne'
  have hdec : ∀ (t : ℝ≥0) ω, (t : WithTop ℝ≥0) ≤ (fun _ : Ω => (⊤ : WithTop ℝ≥0)) ω →
      W t ω = Real.sqrt κ * (martProc (jointρ ρL ρR) W (jointV VL VR) t ω / Real.sqrt κ)
        - (1 / 2) * ((∑ i, ρL i * (VL i t ω - VL i 0 ω)) + ∑ j, ρR j * (VR j t ω - VR j 0 ω)) :=
    fun t ω _ => driver_eq_martProc hκ hW0 t ω
  have hL := ae_forceDefect_left_eq_zero_before (xL := fun ω i => VL i 0 ω) (xR := fun ω j => VR j 0 ω)
    hsk hBpre isStoppingTime_top hdec hWc hWa hVLa hVRa hpathL hpathR hordL hantiL hmonoR hmergeL hidxL hsep
  have hR := ae_forceDefect_right_eq_zero_before (xL := fun ω i => VL i 0 ω) (xR := fun ω j => VR j 0 ω)
    hsk hBpre isStoppingTime_top hdec hWc hWa hVLa hVRa hpathL hpathR hordR hantiL hmonoR hmergeR hidxR hsep
  have hζ := measurableSet_thresholdTime_le (ρL := ρL) (ρR := ρR) hWc hVLc hVRc hWa hVLa hVRa hmergeL hmergeR
  refine ⟨le_rfl, MeasurableSet.univ, (@measurable_pi_iff Ω (Fin nL) _ (𝓕 0) _ _).2 fun i => (hVLa i 0).measurable,
    (@measurable_pi_iff Ω (Fin nR) _ (𝓕 0) _ _).2 fun j => (hVRa j 0).measurable, hB,
    adaptedBefore_of_stronglyAdapted hζ hWa, fun i => adaptedBefore_of_stronglyAdapted hζ (hVLa i),
    fun j => adaptedBefore_of_stronglyAdapted hζ (hVRa j), ?_⟩
  filter_upwards [hL, hR] with ω hLω hRω _
  have hnot : ∀ t : ℝ≥0, (t : ℝ≥0∞) < thresholdTime ρL ρR (fun t => W t ω) (fun i t => VL i t ω)
      (fun j t => VR j t ω) → ∀ u : ℝ≥0, 0 < u → u ≤ t →
        ColliderNe ρL (fun t => W t ω) (fun i t => VL i t ω) u ∧
          ColliderNe ρR (fun t => W t ω) (fun j t => VR j t ω) u :=
    fun t ht u _ hu => colliderNe_of_not_thresholdCondition
      (notMem_thresholdSet_of_lt ((ENNReal.coe_le_coe.2 hu).trans_lt ht))
  exact isIntegratedSLEPath_of_forceDefect_eq_zero (hW0 ω) (fun i => rfl) (fun j => rfl) (hWc ω) (hpathL ω)
    (hpathR ω) (hordL ω) (hordR ω) (hidxL ω) (hidxR ω) (hmergeL ω) (hmergeR ω) (fun t => hdec t ω le_top)
    (fun t ht i => hLω t le_top (fun u hu hut => (hnot t ht u hu hut).1) i)
    (fun t ht j => hRω t le_top (fun u hu hut => (hnot t ht u hu hut).2) j)

/-- **Aux. lemma 122 with a random initial word: the phase vanishes and the coordinates form the canonical evolution**
(specification pp. 389–391, globally defined coordinates). Put `k > 4`, `A = k/2 − 2`; seed weights
`r_L, r_R ∈ (−2, 2A − 2)`. Let the driver and the force coordinates of a finite word (seeds `0⁻, 0⁺` at index `0`
started at `0`, other marks started at random positions strictly away from `0`) be continuous adapted processes with
the deterministic properties of geometric force images, in a right-continuous filtration. Assume the exact boundary
description at every `t > 0` with a common phase `d_t ∈ 2πχℤ` (no measurability of `d` assumed), coupling means that
are local martingales until swallowing and continuous in time before swallowing (for every choice of the extensions).
Then there is a time-zero event `A` of probability one on which `d_t = 0` for every `t > 0`, and conditionally on `A`
the coordinates form an integrated `SLE_k(ρ)` evolution of their random initial word, with initial σ-algebra the
time-zero σ-algebra and lifetime the continuation threshold ("Conditional on initial information fixing the word and
its marked positions, the coordinates satisfy this SDE with Brownian noise independent of that initial information").
-/
theorem aux122_isRandomWordEvolution [IsProbabilityMeasure P] [𝓕.IsRightContinuous] {k : ℝ} (hk : 4 < k)
    {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ}
    (hrL : -2 < ρL 0) (hrL' : ρL 0 < 2 * (k / 2 - 2) - 2) (hrR : -2 < ρR 0) (hrR' : ρR 0 < 2 * (k / 2 - 2) - 2)
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ} {VR : Fin (nR + 1) → ℝ≥0 → Ω → ℝ}
    (hseedL : ∀ ω, VL 0 0 ω = 0) (hseedR : ∀ ω, VR 0 0 ω = 0)
    (hxLd : ∀ ω (i : Fin nL), VL i.succ 0 ω < 0) (hxRd : ∀ ω (j : Fin nR), 0 < VR j.succ 0 ω)
    (hW0 : ∀ ω, W 0 ω = 0) (hWc : ∀ ω, Continuous fun t => W t ω) (hWa : StronglyAdapted 𝓕 W)
    (hVLa : ∀ i, StronglyAdapted 𝓕 (VL i)) (hVRa : ∀ i, StronglyAdapted 𝓕 (VR i))
    (hordL : ∀ ω t i, VL i t ω ≤ W t ω) (hordR : ∀ ω t i, W t ω ≤ VR i t ω)
    (hpathL : ∀ ω i, IsForcePath (fun t => W t ω) (fun t => VL i t ω))
    (hpathR : ∀ ω i, IsForcePath (fun t => W t ω) (fun t => VR i t ω))
    (hantiL : ∀ ω i, Antitone fun t => VL i t ω) (hmonoR : ∀ ω j, Monotone fun t => VR j t ω)
    (hidxL : ∀ ω t, Antitone fun i => VL i t ω) (hidxR : ∀ ω t, Monotone fun j => VR j t ω)
    (hmergeL : ∀ ω i j s t, s ≤ t → VL i s ω = VL j s ω → VL i t ω = VL j t ω)
    (hmergeR : ∀ ω i j s t, s ≤ t → VR i s ω = VR j s ω → VR i t ω = VR j t ω)
    (hsep : ∀ ω t, 0 < t → ∀ i j, VL i t ω = W t ω → VR j t ω ≠ W t ω)
    {d : ℝ≥0 → Ω → ℝ} (hd : ∀ (t : ℝ≥0) ω, 0 < t → ∃ n : ℤ, d t ω = n * phaseStep k)
    (hmart : ∀ U : Ω → ℝ≥0 → ℂ → ℝ, (∀ ω t, IsBoundedHarmonicExtension
        (phaseData k ρL ρR (fun i => VL i t ω - W t ω) (fun j => VR j t ω - W t ω) (d t ω))
        (forceJumpSet (fun i => VL i t ω - W t ω) (fun j => VR j t ω - W t ω)) (U ω t)) →
      ∀ z ∈ H, IsLocalMartingaleBefore 𝓕 P (fun ω => (QuantumZipper.swallowTime (wpath W ω) z : WithTop ℝ≥0))
        (fun t ω => couplingMean k (wpath W ω) t (U ω t) z))
    (hcont : ∀ U : Ω → ℝ≥0 → ℂ → ℝ, (∀ ω t, IsBoundedHarmonicExtension
        (phaseData k ρL ρR (fun i => VL i t ω - W t ω) (fun j => VR j t ω - W t ω) (d t ω))
        (forceJumpSet (fun i => VL i t ω - W t ω) (fun j => VR j t ω - W t ω)) (U ω t)) →
      ∀ ω (z : ℂ) (T' : ℝ), 0 ≤ T' → z ∈ H \ QuantumZipper.fwdHull (wpath W ω) T' →
        ContinuousOn (fun t : ℝ => couplingMean k (wpath W ω) t (U ω t.toNNReal) z) (Icc 0 T')) :
    ∃ A : Set Ω, MeasurableSet[𝓕 0] A ∧ P A = 1 ∧ (∀ ω ∈ A, ∀ t : ℝ≥0, 0 < t → d t ω = 0) ∧
      ∃ B : ℝ≥0 → A → ℝ, Aux122Disint.IsRandomWordEvolution k (condSub P A) (subFilt 𝓕 A 0) univ
        (fun (ω : A) i => VL i 0 ω) (fun (ω : A) j => VR j 0 ω) ρL ρR (subFilt 𝓕 A) (fun t (ω : A) => W t ω)
        (fun i t (ω : A) => VL i t ω) (fun j t (ω : A) => VR j t ω) B
        (fun ω : A => thresholdTime ρL ρR (fun t => W t ω) (fun i t => VL i t ω) (fun j t => VR j t ω)) := by
  have hk0 : 0 < k := by linarith
  obtain ⟨A, hA0, hAd, hAae, hloc⟩ := PhaseSelAdapt.aux122_adapt (P := P) (𝓕 := 𝓕) (T := fun _ => ⊤) hk hrL hrL'
    hrR hrR' hseedL hseedR hxLd hxRd hW0 hWc hWa hVLa hVRa hordL hordR hpathL hpathR hantiL hmonoR hidxL hidxR
    hmergeL hmergeR hsep isStoppingTime_top (fun t ω ht _ => hd t ω ht)
    (fun U hU z hz => PhaseSelAdapt.isLocalMartingaleBefore_congr_life (fun ω => (min_top_right _).symm)
      (hmart U hU z hz))
    (fun U hU ω z T' h0 _ hz => hcont U hU ω z T' h0 hz)
  have hAm : MeasurableSet A := 𝓕.le 0 _ hA0
  have hae : ∀ᵐ ω ∂P, ω ∈ A := hAae.mono fun ω h => h (WithTop.coe_lt_top 0)
  have hP1 : P A = 1 := by
    rw [← prob_compl_eq_zero_iff hAm]
    exact ae_iff.1 hae
  have h0 : P A ≠ 0 := by rw [hP1]; exact one_ne_zero
  have : IsProbabilityMeasure (condSub P A) := isProbabilityMeasure_condSub hAm h0
  have hmA : ∀ z ∈ H, IsLocalMartingaleBefore (subFilt 𝓕 A) (condSub P A)
      (fun ω : A => (QuantumZipper.swallowTime (wpath (fun t (ω : A) => W t ω) ω) z : WithTop ℝ≥0))
      (coupProc k ρL ρR (fun t (ω : A) => W t ω) (fun i t (ω : A) => VL i t ω) (fun j t (ω : A) => VR j t ω) z) :=
    fun z hz => PhaseSelAdapt.isLocalMartingaleBefore_congr_life (fun ω => min_top_right _) (hloc h0 z hz)
  refine ⟨A, hA0, hP1, fun ω hω t ht => (hAd ω hω).2 t ht le_top, _,
    isRandomWordEvolution_of_coupProc (P := condSub P A) (𝓕 := subFilt 𝓕 A) (ρL := ρL) (ρR := ρR)
      (W := fun t (ω : A) => W t ω) (VL := fun i t (ω : A) => VL i t ω) (VR := fun j t (ω : A) => VR j t ω)
      hk0 (fun ω => hW0 ω) (fun ω => hWc ω) (stronglyAdapted_sub hWa)
      (fun i => stronglyAdapted_sub (hVLa i)) (fun i => stronglyAdapted_sub (hVRa i)) (fun ω => hordL ω)
      (fun ω => hordR ω) (fun ω => hpathL ω) (fun ω => hpathR ω) (fun ω => hantiL ω) (fun ω => hmonoR ω)
      (fun ω => hidxL ω) (fun ω => hidxR ω) (fun ω => hmergeL ω) (fun ω => hmergeR ω) (fun ω => hsep ω) hmA⟩

end PocketWord

end Sec7

end InteractingSLE
