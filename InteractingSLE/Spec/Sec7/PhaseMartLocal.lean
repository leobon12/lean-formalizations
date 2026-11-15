/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PhaseMartMean

/-!
# Aux. lemma 122 with a nonzero phase, part 2: the coupling means of the phase-shifted word are local martingales

Packet PROVE-PHASEMART (specification §7.4, Aux. lemma 122, pp. 389–391; Astra's follow-up 5 §3.2, (3.2):
`M_t − M⁰_t = δ_t ω_t`, "Right continuity of the retained filtration makes this constant measurable at time zero").

The phase version of PROVE-CPL-MART2's `MartMeans2.exists_isLocalMartingaleBefore_meanProcOn`: if a random
distribution `h` with integrable pairings satisfies the conditional-law clause for the phase-shifted word
(`IsPhaseCouplingCharFun`) with a phase `c` that is **measurable at time zero** (constant in time), then for every
choice of the bounded harmonic extensions of the phase-`c` word, the coupling mean of every `z ∈ ℍ`, set to `0` off a
full-measure event of `𝓖₀`, is a local martingale before `ζ ∧ s(z)`.

Proof (as for the force word, at the localizing stops `σ_n` and the bumps `φ_n`): on the safe ball the coupling mean
is the explicit mean of the shifted word plus `c` (`couplingMean_eq_phase_of_safe`), whose bump pairing is
`(𝔥^{(c)}(z) + c) ∫ φ_n` (`integral_couplingMean_mul_bumpFun_phase`), so the clause at `σ_n ∧ t` identifies the stopped
mean with `E[(h, φ_n) | 𝓖_{σ_n∧t}]/∫ φ_n`. Adaptedness: the explicit mean is affine in the phase
(`meanCan_shift_affine`), `𝔥^{(c)} = 𝔥 + c (𝔥^{(1)} − 𝔥)`, and `𝔥`, `𝔥^{(1)}` are means of FIXED words, so their
stopped bump pairings are measurable for the stopped σ-algebra (`measurable_stoppedPair`); `c` is `𝓖₀`-measurable.

## Main result

* **`exists_isLocalMartingaleBefore_meanProcOn_phase`**.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology QuantumZipper Complex Metric
open scoped NNReal ENNReal Classical

namespace InteractingSLE.Sec7.PhaseMart

open Coupling Coupling.MartMeans Coupling.MartMeans2 Ito PhaseSel

variable {nL nR : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω}

section Main

variable {P : Measure Ω} {𝓖 : Filtration ℝ≥0 mΩ} {κ : ℝ} {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ} {VR : Fin (nR + 1) → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
  {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}

/-- The time-zero σ-algebra is below the σ-algebra of every stopping time. -/
theorem le_measurableSpace_of_isStoppingTime {ρ : Ω → ℝ≥0} (hρ : IsStoppingTime 𝓖 fun ω => (ρ ω : WithTop ℝ≥0)) :
    𝓖 0 ≤ hρ.measurableSpace := by
  have h := (isStoppingTime_const 𝓖 (0 : ℝ≥0)).measurableSpace_mono hρ
    (fun ω => WithTop.coe_le_coe.2 (zero_le : (0 : ℝ≥0) ≤ ρ ω))
  rwa [IsStoppingTime.measurableSpace_const] at h

/-- **The coupling means of the phase-shifted word are local martingales before `ζ ∧ s(z)`, exactly, after a
modification on a null event of `𝓖₀`** (Aux. lemma 122's martingale hypothesis with a nonzero phase). Let `𝓖` be a
right-continuous filtration containing the measurable `P`-null sets, in which `W`, `V^L`, `V^R` are adapted before
the lifetime `ζ`, let `ζ` have an announcing sequence in `𝓖`, and suppose that almost surely `W₀ = 0`, the
coordinates are continuous on `[0, ζ)` and `V^L ≤ W ≤ V^R` there, with `ζ > 0`. Let `c` be a `𝓖₀`-measurable
phase. If `h` has integrable pairings and satisfies the conditional-law clause of the phase-`c` word
(`IsPhaseCouplingCharFun`), then for every choice `u` of the bounded harmonic extensions of the phase-`c` word before
`ζ` and every `z ∈ ℍ` there is a
full-measure event `G ∈ 𝓖₀` such that the coupling mean of `z`, set to `0` off `G`, is a local martingale before
`ζ ∧ s(z)`. -/
theorem exists_isLocalMartingaleBefore_meanProcOn_phase [IsProbabilityMeasure P] [𝓖.IsRightContinuous]
    (hκ : 0 < κ) (hnull : ∀ s, MeasurableSet s → P s = 0 → MeasurableSet[𝓖 0] s) (hWa : AdaptedBefore 𝓖 ζ W)
    (hVLa : ∀ i, AdaptedBefore 𝓖 ζ (VL i)) (hVRa : ∀ i, AdaptedBefore 𝓖 ζ (VR i))
    (hpath : ∀ᵐ ω ∂P, W 0 ω = 0 ∧ ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω} ∧
      ((∀ i, ContinuousOn (fun t => VL i t ω) {t | (t : ℝ≥0∞) < ζ ω}) ∧
        ∀ i, ContinuousOn (fun t => VR i t ω) {t | (t : ℝ≥0∞) < ζ ω}) ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → (∀ i, VL i t ω ≤ W t ω) ∧ ∀ i, W t ω ≤ VR i t ω)
    {T : ℕ → Ω → ℝ≥0} (hT : IsAnnouncingSeq 𝓖 P ζ T)
    (hint : ∀ φ : LQGMetric.TestOn upperHalfPlaneOpens, Integrable (fun ω => h ω φ) P)
    {c : Ω → ℝ} (hcm : Measurable[𝓖 0] c)
    (hcf : IsPhaseCouplingCharFun κ ρL ρR P 𝓖 W VL VR (fun _ ω => c ω) ζ h) (hζ0 : ∀ ω, 0 < ζ ω)
    (u : Ω → ℝ≥0 → ℂ → ℝ)
    (hu : ∀ ω (t : ℝ≥0), (t : ℝ≥0∞) < ζ ω → IsBoundedHarmonicExtension
      (phaseData κ ρL ρR (fun i => VL i t ω - W t ω) (fun i => VR i t ω - W t ω) (c ω))
      (forceJumpSet (fun i => VL i t ω - W t ω) (fun i => VR i t ω - W t ω)) (u ω t))
    {z : ℂ} (hz : z ∈ H) :
    ∃ G : Set Ω, MeasurableSet[𝓖 0] G ∧ (∀ᵐ ω ∂P, ω ∈ G) ∧
      MartChar.IsLocalMartingaleBefore 𝓖 P
        (fun ω => min (ζ ω) (QuantumZipper.swallowTime (fun s : ℝ => W s.toNNReal ω) z))
        (meanProcOn κ W u z G) := by
  have hz' : 0 < z.im := hz
  -- the good event
  set good : Ω → Prop := fun ω => (W 0 ω = 0 ∧ ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω} ∧
      ((∀ i, ContinuousOn (fun t => VL i t ω) {t | (t : ℝ≥0∞) < ζ ω}) ∧
        ∀ i, ContinuousOn (fun t => VR i t ω) {t | (t : ℝ≥0∞) < ζ ω}) ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → (∀ i, VL i t ω ≤ W t ω) ∧ ∀ i, W t ω ≤ VR i t ω) ∧
    (∀ n, (T n ω : ℝ≥0∞) < ζ ω) ∧ ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → ∃ n, t ≤ T n ω with hgood
  have hae : ∀ᵐ ω ∂P, good ω := by
    filter_upwards [hpath, ae_all_iff.2 hT.2.2.1, hT.2.2.2] with ω h1 h2 h3 using ⟨h1, h2, h3⟩
  obtain ⟨G, hGm, hGc, hGgood⟩ : ∃ G : Set Ω, MeasurableSet G ∧ P Gᶜ = 0 ∧ ∀ ω ∈ G, good ω := by
    refine ⟨(toMeasurable P {ω | ¬ good ω})ᶜ, (measurableSet_toMeasurable _ _).compl, ?_,
      fun ω hω => ?_⟩
    · rw [compl_compl, measure_toMeasurable]; exact ae_iff.1 hae
    · by_contra hc; exact hω (subset_toMeasurable _ _ hc)
  have hG0 : MeasurableSet[𝓖 0] G := by
    have := (hnull _ hGm.compl hGc).compl
    rwa [compl_compl] at this
  have hG : ∀ t, MeasurableSet[𝓖 t] G := fun t => 𝓖.mono bot_le _ hG0
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := by rw [ae_iff]; exact hGc
  have hwc : ∀ ω ∈ G, ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω} := fun ω hω =>
    (hGgood ω hω).1.2.1
  have hσ : ∀ n, IsStoppingTime 𝓖 (locStopL z n T ζ G W) := fun n =>
    isStoppingTime_locStopL hWa hwc hG (hT.1 n) hz'
  have hsafe : ∀ n, ∀ ω ∈ G, IsSafeAt (closedBall z (locRad z n)) (locLevel z n) n (T n ω) (ζ ω) (W · ω)
      (locTimeL z n (T n ω) (ζ ω) (W · ω)) := fun n ω hω =>
    isSafeAt_locTimeL (hGgood ω hω).1.2.1 (hGgood ω hω).1.1 hz' n ((hGgood ω hω).2.1 n)
  refine ⟨G, hG0, hGae, fun n => locStopL z n T ζ G W, hσ, fun n ω => ?_, ?_, fun n => ?_⟩
  · -- the localizing times stay below `ζ ∧ s(z)`, everywhere
    show locStopL z n T ζ G W ω ≤ min (ζ ω) (QuantumZipper.swallowTime (fun s : ℝ => W s.toNNReal ω) z)
    by_cases hω : ω ∈ G
    · rw [locStopL_of_mem hω]
      exact le_min (hsafe n ω hω).1.le
        (locTimeL_le_swallowTime (hGgood ω hω).1.2.1 (hGgood ω hω).1.1 hz' n ((hGgood ω hω).2.1 n))
    · simp only [locStopL, hω, ↓reduceIte, WithTop.coe_zero]
      exact bot_le
  · -- exhaustion
    filter_upwards [hGae] with ω hω r hr
    obtain ⟨⟨-, hwc', -⟩, -, hTex⟩ := hGgood ω hω
    have hrζ : (r : ℝ≥0∞) < ζ ω := lt_of_lt_of_le hr (min_le_left _ _)
    have hrs : (r : ℝ≥0∞) < QuantumZipper.swallowTime (fun s : ℝ => W s.toNNReal ω) z :=
      lt_of_lt_of_le hr (min_le_right _ _)
    refine (eventually_lt_locTimeL hwc' hz' (hT.2.1 ω) hTex hrs hrζ).mono fun m hm => ?_
    show (r : WithTop ℝ≥0) < locStopL z m T ζ G W ω
    rw [locStopL_of_mem hω]
    exact WithTop.coe_lt_coe.2 hm
  -- the martingale: conditional means of the normalized bump pairing at `σ_n ∧ t`
  set φ := bumpTestAt z hz' n with hφ
  have hstop : ∀ t ω, ω ∈ G → stoppedProcess (meanProcOn κ W u z G) (locStopL z n T ζ G W) t ω =
      meanProc κ W u z (min t (locTimeL z n (T n ω) (ζ ω) (W · ω))) ω := fun t ω hω => by
    rw [stoppedProcess_apply_of_eq (locStopL_of_mem hω) t]
    simp only [meanProcOn, hω, ↓reduceIte]
  -- the value of the stopped mean: the explicit mean of the shifted word plus the phase
  have hval : ∀ (s : ℝ≥0) (ω : Ω), ω ∈ G → s ≤ locTimeL z n (T n ω) (ζ ω) (W · ω) →
      meanProc κ W u z s ω = meanCan κ (shiftL κ ρL (c ω)) (shiftR κ ρR (c ω)) (W · ω)
        (fun i t => VL i t ω) (fun i t => VR i t ω) s z + c ω := by
    intro s ω hωG hsr
    obtain ⟨⟨-, hwc', -, hord⟩, -, -⟩ := hGgood ω hωG
    have hζs : (s : ℝ≥0∞) < ζ ω := lt_of_le_of_lt (by exact_mod_cast hsr) (hsafe n ω hωG).1
    exact couplingMean_eq_phase_of_safe (vL := fun i t => VL i t ω) (vR := fun i t => VR i t ω) hκ hwc' hz' n
      (hsafe n ω hωG) hsr (hord _ hζs).1 (hord _ hζs).2 (hu ω s hζs) (mem_closedBall_self (locRad_pos hz' n).le)
  refine martingale_of_ae_eq_condExp_min_const (hσ n) ((hint φ).div_const (bumpNorm z n)) (fun t => ?_)
    (fun t => ?_)
  · -- adaptedness: the explicit mean is affine in the phase, with means of fixed words
    set ρ : Ω → ℝ≥0 := fun ω => min (if ω ∈ G then locTimeL z n (T n ω) (ζ ω) (W · ω) else 0) t with hρdef
    have hρ : IsStoppingTime 𝓖 fun ω => (ρ ω : WithTop ℝ≥0) := by
      have h1 := (hσ n).min_const t
      have e : (fun ω => min (locStopL z n T ζ G W ω) (t : WithTop ℝ≥0)) =
          fun ω => ((ρ ω : ℝ≥0) : WithTop ℝ≥0) := by
        funext ω
        rw [hρdef]
        dsimp only
        rw [WithTop.coe_min]
        rfl
      rw [e] at h1
      exact h1
    have hρω : ∀ ω ∈ G, ρ ω = min t (locTimeL z n (T n ω) (ζ ω) (W · ω)) := fun ω hω => by
      rw [hρdef]; dsimp only; simp only [hω, ↓reduceIte]; rw [min_comm]
    have hsafeρ : ∀ ω ∈ G, IsSafeAt (tsupport (GFF.bumpFun z (bumpRadius z n))) (locLevel z n) n (T n ω) (ζ ω)
        (W · ω) (ρ ω) := fun ω hω => by
      rw [hρω ω hω]
      exact ((hsafe n ω hω).anti (hwc ω hω) (closedBall_locRad_subset hz' n) (min_le_right _ _)).subset
        (tsupport_bumpFun_subset_locBall hz' n)
    have hmA := measurable_stoppedPair (κ := κ) (ρL := ρL) (ρR := ρR) (W := W) (VL := VL) (VR := VR)
      (ζ := ζ) (G := G) (φ := GFF.bumpFun z (bumpRadius z n)) (δ := locLevel z n) hWa hVLa hVRa hwc
      (fun ω hω => (hGgood ω hω).1.2.2.1) hG0 (GFF.contDiff_bumpFun z _).continuous
      (GFF.hasCompactSupport_bumpFun (bumpRadius_pos hz' n))
      ((tsupport_bumpFun_subset_locBall hz' n).trans (closedBall_locRad_subset hz' n))
      (locLevel_pos hz' n) hρ (N := n) (σ₀ := T n) hsafeρ
    have hmB := measurable_stoppedPair (κ := κ) (ρL := shiftL κ ρL 1) (ρR := shiftR κ ρR 1) (W := W) (VL := VL)
      (VR := VR) (ζ := ζ) (G := G) (φ := GFF.bumpFun z (bumpRadius z n)) (δ := locLevel z n) hWa hVLa hVRa hwc
      (fun ω hω => (hGgood ω hω).1.2.2.1) hG0 (GFF.contDiff_bumpFun z _).continuous
      (GFF.hasCompactSupport_bumpFun (bumpRadius_pos hz' n))
      ((tsupport_bumpFun_subset_locBall hz' n).trans (closedBall_locRad_subset hz' n))
      (locLevel_pos hz' n) hρ (N := n) (σ₀ := T n) hsafeρ
    set pA := fun ω => if ω ∈ G then ((∫ y, meanCan κ ρL ρR (W · ω) (fun i t => VL i t ω)
        (fun i t => VR i t ω) (ρ ω) y * GFF.bumpFun z (bumpRadius z n) y),
        loewnerGreenEnergy (rpath (W · ω)) (ρ ω) (GFF.bumpFun z (bumpRadius z n))) else ((0 : ℝ), (0 : ℝ))
      with hpA
    set pB := fun ω => if ω ∈ G then ((∫ y, meanCan κ (shiftL κ ρL 1) (shiftR κ ρR 1) (W · ω)
        (fun i t => VL i t ω) (fun i t => VR i t ω) (ρ ω) y * GFF.bumpFun z (bumpRadius z n) y),
        loewnerGreenEnergy (rpath (W · ω)) (ρ ω) (GFF.bumpFun z (bumpRadius z n))) else ((0 : ℝ), (0 : ℝ))
      with hpB
    have h0le := le_measurableSpace_of_isStoppingTime hρ
    have hGρ : MeasurableSet[hρ.measurableSpace] G := h0le _ hG0
    have hcρ : Measurable[hρ.measurableSpace] c := hcm.mono h0le le_rfl
    have hF : Measurable[hρ.measurableSpace] fun ω => if ω ∈ G then
        ((pA ω).1 / bumpNorm z n + c ω * ((pB ω).1 / bumpNorm z n - (pA ω).1 / bumpNorm z n) + c ω) else 0 := by
      refine Measurable.ite hGρ ?_ measurable_const
      exact (((measurable_fst.comp hmA).div_const _).add (hcρ.mul (((measurable_fst.comp hmB).div_const _).sub
        ((measurable_fst.comp hmA).div_const _)))).add hcρ
    have h3 := hF.mono (hρ.measurableSpace_le_of_le_const fun ω => WithTop.coe_le_coe.2 (min_le_right _ _)) le_rfl
    have heq : stoppedProcess (meanProcOn κ W u z G) (locStopL z n T ζ G W) t = fun ω => if ω ∈ G then
        ((pA ω).1 / bumpNorm z n + c ω * ((pB ω).1 / bumpNorm z n - (pA ω).1 / bumpNorm z n) + c ω) else 0 := by
      funext ω
      by_cases hω : ω ∈ G
      · obtain ⟨⟨-, hwc', -⟩, -, -⟩ := hGgood ω hω
        have hρr : ρ ω ≤ locTimeL z n (T n ω) (ζ ω) (W · ω) := by rw [hρω ω hω]; exact min_le_right _ _
        rw [hstop t ω hω, ← hρω ω hω, hval (ρ ω) ω hω hρr, meanCan_shift_affine]
        simp only [hω, ↓reduceIte, hpA, hpB]
        rw [← meanCan_eq_integral_div_of_safe hwc' hz' n (hsafe n ω hω) hρr,
          ← meanCan_eq_integral_div_of_safe hwc' hz' n (hsafe n ω hω) hρr]
      · have h0 : locStopL z n T ζ G W ω = ((0 : ℝ≥0) : WithTop ℝ≥0) := by
          simp only [locStopL, hω, ↓reduceIte]
        rw [stoppedProcess_apply_of_eq h0 t]
        simp only [meanProcOn, hω, ↓reduceIte]
    rw [heq]
    exact h3.stronglyMeasurable
  · -- conditional means at `σ_n ∧ t`
    set τ : Ω → WithTop ℝ≥0 := fun ω => min (locStopL z n T ζ G W ω) (t : WithTop ℝ≥0) with hτ
    have hτu : ∀ ω ∈ G, (τ ω).untopD 0 = min (locTimeL z n (T n ω) (ζ ω) (W · ω)) t := fun ω hω => by
      rw [hτ]
      dsimp only
      rw [locStopL_of_mem hω, ← WithTop.coe_min, WithTop.untopD_coe]
    have hlt : ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < ζ ω := by
      filter_upwards [hGae] with ω hω
      have h1 : (τ ω : ℝ≥0∞) ≤ (locTimeL z n (T n ω) (ζ ω) (W · ω) : ℝ≥0∞) := by
        have : τ ω ≤ locStopL z n T ζ G W ω := min_le_left _ _
        rw [locStopL_of_mem hω] at this
        exact this
      exact lt_of_le_of_lt h1 (hsafe n ω hω).1
    have key : ∀ c' : ℝ, P[fun ω => cexp (I * ((c' * h ω φ : ℝ) : ℂ)) |
        ((hσ n).min_const t).measurableSpace] =ᵐ[P] fun ω => cexp (I * ((c' *
          (∫ y, couplingMean κ (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)
            (u ω ((τ ω).untopD 0)) y * GFF.bumpFun z (bumpRadius z n) y) : ℝ) : ℂ) -
          (((1 / 2) * (c' ^ 2 * loewnerGreenEnergy (fun s : ℝ => W s.toNNReal ω)
            ((τ ω).untopD 0 : ℝ≥0) (GFF.bumpFun z (bumpRadius z n))) : ℝ) : ℂ)) := by
      intro c'
      have hτζ : ∀ ω, (((τ ω).untopD 0 : ℝ≥0) : ℝ≥0∞) < ζ ω := fun ω => by
        by_cases hω : ω ∈ G
        · rw [hτu ω hω]
          exact lt_of_le_of_lt (by exact_mod_cast min_le_left _ _) (hsafe n ω hω).1
        · have h0 : τ ω = ((0 : ℝ≥0) : WithTop ℝ≥0) := by
            simp only [hτ, locStopL, hω, ↓reduceIte, WithTop.coe_zero]
            exact min_eq_left bot_le
          rw [h0, WithTop.untopD_coe, ENNReal.coe_zero]
          exact hζ0 ω
      have hcl := hcf τ ((hσ n).min_const t) hlt (fun ω => u ω ((τ ω).untopD 0)) (fun ω => hu ω _ (hτζ ω))
        (c' • φ)
      have e1 : (fun ω' => cexp (I * ((h ω' (c' • φ) : ℝ) : ℂ))) =
          fun ω' => cexp (I * ((c' * h ω' φ : ℝ) : ℂ)) := by
        funext ω'; simp
      rw [e1] at hcl
      filter_upwards [hcl, hGae] with ω hω hωG
      have hcoe : (⇑(c' • φ) : ℂ → ℝ) = c' • GFF.bumpFun z (bumpRadius z n) := by
        funext y; simp [hφ, coe_bumpTestAt]
      have hdisj : Disjoint (tsupport ⇑(c' • φ))
          (fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)) := by
        rw [hτu ω hωG]
        refine Disjoint.mono_left ?_ (disjoint_locBall_fwdHull_of_safe (hGgood ω hωG).1.2.1 hz' n
          (hsafe n ω hωG) (min_le_left _ _))
        rw [hcoe]
        exact (tsupport_smul_subset_right (fun _ : ℂ => c') (GFF.bumpFun z (bumpRadius z n))).trans
          (tsupport_bumpFun_subset_locBall hz' n)
      rw [hω hdisj, hcoe, integral_mul_smul, loewnerGreenEnergy_smul]
    have hA := condExp_ae_eq_of_condCharFun (hint φ) key
    have hs := condExp_smul (μ := P) (bumpNorm z n)⁻¹ (fun ω => h ω φ)
      ((hσ n).min_const t).measurableSpace
    have e2 : (fun ω => h ω φ / bumpNorm z n) = (bumpNorm z n)⁻¹ • fun ω => h ω φ := by
      funext ω; simp [div_eq_inv_mul]
    rw [e2]
    filter_upwards [hA, hs, hGae] with ω h1 h2 hωG
    obtain ⟨⟨-, hwc', -, hord⟩, -, -⟩ := hGgood ω hωG
    set r := locTimeL z n (T n ω) (ζ ω) (W · ω) with hr
    have hsr : min r t ≤ r := min_le_left _ _
    have hζs : ((min r t : ℝ≥0) : ℝ≥0∞) < ζ ω :=
      lt_of_le_of_lt (by exact_mod_cast hsr) (hsafe n ω hωG).1
    rw [h2, Pi.smul_apply, h1, smul_eq_mul, hstop t ω hωG, min_comm]
    simp only [hτu ω hωG]
    rw [hval (min r t) ω hωG hsr]
    have h4 := integral_couplingMean_mul_bumpFun_phase (vL := fun i t => VL i t ω) (vR := fun i t => VR i t ω)
      hκ hwc' hz' n (hsafe n ω hωG) hsr (hord _ hζs).1 (hord _ hζs).2 (hu ω (min r t) hζs)
    rw [show (fun s : ℝ => W s.toNNReal ω) = rpath (W · ω) from rfl, h4]
    field_simp [(bumpNorm_pos hz' n).ne']

end Main

end InteractingSLE.Sec7.PhaseMart
