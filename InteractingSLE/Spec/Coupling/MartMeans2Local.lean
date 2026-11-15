/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.MartMeans2Announce

/-!
# The exact local-martingale form of the coupling means below a lifetime

Packet PROVE-CPL-MART2, part (1), upgrade. PROVE-CPL-MART's `exists_martingale_stoppedProcess_meanProc` gives, for a
coupling whose driving paths are regular only almost surely, the form "each stopped coupling mean agrees almost
surely, at every time, with a martingale". The coupling mean itself need not be adapted off a null set (the
harmonic extensions `u` are arbitrary there). Here the coupling mean is set to `0` off a `𝓖₀`-measurable full-measure
event `G` of good paths (`meanProcOn`), and the modified process is, exactly, a local martingale before
`ζ ∧ s(z)` in the sense of `MartChar.IsLocalMartingaleBefore` (the hypothesis form of Theorem 2.4's converse): the
stopped processes are adapted (`measurable_stoppedPair` at the safe stops) and martingales.

## Main results

* `meanProcOn`: the coupling mean of `z`, set to `0` off `G`;
* **`exists_isLocalMartingaleBefore_meanProcOn`**: the generic statement (right-continuous filtration with the null
  sets, announcing sequence, coordinates adapted before `ζ` with continuous ordered paths almost surely);
* **`IsOptionalHullCoupling.exists_isLocalMartingaleBefore_meanProcOn`**: for the frozen optional hull specification
  with an admissible seed and `κ > 0`, in the driving filtration.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology QuantumZipper Complex Metric
open scoped NNReal ENNReal Classical

namespace InteractingSLE

namespace Coupling

namespace MartMeans2

open Ito MartMeans

variable {nL nR : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The coupling mean `t ↦ 𝔥_t(z)` set to `0` off the event `G`. -/
def meanProcOn (κ : ℝ) (W : ℝ≥0 → Ω → ℝ) (u : Ω → ℝ≥0 → ℂ → ℝ) (z : ℂ) (G : Set Ω) : ℝ≥0 → Ω → ℝ :=
  fun t ω => if ω ∈ G then meanProc κ W u z t ω else 0

section Main

variable {P : Measure Ω} {𝓖 : Filtration ℝ≥0 mΩ} {κ : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
  {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}

/-- **The coupling means are local martingales before `ζ ∧ s(z)`, exactly, after a modification on a null event of
`𝓖₀`.** Let `𝓖` be a right-continuous filtration containing the measurable `P`-null sets, in which `W`, `V^L`, `V^R`
are adapted before the lifetime `ζ`, let `ζ` have an announcing sequence in `𝓖`, and suppose that almost surely
`W₀ = 0`, the coordinates are continuous on `[0, ζ)` and `V^L ≤ W ≤ V^R` there. If `h` has integrable pairings and
satisfies the conditional-law clause `IsCouplingCharFun`, then for every choice `u` of the bounded harmonic
extensions and every `z ∈ ℍ` there is a full-measure event `G ∈ 𝓖₀` such that the coupling mean of `z`, set to `0`
off `G`, is a local martingale before `ζ ∧ s(z)` (`MartChar.IsLocalMartingaleBefore`). -/
theorem exists_isLocalMartingaleBefore_meanProcOn [IsProbabilityMeasure P] [𝓖.IsRightContinuous]
    (hnull : ∀ s, MeasurableSet s → P s = 0 → MeasurableSet[𝓖 0] s) (hWa : AdaptedBefore 𝓖 ζ W)
    (hVLa : ∀ i, AdaptedBefore 𝓖 ζ (VL i)) (hVRa : ∀ i, AdaptedBefore 𝓖 ζ (VR i))
    (hpath : ∀ᵐ ω ∂P, W 0 ω = 0 ∧ ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω} ∧
      ((∀ i, ContinuousOn (fun t => VL i t ω) {t | (t : ℝ≥0∞) < ζ ω}) ∧
        ∀ i, ContinuousOn (fun t => VR i t ω) {t | (t : ℝ≥0∞) < ζ ω}) ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → (∀ i, VL i t ω ≤ W t ω) ∧ ∀ i, W t ω ≤ VR i t ω)
    {T : ℕ → Ω → ℝ≥0} (hT : IsAnnouncingSeq 𝓖 P ζ T)
    (hint : ∀ φ : LQGMetric.TestOn upperHalfPlaneOpens, Integrable (fun ω => h ω φ) P)
    (hcf : IsCouplingCharFun κ ρL ρR P 𝓖 W VL VR ζ h) (u : Ω → ℝ≥0 → ℂ → ℝ)
    (hu : ∀ ω t, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => VL i t ω - W t ω) (fun i => VR i t ω - W t ω))
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
  have hval : ∀ t, ∀ ω ∈ G, meanProc κ W u z (min t (locTimeL z n (T n ω) (ζ ω) (W · ω))) ω =
      (∫ y, meanCan κ ρL ρR (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω)
        (min t (locTimeL z n (T n ω) (ζ ω) (W · ω))) y * GFF.bumpFun z (bumpRadius z n) y) / bumpNorm z n := by
    intro t ω hωG
    obtain ⟨⟨-, hwc', -, hord⟩, -, -⟩ := hGgood ω hωG
    set r := locTimeL z n (T n ω) (ζ ω) (W · ω) with hr
    have hsr : min t r ≤ r := min_le_right _ _
    have hζs : ((min t r : ℝ≥0) : ℝ≥0∞) < ζ ω :=
      lt_of_le_of_lt (by exact_mod_cast hsr) (hsafe n ω hωG).1
    have e3 : meanProc κ W u z (min t r) ω =
        couplingMean κ (rpath (W · ω)) (min t r : ℝ≥0) (u ω (min t r)) z := rfl
    rw [e3, couplingMean_eq_meanCan_of_safe (ρL := ρL) (ρR := ρR) (vL := fun i t => VL i t ω)
        (vR := fun i t => VR i t ω) hwc' hz' n (hsafe n ω hωG) hsr (hord _ hζs).1 (hord _ hζs).2
        (hu ω (min t r)) (mem_closedBall_self (locRad_pos hz' n).le),
      meanCan_eq_integral_div_of_safe hwc' hz' n (hsafe n ω hωG) hsr]
  refine martingale_of_ae_eq_condExp_min_const (hσ n) ((hint φ).div_const (bumpNorm z n)) (fun t => ?_)
    (fun t => ?_)
  · -- adaptedness, through the measurability of the tested mean at the safe stop `σ_n ∧ t`
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
    have hm := measurable_stoppedPair (κ := κ) (ρL := ρL) (ρR := ρR) (W := W) (VL := VL) (VR := VR)
      (ζ := ζ) (G := G) (φ := GFF.bumpFun z (bumpRadius z n)) (δ := locLevel z n) hWa hVLa hVRa hwc
      (fun ω hω => (hGgood ω hω).1.2.2.1) hG0 (GFF.contDiff_bumpFun z _).continuous
      (GFF.hasCompactSupport_bumpFun (bumpRadius_pos hz' n))
      ((tsupport_bumpFun_subset_locBall hz' n).trans (closedBall_locRad_subset hz' n))
      (locLevel_pos hz' n) hρ (N := n) (σ₀ := T n)
      (fun ω hω => by
        have hρω : ρ ω = min (locTimeL z n (T n ω) (ζ ω) (W · ω)) t := by
          rw [hρdef]; dsimp only; simp only [hω, ↓reduceIte]
        rw [hρω]
        exact ((hsafe n ω hω).anti (hwc ω hω) (closedBall_locRad_subset hz' n) (min_le_left _ _)).subset
          (tsupport_bumpFun_subset_locBall hz' n))
    have h3 := (measurable_fst.comp hm).mono
      (hρ.measurableSpace_le_of_le_const fun ω => WithTop.coe_le_coe.2 (min_le_right _ _)) le_rfl
    have heq : stoppedProcess (meanProcOn κ W u z G) (locStopL z n T ζ G W) t = fun ω =>
        (Prod.fst ∘ fun ω => if ω ∈ G then ((∫ y, meanCan κ ρL ρR (W · ω) (fun i t => VL i t ω)
          (fun i t => VR i t ω) (ρ ω) y * GFF.bumpFun z (bumpRadius z n) y),
          loewnerGreenEnergy (rpath (W · ω)) (ρ ω) (GFF.bumpFun z (bumpRadius z n))) else ((0 : ℝ), (0 : ℝ)))
          ω / bumpNorm z n := by
      funext ω
      by_cases hω : ω ∈ G
      · rw [hstop t ω hω, hval t ω hω]
        have hρω : ρ ω = min t (locTimeL z n (T n ω) (ζ ω) (W · ω)) := by
          rw [hρdef]; dsimp only; simp only [hω, ↓reduceIte]; rw [min_comm]
        simp only [Function.comp_apply, hω, ↓reduceIte, hρω]
      · have h0 : locStopL z n T ζ G W ω = ((0 : ℝ≥0) : WithTop ℝ≥0) := by
          simp only [locStopL, hω, ↓reduceIte]
        rw [stoppedProcess_apply_of_eq h0 t]
        simp only [meanProcOn, hω, ↓reduceIte, Function.comp_apply, zero_div]
    rw [heq]
    exact (h3.div_const _).stronglyMeasurable
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
    have key : ∀ c : ℝ, P[fun ω => cexp (I * ((c * h ω φ : ℝ) : ℂ)) |
        ((hσ n).min_const t).measurableSpace] =ᵐ[P] fun ω => cexp (I * ((c *
          (∫ y, couplingMean κ (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)
            (u ω ((τ ω).untopD 0)) y * GFF.bumpFun z (bumpRadius z n) y) : ℝ) : ℂ) -
          (((1 / 2) * (c ^ 2 * loewnerGreenEnergy (fun s : ℝ => W s.toNNReal ω)
            ((τ ω).untopD 0 : ℝ≥0) (GFF.bumpFun z (bumpRadius z n))) : ℝ) : ℂ)) := by
      intro c
      have hcl := hcf τ ((hσ n).min_const t) hlt (fun ω => u ω ((τ ω).untopD 0)) (fun ω => hu ω _)
        (c • φ)
      have e1 : (fun ω' => cexp (I * ((h ω' (c • φ) : ℝ) : ℂ))) =
          fun ω' => cexp (I * ((c * h ω' φ : ℝ) : ℂ)) := by
        funext ω'; simp
      rw [e1] at hcl
      filter_upwards [hcl, hGae] with ω hω hωG
      have hcoe : (⇑(c • φ) : ℂ → ℝ) = c • GFF.bumpFun z (bumpRadius z n) := by
        funext y; simp [hφ, coe_bumpTestAt]
      have hdisj : Disjoint (tsupport ⇑(c • φ))
          (fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)) := by
        rw [hτu ω hωG]
        refine Disjoint.mono_left ?_ (disjoint_locBall_fwdHull_of_safe (hGgood ω hωG).1.2.1 hz' n
          (hsafe n ω hωG) (min_le_left _ _))
        rw [hcoe]
        exact (tsupport_smul_subset_right (fun _ : ℂ => c) (GFF.bumpFun z (bumpRadius z n))).trans
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
    have e3 : meanProc κ W u z (min r t) ω =
        couplingMean κ (rpath (W · ω)) (min r t : ℝ≥0) (u ω (min r t)) z := rfl
    rw [e3, couplingMean_eq_meanCan_of_safe (ρL := ρL) (ρR := ρR) (vL := fun i t => VL i t ω)
        (vR := fun i t => VR i t ω) hwc' hz' n (hsafe n ω hωG) hsr (hord _ hζs).1 (hord _ hζs).2
        (hu ω (min r t)) (mem_closedBall_self (locRad_pos hz' n).le),
      meanCan_eq_integral_div_of_safe hwc' hz' n (hsafe n ω hωG) hsr]
    have h4 := integral_couplingMean_mul_bumpFun_of_safe (κ := κ) (ρL := ρL) (ρR := ρR)
      (vL := fun i t => VL i t ω) (vR := fun i t => VR i t ω) hwc' hz' n (hsafe n ω hωG) hsr
      (hord _ hζs).1 (hord _ hζs).2 (hu ω (min r t))
    rw [show (fun s : ℝ => W s.toNNReal ω) = rpath (W · ω) from rfl, h4, div_eq_inv_mul]

end Main

/-! ### The frozen optional hull specification -/

section Frozen

variable {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
  {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}

/-- **The coupling means of the frozen optional hull specification are local martingales before `ζ ∧ s(z)`**, exactly,
in the driving filtration, after setting them to `0` on a null event of its time-zero σ-algebra (admissible seed,
`κ > 0`). -/
theorem _root_.InteractingSLE.IsOptionalHullCoupling.exists_isLocalMartingaleBefore_meanProcOn
    [IsProbabilityMeasure P] (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h) (hκ : 0 < κ)
    (hseed : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR) (hX : IsMeasurableKilledDriving W VL VR ζ)
    (u : Ω → ℝ≥0 → ℂ → ℝ)
    (hu : ∀ ω t, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => VL i t ω - W t ω) (fun i => VR i t ω - W t ω))
      (forceJumpSet (fun i => VL i t ω - W t ω) (fun i => VR i t ω - W t ω)) (u ω t))
    {z : ℂ} (hz : z ∈ H) :
    ∃ G : Set Ω, MeasurableSet[drivingFiltration P hX 0] G ∧ (∀ᵐ ω ∂P, ω ∈ G) ∧
      MartChar.IsLocalMartingaleBefore (drivingFiltration P hX) P
        (fun ω => min (ζ ω) (QuantumZipper.swallowTime (fun s : ℝ => W s.toNNReal ω) z))
        (meanProcOn κ W u z G) := by
  have := isRightContinuous_drivingFiltration (P := P) hX
  obtain ⟨_, hcf⟩ := hC.exists_isCouplingCharFun
  obtain ⟨T, hT, -⟩ := hC.1.exists_isAnnouncingSeq_drivingFiltration hκ hseed hX
  have hle : killedDrivingFiltration hX ≤ drivingFiltration P hX := le_usualAugmentation _ P
  have hpath : ∀ᵐ ω ∂P, W 0 ω = 0 ∧ ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω} ∧
      ((∀ i, ContinuousOn (fun t => VL i t ω) {t | (t : ℝ≥0∞) < ζ ω}) ∧
        ∀ i, ContinuousOn (fun t => VR i t ω) {t | (t : ℝ≥0∞) < ζ ω}) ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → (∀ i, VL i t ω ≤ W t ω) ∧ ∀ i, W t ω ≤ VR i t ω := by
    filter_upwards [hC.1.2.2.2.2] with ω hω
    exact ⟨hω.1, hω.2.2.2.1, ⟨hω.isForcePath.continuousOn_vL, hω.isForcePath.continuousOn_vR⟩,
      fun t ht => ⟨hω.2.2.2.2.2.2.2.1 t ht, hω.2.2.2.2.2.2.2.2.1 t ht⟩⟩
  exact MartMeans2.exists_isLocalMartingaleBefore_meanProcOn
    (fun s hs h0 => measurableSet_usualAugmentation_of_null hs h0 0)
    (adaptedBefore_mono hle (adaptedBefore_killedDriving_W hX))
    (fun i => adaptedBefore_mono hle (adaptedBefore_killedDriving_VL hX i))
    (fun i => adaptedBefore_mono hle (adaptedBefore_killedDriving_VR hX i)) hpath hT
    hC.integrable_apply hcf u hu hz

end Frozen

end MartMeans2

end Coupling

end InteractingSLE
