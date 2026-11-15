/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PhaseMartLocal
import InteractingSLE.Spec.Sec7.PocketPhaseMeans

/-!
# Aux. lemma 122 with a nonzero phase, part 3: `HasPhaseMeansBefore` from the clause of the phase-shifted word

Packet PROVE-PHASEMART (specification §7.4, Aux. lemma 122, pp. 389–391: "Retain a stopped Gaussian field kernel
whose harmonic mean `M_t(z)` is a continuous local martingale until `z` is swallowed. Assume the following exact
boundary description […]"; Aux. lemma 125, p. 397; Astra's follow-up 5 §3.2: "Right continuity of the retained
filtration makes this constant measurable at time zero").

PROVE-STRIPSYS18's `PocketPhaseMeans.hasPhaseMeansBefore_zero_of_charFun` produces Aux. lemma 122's hypotheses
before the lifetime (`PocketMartLife.HasPhaseMeansBefore`) only for the canonical phase `d = 0`. Here they are produced
for **every phase `d` that is constant before the lifetime with a `𝓖₀`-measurable value `c`** — the form the phase has
by (3.2) (lattice-valued and continuous on the positive lifetime, hence constant; measurable at time zero by right
continuity) — from the conditional-law clause of the phase-shifted word (`IsPhaseCouplingCharFun`) with the geometric
force coordinates of random time-zero marks. Aux. lemma 122 (`PhaseSide.ae_phase_eq_zero_of_hasPhaseMeans`) then
shows `c = 0` almost surely when the seed weights lie in `(−2, k − 6)`.

## Main results

* `continuousOn_couplingMean_of_ext_phase`: continuity in time of the coupling mean of any extension of the phase-`c`
  word along continuous ordered coordinates;
* **`hasPhaseMeansBefore_of_phaseCharFun`**: `HasPhaseMeansBefore κ ρL ρR P 𝓖 W xL xR d T` from
  `IsPhaseCouplingCharFun κ ρL ρR P 𝓖 W (geomLW W xL) (geomRW W xR) c T h`, for `d = c` before `T`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PhaseMart

open MartChar Coupling PocketTraversal PocketMartLife PhaseSel PocketPhaseMeans

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {nL nR : ℕ}

/-! ### Continuity in time of the coupling mean of the phase-shifted word -/

section Cont

variable {κ : ℝ} {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ}

/-- **Continuity in time of the coupling mean of any extension of the phase-`c` word** along continuous ordered
coordinates, at a point not swallowed by `T'`: it is `c` plus the coupling mean of an extension of the canonical word
of the shifted seed weights ((PS9.2)), which is continuous (`continuousOn_couplingMean_of_ext`). -/
theorem continuousOn_couplingMean_of_ext_phase (hκ : 0 < κ) {w : ℝ → ℝ} {vL : Fin (nL + 1) → ℝ → ℝ}
    {vR : Fin (nR + 1) → ℝ → ℝ} {T' : ℝ} (hT' : 0 ≤ T') (hw : ContinuousOn w (Icc 0 T'))
    (hvL : ∀ i, ContinuousOn (vL i) (Icc 0 T')) (hvR : ∀ j, ContinuousOn (vR j) (Icc 0 T'))
    (hord : ∀ t ∈ Icc 0 T', (∀ i, vL i t ≤ w t) ∧ ∀ j, w t ≤ vR j t) {c : ℝ} {u : ℝ → ℂ → ℝ}
    (hu : ∀ t ∈ Icc 0 T', IsBoundedHarmonicExtension
      (phaseData κ ρL ρR (fun i => vL i t - w t) (fun j => vR j t - w t) c)
      (forceJumpSet (fun i => vL i t - w t) (fun j => vR j t - w t)) (u t))
    {z : ℂ} (hz : z ∈ H \ QuantumZipper.fwdHull w T') :
    ContinuousOn (fun t => couplingMean κ w t (u t) z) (Icc 0 T') := by
  have h := continuousOn_couplingMean_of_ext (ρL := shiftL κ ρL c) (ρR := shiftR κ ρR c) hT' hw hvL hvR hord
    (u := fun t ξ => u t ξ - c) (fun t ht => isBoundedHarmonicExtension_shift hκ
      (sub_nonpos.2 ((hord t ht).1 0)) (sub_nonneg.2 ((hord t ht).2 0)) (hu t ht)) hz
  refine (h.add (continuousOn_const (c := c))).congr fun t _ => ?_
  simp only [Pi.add_apply]
  rw [couplingMean_sub_const, sub_add_cancel]

/-- The explicit harmonic function of the shifted word is affine in the phase. -/
theorem meanHarmonic_shift_affine (ρL : Fin (nL + 1) → ℝ) (ρR : Fin (nR + 1) → ℝ) (vL : Fin (nL + 1) → ℝ)
    (vR : Fin (nR + 1) → ℝ) (c : ℝ) (ξ : ℂ) :
    Ito.meanHarmonic κ (shiftL κ ρL c) (shiftR κ ρR c) vL vR ξ = Ito.meanHarmonic κ ρL ρR vL vR ξ +
      c * (Ito.meanHarmonic κ (shiftL κ ρL 1) (shiftR κ ρR 1) vL vR ξ - Ito.meanHarmonic κ ρL ρR vL vR ξ) := by
  rw [meanHarmonic_shift, meanHarmonic_shift]
  ring

end Cont

/-! ### Aux. lemma 122's hypotheses with a time-zero measurable phase -/

section Main

variable {P : Measure Ω} [IsProbabilityMeasure P] {𝓖 : Filtration ℝ≥0 mΩ} [𝓖.IsRightContinuous] {κ : ℝ}
  {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ} {T : Ω → ℝ≥0∞} {W : ℝ≥0 → Ω → ℝ}
  {xL : Ω → Fin (nL + 1) → ℝ} {xR : Ω → Fin (nR + 1) → ℝ}

/-- **Aux. lemma 122's hypotheses before the lifetime with a nonzero phase, from the conditional-law clause of the
phase-shifted word** (specification pp. 389–390 and p. 397; follow-up 5 §3.2). Let `𝓖` be a right-continuous
filtration whose time-zero σ-algebra contains the measurable null sets, `W` a driver started at `0`, continuous and
adapted on `[0, T)` with `T > 0`, almost surely unbounded near a finite `T`, `xL`, `xR` `𝓖₀`-measurable marks, and
`d` a phase equal before `T` to a `𝓖₀`-measurable `c`. If a random distribution `h` with integrable pairings
satisfies the conditional-law clause with lifetime `T` for the word `(ρL; ρR)` with the exposed interval raised by `c`,
at the geometric force coordinates of the marks (`IsPhaseCouplingCharFun`), then
`HasPhaseMeansBefore κ ρL ρR P 𝓖 W xL xR d T`: for every choice of the extensions of the phase-shifted data before
`T`, the coupling means are local martingales before `min (swallowTime z) T` and continuous on compact windows before
swallowing. -/
theorem hasPhaseMeansBefore_of_phaseCharFun {h : Ω → DistOn upperHalfPlaneOpens} (hκ : 0 < κ)
    (hnull : ∀ s, MeasurableSet s → P s = 0 → MeasurableSet[𝓖 0] s) (hW0 : ∀ ω, W 0 ω = 0)
    (hT0 : ∀ ω, 0 < T ω) (hc : ∀ ω, ContinuousOn (fun t => W t ω) {t : ℝ≥0 | (t : ℝ≥0∞) < T ω})
    (hWa : AdaptedBefore 𝓖 T W)
    (hunb : ∀ᵐ ω ∂P, T ω ≠ ⊤ → ∀ C : ℝ, ∃ s : ℝ≥0, (s : ℝ≥0∞) < T ω ∧ C < |W s ω|)
    (hxLm : Measurable[𝓖 0] xL) (hxRm : Measurable[𝓖 0] xR)
    (hint : ∀ φ : TestOn upperHalfPlaneOpens, Integrable (fun ω => h ω φ) P)
    {c : Ω → ℝ} (hcm : Measurable[𝓖 0] c) {d : ℝ≥0 → Ω → ℝ}
    (hdc : ∀ ω (t : ℝ≥0), (t : ℝ≥0∞) < T ω → d t ω = c ω)
    (hcf : IsPhaseCouplingCharFun κ ρL ρR P 𝓖 W (geomLW W xL) (geomRW W xR) (fun _ ω => c ω) T h) :
    HasPhaseMeansBefore κ ρL ρR P 𝓖 W xL xR d T := by
  classical
  have hcW : ∀ ω, ContinuousOn (W · ω) {t | (t : WithTop ℝ≥0) < T ω} := hc
  have hord : ∀ ω (t : ℝ≥0), (t : ℝ≥0∞) < T ω →
      (∀ i, geomLW W xL i t ω ≤ W t ω) ∧ ∀ j, W t ω ≤ geomRW W xR j t ω :=
    fun ω t ht => ⟨fun i => geomLW_le_of_lt (hcW ω) ht xL i, fun j => le_geomRW_of_lt (hcW ω) ht xR j⟩
  intro U hU
  -- the extensions are extensions of the phase-`c` word before `T`
  have hU' : ∀ ω (t : ℝ≥0), (t : ℝ≥0∞) < T ω → IsBoundedHarmonicExtension
      (phaseData κ ρL ρR (fun i => geomLW W xL i t ω - W t ω) (fun j => geomRW W xR j t ω - W t ω) (c ω))
      (forceJumpSet (fun i => geomLW W xL i t ω - W t ω) (fun j => geomRW W xR j t ω - W t ω)) (U ω t) := by
    intro ω t ht
    have h1 := hU ω t ht
    rwa [hdc ω t ht] at h1
  -- the continuity clause
  have hcont : ∀ ω (z : ℂ) (T' : ℝ), 0 ≤ T' → ((T'.toNNReal : ℝ≥0) : ℝ≥0∞) < T ω →
      z ∈ H \ QuantumZipper.fwdHull (wpath W ω) T' →
      ContinuousOn (fun t : ℝ => couplingMean κ (wpath W ω) t (U ω t.toNNReal) z) (Icc 0 T') := by
    intro ω z T' hT' hT'T hz
    have hlt : ∀ t ∈ Icc (0 : ℝ) T', ((t.toNNReal : ℝ≥0) : ℝ≥0∞) < T ω := fun t ht =>
      lt_of_le_of_lt (ENNReal.coe_le_coe.2 (Real.toNNReal_le_toNNReal ht.2)) hT'T
    have hmaps : MapsTo Real.toNNReal (Icc (0 : ℝ) T') {s : ℝ≥0 | (s : ℝ≥0∞) < T ω} := fun t ht => hlt t ht
    exact continuousOn_couplingMean_of_ext_phase (vL := fun i t => geomLW W xL i t.toNNReal ω)
      (vR := fun j t => geomRW W xR j t.toNNReal ω) (u := fun t => U ω t.toNNReal) hκ hT'
      ((hc ω).comp continuous_real_toNNReal.continuousOn hmaps)
      (fun i => (continuousOn_geomLW_of_lt hcW xL i ω).comp continuous_real_toNNReal.continuousOn hmaps)
      (fun j => (continuousOn_geomRW_of_lt hcW xR j ω).comp continuous_real_toNNReal.continuousOn hmaps)
      (fun t ht => hord ω _ (hlt t ht)) (fun t ht => hU' ω _ (hlt t ht)) hz
  refine ⟨fun z hz => ?_, hcont⟩
  -- the martingale clause
  have hz0 : z ≠ 0 := fun h0 => lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from h0 ▸ hz)
  obtain ⟨G₁, hG₁0, hG₁ae, hG₁⟩ := exists_mem_zero_of_ae hnull hunb
  have hann := Lemma71C.isAnnouncingSeq_annSeq (P := P) hWa hG₁0 hc hG₁ae hG₁
  obtain ⟨G, hG0, hGae, hloc⟩ := exists_isLocalMartingaleBefore_meanProcOn_phase hκ hnull hWa
    (fun i => adaptedBefore_geomLW hc hWa hxLm i) (fun j => adaptedBefore_geomRW hc hWa hxRm j)
    (Eventually.of_forall fun ω => ⟨hW0 ω, hc ω,
      ⟨fun i => continuousOn_geomLW_of_lt hcW xL i ω, fun j => continuousOn_geomRW_of_lt hcW xR j ω⟩,
      fun t ht => hord ω t ht⟩)
    hann hint hcm hcf hT0 U hU' hz
  obtain ⟨G₂, hG₂0, hG₂ae, hG₂⟩ := exists_mem_zero_of_ae hnull (ae_all_iff.2 hann.2.2.1)
  obtain ⟨G₃, hG₃0, hG₃ae, hG₃⟩ := exists_mem_zero_of_ae hnull hann.2.2.2
  have hGG : ∀ᵐ ω ∂P, ω ∈ G ∩ G₂ ∩ G₃ := by
    filter_upwards [hGae, hG₂ae, hG₃ae] with ω h1 h2 h3 using ⟨⟨h1, h2⟩, h3⟩
  refine isLocalMartingaleBefore_of_eq_before (T := T) (X := MartMeans2.meanProcOn κ W U z G) hnull
    ((hG0.inter hG₂0).inter hG₃0) hGG (fun ω => min_le_right _ _) hann.1 hann.2.1
    (fun n ω hω => hG₂ ω hω.1.2 n) (fun ω hω t ht => hG₃ ω hω.2 t ht) ?_ ?_ ?_ ?_
  · -- the local martingale, with the lifetime written in the other order
    convert hloc using 2 with ω
    exact min_comm _ _
  · -- right-continuity before the lifetime
    intro ω s hs
    by_cases hω : ω ∈ G
    · have h := PhaseSelAdapt.continuousWithinAt_of_continuousOn_Icc hz
        (fun T' hT' hT'T hzK => hcont ω z T' hT' hT'T hzK) hs
      refine h.congr (fun t _ => ?_) ?_
      · simp only [MartMeans2.meanProcOn, hω, ↓reduceIte, MartMeans.meanProc, Real.toNNReal_coe]
        rfl
      · simp only [MartMeans2.meanProcOn, hω, ↓reduceIte, MartMeans.meanProc, Real.toNNReal_coe]
        rfl
    · have e : (fun t => MartMeans2.meanProcOn κ W U z G t ω) = fun _ => 0 := by
        funext t
        simp only [MartMeans2.meanProcOn, hω, ↓reduceIte]
      rw [e]
      exact continuousWithinAt_const
  · -- agreement before `T` on the good event
    intro ω hω t _
    simp only [MartMeans2.meanProcOn, hω.1.1, ↓reduceIte, MartMeans.meanProc]
    rfl
  · -- the time-zero mean is measurable: it is affine in the `𝓖₀`-measurable phase
    have hgL : ∀ i, Measurable fun ω => geomLW W xL i 0 ω := fun i => by
      intro A hA
      have h := adaptedBefore_geomLW hc hWa hxLm i 0 A hA
      have e : {ω | ((0 : ℝ≥0) : ℝ≥0∞) < T ω ∧ geomLW W xL i 0 ω ∈ A} = (fun ω => geomLW W xL i 0 ω) ⁻¹' A := by
        ext ω
        simp only [mem_ofPred_eq, mem_preimage, ENNReal.coe_zero, hT0 ω, true_and]
      rw [e] at h
      exact 𝓖.le 0 _ h
    have hgR : ∀ j, Measurable fun ω => geomRW W xR j 0 ω := fun j => by
      intro A hA
      have h := adaptedBefore_geomRW hc hWa hxRm j 0 A hA
      have e : {ω | ((0 : ℝ≥0) : ℝ≥0∞) < T ω ∧ geomRW W xR j 0 ω ∈ A} = (fun ω => geomRW W xR j 0 ω) ⁻¹' A := by
        ext ω
        simp only [mem_ofPred_eq, mem_preimage, ENNReal.coe_zero, hT0 ω, true_and]
      rw [e] at h
      exact 𝓖.le 0 _ h
    set vL0 : Ω → Fin (nL + 1) → ℝ := fun ω i => geomLW W xL i 0 ω - W 0 ω with hvL0
    set vR0 : Ω → Fin (nR + 1) → ℝ := fun ω j => geomRW W xR j 0 ω - W 0 ω with hvR0
    have hm : ∀ ω, couplingMean κ (wpath W ω) ((0 : ℝ≥0) : ℝ) (U ω 0) z =
        Ito.meanHarmonic κ ρL ρR (vL0 ω) (vR0 ω) z + c ω * (Ito.meanHarmonic κ (shiftL κ ρL 1) (shiftR κ ρR 1)
          (vL0 ω) (vR0 ω) z - Ito.meanHarmonic κ ρL ρR (vL0 ω) (vR0 ω) z) + c ω := by
      intro ω
      have hw0 : wpath W ω 0 = 0 := by simp [wpath, hW0 ω]
      have hf0 : QuantumZipper.fwdMap (wpath W ω) 0 z = z := by
        rw [QuantumZipper.B5.fwdMap_zero_time _ (by rw [hw0]; exact hz0), hw0, Complex.ofReal_zero, sub_zero]
      have h0 := hord ω 0 (hT0 ω)
      have hsh := isBoundedHarmonicExtension_shift hκ (sub_nonpos.2 (h0.1 0)) (sub_nonneg.2 (h0.2 0))
        (hU' ω 0 (hT0 ω))
      have e1 : couplingMean κ (wpath W ω) ((0 : ℝ≥0) : ℝ) (U ω 0) z =
          couplingMean κ (wpath W ω) ((0 : ℝ≥0) : ℝ) (fun ξ => U ω 0 ξ - c ω) z + c ω := by
        rw [couplingMean_sub_const, sub_add_cancel]
      rw [e1, NNReal.coe_zero, Ito.couplingMean_eq_meanHarmonic (fun i => sub_nonpos.2 (h0.1 i))
        (fun j => sub_nonneg.2 (h0.2 j)) hsh (by rw [hf0]; exact hz), hf0, MartMeans2.logDerivFwd_zero,
        Complex.zero_im, mul_zero, sub_zero, meanHarmonic_shift_affine]
    have e : (fun ω => couplingMean κ (wpath W ω) ((0 : ℝ≥0) : ℝ) (U ω 0) z) = fun ω =>
        Ito.meanHarmonic κ ρL ρR (vL0 ω) (vR0 ω) z + c ω * (Ito.meanHarmonic κ (shiftL κ ρL 1) (shiftR κ ρR 1)
          (vL0 ω) (vR0 ω) z - Ito.meanHarmonic κ ρL ρR (vL0 ω) (vR0 ω) z) + c ω := funext hm
    show Measurable fun ω => couplingMean κ (wpath W ω) ((0 : ℝ≥0) : ℝ) (U ω 0) z
    rw [e]
    have hW0m : Measurable fun ω => W 0 ω := by
      simp only [hW0]
      exact measurable_const
    have hvLm : Measurable vL0 := measurable_pi_iff.2 fun i => (hgL i).sub hW0m
    have hvRm : Measurable vR0 := measurable_pi_iff.2 fun j => (hgR j).sub hW0m
    have hcm' : Measurable c := hcm.mono (𝓖.le 0) le_rfl
    have hA := measurable_meanHarmonic (κ := κ) (ρL := ρL) (ρR := ρR) hvLm hvRm z
    have hB := measurable_meanHarmonic (κ := κ) (ρL := shiftL κ ρL 1) (ρR := shiftR κ ρR 1) hvLm hvRm z
    exact (hA.add (hcm'.mul (hB.sub hA))).add hcm'

end Main

end InteractingSLE.Sec7.PhaseMart
