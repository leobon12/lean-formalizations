/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.LocalExtAPath
import InteractingSLE.Spec.Sec7.LocalExtBStep7

/-!
# Aux. lemma 55, (HL9): the shifted conditional mean is the two-seed mean

Packet PROVE-LOCEXT-C (step 5, kernel half, deterministic part). Specification p. 250: "Conditional Cameron–Martin
shifting changes the mean to `C_{K_t} − P_t f` and leaves this covariance unchanged. Equation (HL8) then changes its
outside-hull mean to `M_t − P_t f + f − q = M_t − q + (f − P_t f) = M_t − q_t = M⁰_t`. (HL9)"

Along a good path, at a time `t` through the local stop and at a point `y ∈ ℍ ∖ K_t`:

* `couplingMean_eq_add_qAt`: the coupling mean of the force word is the coupling mean with the seed weights only plus
  the distant harmonic correction `q_t(y)` of (HL5) (`meanHarmonic_eq_add_distantHarm` in the chart);
* `meanHarmonic_seedWt_eq_twoSeed`: the mean with the seed weights only is the mean of the **two-seed word** (the seed
  group of each side amalgamated into one mark of weight `seedSumL` / `seedSumR` at the common seed position);
* **`couplingMean_sub_greenPot_add_eq`** ((HL9)): `𝔥_t(y) − G_{ℍ∖K_t} v (y) + f(y) − q(y) = 𝔥⁰_t(y)`, where `𝔥⁰_t` is the
  coupling mean of the two-seed word at the merged seed positions (every bounded harmonic extension of its data), by
  (HL6) along the good path (`greenPot_eq_of_isGoodPath`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace LocalExt

open QuantumZipper

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}

/-- **The seed-weight mean is the two-seed mean**: if every left seed mark is at `cL` and every right seed mark at
`cR`, the canonical mean with the seed weights only (`seedWtL`, `seedWtR`) is the canonical mean of the two-seed word
with weights `(seedSumL, seedSumR)` at `(cL, cR)`. -/
theorem meanHarmonic_seedWt_eq_twoSeed (κ : ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ)
    (ρR : Fin nR → ℝ) {vL : Fin nL → ℝ} {vR : Fin nR → ℝ} {cL cR : ℝ} (hL : ∀ i, xL i = 0 → vL i = cL)
    (hR : ∀ j, xR j = 0 → vR j = cR) (w : ℂ) :
    Ito.meanHarmonic κ (seedWtL xL ρL) (seedWtR xR ρR) vL vR w =
      Ito.meanHarmonic κ (fun _ : Fin 1 => seedSumL xL ρL) (fun _ : Fin 1 => seedSumR xR ρR) (fun _ => cL)
        (fun _ => cR) w := by
  have e1 : ∑ i, seedWtL xL ρL i * Complex.arg (w - vL i) = seedSumL xL ρL * Complex.arg (w - cL) := by
    rw [seedSumL, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : xL i = 0
    · rw [hL i hi]
    · simp [seedWtL, hi]
  have e2 : ∑ j, seedWtR xR ρR j * Complex.arg (w - vR j) = seedSumR xR ρR * Complex.arg (w - cR) := by
    rw [seedSumR, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : xR j = 0
    · rw [hR j hj]
    · simp [seedWtR, hj]
  simp only [Ito.meanHarmonic, Finset.univ_unique, Finset.sum_singleton]
  rw [e1, e2]
  rfl

/-- **The coupling mean splits** into the seed-weight coupling mean and the distant correction (HL5) in the chart. -/
theorem couplingMean_eq_add_distantHarm (κ : ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ)
    (ρR : Fin nR → ℝ) {vL : Fin nL → ℝ} {vR : Fin nR → ℝ} (hvL : ∀ i, vL i ≤ 0) (hvR : ∀ i, 0 ≤ vR i)
    {u u₀ : ℂ → ℝ}
    (hu : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR vL vR) (forceJumpSet vL vR) u)
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ (seedWtL xL ρL) (seedWtR xR ρR) vL vR)
      (forceJumpSet vL vR) u₀)
    {w : ℝ → ℝ} {t : ℝ} {z : ℂ} (hz : fwdMap w t z ∈ H) :
    couplingMean κ w t u z = couplingMean κ w t u₀ z + distantHarm κ xL xR ρL ρR vL vR (fwdMap w t z) := by
  rw [Ito.couplingMean_eq_meanHarmonic hvL hvR hu hz, Ito.couplingMean_eq_meanHarmonic hvL hvR hu₀ hz,
    meanHarmonic_eq_add_distantHarm]
  ring

/-- **(HL9) along a good path.** At a time `t ≤ S` and a point `y ∈ ℍ ∖ K_t`, with `u` a bounded harmonic extension of
the force data at the centred positions at time `t` and `u₂` one of the two-seed data (weights `(seedSumL, seedSumR)`)
at centred positions `(cL, cR)` that are the merged seed positions (`cL ≤ 0 ≤ cR`; on a side without seed any such
position, the weight being `0`):

`𝔥_t(y) − G_{ℍ∖K_t} v (y) + f(y) − q(y) = 𝔥⁰_t(y)`. -/
theorem couplingMean_sub_greenPot_add_eq {r : ℝ} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ}
    {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} (hp : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ)
    (hterm : HasThresholdLimit ρL ρR w vL vR ζ) (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r)
    (hseed : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR) {t : ℝ≥0}
    (ht : (t : WithTop ℝ≥0) ≤ localStopPath r ζ w) (htζ : (t : ℝ≥0∞) < ζ) {y : ℂ}
    (hy : y ∈ H \ fwdHull (Ito.rpath w) t) {u u₂ : ℂ → ℝ}
    (hu : IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => vL i t - w t) (fun i => vR i t - w t))
      (forceJumpSet (fun i => vL i t - w t) (fun i => vR i t - w t)) u)
    {cL cR : ℝ} (hcL : cL ≤ 0) (hcR : 0 ≤ cR) (hcL' : ∀ i, xL i = 0 → vL i t - w t = cL)
    (hcR' : ∀ j, xR j = 0 → vR j t - w t = cR)
    (hu₂ : IsBoundedHarmonicExtension
      (forceBoundaryData κ (fun _ : Fin 1 => seedSumL xL ρL) (fun _ : Fin 1 => seedSumR xR ρR) (fun _ => cL)
        (fun _ => cR)) (forceJumpSet (fun _ : Fin 1 => cL) (fun _ : Fin 1 => cR)) u₂) :
    couplingMean κ (Ito.rpath w) t u y - greenPot κ xL xR ρL ρR r (Ito.rpath w) t y + fCut κ xL xR ρL ρR r y -
        qExt κ xL xR ρL ρR y = couplingMean κ (Ito.rpath w) t u₂ y := by
  have hpu := hp.isSLEPathUpTo le_rfl
  set vL' : Fin nL → ℝ := fun i => vL i t - w t with hvL'
  set vR' : Fin nR → ℝ := fun i => vR i t - w t with hvR'
  have hvL0 : ∀ i, vL' i ≤ 0 := fun i => by simp only [hvL']; linarith [hpu.vL_le_w htζ i]
  have hvR0 : ∀ i, 0 ≤ vR' i := fun i => by simp only [hvR']; linarith [hpu.w_le_vR htζ i]
  -- the image of `y` lies in `ℍ`
  have hwc : ContinuousOn (Ito.rpath w) (Icc 0 (t : ℝ)) := by
    refine hpu.continuousOn_w.comp continuous_real_toNNReal.continuousOn fun s hs => ?_
    exact toNNReal_lt_of_mem_Icc htζ hs
  have hfH : fwdMap (Ito.rpath w) t y ∈ H :=
    Ito.im_fwdMap_pos_of_continuousOn t.coe_nonneg hwc hy.1 (Ito.exists_isForwardSol_of_mem t.coe_nonneg hy)
      ⟨t.coe_nonneg, le_rfl⟩
  -- the seed-weight extension, given explicitly
  have hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ (seedWtL xL ρL) (seedWtR xR ρR) vL' vR')
      (forceJumpSet vL' vR') (Impl.forceExt κ (Ito.weightWord (seedWtL xL ρL) (seedWtR xR ρR)) vL' vR') :=
    Impl.isBoundedHarmonicExtension_forceExt κ (Ito.weightWord (seedWtL xL ρL) (seedWtR xR ρR)) vL' vR'
  have hsplit := couplingMean_eq_add_distantHarm κ xL xR ρL ρR hvL0 hvR0 hu hu₀ hfH
  -- the seed-weight mean is the two-seed mean
  have h2 : couplingMean κ (Ito.rpath w) t
      (Impl.forceExt κ (Ito.weightWord (seedWtL xL ρL) (seedWtR xR ρR)) vL' vR') y =
      couplingMean κ (Ito.rpath w) t u₂ y := by
    rw [Ito.couplingMean_eq_meanHarmonic hvL0 hvR0 hu₀ hfH,
      Ito.couplingMean_eq_meanHarmonic (fun _ => hcL) (fun _ => hcR) hu₂ hfH,
      meanHarmonic_seedWt_eq_twoSeed κ xL xR ρL ρR hcL' hcR']
  -- (HL6)
  have hG := greenPot_eq_of_isGoodPath hp hterm hF hr hseed t.coe_nonneg (by rwa [Real.toNNReal_coe]) hy
  have hq : qAt κ xL xR ρL ρR (Ito.rpath w) (fun i => Ito.rpath (vL i)) (fun i => Ito.rpath (vR i)) t y =
      distantHarm κ xL xR ρL ρR vL' vR' (fwdMap (Ito.rpath w) t y) := by
    simp only [qAt, Ito.rpath_coe, hvL', hvR']
  rw [hsplit, hG, hq, h2]
  ring

end LocalExt

end InteractingSLE
