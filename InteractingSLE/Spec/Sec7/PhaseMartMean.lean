/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PhaseSel2
import InteractingSLE.Spec.Coupling.MartMeans2Local

/-!
# Aux. lemma 122 with a nonzero phase, part 1: the explicit mean of the phase-shifted word

Packet PROVE-PHASEMART (specification §7.4, Aux. lemma 122, `source/spec/p385-432.md` L103–L139, pp. 389–391:
"Retain a stopped Gaussian field kernel whose harmonic mean `M_t(z)` is a continuous local martingale until `z` is
swallowed. Assume the following exact boundary description […]"; Astra's follow-up 5 §3.2,
`source/external/AstraIG1/ig1_followup5.txt` L456–L475, (3.2): `M_t(z) − M⁰_t(z) = δ_t ω_t(z)`).

The boundary word of Aux. lemma 122 at time `t` is the force word with the exposed interval `(V⁻, V⁺)` raised by the
phase `d_t` (`PhaseSel.phaseData`). By (PS9.2) (`PhaseSel.isBoundedHarmonicExtension_shift`) every bounded harmonic
extension of it is `c` plus an extension of the canonical word of the shifted seed weights `shiftL c`, `shiftR c`.
Here the explicit harmonic mean of the shifted word is shown to be **affine in the phase** (`meanCan_shift_affine`:
`𝔥^{(c)} = 𝔥 + c (𝔥^{(1)} − 𝔥)`, the window term of (3.2)), and the mean value identities on a safe ball are proved
for the phase-shifted word (`couplingMean_eq_phase_of_safe`, `integral_couplingMean_mul_bumpFun_phase`). The
conditional-law clause of the optional hull specification is stated for the phase-shifted word
(`IsPhaseCouplingCharFun`); with the zero phase it is `MartMeans.IsCouplingCharFun`
(`isPhaseCouplingCharFun_zero_iff`).

## Main definitions and results

* `phaseWin κ a b ξ = (arg(ξ − b) − arg(ξ − a) − π)/√κ`: the window term;
* `meanHarmonic_shift`, `meanCan_shift`, **`meanCan_shift_affine`**: the explicit mean is affine in the phase;
* **`couplingMean_eq_phase_of_safe`**, **`integral_couplingMean_mul_bumpFun_phase`**: on a safe ball the coupling mean
  of any extension of the phase-`c` word is `𝔥^{(c)} + c`, and its bump pairing is `(𝔥^{(c)}(z) + c) ∫ bump`;
* `IsPhaseCouplingCharFun`: the conditional-law clause for the phase-shifted word, with a phase process `d`;
* `isPhaseCouplingCharFun_zero_iff`: with `d = 0` it is `IsCouplingCharFun`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology QuantumZipper Complex Metric
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PhaseMart

open Coupling Coupling.MartMeans Ito PhaseSel

variable {nL nR : ℕ}

/-! ### The explicit mean is affine in the phase -/

section Affine

/-- **The window term** of (3.2) at the centred seed positions `a ≤ 0 ≤ b`, up to the factor `Λ = π/√κ`:
`(arg(ξ − b) − arg(ξ − a) − π)/√κ`. -/
def phaseWin (κ : ℝ) (a b : ℝ) (ξ : ℂ) : ℝ :=
  1 / Real.sqrt κ * (Complex.arg (ξ - b) - Complex.arg (ξ - a) - Real.pi)

/-- Raising the left seed weight by `a` and lowering the right one by `a` adds `a` times the window term. -/
theorem meanHarmonic_update (κ : ℝ) (ρL : Fin (nL + 1) → ℝ) (ρR : Fin (nR + 1) → ℝ) (vL : Fin (nL + 1) → ℝ)
    (vR : Fin (nR + 1) → ℝ) (a : ℝ) (ξ : ℂ) :
    meanHarmonic κ (Function.update ρL 0 (ρL 0 + a)) (Function.update ρR 0 (ρR 0 + -a)) vL vR ξ =
      meanHarmonic κ ρL ρR vL vR ξ + a * phaseWin κ (vL 0) (vR 0) ξ := by
  simp only [meanHarmonic, phaseWin, update_zero_add_eq, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  ring

/-- **The explicit harmonic function of the shifted word** (PS9.2): the seed weights shifted by the field constant
`c` add `(c/Λ)` times the window term. -/
theorem meanHarmonic_shift (κ : ℝ) (ρL : Fin (nL + 1) → ℝ) (ρR : Fin (nR + 1) → ℝ) (vL : Fin (nL + 1) → ℝ)
    (vR : Fin (nR + 1) → ℝ) (c : ℝ) (ξ : ℂ) :
    meanHarmonic κ (shiftL κ ρL c) (shiftR κ ρR c) vL vR ξ =
      meanHarmonic κ ρL ρR vL vR ξ + c / (Real.pi / Real.sqrt κ) * phaseWin κ (vL 0) (vR 0) ξ := by
  have hR : shiftR κ ρR c = Function.update ρR 0 (ρR 0 + -(c / (Real.pi / Real.sqrt κ))) := by
    simp only [shiftR, sub_eq_add_neg]
  rw [shiftL, hR, meanHarmonic_update]

/-- **The explicit mean of the shifted word along a path** is the explicit mean plus `(c/Λ)` times the window term
at the image point. -/
theorem meanCan_shift (κ : ℝ) (ρL : Fin (nL + 1) → ℝ) (ρR : Fin (nR + 1) → ℝ) (w : ℝ≥0 → ℝ)
    (vL : Fin (nL + 1) → ℝ≥0 → ℝ) (vR : Fin (nR + 1) → ℝ≥0 → ℝ) (s : ℝ≥0) (y : ℂ) (c : ℝ) :
    meanCan κ (shiftL κ ρL c) (shiftR κ ρR c) w vL vR s y =
      meanCan κ ρL ρR w vL vR s y +
        c / (Real.pi / Real.sqrt κ) * phaseWin κ (vL 0 s - w s) (vR 0 s - w s) (fwdMap (rpath w) s y) := by
  simp only [meanCan, meanHarmonic_shift]
  ring

/-- **The explicit mean is affine in the phase** ((3.2): `M − M⁰ = δ ω`):
`𝔥^{(c)} = 𝔥 + c (𝔥^{(1)} − 𝔥)`. -/
theorem meanCan_shift_affine (κ : ℝ) (ρL : Fin (nL + 1) → ℝ) (ρR : Fin (nR + 1) → ℝ) (w : ℝ≥0 → ℝ)
    (vL : Fin (nL + 1) → ℝ≥0 → ℝ) (vR : Fin (nR + 1) → ℝ≥0 → ℝ) (s : ℝ≥0) (y : ℂ) (c : ℝ) :
    meanCan κ (shiftL κ ρL c) (shiftR κ ρR c) w vL vR s y =
      meanCan κ ρL ρR w vL vR s y +
        c * (meanCan κ (shiftL κ ρL 1) (shiftR κ ρR 1) w vL vR s y - meanCan κ ρL ρR w vL vR s y) := by
  rw [meanCan_shift, meanCan_shift]
  ring

end Affine

/-! ### The coupling mean of the phase-shifted word on a safe ball -/

section Safe

variable {κ : ℝ} {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin (nL + 1) → ℝ≥0 → ℝ}
  {vR : Fin (nR + 1) → ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {N : ℝ} {σ₀ r s : ℝ≥0} {z : ℂ}

/-- **On a safe ball the coupling mean of any extension of the phase-`c` word is the explicit mean of the shifted
word plus `c`** ((PS9.2) and the explicit mean `couplingMean_eq_meanCan_of_safe`). -/
theorem couplingMean_eq_phase_of_safe (hκ : 0 < κ) (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) (hz : 0 < z.im)
    (n : ℕ) (hsafe : IsSafeAt (closedBall z (locRad z n)) (locLevel z n) N σ₀ ζ w r) (hs : s ≤ r)
    (hvL : ∀ i, vL i s ≤ w s) (hvR : ∀ i, w s ≤ vR i s) {c : ℝ} {u : ℂ → ℝ}
    (hu : IsBoundedHarmonicExtension
      (phaseData κ ρL ρR (fun i => vL i s - w s) (fun i => vR i s - w s) c)
      (forceJumpSet (fun i => vL i s - w s) (fun i => vR i s - w s)) u) {y : ℂ}
    (hy : y ∈ closedBall z (locRad z n)) :
    couplingMean κ (rpath w) s u y = meanCan κ (shiftL κ ρL c) (shiftR κ ρR c) w vL vR s y + c := by
  have hu' := isBoundedHarmonicExtension_shift hκ (sub_nonpos.2 (hvL 0)) (sub_nonneg.2 (hvR 0)) hu
  have h := couplingMean_eq_meanCan_of_safe (ρL := shiftL κ ρL c) (ρR := shiftR κ ρR c) hw hz n hsafe hs hvL hvR
    hu' hy
  rw [couplingMean_sub_const] at h
  linarith

/-- A function continuous on the localizing ball, times the bump, is integrable. -/
theorem integrable_mul_bumpFun_of_continuousOn {f : ℂ → ℝ} (hz : 0 < z.im) (n : ℕ)
    (hf : ContinuousOn f (closedBall z (locRad z n))) :
    Integrable (fun y => f y * GFF.bumpFun z (bumpRadius z n) y) := by
  have hφc : Continuous (GFF.bumpFun z (bumpRadius z n)) := (GFF.contDiff_bumpFun z _).continuous
  have hI : IntegrableOn (fun y => f y * GFF.bumpFun z (bumpRadius z n) y) (closedBall z (locRad z n)) :=
    (hf.mul hφc.continuousOn).integrableOn_compact (isCompact_closedBall z _)
  refine (integrableOn_iff_integrable_of_support_subset fun y hy => ?_).1 hI
  by_contra hns
  have h0 : GFF.bumpFun z (bumpRadius z n) y = 0 :=
    image_eq_zero_of_notMem_tsupport fun ht => hns (tsupport_bumpFun_subset_locBall hz n ht)
  exact hy (by simp only [h0, mul_zero])

/-- **The bump pairing of the coupling mean of the phase-`c` word on a safe ball**: `(𝔥^{(c)}(z) + c) ∫ bump`. -/
theorem integral_couplingMean_mul_bumpFun_phase (hκ : 0 < κ) (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ})
    (hz : 0 < z.im) (n : ℕ) (hsafe : IsSafeAt (closedBall z (locRad z n)) (locLevel z n) N σ₀ ζ w r) (hs : s ≤ r)
    (hvL : ∀ i, vL i s ≤ w s) (hvR : ∀ i, w s ≤ vR i s) {c : ℝ} {u : ℂ → ℝ}
    (hu : IsBoundedHarmonicExtension
      (phaseData κ ρL ρR (fun i => vL i s - w s) (fun i => vR i s - w s) c)
      (forceJumpSet (fun i => vL i s - w s) (fun i => vR i s - w s)) u) :
    ∫ y, couplingMean κ (rpath w) s u y * GFF.bumpFun z (bumpRadius z n) y =
      (meanCan κ (shiftL κ ρL c) (shiftR κ ρR c) w vL vR s z + c) * bumpNorm z n := by
  set φ := GFF.bumpFun z (bumpRadius z n) with hφ
  have hr : 0 < bumpRadius z n := bumpRadius_pos hz n
  have h1 : (fun y => couplingMean κ (rpath w) s u y * φ y) =
      fun y => meanCan κ (shiftL κ ρL c) (shiftR κ ρR c) w vL vR s y * φ y + c * φ y := by
    funext y
    by_cases hy : y ∈ closedBall z (locRad z n)
    · rw [couplingMean_eq_phase_of_safe hκ hw hz n hsafe hs hvL hvR hu hy]
      ring
    · have h0 : φ y = 0 := by
        rw [hφ]
        refine GFF.bumpFun_eq_zero hr ?_
        rw [mem_closedBall, not_le] at hy
        exact (bumpRadius_le hz n).trans hy.le
      simp only [h0, mul_zero, add_zero]
  have hint1 : Integrable fun y => meanCan κ (shiftL κ ρL c) (shiftR κ ρR c) w vL vR s y * φ y :=
    integrable_mul_bumpFun_of_continuousOn hz n
      (hsafe.continuousOn_meanCan_space hw (closedBall_locRad_subset hz n) (locLevel_pos hz n) hs)
  have hint2 : Integrable fun y => c * φ y :=
    ((GFF.contDiff_bumpFun z _).continuous.integrable_of_hasCompactSupport
      (GFF.hasCompactSupport_bumpFun hr)).const_mul c
  rw [h1, integral_add hint1 hint2, integral_const_mul, hφ, GFF.integral_bumpFun hr,
    hsafe.integral_meanCan_mul_bumpFun hw (closedBall_locRad_subset hz n) hs hr (bumpRadius_le hz n)]
  simp only [bumpNorm]
  ring

end Safe

/-! ### The conditional-law clause for the phase-shifted word -/

section Clause

/-- **The conditional-law clause of the optional hull specification for the phase-shifted word** (Aux. lemma 122's
boundary description, specification p. 389): for every stopping time `τ < ζ` of `𝓖`, every choice `u` of the bounded
harmonic extensions of the word `ρ` at the centred positions at `τ` with the exposed interval raised by the phase
`d_τ` (`PhaseSel.phaseData`), and every test function `φ`, almost surely on `{supp φ ∩ K_τ = ∅}`,
`E[e^{i (h, φ)} | 𝓖_τ] = exp(i (𝔥_τ, φ) − ½ E_τ(φ))`. With `d = 0` this is `MartMeans.IsCouplingCharFun`. -/
def IsPhaseCouplingCharFun (κ : ℝ) (ρL : Fin (nL + 1) → ℝ) (ρR : Fin (nR + 1) → ℝ) {Ω : Type*}
    {mΩ : MeasurableSpace Ω} (P : Measure Ω) (𝓖 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ)
    (VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ) (VR : Fin (nR + 1) → ℝ≥0 → Ω → ℝ) (d : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞)
    (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens) : Prop :=
  ∀ (τ : Ω → WithTop ℝ≥0) (hτ : IsStoppingTime 𝓖 τ), (∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < ζ ω) →
    ∀ u : Ω → ℂ → ℝ,
      (∀ ω, IsBoundedHarmonicExtension
          (phaseData κ ρL ρR (fun i => VL i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)
            (fun i => VR i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω) (d ((τ ω).untopD 0) ω))
          (forceJumpSet (fun i => VL i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)
            (fun i => VR i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω))
          (u ω)) →
      ∀ φ : LQGMetric.TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P,
        Disjoint (tsupport φ) (QuantumZipper.fwdHull (fun s : ℝ => W s.toNNReal ω)
            ((τ ω).untopD 0 : ℝ≥0)) →
          condExp hτ.measurableSpace P
              (fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ))) ω =
            Complex.exp (Complex.I * ((∫ z, couplingMean κ (fun s : ℝ => W s.toNNReal ω)
                ((τ ω).untopD 0 : ℝ≥0) (u ω) z * φ z : ℝ) : ℂ) -
              (((1 / 2 : ℝ) * loewnerGreenEnergy (fun s : ℝ => W s.toNNReal ω)
                ((τ ω).untopD 0 : ℝ≥0) φ : ℝ) : ℂ))

/-- **With the zero phase the clause is the conditional-law clause of the force word.** -/
theorem isPhaseCouplingCharFun_zero_iff {κ : ℝ} {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ} {Ω : Type*}
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓖 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ} {VR : Fin (nR + 1) → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} :
    IsPhaseCouplingCharFun κ ρL ρR P 𝓖 W VL VR (fun _ _ => 0) ζ h ↔ IsCouplingCharFun κ ρL ρR P 𝓖 W VL VR ζ h := by
  have e : ∀ (vL : Fin (nL + 1) → ℝ) (vR : Fin (nR + 1) → ℝ),
      phaseData κ ρL ρR vL vR 0 = forceBoundaryData κ ρL ρR vL vR := fun vL vR => by
    funext x
    simp [phaseData]
  simp only [IsPhaseCouplingCharFun, IsCouplingCharFun, e]

end Clause

end InteractingSLE.Sec7.PhaseMart
