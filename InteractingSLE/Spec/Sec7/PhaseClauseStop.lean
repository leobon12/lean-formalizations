/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PhaseMartMean
import InteractingSLE.Spec.Restart.DomainMarkovAux79Stop

/-!
# The phase conditional-law clause at stopping times from the phase law at positive fixed times

Packet PROVE-PHASECLAUSE. Specification Aux. lemma 122 (`source/spec/p385-432.md`, pp. 389–391: "Retain a stopped
Gaussian field kernel whose harmonic mean `M_t(z)` is a continuous local martingale until `z` is swallowed") and
Astra's follow-up 5 §3.2 (R73, `source/external/AstraIG1/ig1_followup5.txt` L456–L483: "On a time-zero event with
`δ = 2πnχ`, subtracting this constant from the field changes its formal seed weights").

PROVE-PHASEMART reduced Aux. lemma 122's retained hypothesis for a lattice phase `c` to the conditional-law clause
`PhaseMart.IsPhaseCouplingCharFun` of the phase-`c` word (the force word with the exposed interval raised by `c`) at
every stopping time. The landed bridge from fixed times to stopping times
(`Restart.DomainMarkov.Aux79.isCouplingCharFun_of_hasSafeLaw`) is written for a fixed word and asks for the law at
every fixed time including `0`. This file reruns it for a **random phase `c` known at time `0`** of the usual
augmentation, from the law at **positive** fixed times only (the dyadic approximation from above uses only the times
`(k + 1)/2ⁿ > 0`; at time `0` the retained σ-algebra need not know the phase):

* `phaseProc`: the explicit extension of the phase-`c` word (the canonical extension of the shifted word plus `c`);
* `couplingMean_eq_phase`, `integral_couplingMean_phase`, `phaseInt`: on a safe time the tested coupling mean of
  every extension of the phase-`c` word is `𝔥_A + c (𝔥_B − 𝔥_A) + c ∫ψ`, with `𝔥_A`, `𝔥_B` the explicit tested means
  of the two fixed words `(ρL; ρR)` and `(shiftL 1; shiftR 1)` (PROVE-PHASEMART's affine identity);
* `HasPhaseSafeLaw` (K2's (S) for the phase word at positive times);
* **`isPhaseCouplingCharFun_of_hasPhaseSafeLaw`**: (S) for the phase word at positive times, a phase measurable at
  time `0` of the usual augmentation and pathwise regularity give `IsPhaseCouplingCharFun` with the constant phase.

The proofs are copies of `DomainMarkovAux79Stop` with the fixed word replaced by the phase word (provenance in the
docstrings). Conditional helpers; no source theorem is replaced. Ruling R48: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement` or any result taking them as hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology QuantumZipper
open scoped NNReal ENNReal Classical

namespace InteractingSLE.Sec7.PhaseClause

open Restart.DomainMarkov Restart.DomainMarkov.Aux79 Restart.DomainMarkov.K2 Coupling Ito PhaseSel PhaseMart

variable {nL nR : ℕ} {κ : ℝ} {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ}

/-! ### The phase mean along one path on a safe time -/

section Safe

variable {w : ℝ≥0 → ℝ} {vL : Fin (nL + 1) → ℝ≥0 → ℝ} {vR : Fin (nR + 1) → ℝ≥0 → ℝ} {ζ₀ : ℝ≥0∞}
  {K : Set ℂ} {δ N : ℝ} {σ₀ r s : ℝ≥0} {z : ℂ}

/-- **On a safe time the coupling mean of any extension of the phase-`c` word is the explicit mean of the shifted
word plus `c`** ((PS9.2) and `Coupling.couplingMean_eq_meanCan`). -/
theorem couplingMean_eq_phase (hκ : 0 < κ) (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ₀}) (hKH : K ⊆ H)
    (h : IsSafeAt K δ N σ₀ ζ₀ w r) (hδ : 0 < δ) (hs : s ≤ r) (hz : z ∈ K)
    (hvL : ∀ i, vL i s ≤ w s) (hvR : ∀ i, w s ≤ vR i s) {c : ℝ} {u : ℂ → ℝ}
    (hu : IsBoundedHarmonicExtension (phaseData κ ρL ρR (fun i => vL i s - w s) (fun i => vR i s - w s) c)
      (forceJumpSet (fun i => vL i s - w s) (fun i => vR i s - w s)) u) :
    couplingMean κ (rpath w) s u z = meanCan κ (shiftL κ ρL c) (shiftR κ ρR c) w vL vR s z + c := by
  have hu' := isBoundedHarmonicExtension_shift hκ (sub_nonpos.2 (hvL 0)) (sub_nonneg.2 (hvR 0)) hu
  have h1 := couplingMean_eq_meanCan (ρL := shiftL κ ρL c) (ρR := shiftR κ ρR c) hw hKH h hδ hs hz hvL hvR hu'
  rw [couplingMean_sub_const] at h1
  linarith

/-- On a safe time the explicit mean times a test function is integrable. -/
theorem integrable_meanCan_mul {ψ : ℂ → ℝ} (hψc : Continuous ψ) (hψs : HasCompactSupport ψ)
    (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ₀}) (hKH : tsupport ψ ⊆ H)
    (h : IsSafeAt (tsupport ψ) δ N σ₀ ζ₀ w r) (hδ : 0 < δ) (hs : s ≤ r) {nL' nR' : ℕ} (ρL' : Fin nL' → ℝ)
    (ρR' : Fin nR' → ℝ) (vL' : Fin nL' → ℝ≥0 → ℝ) (vR' : Fin nR' → ℝ≥0 → ℝ) :
    Integrable (fun z => meanCan κ ρL' ρR' w vL' vR' s z * ψ z) := by
  refine Integrable.mono' ((hψc.integrable_of_hasCompactSupport hψs).abs.const_mul
    (meanHarmonicBound κ ρL' ρR' + |chiC κ| * (2 / δ ^ 2 * r)))
    (h.aestronglyMeasurable_meanCan_mul hψc hw hKH hδ hs) (ae_of_all _ fun z => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  by_cases hz : z ∈ tsupport ψ
  · exact mul_le_mul_of_nonneg_right (h.abs_meanCan_le hw hKH hδ hs hz) (abs_nonneg _)
  · simp [image_eq_zero_of_notMem_tsupport hz]

/-- **The explicit tested mean of the phase-`c` word**: `𝔥_A + c (𝔥_B − 𝔥_A) + c ∫ψ`, with `𝔥_A`, `𝔥_B` the tested
explicit means of the words `(ρL; ρR)` and `(shiftL 1; shiftR 1)`. -/
def phaseInt (κ : ℝ) (ρL : Fin (nL + 1) → ℝ) (ρR : Fin (nR + 1) → ℝ) (w : ℝ≥0 → ℝ)
    (vL : Fin (nL + 1) → ℝ≥0 → ℝ) (vR : Fin (nR + 1) → ℝ≥0 → ℝ) (s : ℝ≥0) (ψ : ℂ → ℝ) (c : ℝ) : ℝ :=
  (∫ z, meanCan κ ρL ρR w vL vR s z * ψ z) +
    c * ((∫ z, meanCan κ (shiftL κ ρL 1) (shiftR κ ρR 1) w vL vR s z * ψ z) -
      (∫ z, meanCan κ ρL ρR w vL vR s z * ψ z)) + c * (∫ z, ψ z)

/-- **On a safe time the tested coupling mean of every extension of the phase-`c` word is `phaseInt`.** -/
theorem integral_couplingMean_phase (hκ : 0 < κ) {ψ : ℂ → ℝ} (hψc : Continuous ψ) (hψs : HasCompactSupport ψ)
    (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ₀}) (hKH : tsupport ψ ⊆ H)
    (h : IsSafeAt (tsupport ψ) δ N σ₀ ζ₀ w r) (hδ : 0 < δ) (hs : s ≤ r)
    (hvL : ∀ i, vL i s ≤ w s) (hvR : ∀ i, w s ≤ vR i s) {c : ℝ} {u : ℂ → ℝ}
    (hu : IsBoundedHarmonicExtension (phaseData κ ρL ρR (fun i => vL i s - w s) (fun i => vR i s - w s) c)
      (forceJumpSet (fun i => vL i s - w s) (fun i => vR i s - w s)) u) :
    ∫ z, couplingMean κ (rpath w) s u z * ψ z = phaseInt κ ρL ρR w vL vR s ψ c := by
  have hA := integrable_meanCan_mul (κ := κ) hψc hψs hw hKH h hδ hs ρL ρR vL vR
  have hB := integrable_meanCan_mul (κ := κ) hψc hψs hw hKH h hδ hs (shiftL κ ρL 1) (shiftR κ ρR 1) vL vR
  have hψi : Integrable ψ := hψc.integrable_of_hasCompactSupport hψs
  have e : (fun z => couplingMean κ (rpath w) s u z * ψ z) = fun z =>
      (meanCan κ ρL ρR w vL vR s z * ψ z + c * (meanCan κ (shiftL κ ρL 1) (shiftR κ ρR 1) w vL vR s z * ψ z -
        meanCan κ ρL ρR w vL vR s z * ψ z)) + c * ψ z := by
    funext z
    by_cases hz : z ∈ tsupport ψ
    · rw [couplingMean_eq_phase hκ hw hKH h hδ hs hz hvL hvR hu, meanCan_shift_affine]
      ring
    · simp [image_eq_zero_of_notMem_tsupport hz]
  have i2 : Integrable (fun z => c * (meanCan κ (shiftL κ ρL 1) (shiftR κ ρR 1) w vL vR s z * ψ z -
      meanCan κ ρL ρR w vL vR s z * ψ z)) := (hB.sub hA).const_mul c
  have i1 : Integrable (fun z => meanCan κ ρL ρR w vL vR s z * ψ z + c *
      (meanCan κ (shiftL κ ρL 1) (shiftR κ ρR 1) w vL vR s z * ψ z - meanCan κ ρL ρR w vL vR s z * ψ z)) :=
    hA.add i2
  have i3 : Integrable (fun z => c * ψ z) := hψi.const_mul c
  rw [e, integral_add i1 i3, integral_add hA i2, integral_const_mul, integral_sub hB hA, integral_const_mul,
    phaseInt]

/-- The explicit tested phase mean is continuous in time up to a safe time. -/
theorem continuousOn_phaseInt {ψ : ℂ → ℝ} (hψc : Continuous ψ) (hψs : HasCompactSupport ψ)
    (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ₀}) (hvLc : ∀ i, ContinuousOn (vL i) {t | (t : ℝ≥0∞) < ζ₀})
    (hvRc : ∀ i, ContinuousOn (vR i) {t | (t : ℝ≥0∞) < ζ₀}) (hKH : tsupport ψ ⊆ H)
    (h : IsSafeAt (tsupport ψ) δ N σ₀ ζ₀ w r) (hδ : 0 < δ) (c : ℝ) :
    ContinuousOn (fun s => phaseInt κ ρL ρR w vL vR s ψ c) (Iic r) := by
  have hA := h.continuousOn_meanInt (κ := κ) (ρL := ρL) (ρR := ρR) hψc hψs hw hvLc hvRc hKH hδ
  have hB := h.continuousOn_meanInt (κ := κ) (ρL := shiftL κ ρL 1) (ρR := shiftR κ ρR 1) hψc hψs hw hvLc hvRc
    hKH hδ
  exact (hA.add (continuousOn_const.mul (hB.sub hA))).add continuousOn_const

end Safe

/-! ### The phase extension process -/

section Proc

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ} {VR : Fin (nR + 1) → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **The phase extension process**: the canonical bounded harmonic extension of the shifted word
`(shiftL c; shiftR c)` plus the phase `c` (an extension of the phase-`c` word, (PS9.2)). -/
def phaseProc (κ : ℝ) (ρL : Fin (nL + 1) → ℝ) (ρR : Fin (nR + 1) → ℝ) (W : ℝ≥0 → Ω → ℝ)
    (VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ) (VR : Fin (nR + 1) → ℝ≥0 → Ω → ℝ) (c : Ω → ℝ) : Ω → ℝ≥0 → ℂ → ℝ :=
  fun ω s ξ => bheProc κ (shiftL κ ρL (c ω)) (shiftR κ ρR (c ω)) W VL VR ω s ξ + c ω

omit mΩ in
/-- The phase extension process extends the phase-`c` word when the seeds are on their sides of the driver. -/
theorem isBoundedHarmonicExtension_phaseProc (hκ : 0 < κ) (c : Ω → ℝ) {ω : Ω} {s : ℝ≥0}
    (hL : VL 0 s ω ≤ W s ω) (hR : W s ω ≤ VR 0 s ω) :
    IsBoundedHarmonicExtension
      (phaseData κ ρL ρR (fun i => VL i s ω - W s ω) (fun j => VR j s ω - W s ω) (c ω))
      (forceJumpSet (fun i => VL i s ω - W s ω) (fun j => VR j s ω - W s ω))
      (phaseProc κ ρL ρR W VL VR c ω s) :=
  isBoundedHarmonicExtension_unshift hκ (sub_nonpos.2 hL) (sub_nonneg.2 hR) (isBoundedHarmonicExtension_bheProc ω s)

/-- **Along one good path, times decreasing to an avoidance time are eventually safe, and `cfAt` of the phase word
converges** (`Aux79.exists_eventually_isSafeAt_tendsto_cfAt'` for the phase word). -/
theorem exists_eventually_isSafeAt_tendsto_cfAt_phase (hκ : 0 < κ) {c : Ω → ℝ} {u : Ω → ℝ≥0 → ℂ → ℝ}
    (ψ : LQGMetric.TestOn upperHalfPlaneOpens) {ω : Ω}
    (hu : ∀ s : ℝ≥0, (s : ℝ≥0∞) < ζ ω → IsBoundedHarmonicExtension
      (phaseData κ ρL ρR (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω) (c ω))
      (forceJumpSet (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω)) (u ω s))
    (hp : IsForceReg W VL VR ζ ω) {a : ℝ≥0} (haζ : (a : ℝ≥0∞) < ζ ω)
    (hdis : Disjoint (tsupport ψ) (fwdHull (fun s : ℝ => W s.toNNReal ω) a))
    {t : ℕ → ℝ≥0} (ht : Tendsto t atTop (𝓝 a)) :
    ∃ m : ℕ, (∀ᶠ n in atTop, IsSafeAt (tsupport ψ) (1 / ((m : ℝ) + 1)) (t n) (t n) (ζ ω) (W · ω) (t n)) ∧
      Tendsto (fun n => cfAt κ W u ψ 1 (fun _ => t n) ω) atTop (𝓝 (cfAt κ W u ψ 1 (fun _ => a) ω)) := by
  set K : Set ℂ := tsupport (ψ : ℂ → ℝ) with hKdef
  have hKH : K ⊆ H := tsupport_subset_H ψ
  have hK : IsCompact K := ψ.hasCompactSupport.isCompact
  have hw : ContinuousOn (W · ω) {t | (t : ℝ≥0∞) < ζ ω} := hp.2.1
  obtain ⟨δ', hδ', hrζ, hdisj⟩ := exists_pos_disjoint_fwdHull_rpath' hw haζ hK hKH hdis
  set r : ℝ≥0 := a + δ' with hr
  have halive : ∀ z ∈ K, ∃ v, IsForwardSol (rpath (W · ω)) z r v := fun z hz =>
    exists_isForwardSol_of_mem r.coe_nonneg ⟨hKH hz, fun hzK => Set.disjoint_left.1 (hdisj r le_rfl) hz hzK⟩
  obtain ⟨δ₀, hδ₀, hsafe⟩ := exists_isSafeAt_self hw hp.1 hK hKH hrζ halive
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ₀
  have har : a < r := lt_add_of_pos_right a hδ'
  have hev_le : ∀ᶠ n in atTop, t n ≤ r := ((tendsto_order.1 ht).2 r har).mono fun n h => h.le
  refine ⟨m, hev_le.mono fun n hn => ?_, ?_⟩
  · exact (isSafeAt_self_of (hsafe.anti hw hKH hn)).mono hm.le le_rfl le_rfl
  set g : ℝ≥0 → ℂ := fun s => Complex.exp (Complex.I * 1 *
      ((phaseInt κ ρL ρR (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω) s ψ (c ω) : ℝ) : ℂ) -
      1 ^ 2 * ((loewnerGreenEnergy (rpath (W · ω)) s ψ : ℝ) : ℂ) / 2) with hg
  have hgc : ContinuousOn g (Iic r) := by
    have h1 := continuousOn_phaseInt (κ := κ) (ρL := ρL) (ρR := ρR) ψ.continuous ψ.hasCompactSupport hw hp.2.2.1
      hp.2.2.2.1 hKH hsafe hδ₀ (c ω)
    have h2 := hsafe.continuousOn_loewnerGreenEnergy ψ.continuous ψ.hasCompactSupport hw hKH hδ₀
    exact ((continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn h1)).sub
      ((continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn h2)).div_const 2)).cexp
  have hcf : ∀ s ≤ r, cfAt κ W u ψ 1 (fun _ => s) ω = g s := fun s hs => by
    have hsζ : (s : ℝ≥0∞) < ζ ω := lt_of_le_of_lt (by exact_mod_cast hs) hrζ
    have hvL : ∀ i, VL i s ω ≤ W s ω := (hp.2.2.2.2 s hsζ).1
    have hvR : ∀ i, W s ω ≤ VR i s ω := (hp.2.2.2.2 s hsζ).2
    have hmean : (∫ z, couplingMean κ (fun x : ℝ => W x.toNNReal ω) s (u ω s) z * ψ z) =
        phaseInt κ ρL ρR (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω) s ψ (c ω) :=
      integral_couplingMean_phase (vL := fun i t => VL i t ω) (vR := fun i t => VR i t ω) hκ ψ.continuous
        ψ.hasCompactSupport hw hKH hsafe hδ₀ hs hvL hvR (hu s hsζ)
    simp only [cfAt, hg, hmean]
    rfl
  have hlim : Tendsto (fun n => g (t n)) atTop (𝓝 (g a)) :=
    (hgc a (mem_Iic.2 har.le)).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨ht, hev_le⟩)
  rw [hcf a har.le]
  exact hlim.congr' (hev_le.mono fun n hn => (hcf (t n) hn).symm)

/-- On a safe event at a fixed time `q`, `cfAt q` of the phase word is measurable (the explicit tested means `meanK` of
the two fixed words, the phase and the energy; `Aux79.measurable_safeSet_indicator_cfAt'`). -/
theorem measurable_safeSet_indicator_cfAt_phase {𝓖 : Filtration ℝ≥0 mΩ} (hκ : 0 < κ) {c : Ω → ℝ}
    (hcm : Measurable c) (ψ : LQGMetric.TestOn upperHalfPlaneOpens) {G : Set Ω}
    (hGp : ∀ ω ∈ G, IsForceReg W VL VR ζ ω) (hG0 : MeasurableSet[𝓖 0] G) (hWa : AdaptedBefore 𝓖 ζ W)
    (hVLa : ∀ i, AdaptedBefore 𝓖 ζ (VL i)) (hVRa : ∀ i, AdaptedBefore 𝓖 ζ (VR i)) {δ : ℝ} (hδ : 0 < δ)
    (q : ℝ≥0) :
    Measurable ((safeSet W ζ G ψ δ q).indicator (cfAt κ W (phaseProc κ ρL ρR W VL VR c) ψ 1 fun _ => q)) := by
  have hKH : tsupport (ψ : ℂ → ℝ) ⊆ H := tsupport_subset_H ψ
  have hGc : ∀ ω ∈ G, ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω} := fun ω hω =>
    (hGp ω hω).2.1
  set mA := meanK κ ρL ρR W VL VR ζ G ψ δ q with hmA
  set mB := meanK κ (shiftL κ ρL 1) (shiftR κ ρR 1) W VL VR ζ G ψ δ q with hmB
  have e : (safeSet W ζ G ψ δ q).indicator (cfAt κ W (phaseProc κ ρL ρR W VL VR c) ψ 1 fun _ => q) =
      (safeSet W ζ G ψ δ q).indicator (fun ω =>
        Complex.exp (Complex.I * 1 * ((mA ω + c ω * (mB ω - mA ω) + c ω * (∫ z, ψ z) : ℝ) : ℂ) -
          1 ^ 2 * ((energyK W ζ G ψ δ q ω : ℝ) : ℂ) / 2)) := by
    refine indicator_congr fun ω hω => ?_
    have hp := hGp ω hω.1
    have hw := hGc ω hω.1
    have hvL : ∀ i, VL i q ω ≤ W q ω := (hp.2.2.2.2 q hω.2.1).1
    have hvR : ∀ i, W q ω ≤ VR i q ω := (hp.2.2.2.2 q hω.2.1).2
    have hmean : (∫ z, couplingMean κ (fun x : ℝ => W x.toNNReal ω) q (phaseProc κ ρL ρR W VL VR c ω q) z *
        ψ z) = phaseInt κ ρL ρR (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω) q ψ (c ω) :=
      integral_couplingMean_phase (vL := fun i t => VL i t ω) (vR := fun i t => VR i t ω) hκ ψ.continuous
        ψ.hasCompactSupport hw hKH hω.2 hδ le_rfl hvL hvR
        (isBoundedHarmonicExtension_phaseProc hκ c (hvL 0) (hvR 0))
    have hA : mA ω = ∫ z, meanCan κ ρL ρR (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω) q z * ψ z := by
      simp only [hmA, meanK, hω, ↓reduceIte]
    have hB : mB ω = ∫ z, meanCan κ (shiftL κ ρL 1) (shiftR κ ρR 1) (W · ω) (fun i t => VL i t ω)
        (fun i t => VR i t ω) q z * ψ z := by
      simp only [hmB, meanK, hω, ↓reduceIte]
    have he : energyK W ζ G ψ δ q ω = loewnerGreenEnergy (rpath (W · ω)) q ψ := by
      simp only [energyK, hω, ↓reduceIte]
    rw [hA, hB, he]
    simp only [cfAt, hmean]
    rfl
  rw [e]
  refine Measurable.indicator ?_ ((𝓖.le q) _ (measurableSet_safeSet hWa hGc hG0 hKH hδ q))
  have h1 := (measurable_meanK hWa hGc hG0 hKH hδ κ ρL ρR hVLa hVRa ψ.continuous.measurable q).mono
    (𝓖.le q) le_rfl
  have h1' := (measurable_meanK hWa hGc hG0 hKH hδ κ (shiftL κ ρL 1) (shiftR κ ρR 1) hVLa hVRa
    ψ.continuous.measurable q).mono (𝓖.le q) le_rfl
  have h2 := (measurable_energyK hWa hGc hG0 hKH hδ ψ.continuous.measurable q).mono (𝓖.le q) le_rfl
  have h3 : Measurable fun ω => mA ω + c ω * (mB ω - mA ω) + c ω * (∫ z, ψ z) :=
    (h1.add (hcm.mul (h1'.sub h1))).add (hcm.mul_const _)
  exact Complex.measurable_exp.comp ((measurable_const.mul (Complex.measurable_ofReal.comp h3)).sub
    ((measurable_const.mul (Complex.measurable_ofReal.comp h2)).div_const 2))

/-- `cfAt q` of the phase word restricted to the safe union is almost everywhere strongly measurable
(`Aux79.aestronglyMeasurable_safeU_indicator_cfAt'`). -/
theorem aestronglyMeasurable_safeU_indicator_cfAt_phase {𝓖 : Filtration ℝ≥0 mΩ} (hκ : 0 < κ) {c : Ω → ℝ}
    (hcm : Measurable c) (ψ : LQGMetric.TestOn upperHalfPlaneOpens) {G : Set Ω}
    (hGp : ∀ ω ∈ G, IsForceReg W VL VR ζ ω) (hG0 : MeasurableSet[𝓖 0] G) (hWa : AdaptedBefore 𝓖 ζ W)
    (hVLa : ∀ i, AdaptedBefore 𝓖 ζ (VL i)) (hVRa : ∀ i, AdaptedBefore 𝓖 ζ (VR i)) (q : ℝ≥0) :
    AEStronglyMeasurable ((safeU W ζ G ψ q).indicator
      (cfAt κ W (phaseProc κ ρL ρR W VL VR c) ψ 1 fun _ => q)) P := by
  have hmK : ∀ m : ℕ, Measurable ((safeSet W ζ G ψ (1 / ((m : ℝ) + 1)) q).indicator
      (cfAt κ W (phaseProc κ ρL ρR W VL VR c) ψ 1 fun _ => q)) := fun m =>
    measurable_safeSet_indicator_cfAt_phase hκ hcm ψ hGp hG0 hWa hVLa hVRa (by positivity) q
  refine aestronglyMeasurable_of_tendsto_ae atTop (fun m => (hmK m).aestronglyMeasurable)
    (ae_of_all _ fun ω => ?_)
  by_cases hω : ω ∈ safeU W ζ G ψ q
  · obtain ⟨m₀, hm₀⟩ := mem_iUnion.1 hω
    rw [indicator_of_mem hω]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop m₀] with m hm
    have hle : 1 / ((m : ℝ) + 1) ≤ 1 / ((m₀ : ℝ) + 1) := by gcongr
    rw [indicator_of_mem (show ω ∈ safeSet W ζ G ψ (1 / ((m : ℝ) + 1)) q from
      ⟨hm₀.1, hm₀.2.mono hle le_rfl le_rfl⟩)]
  · rw [indicator_of_notMem hω]
    exact tendsto_const_nhds.congr fun m =>
      (indicator_of_notMem (fun h' => hω (mem_iUnion.2 ⟨m, h'⟩)) _).symm

/-- **Pointwise convergence of the discretized integrands for the phase word** (`Aux79.ae_tendsto_sum_piece'`). -/
theorem ae_tendsto_sum_piece_phase (hκ : 0 < κ) {c : Ω → ℝ} (ψ : LQGMetric.TestOn upperHalfPlaneOpens)
    {G : Set Ω} (hGp : ∀ ω ∈ G, IsForceReg W VL VR ζ ω) {τ : Ω → WithTop ℝ≥0} {A : Set Ω} (f : Ω → ℂ)
    (hAE : A ⊆ {ω | Disjoint (tsupport ψ) (fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0))})
    (hGae : ∀ᵐ ω ∂P, ω ∈ G) (hτζ : ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < ζ ω) :
    ∀ᵐ ω ∂P, Tendsto (fun n => ∑ k ∈ Finset.range (4 ^ n), (piece τ A W ζ G ψ n k).indicator f ω) atTop
        (𝓝 ((A ∩ {ω | τ ω ≠ ⊤}).indicator f ω)) ∧
      Tendsto (fun n => ∑ k ∈ Finset.range (4 ^ n),
          (piece τ A W ζ G ψ n k).indicator
            (cfAt κ W (phaseProc κ ρL ρR W VL VR c) ψ 1 fun _ => dyT n (k + 1)) ω) atTop
        (𝓝 ((A ∩ {ω | τ ω ≠ ⊤}).indicator
          (cfAt κ W (phaseProc κ ρL ρR W VL VR c) ψ 1 fun ω => (τ ω).untopD 0) ω)) := by
  have hlab : ∀ n k ω, ω ∈ piece τ A W ζ G ψ n k → ⌈2 ^ n * (τ ω).untopD 0⌉₊ = k := fun n k ω hω => hω.1.2.2
  filter_upwards [hGae, hτζ] with ω hωG hωζ
  by_cases hωA : ω ∈ A ∩ {ω | τ ω ≠ ⊤}
  · have hne : τ ω ≠ ⊤ := hωA.2
    set a : ℝ≥0 := (τ ω).untopD 0 with ha
    have haζ : (a : ℝ≥0∞) < ζ ω := coe_untopD_lt_zeta hωζ
    have hp := hGp ω hωG
    obtain ⟨m, hevs, htend⟩ := exists_eventually_isSafeAt_tendsto_cfAt_phase (u := phaseProc κ ρL ρR W VL VR c)
      hκ ψ (fun s hs => isBoundedHarmonicExtension_phaseProc hκ c ((hp.2.2.2.2 s hs).1 0)
        ((hp.2.2.2.2 s hs).2 0)) hp haζ (hAE hωA.1) (tendsto_dyT_ceil a)
    have hevC : ∀ᶠ n in atTop, ⌈2 ^ n * a⌉₊ ∈ Finset.range (4 ^ n) ∧
        ω ∈ piece τ A W ζ G ψ n ⌈2 ^ n * a⌉₊ := by
      filter_upwards [eventually_ceil_lt_four_pow a, hevs] with n hn hs
      exact ⟨Finset.mem_range.2 hn, ⟨⟨hωA.1, hne, rfl⟩, mem_safeU_of_isSafeAt hωG hs⟩⟩
    rw [indicator_of_mem hωA, indicator_of_mem hωA]
    refine ⟨tendsto_const_nhds.congr' (hevC.mono fun n hn => ?_), htend.congr' (hevC.mono fun n hn => ?_)⟩
    · beta_reduce
      rw [sum_indicator_eq_of_label (hlab n) ω]
      split_ifs with hc
      · exact (indicator_of_mem hn.2 _).symm
      · exact absurd hn.1 hc
    · beta_reduce
      rw [sum_indicator_eq_of_label (hlab n) ω]
      split_ifs with hc
      · exact (indicator_of_mem hn.2 _).symm
      · exact absurd hn.1 hc
  · have h0 : ∀ n k, ω ∉ piece τ A W ζ G ψ n k := fun n k hω => hωA ⟨hω.1.1, hω.1.2.1⟩
    rw [indicator_of_notMem hωA, indicator_of_notMem hωA]
    exact ⟨tendsto_const_nhds.congr fun n => (Finset.sum_eq_zero fun k _ => indicator_of_notMem (h0 n k) _).symm,
      tendsto_const_nhds.congr fun n => (Finset.sum_eq_zero fun k _ => indicator_of_notMem (h0 n k) _).symm⟩

/-! ### The phase law at positive fixed times and at stopping times -/

/-- **K2's (S) for the phase word at positive fixed times**: at every capacity time `q > 0`, on every event of `𝓗_q`
inside the avoidance event `{q < ζ, supp ψ ∩ K_q = ∅}`, `∫_D e^{i(X,ψ)} = ∫_D cfAt_q(ψ)` with the coupling mean of the
phase-`c` word (`phaseProc`). Time `0` is not required: the stopping-time bridge approximates from above by the times
`(k + 1)/2ⁿ`. -/
def HasPhaseSafeLaw (κ : ℝ) (ρL : Fin (nL + 1) → ℝ) (ρR : Fin (nR + 1) → ℝ) (P : Measure Ω)
    (𝓗 : Filtration ℝ≥0 mΩ) (ζ : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ) (VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ)
    (VR : Fin (nR + 1) → ℝ≥0 → Ω → ℝ) (c : Ω → ℝ) (X : Ω → LQGMetric.DistOn upperHalfPlaneOpens) : Prop :=
  ∀ (ψ : LQGMetric.TestOn upperHalfPlaneOpens) (q : ℝ≥0), 0 < q → ∀ D : Set Ω, MeasurableSet[𝓗 q] D →
    (∀ᵐ ω ∂P, ω ∈ D → ω ∈ avoidSet W ζ ψ q) →
    ∫ ω in D, Complex.exp (Complex.I * (X ω ψ : ℂ)) ∂P =
      ∫ ω in D, cfAt κ W (phaseProc κ ρL ρR W VL VR c) ψ 1 (fun _ => q) ω ∂P

/-- **The phase law at every stopping time from (S) at positive fixed times**
(`Aux79.setIntegral_cexp_eq_cfAt_of_hasSafeLaw` for the phase word; the dyadic identities are used only at the positive
times `(k + 1)/2ⁿ`). -/
theorem setIntegral_cexp_eq_cfAt_of_hasPhaseSafeLaw [IsProbabilityMeasure P] (hκ : 0 < κ)
    {𝓗 : Filtration ℝ≥0 mΩ} {c : Ω → ℝ} (hcm : Measurable c)
    (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens) (hh : ∀ ψ, Measurable fun ω => h ω ψ)
    (hlaw : HasPhaseSafeLaw κ ρL ρR P 𝓗 ζ W VL VR c h) (hpath : ∀ᵐ ω ∂P, IsForceReg W VL VR ζ ω)
    (hWa₀ : AdaptedBefore 𝓗 ζ W) (hVLa₀ : ∀ i, AdaptedBefore 𝓗 ζ (VL i))
    (hVRa₀ : ∀ i, AdaptedBefore 𝓗 ζ (VR i)) (ψ : LQGMetric.TestOn upperHalfPlaneOpens)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime (usualAugmentation 𝓗 P) τ)
    (hτζ : ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < ζ ω) {A : Set Ω} (hA : MeasurableSet[hτ.measurableSpace] A)
    (hAE : A ⊆ {ω | Disjoint (tsupport ψ) (fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0))}) :
    ∫ ω in A, Complex.exp (Complex.I * (h ω ψ : ℂ)) ∂P =
      ∫ ω in A, cfAt κ W (phaseProc κ ρL ρR W VL VR c) ψ 1 (fun ω => (τ ω).untopD 0) ω ∂P := by
  set u := phaseProc κ ρL ρR W VL VR c with hudef
  set 𝓐 := nullAugmented 𝓗 P with h𝓐
  set f : Ω → ℂ := fun ω => Complex.exp (Complex.I * (h ω ψ : ℂ)) with hf
  have hfm : Measurable f :=
    Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp (hh ψ)))
  have hfb : ∀ ω, ‖f ω‖ ≤ 1 := fun ω => (norm_cexp_I_mul_ofReal _).le
  have hfint : Integrable f P := Integrable.of_bound hfm.aestronglyMeasurable 1 (ae_of_all _ hfb)
  -- the good set
  obtain ⟨N, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 hpath)
  set G : Set Ω := Nᶜ with hGdef
  have hGp : ∀ ω ∈ G, IsForceReg W VL VR ζ ω := fun ω hω => by
    by_contra hc
    exact hω (hNsub hc)
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := by
    rw [ae_iff]
    simpa [hGdef] using hN0
  have hG0 : MeasurableSet[𝓐 0] G := (measurableSet_nullAugmented_of_null hNm hN0 0).compl
  have hWa : AdaptedBefore 𝓐 ζ W :=
    adaptedBefore_mono (le_nullAugmented 𝓗 P) hWa₀
  have hVLa : ∀ i, AdaptedBefore 𝓐 ζ (VL i) := fun i =>
    adaptedBefore_mono (le_nullAugmented 𝓗 P) (hVLa₀ i)
  have hVRa : ∀ i, AdaptedBefore 𝓐 ζ (VR i) := fun i =>
    adaptedBefore_mono (le_nullAugmented 𝓗 P) (hVRa₀ i)
  have hGc : ∀ ω ∈ G, ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω} := fun ω hω =>
    (hGp ω hω).2.1
  -- the pieces
  set C : ℕ → ℕ → Set Ω := fun n k => piece τ A W ζ G ψ n k with hC
  have hCm𝓐 : ∀ n k, MeasurableSet[𝓐 (dyT n (k + 1))] (C n k) := fun n k => by
    have h1 : MeasurableSet[𝓐 (dyT n (k + 1))]
        (A ∩ {ω | τ ω ≠ ⊤ ∧ ⌈2 ^ n * (τ ω).untopD 0⌉₊ = k}) :=
      usualAugmentation_le_nullAugmented (P := P) 𝓗 (dyT_lt_dyT_succ n k) _ (measurableSet_piece hτ hA n k)
    have h2 : MeasurableSet[𝓐 (dyT n (k + 1))] (safeU W ζ G ψ (dyT n (k + 1))) :=
      MeasurableSet.iUnion fun m => measurableSet_safeSet hWa hGc hG0 (tsupport_subset_H ψ) (by positivity) _
    exact h1.inter h2
  have hCm : ∀ n k, MeasurableSet (C n k) := fun n k => 𝓐.le _ _ (hCm𝓐 n k)
  have hcfint : ∀ n k, Integrable ((C n k).indicator (cfAt κ W u ψ 1 fun _ => dyT n (k + 1))) P := by
    intro n k
    have e : (C n k).indicator (cfAt κ W u ψ 1 fun _ => dyT n (k + 1)) =
        (C n k).indicator ((safeU W ζ G ψ (dyT n (k + 1))).indicator
          (cfAt κ W u ψ 1 fun _ => dyT n (k + 1))) := by
      rw [indicator_indicator, inter_eq_left.2 (fun ω hω => hω.2)]
    rw [e]
    refine Integrable.of_bound (((aestronglyMeasurable_safeU_indicator_cfAt_phase hκ hcm ψ hGp hG0 hWa hVLa hVRa
      _).indicator (hCm n k))) 1 (ae_of_all _ fun ω => ?_)
    by_cases hω : ω ∈ C n k
    · rw [indicator_of_mem hω, indicator_of_mem hω.2]
      exact norm_cfAt_le_one_of_mem_safeU' ψ hGp u hω.2
    · rw [indicator_of_notMem hω, norm_zero]; exact zero_le_one
  -- the dyadic identity, summed over the pieces at level `n`
  have hGF : ∀ n, ∫ ω, ∑ k ∈ Finset.range (4 ^ n), (C n k).indicator f ω ∂P =
      ∫ ω, ∑ k ∈ Finset.range (4 ^ n), (C n k).indicator (cfAt κ W u ψ 1 fun _ => dyT n (k + 1)) ω ∂P := by
    intro n
    rw [integral_finsetSum _ (fun k _ => hfint.indicator (hCm n k)),
      integral_finsetSum _ (fun k _ => hcfint n k)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_indicator (hCm n k), integral_indicator (hCm n k)]
    obtain ⟨C', hC'm, hCC'⟩ := exists_ae_eq_of_measurableSet_nullAugmented (hCm𝓐 n k)
    rw [setIntegral_congr_set hCC', setIntegral_congr_set hCC']
    refine hlaw ψ (dyT n (k + 1)) (lt_of_le_of_lt (zero_le (a := dyT n k)) (dyT_lt_dyT_succ n k)) C' hC'm ?_
    filter_upwards [hCC'] with ω hω hωC'
    have hωC : ω ∈ C n k := by
      have : (ω ∈ C n k) = (ω ∈ C') := hω
      rw [this]; exact hωC'
    exact safeU_subset_avoidSet' ψ hGp _ hωC.2
  -- bounds
  have hlab : ∀ n k ω, ω ∈ C n k → ⌈2 ^ n * (τ ω).untopD 0⌉₊ = k := fun n k ω hω => hω.1.2.2
  have hGb : ∀ n ω, ‖∑ k ∈ Finset.range (4 ^ n), (C n k).indicator f ω‖ ≤ 1 := fun n ω => by
    rw [sum_indicator_eq_of_label (hlab n) ω]
    split_ifs
    · by_cases hω : ω ∈ C n ⌈2 ^ n * (τ ω).untopD 0⌉₊
      · rw [indicator_of_mem hω]; exact hfb ω
      · rw [indicator_of_notMem hω, norm_zero]; exact zero_le_one
    · rw [norm_zero]; exact zero_le_one
  have hFb : ∀ n ω, ‖∑ k ∈ Finset.range (4 ^ n),
      (C n k).indicator (cfAt κ W u ψ 1 fun _ => dyT n (k + 1)) ω‖ ≤ 1 := fun n ω => by
    rw [sum_indicator_eq_of_label (hlab n) ω]
    split_ifs
    · by_cases hω : ω ∈ C n ⌈2 ^ n * (τ ω).untopD 0⌉₊
      · rw [indicator_of_mem hω]; exact norm_cfAt_le_one_of_mem_safeU' ψ hGp u hω.2
      · rw [indicator_of_notMem hω, norm_zero]; exact zero_le_one
    · rw [norm_zero]; exact zero_le_one
  -- dominated convergence
  have hpt := ae_tendsto_sum_piece_phase (P := P) (ρL := ρL) (ρR := ρR) (c := c) hκ ψ hGp f hAE hGae hτζ
  have hlimG := tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
    (fun n => (integrable_finsetSum _ (fun k _ => hfint.indicator (hCm n k))).aestronglyMeasurable)
    (integrable_const 1) (fun n => ae_of_all _ (hGb n)) (hpt.mono fun ω h => h.1)
  have hlimF := tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
    (fun n => (integrable_finsetSum _ (fun k _ => hcfint n k)).aestronglyMeasurable)
    (integrable_const 1) (fun n => ae_of_all _ (hFb n)) (hpt.mono fun ω h => h.2)
  have heq := tendsto_nhds_unique (hlimG.congr hGF) hlimF
  have hA'm : MeasurableSet (A ∩ {ω | τ ω ≠ ⊤}) :=
    (hτ.measurableSpace_le _ hA).inter (measurableSet_eq_top_of_isStoppingTime hτ).compl
  rw [integral_indicator hA'm, integral_indicator hA'm] at heq
  have hAA' : A =ᵐ[P] (A ∩ {ω | τ ω ≠ ⊤} : Set Ω) := by
    filter_upwards [hτζ] with ω hω
    exact propext ⟨fun h => ⟨h, ne_top_of_lt_zeta hω⟩, fun h => h.1⟩
  rw [setIntegral_congr_set hAA', setIntegral_congr_set hAA']
  exact heq

/-- **Measurability at a stopping time of the usual augmentation, for the phase word**
(`Aux79.exists_stopped_measurable` for the phase word): the frozen right-hand side at `τ` with any extension `u` of
the phase-`c` word is measurable for `𝓖_τ` on an event `E'` of `𝓖_τ` that is almost surely the avoidance event. The
stopped tested mean is `𝔥_A + c (𝔥_B − 𝔥_A) + c ∫ψ` (`integral_couplingMean_phase`), with the stopped pairs of the two
fixed words (`Coupling.measurable_stoppedPair`) and the phase, measurable at time `0`. -/
theorem exists_stopped_measurable_phase [IsProbabilityMeasure P] (hκ : 0 < κ) {𝓗 : Filtration ℝ≥0 mΩ}
    {c : Ω → ℝ} (hcm : Measurable[usualAugmentation 𝓗 P 0] c)
    (hpath : ∀ᵐ ω ∂P, IsForceReg W VL VR ζ ω) (hWa₀ : AdaptedBefore 𝓗 ζ W)
    (hVLa₀ : ∀ i, AdaptedBefore 𝓗 ζ (VL i)) (hVRa₀ : ∀ i, AdaptedBefore 𝓗 ζ (VR i))
    (ψ : LQGMetric.TestOn upperHalfPlaneOpens)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime (usualAugmentation 𝓗 P) τ)
    (hτζ : ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < ζ ω) (u : Ω → ℂ → ℝ)
    (hu : ∀ ω, IsBoundedHarmonicExtension
      (phaseData κ ρL ρR (fun i => VL i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)
        (fun i => VR i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω) (c ω))
      (forceJumpSet (fun i => VL i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)
        (fun i => VR i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)) (u ω)) :
    ∃ E' : Set Ω, MeasurableSet[hτ.measurableSpace] E' ∧
      E' ⊆ {ω | Disjoint (tsupport ψ)
        (fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0))} ∧
      (∀ᵐ ω ∂P, Disjoint (tsupport ψ)
        (fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)) → ω ∈ E') ∧
      (∀ ω ∈ E', ∀ v : ℂ → ℝ, IsBoundedHarmonicExtension
        (phaseData κ ρL ρR (fun i => VL i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)
          (fun i => VR i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω) (c ω))
        (forceJumpSet (fun i => VL i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)
          (fun i => VR i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)) v →
        ∫ z, couplingMean κ (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0) v z * ψ z =
          ∫ z, couplingMean κ (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0) (u ω) z * ψ z) ∧
      (∀ ω ∈ E', ContinuousOn (rpath (W · ω)) (Icc 0 (((τ ω).untopD 0 : ℝ≥0) : ℝ)) ∧ W 0 ω = 0 ∧
        ∀ z ∈ tsupport ψ, ∃ v, IsForwardSol (rpath (W · ω)) z (((τ ω).untopD 0 : ℝ≥0) : ℝ) v) ∧
      (∀ ω ∈ E', IsForceReg W VL VR ζ ω ∧ (((τ ω).untopD 0 : ℝ≥0) : ℝ≥0∞) < ζ ω) ∧
      StronglyMeasurable[hτ.measurableSpace]
        (E'.indicator (frozenRHS κ W u ψ fun ω => (τ ω).untopD 0)) := by
  set 𝓓 := usualAugmentation 𝓗 P with h𝓓
  set τ' : Ω → ℝ≥0 := fun ω => (τ ω).untopD 0 with hτ'def
  have hτf : ∀ᵐ ω ∂P, τ ω ≠ ⊤ := hτζ.mono fun _ h => ne_top_of_lt_zeta h
  have hτ' : IsStoppingTime 𝓓 fun ω => (τ' ω : WithTop ℝ≥0) := isStoppingTime_untopD (𝓕 := 𝓗) hτ hτf
  have hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[𝓓 0] s := fun s hs h0 =>
    measurableSet_usualAugmentation_of_null (𝓕 := 𝓗) hs h0 0
  have hσeq : hτ.measurableSpace = hτ'.measurableSpace := measurableSpace_untopD_eq hnull hτ hτf hτ'
  have hWa : AdaptedBefore 𝓓 ζ W :=
    adaptedBefore_mono (le_usualAugmentation 𝓗 P) hWa₀
  have hVLa : ∀ i, AdaptedBefore 𝓓 ζ (VL i) := fun i =>
    adaptedBefore_mono (le_usualAugmentation 𝓗 P) (hVLa₀ i)
  have hVRa : ∀ i, AdaptedBefore 𝓓 ζ (VR i) := fun i =>
    adaptedBefore_mono (le_usualAugmentation 𝓗 P) (hVRa₀ i)
  have hpath' : ∀ᵐ ω ∂P, ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω} ∧ W 0 ω = 0 := by
    filter_upwards [hpath] with ω hP using ⟨hP.2.1, hP.1⟩
  -- the support of `ψ`
  set K : Set ℂ := tsupport ψ with hKdef
  have hKH : K ⊆ H := tsupport_subset_H ψ
  have hK : IsCompact K := ψ.hasCompactSupport.isCompact
  obtain ⟨m, hm, hKm⟩ := exists_pos_le_im_of_isCompact hK hKH
  -- the truncations `τ ∧ n` and the safe stops below them
  set σ₀ : ℕ → Ω → ℝ≥0 := fun n ω => min (τ' ω) n with hσ₀_def
  have hσ₀ : ∀ n : ℕ, IsStoppingTime 𝓓 fun ω => (σ₀ n ω : WithTop ℝ≥0) := fun n => by
    have h := hτ'.min_const (n : ℝ≥0)
    convert h using 2 with ω
    simp only [hσ₀_def, WithTop.coe_min]
  have hσ₀m : ∀ ω, Monotone fun n => σ₀ n ω := fun ω n n' h =>
    min_le_min le_rfl (by exact_mod_cast h)
  have hσ₀ζ : ∀ n, ∀ᵐ ω ∂P, (σ₀ n ω : ℝ≥0∞) < ζ ω := fun n => by
    filter_upwards [hτζ] with ω h
    exact lt_of_le_of_lt (by exact_mod_cast min_le_left _ _) (coe_untopD_lt_zeta h)
  obtain ⟨ρ, hρst, hρle, hρmono, hρsafe, hρex⟩ := exists_safeSeq_of_adapted (𝓗 := 𝓗) (P := P)
    hWa₀ hpath' hK hKH hm hKm hσ₀ hσ₀m hσ₀ζ
  -- the good event
  set good : Ω → Prop := fun ω => IsForceReg W VL VR ζ ω ∧
    ((τ' ω : ℝ≥0∞) < ζ ω) ∧
    (∀ n : ℕ, IsSafeAt K (m / ((n : ℝ) + 1)) n (σ₀ n ω) (ζ ω) (W · ω) (ρ n ω)) ∧
    ∀ (j : ℕ) (t : ℝ≥0), t ≤ σ₀ j ω →
      (∀ z ∈ K, ∃ u, IsForwardSol (rpath (W · ω)) z t u) → ∀ᶠ n in atTop, t ≤ ρ n ω with hgood
  have hae : ∀ᵐ ω ∂P, good ω := by
    filter_upwards [hpath, hτζ, ae_all_iff.2 hρsafe, hρex] with ω h1 h2 h3 h4
    exact ⟨h1, coe_untopD_lt_zeta h2, h3, h4⟩
  obtain ⟨G, hGm, hGc, hGgood⟩ : ∃ G : Set Ω, MeasurableSet G ∧ P Gᶜ = 0 ∧ ∀ ω ∈ G, good ω := by
    refine ⟨(toMeasurable P {ω | ¬ good ω})ᶜ, (measurableSet_toMeasurable _ _).compl, ?_,
      fun ω hω => ?_⟩
    · rw [compl_compl, measure_toMeasurable]; exact ae_iff.1 hae
    · by_contra h; exact hω (subset_toMeasurable _ _ h)
  have hG0 : MeasurableSet[𝓓 0] G := by
    have := (hnull _ hGm.compl hGc).compl
    rwa [compl_compl] at this
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := by rw [ae_iff]; exact hGc
  have hGw : ∀ ω ∈ G, ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω} := fun ω hω =>
    (hGgood ω hω).1.2.1
  have hGv : ∀ ω ∈ G, (∀ i, ContinuousOn (fun t => VL i t ω) {t | (t : ℝ≥0∞) < ζ ω}) ∧
      ∀ i, ContinuousOn (fun t => VR i t ω) {t | (t : ℝ≥0∞) < ζ ω} := fun ω hω =>
    ⟨(hGgood ω hω).1.2.2.1, (hGgood ω hω).1.2.2.2.1⟩
  have hδ : ∀ n : ℕ, 0 < m / ((n : ℝ) + 1) := fun n => by positivity
  have hψc : Continuous (ψ : ℂ → ℝ) := ψ.continuous
  -- the stopped pairs of the two fixed words, and the phase
  have hYA : ∀ n : ℕ, Measurable[(hρst n).measurableSpace] fun ω => if ω ∈ G then
      ((∫ z, meanCan κ ρL ρR (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω) (ρ n ω) z * ψ z),
        loewnerGreenEnergy (rpath (W · ω)) (ρ n ω) ψ) else ((0 : ℝ), (0 : ℝ)) := fun n =>
    measurable_stoppedPair hWa hVLa hVRa hGw hGv hG0 hψc ψ.hasCompactSupport hKH (hδ n) (hρst n)
      fun ω hω => (hGgood ω hω).2.2.1 n
  have hYB : ∀ n : ℕ, Measurable[(hρst n).measurableSpace] fun ω => if ω ∈ G then
      ((∫ z, meanCan κ (shiftL κ ρL 1) (shiftR κ ρR 1) (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω)
          (ρ n ω) z * ψ z),
        loewnerGreenEnergy (rpath (W · ω)) (ρ n ω) ψ) else ((0 : ℝ), (0 : ℝ)) := fun n =>
    measurable_stoppedPair hWa hVLa hVRa hGw hGv hG0 hψc ψ.hasCompactSupport hKH (hδ n) (hρst n)
      fun ω hω => (hGgood ω hω).2.2.1 n
  have hcρ : ∀ n, Measurable[(hρst n).measurableSpace] c := fun n => by
    have h0 := IsStoppingTime.measurableSpace_mono (isStoppingTime_const 𝓓 (0 : ℝ≥0)) (hρst n)
      (fun ω => WithTop.coe_le_coe.2 (zero_le (a := ρ n ω)))
    rw [IsStoppingTime.measurableSpace_const] at h0
    exact hcm.mono h0 le_rfl
  set Y : ℕ → Ω → ℝ × ℝ := fun n ω =>
    ((if ω ∈ G then
        ((∫ z, meanCan κ ρL ρR (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω) (ρ n ω) z * ψ z),
          loewnerGreenEnergy (rpath (W · ω)) (ρ n ω) ψ) else ((0 : ℝ), (0 : ℝ))).1 +
      c ω * ((if ω ∈ G then
        ((∫ z, meanCan κ (shiftL κ ρL 1) (shiftR κ ρR 1) (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω)
            (ρ n ω) z * ψ z),
          loewnerGreenEnergy (rpath (W · ω)) (ρ n ω) ψ) else ((0 : ℝ), (0 : ℝ))).1 -
        (if ω ∈ G then
          ((∫ z, meanCan κ ρL ρR (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω) (ρ n ω) z * ψ z),
            loewnerGreenEnergy (rpath (W · ω)) (ρ n ω) ψ) else ((0 : ℝ), (0 : ℝ))).1) +
      c ω * (∫ z, ψ z),
    (if ω ∈ G then
        ((∫ z, meanCan κ ρL ρR (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω) (ρ n ω) z * ψ z),
          loewnerGreenEnergy (rpath (W · ω)) (ρ n ω) ψ) else ((0 : ℝ), (0 : ℝ))).2) with hYdef
  have hY : ∀ n, Measurable[(hρst n).measurableSpace] (Y n) := fun n =>
    ((((hYA n).fst.add ((hcρ n).mul ((hYB n).fst.sub (hYA n).fst))).add ((hcρ n).mul_const _)).prodMk
      (hYA n).snd)
  have hle : ∀ n, (hρst n).measurableSpace ≤ hτ'.measurableSpace := fun n =>
    IsStoppingTime.measurableSpace_mono (hρst n) hτ' fun ω =>
      WithTop.coe_le_coe.2 ((hρle n ω).trans (min_le_left _ _))
  -- the events `F n = G ∩ {ρ_n = τ}`
  set F : ℕ → Set Ω := fun n => G ∩ {ω | ρ n ω = τ' ω} with hFdef
  have hGτ : MeasurableSet[hτ'.measurableSpace] G := by
    have h0 := IsStoppingTime.measurableSpace_mono (isStoppingTime_const 𝓓 (0 : ℝ≥0)) hτ'
      (fun ω => WithTop.coe_le_coe.2 (zero_le (a := τ' ω)))
    rw [IsStoppingTime.measurableSpace_const] at h0
    exact h0 _ hG0
  have hF : ∀ n, MeasurableSet[hτ'.measurableSpace] (F n) := fun n => by
    have h := IsStoppingTime.measurableSet_eq_stopping_time hτ' (hρst n)
    have e : {ω | ρ n ω = τ' ω} = {ω | (τ' ω : WithTop ℝ≥0) = (ρ n ω : WithTop ℝ≥0)} := by
      ext ω; simp only [mem_ofPred_eq, WithTop.coe_inj, eq_comm]
    rw [hFdef]; simp only
    rw [e]
    exact hGτ.inter h
  have hFmono : ∀ ω n n', n ≤ n' → ω ∈ F n → ω ∈ F n' := fun ω n n' hnn' ⟨hω, heq⟩ =>
    ⟨hω, le_antisymm ((hρle n' ω).trans (min_le_left _ _)) (heq ▸ hρmono ω hnn')⟩
  -- on `F n`, the support is safe at `τ`
  have hsafeτ : ∀ n, ∀ ω ∈ F n,
      IsSafeAt K (m / ((n : ℝ) + 1)) n (σ₀ n ω) (ζ ω) (W · ω) (τ' ω) := fun n ω ⟨hω, heq⟩ => by
    have := (hGgood ω hω).2.2.1 n
    rwa [heq] at this
  have hmeanEq : ∀ n, ∀ ω ∈ F n, ∀ v : ℂ → ℝ, IsBoundedHarmonicExtension
      (phaseData κ ρL ρR (fun i => VL i (τ' ω) ω - W (τ' ω) ω) (fun i => VR i (τ' ω) ω - W (τ' ω) ω) (c ω))
      (forceJumpSet (fun i => VL i (τ' ω) ω - W (τ' ω) ω) (fun i => VR i (τ' ω) ω - W (τ' ω) ω)) v →
      ∫ z, couplingMean κ (fun s : ℝ => W s.toNNReal ω) (τ' ω : ℝ≥0) v z * ψ z =
        phaseInt κ ρL ρR (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω) (τ' ω) ψ (c ω) :=
    fun n ω hωF v hv => by
      have hω := hωF.1
      have hP := (hGgood ω hω).1
      have hτζω := (hGgood ω hω).2.1
      have h1 : ∀ i, VL i (τ' ω) ω ≤ W (τ' ω) ω := fun i => (hP.2.2.2.2 (τ' ω) hτζω).1 i
      have h2 : ∀ i, W (τ' ω) ω ≤ VR i (τ' ω) ω := fun i => (hP.2.2.2.2 (τ' ω) hτζω).2 i
      exact integral_couplingMean_phase (vL := fun i t => VL i t ω) (vR := fun i t => VR i t ω) hκ hψc
        ψ.hasCompactSupport (hGw ω hω) hKH (hsafeτ n ω hωF) (hδ n) le_rfl h1 h2 hv
  refine ⟨⋃ n, F n, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hσeq]; exact MeasurableSet.iUnion hF
  · -- inside the avoidance event
    rintro ω ⟨_, ⟨n, rfl⟩, hωF⟩
    have hs := hsafeτ n ω hωF
    have hw := hGw ω hωF.1
    refine Set.disjoint_left.2 fun z hz hzK => ?_
    exact notMem_fwdHull_of_alive hw hs.1 (hKH hz) (hs.2.2.2 z hz).1 hzK
  · -- almost surely equal to it
    filter_upwards [hGae] with ω hω hdis
    obtain ⟨hP, hτζω, -, hexh⟩ := hGgood ω hω
    have halive : ∀ z ∈ K, ∃ u, IsForwardSol (rpath (W · ω)) z (τ' ω) u := fun z hz =>
      exists_isForwardSol_of_mem (τ' ω).coe_nonneg ⟨hKH hz, Set.disjoint_left.1 hdis hz⟩
    obtain ⟨j, hj⟩ : ∃ j : ℕ, τ' ω ≤ (j : ℝ≥0) := by
      obtain ⟨j, hj⟩ := exists_nat_ge (τ' ω); exact ⟨j, hj⟩
    have hτj : τ' ω ≤ σ₀ j ω := le_min le_rfl hj
    obtain ⟨n, hn⟩ := (hexh j (τ' ω) hτj halive).exists
    exact mem_iUnion.2 ⟨n, hω, le_antisymm ((hρle n ω).trans (min_le_left _ _)) hn⟩
  · -- the mean does not depend on the bounded harmonic extension
    rintro ω ⟨_, ⟨n, rfl⟩, hωF⟩ v hv
    rw [hmeanEq n ω hωF v hv, hmeanEq n ω hωF (u ω) (hu ω)]
  · -- path facts
    rintro ω ⟨_, ⟨n, rfl⟩, hωF⟩
    have hs := hsafeτ n ω hωF
    exact ⟨continuousOn_rpath (hGw ω hωF.1) hs.1, (hGgood ω hωF.1).1.1,
      fun z hz => (hs.2.2.2 z hz).1⟩
  · -- regularity
    rintro ω ⟨_, ⟨n, rfl⟩, hωF⟩
    exact ⟨(hGgood ω hωF.1).1, (hGgood ω hωF.1).2.1⟩
  · -- measurability, as a limit of the values at the safe stops
    rw [hσeq]
    set Z : ℕ → Ω → ℂ := fun n => (F n).indicator fun ω => cfPair (Y n ω) with hZ
    have hZm : ∀ n, StronglyMeasurable[hτ'.measurableSpace] (Z n) := fun n =>
      (((continuous_cfPair.measurable.comp (hY n)).mono (hle n) le_rfl).stronglyMeasurable).indicator
        (hF n)
    refine stronglyMeasurable_of_tendsto (m := hτ'.measurableSpace) atTop hZm
      (tendsto_pi_nhds.2 fun ω => ?_)
    by_cases hω : ω ∈ ⋃ n, F n
    · obtain ⟨n₀, hn₀⟩ := mem_iUnion.1 hω
      rw [indicator_of_mem hω]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop n₀] with n hn
      have hωF := hFmono ω n₀ n hn hn₀
      have hωG : ω ∈ G := hωF.1
      simp only [hZ, hYdef, indicator_of_mem hωF, hωG, ↓reduceIte, frozenRHS, cfPair]
      rw [hmeanEq n ω hωF (u ω) (hu ω), hωF.2]
      rfl
    · rw [indicator_of_notMem hω]
      have : ∀ n, Z n ω = 0 := fun n => indicator_of_notMem (fun h => hω (mem_iUnion.2 ⟨n, h⟩)) _
      simp only [this]
      exact tendsto_const_nhds

/-- **The phase conditional-law clause at every stopping time from (S) of the phase word at positive fixed times**
(`Aux79.isCouplingCharFun_of_hasSafeLaw` for the phase word): if the continuation is adapted before `ζ` to `𝓗` and
almost surely regular (`IsForceReg`), the phase `c` is measurable at time `0` of the usual augmentation of `𝓗`, and the
field satisfies `HasPhaseSafeLaw` for `𝓗`, then `PhaseMart.IsPhaseCouplingCharFun` holds for the usual augmentation
with the constant phase `c`. -/
theorem isPhaseCouplingCharFun_of_hasPhaseSafeLaw [IsProbabilityMeasure P] (hκ : 0 < κ)
    {𝓗 : Filtration ℝ≥0 mΩ} {c : Ω → ℝ} (hcm : Measurable[usualAugmentation 𝓗 P 0] c)
    (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens) (hh : ∀ ψ, Measurable fun ω => h ω ψ)
    (hlaw : HasPhaseSafeLaw κ ρL ρR P 𝓗 ζ W VL VR c h) (hpath : ∀ᵐ ω ∂P, IsForceReg W VL VR ζ ω)
    (hWa₀ : AdaptedBefore 𝓗 ζ W) (hVLa₀ : ∀ i, AdaptedBefore 𝓗 ζ (VL i))
    (hVRa₀ : ∀ i, AdaptedBefore 𝓗 ζ (VR i)) :
    IsPhaseCouplingCharFun κ ρL ρR P (usualAugmentation 𝓗 P) W VL VR (fun _ ω => c ω) ζ h := by
  intro τ hτ hτζ uτ huτ φ
  set u := phaseProc κ ρL ρR W VL VR c with hudef
  set τ' : Ω → ℝ≥0 := fun ω => (τ ω).untopD 0 with hτ'def
  have hcm' : Measurable c := hcm.mono ((usualAugmentation 𝓗 P).le 0) le_rfl
  obtain ⟨E', hE'm, hE'sub, hE'ae, hE'mean, hE'path, hE'reg, hE'sm⟩ :=
    exists_stopped_measurable_phase hκ hcm hpath hWa₀ hVLa₀ hVRa₀ φ hτ hτζ uτ huτ
  set f : Ω → ℂ := fun ω => Complex.exp (Complex.I * (h ω φ : ℂ)) with hf
  have hfm : Measurable f :=
    Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp (hh φ)))
  have hfint : Integrable f P :=
    Integrable.of_bound hfm.aestronglyMeasurable 1
      (ae_of_all _ fun ω => (norm_cexp_I_mul_ofReal _).le)
  set g : Ω → ℂ := E'.indicator (frozenRHS κ W uτ φ τ') with hg
  have hcf : ∀ ω ∈ E', frozenRHS κ W uτ φ τ' ω = cfAt κ W u φ 1 τ' ω := fun ω hω => by
    have hreg := hE'reg ω hω
    simp only [frozenRHS, cfAt]
    rw [← hE'mean ω hω (u ω (τ' ω)) (isBoundedHarmonicExtension_phaseProc hκ c
      ((hreg.1.2.2.2.2 _ hreg.2).1 0) ((hreg.1.2.2.2.2 _ hreg.2).2 0))]
    congr 1
    push_cast
    ring
  have hgb : ∀ ω, ‖g ω‖ ≤ 1 := fun ω => by
    by_cases hω : ω ∈ E'
    · rw [hg, indicator_of_mem hω, hcf ω hω]
      obtain ⟨h1, h2, h3⟩ := hE'path ω hω
      exact norm_cfAt_le_one u 1 φ (r := τ') h1 h2 h3
    · rw [hg, indicator_of_notMem hω, norm_zero]; exact zero_le_one
  have hgm : StronglyMeasurable[hτ.measurableSpace] g := hE'sm
  have hgint : Integrable g P :=
    Integrable.of_bound ((hgm.mono hτ.measurableSpace_le).aestronglyMeasurable) 1 (ae_of_all _ hgb)
  have hE'mΩ : MeasurableSet E' := hτ.measurableSpace_le _ hE'm
  have key : g =ᵐ[P] condExp hτ.measurableSpace P (E'.indicator f) := by
    refine ae_eq_condExp_of_forall_setIntegral_eq hτ.measurableSpace_le
      (hfint.indicator hE'mΩ) (fun A _ _ => hgint.integrableOn) (fun A hA _ => ?_)
      hgm.aestronglyMeasurable
    have hAm : MeasurableSet A := hτ.measurableSpace_le _ hA
    rw [hg, setIntegral_indicator hE'mΩ, setIntegral_indicator hE'mΩ]
    have hAE : MeasurableSet[hτ.measurableSpace] (A ∩ E') :=
      @MeasurableSet.inter Ω hτ.measurableSpace _ _ hA hE'm
    have hdy' := setIntegral_cexp_eq_cfAt_of_hasPhaseSafeLaw hκ hcm' h hh hlaw hpath hWa₀ hVLa₀ hVRa₀ φ hτ hτζ
      hAE (inter_subset_right.trans hE'sub)
    rw [hdy']
    refine setIntegral_congr_fun (hAm.inter hE'mΩ) fun ω hω => ?_
    exact hcf ω hω.2
  have hind := condExp_indicator (m := hτ.measurableSpace) (μ := P) hfint hE'm
  filter_upwards [key, hind, hE'ae] with ω h1 h2 h3 hdis
  have hω : ω ∈ E' := h3 hdis
  have e1 : condExp hτ.measurableSpace P f ω =
      E'.indicator (condExp hτ.measurableSpace P f) ω := (indicator_of_mem hω _).symm
  rw [e1, ← h2, ← h1, hg, indicator_of_mem hω]
  rfl

end Proc

end InteractingSLE.Sec7.PhaseClause
