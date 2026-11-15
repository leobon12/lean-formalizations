/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma71MData

/-!
# Lemma 7.1, the prime-end premise P: the explicit chart of the active pocket component

Packet PROVE-LEMMA71M. The prime-end premise `Lemma71L.PocketPrimeEnd` asks, on the chart domain
`D = ψ⁻¹(ℍ ∖ K_t)` of the active component, for harmonic representatives of the three local-set means, a chart
`(f, φ_D, G, L)` of `D` (Aux. lemma 28: `f` from the disc, `φ_D` onto `ℍ`, `G` bounded harmonic, `L` a continuous
argument of `φ_D′`), the prime-end alternative at all but finitely many prime ends, and the pairing identity
`∫ (G ∘ φ_D − χ L) φ = M`. This file constructs the chart explicitly (PROVE-LEMMA71L's "intended witnesses") and
reduces P, for every `ω`, to the **side limits in the half-plane coordinate** (`PocketSideLimit`):

* `pocketFwd c w t = f_t ∘ ψ` (the centred Loewner map at `t` after the pocket chart), `pocketDom c w t = ψ⁻¹(ℍ ∖ K_t)`,
  `pocketInv c w t` its inverse (`Function.invFunOn`), `pocketLift c w t = arg f_t′ ∘ ψ + lift` and `pocketG` the
  explicit harmonic function of the two seed weights (`meanHarmonic`) minus `a'`;
* `isConformalBijection_pocketFwd`, `pocketInv_spec`, `isConformalBijection_pocketDisc`, `continuousOn_pocketLift`,
  `deriv_pocketFwd`: the chart clauses (through `Chart.loewner` of the clamped driver);
* `pocketG_pocketFwd_sub`: the pairing identity, pointwise;
* `PocketSideLimit`: at every real `x` outside a finite set, the inverse chart has a limit `p` at `x` from `ℍ`, and
  either `p ∈ A ∪ ℝ`, the full union is `A` near `p` and `vL + F − (G − χ L ∘ ψ_t⁻¹) → 0` at `x`, or `p ∈ A_T ∪ ℝ`, `A`
  is inside the outer union near `p` and `vT + F − (G − χ L ∘ ψ_t⁻¹) → 0` at `x` (the Cayley transform carries
  prime ends of the disc other than `1` to real points);
* **`pocketPrimeEnd_of_sideLimit`**: `PocketSideLimit` (with harmonic representatives) gives `PocketPrimeEnd` on
  `pocketDom` with the chart mean as its value.

Conditional helpers; they replace no source theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric Complex
open LQGMetric (DistOn TestOn)
open SupercriticalConformalCovariance (IsConformalBijection)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec7.Lemma71M

open QuantumZipper (H fwdHull fwdMap fwdMapInv logDerivFwd)
open Ito Coupling Lemma71C Lemma71D

/-! ### The chart of the active component -/

section Chart

variable {nL nR : ℕ}

/-- The chart `φ_D = f_t ∘ ψ` of the active component (centred Loewner map at `t` after the pocket chart). -/
def pocketFwd (c : Chart) (w : ℝ≥0 → ℝ) (t : ℝ≥0) (z : ℂ) : ℂ := fwdMap (rpath w) t (c.1 z)

/-- The active component `D = ψ⁻¹(ℍ ∖ K_t)`. -/
def pocketDom (c : Chart) (w : ℝ≥0 → ℝ) (t : ℝ≥0) : Set ℂ := c.2.1 '' (H \ fwdHull (rpath w) t)

/-- The inverse chart `ℍ → D`. -/
def pocketInv (c : Chart) (w : ℝ≥0 → ℝ) (t : ℝ≥0) : ℂ → ℂ := Function.invFunOn (pocketFwd c w t) (pocketDom c w t)

/-- The argument of `φ_D′`: `arg f_t′ ∘ ψ + lift`. -/
def pocketLift (c : Chart) (w : ℝ≥0 → ℝ) (t : ℝ≥0) (z : ℂ) : ℝ := (logDerivFwd (rpath w) t (c.1 z)).im + c.2.2 z

/-- The bounded harmonic function of the two seed weights on `ℍ`, minus `a'`. -/
def pocketG (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (w : ℝ≥0 → ℝ) (vL : Fin nL → ℝ≥0 → ℝ)
    (vR : Fin nR → ℝ≥0 → ℝ) (t : ℝ≥0) (a' : ℝ) (y : ℂ) : ℝ :=
  meanHarmonic κ ρL ρR (fun i => vL i t - w t) (fun i => vR i t - w t) y - a'

variable {c : Chart} {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {t : ℝ≥0}

/-- A continuous driver agreeing with `rpath w` up to time `t` (the clamped driver beyond `t`). -/
theorem exists_clamp (hw : ContinuousOn w {s | (s : ℝ≥0∞) < ζ}) (hw0 : w 0 = 0) (ht : (t : ℝ≥0∞) < ζ) :
    ∃ W : ℝ → ℝ, Continuous W ∧ W 0 = 0 ∧ (∀ z, fwdMap W t z = fwdMap (rpath w) t z) ∧
      (∀ z, logDerivFwd W t z = logDerivFwd (rpath w) t z) ∧ fwdHull W t = fwdHull (rpath w) t := by
  obtain ⟨t₂, htt₂, ht₂ζ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ht
  have htt₂' : (t : ℝ) < t₂ := by exact_mod_cast htt₂
  refine ⟨clampDrv (rpath w) t₂, continuous_clampDrv t₂.coe_nonneg (continuousOn_rpath hw ht₂ζ), ?_,
    fun z => fwdMap_clampDrv_of_le htt₂'.le, fun z => logDerivFwd_clampDrv_of_le t.coe_nonneg htt₂'.le, ?_⟩
  · rw [clampDrv_eqOn (W := rpath w) ⟨le_rfl, t₂.coe_nonneg⟩]
    show w (0 : ℝ).toNNReal = 0
    rw [Real.toNNReal_zero, hw0]
  · exact InteractingSLE.fwdHull_eq_of_eqOn t.coe_nonneg htt₂' fun r hr => clampDrv_eqOn (W := rpath w) hr

/-- The pocket chart, through `Chart.loewner` of a clamped driver: a conformal chart whose forward map is
`pocketFwd` and whose domain is `pocketDom`. -/
theorem exists_loewnerChart (hc : c.IsConformal) (hw : ContinuousOn w {s | (s : ℝ≥0∞) < ζ}) (hw0 : w 0 = 0)
    (ht : (t : ℝ≥0∞) < ζ) :
    ∃ W : ℝ → ℝ, Continuous W ∧ W 0 = 0 ∧ (c.loewner W t).IsConformal ∧
      (c.loewner W t).1 = pocketFwd c w t ∧ ((c.loewner W t).dom : Set ℂ) = pocketDom c w t ∧
      (∀ z, logDerivFwd W t z = logDerivFwd (rpath w) t z) ∧ fwdHull W t = fwdHull (rpath w) t := by
  obtain ⟨W, hW, hW0, hf, hL, hK⟩ := exists_clamp hw hw0 ht
  have hc' := hc.loewner hW hW0 t.coe_nonneg
  refine ⟨W, hW, hW0, hc', funext fun z => hf (c.1 z), ?_, hL, hK⟩
  rw [hc'.coe_dom]
  show (fun z => c.2.1 (fwdMapInv W t z)) '' H = c.2.1 '' (H \ fwdHull (rpath w) t)
  rw [← image_image c.2.1 (fwdMapInv W t), QuantumZipper.RS.image_fwdMapInv_H hW hW0 t.coe_nonneg, hK]

theorem pocketDom_subset_dom (hc : c.IsConformal) : pocketDom c w t ⊆ c.dom := by
  rintro _ ⟨y, hy, rfl⟩
  exact hc.inv_mem_dom hy.1

theorem fwd_mem_of_mem_pocketDom (hc : c.IsConformal) {z : ℂ} (hz : z ∈ pocketDom c w t) :
    c.1 z ∈ H \ fwdHull (rpath w) t := by
  obtain ⟨y, hy, rfl⟩ := hz
  rw [hc.2.2 y hy.1]
  exact hy

/-- **`φ_D` is a conformal bijection of `D` onto `ℍ`.** -/
theorem isConformalBijection_pocketFwd (hc : c.IsConformal) (hw : ContinuousOn w {s | (s : ℝ≥0∞) < ζ})
    (hw0 : w 0 = 0) (ht : (t : ℝ≥0∞) < ζ) :
    IsConformalBijection (pocketFwd c w t) (pocketDom c w t) {y : ℂ | 0 < y.im} := by
  obtain ⟨W, -, -, hc', h1, hdom, -⟩ := exists_loewnerChart hc hw hw0 ht
  rw [← h1, ← hdom]
  refine ⟨hc'.differentiableOn_fwd, fun z hz => hc'.fwd_mem hz, fun z₁ hz₁ z₂ hz₂ h => ?_, fun y hy => ?_⟩
  · rw [← hc'.inv_fwd hz₁, ← hc'.inv_fwd hz₂, h]
  · exact ⟨(c.loewner W t).2.1 y, hc'.inv_mem_dom hy, hc'.2.2 y hy⟩

/-- **The inverse chart**: for `y ∈ ℍ`, `pocketInv y ∈ D` and `φ_D (pocketInv y) = y`. -/
theorem pocketInv_spec (hc : c.IsConformal) (hw : ContinuousOn w {s | (s : ℝ≥0∞) < ζ}) (hw0 : w 0 = 0)
    (ht : (t : ℝ≥0∞) < ζ) {y : ℂ} (hy : y ∈ H) :
    pocketInv c w t y ∈ pocketDom c w t ∧ pocketFwd c w t (pocketInv c w t y) = y :=
  Function.invFunOn_pos ((isConformalBijection_pocketFwd hc hw hw0 ht).2.surjOn hy)

/-- The inverse chart is the inverse map of the Loewner chart on `ℍ`. -/
theorem pocketInv_eq (hc : c.IsConformal) (hw : ContinuousOn w {s | (s : ℝ≥0∞) < ζ}) (hw0 : w 0 = 0)
    (ht : (t : ℝ≥0∞) < ζ) {W : ℝ → ℝ} (hc' : (c.loewner W t).IsConformal)
    (h1 : (c.loewner W t).1 = pocketFwd c w t) (hdom : ((c.loewner W t).dom : Set ℂ) = pocketDom c w t)
    {y : ℂ} (hy : y ∈ H) : pocketInv c w t y = (c.loewner W t).2.1 y := by
  obtain ⟨hm, he⟩ := pocketInv_spec hc hw hw0 ht hy
  have hm' : (c.loewner W t).2.1 y ∈ pocketDom c w t := by
    rw [← hdom]; exact hc'.inv_mem_dom hy
  have he' : pocketFwd c w t ((c.loewner W t).2.1 y) = y := by
    rw [← h1]; exact hc'.2.2 y hy
  exact (isConformalBijection_pocketFwd hc hw hw0 ht).2.injOn hm hm' (he.trans he'.symm)

/-- **The chart from the disc**: `q ↦ pocketInv (cayleyInv q)` is a conformal bijection of the unit disc onto `D`. -/
theorem isConformalBijection_pocketDisc (hc : c.IsConformal) (hw : ContinuousOn w {s | (s : ℝ≥0∞) < ζ})
    (hw0 : w 0 = 0) (ht : (t : ℝ≥0∞) < ζ) :
    IsConformalBijection (fun q => pocketInv c w t (QuantumZipper.CA.cayleyInv q)) (ball 0 1)
      (pocketDom c w t) := by
  obtain ⟨W, -, -, hc', h1, hdom, -⟩ := exists_loewnerChart hc hw hw0 ht
  have hbij := isConformalBijection_pocketFwd hc hw hw0 ht
  have hne : ∀ q ∈ ball (0 : ℂ) 1, q ≠ 1 := fun q hq h1 => by
    rw [h1, mem_ball_zero_iff, norm_one] at hq; exact lt_irrefl _ hq
  refine ⟨fun q hq => ?_, fun q hq => (pocketInv_spec hc hw hw0 ht (QuantumZipper.CA.cayleyInv_mem_H hq)).1,
    fun q₁ hq₁ q₂ hq₂ h => ?_, fun z hz => ?_⟩
  · have hd : DifferentiableWithinAt ℂ (fun q => (c.loewner W t).2.1 (QuantumZipper.CA.cayleyInv q)) (ball 0 1) q :=
      ((hc'.1 _ (QuantumZipper.CA.cayleyInv_mem_H hq)).comp q
        (QuantumZipper.CA.differentiableAt_cayleyInv (hne q hq)).differentiableWithinAt
        fun q' hq' => QuantumZipper.CA.cayleyInv_mem_H hq')
    refine hd.congr (fun q' hq' => ?_) ?_
    · exact pocketInv_eq hc hw hw0 ht hc' h1 hdom (QuantumZipper.CA.cayleyInv_mem_H hq')
    · exact pocketInv_eq hc hw hw0 ht hc' h1 hdom (QuantumZipper.CA.cayleyInv_mem_H hq)
  · have e₁ := (pocketInv_spec hc hw hw0 ht (QuantumZipper.CA.cayleyInv_mem_H hq₁)).2
    have e₂ := (pocketInv_spec hc hw hw0 ht (QuantumZipper.CA.cayleyInv_mem_H hq₂)).2
    have h' : QuantumZipper.CA.cayleyInv q₁ = QuantumZipper.CA.cayleyInv q₂ := by
      rw [← e₁, ← e₂]
      exact congrArg (pocketFwd c w t) h
    rw [← QuantumZipper.CA.cayley_cayleyInv (hne q₁ hq₁), ← QuantumZipper.CA.cayley_cayleyInv (hne q₂ hq₂), h']
  · have hy : pocketFwd c w t z ∈ H := hbij.2.mapsTo hz
    have hI : pocketFwd c w t z + Complex.I ≠ 0 := QuantumZipper.CA.add_I_ne_zero_of_im_nonneg (le_of_lt hy)
    refine ⟨QuantumZipper.CA.cayley (pocketFwd c w t z), QuantumZipper.CA.cayley_mem_ball hy, ?_⟩
    show pocketInv c w t (QuantumZipper.CA.cayleyInv (QuantumZipper.CA.cayley (pocketFwd c w t z))) = z
    rw [QuantumZipper.CA.cayleyInv_cayley hI]
    obtain ⟨hm, he⟩ := pocketInv_spec hc hw hw0 ht hy
    exact hbij.2.injOn hm hz he

/-- **The argument of `φ_D′` is continuous on `D`.** -/
theorem continuousOn_pocketLift (hc : c.IsConformal) (hlc : ContinuousOn c.2.2 c.dom)
    (hw : ContinuousOn w {s | (s : ℝ≥0∞) < ζ}) (hw0 : w 0 = 0) (ht : (t : ℝ≥0∞) < ζ) :
    ContinuousOn (pocketLift c w t) (pocketDom c w t) := by
  obtain ⟨W, hW, -, -, -, -, hL, hK⟩ := exists_loewnerChart hc hw hw0 ht
  intro z hz
  have hzd : z ∈ c.dom := pocketDom_subset_dom hc hz
  have hz' : c.1 z ∈ H \ fwdHull W t := by rw [hK]; exact fwd_mem_of_mem_pocketDom hc hz
  have h1 : ContinuousAt c.1 z :=
    (hc.differentiableOn_fwd.continuousOn z hzd).continuousAt (c.dom.isOpen.mem_nhds hzd)
  have h2 : ContinuousAt (fun z => (logDerivFwd W t (c.1 z)).im) z :=
    Complex.continuous_im.continuousAt.comp ((continuousAt_logDerivFwd hW t.coe_nonneg hz').comp h1)
  have h3 : ContinuousAt c.2.2 z := (hlc z hzd).continuousAt (c.dom.isOpen.mem_nhds hzd)
  refine (h2.add h3).continuousWithinAt.congr (fun z' _ => ?_) ?_
  · simp only [pocketLift, hL, Pi.add_apply]
  · simp only [pocketLift, hL, Pi.add_apply]

/-- **The derivative of `φ_D` has argument `pocketLift`** when the pocket lift is the imaginary part of a logarithm of
`ψ′` on the chart domain. -/
theorem deriv_pocketFwd (hc : c.IsConformal) {Lg : ℂ → ℂ} (hLg : IsDerivLog c.1 Lg c.dom)
    (hLe : ∀ z ∈ c.dom, c.2.2 z = (Lg z).im) (hw : ContinuousOn w {s | (s : ℝ≥0∞) < ζ}) (hw0 : w 0 = 0)
    (ht : (t : ℝ≥0∞) < ζ) {z : ℂ} (hz : z ∈ pocketDom c w t) :
    deriv (pocketFwd c w t) z = ‖deriv (pocketFwd c w t) z‖ * Complex.exp (pocketLift c w t z * Complex.I) := by
  obtain ⟨W, hW, -, -, h1, -, hL, hK⟩ := exists_loewnerChart hc hw hw0 ht
  have hzd : z ∈ c.dom := pocketDom_subset_dom hc hz
  have hz' : c.1 z ∈ H \ fwdHull W t := by rw [hK]; exact fwd_mem_of_mem_pocketDom hc hz
  have hdc : HasDerivAt c.1 (Complex.exp (Lg z)) z := by
    have hd : DifferentiableAt ℂ c.1 z :=
      (hc.differentiableOn_fwd z hzd).differentiableAt (c.dom.isOpen.mem_nhds hzd)
    rw [hLg.2 z hzd]
    exact hd.hasDerivAt
  have hdf : HasDerivAt (fwdMap W t) (Complex.exp (logDerivFwd W t (c.1 z))) (c.1 z) :=
    QuantumZipper.FwdHolo.hasDerivAt_fwdMap hW t.coe_nonneg hz'
  have hpf : pocketFwd c w t = fwdMap W t ∘ c.1 := by
    rw [← h1]; rfl
  have hder : deriv (pocketFwd c w t) z = Complex.exp (logDerivFwd W t (c.1 z) + Lg z) := by
    rw [hpf, (hdf.comp z hdc).deriv, Complex.exp_add]
  set X := logDerivFwd W t (c.1 z) + Lg z with hX
  have hLc : pocketLift c w t z = X.im := by
    simp only [pocketLift, hX, Complex.add_im, hL, hLe z hzd]
  rw [hder, hLc, Complex.norm_exp]
  conv_lhs => rw [← Complex.re_add_im X, Complex.exp_add]
  rw [Complex.ofReal_exp]

/-- **The pairing identity, pointwise**: `G ∘ φ_D − χ · pocketLift` is the chart-mean integrand. -/
theorem pocketG_pocketFwd_sub (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (vL : Fin nL → ℝ≥0 → ℝ)
    (vR : Fin nR → ℝ≥0 → ℝ) (a' : ℝ) (z : ℂ) :
    pocketG κ ρL ρR w vL vR t a' (pocketFwd c w t z) - QuantumZipper.chiC κ * pocketLift c w t z =
      meanCan κ ρL ρR w vL vR t (c.1 z) - a' - QuantumZipper.chiC κ * c.2.2 z := by
  simp only [pocketG, pocketFwd, pocketLift, meanCan]
  ring

/-- **`G` is bounded harmonic on `ℍ`** when the seeds are ordered (`V^L ≤ W ≤ V^R`). -/
theorem harmonicOnNhd_pocketG (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) {vL : Fin nL → ℝ≥0 → ℝ}
    {vR : Fin nR → ℝ≥0 → ℝ} (hvL : ∀ i, vL i t ≤ w t) (hvR : ∀ i, w t ≤ vR i t) (a' : ℝ) :
    InnerProductSpace.HarmonicOnNhd (pocketG κ ρL ρR w vL vR t a') {y : ℂ | 0 < y.im} ∧
      ∃ M' : ℝ, ∀ y : ℂ, 0 < y.im → |pocketG κ ρL ρR w vL vR t a' y| ≤ M' := by
  have e : pocketG κ ρL ρR w vL vR t a' = fun y => Impl.forceExt κ (weightWord ρL ρR)
      (fun i => vL i t - w t) (fun i => vR i t - w t) y - a' := by
    funext y
    exact congrArg (· - a')
      (forceExt_eq_meanHarmonic κ ρL ρR (fun i => sub_nonpos.2 (hvL i)) (fun i => sub_nonneg.2 (hvR i)) y).symm
  refine ⟨?_, meanHarmonicBound κ ρL ρR + |a'|, fun y _ => ?_⟩
  · rw [e]
    exact (Impl.harmonicOnNhd_forceExt κ (weightWord ρL ρR) _ _).sub
      (InnerProductSpace.harmonicOnNhd_const a')
  · simp only [pocketG]
    exact (abs_sub _ _).trans (by
      linarith [abs_meanHarmonic_le κ ρL ρR (fun i => vL i t - w t) (fun i => vR i t - w t) y])

end Chart

/-! ### The side limits in the half-plane coordinate, and P -/

section Side

variable {nL nR : ℕ}

/-- The chart-side function in the half-plane coordinate: `G − χ · pocketLift ∘ pocketInv`. -/
def pocketGl (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (c : Chart) (w : ℝ≥0 → ℝ) (vL : Fin nL → ℝ≥0 → ℝ)
    (vR : Fin nR → ℝ≥0 → ℝ) (t : ℝ≥0) (a' : ℝ) (y : ℂ) : ℝ :=
  pocketG κ ρL ρR w vL vR t a' y - QuantumZipper.chiC κ * pocketLift c w t (pocketInv c w t y)

/-- **The side limits of the active component in the half-plane coordinate** (the content of P, Remark 6.7): at
every real `x` outside the finite set `Ex`, the inverse chart `Finv` has a limit `p` at `x` from `ℍ`, and either `p`
lies on `A ∪ ℝ` with the full union `AL` inside `A` near `p` and `vL + F − Gl → 0` at `x` (the mean of the complete
curves has the chart boundary values), or `p` lies on `AT ∪ ℝ` with `A` inside the outer union near `p` and
`vT + F − Gl → 0` at `x`. -/
def PocketSideLimit (A AL AT : Set ℂ) (vL vT F : ℂ → ℝ) (Finv : ℂ → ℂ) (Gl : ℂ → ℝ) (Ex : Set ℝ) : Prop :=
  ∀ x : ℝ, x ∉ Ex → ∃ p : ℂ, Tendsto Finv (𝓝[H] (x : ℂ)) (𝓝 p) ∧
    ((p ∈ A ∪ {z : ℂ | z.im = 0} ∧ (∃ r > 0, AL ∩ ball p r ⊆ A) ∧
        Tendsto (fun y => vL (Finv y) + F (Finv y) - Gl y) (𝓝[H] (x : ℂ)) (𝓝 0)) ∨
      (p ∈ AT ∪ {z : ℂ | z.im = 0} ∧ (∃ r > 0, A ∩ ball p r ⊆ AT) ∧
        Tendsto (fun y => vT (Finv y) + F (Finv y) - Gl y) (𝓝[H] (x : ℂ)) (𝓝 0)))

/-- The Cayley transform carries a prime end `q ≠ 1` of the disc to the real point `cayleyInv q`, and the disc
filter to the half-plane filter there. -/
theorem cayleyInv_boundary {q : ℂ} (hq : q ∈ sphere (0 : ℂ) 1) (hq1 : q ≠ 1) :
    ((QuantumZipper.CA.cayleyInv q).re : ℂ) = QuantumZipper.CA.cayleyInv q ∧
      Tendsto QuantumZipper.CA.cayleyInv (𝓝[ball 0 1] q) (𝓝[H] (QuantumZipper.CA.cayleyInv q)) := by
  have hn : ‖q‖ = 1 := by rwa [mem_sphere_zero_iff_norm] at hq
  have him : (QuantumZipper.CA.cayleyInv q).im = 0 := by
    rw [QuantumZipper.CA.im_cayleyInv, hn]; simp
  refine ⟨Complex.ext (by simp) (by simp [him]), ?_⟩
  refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun ζ hζ =>
    QuantumZipper.CA.cayleyInv_mem_H hζ⟩
  exact ((QuantumZipper.CA.differentiableAt_cayleyInv hq1).continuousAt.tendsto).mono_left
    nhdsWithin_le_nhds

variable {c : Chart} {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {t : ℝ≥0}

/-- **P on the active component from its side limits.** For a conformal pocket chart `c` whose lift is the imaginary
part of a logarithm of `ψ′`, a driver continuous before `ζ > t` with `w 0 = 0` and ordered seeds, harmonic
representatives `v`, `vL`, `vT` of the three local-set means, and side limits at all but finitely many real points,
the prime-end premise holds on `D = ψ⁻¹(ℍ ∖ K_t)` with the chart mean as its value (chart `(pocketInv ∘ cayleyInv,
pocketFwd, pocketG, pocketLift)`). -/
theorem pocketPrimeEnd_of_sideLimit {A AL AT : Set ℂ} {gS gL gT : DistOn upperHalfPlaneOpens} {u₀ : ℂ → ℝ}
    (φ : TestOn upperHalfPlaneOpens) (hc : c.IsConformal) {Lg : ℂ → ℂ} (hLg : IsDerivLog c.1 Lg c.dom)
    (hLe : ∀ z ∈ c.dom, c.2.2 z = (Lg z).im) (hw : ContinuousOn w {s | (s : ℝ≥0∞) < ζ}) (hw0 : w 0 = 0)
    (ht : (t : ℝ≥0∞) < ζ) (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) {vL : Fin nL → ℝ≥0 → ℝ}
    {vR : Fin nR → ℝ≥0 → ℝ} (hvL : ∀ i, vL i t ≤ w t) (hvR : ∀ i, w t ≤ vR i t) (a' : ℝ)
    {v vLh vT : ℂ → ℝ} (hv : InnerProductSpace.HarmonicOnNhd v (H \ A))
    (hgv : ∀ ψ : TestOn upperHalfPlaneOpens, tsupport ψ ⊆ H \ A → gS ψ = ∫ x, v x * ψ x)
    (hvL' : InnerProductSpace.HarmonicOnNhd vLh (H \ AL))
    (hgvL : ∀ ψ : TestOn upperHalfPlaneOpens, tsupport ψ ⊆ H \ AL → gL ψ = ∫ x, vLh x * ψ x)
    (hvT : InnerProductSpace.HarmonicOnNhd vT (H \ AT))
    (hgvT : ∀ ψ : TestOn upperHalfPlaneOpens, tsupport ψ ⊆ H \ AT → gT ψ = ∫ x, vT x * ψ x)
    {Ex : Set ℝ} (hEx : Ex.Finite)
    (hside : PocketSideLimit A AL AT vLh vT u₀ (pocketInv c w t) (pocketGl κ ρL ρR c w vL vR t a') Ex) :
    Lemma71L.PocketPrimeEnd A AL AT gS gL gT u₀ (QuantumZipper.chiC κ) φ (pocketDom c w t)
      (chartMean κ ρL ρR w vL vR c a' (QuantumZipper.chiC κ) φ t) := by
  have hlc : ContinuousOn c.2.2 c.dom :=
    (Complex.continuous_im.comp_continuousOn hLg.1.continuousOn).congr fun z hz => hLe z hz
  obtain ⟨hG, hGb⟩ := harmonicOnNhd_pocketG (w := w) (t := t) κ ρL ρR hvL hvR a'
  refine ⟨v, vLh, vT, hv, hgv, hvL', hgvL, hvT, hgvT, fun q => pocketInv c w t (QuantumZipper.CA.cayleyInv q),
    pocketFwd c w t, pocketG κ ρL ρR w vL vR t a', pocketLift c w t,
    insert 1 ((fun x : ℝ => QuantumZipper.CA.cayley (x : ℂ)) '' Ex),
    isConformalBijection_pocketDisc hc hw hw0 ht, isConformalBijection_pocketFwd hc hw hw0 ht, hG, hGb,
    continuousOn_pocketLift hc hlc hw hw0 ht, fun z hz => deriv_pocketFwd hc hLg hLe hw hw0 ht hz,
    (hEx.image _).insert 1, fun q hq hqE => ?_, ?_⟩
  · have hq1 : q ≠ 1 := fun h => hqE (Set.mem_insert_iff.2 (Or.inl h))
    obtain ⟨hre, hlim⟩ := cayleyInv_boundary hq hq1
    set x : ℝ := (QuantumZipper.CA.cayleyInv q).re with hx
    have hxE : x ∉ Ex := fun h => hqE (mem_insert_of_mem _ ⟨x, h, by
      simp only
      rw [hre, QuantumZipper.CA.cayley_cayleyInv hq1]⟩)
    rw [← hre] at hlim
    obtain ⟨p, hp, halt⟩ := hside x hxE
    refine ⟨p, hp.comp hlim, ?_⟩
    have hev : ∀ (V : ℂ → ℝ), (fun y => V (pocketInv c w t y) + u₀ (pocketInv c w t y) -
          pocketGl κ ρL ρR c w vL vR t a' y) ∘ QuantumZipper.CA.cayleyInv =ᶠ[𝓝[ball 0 1] q]
        fun ζ' => (V (pocketInv c w t (QuantumZipper.CA.cayleyInv ζ')) +
          u₀ (pocketInv c w t (QuantumZipper.CA.cayleyInv ζ'))) -
          (pocketG κ ρL ρR w vL vR t a' (pocketFwd c w t (pocketInv c w t (QuantumZipper.CA.cayleyInv ζ'))) -
            QuantumZipper.chiC κ * pocketLift c w t (pocketInv c w t (QuantumZipper.CA.cayleyInv ζ'))) := by
      intro V
      refine eventually_nhdsWithin_of_forall fun ζ' hζ' => ?_
      have hy := (pocketInv_spec hc hw hw0 ht (QuantumZipper.CA.cayleyInv_mem_H hζ')).2
      simp only [Function.comp_apply, pocketGl, hy]
    rcases halt with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · exact Or.inl ⟨h1, h2, (h3.comp hlim).congr' (hev vLh)⟩
    · exact Or.inr ⟨h1, h2, (h3.comp hlim).congr' (hev vT)⟩
  · simp only [chartMean]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    beta_reduce
    rw [pocketG_pocketFwd_sub]

end Side

end InteractingSLE.Sec7.Lemma71M
