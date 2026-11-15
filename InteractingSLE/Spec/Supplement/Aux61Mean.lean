/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.Aux61Green

/-!
# Aux. lemma 61, deterministic layer: the difference of two canonical means along the flow

Packet PROVE-GB7A2. Source: specification Aux. lemma 61 (`source/spec/p241-288.md`, pp. 261–262), (PC1). The
canonical mean of a force word in the half-plane chart at time `s` is, off its seed term (common to every flow line),
the sum `∑ⱼ −(ρⱼ/√κ) arg(f_s(z) − P_j(s))` over the marks, `P_j(s) = f_s(p_j)` the centred image of the mark `p_j`
(the frozen `couplingMean`, `Ito.meanHarmonic`). The difference of two such means (an actual word and a reference
word) is therefore an *arg sum* `c₀ + ∑ⱼ cⱼ arg(f_s(z) − f_s(p_j))` over the marks of both words, without the seed
term.

* `argSum W p c c₀ s z`, `markDrift W p c s = ∑ⱼ cⱼ / Re f_s(p_j)`;
* `argSum_eq_sub_integral`: **the evolution of an arg sum**
  `argSum s z = argSum 0 z − ∫₀ˢ Im(2/f_u(z)) markDrift(u) du` (the driver cancels in `g_u(z) − g_u(p_j)`), for `z`
  and the marks alive through `[0, s]`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open scoped NNReal ENNReal ComplexConjugate Interval

namespace InteractingSLE

namespace GB7a

open QuantumZipper (H fwdMap fwdHull IsForwardSol greenH)

variable {ι : Type*} [Fintype ι]

/-- **An arg sum** `c₀ + ∑ⱼ cⱼ arg(f_s(z) − f_s(p_j))` (the difference of two canonical means, off the common
seed term). -/
def argSum (W : ℝ → ℝ) (p c : ι → ℝ) (c₀ : ℝ) (s : ℝ) (z : ℂ) : ℝ :=
  c₀ + ∑ j, c j * Complex.arg (fwdMap W s z - fwdMap W s (p j))

/-- **The mark drift** `∑ⱼ cⱼ / Re f_s(p_j)`. -/
def markDrift (W : ℝ → ℝ) (p c : ι → ℝ) (s : ℝ) : ℝ := ∑ j, c j / (fwdMap W s (p j)).re

variable {W : ℝ → ℝ}

/-- All marks are alive through `[0, t]`. -/
def MarksAlive (W : ℝ → ℝ) (p : ι → ℝ) (t : ℝ) : Prop := ∀ j, ∃ u, IsForwardSol W (p j : ℂ) t u

omit [Fintype ι] in
theorem MarksAlive.mono {p : ι → ℝ} {t : ℝ} (h : MarksAlive W p t) {s : ℝ} (hs : s ∈ Icc 0 t) :
    MarksAlive W p s := fun j => by
  obtain ⟨u, hu⟩ := h j
  exact ⟨u, QuantumZipper.isForwardSol_restrict hu hs.1 hs.2⟩

/-- The image of an alive real mark is real. -/
theorem im_fwdMap_real_eq_zero (hW : Continuous W) {x t : ℝ} {u : ℝ → ℂ} (hu : IsForwardSol W (x : ℂ) t u)
    {s : ℝ} (hs : s ∈ Icc 0 t) : (fwdMap W s x).im = 0 := by
  rw [fwdMap_eq_of_isForwardSol hW hu hs]
  exact im_eq_zero_of_isForwardSol_real hW hu hs

theorem fwdMap_real_ne_zero (hW : Continuous W) {x t : ℝ} {u : ℝ → ℂ} (hu : IsForwardSol W (x : ℂ) t u)
    {s : ℝ} (hs : s ∈ Icc 0 t) : fwdMap W s x ≠ 0 := by
  rw [fwdMap_eq_of_isForwardSol hW hu hs]
  exact (hu.2 s hs).1

theorem re_fwdMap_real_ne_zero (hW : Continuous W) {x t : ℝ} {u : ℝ → ℂ} (hu : IsForwardSol W (x : ℂ) t u)
    {s : ℝ} (hs : s ∈ Icc 0 t) : (fwdMap W s x).re ≠ 0 := fun h0 =>
  fwdMap_real_ne_zero hW hu hs (Complex.ext h0 (im_fwdMap_real_eq_zero hW hu hs))

theorem continuousOn_fwdMap_real (hW : Continuous W) {x t : ℝ} {u : ℝ → ℂ} (hu : IsForwardSol W (x : ℂ) t u) :
    ContinuousOn (fun s => fwdMap W s x) (Icc 0 t) :=
  hu.1.congr fun _ hs => fwdMap_eq_of_isForwardSol hW hu hs

theorem continuousOn_markDrift (hW : Continuous W) {p c : ι → ℝ} {t : ℝ} (h : MarksAlive W p t) :
    ContinuousOn (markDrift W p c) (Icc 0 t) := by
  refine continuousOn_finsetSum _ fun j _ => ?_
  obtain ⟨u, hu⟩ := h j
  exact continuousOn_const.div (Complex.continuous_re.comp_continuousOn (continuousOn_fwdMap_real hW hu))
    fun s hs => re_fwdMap_real_ne_zero hW hu hs

/-- The uncentred difference `g_u(z) − g_u(x) = f_u(z) − f_u(x)` for `z` and `x` alive: `(z − x) + ∫₀ᵘ (2/f(z) −
2/f(x))` (the driver cancels). -/
theorem fwdMap_sub_eq (hW : Continuous W) {t : ℝ} (ht : 0 ≤ t) {z : ℂ} (hz : z ∈ H \ fwdHull W t)
    {x : ℝ} {u : ℝ → ℂ} (hu : IsForwardSol W (x : ℂ) t u) {s : ℝ} (hs : s ∈ Icc 0 t) :
    fwdMap W s z - fwdMap W s x = (z - x) + ∫ r in (0 : ℝ)..s, (2 / fwdMap W r z - 2 / fwdMap W r x) := by
  have h1 := Ito.fwdMap_eq_sub_add_integral hW ht hz hs
  have h2 : fwdMap W s x = x - W s + ∫ r in (0 : ℝ)..s, 2 / fwdMap W r x := by
    rw [fwdMap_eq_of_isForwardSol hW hu hs, (hu.2 s hs).2]
    congr 1
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [uIcc_of_le hs.1] at hr
    rw [fwdMap_eq_of_isForwardSol hW hu ⟨hr.1, hr.2.trans hs.2⟩]
  have hcz : ContinuousOn (fun r => 2 / fwdMap W r z) (Icc 0 t) :=
    continuousOn_const.div (Ito.continuousOn_fwdMap_time' hW ht hz) fun r hr => Ito.fwdMap_ne_zero hW ht hz hr
  have hcx : ContinuousOn (fun r => 2 / fwdMap W r x) (Icc 0 t) :=
    continuousOn_const.div (continuousOn_fwdMap_real hW hu) fun r hr => fwdMap_real_ne_zero hW hu hr
  have hsub : uIcc 0 s ⊆ Icc 0 t := by rw [uIcc_of_le hs.1]; exact Icc_subset_Icc le_rfl hs.2
  rw [h1, h2, intervalIntegral.integral_sub ((hcz.mono hsub).intervalIntegrable)
    ((hcx.mono hsub).intervalIntegrable)]
  ring

/-- The time derivative of `arg(f_u(z) − f_u(x))` for `z ∈ ℍ` and a real `x`, both alive:
`−Im(2/f_u(z)) / Re f_u(x)`. -/
theorem hasDerivWithinAt_arg_fwdMap_sub (hW : Continuous W) {t : ℝ} (ht : 0 ≤ t) {z : ℂ}
    (hz : z ∈ H \ fwdHull W t) {x : ℝ} {u : ℝ → ℂ} (hu : IsForwardSol W (x : ℂ) t u) {s : ℝ}
    (hs : s ∈ Icc 0 t) :
    HasDerivWithinAt (fun r => Complex.arg (fwdMap W r z - fwdMap W r x))
      (-(2 / fwdMap W s z).im / (fwdMap W s x).re) (Icc 0 t) s := by
  set φ : ℝ → ℂ := fun r => fwdMap W r z - fwdMap W r x with hφ
  set φ' : ℝ → ℂ := fun r => 2 / fwdMap W r z - 2 / fwdMap W r x with hφ'
  have hcφ' : ContinuousOn φ' (Icc 0 t) :=
    (continuousOn_const.div (Ito.continuousOn_fwdMap_time' hW ht hz) fun r hr =>
      Ito.fwdMap_ne_zero hW ht hz hr).sub
      (continuousOn_const.div (continuousOn_fwdMap_real hW hu) fun r hr => fwdMap_real_ne_zero hW hu hr)
  -- `φ = (z − x) + ∫₀ʳ φ'` on `[0, t]`
  have hφeq : ∀ r ∈ Icc (0 : ℝ) t, φ r = (z - x) + ∫ q in (0 : ℝ)..r, φ' q := fun r hr =>
    fwdMap_sub_eq hW ht hz hu hr
  have hint : HasDerivWithinAt (fun r => (z - x) + ∫ q in (0 : ℝ)..r, φ' q) (φ' s) (Icc 0 t) s :=
    (LocalExt.hasDerivWithinAt_integral_Icc hcφ' hs).const_add (z - x)
  have hφd : HasDerivWithinAt φ (φ' s) (Icc 0 t) s := hint.congr (fun r hr => hφeq r hr) (hφeq s hs)
  -- `φ s ∈ ℍ`
  have him : (φ s).im = (fwdMap W s z).im := by
    simp only [hφ, Complex.sub_im, im_fwdMap_real_eq_zero hW hu hs, sub_zero]
  have hpos : 0 < (φ s).im := him ▸ Ito.im_fwdMap_pos hW ht hz hs
  have hslit : φ s ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.2 (Or.inr hpos.ne')
  have hlog := hφd.clog_real hslit
  have harg : HasDerivWithinAt (fun r => (Complex.log (φ r)).im) (φ' s / φ s).im (Icc 0 t) s :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivWithinAt s hlog
  have heq : (fun r => Complex.arg (φ r)) = fun r => (Complex.log (φ r)).im := by
    funext r; rw [Complex.log_im]
  rw [heq]
  convert harg using 1
  -- the algebra: `(2/f − 2/u)/(f − u) = −2/(f u)`
  have hfz : fwdMap W s z ≠ 0 := Ito.fwdMap_ne_zero hW ht hz hs
  set X : ℝ := (fwdMap W s x).re with hX
  have hux : fwdMap W s x = (X : ℂ) :=
    Complex.ext (by simp [hX]) (by simp [im_fwdMap_real_eq_zero hW hu hs])
  have hre0 : X ≠ 0 := re_fwdMap_real_ne_zero hW hu hs
  have hφ0 : φ s ≠ 0 := fun h0 => by rw [h0, Complex.zero_im] at hpos; exact lt_irrefl 0 hpos
  have hr0 : (X : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hre0
  have hk : φ' s / φ s = -(2 / fwdMap W s z) * ((1 / X : ℝ) : ℂ) := by
    have hmul : φ' s = (-(2 / fwdMap W s z) * ((1 / X : ℝ) : ℂ)) * φ s := by
      simp only [hφ', hφ]
      rw [hux]
      push_cast
      field_simp
      ring
    rw [hmul, mul_div_assoc, div_self hφ0, mul_one]
  rw [hk, Complex.im_mul_ofReal, Complex.neg_im]
  ring

/-- **The evolution of an arg sum**: for `z ∈ ℍ` and the marks alive through `[0, t]`,
`argSum s z = argSum 0 z − ∫₀ˢ Im(2/f_u(z)) markDrift(u) du`. -/
theorem argSum_eq_sub_integral (hW : Continuous W) {t : ℝ} (ht : 0 ≤ t) {p c : ι → ℝ} (c₀ : ℝ)
    (hp : MarksAlive W p t) {z : ℂ} (hz : z ∈ H \ fwdHull W t) {s : ℝ} (hs : s ∈ Icc 0 t) :
    argSum W p c c₀ s z =
      argSum W p c c₀ 0 z - ∫ u in (0 : ℝ)..s, (2 / fwdMap W u z).im * markDrift W p c u := by
  have hderiv : ∀ r ∈ Icc (0 : ℝ) t, HasDerivWithinAt (fun q => argSum W p c c₀ q z)
      (-(2 / fwdMap W r z).im * markDrift W p c r) (Icc 0 t) r := by
    intro r hr
    have hsum : HasDerivWithinAt (fun q => ∑ j, c j * Complex.arg (fwdMap W q z - fwdMap W q (p j)))
        (∑ j, c j * (-(2 / fwdMap W r z).im / (fwdMap W r (p j)).re)) (Icc 0 t) r := by
      refine HasDerivWithinAt.fun_sum fun j _ => ?_
      obtain ⟨u, hu⟩ := hp j
      exact (hasDerivWithinAt_arg_fwdMap_sub hW ht hz hu hr).const_mul (c j)
    have heq : (∑ j, c j * (-(2 / fwdMap W r z).im / (fwdMap W r (p j)).re)) =
        -(2 / fwdMap W r z).im * markDrift W p c r := by
      simp only [markDrift, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    exact (hsum.const_add c₀).congr_deriv heq
  have hcont : ContinuousOn (fun r => -(2 / fwdMap W r z).im * markDrift W p c r) (Icc 0 t) :=
    (Complex.continuous_im.comp_continuousOn (continuousOn_const.div (Ito.continuousOn_fwdMap_time' hW ht hz)
      fun r hr => Ito.fwdMap_ne_zero hW ht hz hr)).neg.mul (continuousOn_markDrift hW hp)
  have hFTC := Ito.integral_eq_sub_of_hasDerivWithinAt_Icc hderiv hcont hs.1 hs.2
  have hneg : ∫ r in (0 : ℝ)..s, -(2 / fwdMap W r z).im * markDrift W p c r =
      -∫ r in (0 : ℝ)..s, (2 / fwdMap W r z).im * markDrift W p c r := by
    rw [← intervalIntegral.integral_neg]; congr 1; funext r; ring
  rw [hneg] at hFTC
  linarith

end GB7a

end InteractingSLE
