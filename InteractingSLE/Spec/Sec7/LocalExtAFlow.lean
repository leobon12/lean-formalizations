/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.LocalExtACutoff
import InteractingSLE.Spec.Ito.Loewner

/-!
# The local comparison of Aux. lemma 55: the Loewner dynamics of `q_t` (HL5) and elementary flow bounds

Packet PROVE-LOCEXT-A, deterministic parts of step 4 (`planning/handoffs/PROVE-AUX52-55.md`, item 4). Source: Aux.
lemma 55, proof (`source/spec/p241-288.md` L184–L212, pp. 248–249):

"Keep the same driver and the same seed force coordinates, and let `M^0_t` be the two-seed canonical harmonic formula
for them. From (2.5), their difference is `q_t(z) := M_t(z) − M^0_t(z) = π κ^{-1/2} ∑_{j∈J, right} ρ_j −
κ^{-1/2} ∑_{j∈J} ρ_j arg(g_t(z) − V^j_t)` (HL5)."

Along the Loewner flow, `g_t(z) − V^j_t` moves by `2/f_t(z) − 2/(V^j_t − W_t)` (no driver increment appears), so
`arg(g_t(z) − V^j_t)` is absolutely continuous with derivative `−Im(2/f_t(z))/(V^j_t − W_t)` and

`q_s(z) − q(z) = −∫₀ˢ E(u) Im(2/f_u(z)) du`,  `E(u) = κ^{-1/2} ∑_{j∈J} ρ_j/(W_u − V^j_u)`

(the drift (HL7) of the distant marks). This is the identity that, together with the integrated Loewner–Green
identity, makes (HL6) a statement about one bounded harmonic function.

## Main results

* `arg_fwdMap_sub_mark`: the `arg` of `g_s(z) − V_s` for one mark separated from the driver;
* `distantHarm_fwdMap_sub_qExt`: **the dynamics of (HL5)**.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open scoped NNReal ENNReal ComplexConjugate

namespace InteractingSLE

namespace LocalExt

open QuantumZipper (H fwdMap fwdHull IsForwardSol)

/-! ### Fundamental theorem of calculus on `[0, T]` -/

theorem hasDerivWithinAt_integral_Icc {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {k : ℝ → E} {T : ℝ} (hk : ContinuousOn k (Icc 0 T)) {s : ℝ} (hs : s ∈ Icc 0 T) :
    HasDerivWithinAt (fun u => ∫ r in (0 : ℝ)..u, k r) (k s) (Icc 0 T) s := by
  have : Fact (s ∈ Icc 0 T) := ⟨hs⟩
  have hint : IntervalIntegrable k volume 0 s :=
    (hk.mono (by rw [uIcc_of_le hs.1]; exact Icc_subset_Icc_right hs.2)).intervalIntegrable
  exact intervalIntegral.integral_hasDerivWithinAt_right (s := Icc 0 T) (t := Icc 0 T) hint
    (hk.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc s) (hk s hs)

/-! ### One mark separated from the driver -/

section Mark

variable {W V : ℝ → ℝ} {T x δ : ℝ} {y : ℂ}

/-- **The `arg` of `g_s(y) − V_s` along the flow**, for a mark `V` started at `x` that solves the real Loewner
equation and stays at distance `≥ δ > 0` from the driver on `[0, T]`:
`arg(f_s(y) − (V_s − W_s)) = arg(y − x) − ∫₀ˢ Im(2/f_r(y))/(V_r − W_r) dr`. -/
theorem arg_fwdMap_sub_mark (hW : Continuous W) (hT : 0 ≤ T) (hy : y ∈ H \ fwdHull W T)
    (hVc : ContinuousOn V (Icc 0 T)) (hV : ∀ u ∈ Icc (0 : ℝ) T, V u = x + ∫ r in (0 : ℝ)..u, 2 / (V r - W r))
    (hδ : 0 < δ) (hsep : ∀ u ∈ Icc (0 : ℝ) T, δ ≤ |V u - W u|) {s : ℝ} (hs : s ∈ Icc 0 T) :
    Complex.arg (fwdMap W s y - ((V s - W s : ℝ) : ℂ)) =
      Complex.arg (y - x) - ∫ r in (0 : ℝ)..s, (2 / fwdMap W r y).im / (V r - W r) := by
  have hne : ∀ u ∈ Icc (0 : ℝ) T, V u - W u ≠ 0 := fun u hu h => by
    have := hsep u hu; rw [h, abs_zero] at this; linarith
  have hkV : ContinuousOn (fun r => 2 / (V r - W r)) (Icc 0 T) :=
    continuousOn_const.div (hVc.sub hW.continuousOn) hne
  have hf : ContinuousOn (fun r => fwdMap W r y) (Icc 0 T) := Ito.continuousOn_fwdMap_time' hW hT hy
  have hf0 : ∀ u ∈ Icc (0 : ℝ) T, fwdMap W u y ≠ 0 := fun u hu => Ito.fwdMap_ne_zero hW hT hy hu
  have hfim : ∀ u ∈ Icc (0 : ℝ) T, 0 < (fwdMap W u y).im := fun u hu => Ito.im_fwdMap_pos hW hT hy hu
  -- `Z u = g_u(y) − V_u`
  set Z : ℝ → ℂ := fun u => (fwdMap W u y + W u) - (V u : ℂ) with hZ
  have hZeq : ∀ u, Z u = fwdMap W u y - ((V u - W u : ℝ) : ℂ) := fun u => by
    simp only [hZ, Complex.ofReal_sub]; ring
  have hZim : ∀ u ∈ Icc (0 : ℝ) T, (Z u).im = (fwdMap W u y).im := fun u _ => by
    simp [hZ]
  have hZslit : ∀ u ∈ Icc (0 : ℝ) T, Z u ∈ Complex.slitPlane := fun u hu =>
    Complex.mem_slitPlane_iff.2 (Or.inr (by rw [hZim u hu]; exact (hfim u hu).ne'))
  have hZne : ∀ u ∈ Icc (0 : ℝ) T, Z u ≠ 0 := fun u hu h => by
    have := hZim u hu; rw [h, Complex.zero_im] at this; linarith [hfim u hu]
  have hVd : ∀ u ∈ Icc (0 : ℝ) T, HasDerivWithinAt V (2 / (V u - W u)) (Icc 0 T) u := fun u hu =>
    ((hasDerivWithinAt_integral_Icc hkV hu).const_add x).congr (fun t ht => hV t ht) (hV u hu)
  have hZd : ∀ u ∈ Icc (0 : ℝ) T, HasDerivWithinAt Z (2 / fwdMap W u y - ((2 / (V u - W u) : ℝ) : ℂ))
      (Icc 0 T) u := fun u hu =>
    (Ito.hasDerivWithinAt_fwdMap_add hW hT hy hu).sub (hVd u hu).ofReal_comp
  -- the logarithmic derivative
  have hderiv : ∀ u ∈ Icc (0 : ℝ) T, (2 / fwdMap W u y - ((2 / (V u - W u) : ℝ) : ℂ)) / Z u =
      -(2 / (fwdMap W u y * ((V u - W u : ℝ) : ℂ))) := fun u hu => by
    have h1 := hf0 u hu
    have h2 : ((V u - W u : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (hne u hu)
    have h3 := hZne u hu
    rw [hZeq u] at h3 ⊢
    push_cast at h2 h3 ⊢
    field_simp
    ring
  have hLd : ∀ u ∈ Icc (0 : ℝ) T, HasDerivWithinAt (fun u => Complex.log (Z u))
      (-(2 / (fwdMap W u y * ((V u - W u : ℝ) : ℂ)))) (Icc 0 T) u := fun u hu => by
    rw [← hderiv u hu]
    exact (hZd u hu).clog_real (hZslit u hu)
  have hLc : ContinuousOn (fun u => -(2 / (fwdMap W u y * ((V u - W u : ℝ) : ℂ)))) (Icc 0 T) := by
    refine (continuousOn_const.div (hf.mul (Complex.continuous_ofReal.comp_continuousOn
      (hVc.sub hW.continuousOn))) fun u hu => mul_ne_zero (hf0 u hu)
        (Complex.ofReal_ne_zero.2 (hne u hu))).neg
  have hFTC := Ito.integral_eq_sub_of_hasDerivWithinAt_Icc hLd hLc hs.1 hs.2
  have h0 : Z 0 = y - x := by
    have := Ito.fwdMap_eq_sub_add_integral hW hT hy ⟨le_rfl, hT⟩
    simp only [intervalIntegral.integral_same, add_zero] at this
    rw [hZ]
    simp only
    rw [this, hV 0 ⟨le_rfl, hT⟩, intervalIntegral.integral_same, add_zero]
    ring
  have him := congrArg Complex.im hFTC
  rw [Complex.sub_im, Complex.log_im, Complex.log_im, h0] at him
  have hint : (∫ r in (0 : ℝ)..s, -(2 / (fwdMap W r y * ((V r - W r : ℝ) : ℂ)))).im =
      ∫ r in (0 : ℝ)..s, -((2 / fwdMap W r y).im / (V r - W r)) := by
    rw [← Complex.imCLM_apply, ← ContinuousLinearMap.intervalIntegral_comp_comm]
    · refine intervalIntegral.integral_congr fun r _ => ?_
      simp only [Complex.imCLM_apply, Complex.neg_im]
      rw [← div_div, Complex.div_ofReal_im]
    · exact (hLc.mono (by rw [uIcc_of_le hs.1]; exact Icc_subset_Icc_right hs.2)).intervalIntegrable
  rw [hint, intervalIntegral.integral_neg] at him
  rw [← hZeq s]
  linarith

/-- A mark separated from the driver on `[0, T]`: continuous, solving the real Loewner equation from `x`, at
distance `≥ δ` from the driver. -/
structure IsSeparatedMark (W V : ℝ → ℝ) (x T δ : ℝ) : Prop where
  cont : ContinuousOn V (Icc 0 T)
  eq : ∀ u ∈ Icc (0 : ℝ) T, V u = x + ∫ r in (0 : ℝ)..u, 2 / (V r - W r)
  sep : ∀ u ∈ Icc (0 : ℝ) T, δ ≤ |V u - W u|

theorem IsSeparatedMark.ne_zero {δ : ℝ} (hδ : 0 < δ) (hm : IsSeparatedMark W V x T δ) {u : ℝ}
    (hu : u ∈ Icc 0 T) : V u - W u ≠ 0 := fun h => by
  have := hm.sep u hu; rw [h, abs_zero] at this; linarith

theorem IsSeparatedMark.continuousOn_inv (hW : Continuous W) {δ : ℝ} (hδ : 0 < δ)
    (hm : IsSeparatedMark W V x T δ) : ContinuousOn (fun r => (V r - W r)⁻¹) (Icc 0 T) :=
  (hm.cont.sub hW.continuousOn).inv₀ fun _ hu => hm.ne_zero hδ hu

end Mark

/-! ### The dynamics of (HL5) -/

section Dynamics

variable {nL nR : ℕ} {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}

variable (κ xL xR ρL ρR) in
/-- **The drift (HL7) of the distant marks**: `E = κ^{-1/2} ∑_{j∈J} ρ_j/(w − v_j)`. -/
def distDrift (w : ℝ) (vL : Fin nL → ℝ) (vR : Fin nR → ℝ) : ℝ :=
  1 / Real.sqrt κ * (∑ i ∈ distSetL xL, ρL i / (w - vL i) + ∑ i ∈ distSetR xR, ρR i / (w - vR i))

variable {W : ℝ → ℝ} {VL : Fin nL → ℝ → ℝ} {VR : Fin nR → ℝ → ℝ} {T δ : ℝ} {y : ℂ}

/-- **The dynamics of (HL5)**: along the Loewner flow, with the distant marks separated from the driver,
`q_s(y) − q(y) = −∫₀ˢ E(u) Im(2/f_u(y)) du`, where `q_s(y) = distantHarm (V_s − W_s) (f_s(y))` and `q = qExt`. -/
theorem distantHarm_fwdMap_sub_qExt (hW : Continuous W) (hT : 0 ≤ T) (hy : y ∈ H \ fwdHull W T) (hδ : 0 < δ)
    (hL : ∀ i ∈ distSetL xL, IsSeparatedMark W (VL i) (xL i) T δ)
    (hR : ∀ i ∈ distSetR xR, IsSeparatedMark W (VR i) (xR i) T δ) {s : ℝ} (hs : s ∈ Icc 0 T) :
    distantHarm κ xL xR ρL ρR (fun i => VL i s - W s) (fun i => VR i s - W s) (fwdMap W s y) -
        qExt κ xL xR ρL ρR y =
      -∫ u in (0 : ℝ)..s, distDrift κ xL xR ρL ρR (W u) (fun i => VL i u) (fun i => VR i u) *
        (2 / fwdMap W u y).im := by
  have hsI : uIcc (0 : ℝ) s ⊆ Icc 0 T := by rw [uIcc_of_le hs.1]; exact Icc_subset_Icc_right hs.2
  have hfim : ContinuousOn (fun u => (2 / fwdMap W u y).im) (Icc 0 T) :=
    Complex.continuous_im.comp_continuousOn (continuousOn_const.div (Ito.continuousOn_fwdMap_time' hW hT hy)
      fun u hu => Ito.fwdMap_ne_zero hW hT hy hu)
  have hintL : ∀ i ∈ distSetL xL,
      IntervalIntegrable (fun u => (2 / fwdMap W u y).im / (VL i u - W u)) volume 0 s := fun i hi =>
    ((hfim.mul ((hL i hi).continuousOn_inv hW hδ)).mono hsI).intervalIntegrable.congr_ae
      (ae_of_all _ fun u => by simp [div_eq_mul_inv])
  have hintR : ∀ i ∈ distSetR xR,
      IntervalIntegrable (fun u => (2 / fwdMap W u y).im / (VR i u - W u)) volume 0 s := fun i hi =>
    ((hfim.mul ((hR i hi).continuousOn_inv hW hδ)).mono hsI).intervalIntegrable.congr_ae
      (ae_of_all _ fun u => by simp [div_eq_mul_inv])
  have hargL : ∀ i ∈ distSetL xL, Complex.arg (fwdMap W s y - ((VL i s - W s : ℝ) : ℂ)) =
      Complex.arg (y - xL i) - ∫ u in (0 : ℝ)..s, (2 / fwdMap W u y).im / (VL i u - W u) := fun i hi =>
    arg_fwdMap_sub_mark hW hT hy (hL i hi).cont (hL i hi).eq hδ (hL i hi).sep hs
  have hargR : ∀ i ∈ distSetR xR, Complex.arg (fwdMap W s y - ((VR i s - W s : ℝ) : ℂ)) =
      Complex.arg (y - xR i) - ∫ u in (0 : ℝ)..s, (2 / fwdMap W u y).im / (VR i u - W u) := fun i hi =>
    arg_fwdMap_sub_mark hW hT hy (hR i hi).cont (hR i hi).eq hδ (hR i hi).sep hs
  have hyH : 0 < y.im := hy.1
  have hsumL : ∑ i ∈ distSetL xL, ρL i * Complex.arg (fwdMap W s y - ((VL i s - W s : ℝ) : ℂ)) =
      ∑ i ∈ distSetL xL, ρL i * Complex.arg (y - xL i) -
        ∑ i ∈ distSetL xL, ρL i * (∫ u in (0 : ℝ)..s, (2 / fwdMap W u y).im / (VL i u - W u)) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i hi => by rw [hargL i hi, mul_sub]
  have hsumR : ∑ i ∈ distSetR xR, ρR i * Complex.arg (fwdMap W s y - ((VR i s - W s : ℝ) : ℂ)) =
      ∑ i ∈ distSetR xR, ρR i * Complex.arg (y - xR i) -
        ∑ i ∈ distSetR xR, ρR i * (∫ u in (0 : ℝ)..s, (2 / fwdMap W u y).im / (VR i u - W u)) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i hi => by rw [hargR i hi, mul_sub]
  -- the drift integral, split over the marks
  have hE : ∫ u in (0 : ℝ)..s, distDrift κ xL xR ρL ρR (W u) (fun i => VL i u) (fun i => VR i u) *
      (2 / fwdMap W u y).im =
      -(1 / Real.sqrt κ) * (∑ i ∈ distSetL xL, ρL i * (∫ u in (0 : ℝ)..s,
          (2 / fwdMap W u y).im / (VL i u - W u))
        + ∑ i ∈ distSetR xR, ρR i * (∫ u in (0 : ℝ)..s, (2 / fwdMap W u y).im / (VR i u - W u))) := by
    have e : ∀ u, distDrift κ xL xR ρL ρR (W u) (fun i => VL i u) (fun i => VR i u) *
        (2 / fwdMap W u y).im = -(1 / Real.sqrt κ) * (∑ i ∈ distSetL xL, ρL i *
          ((2 / fwdMap W u y).im / (VL i u - W u)) + ∑ i ∈ distSetR xR, ρR i *
          ((2 / fwdMap W u y).im / (VR i u - W u))) := fun u => by
      set F := (2 / fwdMap W u y).im
      have hA : (∑ i ∈ distSetL xL, ρL i / (W u - VL i u)) * F =
          -∑ i ∈ distSetL xL, ρL i * (F / (VL i u - W u)) := by
        rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [show W u - VL i u = -(VL i u - W u) by ring, div_neg]
        ring
      have hB : (∑ i ∈ distSetR xR, ρR i / (W u - VR i u)) * F =
          -∑ i ∈ distSetR xR, ρR i * (F / (VR i u - W u)) := by
        rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [show W u - VR i u = -(VR i u - W u) by ring, div_neg]
        ring
      simp only [distDrift]
      linear_combination (1 / Real.sqrt κ) * hA + (1 / Real.sqrt κ) * hB
    have iL : IntervalIntegrable (fun u => ∑ i ∈ distSetL xL, ρL i *
        ((2 / fwdMap W u y).im / (VL i u - W u))) volume 0 s := by
      have := IntervalIntegrable.sum (distSetL xL) fun i hi => (hintL i hi).const_mul (ρL i)
      rwa [Finset.sum_fn] at this
    have iR : IntervalIntegrable (fun u => ∑ i ∈ distSetR xR, ρR i *
        ((2 / fwdMap W u y).im / (VR i u - W u))) volume 0 s := by
      have := IntervalIntegrable.sum (distSetR xR) fun i hi => (hintR i hi).const_mul (ρR i)
      rwa [Finset.sum_fn] at this
    simp_rw [e]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add iL iR,
      intervalIntegral.integral_finsetSum (fun i hi => (hintL i hi).const_mul _),
      intervalIntegral.integral_finsetSum (fun i hi => (hintR i hi).const_mul _)]
    simp only [intervalIntegral.integral_const_mul]
  rw [qExt_eq_distantHarm hyH]
  simp only [distantHarm]
  rw [hsumL, hsumR, hE]
  ring

end Dynamics

/-! ### Elementary flow bounds (barriers) -/

section Barrier

variable {W : ℝ → ℝ} {T M : ℝ} {y : ℂ}

theorem hasDerivWithinAt_Ici_of_Icc {f : ℝ → ℝ} {f' : ℝ} {x : ℝ} (h : HasDerivWithinAt f f' (Icc 0 T) x)
    (hx : x ∈ Ico 0 T) : HasDerivWithinAt f f' (Ici x) x :=
  h.mono_of_mem_nhdsWithin (mem_of_superset (Icc_mem_nhdsGE hx.2) (Icc_subset_Icc_left hx.1))

/-- The real part of `g_u(y)` has derivative `Re(2/f_u(y)) = 2 Re f_u(y)/|f_u(y)|²`. -/
theorem hasDerivWithinAt_re_g (hW : Continuous W) (hT : 0 ≤ T) (hy : y ∈ H \ fwdHull W T) {u : ℝ}
    (hu : u ∈ Icc 0 T) :
    HasDerivWithinAt (fun r => (fwdMap W r y).re + W r) (2 / fwdMap W u y).re (Icc 0 T) u := by
  have h := Complex.reCLM.hasFDerivAt.comp_hasDerivWithinAt u (Ito.hasDerivWithinAt_fwdMap_add hW hT hy hu)
  exact h.congr (fun r _ => by simp) (by simp)

theorem hasDerivWithinAt_im_f (hW : Continuous W) (hT : 0 ≤ T) (hy : y ∈ H \ fwdHull W T) {u : ℝ}
    (hu : u ∈ Icc 0 T) :
    HasDerivWithinAt (fun r => (fwdMap W r y).im) (2 / fwdMap W u y).im (Icc 0 T) u := by
  have h := Complex.imCLM.hasFDerivAt.comp_hasDerivWithinAt u (Ito.hasDerivWithinAt_fwdMap_add hW hT hy hu)
  exact h.congr (fun r _ => by simp) (by simp)

theorem re_two_div (f : ℂ) : (2 / f).re = 2 * f.re / Complex.normSq f := by
  simp [Complex.div_re]

theorem im_two_div (f : ℂ) : (2 / f).im = -(2 * f.im) / Complex.normSq f := by
  simp [Complex.div_im, neg_div]

theorem continuousOn_re_g (hW : Continuous W) (hT : 0 ≤ T) (hy : y ∈ H \ fwdHull W T) :
    ContinuousOn (fun r => (fwdMap W r y).re + W r) (Icc 0 T) :=
  (Complex.continuous_re.comp_continuousOn (Ito.continuousOn_fwdMap_time' hW hT hy)).add hW.continuousOn

/-- **Lower barrier**: if `|W| ≤ M` on `[0, T]` and `Re y ≥ M + δ`, `δ > 0`, then `Re g_u(y) ≥ Re y` and
`Re f_u(y) ≥ δ` on `[0, T]` ("the real Loewner equation moves that coordinate away from the driver", p. 249). -/
theorem le_re_fwdMap_of_le_re (hW : Continuous W) (hT : 0 ≤ T) (hy : y ∈ H \ fwdHull W T)
    (hM : ∀ u ∈ Icc (0 : ℝ) T, |W u| ≤ M) {δ : ℝ} (hδ : 0 < δ) (hyre : M + δ ≤ y.re) {u : ℝ}
    (hu : u ∈ Icc 0 T) : δ ≤ (fwdMap W u y).re := by
  have hcont : ContinuousOn (fun r => y.re - ((fwdMap W r y).re + W r)) (Icc 0 T) :=
    continuousOn_const.sub (continuousOn_re_g hW hT hy)
  have hle := image_le_of_deriv_right_lt_deriv_boundary' hcont
    (f' := fun r => -(2 / fwdMap W r y).re)
    (fun x hx => hasDerivWithinAt_Ici_of_Icc ((hasDerivWithinAt_re_g hW hT hy (Ico_subset_Icc_self hx)).const_sub
      _) hx)
    (B := fun _ => 0) (B' := fun _ => 0) (by
      have h0 := Ito.fwdMap_eq_sub_add_integral hW hT hy ⟨le_rfl, hT⟩
      simp only [intervalIntegral.integral_same, add_zero] at h0
      simp [h0]) continuousOn_const (fun x _ => hasDerivWithinAt_const _ _ _) (fun x hx heq => by
      have hx' := Ico_subset_Icc_self hx
      have hre : y.re - W x ≤ (fwdMap W x y).re := by linarith
      have hpos : 0 < (fwdMap W x y).re := by
        have := (abs_le.1 (hM x hx')).2; linarith
      have hns : 0 < Complex.normSq (fwdMap W x y) := Complex.normSq_pos.2 (Ito.fwdMap_ne_zero hW hT hy hx')
      simp only [re_two_div, neg_lt_zero]
      positivity)
  have h := hle hu
  have := (abs_le.1 (hM u hu)).2
  beta_reduce at h
  linarith

/-- **Lower barrier, left side**: if `|W| ≤ M` on `[0, T]` and `Re y ≤ −M − δ`, then `Re f_u(y) ≤ −δ`. -/
theorem re_fwdMap_le_of_re_le (hW : Continuous W) (hT : 0 ≤ T) (hy : y ∈ H \ fwdHull W T)
    (hM : ∀ u ∈ Icc (0 : ℝ) T, |W u| ≤ M) {δ : ℝ} (hδ : 0 < δ) (hyre : y.re ≤ -M - δ) {u : ℝ}
    (hu : u ∈ Icc 0 T) : (fwdMap W u y).re ≤ -δ := by
  have hcont : ContinuousOn (fun r => ((fwdMap W r y).re + W r) - y.re) (Icc 0 T) :=
    (continuousOn_re_g hW hT hy).sub continuousOn_const
  have hle := image_le_of_deriv_right_lt_deriv_boundary' hcont
    (f' := fun r => (2 / fwdMap W r y).re)
    (fun x hx => hasDerivWithinAt_Ici_of_Icc ((hasDerivWithinAt_re_g hW hT hy (Ico_subset_Icc_self hx)).sub_const
      _) hx)
    (B := fun _ => 0) (B' := fun _ => 0) (by
      have h0 := Ito.fwdMap_eq_sub_add_integral hW hT hy ⟨le_rfl, hT⟩
      simp only [intervalIntegral.integral_same, add_zero] at h0
      simp [h0]) continuousOn_const (fun x _ => hasDerivWithinAt_const _ _ _) (fun x hx heq => by
      have hx' := Ico_subset_Icc_self hx
      have hneg : (fwdMap W x y).re < 0 := by
        have := (abs_le.1 (hM x hx')).1; linarith
      have hns : 0 < Complex.normSq (fwdMap W x y) := Complex.normSq_pos.2 (Ito.fwdMap_ne_zero hW hT hy hx')
      simp only [re_two_div]
      exact div_neg_of_neg_of_pos (by linarith) hns)
  have h := hle hu
  have := (abs_le.1 (hM u hu)).1
  beta_reduce at h
  linarith

/-- **The height barrier**: `(Im f_u(y))² ≥ (Im y)² − 5u` (the source's `(Im g_t(z))² ≥ (Im z)² − 4t`, p. 249, with
slack). -/
theorem sq_im_le_sq_im_fwdMap (hW : Continuous W) (hT : 0 ≤ T) (hy : y ∈ H \ fwdHull W T) {u : ℝ}
    (hu : u ∈ Icc 0 T) : y.im ^ 2 - 5 * u ≤ (fwdMap W u y).im ^ 2 := by
  have hcont : ContinuousOn (fun r => y.im ^ 2 - 5 * r - (fwdMap W r y).im ^ 2) (Icc 0 T) :=
    (continuousOn_const.sub (continuousOn_const.mul continuousOn_id)).sub
      ((Complex.continuous_im.comp_continuousOn (Ito.continuousOn_fwdMap_time' hW hT hy)).pow 2)
  have hle := image_le_of_deriv_right_lt_deriv_boundary' hcont
    (f' := fun r => -5 - 2 * (fwdMap W r y).im * (2 / fwdMap W r y).im)
    (fun x hx => by
      have hx' := Ico_subset_Icc_self hx
      have h := ((hasDerivWithinAt_const x (Icc 0 T) (y.im ^ 2)).sub
        ((hasDerivWithinAt_id x (Icc 0 T)).const_mul 5)).sub ((hasDerivWithinAt_im_f hW hT hy hx').pow 2)
      refine hasDerivWithinAt_Ici_of_Icc (h.congr_deriv ?_) hx
      simp only [Nat.cast_ofNat]
      ring)
    (B := fun _ => 0) (B' := fun _ => 0) (by
      have h0 := Ito.fwdMap_eq_sub_add_integral hW hT hy ⟨le_rfl, hT⟩
      simp only [intervalIntegral.integral_same, add_zero] at h0
      simp [h0]) continuousOn_const (fun x _ => hasDerivWithinAt_const _ _ _) (fun x hx _ => by
      have hx' := Ico_subset_Icc_self hx
      have hns : 0 < Complex.normSq (fwdMap W x y) := Complex.normSq_pos.2 (Ito.fwdMap_ne_zero hW hT hy hx')
      have hle : (fwdMap W x y).im ^ 2 ≤ Complex.normSq (fwdMap W x y) := by
        rw [Complex.normSq_apply]; nlinarith [sq_nonneg (fwdMap W x y).re]
      rw [im_two_div]
      have : 2 * (fwdMap W x y).im * (-(2 * (fwdMap W x y).im) / Complex.normSq (fwdMap W x y)) =
          -4 * ((fwdMap W x y).im ^ 2 / Complex.normSq (fwdMap W x y)) := by ring
      rw [this]
      have : (fwdMap W x y).im ^ 2 / Complex.normSq (fwdMap W x y) ≤ 1 := (div_le_one hns).2 hle
      linarith)
  have h := hle hu
  beta_reduce at h
  linarith

/-- **Upper barrier**: if `|W| ≤ M` on `[0, T]` and `R₀ > 0`, then `Re g_u(y) ≤ max (Re y) (M + R₀) + 4u/R₀`. -/
theorem re_g_le (hW : Continuous W) (hT : 0 ≤ T) (hy : y ∈ H \ fwdHull W T)
    (hM : ∀ u ∈ Icc (0 : ℝ) T, |W u| ≤ M) {R₀ : ℝ} (hR₀ : 0 < R₀) {u : ℝ} (hu : u ∈ Icc 0 T) :
    (fwdMap W u y).re + W u ≤ max y.re (M + R₀) + 4 / R₀ * u := by
  set L := max y.re (M + R₀)
  have hcont : ContinuousOn (fun r => (fwdMap W r y).re + W r - L - 4 / R₀ * r) (Icc 0 T) :=
    ((continuousOn_re_g hW hT hy).sub continuousOn_const).sub (continuousOn_const.mul continuousOn_id)
  have hle := image_le_of_deriv_right_lt_deriv_boundary' hcont
    (f' := fun r => (2 / fwdMap W r y).re - 4 / R₀)
    (fun x hx => by
      have hx' := Ico_subset_Icc_self hx
      have h := ((hasDerivWithinAt_re_g hW hT hy hx').sub_const L).sub
        ((hasDerivWithinAt_id x (Icc 0 T)).const_mul (4 / R₀))
      refine hasDerivWithinAt_Ici_of_Icc (h.congr_deriv ?_) hx
      simp)
    (B := fun _ => 0) (B' := fun _ => 0) (by
      have h0 := Ito.fwdMap_eq_sub_add_integral hW hT hy ⟨le_rfl, hT⟩
      simp only [intervalIntegral.integral_same, add_zero] at h0
      simp only [h0, Complex.sub_re, Complex.ofReal_re, mul_zero, sub_zero]
      have := le_max_left y.re (M + R₀)
      linarith) continuousOn_const (fun x _ => hasDerivWithinAt_const _ _ _) (fun x hx heq => by
      have hx' := Ico_subset_Icc_self hx
      have hWx := (abs_le.1 (hM x hx')).2
      have hLx : M + R₀ ≤ L := le_max_right _ _
      have hRe : R₀ ≤ (fwdMap W x y).re := by
        have : 0 ≤ 4 / R₀ * x := mul_nonneg (by positivity) hx'.1
        linarith
      have hns : 0 < Complex.normSq (fwdMap W x y) := Complex.normSq_pos.2 (Ito.fwdMap_ne_zero hW hT hy hx')
      have hsq : (fwdMap W x y).re ^ 2 ≤ Complex.normSq (fwdMap W x y) := by
        rw [Complex.normSq_apply]; nlinarith [sq_nonneg (fwdMap W x y).im]
      rw [re_two_div]
      have hRpos : 0 < (fwdMap W x y).re := lt_of_lt_of_le hR₀ hRe
      have h1 : 2 * (fwdMap W x y).re / Complex.normSq (fwdMap W x y) ≤ 2 / (fwdMap W x y).re := by
        rw [div_le_div_iff₀ hns hRpos]; nlinarith
      have h2 : 2 / (fwdMap W x y).re ≤ 2 / R₀ := div_le_div_of_nonneg_left zero_le_two hR₀ hRe
      have h3 : 2 / R₀ < 4 / R₀ := div_lt_div_of_pos_right (by norm_num) hR₀
      linarith)
  have h := hle hu
  beta_reduce at h
  linarith

/-- **Upper barrier, left side**: `Re g_u(y) ≥ min (Re y) (−M − R₀) − 4u/R₀`. -/
theorem le_re_g (hW : Continuous W) (hT : 0 ≤ T) (hy : y ∈ H \ fwdHull W T)
    (hM : ∀ u ∈ Icc (0 : ℝ) T, |W u| ≤ M) {R₀ : ℝ} (hR₀ : 0 < R₀) {u : ℝ} (hu : u ∈ Icc 0 T) :
    min y.re (-M - R₀) - 4 / R₀ * u ≤ (fwdMap W u y).re + W u := by
  set L := min y.re (-M - R₀)
  have hcont : ContinuousOn (fun r => L - 4 / R₀ * r - ((fwdMap W r y).re + W r)) (Icc 0 T) :=
    (continuousOn_const.sub (continuousOn_const.mul continuousOn_id)).sub (continuousOn_re_g hW hT hy)
  have hle := image_le_of_deriv_right_lt_deriv_boundary' hcont
    (f' := fun r => -(4 / R₀) - (2 / fwdMap W r y).re)
    (fun x hx => by
      have hx' := Ico_subset_Icc_self hx
      have h := ((hasDerivWithinAt_const x (Icc 0 T) L).sub
        ((hasDerivWithinAt_id x (Icc 0 T)).const_mul (4 / R₀))).sub (hasDerivWithinAt_re_g hW hT hy hx')
      refine hasDerivWithinAt_Ici_of_Icc (h.congr_deriv ?_) hx
      simp)
    (B := fun _ => 0) (B' := fun _ => 0) (by
      have h0 := Ito.fwdMap_eq_sub_add_integral hW hT hy ⟨le_rfl, hT⟩
      simp only [intervalIntegral.integral_same, add_zero] at h0
      simp only [h0, Complex.sub_re, Complex.ofReal_re, mul_zero, sub_zero]
      have := min_le_left y.re (-M - R₀)
      linarith) continuousOn_const (fun x _ => hasDerivWithinAt_const _ _ _) (fun x hx heq => by
      have hx' := Ico_subset_Icc_self hx
      have hWx := (abs_le.1 (hM x hx')).1
      have hLx : L ≤ -M - R₀ := min_le_right _ _
      have hRe : (fwdMap W x y).re ≤ -R₀ := by
        have : 0 ≤ 4 / R₀ * x := mul_nonneg (by positivity) hx'.1
        linarith
      have hns : 0 < Complex.normSq (fwdMap W x y) := Complex.normSq_pos.2 (Ito.fwdMap_ne_zero hW hT hy hx')
      have hsq : (fwdMap W x y).re ^ 2 ≤ Complex.normSq (fwdMap W x y) := by
        rw [Complex.normSq_apply]; nlinarith [sq_nonneg (fwdMap W x y).im]
      rw [re_two_div]
      have hRneg : (fwdMap W x y).re < 0 := by linarith
      have h1 : 2 / (fwdMap W x y).re ≤ 2 * (fwdMap W x y).re / Complex.normSq (fwdMap W x y) := by
        have e : 2 * (fwdMap W x y).re / Complex.normSq (fwdMap W x y) - 2 / (fwdMap W x y).re =
            2 * (Complex.normSq (fwdMap W x y) - (fwdMap W x y).re ^ 2) /
              (-(fwdMap W x y).re * Complex.normSq (fwdMap W x y)) := by
          field_simp
          ring
        have : 0 ≤ 2 * (Complex.normSq (fwdMap W x y) - (fwdMap W x y).re ^ 2) /
            (-(fwdMap W x y).re * Complex.normSq (fwdMap W x y)) :=
          div_nonneg (mul_nonneg zero_le_two (sub_nonneg.2 hsq))
            (mul_nonneg (neg_nonneg.2 hRneg.le) hns.le)
        linarith
      have h2 : -(2 / R₀) ≤ 2 / (fwdMap W x y).re := by
        rw [neg_le, ← div_neg]
        exact div_le_div_of_nonneg_left zero_le_two hR₀ (by linarith)
      have h3 : 2 / R₀ < 4 / R₀ := div_lt_div_of_pos_right (by norm_num) hR₀
      linarith)
  have h := hle hu
  beta_reduce at h
  linarith

end Barrier

end LocalExt

end InteractingSLE
