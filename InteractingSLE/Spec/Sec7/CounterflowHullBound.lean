/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import QuantumZipper.Proofs.Thm11.ForwardClock

/-!
# §7.4: the imaginary-part half of the Loewner rectangle bound

Packet PROVE-SEC7-D. Aux. lemmas 117 and 122 (`source/spec/p337-384.md` L913, `p385-432.md` L114) fix a bounded
capacity horizon `t₀` and use the point `z = iY` with `Y² > 4t₀`: "this point is not swallowed by that horizon". The
same estimate is the height half of the Loewner rectangle bound (`EXT.Law05.loewner-rectangle-bound`) used for the
buffered stop (FS11.1) of Aux. lemma 126 (hulls through `S_r` have height at most `2√(r²/64) = r/4`) and in the proof of
Lemma 7.24.

Along the centred forward flow `u(s) = g_s(z) − W_s` (QuantumZipper's `IsForwardSol`),
`d(Im u)²/ds = −4 (Im u)²/|u|² ≥ −4`, so `(Im u(s))² + 4s` is nondecreasing (`monotoneOn_im_sq_add_four_mul`). Hence
`(Im f_t(z))² ≥ (Im z)² − 4t` (`im_fwdMap_sq_ge`), and a point with `4T < (Im z)²` is not in the hull `K_T`
(`notMem_fwdHull_of_four_mul_lt_im_sq`); equivalently every hull point has `Im z ≤ 2√T`
(`im_le_two_mul_sqrt_of_mem_fwdHull`); in particular `iY ∉ K_{t₀}` when `Y² > 4t₀` (`I_mul_notMem_fwdHull`).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology MeasureTheory
open scoped Real ENNReal
open QuantumZipper (H IsForwardSol swallowTime fwdHull fwdMap)

namespace InteractingSLE

namespace Sec7

variable {W : ℝ → ℝ} {z : ℂ} {T : ℝ} {u : ℝ → ℂ}

theorem im_two_div (w : ℂ) : (2 / w).im = -2 * w.im / normSq w := by
  rw [div_im]; simp; ring

/-- Along a forward solution, `(Im u(s))² + 4s` is nondecreasing on `[0, T]`. -/
theorem monotoneOn_im_sq_add_four_mul (hu : IsForwardSol W z T u) :
    MonotoneOn (fun s => (u s).im ^ 2 + 4 * s) (Icc 0 T) := by
  obtain ⟨hcont, hsol⟩ := hu
  set F : ℝ → ℂ := fun s => ∫ r in (0 : ℝ)..s, 2 / u r with hF
  have hcont2 : ContinuousOn (fun r => 2 / u r) (Icc 0 T) :=
    continuousOn_const.div hcont fun r hr => (hsol r hr).1
  -- `Im u = Im z + Im F` on `[0, T]`
  have him : ∀ s ∈ Icc (0 : ℝ) T, (u s).im = z.im + (F s).im := by
    intro s hs
    rw [(hsol s hs).2]; simp [hF]
  -- derivative of `Im F` at interior points
  have hderiv : ∀ s ∈ Ioo (0 : ℝ) T, HasDerivAt (fun s => (u s).im) (2 / u s).im s := by
    intro s hs
    have hsI : s ∈ Icc (0 : ℝ) T := Ioo_subset_Icc_self hs
    have hca : ContinuousAt (fun r => 2 / u r) s :=
      hcont2.continuousAt (Icc_mem_nhds hs.1 hs.2)
    have hii : IntervalIntegrable (fun r => 2 / u r) volume 0 s :=
      (hcont2.mono (Icc_subset_Icc le_rfl hsI.2)).intervalIntegrable_of_Icc hsI.1
    have hmeas : StronglyMeasurableAtFilter (fun r => 2 / u r) (𝓝 s) volume :=
      ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo (hcont2.mono Ioo_subset_Icc_self) s hs
    have hFd : HasDerivAt F (2 / u s) s := intervalIntegral.integral_hasDerivAt_right hii hmeas hca
    have hIm : HasDerivAt (fun s => z.im + (F s).im) (2 / u s).im s := by
      have := (Complex.imCLM.hasFDerivAt.comp_hasDerivAt s hFd)
      simpa using this.const_add z.im
    refine hIm.congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds hs.1 hs.2] with r hr
    exact him r (Ioo_subset_Icc_self hr)
  have hcontIm : ContinuousOn (fun s => (u s).im ^ 2 + 4 * s) (Icc 0 T) :=
    ((continuous_im.comp_continuousOn hcont).pow 2).add (continuousOn_const.mul continuousOn_id)
  have hd : ∀ s ∈ Ioo (0 : ℝ) T, HasDerivAt (fun s => (u s).im ^ 2 + 4 * s)
      (2 * (u s).im * (2 / u s).im + 4) s := by
    intro s hs
    have h3 := ((hderiv s hs).pow 2).add ((hasDerivAt_id s).const_mul (4 : ℝ))
    refine h3.congr_deriv ?_
    norm_num
  refine monotoneOn_of_deriv_nonneg (convex_Icc 0 T) hcontIm ?_ ?_
  · rw [interior_Icc]
    intro s hs
    exact (hd s hs).differentiableAt.differentiableWithinAt
  · rw [interior_Icc]
    intro s hs
    rw [(hd s hs).deriv, im_two_div]
    have hne : u s ≠ 0 := (hsol s (Ioo_subset_Icc_self hs)).1
    have hns : 0 < normSq (u s) := normSq_pos.2 hne
    have hle : (u s).im ^ 2 ≤ normSq (u s) := by
      rw [normSq_apply]; nlinarith [sq_nonneg (u s).re]
    have e : 2 * (u s).im * (-2 * (u s).im / normSq (u s)) = -4 * ((u s).im ^ 2 / normSq (u s)) := by
      ring
    have h1 : (u s).im ^ 2 / normSq (u s) ≤ 1 := (div_le_one hns).2 hle
    rw [e]
    linarith

/-- `(Im f_t(z))² ≥ (Im z)² − 4t` while `z` is unswallowed. -/
theorem im_fwdMap_sq_ge (hW : Continuous W) (hz : 0 < z.im) {t : ℝ} (ht : 0 ≤ t)
    (hsol : IsForwardSol W z t u) : z.im ^ 2 - 4 * t ≤ (fwdMap W t z).im ^ 2 := by
  have hmono := monotoneOn_im_sq_add_four_mul hsol
  have h0 : (u 0).im = z.im := by
    rw [((hsol.2 0 ⟨le_rfl, ht⟩).2)]; simp
  have := hmono ⟨le_rfl, ht⟩ ⟨ht, le_rfl⟩ ht
  rw [QuantumZipper.fwdMap_eq hW hz hsol ⟨ht, le_rfl⟩]
  simp only [h0, mul_zero, add_zero] at this
  linarith

/-- **The height bound**: if `4T < (Im z)²`, then `z` is not swallowed by time `T`. -/
theorem notMem_fwdHull_of_four_mul_lt_im_sq (hW : Continuous W) (hz : 0 < z.im)
    (h : 4 * T < z.im ^ 2) : z ∉ fwdHull W T := by
  intro hK
  obtain ⟨-, σ, hσT, hσ, hc⟩ := (QuantumZipper.FwdClock.mem_fwdHull_iff_inf_im hW).1 hK
  set c := Real.sqrt (z.im ^ 2 - 4 * T) with hcdef
  have hc0 : 0 < c := Real.sqrt_pos.2 (by linarith)
  obtain ⟨t, ht0, htσ, hlt⟩ := hc c hc0
  have hσ0 : 0 < σ := lt_of_le_of_lt ht0 htσ
  have hlt' : ENNReal.ofReal t < swallowTime W z := by
    rw [hσ]; exact (ENNReal.ofReal_lt_ofReal_iff hσ0).2 htσ
  obtain ⟨u, hu⟩ := QuantumZipper.exists_isForwardSol_of_not_mem_fwdHull ht0 hz
    (fun h' => (not_le.2 hlt') h'.2)
  have hsq := im_fwdMap_sq_ge hW hz ht0 hu
  have hpos : 0 < (fwdMap W t z).im := by
    rw [QuantumZipper.fwdMap_eq hW hz hu ⟨ht0, le_rfl⟩]
    exact (QuantumZipper.im_isForwardSol_le hW hz hu).2 t ⟨ht0, le_rfl⟩
  have hc2 : c ^ 2 = z.im ^ 2 - 4 * T := Real.sq_sqrt (by linarith)
  have : c ^ 2 ≤ (fwdMap W t z).im ^ 2 := by
    rw [hc2]; linarith [htσ.le.trans hσT]
  have hcx : c ≤ (fwdMap W t z).im := by nlinarith
  linarith

/-- Every point of the hull `K_T` has `Im z ≤ 2√T`. -/
theorem im_le_two_mul_sqrt_of_mem_fwdHull (hW : Continuous W) (hT : 0 ≤ T) (hK : z ∈ fwdHull W T) :
    z.im ≤ 2 * Real.sqrt T := by
  have hz : 0 < z.im := hK.1
  by_contra hlt
  push Not at hlt
  refine notMem_fwdHull_of_four_mul_lt_im_sq hW hz ?_ hK
  have h2 : (2 * Real.sqrt T) ^ 2 = 4 * T := by rw [mul_pow, Real.sq_sqrt hT]; norm_num
  rw [← h2]
  exact pow_lt_pow_left₀ hlt (by positivity) two_ne_zero

/-- Aux. lemmas 117 and 122: `z = iY` with `Y² > 4t₀` is not swallowed by the horizon `t₀`. -/
theorem I_mul_notMem_fwdHull (hW : Continuous W) {Y t₀ : ℝ} (hY : 0 < Y)
    (h : 4 * t₀ < Y ^ 2) : I * Y ∉ fwdHull W t₀ := by
  have him : (I * (Y : ℂ)).im = Y := by simp
  exact notMem_fwdHull_of_four_mul_lt_im_sq hW (by rw [him]; exact hY) (by rw [him]; exact h)

end Sec7

end InteractingSLE
