import InteractingSLE.Foundations.Loewner.YuanCorollary13
import QuantumZipper.Proofs.Thm11.ForwardClock

/-!
# The vertical slit: the Loewner chain of the zero driver

Packet PROVE-YUAN-M1 (used to extend a finite-horizon trace, `YuanCorollary13Finite.lean`). For the
zero driver the centred forward flow is `f_t(z) = √(z² + 4t)` ([Law05] Example 4.12): with the
principal power,

  `slitSol z t = i · (−(z² + 4t))^{1/2}`,

which equals `z` at `t = 0` for `z ∈ ℍ`, solves `ḟ = 2/f`, and vanishes exactly when `z = iy`,
`t = y²/4`. Hence the hull at time `s` is the vertical slit `{iy : 0 < y ≤ 2√s}`
(`mem_fwdHull_zero_iff`).

We also record that the hull at time `t` is determined by solutions on the closed interval
`[0, t]` (`not_mem_fwdHull_iff`): a solution that survives to time `t` survives a little longer.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology

open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv IsForwardSol)

namespace InteractingSLE

namespace YuanCorollary13

/-! ### Hulls are determined on closed intervals -/

/-- A point of `ℍ` is outside `K_t` iff a solution of the centred flow exists on `[0, t]`. -/
theorem not_mem_fwdHull_iff {V : ℝ → ℝ} (hV : Continuous V) {t : ℝ} (ht : 0 ≤ t) {z : ℂ}
    (hz : z ∈ H) : z ∉ fwdHull V t ↔ ∃ u, IsForwardSol V z t u := by
  constructor
  · exact QuantumZipper.exists_isForwardSol_of_not_mem_fwdHull ht hz
  · rintro ⟨u, hu⟩ hK
    have hut : 0 < (u t).im := QuantumZipper.FwdClock.sol_im_pos hV hz hu ⟨ht, le_rfl⟩
    obtain ⟨ε, hε, v, hv⟩ := QuantumZipper.exists_isForwardSol_small
      (W := fun r => V (t + r) - V t) (by fun_prop) hut
    have hglue := QuantumZipper.isForwardSol_glue ht hε.le hu hv
    have h1 := QuantumZipper.ofReal_le_swallowTime (by linarith) ⟨_, hglue⟩
    have h2 : ENNReal.ofReal t < ENNReal.ofReal (t + ε) :=
      (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
    exact absurd (hK.2.trans_lt (h2.trans_le h1)) (lt_irrefl _)

/-- Two drivers that agree on `[0, t]` have the same hull at time `t`. -/
theorem fwdHull_eq_of_eqOn_Icc {V V' : ℝ → ℝ} (hV : Continuous V) (hV' : Continuous V') {t : ℝ}
    (ht : 0 ≤ t) (h : ∀ r ∈ Icc (0 : ℝ) t, V r = V' r) : fwdHull V t = fwdHull V' t := by
  ext z
  by_cases hz : z ∈ H
  · have h1 := not_mem_fwdHull_iff hV ht hz
    have h2 := not_mem_fwdHull_iff hV' ht hz
    constructor
    · intro hK
      by_contra hK'
      obtain ⟨u, hu⟩ := h2.1 hK'
      exact (h1.2 ⟨u, QuantumZipper.isForwardSol_congr_drive (fun r hr => (h r hr).symm) hu⟩) hK
    · intro hK
      by_contra hK'
      obtain ⟨u, hu⟩ := h1.1 hK'
      exact (h2.2 ⟨u, QuantumZipper.isForwardSol_congr_drive h hu⟩) hK
  · exact ⟨fun h' => absurd h'.1 hz, fun h' => absurd h'.1 hz⟩

/-! ### The explicit solution -/

/-- The centred flow of the zero driver: `slitSol z t = i (−(z² + 4t))^{1/2}`. -/
def slitSol (z : ℂ) (t : ℝ) : ℂ := I * (-(z ^ 2 + 4 * (t : ℂ))) ^ ((2 : ℂ)⁻¹)

theorem slitSol_sq (z : ℂ) (t : ℝ) : slitSol z t ^ 2 = z ^ 2 + 4 * (t : ℂ) := by
  rw [slitSol, mul_pow, Complex.cpow_ofNat_inv_pow, I_sq]
  ring

theorem slitSol_ne_zero {z : ℂ} {t : ℝ} (h : z ^ 2 + 4 * (t : ℂ) ≠ 0) : slitSol z t ≠ 0 := by
  intro h0
  apply h
  rw [← slitSol_sq, h0]
  ring

/-- The principal square root of `a²` is `a` when `Re a > 0`. -/
theorem sq_cpow_inv_two {a : ℂ} (ha : 0 < a.re) : (a ^ 2) ^ ((2 : ℂ)⁻¹) = a := by
  have harg : |a.arg| < Real.pi / 2 := Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl ha)
  have him : (Complex.log a * 2).im = 2 * a.arg := by
    simp only [Complex.mul_im, Complex.log_im, Complex.log_re]
    norm_num
    ring
  have h1 : -Real.pi < (Complex.log a * 2).im := by
    rw [him]; linarith [(abs_lt.1 harg).1]
  have h2 : (Complex.log a * 2).im ≤ Real.pi := by
    rw [him]; linarith [(abs_lt.1 harg).2]
  have h := Complex.cpow_mul (x := a) (y := 2) ((2 : ℂ)⁻¹) h1 h2
  rw [show (2 : ℂ) * (2 : ℂ)⁻¹ = 1 by norm_num, Complex.cpow_one] at h
  calc (a ^ 2) ^ (2 : ℂ)⁻¹ = (a ^ (2 : ℂ)) ^ (2 : ℂ)⁻¹ := by rw [Complex.cpow_ofNat]
    _ = a := h.symm

theorem slitSol_zero {z : ℂ} (hz : 0 < z.im) : slitSol z 0 = z := by
  have ha : 0 < (-I * z).re := by simpa using hz
  have hsq : -(z ^ 2 + 4 * ((0 : ℝ) : ℂ)) = (-I * z) ^ 2 := by
    rw [mul_pow, neg_sq, I_sq]; push_cast; ring
  rw [slitSol, hsq, sq_cpow_inv_two ha]
  rw [← mul_assoc, show I * -I = 1 by rw [mul_neg, I_mul_I, neg_neg], one_mul]

/-- The slit-plane condition for `−(z² + 4t)`. -/
theorem neg_sq_add_mem_slitPlane {z : ℂ} (hz : 0 < z.im) {t : ℝ}
    (h : z.re ≠ 0 ∨ 4 * t < z.im ^ 2) : -(z ^ 2 + 4 * (t : ℂ)) ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  rcases h with h | h
  · right
    simp only [neg_im, add_im, sq, mul_im, ofReal_im, ofReal_re, re_ofNat, im_ofNat]
    intro h0
    have : z.re * z.im = 0 := by linarith
    rcases mul_eq_zero.1 this with h' | h'
    · exact h h'
    · linarith
  · by_cases hre : z.re = 0
    · left
      simp only [neg_re, add_re, sq, mul_re, ofReal_im, ofReal_re, re_ofNat, im_ofNat, hre]
      nlinarith
    · right
      simp only [neg_im, add_im, sq, mul_im, ofReal_im, ofReal_re, re_ofNat, im_ofNat]
      intro h0
      have : z.re * z.im = 0 := by linarith
      rcases mul_eq_zero.1 this with h' | h'
      · exact hre h'
      · linarith

/-- `ṡlitSol = 2/slitSol` off the branch cut. -/
theorem hasDerivAt_slitSol {z : ℂ} {t : ℝ} (h : -(z ^ 2 + 4 * (t : ℂ)) ∈ slitPlane) :
    HasDerivAt (slitSol z) (2 / slitSol z t) t := by
  have hf : HasDerivAt (fun w : ℂ => -(z ^ 2 + 4 * w)) (-(4 * 1)) (t : ℂ) :=
    (((hasDerivAt_id (t : ℂ)).const_mul (4 : ℂ)).const_add (z ^ 2)).neg
  have hc := (hf.cpow_const (c := (2 : ℂ)⁻¹) h).const_mul I
  have hr := hc.comp_ofReal
  have hne : (-(z ^ 2 + 4 * (t : ℂ))) ^ ((2 : ℂ)⁻¹) ≠ 0 := by
    intro h0
    have h1 := Complex.cpow_ofNat_inv_pow (-(z ^ 2 + 4 * (t : ℂ))) 2
    rw [h0] at h1
    exact slitPlane_ne_zero h (by rw [← h1]; ring)
  have hval : 2 / slitSol z t = I * ((2 : ℂ)⁻¹ * (-(z ^ 2 + 4 * (t : ℂ))) ^ ((2 : ℂ)⁻¹ - 1) *
      -(4 * 1)) := by
    unfold slitSol
    rw [show (2 : ℂ)⁻¹ - 1 = -(2 : ℂ)⁻¹ by norm_num, Complex.cpow_neg]
    field_simp
    rw [I_sq]
    ring
  rw [hval]
  exact hr

/-- **The explicit forward solution of the zero driver** on `[0, T]` when the branch cut is not
reached: `Re z ≠ 0`, or `z = iy` with `4T < y²`. -/
theorem isForwardSol_slitSol {z : ℂ} (hz : 0 < z.im) {T : ℝ}
    (h : z.re ≠ 0 ∨ 4 * T < z.im ^ 2) :
    IsForwardSol (fun _ => (0 : ℝ)) z T (slitSol z) := by
  have hcut : ∀ t ∈ Icc (0 : ℝ) T, -(z ^ 2 + 4 * (t : ℂ)) ∈ slitPlane := fun t ht =>
    neg_sq_add_mem_slitPlane hz (h.imp id fun h' => by linarith [ht.2])
  have hd : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt (slitSol z) (2 / slitSol z t) t := fun t ht =>
    hasDerivAt_slitSol (hcut t ht)
  have hne : ∀ t ∈ Icc (0 : ℝ) T, slitSol z t ≠ 0 := fun t ht =>
    slitSol_ne_zero fun h0 => slitPlane_ne_zero (hcut t ht) (by rw [h0, neg_zero])
  have hcont : ContinuousOn (slitSol z) (Icc 0 T) := fun t ht =>
    (hd t ht).continuousAt.continuousWithinAt
  refine ⟨hcont, fun t ht => ⟨hne t ht, ?_⟩⟩
  have hsub : uIcc 0 t ⊆ Icc 0 T := by
    rw [uIcc_of_le ht.1]; exact Icc_subset_Icc_right ht.2
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := slitSol z)
    (f' := fun s => 2 / slitSol z s) (fun s hs => hd s (hsub hs))
    ((continuousOn_const.div hcont fun s hs => hne s hs).mono hsub).intervalIntegrable
  rw [hint, slitSol_zero hz]
  simp

/-- `slitSol z t → 0` at the swallowing time `t₀ = y²/4` of `z = iy`. -/
theorem tendsto_slitSol_zero {y : ℝ} :
    Tendsto (slitSol ((y : ℂ) * I)) (𝓝 (y ^ 2 / 4)) (𝓝 0) := by
  have hsq : ∀ t, ‖slitSol ((y : ℂ) * I) t‖ = Real.sqrt |4 * t - y ^ 2| := fun t => by
    rw [← Real.sqrt_sq (norm_nonneg (slitSol ((y : ℂ) * I) t)), ← norm_pow, slitSol_sq]
    congr 1
    have : ((y : ℂ) * I) ^ 2 + 4 * (t : ℂ) = ((4 * t - y ^ 2 : ℝ) : ℂ) := by
      push_cast
      rw [mul_pow, I_sq]
      ring
    rw [this, Complex.norm_real, Real.norm_eq_abs]
  have hc : Continuous (fun t : ℝ => Real.sqrt |4 * t - y ^ 2|) := by fun_prop
  have hlim := hc.tendsto (y ^ 2 / 4)
  rw [show 4 * (y ^ 2 / 4) - y ^ 2 = 0 by ring, abs_zero, Real.sqrt_zero] at hlim
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simpa only [hsq] using hlim

/-! ### The hull of the zero driver -/

/-- **The vertical slit.** For `s ≥ 0` and `z ∈ ℍ`: `z ∈ K_s` (zero driver) iff `Re z = 0` and
`Im z ≤ 2√s`. -/
theorem mem_fwdHull_zero_iff {s : ℝ} (hs : 0 ≤ s) {z : ℂ} (hz : z ∈ H) :
    z ∈ fwdHull (fun _ => (0 : ℝ)) s ↔ z.re = 0 ∧ z.im ≤ 2 * Real.sqrt s := by
  have hz0 : 0 < z.im := hz
  have hc : Continuous (fun _ : ℝ => (0 : ℝ)) := continuous_const
  constructor
  · intro hK
    by_contra hcon
    have hsol : ∃ u, IsForwardSol (fun _ => (0 : ℝ)) z s u := by
      refine ⟨slitSol z, isForwardSol_slitSol hz0 ?_⟩
      by_cases hre : z.re = 0
      · right
        have h1 : 2 * Real.sqrt s < z.im := by
          by_contra hle; exact hcon ⟨hre, not_lt.1 hle⟩
        have h2 : (2 * Real.sqrt s) ^ 2 = 4 * s := by
          rw [mul_pow, Real.sq_sqrt hs]; ring
        nlinarith [Real.sqrt_nonneg s]
      · exact Or.inl hre
    exact (not_mem_fwdHull_iff hc hs hz).2 hsol hK
  · rintro ⟨hre, hle⟩
    by_contra hK
    obtain ⟨u, hu⟩ := (not_mem_fwdHull_iff hc hs hz).1 hK
    set y := z.im with hy
    have hzy : z = (y : ℂ) * I := Complex.ext (by simp [hre]) (by simp [hy])
    set t₀ := y ^ 2 / 4 with ht₀
    have ht₀pos : 0 < t₀ := by positivity
    have ht₀s : t₀ ≤ s := by
      have h1 : y ^ 2 ≤ (2 * Real.sqrt s) ^ 2 := pow_le_pow_left₀ hz0.le hle 2
      rw [mul_pow, Real.sq_sqrt hs] at h1
      rw [ht₀]; linarith
    -- `u = slitSol z` before `t₀`
    have heq : ∀ t ∈ Ico 0 t₀, u t = slitSol z t := by
      intro t ht
      have hsl := isForwardSol_slitSol hz0 (T := t) (Or.inr (by
        have := ht.2; rw [ht₀] at this; linarith))
      have hur := QuantumZipper.isForwardSol_restrict hu ht.1 (ht.2.le.trans ht₀s)
      exact QuantumZipper.isForwardSol_unique hc hz0 hur hsl ⟨ht.1, le_rfl⟩
    have hucont : ContinuousWithinAt u (Icc 0 s) t₀ := hu.1 t₀ ⟨ht₀pos.le, ht₀s⟩
    have hmem : Icc 0 s ∈ 𝓝[<] t₀ := mem_of_superset (Ioo_mem_nhdsLT ht₀pos) fun t ht =>
      ⟨ht.1.le, ht.2.le.trans ht₀s⟩
    have h1 : Tendsto u (𝓝[<] t₀) (𝓝 (u t₀)) :=
      hucont.tendsto.mono_left (nhdsWithin_le_of_mem hmem)
    have h2 : Tendsto u (𝓝[<] t₀) (𝓝 0) := by
      have := (tendsto_slitSol_zero (y := y)).mono_left (nhdsWithin_le_nhds (s := Iio t₀))
      rw [← hzy] at this
      refine this.congr' ?_
      filter_upwards [Ioo_mem_nhdsLT ht₀pos] with t ht
      exact (heq t ⟨ht.1.le, ht.2⟩).symm
    have h3 : u t₀ = 0 := tendsto_nhds_unique h1 h2
    exact (hu.2 t₀ ⟨ht₀pos.le, ht₀s⟩).1 h3

end YuanCorollary13

end InteractingSLE
