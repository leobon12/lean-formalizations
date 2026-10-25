import SupercriticalLQGUniqueness.Uniqueness.Objects.Tube.Polar




 












set_option autoImplicit false

noncomputable section

open Complex Set Metric Real

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Tube

 
def InSector (x : ℂ) (m a b : ℝ) : Prop := ∃ R, m ≤ R ∧ ∃ φ ∈ Icc a b, x = pol R φ

theorem InSector.mono {x : ℂ} {m a b m' a' b' : ℝ} (h : InSector x m a b) (hm : m' ≤ m)
    (ha : a' ≤ a) (hb : b ≤ b') : InSector x m' a' b' := by
  obtain ⟨R, hR, φ, hφ, rfl⟩ := h
  exact ⟨R, hm.trans hR, φ, ⟨ha.trans hφ.1, hφ.2.trans hb⟩, rfl⟩

theorem InSector.norm_ge {x : ℂ} {m a b : ℝ} (h : InSector x m a b) (hm : 0 ≤ m) : m ≤ ‖x‖ := by
  obtain ⟨R, hR, φ, -, rfl⟩ := h
  rw [norm_pol (hm.trans hR)]; exact hR

 
theorem InSector.add_two_pi {x : ℂ} {m a b : ℝ} (h : InSector x m a b) (j : ℤ) :
    InSector x m (a + j * (2 * π)) (b + j * (2 * π)) := by
  obtain ⟨R, hR, φ, hφ, rfl⟩ := h
  refine ⟨R, hR, φ + j * (2 * π), ⟨by linarith [hφ.1], by linarith [hφ.2]⟩, ?_⟩
  unfold pol; rw [ex_add_int_mul_two_pi]

 
theorem one_sub_cos_ge {γ : ℝ} (h0 : 0 ≤ γ) (hπ : γ ≤ π) : 2 * γ ^ 2 / π ^ 2 ≤ 1 - Real.cos γ := by
  have hπ0 : 0 < π := Real.pi_pos
  have hs : γ / π ≤ Real.sin (γ / 2) := by
    have := Real.mul_le_sin (x := γ / 2) (by linarith) (by linarith)
    calc γ / π = 2 / π * (γ / 2) := by field_simp
      _ ≤ Real.sin (γ / 2) := this
  have hc : Real.cos γ = 1 - 2 * Real.sin (γ / 2) ^ 2 := by
    have e : Real.cos γ = Real.cos (2 * (γ / 2)) := by ring_nf
    rw [e, Real.cos_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq (γ / 2)]
  have hγπ : 0 ≤ γ / π := div_nonneg h0 hπ0.le
  have hsq : (γ / π) ^ 2 ≤ Real.sin (γ / 2) ^ 2 := pow_le_pow_left₀ hγπ hs 2
  have e2 : 2 * γ ^ 2 / π ^ 2 = 2 * (γ / π) ^ 2 := by rw [div_pow]; ring
  rw [hc, e2]
  linarith

 
theorem cos_le_cos_of_mem {γ δ : ℝ} (h0 : 0 ≤ γ) (h1 : γ ≤ δ) (h2 : δ ≤ 2 * π - γ) :
    Real.cos δ ≤ Real.cos γ := by
  rcases le_total δ π with h | h
  · exact Real.cos_le_cos_of_nonneg_of_le_pi h0 h h1
  · have : Real.cos δ = Real.cos (2 * π - δ) := by
      rw [Real.cos_two_pi_sub]
    rw [this]
    exact Real.cos_le_cos_of_nonneg_of_le_pi h0 (by linarith) (by linarith)

 
theorem dist_ge_of_sectors {x y : ℂ} {m a b c d γ : ℝ} (hm : 0 ≤ m) (hx : InSector x m a b)
    (hy : InSector y m c d) (hγ0 : 0 ≤ γ) (hγπ : γ ≤ π) (h1 : γ ≤ c - b)
    (h2 : γ ≤ a + 2 * π - d) : 2 * m * γ / π ≤ dist x y := by
  obtain ⟨R, hR, φ, hφ, rfl⟩ := hx
  obtain ⟨S, hS, ψ, hψ, rfl⟩ := hy
  have hR0 : 0 ≤ R := hm.trans hR
  have hS0 : 0 ≤ S := hm.trans hS
  have hcos : Real.cos (φ - ψ) ≤ Real.cos γ := by
    rw [← Real.cos_neg, neg_sub]
    exact cos_le_cos_of_mem hγ0 (by linarith [hφ.2, hψ.1]) (by linarith [hφ.1, hψ.2])
  have hsq := normSq_pol_sub R S φ ψ
  have hc1 := one_sub_cos_ge hγ0 hγπ
  have hπ0 : 0 < π := Real.pi_pos
  have key : (2 * m * γ / π) ^ 2 ≤ ‖pol R φ - pol S ψ‖ ^ 2 := by
    rw [hsq]
    have hRS : m * m ≤ R * S := mul_le_mul hR hS hm hR0
    have e1 : (2 * m * γ / π) ^ 2 = 2 * m ^ 2 * (2 * γ ^ 2 / π ^ 2) := by
      field_simp
    rw [e1]
    have h3 : 2 * m ^ 2 * (2 * γ ^ 2 / π ^ 2) ≤ 2 * (R * S) * (1 - Real.cos γ) := by
      have hpos : 0 ≤ 2 * γ ^ 2 / π ^ 2 := by positivity
      have : m ^ 2 ≤ R * S := by nlinarith
      calc 2 * m ^ 2 * (2 * γ ^ 2 / π ^ 2) ≤ 2 * (R * S) * (2 * γ ^ 2 / π ^ 2) := by
            apply mul_le_mul_of_nonneg_right _ hpos; linarith
        _ ≤ 2 * (R * S) * (1 - Real.cos γ) := by
            apply mul_le_mul_of_nonneg_left hc1; positivity
    nlinarith [sq_nonneg (R - S), mul_nonneg hR0 hS0]
  have hpos : 0 ≤ 2 * m * γ / π := by positivity
  rw [Complex.dist_eq]
  nlinarith [norm_nonneg (pol R φ - pol S ψ)]

 
theorem abs_arctan_le (t : ℝ) : |Real.arctan t| ≤ |t| := by
  have key : ∀ u : ℝ, 0 ≤ u → Real.arctan u ≤ u := by
    intro u hu
    have h0 : 0 ≤ Real.arctan u := Real.arctan_nonneg.mpr hu
    have h1 := Real.le_tan h0 (Real.arctan_lt_pi_div_two u)
    rwa [Real.tan_arctan] at h1
  rcases le_total 0 t with h | h
  · rw [abs_of_nonneg (Real.arctan_nonneg.mpr h), abs_of_nonneg h]; exact key t h
  · rw [abs_of_nonpos (Real.arctan_le_zero.mpr h), abs_of_nonpos h]
    have := key (-t) (by linarith)
    rw [Real.arctan_neg] at this; linarith

 
theorem arg_eq_arctan {w : ℂ} (hre : 0 < w.re) : Complex.arg w = Real.arctan (w.im / w.re) := by
  have habs : |Complex.arg w| < π / 2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre)
  rw [← Complex.tan_arg, Real.arctan_tan (by linarith [neg_abs_le (Complex.arg w)])
    (by linarith [le_abs_self (Complex.arg w)])]

theorem pol_norm_arg (w : ℂ) : pol ‖w‖ (Complex.arg w) = w := by
  unfold pol ex; exact Complex.norm_mul_exp_arg_mul_I w

 
theorem inSector_of_re_im {w : ℂ} {h : ℝ} (hh0 : 0 ≤ h) (hh : h < π / 2) (hre : 0 < w.re)
    (him : |w.im| ≤ Real.tan h * w.re) : InSector w w.re (-h) h := by
  refine ⟨‖w‖, Complex.re_le_norm w, Complex.arg w, ?_, (pol_norm_arg w).symm⟩
  rw [arg_eq_arctan hre]
  have hq : |w.im / w.re| ≤ Real.tan h := by
    rw [abs_div, abs_of_pos hre, div_le_iff₀ hre]; exact him
  have hth : Real.arctan (Real.tan h) = h := Real.arctan_tan (by linarith) hh
  constructor
  · have := Real.arctan_mono (neg_le_of_abs_le hq)
    rw [Real.arctan_neg, hth] at this; exact this
  · have := Real.arctan_mono (le_of_abs_le hq)
    rwa [hth] at this

 

theorem inSector_of_near {x : ℂ} {R θ ε : ℝ} (hR : 0 < R) (hε : 0 ≤ ε) (h2 : 2 * ε ≤ R)
    (hx : dist x (pol R θ) ≤ ε) : InSector x (R - ε) (θ - 2 * ε / R) (θ + 2 * ε / R) := by
  set w := ex (-θ) * x with hw
  have hpol : ex (-θ) * pol R θ = (R : ℂ) := by
    rw [ex_mul_pol, add_neg_cancel, pol_zero_right]
  have hwR : ‖w - R‖ ≤ ε := by
    rw [hw, ← hpol, ← mul_sub, norm_mul, norm_ex, one_mul, ← Complex.dist_eq]; exact hx
  have hre : R - ε ≤ w.re := by
    have := Complex.abs_re_le_norm (w - R)
    rw [Complex.sub_re, Complex.ofReal_re] at this
    linarith [neg_abs_le (w.re - R)]
  have him : |w.im| ≤ ε := by
    have := Complex.abs_im_le_norm (w - R)
    rw [Complex.sub_im, Complex.ofReal_im, sub_zero] at this
    linarith
  have hre0 : 0 < w.re := by linarith
  have harg : |Complex.arg w| ≤ 2 * ε / R := by
    rw [arg_eq_arctan hre0]
    refine (abs_arctan_le _).trans ?_
    rw [abs_div, abs_of_pos hre0, div_le_div_iff₀ hre0 hR]
    nlinarith [abs_nonneg w.im]
  have hxw : x = ex θ * w := by
    rw [hw, ← mul_assoc, ← ex_add, add_neg_cancel, ex_zero, one_mul]
  have hnorm : ‖x‖ = ‖w‖ := by rw [hxw, norm_mul, norm_ex, one_mul]
  refine ⟨‖x‖, ?_, θ + Complex.arg w, ⟨?_, ?_⟩, ?_⟩
  · rw [hnorm]; exact hre.trans (Complex.re_le_norm w)
  · linarith [neg_abs_le (Complex.arg w)]
  · linarith [le_abs_self (Complex.arg w)]
  · rw [hnorm, hxw, show θ + Complex.arg w = Complex.arg w + θ by ring, ← ex_mul_pol,
      pol_norm_arg]

end SupercriticalLQGUniqueness.Uniqueness.Objects.Tube
