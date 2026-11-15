import InteractingSLE.Foundations.Loewner.RealPoints

/-!
# Section 6.2: the derivative-argument lift at untouched real points, (CA2)

Specification §6.2, proof of **Aux. lemma 45** (`source/spec/p193-240.md`, p. 214, (CA2)): "At a
real point `x` outside that crosscut's base interval, the usual Loewner maps satisfy
`d/dt log g_t'(x) = −2/(g_t(x) − W_t)²`, `log g_0'(x) = 0`. Thus the logarithm of the derivative,
normalized at infinity, has imaginary part exactly zero at every such point."

For a Loewner chain with continuous driver `W` (QuantumZipper conventions: `f_t = g_t − W_t` is
`fwdMap W t`, and `logDerivFwd W T z = −∫₀ᵀ 2/f_s(z)² ds` is the branch of `log f_T'(z)` vanishing
at `T = 0` and at `∞`), this file proves the boundary statement:

* `tendsto_logDerivFwd_of_isForwardSol`: if the centred flow has a solution `u` on `[0, T]` from a
  point `p ∈ ℍ̄` (for a real `p`: `p` is not swallowed by time `T`), then
  `log f_T'(z) → −∫₀ᵀ 2/u(s)² ds` as `z → p` in `ℍ`;
* `tendsto_im_logDerivFwd_of_isForwardSol_real`: **(CA2)** for a real starting point the limit is
  real, so `Im log f_T'(z) → 0` as `z → x`: the normalized argument of `f_T'` vanishes at every
  untouched real point.

The rest of Aux. lemma 45 (the crosscut decomposition of a general hull, kernel limits (CA3), and
the Jordan-coordinate conjugation) is not formalized here; see the handoff of PROVE-SEC6-B.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology

open QuantumZipper (H)

namespace InteractingSLE.Sec6

/-- `‖2/a² − 2/b²‖ ≤ 2(2M + δ)/δ⁴ · ‖a − b‖` when `‖a‖, ‖b‖ ≥ δ`, `‖b‖ ≤ M` and `‖a − b‖ ≤ δ`. -/
theorem norm_two_div_sq_sub_le {a b : ℂ} {δ M : ℝ} (hδ : 0 < δ) (ha : δ ≤ ‖a‖) (hb : δ ≤ ‖b‖)
    (hbM : ‖b‖ ≤ M) (hab : ‖a - b‖ ≤ δ) :
    ‖2 / a ^ 2 - 2 / b ^ 2‖ ≤ 2 * (2 * M + δ) / δ ^ 4 * ‖a - b‖ := by
  have ha0 : a ≠ 0 := norm_pos_iff.1 (hδ.trans_le ha)
  have hb0 : b ≠ 0 := norm_pos_iff.1 (hδ.trans_le hb)
  have heq : 2 / a ^ 2 - 2 / b ^ 2 = 2 * (b - a) * (b + a) / (a ^ 2 * b ^ 2) := by
    field_simp; ring
  have hsum : ‖b + a‖ ≤ 2 * M + δ := by
    have h1 : ‖a‖ ≤ ‖b‖ + ‖a - b‖ := by
      have := norm_add_le (a - b) b
      rw [sub_add_cancel] at this; linarith
    have := norm_add_le b a
    linarith
  have hden : δ ^ 4 ≤ ‖a ^ 2 * b ^ 2‖ := by
    rw [norm_mul, norm_pow, norm_pow]
    have h1 : δ ^ 2 ≤ ‖a‖ ^ 2 := pow_le_pow_left₀ hδ.le ha 2
    have h2 : δ ^ 2 ≤ ‖b‖ ^ 2 := pow_le_pow_left₀ hδ.le hb 2
    calc δ ^ 4 = δ ^ 2 * δ ^ 2 := by ring
      _ ≤ ‖a‖ ^ 2 * ‖b‖ ^ 2 := mul_le_mul h1 h2 (by positivity) (by positivity)
  rw [heq, norm_div, norm_mul, norm_mul, div_le_iff₀ (lt_of_lt_of_le (by positivity) hden)]
  have hn2 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [hn2, norm_sub_rev b a]
  have hM : 0 ≤ 2 * M + δ := (norm_nonneg _).trans hsum
  calc 2 * ‖a - b‖ * ‖b + a‖ ≤ 2 * ‖a - b‖ * (2 * M + δ) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 2 * (2 * M + δ) / δ ^ 4 * ‖a - b‖ * δ ^ 4 := by field_simp
    _ ≤ 2 * (2 * M + δ) / δ ^ 4 * ‖a - b‖ * ‖a ^ 2 * b ^ 2‖ :=
        mul_le_mul_of_nonneg_left hden (by positivity)

variable {W : ℝ → ℝ}

/-- **Boundary values of the normalized `log f_T'`** at the starting point `p ∈ ℍ̄` of a solution of
the centred Loewner flow on `[0, T]`: `logDerivFwd W T z → −∫₀ᵀ 2/u(s)² ds` as `z → p` in `ℍ`. For
`z` near `p` the solution from `z` stays uniformly close to `u` (`norm_sub_le_of_isForwardSol`), so
the integrands `2/f_s(z)²` converge uniformly on `[0, T]`. -/
theorem tendsto_logDerivFwd_of_isForwardSol (hW : Continuous W) {p : ℂ} {T : ℝ} {u : ℝ → ℂ}
    (hT : 0 ≤ T) (hu : QuantumZipper.IsForwardSol W p T u) :
    Tendsto (QuantumZipper.logDerivFwd W T) (𝓝[H] p)
      (𝓝 (-∫ s in (0 : ℝ)..T, 2 / (u s) ^ 2)) := by
  obtain ⟨δ, hδ, hlow⟩ := exists_two_mul_le_norm_of_isForwardSol hT hu
  obtain ⟨M, hM⟩ : ∃ M, ∀ s ∈ Icc (0 : ℝ) T, ‖u s‖ ≤ M := by
    obtain ⟨M, hM⟩ := (isCompact_Icc.image_of_continuousOn hu.1).isBounded.exists_norm_le
    exact ⟨M, fun s hs => hM _ (mem_image_of_mem u hs)⟩
  set E := Real.exp (2 / δ ^ 2 * T) with hEdef
  have hE : 0 < E := Real.exp_pos _
  set C := 2 * (2 * M + δ) / δ ^ 4 with hCdef
  have hC : 0 ≤ C := by
    have : 0 ≤ M := (norm_nonneg _).trans (hM 0 ⟨le_rfl, hT⟩)
    positivity
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  set η := min (δ / 2) (ε / ((C + 1) * (T + 1))) with hηdef
  have hη : 0 < η := lt_min (half_pos hδ) (by positivity)
  refine ⟨η / E, div_pos hη hE, fun z hz hzd => ?_⟩
  rw [dist_eq_norm] at hzd
  have hzp : ‖z - p‖ * E < η := by rwa [lt_div_iff₀ hE] at hzd
  have hzp' : ‖z - p‖ * E < δ := hzp.trans_le ((min_le_left _ _).trans (by linarith))
  have hz0 : 0 < z.im := hz
  have hzK := not_mem_fwdHull_of_isForwardSol hW hu hδ hlow hz0 hzp'
  obtain ⟨v, hv⟩ := QuantumZipper.exists_isForwardSol_of_not_mem_fwdHull hT hz0 hzK
  have hb := norm_sub_le_of_isForwardSol hW hu hv hδ hT le_rfl hlow hzp'
  -- uniform closeness on `[0, T]`
  have hclose : ∀ s ∈ Icc (0 : ℝ) T, ‖v s - u s‖ ≤ η := fun s hs =>
    ((hb s hs).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2
      (mul_le_mul_of_nonneg_left hs.2 (by positivity))) (norm_nonneg _))).trans hzp.le
  have hcongr : EqOn (fun s => 2 / (QuantumZipper.fwdMap W s z) ^ 2) (fun s => 2 / (v s) ^ 2)
      (uIcc 0 T) := by
    intro s hs
    rw [uIcc_of_le hT] at hs
    simp only [QuantumZipper.fwdMap_eq hW hz0 hv hs]
  have hL : QuantumZipper.logDerivFwd W T z = -∫ s in (0 : ℝ)..T, 2 / (v s) ^ 2 := by
    rw [QuantumZipper.logDerivFwd, intervalIntegral.integral_congr hcongr]
  have hint : ∀ w : ℝ → ℂ, ContinuousOn w (Icc 0 T) → (∀ s ∈ Icc (0 : ℝ) T, w s ≠ 0) →
      IntervalIntegrable (fun s => 2 / (w s) ^ 2) MeasureTheory.volume 0 T := by
    intro w hwc hw0
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hT]
    exact continuousOn_const.div (hwc.pow 2) fun s hs => pow_ne_zero 2 (hw0 s hs)
  have hbound : ∀ s ∈ uIoc (0 : ℝ) T, ‖2 / (u s) ^ 2 - 2 / (v s) ^ 2‖ ≤ C * η := by
    intro s hs
    rw [uIoc_of_le hT] at hs
    have hs' : s ∈ Icc (0 : ℝ) T := ⟨hs.1.le, hs.2⟩
    have hcl := hclose s hs'
    have hηδ : η ≤ δ / 2 := min_le_left _ _
    have hus := hlow s hs'
    have hvs : δ ≤ ‖v s‖ := by
      have := norm_sub_norm_le (u s) (v s)
      rw [norm_sub_rev] at this
      linarith
    rw [norm_sub_rev]
    exact (norm_two_div_sq_sub_le hδ hvs (by linarith) (hM s hs') (by linarith)).trans
      (mul_le_mul_of_nonneg_left hcl hC)
  rw [dist_eq_norm, hL, neg_sub_neg, ← intervalIntegral.integral_sub
    (hint u hu.1 fun s hs => (hu.2 s hs).1) (hint v hv.1 fun s hs => (hv.2 s hs).1)]
  refine (intervalIntegral.norm_integral_le_of_norm_le_const hbound).trans_lt ?_
  rw [sub_zero, abs_of_nonneg hT]
  have h1 : η * ((C + 1) * (T + 1)) ≤ ε := by
    rw [← le_div_iff₀ (by positivity)]; exact min_le_right _ _
  nlinarith [mul_nonneg hη.le hC, mul_nonneg hη.le hT]

/-- **(CA2) of Aux. lemma 45** (Specification p. 214): at a real point `x` from which the centred
Loewner flow has a solution on `[0, T]` (a real point not swallowed by time `T`), the normalized
argument of `f_T'` vanishes: `Im log f_T'(z) → 0` as `z → x` in `ℍ`. The limit
`−∫₀ᵀ 2/u(s)² ds` of `tendsto_logDerivFwd_of_isForwardSol` is real because `u` is real
(`im_eq_zero_of_isForwardSol_real`). -/
theorem tendsto_im_logDerivFwd_of_isForwardSol_real (hW : Continuous W) {x T : ℝ} {u : ℝ → ℂ}
    (hT : 0 ≤ T) (hu : QuantumZipper.IsForwardSol W x T u) :
    Tendsto (fun z => (QuantumZipper.logDerivFwd W T z).im) (𝓝[H] (x : ℂ)) (𝓝 0) := by
  have hlim := (Complex.continuous_im.tendsto _).comp (tendsto_logDerivFwd_of_isForwardSol hW hT hu)
  have hreal : EqOn (fun s => 2 / (u s) ^ 2) (fun s => ((2 / (u s).re ^ 2 : ℝ) : ℂ))
      (uIcc 0 T) := by
    intro s hs
    rw [uIcc_of_le hT] at hs
    have hu' : u s = ((u s).re : ℂ) :=
      Complex.ext (by simp) (by simp [im_eq_zero_of_isForwardSol_real hW hu hs])
    simp only
    rw [hu']
    push_cast
    simp
  have h0 : (-∫ s in (0 : ℝ)..T, 2 / (u s) ^ 2).im = 0 := by
    rw [intervalIntegral.integral_congr hreal, intervalIntegral.integral_ofReal]
    simp
  rw [h0] at hlim
  exact hlim

end InteractingSLE.Sec6
