import SupercriticalLQGUniqueness.Uniqueness.Objects.BlockMarginal.S4Arcs




 









set_option autoImplicit false

noncomputable section

open Set Metric Filter Real
open scoped Topology

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.BlockMarginal

 
def blockSite (T : Objects.CorrectedEvent.TubeData) (m i t : ℕ) : ℂ :=
  Objects.CorrectedEvent.site T ⟨(blockStart T.K m i + t) % T.K, Nat.mod_lt _ T.Kpos⟩

theorem blockSites_eq (T : Objects.CorrectedEvent.TubeData) (m i N : ℕ) :
    blockSites T m i N = (Finset.range N).image (blockSite T m i) := by
  unfold blockSites blockIdx
  rw [Finset.image_image]
  rfl

theorem norm_two_exp_sub (R a b : ℝ) (hR : 0 ≤ R) :
    ‖((R : ℝ) : ℂ) * Complex.exp ((a : ℂ) * Complex.I) -
        ((R : ℝ) : ℂ) * Complex.exp ((b : ℂ) * Complex.I)‖ =
      R * ‖2 * Real.sin ((a - b) / 2)‖ := by
  have h : ((R : ℝ) : ℂ) * Complex.exp ((a : ℂ) * Complex.I) -
      ((R : ℝ) : ℂ) * Complex.exp ((b : ℂ) * Complex.I) =
      ((R : ℝ) : ℂ) * Complex.exp ((b : ℂ) * Complex.I) *
        (Complex.exp (Complex.I * ((a - b : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, mul_assoc, ← Complex.exp_add]
    congr 3
    push_cast
    ring
  rw [h, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hR,
    Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_exp_I_mul_ofReal_sub_one]

 
theorem abs_two_sin_ge {x : ℝ} (hx : |x| ≤ π / 2) : 4 / π * |x| ≤ ‖2 * Real.sin x‖ := by
  have hπ := Real.pi_pos
  have hJ := Real.mul_le_sin (abs_nonneg x) hx
  have hsin : Real.sin |x| = |Real.sin x| := by
    rcases le_or_gt 0 x with h0 | h0
    · rw [abs_of_nonneg h0, abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi h0
        (by linarith [abs_of_nonneg h0 ▸ hx]))]
    · rw [abs_of_neg h0, Real.sin_neg, abs_of_nonpos]
      have : 0 ≤ Real.sin (-x) :=
        Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [abs_of_neg h0 ▸ hx])
      rw [Real.sin_neg] at this
      linarith
  rw [Real.norm_eq_abs, abs_mul, abs_two, ← hsin]
  have : 4 / π * |x| = 2 * (2 / π * |x|) := by ring
  linarith

 
theorem blockSite_sep (T : Objects.CorrectedEvent.TubeData) (hr : 0 < T.r) (Asp : ℝ) (hA : 0 < Asp) (hA1 : Asp ≤ 1)
    {N : ℕ} (hN : N ≤ blockCount T.K Asp) (m i : ℕ) {t t' : ℕ} (ht : t < N) (ht' : t' < N)
    (htt : t ≠ t') : 8 * T.r / T.K ≤ ‖blockSite T m i t - blockSite T m i t'‖ := by
  have hK : (0 : ℝ) < T.K := by exact_mod_cast T.Kpos
  have hπ := Real.pi_pos
  have hNle : (N : ℝ) ≤ T.K * Asp / (16 * π) :=
    (Nat.cast_le.2 hN).trans (Nat.floor_le (by positivity))
  unfold blockSite
  rw [site_eq_exp, site_eq_exp, norm_two_exp_sub _ _ _ (by linarith)]
  set x : ℝ := (2 * π * ((blockStart T.K m i + t : ℕ) : ℝ) / T.K -
    2 * π * ((blockStart T.K m i + t' : ℕ) : ℝ) / T.K) / 2 with hx
  have hxe : x = π * ((t : ℝ) - t') / T.K := by
    rw [hx]; push_cast; field_simp; ring
  have hdiff : (1 : ℝ) ≤ |(t : ℝ) - t'| := by
    rcases lt_or_gt_of_ne htt with h | h
    · have : (t : ℝ) + 1 ≤ t' := by exact_mod_cast h
      rw [abs_of_neg (by linarith)]; linarith
    · have : (t' : ℝ) + 1 ≤ t := by exact_mod_cast h
      rw [abs_of_pos (by linarith)]; linarith
  have hdiffN : |(t : ℝ) - t'| ≤ N := by
    have h1 : (t : ℝ) < N := by exact_mod_cast ht
    have h2 : (t' : ℝ) < N := by exact_mod_cast ht'
    rw [abs_le]; constructor <;> linarith [Nat.cast_nonneg (α := ℝ) t, Nat.cast_nonneg (α := ℝ) t']
  have habsx : |x| = π * |(t : ℝ) - t'| / T.K := by
    rw [hxe, abs_div, abs_mul, abs_of_pos hπ, abs_of_pos hK]
  have hxsmall : |x| ≤ π / 2 := by
    rw [habsx, div_le_iff₀ hK]
    have h1 : π * |(t : ℝ) - t'| ≤ π * N := mul_le_mul_of_nonneg_left hdiffN hπ.le
    have h2 : π * (N : ℝ) ≤ π * (T.K * Asp / (16 * π)) := mul_le_mul_of_nonneg_left hNle hπ.le
    have e : π * (T.K * Asp / (16 * π)) = T.K * Asp / 16 := by field_simp
    have h3 : (T.K : ℝ) * Asp ≤ T.K := mul_le_of_le_one_right hK.le hA1
    have h4 : (T.K : ℝ) ≤ π / 2 * T.K := by
      have := Real.pi_gt_three
      nlinarith
    linarith
  have hsin := abs_two_sin_ge hxsmall
  have hxlow : π / T.K ≤ |x| := by
    rw [habsx, div_le_div_iff_of_pos_right hK]
    nlinarith
  have h4 : 4 / π * (π / T.K) ≤ 4 / π * |x| := mul_le_mul_of_nonneg_left hxlow (by positivity)
  have e2 : 4 / π * (π / T.K) = 4 / T.K := by field_simp
  rw [e2] at h4
  have h5 : 4 / (T.K : ℝ) ≤ ‖2 * Real.sin x‖ := h4.trans hsin
  have e3 : 8 * T.r / T.K = 2 * T.r * (4 / T.K) := by ring
  rw [e3]
  exact mul_le_mul_of_nonneg_left h5 (by linarith)

 
theorem card_blockSites (T : Objects.CorrectedEvent.TubeData) (hr : 0 < T.r) (Asp : ℝ) (hA : 0 < Asp) (hA1 : Asp ≤ 1)
    {N : ℕ} (hN : N ≤ blockCount T.K Asp) (m i : ℕ) : (blockSites T m i N).card = N := by
  rw [blockSites_eq, Finset.card_image_of_injOn, Finset.card_range]
  intro t ht t' ht' h
  by_contra hne
  have := blockSite_sep T hr Asp hA hA1 hN m i (Finset.mem_range.1 ht) (Finset.mem_range.1 ht') hne
  have hK : (0 : ℝ) < T.K := by exact_mod_cast T.Kpos
  rw [h, sub_self, norm_zero] at this
  have : 0 < 8 * T.r / T.K := by positivity
  linarith

 
theorem blockSites_sep (T : Objects.CorrectedEvent.TubeData) (hr : 0 < T.r) (Asp : ℝ) (hA : 0 < Asp) (hA1 : Asp ≤ 1)
    {N : ℕ} (hN : N ≤ blockCount T.K Asp) (m i : ℕ) :
    ∀ z ∈ blockSites T m i N, ∀ w ∈ blockSites T m i N, z ≠ w → 8 * T.r / T.K ≤ ‖z - w‖ := by
  intro z hz w hw hzw
  rw [blockSites_eq] at hz hw
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hz
  obtain ⟨t', ht', rfl⟩ := Finset.mem_image.1 hw
  have htt : t ≠ t' := fun h => hzw (by rw [h])
  exact blockSite_sep T hr Asp hA hA1 hN m i (Finset.mem_range.1 ht) (Finset.mem_range.1 ht') htt

end SupercriticalLQGUniqueness.Uniqueness.Objects.BlockMarginal
