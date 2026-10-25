import SupercriticalLQGUniqueness.Uniqueness.Objects.CorrectedEvent.EventPredicate




 















set_option autoImplicit false

noncomputable section

open Set Metric

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.AnnulusTails

 
def gridBoxFinset (a : ℝ) (N : ℕ) : Finset ℂ :=
  ((Finset.Icc (-(N : ℤ)) N) ×ˢ (Finset.Icc (-(N : ℤ)) N)).image
    (fun p : ℤ × ℤ => ((a * p.1 : ℝ) : ℂ) + ((a * p.2 : ℝ) : ℂ) * Complex.I)

theorem card_gridBoxFinset_le (a : ℝ) (N : ℕ) : (gridBoxFinset a N).card ≤ (2 * N + 1) ^ 2 := by
  unfold gridBoxFinset
  refine Finset.card_image_le.trans ?_
  rw [Finset.card_product, Int.card_Icc, sq]
  have : ((N : ℤ) + 1 - -(N : ℤ)).toNat = 2 * N + 1 := by omega
  rw [this]

 
theorem grid_inter_closedBall_subset {a ρ : ℝ} (ha : 0 < a) :
    Objects.CorrectedEvent.grid a ∩ closedBall 0 ρ ⊆ ↑(gridBoxFinset a ⌈ρ / a⌉₊) := by
  rintro z ⟨⟨m, n, rfl⟩, hz⟩
  rw [mem_closedBall, dist_zero_right] at hz
  have hre : |a * m| ≤ ρ := by
    have h := Complex.abs_re_le_norm (((a * m : ℝ) : ℂ) + ((a * n : ℝ) : ℂ) * Complex.I)
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, sub_zero, add_zero, mul_one] at h
    linarith
  have him : |a * n| ≤ ρ := by
    have h := Complex.abs_im_le_norm (((a * m : ℝ) : ℂ) + ((a * n : ℝ) : ℂ) * Complex.I)
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, mul_zero, add_zero, zero_add, mul_one] at h
    linarith
  have hbound : ∀ k : ℤ, |a * k| ≤ ρ → -(⌈ρ / a⌉₊ : ℤ) ≤ k ∧ k ≤ ⌈ρ / a⌉₊ := by
    intro k hk
    rw [abs_mul, abs_of_pos ha] at hk
    have hk' : |(k : ℝ)| ≤ ρ / a := by rw [le_div_iff₀ ha]; linarith
    have hc := Nat.le_ceil (ρ / a)
    have h2 := abs_le.1 (hk'.trans hc)
    constructor
    · have : (-(⌈ρ / a⌉₊ : ℝ)) ≤ (k : ℝ) := by linarith [h2.1]
      exact_mod_cast this
    · have : (k : ℝ) ≤ (⌈ρ / a⌉₊ : ℝ) := h2.2
      exact_mod_cast this
  refine Finset.mem_coe.2 (Finset.mem_image.2 ⟨(m, n), ?_, rfl⟩)
  rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
  exact ⟨hbound m hre, hbound n him⟩

 
theorem norm_le_of_infDist_cann_le {z : ℂ} {a c d : ℝ} (hc : 0 ≤ c) (hcd : c ≤ d)
    (hz : infDist z (Objects.CorrectedEvent.cann 0 c d) ≤ a) : ‖z‖ ≤ d + a := by
  have hne : (Objects.CorrectedEvent.cann 0 c d).Nonempty := ⟨(d : ℂ), by
    change c ≤ dist (d : ℂ) 0 ∧ dist (d : ℂ) 0 ≤ d
    rw [dist_zero_right, Complex.norm_real, Real.norm_of_nonneg (hc.trans hcd)]
    exact ⟨hcd, le_rfl⟩⟩
  have hle : ‖z‖ - d ≤ infDist z (Objects.CorrectedEvent.cann 0 c d) := by
    rw [le_infDist hne]
    intro k hk
    have hk' : dist k 0 ≤ d := hk.2
    rw [dist_zero_right] at hk'
    have := norm_le_norm_add_norm_sub' z k
    rw [dist_eq_norm]
    have h3 : ‖z‖ ≤ ‖k‖ + ‖z - k‖ := by
      calc ‖z‖ = ‖k + (z - k)‖ := by ring_nf
        _ ≤ ‖k‖ + ‖z - k‖ := norm_add_le _ _
    linarith
  linarith

end SupercriticalLQGUniqueness.Uniqueness.Objects.AnnulusTails
