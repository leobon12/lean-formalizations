import SupercriticalLQGUniqueness.B2.PfeLocal.L4Copy

 













set_option autoImplicit false
noncomputable section

open Set Metric MeasureTheory Filter Topology
open scoped ENNReal
open LQGMetric

namespace SupercriticalLQGUniqueness.B2.PfeLocal

 
def l4Spacing (k₀ : ℕ) : ℝ := l1Scale k₀ k₀ / 4

theorem l4Spacing_pos (k₀ : ℕ) : 0 < l4Spacing k₀ := by
  unfold l4Spacing; have := l1Scale_pos k₀ k₀; positivity

 
def l4N (k₀ : ℕ) (R : ℝ) : ℕ := ⌈(R + 1) / l4Spacing k₀⌉₊

 
def l4Lattice (k₀ : ℕ) (R : ℝ) : Finset ℂ :=
  ((Finset.Icc (-(l4N k₀ R : ℤ)) (l4N k₀ R)) ×ˢ (Finset.Icc (-(l4N k₀ R : ℤ)) (l4N k₀ R))).image
    fun q => ⟨l4Spacing k₀ * q.1, l4Spacing k₀ * q.2⟩

theorem l4Lattice_card_le (k₀ : ℕ) (R : ℝ) :
    ((l4Lattice k₀ R).card : ℝ) ≤ (2 * l4N k₀ R + 1) ^ 2 := by
  unfold l4Lattice
  refine (Nat.cast_le.2 Finset.card_image_le).trans ?_
  rw [Finset.card_product, Int.card_Icc]
  push_cast
  have : ((l4N k₀ R : ℤ) + 1 - -(l4N k₀ R : ℤ)).toNat = 2 * l4N k₀ R + 1 := by omega
  rw [this]; push_cast; ring_nf; exact le_rfl

 
theorem l4_lattice_near (k₀ : ℕ) {R : ℝ} (hR : 0 ≤ R) {p : ℂ} (hp : ‖p‖ ≤ R) :
    ∃ w ∈ l4Lattice k₀ R, dist p w < l4Spacing k₀ := by
  set s := l4Spacing k₀ with hsdef
  have hs : 0 < s := l4Spacing_pos k₀
  have hs1 : s ≤ 1 := by
    rw [hsdef]; unfold l4Spacing l1Scale
    have : (1 / 16 : ℝ) ^ (k₀ + k₀) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    linarith
  set m : ℤ := round (p.re / s)
  set n : ℤ := round (p.im / s)
  have hm : |p.re / s - m| ≤ 1 / 2 := abs_sub_round _
  have hn : |p.im / s - n| ≤ 1 / 2 := abs_sub_round _
  have hre : |p.re| ≤ R := (Complex.abs_re_le_norm p).trans hp
  have him : |p.im| ≤ R := (Complex.abs_im_le_norm p).trans hp
  have hN : (R + 1) / s ≤ l4N k₀ R := Nat.le_ceil _
  have hbound : ∀ x : ℝ, |x| ≤ R → ∀ k : ℤ, |x / s - k| ≤ 1 / 2 →
      -(l4N k₀ R : ℤ) ≤ k ∧ k ≤ l4N k₀ R := by
    intro x hx k hk
    have h1 : |x / s| ≤ R / s := by
      rw [abs_div, abs_of_pos hs]; exact div_le_div_of_nonneg_right hx hs.le
    have h2 : R / s + 1 / 2 ≤ (l4N k₀ R : ℝ) := by
      have : R / s + 1 / 2 ≤ (R + 1) / s := by
        rw [add_div]
        have : 1 / 2 ≤ 1 / s := by
          rw [div_le_div_iff₀ (by norm_num) hs]; linarith
        linarith
      linarith
    have hk' : |(k : ℝ)| ≤ (l4N k₀ R : ℝ) := by
      have := abs_sub_abs_le_abs_sub (x / s) k
      have : |(k : ℝ)| ≤ |x / s| + 1 / 2 := by
        have := abs_sub_abs_le_abs_sub (k : ℝ) (x / s)
        rw [abs_sub_comm] at this; linarith
      linarith
    constructor
    · have := neg_abs_le (k : ℝ); exact_mod_cast (by linarith : (-(l4N k₀ R : ℝ)) ≤ k)
    · have := le_abs_self (k : ℝ); exact_mod_cast (by linarith : (k : ℝ) ≤ (l4N k₀ R : ℝ))
  obtain ⟨hm1, hm2⟩ := hbound _ hre m hm
  obtain ⟨hn1, hn2⟩ := hbound _ him n hn
  refine ⟨⟨s * m, s * n⟩, Finset.mem_image.2 ⟨(m, n), Finset.mem_product.2
    ⟨Finset.mem_Icc.2 ⟨hm1, hm2⟩, Finset.mem_Icc.2 ⟨hn1, hn2⟩⟩, rfl⟩, ?_⟩
  have hre' : |p.re - s * m| ≤ s / 2 := by
    rw [show p.re - s * m = s * (p.re / s - m) by field_simp [hs.ne'], abs_mul, abs_of_pos hs]
    nlinarith
  have him' : |p.im - s * n| ≤ s / 2 := by
    rw [show p.im - s * n = s * (p.im / s - n) by field_simp [hs.ne'], abs_mul, abs_of_pos hs]
    nlinarith
  rw [Complex.dist_eq, Complex.norm_eq_sqrt_sq_add_sq]
  simp only [Complex.sub_re, Complex.sub_im]
  rw [Real.sqrt_lt' hs]
  have e1 := sq_abs (p.re - s * m)
  have e2 := sq_abs (p.im - s * n)
  nlinarith [abs_nonneg (p.re - s * m), abs_nonneg (p.im - s * n)]

 
theorem l4_finset_meet {J : ℕ} (hJ : 1 ≤ J) {S₁ S₂ : Finset ℕ} (h₁ : S₁ ⊆ Finset.Icc 1 J)
    (h₂ : S₂ ⊆ Finset.Icc 1 J) (hc₁ : (3 / 4 : ℝ) * J ≤ S₁.card)
    (hc₂ : (3 / 4 : ℝ) * J ≤ S₂.card) : (S₁ ∩ S₂).Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro hempty
  have hU : (S₁ ∪ S₂).card ≤ J := by
    have := Finset.card_le_card (Finset.union_subset h₁ h₂)
    simpa using this
  have hdis : (S₁ ∪ S₂).card = S₁.card + S₂.card := by
    rw [Finset.card_union_of_disjoint (Finset.disjoint_iff_inter_eq_empty.2 hempty)]
  have : (S₁.card : ℝ) + S₂.card ≤ J := by exact_mod_cast hdis ▸ hU
  have hJ' : (1 : ℝ) ≤ J := by exact_mod_cast hJ
  linarith

end SupercriticalLQGUniqueness.B2.PfeLocal
