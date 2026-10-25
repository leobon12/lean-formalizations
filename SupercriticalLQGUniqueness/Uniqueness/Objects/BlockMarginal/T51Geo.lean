import SupercriticalLQGUniqueness.Uniqueness.Objects.BlockMarginal.Family
import SupercriticalLQGUniqueness.Uniqueness.Objects.Blocks.Basic




 












set_option autoImplicit false

noncomputable section

open Set Metric Real

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.BlockMarginal

 
def halfOK (n q : ℂ) : Prop := 0 ≤ (q * (starRingEnd ℂ) n).re

 
def orient : Fin 4 → ℂ := ![1, -1, Complex.I, -Complex.I]

theorem orient_mem (i : Fin 4) : orient i ∈ orientations := by
  fin_cases i <;> simp [orient, orientations]

theorem orient_norm (i : Fin 4) : ‖orient i‖ = 1 := orientation_norm (orient_mem i)

 
theorem exists_orient_of_small_diam {S : Set ℂ} {r : ℝ} (hr : 0 < r) (hS : S.Nonempty)
    (hlow : ∀ w ∈ S, 3 / 4 * r ≤ ‖w‖) (hdiam : ∀ x ∈ S, ∀ y ∈ S, ‖x - y‖ ≤ r / 100) :
    ∃ i : Fin 4, ∀ w ∈ S, halfOK (orient i) w := by
  obtain ⟨s₀, hs₀⟩ := hS
  rcases Objects.Blocks.halfPlane_of_small_diam hr hs₀ hlow hdiam with h | h | h | h
  · refine ⟨0, fun w hw => ?_⟩
    have := h w hw
    simp only [halfOK, orient, Matrix.cons_val_zero, map_one, mul_one]
    exact this.le
  · refine ⟨1, fun w hw => ?_⟩
    have := h w hw
    simp only [halfOK, orient, Matrix.cons_val_one, Matrix.cons_val_zero, map_neg, map_one,
      mul_neg, mul_one, Complex.neg_re]
    linarith
  · refine ⟨2, fun w hw => ?_⟩
    have := h w hw
    simp only [halfOK, orient, Complex.conj_I, mul_neg, Complex.neg_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Matrix.cons_val, mul_zero, mul_one, zero_sub, neg_neg]
    linarith
  · refine ⟨3, fun w hw => ?_⟩
    have := h w hw
    simp only [halfOK, orient, map_neg, Complex.conj_I, neg_neg, Complex.mul_re, Complex.I_re,
      Complex.I_im, Matrix.cons_val, mul_zero, mul_one, zero_sub]
    linarith

 

theorem gridHalf_mul_le {δ : ℝ} (hδ : 0 < δ) : (gridHalf δ : ℝ) * δ ≤ π / 2 := by
  have := Nat.floor_le (show 0 ≤ π / 2 / δ by positivity)
  rw [le_div_iff₀ hδ] at this
  exact this

theorem lt_gridHalf_succ_mul {δ : ℝ} (hδ : 0 < δ) : π / 2 < ((gridHalf δ : ℝ) + 1) * δ := by
  have := Nat.lt_floor_add_one (π / 2 / δ)
  rw [div_lt_iff₀ hδ] at this
  exact this

theorem exists_gridAngle_near {δ : ℝ} (hδ : 0 < δ) {φ : ℝ} (hφ : |φ| ≤ π / 2) :
    ∃ ψ ∈ gridAngles δ, |φ - ψ| ≤ δ := by
  obtain ⟨hφ1, hφ2⟩ := abs_le.mp hφ
  have hJ2 := lt_gridHalf_succ_mul hδ
  set J : ℕ := gridHalf δ with hJ
  set j₀ : ℤ := ⌊φ / δ⌋ with hj₀
  have hf1 : (j₀ : ℝ) ≤ φ / δ := Int.floor_le _
  have hf2 : φ / δ < (j₀ : ℝ) + 1 := Int.lt_floor_add_one _
  rw [le_div_iff₀ hδ] at hf1
  rw [div_lt_iff₀ hδ] at hf2
  have hj₀J : j₀ ≤ (J : ℤ) := by
    have h1 : (j₀ : ℝ) * δ < ((J : ℝ) + 1) * δ := by linarith
    have h2 : (j₀ : ℝ) < (J : ℝ) + 1 := lt_of_mul_lt_mul_right h1 hδ.le
    have h3 : j₀ < (J : ℤ) + 1 := by exact_mod_cast h2
    omega
  rcases le_total j₀ (-(J : ℤ)) with hcase | hcase
  · refine ⟨δ * ((-(J : ℤ) : ℤ) : ℝ), Finset.mem_image.2 ⟨-(J : ℤ), Finset.mem_Icc.2
      ⟨le_rfl, by omega⟩, rfl⟩, ?_⟩
    have h2 : (j₀ : ℝ) ≤ -(J : ℝ) := by exact_mod_cast hcase
    push_cast
    rw [abs_le]
    constructor <;> nlinarith
  · refine ⟨δ * (j₀ : ℝ), Finset.mem_image.2 ⟨j₀, Finset.mem_Icc.2 ⟨hcase, hj₀J⟩, rfl⟩, ?_⟩
    rw [abs_le]
    constructor <;> nlinarith

theorem chord_le_arc' (ρ φ ψ : ℝ) (hρ : 0 ≤ ρ) :
    ‖(ρ : ℂ) * Complex.exp (φ * Complex.I) - (ρ : ℂ) * Complex.exp (ψ * Complex.I)‖ ≤
      ρ * |φ - ψ| := by
  have hfac : (ρ : ℂ) * Complex.exp (φ * Complex.I) - (ρ : ℂ) * Complex.exp (ψ * Complex.I) =
      (ρ : ℂ) * Complex.exp (Complex.I * ψ) *
        (Complex.exp (Complex.I * ((φ - ψ : ℝ) : ℂ)) - 1) := by
    have h : (φ : ℂ) * Complex.I = Complex.I * (ψ : ℂ) + Complex.I * ((φ - ψ : ℝ) : ℂ) := by
      push_cast; ring
    rw [h, Complex.exp_add, mul_comm (ψ : ℂ) Complex.I]
    ring
  rw [hfac, norm_mul, norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hρ]
  have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := φ - ψ)
  rw [Real.norm_eq_abs] at h
  exact mul_le_mul_of_nonneg_left h hρ

 
theorem grid_point_near {ρ : ℝ} (hρ : 0 < ρ) {n u : ℂ} (hn : ‖n‖ = 1) (hu : ‖u‖ = ρ)
    (hhalf : halfOK n u) {δ : ℝ} (hδ : 0 < δ) :
    ∃ ψ ∈ gridAngles δ, ‖u - (ρ : ℂ) * n * Complex.exp (ψ * Complex.I)‖ ≤ ρ * δ := by
  set v : ℂ := u * (starRingEnd ℂ) n with hvdef
  have hv : ‖v‖ = ρ := by rw [hvdef, norm_mul, Complex.norm_conj, hn, mul_one, hu]
  have harg : |Complex.arg v| ≤ π / 2 := Complex.abs_arg_le_pi_div_two_iff.mpr hhalf
  obtain ⟨ψ, hψ, hclose⟩ := exists_gridAngle_near hδ harg
  refine ⟨ψ, hψ, ?_⟩
  have hnn : (starRingEnd ℂ) n * n = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]
    norm_num
  have hu' : u = v * n := by
    rw [hvdef, mul_assoc, hnn, mul_one]
  have hvpolar : v = (ρ : ℂ) * Complex.exp (Complex.arg v * Complex.I) := by
    rw [← hv]
    exact (Complex.norm_mul_exp_arg_mul_I v).symm
  have heq : u - (ρ : ℂ) * n * Complex.exp (ψ * Complex.I) =
      ((ρ : ℂ) * Complex.exp (Complex.arg v * Complex.I) -
        (ρ : ℂ) * Complex.exp (ψ * Complex.I)) * n := by
    rw [hu']
    nth_rewrite 1 [hvpolar]
    ring
  rw [heq, norm_mul, hn, mul_one]
  exact (chord_le_arc' ρ _ ψ hρ.le).trans (mul_le_mul_of_nonneg_left hclose hρ.le)

 

 
def blockShapeAt (b α : ℝ) (n : ℂ) : Set ℂ :=
  (fun w : ℂ => (b : ℂ) * n * w) '' {w : ℂ | α < ‖w‖ ∧ ‖w‖ < 1 ∧ 0 < w.re}

theorem mem_closure_halfAnnulus {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    {w : ℂ} (hw1 : α ≤ ‖w‖) (hw2 : ‖w‖ ≤ 1) (hre : 0 ≤ w.re) :
    w ∈ closure {w : ℂ | α < ‖w‖ ∧ ‖w‖ < 1 ∧ 0 < w.re} := by
  let Φ : ℝ × ℝ → ℂ := fun p => (p.1 : ℂ) * Complex.exp (p.2 * Complex.I)
  have hΦ : Continuous Φ := by
    unfold Φ
    fun_prop
  have hrect : Φ '' (Ioo α 1 ×ˢ Ioo (-(π / 2)) (π / 2)) ⊆
      {w : ℂ | α < ‖w‖ ∧ ‖w‖ < 1 ∧ 0 < w.re} := by
    rintro _ ⟨p, ⟨hp1, hp2⟩, rfl⟩
    have hpos : 0 < p.1 := hα.trans hp1.1
    have hnorm : ‖Φ p‖ = p.1 := by
      change ‖(p.1 : ℂ) * Complex.exp (p.2 * Complex.I)‖ = p.1
      rw [norm_mul, Complex.norm_real, Complex.norm_exp_ofReal_mul_I, mul_one, Real.norm_eq_abs,
        abs_of_pos hpos]
    refine ⟨by rw [hnorm]; exact hp1.1, by rw [hnorm]; exact hp1.2, ?_⟩
    change 0 < ((p.1 : ℂ) * Complex.exp (p.2 * Complex.I)).re
    rw [Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
    exact mul_pos hpos (Real.cos_pos_of_mem_Ioo hp2)
  have hmem : (‖w‖, Complex.arg w) ∈ closure (Ioo α 1 ×ˢ Ioo (-(π / 2)) (π / 2)) := by
    rw [closure_prod_eq, closure_Ioo hα1.ne, closure_Ioo (by linarith [Real.pi_pos])]
    exact ⟨⟨hw1, hw2⟩, abs_le.mp (Complex.abs_arg_le_pi_div_two_iff.mpr hre)⟩
  have hw : Φ (‖w‖, Complex.arg w) = w := Complex.norm_mul_exp_arg_mul_I w
  rw [← hw]
  exact closure_mono hrect (image_closure_subset_closure_image hΦ ⟨_, hmem, rfl⟩)

theorem mem_closure_blockShapeAt {b α : ℝ} (hb : 0 < b) (hα : 0 < α) (hα1 : α < 1) {n : ℂ}
    (hn : ‖n‖ = 1) {q : ℂ} (hq1 : α * b ≤ ‖q‖) (hq2 : ‖q‖ ≤ b) (hhalf : halfOK n q) :
    q ∈ closure (blockShapeAt b α n) := by
  set w : ℂ := q * (starRingEnd ℂ) n / (b : ℂ) with hwdef
  have hb' : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  have hnn : n * (starRingEnd ℂ) n = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]
    norm_num
  have hq : q = (b : ℂ) * n * w := by
    have h : (b : ℂ) * n * w = q * (n * (starRingEnd ℂ) n) := by
      rw [hwdef]
      field_simp
    rw [h, hnn, mul_one]
  have hwnorm : ‖w‖ = ‖q‖ / b := by
    rw [hwdef, norm_div, norm_mul, Complex.norm_conj, hn, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hb]
  have hw : w ∈ closure {w : ℂ | α < ‖w‖ ∧ ‖w‖ < 1 ∧ 0 < w.re} := by
    refine mem_closure_halfAnnulus hα hα1 ?_ ?_ ?_
    · rw [hwnorm, le_div_iff₀ hb]
      exact hq1
    · rw [hwnorm, div_le_iff₀ hb, one_mul]
      exact hq2
    · rw [hwdef, Complex.div_ofReal_re]
      exact div_nonneg hhalf hb.le
  have hcont : Continuous (fun x : ℂ => (b : ℂ) * n * x) := by fun_prop
  rw [hq]
  exact image_closure_subset_closure_image hcont ⟨w, hw, rfl⟩

end SupercriticalLQGUniqueness.Uniqueness.Objects.BlockMarginal
