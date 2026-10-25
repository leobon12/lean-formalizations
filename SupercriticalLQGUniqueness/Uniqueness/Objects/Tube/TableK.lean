import SupercriticalLQGUniqueness.Uniqueness.Objects.Tube.Frame




 














set_option autoImplicit false

noncomputable section

open Complex Set Metric Real

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Tube

 

theorem dist_ge_of_norm {x y : ℂ} {A B : ℝ} (hx : ‖x‖ ≤ A) (hy : B ≤ ‖y‖) : B - A ≤ dist x y := by
  have := norm_gap_le_dist y x
  rw [dist_comm] at this
  linarith [le_abs_self (‖y‖ - ‖x‖)]

theorem dist_ge_of_norm' {x y : ℂ} {A B : ℝ} (hx : B ≤ ‖x‖) (hy : ‖y‖ ≤ A) : B - A ≤ dist x y := by
  rw [dist_comm]; exact dist_ge_of_norm hy hx

theorem dist_ge_of_re (c : ℂ) (hc : ‖c‖ = 1) {x y : ℂ} {p : ℝ}
    (h : p ≤ (c * y).re - (c * x).re) : p ≤ dist x y := by
  have := re_gap_le_dist c x y hc
  rw [abs_sub_comm] at this
  linarith [le_abs_self ((c * y).re - (c * x).re)]

 
theorem dist_negReal_ge {R : ℝ} (hR : 0 ≤ R) {y : ℂ} (hy : 0 ≤ y.re) : ‖y‖ ≤ dist (pol R π) y := by
  rw [Complex.dist_eq, pol_pi]
  have h1 : ‖y‖ ^ 2 ≤ ‖-(R : ℂ) - y‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
      Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
      Complex.ofReal_im]
    nlinarith
  nlinarith [norm_nonneg y, norm_nonneg (-(R : ℂ) - y)]

theorem cos_nonneg_of_abs_le {x : ℝ} (h : |x| ≤ π / 2) : 0 ≤ Real.cos x :=
  Real.cos_nonneg_of_mem_Icc ⟨by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩

theorem half_le_cos_of_abs_le {x : ℝ} (h : |x| ≤ π / 3) : 1 / 2 ≤ Real.cos x := by
  rw [← Real.cos_abs]
  calc (1 : ℝ) / 2 = Real.cos (π / 3) := Real.cos_pi_div_three.symm
    _ ≤ Real.cos |x| :=
      Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_pos]) h

 
theorem abs_sub_mid_le {a b φ : ℝ} (hφ : φ ∈ uIcc a b) : |φ - (a + b) / 2| ≤ |b - a| / 2 := by
  rw [mem_uIcc] at hφ
  rw [abs_le]
  rcases hφ with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have : |b - a| = b - a := abs_of_nonneg (by linarith)
    rw [this]; constructor <;> linarith
  · have : |b - a| = a - b := by rw [abs_sub_comm]; exact abs_of_nonneg (by linarith)
    rw [this]; constructor <;> linarith

 
theorem abs_sub_left_le {a b φ : ℝ} (hφ : φ ∈ uIcc a b) : |φ - a| ≤ |b - a| := by
  rw [mem_uIcc] at hφ
  rcases hφ with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; linarith
  · rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith

theorem abs_sub_right_le {a b φ : ℝ} (hφ : φ ∈ uIcc a b) : |φ - b| ≤ |b - a| := by
  rw [uIcc_comm] at hφ
  have := abs_sub_left_le hφ
  rwa [abs_sub_comm a b] at this

 

theorem J_lemma {a b φ φ' R R' : ℝ} (hab : |b - a| ≤ π / 2) (hφ : φ ∈ uIcc a b)
    (hφ' : φ' ∈ uIcc a b) (hR : 0 ≤ R) (hR' : 0 ≤ R') :
    (R + R') / 2 ≤ dist (pol R (φ + π)) (pol R' φ') := by
  set m := (a + b) / 2 with hm
  have key : ∀ ψ ∈ uIcc a b, 1 / 2 ≤ Real.cos (ψ + -m) := by
    intro ψ hψ
    apply half_le_cos_of_abs_le
    have := abs_sub_mid_le hψ
    rw [← sub_eq_add_neg]
    linarith [Real.pi_pos]
  have h1 := key φ hφ
  have h2 := key φ' hφ'
  apply dist_ge_of_re (ex (-m)) (norm_ex _)
  rw [re_ex_mul_pol, re_ex_mul_pol, show φ + π + -m = (φ + -m) + π by ring, Real.cos_add_pi]
  nlinarith

 

section Bounds

variable {α sp ψu ψv Δ : ℝ}

theorem norm_le_four_of_mem_outPath (hsp : 0 ≤ sp) (hsp1 : sp ≤ 2 / 3) {y : ℂ}
    (hy : y ∈ range (outPath sp ψv Δ)) : ‖y‖ ≤ 4 := by
  rw [range_outPath] at hy
  rcases hy with hy | hy
  · obtain ⟨R, hR, rfl⟩ := mem_o1 hsp1 hy; rw [norm_pol (by linarith [hR.1])]; linarith [hR.2]
  simp only [outRest, mem_union] at hy
  rcases hy with ((((hy | hy) | hy) | hy) | hy) | hy
  · obtain ⟨φ, -, rfl⟩ := mem_o2 hy; rw [norm_pol (by norm_num)]; norm_num
  · obtain ⟨R, hR, rfl⟩ := mem_o3 hy; rw [norm_pol (by linarith [hR.1])]; linarith [hR.2]
  · obtain ⟨φ, -, rfl⟩ := mem_t1 hy; rw [norm_pol (by norm_num)]; norm_num
  · obtain ⟨R, hR, rfl⟩ := mem_t2 hy; rw [norm_pol (by linarith [hR.1])]; linarith [hR.2]
  · obtain ⟨φ, -, rfl⟩ := mem_t3 hy; rw [norm_pol (by norm_num)]; norm_num
  · obtain ⟨R, hR, rfl⟩ := mem_t4 hy; rw [norm_pol (by linarith [hR.1])]; linarith [hR.2]

theorem norm_ge_of_mem_outPath (hsp : 0 ≤ sp) (hsp1 : sp ≤ 2 / 3) {y : ℂ}
    (hy : y ∈ range (outPath sp ψv Δ)) : 1 + 3 * sp / 4 ≤ ‖y‖ := by
  rw [range_outPath] at hy
  rcases hy with hy | hy
  · obtain ⟨R, hR, rfl⟩ := mem_o1 hsp1 hy; rw [norm_pol (by linarith [hR.1])]; linarith [hR.1]
  simp only [outRest, mem_union] at hy
  rcases hy with ((((hy | hy) | hy) | hy) | hy) | hy
  · obtain ⟨φ, -, rfl⟩ := mem_o2 hy; rw [norm_pol (by norm_num)]; linarith
  · obtain ⟨R, hR, rfl⟩ := mem_o3 hy; rw [norm_pol (by linarith [hR.1])]; linarith [hR.1]
  · obtain ⟨φ, -, rfl⟩ := mem_t1 hy; rw [norm_pol (by norm_num)]; linarith
  · obtain ⟨R, hR, rfl⟩ := mem_t2 hy; rw [norm_pol (by linarith [hR.1])]; linarith [hR.1]
  · obtain ⟨φ, -, rfl⟩ := mem_t3 hy; rw [norm_pol (by norm_num)]; linarith
  · obtain ⟨R, hR, rfl⟩ := mem_t4 hy; rw [norm_pol (by linarith [hR.1])]; linarith [hR.1]

theorem norm_ge_of_mem_outRest {y : ℂ} (hy : y ∈ outRest ψv Δ) : 3 / 2 ≤ ‖y‖ := by
  simp only [outRest, mem_union] at hy
  rcases hy with ((((hy | hy) | hy) | hy) | hy) | hy
  · obtain ⟨φ, -, rfl⟩ := mem_o2 hy; rw [norm_pol (by norm_num)]
  · obtain ⟨R, hR, rfl⟩ := mem_o3 hy; rw [norm_pol (by linarith [hR.1])]; linarith [hR.1]
  · obtain ⟨φ, -, rfl⟩ := mem_t1 hy; rw [norm_pol (by norm_num)]; norm_num
  · obtain ⟨R, hR, rfl⟩ := mem_t2 hy; rw [norm_pol (by linarith [hR.1])]; linarith [hR.1]
  · obtain ⟨φ, -, rfl⟩ := mem_t3 hy; rw [norm_pol (by norm_num)]; norm_num
  · obtain ⟨R, hR, rfl⟩ := mem_t4 hy; rw [norm_pol (by linarith [hR.1])]; linarith [hR.1]

theorem norm_ge_of_mem_inRest {x : ℂ} (hx : x ∈ inRest Δ) (hx2 : x ∉ range i2) :
    5 / 2 ≤ ‖x‖ := by
  simp only [inRest, mem_union] at hx
  rcases hx with ((((hx | hx) | hx) | hx) | hx)
  · obtain ⟨R, hR, rfl⟩ := mem_nt4 hx; rw [norm_pol (by linarith [hR.1])]; linarith [hR.1]
  · obtain ⟨φ, -, rfl⟩ := mem_nt3 hx; rw [norm_pol (by norm_num)]; norm_num
  · obtain ⟨R, hR, rfl⟩ := mem_nt2 hx; rw [norm_pol (by linarith [hR.1])]; linarith [hR.1]
  · obtain ⟨φ, -, rfl⟩ := mem_nt1 hx; rw [norm_pol (by norm_num)]
  · exact absurd hx hx2

theorem norm_le_four_of_mem_inPath (hpos : 0 ≤ α - 3 * sp / 4) (hsp : 0 ≤ sp) (hα : α ≤ 4) {x : ℂ}
    (hx : x ∈ range (inPath α sp ψu Δ)) : ‖x‖ ≤ 4 := by
  rw [range_inPath] at hx
  rcases hx with hx | hx
  · simp only [inRest, mem_union] at hx
    rcases hx with ((((hx | hx) | hx) | hx) | hx)
    · obtain ⟨R, hR, rfl⟩ := mem_nt4 hx; rw [norm_pol (by linarith [hR.1])]; linarith [hR.2]
    · obtain ⟨φ, -, rfl⟩ := mem_nt3 hx; rw [norm_pol (by norm_num)]; norm_num
    · obtain ⟨R, hR, rfl⟩ := mem_nt2 hx; rw [norm_pol (by linarith [hR.1])]; linarith [hR.2]
    · obtain ⟨φ, -, rfl⟩ := mem_nt1 hx; rw [norm_pol (by norm_num)]; norm_num
    · obtain ⟨R, hR, rfl⟩ := mem_i2 hx; rw [norm_pol hR.1]; linarith [hR.2]
  · obtain ⟨R, hR, rfl⟩ := mem_i1 hpos hx; rw [norm_pol hR.1]; linarith [hR.2]

theorem norm_ge_of_mem_corrOutH {x : ℂ} (hx : x ∈ corrOutH Δ) : 4 ≤ ‖x‖ := by
  have h1 : (ex (-Δ) * x).re ≤ ‖ex (-Δ) * x‖ := Complex.re_le_norm _
  rw [norm_mul, norm_ex, one_mul] at h1
  exact le_trans hx h1

theorem norm_ge_of_mem_corrInH {x : ℂ} (hx : x ∈ corrInH Δ) : 4 ≤ ‖x‖ := by
  have h1 : -(ex (-Δ) * x).re ≤ ‖ex (-Δ) * x‖ := by
    have := Complex.abs_re_le_norm (ex (-Δ) * x)
    linarith [neg_abs_le (ex (-Δ) * x).re]
  rw [norm_mul, norm_ex, one_mul] at h1
  exact le_trans hx h1

end Bounds

 

theorem abs_le_of_mem_uIcc_zero_left {φ b : ℝ} (h : φ ∈ uIcc 0 b) : |φ| ≤ |b| := by
  have := abs_sub_left_le h; simpa using this

theorem abs_le_of_mem_uIcc_zero_right {φ b : ℝ} (h : φ ∈ uIcc b 0) : |φ| ≤ |b| := by
  have := abs_sub_right_le h
  simp only [sub_zero, zero_sub, abs_neg] at this; exact this

theorem abs_half_le {Δ : ℝ} (hΔ : Δ ∈ Icc (-π) π) : |Δ / 2| ≤ π / 2 := by
  rw [abs_le]; constructor <;> linarith [hΔ.1, hΔ.2]

theorem abs_half_sub_le {Δ : ℝ} (hΔ : Δ ∈ Icc (-π) π) : |Δ - Δ / 2| ≤ π / 2 := by
  rw [show Δ - Δ / 2 = Δ / 2 by ring]; exact abs_half_le hΔ

theorem abs_le_pi_div_two_of_Icc {ψ : ℝ} (h : ψ ∈ Icc (-(π / 2)) (π / 2)) : |ψ| ≤ π / 2 :=
  abs_le.mpr ⟨h.1, h.2⟩

theorem norm_pol_le {R A θ : ℝ} (h0 : 0 ≤ R) (h : R ≤ A) : ‖pol R θ‖ ≤ A := by
  rw [norm_pol h0]; exact h

theorem le_norm_pol {R A θ : ℝ} (h0 : 0 ≤ R) (h : A ≤ R) : A ≤ ‖pol R θ‖ := by
  rw [norm_pol h0]; exact h

 

section Rows

variable {α sp ψu ψv Δ : ℝ}

 
theorem K1 (hsp : 0 ≤ sp) (hsp1 : sp ≤ 2 / 3) (hpos : 0 ≤ α - 3 * sp / 4) {x y : ℂ}
    (hx : x ∈ range (i1 α sp ψu)) (hy : y ∈ range (outPath sp ψv Δ) ∪ corrOutH Δ) :
    1 - α + 3 * sp / 2 ≤ dist x y := by
  obtain ⟨R, hR, rfl⟩ := mem_i1 hpos hx
  have hyn : 1 + 3 * sp / 4 ≤ ‖y‖ := by
    rcases hy with hy | hy
    · exact norm_ge_of_mem_outPath hsp hsp1 hy
    · have := norm_ge_of_mem_corrOutH hy; linarith
  have := dist_ge_of_norm (norm_pol_le (θ := ψu) hR.1 hR.2) hyn
  linarith

 

theorem K2 (hsp : 0 ≤ sp) (hsp1 : sp ≤ 2 / 3) (hψv : ψv ∈ Icc (-(π / 2)) (π / 2))
    (hΔ : Δ ∈ Icc (-π) π) {x y : ℂ} (hx : x ∈ range i2)
    (hy : y ∈ range (outPath sp ψv Δ) ∪ corrOutH Δ) : 1 ≤ dist x y := by
  obtain ⟨R, hR, rfl⟩ := mem_i2 hx
  have hxn : ‖pol R π‖ ≤ 5 / 2 := norm_pol_le hR.1 hR.2
  rcases hy with hy | hy
  · rw [range_outPath] at hy
    rcases hy with hy | hy
    · obtain ⟨R', hR', rfl⟩ := mem_o1 hsp1 hy
      have hre : 0 ≤ (pol R' ψv).re := by
        rw [pol_re]; exact mul_nonneg (by linarith [hR'.1]) (Real.cos_nonneg_of_mem_Icc hψv)
      have := dist_negReal_ge hR.1 hre
      rw [norm_pol (by linarith [hR'.1])] at this; linarith [hR'.1]
    simp only [outRest, mem_union] at hy
    rcases hy with ((((hy | hy) | hy) | hy) | hy) | hy
    · obtain ⟨φ, hφ, rfl⟩ := mem_o2 hy
      have hφ' : |φ| ≤ π / 2 :=
        (abs_le_of_mem_uIcc_zero_right hφ).trans (abs_le_pi_div_two_of_Icc hψv)
      have hre : 0 ≤ (pol (3 / 2) φ).re := by
        rw [pol_re]; exact mul_nonneg (by norm_num) (cos_nonneg_of_abs_le hφ')
      have := dist_negReal_ge hR.1 hre
      rw [norm_pol (by norm_num)] at this; linarith
    · obtain ⟨R', hR', rfl⟩ := mem_o3 hy
      have hre : 0 ≤ (pol R' 0).re := by
        rw [pol_re, Real.cos_zero, mul_one]; linarith [hR'.1]
      have := dist_negReal_ge hR.1 hre
      rw [norm_pol (by linarith [hR'.1])] at this; linarith [hR'.1]
    · obtain ⟨φ, hφ, rfl⟩ := mem_t1 hy
      have hφ' : |φ| ≤ π / 2 := (abs_le_of_mem_uIcc_zero_left hφ).trans (abs_half_le hΔ)
      have hre : 0 ≤ (pol (5 / 2) φ).re := by
        rw [pol_re]; exact mul_nonneg (by norm_num) (cos_nonneg_of_abs_le hφ')
      have := dist_negReal_ge hR.1 hre
      rw [norm_pol (by norm_num)] at this; linarith
    · obtain ⟨R', hR', rfl⟩ := mem_t2 hy
      have hre : 0 ≤ (pol R' (Δ / 2)).re := by
        rw [pol_re]
        exact mul_nonneg (by linarith [hR'.1]) (cos_nonneg_of_abs_le (abs_half_le hΔ))
      have := dist_negReal_ge hR.1 hre
      rw [norm_pol (by linarith [hR'.1])] at this; linarith [hR'.1]
    · obtain ⟨φ, -, rfl⟩ := mem_t3 hy
      have := dist_ge_of_norm hxn (le_norm_pol (θ := φ) (by norm_num) (le_refl (7 / 2 : ℝ)))
      linarith
    · obtain ⟨R', hR', rfl⟩ := mem_t4 hy
      have := dist_ge_of_norm hxn (le_norm_pol (θ := Δ) (by linarith [hR'.1]) hR'.1)
      linarith
  · have := dist_ge_of_norm hxn (norm_ge_of_mem_corrOutH hy); linarith

 
theorem K3_nt1 (hsp : 0 ≤ sp) (hsp1 : sp ≤ 2 / 3) (hΔ : Δ ∈ Icc (-π) π) {x y : ℂ} (hx : x ∈ range (nt1 Δ))
    (hy : y ∈ range (outPath sp ψv Δ) ∪ corrOutH Δ) : 1 ≤ dist x y := by
  obtain ⟨φ, hφ, rfl⟩ := mem_nt1 hx
  have hxn : ‖pol (5 / 2) (φ + π)‖ = 5 / 2 := norm_pol (by norm_num) _
  have hφ' : |φ| ≤ π / 2 := (abs_le_of_mem_uIcc_zero_left hφ).trans (abs_half_le hΔ)
  have hab : |Δ / 2 - 0| ≤ π / 2 := by rw [sub_zero]; exact abs_half_le hΔ
  rcases hy with hy | hy
  · rw [range_outPath] at hy
    rcases hy with hy | hy
    · obtain ⟨R', hR', rfl⟩ := mem_o1 hsp1 hy
      have := dist_ge_of_norm' (le_of_eq hxn.symm) (norm_pol_le (θ := ψv) (by linarith [hR'.1]) hR'.2)
      linarith
    simp only [outRest, mem_union] at hy
    rcases hy with ((((hy | hy) | hy) | hy) | hy) | hy
    · obtain ⟨φ', -, rfl⟩ := mem_o2 hy
      have := dist_ge_of_norm' (le_of_eq hxn.symm) (norm_pol_le (θ := φ') (by norm_num)
        (le_refl (3 / 2 : ℝ)))
      linarith
    · obtain ⟨R', hR', rfl⟩ := mem_o3 hy
      apply dist_ge_of_re (ex 0) (norm_ex 0)
      simp only [re_ex_mul_pol, add_zero, Real.cos_zero, Real.cos_add_pi]
      nlinarith [cos_nonneg_of_abs_le hφ', hR'.1]
    · obtain ⟨φ', hφ'', rfl⟩ := mem_t1 hy
      have := J_lemma hab hφ hφ'' (by norm_num : (0 : ℝ) ≤ 5 / 2) (by norm_num : (0 : ℝ) ≤ 5 / 2)
      linarith
    · obtain ⟨R', hR', rfl⟩ := mem_t2 hy
      have := J_lemma hab hφ right_mem_uIcc (by norm_num : (0 : ℝ) ≤ 5 / 2)
        (by linarith [hR'.1] : (0 : ℝ) ≤ R')
      linarith [hR'.1]
    · obtain ⟨φ', -, rfl⟩ := mem_t3 hy
      have := dist_ge_of_norm (le_of_eq hxn) (le_norm_pol (θ := φ') (by norm_num)
        (le_refl (7 / 2 : ℝ)))
      linarith
    · obtain ⟨R', hR', rfl⟩ := mem_t4 hy
      have := dist_ge_of_norm (le_of_eq hxn) (le_norm_pol (θ := Δ) (by linarith [hR'.1]) hR'.1)
      linarith
  · have := dist_ge_of_norm (le_of_eq hxn) (norm_ge_of_mem_corrOutH hy); linarith

 
theorem K3_nt2 (hsp : 0 ≤ sp) (hsp1 : sp ≤ 2 / 3) (hΔ : Δ ∈ Icc (-π) π) {x y : ℂ} (hx : x ∈ range (nt2 Δ))
    (hy : y ∈ range (outPath sp ψv Δ) ∪ corrOutH Δ) : 1 ≤ dist x y := by
  obtain ⟨R, hR, rfl⟩ := mem_nt2 hx
  have hR0 : 0 ≤ R := by linarith [hR.1]
  have hxn : ‖pol R (Δ / 2 + π)‖ = R := norm_pol hR0 _
  have hab : |Δ / 2 - 0| ≤ π / 2 := by rw [sub_zero]; exact abs_half_le hΔ
  have hab' : |Δ - Δ / 2| ≤ π / 2 := abs_half_sub_le hΔ
  rcases hy with hy | hy
  · rw [range_outPath] at hy
    rcases hy with hy | hy
    · obtain ⟨R', hR', rfl⟩ := mem_o1 hsp1 hy
      have := dist_ge_of_norm' (le_of_eq hxn.symm) (norm_pol_le (θ := ψv) (by linarith [hR'.1]) hR'.2)
      linarith [hR.1]
    simp only [outRest, mem_union] at hy
    rcases hy with ((((hy | hy) | hy) | hy) | hy) | hy
    · obtain ⟨φ', -, rfl⟩ := mem_o2 hy
      have := dist_ge_of_norm' (le_of_eq hxn.symm) (norm_pol_le (θ := φ') (by norm_num)
        (le_refl (3 / 2 : ℝ)))
      linarith [hR.1]
    · obtain ⟨R', hR', rfl⟩ := mem_o3 hy
      apply dist_ge_of_re (ex 0) (norm_ex 0)
      simp only [re_ex_mul_pol, add_zero, Real.cos_zero, Real.cos_add_pi]
      nlinarith [cos_nonneg_of_abs_le (abs_half_le hΔ), hR'.1]
    · obtain ⟨φ', hφ'', rfl⟩ := mem_t1 hy
      have := J_lemma hab right_mem_uIcc hφ'' hR0 (by norm_num : (0 : ℝ) ≤ 5 / 2)
      linarith [hR.1]
    · obtain ⟨R', hR', rfl⟩ := mem_t2 hy
      have := J_lemma hab right_mem_uIcc right_mem_uIcc hR0 (by linarith [hR'.1] : (0 : ℝ) ≤ R')
      linarith [hR.1, hR'.1]
    · obtain ⟨φ', hφ'', rfl⟩ := mem_t3 hy
      have := J_lemma hab' left_mem_uIcc hφ'' hR0 (by norm_num : (0 : ℝ) ≤ 7 / 2)
      linarith [hR.1]
    · obtain ⟨R', hR', rfl⟩ := mem_t4 hy
      have := J_lemma hab' left_mem_uIcc right_mem_uIcc hR0 (by linarith [hR'.1] : (0 : ℝ) ≤ R')
      linarith [hR.1, hR'.1]
  · apply dist_ge_of_re (ex (-Δ)) (norm_ex _)
    rw [re_ex_mul_pol, show Δ / 2 + π + -Δ = -(Δ / 2) + π by ring, Real.cos_add_pi, Real.cos_neg]
    have h1 : 4 ≤ (ex (-Δ) * y).re := hy
    nlinarith [cos_nonneg_of_abs_le (abs_half_le hΔ)]

 
theorem K3_nt34 (hsp : 0 ≤ sp) (hsp1 : sp ≤ 2 / 3) (hΔ : Δ ∈ Icc (-π) π) {x y : ℂ}
    (hx : x ∈ range (nt3 Δ) ∪ range (nt4 Δ))
    (hy : y ∈ range (outPath sp ψv Δ) ∪ corrOutH Δ) : 1 ≤ dist x y := by
  have hab' : |Δ - Δ / 2| ≤ π / 2 := abs_half_sub_le hΔ
  obtain ⟨R, hR, φ, hφ, rfl⟩ : ∃ R ∈ Icc (7 / 2 : ℝ) 4, ∃ φ ∈ uIcc (Δ / 2) Δ, x = pol R (φ + π) := by
    rcases hx with hx | hx
    · obtain ⟨φ, hφ, rfl⟩ := mem_nt3 hx
      exact ⟨7 / 2, ⟨le_refl _, by norm_num⟩, φ, hφ, rfl⟩
    · obtain ⟨R, hR, rfl⟩ := mem_nt4 hx
      exact ⟨R, hR, Δ, right_mem_uIcc, rfl⟩
  have hR0 : 0 ≤ R := by linarith [hR.1]
  have hxn : ‖pol R (φ + π)‖ = R := norm_pol hR0 _
  have hφΔ : |φ - Δ| ≤ π / 2 := (abs_sub_right_le hφ).trans hab'
  rcases hy with hy | hy
  · rw [range_outPath] at hy
    rcases hy with hy | hy
    · obtain ⟨R', hR', rfl⟩ := mem_o1 hsp1 hy
      have := dist_ge_of_norm' (le_of_eq hxn.symm) (norm_pol_le (θ := ψv) (by linarith [hR'.1]) hR'.2)
      linarith [hR.1]
    simp only [outRest, mem_union] at hy
    rcases hy with ((((hy | hy) | hy) | hy) | hy) | hy
    · obtain ⟨φ', -, rfl⟩ := mem_o2 hy
      have := dist_ge_of_norm' (le_of_eq hxn.symm) (norm_pol_le (θ := φ') (by norm_num)
        (le_refl (3 / 2 : ℝ)))
      linarith [hR.1]
    · obtain ⟨R', hR', rfl⟩ := mem_o3 hy
      have := dist_ge_of_norm' (le_of_eq hxn.symm) (norm_pol_le (θ := 0) (by linarith [hR'.1]) hR'.2)
      linarith [hR.1]
    · obtain ⟨φ', -, rfl⟩ := mem_t1 hy
      have := dist_ge_of_norm' (le_of_eq hxn.symm) (norm_pol_le (θ := φ') (by norm_num)
        (le_refl (5 / 2 : ℝ)))
      linarith [hR.1]
    · obtain ⟨R', hR', rfl⟩ := mem_t2 hy
      have := J_lemma hab' hφ left_mem_uIcc hR0 (by linarith [hR'.1] : (0 : ℝ) ≤ R')
      linarith [hR.1, hR'.1]
    · obtain ⟨φ', hφ'', rfl⟩ := mem_t3 hy
      have := J_lemma hab' hφ hφ'' hR0 (by norm_num : (0 : ℝ) ≤ 7 / 2)
      linarith [hR.1]
    · obtain ⟨R', hR', rfl⟩ := mem_t4 hy
      have := J_lemma hab' hφ right_mem_uIcc hR0 (by linarith [hR'.1] : (0 : ℝ) ≤ R')
      linarith [hR.1, hR'.1]
  · apply dist_ge_of_re (ex (-Δ)) (norm_ex _)
    rw [re_ex_mul_pol, show φ + π + -Δ = (φ - Δ) + π by ring, Real.cos_add_pi]
    have h1 : 4 ≤ (ex (-Δ) * y).re := hy
    nlinarith [cos_nonneg_of_abs_le hφΔ]

 

theorem in_out (hα : 3 / 4 < α) (hsp : 0 ≤ sp) (hsp1 : sp ≤ 2 / 3) (hpos : 0 ≤ α - 3 * sp / 4)
    (hψv : ψv ∈ Icc (-(π / 2)) (π / 2)) (hΔ : Δ ∈ Icc (-π) π) {x y : ℂ}
    (hx : x ∈ range (inPath α sp ψu Δ)) (hy : y ∈ range (outPath sp ψv Δ) ∪ corrOutH Δ) :
    1 - α ≤ dist x y := by
  rw [range_inPath] at hx
  rcases hx with hx | hx
  · simp only [inRest, mem_union] at hx
    rcases hx with ((((hx | hx) | hx) | hx) | hx)
    · have := K3_nt34 hsp hsp1 hΔ (Or.inr hx) hy; linarith
    · have := K3_nt34 hsp hsp1 hΔ (Or.inl hx) hy; linarith
    · have := K3_nt2 hsp hsp1 hΔ hx hy; linarith
    · have := K3_nt1 hsp hsp1 hΔ hx hy; linarith
    · have := K2 hsp hsp1 hψv hΔ hx hy; linarith
  · have := K1 hsp hsp1 hpos hx hy; linarith

 

theorem cin_out (hsp : 0 ≤ sp) (hsp1 : sp ≤ 2 / 3) (hΔ : Δ ∈ Icc (-π) π) {x y : ℂ} (hx : x ∈ corrInH Δ)
    (hy : y ∈ range (outPath sp ψv Δ) ∪ corrOutH Δ) : 3 / 2 ≤ dist x y := by
  have hxn := norm_ge_of_mem_corrInH hx
  have hx' : 4 ≤ -(ex (-Δ) * x).re := hx
  have hab' : |Δ - Δ / 2| ≤ π / 2 := abs_half_sub_le hΔ
  
  have hangle : ∀ R φ, 0 ≤ R → |φ - Δ| ≤ π / 2 → 4 ≤ dist x (pol R φ) := by
    intro R φ hR hφ
    apply dist_ge_of_re (ex (-Δ)) (norm_ex _)
    rw [re_ex_mul_pol, ← sub_eq_add_neg]
    nlinarith [cos_nonneg_of_abs_le hφ]
  rcases hy with hy | hy
  · rw [range_outPath] at hy
    rcases hy with hy | hy
    · obtain ⟨R', hR', rfl⟩ := mem_o1 hsp1 hy
      have := dist_ge_of_norm' hxn (norm_pol_le (θ := ψv) (by linarith [hR'.1]) hR'.2); linarith
    simp only [outRest, mem_union] at hy
    rcases hy with ((((hy | hy) | hy) | hy) | hy) | hy
    · obtain ⟨φ', -, rfl⟩ := mem_o2 hy
      have := dist_ge_of_norm' hxn (norm_pol_le (θ := φ') (by norm_num) (le_refl (3 / 2 : ℝ)))
      linarith
    · obtain ⟨R', hR', rfl⟩ := mem_o3 hy
      have := dist_ge_of_norm' hxn (norm_pol_le (θ := 0) (by linarith [hR'.1]) hR'.2); linarith
    · obtain ⟨φ', -, rfl⟩ := mem_t1 hy
      have := dist_ge_of_norm' hxn (norm_pol_le (θ := φ') (by norm_num) (le_refl (5 / 2 : ℝ)))
      linarith
    · obtain ⟨R', hR', rfl⟩ := mem_t2 hy
      have := hangle R' (Δ / 2) (by linarith [hR'.1])
        (by rw [abs_sub_comm]; exact hab')
      linarith
    · obtain ⟨φ', hφ'', rfl⟩ := mem_t3 hy
      have := hangle (7 / 2) φ' (by norm_num) ((abs_sub_right_le hφ'').trans hab'); linarith
    · obtain ⟨R', hR', rfl⟩ := mem_t4 hy
      have := hangle R' Δ (by linarith [hR'.1]) (by rw [sub_self, abs_zero]; positivity)
      linarith
  · have hy' : 4 ≤ (ex (-Δ) * y).re := hy
    have := dist_ge_of_re (ex (-Δ)) (norm_ex _) (x := x) (y := y) (p := 8) (by linarith)
    linarith

 
theorem K5_out {ζ y : ℂ} (hζ : ζ ∈ blockNorm α) (hy : y ∈ outRest ψv Δ ∪ corrOutH Δ ∪ corrInH Δ) :
    1 / 2 ≤ dist ζ y := by
  have hζn : ‖ζ‖ ≤ 1 := hζ.2.1.le
  have hyn : 3 / 2 ≤ ‖y‖ := by
    rcases hy with (hy | hy) | hy
    · exact norm_ge_of_mem_outRest hy
    · have := norm_ge_of_mem_corrOutH hy; linarith
    · have := norm_ge_of_mem_corrInH hy; linarith
  have := dist_ge_of_norm hζn hyn; linarith

 
theorem K5_in (hα : 3 / 4 < α) {ζ y : ℂ} (hζ : ζ ∈ blockNorm α) (hy : y ∈ inRest Δ) :
    1 / 2 ≤ dist ζ y := by
  by_cases h2 : y ∈ range i2
  · obtain ⟨R, hR, rfl⟩ := mem_i2 h2
    have := dist_negReal_ge hR.1 hζ.2.2.le
    rw [dist_comm] at this; linarith [hζ.1]
  · have := dist_ge_of_norm hζ.2.1.le (norm_ge_of_mem_inRest hy h2); linarith

 
theorem K6_i1 (hsp : 0 ≤ sp) (hpos : 0 ≤ α - 3 * sp / 4) {ℓ ζ : ℂ} (hℓ : ℓ ∈ range (i1 α sp ψu))
    (hζ : ζ ∈ blockNorm α) : dist ℓ (pol α ψu) ≤ dist ℓ ζ := by
  obtain ⟨R, hR, rfl⟩ := mem_i1 hpos hℓ
  rw [Complex.dist_eq, norm_pol_sub_pol_same_angle, abs_of_nonpos (by linarith [hR.2])]
  have := dist_ge_of_norm (norm_pol_le (θ := ψu) hR.1 le_rfl) hζ.1.le
  linarith

 
theorem K6_o1 (hsp : 0 ≤ sp) (hsp1 : sp ≤ 2 / 3) {ℓ ζ : ℂ} (hℓ : ℓ ∈ range (o1 sp ψv))
    (hζ : ζ ∈ blockNorm α) : dist ℓ (pol 1 ψv) ≤ dist ℓ ζ := by
  obtain ⟨R, hR, rfl⟩ := mem_o1 hsp1 hℓ
  rw [Complex.dist_eq, norm_pol_sub_pol_same_angle, abs_of_nonneg (by linarith [hR.1])]
  have := dist_ge_of_norm' (le_norm_pol (R := R) (A := R) (θ := ψv) (by linarith [hR.1]) le_rfl)
    hζ.2.1.le
  linarith

 
theorem K7_u (hα : 0 ≤ α) (hsp : 0 ≤ sp) (hsp1 : sp ≤ 2 / 3) {y : ℂ}
    (hy : y ∈ range (outPath sp ψv Δ) ∪ corrOutH Δ) : 1 + 3 * sp / 4 - α ≤ dist (pol α ψu) y := by
  have hyn : 1 + 3 * sp / 4 ≤ ‖y‖ := by
    rcases hy with hy | hy
    · exact norm_ge_of_mem_outPath hsp hsp1 hy
    · have := norm_ge_of_mem_corrOutH hy; linarith
  exact dist_ge_of_norm (norm_pol_le hα le_rfl) hyn

 
theorem K7_v (hpos : 0 ≤ α - 3 * sp / 4)
    (hψv : ψv ∈ Icc (-(π / 2)) (π / 2)) {x : ℂ}
    (hx : x ∈ range (inPath α sp ψu Δ) ∪ corrInH Δ) : 1 - α + 3 * sp / 4 ≤ dist (pol 1 ψv) x := by
  have hvn : ‖pol 1 ψv‖ = 1 := norm_pol (by norm_num) _
  rcases hx with hx | hx
  · rw [range_inPath] at hx
    rcases hx with hx | hx
    · by_cases h2 : x ∈ range i2
      · obtain ⟨R, hR, rfl⟩ := mem_i2 h2
        have hre : 0 ≤ (pol 1 ψv).re := by
          rw [pol_re, one_mul]; exact Real.cos_nonneg_of_mem_Icc hψv
        have := dist_negReal_ge hR.1 hre
        rw [hvn, dist_comm] at this; linarith
      · have := dist_ge_of_norm (le_of_eq hvn) (norm_ge_of_mem_inRest hx h2); linarith
    · obtain ⟨R, hR, rfl⟩ := mem_i1 hpos hx
      have := dist_ge_of_norm' (le_of_eq hvn.symm) (norm_pol_le (θ := ψu) hR.1 hR.2); linarith
  · have := dist_ge_of_norm (le_of_eq hvn) (norm_ge_of_mem_corrInH hx); linarith

 
theorem K8 (hα : 0 ≤ α) : 1 - α ≤ dist (pol α ψu) (pol 1 ψv) := by
  have := dist_ge_of_norm (norm_pol_le (θ := ψu) hα le_rfl) (le_norm_pol (θ := ψv) zero_le_one le_rfl)
  linarith

end Rows

 

section Spine

variable {α sp ψu ψv : ℝ}

theorem clampAng_mem (hsp2 : sp ≤ 2) (ψ : ℝ) :
    clampAng sp ψ ∈ Icc (-(π / 2) + sp / 4) (π / 2 - sp / 4) := by
  have hL : -(π / 2) + sp / 4 ≤ π / 2 - sp / 4 := by linarith [Real.pi_gt_three]
  exact ⟨le_max_left _ _, max_le hL (min_le_right _ _)⟩

theorem abs_clampAng_sub (hsp : 0 ≤ sp) (hsp2 : sp ≤ 2) {ψ : ℝ}
    (hψ : ψ ∈ Icc (-(π / 2)) (π / 2)) : |clampAng sp ψ - ψ| ≤ sp / 4 := by
  have hL : -(π / 2) + sp / 4 ≤ π / 2 - sp / 4 := by linarith [Real.pi_gt_three]
  unfold clampAng
  rw [abs_le]
  rcases le_total ψ (π / 2 - sp / 4) with h | h
  · rw [min_eq_left h]
    rcases le_total (-(π / 2) + sp / 4) ψ with h' | h'
    · rw [max_eq_right h']; constructor <;> linarith
    · rw [max_eq_left h']; constructor <;> linarith [hψ.1]
  · rw [min_eq_right h, max_eq_right hL]; constructor <;> linarith [hψ.2]

 
theorem blockSpine_mem (hα : 3 / 4 < α) (hα1 : α < 1) (hsp : 0 < sp) (hsp1 : 4 * sp ≤ 1 - α)
    (hψu : ψu ∈ Icc (-(π / 2)) (π / 2)) (hψv : ψv ∈ Icc (-(π / 2)) (π / 2)) {x : ℂ}
    (hx : x ∈ range (blockSpine α sp ψu ψv)) :
    x ∈ ball (pol α ψu) sp ∨ x ∈ blockNorm α ∨ x ∈ ball (pol 1 ψv) sp := by
  have hsp2 : sp ≤ 2 := by linarith
  simp only [blockSpine, Path.trans_range, mem_union] at hx
  rcases hx with hx | hx | hx | hx | hx
  · left
    obtain ⟨R, hR, rfl⟩ := mem_range_polarPath_spoke hx
    rw [uIcc_of_le (by linarith)] at hR
    rw [mem_ball, Complex.dist_eq, norm_pol_sub_pol_same_angle, abs_lt]
    constructor <;> linarith [hR.1, hR.2]
  · left
    obtain ⟨φ, hφ, rfl⟩ := mem_range_polarPath_arc hx
    rw [mem_ball]
    have h1 : ‖pol (α + sp / 2) φ - pol (α + sp / 2) ψu‖ ≤ (α + sp / 2) * (sp / 4) := by
      have := norm_pol_sub_pol_le (α + sp / 2) φ ψu
      rw [abs_of_nonneg (by linarith)] at this
      have h2 : |φ - ψu| ≤ sp / 4 := (abs_sub_left_le hφ).trans (abs_clampAng_sub hsp.le hsp2 hψu)
      exact this.trans (mul_le_mul_of_nonneg_left h2 (by linarith))
    have h3 : ‖pol (α + sp / 2) ψu - pol α ψu‖ = sp / 2 := by
      rw [norm_pol_sub_pol_same_angle, show α + sp / 2 - α = sp / 2 by ring,
        abs_of_nonneg (by linarith)]
    rw [Complex.dist_eq]
    calc ‖pol (α + sp / 2) φ - pol α ψu‖
        ≤ ‖pol (α + sp / 2) φ - pol (α + sp / 2) ψu‖ + ‖pol (α + sp / 2) ψu - pol α ψu‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ (α + sp / 2) * (sp / 4) + sp / 2 := by rw [h3]; linarith
      _ < sp := by nlinarith
  · right; left
    obtain ⟨R, hR, φ, hφ, rfl⟩ := mem_range_polarPath hx
    rw [uIcc_of_le (by linarith)] at hR
    have hφ' : φ ∈ Icc (-(π / 2) + sp / 4) (π / 2 - sp / 4) :=
      uIcc_subset_Icc (clampAng_mem hsp2 ψu) (clampAng_mem hsp2 ψv) hφ
    have hR0 : 0 ≤ R := by linarith [hR.1]
    refine ⟨?_, ?_, ?_⟩
    · rw [norm_pol hR0]; linarith [hR.1]
    · rw [norm_pol hR0]; linarith [hR.2]
    · rw [pol_re]
      apply mul_pos (by linarith [hR.1])
      apply Real.cos_pos_of_mem_Ioo
      constructor <;> linarith [hφ'.1, hφ'.2]
  · right; right
    obtain ⟨φ, hφ, rfl⟩ := mem_range_polarPath_arc hx
    rw [mem_ball]
    have h1 : ‖pol (1 - sp / 2) φ - pol (1 - sp / 2) ψv‖ ≤ (1 - sp / 2) * (sp / 4) := by
      have := norm_pol_sub_pol_le (1 - sp / 2) φ ψv
      rw [abs_of_nonneg (by linarith)] at this
      have h2 : |φ - ψv| ≤ sp / 4 := by
        have := abs_sub_right_le hφ
        rw [abs_sub_comm ψv] at this
        exact this.trans (abs_clampAng_sub hsp.le hsp2 hψv)
      exact this.trans (mul_le_mul_of_nonneg_left h2 (by linarith))
    have h3 : ‖pol (1 - sp / 2) ψv - pol 1 ψv‖ = sp / 2 := by
      rw [norm_pol_sub_pol_same_angle, show 1 - sp / 2 - 1 = -(sp / 2) by ring, abs_neg,
        abs_of_nonneg (by linarith)]
    rw [Complex.dist_eq]
    calc ‖pol (1 - sp / 2) φ - pol 1 ψv‖
        ≤ ‖pol (1 - sp / 2) φ - pol (1 - sp / 2) ψv‖ + ‖pol (1 - sp / 2) ψv - pol 1 ψv‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ (1 - sp / 2) * (sp / 4) + sp / 2 := by rw [h3]; linarith
      _ < sp := by nlinarith
  · right; right
    obtain ⟨R, hR, rfl⟩ := mem_range_polarPath_spoke hx
    rw [uIcc_of_le (by linarith)] at hR
    rw [mem_ball, Complex.dist_eq, norm_pol_sub_pol_same_angle, abs_lt]
    constructor <;> linarith [hR.1, hR.2]

theorem norm_le_of_mem_blockSpine (hα : 3 / 4 < α) (hα1 : α < 1) (hsp : 0 < sp)
    (hsp1 : 4 * sp ≤ 1 - α) (hψu : ψu ∈ Icc (-(π / 2)) (π / 2))
    (hψv : ψv ∈ Icc (-(π / 2)) (π / 2)) {x : ℂ} (hx : x ∈ range (blockSpine α sp ψu ψv)) :
    ‖x‖ ≤ 1 + sp := by
  rcases blockSpine_mem hα hα1 hsp hsp1 hψu hψv hx with h | h | h
  · rw [mem_ball, Complex.dist_eq] at h
    have := norm_le_norm_add_norm_sub' x (pol α ψu)
    rw [norm_pol (by linarith)] at this; linarith
  · linarith [h.2.1]
  · rw [mem_ball, Complex.dist_eq] at h
    have := norm_le_norm_add_norm_sub' x (pol 1 ψv)
    rw [norm_pol (by norm_num)] at this; linarith

end Spine

end SupercriticalLQGUniqueness.Uniqueness.Objects.Tube
