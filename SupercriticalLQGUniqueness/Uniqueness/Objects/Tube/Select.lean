import SupercriticalLQGUniqueness.Uniqueness.Objects.Tube.G1




 










set_option autoImplicit false

noncomputable section

open Complex Set Metric Real

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Tube

 
theorem dist_pol_le (R S a b : ℝ) : dist (pol R a) (pol S b) ≤ |R - S| + |S| * |a - b| := by
  rw [Complex.dist_eq]
  calc ‖pol R a - pol S b‖ ≤ ‖pol R a - pol S a‖ + ‖pol S a - pol S b‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ |R - S| + |S| * |a - b| := by
        rw [norm_pol_sub_pol_same_angle]; linarith [norm_pol_sub_pol_le S a b]

theorem pol_add_two_pi (R θ : ℝ) : pol R (θ + 2 * π) = pol R θ := by
  unfold pol; rw [ex_add_two_pi]

theorem pol_sub_two_pi (R θ : ℝ) : pol R (θ - 2 * π) = pol R θ := by
  rw [← pol_add_two_pi R (θ - 2 * π), sub_add_cancel]

namespace TubeParams

variable {P : TubeParams} {r Asup : ℝ}

 

def EEvent (P : TubeParams) (r Asp : ℝ) (F : ℂ → Prop) : Prop :=
  ∀ θ₀ θ₁ : ℝ, 0 ≤ θ₁ - θ₀ → θ₁ - θ₀ ≤ 2 * π → Asp * r / 2 ≤ 2 * r * (θ₁ - θ₀) →
    ∃ k : ℤ, F (P.site r k) ∧ ∃ θ ∈ Icc θ₀ θ₁, P.site r k = pol (2 * r) θ

theorem ω_lt_ω (hK : (0 : ℝ) < P.K) {k k' : ℤ} (h : k < k') : P.ω k < P.ω k' := by
  unfold ω
  apply div_lt_div_of_pos_right _ hK
  have : (k : ℝ) < k' := by exact_mod_cast h
  nlinarith [Real.pi_pos]

theorem ω_le_ω (hK : (0 : ℝ) < P.K) {k k' : ℤ} (h : k ≤ k') : P.ω k ≤ P.ω k' := by
  rcases h.lt_or_eq with h | h
  · exact (ω_lt_ω hK h).le
  · rw [h]

theorem lt_of_ω_lt (hK : (0 : ℝ) < P.K) {k k' : ℤ} (h : P.ω k < P.ω k') : k < k' := by
  by_contra hc
  exact absurd h (not_lt.mpr (ω_le_ω hK (not_lt.mp hc)))

theorem ω_add_K_mul (hK : (P.K : ℝ) ≠ 0) (k n : ℤ) : P.ω (k + P.K * n) = P.ω k + 2 * π * n := by
  unfold ω; push_cast; field_simp

theorem site_add_K_mul (hK : (P.K : ℝ) ≠ 0) (k n : ℤ) : P.site r (k + P.K * n) = P.site r k := by
  unfold site pol
  rw [ω_add_K_mul hK, show 2 * π * (n : ℝ) = n * (2 * π) by ring, ex_add_int_mul_two_pi]

 
theorem exists_index_of_site_eq (hr : 0 < r) (hK : (P.K : ℝ) ≠ 0) {k : ℤ} {θ : ℝ}
    (h : P.site r k = pol (2 * r) θ) : ∃ j : ℤ, P.site r j = P.site r k ∧ P.ω j = θ := by
  unfold site pol at h
  have h2r : ((2 * r : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by linarith : (2 * r : ℝ) ≠ 0)
  have hex : ex (P.ω k) = ex θ := mul_left_cancel₀ h2r h
  unfold ex at hex
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hex
  have hθ : P.ω k = θ + n * (2 * π) := by
    have e : (θ : ℂ) * Complex.I + (n : ℂ) * (2 * (π : ℂ) * Complex.I) =
        ((θ + n * (2 * π) : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [e] at hn
    exact_mod_cast mul_right_cancel₀ Complex.I_ne_zero hn
  refine ⟨k + P.K * (-n), site_add_K_mul hK k (-n), ?_⟩
  rw [ω_add_K_mul hK, hθ]; push_cast; ring

 
theorem not_mem_closure_of_far {S : Set ℂ} {x : ℂ} {c : ℝ} (hc : 0 < c)
    (h : ∀ z ∈ S, c ≤ dist x z) : x ∉ closure S := by
  intro hx
  obtain ⟨z, hz, hxz⟩ := Metric.mem_closure_iff.mp hx c hc
  linarith [h z hz]

section Select

variable (hP : P.Good) (hr : 0 < r) (hA0 : 0 < Asup) (hA : 100 * Asup ≤ P.sp * P.ρ)
include hP hr hA0 hA

omit hA in
 
theorem nbhd_eq_window (lo : ℤ) :
    P.nbhd r Asup = ⋃ i ∈ Icc lo (lo + 4 * P.K - 1), P.X r Asup i := by
  have hm : 0 < P.ρ * r := mul_pos hP.ρ_pos hr
  have hs : 0 < P.s r := by unfold s; have := hP.sp_pos; have := hP.ρ_pos; positivity
  have hw : 0 < P.w r := by unfold w; have := hP.wp_pos; have := hP.ρ_pos; positivity
  rw [nbhd_eq_iUnion_X hs hw (mul_pos hA0 hr)]
  apply Subset.antisymm
  · intro x hx
    rw [mem_iUnion] at hx
    obtain ⟨i, hx⟩ := hx
    have hKZ : (0 : ℤ) < P.K := by have := hP.K_pos; exact_mod_cast this
    set i' := lo + (i - lo) % (4 * P.K) with hi'
    have hmod0 : 0 ≤ (i - lo) % (4 * (P.K : ℤ)) := Int.emod_nonneg _ (by omega)
    have hmod1 : (i - lo) % (4 * (P.K : ℤ)) < 4 * P.K := Int.emod_lt_of_pos _ (by omega)
    have hdecomp := Int.mul_ediv_add_emod (i - lo) (4 * P.K)
    have hii : i = i' + 4 * (P.K * ((i - lo) / (4 * P.K))) := by rw [hi']; linarith
    rw [hii, X_add_mul hP.K_ne] at hx
    exact mem_biUnion (x := i') ⟨by omega, by omega⟩ hx
  · exact iUnion₂_subset fun i _ => subset_iUnion (P.X r Asup) i

theorem X_inSector (i : ℤ) {x : ℂ} (hx : x ∈ P.X r Asup i) :
    InSector x (2 * r - 11 * (P.ρ * r)) (P.ω (i / 4) - 5 * P.ρ) (P.ω (i / 4 + 1) + 5 * P.ρ) :=
  piece_inSector hP hr hA0 hA hx

theorem X_inSector_module (i : ℤ) (ha : i % 4 ≤ 2) {x : ℂ} (hx : x ∈ P.X r Asup i) :
    InSector x (2 * r - 11 * (P.ρ * r)) (P.ω (i / 4) - 5 * P.ρ) (P.ω (i / 4) + 5 * P.ρ) := by
  have hm : 0 < P.ρ * r := mul_pos hP.ρ_pos hr
  have h1 := dist_piece_site_le hP hr hA0 hA (k := i / 4) (a := (i % 4).toNat) (by omega) hx
  exact inSector_near_site' hP hr (by linarith)

 
theorem X_inSector_range {j j' i : ℤ} (hi1 : 4 * j ≤ i) (hi2 : i ≤ 4 * j' + 2) {x : ℂ}
    (hx : x ∈ P.X r Asup i) :
    InSector x (2 * r - 11 * (P.ρ * r)) (P.ω j - 5 * P.ρ) (P.ω j' + 5 * P.ρ) := by
  have hK := hP.K_pos
  rcases (show i % 4 ≤ 2 ∨ i % 4 = 3 by omega) with ha | ha
  · refine (X_inSector_module hP hr hA0 hA i ha hx).mono le_rfl ?_ ?_
    · linarith [ω_le_ω (P := P) hK (show j ≤ i / 4 by omega)]
    · linarith [ω_le_ω (P := P) hK (show i / 4 ≤ j' by omega)]
  · refine (X_inSector hP hr hA0 hA i hx).mono le_rfl ?_ ?_
    · linarith [ω_le_ω (P := P) hK (show j ≤ i / 4 by omega)]
    · linarith [ω_le_ω (P := P) hK (show i / 4 + 1 ≤ j' by omega)]

omit hA0 in
 

theorem select_angles {Asp : ℝ} (hρAsp : 10 ^ 4 * P.ρ ≤ Asp) {x y : ℂ}
    (hx : x ∈ closure (P.nbhd r Asup)) (hy : y ∈ closure (P.nbhd r Asup))
    (hxy : Asp * r ≤ dist x y) :
    ∃ φx φy : ℝ, pol ‖x‖ φx = x ∧ pol ‖y‖ φy = y ∧ φx < φy ∧ φy < φx + 2 * π ∧
      Asp / 3 ≤ φy - φx ∧ Asp / 3 ≤ φx + 2 * π - φy := by
  have hm : 0 < P.ρ * r := mul_pos hP.ρ_pos hr
  have hρ := hP.ρ_pos
  have hρ8 := hP.ρ_le
  have hlx := closure_nbhd_near_circle hP hr hA hx
  have hly := closure_nbhd_near_circle hP hr hA hy
  rw [abs_le] at hlx hly
  have h22 : |‖x‖ - ‖y‖| ≤ 22 * (P.ρ * r) := by rw [abs_le]; constructor <;> linarith
  have hsmall : 22 * (P.ρ * r) < Asp * r := by nlinarith
  have hxp : pol ‖x‖ (Complex.arg x) = x := pol_norm_arg x
  have hyp0 : pol ‖y‖ (Complex.arg y) = y := pol_norm_arg y
  have hφx1 := Complex.neg_pi_lt_arg x
  have hφx2 := Complex.arg_le_pi x
  have hφ01 := Complex.neg_pi_lt_arg y
  have hφ02 := Complex.arg_le_pi y
  have hny : 0 ≤ ‖y‖ := norm_nonneg y
  have hne : Complex.arg y ≠ Complex.arg x := by
    intro h
    have h1 := dist_pol_le ‖x‖ ‖y‖ (Complex.arg x) (Complex.arg y)
    rw [hxp, hyp0, h, sub_self, abs_zero, mul_zero, add_zero] at h1
    linarith
  obtain ⟨φy, hyp, hφ1, hφ2⟩ : ∃ φy, pol ‖y‖ φy = y ∧ Complex.arg x < φy ∧
      φy < Complex.arg x + 2 * π := by
    rcases lt_or_gt_of_ne hne with h | h
    · exact ⟨Complex.arg y + 2 * π, by rw [pol_add_two_pi, hyp0], by linarith, by linarith⟩
    · exact ⟨Complex.arg y, hyp0, h, by linarith⟩
  refine ⟨Complex.arg x, φy, hxp, hyp, hφ1, hφ2, ?_, ?_⟩
  · have h1 := dist_pol_le ‖x‖ ‖y‖ (Complex.arg x) φy
    rw [hxp, hyp, abs_of_nonneg hny, abs_of_neg (by linarith : Complex.arg x - φy < 0)] at h1
    by_contra hcon
    have hlt : φy - Complex.arg x < Asp / 3 := not_le.mp hcon
    nlinarith
  · have hyp' : pol ‖y‖ (φy - 2 * π) = y := by rw [pol_sub_two_pi, hyp]
    have h1 := dist_pol_le ‖x‖ ‖y‖ (Complex.arg x) (φy - 2 * π)
    rw [hxp, hyp', abs_of_nonneg hny,
      abs_of_nonneg (by linarith : 0 ≤ Complex.arg x - (φy - 2 * π))] at h1
    by_contra hcon
    have hlt : Complex.arg x + 2 * π - φy < Asp / 3 := not_le.mp hcon
    nlinarith

omit hA0 hA in
 

theorem select_indices {Asp : ℝ} (hρAsp : 10 ^ 4 * P.ρ ≤ Asp) {F : ℂ → Prop}
    (hE : EEvent P r Asp F) {φx φy : ℝ} (h1 : Asp / 3 ≤ φy - φx) (h2 : Asp / 3 ≤ φx + 2 * π - φy) :
    ∃ j j' : ℤ, F (P.site r j) ∧ F (P.site r j') ∧
      P.ω j ∈ Icc (φx + 100 * P.ρ) (φy - 100 * P.ρ) ∧
      P.ω j' ∈ Icc (φy + 100 * P.ρ) (φx + 2 * π - 100 * P.ρ) := by
  have hρ := hP.ρ_pos
  have hKne := hP.K_ne
  obtain ⟨k₁, hF₁, θa, hθa, hsite₁⟩ := hE (φx + 100 * P.ρ) (φy - 100 * P.ρ) (by linarith)
    (by linarith) (by nlinarith)
  obtain ⟨j, hj, hωj⟩ := exists_index_of_site_eq hr hKne hsite₁
  obtain ⟨k₂, hF₂, θb, hθb, hsite₂⟩ := hE (φy + 100 * P.ρ) (φx + 2 * π - 100 * P.ρ)
    (by linarith) (by linarith) (by nlinarith)
  obtain ⟨j', hj', hωj'⟩ := exists_index_of_site_eq hr hKne hsite₂
  exact ⟨j, j', by rw [hj]; exact hF₁, by rw [hj']; exact hF₂, by rw [hωj]; exact hθa,
    by rw [hωj']; exact hθb⟩

omit hr hA0 hA in
 
theorem select_order {φx φy : ℝ} {j j' : ℤ}
    (hj : P.ω j ∈ Icc (φx + 100 * P.ρ) (φy - 100 * P.ρ))
    (hj' : P.ω j' ∈ Icc (φy + 100 * P.ρ) (φx + 2 * π - 100 * P.ρ)) : j < j' ∧ j' < j + P.K := by
  have hρ := hP.ρ_pos
  have hK := hP.K_pos
  refine ⟨lt_of_ω_lt hK (by linarith [hj.2, hj'.1]), ?_⟩
  have h1 := ω_add_K_mul hP.K_ne j 1
  rw [mul_one, Int.cast_one, mul_one] at h1
  exact lt_of_ω_lt hK (by rw [h1]; linarith [hj.1, hj'.2])

omit hA0 hA in
 

theorem select_far {z : ℂ} {φ : ℝ} {j : ℤ} (hz : pol ‖z‖ φ = z) (hzn : 2 * r - 11 * (P.ρ * r) ≤ ‖z‖)
    (h1 : 100 * P.ρ ≤ P.ω j - φ) (h2 : 100 * P.ρ ≤ φ + 2 * π - P.ω j) :
    100 * (P.ρ * r) < dist z (P.site r j) := by
  have hm : 0 < P.ρ * r := mul_pos hP.ρ_pos hr
  have hρ := hP.ρ_pos
  have hρ8 := hP.ρ_le
  have hπ := Real.pi_pos
  have hπ4 := Real.pi_lt_d2
  have hm₀ : 0 ≤ 2 * r - 11 * (P.ρ * r) := by nlinarith
  have hsz : InSector z (2 * r - 11 * (P.ρ * r)) φ φ := ⟨‖z‖, hzn, φ, ⟨le_rfl, le_rfl⟩, hz.symm⟩
  have hsj : InSector (P.site r j) (2 * r - 11 * (P.ρ * r)) (P.ω j) (P.ω j) :=
    ⟨2 * r, by nlinarith, P.ω j, ⟨le_rfl, le_rfl⟩, rfl⟩
  have d := dist_ge_of_sectors hm₀ hsz hsj (by positivity) (by nlinarith) h1 h2
  have hfar : 100 * (P.ρ * r) < 2 * (2 * r - 11 * (P.ρ * r)) * (100 * P.ρ) / π := by
    rw [lt_div_iff₀ hπ]; nlinarith
  linarith

 
theorem select_mem_S0 {x : ℂ} {φx : ℝ} {j j' : ℤ} (hx : x ∈ closure (P.nbhd r Asup))
    (hxp : pol ‖x‖ φx = x) (hxn : 2 * r - 11 * (P.ρ * r) ≤ ‖x‖)
    (hj : φx + 100 * P.ρ ≤ P.ω j) (hj' : P.ω j' ≤ φx + 2 * π - 100 * P.ρ) :
    x ∈ closure (⋃ i ∈ Icc (4 * j' + 3) (4 * j + 4 * P.K - 1), P.X r Asup i) := by
  have hm : 0 < P.ρ * r := mul_pos hP.ρ_pos hr
  have hρ := hP.ρ_pos
  have hρ8 := hP.ρ_le
  have hπ := Real.pi_pos
  have hπ3 := Real.pi_gt_three
  have hm₀ : 0 < 2 * r - 11 * (P.ρ * r) := by nlinarith
  have hsx : InSector x (2 * r - 11 * (P.ρ * r)) φx φx := ⟨‖x‖, hxn, φx, ⟨le_rfl, le_rfl⟩, hxp.symm⟩
  have hpos : 0 < 2 * (2 * r - 11 * (P.ρ * r)) * (95 * P.ρ) / π := by positivity
  rw [nbhd_eq_window hP hr hA0 (4 * j), (Set.finite_Icc _ _).closure_biUnion, mem_iUnion₂] at hx
  obtain ⟨i, hi, hxi⟩ := hx
  have hi1 := hi.1
  have hi2 := hi.2
  have hi' : 4 * j' + 3 ≤ i := by
    by_contra hcon
    apply not_mem_closure_of_far hpos _ hxi
    intro z hz
    have hzs := X_inSector_range hP hr hA0 hA (j := j) (j' := j') hi1 (by omega) hz
    exact dist_ge_of_sectors hm₀.le hsx hzs (by positivity) (by nlinarith) (by linarith)
      (by linarith)
  exact closure_mono (subset_biUnion_of_mem (u := P.X r Asup)
    (show i ∈ Icc (4 * j' + 3) (4 * j + 4 * P.K - 1) from ⟨hi', hi2⟩)) hxi

 
theorem select_mem_S4 {y : ℂ} {φy : ℝ} {j j' : ℤ} (hy : y ∈ closure (P.nbhd r Asup))
    (hyp : pol ‖y‖ φy = y) (hyn : 2 * r - 11 * (P.ρ * r) ≤ ‖y‖)
    (hj : P.ω j ≤ φy - 100 * P.ρ) (hj' : φy + 100 * P.ρ ≤ P.ω j') :
    y ∈ closure (⋃ i ∈ Icc (4 * j + 3) (4 * j' - 1), P.X r Asup i) := by
  have hm : 0 < P.ρ * r := mul_pos hP.ρ_pos hr
  have hρ := hP.ρ_pos
  have hρ8 := hP.ρ_le
  have hπ := Real.pi_pos
  have hπ3 := Real.pi_gt_three
  have hm₀ : 0 < 2 * r - 11 * (P.ρ * r) := by nlinarith
  have hsy : InSector y (2 * r - 11 * (P.ρ * r)) φy φy := ⟨‖y‖, hyn, φy, ⟨le_rfl, le_rfl⟩, hyp.symm⟩
  have hpos : 0 < 2 * (2 * r - 11 * (P.ρ * r)) * (95 * P.ρ) / π := by positivity
  rw [nbhd_eq_window hP hr hA0 (4 * j + 3), (Set.finite_Icc _ _).closure_biUnion, mem_iUnion₂] at hy
  obtain ⟨i, hi, hyi⟩ := hy
  have hi1 := hi.1
  have hi2 := hi.2
  have hi' : i ≤ 4 * j' - 1 := by
    by_contra hcon
    apply not_mem_closure_of_far hpos _ hyi
    intro z hz
    have hzs := X_inSector_range hP hr hA0 hA (j := j') (j' := j + P.K) (by omega) (by omega) hz
    have hωK := ω_add_K (P := P) hP.K_ne j
    exact dist_ge_of_sectors hm₀.le hsy hzs (by positivity) (by nlinarith) (by linarith)
      (by linarith)
  exact closure_mono (subset_biUnion_of_mem (u := P.X r Asup)
    (show i ∈ Icc (4 * j + 3) (4 * j' - 1) from ⟨hi1, hi'⟩)) hyi

 




theorem select {Asp : ℝ} (hρAsp : 10 ^ 4 * P.ρ ≤ Asp) {F : ℂ → Prop} (hE : EEvent P r Asp F)
    {x y : ℂ} (hx : x ∈ closure (P.nbhd r Asup)) (hy : y ∈ closure (P.nbhd r Asup))
    (hxy : Asp * r ≤ dist x y) :
    ∃ j j' : ℤ, F (P.site r j) ∧ F (P.site r j') ∧ j < j' ∧ j' < j + P.K ∧
      100 * (P.ρ * r) < dist x (P.site r j) ∧ 100 * (P.ρ * r) < dist y (P.site r j) ∧
      100 * (P.ρ * r) < dist x (P.site r j') ∧ 100 * (P.ρ * r) < dist y (P.site r j') ∧
      x ∈ closure (⋃ i ∈ Icc (4 * j' + 3) (4 * j + 4 * P.K - 1), P.X r Asup i) ∧
      y ∈ closure (⋃ i ∈ Icc (4 * j + 3) (4 * j' - 1), P.X r Asup i) := by
  have hρ := hP.ρ_pos
  obtain ⟨φx, φy, hxp, hyp, h12, h21, hg1, hg2⟩ := select_angles hP hr hA hρAsp hx hy hxy
  obtain ⟨j, j', hFj, hFj', hj, hj'⟩ := select_indices hP hr hρAsp hE hg1 hg2
  obtain ⟨hjj', hj'K⟩ := select_order hP hj hj'
  have hlx := closure_nbhd_near_circle hP hr hA hx
  have hly := closure_nbhd_near_circle hP hr hA hy
  rw [abs_le] at hlx hly
  have hyp' : pol ‖y‖ (φy - 2 * π) = y := by rw [pol_sub_two_pi, hyp]
  refine ⟨j, j', hFj, hFj', hjj', hj'K, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact select_far hP hr hxp (by linarith) (by linarith [hj.1]) (by linarith [hj.2])
  · exact select_far hP hr hyp' (by linarith) (by linarith [hj.1]) (by linarith [hj.2])
  · exact select_far hP hr hxp (by linarith) (by linarith [hj'.1]) (by linarith [hj'.2])
  · exact select_far hP hr hyp (by linarith) (by linarith [hj'.1]) (by linarith [hj'.2])
  · exact select_mem_S0 hP hr hA0 hA hx hxp (by linarith) hj.1 hj'.2
  · exact select_mem_S4 hP hr hA0 hA hy hyp (by linarith) hj.2 hj'.1

end Select

end TubeParams

end SupercriticalLQGUniqueness.Uniqueness.Objects.Tube
