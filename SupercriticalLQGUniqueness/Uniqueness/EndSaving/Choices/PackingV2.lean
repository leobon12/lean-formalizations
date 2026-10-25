import SupercriticalLQGUniqueness.Uniqueness.EndSaving.Choices.StableV2




 










set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Finset Filter
open scoped ENNReal Topology

namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.Choices

 
theorem le_dist_of_euclidSetDist {A B : Set ℂ} {d : ℝ}
    (h : ENNReal.ofReal d ≤ EndSaving.Interfaces.euclidSetDist A B) {x y : ℂ} (hx : x ∈ A) (hy : y ∈ B) :
    d ≤ dist x y := by
  have h1 : EndSaving.Interfaces.euclidSetDist A B ≤ ENNReal.ofReal (dist x y) :=
    iInf₂_le_of_le x hx (iInf₂_le y hy)
  have h2 := h.trans h1
  by_cases hd : d ≤ 0
  · exact hd.trans dist_nonneg
  · exact (ENNReal.ofReal_le_ofReal_iff dist_nonneg).mp h2

 
theorem far_of_near {K₁ A : Set ℂ} (hK₁ : IsCompact K₁) (hne : K₁.Nonempty) {d s : ℝ}
    (hfar : ENNReal.ofReal d ≤ EndSaving.Interfaces.euclidSetDist K₁ A) {x : ℂ}
    (hx : Metric.infDist x K₁ ≤ s) {y : ℂ} (hy : y ∈ A) :
    d - s ≤ dist x y := by
  obtain ⟨w, hw, hwx⟩ := hK₁.exists_infDist_eq_dist hne x
  have hd := le_dist_of_euclidSetDist hfar hw hy
  have htri : dist w y ≤ dist w x + dist x y := dist_triangle _ _ _
  rw [dist_comm w x, ← hwx] at htri
  linarith

 
theorem exists_level_times {P : ℝ → ℂ} {T : ℝ} (hP : ContinuousOn P (Icc 0 T))
    (hT : 0 ≤ T) {K₁ : Set ℂ} (hP0 : P 0 ∈ K₁) {L : ℝ} (hPT : L ≤ Metric.infDist (P T) K₁)
    (lev : ℕ → ℝ) (J : ℕ) (hlev0 : ∀ j ≤ J, 0 ≤ lev j) (hlevL : ∀ j ≤ J, lev j ≤ L) :
    ∃ t : ℕ → ℝ, ∀ j ≤ J, t j ∈ Icc 0 T ∧ Metric.infDist (P (t j)) K₁ = lev j := by
  have hg : ContinuousOn (fun u => Metric.infDist (P u) K₁) (Icc 0 T) :=
    (Metric.continuous_infDist_pt K₁).comp_continuousOn hP
  have hex : ∀ j, j ≤ J → ∃ t ∈ Icc 0 T, Metric.infDist (P t) K₁ = lev j := by
    intro j hj
    have h0 : Metric.infDist (P 0) K₁ = 0 := Metric.infDist_zero_of_mem hP0
    obtain ⟨t, ht, hteq⟩ := intermediate_value_Icc hT hg
      ⟨by rw [h0]; exact hlev0 j hj, (hlevL j hj).trans hPT⟩
    exact ⟨t, ht, hteq⟩
  choose! t ht using hex
  exact ⟨t, fun j hj => ht j hj⟩

 
theorem level_points_sep {K : Set ℂ} {x y : ℂ} :
    |Metric.infDist x K - Metric.infDist y K| ≤ dist x y := by
  rw [abs_le]
  constructor
  · have := Metric.infDist_le_infDist_add_dist (x := y) (y := x) (s := K)
    rw [dist_comm] at this
    linarith
  · have := Metric.infDist_le_infDist_add_dist (x := x) (y := y) (s := K)
    linarith

 
theorem admissible_floor_injective (R : EndSaving.Interfaces.AdmissibleRadii) {r s : ℝ}
    (hr : r ∈ R.radii) (hs : s ∈ R.radii)
    (hfl : ⌊Real.logb 8 r⌋ = ⌊Real.logb 8 s⌋) : r = s := by
  by_contra hne
  have hr0 : 0 < r := (R.subset_unit hr).1
  have hs0 : 0 < s := (R.subset_unit hs).1
  have key : ∀ a c : ℝ, a ∈ R.radii → c ∈ R.radii → 0 < a → a < c →
      ⌊Real.logb 8 a⌋ < ⌊Real.logb 8 c⌋ := by
    intro a c ha hc ha0 hac
    have h8 := R.separated ha hc hac
    have hlog : Real.logb 8 a + 1 ≤ Real.logb 8 c := by
      have hc8 : Real.logb 8 (8 * a) ≤ Real.logb 8 c :=
        Real.logb_le_logb_of_le (by norm_num) (by positivity) h8
      rw [Real.logb_mul (by norm_num) ha0.ne', Real.logb_self_eq_one (by norm_num)] at hc8
      linarith
    have := Int.floor_le (Real.logb 8 a)
    have := Int.lt_floor_add_one (Real.logb 8 a)
    have h1 : ⌊Real.logb 8 a⌋ + 1 ≤ ⌊Real.logb 8 c⌋ := by
      rw [← Int.cast_le (R := ℝ)]
      push_cast
      have := Int.floor_le (Real.logb 8 a)
      have hfc : ((⌊Real.logb 8 a⌋ + 1 : ℤ) : ℝ) ≤ Real.logb 8 c := by push_cast; linarith
      exact_mod_cast (Int.le_floor.mpr hfc)
    omega
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact absurd hfl (key r s hr hs hr0 hlt).ne
  · exact absurd hfl.symm (key s r hs hr hs0 hgt).ne

 
theorem floor_logb_mem_box {ε b r : ℝ} (hε : 0 < ε) (hb : 0 < b)
    (hlo : ε ^ 2 * b ≤ r) (hhi : r ≤ ε * b) :
    ⌊Real.logb 8 r⌋ ∈ Finset.Icc ⌊Real.logb 8 (ε ^ 2 * b)⌋ ⌊Real.logb 8 (ε * b)⌋ := by
  have hpos : 0 < ε ^ 2 * b := by positivity
  rw [Finset.mem_Icc]
  exact ⟨Int.floor_mono (Real.logb_le_logb_of_le (by norm_num) hpos hlo),
    Int.floor_mono (Real.logb_le_logb_of_le (by norm_num) (hpos.trans_le hlo) hhi)⟩

theorem card_floor_box_le {ε b : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hb : 0 < b) :
    ((Finset.Icc ⌊Real.logb 8 (ε ^ 2 * b)⌋ ⌊Real.logb 8 (ε * b)⌋).card : ℝ) ≤
      Real.logb 8 ε⁻¹ + 2 := by
  rw [Int.card_Icc]
  have hdiff : Real.logb 8 (ε * b) - Real.logb 8 (ε ^ 2 * b) = Real.logb 8 ε⁻¹ := by
    rw [Real.logb_mul hε.ne' hb.ne', Real.logb_mul (by positivity) hb.ne', Real.logb_pow,
      Real.logb_inv]
    ring
  have h1 := Int.floor_le (Real.logb 8 (ε * b))
  have h2 := Int.lt_floor_add_one (Real.logb 8 (ε ^ 2 * b))
  have hnn : (0 : ℤ) ≤ ⌊Real.logb 8 (ε * b)⌋ + 1 - ⌊Real.logb 8 (ε ^ 2 * b)⌋ ∨
      ⌊Real.logb 8 (ε * b)⌋ + 1 - ⌊Real.logb 8 (ε ^ 2 * b)⌋ < 0 := le_or_gt _ _
  have hlog0 : 0 ≤ Real.logb 8 ε⁻¹ :=
    Real.logb_nonneg (by norm_num) (one_le_inv₀ hε |>.mpr hε1)
  rcases hnn with hnn | hneg
  · rw [← Int.cast_natCast, Int.toNat_of_nonneg hnn]
    push_cast
    linarith
  · rw [Int.toNat_of_nonpos hneg.le]
    push_cast
    linarith

 
theorem exists_dyadic_bin {y : ℝ} (hy : 0 < y) :
    ∃ ℓ : ℤ, (2 : ℝ) ^ ℓ ≤ y ∧ y ≤ 2 * (2 : ℝ) ^ ℓ ∧ ℓ = ⌊Real.logb 2 y⌋ := by
  refine ⟨⌊Real.logb 2 y⌋, ?_, ?_, rfl⟩
  · have h := Int.floor_le (Real.logb 2 y)
    have : (2 : ℝ) ^ (⌊Real.logb 2 y⌋ : ℝ) ≤ (2 : ℝ) ^ (Real.logb 2 y) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) h
    rwa [Real.rpow_logb (by norm_num) (by norm_num) hy, Real.rpow_intCast] at this
  · have h := (Int.lt_floor_add_one (Real.logb 2 y)).le
    have : (2 : ℝ) ^ (Real.logb 2 y) ≤ (2 : ℝ) ^ ((⌊Real.logb 2 y⌋ : ℝ) + 1) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) h
    rwa [Real.rpow_logb (by norm_num) (by norm_num) hy, Real.rpow_add (by norm_num),
      Real.rpow_intCast, Real.rpow_one, mul_comm] at this

 
theorem dyadic_exp_mem_box {lo hi : ℝ} (hlo : 0 < lo) {ℓ : ℤ}
    (h1 : lo ≤ (2 : ℝ) ^ ℓ) (h2 : (2 : ℝ) ^ ℓ ≤ hi) :
    ℓ ∈ Finset.Icc ⌈Real.logb 2 lo⌉ ⌊Real.logb 2 hi⌋ := by
  have hz : (2 : ℝ) ^ ℓ = (2 : ℝ) ^ (ℓ : ℝ) := (Real.rpow_intCast 2 ℓ).symm
  have hlog : Real.logb 2 ((2 : ℝ) ^ ℓ) = ℓ := by
    rw [hz, Real.logb_rpow (by norm_num) (by norm_num)]
  have hpos : 0 < (2 : ℝ) ^ ℓ := zpow_pos (by norm_num) ℓ
  rw [Finset.mem_Icc]
  constructor
  · apply Int.ceil_le.mpr
    rw [← hlog]
    exact Real.logb_le_logb_of_le (by norm_num) hlo h1
  · apply Int.le_floor.mpr
    rw [← hlog]
    exact Real.logb_le_logb_of_le (by norm_num) hpos h2

theorem card_dyadic_box_le {lo hi : ℝ} (_hlo : 0 < lo) :
    ((Finset.Icc ⌈Real.logb 2 lo⌉ ⌊Real.logb 2 hi⌋).card : ℝ) ≤
      max 0 (Real.logb 2 hi - Real.logb 2 lo + 1) := by
  rw [Int.card_Icc]
  have h1 := Int.floor_le (Real.logb 2 hi)
  have h2 := Int.le_ceil (Real.logb 2 lo)
  rcases le_or_gt (0 : ℤ) (⌊Real.logb 2 hi⌋ + 1 - ⌈Real.logb 2 lo⌉) with hnn | hneg
  · rw [← Int.cast_natCast, Int.toNat_of_nonneg hnn]
    push_cast
    exact le_max_of_le_right (by linarith)
  · rw [Int.toNat_of_nonpos hneg.le]
    push_cast
    exact le_max_left _ _


end SupercriticalLQGUniqueness.Uniqueness.EndSaving.Choices
