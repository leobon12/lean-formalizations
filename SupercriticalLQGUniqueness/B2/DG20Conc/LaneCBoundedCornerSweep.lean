import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCCornerFirstTop

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Metric
namespace SupercriticalLQGUniqueness.B2.DG20Conc
open LQGMetric LQGMetric.DDDF

 

theorem laneC_corner_crosscut_of_bounded_lift
    (D : ContMetric) {ρ : ℝ → ℂ} {a b s t : ℝ}
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t)
    (hρ : ContinuousOn ρ (Icc a b))
    {c : ℂ} {r : ℝ}
    (hρann : ∀ x ∈ Icc a b,
      r < dist (ρ x) c ∧ dist (ρ x) c < 2 * r)
    (hcre0 : 0 ≤ c.re) (hcreNear : c.re ≤ r)
    (hcim1 : c.im ≤ 1) (hTopNear : 1 - c.im ≤ r)
    (hbelow : 2 * r ≤ c.im) (hright : c.re + 2 * r ≤ 1)
    {L : ℝ → ℂ} (hL : ContinuousOn L (Icc s t))
    (hlog : ∀ x ∈ Icc s t, Complex.exp (L x) = ρ x - c)
    (hsAng : (L s).im = Real.pi)
    (htAng : (L t).im = 5 * Real.pi / 2)
    (hAng : ∀ x ∈ Icc s t,
      Real.pi ≤ (L x).im ∧ (L x).im ≤ 5 * Real.pi / 2) :
    ∃ α : ℝ → ℂ,
      ContinuousOn α (Icc (0 : ℝ) 1) ∧
      (∀ v ∈ Icc (0 : ℝ) 1,
        r < dist (α v) c ∧ dist (α v) c < 2 * r ∧
          α v ∈ (rectAB 1 1).toSet) ∧
      α 0 ∈ (rectAB 1 1).side₁ ∧
      (α 1).im = 1 ∧
      D.len α 0 1 ≤ D.len ρ a b := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have hθ : ContinuousOn (fun x => (L x).im) (Icc s t) :=
    Complex.continuous_im.comp_continuousOn hL
  have hf : ContinuousOn (fun x => 2 * Real.pi - (L x).im) (Icc s t) :=
    continuousOn_const.sub hθ
  obtain ⟨u₀, hu₀, hu₀eq⟩ :
      ∃ u₀ ∈ Icc s t, 2 * Real.pi - (L u₀).im = 0 :=
    intermediate_value_Icc' hst hf ⟨by rw [htAng]; linarith,
      by rw [hsAng]; linarith⟩
  obtain ⟨u, hu, hueq, hupre⟩ :=
    laneC_exists_first_zero_nonneg hu₀.1
      (hf.mono (Icc_subset_Icc le_rfl hu₀.2))
      (by rw [hsAng]; linarith : 0 ≤ 2 * Real.pi - (L s).im)
      hu₀eq
  have huang : (L u).im = 2 * Real.pi := by linarith
  have huim : (ρ u).im = c.im := by
    have he := hlog u ⟨hu.1, hu.2.trans hu₀.2⟩
    have hi : (Complex.exp (L u)).im = 0 := by
      rw [Complex.exp_im, huang, Real.sin_two_pi]
      ring
    rw [he, Complex.sub_im] at hi
    linarith
  have hure : 0 ≤ (ρ u).re := by
    have he := hlog u ⟨hu.1, hu.2.trans hu₀.2⟩
    have hr := laneC_exp_right_half
      (by rw [huang]; linarith) (by rw [huang]; linarith)
    rw [he, Complex.sub_re] at hr
    linarith
  have hwest : (ρ s).re < 0 :=
    laneC_west_point_left (hlog s ⟨le_rfl, hst⟩)
      hsAng (hρann s hs).1 hcreNear
  have hfullOther : ∀ x ∈ Icc s t,
      0 ≤ (ρ x).im ∧ (ρ x).re ≤ 1 := by
    intro x hx
    have hxm : x ∈ Icc a b := ⟨hs.1.trans hx.1, hx.2.trans ht.2⟩
    have hd := (hρann x hxm).2
    have hn : ‖ρ x - c‖ < 2 * r := by simpa [dist_eq_norm] using hd
    have him := Complex.abs_im_le_norm (ρ x - c)
    have hre := Complex.abs_re_le_norm (ρ x - c)
    simp only [Complex.sub_im] at him
    simp only [Complex.sub_re] at hre
    constructor
    · linarith [(abs_le.mp him).1]
    · linarith [(abs_le.mp hre).2]
  have hpreU : ∀ x ∈ Icc s u, (ρ x).im ≤ 1 := by
    intro x hx
    have hxst : x ∈ Icc s t := ⟨hx.1, hx.2.trans (hu.2.trans hu₀.2)⟩
    have he := laneC_exp_lower_half (hAng x hxst).1
      (by linarith [hupre x hx])
    rw [hlog x hxst, Complex.sub_im] at he
    linarith
  by_cases htopEq : c.im = 1
  · have htop : (ρ u).im = 1 := by linarith
    have huMem : u ∈ Icc a b := ⟨hs.1.trans hu.1,
      (hu.2.trans hu₀.2).trans ht.2⟩
    exact laneC_corner_crosscut_of_first_top D hs huMem hu.1 hρ
      hρann hwest htop hure hpreU
      (fun x hx => hfullOther x ⟨hx.1, hx.2.trans (hu.2.trans hu₀.2)⟩)
  · have hstrict : c.im < 1 := lt_of_le_of_ne hcim1 htopEq
    have hnorth : 1 < (ρ t).im :=
      laneC_north_point_above (hlog t ⟨hst, le_rfl⟩)
        htAng (hρann t ht).1 hTopNear
    have hρtop : ContinuousOn (fun x => 1 - (ρ x).im) (Icc a b) :=
      continuousOn_const.sub (Complex.continuous_im.comp_continuousOn hρ)
    have hut : u ≤ t := hu.2.trans hu₀.2
    obtain ⟨q₀, hq₀, hq₀eq⟩ :
        ∃ q₀ ∈ Icc u t, 1 - (ρ q₀).im = 0 :=
      intermediate_value_Icc' hut
        (hρtop.mono (Icc_subset_Icc (hs.1.trans hu.1) ht.2))
        ⟨by linarith, by linarith⟩
    obtain ⟨q, hq, hqeq, hqpre⟩ :=
      laneC_exists_first_zero_nonneg hq₀.1
        (hρtop.mono (Icc_subset_Icc (hs.1.trans hu.1)
          (hq₀.2.trans ht.2)))
        (by linarith : 0 ≤ 1 - (ρ u).im) hq₀eq
    have hqst : q ∈ Icc s t := ⟨hu.1.trans hq.1,
      hq.2.trans hq₀.2⟩
    have hqAng : 2 * Real.pi ≤ (L q).im := by
      by_contra hn
      have hqlo := (hAng q hqst).1
      have he := laneC_exp_lower_half hqlo (le_of_not_ge hn)
      rw [hlog q hqst, Complex.sub_im] at he
      linarith
    have hqRe : 0 ≤ (ρ q).re := by
      have he := laneC_exp_right_half
        (by linarith : 3 * Real.pi / 2 ≤ (L q).im)
        (hAng q hqst).2
      rw [hlog q hqst, Complex.sub_re] at he
      linarith
    have hqMem : q ∈ Icc a b :=
      ⟨hs.1.trans hqst.1, hqst.2.trans ht.2⟩
    have hpreQ : ∀ x ∈ Icc s q, (ρ x).im ≤ 1 := by
      intro x hx
      by_cases hxu : x ≤ u
      · exact hpreU x ⟨hx.1, hxu⟩
      · have h := hqpre x ⟨le_of_not_ge hxu, hx.2⟩
        linarith
    exact laneC_corner_crosscut_of_first_top D hs hqMem hqst.1 hρ
      hρann hwest (by linarith : (ρ q).im = 1) hqRe hpreQ
      (fun x hx => hfullOther x ⟨hx.1, hx.2.trans hqst.2⟩)

end SupercriticalLQGUniqueness.B2.DG20Conc
