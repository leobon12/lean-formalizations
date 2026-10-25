import SupercriticalLQGUniqueness.B2.Median.UpperCurve

 











set_option autoImplicit false
noncomputable section

open Set Filter Topology Metric MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.Median

 
def ratCircle (c : ℚ × ℚ × ℕ) : Set ℂ :=
  sphere (⟨(c.1 : ℝ), (c.2.1 : ℝ)⟩ : ℂ) (1 / ((c.2.2 : ℝ) + 1))

theorem isRationalCircle_ratCircle (c : ℚ × ℚ × ℕ) :
    B2.Iface.IsRationalCircle (ratCircle c) := by
  refine ⟨c.1, c.2.1, 1 / ((c.2.2 : ℚ) + 1), ?_, ?_⟩
  · have : (0 : ℚ) < (c.2.2 : ℚ) + 1 := by positivity
    exact (one_div_pos.mpr this).le
  simp only [ratCircle]
  congr 1
  push_cast
  ring

 
def ratRho (k : ℕ) : Set.Ioi (0 : ℝ) := ⟨1 / ((k : ℝ) + 1), Set.mem_Ioi.mpr (by positivity)⟩

 
abbrev BarrierIndex := (ℚ × ℚ × ℚ × ℚ) × ℕ × ℕ × (ℚ × ℚ × ℕ) × (ℚ × ℚ × ℕ)

theorem penaltyField_eq_zero_of_mem {N : Set ℂ} {ρ : Set.Ioi (0 : ℝ)} {M : ℝ} {z : ℂ}
    (hz : z ∈ N) : penaltyField N ρ M z = 0 := by
  simp [penaltyField, distanceBarrier_eq_zero_of_mem hz]

 
theorem exists_ratCircle_around (p : ℂ) {s : ℝ} (hs : 0 < s) :
    ∃ c : ℚ × ℚ × ℕ, dist p (⟨(c.1 : ℝ), (c.2.1 : ℝ)⟩ : ℂ) < 1 / ((c.2.2 : ℝ) + 1) ∧
      2 * (1 / ((c.2.2 : ℝ) + 1)) < s := by
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt (half_pos hs)
  set r : ℝ := 1 / ((k : ℝ) + 1) with hr
  have hr0 : 0 < r := by positivity
  obtain ⟨x, hx⟩ := exists_rat_btwn (show p.re - r / 2 < p.re by linarith)
  obtain ⟨y, hy⟩ := exists_rat_btwn (show p.im - r / 2 < p.im by linarith)
  refine ⟨(x, y, k), ?_, by linarith⟩
  simp only
  rw [Complex.dist_eq]
  calc ‖p - ⟨(x : ℝ), (y : ℝ)⟩‖
      ≤ |(p - ⟨(x : ℝ), (y : ℝ)⟩).re| + |(p - ⟨(x : ℝ), (y : ℝ)⟩).im| :=
        Complex.norm_le_abs_re_add_abs_im _
    _ = |p.re - x| + |p.im - y| := by simp
    _ < r / 2 + r / 2 := by
        apply add_lt_add
        · rw [abs_lt]; constructor <;> linarith [hx.1, hx.2]
        · rw [abs_lt]; constructor <;> linarith [hy.1, hy.2]
    _ = r := by ring

 
theorem ae_limsup_le_len_of_strip_curve
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ξ : Set.Ioi (0 : ℝ))
    (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (ε : ℕ → Set.Ioi (0 : ℝ))
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
    (D : LQGMetric.DistC → LSCMetric)
    (hsub : B2.Iface.SubseqLimit ξ m ε D)
    (c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (hweak : B2.Iface.IsPfeWeakMetric ξ D c)
    (h : Ω → LQGMetric.DistC) (hh : LQGMetric.IsGFFPlusBddCont h P)
    (X : Set.Ioi (0 : ℝ) → Ω → C(ℂ, ℝ))
    (hX : ∀ δ, IsHeatSmoothing P h δ (X δ)) :
    ∀ᵐ ω ∂P, ∀ (G : ℝ → ℂ) (a b : ℝ), (D (h ω)).IsCurve G a b →
      (G a).re < 0 → 1 < (G b).re → (∀ t ∈ Icc a b, G t ∈ surgeryRegion) →
      limsup (fun n => ENNReal.ofReal ((m (ε n) : ℝ)⁻¹) *
        lfppCrossingLength (ξ : ℝ) (X (ε n) ω)) atTop ≤ (D (h ω)).len G a b := by
  have hmetric := ae_lfppMetric_tendsto_of_subseqLimit P ξ m ε D hsub h hh X hX
  have hconv : ∀ᵐ ω ∂P, ∀ β : BarrierIndex,
      Tendsto (fun n => ENNReal.ofReal ((m (ε n) : ℝ)⁻¹) *
        B2.Iface.setDistance
          (lfppDistance (ξ : ℝ)
            (X (ε n) ω + LQGMetric.LFPP.mollCont (ε n : ℝ) (ε n).property.ne'
              (penaltyField (ratRect 0 β.1) (ratRho β.2.1) ((β.2.2.1 : ℝ) + 1))
              ((β.2.2.1 : ℝ) + 1)
              (penaltyField_abs_le (ratRect 0 β.1) (ratRho β.2.1) (by positivity))))
          (ratCircle β.2.2.2.1) (ratCircle β.2.2.2.2)) atTop
        (𝓝 (B2.Iface.setDistance
          (weylScale (ξ : ℝ)
            (penaltyField (ratRect 0 β.1) (ratRho β.2.1) ((β.2.2.1 : ℝ) + 1)) (D (h ω)))
          (ratCircle β.2.2.2.1) (ratCircle β.2.2.2.2))) := by
    rw [ae_all_iff]
    intro β
    exact ae_shifted_circle_convergence_weyl_of_inputs P ξ m ε D hsub c hweak h hh X hX
      _ _ _ _ _ (isRationalCircle_ratCircle _) (isRationalCircle_ratCircle _)
  filter_upwards [hmetric, hconv] with ω hG hβ
  intro G a b hGc hGa hGb htr
  set d := D (h ω) with hd
  by_cases hfin : d.len G a b = ∞
  · rw [hfin]; exact le_top
  
  have hbdd : Bornology.IsBounded (G '' Icc a b) :=
    isBounded_surgeryRegion.subset (fun w ⟨t, ht, hw⟩ => hw ▸ htr t ht)
  have hcont : ContinuousOn G (Icc a b) :=
    Uniqueness.Toolkit.PathInfimum.continuousOn_euclidean_of_bounded d G hGc hbdd
  have hab : a ≤ b := hGc.1
  have him : ContinuousOn (fun t => (G t).im) (Icc a b) :=
    Complex.continuous_im.comp_continuousOn hcont
  obtain ⟨t₁, ht₁, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hab) him
  obtain ⟨t₂, ht₂, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hab) him
  set δ : ℝ := min ((G t₁).im) (1 - (G t₂).im) with hδ
  have hδ0 : 0 < δ := lt_min (htr t₁ ht₁).1 (by linarith [(htr t₂ ht₂).2.1])
  have hδle : δ ≤ 1 / 2 := by
    have := (htr t₁ ht₁).2.1
    have h1 : δ ≤ (G t₁).im := min_le_left _ _
    have h2 : δ ≤ 1 - (G t₂).im := min_le_right _ _
    have h3 : (G t₁).im ≤ (G t₂).im := hmax ht₁
    linarith
  have himb : ∀ t ∈ Icc a b, δ ≤ (G t).im ∧ (G t).im ≤ 1 - δ := fun t ht =>
    ⟨(min_le_left _ _).trans (hmin ht), by
      have h3 : (G t).im ≤ (G t₂).im := hmax ht
      have h2 : δ ≤ 1 - (G t₂).im := min_le_right _ _
      linarith⟩
  
  have hGa' := htr a (left_mem_Icc.mpr hab)
  have hGb' := htr b (right_mem_Icc.mpr hab)
  obtain ⟨cL, hcL, hcL2⟩ := exists_ratCircle_around (G a)
    (lt_min (half_pos hδ0) (neg_pos.mpr hGa) : 0 < min (δ / 2) (-(G a).re))
  obtain ⟨cR, hcR, hcR2⟩ := exists_ratCircle_around (G b)
    (lt_min (half_pos hδ0) (sub_pos.mpr hGb) : 0 < min (δ / 2) ((G b).re - 1))
  set zL : ℂ := ⟨(cL.1 : ℝ), (cL.2.1 : ℝ)⟩ with hzL
  set zR : ℂ := ⟨(cR.1 : ℝ), (cR.2.1 : ℝ)⟩ with hzR
  set rL : ℝ := 1 / ((cL.2.2 : ℝ) + 1) with hrL
  set rR : ℝ := 1 / ((cR.2.2 : ℝ) + 1) with hrR
  have hrL0 : 0 < rL := by positivity
  have hrR0 : 0 < rR := by positivity
  
  have hdiskL : ∀ w, dist w zL ≤ rL → dist w (G a) < min (δ / 2) (-(G a).re) := by
    intro w hw
    have := dist_triangle w zL (G a)
    rw [dist_comm zL (G a)] at this
    linarith
  have hdiskR : ∀ w, dist w zR ≤ rR → dist w (G b) < min (δ / 2) ((G b).re - 1) := by
    intro w hw
    have := dist_triangle w zR (G b)
    rw [dist_comm zR (G b)] at this
    linarith
  
  obtain ⟨y₁, hy₁⟩ := exists_rat_btwn (show δ / 4 < δ / 2 by linarith)
  obtain ⟨y₂, hy₂⟩ := exists_rat_btwn (show 1 - δ / 2 < 1 - δ / 4 by linarith)
  obtain ⟨kρ, hkρ⟩ := exists_nat_one_div_lt (show 0 < δ / 8 by positivity)
  set q : ℚ × ℚ × ℚ × ℚ := (-4, 5, y₁, y₂) with hq
  set N : Set ℂ := ratRect 0 q with hN
  set ρ : Set.Ioi (0 : ℝ) := ratRho kρ with hρ
  have hρval : (ρ : ℝ) = 1 / ((kρ : ℝ) + 1) := rfl
  have hmemN : ∀ w : ℂ, -4 ≤ w.re → w.re ≤ 5 → (y₁ : ℝ) ≤ w.im → w.im ≤ (y₂ : ℝ) → w ∈ N := by
    intro w h1 h2 h3 h4
    simp only [hN, hq, mem_ratRect_iff, sub_zero, Rat.cast_neg, Rat.cast_ofNat]
    exact ⟨h1, h2, h3, h4⟩
  have hNcpt : IsCompact N := isCompact_ratRect 0 q
  have hGN : ∀ t ∈ Icc a b, G t ∈ N := by
    intro t ht
    obtain ⟨_, _, h3, h4⟩ := htr t ht
    exact hmemN _ (by linarith) (by linarith) (by linarith [(himb t ht).1, hy₁.2])
      (by linarith [(himb t ht).2, hy₂.1])
  have hNne : N.Nonempty := ⟨G a, hGN a (left_mem_Icc.mpr hab)⟩
  have hdiskN : ∀ w, (dist w zL ≤ rL ∨ dist w zR ≤ rR) → w ∈ N := by
    intro w hw
    rcases hw with hw | hw
    · have h1 := hdiskL w hw
      have hre := abs_lt.mp (lt_of_le_of_lt (abs_re_sub_le_dist w (G a)) (h1.trans_le (min_le_left _ _)))
      have him' := abs_lt.mp (lt_of_le_of_lt (abs_im_sub_le_dist w (G a)) (h1.trans_le (min_le_left _ _)))
      have hb := himb a (left_mem_Icc.mpr hab)
      exact hmemN _ (by linarith [hGa'.2.2.1]) (by linarith [hGa'.2.2.2])
        (by linarith [hy₁.2]) (by linarith [hy₂.1])
    · have h1 := hdiskR w hw
      have hre := abs_lt.mp (lt_of_le_of_lt (abs_re_sub_le_dist w (G b)) (h1.trans_le (min_le_left _ _)))
      have him' := abs_lt.mp (lt_of_le_of_lt (abs_im_sub_le_dist w (G b)) (h1.trans_le (min_le_left _ _)))
      have hb := himb b (right_mem_Icc.mpr hab)
      exact hmemN _ (by linarith [hGb'.2.2.1]) (by linarith [hGb'.2.2.2])
        (by linarith [hy₁.2]) (by linarith [hy₂.1])
  have hOL : ratCircle cL ⊆ N := fun w hw => hdiskN w (Or.inl (mem_sphere.mp hw).le)
  have hOLleft : ∀ w ∈ ratCircle cL, w.re ≤ 0 := by
    intro w hw
    have h1 := hdiskL w (mem_sphere.mp hw).le
    have hre := abs_lt.mp (lt_of_le_of_lt (abs_re_sub_le_dist w (G a)) (h1.trans_le (min_le_right _ _)))
    linarith [hre.2]
  have hORright : ∀ w ∈ ratCircle cR, 1 ≤ w.re := by
    intro w hw
    have h1 := hdiskR w (mem_sphere.mp hw).le
    have hre := abs_lt.mp (lt_of_le_of_lt (abs_re_sub_le_dist w (G b)) (h1.trans_le (min_le_right _ _)))
    linarith [hre.1]
  have hstrip : ∀ z : ℂ, Metric.infDist z N ≤ (ρ : ℝ) → 0 ≤ z.im ∧ z.im ≤ 1 := by
    intro z hz
    obtain ⟨w, hwN, hw⟩ := hNcpt.exists_infDist_eq_dist hNne z
    have hdz : dist z w ≤ ρ := by rw [← hw]; exact hz
    have hwim := abs_le.mp ((abs_im_sub_le_dist z w).trans hdz)
    simp only [hN, hq, mem_ratRect_iff, sub_zero] at hwN
    obtain ⟨_, _, hw3, hw4⟩ := hwN
    have hρlt : (ρ : ℝ) < δ / 8 := by rw [hρval]; exact hkρ
    constructor <;> linarith [hy₁.1, hy₂.2]
  
  obtain ⟨R, hR, hball⟩ := exists_ball_for_infDist_thickening N hNcpt hNne ρ
  obtain ⟨μ, hμ, hsep⟩ :=
    Uniqueness.Toolkit.PathInfimum.eventually_separated_pairs_pos hG
      (isCompact_infDist_thickening N hNcpt hNne ρ) (div_pos ρ.property (by norm_num))
      (separated_pair_in_infDist_thickening N hNne ρ)
  
  set lenG : ℝ≥0∞ := d.len G a b with hlenG
  have hM : ∃ kM : ℕ, lenG < ENNReal.ofReal (Real.exp ((ξ : ℝ) * (((kM : ℝ) + 1) / 4))) * μ := by
    by_cases hμtop : μ = ∞
    · refine ⟨0, ?_⟩
      rw [hμtop, ENNReal.mul_top (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne']
      exact lt_top_iff_ne_top.mpr hfin
    · have hμr : 0 < μ.toReal := ENNReal.toReal_pos hμ.ne' hμtop
      obtain ⟨kM, hkM⟩ := exists_nat_gt (4 * lenG.toReal / ((ξ : ℝ) * μ.toReal))
      refine ⟨kM, ?_⟩
      have hξ : (0 : ℝ) < ξ := ξ.property
      have hx : lenG.toReal / μ.toReal < (ξ : ℝ) * (((kM : ℝ) + 1) / 4) := by
        rw [div_lt_iff₀ (mul_pos hξ hμr)] at hkM
        rw [div_lt_iff₀ hμr]
        nlinarith
      have hexp : lenG.toReal / μ.toReal < Real.exp ((ξ : ℝ) * (((kM : ℝ) + 1) / 4)) :=
        hx.trans (by
          have := Real.add_one_lt_exp (show (ξ : ℝ) * (((kM : ℝ) + 1) / 4) ≠ 0 by positivity)
          linarith)
      rw [← ENNReal.ofReal_toReal hμtop, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
        ← ENNReal.ofReal_toReal hfin]
      exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr
        ((div_lt_iff₀ hμr).mp hexp)
  obtain ⟨kM, hkM⟩ := hM
  set Mv : ℝ := (kM : ℝ) + 1 with hMv
  
  have hW : B2.Iface.setDistance (weylScale (ξ : ℝ) (penaltyField N ρ Mv) d)
      (ratCircle cL) (ratCircle cR) ≤ lenG := by
    have hf1 : ContinuousOn (fun t => dist (G t) zL) (Icc a b) :=
      continuous_dist.comp_continuousOn (hcont.prodMk continuousOn_const)
    have hfa : dist (G a) zL ≤ rL := hcL.le
    have hfb : rL ≤ dist (G b) zL := by
      have := hdiskR (G b) (by simp [hcR.le, dist_self])
      by_contra hlt
      rw [not_le] at hlt
      have h2 := hdiskL (G b) hlt.le
      have h3 := abs_lt.mp (lt_of_le_of_lt (abs_re_sub_le_dist (G b) (G a))
        (h2.trans_le (min_le_right _ _)))
      linarith [h3.2]
    obtain ⟨s₀, hs₀, hs₀eq⟩ := intermediate_value_Icc hab hf1 ⟨hfa, hfb⟩
    have hs₀L : G s₀ ∈ ratCircle cL := mem_sphere.mpr hs₀eq
    have hf2 : ContinuousOn (fun t => dist (G t) zR) (Icc s₀ b) :=
      continuous_dist.comp_continuousOn ((hcont.mono (Icc_subset_Icc hs₀.1 le_rfl)).prodMk
        continuousOn_const)
    have hfs : rR ≤ dist (G s₀) zR := by
      by_contra hlt
      rw [not_le] at hlt
      have h2 := hdiskR (G s₀) hlt.le
      have h3 := abs_lt.mp (lt_of_le_of_lt (abs_re_sub_le_dist (G s₀) (G b))
        (h2.trans_le (min_le_right _ _)))
      have := hOLleft _ hs₀L
      linarith [h3.1]
    obtain ⟨s₁, hs₁, hs₁eq⟩ := intermediate_value_Icc' hs₀.2 hf2 ⟨hcR.le, hfs⟩
    have hs₁R : G s₁ ∈ ratCircle cR := mem_sphere.mpr hs₁eq
    have hsub : d.IsCurve G s₀ s₁ :=
      ⟨hs₁.1, hGc.2.mono (Icc_subset_Icc hs₀.1 hs₁.2)⟩
    have hlesub : d.len G s₀ s₁ ≤ lenG :=
      LQGMetric.MetricGeometry.curveLength_mono _ hs₀.1 hs₁.2
    have hzero : ∀ t ∈ Icc s₀ s₁, penaltyField N ρ Mv (G t) = 0 := fun t ht =>
      penaltyField_eq_zero_of_mem (hGN t ⟨hs₀.1.trans ht.1, ht.2.trans hs₁.2⟩)
    have hweyl := weylScale_le_len_of_zero_on_trace (ξ : ℝ) (penaltyField N ρ Mv) d hsub
      (ne_top_of_le_ne_top hfin hlesub) hzero
    calc B2.Iface.setDistance (weylScale (ξ : ℝ) (penaltyField N ρ Mv) d)
          (ratCircle cL) (ratCircle cR)
        ≤ weylScale (ξ : ℝ) (penaltyField N ρ Mv) d (G s₀, G s₁) :=
          iInf₂_le_of_le (G s₀) hs₀L (iInf₂_le (G s₁) hs₁R)
      _ ≤ d.len G s₀ s₁ := hweyl
      _ ≤ lenG := hlesub
  
  set T : ℝ≥0∞ := ENNReal.ofReal (Real.exp ((ξ : ℝ) * (Mv / 4))) * μ with hT
  have hWT : B2.Iface.setDistance (weylScale (ξ : ℝ) (penaltyField N ρ Mv) d)
      (ratCircle cL) (ratCircle cR) < T := hW.trans_lt hkM
  have hlimβ := hβ (q, kρ, kM, cL, cR)
  refine (limsup_le_of_eventually_lt_between _ _ T hWT fun L hWL hLT => ?_).trans hW
  exact barrier_crossing_eventually_lt_of_sep ξ ε (fun n => m (ε n)) hε
    (fun n => X (ε n) ω) N ρ R hR hball hstrip μ hsep Mv (by positivity)
    (ratCircle cL) (ratCircle cR) hOL hOLleft hORright _ L hlimβ hWL hLT

end SupercriticalLQGUniqueness.B2.Median
