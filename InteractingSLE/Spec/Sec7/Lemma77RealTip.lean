/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma77Close
import InteractingSLE.Foundations.Topology.PathComplement

/-!
# Lemma 7.7 at a real corner: planar tools and the contact point

Packet PROVE-LEMMA77-B (specification §7.2, Aux. lemmas 74–75 and Lemma 7.7, pp. 279–282,
`source/spec/p241-288.md#aux-74`): the deterministic planar facts used at a common first contact on `ℝ`
("A physical real endpoint is interpreted through its incident prime end", Aux. lemma 74).

* `H_diff_fillH_inter_subset_of_real`: Janiszewski's theorem in `ℍ` for two compact sets meeting only on `ℝ`;
* `mem_H_diff_fillH_of_ray`: a point of `ℍ` whose upward vertical ray misses a compact set is in its unbounded
  domain; `mem_H_diff_fillH_union_of_subset_ball`: adding a compact set inside a ball centred on `ℝ`, attached at
  real points only, traps no point outside the ball;
* `exists_mem_H_diff_fillH_union_dist_lt`: the accumulation argument at a real point approached by real touches;
* `IsPathGood.mem_closure_of_finalArch`: every point of a final excursion `η((u, a))` in `ℍ` ending on `ℝ` is
  adherent to the unbounded domain of `η([0, a])` (Jordan curve through a lower closing arc);
* `IsPathGood.mem_closure_self_of_real`: the tip property at a real tip, terminal tips included;
* `mem_closure_H_diff_fillH_of_real`: a real common first contact point is adherent to the joint unbounded domain
  (Lemma 7.7's confinement clause at the contact point itself, "a path which terminates at the contact has no
  nontrivial continuation to check", Aux. lemma 75).
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter Topology Bornology Complex
open scoped NNReal ENNReal

open QuantumZipper (H)

namespace InteractingSLE

namespace Sec7

open HalfPlaneSep Restart Foundations.ThetaCurve

/-! ### Planar tools -/

/-- **Janiszewski in `ℍ`** for two compact sets meeting only on the real line. -/
theorem H_diff_fillH_inter_subset_of_real {F₁ F₂ : Set ℂ} (hF₁ : IsCompact F₁) (hF₂ : IsCompact F₂)
    (h : ∀ y ∈ F₁ ∩ F₂, y.im = 0) {z : ℂ} (h₁ : z ∈ H \ fillH F₁) (h₂ : z ∈ H \ fillH F₂) :
    z ∈ H \ fillH (F₁ ∪ F₂) :=
  H_diff_fillH_inter_subset hF₁ hF₂ (fun y hy => ⟨{y}, singleton_subset_iff.2 hy,
    isPreconnected_singleton, mem_singleton y, y, mem_singleton y, h y hy⟩) ⟨h₁, h₂⟩

/-- Moving up from a point of `ℍ̄` does not approach a real point. -/
theorem dist_le_dist_add_mul_I {z w : ℂ} (hz : 0 ≤ z.im) (hw : w.im = 0) {t : ℝ} (ht : 0 ≤ t) :
    dist z w ≤ dist (z + (t : ℂ) * I) w := by
  rw [dist_eq_norm, dist_eq_norm]
  have h1 : ‖z - w‖ ^ 2 ≤ ‖z + (t : ℂ) * I - w‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, normSq_apply, normSq_apply]
    simp only [sub_re, add_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_zero,
      sub_im, add_im, mul_im, add_zero, hw]
    nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h1

/-- **The vertical ray.** A point of `ℍ` whose upward vertical ray misses a compact set `G` is in the unbounded
domain of `G`. -/
theorem mem_H_diff_fillH_of_ray {G : Set ℂ} (hG : IsCompact G) {z : ℂ} (hz : z ∈ H)
    (hray : ∀ t : ℝ, 0 ≤ t → z + (t : ℂ) * I ∉ G) : z ∈ H \ fillH G := by
  set T : Set ℂ := (fun t : ℝ => z + (t : ℂ) * I) '' Ici 0 with hT
  have hTc : IsPreconnected T := isPreconnected_Ici.image _ (by fun_prop)
  have hTu : ¬ IsBounded T := by
    intro hb
    obtain ⟨R, hR⟩ := hb.subset_closedBall 0
    set M : ℝ := ‖z‖ + |R| + 1 with hM
    have hM0 : 0 < M := by positivity
    have hmem : z + (M : ℂ) * I ∈ T := ⟨M, hM0.le, rfl⟩
    have h1 := mem_closedBall_zero_iff.1 (hR hmem)
    have h2 : ‖(M : ℂ) * I‖ ≤ ‖z + (M : ℂ) * I‖ + ‖z‖ := by
      calc ‖(M : ℂ) * I‖ = ‖(z + (M : ℂ) * I) - z‖ := by rw [add_sub_cancel_left]
        _ ≤ ‖z + (M : ℂ) * I‖ + ‖z‖ := norm_sub_le _ _
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hM0] at h2
    linarith [le_abs_self R]
  have hTG : T ⊆ H \ G := by
    rintro _ ⟨t, ht, rfl⟩
    refine ⟨?_, hray t ht⟩
    show 0 < (z + (t : ℂ) * I).im
    simp only [add_im, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero]
    exact add_pos_of_pos_of_nonneg hz (show (0 : ℝ) ≤ t from ht)
  exact subset_H_diff_fillH_of_not_isBounded hG.isClosed hTc hTu hTG ⟨0, le_refl (0 : ℝ), by simp⟩

/-- **Adding a small set at a real point.** If `G` lies in a ball of radius `ρ` about a real point `w` and meets `F`
only on `ℝ`, a point of the unbounded domain of `F` at distance at least `ρ` from `w` is in that of `F ∪ G`. -/
theorem mem_H_diff_fillH_union_of_subset_ball {F G : Set ℂ} (hF : IsCompact F) (hG : IsCompact G)
    (hFG : ∀ y ∈ F ∩ G, y.im = 0) {w : ℂ} (hw : w.im = 0) {ρ : ℝ} (hGw : G ⊆ ball w ρ) {z : ℂ}
    (hz : z ∈ H \ fillH F) (hzw : ρ ≤ dist z w) : z ∈ H \ fillH (F ∪ G) := by
  refine H_diff_fillH_inter_subset_of_real hF hG hFG hz
    (mem_H_diff_fillH_of_ray hG hz.1 fun t ht hmem => ?_)
  have h1 := mem_ball.1 (hGw hmem)
  have h2 := dist_le_dist_add_mul_I (show (0 : ℝ) < z.im from hz.1).le hw ht
  linarith

/-- The unbounded domain of a compact set meets every circle about a point adherent to it. -/
theorem exists_mem_H_diff_fillH_dist_eq {F : Set ℂ} (hF : IsCompact F) {w : ℂ}
    (hw : w ∈ closure (H \ fillH F)) {r : ℝ} (hr : 0 < r) : ∃ z ∈ H \ fillH F, dist z w = r := by
  have hc := isPreconnected_H_diff_fillH hF.isClosed hF.isBounded
  obtain ⟨z₁, hz₁, hz₁w⟩ := Metric.mem_closure_iff.1 hw r hr
  obtain ⟨R, hR, hFR, -⟩ := exists_H_diff_fillH_eq hF.isClosed hF.isBounded
  set M : ℝ := R + ‖w‖ + r + 1 with hM
  have hM0 : 0 < M := by positivity
  set z₂ : ℂ := (M : ℂ) * I with hz₂
  have hnz₂ : ∀ t : ℝ, 0 ≤ t → ‖z₂ + (t : ℂ) * I‖ = M + t := by
    intro t ht
    rw [hz₂, ← add_mul, ← ofReal_add, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by linarith)]
  have hz₂H : z₂ ∈ H := by
    show 0 < z₂.im
    simp only [hz₂, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero]
    exact hM0
  have hz₂U : z₂ ∈ H \ fillH F := by
    refine mem_H_diff_fillH_of_ray hF hz₂H fun t ht hmem => ?_
    have := mem_ball_zero_iff.1 (hFR hmem)
    rw [hnz₂ t ht] at this
    linarith [norm_nonneg w]
  have hd₂ : r < dist z₂ w := by
    have h := norm_sub_norm_le z₂ w
    have hn : ‖z₂‖ = M := by simpa using hnz₂ 0 le_rfl
    rw [dist_eq_norm]
    linarith
  have hsub := hc.intermediate_value (f := fun y : ℂ => dist y w) hz₁ hz₂U
    (continuous_id.dist continuous_const).continuousOn
  obtain ⟨z, hz, hzr⟩ := hsub ⟨by rw [dist_comm] at hz₁w; exact hz₁w.le, hd₂.le⟩
  exact ⟨z, hz, hzr⟩

/-- **The accumulation argument at a real point.** If `w ∈ ℝ` is adherent to the unbounded domain of `F`, and `G`
lies within `δ / 2` of `w` and meets `F` only on `ℝ`, then the unbounded domain of `F ∪ G` has a point within `δ`
of `w`. -/
theorem exists_mem_H_diff_fillH_union_dist_lt {F G : Set ℂ} (hF : IsCompact F) (hG : IsCompact G)
    (hFG : ∀ y ∈ F ∩ G, y.im = 0) {w : ℂ} (hw : w.im = 0) (hwF : w ∈ closure (H \ fillH F)) {δ : ℝ}
    (hδ : 0 < δ) (hGw : G ⊆ ball w (δ / 2)) : ∃ z ∈ H \ fillH (F ∪ G), dist z w < δ := by
  obtain ⟨z, hz, hzw⟩ := exists_mem_H_diff_fillH_dist_eq hF hwF (show 0 < 3 * δ / 4 by positivity)
  exact ⟨z, mem_H_diff_fillH_union_of_subset_ball hF hG hFG hw hGw hz (by rw [hzw]; linarith),
    by rw [hzw]; linarith⟩

/-! ### Good paths -/

section GoodPath

variable {η : ℝ≥0 → ℂ} {ζ : ℝ≥0∞} {x : ℝ}

/-- A good path stays good on a shorter lifetime. -/
theorem IsPathGood.mono {ζ' : ℝ≥0∞} (hp : IsPathGood η ζ x) (h : ζ' ≤ ζ) : IsPathGood η ζ' x := by
  obtain ⟨hi, w, hw, hw0, hg⟩ := hp
  exact ⟨hi.mono fun t (ht : (t : ℝ≥0∞) ≤ ζ') => ht.trans h, w,
    hw.mono fun t (ht : (t : ℝ≥0∞) < ζ') => ht.trans_le h, hw0, hg.1,
    hg.2.1.mono fun t (ht : (t : ℝ≥0∞) ≤ ζ') => ht.trans h, fun t ht => hg.2.2 t (ht.trans_le h)⟩

/-- Dense interior times of a good path. -/
theorem IsPathGood.exists_mem_H (hp : IsPathGood η ζ x) {a c : ℝ≥0} (hac : a < c) (hc : (c : ℝ≥0∞) ≤ ζ) :
    ∃ s ∈ Ioo a c, η s ∈ H := by
  obtain ⟨-, w, hw, hw0, hg⟩ := hp
  exact IsGeneratingTrace.exists_mem_H_add hg hw hw0 hac hc

/-- A rational interior time in every nonempty parameter interval. -/
theorem IsPathGood.exists_rat_mem_H (hp : IsPathGood η ζ x) {a c : ℝ≥0} (hac : a < c) (hc : (c : ℝ≥0∞) ≤ ζ) :
    ∃ q : ℚ, a < (q : ℝ).toNNReal ∧ (q : ℝ).toNNReal < c ∧ η (q : ℝ).toNNReal ∈ H := by
  obtain ⟨s, hs, hsH⟩ := IsPathGood.exists_mem_H hp hac hc
  have hsub : Ioo a c ⊆ {t : ℝ≥0 | (t : ℝ≥0∞) ≤ ζ} := fun t ht =>
    (ENNReal.coe_le_coe.2 ht.2.le).trans hc
  have hcont : ContinuousAt η s :=
    hp.continuousOn.continuousAt (Filter.mem_of_superset (isOpen_Ioo.mem_nhds hs) hsub)
  have hU : η ⁻¹' H ∩ Ioo a c ∈ 𝓝 s :=
    Filter.inter_mem (hcont.preimage_mem_nhds (QuantumZipper.isOpen_H.mem_nhds hsH)) (isOpen_Ioo.mem_nhds hs)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hU
  have hε2 : (0 : ℝ) < ε / 2 := half_pos hε
  obtain ⟨q, hq₁, hq₂⟩ := exists_rat_toNNReal_btwn
    (show s < s + (ε / 2).toNNReal from lt_add_of_pos_right _ (Real.toNNReal_pos.2 hε2))
  have hqball : (q : ℝ).toNNReal ∈ ball s ε := by
    rw [mem_ball, NNReal.dist_eq]
    have h1 : (s : ℝ) < ((q : ℝ).toNNReal : ℝ) := hq₁
    have h2 : (((q : ℝ).toNNReal : ℝ)) < s + ε / 2 := by
      have := NNReal.coe_lt_coe.2 hq₂
      rwa [NNReal.coe_add, Real.coe_toNNReal _ hε2.le] at this
    rw [abs_of_pos (by linarith)]
    linarith
  obtain ⟨hqH, hq⟩ := hball hqball
  exact ⟨q, hq.1, hq.2, hqH⟩

theorem IsPathGood.im_eq_zero (hp : IsPathGood η ζ x) {s : ℝ≥0} (hs : (s : ℝ≥0∞) ≤ ζ) (h : η s ∉ H) :
    (η s).im = 0 :=
  le_antisymm (not_lt.1 (show ¬ (0 < (η s).im) from h)) (IsPathGood.im_nonneg hp hs)

end GoodPath

/-- A lower closing arc between two distinct real points: an arc in the closed lower half-plane whose only real
points are its endpoints. -/
theorem exists_isArcFrom_lower {x y : ℝ} (hxy : x ≠ y) :
    ∃ ℓ : ℝ → ℂ, IsArcFrom ℓ (x : ℂ) (y : ℂ) ∧ (∀ z ∈ arc ℓ, z.im ≤ 0) ∧
      ∀ z ∈ arc ℓ, z.im = 0 → z = x ∨ z = y := by
  rcases lt_or_gt_of_ne hxy with h | h
  · refine ⟨Sec6.arcRev (lowerArcPath x y), isArcFrom_arcRev (isArcFrom_lowerArcPath h),
      fun z hz => ?_, fun z hz h0 => ?_⟩
    · rw [arc_arcRev] at hz
      exact (im_le_zero_of_mem_lowerArc (x₂ := x) (x₁ := y) hz).1
    · rw [arc_arcRev] at hz
      exact ((im_le_zero_of_mem_lowerArc (x₂ := x) (x₁ := y) hz).2 h0).symm
  · exact ⟨lowerArcPath y x, isArcFrom_lowerArcPath h,
      fun z hz => (im_le_zero_of_mem_lowerArc (x₂ := y) (x₁ := x) hz).1,
      fun z hz h0 => (im_le_zero_of_mem_lowerArc (x₂ := y) (x₁ := x) hz).2 h0⟩

/-! ### The tip property at a real tip -/

section RealTip

variable {η : ℝ≥0 → ℂ} {ζ : ℝ≥0∞} {x : ℝ}

/-- **A final excursion to the real line.** If `η((u, a)) ⊆ ℍ` and `η(a) ∈ ℝ`, every point `η(s)`, `u < s < a`, is
adherent to the unbounded domain of `η([0, a])`. Proof: `η([0, a])` closed by a lower arc from the seed to `η(a)` is
a Jordan curve; `η(s)` is adherent to its outside, and near `η(s)` the outside lies in the unbounded domain (the
closing-curve lemma with `F = η([0, u']) ∪ {η(a)}`, `u < u' < s`). -/
theorem IsPathGood.mem_closure_of_finalArch (hp : IsPathGood η ζ x) {u a : ℝ≥0} (ha : (a : ℝ≥0∞) ≤ ζ)
    (hua : u < a) (harch : ∀ s ∈ Ioo u a, η s ∈ H) (hwR : η a ∉ H) {s : ℝ≥0} (hs : s ∈ Ioo u a) :
    η s ∈ closure (H \ fillH (η '' Icc 0 a)) := by
  have ha0 : 0 < a := lt_of_le_of_lt (zero_le : (0 : ℝ≥0) ≤ u) hua
  have hw0 : (η a).im = 0 := IsPathGood.im_eq_zero hp ha hwR
  have hx : η 0 = x := IsPathGood.zero hp
  have hwre : (((η a).re : ℝ) : ℂ) = η a := Complex.ext (by simp) (by simp [hw0])
  have hxw : x ≠ (η a).re := by
    intro h
    have he : η a = η 0 := by rw [hx, ← hwre, h]
    have := hp.1 ha (show ((0 : ℝ≥0) : ℝ≥0∞) ≤ ζ from (ENNReal.coe_le_coe.2 zero_le).trans ha) he
    exact absurd this (ne_of_gt ha0)
  obtain ⟨ℓ, hℓ, hℓim, hℓre⟩ := exists_isArcFrom_lower hxw
  have hxL : (x : ℂ) ∈ arc ℓ := ⟨0, ⟨le_rfl, zero_le_one⟩, hℓ.2.2.1⟩
  have hwL : η a ∈ arc ℓ := ⟨1, ⟨zero_le_one, le_rfl⟩, by rw [hℓ.2.2.2, hwre]⟩
  have hLc : IsCompact (arc ℓ) := isCompact_Icc.image_of_continuousOn hℓ.1
  have hLpc : IsPreconnected (arc ℓ) := isPreconnected_Icc.image _ hℓ.1
  have hc := IsPathGood.continuousOn_Icc hp ha
  have hi := IsPathGood.injOn_Icc hp ha
  have hηarc : IsArcFrom (segArc η 0 a) (x : ℂ) (((η a).re : ℝ) : ℂ) := by
    have := isArcFrom_segArc ha0 hc hi
    rwa [hx, ← hwre] at this
  have harc : arc (segArc η 0 a) = η '' Icc 0 a := arc_segArc zero_le
  have hJ : LQGMetric.JordanMap.IsJordanCurve (η '' Icc 0 a ∪ arc ℓ) := by
    have := isJordanCurve_arc_union hηarc hℓ ?_
    · rwa [harc] at this
    rw [harc]
    rintro z ⟨⟨t, ht, rfl⟩, hzL⟩
    have him : (η t).im = 0 := le_antisymm (hℓim _ hzL)
      (IsPathGood.im_nonneg hp ((ENNReal.coe_le_coe.2 ht.2).trans ha))
    exact hℓre _ hzL him
  -- the free ball of `η(s)` for an earlier prefix
  obtain ⟨u', huu', hu's⟩ := exists_between hs.1
  have hsζ : (s : ℝ≥0∞) ≤ ζ := (ENNReal.coe_le_coe.2 hs.2.le).trans ha
  obtain ⟨ε, hε, hball⟩ := exists_ball_of_isFreeAt (IsPathGood.isFreeAt_of_lt hp hu's hsζ)
  have hsH : η s ∈ H := harch s hs
  have hηsJ : η s ∈ closure (WangWu.jordanOut (η '' Icc 0 a ∪ arc ℓ)) := by
    rw [closure_jordanOut hJ]
    exact Or.inr (Or.inl ⟨s, ⟨zero_le, hs.2.le⟩, rfl⟩)
  have hu'a : u' ≤ a := hu's.le.trans hs.2.le
  have hu'ζ : (u' : ℝ≥0∞) ≤ ζ := (ENNReal.coe_le_coe.2 hu'a).trans ha
  have hcF : IsCompact (η '' Icc 0 u' ∪ {η a}) :=
    (IsPathGood.isCompact_image hp hu'ζ).union isCompact_singleton
  have hfill : fillH (η '' Icc 0 u' ∪ {η a}) = fillH (η '' Icc 0 u') :=
    fillH_union_of_forall_notMem_H fun z hz => by rw [mem_singleton_iff.1 hz]; exact hwR
  have hFL : IsPreconnected (η '' Icc 0 u' ∪ {η a} ∪ arc ℓ) := by
    have he : η '' Icc 0 u' ∪ {η a} ∪ arc ℓ = η '' Icc 0 u' ∪ arc ℓ := by
      ext z
      simp only [mem_union, mem_singleton_iff]
      constructor
      · rintro ((h | rfl) | h)
        · exact Or.inl h
        · exact Or.inr hwL
        · exact Or.inr h
      · rintro (h | h)
        · exact Or.inl (Or.inl h)
        · exact Or.inr h
    rw [he]
    exact (isPreconnected_Icc.image _ (IsPathGood.continuousOn_Icc hp hu'ζ)).union (x : ℂ)
      ⟨0, ⟨le_rfl, zero_le⟩, hx⟩ hxL hLpc
  rw [Metric.mem_closure_iff]
  intro δ hδ
  obtain ⟨z, hzJ, hzd⟩ := Metric.mem_closure_iff.1 hηsJ (min δ (min ε (η s).im))
    (lt_min hδ (lt_min hε hsH))
  have hzH : z ∈ H := by
    show 0 < z.im
    have h1 : |(η s - z).im| ≤ ‖η s - z‖ := Complex.abs_im_le_norm _
    rw [sub_im, ← dist_eq_norm] at h1
    have h2 : dist (η s) z < (η s).im := hzd.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    have h3 := neg_abs_le ((η s).im - z.im)
    have h4 : (η s).im - z.im ≤ |(η s).im - z.im| := le_abs_self _
    linarith
  have hzF : z ∈ H \ fillH (η '' Icc 0 u') :=
    hball z (mem_ball.2 (by
      rw [dist_comm]; exact hzd.trans_le ((min_le_right _ _).trans (min_le_left _ _)))) hzH
  refine ⟨z, ?_, hzd.trans_le (min_le_left _ _)⟩
  refine mem_H_diff_fillH_of_mem_jordanOut_closing hcF (IsPathGood.isCompact_image hp ha) hLc
    (union_subset (image_mono (Icc_subset_Icc_right hu'a)) (singleton_subset_iff.2 ⟨a, ⟨zero_le, le_rfl⟩, rfl⟩))
    ?_ ?_ hℓim hFL (by rw [hfill]; exact hzF) hzJ
  · rintro _ ⟨t, ht, rfl⟩
    exact IsPathGood.im_nonneg hp ((ENNReal.coe_le_coe.2 ht.2).trans ha)
  · rintro _ ⟨t, ht, rfl⟩ h0
    rcases le_or_gt t u' with htu | htu
    · exact Or.inl ⟨t, ⟨ht.1, htu⟩, rfl⟩
    rcases eq_or_lt_of_le ht.2 with hta | hta
    · exact Or.inr (by rw [hta]; exact mem_singleton _)
    · exact absurd h0 (ne_of_gt (harch t ⟨huu'.trans htu, hta⟩))

/-- **The tip property at a real tip** (terminal tips included): `η(a) ∈ ℝ` is adherent to the unbounded domain of
`η([0, a])`. A final excursion is `IsPathGood.mem_closure_of_finalArch`; real touches accumulating at `a` are the
accumulation argument. -/
theorem IsPathGood.mem_closure_self_of_real (hp : IsPathGood η ζ x) {a : ℝ≥0} (ha : (a : ℝ≥0∞) ≤ ζ)
    (hwR : η a ∉ H) : η a ∈ closure (H \ fillH (η '' Icc 0 a)) := by
  have hw0 : (η a).im = 0 := IsPathGood.im_eq_zero hp ha hwR
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ a) with h0 | ha0
  · -- the seed: points straight above it
    subst h0
    rw [Metric.mem_closure_iff]
    intro δ hδ
    have hδ2 : (0 : ℝ) < δ / 2 := half_pos hδ
    refine ⟨η 0 + ((δ / 2 : ℝ) : ℂ) * I, ?_, ?_⟩
    · have hzH : η 0 + ((δ / 2 : ℝ) : ℂ) * I ∈ H := by
        show 0 < (η 0 + ((δ / 2 : ℝ) : ℂ) * I).im
        simp only [add_im, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero, hw0]
        linarith
      refine mem_H_diff_fillH_of_ray (IsPathGood.isCompact_image hp ha) hzH fun t ht hmem => ?_
      obtain ⟨t', ht', he⟩ := hmem
      have ht'0 : t' = 0 := le_antisymm ht'.2 zero_le
      rw [ht'0] at he
      have := congrArg Complex.im he
      simp only [add_im, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero, hw0] at this
      linarith
    · rw [dist_eq_norm, sub_add_cancel_left, norm_neg, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hδ2]
      linarith
  by_cases harch : ∃ u < a, ∀ s ∈ Ioo u a, η s ∈ H
  · obtain ⟨u, hua, harch⟩ := harch
    have hcont : ContinuousWithinAt η (Ioo u a) a :=
      (hp.continuousOn a ha).mono fun t ht => (ENNReal.coe_le_coe.2 ht.2.le).trans ha
    have hcl : a ∈ closure (Ioo u a) := by
      rw [closure_Ioo hua.ne]
      exact ⟨hua.le, le_rfl⟩
    refine closure_minimal ?_ isClosed_closure (hcont.mem_closure_image hcl)
    rintro _ ⟨s, hs, rfl⟩
    exact IsPathGood.mem_closure_of_finalArch hp ha hua harch hwR hs
  push Not at harch
  rw [Metric.mem_closure_iff]
  intro δ hδ
  obtain ⟨u₀, hu₀, hu₀ball⟩ := exists_lt_forall_Icc_mem_ball hp.continuousOn ha ha0 (half_pos hδ)
  obtain ⟨s, hs, hsH⟩ := harch u₀ hu₀
  have hsζ : (s : ℝ≥0∞) ≤ ζ := (ENNReal.coe_le_coe.2 hs.2.le).trans ha
  have hreal : ∀ y ∈ η '' Icc 0 s ∩ η '' Icc s a, y.im = 0 := by
    rintro _ ⟨⟨r, hr, rfl⟩, ⟨r', hr', hrr'⟩⟩
    have hr'ζ : (r' : ℝ≥0∞) ≤ ζ := (ENNReal.coe_le_coe.2 hr'.2).trans ha
    have hrζ : (r : ℝ≥0∞) ≤ ζ := (ENNReal.coe_le_coe.2 hr.2).trans hsζ
    have := hp.1 hr'ζ hrζ hrr'
    rw [← this, le_antisymm (this ▸ hr.2) hr'.1]
    exact IsPathGood.im_eq_zero hp hsζ hsH
  obtain ⟨z, hz, hzd⟩ := exists_mem_H_diff_fillH_union_dist_lt (IsPathGood.isCompact_image hp hsζ)
    (IsPathGood.isCompact_image_Icc hp ha) hreal hw0 (IsPathGood.mem_closure_of_lt hp hs.2 ha) hδ
    ((image_mono (Icc_subset_Icc_left hs.1.le)).trans hu₀ball)
  rw [← image_union, Icc_union_Icc_eq_Icc zero_le hs.2.le] at hz
  exact ⟨z, hz, by rw [dist_comm]; exact hzd⟩

end RealTip

/-! ### The contact point -/

section Contact

variable {α β : ℝ≥0 → ℂ} {ζα ζβ : ℝ≥0∞} {xα xβ : ℝ} {a b : ℝ≥0}

/-- The two selected prefixes of a first contact meet only at the contact point. -/
theorem image_inter_image_subset_of_isFirstContact (hfc : IsFirstContact α ζα β ζβ a b) :
    α '' Icc 0 a ∩ β '' Icc 0 b ⊆ {α a} := by
  rintro _ ⟨⟨s, hs, rfl⟩, ⟨t, ht, hts⟩⟩
  have := (hfc.2.2.2 s t ((ENNReal.coe_le_coe.2 hs.2).trans hfc.1) ((ENNReal.coe_le_coe.2 ht.2).trans hfc.2.1)
    hts.symm).1
  rw [mem_singleton_iff, le_antisymm hs.2 this]

/-- The second prefix before the contact avoids the first prefix. -/
theorem image_Ico_subset_of_isFirstContact (hpβ : IsPathGood β ζβ xβ) (hfc : IsFirstContact α ζα β ζβ a b) :
    β '' Ico 0 b ⊆ {y : ℂ | 0 ≤ y.im} \ α '' Icc 0 a := by
  rintro _ ⟨t, ht, rfl⟩
  have htζ : (t : ℝ≥0∞) ≤ ζβ := (ENNReal.coe_le_coe.2 ht.2.le).trans hfc.2.1
  refine ⟨IsPathGood.im_nonneg hpβ htζ, ?_⟩
  rintro ⟨s, hs, hst⟩
  have := (hfc.2.2.2 s t ((ENNReal.coe_le_coe.2 hs.2).trans hfc.1) htζ hst).2
  exact absurd ht.2 (not_lt.2 this)

/-- If the second prefix before the contact is trapped by the first prefix, the unbounded domain of the first prefix
is in the joint unbounded domain. -/
theorem H_diff_fillH_subset_of_isTrappedAt (hpα : IsPathGood α ζα xα) (hpβ : IsPathGood β ζβ xβ)
    (hfc : IsFirstContact α ζα β ζβ a b) (hwR : α a ∉ H)
    (htr : ∀ y ∈ β '' Ico 0 b, IsTrappedAt (α '' Icc 0 a) y) :
    H \ fillH (α '' Icc 0 a) ⊆ H \ fillH (α '' Icc 0 a ∪ β '' Icc 0 b) := by
  have hcα := IsPathGood.isCompact_image hpα hfc.1
  have hcβ := IsPathGood.isCompact_image hpβ hfc.2.1
  refine H_diff_fillH_subset_union_of_disjoint hcα.isClosed hcα.isBounded hcβ.isClosed ?_
  rw [Set.disjoint_left]
  rintro _ ⟨t, ht, rfl⟩ hmem
  rcases eq_or_lt_of_le ht.2 with htb | htb
  · rw [htb, ← hfc.2.2.1] at hmem
    exact hwR hmem.1
  · exact (htr _ ⟨t, ⟨ht.1, htb⟩, rfl⟩).notMem hmem

/-- The contact point when the second path ends with a final excursion. -/
theorem mem_closure_H_diff_fillH_of_finalArch (hpα : IsPathGood α ζα xα) (hpβ : IsPathGood β ζβ xβ)
    (hfc : IsFirstContact α ζα β ζβ a b) (hwR : α a ∉ H) {t₁ : ℝ≥0} (ht₁ : t₁ < b)
    (harch : ∀ t ∈ Ioo t₁ b, β t ∈ H) : α a ∈ closure (H \ fillH (α '' Icc 0 a ∪ β '' Icc 0 b)) := by
  have hcα := IsPathGood.isCompact_image hpα hfc.1
  have hcβ := IsPathGood.isCompact_image hpβ hfc.2.1
  have hw0 : (α a).im = 0 := IsPathGood.im_eq_zero hpα hfc.1 hwR
  have hreal : ∀ y ∈ α '' Icc 0 a ∩ β '' Icc 0 b, y.im = 0 := fun y hy => by
    rw [mem_singleton_iff.1 (image_inter_image_subset_of_isFirstContact hfc hy)]; exact hw0
  have hβc : ContinuousOn β (Ico 0 b) :=
    hpβ.continuousOn.mono fun t ht => (ENNReal.coe_le_coe.2 ht.2.le).trans hfc.2.1
  rcases isFreeAt_or_isTrappedAt_of_isPreconnected hcα.isClosed (isPreconnected_Ico.image _ hβc)
      (image_Ico_subset_of_isFirstContact hpβ hfc) with hfr | htr
  · have hlim : α a ∈ closure (β '' Ioo t₁ b) := by
      rw [hfc.2.2.1]
      have hcont : ContinuousWithinAt β (Ioo t₁ b) b :=
        (hpβ.continuousOn b hfc.2.1).mono fun t ht => (ENNReal.coe_le_coe.2 ht.2.le).trans hfc.2.1
      have hcl : b ∈ closure (Ioo t₁ b) := by
        rw [closure_Ioo ht₁.ne]
        exact ⟨ht₁.le, le_rfl⟩
      exact hcont.mem_closure_image hcl
    refine closure_minimal ?_ isClosed_closure hlim
    rintro _ ⟨t, ht, rfl⟩
    have h1 : β t ∈ H \ fillH (α '' Icc 0 a) :=
      mem_H_diff_fillH_of_isFreeAt (hfr _ ⟨t, ⟨zero_le, ht.2⟩, rfl⟩) (harch t ht)
    have h2 : β t ∈ closure (H \ fillH (β '' Icc 0 b)) :=
      IsPathGood.mem_closure_of_finalArch hpβ hfc.2.1 ht₁ harch (hfc.2.2.1 ▸ hwR) ht
    have h3 := (isOpen_H_diff_fillH hcα.isBounded).inter_closure ⟨h1, h2⟩
    exact closure_mono (fun y hy => H_diff_fillH_inter_subset_of_real hcα hcβ hreal hy.1 hy.2) h3
  · exact closure_mono (H_diff_fillH_subset_of_isTrappedAt hpα hpβ hfc hwR htr)
      (IsPathGood.mem_closure_self_of_real hpα hfc.1 hwR)

/-- **A real common first contact point is adherent to the joint unbounded domain.** -/
theorem mem_closure_H_diff_fillH_of_real (hpα : IsPathGood α ζα xα) (hpβ : IsPathGood β ζβ xβ)
    (hfc : IsFirstContact α ζα β ζβ a b) (hwR : α a ∉ H) :
    α a ∈ closure (H \ fillH (α '' Icc 0 a ∪ β '' Icc 0 b)) := by
  obtain ⟨haζ, hbζ, hab, hmin⟩ := id hfc
  by_cases hβarch : ∃ t₁ < b, ∀ t ∈ Ioo t₁ b, β t ∈ H
  · obtain ⟨t₁, ht₁, harch⟩ := hβarch
    exact mem_closure_H_diff_fillH_of_finalArch hpα hpβ hfc hwR ht₁ harch
  by_cases hαarch : ∃ u₁ < a, ∀ s ∈ Ioo u₁ a, α s ∈ H
  · obtain ⟨u₁, hu₁, harch⟩ := hαarch
    have := mem_closure_H_diff_fillH_of_finalArch hpβ hpα (isFirstContact_swap hfc) (hab ▸ hwR) hu₁ harch
    rwa [← hab, union_comm] at this
  push Not at hβarch hαarch
  have hw0 : (α a).im = 0 := IsPathGood.im_eq_zero hpα haζ hwR
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ a) with ha0 | ha0
  · -- the first prefix is its real seed
    have hK : fillH (α '' Icc 0 a ∪ β '' Icc 0 b) = fillH (β '' Icc 0 b) := by
      rw [union_comm, fillH_union_of_forall_notMem_H]
      rintro _ ⟨s, hs, rfl⟩
      have hs0 : s = a := le_antisymm hs.2 (ha0 ▸ hs.1)
      rw [hs0]
      exact hwR
    rw [hK, hab]
    exact IsPathGood.mem_closure_self_of_real hpβ hbζ (hab ▸ hwR)
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ b) with hb0 | hb0
  · have hK : fillH (α '' Icc 0 a ∪ β '' Icc 0 b) = fillH (α '' Icc 0 a) := by
      rw [fillH_union_of_forall_notMem_H]
      rintro _ ⟨t, ht, rfl⟩
      have ht0 : t = b := le_antisymm ht.2 (hb0 ▸ ht.1)
      rw [ht0, ← hab]
      exact hwR
    rw [hK]
    exact IsPathGood.mem_closure_self_of_real hpα haζ hwR
  -- real touches of both paths accumulate at the contact
  rw [Metric.mem_closure_iff]
  intro δ hδ
  obtain ⟨u₀, hu₀, hu₀ball⟩ := exists_lt_forall_Icc_mem_ball hpα.continuousOn haζ ha0 (half_pos hδ)
  obtain ⟨t₀, ht₀, ht₀ball⟩ := exists_lt_forall_Icc_mem_ball hpβ.continuousOn hbζ hb0 (half_pos hδ)
  rw [← hab] at ht₀ball
  obtain ⟨u, hu, huH⟩ := hαarch u₀ hu₀
  obtain ⟨t, ht, htH⟩ := hβarch t₀ ht₀
  have huζ : (u : ℝ≥0∞) ≤ ζα := (ENNReal.coe_le_coe.2 hu.2.le).trans haζ
  have htζ : (t : ℝ≥0∞) ≤ ζβ := (ENNReal.coe_le_coe.2 ht.2.le).trans hbζ
  have hcα := IsPathGood.isCompact_image hpα huζ
  have hcβ := IsPathGood.isCompact_image hpβ htζ
  have hdisj : Disjoint (α '' Icc 0 u) (β '' Icc 0 t) := by
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨s, hs, rfl⟩ ⟨s', hs', hss'⟩
    have := (hmin s s' ((ENNReal.coe_le_coe.2 hs.2).trans huζ) ((ENNReal.coe_le_coe.2 hs'.2).trans htζ)
      hss'.symm).1
    exact absurd (this.trans hs.2) (not_le.2 hu.2)
  have hfree : IsFreeAt (α '' Icc 0 u ∪ β '' Icc 0 t) (α a) := by
    refine isFreeAt_union_of_disjoint hcα hcβ hdisj (IsPathGood.isFreeAt_of_lt hpα hu.2 haζ) ?_
    rw [hab]
    exact IsPathGood.isFreeAt_of_lt hpβ ht.2 hbζ
  have hwF := mem_closure_H_diff_fillH_of_isFreeAt hfree hw0.ge
  have hGw : α '' Icc u a ∪ β '' Icc t b ⊆ ball (α a) (δ / 2) :=
    union_subset ((image_mono (Icc_subset_Icc_left hu.1.le)).trans hu₀ball)
      ((image_mono (Icc_subset_Icc_left ht.1.le)).trans ht₀ball)
  have hreal : ∀ y ∈ (α '' Icc 0 u ∪ β '' Icc 0 t) ∩ (α '' Icc u a ∪ β '' Icc t b), y.im = 0 := by
    rintro y ⟨hyF, hyG⟩
    rcases hyF with ⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩ <;> rcases hyG with ⟨s', hs', hss'⟩ | ⟨s', hs', hss'⟩
    · have := hpα.1 ((ENNReal.coe_le_coe.2 hs'.2).trans haζ) ((ENNReal.coe_le_coe.2 hs.2).trans huζ) hss'
      rw [← this, le_antisymm (this ▸ hs.2) hs'.1]
      exact IsPathGood.im_eq_zero hpα huζ huH
    · have := (hmin s s' ((ENNReal.coe_le_coe.2 hs.2).trans huζ) ((ENNReal.coe_le_coe.2 hs'.2).trans hbζ)
        hss'.symm).1
      exact absurd (this.trans hs.2) (not_le.2 hu.2)
    · have := (hmin s' s ((ENNReal.coe_le_coe.2 hs'.2).trans haζ) ((ENNReal.coe_le_coe.2 hs.2).trans htζ)
        hss').2
      exact absurd (this.trans hs.2) (not_le.2 ht.2)
    · have := hpβ.1 ((ENNReal.coe_le_coe.2 hs'.2).trans hbζ) ((ENNReal.coe_le_coe.2 hs.2).trans htζ) hss'
      rw [← this, le_antisymm (this ▸ hs.2) hs'.1]
      exact IsPathGood.im_eq_zero hpβ htζ htH
  obtain ⟨z, hz, hzd⟩ := exists_mem_H_diff_fillH_union_dist_lt (hcα.union hcβ)
    ((IsPathGood.isCompact_image_Icc hpα haζ).union (IsPathGood.isCompact_image_Icc hpβ hbζ)) hreal hw0 hwF hδ hGw
  have hK : α '' Icc 0 u ∪ β '' Icc 0 t ∪ (α '' Icc u a ∪ β '' Icc t b) = α '' Icc 0 a ∪ β '' Icc 0 b := by
    rw [← Icc_union_Icc_eq_Icc (zero_le : (0 : ℝ≥0) ≤ u) hu.2.le,
      ← Icc_union_Icc_eq_Icc (zero_le : (0 : ℝ≥0) ≤ t) ht.2.le, image_union, image_union]
    ext y; simp only [mem_union]; tauto
  rw [hK] at hz
  exact ⟨z, hz, by rw [dist_comm]; exact hzd⟩

end Contact

end Sec7

end InteractingSLE
