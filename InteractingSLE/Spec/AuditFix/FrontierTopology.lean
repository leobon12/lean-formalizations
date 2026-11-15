/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.Prop420Ext
import InteractingSLE.Spec.Supplement.SB4SewSides
import InteractingSLE.Spec.Supplement.S9BOrder
import InteractingSLE.Spec.Supplement.WalkContinuum
import InteractingSLE.Spec.Sec5.Prop411QSide
import InteractingSLE.Foundations.Topology.JaniszewskiHalfPlane

/-!
# Audit fix, frontier bridge: the deterministic planar topology

Packet PROVE-AF-FRONTIER (external audit §3.4, p. 9: "A bridge to a specified notion of outer boundary should be
exported if that terminology is meant as an exact equality. Boundary connectors make a naive frontier identity
delicate."). This file proves the deterministic topology behind `Spec/AuditFix/FrontierBridge.lean`.

Throughout, `ℍ = QuantumZipper.H` is the open upper half-plane, `A` is a closed set (a boundary walk) contained in a
set `K` (the completed counterflow range), and the side of `A` facing a set of reals `I` is `WangWu.sideOf I A`: the
points of `ℍ \ A` whose component in `ℍ \ A` has a point of `I` off `A` in its closure (`rightSideOf = sideOf (Ioi 0)`,
`leftSideOf = sideOf (Iio 0)`, both by `rfl`). The *frontier conditions* are `A ⊆ K`, `K ∩ sideOf I A = ∅` (the frozen
frontier anchor) and: every point of `K` on `I` is a limit of points of `K ∩ ℍ` (the counterflow does not trace the
boundary).

## Main results

* `sideOf_eq_of_frontier`: under the frontier conditions, `sideOf I K = sideOf I A` — the complementary region of the
  range facing `I` is exactly the region strictly on that side of the walk;
* `ofReal_mem_of_frontier`: under the same conditions every point of `K` on `I` lies on `A`;
* `frontier_sideOf_inter_H`: for a closed `A` whose points in `ℍ` are limits of its side,
  `frontier (sideOf I A) ∩ ℍ = A ∩ ℍ`;
* `range_inter_H_subset_closure_rightSideOf`, `range_inter_H_subset_closure_leftSideOf`: Jordan separation — every
  point in `ℍ` of a proper curve from `0` is a limit of points strictly on its right, and of points strictly on its
  left (`Supp9B.seedRayClosure_subset_closure_rightSide`, S5's gate `Theorem14.SB.rightSide_inter_H_subset_rightSideOf`);
* `exists_real_arc_of_notMem_closure`: a point of a proper curve that is not a limit of its points in `ℍ` lies on a
  nondegenerate real arc of the curve; hence `range_subset_closure_union_Ici` (no negative real arc),
  `range_subset_closure_union_Iic` (no positive real arc) and `range_subset_closure_of_interior_eq_empty` (no real arc
  of `K` at all);
* `bridge_core`, `bridge_of_walks`, `bridge_nbf_of_walks`: the frontier bridge for one sample.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal
open QuantumZipper (H)

namespace InteractingSLE.AuditFix.Frontier

open WangWu (sideOf)

/-! ### The side of a closed set and of a larger set -/

section Sides

variable {I : Set ℝ} {A K : Set ℂ}

/-- The side of a closed set is open: it is a union of components of the open set `ℍ \ A`. -/
theorem isOpen_sideOf (hA : IsClosed A) : IsOpen (sideOf I A) := by
  rw [isOpen_iff_forall_mem_open]
  intro z hz
  exact ⟨connectedComponentIn (H \ A) z, fun w hw => WangWu.mem_sideOf_of_mem_connectedComponentIn hz hw,
    (QuantumZipper.isOpen_H.sdiff hA).connectedComponentIn, mem_connectedComponentIn hz.1⟩

/-- **A larger set has a smaller side.** -/
theorem sideOf_anti (hAK : A ⊆ K) : sideOf I K ⊆ sideOf I A := by
  rintro z ⟨⟨hzH, hzK⟩, x, hxI, hxK, hxcl⟩
  exact ⟨⟨hzH, fun hzA => hzK (hAK hzA)⟩, x, hxI, fun hxA => hxK (hAK hxA),
    closure_mono (connectedComponentIn_mono z (sdiff_subset_sdiff_right hAK)) hxcl⟩

theorem notMem_of_mem_sideOf (hdis : K ∩ sideOf I A = ∅) {z : ℂ} (hz : z ∈ sideOf I A) : z ∉ K :=
  fun hzK => (eq_empty_iff_forall_notMem.1 hdis) z ⟨hzK, hz⟩

/-- **Components on the side of `A` are components of the complement of `K`**: if `A ⊆ K` and `K` misses the side of
`A`, the component in `ℍ \ K` of a point on that side is its component in `ℍ \ A`. -/
theorem connectedComponentIn_eq_of_mem_sideOf (hAK : A ⊆ K) (hdis : K ∩ sideOf I A = ∅) {z : ℂ}
    (hz : z ∈ sideOf I A) : connectedComponentIn (H \ K) z = connectedComponentIn (H \ A) z := by
  refine Subset.antisymm (connectedComponentIn_mono z (sdiff_subset_sdiff_right hAK)) ?_
  refine isPreconnected_connectedComponentIn.subset_connectedComponentIn
    (mem_connectedComponentIn hz.1) fun w hw => ?_
  have hws : w ∈ sideOf I A := WangWu.mem_sideOf_of_mem_connectedComponentIn hz hw
  exact ⟨hws.1.1, notMem_of_mem_sideOf hdis hws⟩

/-- The upper half of a small ball around a point `x ∈ I` off `A` lies on the side of `A` facing `I`. -/
theorem mem_sideOf_of_mem_half_ball {x : ℝ} (hxI : x ∈ I) (hxA : (x : ℂ) ∉ A) {δ : ℝ} (hδ : 0 < δ)
    (hball : Metric.ball (x : ℂ) δ ∩ A = ∅) {w : ℂ} (hw : w ∈ Metric.ball (x : ℂ) δ ∩ H) :
    w ∈ sideOf I A := by
  have hsub : Metric.ball (x : ℂ) δ ∩ H ⊆ H \ A := fun v hv =>
    ⟨hv.2, fun hvA => (eq_empty_iff_forall_notMem.1 hball) v ⟨hv.1, hvA⟩⟩
  have hcomp := (HalfPlaneSep.isPreconnected_ball_inter_H (x : ℂ) δ).subset_connectedComponentIn hw hsub
  exact ⟨hsub hw, x, hxI, hxA, closure_mono hcomp (Sec5.Prop411Q.ofReal_mem_closure_ball_inter_H x hδ)⟩

/-- **Every point of `K` on `I` lies on `A`** under the frontier conditions: the upper half-ball at a point of `I`
off the closed set `A` lies on the side of `A`, which `K` misses, while `K` has points of `ℍ` near each of its
points on `I`. -/
theorem ofReal_mem_of_frontier (hA : IsClosed A) (hdis : K ∩ sideOf I A = ∅)
    (hK : ∀ x ∈ I, (x : ℂ) ∈ K → (x : ℂ) ∈ closure (K ∩ H)) {x : ℝ} (hxI : x ∈ I) (hxK : (x : ℂ) ∈ K) :
    (x : ℂ) ∈ A := by
  by_contra hxA
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hA.isOpen_compl (x : ℂ) hxA
  have hδA : Metric.ball (x : ℂ) δ ∩ A = ∅ := eq_empty_of_forall_notMem fun v hv => hball hv.1 hv.2
  obtain ⟨y, hyK, hyd⟩ := Metric.mem_closure_iff.1 (hK x hxI hxK) δ hδ
  have hyB : y ∈ Metric.ball (x : ℂ) δ ∩ H := ⟨by rw [Metric.mem_ball, dist_comm]; exact hyd, hyK.2⟩
  exact notMem_of_mem_sideOf hdis (mem_sideOf_of_mem_half_ball hxI hxA hδ hδA hyB) hyK.1

/-- **The side of the range is the side of the walk** under the frontier conditions. -/
theorem sideOf_eq_of_frontier (hA : IsClosed A) (hAK : A ⊆ K) (hdis : K ∩ sideOf I A = ∅)
    (hK : ∀ x ∈ I, (x : ℂ) ∈ K → (x : ℂ) ∈ closure (K ∩ H)) : sideOf I K = sideOf I A := by
  refine Subset.antisymm (sideOf_anti hAK) fun z hz => ?_
  obtain ⟨⟨hzH, -⟩, x, hxI, hxA, hxcl⟩ := id hz
  refine ⟨⟨hzH, notMem_of_mem_sideOf hdis hz⟩, x, hxI,
    fun hxK => hxA (ofReal_mem_of_frontier hA hdis hK hxI hxK), ?_⟩
  rwa [connectedComponentIn_eq_of_mem_sideOf hAK hdis hz]

/-- **The closure of the side of a closed set, inside `ℍ`, adds only points of the set.** -/
theorem closure_sideOf_inter_H_subset (hA : IsClosed A) : closure (sideOf I A) ∩ H ⊆ sideOf I A ∪ A := by
  rintro w ⟨hwcl, hwH⟩
  by_cases hwA : w ∈ A
  · exact Or.inr hwA
  refine Or.inl ?_
  have hU : IsOpen (connectedComponentIn (H \ A) w) :=
    (QuantumZipper.isOpen_H.sdiff hA).connectedComponentIn
  obtain ⟨v, hvU, hvS⟩ := _root_.mem_closure_iff.1 hwcl _ hU (mem_connectedComponentIn ⟨hwH, hwA⟩)
  have hwv : w ∈ connectedComponentIn (H \ A) v := by
    rw [← connectedComponentIn_eq hvU]
    exact mem_connectedComponentIn ⟨hwH, hwA⟩
  exact WangWu.mem_sideOf_of_mem_connectedComponentIn hvS hwv

/-- **The relative boundary of the side in `ℍ`**: for a closed `A` whose points in `ℍ` are limits of its side,
`frontier (sideOf I A) ∩ ℍ = A ∩ ℍ`. -/
theorem frontier_sideOf_inter_H (hA : IsClosed A) (hcl : A ∩ H ⊆ closure (sideOf I A)) :
    frontier (sideOf I A) ∩ H = A ∩ H := by
  rw [(isOpen_sideOf (I := I) hA).frontier_eq]
  refine Subset.antisymm (fun w hw => ?_) fun w hw => ⟨⟨hcl hw, fun hwS => hwS.1.2 hw.1⟩, hw.2⟩
  obtain ⟨⟨hwcl, hwS⟩, hwH⟩ := hw
  rcases closure_sideOf_inter_H_subset hA ⟨hwcl, hwH⟩ with h | h
  · exact absurd h hwS
  · exact ⟨h, hwH⟩

end Sides

/-! ### Proper curves: Jordan separation and real arcs -/

section Curves

variable {γ : ℝ≥0 → ℂ}

/-- **Every point in `ℍ` of a proper curve from `0` is a limit of points strictly on its right** (Jordan separation
of the curve closed along its lower vertical ray, and S5's gate identifying the Jordan right side in `ℍ` with the
frozen `rightSideOf`). -/
theorem range_inter_H_subset_closure_rightSideOf (hγ : Supp9B.IsProperCurve γ) (hγ0 : γ 0 = 0) :
    range γ ∩ H ⊆ closure (rightSideOf (range γ)) := by
  rintro z ⟨hz, hzH⟩
  have h0 : (γ 0).im = 0 := by rw [hγ0]; rfl
  have hcl : z ∈ closure (Supp9B.rightSide γ) :=
    Supp9B.seedRayClosure_subset_closure_rightSide hγ h0 (Or.inl hz)
  exact closure_mono (fun w hw => Theorem14.SB.rightSide_inter_H_subset_rightSideOf hγ hγ0 ⟨hw.2, hw.1⟩)
    (QuantumZipper.isOpen_H.inter_closure ⟨hzH, hcl⟩)

/-- **Every point in `ℍ` of a proper curve from `0` is a limit of points strictly on its left.** -/
theorem range_inter_H_subset_closure_leftSideOf (hγ : Supp9B.IsProperCurve γ) (hγ0 : γ 0 = 0) :
    range γ ∩ H ⊆ closure (leftSideOf (range γ)) := by
  rintro z ⟨hz, hzH⟩
  have h0 : (γ 0).im = 0 := by rw [hγ0]; rfl
  have hcl : z ∈ closure (Supp9B.leftSide γ) :=
    Supp9B.seedRayClosure_subset_closure_leftSide hγ h0 (Or.inl hz)
  exact closure_mono (fun w hw => Theorem14.SB.leftSide_inter_H_subset_leftSideOf hγ hγ0 ⟨hw.2, hw.1⟩)
    (QuantumZipper.isOpen_H.inter_closure ⟨hzH, hcl⟩)

/-- **A point of a proper curve that is not a limit of its points in `ℍ` lies on a real arc of the curve**: for every
`ε > 0` there is a preconnected set of real points of the curve, with two points, within `ε` of it. -/
theorem exists_real_arc_of_notMem_closure (hγ : Supp9B.IsProperCurve γ) {t₀ : ℝ≥0}
    (hz : γ t₀ ∉ closure (range γ ∩ H)) {ε : ℝ} (hε : 0 < ε) :
    ∃ S ⊆ range γ, IsPreconnected S ∧ ¬ S.Subsingleton ∧ S ⊆ Metric.ball (γ t₀) ε ∧ ∀ w ∈ S, w.im = 0 := by
  obtain ⟨ε₁, hε₁, hball⟩ := Metric.isOpen_iff.1 isClosed_closure.isOpen_compl _ hz
  have hr : 0 < min ε ε₁ := lt_min hε hε₁
  obtain ⟨δ, hδ, hδs⟩ := Metric.continuousAt_iff.1 hγ.1.continuousAt (min ε ε₁) hr
  have ht : t₀ < t₀ + (δ / 2).toNNReal := lt_add_of_pos_right t₀ (Real.toNNReal_pos.2 (half_pos hδ))
  have hnear : ∀ t ∈ Icc t₀ (t₀ + (δ / 2).toNNReal), dist (γ t) (γ t₀) < min ε ε₁ := by
    intro t ht'
    apply hδs
    rw [NNReal.dist_eq, abs_of_nonneg (sub_nonneg.2 (NNReal.coe_le_coe.2 ht'.1))]
    have h1 : (t : ℝ) ≤ t₀ + δ / 2 := by
      have := NNReal.coe_le_coe.2 ht'.2
      rwa [NNReal.coe_add, Real.coe_toNNReal _ (half_pos hδ).le] at this
    linarith
  refine ⟨γ '' Icc t₀ (t₀ + (δ / 2).toNNReal), image_subset_range _ _,
    isPreconnected_Icc.image _ hγ.1.continuousOn, fun hsub => ?_, ?_, ?_⟩
  · exact hγ.2.1.ne ht.ne (hsub ⟨t₀, left_mem_Icc.2 ht.le, rfl⟩ ⟨_, right_mem_Icc.2 ht.le, rfl⟩)
  · rintro _ ⟨t, ht', rfl⟩
    exact Metric.mem_ball.2 (lt_of_lt_of_le (hnear t ht') (min_le_left _ _))
  · rintro _ ⟨t, ht', rfl⟩
    have hb : γ t ∈ Metric.ball (γ t₀) ε₁ :=
      Metric.mem_ball.2 (lt_of_lt_of_le (hnear t ht') (min_le_right _ _))
    have hnot : ¬ (0 : ℝ) < (γ t).im := fun hH => hball hb (subset_closure ⟨⟨t, rfl⟩, hH⟩)
    exact le_antisymm (not_lt.1 hnot) (hγ.2.2.1 t)

/-- A preconnected set of real points with two points, inside `K`, gives `ℝ ∩ K` a nonempty interior. -/
theorem interior_preimage_nonempty_of_real_arc {K S : Set ℂ} (hSK : S ⊆ K) (hS : IsPreconnected S)
    (hS2 : ¬ S.Subsingleton) (hSr : ∀ w ∈ S, w.im = 0) :
    (interior (((↑) : ℝ → ℂ) ⁻¹' K)).Nonempty := by
  obtain ⟨a, ha, c, hc, hac⟩ := not_subsingleton_iff.1 hS2
  have hre : IsPreconnected (Complex.re '' S) := hS.image _ Complex.continuous_re.continuousOn
  have hsub : Complex.re '' S ⊆ ((↑) : ℝ → ℂ) ⁻¹' K := by
    rintro _ ⟨w, hw, rfl⟩
    have hw' : ((w.re : ℝ) : ℂ) = w := Complex.ext (by simp) (by simp [hSr w hw])
    show ((w.re : ℝ) : ℂ) ∈ K
    rw [hw']
    exact hSK hw
  have hne : a.re ≠ c.re := fun h => hac (Complex.ext h ((hSr a ha).trans (hSr c hc).symm))
  have key : ∀ p q : ℂ, p ∈ S → q ∈ S → p.re < q.re → (interior (((↑) : ℝ → ℂ) ⁻¹' K)).Nonempty :=
    fun p q hp hq hpq => ⟨(p.re + q.re) / 2, interior_maximal
      (Ioo_subset_Icc_self.trans ((hre.Icc_subset ⟨p, hp, rfl⟩ ⟨q, hq, rfl⟩).trans hsub)) isOpen_Ioo
      ⟨left_lt_add_div_two.2 hpq, add_div_two_lt_right.2 hpq⟩⟩
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact key a c ha hc hlt
  · exact key c a hc ha hlt

/-- The real point `w.re` of a real `w`. -/
theorem ofReal_re_of_im_eq_zero {w : ℂ} (hw : w.im = 0) : ((w.re : ℝ) : ℂ) = w :=
  Complex.ext (by simp) (by simp [hw])

/-- **Points of a proper curve off its `ℍ`-closure are nonnegative reals** when the curve contains no nondegenerate
preconnected set of negative reals. -/
theorem range_subset_closure_union_Ici (hγ : Supp9B.IsProperCurve γ)
    (hneg : ∀ S ⊆ range γ ∩ ((↑) : ℝ → ℂ) '' Iio 0, IsPreconnected S → S.Subsingleton) :
    range γ ⊆ closure (range γ ∩ H) ∪ ((↑) : ℝ → ℂ) '' Ici 0 := by
  rintro _ ⟨t₀, rfl⟩
  by_contra hno
  rw [mem_union, not_or] at hno
  obtain ⟨hcl, hre⟩ := hno
  have hH : ¬ (0 : ℝ) < (γ t₀).im := fun h => hcl (subset_closure ⟨⟨t₀, rfl⟩, h⟩)
  have him : (γ t₀).im = 0 := le_antisymm (not_lt.1 hH) (hγ.2.2.1 t₀)
  have hneg0 : (γ t₀).re < 0 := by
    by_contra h
    exact hre ⟨(γ t₀).re, not_lt.1 h, ofReal_re_of_im_eq_zero him⟩
  obtain ⟨S, hSγ, hSc, hS2, hSb, hSr⟩ := exists_real_arc_of_notMem_closure hγ hcl (neg_pos.2 hneg0)
  refine hS2 (hneg S (fun w hw => ⟨hSγ hw, w.re, ?_, ofReal_re_of_im_eq_zero (hSr w hw)⟩) hSc)
  have hd : dist w (γ t₀) < -(γ t₀).re := Metric.mem_ball.1 (hSb hw)
  have h1 : (w - γ t₀).re ≤ ‖w - γ t₀‖ := (le_abs_self _).trans (Complex.abs_re_le_norm _)
  rw [← dist_eq_norm, Complex.sub_re] at h1
  show w.re < 0
  linarith

/-- **Points of a proper curve off its `ℍ`-closure are nonpositive reals** when the curve contains no nondegenerate
preconnected set of positive reals. -/
theorem range_subset_closure_union_Iic (hγ : Supp9B.IsProperCurve γ)
    (hpos : ∀ S ⊆ range γ ∩ ((↑) : ℝ → ℂ) '' Ioi 0, IsPreconnected S → S.Subsingleton) :
    range γ ⊆ closure (range γ ∩ H) ∪ ((↑) : ℝ → ℂ) '' Iic 0 := by
  rintro _ ⟨t₀, rfl⟩
  by_contra hno
  rw [mem_union, not_or] at hno
  obtain ⟨hcl, hre⟩ := hno
  have hH : ¬ (0 : ℝ) < (γ t₀).im := fun h => hcl (subset_closure ⟨⟨t₀, rfl⟩, h⟩)
  have him : (γ t₀).im = 0 := le_antisymm (not_lt.1 hH) (hγ.2.2.1 t₀)
  have hpos0 : 0 < (γ t₀).re := by
    by_contra h
    exact hre ⟨(γ t₀).re, not_lt.1 h, ofReal_re_of_im_eq_zero him⟩
  obtain ⟨S, hSγ, hSc, hS2, hSb, hSr⟩ := exists_real_arc_of_notMem_closure hγ hcl hpos0
  refine hS2 (hpos S (fun w hw => ⟨hSγ hw, w.re, ?_, ofReal_re_of_im_eq_zero (hSr w hw)⟩) hSc)
  have hd : dist w (γ t₀) < (γ t₀).re := Metric.mem_ball.1 (hSb hw)
  have h1 : -(w - γ t₀).re ≤ ‖w - γ t₀‖ := (neg_le_abs _).trans (Complex.abs_re_le_norm _)
  rw [← dist_eq_norm, Complex.sub_re] at h1
  show 0 < w.re
  linarith

/-- **A proper curve inside a set with no real interior is the closure of its points in `ℍ`.** -/
theorem range_subset_closure_of_interior_eq_empty (hγ : Supp9B.IsProperCurve γ) {K : Set ℂ}
    (hγK : range γ ⊆ K) (hint : interior (((↑) : ℝ → ℂ) ⁻¹' K) = ∅) : range γ ⊆ closure (range γ ∩ H) := by
  rintro _ ⟨t₀, rfl⟩
  by_contra hcl
  obtain ⟨S, hSγ, hSc, hS2, -, hSr⟩ := exists_real_arc_of_notMem_closure hγ hcl one_pos
  obtain ⟨x, hx⟩ := interior_preimage_nonempty_of_real_arc (hSγ.trans hγK) hSc hS2 hSr
  rw [hint] at hx
  exact hx

end Curves

/-! ### The frontier bridge for one sample -/

section Bridge

variable {K : Set ℂ} {γ γR γL : ℝ≥0 → ℂ}

/-- **The two sides of a proper curve from `0` are disjoint**: a component of `ℍ \ range γ` on the right lies in the
Jordan right side, and a negative real point off the curve lies in the open Jordan left side. -/
theorem disjoint_leftSideOf_rightSideOf_range (hγ : Supp9B.IsProperCurve γ) (hγ0 : γ 0 = 0) :
    Disjoint (leftSideOf (range γ)) (rightSideOf (range γ)) := by
  refine Set.disjoint_left.2 fun z hzL hzR => ?_
  have h0 : (γ 0).im = 0 := by rw [hγ0]; rfl
  obtain ⟨-, x, hx, hxγ, hxcl⟩ := hzL
  have hCR : connectedComponentIn (H \ range γ) z ⊆ Supp9B.rightSide γ := fun w hw =>
    ((Theorem14.SB.rightSideOf_range_eq_inter_H hγ hγ0).subset
      (WangWu.mem_rightSideOf_of_mem_connectedComponentIn hzR hw)).1
  have hxS : (x : ℂ) ∉ seedRayClosure γ := by
    rintro (hxγ' | ⟨hre, -⟩)
    · exact hxγ hxγ'
    · rw [hγ0] at hre
      simp at hre
      linarith
  have hxL : (x : ℂ) ∈ Supp9B.leftSide γ :=
    Supp9B.ofReal_mem_leftSide hγ.2.2.1 h0 (by rw [hγ0, Complex.zero_re]; exact hx) hxS
  obtain ⟨w, hwL, hwR⟩ :=
    _root_.mem_closure_iff.1 (closure_mono hCR hxcl) _ (Supp9B.isOpen_leftSide hγ) hxL
  exact Set.disjoint_left.1 (Supp9B.disjoint_leftSide_rightSide hγ h0) hwL hwR

/-- Every point of the closure of a side lies in the closed upper half-plane. -/
theorem im_nonneg_of_mem_closure_sideOf {I : Set ℝ} {A : Set ℂ} {z : ℂ} (hz : z ∈ closure (sideOf I A)) :
    0 ≤ z.im :=
  closure_minimal (fun w hw => le_of_lt (show (0 : ℝ) < w.im from hw.1.1))
    (isClosed_le continuous_const Complex.continuous_im) hz

/-- **Points of the range on the boundary of its right complementary region lie on the right walk**: in `ℍ` by the
relative-boundary identity, on `[0, ∞)` by the real-point identity, and on `(−∞, 0)` because the upper half-ball at
a negative real point off the walk lies on its left side, which is disjoint from its right side. -/
theorem frontier_rightSideOf_inter_subset (hγ : Supp9B.IsProperCurve γ) (hγ0 : γ 0 = 0)
    (hs : rightSideOf K = rightSideOf (range γ)) (hb : frontier (rightSideOf K) ∩ H = range γ ∩ H)
    (hpos : K ∩ ((↑) : ℝ → ℂ) '' Ici 0 ⊆ range γ) : frontier (rightSideOf K) ∩ K ⊆ range γ := by
  rintro z ⟨hzf, hzK⟩
  by_cases hzH : z ∈ H
  · have h1 : z ∈ frontier (rightSideOf K) ∩ H := ⟨hzf, hzH⟩
    rw [hb] at h1
    exact h1.1
  have hzcl : z ∈ closure (rightSideOf (range γ)) := hs ▸ frontier_subset_closure hzf
  have him : z.im = 0 :=
    le_antisymm (not_lt.1 (show ¬ (0 : ℝ) < z.im from hzH)) (im_nonneg_of_mem_closure_sideOf (I := Ioi 0) hzcl)
  have hz : ((z.re : ℝ) : ℂ) = z := ofReal_re_of_im_eq_zero him
  rcases le_or_gt 0 z.re with hre | hre
  · exact hpos ⟨hzK, z.re, hre, hz⟩
  by_contra hzγ
  have hRc : IsClosed (range γ) :=
    (Theorem14.WalkCont.isClosedEmbedding_of_isProperCurve hγ).isClosed_range
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hRc.isOpen_compl z hzγ
  have hδR : Metric.ball ((z.re : ℝ) : ℂ) δ ∩ range γ = ∅ := by
    rw [hz]
    exact eq_empty_of_forall_notMem fun v hv => hball hv.1 hv.2
  obtain ⟨w, hwR, hwd⟩ := Metric.mem_closure_iff.1 hzcl δ hδ
  have hwB : w ∈ Metric.ball ((z.re : ℝ) : ℂ) δ ∩ H :=
    ⟨by rw [hz, Metric.mem_ball, dist_comm]; exact hwd, hwR.1.1⟩
  have hwL : w ∈ leftSideOf (range γ) :=
    mem_sideOf_of_mem_half_ball (I := Iio 0) hre (by rw [hz]; exact hzγ) hδ hδR hwB
  exact Set.disjoint_left.1 (disjoint_leftSideOf_rightSideOf_range hγ hγ0) hwL hwR

/-- **Points of the range on the boundary of its left complementary region lie on the left walk** (the mirror of
`frontier_rightSideOf_inter_subset`). -/
theorem frontier_leftSideOf_inter_subset (hγ : Supp9B.IsProperCurve γ) (hγ0 : γ 0 = 0)
    (hs : leftSideOf K = leftSideOf (range γ)) (hb : frontier (leftSideOf K) ∩ H = range γ ∩ H)
    (hneg : K ∩ ((↑) : ℝ → ℂ) '' Iic 0 ⊆ range γ) : frontier (leftSideOf K) ∩ K ⊆ range γ := by
  rintro z ⟨hzf, hzK⟩
  by_cases hzH : z ∈ H
  · have h1 : z ∈ frontier (leftSideOf K) ∩ H := ⟨hzf, hzH⟩
    rw [hb] at h1
    exact h1.1
  have hzcl : z ∈ closure (leftSideOf (range γ)) := hs ▸ frontier_subset_closure hzf
  have him : z.im = 0 :=
    le_antisymm (not_lt.1 (show ¬ (0 : ℝ) < z.im from hzH)) (im_nonneg_of_mem_closure_sideOf (I := Iio 0) hzcl)
  have hz : ((z.re : ℝ) : ℂ) = z := ofReal_re_of_im_eq_zero him
  rcases le_or_gt z.re 0 with hre | hre
  · exact hneg ⟨hzK, z.re, hre, hz⟩
  by_contra hzγ
  have hRc : IsClosed (range γ) :=
    (Theorem14.WalkCont.isClosedEmbedding_of_isProperCurve hγ).isClosed_range
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hRc.isOpen_compl z hzγ
  have hδR : Metric.ball ((z.re : ℝ) : ℂ) δ ∩ range γ = ∅ := by
    rw [hz]
    exact eq_empty_of_forall_notMem fun v hv => hball hv.1 hv.2
  obtain ⟨w, hwL, hwd⟩ := Metric.mem_closure_iff.1 hzcl δ hδ
  have hwB : w ∈ Metric.ball ((z.re : ℝ) : ℂ) δ ∩ H :=
    ⟨by rw [hz, Metric.mem_ball, dist_comm]; exact hwd, hwL.1.1⟩
  have hwR : w ∈ rightSideOf (range γ) :=
    mem_sideOf_of_mem_half_ball (I := Ioi 0) hre (by rw [hz]; exact hzγ) hδ hδR hwB
  exact Set.disjoint_left.1 (disjoint_leftSideOf_rightSideOf_range hγ hγ0) hwL hwR

/-- **The frontier bridge for one sample** (deterministic). Let `R = range γR`, `L = range γL` be proper curves from
`0` inside a closed set `K` with `closure (K ∩ ℍ) = K`, `K` missing the right side of `R` and the left side of `L`.
Then: the right and left complementary regions of `K` are the sides of `R` and `L`; their relative boundaries in `ℍ`
are `R ∩ ℍ` and `L ∩ ℍ`; the relative boundary in `ℍ` of the outer region is `(R ∪ L) ∩ ℍ`, inside the frontier of
`K`; `R` and `K` have the same points on `[0, ∞)`, `L` and `K` on `(−∞, 0]`; and the points of `K` on the boundary of
its right (left) complementary region lie on `R` (`L`). -/
theorem bridge_core (hγR : Supp9B.IsProperCurve γR) (hγR0 : γR 0 = 0) (hγL : Supp9B.IsProperCurve γL)
    (hγL0 : γL 0 = 0) (hKc : IsClosed K) (hKH : closure (K ∩ H) = K) (hRK : range γR ⊆ K)
    (hfR : K ∩ rightSideOf (range γR) = ∅) (hLK : range γL ⊆ K) (hfL : K ∩ leftSideOf (range γL) = ∅) :
    rightSideOf K = rightSideOf (range γR) ∧ leftSideOf K = leftSideOf (range γL) ∧
      frontier (rightSideOf K) ∩ H = range γR ∩ H ∧ frontier (leftSideOf K) ∩ H = range γL ∩ H ∧
      frontier (rightSideOf K ∪ leftSideOf K) ∩ H = (range γR ∪ range γL) ∩ H ∧
      (range γR ∪ range γL) ∩ H ⊆ frontier K ∧
      range γR ∩ ((↑) : ℝ → ℂ) '' Ici 0 = K ∩ ((↑) : ℝ → ℂ) '' Ici 0 ∧
      range γL ∩ ((↑) : ℝ → ℂ) '' Iic 0 = K ∩ ((↑) : ℝ → ℂ) '' Iic 0 ∧
      frontier (rightSideOf K) ∩ K ⊆ range γR ∧ frontier (leftSideOf K) ∩ K ⊆ range γL := by
  have hRc : IsClosed (range γR) :=
    (Theorem14.WalkCont.isClosedEmbedding_of_isProperCurve hγR).isClosed_range
  have hLc : IsClosed (range γL) :=
    (Theorem14.WalkCont.isClosedEmbedding_of_isProperCurve hγL).isClosed_range
  have hKcl : ∀ (I : Set ℝ), ∀ x ∈ I, (x : ℂ) ∈ K → (x : ℂ) ∈ closure (K ∩ H) := fun _ x _ hx => by
    rw [hKH]; exact hx
  have hsR : rightSideOf K = rightSideOf (range γR) :=
    sideOf_eq_of_frontier (I := Ioi 0) hRc hRK hfR (hKcl _)
  have hsL : leftSideOf K = leftSideOf (range γL) :=
    sideOf_eq_of_frontier (I := Iio 0) hLc hLK hfL (hKcl _)
  have hbR : frontier (rightSideOf K) ∩ H = range γR ∩ H := by
    rw [hsR]
    exact frontier_sideOf_inter_H (I := Ioi 0) hRc (range_inter_H_subset_closure_rightSideOf hγR hγR0)
  have hbL : frontier (leftSideOf K) ∩ H = range γL ∩ H := by
    rw [hsL]
    exact frontier_sideOf_inter_H (I := Iio 0) hLc (range_inter_H_subset_closure_leftSideOf hγL hγL0)
  have hoR : IsOpen (rightSideOf K) := isOpen_sideOf (I := Ioi 0) hKc
  have hoL : IsOpen (leftSideOf K) := isOpen_sideOf (I := Iio 0) hKc
  have hout : frontier (rightSideOf K ∪ leftSideOf K) ∩ H = (range γR ∪ range γL) ∩ H := by
    rw [(hoR.union hoL).frontier_eq]
    refine Subset.antisymm ?_ ?_
    · rintro w ⟨⟨hwcl, hwS⟩, hwH⟩
      rw [closure_union] at hwcl
      rcases hwcl with hw | hw
      · have h1 : w ∈ frontier (rightSideOf K) ∩ H :=
          ⟨by rw [hoR.frontier_eq]; exact ⟨hw, fun h => hwS (Or.inl h)⟩, hwH⟩
        rw [hbR] at h1
        exact ⟨Or.inl h1.1, hwH⟩
      · have h1 : w ∈ frontier (leftSideOf K) ∩ H :=
          ⟨by rw [hoL.frontier_eq]; exact ⟨hw, fun h => hwS (Or.inr h)⟩, hwH⟩
        rw [hbL] at h1
        exact ⟨Or.inr h1.1, hwH⟩
    · rintro w ⟨hw, hwH⟩
      have hwK : w ∈ K := hw.elim (fun h => hRK h) fun h => hLK h
      refine ⟨⟨?_, fun h => h.elim (fun h' => h'.1.2 hwK) fun h' => h'.1.2 hwK⟩, hwH⟩
      rcases hw with hw | hw
      · have h1 : w ∈ frontier (rightSideOf K) ∩ H := by rw [hbR]; exact ⟨hw, hwH⟩
        exact closure_mono subset_union_left (frontier_subset_closure h1.1)
      · have h1 : w ∈ frontier (leftSideOf K) ∩ H := by rw [hbL]; exact ⟨hw, hwH⟩
        exact closure_mono subset_union_right (frontier_subset_closure h1.1)
  have hfK : (range γR ∪ range γL) ∩ H ⊆ frontier K := by
    intro w hw
    have hwK : w ∈ K := hw.1.elim (fun h => hRK h) fun h => hLK h
    have hwcl : w ∈ closure (rightSideOf K ∪ leftSideOf K) := by
      rw [← hout] at hw
      exact frontier_subset_closure hw.1
    rw [frontier_eq_closure_inter_closure]
    refine ⟨subset_closure hwK, closure_mono ?_ hwcl⟩
    rintro v (hv | hv)
    · exact hv.1.2
    · exact hv.1.2
  have hrR : range γR ∩ ((↑) : ℝ → ℂ) '' Ici 0 = K ∩ ((↑) : ℝ → ℂ) '' Ici 0 := by
    refine Subset.antisymm (inter_subset_inter_left _ hRK) ?_
    rintro _ ⟨hzK, x, hx, rfl⟩
    refine ⟨?_, x, hx, rfl⟩
    rcases (mem_Ici.1 hx).eq_or_lt with h0 | hpos
    · subst h0
      exact ⟨0, by rw [hγR0, Complex.ofReal_zero]⟩
    · exact ofReal_mem_of_frontier (I := Ioi 0) hRc hfR (hKcl _) hpos hzK
  have hrL : range γL ∩ ((↑) : ℝ → ℂ) '' Iic 0 = K ∩ ((↑) : ℝ → ℂ) '' Iic 0 := by
    refine Subset.antisymm (inter_subset_inter_left _ hLK) ?_
    rintro _ ⟨hzK, x, hx, rfl⟩
    refine ⟨?_, x, hx, rfl⟩
    rcases (mem_Iic.1 hx).eq_or_lt with h0 | hneg
    · subst h0
      exact ⟨0, by rw [hγL0, Complex.ofReal_zero]⟩
    · exact ofReal_mem_of_frontier (I := Iio 0) hLc hfL (hKcl _) hneg hzK
  exact ⟨hsR, hsL, hbR, hbL, hout, hfK, hrR, hrL,
    frontier_rightSideOf_inter_subset hγR hγR0 hsR hbR (by rw [← hrR]; exact inter_subset_left),
    frontier_leftSideOf_inter_subset hγL hγL0 hsL hbL (by rw [← hrL]; exact inter_subset_left)⟩

/-- **The walks from the range, for one sample** (deterministic): under the hypotheses of `bridge_core`, if `R`
contains no nondegenerate preconnected set of negative reals and `L` none of positive reals, then
`R = closure (frontier (rightSideOf K) ∩ ℍ) ∪ (K ∩ [0, ∞)) = (frontier (rightSideOf K) ∩ K) ∪ (K ∩ [0, ∞))`, and the
left mirror. -/
theorem bridge_of_walks (hγR : Supp9B.IsProperCurve γR) (hγR0 : γR 0 = 0) (hγL : Supp9B.IsProperCurve γL)
    (hγL0 : γL 0 = 0) (hKc : IsClosed K) (hKH : closure (K ∩ H) = K) (hRK : range γR ⊆ K)
    (hfR : K ∩ rightSideOf (range γR) = ∅) (hLK : range γL ⊆ K) (hfL : K ∩ leftSideOf (range γL) = ∅)
    (hNR : ∀ S ⊆ range γR ∩ ((↑) : ℝ → ℂ) '' Iio 0, IsPreconnected S → S.Subsingleton)
    (hPL : ∀ S ⊆ range γL ∩ ((↑) : ℝ → ℂ) '' Ioi 0, IsPreconnected S → S.Subsingleton) :
    range γR = closure (frontier (rightSideOf K) ∩ H) ∪ (K ∩ ((↑) : ℝ → ℂ) '' Ici 0) ∧
      range γL = closure (frontier (leftSideOf K) ∩ H) ∪ (K ∩ ((↑) : ℝ → ℂ) '' Iic 0) ∧
      range γR = (frontier (rightSideOf K) ∩ K) ∪ (K ∩ ((↑) : ℝ → ℂ) '' Ici 0) ∧
      range γL = (frontier (leftSideOf K) ∩ K) ∪ (K ∩ ((↑) : ℝ → ℂ) '' Iic 0) := by
  obtain ⟨-, -, hbR, hbL, -, -, hrR, hrL, hfiR, hfiL⟩ :=
    bridge_core hγR hγR0 hγL hγL0 hKc hKH hRK hfR hLK hfL
  have hRc : IsClosed (range γR) :=
    (Theorem14.WalkCont.isClosedEmbedding_of_isProperCurve hγR).isClosed_range
  have hLc : IsClosed (range γL) :=
    (Theorem14.WalkCont.isClosedEmbedding_of_isProperCurve hγL).isClosed_range
  have hiR : range γR = closure (frontier (rightSideOf K) ∩ H) ∪ (K ∩ ((↑) : ℝ → ℂ) '' Ici 0) := by
    rw [hbR, ← hrR]
    refine Subset.antisymm (fun z hz => ?_)
      (union_subset (closure_minimal inter_subset_left hRc) inter_subset_left)
    rcases range_subset_closure_union_Ici hγR hNR hz with h | h
    · exact Or.inl h
    · exact Or.inr ⟨hz, h⟩
  have hiL : range γL = closure (frontier (leftSideOf K) ∩ H) ∪ (K ∩ ((↑) : ℝ → ℂ) '' Iic 0) := by
    rw [hbL, ← hrL]
    refine Subset.antisymm (fun z hz => ?_)
      (union_subset (closure_minimal inter_subset_left hLc) inter_subset_left)
    rcases range_subset_closure_union_Iic hγL hPL hz with h | h
    · exact Or.inl h
    · exact Or.inr ⟨hz, h⟩
  refine ⟨hiR, hiL, Subset.antisymm (fun z hz => ?_) (union_subset hfiR (by rw [← hrR]; exact inter_subset_left)),
    Subset.antisymm (fun z hz => ?_) (union_subset hfiL (by rw [← hrL]; exact inter_subset_left))⟩
  · rw [hiR] at hz
    rcases hz with h | h
    · exact Or.inl ⟨closure_minimal inter_subset_left isClosed_frontier h, hRK (by rw [hiR]; exact Or.inl h)⟩
    · exact Or.inr h
  · rw [hiL] at hz
    rcases hz with h | h
    · exact Or.inl ⟨closure_minimal inter_subset_left isClosed_frontier h, hLK (by rw [hiL]; exact Or.inl h)⟩
    · exact Or.inr h

/-- **The walks from the range in the nowhere-boundary-filling case, for one sample** (deterministic): under the
hypotheses of `bridge_core`, if `ℝ ∩ K` has empty interior then `R = frontier (rightSideOf K) ∩ K =
closure (frontier (rightSideOf K) ∩ ℍ)`, the left mirror, and
`R ∪ L = frontier (rightSideOf K ∪ leftSideOf K) ∩ K = closure (frontier (rightSideOf K ∪ leftSideOf K) ∩ ℍ)`. -/
theorem bridge_nbf_of_walks (hγR : Supp9B.IsProperCurve γR) (hγR0 : γR 0 = 0) (hγL : Supp9B.IsProperCurve γL)
    (hγL0 : γL 0 = 0) (hKc : IsClosed K) (hKH : closure (K ∩ H) = K) (hRK : range γR ⊆ K)
    (hfR : K ∩ rightSideOf (range γR) = ∅) (hLK : range γL ⊆ K) (hfL : K ∩ leftSideOf (range γL) = ∅)
    (hint : interior (((↑) : ℝ → ℂ) ⁻¹' K) = ∅) :
    range γR = frontier (rightSideOf K) ∩ K ∧ range γL = frontier (leftSideOf K) ∩ K ∧
      range γR = closure (frontier (rightSideOf K) ∩ H) ∧ range γL = closure (frontier (leftSideOf K) ∩ H) ∧
      range γR ∪ range γL = frontier (rightSideOf K ∪ leftSideOf K) ∩ K ∧
      range γR ∪ range γL = closure (frontier (rightSideOf K ∪ leftSideOf K) ∩ H) := by
  obtain ⟨-, -, hbR, hbL, hout, -, -, -, hfiR, hfiL⟩ :=
    bridge_core hγR hγR0 hγL hγL0 hKc hKH hRK hfR hLK hfL
  have hRc : IsClosed (range γR) :=
    (Theorem14.WalkCont.isClosedEmbedding_of_isProperCurve hγR).isClosed_range
  have hLc : IsClosed (range γL) :=
    (Theorem14.WalkCont.isClosedEmbedding_of_isProperCurve hγL).isClosed_range
  have hR : range γR = closure (range γR ∩ H) :=
    Subset.antisymm (range_subset_closure_of_interior_eq_empty hγR hRK hint)
      (closure_minimal inter_subset_left hRc)
  have hL : range γL = closure (range γL ∩ H) :=
    Subset.antisymm (range_subset_closure_of_interior_eq_empty hγL hLK hint)
      (closure_minimal inter_subset_left hLc)
  have hR' : range γR = closure (frontier (rightSideOf K) ∩ H) := by rw [hbR]; exact hR
  have hL' : range γL = closure (frontier (leftSideOf K) ∩ H) := by rw [hbL]; exact hL
  have hfR' : range γR = frontier (rightSideOf K) ∩ K := by
    refine Subset.antisymm (fun z hz => ⟨?_, hRK hz⟩) hfiR
    rw [hR'] at hz
    exact closure_minimal inter_subset_left isClosed_frontier hz
  have hfL' : range γL = frontier (leftSideOf K) ∩ K := by
    refine Subset.antisymm (fun z hz => ⟨?_, hLK hz⟩) hfiL
    rw [hL'] at hz
    exact closure_minimal inter_subset_left isClosed_frontier hz
  have hoR : IsOpen (rightSideOf K) := isOpen_sideOf (I := Ioi 0) hKc
  have hoL : IsOpen (leftSideOf K) := isOpen_sideOf (I := Iio 0) hKc
  refine ⟨hfR', hfL', hR', hL', Subset.antisymm ?_ ?_, ?_⟩
  · rintro z (hz | hz)
    · have h1 : z ∈ frontier (rightSideOf K) ∩ K := by rw [← hfR']; exact hz
      refine ⟨?_, h1.2⟩
      rw [(hoR.union hoL).frontier_eq]
      exact ⟨closure_mono subset_union_left (frontier_subset_closure h1.1),
        fun h => h.elim (fun h' => h'.1.2 h1.2) fun h' => h'.1.2 h1.2⟩
    · have h1 : z ∈ frontier (leftSideOf K) ∩ K := by rw [← hfL']; exact hz
      refine ⟨?_, h1.2⟩
      rw [(hoR.union hoL).frontier_eq]
      exact ⟨closure_mono subset_union_right (frontier_subset_closure h1.1),
        fun h => h.elim (fun h' => h'.1.2 h1.2) fun h' => h'.1.2 h1.2⟩
  · rintro z ⟨hzf, hzK⟩
    rw [(hoR.union hoL).frontier_eq, closure_union] at hzf
    obtain ⟨hzcl | hzcl, hzS⟩ := hzf
    · refine Or.inl (hfiR ⟨?_, hzK⟩)
      rw [hoR.frontier_eq]
      exact ⟨hzcl, fun h => hzS (Or.inl h)⟩
    · refine Or.inr (hfiL ⟨?_, hzK⟩)
      rw [hoL.frontier_eq]
      exact ⟨hzcl, fun h => hzS (Or.inr h)⟩
  · rw [hout, union_inter_distrib_right, closure_union, ← hR, ← hL]

end Bridge

end InteractingSLE.AuditFix.Frontier
