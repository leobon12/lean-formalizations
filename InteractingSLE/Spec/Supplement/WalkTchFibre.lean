/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBLvPinch
import InteractingSLE.Spec.Supplement.WalkWordsComp

/-!
# Boundary injectivity of a launch chart at the points of its piece

Packet PROVE-WALK-TOUCH (Theorem 1.4's walk chart, `WalkTouchMatchStatement`). A recorded piece `pc` of a boundary
walk is read through its launch chart: `PieceData pc A f W α` gives the boundary-limit map `f` of the chart's inverse
`φ = pc.1.2.1` and the model trace `α`; the physical piece is `g(t) = f(α(t))`. At a **real touch point**
`p = g(t₀)` (`t₀ > 0`) the launch chart is not analytic, and PROVE-WALK-WORDS2's cluster-set lemma needs that `p`
has a single real preimage under `f`:

* **`eq_of_eq_of_germs`** (abstract, after PROVE-T14-SBLEAVES' `SB.Lv.finite_real_fibre_of_cover`): for a boundary map
  `F` (`SB.Lv.IsBoundaryMap`), if every real boundary value `F(m) ≠ z` lies in an *unbounded* preconnected set missing
  `z` and `F(ℍ)`, then `z` has at most one real preimage. Two preimages `y₁ < y₂` give the semicircle Jordan curve
  `J ∋ z` (`SB.Lv.exists_isSemiJordan`), some `m ∈ (y₁, y₂)` with `F(m) ≠ z` (`exists_ne_of_injOn`) inside `J`
  (`SB.Lv.mem_jordanIn_of_isSemiJordan`); its germ misses `J ⊆ F(ℍ) ∪ {z}`, so lies inside `J`, which is bounded.
* **`eq_of_eq_of_old`**: the germs exist when `frontier F(ℍ) ∩ ℍ ⊆ A`, `F(ℍ) ∩ A = ∅`, `z ∉ A`, and every point of
  `A ∩ ℍ` lies in a preconnected subset of `A` with a real point: a real value `F(m)` uses a real ray at `z`
  (`SB.Lv.realGermL/R`); a value `F(m) ∈ ℍ` is a frontier point of `F(ℍ)`, hence in `A`, and its germ is the connecting
  set plus a real ray.
* **`PieceData.eq_of_land_eq`**: for a recorded piece with earlier pieces `pre` (old set `A`), every point `g(t)`,
  `t > 0`, has at most one real preimage under `f` — the frontier and disjointness facts of the launch chart, real
  time-0 tips (all launches are real), and `exists_preconnected_old` (an old point `g'(s)` is joined to the real start
  `g'(0)` by `g'([0, s])`).
* **`PieceData.tendsto_fwd`**: then the launch chart's forward map tends to `α(t)` at `g(t)` within the launch domain
  (cluster points `ξ` satisfy `f(ξ) = g(t)`; in `ℍ` injectivity, on `ℝ` the fibre).

Deterministic.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Set Topology Complex Metric Bornology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.WalkTch

open WalkBdry WalkWords SB.Lv

/-! ### Real rays are unbounded -/

theorem not_isBounded_realGermL (z : ℂ) : ¬ IsBounded (realGermL z) := by
  intro hb
  obtain ⟨R, hR⟩ := hb.subset_closedBall 0
  set x : ℝ := min z.re (-(R + 1)) - 1 with hx
  have hx1 : x < z.re := by have := min_le_left z.re (-(R + 1)); linarith
  have hx2 : x < -(R + 1) := by have := min_le_right z.re (-(R + 1)); linarith
  have hne : (x : ℂ) ≠ z := fun h => by
    have := congrArg Complex.re h
    simp only [ofReal_re] at this
    linarith
  have h1 := hR ⟨x, ⟨hne, hx1.le⟩, rfl⟩
  rw [mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs] at h1
  have := neg_le_abs x
  linarith

theorem not_isBounded_realGermR (z : ℂ) : ¬ IsBounded (realGermR z) := by
  intro hb
  obtain ⟨R, hR⟩ := hb.subset_closedBall 0
  set x : ℝ := max z.re (R + 1) + 1 with hx
  have hx1 : z.re < x := by have := le_max_left z.re (R + 1); linarith
  have hx2 : R + 1 < x := by have := le_max_right z.re (R + 1); linarith
  have hne : (x : ℂ) ≠ z := fun h => by
    have := congrArg Complex.re h
    simp only [ofReal_re] at this
    linarith
  have h1 := hR ⟨x, ⟨hne, hx1.le⟩, rfl⟩
  rw [mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs] at h1
  have := le_abs_self x
  linarith

/-! ### The abstract fibre lemma -/

section Abstract

variable {F : ℂ → ℂ}

/-- A real boundary value of a boundary map lies in the closure of its image. -/
theorem mem_closure_image_of_real (hF : IsBoundaryMap F) (m : ℝ) : F m ∈ closure (F '' H) := by
  have hFlim : Tendsto (fun ε : ℝ => F ((m : ℂ) + (ε : ℂ) * I)) (𝓝[>] 0) (𝓝 (F m)) :=
    ((hF.2.1 _ (show (0 : ℝ) ≤ ((m : ℂ)).im by simp)).tendsto.mono_left
      (nhdsWithin_mono _ QuantumZipper.H_subset_Hbar)).comp (SB.Lv.tendsto_vertical m)
  refine mem_closure_of_tendsto hFlim ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact ⟨_, show 0 < ((m : ℂ) + (ε : ℂ) * I).im by simpa using hε, rfl⟩

/-- A real boundary value of a boundary map lies in `ℍ̄`. -/
theorem mem_Hbar_of_real (hF : IsBoundaryMap F) (m : ℝ) : F m ∈ Hbar :=
  QuantumZipper.isClosed_Hbar.closure_subset_iff.2
    (by rintro _ ⟨w, hw, rfl⟩; exact QuantumZipper.H_subset_Hbar (hF.2.2.2.1 hw)) (mem_closure_image_of_real hF m)

theorem false_of_lt_of_germs (hF : IsBoundaryMap F) {z : ℂ}
    (hgerm : ∀ m : ℝ, F m ≠ z → ∃ G : Set ℂ, IsPreconnected G ∧ F m ∈ G ∧ Disjoint G (F '' H) ∧ z ∉ G ∧
      ¬ IsBounded G) {y₁ y₂ : ℝ} (hlt : y₁ < y₂) (h₁ : F y₁ = z) (h₂ : F y₂ = z) : False := by
  obtain ⟨J, hJ⟩ := exists_isSemiJordan hF hlt h₁ h₂
  obtain ⟨m, hm, hFm⟩ := exists_ne_of_injOn hF.1 hF.2.1 hF.2.2.1 hlt z
  have hmin := mem_jordanIn_of_isSemiJordan hF hJ
    (abs_lt.2 ⟨by linarith [hm.1, hm.2], by linarith [hm.1, hm.2]⟩) hFm
  obtain ⟨G, hGc, hmG, hGF, hzG, hGu⟩ := hgerm m hFm
  have hGJ : Disjoint G J := by
    refine Set.disjoint_left.2 fun p hpG hpJ => ?_
    rcases hJ.2.2.1 p hpJ with rfl | ⟨w, hw, -, rfl⟩
    · exact hzG hpG
    · exact Set.disjoint_left.1 hGF hpG ⟨w, hw, rfl⟩
  exact hGu ((WangWu.isBounded_jordanIn hJ.1).subset
    (WangWu.IsPreconnected.subset_jordanIn hJ.1 hGc hGJ ⟨_, hmG, hmin⟩))

/-- **The fibre lemma from unbounded germs** (see the module docstring). -/
theorem eq_of_eq_of_germs (hF : IsBoundaryMap F) {z : ℂ}
    (hgerm : ∀ m : ℝ, F m ≠ z → ∃ G : Set ℂ, IsPreconnected G ∧ F m ∈ G ∧ Disjoint G (F '' H) ∧ z ∉ G ∧
      ¬ IsBounded G) {y₁ y₂ : ℝ} (h₁ : F y₁ = z) (h₂ : F y₂ = z) : y₁ = y₂ := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact false_of_lt_of_germs hF hgerm hlt h₁ h₂
  · exact false_of_lt_of_germs hF hgerm hlt h₂ h₁

/-- Real points other than `z` lie in an unbounded real ray at `z` missing `F(ℍ)`. -/
theorem exists_realGerm (hF : IsBoundaryMap F) {z : ℂ} {x : ℝ} (hx : (x : ℂ) ≠ z) :
    ∃ G : Set ℂ, IsPreconnected G ∧ (x : ℂ) ∈ G ∧ Disjoint G (F '' H) ∧ z ∉ G ∧ ¬ IsBounded G := by
  have hdis : ∀ G' : Set ℂ, G' ⊆ range ((↑) : ℝ → ℂ) → Disjoint G' (F '' H) := fun G' hG' =>
    Set.disjoint_left.2 fun p hp ⟨w, hw, hpw⟩ => by
      obtain ⟨r, rfl⟩ := hG' hp
      have h0 : (0 : ℝ) < (F w).im := hF.2.2.2.1 hw
      rw [hpw, ofReal_im] at h0
      exact lt_irrefl 0 h0
  rcases mem_realGerm hx with h | h
  · exact ⟨_, isPreconnected_realGermL z, h, hdis _ (image_subset_range _ _), notMem_realGermL z,
      not_isBounded_realGermL z⟩
  · exact ⟨_, isPreconnected_realGermR z, h, hdis _ (image_subset_range _ _), notMem_realGermR z,
      not_isBounded_realGermR z⟩

/-- **The fibre lemma from an old set connected to `ℝ`** (see the module docstring). -/
theorem eq_of_eq_of_old (hF : IsBoundaryMap F) {A : Set ℂ} (hfront : frontier (F '' H) ∩ H ⊆ A)
    (hdisj : Disjoint (F '' H) A)
    (hconn : ∀ w ∈ A ∩ H, ∃ S ⊆ A, IsPreconnected S ∧ w ∈ S ∧ ∃ x : ℝ, (x : ℂ) ∈ S)
    {z : ℂ} (hzA : z ∉ A) {y₁ y₂ : ℝ} (h₁ : F y₁ = z) (h₂ : F y₂ = z) : y₁ = y₂ := by
  refine eq_of_eq_of_germs hF (fun m hm => ?_) h₁ h₂
  by_cases him : (F m).im = 0
  · have he : (((F m).re : ℝ) : ℂ) = F m := Complex.ext (by simp) (by simp [him])
    rw [← he] at hm ⊢
    exact exists_realGerm hF hm
  · have hmH : F m ∈ H := lt_of_le_of_ne (mem_Hbar_of_real hF m) (Ne.symm him)
    have hfr : F m ∈ frontier (F '' H) := by
      rw [hF.2.2.2.2.1.frontier_eq]
      exact ⟨mem_closure_image_of_real hF m, hF.2.2.2.2.2.1 m⟩
    obtain ⟨S, hSA, hSc, hmS, x, hxS⟩ := hconn _ ⟨hfront ⟨hfr, hmH⟩, hmH⟩
    have hxz : (x : ℂ) ≠ z := fun h => hzA (h ▸ hSA hxS)
    obtain ⟨G, hGc, hxG, hGF, hzG, hGu⟩ := exists_realGerm hF hxz
    refine ⟨S ∪ G, hSc.union (x : ℂ) hxS hxG hGc, Or.inl hmS, ?_, ?_, fun hb => hGu (hb.subset subset_union_right)⟩
    · exact Disjoint.union_left (hdisj.symm.mono_left hSA) hGF
    · rintro (h | h)
      · exact hzA (hSA h)
      · exact hzG h

end Abstract

/-! ### The launch chart of a recorded piece -/

section Piece

variable {pc : Piece} {A : Set ℂ} {f : ℂ → ℂ} {W : ℝ≥0 → ℝ} {α : ℝ≥0 → ℂ}

theorem PieceData.eqOn_land (d : PieceData pc A f W α) : EqOn f pc.1.2.1 H := fun z hz =>
  landing_eq_of_mem_H d.conf hz (d.land z (QuantumZipper.H_subset_Hbar hz))

/-- **The boundary-limit map of a launch chart is a boundary map.** -/
theorem PieceData.isBoundaryMap (d : PieceData pc A f W α) : IsBoundaryMap f := by
  obtain ⟨C, hC⟩ := d.bdd
  refine isBoundaryMap_of_isConformal d.conf (GW1P.continuousOn_of_tendsto d.land) (PieceData.eqOn_land d) ?_
  refine tendsto_norm_atTop_iff_cobounded.1 (tendsto_atTop_mono' _ ?_
    (tendsto_atTop_add_const_right _ (-C) (tendsto_norm_cobounded_atTop.mono_left inf_le_left)))
  refine eventually_inf_principal.2 (Eventually.of_forall fun w hw => ?_)
  have h1 := hC w (QuantumZipper.H_subset_Hbar hw)
  have h2 := norm_sub_norm_le w (f w)
  rw [norm_sub_rev] at h2
  linarith

/-- The launch domain of a recorded piece is the domain of its prefix chart at own time `0`. -/
theorem PieceData.prefixChart_zero_dom (d : PieceData pc A f W α) :
    ((prefixChart pc 0).dom : Set ℂ) = pc.1.2.1 '' H := by
  have himg : (prefixChart pc 0).2.1 '' H = pc.1.2.1 '' H :=
    image_congr fun w hw => d.prefixChart_zero_inv hw
  change interior ((prefixChart pc 0).2.1 '' H) = _
  rw [himg, d.conf.isOpen_image.interior_eq]

/-- **Old points are joined to `ℝ` inside the old set**: a point `g'(s)` of an earlier piece by `g'([0, s])`, whose
start `g'(0)` is real. -/
theorem exists_preconnected_old {pre : List Piece}
    (hd : ∀ p ∈ pre, ∃ (A' : Set ℂ) (f' : ℂ → ℂ) (W' : ℝ≥0 → ℝ) (α' : ℝ≥0 → ℂ), PieceData p A' f' W' α')
    (hreal : ∀ p ∈ pre, ∀ z, p.1.tipAt p.2.1 0 z → z.im = 0) :
    ∀ w ∈ ⋃ p ∈ pre, p.1.tipSet p.2.1 p.2.2, ∃ S ⊆ ⋃ p ∈ pre, p.1.tipSet p.2.1 p.2.2,
      IsPreconnected S ∧ w ∈ S ∧ ∃ x : ℝ, (x : ℂ) ∈ S := by
  intro w hw
  obtain ⟨p, hp, hwp⟩ := mem_iUnion₂.1 hw
  obtain ⟨A', f', W', α', d⟩ := hd p hp
  rw [d.tipSet_eq] at hwp
  obtain ⟨t, ht, rfl⟩ := hwp
  have hsub : Icc 0 t ⊆ {s : ℝ≥0 | (s : ℝ≥0∞) ≤ p.2.2} := fun s hs =>
    le_trans (ENNReal.coe_le_coe.2 hs.2) ht
  refine ⟨(fun s => f' (α' s)) '' Icc 0 t, ?_, isPreconnected_Icc.image _ (d.continuousOn.mono hsub),
    ⟨t, ⟨zero_le, le_rfl⟩, rfl⟩, ?_⟩
  · rintro _ ⟨s, hs, rfl⟩
    exact mem_iUnion₂.2 ⟨p, hp, by rw [d.tipSet_eq]; exact ⟨s, hsub hs, rfl⟩⟩
  · have h0 := hreal p hp _ (d.tipAt (hsub ⟨le_rfl, zero_le⟩))
    exact ⟨(f' (α' 0)).re, 0, ⟨le_rfl, zero_le⟩, Complex.ext (by simp) (by simp [h0])⟩

/-- **Boundary injectivity of a launch chart at the points of its piece** (see the module docstring). -/
theorem PieceData.eq_of_land_eq {pre : List Piece}
    (d : PieceData pc (⋃ p ∈ pre, p.1.tipSet p.2.1 p.2.2) f W α)
    (hfront : frontier ((prefixChart pc 0).dom : Set ℂ) ∩ H ⊆ prefixSet pre pc 0)
    (hdisj : Disjoint ((prefixChart pc 0).dom : Set ℂ) (prefixSet pre pc 0))
    (hreal0 : ∀ z, pc.1.tipAt pc.2.1 0 z → z.im = 0)
    (hconn : ∀ w ∈ ⋃ p ∈ pre, p.1.tipSet p.2.1 p.2.2, ∃ S ⊆ ⋃ p ∈ pre, p.1.tipSet p.2.1 p.2.2,
      IsPreconnected S ∧ w ∈ S ∧ ∃ x : ℝ, (x : ℂ) ∈ S)
    {t : ℝ≥0} (ht0 : 0 < t) (ht : (t : ℝ≥0∞) ≤ pc.2.2) {y₁ y₂ : ℝ} (h₁ : f y₁ = f (α t))
    (h₂ : f y₂ = f (α t)) : y₁ = y₂ := by
  rw [(PieceData.prefixChart_zero_dom d)] at hfront hdisj
  have himg : f '' H = pc.1.2.1 '' H := image_congr fun w hw => (PieceData.eqOn_land d) hw
  refine eq_of_eq_of_old (PieceData.isBoundaryMap d) (A := ⋃ p ∈ pre, p.1.tipSet p.2.1 p.2.2) ?_ ?_
    (fun w hw => hconn w hw.1) (d.avoid t ht0 ht) h₁ h₂
  · rw [himg]
    intro z hz
    rcases (hfront hz).1 with hpre | ⟨s, hs, hst⟩
    · exact hpre
    · have hs0 : s = 0 := le_antisymm (by exact_mod_cast hs) bot_le
      subst hs0
      have hzH : (0 : ℝ) < z.im := hz.2
      rw [hreal0 z hst] at hzH
      exact absurd hzH (lt_irrefl 0)
  · rw [himg]
    refine Set.disjoint_left.2 fun z hz hzA => Set.disjoint_left.1 hdisj hz ⟨Or.inl hzA, ?_⟩
    obtain ⟨w, hw, rfl⟩ := hz
    exact d.conf.2.1 hw

/-- **The launch chart's forward map at a point of its piece** (see the module docstring). -/
theorem PieceData.tendsto_fwd (d : PieceData pc A f W α) {t : ℝ≥0} (ht : (t : ℝ≥0∞) ≤ pc.2.2)
    (hfib : ∀ y₁ y₂ : ℝ, f y₁ = f (α t) → f y₂ = f (α t) → y₁ = y₂) :
    Tendsto pc.1.1 (𝓝[pc.1.2.1 '' H] (f (α t))) (𝓝 (α t)) := by
  obtain ⟨C, hC⟩ := d.bdd
  set q : ℂ := f (α t) with hq
  have hfc : ContinuousOn f Hbar := GW1P.continuousOn_of_tendsto d.land
  have hev : ∀ᶠ z in 𝓝[pc.1.2.1 '' H] q, pc.1.1 z ∈ H ∧ f (pc.1.1 z) = z ∧
      pc.1.1 z ∈ closedBall (0 : ℂ) (‖q‖ + 1 + C) := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (ball_mem_nhds q one_pos)] with z hz hzb
    obtain ⟨u, hu, rfl⟩ := hz
    rw [d.conf.2.2 u hu]
    have hfu : f u = pc.1.2.1 u := (PieceData.eqOn_land d) hu
    refine ⟨hu, hfu, ?_⟩
    rw [mem_closedBall, dist_zero_right]
    have h1 := hC u (QuantumZipper.H_subset_Hbar hu)
    rw [mem_ball, dist_eq_norm] at hzb
    have h2 := norm_sub_norm_le u (f u)
    rw [norm_sub_rev] at h2
    have h3 := norm_sub_norm_le (pc.1.2.1 u) q
    rw [← hfu] at hzb h3
    linarith
  have hid : Tendsto (fun z : ℂ => z) (𝓝[pc.1.2.1 '' H] q) (𝓝 q) := tendsto_nhdsWithin_iff.1 tendsto_id |>.1
  refine (isCompact_closedBall (0 : ℂ) _).tendsto_nhds_of_unique_mapClusterPt (hev.mono fun z hz => hz.2.2) ?_
  intro ξ _ hξ
  have hTH : ∀ᶠ z in 𝓝[pc.1.2.1 '' H] q, pc.1.1 z ∈ H := hev.mono fun z hz => hz.1
  have hξH : ξ ∈ Hbar := by
    by_contra hn
    obtain ⟨w, hw1, hw2⟩ := (hξ.frequently (QuantumZipper.isClosed_Hbar.isOpen_compl.mem_nhds hn)).and_eventually
      hTH |>.exists
    exact hw1 (le_of_lt (show (0 : ℝ) < (pc.1.1 w).im from hw2))
  have hfξ : f ξ = q := by
    by_contra hne
    set r : ℝ := dist (f ξ) q / 2 with hr
    have hr0 : 0 < r := by rw [hr]; exact half_pos (dist_pos.2 hne)
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.1 ((hfc ξ hξH).preimage_mem_nhdsWithin (ball_mem_nhds _ hr0))
    obtain ⟨w, hw1, hw2, hw3⟩ := ((hξ.frequently (ball_mem_nhds ξ hε)).and_eventually
      (hev.and (hid.eventually (ball_mem_nhds q hr0)))).exists
    have h1 : f (pc.1.1 w) ∈ ball (f ξ) r := hball ⟨hw1, le_of_lt (show (0 : ℝ) < (pc.1.1 w).im from hw2.1)⟩
    rw [hw2.2.1] at h1
    have h2 := dist_triangle (f ξ) w q
    have hw3' : dist w q < r := hw3
    rw [mem_ball, dist_comm] at h1
    linarith
  by_cases hξH' : ξ ∈ H
  · have hqD : q ∈ pc.1.2.1 '' H := ⟨ξ, hξH', by rw [← hfξ]; exact ((PieceData.eqOn_land d) hξH').symm⟩
    have hαH := d.mem_H_of_mem_image ht hqD
    refine d.conf.injOn hξH' hαH ?_
    rw [← (PieceData.eqOn_land d) hξH', ← (PieceData.eqOn_land d) hαH, hfξ]
  · have hξ0 : ξ.im = 0 := le_antisymm (not_lt.1 hξH') hξH
    have hαH : α t ∉ H := fun hαH => landing_notMem_image_H d.conf hξ0 (d.land ξ hξH)
      ⟨α t, hαH, by rw [hfξ, hq]; exact ((PieceData.eqOn_land d) hαH).symm⟩
    have hα0 : (α t).im = 0 := le_antisymm (not_lt.1 hαH) (d.mem_Hbar ht)
    have hre : ∀ ζ : ℂ, ζ.im = 0 → ((ζ.re : ℝ) : ℂ) = ζ := fun ζ h => Complex.ext (by simp) (by simp [h])
    have := hfib ξ.re (α t).re (by rw [hre ξ hξ0]; exact hfξ) (by rw [hre _ hα0])
    rw [← hre ξ hξ0, ← hre _ hα0, this]

end Piece

end InteractingSLE.Theorem14.WalkTch
