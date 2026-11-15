/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma71OArc

/-!
# Lemma 7.1's inherited branch: the deterministic normalization lemma in the chart

Packet PROVE-LEMMA71O. Supplement §2.3, "Deterministic normalization lemma" (2), `source/spec/p433-480.md` L472–L520
(the branch of Lemma 7.1's pocket chart, p. 225: "with the inherited logarithmic-derivative branch"). On a pathwise
pocket frame with a logarithm `L` of the chart derivative whose imaginary part is the chart's lift, there is **one**
integer `n` with `Lemma71N.IsPocketBranch β α c n` (`exists_isPocketBranch`). The proof follows the source:

* at every wall point the transition from the chart to the wall's Loewner map reflects with positive derivative, so
  `Im (log f_q′ − L)` has an integer boundary value (`wall_local`, from `exists_int_wall`); it is constant along each
  wall arc (`arc_times_lt`, `eq_of_isPreconnected_of_local`) and does not depend on the stopping time (Aux. lemma 57,
  `tendsto_logDerivFwd_sub_of_le`);
* at the opening corner the map of the union `β([0, q₁]) ∪ α([0, q₂])` flattens both sides at once (the pocket lies in
  its unbounded domain, `subset_H_diff_fillH_prefixSet`); its transition has a removable singularity at `0`
  (`exists_int_corner`) and agrees with each wall's map near the wall points (`union_wall_data`), so the two walls'
  integers coincide (`corner_frame`).

Deterministic.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec7.Lemma71O

open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull logDerivFwd)
open Lemma71N (IsPocketFrame IsPocketBranch)

/-! ### The boundary integer of a wall -/

section WallInt

variable {c : Chart} {C : Set ℂ} {L : ℂ → ℂ}

/-- The boundary integer of a wall at a real chart point: `Im (log f_q′ − L) ∘ c.2.1 → 2πm`. -/
def WallInt (c : Chart) (L : ℂ → ℂ) (W : ℝ≥0 → ℝ) (q : ℝ≥0) (ξ : ℝ) (m : ℤ) : Prop :=
  Tendsto (fun y => (logDerivFwd (fun r : ℝ => W r.toNNReal) q (c.2.1 y) - L (c.2.1 y)).im) (𝓝[H] (ξ : ℂ))
    (𝓝 (2 * π * m))

theorem dist_ofReal_ofReal (a b : ℝ) : dist (a : ℂ) (b : ℂ) = dist a b := by
  rw [dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.dist_eq, Real.norm_eq_abs]

theorem nhdsWithin_H_ofReal_neBot (ξ : ℝ) : (𝓝[H] (ξ : ℂ)).NeBot :=
  mem_closure_iff_nhdsWithin_neBot.1 (by rw [closure_H]; exact mem_Hbar_of_im_eq_zero (by simp))

theorem WallInt.unique {W : ℝ≥0 → ℝ} {q : ℝ≥0} {ξ : ℝ} {m m' : ℤ} (h : WallInt c L W q ξ m)
    (h' : WallInt c L W q ξ m') : m = m' := by
  have := nhdsWithin_H_ofReal_neBot ξ
  have he := tendsto_nhds_unique h h'
  have hpi : (2 * π : ℝ) ≠ 0 := by positivity
  exact_mod_cast mul_left_cancel₀ hpi he

/-- **Change of stopping time**: the boundary integer at `ξ` does not depend on the stopping time `q > s` of the
wall, `s` the landing time. -/
theorem WallInt.of_le {η : ℝ≥0 → ℂ} {W : ℝ≥0 → ℝ} (htr : IsGeneratingTrace W ⊤ η) (hW : Continuous W)
    (hW0 : W 0 = 0) (hη : Lemma71I.IsSimpleProper η) (hc : c.IsConformal)
    (hCη : ∀ q : ℝ≥0, (c.dom : Set ℂ) ⊆ H \ fillH (η '' Icc 0 q)) {ξ : ℝ} {s q q' : ℝ≥0} (hsq : s < q)
    (hqq' : q ≤ q') (hland : Tendsto c.2.1 (𝓝[H] (ξ : ℂ)) (𝓝 (η s))) {m : ℤ} :
    WallInt c L W q' ξ m ↔ WallInt c L W q ξ m := by
  have hd := tendsto_logDerivFwd_sub_of_le htr hW hW0 hη hc hCη (mem_Hbar_of_im_eq_zero (by simp)) hsq hqq'
    hland
  constructor
  · intro h
    have := h.sub hd
    rw [sub_zero] at this
    refine this.congr fun y => ?_
    simp only [Complex.sub_im]; ring
  · intro h
    have := h.add hd
    rw [add_zero] at this
    refine this.congr fun y => ?_
    simp only [Complex.sub_im]; ring

/-- **The local boundary integer of a wall** (from `exists_int_wall`): at a real point `ξ` of an open set `S` of chart
points landing on the wall `η`, with landing time `s < q`, the boundary integer exists and is constant near `ξ`. -/
theorem wall_local {η : ℝ≥0 → ℂ} {W : ℝ≥0 → ℝ} (htr : IsGeneratingTrace W ⊤ η) (hW : Continuous W)
    (hW0 : W 0 = 0) (hη : Lemma71I.IsSimpleProper η) (hc : c.IsConformal) (hdom : (c.dom : Set ℂ) = C)
    (hL : IsDerivLog c.1 L C) (hCq : ∀ q : ℝ≥0, C ⊆ H \ fwdHull (fun r : ℝ => W r.toNNReal) q) {ℓ : ℂ → ℂ}
    (hℓ : ∀ w : ℝ, Tendsto c.2.1 (𝓝[H] (w : ℂ)) (𝓝 (ℓ w))) (hℓc : Continuous fun t : ℝ => ℓ t) {S : Set ℝ}
    (hSo : IsOpen S) (hSη : ∀ w ∈ S, ∃ s : ℝ≥0, ℓ w = η s) {ξ : ℝ} (hξ : ξ ∈ S) {s q : ℝ≥0} (hsq : s < q)
    (hξs : ℓ ξ = η s) : ∃ m : ℤ, ∃ ε > 0, ∀ w : ℝ, |w - ξ| < ε → WallInt c L W q w m := by
  have hW'c : Continuous fun r : ℝ => W r.toNNReal := hW.comp continuous_real_toNNReal
  have hW'0 : (fun r : ℝ => W r.toNNReal) 0 = 0 := by simp [hW0]
  obtain ⟨ρ, hρ, hball⟩ := Lemma71N.exists_ball_tail hη hsq
  obtain ⟨r₁, hr₁, hr₁S⟩ := Metric.isOpen_iff.1 hSo ξ hξ
  obtain ⟨r₂, hr₂, hr₂ℓ⟩ := Metric.continuous_iff.1 hℓc ξ ρ hρ
  set r := min r₁ r₂ with hr
  have hr0 : 0 < r := lt_min hr₁ hr₂
  obtain ⟨m, ε, hε, hεr, hint⟩ := exists_int_wall (isLoewnerTrace_of_isGeneratingTrace htr) hW'c hW'0 q.2 hc hdom hL
    (hCq q) hr0 fun z hz hz0 => by
      have hzx : z = ((z.re : ℝ) : ℂ) := eq_ofReal_re_of_im_eq_zero hz0
      have hd : dist z.re ξ < r := by
        rw [hzx, mem_ball, dist_ofReal_ofReal] at hz; exact hz
      obtain ⟨s', hs'⟩ := hSη z.re (hr₁S (lt_of_lt_of_le hd (min_le_left _ _)))
      have hs'q : s' ≤ q := by
        by_contra hlt
        refine hball s' (le_of_lt (not_le.1 hlt)) ?_
        rw [← hs', ← hξs, mem_ball]
        exact hr₂ℓ _ (lt_of_lt_of_le hd (min_le_right _ _))
      refine ⟨ℓ z.re, ?_, ?_⟩
      · rw [hs']; exact notMem_H_diff_fwdHull htr hs'q
      · rw [hzx]; exact hℓ z.re
  refine ⟨m, ε, hε, fun w hw => hint (w : ℂ) ?_ (by simp)⟩
  rw [mem_ball, dist_ofReal_ofReal, Real.dist_eq]
  exact hw

end WallInt

/-! ### The union of the two walls' prefixes near one wall -/

section UnionWall

variable {c : Chart}

/-- **Near a wall point off the other wall, the union map agrees with the wall's map**: the union transition has a
real limit and the canonical logarithm of the union and `log f_q′` have the same imaginary boundary value. -/
theorem union_wall_data {Γ : Set ℂ} (hΓc : IsCompact Γ) (hKΓ : IsHPHull (fillH Γ)) {gK LK : ℂ → ℂ}
    (hgK : IsMapOut (fillH Γ) gK) (hLK : Restart.IsCanonicalDerivLog (fillH Γ) gK LK) (hc : c.IsConformal)
    (hCΓ : (c.dom : Set ℂ) ⊆ H \ fillH Γ) {η η' : ℝ≥0 → ℂ} (hη : Lemma71I.IsSimpleProper η)
    (hη' : Lemma71I.IsSimpleProper η') {W : ℝ≥0 → ℝ} (htr : IsGeneratingTrace W ⊤ η) (hW : Continuous W)
    (hW0 : W 0 = 0) {q : ℝ≥0} (hsub : η '' Icc 0 q ⊆ Γ) (hΓsub : Γ ⊆ η '' Icc 0 q ∪ range η')
    (hCq : (c.dom : Set ℂ) ⊆ H \ fwdHull (fun r : ℝ => W r.toNNReal) q) {x : ℂ} (hx : x ∈ Hbar) {s : ℝ≥0}
    (hsq : s < q) (hsη' : η s ∉ range η') (hland : Tendsto c.2.1 (𝓝[H] x) (𝓝 (η s))) :
    (∃ w : ℂ, w.im = 0 ∧ Tendsto (fun y => gK (c.2.1 y)) (𝓝[H] x) (𝓝 w)) ∧
      Tendsto (fun y => (LK (c.2.1 y)).im - (logDerivFwd (fun r : ℝ => W r.toNNReal) q (c.2.1 y)).im) (𝓝[H] x)
        (𝓝 0) := by
  have hq0 : 0 < q := lt_of_le_of_lt (zero_le (a := s)) hsq
  obtain ⟨ρ, hρ, hρη'⟩ := Lemma71N.exists_ball_notMem_range hη' hsη'
  have hloc : Γ ∩ ball (η s) ρ ⊆ η '' Icc 0 q := by
    rintro z ⟨hzΓ, hzb⟩
    rcases hΓsub hzΓ with h | ⟨u, rfl⟩
    · exact h
    · exact absurd hzb (hρη' u)
  obtain ⟨v, hv, hT⟩ := exists_real_tendsto_wall htr hW hW0 hc hCq hx hsq.le hland
  exact ⟨exists_tendsto_mapOut_comp hΓc hKΓ hgK hc hCΓ hx hland hρ htr hW hW0 hη.2.1 hq0 hsub hloc hv hT,
    tendsto_lift_sub_of_agree_chart hΓc hKΓ hgK hLK hc hCΓ hland hρ htr hW hW0 hη.2.1 hq0 hsub hloc hv hT⟩

end UnionWall

/-! ### The corner of the pocket frame -/

section Corner

variable {β α : ℝ≥0 → ℂ} {C : Set ℂ} {c : Chart} {Ψ : ℂ → ℂ} {a b : ℝ} {L : ℂ → ℂ} {Wβ Wα : ℝ≥0 → ℝ}

open PocketFrame

theorem subset_H_diff_fwdHull_left (hF : IsPocketFrame β α C c Ψ a b) (htr : IsGeneratingTrace Wβ ⊤ β)
    (q : ℝ≥0) : C ⊆ H \ fwdHull (fun r : ℝ => Wβ r.toNNReal) q := fun _ hz =>
  Lemma71N.sides_subset_H_diff_fwdHull hF.hβ htr q (Or.inr (hF.subset_sides hz).2)

theorem subset_H_diff_fwdHull_right (hF : IsPocketFrame β α C c Ψ a b) (htr : IsGeneratingTrace Wα ⊤ α)
    (q : ℝ≥0) : C ⊆ H \ fwdHull (fun r : ℝ => Wα r.toNNReal) q := fun _ hz =>
  Lemma71N.sides_subset_H_diff_fwdHull hF.hα htr q (Or.inl (hF.subset_sides hz).1)

theorem dom_subset_H_diff_fillH {η : ℝ≥0 → ℂ} {W : ℝ≥0 → ℝ} (htr : IsGeneratingTrace W ⊤ η)
    (hdom : (c.dom : Set ℂ) = C) (hCq : ∀ q : ℝ≥0, C ⊆ H \ fwdHull (fun r : ℝ => W r.toNNReal) q)
    (q : ℝ≥0) : (c.dom : Set ℂ) ⊆ H \ fillH (η '' Icc 0 q) := by
  rw [hdom, ← SideHeight.fwdHull_eq_fillH_of_isGeneratingTrace htr (WithTop.coe_lt_top q)]
  exact hCq q

/-- **The corner of the pocket frame** (supplement §2.3: "Reflection on this connected interval again normalizes both
sides together"): with the right prefix stopped at a time `q₂` before a gap point and the left prefix at any time
`q₁` beyond the opening point, the two walls have the same boundary integer near the opening point. -/
theorem corner_frame (hF : IsPocketFrame β α C c Ψ a b) (hL : IsDerivLog c.1 L C)
    (htrβ : IsGeneratingTrace Wβ ⊤ β) (hWβ : Continuous Wβ) (hWβ0 : Wβ 0 = 0)
    (htrα : IsGeneratingTrace Wα ⊤ α) (hWα : Continuous Wα) (hWα0 : Wα 0 = 0) {q₂ t : ℝ≥0}
    (hq₂ : openTime a < q₂) (hq₂t : q₂ < t) (hαt : α t ∉ range β) (hαtC : α t ∈ closure C) {sa q₁ : ℝ≥0}
    (hsa : land c 0 = β sa) (hq₁ : sa < q₁) :
    ∃ n : ℤ, ∃ ε > 0, (∀ ξ : ℝ, -ε < ξ → ξ < 0 → WallInt c L Wβ q₁ ξ n) ∧
      (∀ ξ : ℝ, 0 < ξ → ξ < ε → WallInt c L Wα q₂ ξ n ∧ ∃ s < q₂, land c ξ = α s) := by
  set Γ := Restart.prefixSet β q₁ α q₂ with hΓ
  have hΓc : IsCompact Γ := Restart.isCompact_prefixSet hF.hβ.1.continuousOn hF.hα.1.continuousOn
  have hKΓ : IsHPHull (fillH Γ) := Restart.isHPHull_fillH_prefixSet hF.hβ.1.continuousOn hF.hα.1.continuousOn
    (by rw [hF.hβ.2.2.1]; simp) (by rw [hF.hα.2.2.1]; simp)
  set gK := ConformalImage.mapOut (fillH Γ) with hgKdef
  have hgK : IsMapOut (fillH Γ) gK := ConformalImage.isMapOut_mapOut hKΓ
  obtain ⟨LK, hLK⟩ := Restart.exists_isCanonicalDerivLog hKΓ hgK
  have hCΓ : C ⊆ H \ fillH Γ := subset_H_diff_fillH_prefixSet hF hq₂t hαt hαtC q₁
  have hdomΓ : (c.dom : Set ℂ) ⊆ H \ fillH Γ := hF.hdom ▸ hCΓ
  have hCβ := subset_H_diff_fwdHull_left hF htrβ
  have hCα := subset_H_diff_fwdHull_right hF htrα
  have hx₀α : land c 0 = α (openTime a) := land_zero hF
  obtain ⟨ρβ, hρβ, hballβ⟩ := Lemma71N.exists_ball_tail hF.hβ hq₁
  obtain ⟨ρα, hρα, hballα⟩ := Lemma71N.exists_ball_tail hF.hα hq₂
  set ρ := min (min ρβ ρα) 1 with hρdef
  have hρ : 0 < ρ := lt_min (lt_min hρβ hρα) one_pos
  have h0 : (0 : ℂ) ∈ Hbar := mem_Hbar_of_im_eq_zero (by simp)
  obtain ⟨δ, hδ, hδl⟩ := Metric.continuousWithinAt_iff.1 (continuousOn_land hF 0 h0) ρ hρ
  have hreal : ∀ ξ : ℝ, ((ξ : ℝ) : ℂ) ∈ Hbar := fun ξ => mem_Hbar_of_im_eq_zero (by simp)
  have hnear : ∀ ξ : ℝ, |ξ| < δ → dist (land c ξ) (land c 0) < ρ := fun ξ hξ =>
    hδl (hreal ξ) (by rw [dist_zero_right, Complex.norm_real, Real.norm_eq_abs]; exact hξ)
  -- landing data on both sides of the corner
  have hlandβ : ∀ ξ : ℝ, |ξ| < δ → ξ < 0 → ∃ s, s < q₁ ∧ β s ∉ range α ∧ land c ξ = β s := by
    intro ξ hξδ hξ
    obtain ⟨s, -, hsα, hs⟩ := land_ofReal_neg hF hξ
    refine ⟨s, ?_, hsα, hs⟩
    by_contra hlt
    refine hballβ s (not_lt.1 hlt) ?_
    rw [← hs, ← hsa, mem_ball]
    exact (hnear ξ hξδ).trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hlandα : ∀ ξ : ℝ, |ξ| < δ → 0 < ξ → ∃ s, s < q₂ ∧ α s ∉ range β ∧ land c ξ = α s := by
    intro ξ hξδ hξ
    obtain ⟨s, -, hsβ, hs⟩ := land_ofReal_pos hF hξ
    refine ⟨s, ?_, hsβ, hs⟩
    by_contra hlt
    refine hballα s (not_lt.1 hlt) ?_
    rw [← hs, ← hx₀α, mem_ball]
    exact (hnear ξ hξδ).trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hΓβ : Γ ⊆ β '' Icc 0 q₁ ∪ range α := by
    rintro z (h | ⟨u, -, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨u, rfl⟩
  have hΓα : Γ ⊆ α '' Icc 0 q₂ ∪ range β := by
    rintro z (⟨u, -, rfl⟩ | h)
    · exact Or.inr ⟨u, rfl⟩
    · exact Or.inl h
  have hdataβ : ∀ ξ : ℝ, |ξ| < δ → ξ < 0 →
      (∃ w : ℂ, w.im = 0 ∧ Tendsto (fun y => gK (c.2.1 y)) (𝓝[H] (ξ : ℂ)) (𝓝 w)) ∧
      Tendsto (fun y => (LK (c.2.1 y)).im - (logDerivFwd (fun r : ℝ => Wβ r.toNNReal) q₁ (c.2.1 y)).im)
        (𝓝[H] (ξ : ℂ)) (𝓝 0) := by
    intro ξ hξδ hξ
    obtain ⟨s, hsq, hsα, hs⟩ := hlandβ ξ hξδ hξ
    have hl := tendsto_land hF (hreal ξ)
    rw [hs] at hl
    exact union_wall_data hΓc hKΓ hgK hLK hF.hc hdomΓ hF.hβ hF.hα htrβ hWβ hWβ0 subset_union_left hΓβ
      (hF.hdom ▸ hCβ q₁) (hreal ξ) hsq hsα hl
  have hdataα : ∀ ξ : ℝ, |ξ| < δ → 0 < ξ →
      (∃ w : ℂ, w.im = 0 ∧ Tendsto (fun y => gK (c.2.1 y)) (𝓝[H] (ξ : ℂ)) (𝓝 w)) ∧
      Tendsto (fun y => (LK (c.2.1 y)).im - (logDerivFwd (fun r : ℝ => Wα r.toNNReal) q₂ (c.2.1 y)).im)
        (𝓝[H] (ξ : ℂ)) (𝓝 0) := by
    intro ξ hξδ hξ
    obtain ⟨s, hsq, hsβ, hs⟩ := hlandα ξ hξδ hξ
    have hl := tendsto_land hF (hreal ξ)
    rw [hs] at hl
    exact union_wall_data hΓc hKΓ hgK hLK hF.hc hdomΓ hF.hα hF.hβ htrα hWα hWα0 subset_union_right hΓα
      (hF.hdom ▸ hCα q₂) (hreal ξ) hsq hsβ hl
  -- the bound near the corner
  obtain ⟨M₀, hM₀⟩ := hgK.exists_norm_le hKΓ
  have hM : ∀ y ∈ ball (0 : ℂ) δ ∩ H, ‖gK (c.2.1 y)‖ ≤ ‖land c 0‖ + 1 + M₀ := by
    rintro y ⟨hyb, hy⟩
    have hly : land c y = c.2.1 y := extendFrom_extends hF.hc.1.continuousOn y hy
    have hd := hδl (H_subset_Hbar hy) hyb
    rw [hly] at hd
    have hρ1 : ρ ≤ 1 := min_le_right _ _
    have h1 : ‖c.2.1 y‖ ≤ ‖land c 0‖ + 1 := by
      have := norm_le_norm_add_norm_sub' (c.2.1 y) (land c 0)
      rw [← dist_eq_norm] at this
      linarith
    have h2 := hM₀ _ (hdomΓ (hF.hc.inv_mem_dom hy))
    linarith
  have hlim : ∀ z ∈ ball (0 : ℂ) δ, z.im = 0 → z ≠ 0 → ∃ v : ℂ, v.im = 0 ∧
      Tendsto (fun y => gK (c.2.1 y)) (𝓝[H] z) (𝓝 v) := by
    intro z hz hz0 hzne
    have hzx : z = ((z.re : ℝ) : ℂ) := eq_ofReal_re_of_im_eq_zero hz0
    have hzδ : |z.re| < δ := by
      rw [hzx, mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs] at hz; exact hz
    have hre : z.re ≠ 0 := fun h => hzne (by rw [hzx, h, Complex.ofReal_zero])
    rw [hzx]
    rcases lt_or_gt_of_ne hre with hneg | hpos
    · exact (hdataβ z.re hzδ hneg).1
    · exact (hdataα z.re hzδ hpos).1
  obtain ⟨n, ε, hε, hεδ, hcorner⟩ := exists_int_corner hF.hc hF.hdom hL hKΓ.2.2.1 hCΓ hgK.1.1 hgK.1.2.injOn
    hgK.1.2.mapsTo hLK.1 hδ hM hlim
  have hball : ∀ ξ : ℝ, |ξ| < ε → ((ξ : ℝ) : ℂ) ∈ ball (0 : ℂ) ε := fun ξ hξ => by
    rw [mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs]; exact hξ
  have hcomb : ∀ (W : ℝ≥0 → ℝ) (q : ℝ≥0) (ξ : ℝ), |ξ| < ε →
      Tendsto (fun y => (LK (c.2.1 y)).im - (logDerivFwd (fun r : ℝ => W r.toNNReal) q (c.2.1 y)).im)
        (𝓝[H] (ξ : ℂ)) (𝓝 0) → WallInt c L W q ξ n := by
    intro W q ξ hξ hd
    have h := (hcorner _ (hball ξ hξ) (by simp)).sub hd
    rw [sub_zero] at h
    refine h.congr fun y => ?_
    simp only [Complex.sub_im]; ring
  refine ⟨n, ε, hε, fun ξ hξl hξ => ?_, fun ξ hξ hξr => ?_⟩
  · have hξε : |ξ| < ε := abs_lt.2 ⟨hξl, hξ.trans hε⟩
    exact hcomb Wβ q₁ ξ hξε (hdataβ ξ (hξε.trans_le hεδ) hξ).2
  · have hξε : |ξ| < ε := abs_lt.2 ⟨by linarith, hξr⟩
    obtain ⟨s, hsq, -, hs⟩ := hlandα ξ (hξε.trans_le hεδ) hξ
    exact ⟨hcomb Wα q₂ ξ hξε (hdataα ξ (hξε.trans_le hεδ) hξ).2, s, hsq, hs⟩

end Corner

/-! ### The inherited branch -/

section Branch

variable {β α : ℝ≥0 → ℂ} {C : Set ℂ} {c : Chart} {Ψ : ℂ → ℂ} {a b : ℝ} {L : ℂ → ℂ}

open PocketFrame

theorem continuous_of_isGeneratingTrace_top {W : ℝ≥0 → ℝ} {η : ℝ≥0 → ℂ} (htr : IsGeneratingTrace W ⊤ η) :
    Continuous W := by
  have h := SideHeight.continuousOn_of_isGeneratingTrace htr
  simp only [ENNReal.coe_lt_top, Set.ofPred_true] at h
  exact continuousOn_univ.1 h

/-- The pocket-branch expression from the wall integer (`lift = Im L` on the pocket). -/
theorem tendsto_branch_of_wallInt (hc : c.IsConformal) (hdom : (c.dom : Set ℂ) = C)
    (hlift : ∀ z ∈ C, c.2.2 z = (L z).im) {W : ℝ≥0 → ℝ} {q : ℝ≥0} {ξ : ℝ} {n : ℤ} (h : WallInt c L W q ξ n) :
    Tendsto (fun y => c.2.2 (c.2.1 y) + 2 * π * n - (logDerivFwd (fun r : ℝ => W r.toNNReal) q (c.2.1 y)).im)
      (𝓝[H] (ξ : ℂ)) (𝓝 0) := by
  have h' := h.const_sub (2 * π * n)
  rw [sub_self] at h'
  refine h'.congr' (eventually_nhdsWithin_of_forall fun y hy => ?_)
  have hyC : c.2.1 y ∈ C := by rw [← hdom]; exact hc.inv_mem_dom hy
  dsimp only
  rw [hlift _ hyC, Complex.sub_im]
  ring

/-- **The deterministic normalization lemma in the chart** (supplement §2.3 (2)): on a pocket frame whose chart lift
is the imaginary part of a logarithm `L` of the chart derivative, there is one integer `n` such that the shifted lift
`ℓ + 2πn` has the boundary value of every own prefix's canonical derivative argument on both walls. -/
theorem exists_isPocketBranch (hF : IsPocketFrame β α C c Ψ a b) (hL : IsDerivLog c.1 L C)
    (hlift : ∀ z ∈ C, c.2.2 z = (L z).im) : ∃ n : ℤ, IsPocketBranch β α c n := by
  by_cases hex : ∃ Wβ Wα : ℝ≥0 → ℝ, IsGeneratingTrace Wβ ⊤ β ∧ IsGeneratingTrace Wα ⊤ α
  swap
  · exact ⟨0, fun Wβ Wα h₁ h₂ => absurd ⟨Wβ, Wα, h₁, h₂⟩ hex⟩
  obtain ⟨Wβ, Wα, htrβ, htrα⟩ := hex
  have hWβ := continuous_of_isGeneratingTrace_top htrβ
  have hWα := continuous_of_isGeneratingTrace_top htrα
  have hWβ0 : Wβ 0 = 0 := SideHeight.w_zero_of_isGeneratingTrace htrβ (by simp)
  have hWα0 : Wα 0 = 0 := SideHeight.w_zero_of_isGeneratingTrace htrα (by simp)
  obtain ⟨q₂, t, hq₂, hq₂t, hαt, hαtC⟩ := exists_gap hF
  obtain ⟨sa, hsa⟩ := exists_land_zero_eq hF
  obtain ⟨n, ε₀, hε₀, -, hα₀⟩ := corner_frame hF hL htrβ hWβ hWβ0 htrα hWα hWα0 hq₂ hq₂t hαt hαtC hsa
    (lt_add_one sa)
  have hCβ := subset_H_diff_fwdHull_left hF htrβ
  have hCα := subset_H_diff_fwdHull_right hF htrα
  have hCβf := dom_subset_H_diff_fillH htrβ hF.hdom hCβ
  have hCαf := dom_subset_H_diff_fillH htrα hF.hdom hCα
  have hreal : ∀ ξ : ℝ, ((ξ : ℝ) : ℂ) ∈ Hbar := fun ξ => mem_Hbar_of_im_eq_zero (by simp)
  have hℓ : ∀ w : ℝ, Tendsto c.2.1 (𝓝[H] (w : ℂ)) (𝓝 (land c w)) := fun w => tendsto_land hF (hreal w)
  have hℓc := continuous_land_ofReal hF
  have hℓi : InjOn (fun t : ℝ => land c t) univ := fun x _ y _ h =>
    Complex.ofReal_injective (injOn_land hF (hreal x) (hreal y) h)
  have hSβ : ∀ w ∈ Iio (0 : ℝ), ∃ s : ℝ≥0, land c w = β s := fun w hw => by
    obtain ⟨s, -, -, hs⟩ := land_ofReal_neg hF hw; exact ⟨s, hs⟩
  have hSα : ∀ w ∈ Ioi (0 : ℝ), ∃ s : ℝ≥0, land c w = α s := fun w hw => by
    obtain ⟨s, -, -, hs⟩ := land_ofReal_pos hF hw; exact ⟨s, hs⟩
  have hl0 : land c ((0 : ℝ) : ℂ) = land c 0 := by rw [Complex.ofReal_zero]
  refine ⟨n, fun Wβ' Wα' htrβ' htrα' ξ s q hsq => ⟨fun hξ hland => ?_, fun hξ hland => ?_⟩⟩
  · -- the left wall
    rw [SideHeight.logDerivFwd_eq_of_isGeneratingTrace htrβ' htrβ (WithTop.coe_lt_top q)]
    have := nhdsWithin_H_ofReal_neBot ξ
    have hξs : land c ξ = β s := tendsto_nhds_unique (hℓ ξ) hland
    set q' := max q (sa + 1) with hq'
    have hqq' : q ≤ q' := le_max_left _ _
    have hsaq' : sa < q' := (lt_add_one sa).trans_le (le_max_right _ _)
    obtain ⟨n', ε', hε', hβ', hα'⟩ := corner_frame hF hL htrβ hWβ hWβ0 htrα hWα hWα0 hq₂ hq₂t hαt hαtC hsa hsaq'
    -- the corner integer is `n`
    have hnn' : n' = n := by
      set ξ₀ := min ε₀ ε' / 2 with hξ₀
      have hξ₀0 : 0 < ξ₀ := by positivity
      have h1 : ξ₀ < ε₀ := by rw [hξ₀]; linarith [min_le_left ε₀ ε']
      have h2 : ξ₀ < ε' := by rw [hξ₀]; linarith [min_le_right ε₀ ε']
      exact WallInt.unique (hα' ξ₀ hξ₀0 h2).1 (hα₀ ξ₀ hξ₀0 h1).1
    -- the arc from `ξ` to the corner
    set ξ' := max ξ (-ε' / 2) with hξ'
    have hξξ' : ξ ≤ ξ' := le_max_left _ _
    have hξ'0 : ξ' < 0 := max_lt hξ (by linarith)
    have hξ'ε : -ε' < ξ' := lt_of_lt_of_le (by linarith) (le_max_right _ _)
    have harc := arc_times_lt hF.hβ (ℓ := fun t : ℝ => land c t) hξ.le hℓc.continuousOn (hℓi.mono (subset_univ _))
      (fun w hw => by
        rcases eq_or_lt_of_le hw.2 with rfl | hlt
        · exact ⟨sa, by rw [hl0, hsa]⟩
        · obtain ⟨s', hs'⟩ := hSβ w hlt; exact ⟨s', hs'.symm⟩) hξs (by simp only [hl0, hsa]) (hsq.trans_le hqq')
      hsaq'
    have hI : ∀ w ∈ Icc ξ ξ', ∃ m : ℤ, ∃ ε > 0, ∀ y ∈ Icc ξ ξ', |y - w| < ε → WallInt c L Wβ q' y m := by
      intro w hw
      obtain ⟨s', hs'q, hs'⟩ := harc w ⟨hw.1, hw.2.trans hξ'0.le⟩
      obtain ⟨m, ε, hε, h⟩ := wall_local htrβ hWβ hWβ0 hF.hβ hF.hc hF.hdom hL hCβ hℓ hℓc isOpen_Iio hSβ
        (lt_of_le_of_lt hw.2 hξ'0) hs'q hs'
      exact ⟨m, ε, hε, fun y _ hy => h y hy⟩
    have hend : WallInt c L Wβ q' ξ n :=
      eq_of_isPreconnected_of_local (P := fun w m => WallInt c L Wβ q' w m) isPreconnected_Icc
        (fun w _ m m' => WallInt.unique) hI ⟨hξξ', le_rfl⟩
        ⟨le_rfl, hξξ'⟩ (hnn' ▸ hβ' ξ' hξ'ε hξ'0)
    exact tendsto_branch_of_wallInt hF.hc hF.hdom hlift
      ((WallInt.of_le htrβ hWβ hWβ0 hF.hβ hF.hc hCβf hsq hqq' hland).1 hend)
  · -- the right wall
    rw [SideHeight.logDerivFwd_eq_of_isGeneratingTrace htrα' htrα (WithTop.coe_lt_top q)]
    have := nhdsWithin_H_ofReal_neBot ξ
    have hξs : land c ξ = α s := tendsto_nhds_unique (hℓ ξ) hland
    set q'' := max q q₂ with hq''
    have hqq'' : q ≤ q'' := le_max_left _ _
    have hq₂q'' : q₂ ≤ q'' := le_max_right _ _
    set ξ' := min ξ (ε₀ / 2) with hξ'
    have hξ'ξ : ξ' ≤ ξ := min_le_left _ _
    have hξ'0 : 0 < ξ' := lt_min hξ (by positivity)
    have hξ'ε : ξ' < ε₀ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
    obtain ⟨hint', s', hs'q, hs'⟩ := hα₀ ξ' hξ'0 hξ'ε
    have hl' : Tendsto c.2.1 (𝓝[H] (ξ' : ℂ)) (𝓝 (α s')) := hs' ▸ hℓ ξ'
    have hint'' : WallInt c L Wα q'' ξ' n := (WallInt.of_le htrα hWα hWα0 hF.hα hF.hc hCαf hs'q hq₂q'' hl').2 hint'
    have harc := arc_times_lt hF.hα (ℓ := fun t : ℝ => land c t) hξ.le hℓc.continuousOn (hℓi.mono (subset_univ _))
      (fun w hw => by
        rcases eq_or_lt_of_le hw.1 with rfl | hlt
        · exact ⟨openTime a, by rw [hl0, land_zero hF]⟩
        · obtain ⟨s'', hs''⟩ := hSα w hlt; exact ⟨s'', hs''.symm⟩)
      (by simp only [hl0, land_zero hF]) hξs (hq₂.trans_le hq₂q'') (hsq.trans_le hqq'')
    have hI : ∀ w ∈ Icc ξ' ξ, ∃ m : ℤ, ∃ ε > 0, ∀ y ∈ Icc ξ' ξ, |y - w| < ε → WallInt c L Wα q'' y m := by
      intro w hw
      obtain ⟨s'', hs''q, hs''⟩ := harc w ⟨hξ'0.le.trans hw.1, hw.2⟩
      obtain ⟨m, ε, hε, h⟩ := wall_local htrα hWα hWα0 hF.hα hF.hc hF.hdom hL hCα hℓ hℓc isOpen_Ioi hSα
        (lt_of_lt_of_le hξ'0 hw.1) hs''q hs''
      exact ⟨m, ε, hε, fun y _ hy => h y hy⟩
    have hend : WallInt c L Wα q'' ξ n :=
      eq_of_isPreconnected_of_local (P := fun w m => WallInt c L Wα q'' w m) isPreconnected_Icc
        (fun w _ m m' => WallInt.unique) hI ⟨le_rfl, hξ'ξ⟩
        ⟨hξ'ξ, le_rfl⟩ hint''
    exact tendsto_branch_of_wallInt hF.hc hF.hdom hlift
      ((WallInt.of_le htrα hWα hWα0 hF.hα hF.hc hCαf hsq hqq'' hland).1 hend)

end Branch

end InteractingSLE.Sec7.Lemma71O
