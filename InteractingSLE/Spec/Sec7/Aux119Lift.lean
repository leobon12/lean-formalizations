/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma71OBranch

/-!
# Aux. lemma 119: the common lift of a two-arc pocket chart, without a global order of the walls

Packet PROVE-STRIPSYS22. Specification §7.4, the proof of Aux. lemma 119 (`source/spec/p385-432.md` L14–L33,
pp. 385–387), and its restatement in the supplement, §2.3 "Deterministic normalization lemma"
(`source/spec/p433-480.md` L472–L520):

> Choose its derivative logarithm to have imaginary part zero on this one connected interval. In particular that
> single choice is zero on both sides of zero. […] The two subsequent transitions in (PW13.3)–(PW13.4) also have
> argument exactly zero there. Hence the own height `λ − θ_Lχ` on a right side of the left path, and `−λ − θ_Rχ` on a
> left side of the right path, become exactly the two heights in (PW13.1) in the final chart. […] Two analytic
> logarithms differ by `2πin`, so agreement on that collar fixes the difference to zero.  (Aux. lemma 119)

PROVE-LEMMA71O proved this normalization (`Lemma71O.exists_isPocketBranch`) for Lemma 7.1's pocket frame, whose two
walls are globally ordered. Aux. lemma 119 is applied to the change pocket of Aux. lemma 130, whose walls are only in
increasing contact order and may cross after the pocket. This file isolates the facts the argument really uses in a
frame without any global order (`IsTwoArcFrame`):

* the walls `β` (left) and `α` (right) are simple proper curves and the pocket `C` misses both;
* the chart inverse lands continuously on `ℍ̄`, injectively along `ℝ`, at the opening contact `x₀ = β(s_a) = α(t_a)`
  at `0`, on the left wall off the right wall at negative points and on the right wall off the left wall at positive
  points ("The left incoming arc maps to `ℝ₋` and the right one to `ℝ₊`");
* the pocket lies in the unbounded domain `D_p` of `β([0, q₁]) ∪ α([0, q₂])` for one pair `q₁ > s_a`, `q₂ > t_a`
  ("Let `D_p` be the unbounded component after these two prefixes are removed and filled. Then `C ⊂ D_p`").

**Route.** The source normalizes at the closing contact `y₀` through the hydrodynamic map `g_p` of `D_p`, the Möbius
map `M_p` of (PW13.3) and the reflected transition `r_p`; for `y₀ = ∞` it uses the positive affine map instead, at the
opening contact. Following PROVE-LEMMA71O we use the opening-contact variant in every case (the source: "The case
`x₀` is the original flow seed requires no modification"): the transition of the union map `g_p` across the real
interval around the image of `x₀` reflects with positive derivative and a removable singularity at the corner
(`Lemma71O.exists_int_corner`), which fixes one integer for both sides at once; along each selected arc the integer is
locally constant (`Lemma71O.wall_local`: the transition to the wall's own Loewner chart reflects with positive
derivative) and does not depend on the own stopping time (Aux. lemma 57, `Lemma71O.WallInt.of_le`). The Möbius
transition `M_p` is not needed.

## Main results

* `IsTwoArcFrame` and its API (`tendsto_land`, `continuousOn_land`, `subset_H_diff_fwdHull_left/right`);
* **`IsTwoArcFrame.corner`**: one integer on both sides of the opening corner, for the corner prefixes;
* **`IsTwoArcFrame.exists_isPocketBranch`**: the deterministic normalization (2): one integer `n` such that the
  shifted lift `Im L + 2πn` has the boundary value of every own prefix's canonical derivative argument on both walls
  (`Lemma71N.IsPocketBranch`), and `IsTwoArcFrame.existsUnique_isPocketBranch` (the integer is unique).

Deterministic.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec7.Aux119Lift

open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull logDerivFwd)
open Lemma71O (land WallInt)
open Lemma71N (IsPocketBranch)

/-- **A two-arc pocket frame without a global order of the walls.** Walls `β` (left) and `α` (right), simple proper
curves; a pocket `C` missing both; a conformal chart `c` of `C`; the chart inverse lands continuously on `ℍ̄`
(`land c`), injectively along `ℝ`, at the opening contact `β s_a = α t_a` at `0`, on the left wall off the right wall
at negative points and on the right wall off the left wall at positive points; the pocket lies in the unbounded domain
of the corner prefixes `β([0, q₁]) ∪ α([0, q₂])`, `q₁ > s_a`, `q₂ > t_a`. -/
structure IsTwoArcFrame (β α : ℝ≥0 → ℂ) (C : Set ℂ) (c : Chart) (sa ta q₁ q₂ : ℝ≥0) : Prop where
  left : Lemma71I.IsSimpleProper β
  right : Lemma71I.IsSimpleProper α
  conf : c.IsConformal
  dom : (c.dom : Set ℂ) = C
  disj_left : Disjoint C (range β)
  disj_right : Disjoint C (range α)
  tendsto : ∀ q ∈ Hbar, ∃ p, Tendsto c.2.1 (𝓝[H] q) (𝓝 p)
  inj : Function.Injective fun t : ℝ => land c t
  zero_left : land c 0 = β sa
  zero_right : land c 0 = α ta
  neg : ∀ ξ : ℝ, ξ < 0 → ∃ s, β s ∉ range α ∧ land c ξ = β s
  pos : ∀ ξ : ℝ, 0 < ξ → ∃ s, α s ∉ range β ∧ land c ξ = α s
  lt_left : sa < q₁
  lt_right : ta < q₂
  corner : C ⊆ H \ fillH (Restart.prefixSet β q₁ α q₂)

/-- A simple proper curve's Loewner hulls are contained in its range, so a set missing the range misses every hull. -/
theorem subset_H_diff_fwdHull_of_disjoint {η : ℝ≥0 → ℂ} {W : ℝ≥0 → ℝ} {C : Set ℂ}
    (hη : Lemma71I.IsSimpleProper η) (htr : IsGeneratingTrace W ⊤ η) (hCH : C ⊆ H) (hd : Disjoint C (range η))
    (q : ℝ≥0) : C ⊆ H \ fwdHull (fun r : ℝ => W r.toNNReal) q := by
  have hL : IsLoewnerTrace (fun r : ℝ => W r.toNNReal) (Lemma71I.realPath η) :=
    isLoewnerTrace_of_isGeneratingTrace htr
  intro z hz
  refine ⟨hCH hz, fun hK => Set.disjoint_left.1 hd hz ?_⟩
  have := WangWu.fwdHull_subset_arcRange hL hη.isProperArc q.2 hK
  rwa [Lemma71I.arcRange_realPath] at this

namespace IsTwoArcFrame

variable {β α : ℝ≥0 → ℂ} {C : Set ℂ} {c : Chart} {sa ta q₁ q₂ : ℝ≥0}

theorem subset_H (hF : IsTwoArcFrame β α C c sa ta q₁ q₂) : C ⊆ H := by
  rw [← hF.dom]; exact hF.conf.dom_subset

theorem tendsto_land (hF : IsTwoArcFrame β α C c sa ta q₁ q₂) {q : ℂ} (hq : q ∈ Hbar) :
    Tendsto c.2.1 (𝓝[H] q) (𝓝 (land c q)) := by
  obtain ⟨p, hp⟩ := hF.tendsto q hq
  rwa [land, extendFrom_eq (by rw [closure_H]; exact hq) hp]

theorem continuousOn_land (hF : IsTwoArcFrame β α C c sa ta q₁ q₂) : ContinuousOn (land c) Hbar :=
  continuousOn_extendFrom (by rw [closure_H]) fun q hq => ⟨_, hF.tendsto_land hq⟩

theorem continuous_land_ofReal (hF : IsTwoArcFrame β α C c sa ta q₁ q₂) : Continuous fun t : ℝ => land c t :=
  continuousOn_univ.1 ((continuousOn_land hF).comp Complex.continuous_ofReal.continuousOn
    fun t _ => show (0 : ℝ) ≤ ((t : ℝ) : ℂ).im by simp)

theorem subset_H_diff_fwdHull_left (hF : IsTwoArcFrame β α C c sa ta q₁ q₂) {W : ℝ≥0 → ℝ}
    (htr : IsGeneratingTrace W ⊤ β) (q : ℝ≥0) : C ⊆ H \ fwdHull (fun r : ℝ => W r.toNNReal) q :=
  subset_H_diff_fwdHull_of_disjoint hF.left htr hF.subset_H hF.disj_left q

theorem subset_H_diff_fwdHull_right (hF : IsTwoArcFrame β α C c sa ta q₁ q₂) {W : ℝ≥0 → ℝ}
    (htr : IsGeneratingTrace W ⊤ α) (q : ℝ≥0) : C ⊆ H \ fwdHull (fun r : ℝ => W r.toNNReal) q :=
  subset_H_diff_fwdHull_of_disjoint hF.right htr hF.subset_H hF.disj_right q


/-! ### The corner -/

section Corner

variable {L : ℂ → ℂ} {Wβ Wα : ℝ≥0 → ℝ}

open Lemma71O

/-- **The corner of a two-arc frame** (Aux. lemma 119: "Choose its derivative logarithm to have imaginary part zero
on this one connected interval. In particular that single choice is zero on both sides of zero"): the two walls have
the same boundary integer near the opening point, for the corner prefixes `[0, q₁]` and `[0, q₂]`, and the landing
times there are below the corner times. -/
theorem corner_int (hF : IsTwoArcFrame β α C c sa ta q₁ q₂) (hL : IsDerivLog c.1 L C)
    (htrβ : IsGeneratingTrace Wβ ⊤ β) (hWβ : Continuous Wβ) (hWβ0 : Wβ 0 = 0)
    (htrα : IsGeneratingTrace Wα ⊤ α) (hWα : Continuous Wα) (hWα0 : Wα 0 = 0) :
    ∃ n : ℤ, ∃ ε > 0, (∀ ξ : ℝ, -ε < ξ → ξ < 0 → WallInt c L Wβ q₁ ξ n ∧ ∃ s < q₁, land c ξ = β s) ∧
      (∀ ξ : ℝ, 0 < ξ → ξ < ε → WallInt c L Wα q₂ ξ n ∧ ∃ s < q₂, land c ξ = α s) := by
  set Γ := Restart.prefixSet β q₁ α q₂ with hΓ
  have hΓc : IsCompact Γ := Restart.isCompact_prefixSet hF.left.1.continuousOn hF.right.1.continuousOn
  have hKΓ : IsHPHull (fillH Γ) := Restart.isHPHull_fillH_prefixSet hF.left.1.continuousOn
    hF.right.1.continuousOn (by rw [hF.left.2.2.1]; simp) (by rw [hF.right.2.2.1]; simp)
  set gK := ConformalImage.mapOut (fillH Γ) with hgKdef
  have hgK : IsMapOut (fillH Γ) gK := ConformalImage.isMapOut_mapOut hKΓ
  obtain ⟨LK, hLK⟩ := Restart.exists_isCanonicalDerivLog hKΓ hgK
  have hCΓ : C ⊆ H \ fillH Γ := hF.corner
  have hdomΓ : (c.dom : Set ℂ) ⊆ H \ fillH Γ := hF.dom ▸ hCΓ
  have hCβ := hF.subset_H_diff_fwdHull_left htrβ
  have hCα := hF.subset_H_diff_fwdHull_right htrα
  obtain ⟨ρβ, hρβ, hballβ⟩ := Lemma71N.exists_ball_tail hF.left hF.lt_left
  obtain ⟨ρα, hρα, hballα⟩ := Lemma71N.exists_ball_tail hF.right hF.lt_right
  set ρ := min (min ρβ ρα) 1 with hρdef
  have hρ : 0 < ρ := lt_min (lt_min hρβ hρα) one_pos
  have h0 : (0 : ℂ) ∈ Hbar := mem_Hbar_of_im_eq_zero (by simp)
  obtain ⟨δ, hδ, hδl⟩ := Metric.continuousWithinAt_iff.1 (hF.continuousOn_land 0 h0) ρ hρ
  have hreal : ∀ ξ : ℝ, ((ξ : ℝ) : ℂ) ∈ Hbar := fun ξ => mem_Hbar_of_im_eq_zero (by simp)
  have hnear : ∀ ξ : ℝ, |ξ| < δ → dist (land c ξ) (land c 0) < ρ := fun ξ hξ =>
    hδl (hreal ξ) (by rw [dist_zero_right, Complex.norm_real, Real.norm_eq_abs]; exact hξ)
  -- landing data on both sides of the corner
  have hlandβ : ∀ ξ : ℝ, |ξ| < δ → ξ < 0 → ∃ s, s < q₁ ∧ β s ∉ range α ∧ land c ξ = β s := by
    intro ξ hξδ hξ
    obtain ⟨s, hsα, hs⟩ := hF.neg ξ hξ
    refine ⟨s, ?_, hsα, hs⟩
    by_contra hlt
    refine hballβ s (not_lt.1 hlt) ?_
    rw [← hs, ← hF.zero_left, mem_ball]
    exact (hnear ξ hξδ).trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hlandα : ∀ ξ : ℝ, |ξ| < δ → 0 < ξ → ∃ s, s < q₂ ∧ α s ∉ range β ∧ land c ξ = α s := by
    intro ξ hξδ hξ
    obtain ⟨s, hsβ, hs⟩ := hF.pos ξ hξ
    refine ⟨s, ?_, hsβ, hs⟩
    by_contra hlt
    refine hballα s (not_lt.1 hlt) ?_
    rw [← hs, ← hF.zero_right, mem_ball]
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
    have hl := hF.tendsto_land (hreal ξ)
    rw [hs] at hl
    exact union_wall_data hΓc hKΓ hgK hLK hF.conf hdomΓ hF.left hF.right htrβ hWβ hWβ0 subset_union_left hΓβ
      (hF.dom ▸ hCβ q₁) (hreal ξ) hsq hsα hl
  have hdataα : ∀ ξ : ℝ, |ξ| < δ → 0 < ξ →
      (∃ w : ℂ, w.im = 0 ∧ Tendsto (fun y => gK (c.2.1 y)) (𝓝[H] (ξ : ℂ)) (𝓝 w)) ∧
      Tendsto (fun y => (LK (c.2.1 y)).im - (logDerivFwd (fun r : ℝ => Wα r.toNNReal) q₂ (c.2.1 y)).im)
        (𝓝[H] (ξ : ℂ)) (𝓝 0) := by
    intro ξ hξδ hξ
    obtain ⟨s, hsq, hsβ, hs⟩ := hlandα ξ hξδ hξ
    have hl := hF.tendsto_land (hreal ξ)
    rw [hs] at hl
    exact union_wall_data hΓc hKΓ hgK hLK hF.conf hdomΓ hF.right hF.left htrα hWα hWα0 subset_union_right hΓα
      (hF.dom ▸ hCα q₂) (hreal ξ) hsq hsβ hl
  -- the bound near the corner
  obtain ⟨M₀, hM₀⟩ := hgK.exists_norm_le hKΓ
  have hM : ∀ y ∈ ball (0 : ℂ) δ ∩ H, ‖gK (c.2.1 y)‖ ≤ ‖land c 0‖ + 1 + M₀ := by
    rintro y ⟨hyb, hy⟩
    have hly : land c y = c.2.1 y := extendFrom_extends hF.conf.1.continuousOn y hy
    have hd := hδl (H_subset_Hbar hy) hyb
    rw [hly] at hd
    have hρ1 : ρ ≤ 1 := min_le_right _ _
    have h1 : ‖c.2.1 y‖ ≤ ‖land c 0‖ + 1 := by
      have := norm_le_norm_add_norm_sub' (c.2.1 y) (land c 0)
      rw [← dist_eq_norm] at this
      linarith
    have h2 := hM₀ _ (hdomΓ (hF.conf.inv_mem_dom hy))
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
  obtain ⟨n, ε, hε, hεδ, hcorner⟩ := exists_int_corner hF.conf hF.dom hL hKΓ.2.2.1 hCΓ hgK.1.1
    hgK.1.2.injOn hgK.1.2.mapsTo hLK.1 hδ hM hlim
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
    obtain ⟨s, hsq, -, hs⟩ := hlandβ ξ (hξε.trans_le hεδ) hξ
    exact ⟨hcomb Wβ q₁ ξ hξε (hdataβ ξ (hξε.trans_le hεδ) hξ).2, s, hsq, hs⟩
  · have hξε : |ξ| < ε := abs_lt.2 ⟨by linarith, hξr⟩
    obtain ⟨s, hsq, -, hs⟩ := hlandα ξ (hξε.trans_le hεδ) hξ
    exact ⟨hcomb Wα q₂ ξ hξε (hdataα ξ (hξε.trans_le hεδ) hξ).2, s, hsq, hs⟩

end Corner

/-! ### The inherited branch -/

section Branch

variable {L : ℂ → ℂ}

open Lemma71O

/-- **Aux. lemma 119's common lift: the deterministic normalization (2)** (supplement §2.3; Aux. lemma 119: "The lifts
of `φ′` obtained above agree: they give the same exact lift relative to any one fixed compact left subarc and its fixed
own chart […] This proves the alignment on the whole two-arc boundary, including all finite actual angle jumps"). On a
two-arc frame whose chart lift is the imaginary part of a logarithm `L` of the chart derivative, there is one integer
`n` such that the shifted lift `Im L + 2πn` has the boundary value of every own prefix's canonical derivative argument
on both walls, at every real chart point whose landing time is below the prefix time. -/
theorem exists_isPocketBranch (hF : IsTwoArcFrame β α C c sa ta q₁ q₂) (hL : IsDerivLog c.1 L C)
    (hlift : ∀ z ∈ C, c.2.2 z = (L z).im) : ∃ n : ℤ, IsPocketBranch β α c n := by
  by_cases hex : ∃ Wβ Wα : ℝ≥0 → ℝ, IsGeneratingTrace Wβ ⊤ β ∧ IsGeneratingTrace Wα ⊤ α
  swap
  · exact ⟨0, fun Wβ Wα h₁ h₂ => absurd ⟨Wβ, Wα, h₁, h₂⟩ hex⟩
  obtain ⟨Wβ, Wα, htrβ, htrα⟩ := hex
  have hWβ := continuous_of_isGeneratingTrace_top htrβ
  have hWα := continuous_of_isGeneratingTrace_top htrα
  have hWβ0 : Wβ 0 = 0 := SideHeight.w_zero_of_isGeneratingTrace htrβ (by simp)
  have hWα0 : Wα 0 = 0 := SideHeight.w_zero_of_isGeneratingTrace htrα (by simp)
  obtain ⟨n, ε₀, hε₀, hβ₀, hα₀⟩ := hF.corner_int hL htrβ hWβ hWβ0 htrα hWα hWα0
  have hCβ := hF.subset_H_diff_fwdHull_left htrβ
  have hCα := hF.subset_H_diff_fwdHull_right htrα
  have hCβf := dom_subset_H_diff_fillH htrβ hF.dom hCβ
  have hCαf := dom_subset_H_diff_fillH htrα hF.dom hCα
  have hreal : ∀ ξ : ℝ, ((ξ : ℝ) : ℂ) ∈ Hbar := fun ξ => mem_Hbar_of_im_eq_zero (by simp)
  have hℓ : ∀ w : ℝ, Tendsto c.2.1 (𝓝[H] (w : ℂ)) (𝓝 (land c w)) := fun w => hF.tendsto_land (hreal w)
  have hℓc := hF.continuous_land_ofReal
  have hℓi : InjOn (fun t : ℝ => land c t) univ := fun x _ y _ h => hF.inj h
  have hSβ : ∀ w ∈ Iio (0 : ℝ), ∃ s : ℝ≥0, land c w = β s := fun w hw => by
    obtain ⟨s, -, hs⟩ := hF.neg w hw; exact ⟨s, hs⟩
  have hSα : ∀ w ∈ Ioi (0 : ℝ), ∃ s : ℝ≥0, land c w = α s := fun w hw => by
    obtain ⟨s, -, hs⟩ := hF.pos w hw; exact ⟨s, hs⟩
  have hl0 : land c ((0 : ℝ) : ℂ) = land c 0 := by rw [Complex.ofReal_zero]
  refine ⟨n, fun Wβ' Wα' htrβ' htrα' ξ s q hsq => ⟨fun hξ hland => ?_, fun hξ hland => ?_⟩⟩
  · -- the left wall
    rw [SideHeight.logDerivFwd_eq_of_isGeneratingTrace htrβ' htrβ (WithTop.coe_lt_top q)]
    have := nhdsWithin_H_ofReal_neBot ξ
    have hξs : land c ξ = β s := tendsto_nhds_unique (hℓ ξ) hland
    set q' := max q q₁ with hq'
    have hqq' : q ≤ q' := le_max_left _ _
    have hq₁q' : q₁ ≤ q' := le_max_right _ _
    have hsaq' : sa < q' := hF.lt_left.trans_le hq₁q'
    -- a point of the left side of the corner, at the corner time and then at `q'`
    set ξ' := max ξ (-ε₀ / 2) with hξ'
    have hξξ' : ξ ≤ ξ' := le_max_left _ _
    have hξ'0 : ξ' < 0 := max_lt hξ (by linarith)
    have hξ'ε : -ε₀ < ξ' := lt_of_lt_of_le (by linarith) (le_max_right _ _)
    obtain ⟨hint', s', hs'q, hs'⟩ := hβ₀ ξ' hξ'ε hξ'0
    have hl' : Tendsto c.2.1 (𝓝[H] (ξ' : ℂ)) (𝓝 (β s')) := hs' ▸ hℓ ξ'
    have hint'' : WallInt c L Wβ q' ξ' n :=
      (WallInt.of_le htrβ hWβ hWβ0 hF.left hF.conf hCβf hs'q hq₁q' hl').2 hint'
    -- the arc from `ξ` to the corner
    have harc := arc_times_lt hF.left (ℓ := fun t : ℝ => land c t) hξ.le hℓc.continuousOn
      (hℓi.mono (subset_univ _))
      (fun w hw => by
        rcases eq_or_lt_of_le hw.2 with rfl | hlt
        · exact ⟨sa, by rw [hl0, hF.zero_left]⟩
        · obtain ⟨s'', hs''⟩ := hSβ w hlt; exact ⟨s'', hs''.symm⟩) hξs (by simp only [hl0, hF.zero_left])
      (hsq.trans_le hqq') hsaq'
    have hI : ∀ w ∈ Icc ξ ξ', ∃ m : ℤ, ∃ ε > 0, ∀ y ∈ Icc ξ ξ', |y - w| < ε → WallInt c L Wβ q' y m := by
      intro w hw
      obtain ⟨s'', hs''q, hs''⟩ := harc w ⟨hw.1, hw.2.trans hξ'0.le⟩
      obtain ⟨m, ε, hε, h⟩ := wall_local htrβ hWβ hWβ0 hF.left hF.conf hF.dom hL hCβ hℓ hℓc isOpen_Iio hSβ
        (lt_of_le_of_lt hw.2 hξ'0) hs''q hs''
      exact ⟨m, ε, hε, fun y _ hy => h y hy⟩
    have hend : WallInt c L Wβ q' ξ n :=
      eq_of_isPreconnected_of_local (P := fun w m => WallInt c L Wβ q' w m) isPreconnected_Icc
        (fun w _ m m' => WallInt.unique) hI ⟨hξξ', le_rfl⟩ ⟨le_rfl, hξξ'⟩ hint''
    exact tendsto_branch_of_wallInt hF.conf hF.dom hlift
      ((WallInt.of_le htrβ hWβ hWβ0 hF.left hF.conf hCβf hsq hqq' hland).1 hend)
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
    have hint'' : WallInt c L Wα q'' ξ' n :=
      (WallInt.of_le htrα hWα hWα0 hF.right hF.conf hCαf hs'q hq₂q'' hl').2 hint'
    have harc := arc_times_lt hF.right (ℓ := fun t : ℝ => land c t) hξ.le hℓc.continuousOn
      (hℓi.mono (subset_univ _))
      (fun w hw => by
        rcases eq_or_lt_of_le hw.1 with rfl | hlt
        · exact ⟨ta, by rw [hl0, hF.zero_right]⟩
        · obtain ⟨s'', hs''⟩ := hSα w hlt; exact ⟨s'', hs''.symm⟩)
      (by simp only [hl0, hF.zero_right]) hξs (hF.lt_right.trans_le hq₂q'') (hsq.trans_le hqq'')
    have hI : ∀ w ∈ Icc ξ' ξ, ∃ m : ℤ, ∃ ε > 0, ∀ y ∈ Icc ξ' ξ, |y - w| < ε → WallInt c L Wα q'' y m := by
      intro w hw
      obtain ⟨s'', hs''q, hs''⟩ := harc w ⟨hξ'0.le.trans hw.1, hw.2⟩
      obtain ⟨m, ε, hε, h⟩ := wall_local htrα hWα hWα0 hF.right hF.conf hF.dom hL hCα hℓ hℓc isOpen_Ioi hSα
        (lt_of_lt_of_le hξ'0 hw.1) hs''q hs''
      exact ⟨m, ε, hε, fun y _ hy => h y hy⟩
    have hend : WallInt c L Wα q'' ξ n :=
      eq_of_isPreconnected_of_local (P := fun w m => WallInt c L Wα q'' w m) isPreconnected_Icc
        (fun w _ m m' => WallInt.unique) hI ⟨le_rfl, hξ'ξ⟩ ⟨hξ'ξ, le_rfl⟩ hint''
    exact tendsto_branch_of_wallInt hF.conf hF.dom hlift
      ((WallInt.of_le htrα hWα hWα0 hF.right hF.conf hCαf hsq hqq'' hland).1 hend)


/-- **The integer is unique** (supplement §2.3: "The logarithm with this property is unique"; Aux. lemma 119: "Two
analytic logarithms differ by `2πin`, so agreement on that collar fixes the difference to zero"), as soon as both walls
are generated by drivers. -/
theorem isPocketBranch_unique (hF : IsTwoArcFrame β α C c sa ta q₁ q₂) {Wβ Wα : ℝ≥0 → ℝ}
    (htrβ : IsGeneratingTrace Wβ ⊤ β) (htrα : IsGeneratingTrace Wα ⊤ α) {n n' : ℤ}
    (hn : IsPocketBranch β α c n) (hn' : IsPocketBranch β α c n') : n = n' := by
  obtain ⟨s, -, hs⟩ := hF.neg (-1) (by norm_num)
  have hland : Tendsto c.2.1 (𝓝[H] (((-1 : ℝ)) : ℂ)) (𝓝 (β s)) :=
    hs ▸ hF.tendsto_land (mem_Hbar_of_im_eq_zero (by simp))
  have h1 := (hn Wβ Wα htrβ htrα (-1) s (s + 1) (lt_add_one s)).1 (by norm_num) hland
  have h2 := (hn' Wβ Wα htrβ htrα (-1) s (s + 1) (lt_add_one s)).1 (by norm_num) hland
  have := nhdsWithin_H_ofReal_neBot (-1)
  have h3 := h1.sub h2
  rw [sub_zero] at h3
  have h4 : Tendsto (fun _ : ℂ => 2 * π * ((n : ℝ) - n')) (𝓝[H] (((-1 : ℝ)) : ℂ)) (𝓝 0) :=
    h3.congr fun y => by ring
  have h5 := tendsto_nhds_unique tendsto_const_nhds h4
  have hπ : (2 * π : ℝ) ≠ 0 := by positivity
  have h6 : (n : ℝ) - n' = 0 := (mul_eq_zero.1 h5).resolve_left hπ
  exact_mod_cast sub_eq_zero.1 h6

/-- **Existence and uniqueness of the inherited branch** on a two-arc frame with driven walls. -/
theorem existsUnique_isPocketBranch (hF : IsTwoArcFrame β α C c sa ta q₁ q₂) (hL : IsDerivLog c.1 L C)
    (hlift : ∀ z ∈ C, c.2.2 z = (L z).im) {Wβ Wα : ℝ≥0 → ℝ} (htrβ : IsGeneratingTrace Wβ ⊤ β)
    (htrα : IsGeneratingTrace Wα ⊤ α) : ∃! n : ℤ, IsPocketBranch β α c n := by
  obtain ⟨n, hn⟩ := hF.exists_isPocketBranch hL hlift
  exact ⟨n, hn, fun n' hn' => hF.isPocketBranch_unique htrβ htrα hn' hn⟩

end Branch

end IsTwoArcFrame

end InteractingSLE.Sec7.Aux119Lift
