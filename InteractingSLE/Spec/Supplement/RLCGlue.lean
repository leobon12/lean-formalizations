/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.S9BExtend
import InteractingSLE.Frozen.Spec.activeDomain

/-!
# The planar gluing of the stopped reference tangle (supplement §7.8, pp. 502–503), interior case

Packet PROVE-RLC-A, part (d). Source: "Planar gluing of the stopped reference tangle" (`source/spec/p481-528.md`
L527–L533, pp. 502–503): "Suppose the actual retained old prefixes have ordered proper extensions, their distinct
current tips are active and off the other prefix, and their joint chart has the same active seed order `w₂ < w₁`.
Suppose the stopped tangle in that chart admits the completions just supplied by G9–G10 […] Map those completions
back and append them to the old histories. They are proper injective extensions […] The Jordan separation theorem now
puts the entire second completed curve on the closed left side of the first".

This file proves the gluing pathwise (deterministically) in the **interior case**, where the chart completions lie in
`ℍ` after their seeds (G10's interiorized completions of chart prefixes that do not touch the real line after time
`0`): `hasOrderedProperCompletions_glue`. The order check is done without local orientation arguments:

1. the first glued curve `α″` (the physical prefix `η₁([0, a])`, then the inverse chart `ψ` of the chart completion)
   is a proper completion whose part after `u` lies in the joint domain `D`, so the transfer lemma of PROVE-SUPP9-B
   (`Supp9B.exists_isProperCompletion_subset_closedLeftSide`) puts the old second prefix `η₂([0, r])` in the closed
   left side of `α″`; in particular the second tip `η₂(r) = ψ(0)` is in the open left side;
2. the left side of the chart completion `γ₁`, intersected with `ℍ`, is preconnected
   (`isPreconnected_leftSide_inter_H`, for a proper curve that stays in `ℍ` after its seed); `ψ` maps it into the
   complement of `α″`, hence into one side of `α″`; near the chart seed `0` of the second completion it is the left
   side, by continuity of `ψ` at `0`;
3. every point of the second glued curve is an old point (step 1), or the `ψ`-image of a chart point on the closed left
   side of `γ₁` in `ℍ`: on the open left side (step 2) or on `γ₁` itself, whose image is on `α″`.

## Main results

* `isPreconnected_leftSide_inter_H`: Jordan-side connectivity in `ℍ`.
* `isProperCompletion_junction_of_prefix`: a continuous injective prefix followed by a proper tail.
* `glue_side`: one glued curve and its representation through the chart.
* `hasOrderedProperCompletions_glue`: **the planar gluing** (interior case).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped NNReal

open QuantumZipper (H Hbar)

namespace InteractingSLE

namespace RLC

open Supp9B

/-! ### The left side of a curve that stays in the open half-plane -/

section Sides

variable {γ : ℝ≥0 → ℂ}

/-- A real point to the right of the seed and off the curve is on the right side. -/
theorem ofReal_mem_rightSide (hγ : ∀ t, 0 ≤ (γ t).im) (h0 : (γ 0).im = 0) {x : ℝ}
    (hx : (γ 0).re < x) (hxγ : (x : ℂ) ∉ seedRayClosure γ) : (x : ℂ) ∈ rightSide γ := by
  have hcl : (x : ℂ) ∈ closure (lowerRight (γ 0).re) := by
    have ht : Tendsto (fun s : ℝ => (x : ℂ) - (s : ℂ) * I) (𝓝[>] 0) (𝓝 (x : ℂ)) := by
      have : Continuous (fun s : ℝ => (x : ℂ) - (s : ℂ) * I) := by fun_prop
      simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
    refine mem_closure_of_tendsto ht ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    constructor <;> simp [hx, show (0 : ℝ) < s from hs]
  have hpc : IsPreconnected (insert (x : ℂ) (lowerRight (γ 0).re)) :=
    (convex_lowerRight _).isPreconnected.subset_closure (subset_insert _ _)
      (insert_subset hcl subset_closure)
  exact hpc.subset_connectedComponentIn (mem_insert_of_mem _ (right_ref_mem_lowerRight h0))
    (insert_subset hxγ (lowerRight_subset_compl hγ)) (mem_insert _ _)

/-- A preconnected set off the closed curve which meets the left side lies in it. -/
theorem subset_leftSide_of_mem {s : Set ℂ} (hs : IsPreconnected s) (hsS : s ⊆ (seedRayClosure γ)ᶜ) {z : ℂ}
    (hz : z ∈ s) (hzL : z ∈ leftSide γ) : s ⊆ leftSide γ := by
  rw [leftSide, connectedComponentIn_eq hzL]
  exact hs.subset_connectedComponentIn hz hsS

/-- A point off the closed curve adherent to the left side is on the left side. -/
theorem mem_leftSide_of_mem_closure (hγ : IsProperCurve γ) {z : ℂ} (hz : z ∈ closure (leftSide γ))
    (hzS : z ∉ seedRayClosure γ) : z ∈ leftSide γ := by
  have hSo : IsOpen (seedRayClosure γ)ᶜ := (isClosed_seedRayClosure hγ).isOpen_compl
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hSo z hzS
  obtain ⟨y, hyL, hyB⟩ := Metric.mem_closure_iff.1 hz ρ hρ
  have hyB' : y ∈ ball z ρ := by rw [mem_ball, dist_comm]; exact hyB
  exact subset_leftSide_of_mem (convex_ball z ρ).isPreconnected hball hyB' hyL (mem_ball_self hρ)

/-- A real point other than the seed is off a curve which stays in `ℍ` after its seed. -/
theorem ofReal_notMem_seedRayClosure (hH : ∀ t, 0 < t → γ t ∈ H) {x : ℝ}
    (hx : x ≠ (γ 0).re) : (x : ℂ) ∉ seedRayClosure γ := by
  rintro (⟨t, ht⟩ | ⟨hre, -⟩)
  · rcases eq_zero_or_pos t with rfl | htp
    · exact hx (by rw [ht]; simp)
    · have h1 : (0 : ℝ) < (γ t).im := hH t htp
      rw [ht] at h1
      simp at h1
  · exact hx (by simpa using hre)

/-- The distance from a real point to the closed curve. -/
def gap (γ : ℝ≥0 → ℂ) (x : ℝ) : ℝ := infDist (x : ℂ) (seedRayClosure γ)

theorem continuous_gap (γ : ℝ≥0 → ℂ) : Continuous (gap γ) :=
  (continuous_infDist_pt _).comp continuous_ofReal

theorem gap_pos (hγ : IsProperCurve γ) (hH : ∀ t, 0 < t → γ t ∈ H) {x : ℝ}
    (hx : x ≠ (γ 0).re) : 0 < gap γ x :=
  ((isClosed_seedRayClosure hγ).notMem_iff_infDist_pos ⟨γ 0, Or.inl ⟨0, rfl⟩⟩).1
    (ofReal_notMem_seedRayClosure hH hx)

/-- The thin region above the real half-line left of the seed, below the gap function. -/
def thinLeft (γ : ℝ≥0 → ℂ) : Set ℂ :=
  (fun p : ℝ × ℝ => (p.1 : ℂ) + ((p.2 * gap γ p.1 : ℝ) : ℂ) * I) '' (Iio (γ 0).re ×ˢ Ioo 0 1)

theorem isPreconnected_thinLeft (γ : ℝ≥0 → ℂ) : IsPreconnected (thinLeft γ) := by
  refine (isPreconnected_Iio.prod isPreconnected_Ioo).image _ (Continuous.continuousOn ?_)
  have hg := continuous_gap γ
  fun_prop

theorem thinLeft_subset (hγ : IsProperCurve γ) (h0 : (γ 0).im = 0) (hH : ∀ t, 0 < t → γ t ∈ H) :
    thinLeft γ ⊆ leftSide γ ∩ H := by
  rintro _ ⟨⟨x, s⟩, ⟨hx, hs⟩, rfl⟩
  have hx' : x ≠ (γ 0).re := ne_of_lt hx
  have hg := gap_pos hγ hH hx'
  have hxL : (x : ℂ) ∈ leftSide γ :=
    ofReal_mem_leftSide hγ.2.2.1 h0 hx (ofReal_notMem_seedRayClosure hH hx')
  have hB : ball (x : ℂ) (gap γ x) ⊆ leftSide γ :=
    subset_leftSide_of_mem (convex_ball _ _).isPreconnected ball_infDist_subset_compl
      (mem_ball_self hg) hxL
  refine ⟨hB ?_, ?_⟩
  · rw [mem_ball, dist_eq]
    simp only [add_sub_cancel_left, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs]
    rw [abs_of_pos hs.1, abs_of_pos hg]
    exact mul_lt_of_lt_one_left hg hs.2
  · show 0 < ((x : ℂ) + ((s * gap γ x : ℝ) : ℂ) * I).im
    simpa using mul_pos hs.1 hg

/-- A point of `ℍ` close to a real point left of the seed is in the thin region. -/
theorem mem_thinLeft_of_near (hγ : IsProperCurve γ) (hH : ∀ t, 0 < t → γ t ∈ H) {x : ℝ}
    (hx : x < (γ 0).re) {z : ℂ} (hzH : z ∈ H)
    (hz : dist z x < min (gap γ x / 2) ((γ 0).re - x)) : z ∈ thinLeft γ := by
  have hg := gap_pos hγ hH (ne_of_lt hx)
  have hre : |z.re - x| ≤ dist z x := by
    rw [dist_eq]
    have := Complex.abs_re_le_norm (z - x)
    simpa using this
  have him : z.im ≤ dist z x := by
    rw [dist_eq]
    have := Complex.abs_im_le_norm (z - x)
    simp only [sub_im, ofReal_im, sub_zero] at this
    exact (le_abs_self _).trans this
  have hlt1 : dist z x < gap γ x / 2 := hz.trans_le (min_le_left _ _)
  have hlt2 : dist z x < (γ 0).re - x := hz.trans_le (min_le_right _ _)
  have hgz : gap γ x / 2 < gap γ z.re := by
    have h1 := infDist_le_infDist_add_dist (x := (x : ℂ)) (y := (z.re : ℂ)) (s := seedRayClosure γ)
    have h2 : dist (x : ℂ) (z.re : ℂ) = |z.re - x| := by
      rw [dist_eq, ← ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
    have h3 : gap γ x ≤ gap γ z.re + |z.re - x| := by unfold gap; rw [← h2]; exact h1
    linarith
  have hgz0 : 0 < gap γ z.re := lt_trans (half_pos hg) hgz
  have hzi : 0 < z.im := hzH
  refine ⟨(z.re, z.im / gap γ z.re), ⟨?_, div_pos hzi hgz0, ?_⟩, ?_⟩
  · show z.re < (γ 0).re
    have := (abs_lt.1 (hre.trans_lt hlt2)).2
    linarith
  · rw [div_lt_one hgz0]
    linarith
  · apply Complex.ext <;> simp [div_mul_cancel₀ _ hgz0.ne']

/-- One half of the connectivity argument: if the thin region lies in `u`, so does every point of `ℍ` on the left
side, for open `u`, `v` covering it without a common point there. -/
theorem leftSide_inter_H_subset_of_thinLeft (hγ : IsProperCurve γ) (h0 : (γ 0).im = 0)
    (hH : ∀ t, 0 < t → γ t ∈ H) {u v : Set ℂ} (hu : IsOpen u) (hv : IsOpen v)
    (hcov : leftSide γ ∩ H ⊆ u ∪ v) (hdis : leftSide γ ∩ H ∩ (u ∩ v) = ∅) (hthin : thinLeft γ ⊆ u) :
    leftSide γ ∩ H ⊆ u := by
  by_contra hne
  obtain ⟨z₀, hz₀, hz₀u⟩ := not_subset.1 hne
  set U := leftSide γ ∩ H ∩ v with hU
  have hUo : IsOpen U := ((isOpen_leftSide hγ).inter (isOpen_lt continuous_const continuous_im)).inter hv
  have hz₀U : z₀ ∈ U := ⟨hz₀, (hcov hz₀).resolve_left hz₀u⟩
  -- `U` is closed in the complement of the closed curve
  have hclosed : ∀ z ∈ closure U, z ∉ seedRayClosure γ → z ∈ U := by
    intro z hzc hzS
    have hzL : z ∈ leftSide γ :=
      mem_leftSide_of_mem_closure hγ (closure_mono (fun y hy => hy.1.1) hzc) hzS
    have hzim : 0 ≤ z.im := by
      have : closure U ⊆ {y : ℂ | 0 ≤ y.im} :=
        closure_minimal (fun y hy => show (0 : ℝ) ≤ y.im from le_of_lt (show (0 : ℝ) < y.im from hy.1.2))
          (isClosed_le continuous_const continuous_im)
      exact this hzc
    rcases hzim.lt_or_eq with hpos | hzero
    · have hzLH : z ∈ leftSide γ ∩ H := ⟨hzL, hpos⟩
      rcases hcov hzLH with hzu | hzv
      · exfalso
        obtain ⟨y, hyu, hyU⟩ := mem_closure_iff.1 hzc u hu hzu
        have : y ∈ leftSide γ ∩ H ∩ (u ∩ v) := ⟨hyU.1, hyu, hyU.2⟩
        rw [hdis] at this
        exact this
      · exact ⟨hzLH, hzv⟩
    · exfalso
      have hzr : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [← hzero])
      have hne : z.re ≠ (γ 0).re := by
        intro h
        exact hzS (Or.inr ⟨h, by rw [← hzero, h0]⟩)
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hg := gap_pos hγ hH hne
        have hmin : 0 < min (gap γ z.re / 2) ((γ 0).re - z.re) := lt_min (half_pos hg) (by linarith)
        obtain ⟨y, hyU, hyB⟩ := Metric.mem_closure_iff.1 hzc _ hmin
        have hyT : y ∈ thinLeft γ := by
          refine mem_thinLeft_of_near hγ hH hlt hyU.1.2 ?_
          rw [dist_comm, ← hzr]; exact hyB
        have : y ∈ leftSide γ ∩ H ∩ (u ∩ v) := ⟨hyU.1, hthin hyT, hyU.2⟩
        rw [hdis] at this
        exact this
      · have hzR : z ∈ rightSide γ := by
          rw [hzr]
          exact ofReal_mem_rightSide hγ.2.2.1 h0 hgt (by rw [← hzr]; exact hzS)
        exact Set.disjoint_left.1 (disjoint_leftSide_rightSide hγ h0) hzL hzR
  -- hence the whole left side lies in `U`
  have hcover : leftSide γ ⊆ U ∪ (closure U)ᶜ := by
    intro z hzL
    by_cases hzc : z ∈ closure U
    · exact Or.inl (hclosed z hzc (connectedComponentIn_subset _ _ hzL))
    · exact Or.inr hzc
  have hdisj : Disjoint U (closure U)ᶜ := Set.disjoint_left.2 fun y hy hyc => hyc (subset_closure hy)
  have hsub : leftSide γ ⊆ U :=
    (isPreconnected_connectedComponentIn).subset_left_of_subset_union hUo isClosed_closure.isOpen_compl hdisj
      hcover ⟨z₀, hz₀.1, hz₀U⟩
  have href := hsub (leftRef_mem_leftSide hγ.2.2.1 h0)
  have : (0 : ℝ) < (γ 0 - 1 - I).im := href.1.2
  simp [h0] at this
  norm_num at this

/-- **Connectivity of the left side in `ℍ`.** For a proper curve from a real seed which stays in `ℍ` after time `0`,
the points of `ℍ` on its open left side form a preconnected set. -/
theorem isPreconnected_leftSide_inter_H (hγ : IsProperCurve γ) (h0 : (γ 0).im = 0)
    (hH : ∀ t, 0 < t → γ t ∈ H) : IsPreconnected (leftSide γ ∩ H) := by
  refine isPreconnected_iff_subset_of_disjoint.2 fun u v hu hv hcov hdis => ?_
  have hT := thinLeft_subset hγ h0 hH
  have hTdis : thinLeft γ ∩ (u ∩ v) = ∅ :=
    Set.eq_empty_of_subset_empty fun y hy => hdis ▸ ⟨hT hy.1, hy.2⟩
  rcases isPreconnected_iff_subset_of_disjoint.1 (isPreconnected_thinLeft γ) u v hu hv (hT.trans hcov) hTdis
    with hTu | hTv
  · exact Or.inl (leftSide_inter_H_subset_of_thinLeft hγ h0 hH hu hv hcov hdis hTu)
  · refine Or.inr (leftSide_inter_H_subset_of_thinLeft hγ h0 hH hv hu (fun z hz => (hcov hz).symm) ?_ hTv)
    rw [inter_comm v u]; exact hdis

end Sides

/-! ### Gluing a prefix to a tail -/

section Glue

/-- **A continuous injective prefix followed by a proper tail** is a proper completion of the prefix. -/
theorem isProperCompletion_junction_of_prefix {γ T : ℝ≥0 → ℂ} {a : ℝ≥0}
    (hc : ContinuousOn γ (Icc 0 a)) (hi : InjOn γ (Icc 0 a)) (him : ∀ t ≤ a, 0 ≤ (γ t).im)
    (hT : IsProperCurve T) (hT0 : T 0 = γ a) (hdisj : ∀ x < a, ∀ s, γ x ≠ T s) :
    IsProperCompletion γ a (junction γ T a 0) := by
  refine ⟨?_, ?_, ?_, ?_, fun t ht => junction_of_le ht⟩
  · have : Continuous fun t : ℝ≥0 => if t ≤ a then γ t else T (0 + (t - a)) := by
      refine continuous_if_le continuous_id continuous_const (hc.mono fun t ht => ⟨zero_le, ht⟩)
        (hT.1.comp (continuous_const.add (continuous_id.sub continuous_const))).continuousOn
        fun t ht => ?_
      have ht' : t = a := ht
      subst ht'
      simp only [tsub_self, add_zero, hT0]
    exact this
  · intro x y hxy
    by_cases hx : x ≤ a <;> by_cases hy : y ≤ a
    · rw [junction_of_le hx, junction_of_le hy] at hxy
      exact hi ⟨zero_le, hx⟩ ⟨zero_le, hy⟩ hxy
    · exfalso
      rw [junction_of_le hx, junction_of_lt (not_le.1 hy), zero_add] at hxy
      rcases hx.lt_or_eq with hx' | rfl
      · exact hdisj x hx' _ hxy
      · rw [← hT0] at hxy
        have h1 : y - x = 0 := (hT.2.1 hxy).symm
        exact hy (tsub_eq_zero_iff_le.1 h1)
    · exfalso
      rw [junction_of_lt (not_le.1 hx), junction_of_le hy, zero_add] at hxy
      rcases hy.lt_or_eq with hy' | rfl
      · exact hdisj y hy' _ hxy.symm
      · rw [← hT0] at hxy
        have h1 : x - y = 0 := hT.2.1 hxy
        exact hx (tsub_eq_zero_iff_le.1 h1)
    · rw [junction_of_lt (not_le.1 hx), junction_of_lt (not_le.1 hy), zero_add, zero_add] at hxy
      exact (tsub_left_inj (le_of_lt (not_le.1 hx)) (le_of_lt (not_le.1 hy))).1 (hT.2.1 hxy)
  · intro t
    by_cases ht : t ≤ a
    · rw [junction_of_le ht]; exact him t ht
    · rw [junction_of_lt (not_le.1 ht)]; exact hT.2.2.1 _
  · have h1 : Tendsto (fun t : ℝ≥0 => 0 + (t - a)) atTop atTop := by
      refine tendsto_atTop_atTop.2 fun b => ⟨b + a, fun t ht => ?_⟩
      rw [zero_add]
      exact le_tsub_of_add_le_right ht
    refine (hT.2.2.2.comp h1).congr' ?_
    filter_upwards [eventually_gt_atTop a] with t ht
    simp only [Function.comp, junction_of_lt ht]

/-- **One glued curve.** A physical path `η`, continuous and injective on `[0, a]`, whose part on `[c, a]` is the
`ψ`-image of the chart path `g` on `[0, s]` (`ψ(g(0)) = η(c)`, `ψ(g(s)) = η(a)`), and a chart completion `γ` of
`g([0, s])` lying in `ℍ` after time `0`: the junction of `η` up to `a` with `ψ ∘ γ` after `s` is a proper completion of
`η([0, a])`; its points after `c` are `ψ`-images of points `γ(t')`, `t' > 0`, and every `ψ(γ(t'))` is on it. Here `ψ`
maps `ℍ` injectively into a set `D ⊆ ℍ` disjoint from a set `A` containing `η([0, c])`, is continuous on `ℍ̄` with
bounded displacement, and the chart seed `g(0)` is off `ℍ`. -/
theorem glue_side {η g γ : ℝ≥0 → ℂ} {ψ : ℂ → ℂ} {D A : Set ℂ} {c a s : ℝ≥0} {p : ℂ}
    (hca : c ≤ a) (hc : ContinuousOn η (Icc 0 a)) (hi : InjOn η (Icc 0 a)) (hm : ∀ x ≤ a, 0 ≤ (η x).im)
    (hA : ∀ x ≤ c, η x ∈ A) (hDA : Disjoint D A) (hDH : D ⊆ H)
    (hψH : MapsTo ψ H D) (hψi : InjOn ψ H)
    (hψc : ContinuousOn ψ Hbar) (hψM : ∃ M : ℝ, ∀ z ∈ Hbar, ‖ψ z - z‖ ≤ M)
    (hg0 : g 0 = p) (hψp : ψ p = η c) (hs : 0 < s)
    (himg : η '' Icc c a = (fun t => ψ (g t)) '' Icc 0 s) (hend : ψ (g s) = η a)
    (hγ : IsProperCompletion g s γ) (hH : ∀ t, 0 < t → γ t ∈ H) :
    IsProperCompletion η a (junction η (fun t => ψ (γ (s + t))) a 0) ∧
    (∀ t, c < t → ∃ t' > 0, junction η (fun t => ψ (γ (s + t))) a 0 t = ψ (γ t')) ∧
    (∀ t', ψ (γ t') ∈ range (junction η (fun t => ψ (γ (s + t))) a 0)) := by
  set T : ℝ≥0 → ℂ := fun t => ψ (γ (s + t)) with hTdef
  have hγg : ∀ t ≤ s, γ t = g t := hγ.2.2.2.2
  have hγHbar : ∀ t, γ t ∈ Hbar := hγ.2.2.1
  have hsH : ∀ t, γ (s + t) ∈ H := fun t => hH _ (lt_of_lt_of_le hs le_self_add)
  -- the fresh part of `η` through the chart
  have hrep : ∀ x, c < x → x ≤ a → ∃ t' ∈ Ioc 0 s, η x = ψ (γ t') := by
    intro x hcx hxa
    have hmem : η x ∈ (fun t => ψ (g t)) '' Icc 0 s := by
      rw [← himg]; exact mem_image_of_mem η ⟨hcx.le, hxa⟩
    obtain ⟨t', ht', he⟩ := hmem
    have he' : ψ (g t') = η x := he
    have ht'0 : t' ≠ 0 := by
      rintro rfl
      rw [hg0, hψp] at he'
      exact (ne_of_gt hcx) (hi ⟨zero_le, hxa⟩ ⟨zero_le, hca⟩ he'.symm)
    exact ⟨t', ⟨pos_iff_ne_zero.2 ht'0, ht'.2⟩, by rw [← he', hγg t' ht'.2]⟩
  -- the tail is a proper curve
  obtain ⟨M, hM⟩ := hψM
  have hTp : IsProperCurve T := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact hψc.comp_continuous (hγ.1.comp (continuous_const.add continuous_id)) fun t => hγHbar _
    · intro t t' h
      exact add_left_cancel (hγ.2.1 (hψi (hsH t) (hsH t') h))
    · intro t
      exact le_of_lt (show (0 : ℝ) < (T t).im from hDH (hψH (hsH t)))
    · have hst : Tendsto (fun t : ℝ≥0 => s + t) atTop atTop :=
        tendsto_atTop_atTop.2 fun b => ⟨b, fun t ht => ht.trans le_add_self⟩
      have h1 : Tendsto (fun t => ‖γ (s + t)‖) atTop atTop := hγ.2.2.2.1.comp hst
      refine tendsto_atTop_mono (fun t => ?_) (tendsto_atTop_add_const_right _ (-M) h1)
      have h2 := hM _ (hγHbar (s + t))
      have h3 := norm_sub_norm_le (γ (s + t)) (ψ (γ (s + t)))
      rw [norm_sub_rev] at h3
      show ‖γ (s + t)‖ + -M ≤ ‖ψ (γ (s + t))‖
      linarith
  have hT0 : T 0 = η a := by
    show ψ (γ (s + 0)) = η a
    rw [add_zero, hγg s le_rfl, hend]
  have hTD : ∀ t, T t ∈ D := fun t => hψH (hsH t)
  have hdisj : ∀ x < a, ∀ t, η x ≠ T t := by
    intro x hxa t he
    by_cases hxc : x ≤ c
    · exact Set.disjoint_left.1 hDA (by rw [he]; exact hTD t) (hA x hxc)
    · obtain ⟨t', ht', he'⟩ := hrep x (not_le.1 hxc) hxa.le
      have h1 : γ t' = γ (s + t) := hψi (hH t' ht'.1) (hsH t) (he'.symm.trans he)
      have h2 : t' = s + t := hγ.2.1 h1
      have h3 : t = 0 := by
        have h5 : s + t ≤ s := h2 ▸ ht'.2
        simpa using h5
      have h4 : η x = η a := by rw [he, h3, hT0]
      exact (ne_of_lt hxa) (hi ⟨zero_le, hxa.le⟩ ⟨zero_le, le_rfl⟩ h4)
  have hJ := isProperCompletion_junction_of_prefix hc hi hm hTp hT0 hdisj
  refine ⟨hJ, fun t hct => ?_, fun t' => ?_⟩
  · by_cases hta : t ≤ a
    · obtain ⟨t', ht', he⟩ := hrep t hct hta
      exact ⟨t', ht'.1, by rw [junction_of_le hta, he]⟩
    · refine ⟨s + (t - a), lt_of_lt_of_le hs le_self_add, ?_⟩
      rw [junction_of_lt (not_le.1 hta)]
      simp only [hTdef, zero_add]
  · by_cases hts : t' ≤ s
    · have hmem : ψ (g t') ∈ η '' Icc c a := by rw [himg]; exact ⟨t', ⟨zero_le, hts⟩, rfl⟩
      obtain ⟨x, hx, he⟩ := hmem
      exact ⟨x, by rw [junction_of_le hx.2, he, hγg t' hts]⟩
    · have hst : s < t' := not_le.1 hts
      refine ⟨a + (t' - s), ?_⟩
      rw [junction_of_lt (lt_add_of_pos_right a (tsub_pos_of_lt hst))]
      simp only [hTdef, zero_add, add_tsub_cancel_left, add_tsub_cancel_of_le hst.le]

/-! ### The planar gluing -/

/-- **The planar gluing of the stopped reference tangle, interior case** (supplement §7.8, pp. 502–503). Data:
* the old prefixes `η₁([0, u])`, `η₂([0, r])` have ordered proper completions, from real seeds `η₂(0) ≤ η₁(0)`; the
  second tip `η₂(r)` is interior; each tip is off the other old prefix;
* `ψ` is the inverse joint chart: a bijection of `ℍ` onto the joint domain `D = activeDomain η₁ u η₂ r`, continuous
  on `ℍ̄` with bounded displacement, with `ψ(0) = η₂(r)` and `ψ(w) = η₁(u)`, `w > 0`;
* the physical paths, continuous and injective on `[0, a]`, `[0, b]` (`u ≤ a`, `r ≤ b`), are on `[u, a]`, `[r, b]`
  the `ψ`-images of chart paths `g₁` (from `w`) and `g₂` (from `0`) on `[0, s₁]`, `[0, s₂]`, with matching ends;
* the chart prefixes `g₁([0, s₁])`, `g₂([0, s₂])` have ordered proper completions `γ₁`, `γ₂` which lie in `ℍ` after
  time `0` (G9–G10 in the interior case).

Then the enlarged physical prefixes `η₁([0, a])`, `η₂([0, b])` have ordered proper completions. -/
theorem hasOrderedProperCompletions_glue {η₁ η₂ g₁ g₂ γ₁ γ₂ : ℝ≥0 → ℂ} {ψ : ℂ → ℂ}
    {u r a b s₁ s₂ : ℝ≥0} {w : ℝ}
    (hold : HasOrderedProperCompletions η₁ u η₂ r) (h01 : (η₁ 0).im = 0) (h02 : (η₂ 0).im = 0)
    (hseed : (η₂ 0).re ≤ (η₁ 0).re) (hua : u ≤ a) (hrb : r ≤ b)
    (hc₁ : ContinuousOn η₁ (Icc 0 a)) (hi₁ : InjOn η₁ (Icc 0 a)) (hm₁ : ∀ x ≤ a, 0 ≤ (η₁ x).im)
    (hc₂ : ContinuousOn η₂ (Icc 0 b)) (hi₂ : InjOn η₂ (Icc 0 b)) (hm₂ : ∀ y ≤ b, 0 ≤ (η₂ y).im)
    (htip : η₂ r ∈ H) (hp₂ : η₂ r ∉ η₁ '' Icc 0 u) (hp₁ : η₁ u ∉ η₂ '' Icc 0 r)
    (hbij : BijOn ψ H (activeDomain η₁ u η₂ r)) (hψc : ContinuousOn ψ Hbar)
    (hψM : ∃ M : ℝ, ∀ z ∈ Hbar, ‖ψ z - z‖ ≤ M) (hψ0 : ψ 0 = η₂ r) (hψw : ψ w = η₁ u)
    (hw : 0 < w) (hg₁0 : g₁ 0 = w) (hg₂0 : g₂ 0 = 0) (hs₁ : 0 < s₁) (hs₂ : 0 < s₂)
    (himg₁ : η₁ '' Icc u a = (fun s => ψ (g₁ s)) '' Icc 0 s₁) (hend₁ : ψ (g₁ s₁) = η₁ a)
    (himg₂ : η₂ '' Icc r b = (fun s => ψ (g₂ s)) '' Icc 0 s₂) (hend₂ : ψ (g₂ s₂) = η₂ b)
    (hγ₁ : IsProperCompletion g₁ s₁ γ₁) (hγ₂ : IsProperCompletion g₂ s₂ γ₂)
    (hord : range γ₂ ⊆ closedLeftSide γ₁) (hH₁ : ∀ t, 0 < t → γ₁ t ∈ H)
    (hH₂ : ∀ t, 0 < t → γ₂ t ∈ H) :
    HasOrderedProperCompletions η₁ a η₂ b := by
  set D := activeDomain η₁ u η₂ r with hD
  set A := η₁ '' Icc 0 u ∪ η₂ '' Icc 0 r with hA
  have hDsub : ∀ z ∈ D, z ∈ H ∧ z ∉ A := fun z hz => hz.1
  have hDA : Disjoint D A := Set.disjoint_left.2 fun z hz hzA => (hDsub z hz).2 hzA
  have hDH : D ⊆ H := fun z hz => (hDsub z hz).1
  have h0H : (0 : ℂ) ∉ H := fun h => by
    have h' : (0 : ℝ) < (0 : ℂ).im := h
    simp at h'
  obtain ⟨hα, hαrep, hαrange⟩ := glue_side (A := A) hua hc₁ hi₁ hm₁
    (fun x hx => Or.inl ⟨x, ⟨zero_le, hx⟩, rfl⟩) hDA hDH hbij.mapsTo hbij.injOn hψc hψM hg₁0 hψw hs₁ himg₁
    hend₁ hγ₁ hH₁
  obtain ⟨hβ, hβrep, -⟩ := glue_side (A := A) hrb hc₂ hi₂ hm₂
    (fun y hy => Or.inr ⟨y, ⟨zero_le, hy⟩, rfl⟩) hDA hDH hbij.mapsTo hbij.injOn hψc hψM hg₂0 hψ0 hs₂ himg₂
    hend₂ hγ₂ hH₂
  set α'' := junction η₁ (fun t => ψ (γ₁ (s₁ + t))) a 0 with hα''
  set β'' := junction η₂ (fun t => ψ (γ₂ (s₂ + t))) b 0 with hβ''
  refine ⟨α'', β'', hα, hβ, ?_⟩
  have hαP := isProperCurve_of_isProperCompletion hα
  have hα0 : α'' 0 = η₁ 0 := hα.2.2.2.2 0 zero_le
  have hα''0 : (α'' 0).im = 0 := by rw [hα0]; exact h01
  have hαD : ∀ t, u < t → α'' t ∈ D := fun t ht => by
    obtain ⟨t', ht', he⟩ := hαrep t ht
    rw [he]; exact hbij.mapsTo (hH₁ t' ht')
  -- Step 1: the old second prefix is on the closed left side of the new first curve
  obtain ⟨αo, βo, hαo, hβo, hordo⟩ := hold
  have hαu : IsProperCompletion η₁ u α'' :=
    ⟨hα.1, hα.2.1, hα.2.2.1, hα.2.2.2.1, fun t ht => hα.2.2.2.2 t (ht.trans hua)⟩
  have htail : ∀ s, u ≤ s → ∀ y ≤ r, α'' s ≠ η₂ y := by
    intro s hs y hy he
    rcases hs.lt_or_eq with hs' | heq
    · exact Set.disjoint_left.1 hDA (hαD s hs') (by rw [he]; exact Or.inr ⟨y, ⟨zero_le, hy⟩, rfl⟩)
    · rw [← heq, hα.2.2.2.2 u hua] at he
      exact hp₁ ⟨y, ⟨zero_le, hy⟩, he.symm⟩
  obtain ⟨β₀, hβ₀, hord₀⟩ :=
    exists_isProperCompletion_subset_closedLeftSide hαo hβo hordo h01 h02 hseed hαu htail
  have hold₂ : ∀ y ≤ r, η₂ y ∈ closedLeftSide α'' := fun y hy => by
    rw [← hβ₀.2.2.2.2 y hy]; exact hord₀ ⟨y, rfl⟩
  -- Step 2: the chart left side in `ℍ` goes to the left side of `α''`
  have hγ₁P := isProperCurve_of_isProperCompletion hγ₁
  have hγ₁0 : γ₁ 0 = w := by rw [hγ₁.2.2.2.2 0 zero_le, hg₁0]
  have hγ₁0im : (γ₁ 0).im = 0 := by rw [hγ₁0]; simp
  have hγ₂0 : γ₂ 0 = 0 := by rw [hγ₂.2.2.2.2 0 zero_le, hg₂0]
  have hoffα : ∀ z ∈ H, z ∉ range γ₁ → ψ z ∉ seedRayClosure α'' := by
    intro z hz hzγ hzS
    rcases hzS with ⟨t, ht⟩ | ⟨-, him⟩
    · by_cases htu : t ≤ u
      · have hA' : α'' t ∈ A := by
          rw [hα.2.2.2.2 t (htu.trans hua)]; exact Or.inl ⟨t, ⟨zero_le, htu⟩, rfl⟩
        exact Set.disjoint_left.1 hDA (by rw [ht]; exact hbij.mapsTo hz) hA'
      · obtain ⟨t', ht', he⟩ := hαrep t (not_le.1 htu)
        have : z = γ₁ t' := hbij.injOn hz (hH₁ t' ht') (ht.symm.trans he)
        exact hzγ ⟨t', this.symm⟩
    · rw [hα''0] at him
      exact absurd (show (0 : ℝ) < (ψ z).im from hDH (hbij.mapsTo hz)) (not_lt.2 him)
  have hsides : ∀ z ∈ leftSide γ₁ ∩ H, ψ z ∈ leftSide α'' ∪ rightSide α'' := fun z hz => by
    rw [← compl_seedRayClosure_eq hαP hα''0]
    exact hoffα z hz.2 fun h => connectedComponentIn_subset _ _ hz.1 (Or.inl h)
  have hconn : IsPreconnected (ψ '' (leftSide γ₁ ∩ H)) :=
    (isPreconnected_leftSide_inter_H hγ₁P hγ₁0im hH₁).image ψ
      (hψc.mono fun z hz => show (0 : ℝ) ≤ z.im from le_of_lt (show (0 : ℝ) < z.im from hz.2))
  -- the second tip is on the open left side of `α''`
  have htipL : η₂ r ∈ leftSide α'' := by
    rcases hold₂ r le_rfl with h | h
    · exact h
    · exfalso
      rcases h with ⟨t, ht⟩ | ⟨-, him⟩
      · by_cases htu : t ≤ u
        · rw [hα.2.2.2.2 t (htu.trans hua)] at ht
          exact hp₂ ⟨t, ⟨zero_le, htu⟩, ht⟩
        · exact Set.disjoint_left.1 hDA (ht ▸ hαD t (not_le.1 htu)) (Or.inr ⟨r, ⟨zero_le, le_rfl⟩, rfl⟩)
      · rw [hα''0] at him
        exact absurd (show (0 : ℝ) < (η₂ r).im from htip) (not_lt.2 him)
  -- the chart seed `0` of the second completion is on the open left side of `γ₁`
  have h0L : (0 : ℂ) ∈ leftSide γ₁ := by
    have h0c : (0 : ℂ) ∈ closedLeftSide γ₁ := hγ₂0 ▸ hord ⟨0, rfl⟩
    rcases h0c with h | h
    · exact h
    · exfalso
      rcases h with ⟨t, ht⟩ | ⟨hre, -⟩
      · rcases eq_zero_or_pos t with rfl | htp
        · rw [hγ₁0] at ht
          exact hw.ne' (by exact_mod_cast ht)
        · exact h0H (ht ▸ hH₁ t htp)
      · rw [hγ₁0] at hre
        simp only [zero_re, ofReal_re] at hre
        exact hw.ne' hre.symm
  obtain ⟨ε, hε, hεL⟩ := Metric.isOpen_iff.1 (isOpen_leftSide hγ₁P) 0 h0L
  obtain ⟨ρ, hρ, hρL⟩ := Metric.isOpen_iff.1 (isOpen_leftSide hαP) _ htipL
  have hψ0c : ContinuousWithinAt ψ Hbar 0 := hψc 0 (show (0 : ℝ) ≤ (0 : ℂ).im by simp)
  obtain ⟨δ, hδ, hδψ⟩ := Metric.continuousWithinAt_iff.1 hψ0c ρ hρ
  have hmin : 0 < min ε δ := lt_min hε hδ
  set e : ℝ := min ε δ / 2 with he
  have hepos : 0 < e := half_pos hmin
  have hzH : (e : ℂ) * I ∈ H := show (0 : ℝ) < ((e : ℂ) * I).im by simpa using hepos
  have hzn : ‖(e : ℂ) * I‖ = e := by simp [abs_of_pos hepos]
  have hz1 : (e : ℂ) * I ∈ leftSide γ₁ := hεL (by
    rw [mem_ball, dist_zero_right, hzn]
    exact lt_of_lt_of_le (half_lt_self hmin) (min_le_left _ _))
  have hz2 : ψ ((e : ℂ) * I) ∈ leftSide α'' := hρL (by
    rw [mem_ball, ← hψ0]
    exact hδψ (show (0 : ℝ) ≤ ((e : ℂ) * I).im from le_of_lt hzH) (by
      rw [dist_zero_right, hzn]
      exact lt_of_lt_of_le (half_lt_self hmin) (min_le_right _ _)))
  have hPL : ψ '' (leftSide γ₁ ∩ H) ⊆ leftSide α'' :=
    hconn.subset_left_of_subset_union (isOpen_leftSide hαP) (isOpen_rightSide hαP)
      (disjoint_leftSide_rightSide hαP hα''0) (by rintro _ ⟨z, hz, rfl⟩; exact hsides z hz)
      ⟨_, ⟨_, ⟨hz1, hzH⟩, rfl⟩, hz2⟩
  -- Step 3: every point of the second glued curve
  rintro _ ⟨t, rfl⟩
  by_cases htr : t ≤ r
  · rw [hβ.2.2.2.2 t (htr.trans hrb)]; exact hold₂ t htr
  · obtain ⟨t', ht', he⟩ := hβrep t (not_le.1 htr)
    rw [he]
    have hH' := hH₂ t' ht'
    rcases hord ⟨t', rfl⟩ with hL | hS
    · exact Or.inl (hPL ⟨_, ⟨hL, hH'⟩, rfl⟩)
    · rcases hS with ⟨t'', ht''⟩ | ⟨-, him⟩
      · rw [← ht'']; exact Or.inr (Or.inl (hαrange t''))
      · exfalso
        rw [hγ₁0im] at him
        exact absurd (show (0 : ℝ) < (γ₂ t').im from hH') (not_lt.2 him)

end Glue

end RLC

end InteractingSLE
