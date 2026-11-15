/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2FinChart
import InteractingSLE.Spec.Supplement.RelTransHull

/-!
# SB2(1)'s junction landings on the relative hull image

Packet PROVE-T14-SB2FIN. The field `landK` of `SB.Union.IsRelConfigJ` (PROVE-T14-SB2UNION) for SB2(1)'s relative
chain (`IsSB2RelChain`): every point of the relative hull image `[a_L, a_R)` lands, through the joint parametrization
`c.inv ∘ F_u`, on the closed physical filling (SB2, p. 632: "the accessible boundary of the relative hull [...]
lands on the upper flow").

* `mem_of_mem_closure_fillH_of_mem_closure_compl`: a point of `closure ℍ` in the closures of both a filling and its
  complement in `ℍ` lies on the (closed) set — off the set a small half-disc lies in one component;
* `extendFrom_jointInv_eq`: the joint landing is `g` of the relative landing;
* `mem_closure_fillH_post`: every point of the post-entrance physical prefix is a limit of its points in `ℍ` (no
  original-real arc);
* **`landK_of_isSB2RelChain`**: the field `landK` at every positive relative time `a s`, `0 < s ≤ S₀`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdHull fwdMapInv)

namespace InteractingSLE.Theorem14.SB.FinRel

open Sec7.Lemma71C
open WangWu (chartAL chartAR)

/-- **A common boundary point of a filling and its complement lies on the set**: if `z` is in the closure
of `fill Y` and in the closure of `ℍ ∖ fill Y` (`Y` closed), then `z ∈ Y`. Off `Y`, a small disc about `z` misses `Y`;
its trace on `ℍ` is preconnected, so it lies in one component of `ℍ ∖ Y`, which cannot be both bounded and
unbounded. -/
theorem mem_of_mem_closure_fillH_of_mem_closure_compl {Y : Set ℂ} (hY : IsClosed Y) {z : ℂ}
    (h₁ : z ∈ closure (fillH Y)) (h₂ : z ∈ closure (H \ fillH Y)) : z ∈ Y := by
  by_contra hzY
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hY.isOpen_compl z hzY
  set B := ball z ε ∩ H with hB
  have hBpre : IsPreconnected B :=
    ((convex_ball z ε).inter (convex_halfSpace_gt (f := fun w : ℂ => w.im) Complex.imLm.isLinear 0)).isPreconnected
  have hBY : B ⊆ H \ closure Y := fun w hw => ⟨hw.2, by rw [hY.closure_eq]; exact hball hw.1⟩
  obtain ⟨w₁, hw₁B, hw₁⟩ := mem_closure_iff_nhds.1 h₁ _ (ball_mem_nhds z hε)
  obtain ⟨w₂, hw₂B, hw₂⟩ := mem_closure_iff_nhds.1 h₂ _ (ball_mem_nhds z hε)
  have hw₁H : w₁ ∈ B := ⟨hw₁B, hw₁.1⟩
  have hw₂H : w₂ ∈ B := ⟨hw₂B, hw₂.1⟩
  have hcomp : connectedComponentIn (H \ closure Y) w₁ = connectedComponentIn (H \ closure Y) w₂ :=
    connectedComponentIn_eq (hBpre.subset_connectedComponentIn hw₁H hBY hw₂H)
  rcases hw₁.2 with hcl | hb
  · rw [hY.closure_eq] at hcl
    exact hball hw₁B hcl
  · apply hw₂.2
    exact ⟨hw₂.1, Or.inr (hcomp ▸ hb)⟩

section Land

variable {A : Set ℂ} {L : ℝ} {c : Chart} {g : ℂ → ℂ} {β' γ : ℝ≥0 → ℂ} {tL : ℝ≥0} {S₀ : ℝ} {Wr : ℝ → ℝ}
  {ηr : ℝ → ℂ}

/-- **The joint landing is `g` of the relative landing.** -/
theorem extendFrom_jointInv_eq (hgc : ContinuousOn g {z | 0 ≤ z.im}) (hgi : EqOn g c.2.1 H) (hWr : Continuous Wr)
    (hWr0 : Wr 0 = 0) (hηr : IsLoewnerTrace Wr ηr) {u : ℝ} (hu : 0 ≤ u) {x : ℂ} (hx : x ∈ Hbar) :
    extendFrom H (Supp8.BHMean.jointInv c.2.1 Wr u) x = g (extendFrom H (fwdMapInv Wr u) x) := by
  have hF := (hηr.hasBdryLimits hWr hWr0 hu).tendsto hx
  have hFmem : extendFrom H (fwdMapInv Wr u) x ∈ {z : ℂ | 0 ≤ z.im} := by
    rw [← closure_H] at hx
    have hcl : extendFrom H (fwdMapInv Wr u) x ∈ closure H := by
      have := mem_closure_iff_nhdsWithin_neBot.1 hx
      exact mem_closure_of_tendsto hF (eventually_nhdsWithin_of_forall fun y hy =>
        (QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hWr hWr0 hu hy).1)
    rw [closure_H] at hcl
    exact hcl
  have hF' : Tendsto (fwdMapInv Wr u) (𝓝[H] x) (𝓝[{z : ℂ | 0 ≤ z.im}] (extendFrom H (fwdMapInv Wr u) x)) :=
    tendsto_nhdsWithin_iff.2 ⟨hF, eventually_nhdsWithin_of_forall fun y hy =>
      show 0 ≤ (fwdMapInv Wr u y).im from le_of_lt
        (show 0 < (fwdMapInv Wr u y).im from (QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hWr hWr0 hu hy).1)⟩
  have h1 : Tendsto (Supp8.BHMean.jointInv c.2.1 Wr u) (𝓝[H] x) (𝓝 (g (extendFrom H (fwdMapInv Wr u) x))) := by
    refine ((hgc _ hFmem).tendsto.comp hF').congr' (eventually_nhdsWithin_of_forall fun y hy => ?_)
    simp only [Function.comp, Supp8.BHMean.jointInv]
    exact hgi (QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hWr hWr0 hu hy).1
  rw [← closure_H] at hx
  exact extendFrom_eq hx h1

/-- **The post-entrance physical prefix lies in the closure of the physical filling**: with no open original-real arc
on `(0, S)`, every `β'(t_L + r)`, `r ≤ s`, `0 < s < S`, is a limit of points of the prefix in `ℍ`. -/
theorem mem_closure_fillH_post (hβc : Continuous β') {S : ℝ}
    (hnR : interior {r ∈ Ioo (0 : ℝ) S | β' (tL + r.toNNReal) ∈ {z : ℂ | z.im = 0}} = ∅)
    (hβH : ∀ t, 0 ≤ (β' t).im) {s : ℝ} (hs0 : 0 < s) (hsS : s < S) {r : ℝ≥0} (hr : (r : ℝ) ≤ s) :
    β' (tL + r) ∈ closure (fillH (β' '' Icc 0 (tL + s.toNNReal))) := by
  rw [mem_closure_iff_nhds]
  intro N hN
  have hcont : Continuous fun r' : ℝ => β' (tL + r'.toNNReal) :=
    hβc.comp (continuous_const.add continuous_real_toNNReal)
  have hpre : (fun r' : ℝ => β' (tL + r'.toNNReal)) ⁻¹' N ∈ 𝓝 (r : ℝ) := by
    apply hcont.continuousAt.preimage_mem_nhds
    simpa only [Real.toNNReal_coe] using hN
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.1 hpre
  -- a nonempty open interval of `(0, s)` near `r`
  set lo := max 0 ((r : ℝ) - δ / 2) with hlo
  set hi := min s ((r : ℝ) + δ / 2) with hhi
  have hlohi : lo < hi := by
    rw [hlo, hhi]
    refine max_lt (lt_min hs0 (by positivity)) (lt_min (by linarith) (by linarith))
  have hIsub : Ioo lo hi ⊆ {r' ∈ Ioo (0 : ℝ) S | β' (tL + r'.toNNReal) ∈ {z : ℂ | z.im = 0}} ∨
      ∃ r' ∈ Ioo lo hi, β' (tL + r'.toNNReal) ∉ {z : ℂ | z.im = 0} := by
    by_cases h : ∃ r' ∈ Ioo lo hi, β' (tL + r'.toNNReal) ∉ {z : ℂ | z.im = 0}
    · exact Or.inr h
    · left
      intro r' hr'
      have h0 : 0 < r' := lt_of_le_of_lt (le_max_left _ _) hr'.1
      have hS : r' < S := lt_of_lt_of_le hr'.2 ((min_le_left _ _).trans hsS.le)
      refine ⟨⟨h0, hS⟩, ?_⟩
      by_contra hc
      exact h ⟨r', hr', hc⟩
  rcases hIsub with hsub | ⟨r', hr', hne⟩
  · have := interior_mono hsub
    rw [isOpen_Ioo.interior_eq, hnR] at this
    exact absurd (this (show (lo + hi) / 2 ∈ Ioo lo hi from ⟨by linarith, by linarith⟩)) (notMem_empty _)
  · refine ⟨β' (tL + r'.toNNReal), hδsub ?_, ?_⟩
    · rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      have h1 : (r : ℝ) - δ / 2 ≤ lo := le_max_right _ _
      have h2 : hi ≤ (r : ℝ) + δ / 2 := min_le_right _ _
      constructor <;> linarith [hr'.1, hr'.2]
    · have hpos : 0 < (β' (tL + r'.toNNReal)).im := lt_of_le_of_ne (hβH _) (Ne.symm hne)
      have hr's : r' ≤ s := (le_of_lt hr'.2).trans (min_le_left _ _)
      have hr'0 : 0 ≤ r' := (le_max_left _ _).trans (le_of_lt hr'.1)
      refine ⟨hpos, Or.inl (subset_closure ⟨tL + r'.toNNReal, ⟨zero_le, ?_⟩, rfl⟩)⟩
      exact add_le_add_right (Real.toNNReal_le_toNNReal hr's) tL

/-- **The field `landK`** for SB2(1)'s relative chain at a positive relative time: every point of `[a_L, a_R)` lands
on the closed physical filling. -/
theorem landK_of_isSB2RelChain (hgc : ContinuousOn g {z | 0 ≤ z.im}) (hgi : EqOn g c.2.1 H)
    (hβ' : Supp9B.IsProperCurve β') (hγ : Supp9B.IsProperCurve γ) (hlift : ∀ s, g (γ s) = β' (tL + s))
    (hch : IsSB2RelChain A c β' γ tL S₀ Wr ηr) {S : ℝ} (hS₀S : S₀ < S)
    (hnR : interior {r ∈ Ioo (0 : ℝ) S | β' (tL + r.toNNReal) ∈ {z : ℂ | z.im = 0}} = ∅) {s : ℝ}
    (hs : s ∈ Ioc 0 S₀) :
    ∀ x ∈ Ico (chartAL Wr (capClock (fun r : ℝ => γ r.toNNReal) s))
        (chartAR Wr (capClock (fun r : ℝ => γ r.toNNReal) s)),
      extendFrom H (Supp8.BHMean.jointInv c.2.1 Wr (capClock (fun r : ℝ => γ r.toNNReal) s)) (x : ℂ) ∈
        closure (fillH (β' '' Icc 0 (tL + s.toNNReal))) := by
  obtain ⟨hWr, hWr0, hηr, hc0, hcm, -, hK⟩ := hch
  intro x hx
  set u := capClock (fun r : ℝ => γ r.toNNReal) s with hudef
  have hu : 0 < u := by
    have := hcm ⟨le_rfl, hs.1.le.trans hs.2⟩ ⟨hs.1.le, hs.2⟩ hs.1
    rwa [hc0] at this
  have hlt : chartAL Wr u < chartAR Wr u := lt_of_le_of_lt hx.1 hx.2
  have hxb : (x : ℂ) ∈ Hbar := show (0 : ℝ) ≤ ((x : ℂ)).im by simp
  have hFK : extendFrom H (fwdMapInv Wr u) (x : ℂ) ∈ closure (fwdHull Wr u) :=
    Supp8.RelTrans.Icc_subset_hullImage hηr hWr hWr0 hu hlt (Ico_subset_Icc_self hx)
  have hF := (hηr.hasBdryLimits hWr hWr0 hu.le).tendsto hxb
  have hneb : (𝓝[H] (x : ℂ)).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (by rw [closure_H]; exact hxb)
  have hFc : extendFrom H (fwdMapInv Wr u) (x : ℂ) ∈ closure (H \ fwdHull Wr u) :=
    mem_closure_of_tendsto hF (eventually_nhdsWithin_of_forall fun y hy =>
      QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hWr hWr0 hu.le hy)
  obtain ⟨-, -, hKs, -, -⟩ := hK s ⟨hs.1.le, hs.2⟩
  rw [← hudef] at hKs
  rw [hKs] at hFK hFc
  have hYc : IsClosed (γ '' Icc 0 s.toNNReal) := (isCompact_Icc.image hγ.1).isClosed
  obtain ⟨r, hr, hre⟩ := mem_of_mem_closure_fillH_of_mem_closure_compl hYc hFK hFc
  rw [extendFrom_jointInv_eq hgc hgi hWr hWr0 hηr hu.le hxb, ← hre, hlift]
  have hrs : (r : ℝ) ≤ s := by
    have := hr.2
    rwa [← NNReal.coe_le_coe, Real.coe_toNNReal _ hs.1.le] at this
  exact mem_closure_fillH_post hβ'.1 hnR hβ'.2.2.1 hs.1 (lt_of_le_of_lt hs.2 hS₀S) hrs

end Land

end InteractingSLE.Theorem14.SB.FinRel
