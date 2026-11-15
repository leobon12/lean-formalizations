/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R6TwoTarget

/-!
# R.6: free points on the actual shared wall near the inner target

PROVE-R6-TWO. Compact relative traces have free collars sufficiently far
away. Along an inner Jordan boundary arc approaching its target, its
coordinate tends to infinity. If the outer coordinate has a free collar
at that target, continuity gives points free in both initial coordinates.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Bornology
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R6Two

open Sec6 PocketTraversal PocketStopMarked Lemma71C PocketJordan PocketWordAssembly

/-- The free collar condition holds eventually along any map whose norm
tends to infinity, for a bounded closed trace. -/
theorem eventually_isFreeAt_of_tendsto_norm_atTop {ι : Type*} {l : Filter ι}
    {F : Set ℂ} (hF : IsClosed F) (hFb : IsBounded F) {f : ι → ℂ}
    (hf : Tendsto (fun t => ‖f t‖) l atTop) :
    ∀ᶠ t in l, HalfPlaneSep.IsFreeAt F (f t) := by
  obtain ⟨R, hR, hFR⟩ := exists_closure_subset_ball hFb
  filter_upwards [hf.eventually (eventually_gt_atTop (R + 1))] with t ht
  refine ⟨1, one_pos, fun z hz => HalfPlaneSep.mem_H_diff_fillH_of_le_norm hF hR
    (subset_closure.trans hFR) hz.2 ?_⟩
  have hdist : ‖z - f t‖ < 1 := by simpa only [mem_ball, dist_eq_norm] using hz.1
  have hnorm := norm_sub_norm_le (f t) z
  rw [norm_sub_rev] at hnorm
  linarith

/-- A Jordan target arc, with a continuous outer coordinate free at the
target, contains open-arc points with free collars in both coordinates. -/
theorem exists_arc_point_isFreeAt {V F G : Set ℂ} {x y : ℂ}
    {ψ φ : ℂ → ℂ} {a : ℝ → ℂ}
    (hJ : IsJordanCoord V x y φ) (hGc : IsClosed G) (hGb : IsBounded G)
    (ha : ContinuousOn a (Icc 0 1)) (hi : InjOn a (Icc 0 1)) (ha0 : a 0 = x)
    (haV : MapsTo a (Icc 0 1) (closure V))
    (hψ : ContinuousWithinAt ψ (closure V) x) (hF : HalfPlaneSep.IsFreeAt F (ψ x)) :
    ∃ s ∈ Ioo (0 : ℝ) 1, HalfPlaneSep.IsFreeAt F (ψ (a s)) ∧
      HalfPlaneSep.IsFreeAt G (φ (a s)) := by
  have h01 : Ioo (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT zero_lt_one
  have haLim : Tendsto a (𝓝[>] (0 : ℝ)) (𝓝 x) := by
    rw [← ha0]
    exact (ha 0 ⟨le_rfl, zero_le_one⟩).mono_of_mem_nhdsWithin
      (mem_of_superset h01 Ioo_subset_Icc_self)
  have haMem : ∀ᶠ s in 𝓝[>] (0 : ℝ), a s ∈ closure V \ {x} := by
    filter_upwards [h01] with s hs
    refine ⟨haV (Ioo_subset_Icc_self hs), ?_⟩
    intro he
    exact hs.1.ne' (hi (Ioo_subset_Icc_self hs) ⟨le_rfl, zero_le_one⟩ (he.trans ha0.symm))
  have hψlim : Tendsto (fun s => ψ (a s)) (𝓝[>] (0 : ℝ)) (𝓝 (ψ x)) :=
    hψ.tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨haLim, haMem.mono fun _ h => h.1⟩)
  have hφlim : Tendsto (fun s => φ (a s)) (𝓝[>] (0 : ℝ)) (cobounded ℂ) :=
    hJ.2.2.2.2.2.2.comp (tendsto_nhdsWithin_iff.2 ⟨haLim, haMem⟩)
  have hφnorm : Tendsto (fun s => ‖φ (a s)‖) (𝓝[>] (0 : ℝ)) atTop :=
    tendsto_norm_atTop_iff_cobounded.2 hφlim
  have hOuter := hψlim.eventually ((HalfPlaneSep.isOpen_setOf_isFreeAt F).mem_nhds hF)
  obtain ⟨s, hs, hFs, hGs⟩ := (Filter.Eventually.and h01 (hOuter.and
    (eventually_isFreeAt_of_tendsto_norm_atTop hGc hGb hφnorm))).exists
  exact ⟨s, hs, hFs, hGs⟩

/-- When the two pockets have the same finite target, both Jordan
coordinates tend to infinity along the inner target arc. -/
theorem exists_arc_point_isFreeAt_common_target {C V F G : Set ℂ} {x yC yV : ℂ}
    {ψ φ : ℂ → ℂ} {a : ℝ → ℂ}
    (hC : IsJordanCoord C x yC ψ) (hV : IsJordanCoord V x yV φ) (hVC : V ⊆ C)
    (hFc : IsClosed F) (hFb : IsBounded F) (hGc : IsClosed G) (hGb : IsBounded G)
    (ha : ContinuousOn a (Icc 0 1)) (hi : InjOn a (Icc 0 1)) (ha0 : a 0 = x)
    (haV : MapsTo a (Icc 0 1) (closure V)) :
    ∃ s ∈ Ioo (0 : ℝ) 1, HalfPlaneSep.IsFreeAt F (ψ (a s)) ∧
      HalfPlaneSep.IsFreeAt G (φ (a s)) := by
  have h01 : ∀ᶠ s in 𝓝[>] (0 : ℝ), s ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsGT zero_lt_one
  have haLim : Tendsto a (𝓝[>] (0 : ℝ)) (𝓝 x) := by
    rw [← ha0]
    exact (ha 0 ⟨le_rfl, zero_le_one⟩).mono_of_mem_nhdsWithin
      (mem_of_superset h01 Ioo_subset_Icc_self)
  have haMem : ∀ᶠ s in 𝓝[>] (0 : ℝ), a s ∈ closure V \ {x} := by
    filter_upwards [h01] with s hs
    refine ⟨haV (Ioo_subset_Icc_self hs), ?_⟩
    intro he
    exact hs.1.ne' (hi (Ioo_subset_Icc_self hs) ⟨le_rfl, zero_le_one⟩ (he.trans ha0.symm))
  have hψlim := hC.2.2.2.2.2.2.comp (tendsto_nhdsWithin_iff.2
    ⟨haLim, haMem.mono fun _ h => ⟨closure_mono hVC h.1, h.2⟩⟩)
  have hφlim := hV.2.2.2.2.2.2.comp (tendsto_nhdsWithin_iff.2 ⟨haLim, haMem⟩)
  obtain ⟨s, hs, hFs, hGs⟩ := (h01.and
    ((eventually_isFreeAt_of_tendsto_norm_atTop hFc hFb
      (tendsto_norm_atTop_iff_cobounded.2 hψlim)).and
      (eventually_isFreeAt_of_tendsto_norm_atTop hGc hGb
        (tendsto_norm_atTop_iff_cobounded.2 hφlim)))).exists
  exact ⟨s, hs, hFs, hGs⟩

/-- A witness on the actual common right wall of the bounded two-outer
shape, after the current-domain inclusion has been established. Its two
initial-coordinate images both have unfilled collars. The proof uses
target accessibility and freshness, with no reverse-visit premise on an
outer arm. -/
theorem exists_shared_wall_isFreeAt_two {W : ℝ → ℝ} {η : ℝ → ℂ}
    {R L ML : ℝ≥0 → ℂ} {r s : ℝ≥0} {ψ φ : ℂ → ℂ} {BV : Chart}
    (hcfgC : HOuter.IsOuterCfg R L r W η) (hcfgV : HOuter.IsOuterCfg R ML s W η)
    (hJC : PocketWordAssembly.IsCfJordan R L r ψ)
    (hJV : PocketWordAssembly.IsCfJordan R ML s φ)
    (hVC : PocketJordan.cfPocket R ML s ⊆ PocketJordan.cfPocket R L r)
    (hBV : BV.IsConformal) (hBVdom : (BV.dom : Set ℂ) = PocketJordan.cfPocket R ML s)
    (hBVfwd : EqOn BV.1 φ (PocketJordan.cfPocket R ML s))
    {q qV : ℝ≥0} (hqV : (qV : ℝ≥0∞) < capLife (cfTraversal R ML s η φ))
    (hT : pocketFibre η (PocketJordan.cfPocket R L r)
      (firstHit η (PocketJordan.cfArcR R L r 1)) (firstHit η (PocketJordan.cfArcR R L r 0))
      (clockOf (pocketClock η (PocketJordan.cfPocket R L r)
        (firstHit η (PocketJordan.cfArcR R L r 1)) (firstHit η (PocketJordan.cfArcR R L r 0))
        (firstHit η (PocketJordan.cfArcR R L r 0))) (capInv (cfTraversal R L r η ψ) q)) <
      firstHit η (PocketJordan.cfArcR R ML s 0))
    (hIncl : ((BV.loewner (fun t : ℝ => segDriver (cfTraversal R ML s η φ) t.toNNReal) qV).dom : Set ℂ) ⊆
      PocketJordan.cfPocket R L r ∩ ψ ⁻¹' (H \ fillH
        (cfTraversal R L r η ψ '' Icc 0 (capInv (cfTraversal R L r η ψ) q)))) :
    ∃ u ∈ Ioo (0 : ℝ) 1,
      HalfPlaneSep.IsFreeAt (cfTraversal R L r η ψ '' Icc 0 (capInv (cfTraversal R L r η ψ) q))
        (ψ (PocketJordan.cfArcR R ML s u)) ∧
      HalfPlaneSep.IsFreeAt (cfTraversal R ML s η φ '' Icc 0 (capInv (cfTraversal R ML s η φ) qV))
        (φ (PocketJordan.cfArcR R ML s u)) := by
  let hC := hcfgC.toPocket hJC
  let hV := hcfgV.toPocket hJV
  let a := PocketJordan.cfArcR R ML s
  have hP := hcfgV.conf.isCfPocket
    (PocketMarks.zero_notMem_closure_of_rightLo_pos hcfgV.conf hcfgV.bounded)
  have ha0 : a 0 = PocketJordan.cfArcR R ML s 0 := rfl
  have haV : MapsTo a (Icc 0 1) (closure (PocketJordan.cfPocket R ML s)) := by
    intro u hu
    exact frontier_subset_closure (hP.frontier_eq ▸ Or.inl ⟨u, hu, rfl⟩)
  have hFc : IsCompact (cfTraversal R L r η ψ '' Icc 0 (capInv (cfTraversal R L r η ψ) q)) :=
    isCompact_Icc.image_of_continuousOn (hC.driven.continuousOn.mono fun _ hu => hu.1)
  have hGc : IsCompact (cfTraversal R ML s η φ '' Icc 0 (capInv (cfTraversal R ML s η φ) qV)) :=
    isCompact_Icc.image_of_continuousOn (hV.driven.continuousOn.mono fun _ hu => hu.1)
  by_cases hPole : PocketJordan.cfArcR R ML s 0 =
      PocketJordan.cfArcR R L r 0
  · exact exists_arc_point_isFreeAt_common_target (hPole.symm ▸ hC.jordan) hV.jordan hVC
      hFc.isClosed hFc.isBounded hGc.isClosed hGc.isBounded hP.cont₁ hP.inj₁ ha0 haV
  · have hxC : PocketJordan.cfArcR R ML s 0 ∈
        closure (PocketJordan.cfPocket R L r) := closure_mono hVC (ha0 ▸ haV ⟨le_rfl, zero_le_one⟩)
    have hψ : ContinuousWithinAt ψ (closure (PocketJordan.cfPocket R ML s))
        (PocketJordan.cfArcR R ML s 0) := by
      apply (hC.jordan.1 _ ⟨hxC, hPole⟩).mono_of_mem_nhdsWithin
      exact mem_nhdsWithin.2 ⟨{PocketJordan.cfArcR R L r 0}ᶜ,
        isClosed_singleton.isOpen_compl, hPole, fun z hz => ⟨closure_mono hVC hz.2, hz.1⟩⟩
    exact exists_arc_point_isFreeAt hV.jordan hGc.isClosed hGc.isBounded
      hP.cont₁ hP.inj₁ ha0 haV hψ
      (isFreeAt_outer_inner_target hC hV hBV hBVdom hBVfwd hqV hPole hT hIncl)

end InteractingSLE.Sec7.R6Two
