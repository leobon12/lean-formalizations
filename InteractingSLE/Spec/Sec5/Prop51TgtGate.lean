/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61KernelTop
import InteractingSLE.Spec.Sec5.Prop51HTopoAccessBoundary

/-!
# A positive gate near `0`, and the target component reached from the gate's chart component

Packet PROVE-PROP51-TGT (Theorem 1.2's Proposition 5.1 with (E1) in Astra's target-component form; ruling R71,
`source/external/AstraIG1/ig1_followup4_audited.txt` §1.7 L455–L463: "each later interior point of the same excursion
can be joined, through its outer collar and then the path just constructed, to the original right-target collar while
avoiding `K ∪ η([0, r])`").

In the counterflow chart `Ψ = revChart w s` of `D = ℍ ∖ R(K_s)` (`R z = −1/z`), a free positive gate
(`Prop51HTopo.PositiveBoundaryGate`) is a chart ball about a positive real point `x₀` avoiding the closure of the chart
flow set, whose physical boundary value is a positive real point. This file

* chooses the gate with its physical boundary value **near `0`** (`exists_positiveBoundaryGate_lt`), so that a
  physical half-disc about it misses the counterflow hull, which stays away from `0`
  (`exists_pos_lt_norm_of_mem_cfHullQ`);
* proves the **target-component transfer** `isTargetComp_of_mem_closure`: if a preconnected chart set `G` off the
  chart flow set contains the gate half-ball, then every flow point `η(u)` whose chart image lies in the closure of `G`
  is in the original right-target component of `ℍ ∖ (R(K_s) ∪ η([0, t]))` for every `t < u` — the physical image of
  `G` avoids the whole flow line, so it connects `η(u)` to a physical half-disc at the gate's positive real point.

Deterministic; nothing here replaces a source theorem.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv)

namespace InteractingSLE.Sec5.Prop51Tgt

open WangWu hiding ratPt exists_ratPt_dist_lt
open Prop51G Prop51HTopo

variable {η β : ℝ → ℂ} {w : ℝ → ℝ} {s : ℝ}

/-! ### A gate whose physical boundary value is near `0` -/

/-- **The boundary extension of `F_s` at a far negative real point is a far negative real** (the construction of
`Prop411Q.exists_neg_tendsto_fwdMapInv`, with the extra margin `|B|`): `F̄_s` maps real points left of the hull image to
real points and moves points by a bounded amount. -/
theorem exists_neg_tendsto_fwdMapInv_far (hβ : IsLoewnerTrace w β) (hw : Continuous w) (hw0 : w 0 = 0)
    (hs : 0 ≤ s) (B : ℝ) : ∃ ω₀ y₀ : ℝ, ω₀ < 0 ∧ y₀ < -|B| ∧
      Tendsto (fwdMapInv w s) (𝓝[H] (ω₀ : ℂ)) (𝓝 (y₀ : ℂ)) := by
  obtain ⟨C, -, hC⟩ := exists_norm_extendFrom_sub_le hβ hw hw0 hs
  set ω₀ : ℝ := min (-|C| - |B| - 1) (-MartChar.RealFlow.rightImg (fun r => -w r) 0 s - w s - 1) with hω₀
  have hω₀neg : ω₀ < 0 := (min_le_left _ _).trans_lt (by linarith [abs_nonneg C, abs_nonneg B])
  have hHbar : ((ω₀ : ℝ) : ℂ) ∈ Hbar := mem_Hbar_of_im_eq_zero (by simp)
  set F := extendFrom H (fwdMapInv w s) (ω₀ : ℂ) with hF
  have hFH : F ∉ H := fun h => by
    have := neg_rightImg_sub_lt_of_extendFrom_mem_H hβ hw hw0 hs (x := ω₀) h
    have h2 : ω₀ ≤ -MartChar.RealFlow.rightImg (fun r => -w r) 0 s - w s - 1 := min_le_right _ _
    linarith
  have hFim : F.im = 0 := by
    have h1 : 0 ≤ F.im := extendFrom_mem_Hbar hβ hw hw0 hs hHbar
    have h2 : ¬ 0 < F.im := hFH
    linarith [not_lt.1 h2]
  have hFre : F.re < -|B| := by
    have h1 := hC _ hHbar
    have h2 : |(F - (ω₀ : ℂ)).re| ≤ ‖F - (ω₀ : ℂ)‖ := abs_re_le_norm _
    simp only [sub_re, ofReal_re] at h2
    have h3 : ω₀ ≤ -|C| - |B| - 1 := min_le_left _ _
    have h4 := (abs_le.1 (h2.trans h1)).2
    linarith [le_abs_self C]
  refine ⟨ω₀, F.re, hω₀neg, hFre, ?_⟩
  have hFeq : F = ((F.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hFim])
  rw [← hFeq]
  exact (hβ.hasBdryLimits hw hw0 hs).tendsto hHbar

/-- **A free positive gate whose physical boundary value is below any given `δ > 0`** (the construction of
`Prop51HTopo.exists_positiveBoundaryGate` from `exists_neg_tendsto_fwdMapInv_far`). -/
theorem exists_positiveBoundaryGate_lt (hη : IsProperArc η) (hβ : IsLoewnerTrace w β) (hw : Continuous w)
    (hw0 : w 0 = 0) (hs : 0 ≤ s) {δ : ℝ} (hδ : 0 < δ) :
    ∃ g : PositiveBoundaryGate η w s, g.target < δ := by
  obtain ⟨q, y, hq, hy, hlim⟩ := exists_neg_tendsto_fwdMapInv_far hβ hw hw0 hs δ⁻¹
  let r : ℝ := -q⁻¹
  let x : ℝ := -y⁻¹
  have hy0 : y < 0 := hy.trans_le (neg_nonpos.2 (abs_nonneg _))
  have hr : 0 < r := neg_pos.2 (inv_lt_zero.2 hq)
  have hx : 0 < x := neg_pos.2 (inv_lt_zero.2 hy0)
  have hxδ : x < δ := by
    have hδ' : δ⁻¹ < -y := by rw [abs_of_pos (inv_pos.2 hδ)] at hy; linarith
    have hpos : 0 < -y := by linarith
    have := (inv_lt_comm₀ hpos hδ).2 hδ'
    simpa [x, inv_neg] using this
  have hrq : negInv (r : ℂ) = (q : ℂ) := by simp [negInv, r]
  have hinv : Tendsto negInv (𝓝[H] (r : ℂ)) (𝓝[H] (q : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have hc := (continuousAt_negInv (ofReal_ne_zero.2 hr.ne')).tendsto
      rw [hrq] at hc
      exact hc.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with z hz using negInv_mem_H hz
  have hF : Tendsto (revChartInv w s) (𝓝[H] (r : ℂ)) (𝓝[H] (x : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · change Tendsto (fun z => negInv (fwdMapInv w s (negInv z)))
        (𝓝[H] (r : ℂ)) (𝓝 (x : ℂ))
      have hc := (continuousAt_negInv (ofReal_ne_zero.2 hy0.ne)).tendsto.comp
        (hlim.comp hinv)
      simpa only [revChartInv, negInv, x, ofReal_neg, ofReal_inv,
        Function.comp_def] using hc
    · filter_upwards [self_mem_nhdsWithin] with z hz using (revChartInv_mem hw hw0 hs hz).1
  have hxA : (x : ℂ) ∉ arcRange η := hη.ofReal_notMem_arcRange hx.ne'
  have hfree : ∀ᶠ z in 𝓝[H] (r : ℂ), revChartInv w s z ∉ arcRange η :=
    (hF.mono_right nhdsWithin_le_nhds).eventually
      (hη.isClosed_arcRange.isOpen_compl.mem_nhds hxA)
  obtain ⟨ε, hε, havoid⟩ := Metric.mem_nhdsWithin_iff.1 hfree
  have hdis : Disjoint (ball (r : ℂ) ε) (chartFlowSet η w s) := by
    refine disjoint_left.2 ?_
    rintro z hzb ⟨p, hp, rfl⟩
    have hzH := revChart_mem_H hw hs hp.2
    have hn := havoid ⟨hzb, hzH⟩
    change revChartInv w s (revChart w s p) ∉ arcRange η at hn
    rw [revChartInv_revChart hw hw0 hs hp.2] at hn
    exact hn hp.1
  exact ⟨⟨r, x, ε, hr, hx, hε, hF, disjoint_iff_inter_eq_empty.1 (hdis.closure_right isOpen_ball)⟩, hxδ⟩

/-- **The counterflow hull stays away from `0` in the chart `Q`**: `R(K_s)` lies outside a ball about `0`
(`K_s` is bounded, `QuantumZipper.CaraR.fwdHull_subset_closedBall`). -/
theorem exists_pos_lt_norm_of_mem_cfHullQ (hw : Continuous w) (hs : 0 < s) :
    ∃ ρ > 0, ∀ z ∈ cfHullQ w s, ρ < ‖z‖ := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := s)).exists_bound_of_continuousOn hw.continuousOn
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 ⟨le_rfl, hs.le⟩)
  have hbound : ∀ r ∈ Icc (0 : ℝ) s, |w r| ≤ M := fun r hr => by
    simpa [Real.norm_eq_abs] using hM r hr
  have hsq : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
  set M' : ℝ := M + 3 * Real.sqrt s with hM'def
  have hM' : 0 < M' := by rw [hM'def]; positivity
  refine ⟨1 / (2 * M'), by positivity, fun z hz => ?_⟩
  obtain ⟨ζ, hζ, rfl⟩ := hz
  have hball := QuantumZipper.CaraR.fwdHull_subset_closedBall hw hs hbound hζ
  rw [Metric.mem_closedBall, dist_zero_right] at hball
  have hζH : ζ ∈ H := QuantumZipper.fwdHull_mono.2 _ hζ
  have hζ0 : ζ ≠ 0 := fun h0 => by
    rw [h0] at hζH
    exact lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from hζH)
  have hnpos : 0 < ‖ζ‖ := norm_pos_iff.2 hζ0
  have hnorm : ‖negInv ζ‖ = ‖ζ‖⁻¹ := by simp [negInv]
  rw [hnorm]
  have h1 : M'⁻¹ ≤ ‖ζ‖⁻¹ := inv_anti₀ hnpos hball
  have h2 : 1 / (2 * M') < M'⁻¹ := by
    rw [one_div, mul_inv]
    have : 0 < M'⁻¹ := inv_pos.2 hM'
    linarith
  linarith

/-! ### The target component reached from the gate's chart component -/

/-- **The target-component transfer.** Let `G` be a preconnected chart set off the chart flow set containing the
half-ball of a gate whose physical boundary value lies inside the ball of radius `ρ/2` about `0`, where `R(K_s)` lies
outside the ball of radius `ρ`. If the chart image of `η(u)` (`u > t ≥ 0`, `η(u) ∈ ℍ ∖ R(K_s)`) is in the closure of
`G`, then `η(u)` is in the original right-target component of `ℍ ∖ (R(K_s) ∪ η([0, t]))`. -/
theorem isTargetComp_of_mem_closure (hη : IsProperArc η) (hw : Continuous w) (hw0 : w 0 = 0) (hs : 0 ≤ s)
    (g : PositiveBoundaryGate η w s) {ρ : ℝ} (hρK : ∀ z ∈ cfHullQ w s, ρ < ‖z‖) (hgρ : g.target < ρ / 2)
    {G : Set ℂ} (hGc : IsPreconnected G) (hGA : G ⊆ H \ chartFlowSet η w s)
    (hGgate : ball (g.source : ℂ) g.radius ∩ H ⊆ G) {t u : ℝ} (ht : 0 ≤ t) (htu : t < u)
    (hu : η u ∈ H \ cfHullQ w s) (hcl : revChart w s (η u) ∈ closure G) :
    Aux61Kernel.IsTargetComp w s η t (η u) := by
  set X : Set ℂ := H \ (cfHullQ w s ∪ η '' Icc 0 t) with hXdef
  have hKc : IsCompact (η '' Icc 0 t) := isCompact_Icc.image_of_continuousOn (hη.cont.mono Icc_subset_Ici_self)
  have hXeq : X = (H \ cfHullQ w s) \ η '' Icc 0 t := by
    ext z
    simp only [hXdef, Set.mem_sdiff, Set.mem_union, not_or]
    tauto
  have hXo : IsOpen X := hXeq ▸ (isOpen_H_diff_negInv_fwdHull hw hs).sdiff hKc.isClosed
  set S : Set ℂ := revChartInv w s '' G with hSdef
  have hSX : S ⊆ X := by
    rintro _ ⟨z, hz, rfl⟩
    have hzH := (hGA hz).1
    have hm := revChartInv_mem hw hw0 hs hzH
    refine ⟨hm.1, ?_⟩
    rintro (h | ⟨v, hv, he⟩)
    · exact hm.2 h
    · apply (hGA hz).2
      refine ⟨η v, ⟨⟨v, mem_Ici.2 hv.1, rfl⟩, he ▸ hm⟩, ?_⟩
      rw [he, revChart_revChartInv hw hw0 hs hzH]
  have hSc : IsPreconnected S :=
    hGc.image _ ((continuousOn_revChartInv hw hw0 hs).mono fun z hz => (hGA hz).1)
  have huX : η u ∈ X := by
    refine ⟨hu.1, ?_⟩
    rintro (h | ⟨v, hv, he⟩)
    · exact hu.2 h
    · have := hη.inj (mem_Ici.2 hv.1) (mem_Ici.2 (ht.trans htu.le)) he
      linarith [hv.2]
  have hqH : revChart w s (η u) ∈ H := revChart_mem_H hw hs hu
  have huS : η u ∈ closure S := by
    have hc : ContinuousWithinAt (revChartInv w s) G (revChart w s (η u)) :=
      ((continuousOn_revChartInv hw hw0 hs).continuousAt
        (QuantumZipper.isOpen_H.mem_nhds hqH)).continuousWithinAt
    have := hc.mem_closure_image hcl
    rwa [revChartInv_revChart hw hw0 hs hu] at this
  -- the component of `η u` in `X` contains `S`
  have hcomp : S ⊆ connectedComponentIn X (η u) := by
    have hCo : IsOpen (connectedComponentIn X (η u)) := hXo.connectedComponentIn
    obtain ⟨p, hpC, hpS⟩ := (_root_.mem_closure_iff.1 huS) _ hCo (mem_connectedComponentIn huX)
    rw [connectedComponentIn_eq hpC]
    exact hSc.subset_connectedComponentIn hpS hSX
  -- a physical half-disc at the gate's boundary value lies in `X`
  have htX : (g.target : ℂ) ∉ η '' Icc 0 t := fun h =>
    hη.ofReal_notMem_arcRange g.target_pos.ne' (image_mono Icc_subset_Ici_self h)
  obtain ⟨ε₁, hε₁, hε₁K⟩ := Metric.isOpen_iff.1 hKc.isClosed.isOpen_compl _ htX
  set ε : ℝ := min ε₁ (ρ / 2) with hεdef
  have hρ : 0 < ρ / 2 := by linarith [g.target_pos]
  have hε : 0 < ε := lt_min hε₁ hρ
  have hPX : ball (g.target : ℂ) ε ∩ H ⊆ X := by
    intro y hy
    refine ⟨hy.2, ?_⟩
    rintro (h | h)
    · have h1 := hρK y h
      have h2 : ‖y - (g.target : ℂ)‖ < ε := by rw [← dist_eq_norm]; exact hy.1
      have h3 : ‖(g.target : ℂ)‖ = g.target := by
        rw [norm_real, Real.norm_eq_abs, abs_of_pos g.target_pos]
      have h4 : ‖y‖ ≤ ‖y - (g.target : ℂ)‖ + ‖(g.target : ℂ)‖ := norm_le_norm_sub_add y _
      have h5 : ε ≤ ρ / 2 := min_le_right _ _
      linarith
    · exact hε₁K (ball_subset_ball (min_le_left _ _) hy.1) h
  have hPc : IsPreconnected (ball (g.target : ℂ) ε ∩ H) :=
    ((convex_ball _ _).inter (convex_halfSpace_im_gt 0)).isPreconnected
  -- the half-disc meets `S`
  have : (𝓝[H] (g.source : ℂ)).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.1 (closure_H ▸ mem_Hbar_of_im_eq_zero (by simp))
  obtain ⟨z, hzP, hzG⟩ := ((g.boundary_limit.eventually_mem (inter_mem_nhdsWithin H (ball_mem_nhds _ hε))).and
    (inter_mem_nhdsWithin H (ball_mem_nhds (g.source : ℂ) g.radius_pos))).exists
  have hzS : revChartInv w s z ∈ S := ⟨z, hGgate ⟨hzG.2, hzG.1⟩, rfl⟩
  have hPcomp : ball (g.target : ℂ) ε ∩ H ⊆ connectedComponentIn X (η u) := by
    rw [connectedComponentIn_eq (hcomp hzS)]
    exact hPc.subset_connectedComponentIn ⟨hzP.2, hzP.1⟩ hPX
  refine ⟨g.target, g.target_pos, ?_⟩
  filter_upwards [inter_mem_nhdsWithin H (ball_mem_nhds (g.target : ℂ) hε)] with y hy
  exact hPcomp ⟨hy.2, hy.1⟩

end InteractingSLE.Sec5.Prop51Tgt
