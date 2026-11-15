/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5LiftHull2
import InteractingSLE.Spec.ZhanGT4.TwoTime2Flow
import InteractingSLE.Spec.ZhanGT4.CrosscutInterior
import InteractingSLE.WangWu.ReverseContactBdryChart

/-!
# Lemma R.5's common phase: coordinates inside the seed interval land in the hull

Packet PROVE-R5-LIFT (round 4). For a relative chart whose domain is `C ∩ (ℍ ∖ K)` (an interior-visit reference:
`C` the pocket, `K` the ambient hull at the visit time), every real coordinate strictly between the seed images whose
landing lies in `ℍ` lands in `K` (**`landing_mem_hull_of_mem_seed_interval`**).

Proof: if the landing `p ∈ ℍ` missed `K`, a ball about `p` misses `K`; `p` is not in the domain (a real coordinate's
landing), so `p ∉ C`; hence the base landing `b` of the relative Loewner map is real (an interior `b` lands in `C`);
by continuity of the base inverse extension, a half-disc about `b` maps into the ball, hence avoids the relative hull,
so `b ≠ 0` is alive (`ZhanGT4.exists_isForwardSol_of_disjoint_ball`); `f_Q` is continuous at `b` (alive disc), so the
coordinate is the centred image of `b`, which lies at or beyond a seed image
(`WangWu.rightImg_sub_le_re_fwdMap`, `WangWu.re_fwdMap_le_neg_rightImg`) — a contradiction.

Ruling R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any result taking
them as hypotheses.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric Complex
open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv IsForwardSol)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R5Lift

open PocketStop PocketTraversal Lemma71C PocketStopSide MartChar.RealFlow

variable {Ω : Type*} {c : Ω → Chart} {γ : Ω → ℝ → ℂ} {ω : Ω}

/-- **Coordinates strictly inside the seed interval land in the hull.** -/
theorem landing_mem_hull_of_mem_seed_interval {nL nR : ℕ} {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ}
    {iL : Fin nL} {iR : Fin nR} (hxL : xL ω iL = 0) (hxR : xR ω iR = 0) (hc : (c ω).IsConformal)
    (hγ : IsDrivenCurve (γ ω)) {Q : ℝ≥0} (hQ : (Q : ℝ≥0∞) < capLife (γ ω)) (hQ0 : 0 < Q)
    {E : ℂ → ℂ} (hE : EqOn E (c ω).2.1 H) (hEc : ContinuousOn E Hbar) {C K : Set ℂ}
    (hcdom : ((c ω).dom : Set ℂ) = C) (hKo : IsOpen (H \ K))
    (hdom : ((relChart c γ Q ω).dom : Set ℂ) = C ∩ (H \ K)) {u : ℝ}
    (hu : u ∈ Ioo (geomLW (fun t ω => segDriver (γ ω) t) xL iL Q ω - segDriver (γ ω) Q)
      (geomRW (fun t ω => segDriver (γ ω) t) xR iR Q ω - segDriver (γ ω) Q)) {p : ℂ}
    (hland : Tendsto (relChart c γ Q ω).2.1 (𝓝[H] (u : ℂ)) (𝓝 p)) (hpH : p ∈ H) : p ∈ K := by
  obtain ⟨W, hW, hW0, q', hqq', hWeq, hrel⟩ := exists_relChart_eq_loewner (c := c) hγ hQ
  have hB := hasBdryLimits_relChart_driver hγ hQ hW hW0 hqq' hWeq
  have hQ0' : (0 : ℝ) ≤ Q := Q.coe_nonneg
  have hold : (relChart c γ Q ω).IsConformal := isConformal_relChart_of_driven hγ hQ hc
  have := nhdsWithin_H_neBot u
  -- the seed positions in the local driver
  have hEq : EqOn (fun r : ℝ => (fun t ω => segDriver (γ ω) t) r.toNNReal ω) W (Icc 0 (Q : ℝ)) :=
    fun r hr => hWeq r ⟨hr.1, hr.2.trans hqq'.le⟩
  obtain ⟨hLeq, hReq⟩ := geom_positions_eq_of_driver_eqOn (fun t ω => segDriver (γ ω) t) xL xR hW hEq
  have hL' := congrFun hLeq iL
  have hR' := congrFun hReq iR
  simp only [hxL, hxR, neg_zero] at hL' hR'
  rw [hL', hR'] at hu
  -- the base landing
  have hubar : (u : ℂ) ∈ Hbar := show (0 : ℝ) ≤ (u : ℂ).im by rw [ofReal_im]
  set b := extendFrom H (fwdMapInv W Q) u with hbdef
  have hbT : Tendsto (fwdMapInv W Q) (𝓝[H] (u : ℂ)) (𝓝 b) := hB.tendsto hubar
  have hinvH : ∀ y ∈ H, fwdMapInv W Q y ∈ H := fun y hy => QuantumZipper.RS.fwdMapInv_mem_H hW hW0 hQ0' hy
  have hbbar : b ∈ Hbar := by
    rw [← show closure H = Hbar from Complex.closure_setOfPred_lt_im 0]
    exact mem_closure_of_tendsto hbT (eventually_nhdsWithin_of_forall hinvH)
  have hEb : Tendsto (fun y => E (fwdMapInv W Q y)) (𝓝[H] (u : ℂ)) (𝓝 (E b)) :=
    (hEc b hbbar).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hbT, eventually_nhdsWithin_of_forall fun y hy =>
      QuantumZipper.H_subset_Hbar (hinvH y hy)⟩)
  have hpE : p = E b := by
    refine tendsto_nhds_unique hland (hEb.congr' (eventually_nhdsWithin_of_forall fun y hy => ?_))
    rw [hrel]
    exact hE (hinvH y hy)
  by_contra hpK
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hKo p ⟨hpH, hpK⟩
  -- `p` is not in `C`
  have hpdom := landing_notMem_dom hold hland
  have hpC : p ∉ C := fun hC => hpdom (by rw [hdom]; exact ⟨hC, hball (mem_ball_self hε)⟩)
  -- the base landing is real
  have hbim : b.im = 0 := by
    by_contra hne
    have hbH : b ∈ H := lt_of_le_of_ne (show (0 : ℝ) ≤ b.im from hbbar) (Ne.symm hne)
    apply hpC
    rw [hpE, hE hbH, ← hcdom]
    exact hc.inv_mem_dom hbH
  -- a half-disc about `b` avoids the relative hull
  obtain ⟨δ, hδ, hδE⟩ : ∃ δ > 0, ∀ z ∈ Hbar ∩ ball b δ, E z ∈ ball p ε := by
    have hmem : E ⁻¹' ball p ε ∈ 𝓝[Hbar] b := (hEc b hbbar).preimage_mem_nhdsWithin
      (isOpen_ball.mem_nhds (by rw [← hpE]; exact mem_ball_self hε))
    obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhdsWithin_iff.1 hmem
    exact ⟨δ, hδ, fun z hz => hsub ⟨hz.2, hz.1⟩⟩
  have hdisj : Disjoint (ball b δ) (fwdHull W Q) := by
    rw [Set.disjoint_left]
    intro z hzb hzK
    have hzH : z ∈ H := hzK.1
    have hEz := hδE z ⟨QuantumZipper.H_subset_Hbar hzH, hzb⟩
    rw [hE hzH] at hEz
    have hzC : (c ω).2.1 z ∈ ((relChart c γ Q ω).dom : Set ℂ) := by
      rw [hdom, ← hcdom]
      exact ⟨hc.inv_mem_dom hzH, hball hEz⟩
    rw [hold.coe_dom, hrel] at hzC
    obtain ⟨w, hwH, hw⟩ := hzC
    have hw' : (c ω).2.1 (fwdMapInv W Q w) = (c ω).2.1 z := hw
    have hzw := hc.injOn (hinvH w hwH) hzH hw'
    have hwK : fwdMapInv W Q w ∈ H \ fwdHull W Q := QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hW hW0 hQ0' hwH
    exact hwK.2 (hzw ▸ hzK)
  have hbr : b = (b.re : ℂ) := Complex.ext (by simp) (by simp [hbim])
  have hb0 : b.re ≠ 0 := by
    intro h0
    have h0' : b = 0 := by rw [hbr, h0, ofReal_zero]
    have hcl := ConformalImageFull.zero_mem_closure_fwdHull hW hW0 (show (0 : ℝ) < Q from hQ0)
    rw [Metric.mem_closure_iff] at hcl
    obtain ⟨z, hzK, hz⟩ := hcl δ hδ
    exact Set.disjoint_left.1 hdisj (show z ∈ ball b δ by rw [h0', mem_ball, dist_comm]; exact hz) hzK
  obtain ⟨v, hv⟩ := ZhanGT4.exists_isForwardSol_of_disjoint_ball hW hW0 hb0 hQ0' hδ (hbr ▸ hdisj)
  -- the coordinate is the centred image of `b`
  obtain ⟨δ', hδ', hlow⟩ := exists_two_mul_le_norm_of_isForwardSol hQ0' hv
  have hcontf : ContinuousAt (fwdMap W Q) (b.re : ℂ) := by
    have h1 := ZhanGT4.continuousOn_fwdMap_aliveDisc hW hv hδ' hlow
    have h2 : ContinuousWithinAt (fun q : ℝ × ℂ => fwdMap W q.1 q.2) (Icc 0 (Q : ℝ) ×ˢ ball (b.re : ℂ)
        (ZhanGT4.aliveRad Q δ')) ((Q : ℝ), (b.re : ℂ)) :=
      h1 _ ⟨⟨hQ0', le_rfl⟩, mem_ball_self (ZhanGT4.aliveRad_pos hδ')⟩
    have h3 : ContinuousWithinAt (fwdMap W Q) (ball (b.re : ℂ) (ZhanGT4.aliveRad Q δ')) (b.re : ℂ) := by
      have hpair : ContinuousWithinAt (fun z : ℂ => ((Q : ℝ), z)) (ball (b.re : ℂ) (ZhanGT4.aliveRad Q δ'))
          (b.re : ℂ) := (continuous_const.prodMk continuous_id).continuousWithinAt
      exact h2.comp hpair fun z hz => ⟨⟨hQ0', le_rfl⟩, hz⟩
    exact h3.continuousAt (isOpen_ball.mem_nhds (mem_ball_self (ZhanGT4.aliveRad_pos hδ')))
  have hu_eq : (u : ℂ) = fwdMap W Q (b.re : ℂ) := by
    have h1 : Tendsto (fun y => fwdMap W Q (fwdMapInv W Q y)) (𝓝[H] (u : ℂ)) (𝓝 (fwdMap W Q (b.re : ℂ))) :=
      hcontf.tendsto.comp (hbr ▸ hbT)
    have h2 : Tendsto (fun y : ℂ => y) (𝓝[H] (u : ℂ)) (𝓝 (fwdMap W Q (b.re : ℂ))) :=
      h1.congr' (eventually_nhdsWithin_of_forall fun y hy => QuantumZipper.RS.fwdMap_fwdMapInv hW hW0 hQ0' hy)
    exact tendsto_nhds_unique ((tendsto_id (x := 𝓝 (u : ℂ))).mono_left nhdsWithin_le_nhds) h2
  have hure : u = (fwdMap W Q (b.re : ℂ)).re := by rw [← hu_eq, ofReal_re]
  rcases lt_or_gt_of_ne hb0 with hneg | hpos
  · have := WangWu.re_fwdMap_le_neg_rightImg hW hW0 hQ0' hneg hv
    rw [← hure] at this
    exact absurd hu.1 (not_lt.2 this)
  · have := WangWu.rightImg_sub_le_re_fwdMap hW hW0 hQ0' hpos hv
    rw [← hure] at this
    exact absurd hu.2 (not_lt.2 this)

end InteractingSLE.Sec7.R5Lift
