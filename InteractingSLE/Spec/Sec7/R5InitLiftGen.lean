/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5FreshAnchor
import InteractingSLE.Spec.Sec7.R5LiftSeed

/-!
# Seed-interval landings and the side agreement for incident-component relative domains

Packet PROVE-R5-INIT (outer round; ruling R88). R5-LIFT's `R5Lift.landing_mem_hull_of_mem_seed_interval` and
R5-FRESHTIP's `R5Fresh.curSide_of_seedLand` assume that the relative domain is the **whole** cut pocket
`C ∩ (ℍ ∖ K)`; for an outer pocket it is only the component incident to the target (R88). Their proofs use the equality
only to place a point of `C ∖ K` near the landing inside the relative domain. That holds as soon as the relative
domain's frontier inside `C` lies in `K`: a connected piece of `C ∖ K` meeting the domain stays in it. The variants
below take this frontier condition (and the inclusion `dom ⊆ C ∩ (ℍ ∖ K)`), with the same proofs otherwise:

* **`landing_mem_hull_of_mem_seed_interval_of_frontier`**: coordinates strictly inside the seed interval land in `K`;
* **`exists_ball_landing_mem_hull_of_frontier`**: real points near a coordinate landing in `C` land in `K`;
* **`curSide_of_seedLand_of_frontier`**: the side agreement at the left stop from the seed-interval landings.

Ruling R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any result taking
them as hypotheses.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric Complex
open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv IsForwardSol)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R5Init

open PocketStop PocketTraversal Lemma71C PocketStopSide MartChar.RealFlow YuanSimpleApprox R5Lift R5Fresh

variable {Ω : Type*} {c : Ω → Chart} {γ : Ω → ℝ → ℂ} {ω : Ω}

/-- **Coordinates strictly inside the seed interval land in the hull**, for a relative domain whose frontier inside
the pocket lies in `K` (`R5Lift.landing_mem_hull_of_mem_seed_interval` without the domain identity). -/
theorem landing_mem_hull_of_mem_seed_interval_of_frontier {nL nR : ℕ} {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ}
    {iL : Fin nL} {iR : Fin nR} (hxL : xL ω iL = 0) (hxR : xR ω iR = 0) (hc : (c ω).IsConformal)
    (hγ : IsDrivenCurve (γ ω)) {Q : ℝ≥0} (hQ : (Q : ℝ≥0∞) < capLife (γ ω)) (hQ0 : 0 < Q)
    {E : ℂ → ℂ} (hE : EqOn E (c ω).2.1 H) (hEc : ContinuousOn E Hbar) {C K : Set ℂ}
    (hcdom : ((c ω).dom : Set ℂ) = C) (hKo : IsOpen (H \ K))
    (hfr : frontier ((relChart c γ Q ω).dom : Set ℂ) ∩ C ⊆ K) {u : ℝ}
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
  have hpcl : p ∈ closure ((relChart c γ Q ω).dom : Set ℂ) :=
    mem_closure_of_tendsto hland (eventually_nhdsWithin_of_forall fun y hy => hold.inv_mem_dom hy)
  have hpC : p ∉ C := fun hC => hpK (hfr ⟨by
    rw [(relChart c γ Q ω).dom.isOpen.frontier_eq]; exact ⟨hpcl, hpdom⟩, hC⟩)
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
  -- the half-disc's image is connected, misses `K`, and meets the relative domain
  have hSdom : ∀ z ∈ H ∩ ball b δ, (c ω).2.1 z ∈ ((relChart c γ Q ω).dom : Set ℂ) := by
    have hSc : IsPreconnected ((c ω).2.1 '' (H ∩ ball b δ)) :=
      ((convex_halfSpace_gt Complex.imLm.isLinear 0).inter (convex_ball b δ)).isPreconnected.image _
        (hc.1.continuousOn.mono inter_subset_left)
    have hSK : ∀ z ∈ H ∩ ball b δ, (c ω).2.1 z ∈ C ∧ (c ω).2.1 z ∉ K := by
      intro z hz
      have hEz := hδE z ⟨QuantumZipper.H_subset_Hbar hz.1, hz.2⟩
      rw [hE hz.1] at hEz
      exact ⟨hcdom ▸ hc.inv_mem_dom hz.1, (hball hEz).2⟩
    obtain ⟨y, hyH, hyb⟩ : ∃ y ∈ H, fwdMapInv W Q y ∈ ball b δ := by
      have hev : ∀ᶠ y in 𝓝[H] (u : ℂ), fwdMapInv W Q y ∈ ball b δ :=
        hbT (isOpen_ball.mem_nhds (mem_ball_self hδ))
      obtain ⟨y, hy1, hy2⟩ := (hev.and self_mem_nhdsWithin).exists
      exact ⟨y, hy2, hy1⟩
    have hydom : (c ω).2.1 (fwdMapInv W Q y) ∈ ((relChart c γ Q ω).dom : Set ℂ) := by
      have h := hold.inv_mem_dom hyH
      rw [hrel] at h ⊢
      exact h
    have hsub := hSc.subset_left_of_subset_union (relChart c γ Q ω).dom.isOpen isClosed_closure.isOpen_compl
      ((disjoint_compl_right (a := closure ((relChart c γ Q ω).dom : Set ℂ))).mono_left subset_closure)
      (by
        rintro _ ⟨z, hz, rfl⟩
        by_cases hd : (c ω).2.1 z ∈ ((relChart c γ Q ω).dom : Set ℂ)
        · exact Or.inl hd
        · refine Or.inr fun hcl => (hSK z hz).2 (hfr ⟨?_, (hSK z hz).1⟩)
          rw [(relChart c γ Q ω).dom.isOpen.frontier_eq]
          exact ⟨hcl, hd⟩)
      (show ((c ω).2.1 '' (H ∩ ball b δ) ∩ ((relChart c γ Q ω).dom : Set ℂ)).Nonempty from
        ⟨_, mem_image_of_mem _ ⟨hinvH y hyH, hyb⟩, hydom⟩)
    exact fun z hz => hsub (mem_image_of_mem _ hz)
  have hdisj : Disjoint (ball b δ) (fwdHull W Q) := by
    rw [Set.disjoint_left]
    intro z hzb hzK
    have hzH : z ∈ H := hzK.1
    have hEz := hδE z ⟨QuantumZipper.H_subset_Hbar hzH, hzb⟩
    rw [hE hzH] at hEz
    have hzC : (c ω).2.1 z ∈ ((relChart c γ Q ω).dom : Set ℂ) := hSdom z ⟨hzH, hzb⟩
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


/-- **Landings near a landing in `C` lie in the hull**, for a chart whose domain's frontier inside `C` lies in `K`
(`R5Lift.exists_ball_landing_mem_hull` without the domain identity). -/
theorem exists_ball_landing_mem_hull_of_frontier {ch : Chart} (hch : ch.IsConformal) {F : ℂ → ℂ}
    (hF : EqOn F ch.2.1 H) (hFc : ContinuousOn F Hbar) {C K : Set ℂ} (hCo : IsOpen C)
    (hfr : frontier (ch.dom : Set ℂ) ∩ C ⊆ K) {u : ℝ} (hu : F u ∈ C) :
    ∃ ρ > 0, ∀ v : ℝ, (v : ℂ) ∈ ball (u : ℂ) ρ → F v ∈ K := by
  have hubar : (u : ℂ) ∈ Hbar := show (0 : ℝ) ≤ (u : ℂ).im by rw [ofReal_im]
  have hmem : F ⁻¹' C ∈ 𝓝[Hbar] (u : ℂ) := (hFc _ hubar).preimage_mem_nhdsWithin (hCo.mem_nhds hu)
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhdsWithin_iff.1 hmem
  refine ⟨ρ, hρ, fun v hv => ?_⟩
  have hvbar : (v : ℂ) ∈ Hbar := show (0 : ℝ) ≤ (v : ℂ).im by rw [ofReal_im]
  have hvC : F v ∈ C := hball ⟨hv, hvbar⟩
  have hland : Tendsto ch.2.1 (𝓝[H] (v : ℂ)) (𝓝 (F v)) :=
    ((hFc _ hvbar).mono QuantumZipper.H_subset_Hbar).tendsto.congr'
      (eventually_nhdsWithin_of_forall fun y hy => hF hy)
  have hnot := landing_notMem_dom hch hland
  have := nhdsWithin_H_neBot v
  have hcl : F v ∈ closure (ch.dom : Set ℂ) :=
    mem_closure_of_tendsto hland (eventually_nhdsWithin_of_forall fun y hy => hch.inv_mem_dom hy)
  refine hfr ⟨?_, hvC⟩
  rw [ch.dom.isOpen.frontier_eq]
  exact ⟨hcl, hnot⟩

/-- **The side agreement at the left stop from the seed-interval landings alone**, for relative domains contained in
`C ∩ (ℍ ∖ K_{T(q')})` whose frontier inside `C` at `q` lies in `K_{T(q)}` (`R5Fresh.curSide_of_seedLand` without the
domain identity). -/
theorem curSide_of_seedLand_of_frontier {nL nR : ℕ} {xL : Ω → Fin (nL + 1) → ℝ} {xR : Ω → Fin (nR + 1) → ℝ}
    (hxL : xL ω 0 = 0) (hxR : xR ω 0 = 0) (hc : (c ω).IsConformal) (hγ : IsDrivenCurve (γ ω)) {q : ℝ≥0}
    (hq : (q : ℝ≥0∞) < capLife (γ ω)) (hq0 : 0 < q) {E : ℂ → ℂ} (hE : EqOn E (c ω).2.1 H)
    (hEc : ContinuousOn E Hbar) {C : Set ℂ} (hcdom : ((c ω).dom : Set ℂ) = C) {W : ℝ → ℝ} {η : ℝ → ℂ}
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ≥0 → ℝ} (hT0 : ∀ q', 0 ≤ T q')
    (hsubq : ∀ q' : ℝ≥0, q' ≤ q → ((relChart c γ q' ω).dom : Set ℂ) ⊆ C ∩ (H \ fwdHull W (T q')))
    (hfrq : frontier ((relChart c γ q ω).dom : Set ℂ) ∩ C ⊆ fwdHull W (T q))
    (hsel : ∀ t₀ < T q, ∃ q' : ℝ≥0, q' < q ∧ t₀ < T q' ∧ T q' ≤ T q)
    (hN1 : ∀ u ∈ Ioo (geomLW (fun t ω => segDriver (γ ω) t) xL 0 q ω - segDriver (γ ω) q)
      (geomRW (fun t ω => segDriver (γ ω) t) xR 0 q ω - segDriver (γ ω) q),
      extendFrom H (relChart c γ q ω).2.1 u ∈ H) :
    ∀ u ∈ Ioo (geomLW (fun t ω => segDriver (γ ω) t) xL 0 q ω - segDriver (γ ω) q)
      (geomRW (fun t ω => segDriver (γ ω) t) xR 0 q ω - segDriver (γ ω) q), ∀ y : ℝ,
      Tendsto (fun z => fwdMap W (T q) ((relChart c γ q ω).2.1 z)) (𝓝[H] (u : ℂ)) (𝓝 (y : ℂ)) →
        (u < 0 ↔ y < 0) := by
  set I := Ioo (geomLW (fun t ω => segDriver (γ ω) t) xL 0 q ω - segDriver (γ ω) q)
    (geomRW (fun t ω => segDriver (γ ω) t) xR 0 q ω - segDriver (γ ω) q) with hI
  have hTq := hT0 q
  have hcur := PocketStopSide.isConformal_relChart_of_driven (c := c) hγ hq hc
  obtain ⟨Fc, hFc, hFcc, -⟩ := PocketStopSide.exists_relative_inverse_extension (c := c) (γ := γ) hγ hq hE hEc
  have hK : ((relChart c γ q ω).dom : Set ℂ) ⊆ H \ fwdHull W (T q) := (hsubq q le_rfl).trans inter_subset_right
  have hKo := QuantumZipper.FwdHolo.isOpen_compl_fwdHull hW hTq
  have hland : ∀ u ∈ I, Fc u ∈ fwdHull W (T q) := by
    intro u hu
    obtain ⟨hlim, hFu⟩ := R5Lift.tendsto_of_ext hFc hFcc u
    refine landing_mem_hull_of_mem_seed_interval_of_frontier hxL hxR hc hγ hq hq0 hE hEc hcdom hKo hfrq hu hlim ?_
    rw [hFu]; exact hN1 u hu
  -- the relative chain as a continuous Loewner trace
  obtain ⟨V, γ₁, q₁, hqq₁, hV, hV0, htr, hVeq⟩ := exists_isLoewnerTrace_of_driven hγ hq
  have hrel : ∀ q' : ℝ≥0, q' ≤ q → relChart c γ q' ω = (c ω).loewner V q' := fun q' hq' =>
    loewner_congr (c ω) q'.coe_nonneg (lt_of_le_of_lt (NNReal.coe_le_coe.2 hq') hqq₁) hVeq
  have hEqV : EqOn (fun r : ℝ => (fun t ω => segDriver (γ ω) t) r.toNNReal ω) V (Icc 0 (q : ℝ)) :=
    fun r hr => hVeq r ⟨hr.1, hr.2.trans hqq₁.le⟩
  obtain ⟨hLeq, hReq⟩ := geom_positions_eq_of_driver_eqOn (fun t ω => segDriver (γ ω) t) xL xR hV hEqV
  have hL' := congrFun hLeq 0
  have hR' := congrFun hReq 0
  simp only [hxL, hxR, neg_zero] at hL' hR'
  have hB := htr.hasBdryLimits hV hV0 q.coe_nonneg
  have hout : ∀ u : ℝ, u ∉ I → extendFrom H (fwdMapInv V q) u ∉ H := by
    intro u hu hmem
    apply hu
    rw [hI, hL', hR']
    exact ⟨SideHeight.neg_rightImg_sub_lt_of_extendFrom_mem_H' hB hV hV0 q.coe_nonneg hmem,
      SideHeight.lt_rightImg_sub_of_extendFrom_mem_H' hB hV hV0 q.coe_nonneg hmem⟩
  -- the anchor
  have hanch : ∀ ε > 0, ∀ δ > 0, ∃ u ∈ I, |u| < δ ∧ ∀ y : ℝ,
      Tendsto (fun z => fwdMap W (T q) ((relChart c γ q ω).2.1 z)) (𝓝[H] (u : ℂ)) (𝓝 (y : ℂ)) → |y| < ε := by
    intro ε hε δ hδ
    obtain ⟨η₀, hη₀, hWc⟩ := Metric.continuous_iff.1 hW (T q) (ε / 100) (by positivity)
    set κ := min η₀ ((ε / 100) ^ 2) with hκ
    have hκ0 : 0 < κ := lt_min hη₀ (by positivity)
    have hκ1 := min_le_left η₀ ((ε / 100) ^ 2)
    have hκ2 := min_le_right η₀ ((ε / 100) ^ 2)
    obtain ⟨q', hq'q, ht₀, hTq'⟩ := hsel (T q - κ / 2) (by linarith)
    have hq'q' : (q' : ℝ) < q := by exact_mod_cast hq'q
    have hq'live : (q' : ℝ≥0∞) < capLife (γ ω) := lt_trans (by exact_mod_cast hq'q) hq
    have hM : ∀ r ∈ Icc (0 : ℝ) (T q - T q'), |W (T q' + r) - W (T q')| ≤ ε / 50 := by
      intro r hr
      have h1 : dist (T q' + r) (T q) < η₀ := by
        rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hr.1, hr.2]
      have h2 : dist (T q') (T q) < η₀ := by
        rw [Real.dist_eq, abs_lt]; constructor <;> linarith
      have e1 := hWc _ h1
      have e2 := hWc _ h2
      rw [Real.dist_eq] at e1 e2
      calc |W (T q' + r) - W (T q')| = |(W (T q' + r) - W (T q)) - (W (T q') - W (T q))| := by ring_nf
        _ ≤ |W (T q' + r) - W (T q)| + |W (T q') - W (T q)| := abs_sub _ _
        _ ≤ ε / 50 := by linarith
    have hsq : Real.sqrt (T q - T q') ≤ ε / 100 := by
      have h1 : Real.sqrt (T q - T q') ≤ Real.sqrt ((ε / 100) ^ 2) := Real.sqrt_le_sqrt (by linarith)
      rwa [Real.sqrt_sq (by positivity)] at h1
    obtain ⟨u, hu, huδ, hgH⟩ := exists_trMap_mem_H htr hV hV0 q'.coe_nonneg hq'q' hout hδ
    refine ⟨u, hu, huδ, fun y hy => ?_⟩
    have hcur' := PocketStopSide.isConformal_relChart_of_driven (c := c) hγ hq'live hc
    set w₀ := trMap V q' q u with hw₀
    set p := (relChart c γ q' ω).2.1 w₀ with hp
    have hpdom : p ∈ C ∩ (H \ fwdHull W (T q')) := hsubq q' hq'q.le (hcur'.inv_mem_dom hgH)
    have hpH : p ∈ H := hpdom.2.1
    have hubar : (u : ℂ) ∈ Hbar := show (0 : ℝ) ≤ (u : ℂ).im by rw [ofReal_im]
    have hlimp : Tendsto (relChart c γ q ω).2.1 (𝓝[H] (u : ℂ)) (𝓝 p) := by
      have h1 : Tendsto (trMap V q' q) (𝓝[H] (u : ℂ)) (𝓝[H] w₀) := tendsto_nhdsWithin_iff.2
        ⟨((trMap_continuousOn htr hV hV0 q'.coe_nonneg hq'q'.le _ hubar).mono QuantumZipper.H_subset_Hbar).tendsto,
          eventually_nhdsWithin_of_forall fun z hz => trMap_mem_H hV hq'q'.le hz⟩
      have h2 : ContinuousWithinAt (relChart c γ q' ω).2.1 H w₀ := hcur'.1.continuousOn w₀ hgH
      refine (h2.tendsto.comp h1).congr' (eventually_nhdsWithin_of_forall fun z hz => ?_)
      simp only [Function.comp_apply]
      rw [hrel q le_rfl, hrel q' hq'q.le]
      show (c ω).2.1 (fwdMapInv V q' (trMap V q' q z)) = (c ω).2.1 (fwdMapInv V q z)
      rw [trMap_eq_fwdMapInv hV hq'q'.le hz,
        ← QuantumZipper.RS.fwdMapInv_add_shift hV hV0 q'.coe_nonneg (sub_nonneg.2 hq'q'.le) hz, add_sub_cancel]
    have hpT : p ∈ fwdHull W (T q) :=
      landing_mem_hull_of_mem_seed_interval_of_frontier hxL hxR hc hγ hq hq0 hE hEc hcdom hKo hfrq hu hlimp hpH
    have hF : ∀ᶠ z in 𝓝[H] (u : ℂ), (relChart c γ q ω).2.1 z ∈ H \ fwdHull W (T q) :=
      eventually_nhdsWithin_of_forall fun z hz => hK (hcur.inv_mem_dom hz)
    have := R5Lift.nhdsWithin_H_neBot u
    have hb := norm_le_of_tendsto_increment hW (hT0 q') hTq' hM hF hlimp hpdom.2 hpT hy
    rw [Complex.norm_real, Real.norm_eq_abs] at hb
    linarith
  exact side_of_anchor hcur hFc hFcc hη hW hW0 hTq hK hland hanch

end InteractingSLE.Sec7.R5Init
