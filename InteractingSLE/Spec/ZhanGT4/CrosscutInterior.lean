/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.CrosscutJordan
import InteractingSLE.Spec.ZhanGT4.FirstSwallowSide
import InteractingSLE.Foundations.Loewner.ConformalImageFullClearance
import InteractingSLE.Spec.Dimension.TraceBridge

/-!
# A hull bounded by a crosscut: its inverse map is interior on the open inverse interval

Packet PROVE-ZHAN-GT4-A2. Source: Astra, *Follow-up proofs and dependency audit*, §A.4.2
(`source/external/AstraIG1/ig1_followup_proofs.txt` L743–L777, ruling R38): at the first swallowing time of `−n`
the hull "has a simple crosscut boundary, by §A.3 … the displayed coordinates … lie strictly inside the new hull
interval … The right side is therefore the restriction of a simple interior boundary arc".

## Main results

* `exists_isForwardSol_of_disjoint_ball`: a nonzero real point with a disc around it disjoint from the hull `K_T`
  is alive at `T` (the clearance of `ConformalImageFull.exists_clearance_real` keeps the flows of nearby points away
  from the driver, while the real flow of a swallowed point tends to the driver).
* `isCrosscutDomain_of_frontier`: if `∂(ℍ \ K_σ) ∩ ℍ` is the open part of a simple crosscut, `ℍ \ K_σ` is a
  crosscut domain.
* `mem_H_of_frontier_eq_crosscut`: **the open inverse interval goes into `ℍ`.** If moreover `γ 0 < 0 < γ 1` and `F`
  is the continuous extension of `f_σ = g_σ⁻¹(W_σ + ·)` to `ℍ̄`, then `F v ∈ ℍ` for every real `v` off the exterior
  coordinates. Proof: a real value `x = F v` cannot lie strictly inside `(γ 0, γ 1)` (a half-disc there is inside
  the hull); outside `[γ 0, γ 1]` it is alive and `v = g_σ(x) − W_σ` would be an exterior coordinate; and
  `x ∈ {γ 0, γ 1}` is also the value of `F` at an exterior coordinate (a limit of alive points), contradicting the
  boundary injectivity `IsCrosscutDomain.false_of_eq`.
* `injective_of_frontier_eq_crosscut`: under the same hypotheses `F` is injective on `ℝ`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric Bornology

namespace InteractingSLE.ZhanGT4

open QuantumZipper

variable {W : ℝ → ℝ}

/-! ### Alive real points -/

/-- The real flow of a swallowed negative point tends to the driver (reflection of
`tendsto_fwdMap_of_realSwallowAt`). -/
theorem tendsto_fwdMap_of_realSwallowAt_neg (hW : Continuous W) (hW0 : W 0 = 0) {x σ : ℝ} (hx : x < 0)
    (h : RealSwallowAt W x σ) : Tendsto (fun s => fwdMap W s x) (𝓝[<] σ) (𝓝 0) := by
  have h' : RealSwallowAt (fun t => -W t) (-x) σ := realSwallowAt_neg_iff.2 h
  have ht := tendsto_fwdMap_of_realSwallowAt (W := fun t => -W t) hW.neg (by simp [hW0]) (neg_pos.2 hx) h'
  have hev : (fun s => fwdMap W s x) =ᶠ[𝓝[<] σ] fun s => -fwdMap (fun t => -W t) s ((-x : ℝ) : ℂ) := by
    have hpos : ∀ᶠ s in 𝓝[<] σ, 0 ≤ s := by
      have : Ioo 0 σ ∈ 𝓝[<] σ := Ioo_mem_nhdsLT h.1
      filter_upwards [this] with s hs using hs.1.le
    filter_upwards [hpos, self_mem_nhdsWithin] with s hs0 hsσ
    obtain ⟨v, hv⟩ := h.2.1 s ⟨hs0, hsσ⟩
    rw [fwdMap_neg_real hW hv ⟨hs0, le_rfl⟩, neg_neg]
  have := ht.neg
  rw [neg_zero] at this
  exact this.congr' hev.symm

/-- **A real point with a disc outside the hull is alive.** If `x ≠ 0` and `B(x, r)` misses `K_T`, the centered
real flow from `x` exists on `[0, T]`. -/
theorem exists_isForwardSol_of_disjoint_ball (hW : Continuous W) (hW0 : W 0 = 0) {x : ℝ} (hx : x ≠ 0) {T r : ℝ}
    (hT : 0 ≤ T) (hr : 0 < r) (hd : Disjoint (ball (x : ℂ) r) (fwdHull W T)) :
    ∃ v, IsForwardSol W (x : ℂ) T v := by
  by_contra hdead
  obtain ⟨σ, hσ, hsw⟩ : ∃ σ ∈ Ioc 0 T, RealSwallowAt W x σ := by
    rcases lt_or_gt_of_ne hx with h | h
    · exact exists_realSwallowAt_of_neg hW hW0 h hT hdead
    · exact exists_realSwallowAt hW hW0 h hT hdead
  have htend : Tendsto (fun s => fwdMap W s x) (𝓝[<] σ) (𝓝 0) := by
    rcases lt_or_gt_of_ne hx with h | h
    · exact tendsto_fwdMap_of_realSwallowAt_neg hW hW0 h hsw
    · exact tendsto_fwdMap_of_realSwallowAt hW hW0 h hsw
  obtain ⟨ρ, hρ, s, hs, hcl⟩ := ConformalImageFull.exists_clearance_real hW hW0 hT hr hd hx
  have hlow : ∀ t ∈ Ico (0 : ℝ) σ, ρ ≤ ‖fwdMap W t x‖ := by
    intro t ht
    obtain ⟨u, hu⟩ := hsw.2.1 t ht
    have hlim := tendsto_fwdMap_of_isForwardSol hW ht.1 hu
    rw [fwdMap_eq_of_isForwardSol hW hu ⟨ht.1, le_rfl⟩]
    have := FiniteEndpoint.neBot_nhdsWithin_H (z := (x : ℂ)) (by simp)
    refine ge_of_tendsto hlim.norm ?_
    have hmem : ball (x : ℂ) s ∈ 𝓝 (x : ℂ) := ball_mem_nhds _ hs
    filter_upwards [inter_mem_nhdsWithin H hmem] with a ha
    exact hcl t ⟨ht.1, ht.2.le.trans hσ.2⟩ a ⟨ha.2, ha.1⟩
  have hev : ∀ᶠ t in 𝓝[<] σ, ‖fwdMap W t x‖ < ρ := by
    have := htend.norm
    rw [norm_zero] at this
    exact this.eventually (gt_mem_nhds hρ)
  have hpos : ∀ᶠ t in 𝓝[<] σ, t ∈ Ico (0 : ℝ) σ := by
    filter_upwards [Ioo_mem_nhdsLT hσ.1] with t ht using ⟨ht.1.le, ht.2⟩
  obtain ⟨t, ht1, ht2⟩ := (hev.and hpos).exists
  exact absurd (hlow t ht2) (not_le.2 ht1)

/-! ### The hull at a time whose frontier is a crosscut -/

theorem exists_abs_le_of_continuous (hW : Continuous W) (T : ℝ) : ∃ M : ℝ, ∀ r ∈ Icc (0 : ℝ) T, |W r| ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_Icc.image_of_continuousOn hW.continuousOn).isBounded.subset_closedBall 0
  exact ⟨M, fun r hr => by
    have := hM (mem_image_of_mem W hr)
    rwa [mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this⟩

/-- `ℍ \ K_σ` is a crosscut domain when its frontier in `ℍ` is the open part of a simple crosscut. -/
theorem isCrosscutDomain_of_frontier (hW : Continuous W) (hW0 : W 0 = 0) {σ : ℝ} (hσ : 0 < σ)
    {γ : ℝ → ℂ} (hγ : IsRealCrosscut γ) (hlt : (γ 0).re < (γ 1).re)
    (hfr : frontier (H \ fwdHull W σ) ∩ H = γ '' Ioo 0 1) : IsCrosscutDomain (H \ fwdHull W σ) γ where
  isOpen := FwdHolo.isOpen_compl_fwdHull hW hσ.le
  subset_H := fun z hz => hz.1
  isPreconnected := by
    rw [← RS.image_fwdMapInv_H hW hW0 hσ.le]
    exact (convex_halfSpace_gt (f := fun z : ℂ => z.im) Complex.imLm.isLinear 0).isPreconnected.image _
      (RS.differentiableOn_fwdMapInv hW hW0 hσ.le).continuousOn
  far := by
    obtain ⟨M, hM⟩ := exists_abs_le_of_continuous hW σ
    refine ⟨M + 3 * Real.sqrt σ, fun z hz hzR => ⟨hz, fun hzK => ?_⟩⟩
    have := CaraR.fwdHull_subset_closedBall hW hσ hM hzK
    rw [mem_closedBall, dist_zero_right] at this
    linarith
  crosscut := hγ
  re_lt := hlt
  frontier_inter := hfr

/-- **Points outside `[γ 0, γ 1]` are alive** at a time whose hull is bounded by the crosscut `γ`. -/
theorem exists_isForwardSol_of_crosscut (hW : Continuous W) (hW0 : W 0 = 0) {σ : ℝ} (hσ : 0 < σ)
    {γ : ℝ → ℂ} (hD : IsCrosscutDomain (H \ fwdHull W σ) γ) (h0 : (γ 0).re < 0) (h1 : 0 < (γ 1).re)
    {x : ℝ} (hx : x < (γ 0).re ∨ (γ 1).re < x) : ∃ u, IsForwardSol W (x : ℂ) σ u := by
  obtain ⟨δ, hδ, hball⟩ := hD.exists_ball_inter_H_subset hx
  have hx0 : x ≠ 0 := by rcases hx with h | h <;> intro hx0 <;> rw [hx0] at h <;> linarith
  refine exists_isForwardSol_of_disjoint_ball hW hW0 hx0 hσ.le hδ (Set.disjoint_left.2 fun z hz hzK => ?_)
  exact (hball ⟨hz, hzK.1⟩).2 hzK

/-- If the boundary value of `F = f_σ` at a real `v` is an alive real point `x`, then `v = g_σ(x) − W_σ`. -/
theorem alive_coord_eq (hW : Continuous W) (hW0 : W 0 = 0) {σ : ℝ} (hσ : 0 < σ) {F : ℂ → ℂ}
    (hFeq : EqOn F (fwdMapInv W σ) H) (hFD : ∀ w ∈ H, F w ∈ H \ fwdHull W σ) {v x : ℝ}
    (hlim : Tendsto F (𝓝[H] (v : ℂ)) (𝓝 (F v))) (hFvx : F v = (x : ℂ)) {u : ℝ → ℂ}
    (hu : IsForwardSol W (x : ℂ) σ u) : (fwdMap W σ x).re = v := by
  have hneb : (𝓝[H] (v : ℂ)).NeBot := FiniteEndpoint.neBot_nhdsWithin_H (by simp)
  have hF' : Tendsto F (𝓝[H] (v : ℂ)) (𝓝[H] (x : ℂ)) :=
    tendsto_nhdsWithin_iff.2 ⟨hFvx ▸ hlim, eventually_nhdsWithin_of_forall fun w hw => (hFD w hw).1⟩
  have h1 := (tendsto_fwdMap_of_isForwardSol hW hσ.le hu).comp hF'
  have h2 : (fwdMap W σ ∘ F) =ᶠ[𝓝[H] (v : ℂ)] id := by
    filter_upwards [self_mem_nhdsWithin] with w hw
    simp only [Function.comp_apply, id, hFeq hw]
    exact RS.fwdMap_fwdMapInv hW hW0 hσ.le hw
  have h3 : Tendsto (id : ℂ → ℂ) (𝓝[H] (v : ℂ)) (𝓝 (u σ)) := h1.congr' h2
  have h4 : Tendsto (id : ℂ → ℂ) (𝓝[H] (v : ℂ)) (𝓝 (v : ℂ)) := tendsto_id.mono_left nhdsWithin_le_nhds
  have heq : u σ = (v : ℂ) := tendsto_nhds_unique h3 h4
  rw [fwdMap_eq_of_isForwardSol hW hu ⟨hσ.le, le_rfl⟩, heq, Complex.ofReal_re]

/-- **No interior coordinate is sent to an endpoint of the crosscut.** The endpoint value `e` is also attained at
an exterior coordinate (a limit of alive points), and the boundary injectivity forbids a second preimage. -/
theorem false_at_endpoint (hW : Continuous W) (hW0 : W 0 = 0) {σ : ℝ} (hσ : 0 < σ) {γ : ℝ → ℂ}
    (hD : IsCrosscutDomain (H \ fwdHull W σ) γ) (h0 : (γ 0).re < 0) (h1 : 0 < (γ 1).re) {F : ℂ → ℂ}
    (hFc : ContinuousOn F Hbar) (hFb' : ∀ x : ℝ, F x ∉ H \ fwdHull W σ) (hFd : DifferentiableOn ℂ F H)
    (hFi : InjOn F H) (hFs : F '' H = H \ fwdHull W σ) {C : ℝ} (hFC : ∀ w ∈ H, ‖F w - w‖ ≤ C)
    (hFC' : ∀ u ∈ Hbar, ‖F u - u‖ ≤ C) {v x e : ℝ} (hv : v ∉ exteriorCoords W σ) (hFvx : F v = (x : ℂ))
    (hxe : e = x)
    (hext : ∀ y : ℝ, (∃ u, IsForwardSol W (y : ℂ) σ u) →
      (fwdMap W σ y).re ∈ exteriorCoords W σ ∧ F ((fwdMap W σ y).re : ℝ) = y)
    (he : e = (γ 0).re ∨ e = (γ 1).re) : False := by
  set R := |e| + 1 + C with hR
  set S := exteriorCoords W σ ∩ Icc (-R) R with hS
  have hSc : IsCompact S := isCompact_Icc.inter_left isClosed_closure
  have hFr : ContinuousOn (fun t : ℝ => F t) S :=
    hFc.comp Complex.continuous_ofReal.continuousOn fun t _ => show (0 : ℝ) ≤ ((t : ℂ)).im by simp
  have hK : IsClosed ((fun t : ℝ => F t) '' S) := (hSc.image_of_continuousOn hFr).isClosed
  -- the approach set
  obtain ⟨A, hAalive, hAabs, heA'⟩ : ∃ A : Set ℝ, (∀ y ∈ A, y < (γ 0).re ∨ (γ 1).re < y) ∧
      (∀ y ∈ A, |y| ≤ |e| + 1) ∧ e ∈ closure A := by
    by_cases h : e = (γ 0).re
    · refine ⟨Ioo (e - 1) e, fun y hy => Or.inl (h ▸ hy.2), fun y hy => ?_, ?_⟩
      · rw [abs_le]; constructor <;> linarith [hy.1, hy.2, le_abs_self e, neg_abs_le e]
      · rw [closure_Ioo (by linarith)]; exact ⟨by linarith, le_rfl⟩
    · refine ⟨Ioo e (e + 1), fun y hy => Or.inr ((he.resolve_left h) ▸ hy.1), fun y hy => ?_, ?_⟩
      · rw [abs_le]; constructor <;> linarith [hy.1, hy.2, le_abs_self e, neg_abs_le e]
      · rw [closure_Ioo (by linarith)]; exact ⟨le_rfl, by linarith⟩
  have hAK : ((↑) : ℝ → ℂ) '' A ⊆ (fun t : ℝ => F t) '' S := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨u, hu⟩ := exists_isForwardSol_of_crosscut hW hW0 hσ hD h0 h1 (hAalive y hy)
    obtain ⟨hg, hFg⟩ := hext y ⟨u, hu⟩
    set g := (fwdMap W σ y).re with hgdef
    refine ⟨g, ⟨hg, ?_⟩, hFg⟩
    have hb := hFC' (g : ℂ) (show (0 : ℝ) ≤ ((g : ℂ)).im by simp)
    rw [hFg, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at hb
    have h' := abs_le.1 (hAabs y hy)
    have hb' := abs_le.1 hb
    refine ⟨?_, ?_⟩ <;> linarith [hb'.1, hb'.2, h'.1, h'.2]
  have heA : (e : ℂ) ∈ closure (((↑) : ℝ → ℂ) '' A) :=
    image_closure_subset_closure_image Complex.continuous_ofReal ⟨e, heA', rfl⟩
  obtain ⟨v₁, hv₁S, hFv₁⟩ := (closure_minimal hAK hK) heA
  have hne : v₁ ≠ v := fun h => hv (h ▸ hv₁S.1)
  have hFeq' : F v₁ = F v := by
    simp only at hFv₁; rw [hFv₁, hFvx, hxe]
  rcases lt_or_gt_of_ne hne with h | h
  · exact hD.false_of_eq hFc hFd hFi hFs hFb' ⟨C, hFC⟩ h hFeq'
  · exact hD.false_of_eq hFc hFd hFi hFs hFb' ⟨C, hFC⟩ h hFeq'.symm

/-- **The open inverse interval goes into `ℍ`** at a time `σ` whose hull is bounded by a simple crosscut `γ` with
`γ 0 < 0 < γ 1`: the continuous extension `F` of `f_σ` to `ℍ̄` maps every real point off the exterior coordinates
into `ℍ`. -/
theorem mem_H_of_frontier_eq_crosscut (hW : Continuous W) (hW0 : W 0 = 0) {σ : ℝ} (hσ : 0 < σ)
    {F : ℂ → ℂ} (hFeq : EqOn F (fwdMapInv W σ) H) (hFc : ContinuousOn F Hbar)
    (hFb : ∀ x : ℂ, x.im = 0 → F x ∉ H \ fwdHull W σ) {γ : ℝ → ℂ} (hγ : IsRealCrosscut γ)
    (h0 : (γ 0).re < 0) (h1 : 0 < (γ 1).re) (hfr : frontier (H \ fwdHull W σ) ∩ H = γ '' Ioo 0 1)
    {v : ℝ} (hv : v ∉ exteriorCoords W σ) : F v ∈ H := by
  set D := H \ fwdHull W σ with hDdef
  have hD : IsCrosscutDomain D γ := isCrosscutDomain_of_frontier hW hW0 hσ hγ (by linarith) hfr
  have hFd : DifferentiableOn ℂ F H := (RS.differentiableOn_fwdMapInv hW hW0 hσ.le).congr hFeq
  have hFi : InjOn F H := (RS.injOn_fwdMapInv_H hW hW0 hσ.le).congr hFeq.symm
  have hFs : F '' H = D := hFeq.image_eq.trans (RS.image_fwdMapInv_H hW hW0 hσ.le)
  have hFD : ∀ w ∈ H, F w ∈ D := fun w hw => hFs ▸ mem_image_of_mem F hw
  have hFb' : ∀ x : ℝ, F x ∉ D := fun x => hFb x (by simp)
  obtain ⟨M, hM⟩ := exists_abs_le_of_continuous hW σ
  set C := 24 * M + 8 * Real.sqrt σ with hC
  have hFC : ∀ w ∈ H, ‖F w - w‖ ≤ C := fun w hw => by
    rw [hFeq hw]; exact norm_fwdMapInv_sub_le hW hW0 hσ.le hM hw
  have hFC' : ∀ u ∈ Hbar, ‖F u - u‖ ≤ C := by
    intro u hu
    rw [← closure_H] at hu
    exact le_on_closure (f := fun z => ‖F z - z‖) (g := fun _ => C) hFC
      (by rw [closure_H]; exact (hFc.sub continuousOn_id).norm) continuousOn_const hu
  have hvHbar : ((v : ℂ)) ∈ Hbar := show (0 : ℝ) ≤ ((v : ℂ)).im by simp
  have hneb : (𝓝[H] (v : ℂ)).NeBot := FiniteEndpoint.neBot_nhdsWithin_H (by simp)
  have hlim : Tendsto F (𝓝[H] (v : ℂ)) (𝓝 (F v)) :=
    (hFc (v : ℂ) hvHbar).mono_left (nhdsWithin_mono _ fun z hz => (le_of_lt hz : (0 : ℝ) ≤ z.im))
  have hFvH : F v ∈ Hbar := by
    have : closure H = Hbar := closure_H
    rw [← this]
    exact mem_closure_of_tendsto hlim (eventually_nhdsWithin_of_forall fun w hw => (hFD w hw).1)
  by_contra hvH
  have him : (F v).im = 0 := le_antisymm (not_lt.1 hvH) hFvH
  set x := (F v).re with hx
  have hFvx : F v = (x : ℂ) := eq_ofReal_re_of_im_eq_zero him
  -- the boundary map sends exterior coordinates of alive points back
  have hext : ∀ y : ℝ, (∃ u, IsForwardSol W (y : ℂ) σ u) →
      (fwdMap W σ y).re ∈ exteriorCoords W σ ∧ F ((fwdMap W σ y).re : ℝ) = y := by
    rintro y ⟨u, hu⟩
    refine ⟨subset_closure ⟨y, ⟨u, hu⟩, rfl⟩, ?_⟩
    rw [← fwdMap_eq_ofReal_re hW hu ⟨hσ.le, le_rfl⟩]
    exact extension_fwdMap_eq_of_isForwardSol hW hW0 hσ.le hFeq hFc hu
  rcases lt_trichotomy x (γ 0).re with hx0 | hx0 | hx0
  · -- `x` alive on the left: `v` would be an exterior coordinate
    obtain ⟨u, hu⟩ := exists_isForwardSol_of_crosscut hW hW0 hσ hD h0 h1 (Or.inl hx0)
    exact hv (alive_coord_eq hW hW0 hσ hFeq hFD hlim hFvx hu ▸ (hext x ⟨u, hu⟩).1)
  · exact false_at_endpoint hW hW0 hσ hD h0 h1 hFc hFb' hFd hFi hFs hFC hFC' hv hFvx hx0.symm hext
      (Or.inl rfl)
  rcases lt_trichotomy x (γ 1).re with hx1 | hx1 | hx1
  · -- `x` strictly inside: a half-disc there is inside the hull
    obtain ⟨V, hVo, -, hVH, hVD, -, hVfr, -⟩ := hD.exists_inside
    obtain ⟨r, hr, hball⟩ := hD.exists_ball_inter_H_subset_inside hVo hVH hVfr ⟨hx0, hx1⟩
    have hev : ∀ᶠ w in 𝓝[H] (v : ℂ), F w ∈ ball (x : ℂ) r := by
      rw [hFvx] at hlim; exact hlim (ball_mem_nhds _ hr)
    obtain ⟨w, hw1, hw2⟩ := (hev.and self_mem_nhdsWithin).exists
    exact Set.disjoint_left.1 hVD (hball ⟨hw1, (hFD w hw2).1⟩) (hFD w hw2)
  · exact false_at_endpoint hW hW0 hσ hD h0 h1 hFc hFb' hFd hFi hFs hFC hFC' hv hFvx hx1.symm hext
      (Or.inr rfl)
  · obtain ⟨u, hu⟩ := exists_isForwardSol_of_crosscut hW hW0 hσ hD h0 h1 (Or.inr hx1)
    exact hv (alive_coord_eq hW hW0 hσ hFeq hFD hlim hFvx hu ▸ (hext x ⟨u, hu⟩).1)

/-- **The boundary map of a hull bounded by a crosscut is injective on `ℝ`** (Carathéodory for this Jordan domain,
`IsCrosscutDomain.false_of_eq`). -/
theorem injective_of_frontier_eq_crosscut (hW : Continuous W) (hW0 : W 0 = 0) {σ : ℝ} (hσ : 0 < σ)
    {F : ℂ → ℂ} (hFeq : EqOn F (fwdMapInv W σ) H) (hFc : ContinuousOn F Hbar)
    (hFb : ∀ x : ℂ, x.im = 0 → F x ∉ H \ fwdHull W σ) {γ : ℝ → ℂ} (hγ : IsRealCrosscut γ)
    (hlt : (γ 0).re < (γ 1).re) (hfr : frontier (H \ fwdHull W σ) ∩ H = γ '' Ioo 0 1) :
    Function.Injective fun v : ℝ => F v := by
  have hD : IsCrosscutDomain (H \ fwdHull W σ) γ := isCrosscutDomain_of_frontier hW hW0 hσ hγ hlt hfr
  have hFd : DifferentiableOn ℂ F H := (RS.differentiableOn_fwdMapInv hW hW0 hσ.le).congr hFeq
  have hFi : InjOn F H := (RS.injOn_fwdMapInv_H hW hW0 hσ.le).congr hFeq.symm
  have hFs : F '' H = H \ fwdHull W σ := hFeq.image_eq.trans (RS.image_fwdMapInv_H hW hW0 hσ.le)
  obtain ⟨M, hM⟩ := exists_abs_le_of_continuous hW σ
  have hFC : ∀ w ∈ H, ‖F w - w‖ ≤ 24 * M + 8 * Real.sqrt σ := fun w hw => by
    rw [hFeq hw]; exact norm_fwdMapInv_sub_le hW hW0 hσ.le hM hw
  intro v₁ v₂ h
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt' | hlt'
  · exact hD.false_of_eq hFc hFd hFi hFs (fun x => hFb x (by simp)) ⟨_, hFC⟩ hlt' h
  · exact hD.false_of_eq hFc hFd hFi hFs (fun x => hFb x (by simp)) ⟨_, hFC⟩ hlt' h.symm

end InteractingSLE.ZhanGT4
