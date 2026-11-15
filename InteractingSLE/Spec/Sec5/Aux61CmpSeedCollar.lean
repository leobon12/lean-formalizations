/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GStepPhysical
import InteractingSLE.Spec.Sec5.Aux61GNextRegular
import InteractingSLE.Spec.Sec5.Aux61RestartFinInherited
import InteractingSLE.Spec.Supplement.Aux10FullTD
import InteractingSLE.Spec.Sec5.Prop49QExitMainNR

/-! # Own-side boundary germs along the free current collar

At the restart time `r` the normalized retained chart `c` sends the current
tip to `0`. On a free current collar `F_r(ℍ ∩ B(0, δ)) ⊆ dom c` whose real
points never see the target `1`, the transition `c ∘ F_r` reflects across
`(-δ, δ)` (`exists_isPosReflect_collar`). Its seed-normalized derivative
logarithm has zero imaginary part at every collar point
(`tendsto_phase_collar`): the branch integer is constant along the collar and
zero at the seed. Hence at every chart point `b = (c ∘ F_r)(t)`, `t` in the
collar, the charted own coupling mean has the regular own height at `t`
(`tendsto_charted_couplingMean_sub_refMean0_collar`), and the inverse chart
lands at `F̄_r(t)` (`tendsto_inv_collar`).

When every physical preimage of `F̄_r(t)` lies in the collar, a whole ball
around `F̄_r(t)` minus the own hull lies in the retained domain
(`exists_ball_inter_subset_dom`): the full-ball form of the comparison.

Deterministic; no source statement is replaced.
-/

set_option autoImplicit false
noncomputable section
open Complex Set Metric Filter Topology
open QuantumZipper (H Hbar chiC fwdHull fwdMap fwdMapInv logDerivFwd)

namespace InteractingSLE.Sec5.Aux61Cmp
open Aux61Restart Aux61TwoS Aux61GStep
open Aux61Fib (FibData)

section Collar

variable {W : ℝ → ℝ} {η : ℝ → ℂ} {r : ℝ}
  (hW : Continuous W) (hW0 : W 0 = 0) (hη : IsLoewnerTrace W η) (hr : 0 < r)
  {c : Chart} (hc : c.IsConformal) (hsub : (c.dom : Set ℂ) ⊆ H \ fwdHull W r)
  (hB : IsHPHull (stripTargetHull (c.dom : Set ℂ))) {a ξ : ℝ}
  (hscale : EqOn c.1 (fun z => (a : ℂ) *
      (ConformalImage.mapOut (stripTargetHull (c.dom : Set ℂ)) (stripRightRetarget z) - ξ)) c.dom)
  {δ : ℝ} (hδ : 0 < δ) (hcol : MapsTo (fwdMapInv W r) (ball 0 δ ∩ H) c.dom)
  (hone : ∀ x : ℝ, |x| < δ → extendFrom H (fwdMapInv W r) x ≠ 1)

theorem mapsTo_collar (hcol : MapsTo (fwdMapInv W r) (ball 0 δ ∩ H) c.dom) :
    MapsTo (fwdMapInv W r) (H ∩ ball ((0 : ℝ) : ℂ) δ) c.dom := fun z hz =>
  hcol ⟨by rw [← ofReal_zero]; exact hz.2, hz.1⟩

include hW hW0 hη hr hc hsub hB hscale hδ hcol hone in
/-- The transition `c ∘ F_r` reflects across the whole free collar. -/
theorem exists_isPosReflect_collar : ∃ G, IsPosReflect (c.1 ∘ fwdMapInv W r) G 0 δ := by
  have hcol' := mapsTo_collar hcol
  have hd := hc.differentiableOn_fwd.comp
    ((QuantumZipper.RS.differentiableOn_fwdMapInv hW hW0 hr.le).mono inter_subset_left) hcol'
  refine exists_isPosReflect hδ hd (fun z hz => hc.fwd_mem (hcol' hz)) (fun z hz w hw he => ?_)
    fun x hx => ?_
  · have he' := congrArg c.2.1 he
    dsimp only [Function.comp_apply] at he'
    rw [hc.inv_fwd (hcol' hz), hc.inv_fwd (hcol' hw)] at he'
    exact QuantumZipper.RS.injOn_fwdMapInv_H hW hW0 hr.le hz.1 hw.1 he'
  · apply tendsto_im_transition_zero hW hW0 hη hr.le hc hsub hB hscale
    · exact hone x (ofReal_mem_ball_zero_iff.1 hx)
    · have hnear : ∀ᶠ z in 𝓝[H] (x : ℂ), z ∈ H ∩ ball ((0 : ℝ) : ℂ) δ :=
        inter_mem_nhdsWithin H (isOpen_ball.mem_nhds hx)
      exact hnear.mono hcol'

/-- The seed logarithm of the transition: `log a + Lc ∘ F_r - L_r ∘ F_r`. -/
def collarLog (W : ℝ → ℝ) (r : ℝ) (c : Chart) (a : ℝ) (z : ℂ) : ℂ :=
  (Real.log a : ℂ) + physicalRestartLog (stripTargetHull (c.dom : Set ℂ)) (fwdMapInv W r z) +
    -logDerivFwd W r (fwdMapInv W r z)

include hW hW0 hr hc hB hscale hcol in
/-- `collarLog` is a logarithm of the derivative of `c ∘ F_r` on the collar. -/
theorem isDerivLog_collarLog (ha : 0 < a) :
    IsDerivLog (c.1 ∘ fwdMapInv W r) (collarLog W r c a) (H ∩ ball ((0 : ℝ) : ℂ) δ) := by
  have hcol' := mapsTo_collar hcol
  have hDo : IsOpen (H ∩ ball ((0 : ℝ) : ℂ) δ) := QuantumZipper.isOpen_H.inter isOpen_ball
  have hdom : IsOpen (c.dom : Set ℂ) := c.dom.isOpen
  have hRD := H_diff_stripTargetHull hc.dom_subset
  have hmaps : MapsTo stripRightRetarget (c.dom : Set ℂ) (H \ stripTargetHull (c.dom : Set ℂ)) :=
    fun z hz => by rw [hRD]; exact mem_image_of_mem _ hz
  have hgd : DifferentiableOn ℂ
      (ConformalImage.mapOut (stripTargetHull (c.dom : Set ℂ)) ∘ stripRightRetarget) c.dom :=
    (ConformalImage.isMapOut_mapOut hB).1.1.comp
      (isConformalBijection_stripRightRetarget.1.mono hc.dom_subset) hmaps
  have hLc : IsDerivLog c.1 (fun z => (Real.log a : ℂ) +
      physicalRestartLog (stripTargetHull (c.dom : Set ℂ)) z) c.dom :=
    isDerivLog_pos_scale_sub hdom hgd
      (isDerivLog_physicalRestartLog hdom hB hc.dom_subset hmaps) ha hscale
  have hFd := QuantumZipper.RS.differentiableOn_fwdMapInv hW hW0 hr.le
  have h := IsDerivLog.comp hDo hdom hc.differentiableOn_fwd (hFd.mono inter_subset_left) hcol' hLc
    ((Aux10.isDerivLog_fwdMapInv hW hW0 hr.le).mono inter_subset_left)
  refine ⟨?_, fun z hz => ?_⟩
  · refine h.1.congr fun z _ => ?_
    simp only [collarLog]
  · rw [← h.2 z hz]
    simp only [collarLog]

include hW hW0 hη hr hc hsub hB hscale hδ hcol hone in
/-- **The inherited relative phase vanishes along the whole collar**: the
integer of the transition's derivative argument is constant on `(-δ, δ)` and
zero at the seed (R1's seed normalization). -/
theorem tendsto_phase_collar (ha : 0 < a) (hηinj : InjOn η (Icc 0 r))
    (hηH : ∀ u ∈ Ioc 0 r, η u ∈ H)
    (hlift : ∀ z ∈ (c.dom : Set ℂ),
      c.2.2 z = (physicalRestartLog (stripTargetHull (c.dom : Set ℂ)) z).im)
    {x : ℝ} (hx : |x| < δ) :
    Tendsto (fun z => c.2.2 (fwdMapInv W r z) - (logDerivFwd W r (fwdMapInv W r z)).im)
      (𝓝[H] (x : ℂ)) (𝓝 0) := by
  obtain ⟨G, hG⟩ := exists_isPosReflect_collar hW hW0 hη hr hc hsub hB hscale hδ hcol hone
  have hL := isDerivLog_collarLog hW hW0 hr hc hB hscale hcol (δ := δ) ha
  have hcol' := mapsTo_collar hcol
  have him_eq : ∀ z ∈ H ∩ ball ((0 : ℝ) : ℂ) δ, (collarLog W r c a z).im =
      c.2.2 (fwdMapInv W r z) - (logDerivFwd W r (fwdMapInv W r z)).im := by
    intro z hz
    rw [hlift _ (hcol' hz)]
    simp only [collarLog, add_im, ofReal_im, zero_add, neg_im, sub_eq_add_neg]
  have h0 : Tendsto (fun z => (collarLog W r c a z).im) (𝓝[H] ((0 : ℝ) : ℂ)) (𝓝 0) := by
    have ht := tendsto_relative_phase_of_prefix hW hW0 hη hr hηinj hηH hsub hB ⟨δ, hδ, hcol⟩
    rw [ofReal_zero]
    refine ht.congr fun z => ?_
    simp only [collarLog, add_im, ofReal_im, zero_add, neg_im, sub_eq_add_neg]
  have hall : Tendsto (fun z => (collarLog W r c a z).im) (𝓝[H] (x : ℂ)) (𝓝 0) := by
    refine GlueImg.tendsto_zero_of_forall_tendsto_two_pi_int (I := Ioo (-δ) δ) isPreconnected_Ioo
      (fun y hy => ?_) (x₀ := 0) ⟨by linarith, hδ⟩ h0 (abs_lt.1 hx)
    obtain ⟨r', hr', hsubb⟩ := Aux61TwoS.exists_ball_subset_ball (ofReal_mem_ball_zero_iff.2 (abs_lt.2 hy))
    have hG' := hG.of_subset hr' hsubb
    have hsub' : H ∩ ball (y : ℂ) r' ⊆ H ∩ ball ((0 : ℝ) : ℂ) δ := fun z hz => ⟨hz.1, hsubb hz.2⟩
    exact hG'.exists_int_tendsto_im (hL.1.continuousOn.mono hsub') fun z hz => hL.2 z (hsub' hz)
  have hxB : (x : ℂ) ∈ ball ((0 : ℝ) : ℂ) δ := ofReal_mem_ball_zero_iff.2 hx
  refine hall.congr' ?_
  filter_upwards [inter_mem_nhdsWithin H (isOpen_ball.mem_nhds hxB)] with z hz
  exact him_eq z hz

include hW hW0 hη hr hc hsub hB hscale hδ hcol hone in
/-- **The own-to-retained transition at a collar point**: if `c ∘ F_r → b` at
the collar point `t`, then `f_r ∘ c⁻¹ → t` inside `ℍ` at `b`. -/
theorem tendsto_transition_collar {t b : ℝ} (ht : |t| < δ)
    (htb : Tendsto (fun z => c.1 (fwdMapInv W r z)) (𝓝[H] (t : ℂ)) (𝓝 (b : ℂ))) :
    Tendsto (fun z => fwdMap W r (c.2.1 z)) (𝓝[H] (b : ℂ)) (𝓝[H] (t : ℂ)) := by
  obtain ⟨G, hG⟩ := exists_isPosReflect_collar hW hW0 hη hr hc hsub hB hscale hδ hcol hone
  have hcol' := mapsTo_collar hcol
  have htB : (t : ℂ) ∈ ball ((0 : ℝ) : ℂ) δ := ofReal_mem_ball_zero_iff.2 ht
  have hNB := GlueImg.nhdsWithin_H_neBot t
  have hGt : G t = (b : ℂ) := tendsto_nhds_unique (hG.tendsto htB) htb
  obtain ⟨r', hr', hsubb⟩ := Aux61TwoS.exists_ball_subset_ball htB
  have hG' := hG.of_subset hr' hsubb
  have hleft : ∀ w ∈ H ∩ ball (t : ℂ) r',
      (fun z => fwdMap W r (c.2.1 z)) ((c.1 ∘ fwdMapInv W r) w) = w := by
    intro w hw
    have hw' : w ∈ H ∩ ball ((0 : ℝ) : ℂ) δ := ⟨hw.1, hsubb hw.2⟩
    dsimp only [Function.comp_apply]
    rw [hc.inv_fwd (hcol' hw')]
    exact QuantumZipper.RS.fwdMap_fwdMapInv hW hW0 hr.le hw.1
  have h := hG'.tendsto_leftInv (Θ := fun z => fwdMap W r (c.2.1 z)) hleft
  rwa [hGt] at h

include hW hW0 hη hr hc hsub hB hscale hδ hcol hone in
/-- The inverse chart lands at the physical boundary point `F̄_r(t)`. -/
theorem tendsto_inv_collar {t b : ℝ} (ht : |t| < δ)
    (htb : Tendsto (fun z => c.1 (fwdMapInv W r z)) (𝓝[H] (t : ℂ)) (𝓝 (b : ℂ))) :
    Tendsto c.2.1 (𝓝[H] (b : ℂ)) (𝓝 (extendFrom H (fwdMapInv W r) t)) := by
  have hΘ := tendsto_transition_collar hW hW0 hη hr hc hsub hB hscale hδ hcol hone ht htb
  have hF := ((hη.hasBdryLimits hW hW0 hr.le).tendsto
    (mem_Hbar_of_im_eq_zero (by simp : ((t : ℂ)).im = 0))).comp hΘ
  refine hF.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  dsimp only [Function.comp_apply]
  exact QuantumZipper.RS.fwdMapInv_fwdMap hW hW0 hr.le (hsub (hc.inv_mem_dom hz))

include hW hW0 hη hr hc hsub hB hscale hδ hcol hone in
/-- **The regular own-side germ along the collar.** At a chart point
`b = (c ∘ F_r)(t)` of the collar, off the seed, the reference jumps and the
own force marks, the charted own coupling mean with the inherited lift has the
reference boundary value, provided the reference height at `b` is the own
height at `t`. -/
theorem tendsto_charted_couplingMean_sub_refMean0_collar (ha : 0 < a)
    (hηinj : InjOn η (Icc 0 r)) (hηH : ∀ u ∈ Ioc 0 r, η u ∈ H)
    (hlift : ∀ z ∈ (c.dom : Set ℂ),
      c.2.2 z = (physicalRestartLog (stripTargetHull (c.dom : Set ℂ)) z).im)
    (d : FibData) (F : Impl.ForceWord) (vL : Fin F.nL → ℝ) (vR : Fin F.nR → ℝ)
    {t b : ℝ} (ht : |t| < δ)
    (htb : Tendsto (fun z => c.1 (fwdMapInv W r z)) (𝓝[H] (t : ℂ)) (𝓝 (b : ℂ)))
    (htJ : t ∉ Impl.forceJumpSet F vL vR) (hb0 : b ≠ 0) (hbJ : b ∉ d.JR)
    (hheight : d.bR b = Impl.forceBoundaryData d.κ F vL vR t) :
    Tendsto (fun z => couplingMean d.κ W r (Impl.forceExt d.κ F vL vR) (c.2.1 z) +
      chiC d.κ * c.2.2 (c.2.1 z) - Aux61GlueK.refMean0 d z) (𝓝[H] (b : ℂ)) (𝓝 0) := by
  have hΘ := tendsto_transition_collar hW hW0 hη hr hc hsub hB hscale hδ hcol hone ht htb
  have h1 := ((Impl.isBoundedHarmonicExtension_forceExt d.κ F vL vR).2.2 t htJ).comp hΘ
  have h2 := (tendsto_phase_collar hW hW0 hη hr hc hsub hB hscale hδ hcol hone ha hηinj hηH hlift
    ht).comp hΘ
  have h3 := Aux61GNext.tendsto_refMean0_regular d hb0 hbJ
  have h := (h1.add (h2.const_mul (chiC d.κ))).sub h3
  rw [hheight, mul_zero, add_zero, sub_self] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hF : fwdMapInv W r (fwdMap W r (c.2.1 z)) = c.2.1 z :=
    QuantumZipper.RS.fwdMapInv_fwdMap hW hW0 hr.le (hsub (hc.inv_mem_dom hz))
  simp only [Function.comp_apply, hF, couplingMean]
  ring

end Collar

/-! ### Full-ball containment along the collar -/

section Ball

variable {W : ℝ → ℝ} {η : ℝ → ℂ} {r : ℝ}
  (hW : Continuous W) (hW0 : W 0 = 0) (hη : IsLoewnerTrace W η) (hr : 0 < r)
  {D : Set ℂ} {δ : ℝ} (hcol : MapsTo (fwdMapInv W r) (ball 0 δ ∩ H) D)

include hW hW0 hη hr hcol in
/-- **Full-ball containment**: if every real preimage of the boundary point
`F̄_r(t)` lies in the free collar, a whole ball around `F̄_r(t)` minus the own
hull lies in the retained domain. Proof: `F̄_r` is continuous on `ℍ̄` with
bounded displacement, so the image of the compact annular part
`{δ ≤ |y| ≤ R}` of `ℍ̄` is closed and misses `F̄_r(t)`. -/
theorem exists_ball_inter_subset_dom (t : ℝ)
    (hpre : ∀ y : ℝ, extendFrom H (fwdMapInv W r) y = extendFrom H (fwdMapInv W r) t → |y| < δ) :
    ∃ ρ > 0, ball (extendFrom H (fwdMapInv W r) t) ρ ∩ (H \ fwdHull W r) ⊆ D := by
  set Fb := extendFrom H (fwdMapInv W r) with hFb
  set z₀ := Fb t with hz₀
  obtain ⟨C, hC⟩ := QuantumZipper.R18.exists_norm_fwdMapInv_sub_le hW hW0 hr.le
  have hcont : ContinuousOn Fb Hbar := (hη.hasBdryLimits hW hW0 hr.le).continuousOn
  set R : ℝ := ‖z₀‖ + 1 + C with hR
  set K : Set ℂ := Hbar ∩ {y | δ ≤ ‖y‖ ∧ ‖y‖ ≤ R} with hK
  have hKc : IsCompact K := by
    refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
    · exact QuantumZipper.isClosed_Hbar.inter
        ((isClosed_le continuous_const continuous_norm).inter
          (isClosed_le continuous_norm continuous_const))
    · refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := R)).subset fun y hy => ?_
      rw [mem_closedBall, dist_zero_right]
      exact hy.2.2
  have hFK : IsClosed (Fb '' K) := (hKc.image_of_continuousOn (hcont.mono inter_subset_left)).isClosed
  have hz₀K : z₀ ∉ Fb '' K := by
    rintro ⟨y, hyK, hy⟩
    by_cases hyH : y ∈ H
    · have hn := extendFrom_notMem_compl_fwdHull hW hW0 hη hr.le t
      rw [← hFb, ← hz₀, ← hy, hFb, WangWu.extendFrom_fwdMapInv_eq hW hW0 hr.le hyH] at hn
      exact hn (QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hW hW0 hr.le hyH)
    · have hy0 : y.im = 0 := le_antisymm (not_lt.1 hyH) hyK.1
      have hyr : ((y.re : ℝ) : ℂ) = y := ofReal_re_eq hy0
      have h := hpre y.re (by rw [hyr]; exact hy)
      have h2 := hyK.2.1
      rw [← hyr, norm_real, Real.norm_eq_abs] at h2
      linarith
  obtain ⟨ρ₁, hρ₁, hball⟩ := Metric.isOpen_iff.1 hFK.isOpen_compl z₀ hz₀K
  refine ⟨min ρ₁ 1, lt_min hρ₁ one_pos, fun w hw => ?_⟩
  obtain ⟨hwb, hwH, hwK⟩ := hw
  have hyH : fwdMap W r w ∈ H := QuantumZipper.FwdHolo.mapsTo_fwdMap hW hr.le ⟨hwH, hwK⟩
  have hFy : fwdMapInv W r (fwdMap W r w) = w :=
    QuantumZipper.RS.fwdMapInv_fwdMap hW hW0 hr.le ⟨hwH, hwK⟩
  by_cases hyδ : ‖fwdMap W r w‖ < δ
  · rw [← hFy]
    exact hcol ⟨by rw [mem_ball, dist_zero_right]; exact hyδ, hyH⟩
  · exfalso
    have hwz : dist w z₀ < 1 := lt_of_lt_of_le hwb (min_le_right _ _)
    have h1 := hC _ hyH
    rw [hFy] at h1
    have h2 : ‖w‖ ≤ ‖z₀‖ + 1 := by
      have := norm_sub_norm_le w z₀
      rw [dist_eq_norm] at hwz
      linarith
    have h3 : ‖fwdMap W r w‖ ≤ ‖w‖ + ‖w - fwdMap W r w‖ := by
      have := norm_sub_le w (w - fwdMap W r w)
      rwa [sub_sub_cancel] at this
    have h4 : ‖w - fwdMap W r w‖ ≤ C := h1
    have hyK : fwdMap W r w ∈ K := ⟨QuantumZipper.H_subset_Hbar hyH, not_lt.1 hyδ, by linarith⟩
    refine hball (mem_ball.2 (lt_of_lt_of_le hwb (min_le_left _ _))) ⟨_, hyK, ?_⟩
    rw [hFb, WangWu.extendFrom_fwdMapInv_eq hW hW0 hr.le hyH, hFy]

include hW hW0 hη hr in
/-- A real boundary point of the own chart lies in the own hull or on `ℝ`. -/
theorem extendFrom_mem_hull_or_real (t : ℝ) :
    extendFrom H (fwdMapInv W r) t ∈ fwdHull W r ∪ {z : ℂ | z.im = 0} := by
  have hbar := Prop49Exit.extendFrom_mem_Hbar hη hW hW0 hr.le t
  by_cases hH : extendFrom H (fwdMapInv W r) t ∈ H
  · left
    by_contra hK
    exact extendFrom_notMem_compl_fwdHull hW hW0 hη hr.le t ⟨hH, hK⟩
  · right
    exact le_antisymm (not_lt.1 hH) hbar

end Ball

end InteractingSLE.Sec5.Aux61Cmp
