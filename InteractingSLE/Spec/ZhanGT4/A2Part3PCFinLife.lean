/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A2Part3PCPair
import InteractingSLE.Spec.Zhan.StripEndpointLife
import InteractingSLE.Foundations.Loewner.FiniteEndpointStatement
import InteractingSLE.Spec.ZhanGT4.CrosscutA3SwallowKernel

/-!
# Finite strip life and physical contact with a real ray

Packet PROVE-ZHAN-A2P3-PC. The strip-life infimum is an open first-collision
time. A real point swallowed at finite time forces the earlier hulls to
accumulate somewhere on its exterior real ray, by the landed ray lemma.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology MeasureTheory ProbabilityTheory Bornology Metric
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A2X.P3

open QuantumZipper

/-- Every strip-life time is strictly before its first failure. -/
theorem lt_lifeEnd_of_isStripLife {w v : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}
    (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ})
    (hv : ContinuousOn v {t | (t : ℝ≥0∞) < ζ}) {s : ℝ≥0}
    (hs : Strip.IsStripLife w v ζ s) : (s : ℝ≥0∞) < lifeEnd w v ζ := by
  obtain ⟨s', hss', hs'⟩ := Zhan.exists_gt_isStripLife hw hv hs
  have hle : (s' : ℝ≥0∞) ≤ lifeEnd w v ζ := by
    refine le_iInf₂ fun t ht => ?_
    by_contra h
    exact ht (hs'.mono (ENNReal.coe_le_coe.1 (not_le.1 h).le))
  exact (ENNReal.coe_lt_coe.2 hss').trans_le hle

/-- The strip-life predicate describes exactly the open interval before its end. -/
theorem isStripLife_iff_lt_lifeEnd {w v : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}
    (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ})
    (hv : ContinuousOn v {t | (t : ℝ≥0∞) < ζ}) {s : ℝ≥0} :
    Strip.IsStripLife w v ζ s ↔ (s : ℝ≥0∞) < lifeEnd w v ζ :=
  ⟨lt_lifeEnd_of_isStripLife hw hv, isStripLife_of_lt_lifeEnd⟩

/-- At a finite strip end strictly before the original lifetime, the marked
coordinate meets the driver. -/
theorem eq_at_lifeEnd_of_lt_lifetime {w v : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}
    (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ})
    (hv : ContinuousOn v {t | (t : ℝ≥0∞) < ζ}) {T : ℝ≥0}
    (hT : (T : ℝ≥0∞) = lifeEnd w v ζ) (hTζ : (T : ℝ≥0∞) < ζ)
    (hvw : v T ≤ w T) : v T = w T := by
  by_contra hne
  have hs : Strip.IsStripLife w v ζ T := by
    refine ⟨hTζ, fun r hr => ?_⟩
    rcases hr.lt_or_eq with hrT | rfl
    · exact (isStripLife_of_lt_lifeEnd (hT ▸ ENNReal.coe_lt_coe.2 hrT)).2 r le_rfl
    · exact lt_of_le_of_ne hvw hne
  have hlt := lt_lifeEnd_of_isStripLife hw hv hs
  rw [← hT] at hlt
  exact (lt_irrefl _) hlt

/-- If a positive real point is swallowed at `T`, the earlier hulls accumulate
on the ray starting there. This includes swallowing by an enclosing contact. -/
theorem exists_real_ge_mem_closure_hullBefore_of_swallow
    {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0)
    {x T : ℝ} (hx : 0 < x) (hsw : RealSwallowAt W x T) :
    ∃ r : ℝ, x ≤ r ∧ (r : ℂ) ∈ closure (A34.hullBefore W T) := by
  by_contra h
  push Not at h
  let R : Set ℂ := {z | z.im = 0 ∧ x ≤ z.re}
  have hRc : IsClosed R :=
    (isClosed_eq continuous_im continuous_const).inter (isClosed_le continuous_const continuous_re)
  have hd : Disjoint (closure (A34.hullBefore W T)) R := by
    refine Set.disjoint_left.2 fun z hz hzr => ?_
    have hze : z = (z.re : ℂ) := Complex.ext rfl hzr.1
    exact h z.re hzr.2 (hze ▸ hz)
  have hbb : IsBounded (A34.hullBefore W T) := by
    refine (isBounded_fwdHull hW T).subset ?_
    intro z hz
    simp only [A34.hullBefore, mem_iUnion] at hz
    obtain ⟨s, hs, hzK⟩ := hz
    exact (fwdHull_mono (W := W)).1 hs.2.le hzK
  obtain ⟨ε, hε, hdε⟩ := hd.exists_thickenings hbb.isCompact_closure hRc
  have hball : ∀ s ∈ Ico (0 : ℝ) T, ∀ y : ℝ, x ≤ y →
      Disjoint (ball (y : ℂ) ε) (fwdHull W s) := by
    intro s hs y hy
    refine Set.disjoint_left.2 fun z hzy hzK => ?_
    have hzU : z ∈ closure (A34.hullBefore W T) :=
      subset_closure (mem_biUnion hs hzK)
    have hz₁ : z ∈ thickening ε (closure (A34.hullBefore W T)) :=
      mem_thickening_iff.2 ⟨z, hzU, by simpa only [dist_self] using hε⟩
    have hz₂ : z ∈ thickening ε R :=
      mem_thickening_iff.2 ⟨(y : ℂ), ⟨ofReal_im _, hy⟩, hzy⟩
    exact hdε.ne_of_mem hz₁ hz₂ rfl
  exact FiniteEndpoint.not_tendsto_fwdMap_of_disjoint_ray hW hW0 hsw.1 hx hε
    hball hsw.2.1 (tendsto_fwdMap_of_realSwallowAt hW hW0 hx hsw)

/-- The reflected ray statement for a negative marked point. -/
theorem exists_real_le_mem_closure_hullBefore_of_swallow
    {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0)
    {x T : ℝ} (hx : x < 0) (hsw : RealSwallowAt W x T) :
    ∃ r : ℝ, r ≤ x ∧ (r : ℂ) ∈ closure (A34.hullBefore W T) := by
  obtain ⟨r, hr, hrcl⟩ := exists_real_ge_mem_closure_hullBefore_of_swallow hW.neg
    (by simp only [Pi.neg_apply, hW0, neg_zero]) (neg_pos.2 hx) (realSwallowAt_neg_iff.2 hsw)
  have hreflect : A34.hullBefore (-W) T =
      LP.reflectC '' A34.hullBefore W T := by
    simp only [A34.hullBefore, image_iUnion]
    congr 1
    funext t
    congr 1
    funext _
    exact LP.fwdHull_neg W t
  rw [hreflect, LP.closure_image_reflectC] at hrcl
  obtain ⟨z, hz, hzr⟩ := hrcl
  have hzr' : z = ((-r : ℝ) : ℂ) := by
    have hh := congrArg LP.reflectC hzr
    simpa only [LP.reflectC_reflectC, LP.reflectC_ofReal] using hh
  exact ⟨-r, by linarith only [hr], hzr' ▸ hz⟩

section ForceFlow

variable {a : ℝ} {nL nR : ℕ} {xL ρL : Fin nL → ℝ} {xR ρR : Fin nR → ℝ}
  {w b : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ}
  {ζ : ℝ≥0∞}

/-- The existing separated-force flow formula at any horizon bounded by the
lifetime; unlike the terminal version, the horizon need not equal the lifetime. -/
theorem isForwardSol_gapR_before_horizon
    (hp : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ)
    {T : ℝ≥0} (hTζ : (T : ℝ≥0∞) ≤ ζ) {j : Fin nR}
    (hgap : ∀ t : ℝ≥0, t < T → w t < vR j t) {U : ℝ → ℝ}
    (hU : ∀ r : ℝ, 0 ≤ r → r < T → U r = w r.toNNReal)
    {r : ℝ} (hr : r < T) :
    IsForwardSol U (xR j : ℂ) r (Sec2.IsForcePath.gapR vR w j) := by
  have hf := hp.isForcePath
  have hlt : ∀ s ∈ Icc (0 : ℝ) r, (s.toNNReal : ℝ≥0∞) < ζ := by
    intro s hs
    exact (ENNReal.coe_lt_coe.2 ((Real.toNNReal_lt_iff_lt_coe hs.1).2
      (hs.2.trans_lt hr))).trans_le hTζ
  refine ⟨?_, fun s hs => ⟨?_, ?_⟩⟩
  · exact Complex.continuous_ofReal.comp_continuousOn
      (((hf.continuousOn_vR j).comp continuous_real_toNNReal.continuousOn hlt).sub
        (hf.continuousOn_w.comp continuous_real_toNNReal.continuousOn hlt))
  · have hsT : s.toNNReal < T :=
      (Real.toNNReal_lt_iff_lt_coe hs.1).2 (hs.2.trans_lt hr)
    exact ofReal_ne_zero.2 (sub_ne_zero.2 (hgap _ hsT).ne')
  · have hs0 : ((s.toNNReal : ℝ≥0) : ℝ) = s := Real.coe_toNNReal _ hs.1
    have hveq := hf.vR_eq (hlt s hs) j
    rw [hs0] at hveq
    have hint : (∫ q in (0 : ℝ)..s, (2 : ℂ) / Sec2.IsForcePath.gapR vR w j q) =
        ((∫ q in (0 : ℝ)..s, 2 / (vR j q.toNNReal - w q.toNNReal) : ℝ) : ℂ) := by
      rw [← intervalIntegral.integral_ofReal]
      refine intervalIntegral.integral_congr fun q _ => ?_
      simp only [Sec2.IsForcePath.gapR]
      push_cast
      rfl
    rw [hint, hU s hs.1 (hs.2.trans_lt hr)]
    simp only [Sec2.IsForcePath.gapR]
    rw [hveq]
    push_cast
    ring

/-- Left-side version of the separated-force formula before an arbitrary horizon. -/
theorem isForwardSol_gapL_before_horizon
    (hp : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ)
    {T : ℝ≥0} (hTζ : (T : ℝ≥0∞) ≤ ζ) {j : Fin nL}
    (hgap : ∀ t : ℝ≥0, t < T → vL j t < w t) {U : ℝ → ℝ}
    (hU : ∀ r : ℝ, 0 ≤ r → r < T → U r = w r.toNNReal)
    {r : ℝ} (hr : r < T) :
    IsForwardSol U (xL j : ℂ) r (Sec2.IsForcePath.gapL vL w j) := by
  have hsol := isForwardSol_gapR_before_horizon hp.reflect hTζ (j := j)
    (fun t ht => by simpa only [Pi.neg_apply, neg_lt_neg_iff] using hgap t ht)
    (U := -U) (fun s hs hsT => by simp only [Pi.neg_apply, hU s hs hsT]) hr
  have hsol' := QuantumZipper.RS.isForwardSol_neg hsol
  simp only [neg_neg, Pi.neg_apply, Complex.ofReal_neg] at hsol'
  convert hsol' using 1
  funext t
  simp only [Sec2.IsForcePath.gapR, Sec2.IsForcePath.gapL, Pi.neg_apply]
  push_cast
  ring

/-- A separated left force gap tending to zero gives an actual real swallowing
time, also when the stop precedes the original lifetime. -/
theorem realSwallowAt_of_left_gap_tendsto
    (hp : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ)
    {T : ℝ≥0} (hT : 0 < T) (hTζ : (T : ℝ≥0∞) ≤ ζ) {j : Fin nL}
    (hgap : ∀ t : ℝ≥0, t < T → vL j t < w t) {U : ℝ → ℝ}
    (hU : ∀ r : ℝ, 0 ≤ r → r < T → U r = w r.toNNReal)
    (hlim : Tendsto (fun t : ℝ≥0 => vL j t - w t) (𝓝[<] T) (𝓝 0)) :
    RealSwallowAt U (xL j) T := by
  have hsol := fun (r : ℝ) (hr : r < T) =>
    isForwardSol_gapL_before_horizon hp hTζ hgap hU hr
  refine ⟨NNReal.coe_pos.2 hT, fun r hr => ⟨_, hsol r hr.2⟩, ?_⟩
  apply Sec2.IsForcePath.not_exists_isForwardSol_of_tendsto hT hsol
  exact (Complex.continuous_ofReal.tendsto 0 |>.comp
    (hlim.comp (Sec2.IsForcePath.tendsto_toNNReal_nhdsLT T)))

end ForceFlow

/-- Switching between NNReal and real indexing of the same preterminal hulls. -/
theorem preContactHulls_coe_eq_hullBefore (W : ℝ → ℝ) (T : ℝ≥0) :
    preContactHulls W T = A34.hullBefore W T := by
  ext z
  simp only [preContactHulls, A34.hullBefore, mem_iUnion, physHull_zero]
  constructor
  · rintro ⟨s, hs, hz⟩
    exact ⟨s, ⟨s.coe_nonneg, NNReal.coe_lt_coe.2 (ENNReal.coe_lt_coe.1 hs)⟩, hz⟩
  · rintro ⟨s, hs, hz⟩
    refine ⟨s.toNNReal, ENNReal.coe_lt_coe.2 ((Real.toNNReal_lt_iff_lt_coe hs.1).2 hs.2), ?_⟩
    rwa [Real.coe_toNNReal _ hs.1]

/-- The earlier hull union only depends on driver values strictly before the stop. -/
theorem hullBefore_eq_of_eqOn_lt {W U : ℝ → ℝ} {T : ℝ}
    (he : EqOn W U (Ico 0 T)) : A34.hullBefore W T = A34.hullBefore U T := by
  apply Set.iUnion_congr
  intro s
  apply Set.iUnion_congr
  intro hs
  apply fwdHull_eq_of_eqOn hs.1 (show s < (s + T) / 2 by linarith only [hs.2])
  intro r hr
  exact he ⟨hr.1, by linarith only [hr.2, hs.2]⟩

/-- At a stop equal to the strip end, a swallowed real point at or left of `r`
supplies finite physical contact independently of the small-prefix geometry. -/
theorem finitePhysicalContact_of_swallow_of_contact_eq_lifeEnd
    {x r : ℝ} {w₁ w₂ v₂ : ℝ≥0 → ℝ} {ζ₂ : ℝ≥0∞} {q T : ℝ≥0}
    (hT : (T : ℝ≥0∞) = lifeEnd w₂ v₂ ζ₂)
    (hc : contactTime 0 (Strip.extPath w₂) (lifeEnd w₂ v₂ ζ₂)
      x (Strip.extPath w₁) q = lifeEnd w₂ v₂ ζ₂)
    {U : ℝ → ℝ} (hU : Continuous U) (hU0 : U 0 = 0)
    (he : ∀ s : ℝ, 0 ≤ s → s < T → U s = w₂ s.toNNReal)
    {p : ℝ} (hp : p < 0) (hpr : p ≤ r) (hsw : RealSwallowAt U p T) :
    FinitePhysicalContact x r w₁ w₂ v₂ ζ₂ q := by
  obtain ⟨s, hs, hscl⟩ := exists_real_le_mem_closure_hullBefore_of_swallow hU hU0 hp hsw
  refine ⟨s, ?_, Or.inr ⟨s, hs.trans hpr, rfl⟩⟩
  rw [hc, ← hT, preContactHulls_coe_eq_hullBefore]
  have he' : EqOn (Strip.extPath w₂) U (Ico 0 T) :=
    fun t ht => (he t ht.1 ht.2).symm
  rw [hullBefore_eq_of_eqOn_lt he']
  exact hscl

/-- The end of strip life before the lifetime is a swallowing time of its
marked real point, for any continuous extension of the stopped driver. -/
theorem realSwallowAt_of_lifeEnd_lt_lifetime
    {a : ℝ} {nL nR : ℕ} {xL ρL : Fin nL → ℝ} {xR ρR : Fin nR → ℝ}
    {w b : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ}
    {ζ : ℝ≥0∞} (hp : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ)
    {j : Fin nL} {T : ℝ≥0} (hTpos : 0 < T)
    (hT : (T : ℝ≥0∞) = lifeEnd w (vL j) ζ) (hTζ : (T : ℝ≥0∞) < ζ)
    {U : ℝ → ℝ} (he : ∀ s : ℝ, 0 ≤ s → s < T → U s = w s.toNNReal) :
    RealSwallowAt U (xL j) T := by
  have hf := hp.isForcePath
  have hgap : ∀ t : ℝ≥0, t < T → vL j t < w t := by
    intro t ht
    exact (isStripLife_of_lt_lifeEnd (hT ▸ ENNReal.coe_lt_coe.2 ht)).2 t le_rfl
  have heq := eq_at_lifeEnd_of_lt_lifetime hf.continuousOn_w (hf.continuousOn_vL j)
    hT hTζ (hf.vL_le_w hTζ j)
  have hcl : Tendsto (fun t => vL j t - w t) (𝓝[<] T) (𝓝 0) := by
    have hnhds := (Coupling.isOpen_setOf_coe_lt ζ).mem_nhds hTζ
    have hh := (((hf.continuousOn_vL j).continuousAt hnhds).tendsto.sub
      (hf.continuousOn_w.continuousAt hnhds).tendsto).mono_left
        (nhdsWithin_le_nhds (s := Iio T))
    simpa only [heq, sub_self] using hh
  exact realSwallowAt_of_left_gap_tendsto hp hTpos hTζ.le hgap he hcl

end InteractingSLE.ZhanGT4.A2X.P3
