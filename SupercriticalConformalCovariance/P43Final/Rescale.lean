import SupercriticalConformalCovariance.Small.RescaleRegular
import SupercriticalConformalCovariance.Small.LargeDiskRegular
import SupercriticalConformalCovariance.Small.WeylMonotone
import SupercriticalConformalCovariance.Small.CircleWitness
import SupercriticalConformalCovariance.Small.TargetMetricScale
import SupercriticalConformalCovariance.Small.ZoomData
import SupercriticalConformalCovariance.Small.TangentConfVarying
import SupercriticalConformalCovariance.Good.Probability
import SupercriticalConformalCovariance.Good.Specialized

/-!
# Proposition 4.3: rescaling a failure at `(z, r)`

Paper l. 338–355. Fix a scale `(z, r)`, the zoom `A(w) = z + r w` of the source, the zoom
`B(t) = φ(z) + r t` of the target, `ψ = B⁻¹ ∘ φ ∘ A` (`zoomMap φ z r`), and the circle-average recentred
source field `ĥ = h(z + r·) − h_r(z)` (paper l. 339, with the circle average `h_r(z)` of (7) as the
recentring constant `c`). The zoomed target realization is `(g₀ ∘ B, k ∘ B − c)` (the Proposition 4.3 proof's corrected
pair). This file proves, for one scale:

* `ae_target_mono`: the rescaled transported metric `s · e(A u, A v)`, `s = r^{-ξQ} e^{-ξ c}`, is at most
  the confined zoomed target metric of Lemma 3.3 (`tgtConf`) on the disk `B̄_R(0)` (confinement can only
  increase the `e`-distance, l. 353–354);
* `ae_bad_to_failure`: a regular-pair failure at `(z, r)` (the event of `Prop43Input`) gives a
  unit-scale failure for the confined source metric `conf (D ĥ) 0 R` and `tgtConf`, with the fixed
  bounds of `SourceFailure` (l. 351–360).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Metric TopologicalSpace Filter
open scoped ENNReal

namespace SupercriticalConformalCovariance.P43Final

open LQGMetric (DistC addFun addConst affineComp affinePt ofCont IsGFFPlusCont circleAvg)
open SupercriticalLQGUniqueness (LSCMetric IsStrongLQGMetric)
open SupercriticalConformalCovariance (IsConformalBijection weylScaleOn domainMetric)
open SmallGammaGeodesics.CC (zoomMap)
open SupercriticalConformalCovariance.Small (affinePreimage zoomConformal affinePreimage_conformal negConstOn conf confPullCompact
  zoomEquiv)
open SupercriticalConformalCovariance.Tangent (imageMapK imageMapK_injective)
open SupercriticalConformalCovariance.Domain (exW cutF resC)
open SupercriticalConformalCovariance.BiLip (pathInf)

/-- The confined zoomed target metric of Lemma 3.3 at one scale, written exactly as in
`SupercriticalConformalCovariance.Small.tangent_limit_conf_law_varying`. -/
def tgtConf (D : DistC → LSCMetric) {U V : Opens ℂ} {φ : ℂ → ℂ}
    (hφ : IsConformalBijection φ U V) (z : ℂ) {r : ℝ} (hr : 0 < r) {R : ℝ}
    (hRU : 0 < R ∧ ball (0 : ℂ) (2 * R) ⊆ affinePreimage U z r) (m : ℕ)
    (g : DistC) (k : C(affinePreimage V (φ z) r, ℝ)) : LSCMetric :=
  confPullCompact (D (addFun g (cutF (affinePreimage V (φ z) r) m k)))
    (zoomMap φ z r '' closedBall 0 R) (closedBall 0 R) (isCompact_closedBall _ _)
    ((isCompact_closedBall _ _).image_of_continuousOn
      ((zoomConformal hφ z hr).1.continuousOn.mono
        ((closedBall_subset_ball (by linarith [hRU.1])).trans hRU.2)))
    (imageMapK (zoomMap φ z r) _
      ((zoomConformal hφ z hr).1.continuousOn.mono
        ((closedBall_subset_ball (by linarith [hRU.1])).trans hRU.2)))
    (imageMapK_injective _ ((zoomConformal hφ z hr).2.injOn.mono
      ((closedBall_subset_ball (by linarith [hRU.1])).trans hRU.2)))

/-- The zoomed target correction `k ∘ B − c` on the global zoomed target domain. -/
def zoomCorr {V : Opens ℂ} (a : ℂ) {r : ℝ} (hr : 0 < r) (k : C(V, ℝ)) (c : ℝ) :
    C(affinePreimage V a r, ℝ) :=
  k.comp (SupercriticalConformalCovariance.Root.mapsToCM (affinePreimage_conformal V a hr)) + negConstOn _ c

theorem closedBall_subset_zoom {U : Opens ℂ} {z : ℂ} {r R : ℝ}
    (hRU : 0 < R ∧ ball (0 : ℂ) (2 * R) ⊆ affinePreimage U z r) :
    closedBall (0 : ℂ) R ⊆ affinePreimage U z r :=
  (closedBall_subset_ball (by linarith [hRU.1])).trans hRU.2

/-- `φ(z + r u) = B(ψ(u))`. -/
theorem zoom_apply_eq (φ : ℂ → ℂ) (z : ℂ) {r : ℝ} (hr : 0 < r) (u : ℂ) :
    zoomEquiv (φ z) hr.ne' (zoomMap φ z r u) = φ (z + (r : ℂ) * u) :=
  SmallGammaGeodesics.CC.zoomAff_zoomMap hr.ne' u

/-- **Target monotonicity under confinement** (paper l. 353–354, after the affine/Weyl rescaling of
l. 342–344). -/
theorem ae_target_mono {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ} {D : DistC → LSCMetric}
    (hD : IsStrongLQGMetric ξ Q D) {U V : Opens ℂ} {φ : ℂ → ℂ}
    (hφ : IsConformalBijection φ U V) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (g₀ : Ω → DistC) (hg₀ : IsGFFPlusCont g₀ P)
    (f : Ω → C(V, ℝ)) (hf : Measurable f) (c : Ω → ℝ) (z : ℂ) {r : ℝ} (hr : 0 < r) {R : ℝ}
    (hRU : 0 < R ∧ ball (0 : ℂ) (2 * R) ⊆ affinePreimage U z r) (m : ℕ)
    (hm : zoomMap φ z r '' closedBall 0 R ⊆ exW (affinePreimage V (φ z) r) m) :
    ∀ᵐ ω ∂P, ∀ u ∈ closedBall (0 : ℂ) R, ∀ v ∈ closedBall (0 : ℂ) R,
      ENNReal.ofReal (r ^ (-((ξ : ℝ) * Q)) * Real.exp (-((ξ : ℝ) * c ω))) *
          SupercriticalConformalCovariance.Good.transportedE (ξ : ℝ) D hφ (g₀ ω) (f ω) (z + (r : ℂ) * u, z + (r : ℂ) * v) ≤
        tgtConf D hφ z hr hRU m (affineComp r (φ z) (g₀ ω)) (zoomCorr (φ z) hr (f ω) (c ω))
          (u, v) := by
  classical
  set W : Opens ℂ := affinePreimage V (φ z) r with hW
  set ψ : ℂ → ℂ := zoomMap φ z r with hψ
  set K : Set ℂ := closedBall (0 : ℂ) R with hK
  set L : Set ℂ := ψ '' K with hL
  set B : ℂ ≃ ℂ := zoomEquiv (φ z) hr.ne' with hB
  have hψc : IsConformalBijection ψ (affinePreimage U z r) W := zoomConformal hφ z hr
  have hKU : K ⊆ affinePreimage U z r := closedBall_subset_zoom hRU
  have hLW : L ⊆ (W : Set ℂ) := by
    rintro _ ⟨w, hw, rfl⟩
    exact hψc.2.mapsTo (hKU hw)
  have hLc : IsCompact L :=
    (isCompact_closedBall _ _).image_of_continuousOn (hψc.1.continuousOn.mono hKU)
  set A : Set ℂ := B '' L with hA
  have hBw : ∀ w, B w = φ z + (r : ℂ) * w := fun w => rfl
  have hAV : A ⊆ (V : Set ℂ) := by
    rintro _ ⟨w, hw, rfl⟩
    have h := hLW hw
    change LQGMetric.affinePt r (φ z) w ∈ V at h
    rw [LQGMetric.affinePt_apply] at h
    rw [hBw, add_comm]
    exact h
  have hBc : Continuous B := by
    change Continuous fun w : ℂ => φ z + (r : ℂ) * w
    fun_prop
  have hAc : IsCompact A := hLc.image hBc
  obtain ⟨m', hm'⟩ := SupercriticalConformalCovariance.Domain.exists_subset_exW V.isOpen hAc hAV
  let F : Ω → C(ℂ, ℝ) := fun ω => cutF V m' (f ω)
  have hFm : Measurable F := SupercriticalConformalCovariance.Domain.measurable_cutExt V.isOpen
    (SupercriticalConformalCovariance.Domain.tsupport_cutoff_subset (V : Set ℂ) m') hf
  have hg₁ : IsGFFPlusCont (fun ω => affineComp r (φ z) (g₀ ω)) P :=
    LQGMetric.GM.isGFFPlusCont_affineComp hg₀ hr (φ z)
  filter_upwards [SupercriticalConformalCovariance.Small.ae_rescaled_target_with_correction hD P g₀ hg₀ F hFm ⟨r, hr⟩ (φ z) c,
    SupercriticalConformalCovariance.Domain.ae_weylScaleOn_eq_internal hD P hg₀,
    SupercriticalConformalCovariance.Domain.ae_weylScaleOn_eq_internal hD P hg₁] with ω hpt hw₀ hw₁
  intro u hu v hv
  set s : ℝ≥0∞ := ENNReal.ofReal (r ^ (-((ξ : ℝ) * Q)) * Real.exp (-((ξ : ℝ) * c ω))) with hs
  have hspos : 0 < r ^ (-((ξ : ℝ) * Q)) * Real.exp (-((ξ : ℝ) * c ω)) :=
    mul_pos (Real.rpow_pos_of_pos hr _) (Real.exp_pos _)
  have hs0 : s ≠ 0 := (ENNReal.ofReal_pos.mpr hspos).ne'
  have hst : s ≠ ⊤ := ENNReal.ofReal_ne_top
  -- points
  have hψuL : ψ u ∈ L := mem_image_of_mem ψ hu
  have hψvL : ψ v ∈ L := mem_image_of_mem ψ hv
  have hBuA : B (ψ u) ∈ A := mem_image_of_mem B hψuL
  have hBvA : B (ψ v) ∈ A := mem_image_of_mem B hψvL
  have hAu : z + (r : ℂ) * u ∈ (U : Set ℂ) := by
    have h := hKU hu
    change LQGMetric.affinePt r z u ∈ U at h
    rw [LQGMetric.affinePt_apply, add_comm] at h
    exact h
  have hAv : z + (r : ℂ) * v ∈ (U : Set ℂ) := by
    have h := hKU hv
    change LQGMetric.affinePt r z v ∈ U at h
    rw [LQGMetric.affinePt_apply, add_comm] at h
    exact h
  have heu : B (ψ u) = φ (z + (r : ℂ) * u) := zoom_apply_eq φ z hr u
  have hev : B (ψ v) = φ (z + (r : ℂ) * v) := zoom_apply_eq φ z hr v
  -- (a) the transported metric is the Weyl domain metric of `(g₀, f)` at `B ψ u, B ψ v`
  have ha : SupercriticalConformalCovariance.Good.transportedE (ξ : ℝ) D hφ (g₀ ω) (f ω) (z + (r : ℂ) * u, z + (r : ℂ) * v) =
      weylScaleOn (ξ : ℝ) (f ω) (D (g₀ ω))
        (⟨B (ψ u), hAV hBuA⟩, ⟨B (ψ v), hAV hBvA⟩) := by
    rw [show (z + (r : ℂ) * u, z + (r : ℂ) * v) =
      (((⟨z + (r : ℂ) * u, hAu⟩ : U) : ℂ), ((⟨z + (r : ℂ) * v, hAv⟩ : U) : ℂ)) from rfl,
      SupercriticalConformalCovariance.Good.transportedE_on]
    unfold domainMetric
    congr 2
    · exact Subtype.ext heu.symm
    · exact Subtype.ext hev.symm
  -- (b) restriction to `A` increases it, and (c) identifies it with a whole-plane internal metric
  have hb := SupercriticalConformalCovariance.Small.weylScaleOn_le_restrict (D (g₀ ω)) (ξ : ℝ) hAV (f ω)
    (⟨B (ψ u), hBuA⟩, ⟨B (ψ v), hBvA⟩)
  have hc := hw₀ A (resC hAV (f ω)) (F ω)
    (fun w hw => SupercriticalConformalCovariance.Domain.cutF_eq V m' (f ω) w (hm' hw))
    (⟨B (ψ u), hBuA⟩, ⟨B (ψ v), hBvA⟩)
  -- (d) the affine/Weyl rescaling of internal metrics
  set G' : DistC := addFun (addConst (affineComp r (φ z) (g₀ ω)) (-c ω))
    ((F ω).comp (LQGMetric.affinePt r (φ z))) with hG'
  have hpt' : ∀ a b : ℂ, D G' (a, b) = s * D (addFun (g₀ ω) (F ω)) (B a, B b) := fun a b => hpt a b
  have hd := SupercriticalConformalCovariance.Small.internal_of_rescaled_pointwise B hs0 hst hpt' A
    ⟨B (ψ u), hBuA⟩ ⟨B (ψ v), hBvA⟩
  -- (e) the zoomed carrier is `L`
  have hd' : pathInf (D G') L (ψ u) (ψ v) =
      s * (D (addFun (g₀ ω) (F ω))).internal A (⟨B (ψ u), hBuA⟩, ⟨B (ψ v), hBvA⟩) := by
    have hset : B.symm '' A = L := B.symm_image_image L
    rw [← hd, SupercriticalConformalCovariance.BiLip.internal_eq_pathInf]
    simp only [Equiv.symm_apply_apply]
    rw [hset]
  -- (f), (g): both zoomed whole-plane fields have the same internal metric on `L`
  have hG'eq : G' = addFun (affineComp r (φ z) (g₀ ω))
      (ContinuousMap.const ℂ (-c ω) + (F ω).comp (LQGMetric.affinePt r (φ z))) := by
    rw [hG']
    unfold addConst
    exact SupercriticalLQGUniqueness.Uniqueness.Objects.Producer.addFun_addFun _ _ _
  have hext₁ : ∀ w (hw : w ∈ L),
      (ContinuousMap.const ℂ (-c ω) + (F ω).comp (LQGMetric.affinePt r (φ z))) w =
        resC hLW (zoomCorr (φ z) hr (f ω) (c ω)) ⟨w, hw⟩ := by
    intro w hw
    have hBw' : LQGMetric.affinePt r (φ z) w ∈ A := by
      rw [LQGMetric.affinePt_apply, add_comm]
      exact mem_image_of_mem B hw
    simp only [ContinuousMap.add_apply, ContinuousMap.const_apply, ContinuousMap.comp_apply]
    rw [SupercriticalConformalCovariance.Domain.cutF_eq V m' (f ω) _ (hm' hBw')]
    simp only [resC, zoomCorr, ContinuousMap.comp_apply, ContinuousMap.add_apply, negConstOn,
      ContinuousMap.coe_mk]
    rw [add_comm]
    rfl
  have hext₂ : ∀ w (hw : w ∈ L),
      cutF W m (zoomCorr (φ z) hr (f ω) (c ω)) w = resC hLW (zoomCorr (φ z) hr (f ω) (c ω)) ⟨w, hw⟩ :=
    fun w hw => SupercriticalConformalCovariance.Domain.cutF_eq W m _ w (hm hw)
  have hf₁ := hw₁ L (resC hLW (zoomCorr (φ z) hr (f ω) (c ω))) _ hext₁
    (⟨ψ u, hψuL⟩, ⟨ψ v, hψvL⟩)
  have hf₂ := hw₁ L (resC hLW (zoomCorr (φ z) hr (f ω) (c ω))) _ hext₂
    (⟨ψ u, hψuL⟩, ⟨ψ v, hψvL⟩)
  have hfg : pathInf (D G') L (ψ u) (ψ v) =
      (D (addFun (affineComp r (φ z) (g₀ ω)) (cutF W m (zoomCorr (φ z) hr (f ω) (c ω))))).internal
        L (⟨ψ u, hψuL⟩, ⟨ψ v, hψvL⟩) := by
    rw [hG'eq, ← SupercriticalConformalCovariance.BiLip.internal_eq_pathInf
      (D (addFun (affineComp r (φ z) (g₀ ω))
        (ContinuousMap.const ℂ (-c ω) + (F ω).comp (LQGMetric.affinePt r (φ z))))) L
      (⟨ψ u, hψuL⟩, ⟨ψ v, hψvL⟩)]
    exact hf₁.symm.trans hf₂
  -- (h) the confined target metric on `K`
  have hh : tgtConf D hφ z hr hRU m (affineComp r (φ z) (g₀ ω)) (zoomCorr (φ z) hr (f ω) (c ω))
      (u, v) =
      (D (addFun (affineComp r (φ z) (g₀ ω)) (cutF W m (zoomCorr (φ z) hr (f ω) (c ω))))).internal
        L (⟨ψ u, hψuL⟩, ⟨ψ v, hψvL⟩) := by
    unfold tgtConf
    rw [SupercriticalConformalCovariance.Small.confPullCompact_on _ _ _ _ _ _ _ hu hv]
    rfl
  calc s * SupercriticalConformalCovariance.Good.transportedE (ξ : ℝ) D hφ (g₀ ω) (f ω) (z + (r : ℂ) * u, z + (r : ℂ) * v)
      = s * weylScaleOn (ξ : ℝ) (f ω) (D (g₀ ω))
          (⟨B (ψ u), hAV hBuA⟩, ⟨B (ψ v), hAV hBvA⟩) := by rw [ha]
    _ ≤ s * weylScaleOn (ξ : ℝ) (resC hAV (f ω)) (D (g₀ ω))
          (⟨B (ψ u), hBuA⟩, ⟨B (ψ v), hBvA⟩) := mul_le_mul' le_rfl hb
    _ = s * (D (addFun (g₀ ω) (F ω))).internal A (⟨B (ψ u), hBuA⟩, ⟨B (ψ v), hBvA⟩) := by
        rw [hc]
    _ = pathInf (D G') L (ψ u) (ψ v) := hd'.symm
    _ = _ := hfg
    _ = _ := hh.symm

/-- The circle-average recentred zoom `ĥ = h(z + r ·) − h_r(z)` of the source field. -/
def zoomField (h : DistC) (z : ℂ) (r : ℝ) : DistC :=
  addConst (affineComp r z h) (-circleAvg h r z)

theorem measurable_circleAvg_comp {Ω : Type} [MeasurableSpace Ω] {h : Ω → DistC}
    (hh : Measurable h) (z : ℂ) (r : ℝ) : Measurable fun ω => circleAvg (h ω) r z :=
  (LQGMetric.measurable_circleAvg_left r z).comp hh

theorem isGFFPlusCont_zoomField {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}
    (hh : IsGFFPlusCont h P) (z : ℂ) {r : ℝ} (hr : 0 < r) :
    IsGFFPlusCont (fun ω => zoomField (h ω) z r) P :=
  SupercriticalLQGUniqueness.Uniqueness.Toolkit.LocalEvents.isGFFPlusCont_addConst
    (LQGMetric.GM.isGFFPlusCont_affineComp hh hr z) (measurable_circleAvg_comp hh.1 z r).neg

/-- **Rescaling a failure** (paper l. 338–360): a regular-pair failure at `(z, r)` gives a failure at
unit scale for the confined source metric of `ĥ` and the confined zoomed target metric, with the
deterministic bounds `m = 1`, `M = (1 - α)⁻¹`, `b = 1 - α`. -/
theorem ae_bad_to_failure {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ} {D : DistC → LSCMetric}
    (hD : IsStrongLQGMetric ξ Q D) {U V : Opens ℂ} {φ : ℂ → ℂ}
    (hφ : IsConformalBijection φ U V) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h g₀ : Ω → DistC) (hh : IsGFFPlusCont h P)
    (hg₀ : IsGFFPlusCont g₀ P) (f : Ω → C(V, ℝ)) (hf : Measurable f)
    (q : Ioo (0 : ℝ) (1 / 100)) (a : Ioo (1 - (q : ℝ)) 1) (θ : Ioi (0 : ℝ)) (η : ℝ)
    (z : ℂ) {r : ℝ} (hr : 0 < r) {R : ℝ} (hR2 : 2 ≤ R)
    (hRU : 0 < R ∧ ball (0 : ℂ) (2 * R) ⊆ affinePreimage U z r) (m : ℕ)
    (hm : zoomMap φ z r '' closedBall 0 R ⊆ exW (affinePreimage V (φ z) r) m) :
    ∀ᵐ ω ∂P, ω ∈ SupercriticalConformalCovariance.Good.RegularBadEvent h (D ∘ h)
        (fun ω => SupercriticalConformalCovariance.Good.transportedE (ξ : ℝ) D hφ (g₀ ω) (f ω)) ξ Q q a θ η z ⟨r, hr⟩ →
      ∃ u v : ℂ, SupercriticalConformalCovariance.Regular.SourceFailure (conf (D (zoomField (h ω) z r)) 0 R)
        (tgtConf D hφ z hr hRU m (affineComp r (φ z) (g₀ ω))
          (zoomCorr (φ z) hr (f ω) (circleAvg (h ω) r z)))
        0 u v 1 a θ 1 ((1 - (a : ℝ))⁻¹ * 1) (1 - a) η := by
  let c : Ω → ℝ := fun ω => circleAvg (h ω) r z
  have hH := isGFFPlusCont_zoomField hh z hr
  have hα0 : (3 / 4 : ℝ) < a := by
    have h1 := a.2.1
    have h2 := q.2.2
    linarith
  have hα : (a : ℝ) < 1 := a.2.2
  filter_upwards [SupercriticalConformalCovariance.Small.ae_sourceRegularPair_rescale hD P h hh ⟨r, hr⟩ z c a θ hα0 hα,
    SupercriticalConformalCovariance.Small.ae_rescaled_source_metric hD P h hh ⟨r, hr⟩ z c,
    SupercriticalConformalCovariance.Domain.ae_sample_of_isGFFPlusCont hD P _ hH,
    ae_target_mono hD hφ P g₀ hg₀ f hf c z hr hRU m hm] with ω hreg hscale hsamp hmono
  rintro ⟨c', hc', u₀, v₀, hreg₀, hfail₀⟩
  have hcc : c' = c ω := (SupercriticalConformalCovariance.Small.circleAvg_eq_of_IsCircleAverage (h ω) ⟨r, hr⟩ z c' hc').symm
  have hreg1 := hreg u₀ v₀ c' hreg₀
  rw [hcc, sub_self, mul_zero, Real.exp_zero] at hreg1
  set T := SupercriticalConformalCovariance.Small.regularZoomHomeo z hr with hT
  set u : ℂ := T.symm u₀ with hu
  set v : ℂ := T.symm v₀ with hv
  have hTu : z + (r : ℂ) * u = u₀ := by
    rw [← SupercriticalConformalCovariance.Small.regularZoomHomeo_apply z hr u, hu, Homeomorph.apply_symm_apply]
  have hTv : z + (r : ℂ) * v = v₀ := by
    rw [← SupercriticalConformalCovariance.Small.regularZoomHomeo_apply z hr v, hv, Homeomorph.apply_symm_apply]
  have huK : u ∈ closedBall (0 : ℂ) R := by
    have hs := hreg1.2.1
    rw [mem_sphere, mul_one] at hs
    rw [mem_closedBall, hs]
    linarith
  have hvK : v ∈ closedBall (0 : ℂ) R := by
    have hs := hreg1.2.2.1
    rw [mem_sphere] at hs
    rw [mem_closedBall, hs]
    linarith
  set s : ℝ≥0∞ := ENNReal.ofReal (r ^ (-((ξ : ℝ) * Q)) * Real.exp (-((ξ : ℝ) * c ω))) with hs
  have hscale' : D (zoomField (h ω) z r) (u, v) = s * D (h ω) (u₀, v₀) := by
    rw [← hTu, ← hTv]
    exact hscale u v
  have hfail : ENNReal.ofReal (1 + η) * D (zoomField (h ω) z r) (u, v) ≤
      s * SupercriticalConformalCovariance.Good.transportedE (ξ : ℝ) D hφ (g₀ ω) (f ω) (u₀, v₀) := by
    rw [hscale', mul_left_comm]
    exact mul_le_mul' le_rfl hfail₀
  have hmono' := hmono u huK v hvK
  rw [hTu, hTv] at hmono'
  refine ⟨u, v, SupercriticalConformalCovariance.Small.sourceFailure_conf_ge_two_of_target_mono (D (zoomField (h ω) z r)) _
    hsamp.2.1 (fun P a b hP _ => SupercriticalConformalCovariance.BiLip.curve_continuousOn hsamp.1 hP) R a θ 1 1 η hR2 u v
    _ ⟨hα0, hα⟩ le_rfl hreg1 hfail hmono'⟩

end SupercriticalConformalCovariance.P43Final
