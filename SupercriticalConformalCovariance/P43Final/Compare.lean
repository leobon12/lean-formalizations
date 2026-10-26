import SupercriticalConformalCovariance.P43Final.Rescale
import SupercriticalConformalCovariance.P43Final.Bridge
import SupercriticalConformalCovariance.P43Final.ConfCompare
import SupercriticalConformalCovariance.BiLip.Final

/-!
# Proposition 4.3: Lemma 2.1 for the zoomed confined metrics, almost surely

Paper l. 352–353. At one scale `(z, r)` the recentred zoom `ĥ` (a normalized whole-plane GFF) and the
corrected zoomed target realization `(g₀ ∘ B, k ∘ B − c)` (from `ZoomRealizationBridge`) form an
instance of Lemma 2.1 on the zoomed global domains (`hIz`). With the deterministic constant `C` of
Lemma 2.1 (independent of the domains and the map, ruling A11 D3), the deterministic comparisons of
`ConfCompare` give, almost surely and for all `x, y ∈ ℂ`,
`conf (D ĥ) 0 R ≤ C · tgtConf` and `tgtConf ≤ C · conf (D ĥ) 0 R`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Metric TopologicalSpace Filter
open scoped ENNReal

namespace SupercriticalConformalCovariance.P43Final

open LQGMetric (DistC addFun addConst affineComp IsGFFPlusCont IsWholePlaneGFF circleAvg)
open SupercriticalLQGUniqueness (LSCMetric IsStrongLQGMetric IsLFPPExponent
  IsNormalizedWholePlaneGFF)
open SupercriticalConformalCovariance (IsConformalBijection weylScaleOn)
open SmallGammaGeodesics.CC (zoomMap)
open SupercriticalConformalCovariance.Small (affinePreimage zoomConformal conf confPullCompact)
open SupercriticalConformalCovariance.Domain (exW cutF resC dV SV)
open SupercriticalConformalCovariance.BiLip (pathInf eT)
open HigherDimLQGMetric (internalWith)

/-- The recentred zoom of a normalized whole-plane GFF is a normalized whole-plane GFF. -/
theorem isNormalized_zoomField {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistC} (hh : IsNormalizedWholePlaneGFF h P) (z : ℂ)
    {r : ℝ} (hr : 0 < r) :
    IsNormalizedWholePlaneGFF (fun ω => zoomField (h ω) z r) P := by
  have hwp : IsWholePlaneGFF (fun ω => zoomField (h ω) z r) P :=
    (hh.1.affineComp hr z).addConst (measurable_circleAvg_comp hh.1.measurable z r).neg
  refine ⟨hwp, ?_⟩
  filter_upwards [LQGMetric.CircleAvg.ae_tendsto_mollAvg hwp 0 one_pos,
    LQGMetric.CircleAvg.ae_circleAvg_addConst (hh.1.affineComp hr z) 0 one_pos,
    LQGMetric.CircleAvg.ae_circleAvg_affineComp hh.1 hr z] with ω ⟨b, hb⟩ hadd haff
  have h1 : circleAvg (zoomField (h ω) z r) 1 0 = b :=
    LQGMetric.CircleAvg.circleAvg_eq_of_tendsto hb
  have h2 : circleAvg (zoomField (h ω) z r) 1 0 = 0 := by
    unfold zoomField
    rw [hadd, haff]
    ring
  have hb0 : b = 0 := h1.symm.trans h2
  rw [hb0] at hb
  exact hb

/-- The zoomed data form an instance of Lemma 2.1 on the zoomed global domains. -/
theorem isInstance_zoom (hB : ZoomRealizationBridge) {Q : ℝ} {U V : Opens ℂ} {φ : ℂ → ℂ}
    (hφ : IsConformalBijection φ U V) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h g₀ : Ω → DistC} {f : Ω → C(V, ℝ)}
    (hI : SupercriticalConformalCovariance.BiLip.IsInstance Q U V hφ P h g₀ f) (z : ℂ) {r : ℝ} (hr : 0 < r) :
    SupercriticalConformalCovariance.BiLip.IsInstance Q (affinePreimage U z r) (affinePreimage V (φ z) r) (zoomConformal hφ z hr)
      P (fun ω => zoomField (h ω) z r) (fun ω => affineComp r (φ z) (g₀ ω))
      (fun ω => zoomCorr (φ z) hr (f ω) (circleAvg (h ω) r z)) :=
  ⟨isNormalized_zoomField hI.1 z hr,
    hB Q hφ z hr hI.2 (fun ω => circleAvg (h ω) r z)
      (measurable_circleAvg_comp hI.1.1.measurable z r)⟩

/-- **Lemma 2.1 for the zoomed confined metrics**, almost surely, on all of `ℂ × ℂ`. -/
theorem ae_conf_comparison {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ} {D : DistC → LSCMetric}
    (hD : IsStrongLQGMetric ξ Q D) (hB : ZoomRealizationBridge) {C : ℝ} (hC1 : 1 ≤ C)
    (H21 : ∀ (U V : Opens ℂ) (φ : ℂ → ℂ) (hφ : IsConformalBijection φ U V)
      {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h g₀ : Ω → DistC) (k : Ω → C(V, ℝ)), SupercriticalConformalCovariance.BiLip.IsInstance Q U V hφ P h g₀ k →
      ∀ᵐ ω ∂P, ∀ u ∈ (U : Set ℂ), ∀ v ∈ (U : Set ℂ),
        eT (D (g₀ ω)) ξ (k ω) φ u v ≤ ENNReal.ofReal C * pathInf (D (h ω)) U u v ∧
        pathInf (D (h ω)) U u v ≤ ENNReal.ofReal C * eT (D (g₀ ω)) ξ (k ω) φ u v)
    {U V : Opens ℂ} {φ : ℂ → ℂ} (hφ : IsConformalBijection φ U V)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h g₀ : Ω → DistC) (f : Ω → C(V, ℝ)) (hI : SupercriticalConformalCovariance.BiLip.IsInstance Q U V hφ P h g₀ f)
    (z : ℂ) {r : ℝ} (hr : 0 < r) {R : ℝ}
    (hRU : 0 < R ∧ ball (0 : ℂ) (2 * R) ⊆ affinePreimage U z r) (m : ℕ)
    (hm : zoomMap φ z r '' closedBall 0 R ⊆ exW (affinePreimage V (φ z) r) m) :
    ∀ᵐ ω ∂P, ∀ x y : ℂ,
      conf (D (zoomField (h ω) z r)) 0 R (x, y) ≤ ENNReal.ofReal C *
          tgtConf D hφ z hr hRU m (affineComp r (φ z) (g₀ ω))
            (zoomCorr (φ z) hr (f ω) (circleAvg (h ω) r z)) (x, y) ∧
        tgtConf D hφ z hr hRU m (affineComp r (φ z) (g₀ ω))
            (zoomCorr (φ z) hr (f ω) (circleAvg (h ω) r z)) (x, y) ≤
          ENNReal.ofReal C * conf (D (zoomField (h ω) z r)) 0 R (x, y) := by
  classical
  set W : Opens ℂ := affinePreimage V (φ z) r with hW
  set Uz : Opens ℂ := affinePreimage U z r with hUz
  set ψ : ℂ → ℂ := zoomMap φ z r with hψ
  set K : Set ℂ := closedBall (0 : ℂ) R with hK
  set L : Set ℂ := ψ '' K with hL
  have hψc : IsConformalBijection ψ Uz W := zoomConformal hφ z hr
  have hKU : K ⊆ Uz := closedBall_subset_zoom hRU
  have hψKW : MapsTo ψ K W := fun w hw => hψc.2.mapsTo (hKU hw)
  have hLW : L ⊆ (W : Set ℂ) := by
    rintro _ ⟨w, hw, rfl⟩
    exact hψKW hw
  have hinv := SupercriticalConformalCovariance.GM24.isConformalBijection_invFunOn hψc
  have hχc : ContinuousOn (Function.invFunOn ψ Uz) L := hinv.1.continuousOn.mono hLW
  have hχψ : ∀ x ∈ K, Function.invFunOn ψ Uz (ψ x) = x := fun x hx =>
    hψc.2.injOn.leftInvOn_invFunOn (hKU hx)
  have hIz := isInstance_zoom hB hφ hI z hr
  have hg₁ : IsGFFPlusCont (fun ω => affineComp r (φ z) (g₀ ω)) P :=
    LQGMetric.GM.isGFFPlusCont_affineComp hI.2.2.1 hr (φ z)
  have hC0 : ENNReal.ofReal C ≠ 0 := (ENNReal.ofReal_pos.2 (by linarith)).ne'
  have hCt : ENNReal.ofReal C ≠ ⊤ := ENNReal.ofReal_ne_top
  filter_upwards [H21 Uz W ψ hψc P _ _ _ hIz, SupercriticalConformalCovariance.Domain.ae_sample_of_isGFFPlusCont hD P _ hg₁,
    SupercriticalConformalCovariance.Domain.ae_weylScaleOn_eq_internal hD P hg₁] with ω hcmp hsamp hw
  intro x y
  set fr := zoomCorr (φ z) hr (f ω) (circleAvg (h ω) r z) with hfr
  set M₁ := D (zoomField (h ω) z r) with hM₁
  set D₀ := D (affineComp r (φ z) (g₀ ω)) with hD₀
  set T := tgtConf D hφ z hr hRU m (affineComp r (φ z) (g₀ ω)) fr with hTdef
  by_cases hxy : x = y
  · subst y
    have h1 : conf M₁ 0 R (x, x) = 0 := (conf M₁ 0 R).2.1.1 x
    have h2 : T (x, x) = 0 := T.2.1.1 x
    rw [h1, h2, mul_zero]
    exact ⟨le_rfl, le_rfl⟩
  by_cases hin : x ∈ K ∧ y ∈ K
  · obtain ⟨hx, hy⟩ := hin
    have hS : conf M₁ 0 R (x, y) = pathInf M₁ K x y := by
      rw [SupercriticalConformalCovariance.Small.conf_apply, SupercriticalConformalCovariance.Small.confKernel_eq_intrinsic M₁ 0 R hx hy]
      rfl
    have hT : T (x, y) = internalWith (dV D₀ ξ fr) (SV D₀ L) (D₀.pt (ψ x)) (D₀.pt (ψ y)) := by
      rw [hTdef]
      unfold tgtConf
      rw [SupercriticalConformalCovariance.Small.confPullCompact_on _ _ _ _ _ _ _ hx hy]
      have hext : ∀ w (hw : w ∈ L), cutF W m fr w = resC hLW fr ⟨w, hw⟩ :=
        fun w hw => SupercriticalConformalCovariance.Domain.cutF_eq W m fr w (hm hw)
      have h1 := hw L (resC hLW fr) (cutF W m fr) hext
        (⟨ψ x, mem_image_of_mem ψ hx⟩, ⟨ψ y, mem_image_of_mem ψ hy⟩)
      have h2 := SupercriticalConformalCovariance.Domain.weylScaleOn_resC_eq_internalWith (ξ := (ξ : ℝ)) hsamp.1 W.isOpen hLW fr
        (⟨ψ x, mem_image_of_mem ψ hx⟩, ⟨ψ y, mem_image_of_mem ψ hy⟩)
      exact h1.symm.trans h2
    rw [hS, hT]
    exact ⟨confinedSource_le M₁ D₀ ξ fr W.isOpen hsamp.1 hsamp.2.1 ψ (Function.invFunOn ψ Uz)
        hKU hψKW hχc hχψ hC0 hCt (fun u hu v hv => (hcmp u hu v hv).2) x y hx hy,
      confinedTarget_le M₁ D₀ ξ fr W.isOpen hsamp.1 ψ hKU hψKW hC0 hCt
        (fun u hu v hv => (hcmp u hu v hv).1) x y⟩
  · have h1 : conf M₁ 0 R (x, y) = ⊤ := by
      rw [SupercriticalConformalCovariance.Small.conf_apply]
      exact SupercriticalConformalCovariance.Small.confKernel_outside M₁ 0 R hxy hin
    have h2 : T (x, y) = ⊤ := by
      rw [hTdef]
      unfold tgtConf
      exact SupercriticalConformalCovariance.Small.extendMetric_off _ _ hxy hin
    rw [h1, h2, ENNReal.mul_top hC0]
    exact ⟨le_rfl, le_rfl⟩

end SupercriticalConformalCovariance.P43Final
