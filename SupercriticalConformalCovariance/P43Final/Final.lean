import SupercriticalConformalCovariance.P43Final.Compare
import SupercriticalConformalCovariance.P43Final.Skorokhod
import SupercriticalConformalCovariance.Small.ZoomSequenceGeometry
import SupercriticalConformalCovariance.Small.Uniformity
import SupercriticalConformalCovariance.Root.Forward

/-!
# Proposition 4.3 from the zoom realization bridge

`prop43Input_of_bridge`: `ZoomRealizationBridge → SupercriticalConformalCovariance.Root.Prop43Input ξ Q D` for every strong LQG
metric `D` with LFPP exponent `Q` (paper l. 331–370). Route (paper's proof, in order):

1. **Uniformity** (l. 369–370): `SupercriticalConformalCovariance.Small.uniform_small_scale_of_sequential` reduces the uniform
   statement to sequences `z_n ∈ K`, `z_n → z`, `r_n ↓ 0`; a non-vanishing failure probability gives a
   subsequence with failure probability `≥ ε` (`seq_failure_contradiction`).
2. **Rescaling** (l. 338–350): the circle-average recentred zooms `ĥ_n = h(z_n + r_n ·) − h_{r_n}(z_n)`
   (one law for all `n`), the zoomed maps `ψ_n = zoomMap φ z_n r_n` and global zoomed domains; their
   geometry (`SupercriticalConformalCovariance.Small.zoom_sequence_tangent_geometry`), and the corrected target realizations
   (`ZoomRealizationBridge`).
3. **Lemma 3.3** in law for the triangular array, on the diagonal-corrected confined metrics
   (`SupercriticalConformalCovariance.Small.tangent_limit_conf_law_varying`, proved from the sealed-closure Lemma 3.3).
4. **Confinement and Lemma 2.1** (l. 351–355): a failure at `(z_n, r_n)` is a unit-scale failure of the
   confined metrics (`ae_bad_to_failure`), and Lemma 2.1 compares them with one deterministic `C`
   (`ae_conf_comparison`).
5. **Selection, Skorokhod, Lemma 4.1** (l. 361–368): `skorokhod_failure_contradiction`.

The recentring constant is the circle average `h_r(z)` of (7) itself (the paper uses a smooth average and
then a Gaussian tail for the gap, l. 356–358); with the circle average the gap is `0` and the bound of (7)
is the deterministic `(1 - α)⁻¹` (see the report).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Metric TopologicalSpace Filter Topology
open scoped ENNReal

namespace SupercriticalConformalCovariance.P43Final

open LQGMetric (DistC addFun addConst affineComp affinePt ofCont IsGFFPlusCont IsWholePlaneGFF
  circleAvg restrictTo CoordJ pairJ)
open SupercriticalLQGUniqueness (LSCMetric LSCFun IsStrongLQGMetric IsLFPPExponent
  IsNormalizedWholePlaneGFF)
open SupercriticalLQGUniqueness.B2.PfeAxioms (IsMetricLSCFun)
open SupercriticalConformalCovariance (IsConformalBijection confPullbackField IsDomainRealization)
open SmallGammaGeodesics.CC (zoomMap)
open SupercriticalConformalCovariance.Small (affinePreimage zoomConformal affinePreimage_conformal conf confPullCompact
  ambientMetricLift zoomRealizationData)
open SupercriticalConformalCovariance.Tangent (imageMapK imageMapK_injective)
open SupercriticalConformalCovariance.Domain (exW cutF)

local instance p43FinalMeasurableSpaceLSCFun : MeasurableSpace LSCFun := borel LSCFun
local instance p43FinalBorelSpaceLSCFun : BorelSpace LSCFun := ⟨rfl⟩

/-- The bridge as the realization data of `tangent_limit_conf_law_varying` (the hypothesis version of
`zoomRealizationData_realization`). -/
theorem zoomData_realization_of_bridge (hB : ZoomRealizationBridge) (Q : ℝ)
    {U V : Opens ℂ} {φ : ℂ → ℂ} (hφ : IsConformalBijection φ U V)
    (z : ℂ) {r : ℝ} (hr : 0 < r)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (h g : Ω → DistC) (k : Ω → C(V, ℝ))
    (hR : IsDomainRealization V P
      (fun ω => confPullbackField Q (SupercriticalConformalCovariance.Reversal.inverse_conformal hφ)
        (restrictTo U (h ω))) g k)
    (F₀ : Ω → C(ℂ, ℝ))
    (hwp : IsWholePlaneGFF (fun ω => g ω - ofCont (F₀ ω)) P)
    (c : Ω → ℝ) (hc : Measurable c) :
    IsDomainRealization (affinePreimage V (φ z) r) P
      (fun ω => (zoomRealizationData Q hφ z hr (addConst (affineComp r z (h ω)) (-c ω),
        ((confPullbackField Q (SupercriticalConformalCovariance.Reversal.inverse_conformal hφ) (restrictTo U (h ω)), g ω,
          (k ω, F₀ ω)), c ω))).1)
      (fun ω => (zoomRealizationData Q hφ z hr (addConst (affineComp r z (h ω)) (-c ω),
        ((confPullbackField Q (SupercriticalConformalCovariance.Reversal.inverse_conformal hφ) (restrictTo U (h ω)), g ω,
          (k ω, F₀ ω)), c ω))).2.1)
      (fun ω => (zoomRealizationData Q hφ z hr (addConst (affineComp r z (h ω)) (-c ω),
        ((confPullbackField Q (SupercriticalConformalCovariance.Reversal.inverse_conformal hφ) (restrictTo U (h ω)), g ω,
          (k ω, F₀ ω)), c ω))).2.2.1) ∧
    IsWholePlaneGFF
      (fun ω => (zoomRealizationData Q hφ z hr (addConst (affineComp r z (h ω)) (-c ω),
          ((confPullbackField Q (SupercriticalConformalCovariance.Reversal.inverse_conformal hφ) (restrictTo U (h ω)), g ω,
            (k ω, F₀ ω)), c ω))).2.1 -
        ofCont (zoomRealizationData Q hφ z hr (addConst (affineComp r z (h ω)) (-c ω),
          ((confPullbackField Q (SupercriticalConformalCovariance.Reversal.inverse_conformal hφ) (restrictTo U (h ω)), g ω,
            (k ω, F₀ ω)), c ω))).2.2.2) P :=
  ⟨hB Q hφ z hr hR c hc, SupercriticalConformalCovariance.Small.wholePlaneGFF_zoom_witness P g F₀ hwp (φ z) hr⟩

/-- The source confinement class of Lemma 4.1's metric coordinates. -/
def srcClass (R : ℝ) : Set LSCFun :=
  Set.range (fun G : LSCFun => (conf (ambientMetricLift G) 0 R).toLSCFun)

theorem goodShape_of_mem_srcClass {R : ℝ} {F : LSCFun} (hF : F ∈ srcClass R) : GoodShape F := by
  obtain ⟨G, rfl⟩ := hF
  refine ⟨SupercriticalLQGUniqueness.B2.PfeAxioms.isMetricLSCFun_toLSCFun _, ?_⟩
  exact SupercriticalConformalCovariance.Small.conf_image_geometry 0 R _ ⟨G, rfl⟩

/-- The target confinement class at one scale, with the carriers of `tgtConf`. -/
def tgtClass {U V : Opens ℂ} {φ : ℂ → ℂ} (hφ : IsConformalBijection φ U V) (z : ℂ) {r : ℝ}
    (hr : 0 < r) {R : ℝ} (hRU : 0 < R ∧ ball (0 : ℂ) (2 * R) ⊆ affinePreimage U z r) :
    Set LSCFun :=
  Set.range (fun G : LSCFun => (confPullCompact (ambientMetricLift G)
    (zoomMap φ z r '' closedBall 0 R) (closedBall 0 R) (isCompact_closedBall _ _)
    ((isCompact_closedBall _ _).image_of_continuousOn
      ((zoomConformal hφ z hr).1.continuousOn.mono
        ((closedBall_subset_ball (by linarith [hRU.1])).trans hRU.2)))
    (imageMapK (zoomMap φ z r) _
      ((zoomConformal hφ z hr).1.continuousOn.mono
        ((closedBall_subset_ball (by linarith [hRU.1])).trans hRU.2)))
    (imageMapK_injective _ ((zoomConformal hφ z hr).2.injOn.mono
      ((closedBall_subset_ball (by linarith [hRU.1])).trans hRU.2)))).toLSCFun)

theorem um_tgtClass {U V : Opens ℂ} {φ : ℂ → ℂ} (hφ : IsConformalBijection φ U V) (z : ℂ) {r : ℝ}
    (hr : 0 < r) {R : ℝ} (hRU : 0 < R ∧ ball (0 : ℂ) (2 * R) ⊆ affinePreimage U z r) :
    LQGMetric.UMeasurableSet (tgtClass hφ z hr hRU) :=
  SupercriticalConformalCovariance.Small.um_target_confined_image _ _ _ _ _ _

theorem tgtConf_mem_tgtClass (D : DistC → LSCMetric) {U V : Opens ℂ} {φ : ℂ → ℂ}
    (hφ : IsConformalBijection φ U V) (z : ℂ) {r : ℝ} (hr : 0 < r) {R : ℝ}
    (hRU : 0 < R ∧ ball (0 : ℂ) (2 * R) ⊆ affinePreimage U z r) (m : ℕ)
    (g : DistC) (k : C(affinePreimage V (φ z) r, ℝ)) :
    (tgtConf D hφ z hr hRU m g k).toLSCFun ∈ tgtClass hφ z hr hRU :=
  SupercriticalConformalCovariance.Small.target_conf_mem_um_image _ _ _ _ _ _ _

theorem goodShape_of_mem_tgtClass {U V : Opens ℂ} {φ : ℂ → ℂ} (hφ : IsConformalBijection φ U V)
    (z : ℂ) {r : ℝ} (hr : 0 < r) {R : ℝ}
    (hRU : 0 < R ∧ ball (0 : ℂ) (2 * R) ⊆ affinePreimage U z r) {F : LSCFun}
    (hF : F ∈ tgtClass hφ z hr hRU) : GoodShape F := by
  classical
  have hψc := zoomConformal hφ z hr
  have hKU : closedBall (0 : ℂ) R ⊆ affinePreimage U z r := closedBall_subset_zoom hRU
  let ψ := zoomMap φ z r
  let Uz : Set ℂ := affinePreimage U z r
  have hLW : ψ '' closedBall 0 R ⊆ (affinePreimage V (φ z) r : Set ℂ) := by
    rintro _ ⟨w, hw, rfl⟩
    exact hψc.2.mapsTo (hKU hw)
  have hχc : ContinuousOn (Function.invFunOn ψ Uz) (ψ '' closedBall 0 R) :=
    (SupercriticalConformalCovariance.GM24.isConformalBijection_invFunOn hψc).1.continuousOn.mono hLW
  have hmemK : ∀ y : ψ '' closedBall (0 : ℂ) R, Function.invFunOn ψ Uz y ∈ closedBall (0 : ℂ) R := by
    rintro ⟨_, ⟨x, hx, rfl⟩⟩
    change Function.invFunOn ψ Uz (ψ x) ∈ closedBall (0 : ℂ) R
    rw [hψc.2.injOn.leftInvOn_invFunOn (hKU hx)]
    exact hx
  let jInv : C(ψ '' closedBall (0 : ℂ) R, closedBall (0 : ℂ) R) :=
    ⟨fun y => ⟨Function.invFunOn ψ Uz y, hmemK y⟩,
      ((hχc.comp_continuous continuous_subtype_val fun y => y.2).subtype_mk _)⟩
  have hjInv : ∀ y : ψ '' closedBall (0 : ℂ) R,
      imageMapK ψ (closedBall 0 R) (hψc.1.continuousOn.mono hKU) (jInv y) = y := by
    rintro ⟨_, ⟨x, hx, rfl⟩⟩
    apply Subtype.ext
    change ψ (Function.invFunOn ψ Uz (ψ x)) = ψ x
    rw [hψc.2.injOn.leftInvOn_invFunOn (hKU hx)]
  obtain ⟨G, rfl⟩ := hF
  refine ⟨SupercriticalLQGUniqueness.B2.PfeAxioms.isMetricLSCFun_toLSCFun _, ?_⟩
  exact SupercriticalConformalCovariance.Small.target_conf_image_geometry _ _ _ _ _ _ jInv hjInv _ ⟨G, rfl⟩

/-- **The sequential contradiction** (paper l. 335–368), for the shifted zoom data. -/
theorem seq_core {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ} (hQ : IsLFPPExponent ξ Q)
    {D : DistC → LSCMetric} (hD : IsStrongLQGMetric ξ Q D) (hB : ZoomRealizationBridge)
    {C : ℝ} (hC1 : 1 ≤ C)
    (H21 : ∀ (U V : Opens ℂ) (φ : ℂ → ℂ) (hφ : IsConformalBijection φ U V)
      {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h g₀ : Ω → DistC) (k : Ω → C(V, ℝ)), SupercriticalConformalCovariance.BiLip.IsInstance Q U V hφ P h g₀ k →
      ∀ᵐ ω ∂P, ∀ u ∈ (U : Set ℂ), ∀ v ∈ (U : Set ℂ),
        SupercriticalConformalCovariance.BiLip.eT (D (g₀ ω)) ξ (k ω) φ u v ≤
            ENNReal.ofReal C * SupercriticalConformalCovariance.BiLip.pathInf (D (h ω)) U u v ∧
        SupercriticalConformalCovariance.BiLip.pathInf (D (h ω)) U u v ≤
            ENNReal.ofReal C * SupercriticalConformalCovariance.BiLip.eT (D (g₀ ω)) ξ (k ω) φ u v)
    (q : Ioo (0 : ℝ) (1 / 100)) (a : Ioo (1 - (q : ℝ)) 1) (θ : Ioi (0 : ℝ)) (η : ℝ) (hη : 0 < η)
    {U V : Opens ℂ} {φ : ℂ → ℂ} (hφ : IsConformalBijection φ U V)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h g₀ : Ω → DistC) (f : Ω → C(V, ℝ)) (hI : SupercriticalConformalCovariance.BiLip.IsInstance Q U V hφ P h g₀ f)
    (z : ℕ → ℂ) (r : ℕ → ℝ) (hrpos : ∀ n, 0 < r n)
    {R : ℕ → ℝ} (hR : Tendsto R atTop atTop) (hR2 : ∀ n, 2 ≤ R n)
    (hRU : ∀ n, 0 < R n ∧ ball (0 : ℂ) (2 * R n) ⊆ affinePreimage U (z n) (r n))
    (hexhaust : ∀ K : Set ℂ, IsCompact K → ∀ᶠ n in atTop,
      K ⊆ (affinePreimage U (z n) (r n) : Set ℂ))
    (hzero : ∀ n, zoomMap φ (z n) (r n) 0 = 0) {a₀ : ℂ} (ha0 : a₀ ≠ 0)
    (ha : Tendsto (fun n => deriv (zoomMap φ (z n) (r n)) 0) atTop (𝓝 a₀))
    (ε : ℝ≥0∞) (hε : 0 < ε)
    (hbad : ∀ n, ε ≤ P (SupercriticalConformalCovariance.Good.RegularBadEvent h (D ∘ h)
      (fun ω => SupercriticalConformalCovariance.Good.transportedE (ξ : ℝ) D hφ (g₀ ω) (f ω)) ξ Q q a θ η (z n)
        ⟨r n, hrpos n⟩)) :
    False := by
  classical
  -- fields, marks and realization data
  have hh : IsGFFPlusCont h P := LQGMetric.GM.Tight.isGFFPlusCont_of_wp hI.1.1
  have hg₀ : IsGFFPlusCont g₀ P := hI.2.2.1
  have hfm : Measurable f := hI.2.2.2.1
  obtain ⟨-, F₀, hF₀m, hF₀wp⟩ := id hg₀
  let c : ℕ → Ω → ℝ := fun n ω => circleAvg (h ω) (r n) (z n)
  have hcm : ∀ n, Measurable (c n) := fun n => measurable_circleAvg_comp hh.1 (z n) (r n)
  let H : ℕ → Ω → DistC := fun n ω => zoomField (h ω) (z n) (r n)
  have hHm : ∀ n, Measurable (H n) := fun n => (isGFFPlusCont_zoomField hh (z n) (hrpos n)).1
  let Y : Type := SupercriticalConformalCovariance.Transport.RealizationData V × ℝ
  have : LocallyCompactSpace (V : Set ℂ) := V.isOpen.locallyCompactSpace
  let mark : ℕ → Ω → Y := fun n ω =>
    ((confPullbackField Q (SupercriticalConformalCovariance.Reversal.inverse_conformal hφ) (restrictTo U (h ω)), g₀ ω,
      (f ω, F₀ ω)), c n ω)
  have hmarkm : ∀ n, Measurable (mark n) := by
    intro n
    have h1 : Measurable fun ω =>
        confPullbackField Q (SupercriticalConformalCovariance.Reversal.inverse_conformal hφ) (restrictTo U (h ω)) :=
      (SupercriticalConformalCovariance.Root.measurable_confPullbackField Q _).comp
        ((LQGMetric.measurable_restrictTo _).comp hh.1)
    exact (h1.prodMk (hI.2.2.1.1.prodMk (hfm.prodMk hF₀m))).prodMk (hcm n)
  let hψ : ∀ n, IsConformalBijection (zoomMap φ (z n) (r n)) (affinePreimage U (z n) (r n))
      (affinePreimage V (φ (z n)) (r n)) := fun n => zoomConformal hφ (z n) (hrpos n)
  let J : ∀ n, DistC × Y → SupercriticalConformalCovariance.Transport.RealizationData (affinePreimage V (φ (z n)) (r n)) :=
    fun n => zoomRealizationData Q hφ (z n) (hrpos n)
  have hJ : ∀ n, Measurable (J n) := fun n =>
    SupercriticalConformalCovariance.Small.measurable_zoomRealizationData Q hφ (z n) (hrpos n)
  have hfield : ∀ n p, (J n p).1 =
      confPullbackField Q (SupercriticalConformalCovariance.GM24.isConformalBijection_invFunOn (hψ n))
        (restrictTo (affinePreimage U (z n) (r n)) p.1) := fun n p => rfl
  have hRZ := fun n => zoomData_realization_of_bridge hB Q hφ (z n) (hrpos n) P h g₀ f hI.2 F₀
    hF₀wp (c n) (hcm n)
  -- the common field law
  have hnorm : LQGMetric.IsNormalizedWPGFF h P := ⟨hI.1.1, hI.1.2.mono fun ω hω =>
    SupercriticalConformalCovariance.Small.circleAvg_eq_of_IsCircleAverage (h ω) ⟨1, Set.mem_Ioi.mpr one_pos⟩ 0 0 hω⟩
  let μ : Measure DistC := P.map h
  haveI : IsProbabilityMeasure μ := (Measure.isProbabilityMeasure_map_iff hh.1.aemeasurable).2 inferInstance
  have hlaw : ∀ n, P.map (H n) = μ := fun n =>
    LQGMetric.CircleAvg.map_affine_sub_circleAvg hnorm (hrpos n) (z n)
  have hwpH : IsWholePlaneGFF (H 0) P := (isNormalized_zoomField hI.1 (z 0) (hrpos 0)).1
  haveI : Nonempty Y := inferInstance
  have hg₁m : ∀ n, Measurable fun ω => affineComp (r n) (φ (z n)) (g₀ ω) := fun n =>
    (LQGMetric.measurable_affineComp (r n) (φ (z n))).comp hI.2.2.1.1
  -- Lemma 3.3 in law along the triangular array
  obtain ⟨m, hm, hconv⟩ := SupercriticalConformalCovariance.Small.tangent_limit_conf_law_varying hQ hD hψ hexhaust hzero ha0 ha
    hR hRU P H mark hHm hmarkm μ (Classical.arbitrary Y) hlaw hwpH J hJ hfield
    (fun n => (hRZ n).1) (fun n => (hRZ n).2)
  let Xn : ℕ → Ω → (CoordJ → ℝ) × (LSCFun × LSCFun) := fun n ω =>
    (pairJ ⊤ (H n ω), (conf (D (H n ω)) 0 (R n)).toLSCFun,
      (tgtConf D hφ (z n) (hrpos n) (hRU n) (m n) (affineComp (r n) (φ (z n)) (g₀ ω))
        (zoomCorr (φ (z n)) (hrpos n) (f ω) (c n ω))).toLSCFun)
  let Xlim : Ω → (CoordJ → ℝ) × (LSCFun × LSCFun) := fun ω =>
    (pairJ ⊤ (H 0 ω), (D (H 0 ω)).toLSCFun, (D (H 0 ω)).toLSCFun)
  have hto : Measurable (LSCMetric.toLSCFun) :=
    SupercriticalLQGUniqueness.B2.LscTop.measurable_toLSCFun
  have hXm : ∀ n, Measurable (Xn n) := by
    intro n
    have hfrM : Measurable fun ω => zoomCorr (φ (z n)) (hrpos n) (f ω) (c n ω) :=
      ((measurable_fst.comp measurable_snd).comp measurable_snd).comp
        ((hJ n).comp ((hHm n).prodMk (hmarkm n)))
    have hF : Measurable fun ω => addFun (affineComp (r n) (φ (z n)) (g₀ ω))
        (cutF (affinePreimage V (φ (z n)) (r n)) (m n)
          (zoomCorr (φ (z n)) (hrpos n) (f ω) (c n ω))) :=
      LQGMetric.measurable_addFun.comp ((hg₁m n).prodMk
        (SupercriticalConformalCovariance.Domain.measurable_cutExt (affinePreimage V (φ (z n)) (r n)).isOpen
          (SupercriticalConformalCovariance.Domain.tsupport_cutoff_subset _ (m n)) hfrM))
    refine ((LQGMetric.measurable_pairJ ⊤).comp (hHm n)).prodMk
      (((SupercriticalConformalCovariance.Small.measurable_conf 0 (R n)).comp (hD.1.comp (hHm n))).prodMk ?_)
    exact (SupercriticalConformalCovariance.Small.measurable_confPullCompact _ _ _ _ _ _).comp (hD.1.comp hF)
  have hXlim : Measurable Xlim :=
    ((LQGMetric.measurable_pairJ ⊤).comp (hHm 0)).prodMk
      ((hto.comp (hD.1.comp (hHm 0))).prodMk (hto.comp (hD.1.comp (hHm 0))))
  have hconv' : ∀ F : BoundedContinuousFunction ((CoordJ → ℝ) × (LSCFun × LSCFun)) ℝ,
      Tendsto (fun n => ∫ ω, F (Xn n ω) ∂P) atTop (𝓝 (∫ ω, F (Xlim ω) ∂P)) := fun F => hconv F
  have hlim : ∀ᵐ ω ∂P, (Xlim ω).2.1 = (Xlim ω).2.2 ∧ IsMetricLSCFun (Xlim ω).2.1 :=
    ae_of_all _ fun ω => ⟨rfl, SupercriticalLQGUniqueness.B2.PfeAxioms.isMetricLSCFun_toLSCFun _⟩
  have hshape : ∀ n, ∀ᵐ ω ∂P, (Xn n ω).2.1 ∈ srcClass (R n) ∧
      (Xn n ω).2.2 ∈ tgtClass hφ (z n) (hrpos n) (hRU n) := fun n =>
    ae_of_all _ fun ω => ⟨SupercriticalConformalCovariance.Small.conf_mem_um_image _ 0 (R n),
      tgtConf_mem_tgtClass D hφ (z n) (hrpos n) (hRU n) (m n) _ _⟩
  have hcpos : 0 < C.toNNReal := Real.toNNReal_pos.2 (by linarith)
  have hcomp : ∀ n, ∀ᵐ ω ∂P, ∀ x y : ℂ,
      ambientMetricLift (Xn n ω).2.1 (x, y) ≤
          (C.toNNReal : ℝ≥0∞) * ambientMetricLift (Xn n ω).2.2 (x, y) ∧
      ambientMetricLift (Xn n ω).2.2 (x, y) ≤
          (C.toNNReal : ℝ≥0∞) * ambientMetricLift (Xn n ω).2.1 (x, y) := by
    intro n
    filter_upwards [ae_conf_comparison hD hB hC1 H21 hφ P h g₀ f hI (z n) (hrpos n) (hRU n) (m n)
      (hm n)] with ω hω x y
    simp only [Xn, SupercriticalConformalCovariance.Small.ambientMetricLift_eq]
    exact hω x y
  have hα0 : (0 : ℝ) ≤ a := by
    have h1 := a.2.1
    have h2 := q.2.2
    linarith
  have hα : (a : ℝ) < 1 := a.2.2
  let M : NNReal := ⟨(1 - (a : ℝ))⁻¹ * 1, by
    have : 0 < 1 - (a : ℝ) := by linarith
    positivity⟩
  have hbad' : ∀ n, ε ≤ P {ω | ∃ u v : ℂ, FailAt a θ 1 M η (Xn n ω).2 u v} := by
    intro n
    refine (hbad n).trans (measure_mono_ae ?_)
    filter_upwards [ae_bad_to_failure hD hφ P h g₀ hh hg₀ f hfm q a θ η (z n) (hrpos n) (hR2 n)
      (hRU n) (m n) (hm n)] with ω hω hb
    obtain ⟨u, v, huv⟩ := hω hb
    refine ⟨u, v, ?_⟩
    unfold FailAt
    simp only [Xn, SupercriticalConformalCovariance.Small.ambientMetricLift_eq]
    exact huv
  exact skorokhod_failure_contradiction P Xn hXm Xlim hXlim hconv' hlim
    (fun n => srcClass (R n)) (fun n => tgtClass hφ (z n) (hrpos n) (hRU n))
    (fun n => SupercriticalConformalCovariance.Small.um_confined_image 0 (R n)) (fun n => um_tgtClass hφ (z n) (hrpos n) (hRU n))
    (fun n F hF => goodShape_of_mem_srcClass hF)
    (fun n F hF => goodShape_of_mem_tgtClass hφ (z n) (hrpos n) (hRU n) hF)
    hshape C.toNNReal hcpos hcomp a θ 1 hα0 hα θ.2 M η hη ε hε hbad'

/-- **The sequential contradiction** for an arbitrary failing sequence `z_n → z ∈ K`, `r_n ↓ 0`
(paper l. 335–368): the zoom geometry of Lemma 3.3, a shift making all disks of radius `≥ 2`, and
`seq_core`. -/
theorem seq_failure_contradiction {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ} (hQ : IsLFPPExponent ξ Q)
    {D : DistC → LSCMetric} (hD : IsStrongLQGMetric ξ Q D) (hB : ZoomRealizationBridge)
    {C : ℝ} (hC1 : 1 ≤ C)
    (H21 : ∀ (U V : Opens ℂ) (φ : ℂ → ℂ) (hφ : IsConformalBijection φ U V)
      {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h g₀ : Ω → DistC) (k : Ω → C(V, ℝ)), SupercriticalConformalCovariance.BiLip.IsInstance Q U V hφ P h g₀ k →
      ∀ᵐ ω ∂P, ∀ u ∈ (U : Set ℂ), ∀ v ∈ (U : Set ℂ),
        SupercriticalConformalCovariance.BiLip.eT (D (g₀ ω)) ξ (k ω) φ u v ≤
            ENNReal.ofReal C * SupercriticalConformalCovariance.BiLip.pathInf (D (h ω)) U u v ∧
        SupercriticalConformalCovariance.BiLip.pathInf (D (h ω)) U u v ≤
            ENNReal.ofReal C * SupercriticalConformalCovariance.BiLip.eT (D (g₀ ω)) ξ (k ω) φ u v)
    (q : Ioo (0 : ℝ) (1 / 100)) (a : Ioo (1 - (q : ℝ)) 1) (θ : Ioi (0 : ℝ)) (η : ℝ) (hη : 0 < η)
    {U V : Opens ℂ} {φ : ℂ → ℂ} (hφ : IsConformalBijection φ U V)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h g₀ : Ω → DistC) (f : Ω → C(V, ℝ)) (hI : SupercriticalConformalCovariance.BiLip.IsInstance Q U V hφ P h g₀ f)
    (L : Set ℂ) (hL : IsCompact L) (hLU : L ⊆ U)
    (z : ℕ → ℂ) (r : ℕ → ℝ) (zl : ℂ) (hrpos : ∀ n, 0 < r n) (hr0 : Tendsto r atTop (𝓝 0))
    (hzL : ∀ n, z n ∈ L) (hzl : Tendsto z atTop (𝓝 zl))
    (ε : ℝ≥0∞) (hε : 0 < ε)
    (hbad : ∀ n, ε ≤ P (SupercriticalConformalCovariance.Good.RegularBadEvent h (D ∘ h)
      (fun ω => SupercriticalConformalCovariance.Good.transportedE (ξ : ℝ) D hφ (g₀ ω) (f ω)) ξ Q q a θ η (z n)
        ⟨r n, hrpos n⟩)) :
    False := by
  have hzlL : zl ∈ L := hL.isClosed.mem_of_tendsto hzl (Eventually.of_forall hzL)
  obtain ⟨R₀, hR₀, hR₀U, hexh₀, hzero₀, hda0, hda⟩ :=
    SupercriticalConformalCovariance.Small.zoom_sequence_tangent_geometry hφ (hLU hzlL) z r (fun n => hLU (hzL n)) hrpos
      hzl hr0
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (hR₀.eventually_ge_atTop 2)
  have hsh : Tendsto (fun n => n + N) atTop atTop := tendsto_add_atTop_nat N
  exact seq_core hQ hD hB hC1 H21 q a θ η hη hφ P h g₀ f hI (fun n => z (n + N))
    (fun n => r (n + N)) (fun n => hrpos (n + N)) (R := fun n => R₀ (n + N)) (hR₀.comp hsh)
    (fun n => hN (n + N) (by omega)) (fun n => hR₀U (n + N))
    (fun K hK => hsh.eventually (hexh₀ K hK)) (fun n => hzero₀ (n + N)) hda0 (hda.comp hsh)
    ε hε (fun n => hbad (n + N))

/-- **Proposition 4.3 from the zoom realization bridge** (paper l. 331–370): for every strong LQG
metric with LFPP exponent `Q`, `ZoomRealizationBridge → SupercriticalConformalCovariance.Root.Prop43Input ξ Q D`. -/
theorem prop43Input_of_bridge (hB : ZoomRealizationBridge) (ξ : Ioi (0 : ℝ)) (Q : ℝ)
    (hQ : IsLFPPExponent ξ Q) (D : DistC → LSCMetric) (hD : IsStrongLQGMetric ξ Q D) :
    SupercriticalConformalCovariance.Root.Prop43Input ξ Q D := by
  classical
  obtain ⟨C, hC1, H21full⟩ := SupercriticalConformalCovariance.BiLip.lemma21_lengths ξ Q hQ D hD
  have H21 : ∀ (U V : Opens ℂ) (φ : ℂ → ℂ) (hφ : IsConformalBijection φ U V)
      {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h g₀ : Ω → DistC) (k : Ω → C(V, ℝ)), SupercriticalConformalCovariance.BiLip.IsInstance Q U V hφ P h g₀ k →
      ∀ᵐ ω ∂P, ∀ u ∈ (U : Set ℂ), ∀ v ∈ (U : Set ℂ),
        SupercriticalConformalCovariance.BiLip.eT (D (g₀ ω)) ξ (k ω) φ u v ≤
            ENNReal.ofReal C * SupercriticalConformalCovariance.BiLip.pathInf (D (h ω)) U u v ∧
        SupercriticalConformalCovariance.BiLip.pathInf (D (h ω)) U u v ≤
            ENNReal.ofReal C * SupercriticalConformalCovariance.BiLip.eT (D (g₀ ω)) ξ (k ω) φ u v :=
    fun U V φ hφ Ω _ P _ h g₀ k hI => (H21full U V φ hφ P h g₀ k hI).mono fun ω hω => hω.1
  intro q a θ η hη U V φ hφ Ω _ P _ h g₀ f hI L hL hLU ε hε
  let F : ℂ → ℝ → ℝ≥0∞ := fun z r => if hr : 0 < r then
    P (SupercriticalConformalCovariance.Good.RegularBadEvent h (D ∘ h)
      (fun ω => SupercriticalConformalCovariance.Good.transportedE (ξ : ℝ) D hφ (g₀ ω) (f ω)) ξ Q q a θ η z ⟨r, hr⟩) else 0
  have hseq : ∀ (r : ℕ → ℝ) (z : ℕ → ℂ) (zlim : ℂ), (∀ n, 0 < r n) →
      Tendsto r atTop (𝓝 0) → (∀ n, z n ∈ L) → Tendsto z atTop (𝓝 zlim) →
      Tendsto (fun n => F (z n) (r n)) atTop (𝓝 0) := by
    intro r z zl hrpos hr0 hzL hzl
    rw [ENNReal.tendsto_nhds_zero]
    intro ε' hε'
    by_contra hne
    rw [Filter.not_eventually] at hne
    obtain ⟨φs, hφs, hfreq⟩ := Filter.extraction_of_frequently_atTop hne
    refine seq_failure_contradiction hQ hD hB hC1 H21 q a θ η hη hφ P h g₀ f hI L hL hLU
      (z ∘ φs) (r ∘ φs) zl (fun n => hrpos _) (hr0.comp hφs.tendsto_atTop) (fun n => hzL _)
      (hzl.comp hφs.tendsto_atTop) ε' hε' (fun n => ?_)
    have hn := hfreq n
    simp only [F, dif_pos (hrpos (φs n))] at hn
    exact (not_le.mp hn).le
  obtain ⟨δ, hδ, hF⟩ := SupercriticalConformalCovariance.Small.uniform_small_scale_of_sequential L hL F hseq
    (ENNReal.ofReal ε) (ENNReal.ofReal_pos.2 hε)
  refine ⟨δ / 2, half_pos hδ, fun z hz r hr => ?_⟩
  have h' := hF z hz r r.2 (by linarith)
  simp only [F] at h'
  rw [dif_pos (show (0 : ℝ) < r from r.2)] at h'
  exact h'.le

end SupercriticalConformalCovariance.P43Final
