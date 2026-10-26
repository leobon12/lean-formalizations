import SupercriticalConformalCovariance.BiLip.L51.Event
import SmallGammaGeodesics.CC.UniversalLocality
import LQGMetric.Papers.DFGPS.T12P6B

/-!
# Lemma 5.1's locality, proved

`lemma51LocalInput_proved : IsStrongLQGMetric ξ Q D → SupercriticalConformalCovariance.Root.Lemma51LocalInput ξ Q D` (the exact
definition of `SupercriticalConformalCovariance.Root.Forward`).

For one small pair `(z, r)` (`aeEventIn_goodEvent`), with `A₀ = A_{3r/7,9r/4}(z)` the window of
`SupercriticalConformalCovariance.Cover.localSigma`:
1. **The event of the centred fields** (`ae_goodEvent_iff`): `F_{z,r} =ᵃˢ {(h_c, G_c) ∈ Bset}`.
2. **Law space.** Write `g₀ = X₀ + f₀` (`X₀` a whole-plane GFF), `Y = (h_c, X₀, f₀ + F_c)` and `μ = law(Y)`
   on the standard Borel space `𝒟' × 𝒟' × C(ℂ, ℝ)`. Under `μ` both coordinates are GFFs plus continuous
   functions (`isWholePlaneGFF_of_map_pairProc_eq`). So the strong-metric axioms apply under `μ`: length
   space and internal-metric locality on `A₀` for the source, and locality on `W_T = φ(A₀) ∩ W_m` for the
   target. The barrier event, the finiteness of `D(M, ∂A)` and the target-locality lemma's forward restriction
   `G_c|_{W_T} = R(h_c|_{A₀})` are measurable events of `Y` holding `P`-a.s., hence `μ`-a.s.
3. **Saturation.** On the resulting measurable `μ`-full set, membership in the event depends only on
   `pairJ(h_c|_{A₀})` (`good_transfer`, circle-average locality, `intExt_transfer` for `ehat`).
4. **Measurability.** The event is null-measurable for `μ`: it agrees `μ`-a.s. with the universally
   measurable `Bset'` (`mem_Bset_iff`, `um_Bset'`).
5. SLU `aeEventIn_of_saturated` concludes `AEEventIn P (localSigma h z r) F_{z,r}`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open Set Metric Filter Topology MeasureTheory TopologicalSpace
open scoped ENNReal

namespace SupercriticalConformalCovariance.BiLip.L51

open SupercriticalLQGUniqueness (LSCMetric IsStrongLQGMetric IsCircleAverage)
open SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36Events (eventCarrier eventMiddle eventBoundary)
open SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36 (intExt intExt_transfer intExt_eq_of_internal_eq
  isCircleAverage_congr_restrict)
open SupercriticalLQGUniqueness.Uniqueness.OptimalConstants.Ratios (setDist)
open SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.Barrier (Barrier)
open SupercriticalConformalCovariance (IsConformalBijection domainMetric)
open LQGMetric (DistC DistOn addFun addConst ofCont restrictTo IsGFFPlusCont IsWholePlaneGFF CoordJ)
open LQGMetric.Blueprint (AEEventIn)
open SupercriticalConformalCovariance.Domain (exW exWO cutF)
open SupercriticalConformalCovariance.BiLip (srcWindow ctr)

/-- `β = 𝒟' × 𝒟' × C(ℂ, ℝ)`, and the target field `G(x) = x₂ + x₃` -/
abbrev LawSp : Type := DistC × DistC × C(ℂ, ℝ)

def tgtField (x : LawSp) : DistC := addFun x.2.1 x.2.2

theorem measurable_tgtField : Measurable tgtField := by
  refine LQGMetric.measurable_distOn_iff.2 fun ψ => ?_
  have e : (fun x : LawSp => tgtField x ψ) = fun x => x.2.1 ψ + ofCont x.2.2 ψ := funext fun x => rfl
  rw [e]
  exact ((LQGMetric.measurable_distOn_apply ψ).comp (measurable_fst.comp measurable_snd)).add
    ((LQGMetric.measurable_ofCont_apply ψ).comp (measurable_snd.comp measurable_snd))

theorem eventCarrier_subset_srcWindow (z : ℂ) {r : ℝ} (hr : 0 < r) :
    eventCarrier z r ⊆ (srcWindow z r : Set ℂ) := by
  rintro y ⟨h1, h2⟩
  rw [mem_closedBall, dist_eq_norm] at h1
  rw [mem_ball, not_lt, dist_eq_norm] at h2
  show 1 / 7 * (3 * r) < ‖y - z‖ ∧ ‖y - z‖ < 3 / 4 * (3 * r)
  constructor <;> linarith

theorem sphere_subset_srcWindow (z : ℂ) {r : ℝ} (hr : 0 < r) :
    sphere z r ⊆ (srcWindow z r : Set ℂ) := by
  intro y hy
  rw [mem_sphere, dist_eq_norm] at hy
  show 1 / 7 * (3 * r) < ‖y - z‖ ∧ ‖y - z‖ < 3 / 4 * (3 * r)
  constructor <;> linarith

section Main

variable {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ} {D : DistC → LSCMetric}

/-- the centred source sample properties hold almost surely -/
theorem ae_centered_source (hD : IsStrongLQGMetric ξ Q D) {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC}
    (hhn : SupercriticalLQGUniqueness.IsNormalizedWholePlaneGFF h P) (z : ℂ) {r : ℝ} (hr : 0 < r) :
    ∀ᵐ ω ∂P, Barrier (D (addConst (h ω) (-ctr (h ω) z r))) ∧
      setDist (D (addConst (h ω) (-ctr (h ω) z r))) (eventMiddle z r) (eventBoundary z r) < ⊤ := by
  set rr : Ioi (0 : ℝ) := ⟨r, hr⟩
  have hh := hhn.1
  set c : Ω → ℝ := fun ω => ctr (h ω) z r with hcdef
  have hcm : Measurable c := (LQGMetric.measurable_circleAvg_left (3 * r) z).comp hh.measurable
  have hhc : IsGFFPlusCont (fun ω => addConst (h ω) (-c ω)) P :=
    LQGMetric.GM.Tight.isGFFPlusCont_of_wp (hh.addConst hcm.neg)
  have hW := SupercriticalLQGUniqueness.B2.Strong.isWeakLQGMetric_of_isStrongLQGMetric hD
  have hQ0 : 0 < Q := SupercriticalLQGUniqueness.Uniqueness.Positivity.FromAxioms.axpos ξ Q D hW
  filter_upwards [SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.Barrier.ae_barrier hW hQ0 P h hhn,
    SupercriticalLQGUniqueness.Uniqueness.Positivity.Witnesses.ae_addConst_eq_mul P _ hhc ξ Q D hW c,
    SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36.ae_acrossDist_dilate_lt_top ξ Q D hW P h hhn
      (SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36.halfAnnShape z rr) rr]
    with ω hBh hsc hfin
  set hc := addConst (h ω) (-c ω)
  set lam : ℝ≥0∞ := ENNReal.ofReal (Real.exp (ξ * c ω)) with hlam
  have hl0 : lam ≠ 0 := (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
  have hlt : lam ≠ ⊤ := ENNReal.ofReal_ne_top
  have hhω : addConst hc (c ω) = h ω := SupercriticalConformalCovariance.BiLip.addConst_ctr_eq (h ω) (c ω)
  have hscale : ∀ x y : ℂ, D (h ω) (x, y) = lam * D hc (x, y) := by
    intro x y; have := hsc (x, y); rwa [hhω] at this
  have hscale' : ∀ x y : ℂ, D hc (x, y) = lam⁻¹ * D (h ω) (x, y) := by
    intro x y
    rw [hscale, ← mul_assoc, ENNReal.inv_mul_cancel hl0 hlt, one_mul]
  refine ⟨barrier_of_scale (ENNReal.inv_ne_zero.2 hlt) (ENNReal.inv_ne_top.2 hl0) hscale' hBh, ?_⟩
  have h1 := (SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36.setDist_middle_le_across
    (D (h ω)) z rr).trans_lt hfin
  rw [SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36.setDist_eq_mul_of_scale hl0 hlt hscale] at h1
  exact (SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36.mul_lt_top_iff_of_ne hl0 hlt _).1 h1

/-- **Lemma 5.1's locality at one pair `(z, r)`.** -/
theorem aeEventIn_goodEvent (hD : IsStrongLQGMetric ξ Q D) {U V : Opens ℂ} {φ : ℂ → ℂ}
    (hφ : IsConformalBijection φ U V) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h g₀ : Ω → DistC} {f : Ω → C(V, ℝ)}
    (hI : SupercriticalConformalCovariance.BiLip.IsInstance Q U V hφ P h g₀ f) {C : ℝ} (hC : 1 ≤ C)
    (hcmp : ∀ᵐ ω ∂P, ∀ u v : U,
      ENNReal.ofReal C⁻¹ * (D (h ω)).internal U (u, v) ≤
          domainMetric (ξ : ℝ) D V (g₀ ω) (f ω) (⟨φ u, hφ.2.mapsTo u.2⟩, ⟨φ v, hφ.2.mapsTo v.2⟩) ∧
        domainMetric (ξ : ℝ) D V (g₀ ω) (f ω) (⟨φ u, hφ.2.mapsTo u.2⟩, ⟨φ v, hφ.2.mapsTo v.2⟩) ≤
          ENNReal.ofReal C * (D (h ω)).internal U (u, v))
    (q : Ioo (0 : ℝ) (1 / 100)) (a : Ioo (1 - (q : ℝ)) 1) (K : Ioi (1 : ℝ)) (θ : Ioi (0 : ℝ))
    (η : ℝ) {z : ℂ} {r : ℝ} (hr : 0 < r) (hAU : closure (srcWindow z r : Set ℂ) ⊆ U) :
    AEEventIn P (SupercriticalConformalCovariance.Cover.localSigma h z r)
      (SupercriticalConformalCovariance.Good.GoodEvent h (D ∘ h) (fun ω => SupercriticalConformalCovariance.Good.transportedE (ξ : ℝ) D hφ (g₀ ω) (f ω))
        ξ Q q a K θ (SupercriticalConformalCovariance.Good.shieldK C) η z r) := by
  set rr : Ioi (0 : ℝ) := ⟨r, hr⟩ with hrr
  set A₀ : Opens ℂ := srcWindow z r with hA₀def
  have hA₀U : (A₀ : Set ℂ) ⊆ U := subset_closure.trans hAU
  set Y := eventCarrier z r with hYdef
  have hYA : Y ⊆ (A₀ : Set ℂ) := eventCarrier_subset_srcWindow z hr
  have hYU : Y ⊆ (U : Set ℂ) := hYA.trans hA₀U
  have hYc : IsCompact Y :=
    SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36.isCompact_eventCarrier z r
  have hφc : ContinuousOn φ U := hφ.1.continuousOn
  have hKc : IsCompact (φ '' Y) := hYc.image_of_continuousOn (hφc.mono hYU)
  have hKV : φ '' Y ⊆ (V : Set ℂ) := by rintro _ ⟨w, hw, rfl⟩; exact hφ.2.mapsTo (hYU hw)
  obtain ⟨m, hm⟩ := SupercriticalConformalCovariance.Domain.exists_subset_exW V.isOpen hKc hKV
  set B : Opens ℂ := SupercriticalConformalCovariance.BiLip.imgWindow hφ z r hA₀U with hBdef
  have hBV : B ≤ V := by rintro _ ⟨x, hx, rfl⟩; exact hφ.2.mapsTo (hA₀U hx)
  set WT : Opens ℂ := B ⊓ exWO V m with hWTdef
  have hWB : WT ≤ B := inf_le_left
  have hWE : WT ≤ exWO V m := inf_le_right
  have hKW : φ '' Y ⊆ (WT : Set ℂ) := fun y hy => ⟨by
    obtain ⟨x, hx, rfl⟩ := hy; exact ⟨x, hYA hx, rfl⟩, hm hy⟩
  obtain ⟨Rm, hRm, hRmeq⟩ := SupercriticalConformalCovariance.BiLip.PortT.exists_measurable_forward_restrict Q hφ
    (A := A₀) (B := B) hA₀U hAU (SupercriticalConformalCovariance.BiLip.srcWindow_bounded z r) rfl hBV
  -- the centred instance
  have hI' := hI
  obtain ⟨hhn, hR⟩ := hI'
  have hh := hhn.1
  set c : Ω → ℝ := fun ω => ctr (h ω) z r with hcdef
  have hcm : Measurable c := (LQGMetric.measurable_circleAvg_left (3 * r) z).comp hh.measurable
  set hcf : Ω → DistC := fun ω => addConst (h ω) (-c ω) with hcfdef
  have hhcW : IsWholePlaneGFF hcf P := hh.addConst hcm.neg
  have hR' := SupercriticalConformalCovariance.BiLip.PortT.isDomainRealization_forward_add_const hφ Q hR hcm.neg
  set kc : Ω → C(V, ℝ) := fun ω => f ω + ContinuousMap.const V (-c ω) with hkcdef
  have hkcm : Measurable kc := hR'.2.2.1
  set Fc : Ω → C(ℂ, ℝ) := fun ω => cutF V m (kc ω) with hFcdef
  have hFcm : Measurable Fc :=
    SupercriticalConformalCovariance.Domain.measurable_cutExt V.isOpen (SupercriticalConformalCovariance.Domain.tsupport_cutoff_subset (V : Set ℂ) m) hkcm
  set Gc : Ω → DistC := fun ω => addFun (g₀ ω) (Fc ω) with hGcdef
  -- the GFF part of `g₀`
  obtain ⟨hg₀m, f₀, hf₀m, hX₀⟩ := hR.2.1
  set X₀ : Ω → DistC := fun ω => g₀ ω - ofCont (f₀ ω) with hX₀def
  set Yβ : Ω → LawSp := fun ω => (hcf ω, X₀ ω, f₀ ω + Fc ω) with hYβdef
  have hGcY : ∀ ω, tgtField (Yβ ω) = Gc ω := by
    intro ω
    simp only [tgtField, hYβdef, hX₀def, hGcdef, addFun, LQGMetric.DFGPS.T12.ofCont_add']
    abel
  have hYβm : Measurable Yβ :=
    hhcW.measurable.prodMk (hX₀.measurable.prodMk (hf₀m.add hFcm))
  set μ : Measure LawSp := P.map Yβ with hμdef
  have : IsProbabilityMeasure μ := by rw [hμdef]; infer_instance
  -- the coordinates under `μ`
  have hfst : IsWholePlaneGFF (fun x : LawSp => x.1) μ := by
    refine SmallGammaGeodesics.CC.isWholePlaneGFF_of_map_pairProc_eq measurable_fst hhcW ?_
    rw [hμdef, Measure.map_map (LQGMetric.GFFLaw.measurable_pairProc measurable_fst) hYβm]
    rfl
  have hm2 : Measurable (fun x : LawSp => x.2.1) := measurable_fst.comp measurable_snd
  have hsnd : IsWholePlaneGFF (fun x : LawSp => x.2.1) μ := by
    refine SmallGammaGeodesics.CC.isWholePlaneGFF_of_map_pairProc_eq hm2 hX₀ ?_
    rw [hμdef, Measure.map_map (LQGMetric.GFFLaw.measurable_pairProc hm2) hYβm]
    rfl
  have hfstc : IsGFFPlusCont (fun x : LawSp => x.1) μ := LQGMetric.GM.Tight.isGFFPlusCont_of_wp hfst
  have hGβ : IsGFFPlusCont tgtField μ := by
    refine ⟨measurable_tgtField, fun x => x.2.2, measurable_snd.comp measurable_snd, ?_⟩
    have e : (fun x : LawSp => tgtField x - ofCont x.2.2) = fun x => x.2.1 := by
      funext x; simp only [tgtField, addFun, add_sub_cancel_right]
    rw [e]; exact hsnd
  -- the strong-metric axioms under `μ`
  have hLμ := hD.2.1 μ _ hfstc
  obtain ⟨FD, -, hFD⟩ := hD.2.2.1 μ _ hfstc A₀
  obtain ⟨FT, -, hFT⟩ := hD.2.2.1 μ tgtField hGβ WT
  -- measurable events of `Y` transferred from `P` to `μ`
  have hSB : MeasurableSet {x : LawSp | Barrier (D x.1) ∧
      setDist (D x.1) (eventMiddle z r) (eventBoundary z r) < ⊤} :=
    ((barrier_measurableSet hD.1).preimage measurable_fst).inter
      (measurableSet_lt (((SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36.measurable_setDist_middle
        z hr).comp hD.1).comp measurable_fst) measurable_const)
  have hBμ : ∀ᵐ x ∂μ, Barrier (D x.1) ∧
      setDist (D x.1) (eventMiddle z r) (eventBoundary z r) < ⊤ := by
    rw [hμdef, ae_map_iff hYβm.aemeasurable hSB]
    exact ae_centered_source hD hhn z hr
  have hrelm : Measurable fun x : LawSp => LQGMetric.pairJ WT (restrictTo WT (tgtField x)) :=
    (LQGMetric.measurable_pairJ WT).comp ((LQGMetric.measurable_restrictTo WT).comp measurable_tgtField)
  have hrelm' : Measurable fun x : LawSp =>
      LQGMetric.pairJ WT (SupercriticalConformalCovariance.Domain.restrictOn hWB (Rm (restrictTo A₀ x.1))) :=
    (LQGMetric.measurable_pairJ WT).comp ((SupercriticalConformalCovariance.Domain.measurable_restrictOn hWB).comp
      (hRm.comp ((LQGMetric.measurable_restrictTo A₀).comp measurable_fst)))
  have hSrel : MeasurableSet {x : LawSp | LQGMetric.pairJ WT (restrictTo WT (tgtField x)) =
      LQGMetric.pairJ WT (SupercriticalConformalCovariance.Domain.restrictOn hWB (Rm (restrictTo A₀ x.1)))} :=
    measurableSet_eq_fun hrelm hrelm'
  have hrelμ : ∀ᵐ x ∂μ, LQGMetric.pairJ WT (restrictTo WT (tgtField x)) =
      LQGMetric.pairJ WT (SupercriticalConformalCovariance.Domain.restrictOn hWB (Rm (restrictTo A₀ x.1))) := by
    rw [hμdef, ae_map_iff hYβm.aemeasurable hSrel]
    filter_upwards [SupercriticalConformalCovariance.Domain.ae_restrictTo_cutF hR' m] with ω hcut
    show LQGMetric.pairJ WT (restrictTo WT (tgtField (Yβ ω))) =
      LQGMetric.pairJ WT (SupercriticalConformalCovariance.Domain.restrictOn hWB (Rm (restrictTo A₀ (hcf ω))))
    rw [hGcY]
    congr 1
    have hTc : SupercriticalConformalCovariance.confPullbackField Q
        (SupercriticalConformalCovariance.BiLip.PortRev.inverse_conformal hφ) (restrictTo U (h ω) + SupercriticalConformalCovariance.BiLip.PortT.constOn U (-c ω)) =
        SupercriticalConformalCovariance.confPullbackField Q (SupercriticalConformalCovariance.BiLip.PortRev.inverse_conformal hφ)
          (restrictTo U (addConst (h ω) (-c ω))) := by
      rw [SupercriticalConformalCovariance.BiLip.restrictTo_addConst_eq]
    have h1 : restrictTo (exWO V m) (Gc ω) = SupercriticalConformalCovariance.Domain.restrictOn (SupercriticalConformalCovariance.Domain.exWO_le V m)
        (SupercriticalConformalCovariance.confPullbackField Q (SupercriticalConformalCovariance.BiLip.PortRev.inverse_conformal hφ)
          (restrictTo U (h ω) + SupercriticalConformalCovariance.BiLip.PortT.constOn U (-c ω))) := by
      ext φ'
      exact hcut φ'
    rw [← SupercriticalConformalCovariance.Domain.restrictOn_restrictTo hWE, h1, SupercriticalConformalCovariance.Lemma31.restrictOn_restrictOn, hTc]
    have h2 := hRmeq (restrictTo U (addConst (h ω) (-c ω)))
    have h3 : SupercriticalConformalCovariance.Domain.restrictOn hA₀U (restrictTo U (addConst (h ω) (-c ω))) =
        restrictTo A₀ (addConst (h ω) (-c ω)) :=
      SupercriticalConformalCovariance.Domain.restrictOn_restrictTo hA₀U _
    rw [h3] at h2
    rw [← h2, SupercriticalConformalCovariance.Lemma31.restrictOn_restrictOn]
  -- the good set
  have hGood : ∀ᵐ x ∂μ, (Barrier (D x.1) ∧
      setDist (D x.1) (eventMiddle z r) (eventBoundary z r) < ⊤) ∧ (D x.1).IsLengthSpace ∧
      (D x.1).internal A₀ = FD (restrictTo A₀ x.1) ∧
      (D (tgtField x)).internal WT = FT (restrictTo WT (tgtField x)) ∧
      LQGMetric.pairJ WT (restrictTo WT (tgtField x)) =
        LQGMetric.pairJ WT (SupercriticalConformalCovariance.Domain.restrictOn hWB (Rm (restrictTo A₀ x.1))) := by
    filter_upwards [hBμ, hLμ, hFD, hFT, hrelμ] with x h1 h2 h3 h4 h5
    exact ⟨h1, h2, h3, h4, h5⟩
  obtain ⟨W, hWae, hWm, hWsub⟩ := hGood.exists_measurable_mem
  -- the event on the law space
  set kk := SupercriticalConformalCovariance.Good.shieldK C with hkk
  have hC0 : 0 < C := by linarith
  have hk0 : 0 ≤ kk := (SupercriticalConformalCovariance.Good.shieldK_pos hC).le
  have hk : kk ≤ 1 / 2 := by
    rw [hkk]; unfold SupercriticalConformalCovariance.Good.shieldK
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  set Bβ : Set LawSp := {x | (x.1, tgtField x) ∈ Bset D Y φ ξ Q z rr q a K θ kk η} with hBβdef
  have hB'um : LQGMetric.UMeasurableSet
      ((fun x : LawSp => (x.1, tgtField x)) ⁻¹' Bset' D Y φ ξ Q z rr q a K θ kk η) :=
    (um_Bset' D Y φ ξ Q z rr q a K θ kk η hD.1 hYc (hφc.mono hYU)).preimage
      (measurable_fst.prodMk measurable_tgtField)
  have hBnull : NullMeasurableSet Bβ μ := by
    refine (hB'um.nullMeasurableSet μ).congr ?_
    filter_upwards [hWae] with x hx
    obtain ⟨⟨hB1, -⟩, hL1, -⟩ := hWsub x hx
    have hbar := barrier_eq_ambient (D x.1)
      (fun γ a b hγ => SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.Barrier.continuousOn_of_barrier_of_length
        _ hB1 hL1 hγ) hL1 z rr
    exact propext ((mem_Bset_iff D Y φ ξ Q z rr q a K θ kk η (x.1, tgtField x) hbar).symm)
  -- saturation
  set R : LawSp → CoordJ → ℝ := fun x => LQGMetric.pairJ A₀ (restrictTo A₀ x.1) with hRdef
  have hRmeas : Measurable R :=
    (LQGMetric.measurable_pairJ A₀).comp ((LQGMetric.measurable_restrictTo A₀).comp measurable_fst)
  set V' : Ω → CoordJ → ℝ := fun ω => LQGMetric.pairJ A₀ (restrictTo A₀ (hcf ω)) with hV'def
  have hV' : Measurable[SupercriticalConformalCovariance.Cover.localSigma h z r] V' :=
    (LQGMetric.measurable_pairJ A₀).comp (Measurable.of_comap_le le_rfl)
  have hsat : ∀ x₁ ∈ W, ∀ x₂ ∈ W, R x₁ = R x₂ → x₁ ∈ Bβ → x₂ ∈ Bβ := by
    intro x₁ hx₁ x₂ hx₂ hR12 hB₁
    obtain ⟨⟨hb₁, hs₁⟩, hl₁, hi₁, hT₁, hr₁⟩ := hWsub x₁ hx₁
    obtain ⟨⟨hb₂, hs₂⟩, hl₂, hi₂, hT₂, hr₂⟩ := hWsub x₂ hx₂
    have hres : restrictTo A₀ x₁.1 = restrictTo A₀ x₂.1 := LQGMetric.injective_pairJ A₀ hR12
    have hId : ∀ x y, intExt (D x₁.1) A₀ x y = intExt (D x₂.1) A₀ x y :=
      intExt_eq_of_internal_eq (by rw [hi₁, hi₂, hres])
    have hresT : restrictTo WT (tgtField x₁) = restrictTo WT (tgtField x₂) :=
      LQGMetric.injective_pairJ WT (by rw [hr₁, hr₂, hres])
    have hIT : ∀ x y, intExt (D (tgtField x₁)) WT x y = intExt (D (tgtField x₂)) WT x y :=
      intExt_eq_of_internal_eq (by rw [hT₁, hT₂, hresT])
    have he : ∀ x ∈ Y, ∀ y ∈ Y, ehat D Y φ (tgtField x₁) (x, y) = ehat D Y φ (tgtField x₂) (x, y) := by
      intro x hx y hy
      rw [ehat_of_mem hx hy, ehat_of_mem hx hy, intExt_transfer hKW hIT]
    obtain ⟨c', hc', hG⟩ := hB₁
    refine ⟨c', (isCircleAverage_congr_restrict hres rr z (sphere_subset_srcWindow z hr) c').1 hc', ?_⟩
    exact good_transfer hk0 hk ⟨hb₁, hl₁, hs₁⟩ ⟨hb₂, hl₂, hs₂⟩ hYA hId he hG
  have hLocal := LQGMetric.LocalEvent.aeEventIn_of_saturated (P := P) (m := SupercriticalConformalCovariance.Cover.localSigma h z r)
    (Y := Yβ) (R := R) (V := V') (B := Bβ) (W := W) hYβm hRmeas hV'
    (Eventually.of_forall fun _ => rfl) hWm hBnull (ae_of_ae_map hYβm.aemeasurable hWae) hsat
  -- the literal event is a.s. the preimage
  obtain ⟨F, hF, hFe⟩ := hLocal
  refine ⟨F, hF, ?_⟩
  refine EventuallyEq.trans ?_ hFe
  filter_upwards [ae_goodEvent_iff hD hφ hI hC hcmp q a K θ η hr hYU hm] with ω hω
  refine propext (hω.trans ?_)
  show _ ↔ ((Yβ ω).1, tgtField (Yβ ω)) ∈ Bset D Y φ ξ Q z rr q a K θ kk η
  rw [hGcY]

/-- **Lemma 5.1's locality** (paper l. 416–438), the exact consumption form of the root assembly
(`SupercriticalConformalCovariance.Root.Forward`). -/
theorem lemma51LocalInput_proved (hD : IsStrongLQGMetric ξ Q D) : SupercriticalConformalCovariance.Root.Lemma51LocalInput ξ Q D := by
  intro q a K θ η _ U V φ hφ Ω _ P _ h g₀ f hI C hC hcmp L hL hLU
  obtain ⟨ρ, hρ, hρU⟩ := hL.exists_cthickening_subset_open U.isOpen hLU
  refine ⟨ρ / 4, by positivity, fun z hz r hr => ?_⟩
  have hr0 : 0 < r := hr.1
  have hAU : closure (srcWindow z r : Set ℂ) ⊆ U := by
    refine (closure_minimal ?_ isClosed_closedBall).trans
      ((closedBall_subset_cthickening hz ρ).trans hρU)
    intro y hy
    have hy' : 1 / 7 * (3 * r) < ‖y - z‖ ∧ ‖y - z‖ < 3 / 4 * (3 * r) := hy
    rw [mem_closedBall, dist_eq_norm]
    have := hr.2
    linarith [hy'.2]
  exact aeEventIn_goodEvent hD hφ hI hC hcmp q a K θ η hr0 hAU

end Main

end SupercriticalConformalCovariance.BiLip.L51
