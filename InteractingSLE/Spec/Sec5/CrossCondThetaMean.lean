/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossCondTheta
import InteractingSLE.Spec.Sec5.GlueCondUnionImgInf

/-!
# The cross-conditioning law at relative angle `θ`: the union mean

Packet PROVE-CROSSCOND-THETA. The θ-versions of PROVE-GLUECOND2/3/6's union-mean lemmas on the glued space of
`CrossCondTheta` (the flow line of `h` and the counterflow of `h − θχ`): Proposition 3.8 for the two stopped hulls
(`ae_union_boundary_cfGlueT`), the flow hull's explicit mean (`exists_isLocalSetMean_flowHull_glueT`), the counterflow
hull's mean read through its stopped history (`exists_isLocalSetMean_cfHullQ_pathT`; the counterflow word is built from
the data `𝔟_F − θχ` of `h − θχ`), the harmonic representative of the union mean with its boundary limits on both hulls
(`ae_union_mean_cfGlueT`), and its limit at `∞` against the counterflow mean (`ae_tendsto_union_sub_cfMean_coboundedT`).
Each proof is the landed one read with `h − θχ` in place of `h − π/2 χ`.

Conditional helpers with distinct names; they replace no source theorem. R48: nothing here uses Theorem 1.2/1.3.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal Real
open QuantumZipper (H chiC fwdHull fwdMap)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Sec5.CrossCond.Theta

open WangWu hiding ratPt exists_ratPt_dist_lt continuousAt_negInv
open WangWu.ImgWord LawUnique GlueCond MartChar.RealFlow Cond44Ref CfRegQ Prop411Q WholeField Word49 Sec7.StripSysField
open GlueImg
open LocalSets (IsLocalSetMean)
open SupercriticalConformalCovariance.GM24 (smoothDist)
open Sec4 (regPath regHull safeHist safeIdx safeUnion histStop)

section Mean

variable {κ θ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}
  {Ω₂ : Type u} {mΩ₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
  {h₂ : Ω₂ → DistOn upperHalfPlaneOpens} {W₂ : ℝ≥0 → Ω₂ → ℝ} {ζ₂ : Ω₂ → ℝ≥0∞}
  {k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 0 0)} [IsMarkovKernel k] {u₀ : ℂ → ℝ}

/-- θ-version of `ae_union_boundary_cfGlue` (`Sec5.GlueCond`):
the counterflow field is `h − θχ` instead of `h − π/2 χ`. -/
theorem ae_union_boundary_cfGlueT (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) (hcf : IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂)
    (hreg₂ : ∀ᵐ ω ∂P₂, ζ₂ ω = ⊤ ∧ W₂ 0 ω = 0 ∧ Continuous fun t => W₂ t ω)
    (hlaw : P.map (fun ω => cfFieldT κ θ (h ω)) = P₂.map h₂)
    (hk : P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω)) = P₂.map h₂ ⊗ₘ k)
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀) (q t : ℝ≥0)
    {g gA gG : Ω × HistorySpace 0 0 → DistOn upperHalfPlaneOpens}
    (hg : IsLocalSetMean (fun p : Ω × HistorySpace 0 0 => hullAt q (killedHistory W VL VR ζ p.1) ∪ cfHullQ t p.2)
      (fun p => cenTT κ θ u₀ (cfFieldT κ θ (h p.1)))
      (glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)) g)
    (hgA : IsLocalSetMean (fun p : Ω × HistorySpace 0 0 => hullAt q (killedHistory W VL VR ζ p.1))
      (fun p => cenTT κ θ u₀ (cfFieldT κ θ (h p.1)))
      (glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)) gA)
    (hgG : IsLocalSetMean (fun p : Ω × HistorySpace 0 0 => cfHullQ t p.2)
      (fun p => cenTT κ θ u₀ (cfFieldT κ θ (h p.1)))
      (glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)) gG) :
    ∀ᵐ p ∂(glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)), ∀ wA wG : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd wA (H \ hullAt q (killedHistory W VL VR ζ p.1)) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ hullAt q (killedHistory W VL VR ζ p.1) →
        gA p φ = ∫ z, wA z * φ z) →
      InnerProductSpace.HarmonicOnNhd wG (H \ cfHullQ t p.2) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ cfHullQ t p.2 → gG p φ = ∫ z, wG z * φ z) →
      ∃ w : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w (H \ (hullAt q (killedHistory W VL VR ζ p.1) ∪ cfHullQ t p.2)) ∧
        (∀ φ : TestOn upperHalfPlaneOpens,
          tsupport φ ⊆ H \ (hullAt q (killedHistory W VL VR ζ p.1) ∪ cfHullQ t p.2) → g p φ = ∫ z, w z * φ z) ∧
        (∀ z₀ ∈ hullAt q (killedHistory W VL VR ζ p.1) ∪ {z : ℂ | z.im = 0},
          (∃ r > 0, cfHullQ t p.2 ∩ ball z₀ r ⊆ hullAt q (killedHistory W VL VR ζ p.1)) →
          Tendsto (fun z => w z - wA z)
            (𝓝[H \ (hullAt q (killedHistory W VL VR ζ p.1) ∪ cfHullQ t p.2)] z₀) (𝓝 0)) ∧
        (∀ z₀ ∈ cfHullQ t p.2 ∪ {z : ℂ | z.im = 0},
          (∃ r > 0, hullAt q (killedHistory W VL VR ζ p.1) ∩ ball z₀ r ⊆ cfHullQ t p.2) →
          Tendsto (fun z => w z - wG z)
            (𝓝[H \ (hullAt q (killedHistory W VL VR ζ p.1) ∪ cfHullQ t p.2)] z₀) (𝓝 0)) := by
  have hXm : Measurable fun ω => cfFieldT κ θ (h ω) := (measurable_cfFieldT κ θ).comp hC.2.1
  obtain ⟨hX, -⟩ := hC.2.2.2
  have hAm : Measurable[mΩ, hittingSigma] fun ω => hullAt q (killedHistory W VL VR ζ ω) :=
    (measurable_hullAt q).comp (measurable_killedHistory hX)
  obtain ⟨hAg, hGg, -⟩ := isLocalSet_union_glueT (k := k) hC hζ hcf hreg₂ hlaw hk hu₀ q t
  have hF : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (fun ω => cenTT κ θ u₀ (cfFieldT κ θ (h ω))) P := by
    have e : (fun ω => cenTT κ θ u₀ (cfFieldT κ θ (h ω))) = WholeField.centredField h u₀ :=
      funext fun ω => cenTT_cfFieldT κ θ u₀ (h ω)
    rw [e]
    exact WholeField.isZeroBoundaryGFF_centredField hC hu₀
  exact ae_union_boundary_glue hXm k (measurable_cenTT κ θ u₀) (measurable_cenTT' κ θ u₀) (cenTT'_cenTT κ θ u₀) hF hAm
    (measurable_cfHullQ t) hAg hGg
    (Eventually.of_forall fun p => not_isBounded_lowerUnion_of_isHPHull (isHPHull_hullAt _ _))
    (Eventually.of_forall fun p => not_isBounded_lowerUnion_image_negInv (isHPHull_hullAt _ _)) hg hgA hgG

/-- θ-version of `exists_isLocalSetMean_flowHull_glue` (`Sec5.GlueCond`):
the counterflow field is `h − θχ` instead of `h − π/2 χ`. -/
theorem exists_isLocalSetMean_flowHull_glueT (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hκ : 0 < κ) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤)
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀) (q : ℝ≥0)
    {u : Ω → ℂ → ℝ}
    (hu : ∀ ω, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => VL i q ω - W q ω) (fun i => VR i q ω - W q ω))
      (forceJumpSet (fun i => VL i q ω - W q ω) (fun i => VR i q ω - W q ω)) (u ω)) :
    ∃ g : Ω × HistorySpace 0 0 → DistOn upperHalfPlaneOpens,
      IsLocalSetMean (fun p : Ω × HistorySpace 0 0 => hullAt q (killedHistory W VL VR ζ p.1))
        (fun p => cenTT κ θ u₀ (cfFieldT κ θ (h p.1)))
        (glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)) g ∧
      ∀ᵐ p ∂(glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)),
        ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ hullAt q (killedHistory W VL VR ζ p.1) →
          g p φ = ∫ z, (couplingMean κ (fun s : ℝ => W s.toNNReal p.1) q (u p.1) z - u₀ z) * φ z := by
  have hXm : Measurable fun ω => cfFieldT κ θ (h ω) := (measurable_cfFieldT κ θ).comp hC.2.1
  obtain ⟨hX, -⟩ := hC.2.2.2
  have hAm : Measurable[mΩ, hittingSigma] fun ω => hullAt q (killedHistory W VL VR ζ ω) :=
    (measurable_hullAt q).comp (measurable_killedHistory hX)
  have hh0 := WholeField.isZeroBoundaryGFF_centredField hC hu₀
  have e : (fun ω => cenTT κ θ u₀ (cfFieldT κ θ (h ω))) = WholeField.centredField h u₀ :=
    funext fun ω => cenTT_cfFieldT κ θ u₀ (h ω)
  have hloc : IsLocalSet (fun ω => hullAt q (killedHistory W VL VR ζ ω)) (WholeField.centredField h u₀) P :=
    e ▸ isLocalSet_hullAt_flowT hC hζ hu₀ q
  obtain ⟨g, hg⟩ := LocalSets.IsLocalSet.exists_isLocalSetMean hh0 hAm hloc
  have hτζ : ∀ᵐ ω ∂P, (((fun _ : Ω => ((q : ℝ≥0) : WithTop ℝ≥0)) ω : WithTop ℝ≥0) : ℝ≥0∞) < ζ ω := by
    filter_upwards [hζ] with ω hω
    rw [hω]
    exact ENNReal.coe_lt_top
  have hAK : ∀ᵐ ω ∂P, hullAt q (killedHistory W VL VR ζ ω) =
      (fun z : ℂ => z + ((0 : ℝ) : ℂ)) '' fwdHull (fun s : ℝ => W s.toNNReal ω)
        (((fun _ : Ω => ((q : ℝ≥0) : WithTop ℝ≥0)) ω).untopD 0 : ℝ≥0) := by
    filter_upwards [Aux50Hit.ae_isGoodPath hC.1 hζ] with ω hg
    rw [WithTop.untopD_coe, hullAt, Aux50Hit.regHull_stopHistory_cstop hg q]
    simp only [Complex.ofReal_zero, add_zero, image_id']
    rfl
  have hid := Sec7.SideHeight.ae_apply_eq_of_isLocalSetMean_flowHull (x := 0) (c := 0) hC hκ
    (fun ω => by simpa only [zero_mul] using Sec7.StripSysField.isTranslateAddConst_zero_self (h ω) 0) hh0 hu₀.1 hu₀
    (fun z _ => by simp only [Complex.ofReal_zero, add_zero]) hX (isStoppingTime_const _ q) hτζ hAm hAK hg
    (u := u) (by simpa only [WithTop.untopD_coe] using hu)
  refine ⟨fun p => g p.1, ?_, ?_⟩
  · have hgl := IsLocalSetMean.comp measurable_fst (glueMeasure_fst (μ := P) k hXm) hAm
      (WholeField.measurable_centredField hC.2.1 u₀) hg
    have e' : (fun p : Ω × HistorySpace 0 0 => cenTT κ θ u₀ (cfFieldT κ θ (h p.1))) =
        fun p => WholeField.centredField h u₀ p.1 := funext fun p => cenTT_cfFieldT κ θ u₀ (h p.1)
    rw [e']
    exact hgl
  · have hid' : ∀ᵐ ω ∂P, ∀ φ : TestOn upperHalfPlaneOpens,
        tsupport φ ⊆ H \ hullAt q (killedHistory W VL VR ζ ω) →
          g ω φ = ∫ z, (couplingMean κ (fun s : ℝ => W s.toNNReal ω) q (u ω) z - u₀ z) * φ z := by
      filter_upwards [hid] with ω hω φ hφ
      rw [hω φ hφ]
      simp only [WithTop.untopD_coe, Complex.ofReal_zero, sub_zero]
    exact ae_glue_fst (μ := P) k hXm hid'

/-- θ-version of `exists_isLocalSetMean_cfHullQ_path` (`Sec5.GlueCondPath`):
the counterflow field is `h − θχ` instead of `h − π/2 χ`. -/
theorem exists_isLocalSetMean_cfHullQ_pathT (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hκ : 0 < κ) (hcf : IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂)
    (hreg₂ : ∀ᵐ ω ∂P₂, ζ₂ ω = ⊤ ∧ W₂ 0 ω = 0 ∧ Continuous fun t => W₂ t ω)
    (hlaw : P.map (fun ω => cfFieldT κ θ (h ω)) = P₂.map h₂)
    (hk : P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω)) = P₂.map h₂ ⊗ₘ k)
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀) (t : ℝ≥0)
    {u' : ℂ → ℝ}
    (hu' : IsBoundedHarmonicExtension
      (cfWordData κ (fun x => forceBoundaryData κ ρL ρR xL xR x + -(θ * chiC κ)) (forceJumpFinset xL xR))
      (cfWordJumps κ (fun x => forceBoundaryData κ ρL ρR xL xR x + -(θ * chiC κ)) (forceJumpFinset xL xR)) u') :
    ∃ g : Ω × HistorySpace 0 0 → DistOn upperHalfPlaneOpens,
      IsLocalSetMean (fun p : Ω × HistorySpace 0 0 => cfHullQ t p.2) (fun p => cenTT κ θ u₀ (cfFieldT κ θ (h p.1)))
        (glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)) g ∧
      ∀ᵐ p ∂(glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)),
        ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ cfHullQ t p.2 →
          g p φ = ∫ z, cfMeanQ κ (fun x => forceBoundaryData κ ρL ρR xL xR x + -(θ * chiC κ))
            (forceJumpFinset xL xR) u' t p.2 z * φ z := by
  let _ : MeasurableSpace (Set ℂ) := hittingSigma
  set c : ℝ := -(θ * chiC κ) with hc
  set b : ℝ → ℝ := fun x => forceBoundaryData κ ρL ρR xL xR x + c with hbdef
  set jumps := forceJumpFinset xL xR with hjumps
  have hb : IsPiecewiseConstantBoundaryData b jumps := isPiecewiseConstant_forceData κ ρL ρR xL xR c
  have hXm : Measurable fun ω => cfFieldT κ θ (h ω) := (measurable_cfFieldT κ θ).comp hC.2.1
  have hh₂m := CfRegQ.measurable_of_isCenteredCounterflowDriver hcf
  have hDm := measurable_cfHistory (isMeasurableKilledDriving_of_isCenteredCounterflowDriver hcf)
  have hhh : IsGFFWithBoundaryData P h (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) := ⟨hC.2.1, hC.2.2.1⟩
  have hh' := isGFFWithBoundaryData_flowField_zero hhh c
  rw [← coe_forceJumpFinset] at hh'
  have hh₂ : IsGFFWithBoundaryData P₂ h₂ b jumps := CfRegQ.isGFFWithBoundaryData_of_map_eq hh' hh₂m hlaw
  have hu_b : IsBoundedHarmonicExtension b jumps (fun z => u₀ z + c) := by
    rw [hjumps, coe_forceJumpFinset]
    exact isBoundedHarmonicExtension_add_const hu₀ c
  have hu₀c : ContinuousOn u₀ H := fun z hz => (hu₀.1 z hz).1.continuousAt.continuousWithinAt
  have hu'c : ContinuousOn u' H := fun z hz => (hu'.1 z hz).1.continuousAt.continuousWithinAt
  have hπ₂ : Measurable (cfProj.{u} h₂ W₂ ζ₂) := measurable_up.comp (hh₂m.prodMk hDm)
  set μ := P₂.map (cfProj.{u} h₂ W₂ ζ₂) with hμdef
  have hglue := glueMeasure_map_cfProj hXm hh₂m hDm hlaw hk
  set slit : CfSpace.{u} → Set ℂ := fun q => cfHullQ t q.down.2 with hslit
  set fld : CfSpace.{u} → DistOn upperHalfPlaneOpens := fun q => cenTT κ θ u₀ q.down.1 with hfld
  have hslitm : Measurable[_, hittingSigma] slit := (measurable_cfHullQ t).comp (measurable_snd.comp measurable_down)
  have hfldm : Measurable fld := (measurable_cenTT κ θ u₀).comp (measurable_fst.comp measurable_down)
  -- the counterflow hull is local on the canonical space, and the centred field is a zero-boundary GFF there
  have hG₂ := isLocalSet_cfHullQ_cenTT (θ := θ) hcf hreg₂ hu₀.1 t
  have hpairm : Measurable fun q : CfSpace.{u} => (slit q, fld q) := hslitm.prodMk hfldm
  have hloc : IsLocalSet slit fld μ := by
    refine IsLocalSet.of_map_eq hG₂ hpairm.aemeasurable (ae_of_all _ fun q => cfHullQ_relClosed t q.down.2) ?_
    rw [hμdef, Measure.map_map hpairm hπ₂]
    rfl
  have hZglue : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens
      (fun p : Ω × HistorySpace 0 0 => cenTT κ θ u₀ (cfFieldT κ θ (h p.1)))
      (glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) hXm) := by
    have e : (fun p : Ω × HistorySpace 0 0 => cenTT κ θ u₀ (cfFieldT κ θ (h p.1))) =
        fun p => WholeField.centredField h u₀ p.1 := funext fun p => cenTT_cfFieldT κ θ u₀ (h p.1)
    rw [e]
    exact isZeroBoundaryGFF_comp_of_map_eq (g := WholeField.centredField h u₀) (f := Prod.fst) measurable_fst
      (glueMeasure_fst (μ := P) k hXm) (WholeField.isZeroBoundaryGFF_centredField hC hu₀)
  have hZ : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens fld μ := by
    refine ⟨hfldm, ?_⟩
    rw [hμdef, ← hglue]
    exact Restart.isZBGFFProcess_map (measurable_glueProjCf hXm)
      (fun φ => (LQGMetric.measurable_distOn_apply φ).comp hfldm) hZglue.process
  obtain ⟨g, hg⟩ := LocalSets.IsLocalSet.exists_isLocalSetMean hZ hslitm hloc
  have hgm : Measurable g := hg.1.mono (LocalSets.germSigma_le hslitm hfldm) le_rfl
  -- the identification on the counterflow's space
  set uG : Ω₂ → ℂ → ℝ := fun ω => Classical.choose (WholeField.exists_bhe (16 / κ) (cfRhoL κ b jumps)
    (cfRhoR κ b jumps) (cfPosL κ b jumps (W₂ · ω) t) (cfPosR κ b jumps (W₂ · ω) t)) with huGdef
  have huG : ∀ ω, IsBoundedHarmonicExtension
      (forceBoundaryData (16 / κ) (cfRhoL κ b jumps) (cfRhoR κ b jumps)
        (cfPosL κ b jumps (W₂ · ω) t) (cfPosR κ b jumps (W₂ · ω) t))
      (forceJumpSet (cfPosL κ b jumps (W₂ · ω) t) (cfPosR κ b jumps (W₂ · ω) t)) (uG ω) := fun ω =>
    Classical.choose_spec (WholeField.exists_bhe (16 / κ) (cfRhoL κ b jumps)
      (cfRhoR κ b jumps) (cfPosL κ b jumps (W₂ · ω) t) (cfPosR κ b jumps (W₂ · ω) t))
  obtain ⟨g₂, hg₂, hid₂⟩ := exists_isLocalSetMean_cfHullQ hκ hb hh₂ hcf hreg₂ hu_b hu' t huG
  have hgc : IsLocalSetMean (fun ω => cfHullQ t (cfHistory W₂ ζ₂ ω)) (fun ω => cenTT κ θ u₀ (h₂ ω)) P₂
      (fun ω => g (cfProj h₂ W₂ ζ₂ ω)) :=
    IsLocalSetMean.comp hπ₂ rfl hslitm hfldm hg
  have e : (fun ω => cenTT κ θ u₀ (h₂ ω)) = fun ω => h₂ ω - smoothDist upperHalfPlaneOpens (fun z => u₀ z + c) :=
    funext fun ω => cenTT_eq_sub κ θ hu₀c (h₂ ω)
  rw [e] at hgc
  have hAm : Measurable[mΩ₂, hittingSigma] fun ω => cfHullQ t (cfHistory W₂ ζ₂ ω) :=
    (measurable_cfHullQ t).comp hDm
  have hFm : Measurable fun ω => h₂ ω - smoothDist upperHalfPlaneOpens (fun z => u₀ z + c) :=
    (WholeField.measurable_sub_dist _).comp hh₂m
  -- test function by test function, the Borel tested candidate on the canonical space
  have hφ : ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ q ∂μ,
      Disjoint (tsupport φ) (slit q) → g q φ = cfTested κ b jumps u' t φ q.down.2 := by
    intro φ
    have hS : MeasurableSet {q : CfSpace.{u} |
        Disjoint (tsupport φ) (slit q) → g q φ = cfTested κ b jumps u' t φ q.down.2} := by
      have h1 : MeasurableSet {q : CfSpace.{u} | Disjoint (tsupport φ) (slit q)} :=
        measurableSet_disjoint_of_relClosed hslitm (fun q => cfHullQ_relClosed t q.down.2)
          φ.hasCompactSupport.isCompact φ.tsupport_subset
      have h2 : MeasurableSet {q : CfSpace.{u} | g q φ = cfTested κ b jumps u' t φ q.down.2} :=
        measurableSet_eq_fun ((LQGMetric.measurable_distOn_apply φ).comp hgm)
          ((measurable_cfTested κ b jumps u' t φ).comp (measurable_snd.comp measurable_down))
      have e2 : {q : CfSpace.{u} | Disjoint (tsupport φ) (slit q) → g q φ = cfTested κ b jumps u' t φ q.down.2} =
          {q | Disjoint (tsupport φ) (slit q)}ᶜ ∪ {q | g q φ = cfTested κ b jumps u' t φ q.down.2} := by
        ext q
        simp only [mem_ofPred_eq, mem_union, mem_compl_iff, imp_iff_not_or]
      rw [e2]
      exact h1.compl.union h2
    rw [hμdef, ae_map_iff hπ₂.aemeasurable hS]
    filter_upwards [LocalSets.IsLocalSetMean.ae_apply_eq hAm hFm hgc hg₂ φ, hid₂, hreg₂] with ω e1 e2 hω hdis
    have hφs : tsupport φ ⊆ H \ cfHullQ t (cfHistory W₂ ζ₂ ω) := fun z hz =>
      ⟨φ.tsupport_subset hz, fun hzG => Set.disjoint_left.1 hdis hz hzG⟩
    show g (cfProj h₂ W₂ ζ₂ ω) φ = cfTested κ b jumps u' t φ (cfHistory W₂ ζ₂ ω)
    rw [e1, e2 φ hφs, cfTested_eq κ b jumps hu'c t (cfHistory W₂ ζ₂ ω) (φ := φ) hdis]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    by_cases hz : φ z = 0
    · simp only [hz, mul_zero]
    · show (-couplingMean (16 / κ) (fun s : ℝ => W₂ s.toNNReal ω) t (uG ω) (negInv z) + u' (negInv z)) * φ z =
        cfMeanQ κ b jumps u' t (cfHistory W₂ ζ₂ ω) z * φ z
      rw [cfMeanQ_cfHistory κ b jumps u' hω.1 hω.2.1 hω.2.2 t (huG ω) (hφs (subset_tsupport _ hz))]
  -- all test functions at once, on the canonical space
  have hall : ∀ᵐ q ∂μ, ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ slit q →
      g q φ = ∫ z, cfMeanQ κ b jumps u' t q.down.2 z * φ z := by
    refine ae_forall_apply_eq_of_forall_ae hg.2.1 (ae_of_all _ fun q => (cfHullQ_relClosed t q.down.2).2)
      (ae_of_all _ fun q => harmonicOnNhd_cfMeanQ κ b jumps hu'.1 t q.down.2) fun φ => ?_
    filter_upwards [hφ φ] with q hq hφs
    have hdis : Disjoint (tsupport φ) (slit q) := Set.disjoint_left.2 fun z hz hzG => (hφs hz).2 hzG
    rw [hq hdis, cfTested_eq κ b jumps hu'c t _ hdis]
  refine ⟨fun p => g (glueProjCf (fun ω => cfFieldT κ θ (h ω)) p),
    IsLocalSetMean.comp (measurable_glueProjCf hXm) hglue hslitm hfldm hg, ?_⟩
  have hall' := hall
  rw [hμdef, ← hglue] at hall'
  exact ae_of_ae_map (measurable_glueProjCf hXm).aemeasurable hall'

/-- θ-version of `ae_union_mean_cfGlue` (`Sec5.GlueCondPath`):
the counterflow field is `h − θχ` instead of `h − π/2 χ`. -/
theorem ae_union_mean_cfGlueT (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hκ : 0 < κ) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) (hcf : IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂)
    (hreg₂ : ∀ᵐ ω ∂P₂, ζ₂ ω = ⊤ ∧ W₂ 0 ω = 0 ∧ Continuous fun t => W₂ t ω)
    (hlaw : P.map (fun ω => cfFieldT κ θ (h ω)) = P₂.map h₂)
    (hk : P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω)) = P₂.map h₂ ⊗ₘ k)
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀) (q t : ℝ≥0)
    {u' : ℂ → ℝ}
    (hu' : IsBoundedHarmonicExtension
      (cfWordData κ (fun x => forceBoundaryData κ ρL ρR xL xR x + -(θ * chiC κ)) (forceJumpFinset xL xR))
      (cfWordJumps κ (fun x => forceBoundaryData κ ρL ρR xL xR x + -(θ * chiC κ)) (forceJumpFinset xL xR)) u')
    {u : Ω → ℂ → ℝ}
    (hu : ∀ ω, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => VL i q ω - W q ω) (fun i => VR i q ω - W q ω))
      (forceJumpSet (fun i => VL i q ω - W q ω) (fun i => VR i q ω - W q ω)) (u ω))
    {g : Ω × HistorySpace 0 0 → DistOn upperHalfPlaneOpens}
    (hg : IsLocalSetMean (fun p : Ω × HistorySpace 0 0 => hullAt q (killedHistory W VL VR ζ p.1) ∪ cfHullQ t p.2)
      (fun p => cenTT κ θ u₀ (cfFieldT κ θ (h p.1)))
      (glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)) g) :
    ∀ᵐ p ∂(glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)),
      ∃ w : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w (H \ (hullAt q (killedHistory W VL VR ζ p.1) ∪ cfHullQ t p.2)) ∧
        (∀ φ : TestOn upperHalfPlaneOpens,
          tsupport φ ⊆ H \ (hullAt q (killedHistory W VL VR ζ p.1) ∪ cfHullQ t p.2) → g p φ = ∫ z, w z * φ z) ∧
        (∀ z₀ ∈ hullAt q (killedHistory W VL VR ζ p.1) ∪ {z : ℂ | z.im = 0},
          (∃ r > 0, cfHullQ t p.2 ∩ ball z₀ r ⊆ hullAt q (killedHistory W VL VR ζ p.1)) →
          Tendsto (fun z => w z - (couplingMean κ (fun s : ℝ => W s.toNNReal p.1) q (u p.1) z - u₀ z))
            (𝓝[H \ (hullAt q (killedHistory W VL VR ζ p.1) ∪ cfHullQ t p.2)] z₀) (𝓝 0)) ∧
        (∀ z₀ ∈ cfHullQ t p.2 ∪ {z : ℂ | z.im = 0},
          (∃ r > 0, hullAt q (killedHistory W VL VR ζ p.1) ∩ ball z₀ r ⊆ cfHullQ t p.2) →
          Tendsto (fun z => w z - cfMeanQ κ (fun x => forceBoundaryData κ ρL ρR xL xR x + -(θ * chiC κ))
              (forceJumpFinset xL xR) u' t p.2 z)
            (𝓝[H \ (hullAt q (killedHistory W VL VR ζ p.1) ∪ cfHullQ t p.2)] z₀) (𝓝 0)) := by
  have hXm : Measurable fun ω => cfFieldT κ θ (h ω) := (measurable_cfFieldT κ θ).comp hC.2.1
  obtain ⟨gA, hgA, hidA⟩ := exists_isLocalSetMean_flowHull_glueT (k := k) hC hκ hζ hu₀ q hu
  obtain ⟨gG, hgG, hidG⟩ := exists_isLocalSetMean_cfHullQ_pathT hC hκ hcf hreg₂ hlaw hk hu₀ t hu'
  -- the flow candidate is harmonic off the flow hull
  have hharmA : ∀ᵐ ω ∂P, InnerProductSpace.HarmonicOnNhd
      (fun z => couplingMean κ (fun s : ℝ => W s.toNNReal ω) q (u ω) z - u₀ z)
      (H \ hullAt q (killedHistory W VL VR ζ ω)) := by
    filter_upwards [Aux50Hit.ae_isGoodPath hC.1 hζ] with ω hgω
    have hK : hullAt q (killedHistory W VL VR ζ ω) = fwdHull (Ito.rpath fun t => W t ω) q :=
      Aux50Hit.regHull_stopHistory_cstop hgω q
    rw [hK]
    have h1 := Sec7.SideHeight.harmonicOnNhd_couplingMean (κ := κ) hgω.continuous_rpath q.coe_nonneg (hu ω).1
    intro z hz
    exact (h1 z hz).sub (hu₀.1 z hz.1)
  have hharmA' := ae_glue_fst (μ := P) k hXm hharmA
  filter_upwards [ae_union_boundary_cfGlueT hC hζ hcf hreg₂ hlaw hk hu₀ q t hg hgA hgG, hidA, hidG, hharmA']
    with p hp hA hG hhA
  exact hp _ _ hhA hA (harmonicOnNhd_cfMeanQ _ _ _ hu'.1 t p.2) hG

/-- θ-version of `ae_tendsto_union_sub_cfMean_cobounded` (`Sec5.GlueCondUnionImgInf`):
the counterflow field is `h − θχ` instead of `h − π/2 χ`. -/
theorem ae_tendsto_union_sub_cfMean_coboundedT (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) (hcf : IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂)
    (hreg₂ : ∀ᵐ ω ∂P₂, ζ₂ ω = ⊤ ∧ W₂ 0 ω = 0 ∧ Continuous fun t => W₂ t ω)
    (hlaw : P.map (fun ω => cfFieldT κ θ (h ω)) = P₂.map h₂)
    (hk : P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω)) = P₂.map h₂ ⊗ₘ k)
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀) (q t : ℝ≥0)
    {g gG : Ω × HistorySpace 0 0 → DistOn upperHalfPlaneOpens}
    (hg : IsLocalSetMean (fun p : Ω × HistorySpace 0 0 => hullAt q (killedHistory W VL VR ζ p.1) ∪ cfHullQ t p.2)
      (fun p => cenTT κ θ u₀ (cfFieldT κ θ (h p.1)))
      (glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)) g)
    (hgG : IsLocalSetMean (fun p : Ω × HistorySpace 0 0 => cfHullQ t p.2)
      (fun p => cenTT κ θ u₀ (cfFieldT κ θ (h p.1)))
      (glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)) gG) :
    ∀ᵐ p ∂(glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)), ∀ w wG : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd w (H \ (hullAt q (killedHistory W VL VR ζ p.1) ∪ cfHullQ t p.2)) →
      (∀ φ : TestOn upperHalfPlaneOpens,
        tsupport φ ⊆ H \ (hullAt q (killedHistory W VL VR ζ p.1) ∪ cfHullQ t p.2) → g p φ = ∫ z, w z * φ z) →
      InnerProductSpace.HarmonicOnNhd wG (H \ cfHullQ t p.2) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ cfHullQ t p.2 → gG p φ = ∫ z, wG z * φ z) →
      Tendsto (fun z => w z - wG z)
        (Bornology.cobounded ℂ ⊓ 𝓟 (H \ (hullAt q (killedHistory W VL VR ζ p.1) ∪ cfHullQ t p.2))) (𝓝 0) := by
  set μ := glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1) with hμ
  have hXm : Measurable fun ω => cfFieldT κ θ (h ω) := (measurable_cfFieldT κ θ).comp hC.2.1
  obtain ⟨hX, -⟩ := hC.2.2.2
  set Aω : Ω → Set ℂ := fun ω => hullAt q (killedHistory W VL VR ζ ω) with hAωdef
  have hAm : Measurable[mΩ, hittingSigma] Aω := (measurable_hullAt q).comp (measurable_killedHistory hX)
  obtain ⟨hAg, hGg, -⟩ := isLocalSet_union_glueT (k := k) hC hζ hcf hreg₂ hlaw hk hu₀ q t
  -- the glued field and its reflection are zero-boundary GFFs
  have hF0 : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (fun ω => cenTT κ θ u₀ (cfFieldT κ θ (h ω))) P := by
    have e : (fun ω => cenTT κ θ u₀ (cfFieldT κ θ (h ω))) = WholeField.centredField h u₀ :=
      funext fun ω => cenTT_cfFieldT κ θ u₀ (h ω)
    rw [e]
    exact WholeField.isZeroBoundaryGFF_centredField hC hu₀
  have hF : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (fun p : Ω × HistorySpace 0 0 =>
      cenTT κ θ u₀ (cfFieldT κ θ (h p.1))) μ :=
    isZeroBoundaryGFF_comp_of_map_eq (g := fun ω => cenTT κ θ u₀ (cfFieldT κ θ (h ω))) (f := Prod.fst) measurable_fst
      (glueMeasure_fst (μ := P) k hXm) hF0
  have hFR := isZeroBoundaryGFF_reflectField hF
  -- the reflected hulls: `R(A)` and `R(G) = K′_t`
  have hA₁ : Measurable[_, hittingSigma] fun p : Ω × HistorySpace 0 0 => negInv '' Aω p.1 := by
    let _ : MeasurableSpace (Set ℂ) := hittingSigma
    exact measurable_image_negInv.comp (hAm.comp measurable_fst)
  have hA₂ : Measurable[_, hittingSigma] fun p : Ω × HistorySpace 0 0 => hullAt t p.2 := by
    let _ : MeasurableSpace (Set ℂ) := hittingSigma
    exact (measurable_hullAt t).comp measurable_snd
  have hAωR : Measurable[mΩ, hittingSigma] fun ω => negInv '' Aω ω := by
    let _ : MeasurableSpace (Set ℂ) := hittingSigma
    exact measurable_image_negInv.comp hAm
  have hci := condIndepEv_glue_sets (P := P) hXm k (T := fun f => reflectField (cenTT κ θ u₀ f))
    (measurable_reflectField.comp (measurable_cenTT κ θ u₀)) (T' := fun f => cenTT' κ θ u₀ (reflectField f))
    ((measurable_cenTT' κ θ u₀).comp measurable_reflectField)
    (fun f => by
      show cenTT' κ θ u₀ (reflectField (reflectField (cenTT κ θ u₀ f))) = f
      rw [reflectField_reflectField, cenTT'_cenTT]) hAωR (measurable_hullAt t)
  have hGG : (fun p : Ω × HistorySpace 0 0 => negInv '' cfHullQ t p.2) = fun p => hullAt t p.2 :=
    funext fun p => image_negInv_image_negInv _
  have h₁ := WangWu.IsLocalSet.reflect hAg
  have h₂ := WangWu.IsLocalSet.reflect hGg
  rw [hGG] at h₂
  have hunb : ∀ᵐ p ∂μ, ∀ z ∈ LocalSets.lowerUnion (hullAt t p.2),
      ¬ Bornology.IsBounded (connectedComponentIn (LocalSets.lowerUnion (hullAt t p.2)) z) :=
    Eventually.of_forall fun p => not_isBounded_lowerUnion_of_isHPHull (isHPHull_hullAt _ _)
  have hrel : ∀ p : Ω × HistorySpace 0 0, (Aω p.1 ∪ cfHullQ t p.2) ⊆ H ∧ IsOpen (H \ (Aω p.1 ∪ cfHullQ t p.2)) := by
    intro p
    obtain ⟨h1, h1o⟩ := hullAt_relClosed q (killedHistory W VL VR ζ p.1)
    obtain ⟨h2, h2o⟩ := cfHullQ_relClosed t p.2
    refine ⟨union_subset h1 h2, ?_⟩
    rw [← Set.sdiff_inter_sdiff]; exact h1o.inter h2o
  have hg' := WangWu.IsLocalSetMean.reflect hrel hg
  have hUU : (fun p : Ω × HistorySpace 0 0 => negInv '' (Aω p.1 ∪ cfHullQ t p.2)) =
      fun p => negInv '' Aω p.1 ∪ hullAt t p.2 := by
    funext p; rw [image_union, cfHullQ, image_negInv_image_negInv]
  have hg'' : IsLocalSetMean (fun p : Ω × HistorySpace 0 0 => negInv '' Aω p.1 ∪ hullAt t p.2)
      (fun p => reflectField (cenTT κ θ u₀ (cfFieldT κ θ (h p.1)))) μ (fun p => reflectField (g p)) := by
    rw [← hUU]; exact hg'
  have hgG' : IsLocalSetMean (fun p : Ω × HistorySpace 0 0 => hullAt t p.2)
      (fun p => reflectField (cenTT κ θ u₀ (cfFieldT κ θ (h p.1)))) μ (fun p => reflectField (gG p)) := by
    have := WangWu.IsLocalSetMean.reflect (A := fun p : Ω × HistorySpace 0 0 => cfHullQ t p.2)
      (h := fun p => cenTT κ θ u₀ (cfFieldT κ θ (h p.1))) (g := gG) (fun p => cfHullQ_relClosed t p.2) hgG
    rw [hGG] at this
    exact this
  have h38 := LocalSets.IsLocalSetMean.ae_tendsto_sub_of_union hFR hA₁ hA₂ hci h₁ h₂ hunb hg'' hgG'
  filter_upwards [h38] with p ⟨u, hu, hrep, hlim⟩
  intro w wG hw hrepw hwG hrepwG
  set C := H \ (Aω p.1 ∪ cfHullQ t p.2) with hCdef
  have hCo : IsOpen C := (hrel p).2
  have hCH : C ⊆ H := sdiff_subset
  have hCG : C ⊆ H \ cfHullQ t p.2 := fun z hz => ⟨hz.1, fun h' => hz.2 (Or.inr h')⟩
  have hRC : H \ (negInv '' Aω p.1 ∪ hullAt t p.2) = negInv '' C := by
    rw [← image_negInv_image_negInv (hullAt t p.2), ← image_union, H_diff_image_negInv]
    rfl
  -- `u = −w ∘ R + w_G ∘ R` on `R(C)`
  have hRCo : IsOpen (negInv '' C) := isOpen_image_negInv hCo hCH
  have hRCH : negInv '' C ⊆ H := image_negInv_subset_H hCH
  have hw' := harmonicOnNhd_comp_negInv hCo hCH hw
  have hwG' := harmonicOnNhd_comp_negInv hCo hCH (fun z hz => hwG z (hCG hz))
  have hv : InnerProductSpace.HarmonicOnNhd (fun z => -w (negInv z) + wG (negInv z)) (negInv '' C) :=
    fun z hz => (hw' z hz).neg.add (hwG' z hz)
  have hcont : ∀ {v : ℂ → ℝ} {U : Set ℂ}, InnerProductSpace.HarmonicOnNhd v U → ContinuousOn v U :=
    fun hv z hz => (hv z hz).1.continuousAt.continuousWithinAt
  have hu' : InnerProductSpace.HarmonicOnNhd u (negInv '' C) := by rw [← hRC]; exact hu
  have heq : EqOn u (fun z => -w (negInv z) + wG (negInv z)) (negInv '' C) := by
    refine Sec6.eqOn_of_integral_mul_eq hRCo hRCH hu' hv fun φ hφ => ?_
    have hφ' : tsupport φ ⊆ H \ (negInv '' Aω p.1 ∪ hullAt t p.2) := by rw [hRC]; exact hφ
    have i1 := LocalSets.integrable_mul_test hRCo (hcont hw').neg φ hφ
    have i2 := LocalSets.integrable_mul_test hRCo (hcont hwG') φ hφ
    have e1 := reflectField_rep hrepw φ hφ
    have e2 := reflectField_rep (U := H \ cfHullQ t p.2) hrepwG φ (hφ.trans (image_mono hCG))
    rw [← hrep φ hφ', e1, e2]
    have i1' : Integrable fun z => -w (negInv z) * φ z := i1
    have i2' : Integrable fun z => -wG (negInv z) * φ z := by
      refine i2.neg.congr (Eventually.of_forall fun z => ?_)
      simp only [Pi.neg_apply, Function.comp_apply, neg_mul]
    rw [← integral_sub i1' i2']
    congr 1; funext z; ring
  -- the limit at `0` of the chart `R`
  obtain ⟨M, hM⟩ := (isHPHull_hullAt q (killedHistory W VL VR ζ p.1)).2.1.subset_closedBall 0
  have hM0 : 0 < max M 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hloc : ∃ r > 0, negInv '' Aω p.1 ∩ ball 0 r ⊆ hullAt t p.2 := by
    refine ⟨(max M 1)⁻¹, inv_pos.2 hM0, ?_⟩
    rintro _ ⟨⟨a, ha, rfl⟩, hb⟩
    exfalso
    have ha' : ‖a‖ ≤ max M 1 := by
      have := hM ha
      rw [mem_closedBall, dist_zero_right] at this
      exact this.trans (le_max_left _ _)
    have ha0 : a ≠ 0 := ne_zero_of_mem_H ((hullAt_relClosed q _).1 ha)
    rw [mem_ball, dist_zero_right, norm_negInv] at hb
    have hapos : 0 < ‖a‖ := norm_pos_iff.2 ha0
    have := (inv_lt_inv₀ hapos hM0).1 hb
    linarith
  have h0 := hlim 0 (Or.inr (by simp)) hloc
  rw [hRC] at h0
  refine tendsto_cobounded_of_negInv (u := fun z => -u z) (fun z hz => ?_) ?_
  · have := heq (mem_image_of_mem negInv hz)
    simp only [WangWu.negInv_negInv] at this
    rw [this]; ring
  · simpa using h0.neg

end Mean

end InteractingSLE.Sec5.CrossCond.Theta
