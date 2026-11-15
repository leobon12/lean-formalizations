/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.AssemblyUnique
import InteractingSLE.Spec.Sec2.RestartMarkov
import InteractingSLE.Spec.Coupling.WholeField2Germ
import InteractingSLE.Spec.Exist.BrownianTransfer
import InteractingSLE.Spec.Coupling.Assembly11BProvider
import InteractingSLE.Spec.Sec7.StripSysField
import InteractingSLE.Spec.Sec7.StripSys
import LQGMetric.Field.StandardBorelRange

/-!
# The strip system on a standard Borel space

Packet PROVE-STRIPSYS3, the blocker of PROVE-STRIPSYS2 §5.1: `IsStripSystem` (and the frozen `IsStagedHistory`) need a
standard Borel sample space, while Theorem 1.1's coupling lives on `Ω₀ × 𝒟′(ℍ)` with `Ω₀` the (arbitrary) space of
Theorem 2.2's evolution.

* **Theorem 2.2 on the code space** (`isIntegratedSLEEvolution_code`): every integrated `SLE_a(ρ)` evolution, read
  through the dyadic code of Theorem 2.2's uniqueness proof (`Sec2.Assembly.codeOf`, with a continuous version of the
  noise), has an image law under which the decoded paths form an integrated evolution on the standard Borel space
  `Sec2.Assembly.XCode nL nR`. The solution relation is a measurable set of codes (`measurableSet_cRel`) containing
  almost every code (`ae_codeOf_mem`), and integrated evolutions transfer along laws
  (`Exist.isIntegratedSLEEvolution_of_map_eq`).
* **Theorem 1.1 on a standard Borel space** (`exists_isOptionalHullCoupling_standardBorel`): the landed construction
  `Coupling.exists_isOptionalHullCoupling_of_finiteFamilyProj` run on that evolution gives the coupling on
  `ULift XCode × 𝒟′(ℍ)`, standard Borel by the host's `LQGMetric.standardBorelSpace_distOn`.
* **The centred counterflow on a standard Borel space** (`exists_isCenteredCounterflowDriver_standardBorel`) and the
  strip system (`exists_isStripSystem`, from Theorem 1.4's construction input).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Sec7

namespace StripSysBorel

open LQGMetric Sec2.Assembly

variable {nL nR : ℕ}

/-! ### Almost sure modifications of an integrated evolution -/

/-- **An integrated evolution survives almost sure modifications** of the driving process before the lifetime, of
the lifetime and of the noise, when its filtration contains the null sets and the modified objects are measurable
and satisfy the pathwise relation. -/
theorem isIntegratedSLEEvolution_of_ae_agree {a : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {Q : Measure Ω}
    {𝓖 : Filtration ℝ≥0 mΩ} {W W' : ℝ≥0 → Ω → ℝ} {VL VL' : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR VR' : Fin nR → ℝ≥0 → Ω → ℝ} {B B' : ℝ≥0 → Ω → ℝ} {ζ ζ' : Ω → ℝ≥0∞}
    (hE : IsIntegratedSLEEvolution a xL xR ρL ρR Q 𝓖 W VL VR B ζ)
    (hnull : ∀ t (N : Set Ω), MeasurableSet N → Q N = 0 → MeasurableSet[𝓖 t] N)
    (hX' : IsMeasurableKilledDriving W' VL' VR' ζ') (hB'm : ∀ t, Measurable (B' t))
    (hagree : ∀ᵐ p ∂Q, ζ' p = ζ p ∧ (∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ p → W' t p = W t p ∧
      (∀ i, VL' i t p = VL i t p) ∧ ∀ j, VR' j t p = VR j t p) ∧ ∀ t, B' t p = B t p)
    (hpath : ∀ᵐ p ∂Q, IsIntegratedSLEPath a xL xR ρL ρR (fun t => W' t p) (fun i t => VL' i t p)
      (fun j t => VR' j t p) (fun t => B' t p) (ζ' p)) :
    IsIntegratedSLEEvolution a xL xR ρL ρR Q 𝓖 W' VL' VR' B' ζ' := by
  have hBB : ∀ t, B t =ᵐ[Q] B' t := fun t => hagree.mono fun p hp => (hp.2.2 t).symm
  have hadapt : ∀ (X : ℝ≥0 → Ω → ℝ) (X' : ℝ≥0 → Ω → ℝ), AdaptedBefore 𝓖 ζ X →
      (∀ (t : ℝ≥0) (A : Set ℝ), MeasurableSet A → MeasurableSet {p | (t : ℝ≥0∞) < ζ' p ∧ X' t p ∈ A}) →
      (∀ᵐ p ∂Q, ζ' p = ζ p ∧ ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ p → X' t p = X t p) →
      AdaptedBefore 𝓖 ζ' X' := by
    intro X X' hX hm hXX t A hA
    refine WholeField.measurableSet_of_ae_eq (𝓖.le t) (hnull t) (hm t A hA) (hX t A hA) ?_
    filter_upwards [hXX] with p hp
    apply propext
    rw [hp.1]
    exact ⟨fun h => ⟨h.1, hp.2 t h.1 ▸ h.2⟩, fun h => ⟨h.1, (hp.2 t h.1).symm ▸ h.2⟩⟩
  refine ⟨⟨⟨hE.1.1.toIsPreBrownianReal.congr hBB, ?_⟩, fun t => ?_, fun s t hst => ?_⟩,
    hadapt W W' hE.2.1 (fun (t : ℝ≥0) A hA => hX' t _ (measurable_fst hA))
      (hagree.mono fun p hp => ⟨hp.1, fun t ht => (hp.2.1 t ht).1⟩),
    fun i => hadapt (VL i) (VL' i) (hE.2.2.1 i)
      (fun (t : ℝ≥0) A hA => hX' t _ ((measurable_pi_apply i).comp (measurable_fst.comp measurable_snd) hA))
      (hagree.mono fun p hp => ⟨hp.1, fun t ht => (hp.2.1 t ht).2.1 i⟩),
    fun j => hadapt (VR j) (VR' j) (hE.2.2.2.1 j)
      (fun (t : ℝ≥0) A hA => hX' t _ ((measurable_pi_apply j).comp (measurable_snd.comp measurable_snd) hA))
      (hagree.mono fun p hp => ⟨hp.1, fun t ht => (hp.2.1 t ht).2.2 j⟩), hpath⟩
  · filter_upwards [hE.1.1.cont, hagree] with p hp hq
    have e : (fun t => B' t p) = fun t => B t p := funext fun t => hq.2.2 t
    rw [e]; exact hp
  · exact Sec2.Restart.measurable_of_ae_eq_of_null (𝓖.le t) (hnull t) (hE.1.2.1 t) (hB'm t) (hBB t)
  · refine Sec2.Restart.indep_comap_congr ?_ (hE.1.2.2 s t hst)
    filter_upwards [hagree] with p hp
    simp only [hp.2.2]

/-! ### Theorem 2.2's evolutions on the code space -/

/-- The decoded killed driving of the code space is measurable. -/
theorem isMeasurableKilledDriving_code :
    IsMeasurableKilledDriving (fun t (x : XCode nL nR) => cw x t) (fun i t x => cvL x i t)
      (fun j t x => cvR x j t) cζ := fun r _ hA =>
  (measurableSet_lt measurable_const measurable_cζ).inter (measurable_stateAt r hA)

/-- **Every integrated `SLE_a(ρ)` evolution has a copy on the standard Borel code space**: the decoded paths of
`Sec2.Assembly.XCode nL nR` form an integrated evolution under the law of the code of the given one. -/
theorem isIntegratedSLEEvolution_code {a : ℝ} (ha : 0 < a) {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {Ω₀ : Type*} {m₀ : MeasurableSpace Ω₀} {P₀ : Measure Ω₀}
    [IsProbabilityMeasure P₀] {𝓕 : Filtration ℝ≥0 m₀} {W : ℝ≥0 → Ω₀ → ℝ} {VL : Fin nL → ℝ≥0 → Ω₀ → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω₀ → ℝ} {B : ℝ≥0 → Ω₀ → ℝ} {ζ : Ω₀ → ℝ≥0∞}
    (hE : IsIntegratedSLEEvolution a xL xR ρL ρR P₀ 𝓕 W VL VR B ζ) :
    ∃ (μ : Measure (XCode nL nR)) (_ : IsProbabilityMeasure μ) (𝓗 : Filtration ℝ≥0 (inferInstance :
      MeasurableSpace (XCode nL nR))),
      IsIntegratedSLEEvolution a xL xR ρL ρR μ 𝓗 (fun t x => cw x t) (fun i t x => cvL x i t)
        (fun j t x => cvR x j t) (fun t x => cb x t) cζ := by
  obtain ⟨B', hB'm, hB'c, -, hae⟩ := Sec2.Restart.exists_continuous_version hE.1
  set Φ := codeOf xL xR B' W VL VR ζ with hΦdef
  have hΦ : Measurable Φ := measurable_codeOf hB'm hE.2.1 hE.2.2.1 hE.2.2.2.1
  have hX := isMeasurableKilledDriving_code (nL := nL) (nR := nR)
  have hB : ∀ t, Measurable fun x : XCode nL nR => cb x t := measurable_cb_at
  have hmem := ae_codeOf_mem ha hE hB'c hae
  -- the processes read through the code form an evolution of the usual augmentation
  have hE₀ : IsIntegratedSLEEvolution a xL xR ρL ρR P₀ (usualAugmentation 𝓕 P₀)
      (fun t ω => cw (Φ ω) t) (fun i t ω => cvL (Φ ω) i t) (fun j t ω => cvR (Φ ω) j t)
      (fun t ω => cb (Φ ω) t) (fun ω => cζ (Φ ω)) := by
    refine isIntegratedSLEEvolution_of_ae_agree (Ito.isIntegratedSLEEvolution_usualAugmentation hE)
      (fun t N hN h0 => Ito.measurableSet_usualAugmentation_of_null hN h0 t)
      (Exist.isMeasurableKilledDriving_comp hX hΦ) (fun t => (hB t).comp hΦ) ?_ ?_
    · filter_upwards [hmem, hae] with ω h1 h2
      refine ⟨rfl, fun t ht => ⟨(h1.2 t ht).1, (h1.2 t ht).2.1, (h1.2 t ht).2.2.1⟩, fun t => ?_⟩
      show dec (enc (B' · ω)) t = B t ω
      rw [dec_enc (hB'c ω).continuousWithinAt, h2 t]
    · filter_upwards [hmem] with ω h1
      exact h1.1.1.2.2
  have hμ : ∀ᵐ x ∂(P₀.map Φ), x ∈ CRel a xL xR ρL ρR :=
    (ae_map_iff hΦ.aemeasurable (measurableSet_cRel a xL xR ρL ρR)).2 (hmem.mono fun ω h => h.1)
  refine ⟨P₀.map Φ, inferInstance, _,
    Exist.isIntegratedSLEEvolution_of_map_eq hX hB hΦ hE₀ (g := id) measurable_id Measure.map_id ?_ ?_⟩
  · filter_upwards [hμ] with x hx
    exact hx.1.1.continuous_b
  · filter_upwards [hμ] with x hx
    exact hx.1.2.2

/-! ### Theorem 1.1's coupling on a standard Borel space -/

section Coupling

open Coupling Ito LQGMetric.MarkovZB LocalSets QuantumZipper.K3 QuantumZipper.Thm11Asm
open SupercriticalConformalCovariance.GM24 (smoothDist smoothDist_apply)

/-- The landed construction of Theorem 1.1's coupling (`Coupling.exists_isOptionalHullCoupling_of_finiteFamilyProj`,
the same proof) with its sample space exposed: an evolution on `Ω` gives the coupling on `ULift Ω × 𝒟′(ℍ)` with the
field the second coordinate. -/
theorem exists_isOptionalHullCoupling_prod {κ : ℝ} (hκ : 0 < κ) {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {Ω : Type} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (hI2 : FiniteFamilyProjStatement.{u} κ xL xR ρL ρR) :
    ∃ (μ : Measure (ULift.{u} Ω × DistOn upperHalfPlaneOpens)) (_ : IsProbabilityMeasure μ)
      (𝓕' : Filtration ℝ≥0 (inferInstance : MeasurableSpace (ULift.{u} Ω × DistOn upperHalfPlaneOpens)))
      (W' : ℝ≥0 → ULift.{u} Ω × DistOn upperHalfPlaneOpens → ℝ)
      (VL' : Fin nL → ℝ≥0 → ULift.{u} Ω × DistOn upperHalfPlaneOpens → ℝ)
      (VR' : Fin nR → ℝ≥0 → ULift.{u} Ω × DistOn upperHalfPlaneOpens → ℝ)
      (B' : ℝ≥0 → ULift.{u} Ω × DistOn upperHalfPlaneOpens → ℝ)
      (ζ' : ULift.{u} Ω × DistOn upperHalfPlaneOpens → ℝ≥0∞),
      IsOptionalHullCoupling κ xL xR ρL ρR μ 𝓕' W' VL' VR' B' ζ' (fun p => p.2) := by
  set P₀ : Measure (ULift.{u} Ω) := P.map ULift.up with hP₀
  have hP₀p : IsProbabilityMeasure P₀ := inferInstance
  have hmap : P₀.map ULift.down = P := by
    rw [hP₀, Measure.map_map measurable_down measurable_up]
    exact Measure.map_id
  have hE₀ := IsIntegratedSLEEvolution.comap measurable_down hmap hE
  have hc := measurable_coordVal hE₀
  have hE₁ := isIntegratedSLEEvolution_coordFiltration hE₀
  have hgen := IsAeGen.usualAugmentation (IsAeGen.usualAugmentation (P₀ := P₀)
    (isAeGen_coordFiltration (P₀ := P₀) hc))
  obtain ⟨α, μ, hαp, hμp, hμ1, hμ2, hαG, hfamS, hfamL⟩ :=
    exists_locCoupling_of_evolution hκ hE₁ (measurable_coordMap hc) hgen hI2
  set u₀ : ℂ → ℝ := Impl.forceExt κ (weightWord ρL ρR) xL xR with hu₀def
  have hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀ :=
    Impl.isBoundedHarmonicExtension_forceExt κ (weightWord ρL ρR) xL xR
  have hu₀c : ContinuousOn u₀ QuantumZipper.H := fun z hz => (hu₀.1 z hz).1.continuousAt.continuousWithinAt
  have hEμ := IsIntegratedSLEEvolution.fst (X := DistOn upperHalfPlaneOpens) hμ1 hE₁
  have hZμ : IsZeroBoundaryGFF upperHalfPlaneOpens
      (fun p : ULift.{u} Ω × DistOn upperHalfPlaneOpens => p.2 - smoothDist upperHalfPlaneOpens u₀) μ :=
    isZeroBoundaryGFF_sub_smoothDist measurable_snd hu₀c (isZBGFFProcess_comp_snd hμ2 (hαG u₀ hu₀))
  have hharm : IsHarmonicDistOn (smoothDist upperHalfPlaneOpens u₀) QuantumZipper.H :=
    isHarmonicDistOn_smoothDist_of hu₀
  refine ⟨μ, hμp, _, _, _, _, _, _, isOptionalHullCoupling_of_isFamilySampled hEμ hκ measurable_snd
      (fun u₀' hu₀' => isZBGFFProcess_comp_snd hμ2 (hαG u₀' hu₀')) hfamS fun hX τ hτ hτζ => ?_⟩
  have hl := isLocalSet_hull_of_isFamilyLocal hEμ hX hZμ (hfamL u₀ hu₀) hτ hτζ
  have hl' := IsLocalSet.add_dist hl hharm
  have e : (fun p : ULift.{u} Ω × DistOn upperHalfPlaneOpens =>
      p.2 - smoothDist upperHalfPlaneOpens u₀ + smoothDist upperHalfPlaneOpens u₀) = fun p => p.2 :=
    funext fun p => sub_add_cancel _ _
  rw [e] at hl'
  exact hl'

end Coupling

/-- `ULift` of a standard Borel space is standard Borel. -/
instance instStandardBorelSpaceULift {X : Type} [MeasurableSpace X] [StandardBorelSpace X] :
    StandardBorelSpace (ULift.{u} X) :=
  LQGMetric.standardBorelSpace_of_measurableEquiv MeasurableEquiv.ulift

/-- **Theorem 1.1 on a standard Borel space**: for every ordered force word there is an optional hull coupling on a
standard Borel sample space (any universe). -/
theorem exists_isOptionalHullCoupling_standardBorel {κ : ℝ} (hκ : 0 < κ) {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (hF : IsOrderedForceWord xL xR) :
    ∃ (Ω : Type u) (mΩ : MeasurableSpace Ω) (_ : StandardBorelSpace Ω) (P : Measure Ω)
      (_ : IsProbabilityMeasure P) (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
      (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞)
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens),
      IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h := by
  obtain ⟨Ω, mΩ, P, hP, 𝓕, W, VL, VR, B, ζ, hE⟩ :=
    exists_isIntegratedSLEEvolution_assembled (ρL := ρL) (ρR := ρR) hκ hF
  obtain ⟨μ, hμ, 𝓗, hE'⟩ := isIntegratedSLEEvolution_code hκ hE
  obtain ⟨ν, hν, 𝓕', W', VL', VR', B', ζ', hC⟩ :=
    exists_isOptionalHullCoupling_prod.{u} hκ hE' (Coupling.finiteFamilyProjStatement hκ xL xR ρL ρR)
  exact ⟨ULift.{u} (XCode nL nR) × DistOn upperHalfPlaneOpens, inferInstance, inferInstance, ν, hν, 𝓕', W',
    VL', VR', B', ζ', fun p => p.2, hC⟩

/-! ### The centred counterflow and the strip system on a standard Borel space -/

section Counterflow

open StripSysField

/-- **The centred counterflow coupling on a standard Borel space**: `StripSysField.exists_isCenteredCounterflowDriver`
(the same construction: Theorem 1.1 at `16/κ` for the transported data, then the return transport) on the standard
Borel coupling `exists_isOptionalHullCoupling_standardBorel`. -/
theorem exists_isCenteredCounterflowDriver_standardBorel {κ : ℝ} (hκ : 0 < κ) {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) :
    ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (_ : StandardBorelSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (h : Ω → DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
      IsGFFWithBoundaryData P h b jumps ∧ IsCenteredCounterflowDriver κ P h W ζ ∧
        (IsNonhitCounterflowWord κ b jumps → ∀ᵐ ω ∂P, ζ ω = ⊤) := by
  have hκ' : 0 < 16 / κ := div_pos (by norm_num) hκ
  set b' := counterflowData κ b with hb'def
  set J' := counterflowJumps jumps with hJ'def
  have hb' : IsPiecewiseConstantBoundaryData b' J' := isPiecewiseConstant_counterflowData κ hb
  have hF := Theorem15.isOrderedForceWord_flowLine b' J' 0
  obtain ⟨Ω, mΩ, hSB, P, hP, 𝓕, W, VL, VR, B, ζ, h', hC⟩ :=
    exists_isOptionalHullCoupling_standardBorel.{u} (ρL := flowLineRhoL (16 / κ) b' J' 0 0)
      (ρR := flowLineRhoR (16 / κ) b' J' 0 0) hκ' hF
  refine ⟨Ω, mΩ, hSB, P, hP, fun ω => returnField (cfOffset κ) (cfCoeff κ) (h' ω), W, ζ, ?_, ?_, ?_⟩
  · have hh' : IsGFFWithBoundaryData P h' b' J' := isGFFWithBoundaryData_of_flowLineGFF hκ' hb' ⟨hC.2.1, hC.2.2.1⟩
    have hex : ∃ u, IsBoundedHarmonicExtension b' J' u := by
      obtain ⟨u, hu, -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension hb'
      exact ⟨u, hu⟩
    have hR := isGFFWithBoundaryData_returnField (cfOffset κ) (cfCoeff κ) hex hh'
    refine isGFFWithBoundaryData_of_subset (subset_returnExcept_returnExcept jumps) (fun x hx => ?_) hR
    exact returnData_inverseData _ _ b (ne_zero_of_notMem_returnExcept hx)
  · exact ⟨b', J', h', hb', fun ω => isChartTransport_returnField _ _ (h' ω),
      h', 𝓕, VL, VR, B, fun ω => isTranslateAddConst_zero_self (h' ω) _, hC⟩
  · rintro ⟨c, hc, hL, hR⟩
    exact ae_lifetime_eq_top_of_groupEndSums hc hF hL hR hC.1

/-- **The strip system exists** (PROVE-STRIPSYS §5 A–B) for a non-hit counterflow word, given Theorem 1.4's
construction input `Theorem14.StagedHistoryConstructionStatement` (Theorems 1.1–1.2 in conditional form,
PROVE-FLOWEXIST3's goal): the GFF, the centred counterflow with infinite lifetime and every boundary-continued
staged history on one standard Borel space. -/
theorem exists_isStripSystem (hCon : Theorem14.StagedHistoryConstructionStatement.{u}) {κ : ℝ} (hκ : 0 < κ)
    (hκ4 : κ < 4) {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hnh : IsNonhitCounterflowWord κ b jumps) :
    ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (_ : StandardBorelSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (h : Ω → DistOn upperHalfPlaneOpens) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞)
      (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞), StripSys.IsStripSystem κ b jumps P h W' ζ' E := by
  obtain ⟨Ω, mΩ, hSB, P, hP, h, W', ζ', hh, hcf, hζ⟩ := exists_isCenteredCounterflowDriver_standardBorel.{u} hκ hb
  obtain ⟨E, hE⟩ := StripSys.exists_isStripSystem_of_construction hCon hκ hκ4 hb hh hcf (hζ hnh)
  exact ⟨Ω, mΩ, hSB, P, hP, h, W', ζ', E, hE⟩

end Counterflow

end StripSysBorel

end Sec7

end InteractingSLE
