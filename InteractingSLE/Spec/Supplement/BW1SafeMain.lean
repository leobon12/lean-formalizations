/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.BW1SafeLines
import InteractingSLE.Spec.Supplement.BW1SafeMeas
import InteractingSLE.Spec.Supplement.BW1SafeShape
import InteractingSLE.Spec.Supplement.BW1SafeData
import InteractingSLE.Spec.Supplement.BW1SafeMarks
import InteractingSLE.Spec.Supplement.BW1SafeVer
import InteractingSLE.Spec.Supplement.RelSafeS6
import InteractingSLE.Spec.Supplement.RelSafeS8
import InteractingSLE.Spec.Supplement.GB6LineL3

/-!
# Proposition BW1's relative safe law from the union mean identification

Packet PROVE-BW1-SAFELAW. **`bw1RelSafeLawHStatement_of_mean`**: BW1's K2 inputs (S) and (L) for every version with
hull identities (`BW1RelSafeLawHStatement`) from Theorems 1.2–1.3 and ONE named input, **`BW1LineMeanStatement`** —
the union mean identification at the physical lines (Aux. 79 for BW1; the GB6 analogue is
`GB6LineL.GB6LineMeanStatement`). Hence **`bw1Statement_of_mean`**: Proposition BW1 from Theorems 1.2–1.3, the
canonical driver codes and `BW1LineMeanStatement`.

The line data of K2's lines step (`hasSafe_bw_of_lines`), with the physical filtration `σ(rec) ∨ σ(Wd_{≤t}) ∨ 𝒩`
and the clock `a = min(bClock, V)`:

* (L0) the centring `u₀′`: the bounded harmonic extension of the counterflow's initial data, `h′ − u₀′` a zero-boundary
  GFF;
* (L1) the marks `ℋ_t = σ(rec) ∨ 𝒩 ∨ 𝓕^cf_t` and the physical union `B_t = relClosure(R(A) ∪ K′_t)`: BW1's TERMINAL
  retained set is marked local for its record (`exists_bw1_retained_marks`), the counterflow hull for its driving
  filtration (`RelSafeS.isHistoryAvoidanceLocal_cfHull`), and the union of the two determined marked local sets is
  marked local for the joined marks (`WalkLaw.isHistoryAvoidanceLocal_union_of_det`);
* (L2) the shape of `ℍ ∖ B_t` (`ae_compl_union_eq_relChart_bw`);
* (L4) the safe events (`bw1SafeMeas`);
* the line kernels from the marked locality (`RelSafeS.ae_condExp_cexp_marked`), with the line means the local-set
  means of `B_t` plus `u₀′`; their identification with the canonical relative mean is (L3), the named input.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull chiC zeroGFFTestCov)
open LQGMetric (TestOn DistOn)

universe u

namespace InteractingSLE.Theorem14.BW1Safe

open Exist Exist.Staged Exist.StagedLaw Supp8.GB6 Supp8.GB6.RelDrv Supp8.Q3Stop Supp8.RelSafe LocalSets Restart
  Restart.DomainMarkov.K2 Sec7.PocketTraversal BW1Ver BW1Life

/-- **BW1's union mean identification at the physical lines** (Aux. 79 at the lines of K2's lines step, for BW1):
for every local-set mean `g` of the physical union `B t` of the centred counterflow-frame field `h′ − u₀`, on the
live event before the stop and for `ψ` off the relative hull, the transport of `g + u₀` through the relative chart
of the record is the canonical relative mean at `a(t) = min(bClock t, V)`. -/
def HasBUnionMean {Ω : Type*} [MeasurableSpace Ω] (κ θ : ℝ) (c₀ : BoundaryWord) (P : Measure Ω)
    (h' Hc : Ω → DistOn upperHalfPlaneOpens) (rec : Ω → RecData) (W : ℝ≥0 → Ω → ℝ) (GT : Set Ω)
    (TS : Set RecData) (R : ℝ≥0 → Ω → ℝ) (V : Ω → ℝ≥0∞) (w : WordType) (u₀ : ℂ → ℝ) (B : ℝ≥0 → Ω → Set ℂ) :
    Prop :=
  ∀ (t : ℝ≥0) (g : Ω → DistOn upperHalfPlaneOpens),
    IsLocalSetMean (B t) (WholeField.centredField h' u₀) P g →
    ∀ ψ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ bLive κ θ c₀ rec TS w →
      min (bClock rec W GT t ω) (V ω) < V ω →
      Disjoint (tsupport ψ) (fwdHull (fun r : ℝ => R r.toNNReal ω) (min (bClock rec W GT t ω) (V ω)).toNNReal) →
      Chart.chartTransport (Supp8.RelSafeS.isConformal_relChart (rec ω)) 1 (2 * Real.pi * chiC (16 / κ))
          (chiC (16 / κ)) (g ω + SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀) ψ =
        ∫ z, couplingMean (16 / κ) (fun r : ℝ => R r.toNNReal ω) (min (bClock rec W GT t ω) (V ω)).toNNReal
          (DomainMarkov.bheProc (16 / κ) (typedRhoL w) (typedRhoR w) R
            (fun i t ω => geomLW canonDrv (bTypedL κ θ c₀ w) i t (rec ω, relVar Hc R V ω))
            (fun j t ω => geomRW canonDrv (bTypedR κ θ c₀ w) j t (rec ω, relVar Hc R V ω)) ω
            (min (bClock rec W GT t ω) (V ω)).toNNReal) z * ψ z

/-- **Named input (L3) for BW1: the union mean identification** (binders of `BW1RelSafeLawHStatement`, the physical
driver version `Wd` and good event `GT` of `exists_bw1_safe_data`, the counterflow-frame data `b′ J′ h′` of the
centred counterflow, the counterflow's initial extension `u₀`): for every version `B` of the physical union
`relClosure(R(A) ∪ K′_t)` that is a local set of `h′ − u₀`, `HasBUnionMean` holds. -/
def BW1LineMeanStatement : Prop :=
  ∀ (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens) (W' : ℝ≥0 → Ω → ℝ)
    (ζ' : Ω → ℝ≥0∞) (θ : ℝ) (t : ℝ≥0∞) (gw2 : Bool) (rest : List Instr) (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞),
    IsBW1Setting κ b jumps P h W' ζ' θ t gw2 rest E → ∀ (r : Bool) (TS : Set RecData), MeasurableSet TS →
    (∀ᵐ ω ∂P, ω ∈ bwEvent κ b jumps (bwSpec gw2 θ t rest) E r ↔ bwRec κ b jumps (bwSpec gw2 θ t rest) E ω ∈ TS) →
    ∀ c₀ : BoundaryWord, c₀.jumps = jumps → (∀ y ∉ jumps, c₀.fn y = b y) →
    ∀ (R : ℕ → ℝ≥0 → Ω → ℝ) (V : ℕ → Ω → ℝ≥0∞) (ℓ : Ω → ℝ≥0 → ℝ≥0),
      IsBW1RelVersion P (bwRec κ b jumps (bwSpec gw2 θ t rest) E) (bwEvent κ b jumps (bwSpec gw2 θ t rest) E r)
        (bwChart κ b jumps (bwSpec gw2 θ t rest) E) W' (bwContact κ b jumps (bwSpec gw2 θ t rest) W' E) R V ℓ →
      IsBW1VersionHulls P (bwRec κ b jumps (bwSpec gw2 θ t rest) E) (bwEvent κ b jumps (bwSpec gw2 θ t rest) E r)
        W' (bwContact κ b jumps (bwSpec gw2 θ t rest) W' E) R V →
    ∀ (m : ℕ) (w : WordType) (Wd : ℝ≥0 → Ω → ℝ) (GT : Set Ω), (∀ s, Measurable (Wd s)) →
      (∀ ω, Continuous (Wd · ω)) → (∀ ω, Wd 0 ω = 0) → (∀ᵐ ω ∂P, ∀ s, Wd s ω = W' s ω) → MeasurableSet GT →
      (∀ᵐ ω ∂P, bwRec κ b jumps (bwSpec gw2 θ t rest) E ω ∈ TS → ω ∈ GT) →
      (∀ ω ∈ GT, bwRec κ b jumps (bwSpec gw2 θ t rest) E ω ∈ TS ∧
        BGood (bwRec κ b jumps (bwSpec gw2 θ t rest) E) Wd ω ∧ (∀ s, W' s ω = Wd s ω) ∧
        bwContact κ b jumps (bwSpec gw2 θ t rest) W' E ω = bTc (bwRec κ b jumps (bwSpec gw2 θ t rest) E) Wd ω) →
    ∀ (b' : ℝ → ℝ) (J' : Finset ℝ) (h' : Ω → DistOn upperHalfPlaneOpens), IsPiecewiseConstantBoundaryData b' J' →
      (∀ ω, IsChartTransport infinitySourceChart (-1) (-(Real.pi * chiC κ)) (chiC (16 / κ)) (h ω) (h' ω)) →
      IsFlowLineDriver (16 / κ) b' J' 0 P h' W' ζ' →
    ∀ u₀ : ℂ → ℝ, IsBoundedHarmonicExtension (Supp8.Q3Chain.cfData (16 / κ) b' J')
      (forceJumpSet (flowLineXL b' J' 0) (flowLineXR b' J' 0)) u₀ →
    LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (WholeField.centredField h' u₀) P →
    ∀ B : ℝ≥0 → Ω → Set ℂ, (∀ s, Measurable[mΩ, hittingSigma] (B s)) →
      (∀ s ω, B s ω ⊆ H ∧ IsOpen (H \ B s ω)) →
      (∀ s, ∀ᵐ ω ∂P, B s ω = relClosureH (bRetOfRec TS (bwRec κ b jumps (bwSpec gw2 θ t rest) E ω) ∪
        fwdHull (fun r : ℝ => Wd r.toNNReal ω) s)) →
      (∀ s, IsLocalSet (B s) (WholeField.centredField h' u₀) P) →
      HasBUnionMean κ θ c₀ P h' (bwRelField κ b jumps (bwSpec gw2 θ t rest) h E)
        (bwRec κ b jumps (bwSpec gw2 θ t rest) E) Wd GT TS (R m) (V m) w u₀ B

/-- **BW1's relative safe law (S)/(L) for versions with hull identities, from Theorems 1.2–1.3 and the union mean
identification (L3).** -/
theorem bw1RelSafeLawHStatement_of_mean (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (hM : BW1LineMeanStatement.{u}) : BW1RelSafeLawHStatement.{u} := by
  intro κ b jumps Ω mΩ _ P _ h W' ζ' θ t gw2 rest E hset r TS hTS hFTS c₀ hc₀J hc₀ R V ℓ hver hhull m w
  have hset' := hset
  obtain ⟨hκ, hκ4, hb, hh, hcf, hζ', hθ, hS⟩ := hset'
  set rec := bwRec κ b jumps (bwSpec gw2 θ t rest) E with hrecdef
  have hEm' : ∀ j, Measurable (StagedReg.regHist (bwSpec gw2 θ t rest) E j) := StagedReg.measurable_regHist hS.1
  have hreg' : ∀ j ω, IsRegularDriver (StagedReg.regHist (bwSpec gw2 θ t rest) E j ω) := fun j ω =>
    StagedReg.isRegularDriver_regHist j ω
  have hrec : Measurable rec := measurable_pastMap_one_last hb hEm' hreg'
  -- the physical driver version and the good event
  obtain ⟨Wd, GT, hWdm, hWdc, hWd0, hWdW, hGTm, hGTae, hGT⟩ := exists_bw1_safe_data h13 hset hTS hFTS
  have hGTgood : ∀ ω ∈ GT, BGood rec Wd ω := fun ω hω => (hGT ω hω).2.1
  have hGTp : ∀ s, MeasurableSet[physFilt hrec hWdm P s] GT :=
    measurableSet_goodSet_physFilt' hrec hWdm hTS hGTm (fun ω hω => (hGT ω hω).1) hGTae
  have hGF : ∀ᵐ ω ∂P, ω ∈ GT → ω ∈ bwEvent κ b jumps (bwSpec gw2 θ t rest) E r := by
    filter_upwards [hFTS] with ω hω hG
    exact hω.2 (hGT ω hG).1
  have hv : IsBVer P rec Wd GT (R m) (V m) :=
    isBVer_of_version hver hhull hGF (fun ω hω => ⟨(hGT ω hω).2.2.1, (hGT ω hω).2.2.2⟩) m
  have hFGT : ∀ᵐ ω ∂P, ω ∈ bLive κ θ c₀ rec TS w → ω ∈ GT := by
    filter_upwards [hGTae] with ω hω hL
    exact hω hL.1
  -- the counterflow frame and the chart identity
  have hcf' := hcf
  obtain ⟨b', J', h'', hb', hT, hcfl⟩ := hcf'
  have hk : 0 < 16 / κ := by positivity
  have hh''eq : ∀ ω, h'' ω = GW4Traverse.cfField κ (h ω) := fun ω =>
    (hT ω).unique Chart.isConformal_infinitySourceChart (GW4Traverse.isChartTransport_cfField κ (h ω))
  have hX : ∀ ω, bwRelField κ b jumps (bwSpec gw2 θ t rest) h E ω =
      Chart.chartTransport (Supp8.RelSafeS.isConformal_relChart (rec ω)) 1 (2 * Real.pi * chiC (16 / κ))
        (chiC (16 / κ)) (h'' ω) := fun ω => by
    rw [hh''eq]
    exact bwRelField_eq_chartTransport hκ _ rfl h E ω
  have hHcm : Measurable (bwRelField κ b jumps (bwSpec gw2 θ t rest) h E) :=
    (GW4Traverse.measurable_cfField κ).comp (measurable_bwField hb hh.1 hEm' hreg')
  have hG' : IsGFFWithBoundaryData P h'' b' J' :=
    Theorem14.GW2aPiece.isGFFWithBoundaryData_of_isFlowLineDriver hk hb' hcfl
  -- (L0) the centrings
  obtain ⟨u₀, hu₀, -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension c₀.isPiecewiseConstantBoundaryData
  have hu₀b : IsBoundedHarmonicExtension b jumps u₀ := by
    have h1 : IsBoundedHarmonicExtension c₀.fn jumps u₀ := by rw [← hc₀J]; exact hu₀
    exact (Restart.isBoundedHarmonicExtension_congr (fun y hy => hc₀ y hy) u₀).1 h1
  obtain ⟨u₀', hu₀'⟩ := Sec7.StripSysField.exists_isBoundedHarmonicExtension_forceBoundaryData (16 / κ)
    (flowLineRhoL (16 / κ) b' J' 0 0) (flowLineRhoR (16 / κ) b' J' 0 0) (flowLineXL b' J' 0) (flowLineXR b' J' 0)
  have hcen := Supp8.Q3Chain.centredField_eq_reflect hκ hb hh hb' hG' hT hu₀b hu₀'
  -- the counterflow coupling
  have hcfl' := hcfl
  obtain ⟨hcfF, 𝓕c, VLc, VRc, Bc, htrc, hCc⟩ := hcfl'
  have e3 : hcfF = h'' := funext fun ω => Theorem14.GW2Cone.eq_of_isTranslateAddConst_zero (zero_mul _) (htrc ω)
  rw [e3] at hCc
  have hXc := hCc.2.2.2.1
  have hh0 : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (WholeField.centredField h'' u₀') P :=
    WholeField.isZeroBoundaryGFF_centredField hCc hu₀'
  have hh₀m : Measurable (WholeField.centredField h'' u₀') := hh0.measurable
  -- determination of the counterflow (Theorems 1.2–1.3)
  have hdetc := Exist.Param12.hasFieldDeterminedHistories h12 h13 hk (Theorem15.isOrderedForceWord_flowLine b' J' 0)
    P 𝓕c W' VLc VRc Bc ζ' h'' hCc
  have hcomap' : MeasurableSpace.comap h'' inferInstance ≤
      aeSigma (MeasurableSpace.comap (WholeField.centredField h'' u₀') inferInstance) P :=
    KernelTower.comap_le_aeSigma_comap (WholeField.measurable_add_dist _)
      (Eventually.of_forall fun ω => (sub_add_cancel (h'' ω)
        (SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀')).symm)
  have h𝓕c : ∀ s, drivingFiltration P hXc s ≤
      aeSigma (MeasurableSpace.comap (WholeField.centredField h'' u₀') inferInstance) P := fun s =>
    (Supp8.Q3Chain.drivingFiltration_le_aeSigma hdetc hXc s).trans (Supp8.Q3Chain.aeSigma_le_of_le hcomap')
  -- (L1) the retained set and the union
  obtain ⟨hrecd, hlocR⟩ := exists_bw1_retained_marks h12 h13 hset hc₀ hu₀ hh0 (fun ω => hcen ω) hTS hFTS
  set h₀ := WholeField.centredField h'' u₀' with hh₀def
  set ℋ : ℝ≥0 → MeasurableSpace Ω := fun s =>
    (MeasurableSpace.comap rec inferInstance ⊔ Ito.nullSets P) ⊔ drivingFiltration P hXc s with hℋdef
  set B : ℝ≥0 → Ω → Set ℂ := fun s ω =>
    relClosureH (bRetOfRec TS (rec ω) ∪ Sec5.GlueCond.hullAt s (LawUnique.killedHistory W' VLc VRc ζ' ω))
    with hBdef
  have hloc : ∀ s, WholeField.IsHistoryAvoidanceLocal (ℋ s) (B s) h₀ P := fun s => by
    have hU := Theorem14.WalkLaw.isHistoryAvoidanceLocal_union_of_det hh₀m
      (ℋ₁ := MeasurableSpace.comap rec inferInstance ⊔ Ito.nullSets P) (ℋ₂ := drivingFiltration P hXc s)
      (A₁ := fun ω => bRetOfRec TS (rec ω))
      (A₂ := fun ω => Sec5.GlueCond.hullAt s (LawUnique.killedHistory W' VLc VRc ζ' ω))
      (fun U hUH => le_sup_left (a := MeasurableSpace.comap rec inferInstance) _
        ⟨_, measurable_bRetOfRec hTS (measurableSet_avoid U.isOpen hUH), rfl⟩)
      (fun U hUH => Supp8.RelSafeS.measurableSet_avoid_cfHull hXc s U.isOpen hUH)
      (sup_le hrecd nullSets_le_aeSigma) (h𝓕c s) hlocR
      (Supp8.RelSafeS.isHistoryAvoidanceLocal_cfHull hCc hk hζ' hu₀' s)
    exact Supp8.GB6LineL.isHistoryAvoidanceLocal_relClosureH hU
  have hBm : ∀ s, Measurable[mΩ, hittingSigma] (B s) := fun s =>
    Supp8.GB6LineL.measurable_relClosureH_union ((measurable_bRetOfRec hTS).comp hrec)
      (Supp8.RelSafeS.measurable_cfHull hXc s)
  have hBc : ∀ s ω, B s ω ⊆ H ∧ IsOpen (H \ B s ω) := fun s ω =>
    ⟨Supp8.GB6LineL.relClosureH_subset_H _, Supp8.GB6LineL.isOpen_H_diff_relClosureH _⟩
  have hBeq : ∀ s, ∀ᵐ ω ∂P, B s ω =
      relClosureH (bRetOfRec TS (rec ω) ∪ fwdHull (fun r : ℝ => Wd r.toNNReal ω) s) := fun s => by
    filter_upwards [Supp8.RelSafeS.ae_cfHull_eq hCc hζ' s, hWdW] with ω hK hW
    rw [hBdef]
    simp only [hK, hW]
  have hBloc : ∀ s, IsLocalSet (B s) h₀ P := fun s =>
    ((isLocalSet_tfae hh0 (hBm s) (Eventually.of_forall (hBc s))).out 4 1).2 (hloc s).isAvoidanceLocal
  -- the marks contain the physical filtration
  have h𝓖ℋ : ∀ s, physFilt hrec hWdm P s ≤ ℋ s := by
    intro s
    show (MeasurableSpace.comap rec inferInstance ⊔
      ⨆ q, ⨆ (_ : q ≤ s), MeasurableSpace.comap (Wd q) inferInstance) ⊔ Ito.nullSets P ≤ ℋ s
    refine sup_le (sup_le (le_sup_left.trans le_sup_left) (iSup₂_le fun q hq => ?_))
      (le_sup_right.trans le_sup_left)
    exact (Supp8.RelSafeS.measurable_version_drivingFiltration hXc hζ' hWdm hWdW hq).comap_le.trans le_sup_right
  have hℋm : ∀ s, ℋ s ≤ mΩ := fun s =>
    sup_le (sup_le hrec.comap_le (Ito.nullSets_le P)) ((drivingFiltration P hXc).le s)
  -- (L2) the shape of the union on the live event
  have hBK : ∀ s : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ bLive κ θ c₀ rec TS w → min (bClock rec Wd GT s ω) (V m ω) < V m ω →
      H \ B s ω = (Supp8.RelSafeS.relChart (rec ω)).2.1 ''
        (H \ fwdHull (fun r : ℝ => R m r.toNNReal ω) (min (bClock rec Wd GT s ω) (V m ω)).toNNReal) := by
    intro s
    filter_upwards [ae_compl_union_eq_relChart_bw hGTgood hv s, hFGT, Supp8.RelSafeS.ae_cfHull_eq hCc hζ' s,
      hWdW] with ω hsh hGTω hK hW hlive hlt
    have hωGT : ω ∈ GT := hGTω hlive
    have hrecTS : rec ω ∈ TS := (hGT ω hωGT).1
    have hWpath : (fun r : ℝ => W' r.toNNReal ω) = fun r : ℝ => Wd r.toNNReal ω := funext fun r => (hW _).symm
    have hXo : IsOpen (H \ (Supp8.Q3Rel.invHull (rdrv (rec ω)) (recS (rec ω)) ∪
        fwdHull (fun r : ℝ => Wd r.toNNReal ω) s)) := by
      have e : H \ (Supp8.Q3Rel.invHull (rdrv (rec ω)) (recS (rec ω)) ∪ fwdHull (fun r : ℝ => Wd r.toNNReal ω) s) =
          (H \ WangWu.negInv '' fwdHull (rdrv (rec ω)) (recS (rec ω))) ∩
            (H \ fwdHull (fun r : ℝ => Wd r.toNNReal ω) s) := by
        ext z
        simp only [Supp8.Q3Rel.invHull, WangWu.negInv, Set.mem_sdiff, mem_union, mem_inter_iff, not_or]
        tauto
      rw [e, WangWu.H_diff_image_negInv]
      exact (WangWu.isOpen_image_negInv (QuantumZipper.FwdHolo.isOpen_compl_fwdHull (continuous_rdrv _)
        (recS (rec ω)).coe_nonneg) sdiff_subset).inter
        (QuantumZipper.FwdHolo.isOpen_compl_fwdHull ((hWdc ω).comp continuous_real_toNNReal) s.coe_nonneg)
    have hB : B s ω = relClosureH (Supp8.Q3Rel.invHull (rdrv (rec ω)) (recS (rec ω)) ∪
        fwdHull (fun r : ℝ => Wd r.toNNReal ω) s) := by
      simp only [hBdef, bRetOfRec, hrecTS, ↓reduceIte, hK, hWpath]
    rw [hB, Supp8.GB6LineL.H_diff_relClosureH_of_isOpen hXo]
    exact hsh hωGT hlt
  -- (L4) the safe events are physical
  obtain ⟨hSψ, hSb⟩ := bw1SafeMeas hGTgood hrec hWdm hGTp hv
  -- (L3) the union mean identification (the named input) and the line kernels from the marked locality
  have hmeanM := hM κ b jumps P h W' ζ' θ t gw2 rest E hset r TS hTS hFTS c₀ hc₀J hc₀ R V ℓ hver hhull m w Wd GT
    hWdm hWdc hWd0 hWdW hGTm hGTae hGT b' J' h'' hb' hT hcfl u₀' hu₀' hh0 B hBm hBc hBeq hBloc
  have hgex : ∀ s, ∃ g, IsLocalSetMean (B s) h₀ P g := fun s =>
    IsLocalSet.exists_isLocalSetMean hh0 (hBm s) (hBloc s)
  choose g hgm using hgex
  have hu₀c : ContinuousOn u₀' (upperHalfPlaneOpens : Set ℂ) := fun z hz =>
    (hu₀'.1 z hz).1.continuousAt.continuousWithinAt
  have hker : ∀ (s : ℝ≥0) (φ : TestOn upperHalfPlaneOpens), ∀ᵐ ω ∂P, ω ∈ bLive κ θ c₀ rec TS w →
      min (bClock rec Wd GT s ω) (V m ω) < V m ω →
      tsupport φ ⊆ (Supp8.RelSafeS.relChart (rec ω)).2.1 ''
        (H \ fwdHull (fun r : ℝ => R m r.toNNReal ω) (min (bClock rec Wd GT s ω) (V m ω)).toNNReal) →
      P[fun ω => Complex.exp (Complex.I * (h'' ω φ : ℂ)) | germSigma (B s) h₀ ⊔ ℋ s] ω =
        Complex.exp (Complex.I * ((g s ω + SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀')
            φ : ℂ) -
          (((1 / 2 : ℝ) * zeroGFFTestCov ((Supp8.RelSafeS.relChart (rec ω)).2.1 '' (H \ fwdHull
            (fun r : ℝ => R m r.toNNReal ω) (min (bClock rec Wd GT s ω) (V m ω)).toNNReal)) φ φ : ℝ) : ℂ)) := by
    intro s φ
    have h1 := Supp8.RelSafeS.ae_condExp_cexp_marked hh0 (hBm s) (hBc s) (hℋm s) (hloc s) (hgm s) φ
    have hsplit : (fun ω => Complex.exp (Complex.I * (h'' ω φ : ℂ))) =
        fun ω => Complex.exp (Complex.I * ((∫ z, u₀' z * φ z : ℝ) : ℂ)) *
          Complex.exp (Complex.I * (h₀ ω φ : ℂ)) := by
      funext ω
      rw [← Complex.exp_add, hh₀def, WholeField.centredField_apply h'' hu₀'.1 ω φ]
      congr 1
      push_cast
      ring
    have hcs : (fun ω => Complex.exp (Complex.I * ((∫ z, u₀' z * φ z : ℝ) : ℂ)) *
          Complex.exp (Complex.I * (h₀ ω φ : ℂ))) =
        Complex.exp (Complex.I * ((∫ z, u₀' z * φ z : ℝ) : ℂ)) • fun ω => Complex.exp (Complex.I * (h₀ ω φ : ℂ)) :=
      rfl
    have h2 : P[fun ω => Complex.exp (Complex.I * (h'' ω φ : ℂ)) | germSigma (B s) h₀ ⊔ ℋ s] =ᵐ[P]
        Complex.exp (Complex.I * ((∫ z, u₀' z * φ z : ℝ) : ℂ)) •
          P[fun ω => Complex.exp (Complex.I * (h₀ ω φ : ℂ)) | germSigma (B s) h₀ ⊔ ℋ s] := by
      rw [hsplit, hcs]
      exact condExp_smul _ _ _
    filter_upwards [h2, h1, hBK s] with ω hω2 hω hBKω hωF hlt _
    rw [hω2, Pi.smul_apply, hω, ← hBKω hωF hlt, smul_eq_mul, add_apply,
      SupercriticalConformalCovariance.GM24.smoothDist_apply hu₀c φ, Complex.ofReal_exp]
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    have e : (∫ x, φ x * u₀' x) = ∫ z, u₀' z * φ z := by
      congr 1
      funext z
      ring
    rw [e]
    push_cast
    ring
  exact hasSafe_bw_of_lines hrec hCc.2.1 hHcm hX hTS hWdm hGTgood hGTp hv w hFGT
    (fun s => germSigma (B s) h₀ ⊔ ℋ s) (fun s => (h𝓖ℋ s).trans le_sup_right)
    (fun s => sup_le (germSigma_le (hBm s) hh₀m) (hℋm s))
    (fun s ω => g s ω + SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀') hker
    (fun s ψ => hmeanM s (g s) (hgm s) ψ) hu₀'.1 hh0 ℋ h𝓖ℋ hℋm B hBm hBc hloc hBK hSψ hSb

/-- **Proposition BW1 from Theorems 1.2–1.3, the canonical driver codes and BW1's union mean identification (L3)**
(`bw1Statement_of_lawH` with `bw1RelSafeLawHStatement_of_mean`). -/
theorem bw1Statement_of_mean (h12p : Exist.Staged.Theorem12ParamStatement.{u}) (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (hT13₀ : Exist.Theorem13Statement.{0})
    (hcode : Restart.CanonicalDriverCodeStatement) (hM : BW1LineMeanStatement.{u}) : BW1.BW1Statement.{u} :=
  bw1Statement_of_lawH h12p h13 hT13₀ hcode (bw1RelSafeLawHStatement_of_mean h12 h13 hM)

end InteractingSLE.Theorem14.BW1Safe
