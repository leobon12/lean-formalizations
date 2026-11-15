/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2TpSets
import InteractingSLE.Spec.Supplement.GW2SdeGauss
import InteractingSLE.Spec.Supplement.GW4SafeRKernel
import InteractingSLE.Spec.Supplement.GW2RzLaw
import InteractingSLE.Spec.Restart.R1Glue
import InteractingSLE.Spec.Exist.StagedLawKernel

/-!
# `condGFF` of a root-`x` stage instance: the stage-start conditional law from the mean at stage time `0`

Packet PROVE-GW2-RELDET (round 28; the item moved from PROVE-T14-SB2DRV). The field `condGFF` of ROOTX's
`GW2Rz.OpenLinesX` asks for a σ-algebra `𝒢` reading the stage record, a height bound of the stage words on the record
event, and: almost surely on the record event, under `condExpKernel P 𝒢`, the stage field `Hr` is a GFF with the data
of the stage word. Review P1d: it is the stage mean at stage time `0` plus the marked locality of the union `B 0`.

* `dom_stgChart`: the domain of a stage chart is the image of the complement of the relative hull at the stage start;
* `integral_stageMean_zero`: at stage time `0` the right side of `GW2Rz.stageMeanAtX` is the stage word's mean (the
  hull is empty and the coupling mean is the bounded harmonic extension of the typed data of the word);
* **`condGFF_of_mean0`** (any instance `I` at any root `x₀`): with `𝒢 = germ(B 0) ⊔ ℋ 0`, the marked Gaussian kernel
  of `B 0` (`GW4Fix.ae_condExp_cexp_boundary_marked`), the transport into the stage chart on the record event
  (`Restart.ae_condExp_cexp_chartTransport_random_on`, the chart's domain is `ℍ ∖ B 0` there), the stage mean at stage
  time `0` (the ONLY input of STAGEMEAN: the field `OpenLinesX.mean` at `t = 0`), and the regular conditional law
  (`Exist.StagedLaw.ae_isGFFWithBoundaryData_condExpKernel`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull fwdMapInv zeroGFFTestCov)
open LQGMetric (DistOn TestOn)
open SupercriticalConformalCovariance.GM24 (smoothDist)

universe u

namespace InteractingSLE.Theorem14.GW2Rd

/-! ### The domain of a stage chart -/

/-- **The domain of a stage chart** is the chart's inverse image of the complement of the relative hull at the stage
start. -/
theorem dom_stgChart {c : Chart} (hc : c.IsConformal) {R : ℝ≥0 → ℝ} (hR : Continuous R) (hR0 : R 0 = 0)
    (a : ℝ≥0) : ((stgChart c R a).dom : Set ℂ) = c.2.1 '' (H \ fwdHull (Ito.rpath R) (a : ℝ)) := by
  rw [(isConformal_stgChart hc hR hR0 a).coe_dom]
  have h := stgChart_inv_image c hR hR0 a 0
  have hc0 : Continuous (Ito.rpath (stgDrv R a)) :=
    (continuous_stgDrv hR a).comp continuous_real_toNNReal
  rw [NNReal.coe_zero, QuantumZipper.RS.fwdHull_zero_eq_empty hc0, sdiff_empty, add_zero] at h
  exact h

/-! ### The stage mean at stage time `0` -/

section Zero

open Restart Exist.StagedLaw Supp8.GB6 Supp8.GB6.RelDrv Supp8.Q3Stop Restart.DomainMarkov Restart.DomainMarkov.K2
  Sec7.PocketTraversal GW2Sde GW2Rz GW2TipSystem GW2TipSystem.RootC24

variable {Ω : Type u} [MeasurableSpace Ω] {c : SourceData Ω} {r : ScaledRootIdx c.Θ c.Q}
  {l : List (EntryIdx c.Θ c.Q)}

/-- **At stage time `0` the stage mean is the word's mean**: the right side of `stageMeanAtX` at clock `0`. -/
theorem integral_stageMean_zero (I : StageInst Ω) (x₀ : ℝ) (ω : Ω) {w : WordType}
    (hw : wordType c.κ (I.β (I.srecX c r l x₀ ω)) = w) (hs : (I.β (I.srecX c r l x₀ ω)).IsSorted)
    (ψ : TestOn upperHalfPlaneOpens) :
    ∫ z, couplingMean c.κ (fun s : ℝ => I.drvX c x₀ s.toNNReal ω) (0 : ℝ≥0)
        (bheProc c.κ (typedRhoL w) (typedRhoR w) (I.drvX c x₀)
          (fun i t ω => geomLW canonDrv (fun y => typedXL c.κ w (I.β y.1)) i t
            (I.srecX c r l x₀ ω, relVar I.Hr (I.drvX c x₀) (I.capX c x₀) ω))
          (fun j t ω => geomRW canonDrv (fun y => typedXR c.κ w (I.β y.1)) j t
            (I.srecX c r l x₀ ω, relVar I.Hr (I.drvX c x₀) (I.capX c x₀) ω)) ω (0 : ℝ≥0)) z * ψ z =
      ∫ z, (I.β (I.srecX c r l x₀ ω)).mean z * ψ z := by
  set y : CanonSpace := (I.srecX c r l x₀ ω, relVar I.Hr (I.drvX c x₀) (I.capX c x₀) ω) with hy
  have hW0 : ∀ y : CanonSpace, canonDrv 0 y = 0 := canonDrv_zero
  have hWc : ∀ y : CanonSpace, Continuous fun t => canonDrv t y := continuous_canonDrv
  have hd0 : I.drvX c x₀ 0 ω = 0 := stgDrv_zero _ _
  have hw0 : (fun s : ℝ => I.drvX c x₀ s.toNNReal ω) 0 = 0 := by
    simp only [Real.toNNReal_zero]
    exact hd0
  have hft := isFlowType_typed (κ := c.κ) hw
  obtain ⟨hsL, hsR⟩ := RetAux79.isFlowType_signs hft
  have hL0 : ∀ i, geomLW canonDrv (fun y => typedXL c.κ w (I.β y.1)) i 0 y = typedXL c.κ w (I.β y.1) i :=
    fun i => geomLW_zero hWc hW0 (hsL i)
  have hR0 : ∀ j, geomRW canonDrv (fun y => typedXR c.κ w (I.β y.1)) j 0 y = typedXR c.κ w (I.β y.1) j :=
    fun j => geomRW_zero hWc hW0 (hsR j)
  have hu := isBoundedHarmonicExtension_bheProc (κ := c.κ) (ρL := typedRhoL w) (ρR := typedRhoR w)
    (W := I.drvX c x₀)
    (VL := fun i t ω => geomLW canonDrv (fun y => typedXL c.κ w (I.β y.1)) i t
      (I.srecX c r l x₀ ω, relVar I.Hr (I.drvX c x₀) (I.capX c x₀) ω))
    (VR := fun j t ω => geomRW canonDrv (fun y => typedXR c.κ w (I.β y.1)) j t
      (I.srecX c r l x₀ ω, relVar I.Hr (I.drvX c x₀) (I.capX c x₀) ω)) ω 0
  simp only [← hy, hL0, hR0, hd0, sub_zero] at hu
  have hS : ({0} ∪ ((I.β y.1).jumps : Set ℝ)).Finite := (finite_singleton 0).union (I.β y.1).jumps.finite_toSet
  have hmean := RetAux79.eqOn_mean_add_of_forceBoundaryData hu hs 0 hS fun y' hy' => by
    have h0 : y' ≠ 0 := fun h => hy' (Or.inl h)
    have hJ : y' ∉ (I.β y.1).jumps := fun h => hy' (Or.inr h)
    rw [RetAux79.forceBoundaryData_zero_of_isFlowType hft,
      Sec4.forceBoundaryData_flowLine c.hκ (I.β y.1).isPiecewiseConstantBoundaryData h0 hJ, add_zero]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  by_cases hz : ψ z = 0
  · simp only [hz, mul_zero]
  · have hzH : z ∈ H := ψ.tsupport_subset (subset_tsupport _ hz)
    have hz0 : z ≠ 0 := fun h => by
      rw [h] at hzH
      exact lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from hzH)
    change couplingMean c.κ (fun s : ℝ => I.drvX c x₀ s.toNNReal ω) ((0 : ℝ≥0) : ℝ) _ z * ψ z = _
    rw [NNReal.coe_zero, Coupling.MartMeans2.couplingMean_zero (w := fun s : ℝ => I.drvX c x₀ s.toNNReal ω) c.κ hw0
      _ hz0, hmean z hzH, add_zero]

end Zero

/-! ### The conditional GFF at the stage start -/

section Cond

open LocalSets WholeField GW4Fix GW2Sde GW2Rz Supp8.Q3Stop Exist.StagedLaw GW2TipSystem GW2TipSystem.RootC24

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {c : SourceData Ω}
  {r : ScaledRootIdx c.Θ c.Q} {l : List (EntryIdx c.Θ c.Q)}

/-- **`condGFF` of a root-`x` stage instance from the stage mean at stage time `0`** (review P1d): `germ(B 0) ⊔ ℋ 0`
reads the stage record; on the record event the stage field is, under the regular conditional law, a GFF with the
data of the stage word. Inputs besides STAGEMEAN's mean at `t = 0` (`hmean`): the set-level lines fields at `t = 0`,
the stage records read by `ℋ 0`, the word's properties, and on the record event the shape of the stage chart
(`hdom`) and a positive cap (`hcap`). -/
theorem condGFF_of_mean0 (I : StageInst Ω) (x₀ : ℝ)
    (hu₀ : InnerProductSpace.HarmonicOnNhd I.u₀ H)
    (hzb : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (centredField c.h I.u₀) c.P)
    (hamb : I.ℋ 0 ≤ mΩ) (hBm : Measurable[mΩ, hittingSigma] (I.B 0))
    (hBc : ∀ ω, I.B 0 ω ⊆ H ∧ IsOpen (H \ I.B 0 ω))
    (hloc : IsHistoryAvoidanceLocal (I.ℋ 0) (I.B 0) (centredField c.h I.u₀) c.P)
    (hcf : Measurable[I.ℋ 0] (cfRec c.s c.W c.ζ))
    (hpre : Measurable[I.ℋ 0] (stgPreRecX x₀ c.s c.W c.ζ I.W I.GT I.V I.T I.R))
    (hrec : Measurable[I.ℋ 0] (I.srecX c r l x₀))
    (hRc : ∀ ω, Continuous fun t => I.R t ω) (hR0 : ∀ ω, I.R 0 ω = 0)
    (hE : MeasurableSet I.E) (hcount : (range fun y => wordType c.κ (I.β y)).Countable)
    (hsort : ∀ y ∈ I.E, (I.β y).IsSorted) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ y ∈ I.E, ∀ x ∉ (I.β y).jumps, |(I.β y).fn x| ≤ M)
    (hHrm : Measurable I.Hr)
    (hHr : ∀ ω (hc : (I.chartX c x₀ ω).IsConformal), I.Hr ω = Chart.chartTransport hc 1 I.σa I.kc (c.h ω))
    (hdom : ∀ᵐ ω ∂c.P, I.srecX c r l x₀ ω ∈ I.E → ((I.chartX c x₀ ω).dom : Set ℂ) = H \ I.B 0 ω)
    (hcap : ∀ᵐ ω ∂c.P, I.srecX c r l x₀ ω ∈ I.E → I.clockX c x₀ 0 ω < I.capX c x₀ ω)
    (hmean : ∀ (w : WordType) (g : Ω → DistOn upperHalfPlaneOpens),
      IsLocalSetMean (I.B 0) (centredField c.h I.u₀) c.P g → ∀ ψ : TestOn upperHalfPlaneOpens,
      ∀ᵐ ω ∂c.P, stageMeanAtX I c r l x₀ w 0 ψ ω (g ω)) :
    ∃ (𝒢 : {m : MeasurableSpace Ω // m ≤ mΩ}) (M : ℝ), Measurable[𝒢.1] (I.srecX c r l x₀) ∧ 0 ≤ M ∧
      (∀ y ∈ I.E, ∀ x ∉ (I.β y).jumps, |(I.β y).fn x| ≤ M) ∧
      ∀ᵐ ω₀ ∂c.P, I.srecX c r l x₀ ω₀ ∈ I.E →
        IsGFFWithBoundaryData (condExpKernel c.P 𝒢.1 ω₀) I.Hr (I.β (I.srecX c r l x₀ ω₀)).fn
          (I.β (I.srecX c r l x₀ ω₀)).jumps := by
  have hhm : Measurable c.h := c.hh.1
  have hh0m : Measurable (centredField c.h I.u₀) := measurable_centredField hhm I.u₀
  -- the σ-algebra
  obtain ⟨𝒢s, h𝒢def⟩ : ∃ 𝒢s : {m : MeasurableSpace Ω // m ≤ mΩ},
      𝒢s.1 = germSigma (I.B 0) (centredField c.h I.u₀) ⊔ I.ℋ 0 :=
    ⟨⟨_, sup_le (germSigma_le hBm hh0m) hamb⟩, rfl⟩
  have h𝒢 : 𝒢s.1 ≤ mΩ := 𝒢s.2
  have hℋ𝒢 : I.ℋ 0 ≤ 𝒢s.1 := h𝒢def ▸ le_sup_right
  -- the stage chart, read by `ℋ 0`
  have hK : WalkInf.IsMeasChart (I.ℋ 0) (I.chartX c x₀) := isMeasChart_stgChartX hcf hRc hR0 hpre
  obtain ⟨hc, hliftc, -, hdomm, hfwd, -, hliftm⟩ := hK
  have hdom𝒢 : ∀ z, MeasurableSet[𝒢s.1] {ω | z ∈ (I.chartX c x₀ ω).dom} := fun z => hℋ𝒢 _ (hdomm z)
  have hfwd𝒢 : ∀ z, Measurable[𝒢s.1] ({ω | z ∈ (I.chartX c x₀ ω).dom}.indicator fun ω => (I.chartX c x₀ ω).1 z) :=
    fun z => (hfwd z).mono hℋ𝒢 le_rfl
  have hliftm𝒢 : ∀ z, Measurable[𝒢s.1]
      ({ω | z ∈ (I.chartX c x₀ ω).dom}.indicator fun ω => (I.chartX c x₀ ω).2.2 z) :=
    fun z => (hliftm z).mono hℋ𝒢 le_rfl
  -- the local-set mean of the union at the stage start
  have hl : IsLocalSet (I.B 0) (centredField c.h I.u₀) c.P :=
    ((isLocalSet_tfae hzb hBm (Eventually.of_forall hBc)).out 4 1).2 hloc.isAvoidanceLocal
  obtain ⟨g, hg⟩ := IsLocalSet.exists_isLocalSetMean hzb hBm hl
  set Mf : Ω → DistOn upperHalfPlaneOpens := fun ω => g ω + smoothDist upperHalfPlaneOpens I.u₀ with hMf
  -- the record event
  set Mset : Set Ω := I.srecX c r l x₀ ⁻¹' I.E with hMset
  have hM𝒢 : MeasurableSet[𝒢s.1] Mset := (hrec.mono hℋ𝒢 le_rfl) hE
  -- the marked kernel, read on the chart's domain
  have hcond : ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂c.P, ω ∈ Mset → tsupport φ ⊆ (I.chartX c x₀ ω).dom →
      c.P[fun ω => Complex.exp (Complex.I * (c.h ω φ : ℂ)) | 𝒢s.1] ω =
        Complex.exp (Complex.I * (Mf ω φ : ℂ) -
          (((1 / 2 : ℝ) * zeroGFFTestCov ((I.chartX c x₀ ω).dom : Set ℂ) φ φ : ℝ) : ℂ)) := by
    intro φ
    filter_upwards [ae_condExp_cexp_boundary_marked hu₀ hzb hBm hBc hamb hloc hg φ, hdom] with ω h1 h2 hω _
    rw [h2 hω, h𝒢def]
    exact h1
  -- the mean at stage time `0`, at every word type of the record
  have hmeanAll : ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂c.P,
      ∀ w ∈ range (fun y => wordType c.κ (I.β y)), stageMeanAtX I c r l x₀ w 0 φ ω (g ω) := fun φ =>
    (ae_ball_iff hcount).2 fun w _ => hmean w g hg φ
  have hmean0 : ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂c.P, ω ∈ Mset →
      Chart.chartTransport (hc ω) 1 I.σa I.kc (Mf ω) φ = ∫ z, (I.β (I.srecX c r l x₀ ω)).mean z * φ z := by
    intro φ
    filter_upwards [hmeanAll φ, hcap] with ω h1 h2 hω
    have h0 : I.clockX c x₀ 0 ω = 0 := by
      change min (physClockX x₀ c.s c.W c.ζ I.W I.GT (I.T + 0) ω) (I.V ω) -
        stgStartMX x₀ c.s c.W c.ζ I.W I.GT I.V I.T ω = 0
      rw [add_zero]
      exact tsub_self _
    have hdc : Continuous fun s : ℝ => I.drvX c x₀ s.toNNReal ω :=
      (continuous_stgDrv (hRc ω) _).comp continuous_real_toNNReal
    have h := h1 (wordType c.κ (I.β (I.srecX c r l x₀ ω))) ⟨_, rfl⟩ ⟨hω, rfl⟩ (h2 hω) (by
      rw [h0, ENNReal.toNNReal_zero, NNReal.coe_zero, QuantumZipper.RS.fwdHull_zero_eq_empty hdc]
      exact disjoint_empty _) (hc ω)
    rw [h, h0, ENNReal.toNNReal_zero]
    exact integral_stageMean_zero I x₀ ω rfl (hsort _ hω) φ
  -- the chart field given `𝒢`
  have hG : ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂c.P, ω ∈ Mset →
      c.P[fun ω' => Complex.exp (Complex.I * (I.Hr ω' φ : ℂ)) | 𝒢s.1] ω =
        Restart.gaussCF (I.β (I.srecX c r l x₀ ω)) φ := by
    intro φ
    have hR1 := Restart.ae_condExp_cexp_chartTransport_random_on h𝒢 hc hdom𝒢 hfwd𝒢 hliftm𝒢 hliftc hhm I.kc hM𝒢
      hcond φ
    set e : ℂ := Complex.exp (Complex.I * ((I.σa * Chart.oneDist φ : ℝ) : ℂ)) with he
    have hsplit : (fun ω' => Complex.exp (Complex.I * (I.Hr ω' φ : ℂ))) =
        e • fun ω' => Complex.exp (Complex.I * (Chart.chartTransport (hc ω') 1 0 I.kc (c.h ω') φ : ℂ)) := by
      funext ω'
      rw [Pi.smul_apply, smul_eq_mul, he, ← Complex.exp_add, hHr ω' (hc ω'), Chart.chartTransport_apply',
        Chart.chartTransport_apply']
      congr 1
      push_cast
      ring
    have hce : c.P[fun ω' => Complex.exp (Complex.I * (I.Hr ω' φ : ℂ)) | 𝒢s.1] =ᵐ[c.P]
        e • c.P[fun ω' => Complex.exp (Complex.I * (Chart.chartTransport (hc ω') 1 0 I.kc (c.h ω') φ : ℂ)) | 𝒢s.1] := by
      rw [hsplit]
      exact condExp_smul _ _ _
    filter_upwards [hR1, hce, hmean0 φ] with ω h1 h2 h3 hω
    rw [h2, Pi.smul_apply, smul_eq_mul, h1 hω, he, ← Complex.exp_add, Restart.gaussCF, ← h3 hω,
      Chart.chartTransport_apply', Chart.chartTransport_apply']
    have hH : (upperHalfPlaneOpens : Set ℂ) = H := rfl
    rw [hH]
    congr 1
    push_cast
    ring
  have hsort' : ∀ᵐ ω ∂c.P, ω ∈ Mset → (I.β (I.srecX c r l x₀ ω)).IsSorted :=
    Eventually.of_forall fun ω hω => hsort _ hω
  exact ⟨𝒢s, M, hrec.mono hℋ𝒢 le_rfl, hM0, hM,
    Exist.StagedLaw.ae_isGFFWithBoundaryData_condExpKernel h𝒢 hsort' hHrm hG⟩

end Cond

end InteractingSLE.Theorem14.GW2Rd
