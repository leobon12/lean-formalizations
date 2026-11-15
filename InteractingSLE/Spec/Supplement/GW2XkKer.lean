/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2XkContact
import InteractingSLE.Spec.Supplement.GW2OmxKer

/-!
# The root-`x` kernel port (D38): the union's Gaussian kernel at a root `x`

Packet PROVE-GW2-GEOM2, round 11 (STAGEMEAN's `GW2OmxKer` at a root `x`). The same proofs with RELDET's root-`x`
union `GW2Rd.schedUnionX` (explored hull translated to the root) in place of the root-`0` union, and RELDET's
`GW2Rd.ae_stageSet_subset_schedUnionX` (every root, time-ordered history) in place of its root-`0` version:

* `omxMarksX`, **`exists_kernel_union_meanX`**: a local-set mean `g` of the root-`x` union and countably generated
  marks `𝓜 ⊇ pastG` recording the union and `g`, with the Gaussian kernel of mean `g + u₀` given `𝓜`, under `P` and
  under `condExpKernel P pastG ω₀`;
* **`ae_launch_kernelX`**: the launch-chart kernel of the root-`x` union's launch image (`launchUnionX`) and its
  marked locality for `𝓜`, with the launch data and the chart facts.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology TopologicalSpace
open scoped NNReal ENNReal
open QuantumZipper (H zeroGFFTestCov)
open LQGMetric (DistOn TestOn)
open SupercriticalConformalCovariance.GM24 (smoothDist)

universe u

namespace InteractingSLE.Theorem14.GW2Xk

open GW2Omx LocalSets WholeField GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31 GW2Sdi GW4Fix GW4Fix.CLoc
  GW2Rd

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
  (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)

/-- The coarsened marks of the union at stage time `t` for a mean `g` (`GW2Rd.unionMarks`). -/
@[instance_reducible]
def omxMarksX (t : ℝ≥0) (g : Ω → DistOn upperHalfPlaneOpens) : MeasurableSpace Ω :=
  unionMarks (schedUnionX c r l a (historyTime c r l) t) g (kerMarks c r l a t)

/-- **The union's Gaussian kernel with its local-set mean** (`GW2Rd.exists_kernel_union`, with the mean and the marks
exported). -/
theorem exists_kernel_union_meanX {u₀ : ℂ → ℝ} (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh0 : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (centredField c.h u₀) c.P) (t : ℝ≥0)
    (hloc : IsHistoryAvoidanceLocal (stgF c r l a t) (schedUnionX c r l a (historyTime c r l) t)
      (centredField c.h u₀) c.P) :
    ∃ (g : Ω → DistOn upperHalfPlaneOpens) (𝓜 : {m : MeasurableSpace Ω // m ≤ mΩ}),
      IsLocalSetMean (schedUnionX c r l a (historyTime c r l) t) (centredField c.h u₀) c.P g ∧
      @MeasurableSpace.CountablyGenerated Ω 𝓜.1 ∧ kerMarks c r l a t ≤ 𝓜.1 ∧ GW2Olm.pastG c r l a ≤ 𝓜.1 ∧
      Measurable[𝓜.1, hittingSigma] (schedUnionX c r l a (historyTime c r l) t) ∧ Measurable[𝓜.1] g ∧
      (∀ᵐ ω ∂c.P, IsHarmonicDistOn (g ω + smoothDist upperHalfPlaneOpens u₀)
        (H \ schedUnionX c r l a (historyTime c r l) t ω)) ∧
      (∀ φ : TestOn upperHalfPlaneOpens,
        c.P[fun ω' => Complex.exp (Complex.I * (c.h ω' φ : ℂ)) | 𝓜.1] =ᵐ[c.P]
          fun ω => rangeKerCF (g ω + smoothDist upperHalfPlaneOpens u₀)
            (H \ schedUnionX c r l a (historyTime c r l) t ω) φ) ∧
      ∀ᵐ ω₀ ∂c.P, ∀ φ : TestOn upperHalfPlaneOpens,
        (condExpKernel c.P (GW2Olm.pastG c r l a) ω₀)[fun ω => Complex.exp (Complex.I * (c.h ω φ : ℂ)) | 𝓜.1]
          =ᵐ[condExpKernel c.P (GW2Olm.pastG c r l a) ω₀]
          fun ω => rangeKerCF (g ω + smoothDist upperHalfPlaneOpens u₀)
            (H \ schedUnionX c r l a (historyTime c r l) t ω) φ := by
  set B := schedUnionX c r l a (historyTime c r l) t with hBdef
  have hhm : Measurable c.h := c.hh.1
  have hh0m : Measurable (centredField c.h u₀) := measurable_centredField hhm u₀
  have hBm : Measurable[mΩ, hittingSigma] B := measurable_schedUnionX c r l a (historyTime c r l) t
  have hBc : ∀ ω, B ω ⊆ H ∧ IsOpen (H \ B ω) := schedUnionX_subset_isOpen c r l a (historyTime c r l) t
  have hℋ : stgF c r l a t ≤ mΩ := (stgFilt _ _ _).le t
  have hl : IsLocalSet B (centredField c.h u₀) c.P :=
    ((isLocalSet_tfae hh0 hBm (Eventually.of_forall hBc)).out 4 1).2 hloc.isAvoidanceLocal
  obtain ⟨g, hg⟩ := IsLocalSet.exists_isLocalSetMean hh0 hBm hl
  have hker := ae_condExp_cexp_boundary_marked hu₀ hh0 hBm hBc hℋ hloc hg
  set M : Ω → DistOn upperHalfPlaneOpens := fun ω => g ω + smoothDist upperHalfPlaneOpens u₀ with hM_def
  have hgM : Measurable[(omxMarksX c r l a t g)] g := Measurable.of_comap_le (le_sup_right.trans le_sup_left)
  have hBM : Measurable[(omxMarksX c r l a t g), hittingSigma] B :=
    Measurable.of_comap_le (le_sup_left.trans le_sup_left)
  have hadd : Measurable fun T : DistOn upperHalfPlaneOpens => T + smoothDist upperHalfPlaneOpens u₀ :=
    LQGMetric.measurable_distOn_iff.2 fun φ => ((LQGMetric.measurable_distOn_apply φ).add measurable_const)
  have hMM : Measurable[(omxMarksX c r l a t g)] M := hadd.comp hgM
  have hgerm : (omxMarksX c r l a t g) ≤ germSigma B (centredField c.h u₀) ⊔ stgF c r l a t :=
    sup_le (sup_le (le_sup_left.trans' (comap_le_germSigma _ _)) (le_sup_left.trans' hg.1.comap_le))
      ((kerMarks_le_stgFilt c r l a t).trans le_sup_right)
  have hgle : germSigma B (centredField c.h u₀) ⊔ stgF c r l a t ≤ mΩ := sup_le (germSigma_le hBm hh0m) hℋ
  have hle : (omxMarksX c r l a t g) ≤ mΩ := hgerm.trans hgle
  have hcg : @MeasurableSpace.CountablyGenerated Ω (omxMarksX c r l a t g) := by
    rw [omxMarksX, unionMarks_def]
    exact MeasurableSpace.CountablyGenerated.sup (MeasurableSpace.CountablyGenerated.sup
        (@MeasurableSpace.CountablyGenerated.comap _ _ hittingSigma countablyGenerated_hittingSigma _)
        (MeasurableSpace.CountablyGenerated.comap _)) (countablyGenerated_kerMarks c r l a t)
  have hK : kerMarks c r l a t ≤ (omxMarksX c r l a t g) := le_sup_right
  have hJ : GW2Olm.pastG c r l a ≤ (omxMarksX c r l a t g) := (pastG_le_kerMarks c r l a t).trans hK
  have hkerP : ∀ φ : TestOn upperHalfPlaneOpens,
      c.P[fun ω' => Complex.exp (Complex.I * (c.h ω' φ : ℂ)) | (omxMarksX c r l a t g)] =ᵐ[c.P]
        fun ω => rangeKerCF (M ω) (H \ B ω) φ := by
    intro φ
    have hR : StronglyMeasurable[(omxMarksX c r l a t g)] fun ω => rangeKerCF (M ω) (H \ B ω) φ :=
      (measurable_rangeKerCF hMM hBM hBc φ).stronglyMeasurable
    have hRi : Integrable (fun ω => rangeKerCF (M ω) (H \ B ω) φ) c.P := by
      refine Integrable.of_bound ((hR.mono hle).aestronglyMeasurable) 1 (Eventually.of_forall fun ω => ?_)
      have hcov : 0 ≤ zeroGFFTestCov (H \ B ω) φ φ := zeroGFFTestCov_self_nonneg (hBc ω).2 sdiff_subset φ
      rw [rangeKerCF, Complex.norm_exp]
      simp only [Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.ofReal_re, zero_mul, Complex.I_im,
        Complex.ofReal_im, mul_zero, sub_zero, zero_sub]
      rw [Real.exp_le_one_iff]
      nlinarith
    calc c.P[fun ω' => Complex.exp (Complex.I * (c.h ω' φ : ℂ)) | (omxMarksX c r l a t g)]
        =ᵐ[c.P] c.P[c.P[fun ω' => Complex.exp (Complex.I * (c.h ω' φ : ℂ)) |
          germSigma B (centredField c.h u₀) ⊔ stgF c r l a t] | (omxMarksX c r l a t g)] :=
          (condExp_condExp_of_le hgerm hgle).symm
      _ =ᵐ[c.P] c.P[fun ω => rangeKerCF (M ω) (H \ B ω) φ | (omxMarksX c r l a t g)] := condExp_congr_ae (hker φ)
      _ = fun ω => rangeKerCF (M ω) (H \ B ω) φ := condExp_of_stronglyMeasurable hle hR hRi
  have hν : ∀ᵐ ω₀ ∂c.P, ∀ k : Restart.RatComb,
      (condExpKernel c.P (GW2Olm.pastG c r l a) ω₀)[fun ω => Complex.exp
        (Complex.I * (c.h ω (Restart.ratComb upperHalfPlaneOpens k) : ℂ)) | (omxMarksX c r l a t g)]
        =ᵐ[condExpKernel c.P (GW2Olm.pastG c r l a) ω₀]
          fun ω => rangeKerCF (M ω) (H \ B ω) (Restart.ratComb upperHalfPlaneOpens k) := by
    refine ae_all_iff.2 fun k => ?_
    exact ae_ae_condExp_eq_of_le hJ hle hcg
      (GFF.measurable_exp_I_mul ((LQGMetric.measurable_distOn_apply _).comp hhm)) (C := 1)
      (fun ω => (Complex.norm_exp_I_mul_ofReal _).le) (hkerP _)
  refine ⟨g, ⟨_, hle⟩, hg, hcg, hK, hJ, hBM, hgM, ?_, hkerP, ?_⟩
  · filter_upwards [hg.2.1] with ω hω
    exact Coupling.IsHarmonicDistOn.add' (hBc ω).2 hω
      (IsHarmonicDistOn.mono (isHarmonicDistOn_smoothDist hu₀) sdiff_subset)
  · filter_upwards [hν] with ω₀ hω₀ φ
    exact ae_condExp_cexp_eq_rangeKerCF_of_ratComb (Q := condExpKernel c.P (GW2Olm.pastG c r l a) ω₀)
      hle hhm (Eventually.of_forall fun ω => ⟨(hBc ω).2, sdiff_subset⟩) hω₀ φ

end InteractingSLE.Theorem14.GW2Xk

namespace InteractingSLE.Theorem14.GW2Xk

open GW2Omx

open LocalSets WholeField Exist Staged StagedLaw GW2Schedule GW2Tip GW2TipSystem GW2TipSystem.RootC24
  GW2TipSystem.RootJ31 GW2Sdi Restart.MarkovChart GW4Fix GW4Fix.CLoc Sec5.Prop513Schedule GW2Rd
open QuantumZipper (chiC)

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **The launch-chart kernel of the union and its marked locality, for the coarsened marks** (the proof of
`GW2Rd.kernelUnionLocal` with the marks `𝓜` kept): for `P`-a.e. `ω₀`, at a launch of the current piece in `cL`,
under `ν = condExpKernel P pastG ω₀`, the launch field `X` (a flow line field of the launch data `b'`, centred by its
bounded harmonic extension `u'`) has, given `𝓜`, the Gaussian kernel of mean `cL(g + u₀) − u'` on the launch image of
the union, and that image is marked local for `𝓜`. -/
theorem ae_launch_kernelX (h13 : Exist.Theorem13Statement.{u}) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (hord : TimeOrdered 0 (historyProgram c r l))
    (t : ℝ≥0) {M : Ω → DistOn upperHalfPlaneOpens} (𝓜 : {m : MeasurableSpace Ω // m ≤ mΩ})
    (hB𝓜 : Measurable[𝓜.1, hittingSigma] (schedUnionX c r l a (historyTime c r l) t))
    (hMh : ∀ᵐ ω ∂c.P, IsHarmonicDistOn (M ω) (H \ schedUnionX c r l a (historyTime c r l) t ω))
    (hker : ∀ᵐ ω₀ ∂c.P, ∀ φ : TestOn upperHalfPlaneOpens,
      (condExpKernel c.P (GW2Olm.pastG c r l a) ω₀)[fun ω => Complex.exp (Complex.I * (c.h ω φ : ℂ)) | 𝓜.1]
        =ᵐ[condExpKernel c.P (GW2Olm.pastG c r l a) ω₀]
        fun ω => rangeKerCF (M ω) (H \ schedUnionX c r l a (historyTime c r l) t ω) φ) :
    ∀ᵐ ω₀ ∂c.P, ∀ (cL : Chart) (θ : ℝ), GW2Olm.curLaunch c r l a ω₀ = some (cL, θ) →
      ∃ (hconf : cL.IsConformal) (b' : ℝ → ℝ) (J' : Finset ℝ) (u' : ℂ → ℝ),
        IsPiecewiseConstantBoundaryData b' J' ∧ IsBoundedHarmonicExtension b' J' u' ∧
        IsFlowLineDriver c.κ b' J' θ (condExpKernel c.P (GW2Olm.pastG c r l a) ω₀)
          (fun ω => Chart.chartTransport hconf 1 0 (chiC c.κ) (c.h ω))
          (fun t ω => (GW2Olm.futFam c r l a (GW2Olm.curIdx c r l) ω).1 t)
          (fun ω => (GW2Olm.futFam c r l a (GW2Olm.curIdx c r l) ω).2) ∧
        (∀ᵐ ω ∂(condExpKernel c.P (GW2Olm.pastG c r l a) ω₀),
          IsHarmonicDistOn (Chart.chartTransport hconf 1 0 (chiC c.κ) (M ω) - smoothDist upperHalfPlaneOpens u')
            (H \ launchUnionX c r l a cL t ω)) ∧
        (∀ ψ : TestOn upperHalfPlaneOpens,
          (condExpKernel c.P (GW2Olm.pastG c r l a) ω₀)[fun ω => Complex.exp (Complex.I * (centredField
              (fun ω => Chart.chartTransport hconf 1 0 (chiC c.κ) (c.h ω)) u' ω ψ : ℂ)) | 𝓜.1]
            =ᵐ[condExpKernel c.P (GW2Olm.pastG c r l a) ω₀]
            fun ω => rangeKerCF (Chart.chartTransport hconf 1 0 (chiC c.κ) (M ω) - smoothDist upperHalfPlaneOpens u')
              (H \ launchUnionX c r l a cL t ω) ψ) ∧
        IsHistoryAvoidanceLocal 𝓜.1 (launchUnionX c r l a cL t)
          (centredField (fun ω => Chart.chartTransport hconf 1 0 (chiC c.κ) (c.h ω)) u')
          (condExpKernel c.P (GW2Olm.pastG c r l a) ω₀) ∧
        (∀ ω, IsChartTransport cL 1 0 (chiC c.κ) (c.h ω) (Chart.chartTransport hconf 1 0 (chiC c.κ) (c.h ω))) ∧
        GW1P.HasProperBdryExt cL ∧ ContinuousOn cL.2.2 cL.dom ∧ InnerProductSpace.HarmonicOnNhd cL.2.2 cL.dom := by
  set x := rootPt r.1 with hx
  set L := futureProgram c r l a with hL
  set spec := GW2Olm.futSpec c r l a with hspec
  set E := GW2Olm.futFam c r l a with hEdef
  set k := GW2Olm.curIdx c r l with hkdef
  have hS : IsStagedHistory c.κ c.b c.jumps c.P c.h spec E := isStagedHistory_canonFam c.hκ c.h12p c.βA c.c₀
    (specAngle spec) (specDelta spec) h13 c.hβA c.hb c.hc₀J c.hc₀ c.hh (spec := spec) rfl
    (isFlowProg_spec x true L) (specDelta_ne_top _)
  have hreg : ∀ j ω, IsRegularDriver (E j ω) := fun j ω =>
    isRegularDriver_canonDrive c.hκ c.h12p c.βA c.c₀ x (specAngle spec) (specDelta spec) (c.h ω) j
  have hR := stagedPiecesRegular_of_regular h13 c.hκ c.hb hS hreg
  have h𝒢 : GW2Olm.pastG c r l a ≤ mΩ := hS.2.1 k
  have hhm : Measurable c.h := c.hh.1
  have hlenL : L.length = k + 1 := by rw [hL, futureProgram, List.length_append, List.length_singleton]
  have hlen : spec.2.2.length = k + 1 := (GW2Schedule.length_scheduleProgram 0 L).trans hlenL
  filter_upwards [hker, KernelTower.ae_ae_condExpKernel_of_ae h𝒢 hMh,
    KernelTower.ae_ae_condExpKernel_of_ae h𝒢 (ae_stageSet_subset_schedUnionX h13 c r l a hord t),
    CondDriverBridge.ae_ae_run_eq_of_le (P := c.P) (κ := c.κ) (b := c.b) (jumps := c.jumps) spec
      (fun j _ ω => hreg j ω) h𝒢 le_rfl, hR.ae_pieceRegular, hS.2.2.2 k] with ω₀ hk₀ hMν hgν hrν hpr hst
  intro cL θ hl
  set ν := condExpKernel c.P (GW2Olm.pastG c r l a) ω₀ with hν
  obtain ⟨-, -, hcL⟩ := eq_launch_of_launches (κ := c.κ) (b := c.b) (jumps := c.jumps) spec (fun j => E j ω₀) hl
  have hs : AllSucc (specDelta spec) (fun j => E j ω₀) k := by
    by_contra hn
    have h0 := (launches_run_gw2 (κ := c.κ) (b := c.b) (jumps := c.jumps) (spec := spec) rfl (isFlowProg_spec x true L)
      (specDelta_ne_top _) (fun j => E j ω₀) (show k < spec.2.2.length by omega)).2 hn
    have h1 : GW2Olm.curLaunch c r l a ω₀ = none := h0
    rw [h1] at hl
    simp at hl
  have hlive := ((run_gw2 (κ := c.κ) (b := c.b) (jumps := c.jumps) (spec := spec) rfl (isFlowProg_spec x true L)
    (specDelta_ne_top _) (fun j => E j ω₀) k (by omega)).1 hs).1
  have hnot : stStatus (ExplState.run c.κ c.b c.jumps spec (fun j => E j ω₀) k) ≠ GW1Conn.stDone := by
    rcases hlive with h | h <;> rw [h] <;> exact fun h' => by cases h'
  have hdc := SB.Lw.isDomainChart_runChart (κ := c.κ) (b := c.b) (jumps := c.jumps) spec (fun j => E j ω₀)
    hpr k hnot
  have hdc' : IsDomainChart (H \ fillH (SB.prefixPhysSet c.κ c.b c.jumps spec (fun j => E j ω₀) k)) cL := by
    rw [hcL]
    exact hdc
  have hconf : cL.IsConformal := hdc'.isConformal
  have hdomeq : (cL.dom : Set ℂ) = H \ fillH (SB.prefixPhysSet c.κ c.b c.jumps spec (fun j => E j ω₀) k) := by
    rw [hconf.coe_dom, hdc'.image_eq]
  have hliftc : ContinuousOn cL.2.2 cL.dom := by
    rw [hdomeq]
    exact hdc'.continuousOn_lift
  have hlift : InnerProductSpace.HarmonicOnNhd cL.2.2 cL.dom := by
    rw [hdomeq]
    exact harmonicOnNhd_lift_of_isDomainChart hdc'
  have hℓ : LocallyIntegrableOn (fun w => cL.2.2 (cL.2.1 w)) H :=
    hdc'.continuousOn_lift_inv.locallyIntegrableOn QuantumZipper.isOpen_H.measurableSet
  have hfr : ∀ z ∈ H, z ∈ closure (cL.dom : Set ℂ) → z ∉ cL.dom →
      z ∈ WalkLaw.stageSet c.κ c.b c.jumps spec E k ω₀ := by
    rw [hcL]
    exact WalkLeaf.mem_stageSet_of_frontier spec E ω₀ hpr k
  have hV : ∀ᵐ ω ∂ν, IsOpen (H \ schedUnionX c r l a (historyTime c r l) t ω) ∧
      IsOpen ((H \ schedUnionX c r l a (historyTime c r l) t ω) \ cL.dom) := by
    filter_upwards [hgν, hrν] with ω hg hr
    have hO := (schedUnionX_subset_isOpen c r l a (historyTime c r l) t ω).2
    refine ⟨hO, Restart.StagedEntrance.isOpen_sdiff_dom hO sdiff_subset hfr ?_⟩
    have hst' : WalkLaw.stageSet c.κ c.b c.jumps spec E k ω₀ = WalkLaw.stageSet c.κ c.b c.jumps spec E k ω := by
      unfold WalkLaw.stageSet
      rw [hr]
    rw [hst']
    exact disjoint_left.2 fun z hz hz' => hz'.2 (hg hz)
  obtain ⟨b', j', h', hb', htr', hfl'⟩ := hst cL θ hl
  have hh'eq : h' = fun ω => Chart.chartTransport hconf 1 0 (chiC c.κ) (c.h ω) :=
    funext fun ω => (htr' ω).eq_chartTransport hconf hℓ
  rw [hh'eq] at hfl'
  obtain ⟨u', hu', -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension hb'
  have hk₁ : ∀ ψ : TestOn upperHalfPlaneOpens,
      ν[fun ω => Complex.exp (Complex.I * (Chart.chartTransport hconf 1 0 (chiC c.κ) (c.h ω) ψ : ℂ)) | 𝓜.1]
        =ᵐ[ν] fun ω => rangeKerCF (Chart.chartTransport hconf 1 0 (chiC c.κ) (M ω))
          (chartPre cL (H \ schedUnionX c r l a (historyTime c r l) t ω)) ψ :=
    fun ψ => ae_condExp_cexp_chartTransport (𝓜 := 𝓜.1) (Q := ν) hconf (Or.inl rfl) 0 (chiC c.κ) hV hk₀ ψ
  set S : DistOn upperHalfPlaneOpens := smoothDist upperHalfPlaneOpens u' with hSdef
  have hU : launchUnionX c r l a cL t = fun ω => H \ chartPre cL (H \ schedUnionX c r l a (historyTime c r l) t ω) := by
    funext ω
    exact launchUnion_eq hconf _
  have hk₃ : ∀ ψ : TestOn upperHalfPlaneOpens,
      ν[fun ω => Complex.exp (Complex.I * (centredField
          (fun ω => Chart.chartTransport hconf 1 0 (chiC c.κ) (c.h ω)) u' ω ψ : ℂ)) | 𝓜.1] =ᵐ[ν]
        fun ω => rangeKerCF (Chart.chartTransport hconf 1 0 (chiC c.κ) (M ω) - S)
          (H \ (H \ chartPre cL (H \ schedUnionX c r l a (historyTime c r l) t ω))) ψ := by
    intro ψ
    have hsplit : (fun ω => Complex.exp (Complex.I * (centredField
        (fun ω => Chart.chartTransport hconf 1 0 (chiC c.κ) (c.h ω)) u' ω ψ : ℂ))) =
        Complex.exp (-(Complex.I * (S ψ : ℂ))) •
          fun ω => Complex.exp (Complex.I * (Chart.chartTransport hconf 1 0 (chiC c.κ) (c.h ω) ψ : ℂ)) := by
      funext ω
      rw [Pi.smul_apply, smul_eq_mul, ← Complex.exp_add]
      simp only [centredField, sub_apply, hSdef]
      push_cast
      ring_nf
    rw [hsplit]
    filter_upwards [condExp_smul (Complex.exp (-(Complex.I * (S ψ : ℂ))))
      (fun ω => Complex.exp (Complex.I * (Chart.chartTransport hconf 1 0 (chiC c.κ) (c.h ω) ψ : ℂ))) 𝓜.1
      (μ := ν), hk₁ ψ] with ω h1 h2
    rw [h1, Pi.smul_apply, h2, smul_eq_mul, sdiff_sdiff_cancel_left (chartPre_subset_H _ _), rangeKerCF,
      rangeKerCF, ← Complex.exp_add, sub_apply]
    congr 1
    push_cast
    ring
  have hM₂h : ∀ᵐ ω ∂ν, IsHarmonicDistOn (Chart.chartTransport hconf 1 0 (chiC c.κ) (M ω) - S)
      (H \ (H \ chartPre cL (H \ schedUnionX c r l a (historyTime c r l) t ω))) := by
    filter_upwards [hMν] with ω hω
    rw [sdiff_sdiff_cancel_left (chartPre_subset_H _ _)]
    have hVo : IsOpen (H \ schedUnionX c r l a (historyTime c r l) t ω) :=
      (schedUnionX_subset_isOpen c r l a (historyTime c r l) t ω).2
    have hM1 : IsHarmonicDistOn (Chart.chartTransport hconf 1 0 (chiC c.κ) (M ω))
        (chartPre cL (H \ schedUnionX c r l a (historyTime c r l) t ω)) := by
      refine isHarmonicDistOn_chartTransport_pm hconf hliftc hlift (isOpen_chartPre hconf hVo)
        (chartPre_subset_H _ _) ?_ (Or.inl rfl) 0 (chiC c.κ)
      rw [image_chartPre hconf]
      exact IsHarmonicDistOn.mono hω inter_subset_left
    exact LocalSets.IsHarmonicDistOn.sub' (isOpen_chartPre hconf hVo) hM1
      (IsHarmonicDistOn.mono (isHarmonicDistOn_smoothDist hu'.1) (chartPre_subset_H _ _))
  have hXm : Measurable fun ω => Chart.chartTransport hconf 1 0 (chiC c.κ) (c.h ω) :=
    (Chart.measurable_chartTransport hconf _ _ _).comp hhm
  have hloc' := WFS.isHistoryAvoidanceLocal_of_retainedKernel 𝓜.2 (measurable_centredField hXm u')
    (measurable_launch hconf hB𝓜)
    (Eventually.of_forall fun ω => ⟨sdiff_subset, by
      rw [sdiff_sdiff_cancel_left (chartPre_subset_H _ _)]
      exact isOpen_chartPre hconf (schedUnionX_subset_isOpen c r l a (historyTime c r l) t ω).2⟩) hM₂h hk₃
  refine ⟨hconf, b', j', u', hb', hu', hfl', ?_, ?_, ?_, fun ω => ?_, GW2Later.hasProperBdryExt_of_launch hpr hl,
    hliftc, hlift⟩
  rotate_left 3
  · have h1 := htr' ω
    rw [hh'eq] at h1
    exact h1
  · rw [hU]
    exact hM₂h
  · intro ψ
    rw [hU]
    exact hk₃ ψ
  · rw [hU]
    exact hloc'

end InteractingSLE.Theorem14.GW2Xk
