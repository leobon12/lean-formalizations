/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2XkKer
import InteractingSLE.Spec.Supplement.GW2OmxKerF

/-!
# The root-`x` kernel port (D38): the launch kernel for a countable family of stage times at a root `x`

Packet PROVE-GW2-GEOM2, round 11 (STAGEMEAN's `GW2Omx.ae_launch_kernel_fam` at a root `x`, with RELDET's root-`x`
union `GW2Rd.schedUnionX` and `GW2Rd.ae_stageSet_subset_schedUnionX`):

* **`ae_launch_kernel_famX`**: one launch datum `b'`, `J'`, `u'` and flow-line driver, with the kernel and the marked
  locality of the root-`x` launch union at every stage time `t i` of a countable family.
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

open GW2Omx LocalSets WholeField Exist Staged StagedLaw GW2Schedule GW2Tip GW2TipSystem GW2TipSystem.RootC24
  GW2TipSystem.RootJ31 GW2Sdi Restart.MarkovChart GW4Fix GW4Fix.CLoc Sec5.Prop513Schedule GW2Rd
open QuantumZipper (chiC)

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **`ae_launch_kernelX` for a countable family of stage times, with one launch datum** (root `x`). -/
theorem ae_launch_kernel_famX (h13 : Exist.Theorem13Statement.{u}) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (hord : TimeOrdered 0 (historyProgram c r l))
    {ι : Type*} [Countable ι] (t : ι → ℝ≥0) {M : ι → Ω → DistOn upperHalfPlaneOpens}
    (𝓜 : ι → {m : MeasurableSpace Ω // m ≤ mΩ})
    (hB𝓜 : ∀ i, Measurable[(𝓜 i).1, hittingSigma] (schedUnionX c r l a (historyTime c r l) (t i)))
    (hMh : ∀ i, ∀ᵐ ω ∂c.P, IsHarmonicDistOn (M i ω) (H \ schedUnionX c r l a (historyTime c r l) (t i) ω))
    (hker : ∀ i, ∀ᵐ ω₀ ∂c.P, ∀ φ : TestOn upperHalfPlaneOpens,
      (condExpKernel c.P (GW2Olm.pastG c r l a) ω₀)[fun ω => Complex.exp (Complex.I * (c.h ω φ : ℂ)) | (𝓜 i).1]
        =ᵐ[condExpKernel c.P (GW2Olm.pastG c r l a) ω₀]
        fun ω => rangeKerCF (M i ω) (H \ schedUnionX c r l a (historyTime c r l) (t i) ω) φ) :
    ∀ᵐ ω₀ ∂c.P, ∀ (cL : Chart) (θ : ℝ), GW2Olm.curLaunch c r l a ω₀ = some (cL, θ) →
      ∃ (hconf : cL.IsConformal) (b' : ℝ → ℝ) (J' : Finset ℝ) (u' : ℂ → ℝ),
        IsPiecewiseConstantBoundaryData b' J' ∧ IsBoundedHarmonicExtension b' J' u' ∧
        IsFlowLineDriver c.κ b' J' θ (condExpKernel c.P (GW2Olm.pastG c r l a) ω₀)
          (fun ω => Chart.chartTransport hconf 1 0 (chiC c.κ) (c.h ω))
          (fun t ω => (GW2Olm.futFam c r l a (GW2Olm.curIdx c r l) ω).1 t)
          (fun ω => (GW2Olm.futFam c r l a (GW2Olm.curIdx c r l) ω).2) ∧
        (∀ ω, IsChartTransport cL 1 0 (chiC c.κ) (c.h ω) (Chart.chartTransport hconf 1 0 (chiC c.κ) (c.h ω))) ∧
        GW1P.HasProperBdryExt cL ∧ ContinuousOn cL.2.2 cL.dom ∧ InnerProductSpace.HarmonicOnNhd cL.2.2 cL.dom ∧
        ∀ i, (∀ᵐ ω ∂(condExpKernel c.P (GW2Olm.pastG c r l a) ω₀),
          IsHarmonicDistOn (Chart.chartTransport hconf 1 0 (chiC c.κ) (M i ω) - smoothDist upperHalfPlaneOpens u')
            (H \ launchUnionX c r l a cL (t i) ω)) ∧
        (∀ ψ : TestOn upperHalfPlaneOpens,
          (condExpKernel c.P (GW2Olm.pastG c r l a) ω₀)[fun ω => Complex.exp (Complex.I * (centredField
              (fun ω => Chart.chartTransport hconf 1 0 (chiC c.κ) (c.h ω)) u' ω ψ : ℂ)) | (𝓜 i).1]
            =ᵐ[condExpKernel c.P (GW2Olm.pastG c r l a) ω₀]
            fun ω => rangeKerCF (Chart.chartTransport hconf 1 0 (chiC c.κ) (M i ω) -
              smoothDist upperHalfPlaneOpens u') (H \ launchUnionX c r l a cL (t i) ω) ψ) ∧
        IsHistoryAvoidanceLocal (𝓜 i).1 (launchUnionX c r l a cL (t i))
          (centredField (fun ω => Chart.chartTransport hconf 1 0 (chiC c.κ) (c.h ω)) u')
          (condExpKernel c.P (GW2Olm.pastG c r l a) ω₀) := by
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
  filter_upwards [ae_all_iff.2 hker, ae_all_iff.2 fun i => KernelTower.ae_ae_condExpKernel_of_ae h𝒢 (hMh i),
    ae_all_iff.2 fun i => KernelTower.ae_ae_condExpKernel_of_ae h𝒢
      (ae_stageSet_subset_schedUnionX h13 c r l a hord (t i)),
    CondDriverBridge.ae_ae_run_eq_of_le (P := c.P) (κ := c.κ) (b := c.b) (jumps := c.jumps) spec
      (fun j _ ω => hreg j ω) h𝒢 le_rfl, hR.ae_pieceRegular, hS.2.2.2 k] with ω₀ hk₀a hMνa hgνa hrν hpr hst
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
  obtain ⟨b', j', h', hb', htr', hfl'⟩ := hst cL θ hl
  have hh'eq : h' = fun ω => Chart.chartTransport hconf 1 0 (chiC c.κ) (c.h ω) :=
    funext fun ω => (htr' ω).eq_chartTransport hconf hℓ
  rw [hh'eq] at hfl'
  obtain ⟨u', hu', -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension hb'
  refine ⟨hconf, b', j', u', hb', hu', hfl', fun ω => ?_, GW2Later.hasProperBdryExt_of_launch hpr hl, hliftc,
    hlift, fun i => ?_⟩
  · have h1 := htr' ω
    rw [hh'eq] at h1
    exact h1
  have hk₀ := hk₀a i
  have hMν := hMνa i
  have hgν := hgνa i
  have hV : ∀ᵐ ω ∂ν, IsOpen (H \ schedUnionX c r l a (historyTime c r l) (t i) ω) ∧
      IsOpen ((H \ schedUnionX c r l a (historyTime c r l) (t i) ω) \ cL.dom) := by
    filter_upwards [hgν, hrν] with ω hg hr
    have hO := (schedUnionX_subset_isOpen c r l a (historyTime c r l) (t i) ω).2
    refine ⟨hO, Restart.StagedEntrance.isOpen_sdiff_dom hO sdiff_subset hfr ?_⟩
    have hst' : WalkLaw.stageSet c.κ c.b c.jumps spec E k ω₀ = WalkLaw.stageSet c.κ c.b c.jumps spec E k ω := by
      unfold WalkLaw.stageSet
      rw [hr]
    rw [hst']
    exact disjoint_left.2 fun z hz hz' => hz'.2 (hg hz)
  have hk₁ : ∀ ψ : TestOn upperHalfPlaneOpens,
      ν[fun ω => Complex.exp (Complex.I * (Chart.chartTransport hconf 1 0 (chiC c.κ) (c.h ω) ψ : ℂ)) | (𝓜 i).1]
        =ᵐ[ν] fun ω => rangeKerCF (Chart.chartTransport hconf 1 0 (chiC c.κ) (M i ω))
          (chartPre cL (H \ schedUnionX c r l a (historyTime c r l) (t i) ω)) ψ :=
    fun ψ => ae_condExp_cexp_chartTransport (𝓜 := (𝓜 i).1) (Q := ν) hconf (Or.inl rfl) 0 (chiC c.κ) hV hk₀ ψ
  set S : DistOn upperHalfPlaneOpens := smoothDist upperHalfPlaneOpens u' with hSdef
  have hU : launchUnionX c r l a cL (t i) =
      fun ω => H \ chartPre cL (H \ schedUnionX c r l a (historyTime c r l) (t i) ω) := by
    funext ω
    exact launchUnion_eq hconf _
  have hk₃ : ∀ ψ : TestOn upperHalfPlaneOpens,
      ν[fun ω => Complex.exp (Complex.I * (centredField
          (fun ω => Chart.chartTransport hconf 1 0 (chiC c.κ) (c.h ω)) u' ω ψ : ℂ)) | (𝓜 i).1] =ᵐ[ν]
        fun ω => rangeKerCF (Chart.chartTransport hconf 1 0 (chiC c.κ) (M i ω) - S)
          (H \ (H \ chartPre cL (H \ schedUnionX c r l a (historyTime c r l) (t i) ω))) ψ := by
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
      (fun ω => Complex.exp (Complex.I * (Chart.chartTransport hconf 1 0 (chiC c.κ) (c.h ω) ψ : ℂ))) (𝓜 i).1
      (μ := ν), hk₁ ψ] with ω h1 h2
    rw [h1, Pi.smul_apply, h2, smul_eq_mul, sdiff_sdiff_cancel_left (chartPre_subset_H _ _), rangeKerCF,
      rangeKerCF, ← Complex.exp_add, sub_apply]
    congr 1
    push_cast
    ring
  have hM₂h : ∀ᵐ ω ∂ν, IsHarmonicDistOn (Chart.chartTransport hconf 1 0 (chiC c.κ) (M i ω) - S)
      (H \ (H \ chartPre cL (H \ schedUnionX c r l a (historyTime c r l) (t i) ω))) := by
    filter_upwards [hMν] with ω hω
    rw [sdiff_sdiff_cancel_left (chartPre_subset_H _ _)]
    have hVo : IsOpen (H \ schedUnionX c r l a (historyTime c r l) (t i) ω) :=
      (schedUnionX_subset_isOpen c r l a (historyTime c r l) (t i) ω).2
    have hM1 : IsHarmonicDistOn (Chart.chartTransport hconf 1 0 (chiC c.κ) (M i ω))
        (chartPre cL (H \ schedUnionX c r l a (historyTime c r l) (t i) ω)) := by
      refine isHarmonicDistOn_chartTransport_pm hconf hliftc hlift (isOpen_chartPre hconf hVo)
        (chartPre_subset_H _ _) ?_ (Or.inl rfl) 0 (chiC c.κ)
      rw [image_chartPre hconf]
      exact IsHarmonicDistOn.mono hω inter_subset_left
    exact LocalSets.IsHarmonicDistOn.sub' (isOpen_chartPre hconf hVo) hM1
      (IsHarmonicDistOn.mono (isHarmonicDistOn_smoothDist hu'.1) (chartPre_subset_H _ _))
  have hXm : Measurable fun ω => Chart.chartTransport hconf 1 0 (chiC c.κ) (c.h ω) :=
    (Chart.measurable_chartTransport hconf _ _ _).comp hhm
  have hloc' := WFS.isHistoryAvoidanceLocal_of_retainedKernel (𝓜 i).2 (measurable_centredField hXm u')
    (measurable_launch hconf (hB𝓜 i))
    (Eventually.of_forall fun ω => ⟨sdiff_subset, by
      rw [sdiff_sdiff_cancel_left (chartPre_subset_H _ _)]
      exact isOpen_chartPre hconf (schedUnionX_subset_isOpen c r l a (historyTime c r l) (t i) ω).2⟩) hM₂h hk₃
  refine ⟨?_, fun ψ => ?_, ?_⟩
  · rw [hU]
    exact hM₂h
  · rw [hU]
    exact hk₃ ψ
  · rw [hU]
    exact hloc'

end InteractingSLE.Theorem14.GW2Xk
