/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2TjGeo
import InteractingSLE.Spec.Supplement.GW2TgSets
import InteractingSLE.Spec.Supplement.GW2aPieceChart
import InteractingSLE.Spec.Supplement.GW4CLocChart

/-!
# (T1): the union is marked local under the conditional law of the earlier pieces

Packet PROVE-GW2-RELDET, ruling R117(b), item (T1) (`GW2Olm.KernelUnionLocal`), for the raw marks `kerMarks`.

For `P`-almost every `ω₀`, at a launch of the current piece in the chart `cL`, under `ν = condExpKernel P pastG ω₀`:
1. the field has the Gaussian kernel of the union, given countably generated marks `𝓜 ⊇ kerMarks t`
   (`GW2TjKer.exists_kernel_union`);
2. `cL` is the chart of the run before the current piece: a domain chart (`SB.Lw.isDomainChart_runChart`), whose
   domain has its frontier in `ℍ` on the explored set of the earlier pieces (`WalkLeaf.mem_stageSet_of_frontier`);
   under `ν` that explored set is frozen and lies in the union (`GW2TjGeo.ae_stageSet_subset_schedUnionS`), so
   `(ℍ ∖ B) ∖ dom cL` is open;
3. the kernel is read in `cL` (`GW4Fix.CLoc.ae_condExp_cexp_chartTransport`); the launch field is, under `ν`, a GFF
   with the launch word's data (`IsStagedHistory`), so every `uL` centring it to a zero-boundary GFF has the smoothed
   distribution of a bounded harmonic extension (`smoothDist_eq_of_isZeroBoundaryGFF`);
4. the retained-kernel criterion (`WFS.isHistoryAvoidanceLocal_of_retainedKernel`) gives the marked locality of the
   launch image `H \ chartPre cL (H \ B) = cL(B ∩ dom cL)` for `𝓜`, hence for `kerMarks t`.

* **`kernelUnionLocal`**: (T1) from the marked locality of the union for the stage filtration.
* **`SchedKernelLinesStatementT`**: `GW2Olm.SchedKernelLinesStatement` with decision D1's guard
  `TimeOrdered 0 (historyProgram c r l)`; **`schedKernelLinesStatementT`**: it holds, from Theorems 1.2–1.3.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology TopologicalSpace
open scoped NNReal ENNReal
open QuantumZipper (H chiC zeroGFFTestCov)
open LQGMetric (DistOn TestOn)
open SupercriticalConformalCovariance.GM24 (smoothDist)

universe u

namespace InteractingSLE.Theorem14.GW2Rd

open LocalSets WholeField Exist Staged StagedLaw GW2Schedule GW2Tip GW2TipSystem GW2TipSystem.RootC24
  GW2TipSystem.RootJ31 GW2Sdi Restart.MarkovChart GW4Fix GW4Fix.CLoc Sec5.Prop513Schedule

/-- Two centrings of one field that both make it a zero-boundary GFF have the same smoothed distribution. -/
theorem smoothDist_eq_of_isZeroBoundaryGFF {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    {X : Ω → DistOn upperHalfPlaneOpens} {u₁ u₂ : ℂ → ℝ}
    (h₁ : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (centredField X u₁) Q)
    (h₂ : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (centredField X u₂) Q) :
    smoothDist upperHalfPlaneOpens u₁ = smoothDist upperHalfPlaneOpens u₂ := by
  ext ψ
  have i₁ := (h₁.process.gaussian.hasGaussianLaw_eval ψ).integrable
  have i₂ := (h₂.process.gaussian.hasGaussianLaw_eval ψ).integrable
  have c₁ := h₁.process.centered ψ
  have c₂ := h₂.process.centered ψ
  have e : ∀ ω, centredField X u₂ ω ψ - centredField X u₁ ω ψ =
      smoothDist upperHalfPlaneOpens u₁ ψ - smoothDist upperHalfPlaneOpens u₂ ψ := by
    intro ω
    simp only [centredField, sub_apply]
    ring
  have h := integral_sub i₂ i₁
  rw [c₁, c₂, sub_zero] at h
  have hP : IsProbabilityMeasure Q := h₁.process.gaussian.isProbabilityMeasure
  simp only [e, integral_const, probReal_univ, smul_eq_mul, one_mul] at h
  linarith

section Main

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **The launch image of a union is marked local under the conditional law of the earlier pieces**, for the raw
marks `kerMarks`, for any union `B t` that is hitting-measurable, relatively closed, history-marked local for the stage
filtration and almost surely contains the explored set of the earlier pieces. -/
theorem kernelLocal_of_union (h13 : Exist.Theorem13Statement.{u}) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) {u₀ : ℂ → ℝ} (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh0 : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (centredField c.h u₀) c.P) {B : ℝ≥0 → Ω → Set ℂ}
    (hBm : ∀ t, Measurable[mΩ, hittingSigma] (B t)) (hBc : ∀ t ω, B t ω ⊆ H ∧ IsOpen (H \ B t ω))
    (hloc : ∀ t, IsHistoryAvoidanceLocal (stgF c r l a t) (B t) (centredField c.h u₀) c.P)
    (hgeo : ∀ t, ∀ᵐ ω ∂c.P, WalkLaw.stageSet c.κ c.b c.jumps (GW2Olm.futSpec c r l a) (GW2Olm.futFam c r l a)
      (GW2Olm.curIdx c r l) ω ⊆ B t ω) (t : ℝ≥0) :
    ∀ᵐ ω₀ ∂c.P, ∀ (cL : Chart) (θ : ℝ), GW2Olm.curLaunch c r l a ω₀ = some (cL, θ) →
      ∀ X : Ω → DistOn upperHalfPlaneOpens, (∀ ω, IsChartTransport cL 1 0 (chiC c.κ) (c.h ω) (X ω)) →
      ∀ uL : ℂ → ℝ, LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (centredField X uL)
          (condExpKernel c.P (GW2Olm.pastG c r l a) ω₀) →
        IsHistoryAvoidanceLocal (kerMarks c r l a t) (fun ω => cL.1 '' (B t ω ∩ (cL.dom : Set ℂ)))
          (centredField X uL) (condExpKernel c.P (GW2Olm.pastG c r l a) ω₀) := by
  obtain ⟨M, 𝓜, hK𝓜, hB𝓜, hM𝓜, hMh, hker⟩ := exists_kernel_union_of c r l a hu₀ hh0 t (hBm t) (hBc t) (hloc t)
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
    KernelTower.ae_ae_condExpKernel_of_ae h𝒢 (hgeo t),
    CondDriverBridge.ae_ae_run_eq_of_le (P := c.P) (κ := c.κ) (b := c.b) (jumps := c.jumps) spec
      (fun j _ ω => hreg j ω) h𝒢 le_rfl, hR.ae_pieceRegular, hS.2.2.2 k] with ω₀ hk₀ hMν hgν hrν hpr hst
  intro cL θ hl X hX uL hzb
  set ν := condExpKernel c.P (GW2Olm.pastG c r l a) ω₀ with hν
  -- the launch chart is the chart of the run before the current piece, a domain chart
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
  -- the frontier of the chart domain lies on the explored set of the earlier pieces
  have hfr : ∀ z ∈ H, z ∈ closure (cL.dom : Set ℂ) → z ∉ cL.dom →
      z ∈ WalkLaw.stageSet c.κ c.b c.jumps spec E k ω₀ := by
    rw [hcL]
    exact WalkLeaf.mem_stageSet_of_frontier spec E ω₀ hpr k
  have hV : ∀ᵐ ω ∂ν, IsOpen (H \ B t ω) ∧
      IsOpen ((H \ B t ω) \ cL.dom) := by
    filter_upwards [hgν, hrν] with ω hg hr
    have hO := (hBc t ω).2
    refine ⟨hO, Restart.StagedEntrance.isOpen_sdiff_dom hO sdiff_subset hfr ?_⟩
    have hst' : WalkLaw.stageSet c.κ c.b c.jumps spec E k ω₀ = WalkLaw.stageSet c.κ c.b c.jumps spec E k ω := by
      unfold WalkLaw.stageSet
      rw [hr]
    rw [hst']
    exact disjoint_left.2 fun z hz hz' => hz'.2 (hg hz)
  -- the launch field and its centring
  have hXeq : X = fun ω => Chart.chartTransport hconf 1 0 (chiC c.κ) (c.h ω) :=
    funext fun ω => (hX ω).eq_chartTransport hconf hℓ
  obtain ⟨b', j', h', hb', htr', hfl'⟩ := hst cL θ hl
  have hh'eq : h' = X := funext fun ω =>
    ((htr' ω).eq_chartTransport hconf hℓ).trans ((hX ω).eq_chartTransport hconf hℓ).symm
  have hgff := GW2aPiece.isGFFWithBoundaryData_of_isFlowLineDriver c.hκ hb' hfl'
  obtain ⟨u', hu', -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension hb'
  have hzb' := Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hgff hu'
  rw [hh'eq] at hzb'
  have hSeq := smoothDist_eq_of_isZeroBoundaryGFF hzb hzb'
  have hcent : centredField X uL = centredField X u' := by
    funext ω
    simp only [centredField, hSeq]
  rw [hcent]
  subst hXeq
  -- the kernel in the launch chart
  have hk₁ : ∀ ψ : TestOn upperHalfPlaneOpens,
      ν[fun ω => Complex.exp (Complex.I * (Chart.chartTransport hconf 1 0 (chiC c.κ) (c.h ω) ψ : ℂ)) | 𝓜.1]
        =ᵐ[ν] fun ω => rangeKerCF (Chart.chartTransport hconf 1 0 (chiC c.κ) (M ω))
          (chartPre cL (H \ B t ω)) ψ :=
    fun ψ => ae_condExp_cexp_chartTransport (𝓜 := 𝓜.1) (Q := ν) hconf (Or.inl rfl) 0 (chiC c.κ) hV hk₀ ψ
  set S : DistOn upperHalfPlaneOpens := smoothDist upperHalfPlaneOpens u' with hSdef
  have hk₃ : ∀ ψ : TestOn upperHalfPlaneOpens,
      ν[fun ω => Complex.exp (Complex.I * (centredField
          (fun ω => Chart.chartTransport hconf 1 0 (chiC c.κ) (c.h ω)) u' ω ψ : ℂ)) | 𝓜.1] =ᵐ[ν]
        fun ω => rangeKerCF (Chart.chartTransport hconf 1 0 (chiC c.κ) (M ω) - S)
          (H \ (H \ chartPre cL (H \ B t ω))) ψ := by
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
      (H \ (H \ chartPre cL (H \ B t ω))) := by
    filter_upwards [hMν] with ω hω
    rw [sdiff_sdiff_cancel_left (chartPre_subset_H _ _)]
    have hVo : IsOpen (H \ B t ω) := (hBc t ω).2
    have hM1 : IsHarmonicDistOn (Chart.chartTransport hconf 1 0 (chiC c.κ) (M ω))
        (chartPre cL (H \ B t ω)) := by
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
      exact isOpen_chartPre hconf (hBc t ω).2⟩) hM₂h hk₃
  have hU : (fun ω => cL.1 '' (B t ω ∩ (cL.dom : Set ℂ))) = fun ω => H \ chartPre cL (H \ B t ω) := by
    funext ω
    exact launchUnion_eq hconf _
  rw [hU]
  exact fun U G hUH hG hd F hF => hloc' U G hUH hG hd F (hK𝓜 F hF)

/-- **(T1): the union is marked local under the conditional law of the earlier pieces** (root `0`, time-ordered
history), for the raw marks `kerMarks`, from the marked locality of the union for the stage filtration. -/
theorem kernelUnionLocal (h13 : Exist.Theorem13Statement.{u}) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (hr0 : rootPt r.1 = 0) (hord : TimeOrdered 0 (historyProgram c r l))
    {u₀ : ℂ → ℝ} (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh0 : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (centredField c.h u₀) c.P)
    (hloc : ∀ t, IsHistoryAvoidanceLocal (stgF c r l a t) (schedUnionS c r l a t) (centredField c.h u₀) c.P) :
    GW2Olm.KernelUnionLocal c r l a (kerMarks c r l a) := fun t =>
  kernelLocal_of_union h13 c r l a hu₀ hh0 (measurable_schedUnionS c r l a) (schedUnionS_subset_isOpen c r l a)
    hloc (fun t => ae_stageSet_subset_schedUnionS h13 c r l a hr0 hord t) t

end Main

/-- **Decision D1's successor of `GW2Olm.SchedKernelLinesStatement`** (R117(b), R119): at root `0` and for a
time-ordered history, RELDET's provisions for the corrected union together with raw kernel marks satisfying (T1)
and (T2). -/
def SchedKernelLinesStatementT : Prop :=
  ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ), rootPt r.1 = 0 → TimeOrdered 0 (historyProgram c r l) →
    ∃ (u₀ : ℂ → ℝ) (ℋ : ℝ≥0 → MeasurableSpace Ω),
      InnerProductSpace.HarmonicOnNhd u₀ H ∧
      LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (centredField c.h u₀) c.P ∧
      (∀ t, stgFilt (Supp8.RelSafe.physFilt (GW2Sde.measurable_gb6Rec_src c) (measurable_schedW c r l a) c.P)
        (historyTime c r l) (GW2Sde.measurable_stageEncRec c r l) t ≤ ℋ t) ∧
      (∀ t, ℋ t ≤ mΩ) ∧
      (∀ t, IsHistoryAvoidanceLocal (ℋ t) (schedUnionS c r l a t) (centredField c.h u₀) c.P) ∧
      ∃ 𝓚 : ℝ≥0 → MeasurableSpace Ω, GW2Olm.KernelMarksAgree c r l a 𝓚 ℋ ∧ GW2Olm.KernelUnionLocal c r l a 𝓚

/-- **The union is marked local for the stage filtration** (named marks, review item N2): root `0`, time-ordered
history, the field centred by a bounded harmonic extension of the boundary data (Theorems 1.2–1.3). -/
theorem isHistoryAvoidanceLocal_stgF (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (hr0 : rootPt r.1 = 0) (hord : TimeOrdered 0 (historyProgram c r l))
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension c.b c.jumps u₀) (t : ℝ≥0) :
    IsHistoryAvoidanceLocal (stgF c r l a t) (schedUnionS c r l a t) (centredField c.h u₀) c.P := by
  obtain ⟨u₁, ℋ', -, hzb, hstg, -, -, -, hloc'⟩ :=
    exists_schedLinesLocal_setsT c r l a h12 h13 hr0 hord (le_refl (historyTime c r l))
  have hS := smoothDist_eq_of_isZeroBoundaryGFF hzb
    (Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData c.hh hu₀)
  have hu : centredField c.h u₁ = centredField c.h u₀ := by
    funext ω
    simp only [centredField, hS]
  rw [← hu, GW2Sdj.schedUnionS_eq_schedUnionL]
  exact fun U G hUH hG hd F hF => hloc' t U G hUH hG hd F (hstg t F hF)

/-- **(T1)–(T2) hold, with the stage filtration as the instance's marks** (Theorems 1.2–1.3). -/
theorem schedKernelLinesStatementT (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u}) :
    SchedKernelLinesStatementT.{u} := by
  intro Ω mΩ _ c r l a hr0 hord
  obtain ⟨u₀, ℋ', hharm, hzb, hstg, -, -, -, hloc'⟩ :=
    exists_schedLinesLocal_setsT c r l a h12 h13 hr0 hord (le_refl (historyTime c r l))
  have hloc : ∀ t, IsHistoryAvoidanceLocal (stgF c r l a t) (schedUnionS c r l a t) (centredField c.h u₀) c.P := by
    intro t
    rw [GW2Sdj.schedUnionS_eq_schedUnionL]
    exact fun U G hUH hG hd F hF => hloc' t U G hUH hG hd F (hstg t F hF)
  exact ⟨u₀, stgF c r l a, hharm, hzb, fun t => le_rfl, fun t => (stgFilt _ _ _).le t, hloc,
    kerMarks c r l a, kernelMarksAgree_stgFilt c r l a, kernelUnionLocal h13 c r l a hr0 hord hharm hzb hloc⟩

end InteractingSLE.Theorem14.GW2Rd
