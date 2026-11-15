/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2KxB0Ker2
import InteractingSLE.Spec.Supplement.GW2KxB0Set
import InteractingSLE.Spec.Supplement.GW2KxSupp
import InteractingSLE.Spec.Supplement.GW2OmxPair
import InteractingSLE.Spec.Supplement.GW2SchedRuleGB6
import InteractingSLE.Spec.Supplement.GW2RdLocPre
import InteractingSLE.Spec.Supplement.GW2PsmXferC
import InteractingSLE.Spec.Supplement.GB6LMeanDet

/-!
# The root piece's kernel forms at `P` from the root's start, at a root `x` (launch chart `recenter x`)

Packet PROVE-GW2-GEOM2, round 14 (D49), for the base of Claim(k) at a root `x ∈ {0} ∪ lowerArcRoots`. The root piece
is launched at index `0`, where the retained past is trivial, so the conditional kernel is `P` itself
(`GW1.pastSigma_zero_eq_bot`, `GW1.condExpKernel_bot_apply`), the launch chart is `Chart.id.recenter x`
(`eq_recenter_of_launch_zero`) and the launch datum is BR4a's (`hasLaunchPairEq_zero`; the contact set is `{x}`).
STAGEMEAN's `GW2Omx.kernel_launch_mean_pair` runs with:

* the union at the root piece's end, `schedUnionX c r [] a T 0` (the instance's stage-start union), with RELDET's
  kernel (`GW2Xk.exists_kernel_union_meanX` at `l = []`, `t = 0`);
* the counterflow's retained set `retSet s W ζ`, with GW2's retained marks (`exists_retained_marks_rec_gw2`) and its
  kernel (`exists_kernel_of_local`);
* both transported to the launch chart (`launch_kernel_of`) and localized on the event that the counterflow avoids
  the root up to `s` (`gapPt`).

* **`ae_base_formsX`**: local-set means `g` of the union and `g₁` of the retained set, and the kernel forms at the
  root piece's end (`UnionFormAt`) and at its start (`RetFormAt`) for the same datum and kernel word.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn TestOn)
open QuantumZipper (H chiC fwdHull)
open SupercriticalConformalCovariance.GM24 (smoothDist)

universe u

namespace InteractingSLE.Theorem14.GW2Kx

open GW2Omx Restart Exist Exist.Staged Exist.StagedLaw WholeField LocalSets GW2TipSystem GW2TipSystem.RootC24
  GW2TipSystem.RootJ31 GW2Schedule GW2Tip GW2Sdi GW2Rd GW2Olm Supp8 Supp8.GB6 Restart.MarkovChart GW2Xk GW2Kb
  Supp8.GB6LineL
open Supp8.Q3Rel (invHull)

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **The root piece's kernel forms at `P`** (root `x`, launch chart `recenter x`). -/
theorem ae_base_formsX (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (a : ℕ)
    (hroot : rootPt r.1 = 0 ∨ rootPt r.1 ∈ lowerArcRoots c.κ c.b c.jumps)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension c.b c.jumps u₀) :
    ∃ g g₁ : Ω → DistOn upperHalfPlaneOpens,
      IsLocalSetMean (schedUnionX c r [] a (historyTime c r []) 0) (centredField c.h u₀) c.P g ∧
      IsLocalSetMean (retSet c.s c.W c.ζ) (centredField c.h u₀) c.P g₁ ∧
      ∃ (hconf : (Chart.id.recenter (rootPt r.1)).IsConformal) (b' : ℝ → ℝ) (J' : Finset ℝ) (u' : ℂ → ℝ)
        (Wk : ℝ≥0 → Ω → ℝ) (ζk : Ω → ℝ≥0∞) (ℓ : Ω → ℝ≥0 → ℝ≥0) (c' : BoundaryWord) (γ : Ω → ℝ≥0 → ℂ)
        (uθ : ℂ → ℝ),
        IsPiecewiseConstantBoundaryData b' J' ∧ IsBoundedHarmonicExtension b' J' u' ∧
        IsFlowLineDriver c.κ b' J' (rootEntry r.1).1 c.P
          (fun ω => Chart.chartTransport hconf 1 0 (chiC c.κ) (c.h ω))
          (fun t ω => (futFam c r [] a 0 ω).1 t) (fun ω => (futFam c r [] a 0 ω).2) ∧
        IsCenteredCounterflowDriver c.κ c.P (fun ω => Chart.chartTransport hconf 1 0 (chiC c.κ) (c.h ω)) Wk ζk ∧
        IsBoundedHarmonicExtension (forceBoundaryData c.κ (flowLineRhoL c.κ b' J' 0 (rootEntry r.1).1)
          (flowLineRhoR c.κ b' J' 0 (rootEntry r.1).1) (flowLineXL b' J' 0) (flowLineXR b' J' 0))
          (forceJumpSet (flowLineXL b' J' 0) (flowLineXR b' J' 0)) uθ ∧
        (∀ᵐ ω ∂c.P, ζk ω = ⊤ ∧ IsGeneratingTrace (fun t => Wk t ω) ⊤ (γ ω)) ∧
        (∀ᵐ ω ∂c.P, ζk ω = ⊤ ∧ Continuous (ℓ ω) ∧ StrictMono (ℓ ω) ∧
          range (ℓ ω) = {q : ℝ≥0 | (q : ℝ≥0∞) < firstTipTime infinitySourceChart (fun s => c.W s ω)
            {((rootPt r.1 : ℝ) : ℂ)}} ∧
          ∀ (q : ℝ≥0) (z : ℂ), ((Chart.id.recenter (rootPt r.1)).trans infinitySourceChart).tipAt
            (fun s => Wk s ω) q z ↔ infinitySourceChart.tipAt (fun s => c.W s ω) (ℓ ω q) z) ∧
        (∀ᵐ ω ∂c.P, ∀ t₀ : ℝ≥0, ℓ ω t₀ = c.s → ((historyTime c r [] : ℝ≥0) : ℝ≥0∞) < (futFam c r [] a 0 ω).2 →
          γ ω t₀ ∈ H → 0 < historyTime c r [] →
          ((historyTime c r [] : ℝ≥0) : ℝ≥0∞) < firstContactTime (fun u => (GW2aSingle.chosenTrace
              (fun t ω => (futFam c r [] a 0 ω).1 t) (fun ω => (futFam c r [] a 0 ω).2) ω u : OnePoint ℂ))
            ((fun u => sphereInv (γ ω u : OnePoint ℂ)) '' Icc 0 t₀) →
          ∀ w : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w (H \ (Chart.id.recenter (rootPt r.1)).1 ''
              (schedUnionX c r [] a (historyTime c r []) 0 ω ∩ ((Chart.id.recenter (rootPt r.1)).dom : Set ℂ))) →
            (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (Chart.id.recenter (rootPt r.1)).1 ''
                (schedUnionX c r [] a (historyTime c r []) 0 ω ∩ ((Chart.id.recenter (rootPt r.1)).dom : Set ℂ)) →
              (Chart.chartTransport hconf 1 0 (chiC c.κ) (g ω + smoothDist upperHalfPlaneOpens u₀) -
                smoothDist upperHalfPlaneOpens u') φ = ∫ z, w z * φ z) →
            UnionFormAt c.κ (rootEntry r.1).1 b' J' c' Wk ζk (fun t ω => (futFam c r [] a 0 ω).1 t) uθ ω t₀
              (historyTime c r []) w (H \ (Chart.id.recenter (rootPt r.1)).1 ''
                (schedUnionX c r [] a (historyTime c r []) 0 ω ∩ ((Chart.id.recenter (rootPt r.1)).dom : Set ℂ)))) ∧
        ∀ᵐ ω ∂c.P, ∀ t₀ : ℝ≥0, ℓ ω t₀ = c.s → (0 : ℝ≥0∞) < (futFam c r [] a 0 ω).2 →
          ∀ w : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w (H \ (Chart.id.recenter (rootPt r.1)).1 ''
              (retSet c.s c.W c.ζ ω ∩ ((Chart.id.recenter (rootPt r.1)).dom : Set ℂ))) →
            (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (Chart.id.recenter (rootPt r.1)).1 ''
                (retSet c.s c.W c.ζ ω ∩ ((Chart.id.recenter (rootPt r.1)).dom : Set ℂ)) →
              (Chart.chartTransport hconf 1 0 (chiC c.κ) (g₁ ω + smoothDist upperHalfPlaneOpens u₀) -
                smoothDist upperHalfPlaneOpens u') φ = ∫ z, w z * φ z) →
            RetFormAt c.κ (rootEntry r.1).1 c' Wk ζk uθ ω t₀ w (H \ (Chart.id.recenter (rootPt r.1)).1 ''
              (retSet c.s c.W c.ζ ω ∩ ((Chart.id.recenter (rootPt r.1)).dom : Set ℂ))) := by
  classical
  have hx0 : 0 ≤ rootPt r.1 := hroot.elim (fun h => h.ge) fun h => (GW2Sched.pos_of_mem_lowerArcRoots h).le
  set x := rootPt r.1 with hx
  set T : ℝ≥0 := historyTime c r [] with hT
  set L := futureProgram c r [] a with hL
  set spec := futSpec c r [] a with hspec
  set E := futFam c r [] a with hEdef
  set cL := Chart.id.recenter x with hcLdef
  have hconf : cL.IsConformal := Chart.isConformal_id.recenter x
  have hhm : Measurable c.h := c.hh.1
  have hh0 := Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData c.hh hu₀
  have hS : IsStagedHistory c.κ c.b c.jumps c.P c.h spec E := isStagedHistory_canonFam c.hκ c.h12p c.βA c.c₀
    (specAngle spec) (specDelta spec) h13 c.hβA c.hb c.hc₀J c.hc₀ c.hh (spec := spec) rfl
    (isFlowProg_spec x true L) (specDelta_ne_top _)
  have hreg : ∀ j ω, IsRegularDriver (E j ω) := fun j ω =>
    isRegularDriver_canonDrive c.hκ c.h12p c.βA c.c₀ x (specAngle spec) (specDelta spec) (c.h ω) j
  have hR := stagedPiecesRegular_of_regular h13 c.hκ c.hb hS hreg
  -- the launch at index `0`
  have hlen : 0 < spec.2.2.length := by
    rw [GW2Schedule.length_scheduleProgram]
    simp [futureProgram, historyProgram, schedOf]
  have hθ0 : specAngle spec 0 = (rootEntry r.1).1 := (specAngle_specDelta_nil c r a).1
  have hl0 : ∀ ω₀, (ExplState.run c.κ c.b c.jumps spec (fun j => E j ω₀) (0 + 1)).2.2.2.1 0 =
      some (cL, (rootEntry r.1).1) := by
    intro ω₀
    have h := (launches_run_gw2 (κ := c.κ) (b := c.b) (jumps := c.jumps) (spec := spec) rfl
      (isFlowProg_spec x true L) (specDelta_ne_top _) (fun j => E j ω₀) hlen).1 (allSucc_zero _ _)
    have hc := GW2Later.eq_recenter_of_launch_zero h
    rw [hc, hθ0] at h
    exact h
  have hdc : IsDomainChart H cL := SB.Lf.isDomainChart_recenter isDomainChart_id x
  have hdomH : (cL.dom : Set ℂ) = H := coe_dom_recenter_id x
  have hliftc : ContinuousOn cL.2.2 cL.dom := by
    rw [hdomH]
    exact hdc.continuousOn_lift
  have hlift : InnerProductSpace.HarmonicOnNhd cL.2.2 cL.dom := by
    rw [hdomH]
    exact harmonicOnNhd_lift_of_isDomainChart hdc
  have hℓint : LocallyIntegrableOn (fun w => cL.2.2 (cL.2.1 w)) H :=
    hdc.continuousOn_lift_inv.locallyIntegrableOn QuantumZipper.isOpen_H.measurableSet
  -- the flow line at index `0`, under `P`
  obtain ⟨ω₀, hst⟩ := (hS.2.2.2 0).exists
  have hν0 : condExpKernel c.P (pastSigma c.κ c.b c.jumps spec E 0) ω₀ = c.P := by
    rw [GW1.pastSigma_zero_eq_bot]
    exact GW1.condExpKernel_bot_apply c.P ω₀
  obtain ⟨b', J', h', hb', htr', hfl'⟩ := hst cL (rootEntry r.1).1 (hl0 ω₀)
  rw [hν0] at hfl'
  have hh'eq : h' = fun ω => Chart.chartTransport hconf 1 0 (chiC c.κ) (c.h ω) :=
    funext fun ω => (htr' ω).eq_chartTransport hconf hℓint
  rw [hh'eq] at hfl' htr'
  -- BR4a's datum
  have hBR4a := BR4aIn.br4aStatement_of_thm12_thm13 h12 h13 h12₀ h13₀
  obtain ⟨Wk, ζk, ℓ, hcfk, -, hd⟩ := hasLaunchPairEq_zero hBR4a h13 h13₀ c.hκ c.hκ4 c.hb c.hh c.hcf c.hζ hroot
    E ω₀ cL (rootEntry r.1).1 (hl0 ω₀) _ htr'
  rw [hν0] at hcfk hd
  simp only [contactSet_zero] at hd
  have hζk : ∀ᵐ ω ∂c.P, ζk ω = ⊤ := hd.mono fun _ h => h.1
  have hG' := GW2aPiece.isGFFWithBoundaryData_of_isFlowLineDriver c.hκ hb' hfl'
  obtain ⟨u', hu', -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension hb'
  have huθ := LocalExt.isBoundedHarmonicExtension_bheAt c.κ (flowLineRhoL c.κ b' J' 0 (rootEntry r.1).1)
    (flowLineRhoR c.κ b' J' 0 (rootEntry r.1).1) (flowLineXL b' J' 0) (flowLineXR b' J' 0)
  -- the union's kernel
  have hTO : Sec5.Prop513Schedule.TimeOrdered 0 (historyProgram c r []) :=
    Gm.timeOrdered_of_pairwise_lt (List.pairwise_singleton _ _)
  have hloc₀ := isHistoryAvoidanceLocal_stgFX h12 h13 c r [] a hTO hu₀ 0
  obtain ⟨g, 𝓜, hg, -, hker𝓜, -, hB𝓜, -, hMh, hkP, -⟩ := exists_kernel_union_meanX c r [] a hu₀.1 hh0 0 hloc₀
  have hV : ∀ (B : Ω → Set ℂ), ∀ᵐ ω ∂c.P, IsOpen ((H \ B ω) \ (cL.dom : Set ℂ)) := fun B =>
    Eventually.of_forall fun ω => by
      rw [hdomH, Set.sdiff_eq_empty.2 sdiff_subset]
      exact isOpen_empty
  obtain ⟨hmh', hk', hloc'⟩ := launch_kernel_of (κ := c.κ) hhm hconf hliftc hlift 𝓜 hB𝓜
    (schedUnionX_subset_isOpen c r [] a T 0) (hV _) hMh hkP hu'.1
  -- the retained set's kernel
  obtain ⟨b'', J'', h'', hb'', hTr, hcf⟩ := c.hcf
  obtain ⟨uh, huh⟩ := Sec7.StripSysField.exists_isBoundedHarmonicExtension_forceBoundaryData c.κ
    (flowLineRhoL c.κ c.b c.jumps 0 0) (flowLineRhoR c.κ c.b c.jumps 0 0) (flowLineXL c.b c.jumps 0)
    (flowLineXR c.b c.jumps 0)
  have huh' : IsBoundedHarmonicExtension (Supp8.Q3Chain.cfData c.κ c.b c.jumps)
      (forceJumpSet (flowLineXL c.b c.jumps 0) (flowLineXR c.b c.jumps 0)) uh := huh
  have heqU : EqOn uh u₀ H := fun z hz => by
    have h1 := eqOn_flowLine_harmonicExtension c.hκ c.hb 0 0 hu₀ huh hz
    simpa only [Complex.ofReal_zero, add_zero, zero_mul] using h1
  have hcen : centredField c.h uh = centredField c.h u₀ := by
    funext ω
    simp only [centredField]
    rw [WangWu.smoothDist_congr huh.1.continuousOn hu₀.1.continuousOn heqU]
  have hh0' : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (centredField c.h uh) c.P := by
    rw [hcen]
    exact hh0
  have htr0 : ∀ ω, IsTranslateAddConst 0 (0 * chiC c.κ) (c.h ω) (c.h ω) := fun ω =>
    Sec5.CfGiven.isTranslateAddConst_zero_mul_self (c.h ω) (chiC c.κ)
  obtain ⟨ℋr, -, hrec, hretm, -, hlocR⟩ :=
    exists_retained_marks_rec_gw2 (θ := 0) h12 h13 c.hκ c.hb c.hh hb'' hTr hcf htr0 huh' huh hh0' c.s
  rw [hcen] at hlocR
  have hretm' : Measurable[mΩ, hittingSigma] (retSet c.s c.W c.ζ) := hretm.mono ℋr.2 le_rfl
  have hretc : ∀ ω, retSet c.s c.W c.ζ ω ⊆ H ∧ IsOpen (H \ retSet c.s c.W c.ζ ω) :=
    fun ω => ⟨Supp8.GB6LMean.retSet_subset_H c.s c.W c.ζ ω, Supp8.GB6LMean.isOpen_H_diff_retSet c.s c.W c.ζ ω⟩
  obtain ⟨g₁, 𝓜₀, hg₁, hℋ𝓜₀, hR𝓜₀, hMh₀, hk₀P⟩ := exists_kernel_of_local hhm hu₀.1 hh0 hretm' hretc ℋr hlocR
  obtain ⟨hmh₀', hk₀', hloc₀'⟩ := launch_kernel_of (κ := c.κ) hhm hconf hliftc hlift 𝓜₀ hR𝓜₀ hretc (hV _) hMh₀
    hk₀P hu'.1
  -- the localizing event
  have hI : MeasurableSet[𝓜.1 ⊔ Ito.nullSets c.P] (gapPt c r) :=
    le_sup_left (a := 𝓜.1) _ (hker𝓜 _ (measurableSet_gapEvent (fun q => measurable_cfRead_kerMarks c r [] a 0 q)
      (fun _ => measurable_const) c.s 0))
  have hcfR : ∀ q, Measurable[ℋr.1] fun ω => cfRead c ω q := fun q => by
    have hpath : Measurable fun y : RecData => fun u : ℝ≥0 => rdrv y u :=
      measurable_pi_iff.2 fun u => Exist.StagedLaw.measurable_rdrv_apply (u : ℝ)
    exact (LP.measurable_traceAt q).comp (hpath.comp hrec)
  have hI₀ : MeasurableSet[𝓜₀.1 ⊔ Ito.nullSets c.P] (gapPt c r) :=
    le_sup_left (a := 𝓜₀.1) _ (hℋ𝓜₀ _ (measurableSet_gapEvent hcfR (fun _ => measurable_const) c.s 0))
  -- the launch sets: measurable, open complements
  have hLm : Measurable[𝓜.1, hittingSigma]
      (fun ω => cL.1 '' (schedUnionX c r [] a T 0 ω ∩ (cL.dom : Set ℂ))) := by
    have e : (fun ω => cL.1 '' (schedUnionX c r [] a T 0 ω ∩ (cL.dom : Set ℂ))) =
        fun ω => H \ chartPre cL (H \ schedUnionX c r [] a T 0 ω) := funext fun ω => launchUnion_eq hconf _
    rw [e]
    exact measurable_launch hconf hB𝓜
  have hLc : ∀ ω, cL.1 '' (schedUnionX c r [] a T 0 ω ∩ (cL.dom : Set ℂ)) ⊆ H ∧
      IsOpen (H \ cL.1 '' (schedUnionX c r [] a T 0 ω ∩ (cL.dom : Set ℂ))) := by
    intro ω
    rw [launchUnion_eq hconf]
    refine ⟨sdiff_subset, ?_⟩
    rw [sdiff_sdiff_cancel_left (chartPre_subset_H _ _)]
    exact isOpen_chartPre hconf (schedUnionX_subset_isOpen c r [] a T 0 ω).2
  have hLm₀ : Measurable[𝓜₀.1, hittingSigma]
      (fun ω => cL.1 '' (retSet c.s c.W c.ζ ω ∩ (cL.dom : Set ℂ))) := by
    have e : (fun ω => cL.1 '' (retSet c.s c.W c.ζ ω ∩ (cL.dom : Set ℂ))) =
        fun ω => H \ chartPre cL (H \ retSet c.s c.W c.ζ ω) := funext fun ω => launchUnion_eq hconf _
    rw [e]
    exact measurable_launch hconf hR𝓜₀
  have hLc₀ : ∀ ω, cL.1 '' (retSet c.s c.W c.ζ ω ∩ (cL.dom : Set ℂ)) ⊆ H ∧
      IsOpen (H \ cL.1 '' (retSet c.s c.W c.ζ ω ∩ (cL.dom : Set ℂ))) := by
    intro ω
    rw [launchUnion_eq hconf]
    refine ⟨sdiff_subset, ?_⟩
    rw [sdiff_sdiff_cancel_left (chartPre_subset_H _ _)]
    exact isOpen_chartPre hconf (hretc ω).2
  -- the seed
  by_cases hseed : ForceWord.ThresholdCondition (flowLineRhoL c.κ b' J' 0 (rootEntry r.1).1)
    (flowLineRhoR c.κ b' J' 0 (rootEntry r.1).1) 0 (flowLineXL b' J' 0) (flowLineXR b' J' 0)
  · -- the root piece dies at once: nothing to prove
    have hfl'' := hfl'
    obtain ⟨Xθ', 𝓕', VL', VR', B', htr'', hC⟩ := hfl''
    have hz := Coupling.ae_zeta_eq_zero_of_threshold hC.1 hseed
    obtain ⟨-, -, c', -, -, -, -, γ, -, -, -, -, hcomp, -⟩ :=
      GW2Olm.counterflow_pack h13 c.hκ c.hκ4 hb' hG' hcfk hζk
    refine ⟨g, g₁, hg, hg₁, hconf, b', J', u', Wk, ζk, ℓ, c', γ, _, hb', hu', hfl', hcfk, huθ, hcomp, hd, ?_, ?_⟩
    · filter_upwards [hz] with ω hzω t₀ _ htζ
      rw [hzω] at htζ
      exact absurd htζ not_lt_zero
    · filter_upwards [hz] with ω hzω t₀ _ hpos
      rw [hzω] at hpos
      exact absurd hpos (lt_irrefl 0)
  have hcfreg := GW2Later.ae_counterflow_regular h13 c.hκ c.hcf c.hζ
  have hWkreg := GW2Later.ae_counterflow_regular h13 c.hκ hcfk hζk
  have hvisP := ae_mem_tipSet_root h13 h13₀ c r hroot
  have hfut := Gm.ae_futureJoined_trace h13 c r
  have hpr := hR.ae_pieceRegular
  have hW' : ∀ᵐ ω ∂c.P, Continuous (fun t => c.W t ω) ∧ c.W 0 ω = 0 ∧
      ∃ γ' : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => c.W t ω) ⊤ γ' := by
    filter_upwards [hcfreg] with ω hω
    obtain ⟨γ', hγ', hc, h0, -⟩ := hω
    exact ⟨hc, h0, γ', hγ'⟩
  have hα := (GW2aSingle.ae_chosenTrace h13 c.hκ hfl').mono fun _ h => h.1
  have hid : cL.1 '' H = H := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      change 0 < (w - (x : ℂ)).im
      have : 0 < w.im := hw
      simpa using this
    · intro hz
      refine ⟨z + (x : ℂ), ?_, ?_⟩
      · change 0 < (z + (x : ℂ)).im
        have : 0 < z.im := hz
        simpa using this
      · change z + (x : ℂ) - (x : ℂ) = z
        ring
  -- the sets at a sample
  have hsets : ∀ᵐ ω ∂c.P, ∀ t₀ : ℝ≥0, ℓ ω t₀ = c.s →
      cL.1 '' (retSet c.s c.W c.ζ ω ∩ (cL.dom : Set ℂ)) = invHull (fun q : ℝ => Wk q.toNNReal ω) (t₀ : ℝ) ∧
      (oldSuccess c r [] ω → cL.1 '' (schedUnionX c r [] a T 0 ω ∩ (cL.dom : Set ℂ)) =
        invHull (fun q : ℝ => Wk q.toNNReal ω) (t₀ : ℝ) ∪
          fwdHull (fun q : ℝ => schedW c r [] a q.toNNReal ω) (T : ℝ)) := by
    filter_upwards [hcfreg, c.hζ, hd, hWkreg, hvisP] with ω hcfω hζω hdω hWkω hvisω t₀ ht₀
    obtain ⟨γ', hγ', hW'c, hW'0, -⟩ := hcfω
    obtain ⟨γk, hγk, hWkc, hWk0, -⟩ := hWkω
    obtain ⟨-, hℓc, hℓm, hℓr, hiff⟩ := hdω
    exact launch_sets_root0X c r a hx0 hW'c hW'0 hγ' (by rw [hζω]; exact ENNReal.coe_lt_top) hWkc hWk0 hγk hℓc hℓm
      hℓr (fun hxp => vis_of_mem_tipSet hγ' hW'c hW'0 (hvisω hxp)) hiff ht₀
  -- on the gap event the clock reaches `s`
  have hclk : ∀ᵐ ω ∂c.P, (ω ∈ gapPt c r ↔ ∃ t₀ : ℝ≥0, ℓ ω t₀ = c.s) := by
    filter_upwards [hcfreg, c.hζ, hd] with ω hcfω hζω hdω
    obtain ⟨γ', hγ', hW'c, hW'0, -⟩ := hcfω
    obtain ⟨-, -, -, hℓr, -⟩ := hdω
    rw [mem_gapPt_iff c r hγ' hW'c hW'0 (by rw [hζω]; exact ENNReal.coe_lt_top),
      ← lt_firstTipTime_pt_iff hγ' hW'c hW'0]
    constructor
    · intro h
      have hm : c.s ∈ range (ℓ ω) := by rw [hℓr]; exact h
      exact hm
    · rintro ⟨t₀, ht₀⟩
      have hm : c.s ∈ range (ℓ ω) := ⟨t₀, ht₀⟩
      rw [hℓr] at hm
      exact hm
  have hsub : ∀ᵐ ω ∂c.P, ω ∈ gapPt c r → ∃ t₀ : ℝ≥0, ℓ ω t₀ = c.s ∧ ∀ v ≤ t₀, ∀ u ≤ T,
      (u : ℝ≥0∞) < (E 0 ω).2 → invHull (fun q : ℝ => Wk q.toNNReal ω) (v : ℝ) ∪
        fwdHull (fun q : ℝ => (E 0 ω).1 q.toNNReal) (u : ℝ) ⊆
          cL.1 '' (schedUnionX c r [] a T 0 ω ∩ (cL.dom : Set ℂ)) := by
    filter_upwards [hclk, hsets, hfut, hpr, hWkreg] with ω hclkω hsetsω hfutω hprω hWkω hgap
    obtain ⟨t₀, ht₀⟩ := hclkω.1 hgap
    obtain ⟨γk, hγk, hWkc, hWk0, -⟩ := hWkω
    refine ⟨t₀, ht₀, fun v hv u hu huζ => ?_⟩
    by_cases hold : oldSuccess c r [] ω
    · rw [(hsetsω t₀ ht₀).2 hold]
      obtain ⟨hgood, -⟩ := hfutω [] a hold
      have hc0 := stopDrv_cont_of_oldSuccess c r [] a hold hprω 0 (by simp [curIdx])
      rw [fwdHull_root_eq c r a hold hgood hc0 (hreg 0 ω) hu]
      exact union_subset_union (GW2Omx.invHull_mono (by exact_mod_cast hv))
        (QuantumZipper.fwdHull_mono.1 (by exact_mod_cast hu))
    · have hBH : schedUnionX c r [] a T 0 ω = H := by
        simp only [schedUnionX, schedHullX, hold, ↓reduceIte]
        exact union_eq_right.2 (GW2Shr.invHull_subset_H (continuous_rdrv _) c.s.coe_nonneg)
      rw [hBH, hdomH, inter_self, hid]
      exact union_subset (GW2Shr.invHull_subset_H (hWkc.comp continuous_real_toNNReal) v.coe_nonneg)
        (Exist.fwdHull_subset_H u.coe_nonneg)
  have heq : ∀ᵐ ω ∂c.P, ∀ t₀ : ℝ≥0, ℓ ω t₀ = c.s → (T : ℝ≥0∞) < (E 0 ω).2 → ω ∈ gapPt c r ∧
      cL.1 '' (schedUnionX c r [] a T 0 ω ∩ (cL.dom : Set ℂ)) =
        invHull (fun q : ℝ => Wk q.toNNReal ω) (t₀ : ℝ) ∪ fwdHull (fun q : ℝ => (E 0 ω).1 q.toNNReal) (T : ℝ) := by
    filter_upwards [hclk, hsets, hfut, hpr] with ω hclkω hsetsω hfutω hprω t₀ ht₀ hTζ
    have hold : oldSuccess c r [] ω := (oldSuccess_nil_iff c r a ω).2 hTζ
    obtain ⟨hgood, -⟩ := hfutω [] a hold
    have hc0 := stopDrv_cont_of_oldSuccess c r [] a hold hprω 0 (by simp [curIdx])
    refine ⟨hclkω.2 ⟨t₀, ht₀⟩, ?_⟩
    rw [(hsetsω t₀ ht₀).2 hold, fwdHull_root_eq c r a hold hgood hc0 (hreg 0 ω) le_rfl]
  have hsub₀ : ∀ᵐ ω ∂c.P, ω ∈ gapPt c r → ∃ t₀ : ℝ≥0, ℓ ω t₀ = c.s ∧ ∀ v ≤ t₀,
      invHull (fun q : ℝ => Wk q.toNNReal ω) (v : ℝ) ⊆ cL.1 '' (retSet c.s c.W c.ζ ω ∩ (cL.dom : Set ℂ)) := by
    filter_upwards [hclk, hsets] with ω hclkω hsetsω hgap
    obtain ⟨t₀, ht₀⟩ := hclkω.1 hgap
    refine ⟨t₀, ht₀, fun v hv => ?_⟩
    rw [(hsetsω t₀ ht₀).1]
    exact GW2Omx.invHull_mono (by exact_mod_cast hv)
  have heq₀ : ∀ᵐ ω ∂c.P, ∀ t₀ : ℝ≥0, ℓ ω t₀ = c.s → ω ∈ gapPt c r ∧
      cL.1 '' (retSet c.s c.W c.ζ ω ∩ (cL.dom : Set ℂ)) = invHull (fun q : ℝ => Wk q.toNNReal ω) (t₀ : ℝ) := by
    filter_upwards [hclk, hsets] with ω hclkω hsetsω t₀ ht₀
    exact ⟨hclkω.2 ⟨t₀, ht₀⟩, (hsetsω t₀ ht₀).1⟩
  obtain ⟨Xθ, c', γ, -, hcomp, hmain, hmain₀⟩ := kernel_launch_mean_pair h12 h13 c.hκ c.hκ4 hb' hG' hu' hcfk hW'
    (GW1P.hasProperBdryExt_recenter_id x) hd c.s hfl' hα hseed huθ 𝓜 hLm hLc hloc' hmh' hk' hI T hsub heq 𝓜₀
    hLm₀ hLc₀ hloc₀' hmh₀' hk₀' hI₀ hsub₀ heq₀
  exact ⟨g, g₁, hg, hg₁, hconf, b', J', u', Wk, ζk, ℓ, c', γ, _, hb', hu', hfl', hcfk, huθ, hcomp, hd, hmain,
    hmain₀.mono fun ω h t₀ ht₀ _ => h t₀ ht₀⟩

end InteractingSLE.Theorem14.GW2Kx
