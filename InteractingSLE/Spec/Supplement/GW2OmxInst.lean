/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2OmxSamp
import InteractingSLE.Spec.Supplement.GW2OmxSched
import InteractingSLE.Spec.Supplement.GW2OmxRun
import InteractingSLE.Spec.Supplement.GW2OmxContact
import InteractingSLE.Spec.Supplement.GW2OmxKer
import InteractingSLE.Spec.Supplement.GW2GmJoin
import InteractingSLE.Spec.Supplement.GB6PastStep
import InteractingSLE.Spec.Supplement.GW2aSingle
import InteractingSLE.Spec.Coupling.Assembly11Provider

/-!
# GW2's open lines: the launch mean of the current stage at the actual schedule (root `0`)

Packet PROVE-GW2-STAGEMEAN, R120 round (per-sample assembly). `GW2Omx.kernel_launch_mean` instantiated at the actual
schedule under the conditional kernel `ν = condExpKernel P pastG ω₀`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open LQGMetric (DistOn TestOn)
open QuantumZipper (H chiC fwdHull)
open SupercriticalConformalCovariance.GM24 (smoothDist)

universe u

namespace InteractingSLE.Theorem14.GW2Omx

open Restart Exist Exist.Staged Exist.StagedLaw WholeField LocalSets GW2TipSystem GW2TipSystem.RootC24
  GW2TipSystem.RootJ31 GW2Schedule GW2Tip GW2Sdi GW2Rd GW2Olm Supp8 Supp8.GB6 Restart.MarkovChart

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]

/-- **On success, the stopped drivers of the future program up to the current piece are continuous from `0`.** -/
theorem stopDrv_cont_of_oldSuccess (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q))
    (a : ℕ) {ω : Ω} (hold : oldSuccess c r l ω)
    (hpr : ∀ (k : ℕ) (c' : Chart) (θ : ℝ), (ExplState.run c.κ c.b c.jumps (futSpec c r l a)
        (fun j => futFam c r l a j ω) (k + 1)).2.2.2.1 k = some (c', θ) →
      GW1P.PieceRegular (futFam c r l a k ω).1 (min (instrTime (futSpec c r l a) k) (futFam c r l a k ω).2)) :
    ∀ j < curIdx c r l + 1, Continuous (stopDrv (specDelta (futSpec c r l a) j) (futFam c r l a j ω)) ∧
      stopDrv (specDelta (futSpec c r l a) j) (futFam c r l a j ω) 0 = 0 := by
  intro j hj
  set L := futureProgram c r l a with hL
  set spec := futSpec c r l a with hspec
  set k := curIdx c r l with hk
  have hlenL : L.length = k + 1 := by rw [hL, futureProgram, List.length_append, List.length_singleton]
  have hlen : spec.2.2.length = k + 1 := (GW2Schedule.length_scheduleProgram 0 L).trans hlenL
  have hs : AllSucc (specDelta spec) (fun i => futFam c r l a i ω) k :=
    Gm.allSucc_future_of_oldSuccess c r l a ω hold
  have hsj : AllSucc (specDelta spec) (fun i => futFam c r l a i ω) j := hs.mono (by omega)
  have hl := (launches_run_gw2 (κ := c.κ) (b := c.b) (jumps := c.jumps) (spec := spec) rfl
    (isFlowProg_spec (rootPt r.1) true L) (specDelta_ne_top _) (fun i => futFam c r l a i ω)
    (show j < spec.2.2.length by omega)).1 hsj
  have hreg := hpr j _ _ hl
  have hinstr : instrTime spec j = specDelta spec j := by
    have hi := isFlowProg_spec (rootPt r.1) true L j (show j < spec.2.2.length by omega)
    unfold instrTime
    rw [hi]
  rw [hinstr] at hreg
  exact GW2Later.continuous_stopDrv hreg

variable [StandardBorelSpace Ω]

/-- **The launch mean of the current stage at the actual schedule** (root `0`, strictly time-ordered history, stage
time `t` below the candidate's cap): there is a local-set mean `g` of the instance's union such that, for `P`-a.e.
`ω₀` with GB6's datum, at a launch `(cL, θ)`, under `ν = condExpKernel P pastG ω₀`, almost surely, wherever the
clock reaches `s` at `t₀` and the piece is alive at `t` (and the kernel form's own conditions hold), every harmonic
representative of `cL(g + u₀) − u'` off the launch image of the union is the kernel union's harmonic form. -/
theorem ae_launch_form (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)
    (hr0 : rootPt r.1 = 0) (hord : (historyProgram c r l).Pairwise (fun p q => p.2 < q.2))
    {u₀ : ℂ → ℝ} (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh0 : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (centredField c.h u₀) c.P) (t : ℝ≥0)
    (htcap : t < candidateCap c r a)
    (hloc : IsHistoryAvoidanceLocal (stgF c r l a t) (schedUnionS c r l a t) (centredField c.h u₀) c.P) :
    ∃ g : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean (schedUnionS c r l a t) (centredField c.h u₀) c.P g ∧
      ∀ᵐ ω₀ ∂c.P, HasLaunchPairEq c.κ c.b c.jumps c.P c.h c.W (futSpec c r l a) (futFam c r l a) (curIdx c r l) ω₀ →
        ∀ (cL : Chart) (θ : ℝ), curLaunch c r l a ω₀ = some (cL, θ) →
        ∃ (hconf : cL.IsConformal) (b' : ℝ → ℝ) (J' : Finset ℝ) (u' : ℂ → ℝ) (Wk : ℝ≥0 → Ω → ℝ)
          (ζk : Ω → ℝ≥0∞) (ℓ : Ω → ℝ≥0 → ℝ≥0) (c' : BoundaryWord) (γ : Ω → ℝ≥0 → ℂ) (uθ : ℂ → ℝ),
          ContinuousOn cL.2.2 cL.dom ∧ InnerProductSpace.HarmonicOnNhd cL.2.2 cL.dom ∧ GW1P.HasProperBdryExt cL ∧
          IsPiecewiseConstantBoundaryData b' J' ∧ IsBoundedHarmonicExtension b' J' u' ∧
          IsFlowLineDriver c.κ b' J' θ (condExpKernel c.P (pastG c r l a) ω₀)
            (fun ω => Chart.chartTransport hconf 1 0 (chiC c.κ) (c.h ω))
            (fun t ω => (futFam c r l a (curIdx c r l) ω).1 t) (fun ω => (futFam c r l a (curIdx c r l) ω).2) ∧
          IsCenteredCounterflowDriver c.κ (condExpKernel c.P (pastG c r l a) ω₀)
            (fun ω => Chart.chartTransport hconf 1 0 (chiC c.κ) (c.h ω)) Wk ζk ∧
          IsBoundedHarmonicExtension (forceBoundaryData c.κ (flowLineRhoL c.κ b' J' 0 θ)
            (flowLineRhoR c.κ b' J' 0 θ) (flowLineXL b' J' 0) (flowLineXR b' J' 0))
            (forceJumpSet (flowLineXL b' J' 0) (flowLineXR b' J' 0)) uθ ∧
          (∀ᵐ ω ∂(condExpKernel c.P (pastG c r l a) ω₀), ζk ω = ⊤ ∧
            IsGeneratingTrace (fun t => Wk t ω) ⊤ (γ ω)) ∧
          (∀ᵐ ω ∂(condExpKernel c.P (pastG c r l a) ω₀), ζk ω = ⊤ ∧ Continuous (ℓ ω) ∧ StrictMono (ℓ ω) ∧
            range (ℓ ω) = {q : ℝ≥0 | (q : ℝ≥0∞) < firstTipTime infinitySourceChart (fun s => c.W s ω)
              (contactSet c.κ c.b c.jumps (futSpec c r l a) (fun j => futFam c r l a j ω₀) (curIdx c r l))} ∧
            ∀ (q : ℝ≥0) (z : ℂ), (cL.trans infinitySourceChart).tipAt (fun s => Wk s ω) q z ↔
              infinitySourceChart.tipAt (fun s => c.W s ω) (ℓ ω q) z) ∧
          ∀ᵐ ω ∂(condExpKernel c.P (pastG c r l a) ω₀), ∀ t₀ : ℝ≥0, ℓ ω t₀ = c.s →
            (t : ℝ≥0∞) < (futFam c r l a (curIdx c r l) ω).2 → γ ω t₀ ∈ H → 0 < t →
            ((t : ℝ≥0) : ℝ≥0∞) < firstContactTime (fun u => (GW2aSingle.chosenTrace
                (fun t ω => (futFam c r l a (curIdx c r l) ω).1 t) (fun ω => (futFam c r l a (curIdx c r l) ω).2)
                ω u : OnePoint ℂ))
              ((fun u => sphereInv (γ ω u : OnePoint ℂ)) '' Icc 0 t₀) →
            ∀ w : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w (H \ launchUnion c r l a cL t ω) →
              (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ launchUnion c r l a cL t ω →
                (Chart.chartTransport hconf 1 0 (chiC c.κ) (g ω + smoothDist upperHalfPlaneOpens u₀) -
                  smoothDist upperHalfPlaneOpens u') φ = ∫ z, w z * φ z) →
              UnionFormAt c.κ θ b' J' c' Wk ζk (fun t ω => (futFam c r l a (curIdx c r l) ω).1 t) uθ ω t₀ t w
                (H \ launchUnion c r l a cL t ω) := by
  classical
  obtain ⟨g, 𝓜, hg, -, hker𝓜, -, hB𝓜, -, hMh, -, hkerν⟩ := exists_kernel_union_mean c r l a hu₀ hh0 t hloc
  refine ⟨g, hg, ?_⟩
  have hTO : Sec5.Prop513Schedule.TimeOrdered 0 (historyProgram c r l) := Gm.timeOrdered_of_pairwise_lt hord
  set x := rootPt r.1 with hx
  set L := futureProgram c r l a with hL
  set spec := futSpec c r l a with hspec
  set E := futFam c r l a with hEdef
  set k := curIdx c r l with hkdef
  have hS : IsStagedHistory c.κ c.b c.jumps c.P c.h spec E := isStagedHistory_canonFam c.hκ c.h12p c.βA c.c₀
    (specAngle spec) (specDelta spec) h13 c.hβA c.hb c.hc₀J c.hc₀ c.hh (spec := spec) rfl
    (isFlowProg_spec x true L) (specDelta_ne_top _)
  have hreg : ∀ j ω, IsRegularDriver (E j ω) := fun j ω =>
    isRegularDriver_canonDrive c.hκ c.h12p c.βA c.c₀ x (specAngle spec) (specDelta spec) (c.h ω) j
  have hR := stagedPiecesRegular_of_regular h13 c.hκ c.hb hS hreg
  have h𝒢 : pastG c r l a ≤ mΩ := hS.2.1 k
  filter_upwards [ae_launch_kernel h13 c r l a hr0 hTO t 𝓜 hB𝓜 hMh hkerν, ae_ae_launch_cur h13 c r l a,
    CondDriverBridge.ae_ae_run_eq_of_le (P := c.P) (κ := c.κ) (b := c.b) (jumps := c.jumps) spec
      (fun j _ ω => hreg j ω) h𝒢 le_rfl,
    KernelTower.ae_ae_condExpKernel_of_ae h𝒢 (GW2Later.ae_counterflow_regular h13 c.hκ c.hcf c.hζ),
    KernelTower.ae_ae_condExpKernel_of_ae h𝒢 c.hζ,
    KernelTower.ae_ae_condExpKernel_of_ae h𝒢 (Gm.ae_futureJoined_trace h13 c r),
    KernelTower.ae_ae_condExpKernel_of_ae h𝒢 (ae_schedW_trace c r l a h13),
    KernelTower.ae_ae_condExpKernel_of_ae h𝒢 (ae_contactSet_eq_trace h13 c r l a hr0 hTO),
    KernelTower.ae_ae_condExpKernel_of_ae h𝒢 hR.ae_pieceRegular]
    with ω₀ hK hcur hrun hcfν hζν hfutν hschν hconν hprν hdat cL θ hl
  obtain ⟨hconf, b', J', u', hb', hu', hfl', hmh', hk', hloc', htrX, hext, hlc, hlh⟩ := hK cL θ hl
  set ν := condExpKernel c.P (pastG c r l a) ω₀ with hν
  set X : Ω → DistOn upperHalfPlaneOpens := fun ω => Chart.chartTransport hconf 1 0 (chiC c.κ) (c.h ω) with hX
  obtain ⟨Wk, ζk, ℓ, hcfk, -, hd⟩ := hdat cL θ hl X htrX
  have hζk : ∀ᵐ ω ∂ν, ζk ω = ⊤ := hd.mono fun _ h => h.1
  have hG' := GW2aPiece.isGFFWithBoundaryData_of_isFlowLineDriver c.hκ hb' hfl'
  have huθ := LocalExt.isBoundedHarmonicExtension_bheAt c.κ (flowLineRhoL c.κ b' J' 0 θ)
    (flowLineRhoR c.κ b' J' 0 θ) (flowLineXL b' J' 0) (flowLineXR b' J' 0)
  by_cases hseed : ForceWord.ThresholdCondition (flowLineRhoL c.κ b' J' 0 θ) (flowLineRhoR c.κ b' J' 0 θ) 0
    (flowLineXL b' J' 0) (flowLineXR b' J' 0)
  · -- the piece dies at once: nothing to prove
    have hfl'' := hfl'
    obtain ⟨Xθ', 𝓕', VL', VR', B', htr'', hC⟩ := hfl''
    have hz := Coupling.ae_zeta_eq_zero_of_threshold hC.1 hseed
    obtain ⟨-, -, c', -, -, -, -, γ, -, -, -, -, hcomp, -⟩ :=
      GW2Olm.counterflow_pack h13 c.hκ c.hκ4 hb' hG' hcfk hζk
    refine ⟨hconf, b', J', u', Wk, ζk, ℓ, c', γ, _, hlc, hlh, hext, hb', hu', hfl', hcfk, huθ, hcomp, hd, ?_⟩
    filter_upwards [hz] with ω hzω t₀ _ htζ
    rw [hzω] at htζ
    exact absurd htζ not_lt_zero
  · have hcont : ∀ ω, ExplState.run c.κ c.b c.jumps spec (fun j => E j ω) k =
        ExplState.run c.κ c.b c.jumps spec (fun j => E j ω₀) k →
        contactSet c.κ c.b c.jumps spec (fun j => E j ω₀) k = contactSet c.κ c.b c.jumps spec (fun j => E j ω) k := by
      intro ω h
      unfold contactSet
      rw [h]
    have hWkreg := GW2Later.ae_counterflow_regular h13 c.hκ hcfk hζk
    have hsch : ∀ ω, oldSuccess c r l ω → Continuous (fun u => schedW c r l a u ω) ∧ schedW c r l a 0 ω = 0 := by
      intro ω hold
      simp only [schedW, hold, ite_true]
      exact Gm.continuous_futureJoined c r l a ω
    have hsub : ∀ᵐ ω ∂ν, ω ∈ noContact c r l a → ∃ t₀ : ℝ≥0, ℓ ω t₀ = c.s ∧ ∀ v ≤ t₀, ∀ u ≤ t,
        (u : ℝ≥0∞) < (E k ω).2 → Supp8.Q3Rel.invHull (fun q : ℝ => Wk q.toNNReal ω) (v : ℝ) ∪
          fwdHull (fun q : ℝ => (E k ω).1 q.toNNReal) (u : ℝ) ⊆ launchUnion c r l a cL t ω := by
      filter_upwards [hcur, hrun, hcfν, hζν, hfutν, hschν, hconν, hprν, hd, hWkreg]
        with ω hcurω hrunω hcfω hζω hfutω hschω hconω hprω hdω hWkω hnc
      obtain ⟨hlω, hold⟩ := hcurω cL θ hl
      obtain ⟨γ', hγ', hW'c, hW'0, -⟩ := hcfω
      obtain ⟨γk, hγk, hWkc, hWk0, -⟩ := hWkω
      obtain ⟨-, hℓc, hℓm, hℓr, hiff⟩ := hdω
      rw [hcont ω hrunω, hconω hold] at hℓr
      obtain ⟨hgood, -⟩ := hfutω l a hold
      exact launch_sub_of_noContact c r l a hr0 hord t ω hold hgood hlω (stopDrv_cont_of_oldSuccess c r l a hold hprω)
        hconf hext htcap hWkc hWk0 hγk hW'c hW'0 hγ' (by rw [hζω]; exact ENNReal.coe_lt_top) hschω.1
        (hsch ω hold).1 (hsch ω hold).2 hℓc hℓm hℓr hiff hnc
    have heq : ∀ᵐ ω ∂ν, ∀ t₀ : ℝ≥0, ℓ ω t₀ = c.s → (t : ℝ≥0∞) < (E k ω).2 → ω ∈ noContact c r l a ∧
        launchUnion c r l a cL t ω = Supp8.Q3Rel.invHull (fun q : ℝ => Wk q.toNNReal ω) (t₀ : ℝ) ∪
          fwdHull (fun q : ℝ => (E k ω).1 q.toNNReal) (t : ℝ) := by
      filter_upwards [hcur, hrun, hcfν, hζν, hfutν, hschν, hconν, hprν, hd, hWkreg]
        with ω hcurω hrunω hcfω hζω hfutω hschω hconω hprω hdω hWkω t₀ ht₀ htζ
      obtain ⟨hlω, hold⟩ := hcurω cL θ hl
      obtain ⟨γ', hγ', hW'c, hW'0, -⟩ := hcfω
      obtain ⟨γk, hγk, hWkc, hWk0, -⟩ := hWkω
      obtain ⟨-, hℓc, hℓm, hℓr, hiff⟩ := hdω
      rw [hcont ω hrunω, hconω hold] at hℓr
      obtain ⟨hgood, -⟩ := hfutω l a hold
      exact launch_eq_of_clock c r l a hr0 hord t ω hold hgood hlω (stopDrv_cont_of_oldSuccess c r l a hold hprω)
        hconf hext htcap hWkc hWk0 hγk hW'c hW'0 hγ' (by rw [hζω]; exact ENNReal.coe_lt_top) hschω.1
        (hsch ω hold).1 (hsch ω hold).2 hℓc hℓm hℓr hiff ht₀ htζ
    have hU : launchUnion c r l a cL t = fun ω => H \ chartPre cL (H \ schedUnionS c r l a t ω) :=
      funext fun ω => launchUnion_eq hconf _
    have hLm : Measurable[𝓜.1, hittingSigma] (launchUnion c r l a cL t) := by
      rw [hU]
      exact measurable_launch hconf hB𝓜
    have hLc : ∀ ω, launchUnion c r l a cL t ω ⊆ H ∧ IsOpen (H \ launchUnion c r l a cL t ω) := by
      intro ω
      rw [hU]
      refine ⟨sdiff_subset, ?_⟩
      rw [sdiff_sdiff_cancel_left (chartPre_subset_H _ _)]
      exact isOpen_chartPre hconf (schedUnionS_subset_isOpen c r l a t ω).2
    have hI : MeasurableSet[𝓜.1 ⊔ Ito.nullSets ν] (noContact c r l a) :=
      le_sup_left (a := 𝓜.1) _ (hker𝓜 _ (measurableSet_noContact c r l a t))
    have hW' : ∀ᵐ ω ∂ν, Continuous (fun t => c.W t ω) ∧ c.W 0 ω = 0 ∧
        ∃ γ' : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => c.W t ω) ⊤ γ' := by
      filter_upwards [hcfν] with ω hω
      obtain ⟨γ', hγ', hc, h0, -⟩ := hω
      exact ⟨hc, h0, γ', hγ'⟩
    have hα := (GW2aSingle.ae_chosenTrace h13 c.hκ hfl').mono fun _ h => h.1
    obtain ⟨Xθ, c', γ, -, hcomp, hmain⟩ := kernel_launch_mean h12 h13 c.hκ c.hκ4 hb' hG' hu' hcfk hW' hext hd c.s
      hfl' hα hseed huθ 𝓜 hLm hLc hloc' hmh' hk' hI t hsub heq
    exact ⟨hconf, b', J', u', Wk, ζk, ℓ, c', γ, _, hlc, hlh, hext, hb', hu', hfl', hcfk, huθ, hcomp, hd, hmain⟩

end InteractingSLE.Theorem14.GW2Omx
