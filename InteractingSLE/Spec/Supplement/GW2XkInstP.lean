/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2XkInst
import InteractingSLE.Spec.Supplement.GW2XkKerF
import InteractingSLE.Spec.Supplement.GW2OmxInstP

/-!
# The root-`x` kernel port (D38): the launch means at stage time `t` and at the stage start, at a root `x`

Packet PROVE-GW2-GEOM2, round 11 (STAGEMEAN's `GW2Omx.ae_launch_form_pair` at a root `x ∈ {0} ∪ lowerArcRoots`).
`ae_launch_formX` together with the stage-start form: one launch datum (`ae_launch_kernel_famX`) and one kernel word
(`GW2Omx.kernel_launch_mean_pair`) for RELDET's root-`x` unions at `t` and at `0`. As in `ae_launch_formX`, the
counterflow's visit to `x` (BR4a's input) replaces any protected arc.

* **`ae_launch_form_pairX`**.
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

namespace InteractingSLE.Theorem14.GW2Xk

open GW2Omx Restart Exist Exist.Staged Exist.StagedLaw WholeField LocalSets GW2TipSystem GW2TipSystem.RootC24
  GW2TipSystem.RootJ31 GW2Schedule GW2Tip GW2Sdi GW2Rd GW2Olm Supp8 Supp8.GB6 Restart.MarkovChart

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **The launch means at stage time `t` and at the stage start, at the actual schedule from a root `x`**
(`ae_launch_formX` with the stage-start retained form `RetFormAt`, for the same launch datum and kernel word;
STAGEMEAN's `GW2Omx.ae_launch_form_pair` at `x ∈ {0} ∪ lowerArcRoots`). -/
theorem ae_launch_form_pairX (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h13₀ : Exist.Theorem13Statement.{0}) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (hroot : rootPt r.1 = 0 ∨ rootPt r.1 ∈ lowerArcRoots c.κ c.b c.jumps)
    (hord : (historyProgram c r l).Pairwise (fun p q => p.2 < q.2))
    {u₀ : ℂ → ℝ} (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh0 : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (centredField c.h u₀) c.P) (t : ℝ≥0)
    (htcap : t < candidateCap c r a)
    (hloc : IsHistoryAvoidanceLocal (stgF c r l a t) (schedUnionX c r l a (historyTime c r l) t)
      (centredField c.h u₀) c.P)
    (hloc₀ : IsHistoryAvoidanceLocal (stgF c r l a 0) (schedUnionX c r l a (historyTime c r l) 0)
      (centredField c.h u₀) c.P) :
    ∃ g g₀ : Ω → DistOn upperHalfPlaneOpens,
      IsLocalSetMean (schedUnionX c r l a (historyTime c r l) t) (centredField c.h u₀) c.P g ∧
      IsLocalSetMean (schedUnionX c r l a (historyTime c r l) 0) (centredField c.h u₀) c.P g₀ ∧
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
          (∀ᵐ ω ∂(condExpKernel c.P (pastG c r l a) ω₀), ∀ t₀ : ℝ≥0, ℓ ω t₀ = c.s →
            (t : ℝ≥0∞) < (futFam c r l a (curIdx c r l) ω).2 → γ ω t₀ ∈ H → 0 < t →
            ((t : ℝ≥0) : ℝ≥0∞) < firstContactTime (fun u => (GW2aSingle.chosenTrace
                (fun t ω => (futFam c r l a (curIdx c r l) ω).1 t) (fun ω => (futFam c r l a (curIdx c r l) ω).2)
                ω u : OnePoint ℂ))
              ((fun u => sphereInv (γ ω u : OnePoint ℂ)) '' Icc 0 t₀) →
            ∀ w : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w (H \ launchUnionX c r l a cL t ω) →
              (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ launchUnionX c r l a cL t ω →
                (Chart.chartTransport hconf 1 0 (chiC c.κ) (g ω + smoothDist upperHalfPlaneOpens u₀) -
                  smoothDist upperHalfPlaneOpens u') φ = ∫ z, w z * φ z) →
              UnionFormAt c.κ θ b' J' c' Wk ζk (fun t ω => (futFam c r l a (curIdx c r l) ω).1 t) uθ ω t₀ t w
                (H \ launchUnionX c r l a cL t ω)) ∧
          ∀ᵐ ω ∂(condExpKernel c.P (pastG c r l a) ω₀), ∀ t₀ : ℝ≥0, ℓ ω t₀ = c.s →
            (0 : ℝ≥0∞) < (futFam c r l a (curIdx c r l) ω).2 →
            ∀ w : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w (H \ launchUnionX c r l a cL 0 ω) →
              (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ launchUnionX c r l a cL 0 ω →
                (Chart.chartTransport hconf 1 0 (chiC c.κ) (g₀ ω + smoothDist upperHalfPlaneOpens u₀) -
                  smoothDist upperHalfPlaneOpens u') φ = ∫ z, w z * φ z) →
              RetFormAt c.κ θ c' Wk ζk uθ ω t₀ w (H \ launchUnionX c r l a cL 0 ω) := by
  classical
  obtain ⟨g, 𝓜, hg, -, hker𝓜, -, hB𝓜, -, hMh, -, hkerν⟩ := exists_kernel_union_meanX c r l a hu₀ hh0 t hloc
  obtain ⟨g₀, 𝓜₀, hg₀, -, hker𝓜₀, -, hB𝓜₀, -, hMh₀, -, hkerν₀⟩ :=
    exists_kernel_union_meanX c r l a hu₀ hh0 0 hloc₀
  refine ⟨g, g₀, hg, hg₀, ?_⟩
  have hTO : Sec5.Prop513Schedule.TimeOrdered 0 (historyProgram c r l) := Gm.timeOrdered_of_pairwise_lt hord
  have hx0 : 0 ≤ rootPt r.1 := hroot.elim (fun h => h.ge) fun h => (GW2Sched.pos_of_mem_lowerArcRoots h).le
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
  filter_upwards [ae_launch_kernel_famX h13 c r l a hTO (fun i : Bool => cond i t 0) (fun i => cond i 𝓜 𝓜₀)
      (M := fun i => cond i (fun ω => g ω + smoothDist upperHalfPlaneOpens u₀)
        (fun ω => g₀ ω + smoothDist upperHalfPlaneOpens u₀))
      (fun i => by cases i; exacts [hB𝓜₀, hB𝓜]) (fun i => by cases i; exacts [hMh₀, hMh])
      (fun i => by cases i; exacts [hkerν₀, hkerν]), ae_ae_launch_cur h13 c r l a,
    CondDriverBridge.ae_ae_run_eq_of_le (P := c.P) (κ := c.κ) (b := c.b) (jumps := c.jumps) spec
      (fun j _ ω => hreg j ω) h𝒢 le_rfl,
    KernelTower.ae_ae_condExpKernel_of_ae h𝒢 (GW2Later.ae_counterflow_regular h13 c.hκ c.hcf c.hζ),
    KernelTower.ae_ae_condExpKernel_of_ae h𝒢 c.hζ,
    KernelTower.ae_ae_condExpKernel_of_ae h𝒢 (Gm.ae_futureJoined_trace h13 c r),
    KernelTower.ae_ae_condExpKernel_of_ae h𝒢 (ae_schedW_trace c r l a h13),
    KernelTower.ae_ae_condExpKernel_of_ae h𝒢 (ae_contactSet_eq_traceX h13 c r l a hTO),
    KernelTower.ae_ae_condExpKernel_of_ae h𝒢 hR.ae_pieceRegular,
    KernelTower.ae_ae_condExpKernel_of_ae h𝒢 (ae_mem_tipSet_root h13 h13₀ c r hroot)]
    with ω₀ hK hcur hrun hcfν hζν hfutν hschν hconν hprν hvisν hdat cL θ hl
  obtain ⟨hconf, b', J', u', hb', hu', hfl', htrX, hext, hlc, hlh, hfam⟩ := hK cL θ hl
  obtain ⟨hmh', hk', hloc'⟩ := hfam true
  obtain ⟨hmh₀', hk₀', hloc₀'⟩ := hfam false
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
    refine ⟨hconf, b', J', u', Wk, ζk, ℓ, c', γ, _, hlc, hlh, hext, hb', hu', hfl', hcfk, huθ, hcomp, hd, ?_, ?_⟩
    · filter_upwards [hz] with ω hzω t₀ _ htζ
      rw [hzω] at htζ
      exact absurd htζ not_lt_zero
    · filter_upwards [hz] with ω hzω t₀ _ hpos
      rw [hzω] at hpos
      exact absurd hpos (lt_irrefl 0)
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
    have hsub : ∀ᵐ ω ∂ν, ω ∈ noContactX c r l a → ∃ t₀ : ℝ≥0, ℓ ω t₀ = c.s ∧ ∀ v ≤ t₀, ∀ u ≤ t,
        (u : ℝ≥0∞) < (E k ω).2 → Supp8.Q3Rel.invHull (fun q : ℝ => Wk q.toNNReal ω) (v : ℝ) ∪
          fwdHull (fun q : ℝ => (E k ω).1 q.toNNReal) (u : ℝ) ⊆ launchUnionX c r l a cL t ω := by
      filter_upwards [hcur, hrun, hcfν, hζν, hfutν, hschν, hconν, hprν, hvisν, hd, hWkreg]
        with ω hcurω hrunω hcfω hζω hfutω hschω hconω hprω hvisω hdω hWkω hnc
      obtain ⟨hlω, hold⟩ := hcurω cL θ hl
      obtain ⟨γ', hγ', hW'c, hW'0, -⟩ := hcfω
      obtain ⟨γk, hγk, hWkc, hWk0, -⟩ := hWkω
      obtain ⟨-, hℓc, hℓm, hℓr, hiff⟩ := hdω
      rw [hcont ω hrunω, hconω hold] at hℓr
      obtain ⟨hgood, -⟩ := hfutω l a hold
      exact launch_sub_of_noContactX c r l a hx0 hord t ω hold hgood hlω (stopDrv_cont_of_oldSuccess c r l a hold hprω)
        hconf hext htcap hWkc hWk0 hγk hW'c hW'0 hγ' (by rw [hζω]; exact ENNReal.coe_lt_top) hschω.1
        (hsch ω hold).1 (hsch ω hold).2 hℓc hℓm hℓr
        (fun hxp => vis_of_mem_tipSet hγ' hW'c hW'0 (hvisω hxp)) hiff hnc
    have heq : ∀ᵐ ω ∂ν, ∀ t₀ : ℝ≥0, ℓ ω t₀ = c.s → (t : ℝ≥0∞) < (E k ω).2 → ω ∈ noContactX c r l a ∧
        launchUnionX c r l a cL t ω = Supp8.Q3Rel.invHull (fun q : ℝ => Wk q.toNNReal ω) (t₀ : ℝ) ∪
          fwdHull (fun q : ℝ => (E k ω).1 q.toNNReal) (t : ℝ) := by
      filter_upwards [hcur, hrun, hcfν, hζν, hfutν, hschν, hconν, hprν, hvisν, hd, hWkreg]
        with ω hcurω hrunω hcfω hζω hfutω hschω hconω hprω hvisω hdω hWkω t₀ ht₀ htζ
      obtain ⟨hlω, hold⟩ := hcurω cL θ hl
      obtain ⟨γ', hγ', hW'c, hW'0, -⟩ := hcfω
      obtain ⟨γk, hγk, hWkc, hWk0, -⟩ := hWkω
      obtain ⟨-, hℓc, hℓm, hℓr, hiff⟩ := hdω
      rw [hcont ω hrunω, hconω hold] at hℓr
      obtain ⟨hgood, -⟩ := hfutω l a hold
      exact launch_eq_of_clockX c r l a hx0 hord t ω hold hgood hlω (stopDrv_cont_of_oldSuccess c r l a hold hprω)
        hconf hext htcap hWkc hWk0 hγk hW'c hW'0 hγ' (by rw [hζω]; exact ENNReal.coe_lt_top) hschω.1
        (hsch ω hold).1 (hsch ω hold).2 hℓc hℓm hℓr
        (fun hxp => vis_of_mem_tipSet hγ' hW'c hW'0 (hvisω hxp)) hiff ht₀ htζ
    have hU : launchUnionX c r l a cL t = fun ω => H \ chartPre cL (H \ schedUnionX c r l a (historyTime c r l) t ω) :=
      funext fun ω => launchUnion_eq hconf _
    have hLm : Measurable[𝓜.1, hittingSigma] (launchUnionX c r l a cL t) := by
      rw [hU]
      exact measurable_launch hconf hB𝓜
    have hLc : ∀ ω, launchUnionX c r l a cL t ω ⊆ H ∧ IsOpen (H \ launchUnionX c r l a cL t ω) := by
      intro ω
      rw [hU]
      refine ⟨sdiff_subset, ?_⟩
      rw [sdiff_sdiff_cancel_left (chartPre_subset_H _ _)]
      exact isOpen_chartPre hconf (schedUnionX_subset_isOpen c r l a (historyTime c r l) t ω).2
    have hI : MeasurableSet[𝓜.1 ⊔ Ito.nullSets ν] (noContactX c r l a) :=
      le_sup_left (a := 𝓜.1) _ (hker𝓜 _ (measurableSet_noContactX c r l a t))
    have hW' : ∀ᵐ ω ∂ν, Continuous (fun t => c.W t ω) ∧ c.W 0 ω = 0 ∧
        ∃ γ' : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => c.W t ω) ⊤ γ' := by
      filter_upwards [hcfν] with ω hω
      obtain ⟨γ', hγ', hc, h0, -⟩ := hω
      exact ⟨hc, h0, γ', hγ'⟩
    have hα := (GW2aSingle.ae_chosenTrace h13 c.hκ hfl').mono fun _ h => h.1
    have hpos : ∀ᵐ ω ∂ν, (0 : ℝ≥0∞) < (E k ω).2 := SB.Retain.ae_lifetime_pos_of_seed_admissible hfl' hseed
    have hsub₀ : ∀ᵐ ω ∂ν, ω ∈ noContactX c r l a → ∃ t₀ : ℝ≥0, ℓ ω t₀ = c.s ∧ ∀ v ≤ t₀,
        Supp8.Q3Rel.invHull (fun q : ℝ => Wk q.toNNReal ω) (v : ℝ) ⊆ launchUnionX c r l a cL 0 ω := by
      filter_upwards [hcur, hrun, hcfν, hζν, hfutν, hschν, hconν, hprν, hvisν, hd, hWkreg, hpos]
        with ω hcurω hrunω hcfω hζω hfutω hschω hconω hprω hvisω hdω hWkω hposω hnc
      obtain ⟨hlω, hold⟩ := hcurω cL θ hl
      obtain ⟨γ', hγ', hW'c, hW'0, -⟩ := hcfω
      obtain ⟨γk, hγk, hWkc, hWk0, -⟩ := hWkω
      obtain ⟨-, hℓc, hℓm, hℓr, hiff⟩ := hdω
      rw [hcont ω hrunω, hconω hold] at hℓr
      obtain ⟨hgood, -⟩ := hfutω l a hold
      obtain ⟨t₀, ht₀, hall⟩ := launch_sub_of_noContactX c r l a hx0 hord 0 ω hold hgood hlω
        (stopDrv_cont_of_oldSuccess c r l a hold hprω) hconf hext (candidateCap_pos c r a) hWkc hWk0 hγk hW'c hW'0
        hγ' (by rw [hζω]; exact ENNReal.coe_lt_top) hschω.1 (hsch ω hold).1 (hsch ω hold).2 hℓc hℓm hℓr
        (fun hxp => vis_of_mem_tipSet hγ' hW'c hW'0 (hvisω hxp)) hiff hnc
      exact ⟨t₀, ht₀, fun v hv => subset_union_left.trans (hall v hv 0 le_rfl (by simpa using hposω))⟩
    have heq₀ : ∀ᵐ ω ∂ν, ∀ t₀ : ℝ≥0, ℓ ω t₀ = c.s → ω ∈ noContactX c r l a ∧
        launchUnionX c r l a cL 0 ω = Supp8.Q3Rel.invHull (fun q : ℝ => Wk q.toNNReal ω) (t₀ : ℝ) := by
      filter_upwards [hcur, hrun, hcfν, hζν, hfutν, hschν, hconν, hprν, hvisν, hd, hWkreg, hpos]
        with ω hcurω hrunω hcfω hζω hfutω hschω hconω hprω hvisω hdω hWkω hposω t₀ ht₀
      obtain ⟨hlω, hold⟩ := hcurω cL θ hl
      obtain ⟨γ', hγ', hW'c, hW'0, -⟩ := hcfω
      obtain ⟨γk, hγk, hWkc, hWk0, -⟩ := hWkω
      obtain ⟨-, hℓc, hℓm, hℓr, hiff⟩ := hdω
      rw [hcont ω hrunω, hconω hold] at hℓr
      obtain ⟨hgood, -⟩ := hfutω l a hold
      obtain ⟨hnc, hL⟩ := launch_eq_of_clockX c r l a hx0 hord 0 ω hold hgood hlω
        (stopDrv_cont_of_oldSuccess c r l a hold hprω) hconf hext (candidateCap_pos c r a) hWkc hWk0 hγk hW'c hW'0
        hγ' (by rw [hζω]; exact ENNReal.coe_lt_top) hschω.1 (hsch ω hold).1 (hsch ω hold).2 hℓc hℓm hℓr
        (fun hxp => vis_of_mem_tipSet hγ' hW'c hW'0 (hvisω hxp)) hiff ht₀
        (by simpa using hposω)
      refine ⟨hnc, ?_⟩
      rw [hL, fwdHull_zero_of_regular (hreg k ω) hposω, union_empty]
    have hU₀ : launchUnionX c r l a cL 0 = fun ω => H \ chartPre cL (H \ schedUnionX c r l a (historyTime c r l) 0 ω) :=
      funext fun ω => launchUnion_eq hconf _
    have hLm₀ : Measurable[𝓜₀.1, hittingSigma] (launchUnionX c r l a cL 0) := by
      rw [hU₀]
      exact measurable_launch hconf hB𝓜₀
    have hLc₀ : ∀ ω, launchUnionX c r l a cL 0 ω ⊆ H ∧ IsOpen (H \ launchUnionX c r l a cL 0 ω) := by
      intro ω
      rw [hU₀]
      refine ⟨sdiff_subset, ?_⟩
      rw [sdiff_sdiff_cancel_left (chartPre_subset_H _ _)]
      exact isOpen_chartPre hconf (schedUnionX_subset_isOpen c r l a (historyTime c r l) 0 ω).2
    have hI₀ : MeasurableSet[𝓜₀.1 ⊔ Ito.nullSets ν] (noContactX c r l a) :=
      le_sup_left (a := 𝓜₀.1) _ (hker𝓜₀ _ (measurableSet_noContactX c r l a 0))
    obtain ⟨Xθ, c', γ, -, hcomp, hmain, hmain₀⟩ := kernel_launch_mean_pair h12 h13 c.hκ c.hκ4 hb' hG' hu' hcfk hW'
      hext hd c.s hfl' hα hseed huθ 𝓜 hLm hLc hloc' hmh' hk' hI t hsub heq 𝓜₀ hLm₀ hLc₀ hloc₀' hmh₀' hk₀' hI₀ hsub₀
      heq₀
    exact ⟨hconf, b', J', u', Wk, ζk, ℓ, c', γ, _, hlc, hlh, hext, hb', hu', hfl', hcfk, huθ, hcomp, hd, hmain,
      hmain₀.mono fun ω h t₀ ht₀ _ => h t₀ ht₀⟩

end InteractingSLE.Theorem14.GW2Xk
