/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2KxSamp
import InteractingSLE.Spec.Supplement.GW2PsmKerId
import InteractingSLE.Spec.Supplement.GW2XkInstP
import InteractingSLE.Spec.Supplement.GW2XkContact
import InteractingSLE.Spec.Supplement.GW2XkInst

/-!
# The stage reading at almost every sample of the conditional kernel, at a root `x`

Packet PROVE-GW2-GEOM2, round 14 (D49). STAGEMEAN's `GW2Psm.ae_kernel_identity_root0` at a root
`x = rootPt r.1 ∈ {0} ∪ lowerArcRoots`: round 11's root-`x` launch forms `GW2Xk.ae_launch_form_pairX`, the root-`x`
contact set `GW2Xk.ae_contactSet_eq_traceX` and the counterflow's visit to `x` (`GW2Xk.ae_mem_tipSet_root`, BR4a's
input), assembled at one sample by `sample_identity_rootX`.

* **`ae_kernel_identity_rootX`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn TestOn)
open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull logDerivFwd chiC)
open SupercriticalConformalCovariance.GM24 (smoothDist)

universe u

namespace InteractingSLE.Theorem14.GW2Kx

open Restart Exist Exist.Staged Exist.StagedLaw WholeField LocalSets GW2TipSystem GW2TipSystem.RootC24
  GW2TipSystem.RootJ31 GW2Schedule GW2Tip GW2Sdi GW2Rd GW2Olm Supp8 Supp8.GB6 Restart.MarkovChart GW2Omx
  MartChar.RealFlow GW2Psm GW2Xk
open Supp8.Q3Rel (invHull relLog)

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **The stage reading at almost every sample of the conditional kernel** (root `x`). -/
theorem ae_kernel_identity_rootX (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h13₀ : Exist.Theorem13Statement.{0})
    (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)
    (hroot : rootPt r.1 = 0 ∨ rootPt r.1 ∈ lowerArcRoots c.κ c.b c.jumps) (hord : (historyProgram c r l).Pairwise (fun
      p q => p.2 < q.2)) (hs0 : 0 < c.s)
    {u₀ : ℂ → ℝ} (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh0 : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (centredField c.h u₀) c.P) (t : ℝ≥0) (htpos : 0 < t)
    (htcap : t < candidateCap c r a)
    (hloc : IsHistoryAvoidanceLocal (stgF c r l a t) (schedUnionX c r l a (historyTime c r l) t) (centredField c.h u₀)
      c.P)
    (hloc₀ : IsHistoryAvoidanceLocal (stgF c r l a 0) (schedUnionX c r l a (historyTime c r l) 0) (centredField c.h
      u₀) c.P) :
    ∃ g g₀ : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean (schedUnionX c r l a (historyTime c r l) t) (centredField
        c.h u₀) c.P g ∧
      IsLocalSetMean (schedUnionX c r l a (historyTime c r l) 0) (centredField c.h u₀) c.P g₀ ∧
      ∀ᵐ ω₀ ∂c.P, HasLaunchPairEq c.κ c.b c.jumps c.P c.h c.W (futSpec c r l a) (futFam c r l a) (curIdx c r l) ω₀ →
        ∀ (cL : Chart) (θ : ℝ), curLaunch c r l a ω₀ = some (cL, θ) →
        ∀ᵐ ω ∂(condExpKernel c.P (pastG c r l a) ω₀),
          (t : ℝ≥0∞) < (futFam c r l a (curIdx c r l) ω).2 → c.α ω c.s ∈ H →
          (∀ v ∈ Icc 0 c.s, ∀ u ≤ historyTime c r l + t,
            c.α ω v * ((rootPt r.1 : ℂ) + schedTr c r l a ω u) + 1 ≠ 0) →
          ∀ (R : ℝ≥0 → ℝ) (A : ℝ≥0 → ℝ≥0) (a₀ : ℝ≥0), Continuous R → R 0 = 0 → A 0 = a₀ → (∀ u, a₀ ≤ A u) →
          Continuous A →
          (∀ u ≤ t, H \ schedUnionX c r l a (historyTime c r l) u ω =
            (GW2Rz.relChartX (rootPt r.1) c.s (cfRec c.s c.W c.ζ ω)).2.1 '' (H \ fwdHull (Ito.rpath R) (A u))) →
          ∀ (wP wP₀ : ℂ → ℝ) (σa : ℝ),
          InnerProductSpace.HarmonicOnNhd wP (H \ schedUnionX c r l a (historyTime c r l) t ω) →
          (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ schedUnionX c r l a (historyTime c r l) t ω →
            g ω φ = ∫ z, wP z * φ z) →
          InnerProductSpace.HarmonicOnNhd wP₀ (H \ schedUnionX c r l a (historyTime c r l) 0 ω) →
          (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ schedUnionX c r l a (historyTime c r l) 0 ω →
            g₀ ω φ = ∫ z, wP₀ z * φ z) →
          ∀ {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (U₀ U : ℂ → ℝ)
            (hβ : ℝ), (∀ i, xL i ≤ 0) → (∀ j, 0 ≤ xR j) →
          IsBoundedHarmonicExtension (forceBoundaryData c.κ ρL ρR xL xR) (forceJumpSet xL xR) U₀ →
          (∀ y ∈ ((stgChart (GW2Rz.relChartX (rootPt r.1) c.s (cfRec c.s c.W c.ζ ω)) R a₀).dom : Set ℂ),
            wP₀ y + u₀ y + σa + chiC c.κ * (stgChart (GW2Rz.relChartX (rootPt r.1) c.s (cfRec c.s c.W c.ζ ω)) R
                a₀).2.2 y =
              U₀ ((stgChart (GW2Rz.relChartX (rootPt r.1) c.s (cfRec c.s c.W c.ζ ω)) R a₀).1 y)) →
          (∃ B : ℝ, ∀ y, B < y → y ∉ forceJumpSet xL xR → forceBoundaryData c.κ ρL ρR xL xR y = hβ) →
          sleLambda (16 / c.κ) - Real.pi * chiC c.κ + θ * chiC c.κ = hβ →
          IsBoundedHarmonicExtension
            (forceBoundaryData c.κ ρL ρR
              (fun i => -rightImg (fun s => -Ito.rpath (stgDrv R a₀) s) (-xL i) ((A t : ℝ) - a₀) -
                Ito.rpath (stgDrv R a₀) ((A t : ℝ) - a₀))
              (fun j => rightImg (Ito.rpath (stgDrv R a₀)) (xR j) ((A t : ℝ) - a₀) -
                Ito.rpath (stgDrv R a₀) ((A t : ℝ) - a₀)))
            (forceJumpSet
              (fun i => -rightImg (fun s => -Ito.rpath (stgDrv R a₀) s) (-xL i) ((A t : ℝ) - a₀) -
                Ito.rpath (stgDrv R a₀) ((A t : ℝ) - a₀))
              (fun j => rightImg (Ito.rpath (stgDrv R a₀)) (xR j) ((A t : ℝ) - a₀) -
                Ito.rpath (stgDrv R a₀) ((A t : ℝ) - a₀))) U →
          ∀ z ∈ H \ fwdHull (Ito.rpath (stgDrv R a₀)) ((A t : ℝ) - a₀),
            wP ((stgChart (GW2Rz.relChartX (rootPt r.1) c.s (cfRec c.s c.W c.ζ ω)) R a₀).2.1 z) +
                u₀ ((stgChart (GW2Rz.relChartX (rootPt r.1) c.s (cfRec c.s c.W c.ζ ω)) R a₀).2.1 z) + σa +
                chiC c.κ * (stgChart (GW2Rz.relChartX (rootPt r.1) c.s (cfRec c.s c.W c.ζ ω)) R a₀).2.2
                  ((stgChart (GW2Rz.relChartX (rootPt r.1) c.s (cfRec c.s c.W c.ζ ω)) R a₀).2.1 z) =
              couplingMean c.κ (Ito.rpath (stgDrv R a₀)) ((A t : ℝ) - a₀) U z := by
  classical
  obtain ⟨g, g₀, hg, hg₀, hform⟩ := ae_launch_form_pairX h12 h13 h13₀ c r l a hroot hord hu₀
    hh0 t htcap hloc hloc₀
  refine ⟨g, g₀, hg, hg₀, ?_⟩
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
  have hNRp := GW2Rd.counterflowNoReturn_of_thm13 h13 c.κ c.hκ c.hκ4 c.b c.jumps c.hb c.P c.h c.hh c.W c.ζ c.hcf
    c.hζ
  filter_upwards [hform, ae_isDomainChart_curLaunch h13 c r l a, ae_ae_launch_cur h13 c r l a,
    CondDriverBridge.ae_ae_run_eq_of_le (P := c.P) (κ := c.κ) (b := c.b) (jumps := c.jumps) spec
      (fun j _ ω => hreg j ω) h𝒢 le_rfl,
    KernelTower.ae_ae_condExpKernel_of_ae h𝒢 (GW2Later.ae_counterflow_regular h13 c.hκ c.hcf c.hζ),
    KernelTower.ae_ae_condExpKernel_of_ae h𝒢 c.hζ,
    KernelTower.ae_ae_condExpKernel_of_ae h𝒢 (Gm.ae_futureJoined_trace h13 c r),
    KernelTower.ae_ae_condExpKernel_of_ae h𝒢 (ae_schedW_trace c r l a h13),
    KernelTower.ae_ae_condExpKernel_of_ae h𝒢 (ae_contactSet_eq_traceX h13 c r l a hTO),
    KernelTower.ae_ae_condExpKernel_of_ae h𝒢 hR.ae_pieceRegular,
    KernelTower.ae_ae_condExpKernel_of_ae h𝒢 c.hα,
    KernelTower.ae_ae_condExpKernel_of_ae h𝒢 hNRp,
    KernelTower.ae_ae_condExpKernel_of_ae h𝒢 (ae_mem_tipSet_root h13 h13₀ c r hroot)]
    with ω₀ hF hdc hcur hrun hcfν hζν hfutν hschν hconν hprν hαν hNRν hvisν hdat cL θ hl
  obtain ⟨hconf, b', J', u', Wk, ζk, ℓ, c', γ, uθ, -, -, hext, hb', hu', hfl', hcfk, huθ, hcomp, hd, hmainT,
    hmain0⟩ := hF hdat cL θ hl
  have hcL := hdc cL θ hl
  set ν := condExpKernel c.P (pastG c r l a) ω₀ with hν
  have hζk : ∀ᵐ ω ∂ν, ζk ω = ⊤ := hd.mono fun _ h => h.1
  have hG' := GW2aPiece.isGFFWithBoundaryData_of_isFlowLineDriver c.hκ hb' hfl'
  have hWkreg := GW2Later.ae_counterflow_regular h13 c.hκ hcfk hζk
  have hNRk := GW2Rd.counterflowNoReturn_of_thm13 h13 c.κ c.hκ c.hκ4 b' J' hb' ν _ hG' Wk ζk hcfk hζk
  have hαc := GW2aSingle.ae_chosenTrace h13 c.hκ hfl'
  have hcont : ∀ ω, ExplState.run c.κ c.b c.jumps spec (fun j => E j ω) k =
      ExplState.run c.κ c.b c.jumps spec (fun j => E j ω₀) k →
      contactSet c.κ c.b c.jumps spec (fun j => E j ω₀) k = contactSet c.κ c.b c.jumps spec (fun j => E j ω) k := by
    intro ω h
    unfold contactSet
    rw [h]
  have hsch : ∀ ω, oldSuccess c r l ω → Continuous (fun u => schedW c r l a u ω) ∧ schedW c r l a 0 ω = 0 := by
    intro ω hold
    simp only [schedW, hold, ite_true]
    exact Gm.continuous_futureJoined c r l a ω
  filter_upwards [hcur, hrun, hcfν, hζν, hfutν, hschν, hconν, hprν, hαν, hNRν, hcomp, hd, hWkreg, hNRk, hαc,
    hmainT, hmain0, hvisν]
    with ω hcurω hrunω hcfω hζω hfutω hschω hconω hprω hαω hNRω hcompω hdω hWkω hNRkω hαcω hmTω hm0ω hvisω
    htζ hαs hnc R A a₀ hRc hR0 hA0 hAa hAc hshape wP wP₀ σa hwP hgP hwP₀ hgP₀ nL nR ρL ρR xL xR U₀ U hβ hxL hxR
    hU₀ hinst0 hfarβ hfar hU
  obtain ⟨hlω, hold⟩ := hcurω cL θ hl
  obtain ⟨-, -, hW'c, hW'0, -⟩ := hcfω
  obtain ⟨γk, -, hWkc, hWk0, -⟩ := hWkω
  obtain ⟨-, hℓc, hℓm, hℓr, hiff⟩ := hdω
  rw [hcont ω hrunω, hconω hold] at hℓr
  obtain ⟨hgood, -⟩ := hfutω l a hold
  have hc := stopDrv_cont_of_oldSuccess c r l a hold hprω
  have hx0 : 0 ≤ rootPt r.1 := hroot.elim (fun h => h.ge) fun h => (GW2Sched.pos_of_mem_lowerArcRoots h).le
  have hvis : 0 < rootPt r.1 → ∃ τ, (rootPt r.1 : ℂ) * c.α ω τ + 1 = 0 := fun hxp =>
    vis_of_mem_tipSet hαω hW'c hW'0 (hvisω hxp)
  exact sample_identity_rootX c r l a hx0 hord t htpos ω hold hgood hlω hc hcL hext htcap htζ (hreg k ω) hαcω.1
    hWkc hWk0 hcompω.1 hcompω.2 (fun q hq => hNRkω (γ ω) hcompω.2 q hq) hW'c hW'0 hαω
    (fun v hv => hNRω (c.α ω) hαω v hv) (by rw [hζω]; exact ENNReal.coe_lt_top) hs0 hαs hschω.1
    (hsch ω hold).1 (hsch ω hold).2 hℓc hℓm hℓr hvis hiff hnc hRc hR0 hA0 hAa hAc hshape hb' hu' huθ c' hu₀ hwP hgP hwP₀
    hgP₀ hmTω hm0ω ρL ρR hxL hxR hU₀ hinst0 hfarβ hfar hU

end InteractingSLE.Theorem14.GW2Kx
