/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RnExp
import InteractingSLE.Spec.Supplement.GW2PvDthE
import InteractingSLE.Spec.Supplement.GW2PuDth
import InteractingSLE.Spec.Supplement.GW2PuSmp
import InteractingSLE.Spec.Supplement.GW2RnForm
import InteractingSLE.Spec.Supplement.GW2RnRep
import InteractingSLE.Spec.Supplement.GW2RnSmp
import InteractingSLE.Spec.Supplement.GW2XkContact

/-!
# D46's death clause at a root `x ∈ {0} ∪ lowerArcRoots`, positive lifetime, datum form

Packet PROVE-GW2-STAGEMEAN, R124 round (D72). `GW2Pv.stageDeathExportXDP_root0` ported to the roots `x`, on ROOTX's
port of the export (`GW2Rn.stageKernelExportLD_rootX`) with ROOTX's substitution table: the root-`x` kernel form
`ae_launch_form0WX`, Claim(k) in the root-`x` chart (`ae_stage_repX`), the root-`x` shape and no-contact, the
counterflow's visit to `x` (`GW2Xk.ae_mem_tipSet_root`, `vis_of_mem_tipSet`); per sample `sample_export_rootXD` and
`sample_death_rootX`; the version agreement `GW2Pv.versions_agree_below` (chart-free).

* **`stageDeathExportXDP_rootX`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC fwdHull)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.GW2Pu

open Restart Exist Exist.Staged Exist.StagedLaw Sec7.PocketTraversal Supp8 Supp8.GB6 GW2Rd GW2TipSystem
  GW2TipSystem.RootC24 GW2TipSystem.RootJ31 GW2Rz GW2Rv GW2Sde GW2Sdh GW2Sdi GW2Schedule GW2Tip MartChar.RealFlow
  Sec5.CrossCond.StagedRepLater Sec5.Prop513Schedule Supp8.GB6.RelDrv Supp8.RelSafe GW2Nt GW2Nu Supp8.Q3Stop
  WholeField LocalSets GW2Rn GW2Nv

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **D46's death clause at a root `x ∈ {0} ∪ lowerArcRoots`, positive lifetime, with GB6's datum as a premise**
(`GW2Pv.StageDeathExportXDP`), for a version family with caps below the death clock, D27's exhaustion below a finite
death clock and the stop property of version `j` on the record event, from Claim(k) in the root-`x` chart and the word
map's far height. -/
theorem stageDeathExportXDP_rootX (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h13₀ : Exist.Theorem13Statement.{0}) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (hroot : rootPt r.1 = 0 ∨ rootPt r.1 ∈ lowerArcRoots c.κ c.b c.jumps)
    (hord : (historyProgram c r l).Pairwise (fun p q => p.2 < q.2)) (hs0 : 0 < c.s)
    {GT : Set Ω} (hGT : (∀ ω ∈ GT, PhysGoodX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α ω) ∧
      MeasurableSet GT ∧ (∀ᵐ ω ∂c.P, ω ∈ GT ↔ cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s))
    {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    (hA : IsRelVersionXA (rootPt r.1) c.s c.P c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α R V)
    (hV : ∀ ω, V ω ≠ ⊤) (ch : SchedChoice Ω) (hu₀ : IsBoundedHarmonicExtension c.b c.jumps ch.u₀)
    (hcount : (Set.range fun y => wordType c.κ (ch.β y)).Countable)
    (Rv : ℕ → ℝ≥0 → Ω → ℝ) (Vv : ℕ → Ω → ℝ≥0∞)
    (hAv : ∀ n, IsRelVersionXA (rootPt r.1) c.s c.P c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α (Rv n) (Vv n))
    (hVv : ∀ n ω, Vv n ω ≠ ⊤) (j : ℕ) (hRj : Rv j = R) (hVj : Vv j = V)
    (hE₀pos : ∀ᵐ ω ∂c.P, oldSuccess c r l ω → 0 < candLife c r l a ω →
      (schedInstSX c r l a GT hA ch).srecX c r l (rootPt r.1) ω ∈ ch.E₀)
    (hcaps : ∀ᵐ ω ∂c.P, cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s → oldSuccess c r l ω →
      0 < candLife c r l a ω → ∀ n, Vv n ω < deathClockX c r l a ω)
    (hD27 : ∀ᵐ ω ∂c.P, cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s → oldSuccess c r l ω →
      deathClockX c r l a ω < ⊤ → ∀ t : ℝ≥0,
      (t : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ω →
      ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ω) < deathClockX c r l a ω →
      ∀ᶠ n in atTop, ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ω) < Vv n ω)
    (hVd : ∀ᵐ ω ∂c.P, (schedInstSX c r l a GT hA ch).srecX c r l (rootPt r.1) ω ∈ (schedInstSX c r l a GT hA ch).E →
      V ω ≤ physClockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT
        (historyTime c r l + GW2Psm.candStop c r l a ω) ω)
    (hclaim : ∀ w : WordType, GW2Kx.ClaimAtX c r l a GT hA ch w)
    (hfar : ∀ w : WordType, ∀ᵐ ω ∂c.P, ω ∈ liveEvRec c.κ w ch.β (schedInstSX c r l a GT hA ch).E
        ((schedInstSX c r l a GT hA ch).srecX c r l (rootPt r.1)) →
      GW2Wm.FarR (ch.β ((schedInstSX c r l a GT hA ch).srecX c r l (rootPt r.1) ω))
        (sleLambda (16 / c.κ) - Real.pi * chiC c.κ + candAngle c r l a * chiC c.κ)) :
    GW2Pv.StageDeathExportXDP c r l a (schedInstSX c r l a GT hA ch) Rv Vv (rootPt r.1) := by
  classical
  have hx : (0 : ℝ) ≤ rootPt r.1 :=
    hroot.elim (fun h => h.ge) fun h => (GW2Sched.pos_of_mem_lowerArcRoots h).le
  set I := schedInstSX c r l a GT hA ch with hIdef
  have hTO : TimeOrdered 0 (historyProgram c r l) := Gm.timeOrdered_of_pairwise_lt hord
  have hh0 : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (centredField c.h ch.u₀) c.P :=
    isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData c.hh hu₀
  have hloc₀ := GW2Kx.isHistoryAvoidanceLocal_stgFX h12 h13 c r l a hTO hu₀ 0
  obtain ⟨g₀, hg₀, hform⟩ := ae_launch_form0WX h12 h13 h13₀ c r l a hroot hord hu₀.1 hh0 hloc₀
  have hv := hA.1.1
  have hρ := hA.1.2.choose_spec
  have hfin : ∀ᵐ ω ∂c.P, I.srecX c r l (rootPt r.1) ω ∈ I.E →
      stgStartMX (rootPt r.1) c.s c.W c.ζ I.W I.GT I.V I.T ω ≠ ⊤ :=
    Eventually.of_forall fun ω _ => ne_top_of_le_ne_top (hV ω) (min_le_right _ _)
  have hEgood := StageInst.E_good_of_recordX I hv hρ.2.1 hρ.2.2 inter_subset_right hfin
  have : Countable (Set.range fun y => wordType c.κ (ch.β y)) := hcount.to_subtype
  have hrep := ae_all_iff.2 fun w' : Set.range (fun y => wordType c.κ (ch.β y)) =>
    ae_stage_repX c r l a hx hs0 hGT hA hV ch hu₀ w'.1 (hclaim w'.1) hg₀
  have hfarall := ae_all_iff.2 fun w' : Set.range (fun y => wordType c.κ (ch.β y)) => hfar w'.1
  have hncP := GW2Kx.ae_noContact_rootX hGT.1 hs0 hx hv
  have hshP := GW2Kx.ae_shape_rootX c r l a hx hs0 hGT.1 hv
  have hshAll := ae_all_iff.2 fun n => GW2Kx.ae_shape_rootX c r l a hx hs0 hGT.1 (hAv n).1.1
  have hverAll := ae_all_iff.2 fun n => GW2Ru.versionAtX_of_isRelVersionX (hAv n).1.1
  -- the kernel setup
  set L := futureProgram c r l a with hL
  set spec := GW2Olm.futSpec c r l a with hspec
  set E := GW2Olm.futFam c r l a with hEdef
  set k := GW2Olm.curIdx c r l with hkdef
  have hS : IsStagedHistory c.κ c.b c.jumps c.P c.h spec E := isStagedHistory_canonFam c.hκ c.h12p c.βA c.c₀
    (specAngle spec) (specDelta spec) h13 c.hβA c.hb c.hc₀J c.hc₀ c.hh (spec := spec) rfl
    (isFlowProg_spec (rootPt r.1) true L) (specDelta_ne_top _)
  have hreg : ∀ j ω, IsRegularDriver (E j ω) := fun j ω =>
    isRegularDriver_canonDrive c.hκ c.h12p c.βA c.c₀ (rootPt r.1) (specAngle spec) (specDelta spec) (c.h ω) j
  have hR := stagedPiecesRegular_of_regular h13 c.hκ c.hb hS hreg
  have h𝒢 : GW2Olm.pastG c r l a ≤ mΩ := hS.2.1 k
  have hNRp := counterflowNoReturn_of_thm13 h13 c.κ c.hκ c.hκ4 c.b c.jumps c.hb c.P c.h c.hh c.W c.ζ c.hcf c.hζ
  filter_upwards [hform, GW2Psm.ae_isDomainChart_curLaunch h13 c r l a, GW2Omx.ae_ae_launch_cur h13 c r l a,
    CondDriverBridge.ae_ae_run_eq_of_le (P := c.P) (κ := c.κ) (b := c.b) (jumps := c.jumps) spec
      (fun j _ ω => hreg j ω) h𝒢 le_rfl,
    KernelTower.ae_ae_condExpKernel_of_ae h𝒢 (GW2Later.ae_counterflow_regular h13 c.hκ c.hcf c.hζ),
    KernelTower.ae_ae_condExpKernel_of_ae h𝒢 c.hζ,
    KernelTower.ae_ae_condExpKernel_of_ae h𝒢 (Gm.ae_futureJoined_trace h13 c r),
    KernelTower.ae_ae_condExpKernel_of_ae h𝒢 (ae_schedW_trace c r l a h13),
    KernelTower.ae_ae_condExpKernel_of_ae h𝒢 (GW2Xk.ae_contactSet_eq_traceX h13 c r l a hTO),
    KernelTower.ae_ae_condExpKernel_of_ae h𝒢 hR.ae_pieceRegular,
    KernelTower.ae_ae_condExpKernel_of_ae h𝒢 c.hα,
    KernelTower.ae_ae_condExpKernel_of_ae h𝒢 hNRp, KernelTower.ae_ae_condExpKernel_of_ae h𝒢 hrep,
    KernelTower.ae_ae_condExpKernel_of_ae h𝒢 hfarall, KernelTower.ae_ae_condExpKernel_of_ae h𝒢 hEgood,
    KernelTower.ae_ae_condExpKernel_of_ae h𝒢 hGT.2.2, KernelTower.ae_ae_condExpKernel_of_ae h𝒢 hncP,
    KernelTower.ae_ae_condExpKernel_of_ae h𝒢 hshP, KernelTower.ae_ae_condExpKernel_of_ae h𝒢 hVd,
    KernelTower.ae_ae_condExpKernel_of_ae h𝒢 (GW2Xk.ae_mem_tipSet_root h13 h13₀ c r hroot),
    KernelTower.ae_ae_condExpKernel_of_ae h𝒢 hρ.2.2, KernelTower.ae_ae_condExpKernel_of_ae h𝒢 hE₀pos,
    KernelTower.ae_ae_condExpKernel_of_ae h𝒢 hcaps, KernelTower.ae_ae_condExpKernel_of_ae h𝒢 hD27,
    KernelTower.ae_ae_condExpKernel_of_ae h𝒢 hshAll, KernelTower.ae_ae_condExpKernel_of_ae h𝒢 hverAll]
    with ω₀ hF hdc hcur hrun hcfν hζν hfutν hschν hconν hprν hαν hNRν hrepν hfarν hEν hGTν hncν hshν hVdν hvisν
      hVρν hE₀ν hcapsν hD27ν hshAν hverν hdat
      cL θ hl
  obtain ⟨hconf, b', J', u', W, ζ, ℓ, cw, γ, uθ, -, -, hext, hb', hu', hfl', hcw, huθ, hcomp, hd, hmain0⟩ :=
    hF hdat cL θ hl
  have hcL := hdc cL θ hl
  set ν := condExpKernel c.P (GW2Olm.pastG c r l a) ω₀ with hν
  obtain ⟨b'', J'', h'', hb'', hT, hfl'', hcwJ, hcwb⟩ := id hcw
  have hcfk := hcw.isCenteredCounterflowDriver
  have hζk : ∀ᵐ ω ∂ν, ζ ω = ⊤ := hd.mono fun _ h => h.1
  have hG' := GW2aPiece.isGFFWithBoundaryData_of_isFlowLineDriver c.hκ hb' hfl'
  have hWkreg := GW2Later.ae_counterflow_regular h13 c.hκ hcfk hζk
  have hNRk := counterflowNoReturn_of_thm13 h13 c.κ c.hκ c.hκ4 b' J' hb' ν _ hG' W ζ hcfk hζk
  have hαc := GW2aSingle.ae_chosenTrace h13 c.hκ hfl'
  set Wα : ℝ≥0 → Ω → ℝ := fun t ω => (GW2Olm.futFam c r l a (GW2Olm.curIdx c r l) ω).1 t with hWα
  set ζα : Ω → ℝ≥0∞ := fun ω => (GW2Olm.futFam c r l a (GW2Olm.curIdx c r l) ω).2 with hζα
  set α : Ω → ℝ≥0 → ℂ := GW2aSingle.chosenTrace Wα ζα with hαdef
  have hα' : ∀ᵐ ω ∂ν, IsGeneratingTrace (fun t => Wα t ω) (ζα ω) (α ω) := hαc.mono fun _ h => h.1
  have hext_all : ∀ᵐ ω ∂ν, 0 < ζα ω → ∀ s : ℝ≥0, Continuous (fun t => regW s Wα ζα t ω) ∧
      regW s Wα ζα 0 ω = 0 ∧ (∀ t : ℝ≥0, (t : ℝ≥0∞) < ζα ω → regW s Wα ζα t ω = Wα t ω) ∧
      IsGeneratingTrace (fun t => regW s Wα ζα t ω) ⊤ (extTr s Wα ζα α ω) ∧
      ∀ u : ℝ≥0, (u : ℝ≥0∞) ≤ ζα ω → extTr s Wα ζα α ω u = α ω u := by
    filter_upwards [Supp8.GB6.ae_driver_zero_continuousOn hfl', hα', ae_tendsto_driver_at_lifetime c.hκ hfl']
      with ω hdω hαω hlim hpos s
    obtain ⟨h1, h2, h3, hex⟩ := regW_extension s hdω.1 hdω.2 hαω hpos fun T hT => hlim T hT (by
      rw [← ENNReal.coe_lt_coe, hT]; simpa using hpos)
    exact ⟨h1, h2, h3, Classical.epsilon_spec hex⟩
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
  have hθ : θ = candAngle c r l a := by
    have h := Exist.Staged.angle_of_launch (κ := c.κ) (b := c.b) (jumps := c.jumps) _ _ hl
    rw [h]
    rfl
  obtain ⟨T₀, L₀, F₀', hsel⟩ := GW2Pw.exists_sel3 (μ := ν) (Q := fun ξ s₀ lm F₀ =>
        ξ ∈ I.GT → oldSuccess c r l ξ →
          ((stgStartX (rootPt r.1) c.s c.W c.ζ I.W I.GT I.V I.T ξ : ℝ≥0) : ℝ≥0∞) < I.V ξ → deathClockX c r l a ξ < ⊤ →
          0 < candLife c r l a ξ →
          γ ξ s₀ ∈ H ∧ 0 < lm ∧ F₀.Finite ∧
          (∀ y, y ∉ F₀ → (I.β (I.srecX c r l (rootPt r.1) ξ)).fn y =
            (gw2Word c.κ θ cw (gb6Rec s₀ W ζ ξ)).fn (lm * y)) ∧
          ζα ξ = candLife c r l a ξ ∧
          (0 < candLife c r l a ξ →
            (((candLife c r l a ξ).toNNReal : ℝ≥0) : ℝ≥0∞) < gb6Tc s₀ (extTr s₀ Wα ζα α) γ ξ ∧
            lm ^ 2 * ((deathClockX c r l a ξ).toReal - (stgStartX (rootPt r.1) c.s c.W c.ζ I.W I.GT I.V I.T ξ : ℝ)) =
              gb6Clock s₀ (regW s₀ Wα ζα) W ξ (candLife c r l a ξ).toNNReal ∧
            ∃ Wd : ℝ≥0 → ℝ, Continuous Wd ∧ Wd 0 = 0 ∧ (∀ (n : ℕ) (q : ℝ≥0), (q : ℝ≥0∞) < Vv n ξ → Rv n q ξ = Wd q) ∧
              ∀ t : ℝ≥0, t ≤ (candLife c r l a ξ).toNNReal →
                fwdHull (scD lm (fun q : ℝ => stgDrv Wd (stgStartX (rootPt r.1) c.s c.W c.ζ I.W I.GT I.V I.T ξ)
                    q.toNNReal)) (gb6Clock s₀ (regW s₀ Wα ζα) W ξ t) =
                  relMap (fun r : ℝ => W r.toNNReal ξ) s₀ ''
                    fwdHull (fun r : ℝ => regW s₀ Wα ζα r.toNNReal ξ) t)) (by
    filter_upwards [hcur, hrun, hcfν, hζν, hfutν, hschν, hconν, hprν, hαν, hNRν, hcomp, hd, hWkreg, hNRk, hαc,
      hmain0, hext_all, hrepν, hfarν, hEν, hGTν, hncν, hshν, hVdν, hvisν, hVρν, hE₀ν, hcapsν, hD27ν, hshAν, hverν]
      with ξ hcurξ hrunξ hcfξ hζξ hfutξ hschξ hconξ hprξ hαξ hNRξ hcompξ hdξ hWkξ hNRkξ hαcξ hm0ξ hextξ hrepξ
        hfarξ hEξ' hGTξ hncξ hshξ hVdξ hvisξ hVρξ hE₀ξ hcapsξ hD27ξ hshAξ hverξ
    by_cases hP : ξ ∈ GT ∧ oldSuccess c r l ξ ∧ ((stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT V
        (historyTime c r l) ξ : ℝ≥0) : ℝ≥0∞) < V ξ ∧ deathClockX c r l a ξ < ⊤ ∧ 0 < candLife c r l a ξ
    swap
    · exact ⟨0, 0, ∅, fun h1 h2 h3 h4 h5 => absurd ⟨h1, h2, h3, h4, h5⟩ hP⟩
    obtain ⟨hξGT₀, hold₀, hSV₀, hdth, hℓpos⟩ := hP
    have hEξ : I.srecX c r l (rootPt r.1) ξ ∈ I.E :=
      ⟨⟨hE₀ξ hold₀ hℓpos, (GW2Sdi.augRec_mem_succRec_iff c r l _ ξ).2 hold₀⟩,
        GW2Sdo.mem_aliveRecX hρ.2.1 (stgRecDec_stageEncRec c r l ξ) (hv.2.1 ξ) (hv.2.2.1 ξ) (hGTξ.1 hξGT₀) hVρξ hSV₀⟩
    obtain ⟨hlξ, hold⟩ := hcurξ cL θ hl
    obtain ⟨-, -, hW'c, hW'0, -⟩ := hcfξ
    obtain ⟨γk', -, hWkc, hWk0, -⟩ := hWkξ
    obtain ⟨-, hℓc, hℓm, hℓr, hiff⟩ := hdξ
    rw [hcont ξ hrunξ, hconξ hold] at hℓr
    obtain ⟨hgood, -⟩ := hfutξ l a hold
    have hc := GW2Omx.stopDrv_cont_of_oldSuccess c r l a hold hprξ
    obtain ⟨hgx, hSV'⟩ := hEξ' hEξ
    have hξGT : ξ ∈ GT := hGTξ.2 hgx
    have hαs : c.α ξ c.s ∈ H := (GW2Psm.physGoodX_tip_marks (hGT.1 ξ hξGT)).1
    -- the stage data
    have hVdξ' := hVdξ hEξ
    set a₀ := stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT V (historyTime c r l) ξ with ha₀
    set A : ℝ≥0 → ℝ≥0 := fun u => GW2Psm.capA (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT V
      (historyTime c r l) u ξ with hAdef
    have hminne : ∀ u : ℝ≥0, min (physClockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT
        (historyTime c r l + u) ξ) (V ξ) ≠ ⊤ := fun u => ne_top_of_le_ne_top (hV ξ) (min_le_right _ _)
    have hcoeA : ∀ u : ℝ≥0, ((A u : ℝ≥0) : ℝ≥0∞) = min (physClockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT
        (historyTime c r l + u) ξ) (V ξ) := fun u => ENNReal.coe_toNNReal (hminne u)
    have hA0 : A 0 = a₀ := GW2Psm.capA_zero _ ξ
    have hAm : Monotone A := fun u v huv => ENNReal.toNNReal_mono (hminne v)
      (monotone_min_physClockX hGT.1 hs0 hx (V := V) ξ (add_le_add le_rfl huv))
    have hAc : Continuous A := GW2Psm.continuous_capA hGT.1 hs0 hx _ (hV ξ)
    have hτ : V ξ ≤ (A (GW2Psm.candStop c r l a ξ) : ℝ≥0∞) := by
      rw [hcoeA]
      exact le_min hVdξ' le_rfl
    have hSV : (a₀ : ℝ≥0∞) < V ξ := by
      rw [ha₀, stgStartX, ENNReal.coe_toNNReal (ne_top_of_le_ne_top (hV ξ) (min_le_right _ _))]
      exact hSV'
    have hstopA : ∀ u : ℝ≥0, (A u : ℝ≥0∞) < V ξ →
        u < candidateCap c r a ∧ (u : ℝ≥0∞) < (GW2Olm.futFam c r l a (GW2Olm.curIdx c r l) ξ).2 := by
      intro u hu
      rw [hcoeA] at hu
      have hlt : u < GW2Psm.candStop c r l a ξ := by
        by_contra hcon
        push Not at hcon
        have h1 : min (physClockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT
            (historyTime c r l + GW2Psm.candStop c r l a ξ) ξ) (V ξ) ≤
            min (physClockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT (historyTime c r l + u) ξ) (V ξ) :=
          monotone_min_physClockX hGT.1 hs0 hx (V := V) ξ (add_le_add (le_refl (historyTime c r l)) hcon)
        rw [min_eq_right hVdξ'] at h1
        exact absurd (lt_of_le_of_lt h1 hu) (lt_irrefl _)
      exact ⟨GW2Psm.capb_of_stop hlt, GW2Psm.life_of_stop hlt⟩
    have hshapeA : ∀ u : ℝ≥0, (A u : ℝ≥0∞) < V ξ → H \ schedUnionX c r l a (historyTime c r l) u ξ =
        (relChartX (rootPt r.1) c.s (cfRec c.s c.W c.ζ ξ)).2.1 '' (H \ fwdHull (Ito.rpath fun q => R q ξ) (A u)) :=
      fun u hu => hshξ hξGT hold u (by rw [← hcoeA]; exact hu)
    have hncA : ∀ u : ℝ≥0, (A u : ℝ≥0∞) < V ξ → ∀ v ∈ Icc 0 c.s, ∀ u' ≤ historyTime c r l + u,
        c.α ξ v * ((rootPt r.1 : ℂ) + schedTr c r l a ξ u') + 1 ≠ 0 := by
      intro u hu
      have h0 : min (physClockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT (historyTime c r l + u) ξ) (V ξ) <
          V ξ := by
        rw [← hcoeA]
        exact hu
      exact hncξ hξGT _ h0
    -- the typed data
    set w' : Set.range (fun y => wordType c.κ (ch.β y)) :=
      ⟨wordType c.κ (ch.β (I.srecX c r l (rootPt r.1) ξ)), ⟨_, rfl⟩⟩ with hw'def
    have hlive : ξ ∈ liveEvRec c.κ w'.1 ch.β I.E (I.srecX c r l (rootPt r.1)) := ⟨hEξ, rfl⟩
    obtain ⟨hwP₀, hgP₀⟩ := hrepξ w' hlive
    have hRc : Continuous fun u => R u ξ := hv.2.1 ξ
    have hR0 : R 0 ξ = 0 := hv.2.2.1 ξ
    have hdc' : Continuous fun q => I.drvX c (rootPt r.1) q ξ := continuous_stgDrv hRc _
    have hd0 : I.drvX c (rootPt r.1) 0 ξ = 0 := stgDrv_zero _ _
    have hU₀ := GW2Psm.bhe_bheProc_typedX_zero (r := r) (l := l) I (rootPt r.1) w'.1 ξ hdc' hd0
    have hfarβ := GW2Psm.far_typed c.hκ rfl (hfarξ w' hlive)
    have hfar' : sleLambda (16 / c.κ) - Real.pi * chiC c.κ + θ * chiC c.κ =
        sleLambda (16 / c.κ) - Real.pi * chiC c.κ + candAngle c r l a * chiC c.κ := by rw [hθ]
    have hcsD := GW2Kx.isDomainChart_stgChart_relChartX (rootPt r.1) c.s (cfRec c.s c.W c.ζ ξ) hRc hR0 a₀
    have hposζ : 0 < ζα ξ := by
      have h := (hstopA 0 (by rw [hA0]; exact hSV)).2
      simpa using h
    have hregW := hextξ hposζ
    obtain ⟨t₀, ht₀, hγt₀, lam, hlam, hdil, F, hF, hdata, -⟩ := sample_export_rootXD c r l a hx hord hs0 ξ hold hgood
      hlξ hc hcL hext (hreg k ξ) hαcξ.1 hWkc hWk0 hcompξ.1 hcompξ.2 (fun q hq => hNRkξ (γ ξ) hcompξ.2 q hq) hW'c
      hW'0 hαξ (fun v hv => hNRξ (c.α ξ) hαξ v hv) (by rw [hζξ]; exact ENNReal.coe_lt_top) hαs hschξ.1
      (hsch ξ hold).1 (hsch ξ hold).2 hℓc hℓm hℓr (fun hxp => GW2Xk.vis_of_mem_tipSet hαξ hW'c hW'0 (hvisξ hxp))
      hiff hb' hu' huθ cw hu₀.1 hwP₀ hgP₀ hm0ξ (w := w'.1)
      (β := ch.β (I.srecX c r l (rootPt r.1) ξ)) rfl hU₀ hRc hR0 hA0 hAm hAc hτ hSV hstopA hshapeA hncA
      (fun y hy => by
        have hy0 : (stgChart (GW2Rz.relChartX (rootPt r.1) c.s (cfRec c.s c.W c.ζ ξ)) (fun q => R q ξ) a₀).1 y ≠
            0 :=
          fun h0 => by
            have := hcsD.fwd_mem hy
            rw [h0] at this
            have h' : (0 : ℝ) < (0 : ℂ).im := this
            simp at h'
        have hS0 : Ito.rpath (stgDrv (fun q => R q ξ) a₀) 0 = 0 := by simp [Ito.rpath, stgDrv_zero]
        simp only [GW2Kx.stgMeanRX]
        rw [Coupling.MartMeans2.couplingMean_zero c.κ hS0 _ hy0]
        ring_nf
        try rfl)
      hfarβ hfar' (wr := fun s t => regW s Wα ζα t ξ) (ηr := fun s => extTr s Wα ζα α ξ) hregW
    refine ⟨t₀, lam, F, fun _ _ _ _ _ => ⟨hγt₀, hlam, hF, hdata, rfl, fun _ => ?_⟩⟩
    obtain ⟨hwr, hwr0, hwrW, hηr, hηrα⟩ := hregW t₀
    -- the version family at the sample
    set ℓ₀ : ℝ≥0 := (candLife c r l a ξ).toNNReal with hℓ₀def
    obtain ⟨hcapℓ, hcontℓ⟩ := (GW2Nv.deathClockX_lt_top_iff c r l a ξ).1 hdth
    have hℓne : candLife c r l a ξ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hcapℓ
    have hℓ₀ : (ℓ₀ : ℝ≥0∞) = (GW2Olm.futFam c r l a (GW2Olm.curIdx c r l) ξ).2 := ENNReal.coe_toNNReal hℓne
    have hℓ₀pos : 0 < ℓ₀ := ENNReal.toNNReal_pos hℓpos.ne' hℓne
    have hℓ₀cap : ℓ₀ ≤ candidateCap c r a := by rw [← ENNReal.coe_le_coe, hℓ₀]; exact hcapℓ
    have hd' : deathClockX c r l a ξ = ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a)
        (historyTime c r l + ℓ₀) ξ) := GW2Nv.deathClockX_eq_of_lt_top c r l a hdth
    obtain ⟨-, hKm, hKc⟩ := GW2Nv.clockX_props_at c r l a hGT.1 hs0 hx hξGT
    set C : ℝ≥0 → ℝ := fun u => clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (historyTime c r l + u) ξ
      with hCdef
    have hTu : ∀ u : ℝ≥0, u ≤ ℓ₀ → ((historyTime c r l + u : ℝ≥0) : ℝ≥0∞) <
        contactX (rootPt r.1) c.s (schedTr c r l a) c.α ξ :=
      fun u hu => lt_of_le_of_lt (ENNReal.coe_le_coe.2 (add_le_add le_rfl hu)) hcontℓ
    have hCc : ContinuousOn C (Icc 0 ℓ₀) :=
      hKc.comp (continuous_const.add continuous_id).continuousOn fun u hu => hTu u hu.2
    have hCm : StrictMonoOn C (Icc 0 ℓ₀) := fun u hu v hv huv =>
      hKm (hTu u hu.2) (hTu v hv.2) (add_lt_add_right huv _)
    have hphys : ∀ u : ℝ≥0, u ≤ ℓ₀ → physClockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT
        (historyTime c r l + u) ξ = ENNReal.ofReal (C u) :=
      fun u hu => physClockX_eq_clockX hGT.1 hs0 hx hξGT (hTu u hu)
    obtain ⟨-, hC0nn, -, -, -⟩ := GW2Nv.stage_start_death c r l a hGT.1 hs0 hx hξGT (hV ξ) hSV hdth
    have hC0 : 0 ≤ C 0 := by simpa [hCdef] using hC0nn
    have hCnn : ∀ u : ℝ≥0, u ≤ ℓ₀ → 0 ≤ C u := fun u hu => by
      rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ u) with h | h
      · rw [← h]; exact hC0
      · exact hC0.trans (hCm ⟨le_rfl, zero_le⟩ ⟨zero_le, hu⟩ h).le
    have hcapsξ' : ∀ n, Vv n ξ < ENNReal.ofReal (C ℓ₀) := fun n => by
      rw [show ENNReal.ofReal (C ℓ₀) = deathClockX c r l a ξ from hd'.symm]
      exact hcapsξ hgx hold hℓpos n
    have hpT : physClockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT (historyTime c r l) ξ =
        ENNReal.ofReal (C 0) := by
      have h := hphys 0 zero_le
      rwa [add_zero] at h
    have hminV : min (physClockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT (historyTime c r l) ξ) (V ξ) < V ξ :=
      hSV'
    have hpTV : physClockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT (historyTime c r l) ξ < V ξ :=
      lt_of_not_ge fun hcon => by
        rw [min_eq_right hcon] at hminV
        exact lt_irrefl _ hminV
    have ha₀C : (a₀ : ℝ≥0∞) = ENNReal.ofReal (C 0) := by
      have h : (a₀ : ℝ≥0∞) = min (physClockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT (historyTime c r l) ξ)
          (V ξ) := ENNReal.coe_toNNReal (ne_top_of_le_ne_top (hV ξ) (min_le_right _ _))
      rw [h, min_eq_left hpTV.le, hpT]
    set An : ℕ → ℝ≥0 → ℝ≥0 := fun n u => GW2Psm.capA (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT (Vv n)
      (historyTime c r l) u ξ with hAndef
    have hcoeAn : ∀ n u, ((An n u : ℝ≥0) : ℝ≥0∞) = min (physClockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT
        (historyTime c r l + u) ξ) (Vv n ξ) := fun n u =>
      ENNReal.coe_toNNReal (ne_top_of_le_ne_top (hVv n ξ) (min_le_right _ _))
    have hAn0 : ∀ n, (a₀ : ℝ≥0∞) < Vv n ξ → An n 0 = a₀ := fun n h => by
      apply ENNReal.coe_injective
      rw [hcoeAn, add_zero, hpT, ← ha₀C, min_eq_left h.le]
    have hAmv : ∀ n, Monotone (An n) := fun n u v huv =>
      ENNReal.toNNReal_mono (ne_top_of_le_ne_top (hVv n ξ) (min_le_right _ _))
        (monotone_min_physClockX hGT.1 hs0 hx (V := Vv n) ξ (add_le_add le_rfl huv))
    have hAcv : ∀ n, Continuous (An n) := fun n => GW2Psm.continuous_capA hGT.1 hs0 hx _ (hVv n ξ)
    have hreach : ∀ n, Vv n ξ ≤ (An n ℓ₀ : ℝ≥0∞) := fun n => by
      rw [hcoeAn, hphys ℓ₀ le_rfl]
      exact le_min (hcapsξ' n).le le_rfl
    have hAC : ∀ n u, (An n u : ℝ≥0∞) < Vv n ξ → (An n u : ℝ) = C u := by
      intro n u h
      have huℓ : u < ℓ₀ := lt_of_not_ge fun hu =>
        lt_irrefl _ (lt_of_le_of_lt ((hreach n).trans (ENNReal.coe_le_coe.2 (hAmv n hu))) h)
      have h1 : (An n u : ℝ≥0∞) = ENNReal.ofReal (C u) := by
        have h' := h
        rw [hcoeAn, hphys u huℓ.le] at h' ⊢
        exact min_eq_left (le_of_not_gt fun hc => by
          rw [min_eq_right hc.le] at h'
          exact lt_irrefl _ h')
      have h2 := congrArg ENNReal.toReal h1
      rw [ENNReal.coe_toReal, ENNReal.toReal_ofReal (hCnn u huℓ.le)] at h2
      exact h2
    have hexhA : ∀ u : ℝ≥0, 0 < u → u < ℓ₀ → ∃ n, (a₀ : ℝ≥0∞) < Vv n ξ ∧ (An n u : ℝ≥0∞) < Vv n ξ := by
      intro u hu0 huℓ
      have hCu : C 0 < C u := hCm ⟨le_rfl, zero_le⟩ ⟨zero_le, huℓ.le⟩ hu0
      have hCuℓ : C u < C ℓ₀ := hCm ⟨zero_le, huℓ.le⟩ ⟨zero_le, le_rfl⟩ huℓ
      have hCℓpos : 0 < C ℓ₀ := lt_of_le_of_lt (hCnn u huℓ.le) hCuℓ
      have hlt : ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (historyTime c r l + u) ξ) <
          deathClockX c r l a ξ := by
        rw [hd']
        exact (ENNReal.ofReal_lt_ofReal_iff hCℓpos).2 hCuℓ
      obtain ⟨n, hn⟩ := (hD27ξ hgx hold hdth _ (hTu u huℓ.le) hlt).exists
      refine ⟨n, ?_, ?_⟩
      · rw [ha₀C]
        exact lt_trans ((ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt hC0 hCu)).2 hCu) hn
      · rw [hcoeAn, hphys u huℓ.le, min_eq_left hn.le]
        exact hn
    have hshapeV : ∀ n u, (An n u : ℝ≥0∞) < Vv n ξ → H \ schedUnionX c r l a (historyTime c r l) u ξ =
        (relChartX (rootPt r.1) c.s (cfRec c.s c.W c.ζ ξ)).2.1 ''
          (H \ fwdHull (Ito.rpath (fun q => Rv n q ξ)) (An n u)) :=
      fun n u h => hshAξ n hξGT hold u (by rw [← hcoeAn]; exact h)
    have hncℓ : ∀ v ∈ Icc 0 c.s, ∀ u' ≤ historyTime c r l + ℓ₀,
        c.α ξ v * ((rootPt r.1 : ℂ) + schedTr c r l a ξ u') + 1 ≠ 0 :=
      GW2Kx.mul_add_one_ne_zero_of_lt_contactXx hcontℓ
    have hagree : ∀ (n m : ℕ) (q : ℝ≥0), (q : ℝ≥0∞) < Vv n ξ → (q : ℝ≥0∞) < Vv m ξ → Rv n q ξ = Rv m q ξ :=
      fun n m q hq hq' => GW2Pv.versions_agree_below hGT.1 hs0 hx hξGT (hverξ n hgx) (hverξ m hgx) (hTu ℓ₀ le_rfl)
        (hcapsξ' n) q hq hq'
    have hSj : (a₀ : ℝ≥0∞) < Vv j ξ := by rw [hVj]; exact hSV
    have hdilj : ∀ x ∈ ((stgChart (relChartX (rootPt r.1) c.s (cfRec c.s c.W c.ζ ξ)) (fun q => Rv j q ξ) a₀).dom :
        Set ℂ), relMap (fun q : ℝ => W q.toNNReal ξ) (t₀ : ℝ) (cL.1 x) =
          (lam : ℂ) * (stgChart (relChartX (rootPt r.1) c.s (cfRec c.s c.W c.ζ ξ)) (fun q => Rv j q ξ) a₀).1 x := by
      rw [hRj]
      exact hdil
    obtain ⟨ha, hb, Wd, hWdc, hWd0, hWdag, hhull⟩ := sample_death_rootX c r l a hx hord hs0 ξ hold hgood hlξ hc
      hconf hext (hreg k ξ) hαcξ.1 hWkc hWk0 hcompξ.2 (fun q hq => hNRkξ (γ ξ) hcompξ.2 q hq) hW'c hW'0 hαξ
      (fun v hv => hNRξ (c.α ξ) hαξ v hv) (by rw [hζξ]; exact ENNReal.coe_lt_top) hschξ.1 (hsch ξ hold).1
      (hsch ξ hold).2 hℓc hℓm hℓr (fun hxp => GW2Xk.vis_of_mem_tipSet hαξ hW'c hW'0 (hvisξ hxp)) hiff ht₀ hγt₀ hwr
      hwr0 hwrW hηr hηrα hℓ₀ hℓ₀pos hℓ₀cap hncℓ hCc
      (Rf := fun n q => Rv n q ξ) (fun n => (hAv n).1.1.2.1 ξ) (fun n => (hAv n).1.1.2.2.1 ξ) hagree hAn0 hAmv
      hAcv hreach hAC hexhA hshapeV hSj hlam hdilj
    refine ⟨ha, ?_, Wd, hWdc, hWd0, hWdag, hhull⟩
    rw [hd', ENNReal.toReal_ofReal (hCnn ℓ₀ le_rfl)]
    exact hb)
  exact ⟨b', J', _, Wα, ζα, α, b'', J'', h'', cw, W, ζ, γ, T₀, L₀, F₀', hb', hb'', hT, hfl', hα', hfl'', hcomp,
    hcwJ, hcwb, hsel⟩

end InteractingSLE.Theorem14.GW2Pu
