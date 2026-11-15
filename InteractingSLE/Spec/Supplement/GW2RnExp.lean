/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2PwExp
import InteractingSLE.Spec.Supplement.GW2RnForm
import InteractingSLE.Spec.Supplement.GW2RnRep
import InteractingSLE.Spec.Supplement.GW2RnSmp
import InteractingSLE.Spec.Supplement.GW2XkContact

/-!
# D46's export at a root `x`, with GB6's launch datum as a premise (D65)

PROVE-GW2-ROOTX round 13. STAGEMEAN's `GW2Pw.stageKernelExportLD_root0` at a root `x ∈ {0} ∪ lowerArcRoots`:
`GW2Pw.StageKernelExportLD` (NOTHR's `StageKernelExportL` with the datum premise, D60 (A)) at ROOTX's corrected
instance `schedInstSX c r l a GT hA ch` and the root `x = rootPt r.1`, for versions capped at the candidate's stop
(D49), from Claim(k) in the root-`x` chart (GEOM2's `GW2Kx.ClaimAtX`) and the word map's far height:

* the configuration from `ae_launch_form0WX` (the root-`x` stage-start form with the kernel word given);
* Claim(k) at almost every sample (`ae_stage_repX`), lifted to the kernel;
* the stage facts at a root `x` (GEOM2's `ae_noContact_rootX`, `ae_shape_rootX`, `ae_contactSet_eq_traceX`) and the
  counterflow's visit to `x` (`ae_mem_tipSet_root`, `vis_of_mem_tipSet`);
* the per-sample content from `sample_export_rootX`.

* **`stageKernelExportLD_rootX`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC fwdHull)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.GW2Rn

open Restart Exist Exist.Staged Exist.StagedLaw Sec7.PocketTraversal Supp8 Supp8.GB6 GW2Rd GW2TipSystem
  GW2TipSystem.RootC24 GW2TipSystem.RootJ31 GW2Rz GW2Rv GW2Sde GW2Sdh GW2Sdi GW2Schedule GW2Tip MartChar.RealFlow
  Sec5.CrossCond.StagedRepLater Sec5.Prop513Schedule Supp8.GB6.RelDrv Supp8.RelSafe GW2Nt GW2Nu Supp8.Q3Stop
  WholeField LocalSets

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **D46's export at a root `x ∈ {0} ∪ lowerArcRoots`, with GB6's launch datum as a premise**, for versions
capped at the candidate's stop on the record event (D49, D67), from Claim(k) in the root-`x` chart and the word map's
far height. -/
theorem stageKernelExportLD_rootX (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h13₀ : Exist.Theorem13Statement.{0}) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (hroot : rootPt r.1 = 0 ∨ rootPt r.1 ∈ lowerArcRoots c.κ c.b c.jumps)
    (hord : (historyProgram c r l).Pairwise (fun p q => p.2 < q.2)) (hs0 : 0 < c.s)
    {GT : Set Ω} (hGT : (∀ ω ∈ GT, PhysGoodX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α ω) ∧
      MeasurableSet GT ∧ (∀ᵐ ω ∂c.P, ω ∈ GT ↔ cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s))
    {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    (hA : IsRelVersionXA (rootPt r.1) c.s c.P c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α R V)
    (hV : ∀ ω, V ω ≠ ⊤) (ch : SchedChoice Ω) (hu₀ : IsBoundedHarmonicExtension c.b c.jumps ch.u₀)
    (hcount : (Set.range fun y => wordType c.κ (ch.β y)).Countable)
    (hVd : ∀ᵐ ω ∂c.P, (schedInstSX c r l a GT hA ch).srecX c r l (rootPt r.1) ω ∈ (schedInstSX c r l a GT hA ch).E →
      V ω ≤ physClockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT
        (historyTime c r l + GW2Psm.candStop c r l a ω) ω)
    (hclaim : ∀ w : WordType, GW2Kx.ClaimAtX c r l a GT hA ch w)
    (hfar : ∀ w : WordType, ∀ᵐ ω ∂c.P, ω ∈ liveEvRec c.κ w ch.β (schedInstSX c r l a GT hA ch).E
        ((schedInstSX c r l a GT hA ch).srecX c r l (rootPt r.1)) →
      GW2Wm.FarR (ch.β ((schedInstSX c r l a GT hA ch).srecX c r l (rootPt r.1) ω))
        (sleLambda (16 / c.κ) - Real.pi * chiC c.κ + candAngle c r l a * chiC c.κ)) :
    GW2Pw.StageKernelExportLD c r l a (schedInstSX c r l a GT hA ch) (rootPt r.1) := by
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
    KernelTower.ae_ae_condExpKernel_of_ae h𝒢 (GW2Xk.ae_mem_tipSet_root h13 h13₀ c r hroot)]
    with ω₀ hF hdc hcur hrun hcfν hζν hfutν hschν hconν hprν hαν hNRν hrepν hfarν hEν hGTν hncν hshν hVdν hvisν hdat
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
    I.srecX c r l (rootPt r.1) ξ ∈ I.E →
          γ ξ s₀ ∈ H ∧ 0 < lm ∧ F₀.Finite ∧
            (∀ y, y ∉ F₀ → (I.β (I.srecX c r l (rootPt r.1) ξ)).fn y =
              (gw2Word c.κ θ cw (gb6Rec s₀ W ζ ξ)).fn (lm * y)) ∧
            ∀ u : ℝ≥0, (u : ℝ≥0∞) < I.capX c (rootPt r.1) ξ →
              (((I.T + candidateCap c r a : ℝ≥0) : ℝ≥0∞) < contactX (rootPt r.1) c.s I.γ c.α ξ →
                ((stgStartX (rootPt r.1) c.s c.W c.ζ I.W I.GT I.V I.T ξ : ℝ≥0) : ℝ) + u ≤
                  clockX (rootPt r.1) c.s c.W c.ζ I.W (I.T + candidateCap c r a) ξ) →
              (∃ t : ℝ≥0, (t : ℝ≥0∞) < gw2End s₀ ζα γ α ξ ∧ lm ^ 2 * u < gw2Clock s₀ W Wα ξ t) ∧
              ∀ t : ℝ≥0, (t : ℝ≥0∞) < gb6Tc s₀ (extTr s₀ Wα ζα α) γ ξ →
                gb6Clock s₀ (regW s₀ Wα ζα) W ξ t ≤ lm ^ 2 * u →
                fwdHull (scD lm (fun q : ℝ => I.drvX c (rootPt r.1) q.toNNReal ξ))
                    (gb6Clock s₀ (regW s₀ Wα ζα) W ξ t) =
                  relMap (fun r : ℝ => W r.toNNReal ξ) s₀ ''
                    fwdHull (fun r : ℝ => regW s₀ Wα ζα r.toNNReal ξ) t) (by
    filter_upwards [hcur, hrun, hcfν, hζν, hfutν, hschν, hconν, hprν, hαν, hNRν, hcomp, hd, hWkreg, hNRk, hαc,
      hmain0, hext_all, hrepν, hfarν, hEν, hGTν, hncν, hshν, hVdν, hvisν]
      with ξ hcurξ hrunξ hcfξ hζξ hfutξ hschξ hconξ hprξ hαξ hNRξ hcompξ hdξ hWkξ hNRkξ hαcξ hm0ξ hextξ hrepξ
        hfarξ hEξ' hGTξ hncξ hshξ hVdξ hvisξ
    by_cases hEξ : I.srecX c r l (rootPt r.1) ξ ∈ I.E
    swap
    · exact ⟨0, 0, ∅, fun h => absurd h hEξ⟩
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
    obtain ⟨t₀, -, hγt₀, lam, hlam, F, hF, hdata, hwin⟩ := sample_export_rootX c r l a hx hord hs0 ξ hold hgood
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
    refine ⟨t₀, lam, F, fun _ => ⟨hγt₀, hlam, hF, hdata, fun u hu _ => ?_⟩⟩
    have hu' : ((a₀ + u : ℝ≥0) : ℝ≥0∞) < V ξ := by
      have h1 : (u : ℝ≥0∞) < V ξ - (a₀ : ℝ≥0∞) := hu
      rw [ENNReal.coe_add]
      exact lt_tsub_iff_left.1 h1
    obtain ⟨hwa, hwb⟩ := hwin u hu'
    exact ⟨hwa, fun t ht hle => hwb t ht hle⟩)
  exact ⟨b', J', _, Wα, ζα, α, b'', J'', h'', cw, W, ζ, γ, T₀, L₀, F₀', hb', hb'', hT, hfl', hα', hfl'', hcomp,
    hcwJ, hcwb, hsel⟩

end InteractingSLE.Theorem14.GW2Rn
