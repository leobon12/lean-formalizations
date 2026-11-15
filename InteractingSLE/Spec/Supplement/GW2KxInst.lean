/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2KxSupp
import InteractingSLE.Spec.Supplement.GW2PsmPairI
import InteractingSLE.Spec.Supplement.GW2TpSets

/-!
# The kernel chain at ROOTX's corrected instance, at a root `x`

Packet PROVE-GW2-GEOM2, round 14 (D49). STAGEMEAN's `GW2Psm.pair_instS` / `pair_inst` at a root
`x = rootPt r.1 ∈ {0} ∪ lowerArcRoots`: `pair_rootX` at ROOTX's corrected instance `GW2Rv.schedInstSX`, whose union
is RELDET's `schedUnionX` (`GW2Rd.schedUnionSX_eq_schedUnionX`) and whose chart is `chartX` on `relChartX`. Every
reading of `pair_rootX` is discharged at the instance, with the root-`x` readings of `GW2KxSupp`.

* **`pair_instSX`** (on a measurable event `S`), **`pair_instX`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped NNReal ENNReal
open LQGMetric (DistOn TestOn)
open QuantumZipper (H fwdHull chiC)

universe u

namespace InteractingSLE.Theorem14.GW2Kx

open Restart Exist Exist.Staged Exist.StagedLaw WholeField LocalSets GW2TipSystem GW2TipSystem.RootC24
  GW2TipSystem.RootJ31 GW2Schedule GW2Tip GW2Rd GW2Rz GW2Sde Supp8 Supp8.GB6 Supp8.GB6.RelDrv Supp8.Q3Stop
  Restart.DomainMarkov MartChar.RealFlow GW2JointKernel Sec7.PocketTraversal Supp8.RelSafe GW2Psm

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **The kernel chain at ROOTX's corrected instance, on a measurable event `S`** (root `x`, one word type,
`0 < t <` the cap; the life reading is needed on `S` only). -/
theorem pair_instSX (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)
    (hroot : rootPt r.1 = 0 ∨ rootPt r.1 ∈ lowerArcRoots c.κ c.b c.jumps) (hord : (historyProgram c r l).Pairwise (fun
      p q => p.2 < q.2)) (hs0 : 0 < c.s)
    {GT : Set Ω} (hGT : (∀ ω ∈ GT, PhysGoodX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α ω) ∧
      MeasurableSet GT ∧ (∀ᵐ ω ∂c.P, ω ∈ GT ↔ cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s))
    {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    (hA : IsRelVersionXA (rootPt r.1) c.s c.P c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α R V)
    (hV : ∀ ω, V ω ≠ ⊤) (ch : GW2Sdh.SchedChoice Ω) (hu₀ : IsBoundedHarmonicExtension c.b c.jumps ch.u₀)
    (hkc : ch.kc = chiC c.κ)
    (hβm : Measurable ch.β) (hE₀ : MeasurableSet ch.E₀) (w : WordType) (t : ℝ≥0) (htpos : 0 < t)
    (htcap : t < candidateCap c r a) {S : Set Ω} (hSm : MeasurableSet S)
    (hlife : ∀ᵐ ω ∂c.P, ω ∈ S → ω ∈ liveEvRec c.κ w ch.β (GW2Rv.schedInstSX c r l a GT hA ch).E
        ((GW2Rv.schedInstSX c r l a GT hA ch).srecX c r l (rootPt r.1)) →
      (GW2Rv.schedInstSX c r l a GT hA ch).clockX c (rootPt r.1) t ω <
        (GW2Rv.schedInstSX c r l a GT hA ch).capX c (rootPt r.1) ω →
      (t : ℝ≥0∞) < candLife c r l a ω)
    (hfar : ∀ᵐ ω ∂c.P, ω ∈ liveEvRec c.κ w ch.β (GW2Rv.schedInstSX c r l a GT hA ch).E
        ((GW2Rv.schedInstSX c r l a GT hA ch).srecX c r l (rootPt r.1)) →
      GW2Wm.FarR (ch.β ((GW2Rv.schedInstSX c r l a GT hA ch).srecX c r l (rootPt r.1) ω))
        (sleLambda (16 / c.κ) - Real.pi * chiC c.κ + candAngle c r l a * chiC c.κ))
    (hclaim : ∀ g₀ : Ω → DistOn upperHalfPlaneOpens,
      IsLocalSetMean ((GW2Rv.schedInstSX c r l a GT hA ch).B 0) (centredField c.h ch.u₀) c.P g₀ →
      ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂c.P,
        ω ∈ liveEvRec c.κ w ch.β (GW2Rv.schedInstSX c r l a GT hA ch).E
          ((GW2Rv.schedInstSX c r l a GT hA ch).srecX c r l (rootPt r.1)) →
        (0 : ℝ≥0∞) < (GW2Rv.schedInstSX c r l a GT hA ch).capX c (rootPt r.1) ω →
        tsupport φ ⊆ H \ (GW2Rv.schedInstSX c r l a GT hA ch).B 0 ω →
        g₀ ω φ = ∫ z, stgMeanRX c.κ (rootPt r.1) c.s (cfRec c.s c.W c.ζ ω) (fun q => R q ω)
          (stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT V (historyTime c r l) ω) 0
          (bheProc c.κ (typedRhoL w) (typedRhoR w) ((GW2Rv.schedInstSX c r l a GT hA ch).drvX c (rootPt r.1))
            (fun i t ω => geomLW canonDrv (fun y => typedXL c.κ w (ch.β y.1)) i t
              ((GW2Rv.schedInstSX c r l a GT hA ch).srecX c r l (rootPt r.1) ω,
                relVar (GW2Rv.schedInstSX c r l a GT hA ch).Hr
                  ((GW2Rv.schedInstSX c r l a GT hA ch).drvX c (rootPt r.1))
                  ((GW2Rv.schedInstSX c r l a GT hA ch).capX c (rootPt r.1)) ω))
            (fun j t ω => geomRW canonDrv (fun y => typedXR c.κ w (ch.β y.1)) j t
              ((GW2Rv.schedInstSX c r l a GT hA ch).srecX c r l (rootPt r.1) ω,
                relVar (GW2Rv.schedInstSX c r l a GT hA ch).Hr
                  ((GW2Rv.schedInstSX c r l a GT hA ch).drvX c (rootPt r.1))
                  ((GW2Rv.schedInstSX c r l a GT hA ch).capX c (rootPt r.1)) ω)) ω 0)
          ch.u₀ ch.σa z * φ z)
    (g : Ω → DistOn upperHalfPlaneOpens)
    (hg : IsLocalSetMean ((GW2Rv.schedInstSX c r l a GT hA ch).B t) (centredField c.h ch.u₀) c.P g)
    (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂c.P, ω ∈ S → ω ∈ liveEvRec c.κ w ch.β (GW2Rv.schedInstSX c r l a GT hA ch).E
        ((GW2Rv.schedInstSX c r l a GT hA ch).srecX c r l (rootPt r.1)) →
      (GW2Rv.schedInstSX c r l a GT hA ch).clockX c (rootPt r.1) t ω <
        (GW2Rv.schedInstSX c r l a GT hA ch).capX c (rootPt r.1) ω →
      tsupport φ ⊆ H \ (GW2Rv.schedInstSX c r l a GT hA ch).B t ω →
      g ω φ = ∫ z, stgMeanRX c.κ (rootPt r.1) c.s (cfRec c.s c.W c.ζ ω) (fun q => R q ω)
          (stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT V (historyTime c r l) ω)
          (((GW2Rv.schedInstSX c r l a GT hA ch).clockX c (rootPt r.1) t ω).toNNReal : ℝ)
          (bheProc c.κ (typedRhoL w) (typedRhoR w) ((GW2Rv.schedInstSX c r l a GT hA ch).drvX c (rootPt r.1))
            (fun i t ω => geomLW canonDrv (fun y => typedXL c.κ w (ch.β y.1)) i t
              ((GW2Rv.schedInstSX c r l a GT hA ch).srecX c r l (rootPt r.1) ω,
                relVar (GW2Rv.schedInstSX c r l a GT hA ch).Hr
                  ((GW2Rv.schedInstSX c r l a GT hA ch).drvX c (rootPt r.1))
                  ((GW2Rv.schedInstSX c r l a GT hA ch).capX c (rootPt r.1)) ω))
            (fun j t ω => geomRW canonDrv (fun y => typedXR c.κ w (ch.β y.1)) j t
              ((GW2Rv.schedInstSX c r l a GT hA ch).srecX c r l (rootPt r.1) ω,
                relVar (GW2Rv.schedInstSX c r l a GT hA ch).Hr
                  ((GW2Rv.schedInstSX c r l a GT hA ch).drvX c (rootPt r.1))
                  ((GW2Rv.schedInstSX c r l a GT hA ch).capX c (rootPt r.1)) ω)) ω
            ((GW2Rv.schedInstSX c r l a GT hA ch).clockX c (rootPt r.1) t ω).toNNReal)
          ch.u₀ ch.σa z * φ z := by
  classical
  have hx : (0 : ℝ) ≤ rootPt r.1 :=
    hroot.elim (fun h => h.ge) fun h => (GW2Sched.pos_of_mem_lowerArcRoots h).le
  have hB : ∀ q : ℝ≥0, (GW2Rv.schedInstSX c r l a GT hA ch).B q = schedUnionX c r l a (historyTime c r l) q :=
    fun q => schedUnionSX_eq_schedUnionX c r l a q
  have hharm : InnerProductSpace.HarmonicOnNhd ch.u₀ H := hu₀.1
  have hh0 : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (centredField c.h ch.u₀) c.P :=
    isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData c.hh hu₀
  have hTO := Gm.timeOrdered_of_pairwise_lt hord
  have hloc := isHistoryAvoidanceLocal_stgFX h12 h13 c r l a hTO hu₀ t
  have hloc₀ := isHistoryAvoidanceLocal_stgFX h12 h13 c r l a hTO hu₀ 0
  set G : Set Ω := liveEvRec c.κ w ch.β (GW2Rv.schedInstSX c r l a GT hA ch).E
      ((GW2Rv.schedInstSX c r l a GT hA ch).srecX c r l (rootPt r.1)) ∩
    ({ω | (GW2Rv.schedInstSX c r l a GT hA ch).clockX c (rootPt r.1) t ω <
      (GW2Rv.schedInstSX c r l a GT hA ch).capX c (rootPt r.1) ω} ∩ S) with hGdef
  have hver : IsRelVersionXR (rootPt r.1) c.s c.P c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α R V := hA.1
  have hv := hver.1
  have hWm : ∀ q, Measurable (schedW c r l a q) := measurable_schedW c r l a
  have hGTm : ∀ q, MeasurableSet[physFilt (measurable_gb6Rec_src c) hWm c.P q] GT :=
    measurableSet_goodSetX_physFilt (measurable_gb6Rec_src c) hWm hGT.2.1 hGT.2.2
  have hpre : Measurable (stgPreRecX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT V (historyTime c r l) R) :=
    (measurable_stgPreRecX hGT.1 hs0 hx (measurable_gb6Rec_src c) hWm hGTm hver (historyTime c r l)).mono
      ((physFilt (measurable_gb6Rec_src c) hWm c.P).le _) le_rfl
  have hsrec : Measurable ((GW2Rv.schedInstSX c r l a GT hA ch).srecX c r l (rootPt r.1)) :=
    measurable_augRec (measurable_stageEncRec c r l) hpre
  have hstart := measurable_stgStartX_of_pre hpre
  have hclk : Measurable ((GW2Rv.schedInstSX c r l a GT hA ch).clockX c (rootPt r.1) t) :=
    (measurable_stgClockX hGT.1 hs0 hx (measurable_gb6Rec_src c) hWm hGTm hver (historyTime c r l) t).mono
      ((shiftFilt (physFilt (measurable_gb6Rec_src c) hWm c.P) (historyTime c r l)).le t) le_rfl
  have hcap : Measurable ((GW2Rv.schedInstSX c r l a GT hA ch).capX c (rootPt r.1)) :=
    hv.2.2.2.2.1.sub (measurable_coe_nnreal_ennreal.comp hstart)
  have hEm : MeasurableSet (GW2Rv.schedInstSX c r l a GT hA ch).E :=
    (hE₀.inter (GW2Sdi.measurableSet_succRec c r l)).inter (measurableSet_aliveRecX _ _ c.s hA.1.2.choose_spec.1)
  have hGm : MeasurableSet G := by
    refine (hsrec (hEm.inter ?_)).inter ((measurableSet_lt hclk hcap).inter hSm)
    exact ((measurable_wordType c.κ).comp hβm) (measurableSet_singleton w)
  have hGs : ∀ ω ∈ G, oldSuccess c r l ω := fun ω hω =>
    (GW2Sdi.augRec_mem_succRec_iff c r l _ ω).1 hω.1.1.1.2
  have hθ : ∀ (ω₀ : Ω) (cL : Chart) (θ : ℝ), GW2Olm.curLaunch c r l a ω₀ = some (cL, θ) →
      sleLambda (16 / c.κ) - Real.pi * chiC c.κ + θ * chiC c.κ =
        sleLambda (16 / c.κ) - Real.pi * chiC c.κ + candAngle c r l a * chiC c.κ := by
    intro ω₀ cL θ hl
    have h := Exist.Staged.angle_of_launch (κ := c.κ) (b := c.b) (jumps := c.jumps) _ _ hl
    rw [h]
    rfl
  have hg' : IsLocalSetMean (schedUnionX c r l a (historyTime c r l) t) (centredField c.h ch.u₀) c.P g := by
    rw [← hB t]; exact hg
  -- the stage data
  set I := GW2Rv.schedInstSX c r l a GT hA ch with hIdef
  set a₀ : Ω → ℝ≥0 := fun ω => stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT V (historyTime c r l) ω
    with ha₀
  set A : ℝ≥0 → Ω → ℝ≥0 := fun u ω => capA (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT V (historyTime c r l) u ω
    with hAdef
  set VLp : Fin w.1 → ℝ≥0 → Ω → ℝ := fun i t ω => geomLW canonDrv (fun y => typedXL c.κ w (ch.β y.1)) i t
    (I.srecX c r l (rootPt r.1) ω, relVar I.Hr (I.drvX c (rootPt r.1)) (I.capX c (rootPt r.1)) ω) with hVLp
  set VRp : Fin w.2.1 → ℝ≥0 → Ω → ℝ := fun j t ω => geomRW canonDrv (fun y => typedXR c.κ w (ch.β y.1)) j t
    (I.srecX c r l (rootPt r.1) ω, relVar I.Hr (I.drvX c (rootPt r.1)) (I.capX c (rootPt r.1)) ω) with hVRp
  set U₀ : Ω → ℂ → ℝ := fun ω => bheProc c.κ (typedRhoL w) (typedRhoR w) (I.drvX c (rootPt r.1)) VLp VRp ω 0
    with hU₀
  set U : Ω → ℂ → ℝ := fun ω => bheProc c.κ (typedRhoL w) (typedRhoR w) (I.drvX c (rootPt r.1)) VLp VRp ω
    (I.clockX c (rootPt r.1) t ω).toNNReal with hU
  set xL : Ω → Fin w.1 → ℝ := fun ω => typedXL c.κ w (ch.β (I.srecX c r l (rootPt r.1) ω)) with hxL
  set xR : Ω → Fin w.2.1 → ℝ := fun ω => typedXR c.κ w (ch.β (I.srecX c r l (rootPt r.1) ω)) with hxR
  have hltVG : ∀ ω ∈ G,
      min (physClockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT (historyTime c r l + t) ω) (V ω) < V ω := by
    intro ω hωG
    have hstartne : stgStartMX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT V (historyTime c r l) ω ≠ ⊤ :=
      ne_top_of_le_ne_top (hV ω) (min_le_right _ _)
    by_contra hcon
    push Not at hcon
    have h1 : V ω - stgStartMX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT V (historyTime c r l) ω ≤
        min (physClockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT (historyTime c r l + t) ω) (V ω) -
          stgStartMX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT V (historyTime c r l) ω :=
      tsub_le_tsub_right hcon _
    have h2 : I.capX c (rootPt r.1) ω =
        V ω - stgStartMX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT V (historyTime c r l) ω := by
      show V ω - ((stgStartMX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT V (historyTime c r l) ω).toNNReal :
        ℝ≥0∞) = _
      rw [ENNReal.coe_toNNReal hstartne]
    have h3 : I.clockX c (rootPt r.1) t ω =
        min (physClockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT (historyTime c r l + t) ω) (V ω) -
          stgStartMX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT V (historyTime c r l) ω := rfl
    have hlt' : I.clockX c (rootPt r.1) t ω < I.capX c (rootPt r.1) ω := hωG.2.1
    rw [h2, h3] at hlt'
    exact absurd (lt_of_lt_of_le hlt' h1) (lt_irrefl _)
  have hρ := hA.1.2.choose_spec
  have hfin : ∀ᵐ ω ∂c.P, I.srecX c r l (rootPt r.1) ω ∈ I.E →
      stgStartMX (rootPt r.1) c.s c.W c.ζ I.W I.GT I.V I.T ω ≠ ⊤ :=
    Eventually.of_forall fun ω _ => ne_top_of_le_ne_top (hV ω) (min_le_right _ _)
  have hEgood := StageInst.E_good_of_recordX I hv hρ.2.1 hρ.2.2 inter_subset_right hfin
  have hread : ∀ᵐ ω ∂c.P, ω ∈ G →
      (t : ℝ≥0∞) < (GW2Olm.futFam c r l a (GW2Olm.curIdx c r l) ω).2 ∧ c.α ω c.s ∈ H ∧
      (∀ v ∈ Icc 0 c.s, ∀ u ≤ historyTime c r l + t,
        c.α ω v * ((rootPt r.1 : ℂ) + schedTr c r l a ω u) + 1 ≠ 0) ∧
      Continuous (fun u => R u ω) ∧ R 0 ω = 0 ∧ A 0 ω = a₀ ω ∧ (∀ u, a₀ ω ≤ A u ω) ∧
      Continuous (fun u => A u ω) ∧
      (∀ u ≤ t, H \ schedUnionX c r l a (historyTime c r l) u ω =
        (relChartX (rootPt r.1) c.s (cfRec c.s c.W c.ζ ω)).2.1 '' (H \ fwdHull (Ito.rpath fun q => R q ω) (A u ω))) ∧
      (∀ i, xL ω i ≤ 0) ∧ (∀ j, 0 ≤ xR ω j) ∧
      IsBoundedHarmonicExtension (forceBoundaryData c.κ (typedRhoL w) (typedRhoR w) (xL ω) (xR ω))
        (forceJumpSet (xL ω) (xR ω)) (U₀ ω) ∧
      (∃ B : ℝ, ∀ y, B < y → y ∉ forceJumpSet (xL ω) (xR ω) →
        forceBoundaryData c.κ (typedRhoL w) (typedRhoR w) (xL ω) (xR ω) y =
          sleLambda (16 / c.κ) - Real.pi * chiC c.κ + candAngle c r l a * chiC c.κ) ∧
      IsBoundedHarmonicExtension
        (forceBoundaryData c.κ (typedRhoL w) (typedRhoR w)
          (fun i => -rightImg (fun s => -Ito.rpath (stgDrv (fun q => R q ω) (a₀ ω)) s) (-xL ω i)
            ((A t ω : ℝ) - a₀ ω) - Ito.rpath (stgDrv (fun q => R q ω) (a₀ ω)) ((A t ω : ℝ) - a₀ ω))
          (fun j => rightImg (Ito.rpath (stgDrv (fun q => R q ω) (a₀ ω))) (xR ω j) ((A t ω : ℝ) - a₀ ω) -
            Ito.rpath (stgDrv (fun q => R q ω) (a₀ ω)) ((A t ω : ℝ) - a₀ ω)))
        (forceJumpSet
          (fun i => -rightImg (fun s => -Ito.rpath (stgDrv (fun q => R q ω) (a₀ ω)) s) (-xL ω i)
            ((A t ω : ℝ) - a₀ ω) - Ito.rpath (stgDrv (fun q => R q ω) (a₀ ω)) ((A t ω : ℝ) - a₀ ω))
          (fun j => rightImg (Ito.rpath (stgDrv (fun q => R q ω) (a₀ ω))) (xR ω j) ((A t ω : ℝ) - a₀ ω) -
            Ito.rpath (stgDrv (fun q => R q ω) (a₀ ω)) ((A t ω : ℝ) - a₀ ω))) (U ω) ∧
      InnerProductSpace.HarmonicOnNhd
        (stgMeanRX c.κ (rootPt r.1) c.s (cfRec c.s c.W c.ζ ω) (fun q => R q ω) (a₀ ω) 0 (U₀ ω) ch.u₀ ch.σa)
        (H \ schedUnionX c r l a (historyTime c r l) 0 ω) := by
    filter_upwards [hlife, hfar, hEgood, hGT.2.2, ae_shape_rootX c r l a hx hs0 hGT.1 hv,
      ae_noContact_rootX hGT.1 hs0 hx hv] with ω hlifeω hfarω hEω hGTω hshapeω hncω hωG
    obtain ⟨hlive, hlt, hSω⟩ := hωG
    have hωGT : ω ∈ GT := hGTω.2 (hEω hlive.1).1
    have hsucc : oldSuccess c r l ω := hGs ω ⟨hlive, hlt, hSω⟩
    have hRc : Continuous fun u => R u ω := hv.2.1 ω
    have hR0 : R 0 ω = 0 := hv.2.2.1 ω
    -- the clock is below the cap at the physical times up to `T + t`
    have hltV : min (physClockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT (historyTime c r l + t) ω) (V ω) <
        V ω := hltVG ω ⟨hlive, hlt, hSω⟩
    have hltu : ∀ u ≤ t,
        min (physClockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT (historyTime c r l + u) ω) (V ω) < V ω :=
      fun u hu => lt_of_le_of_lt (monotone_min_physClockX hGT.1 hs0 hx (V := V) ω (add_le_add le_rfl hu)) hltV
    have hdc : Continuous fun q => I.drvX c (rootPt r.1) q ω := continuous_stgDrv hRc _
    have hd0 : I.drvX c (rootPt r.1) 0 ω = 0 := stgDrv_zero _ _
    have hU₀ := bhe_bheProc_typedX_zero (r := r) (l := l) I (rootPt r.1) w ω hdc hd0
    have hU := bhe_bheProc_typedX (r := r) (l := l) I (rootPt r.1) w ω hdc hd0
      (I.clockX c (rootPt r.1) t ω).toNNReal
    have e : ((I.clockX c (rootPt r.1) t ω).toNNReal : ℝ) = (A t ω : ℝ) - a₀ ω :=
      coe_toNNReal_stgClockX hGT.1 hs0 hx (historyTime c r l) t (hV ω)
    rw [e] at hU
    refine ⟨hlifeω hSω hlive hlt, (physGoodX_tip_marks (hGT.1 ω hωGT)).1, hncω hωGT _ hltV, hRc, hR0,
      capA_zero _ ω, stgStart_le_capA hGT.1 hs0 hx _ (hV ω), continuous_capA hGT.1 hs0 hx _ (hV ω),
      fun u hu => hshapeω hωGT hsucc u (hltu u hu), fun i => typedXL_nonpos _ _ _ i,
      fun j => typedXR_nonneg _ _ _ j, hU₀, far_typed c.hκ hlive.2 (hfarω hlive), hU, ?_⟩
    -- the stage-start mean is harmonic off the union
    have hsh0 := hshapeω hωGT hsucc 0 (hltu 0 zero_le)
    rw [hsh0, capA_zero]
    have hi := stgChart_inv_image (relChartX (rootPt r.1) c.s (cfRec c.s c.W c.ζ ω)) hRc hR0 (a₀ ω) 0
    rw [add_zero] at hi
    rw [← hi]
    exact harmonicOnNhd_stgMeanRX c.κ (rootPt r.1) c.s _ hRc hR0 (a₀ ω) le_rfl hU₀.1 hu₀.1 ch.σa
  have hclaim' : ∀ g₀ : Ω → DistOn upperHalfPlaneOpens,
      IsLocalSetMean (schedUnionX c r l a (historyTime c r l) 0) (centredField c.h ch.u₀) c.P g₀ →
      ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂c.P, ω ∈ G → tsupport φ ⊆ H \ schedUnionX c r l a (historyTime c r l) 0
          ω →
        g₀ ω φ = ∫ z, stgMeanRX c.κ (rootPt r.1) c.s (cfRec c.s c.W c.ζ ω) (fun q => R q ω) (a₀ ω) 0 (U₀ ω) ch.u₀
            ch.σa z *
          φ z := by
    intro g₀ hg₀ φ
    have hg₀' : IsLocalSetMean (I.B 0) (centredField c.h ch.u₀) c.P g₀ := by rw [hB 0]; exact hg₀
    filter_upwards [hclaim g₀ hg₀' φ] with ω h hωG hsupp
    have hcap0 : (0 : ℝ≥0∞) < I.capX c (rootPt r.1) ω := lt_of_le_of_lt zero_le hωG.2.1
    rw [hB 0] at h
    exact h hωG.1 hcap0 hsupp
  obtain ⟨F, hFm, hFeq⟩ : ∃ F : TestOn upperHalfPlaneOpens → Ω → ℝ, (∀ φ, Measurable (F φ)) ∧
      ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂c.P, ω ∈ G → tsupport φ ⊆ H \ schedUnionX c r l a (historyTime c r l) t
          ω →
        F φ ω = ∫ z, stgMeanRX c.κ (rootPt r.1) c.s (cfRec c.s c.W c.ζ ω) (fun q => R q ω) (a₀ ω) ((A t ω : ℝ) - a₀ ω)
            (U ω)
          ch.u₀ ch.σa z * φ z := by
    have hRm := hv.1
    have hRcA := hv.2.1
    have hR0A := hv.2.2.1
    have hSc : ∀ ω, Continuous fun u => I.drvX c (rootPt r.1) u ω := fun ω => continuous_stgDrv (hRcA ω) _
    have hS0 : ∀ ω, I.drvX c (rootPt r.1) 0 ω = 0 := fun ω => stgDrv_zero _ _
    have hSm : ∀ u, Measurable (I.drvX c (rootPt r.1) u) := measurable_stgRX hRm hRcA hpre
    have hcs : WalkInf.IsMeasChart mΩ fun ω => I.chartX c (rootPt r.1) ω :=
      isMeasChart_stgChartX (measurable_gb6Rec_src c) hRcA hR0A hpre
    have hHr : Measurable I.Hr := measurable_stgField c.hh.1 hcs
    have hΦ : Measurable fun ω => (I.srecX c r l (rootPt r.1) ω,
        relVar I.Hr (I.drvX c (rootPt r.1)) (I.capX c (rootPt r.1)) ω) :=
      hsrec.prodMk (measurable_relVar hHr hSm hcap)
    have hgL : ∀ i u, Measurable (geomLW canonDrv (fun y : CanonSpace => typedXL c.κ w (ch.β y.1)) i u) :=
      fun i u => (measurable_rightImg_realPath_of_measurable (𝓕 := (⊤ : Filtration ℝ≥0 _))
        (fun q => (measurable_canonDrv q).neg) (fun y => (continuous_canonDrv y).neg)
        (((measurable_pi_apply i).comp ((measurable_typedXL c.κ w).comp (hβm.comp measurable_fst))).neg) u).neg
    have hgR : ∀ j u, Measurable (geomRW canonDrv (fun y : CanonSpace => typedXR c.κ w (ch.β y.1)) j u) :=
      fun j u => measurable_rightImg_realPath_of_measurable (𝓕 := (⊤ : Filtration ℝ≥0 _))
        (fun q => measurable_canonDrv q) (fun y => continuous_canonDrv y)
        ((measurable_pi_apply j).comp ((measurable_typedXR c.κ w).comp (hβm.comp measurable_fst))) u
    have hVLm : ∀ i u, Measurable (VLp i u) := fun i u => (hgL i u).comp hΦ
    have hVRm : ∀ j u, Measurable (VRp j u) := fun j u => (hgR j u).comp hΦ
    have hVLc : ∀ i ω, Continuous fun u => VLp i u ω := fun i ω => by
      have h := Sec5.Prop59Pieces.continuousOn_rightImg_realPath (L := ⊤)
        (X := fun q y => -Q3Stop.canonDrv q y) (ω := (I.srecX c r l (rootPt r.1) ω,
          relVar I.Hr (I.drvX c (rootPt r.1)) (I.capX c (rootPt r.1)) ω))
        ((continuous_canonDrv _).neg.continuousOn) (-typedXL c.κ w (ch.β (I.srecX c r l (rootPt r.1) ω)) i)
      have hu : {u : ℝ≥0 | (u : ℝ≥0∞) < ⊤} = univ := eq_univ_of_forall fun u => ENNReal.coe_lt_top
      rw [hu, continuousOn_univ] at h
      exact h.neg
    have hVRc : ∀ j ω, Continuous fun u => VRp j u ω := fun j ω => by
      have h := Sec5.Prop59Pieces.continuousOn_rightImg_realPath (L := ⊤)
        (X := fun q y => Q3Stop.canonDrv q y) (ω := (I.srecX c r l (rootPt r.1) ω,
          relVar I.Hr (I.drvX c (rootPt r.1)) (I.capX c (rootPt r.1)) ω))
        ((continuous_canonDrv _).continuousOn) (typedXR c.κ w (ch.β (I.srecX c r l (rootPt r.1) ω)) j)
      have hu : {u : ℝ≥0 | (u : ℝ≥0∞) < ⊤} = univ := eq_univ_of_forall fun u => ENNReal.coe_lt_top
      rw [hu, continuousOn_univ] at h
      exact h
    have hQ : Measurable fun ω => (I.clockX c (rootPt r.1) t ω).toNNReal := ENNReal.measurable_toNNReal.comp hclk
    have hu₀c : ContinuousOn ch.u₀ H := fun z hz => (hu₀.1 z hz).1.continuousAt.continuousWithinAt
    refine ⟨fun φ ω => ∫ z, ({p : Ω × ℂ | p.2 ∈ (GW2Omx.movedChart (fun ω => I.chartX c (rootPt r.1) ω)
        (I.drvX c (rootPt r.1)) (fun ω => (I.clockX c (rootPt r.1) t ω).toNNReal) p.1).dom}.indicator
      (fun p => GW2Omx.chartMeanFn c.κ (typedRhoL w) (typedRhoR w)
        (GW2Omx.posAt (I.drvX c (rootPt r.1)) VLp VRp fun ω => (I.clockX c (rootPt r.1) t ω).toNNReal)
        (GW2Omx.movedChart (fun ω => I.chartX c (rootPt r.1) ω) (I.drvX c (rootPt r.1))
          fun ω => (I.clockX c (rootPt r.1) t ω).toNNReal)
        (fun ω => I.chartX c (rootPt r.1) ω) ch.u₀ ch.σa ch.kc p.1 p.2)) (ω, z) * φ z,
      fun φ => GW2Omx.measurable_integral_moved c.κ (typedRhoL w) (typedRhoR w) hcs hSc hS0 hSm hVLc hVLm hVRc
        hVRm hQ hu₀c ch.σa ch.kc φ, fun φ => ?_⟩
    filter_upwards [ae_shape_rootX c r l a hx hs0 hGT.1 hv, hGT.2.2, hEgood] with ω hshω hGTω hEω hωG hsupp
    have hωGT : ω ∈ GT := hGTω.2 (hEω hωG.1.1).1
    have hsucc : oldSuccess c r l ω := hGs ω hωG
    have hsh := hshω hωGT hsucc t (hltVG ω hωG)
    have e : ((I.clockX c (rootPt r.1) t ω).toNNReal : ℝ) = (A t ω : ℝ) - a₀ ω :=
      coe_toNNReal_stgClockX hGT.1 hs0 hx (historyTime c r l) t (hV ω)
    have hsum : a₀ ω + (I.clockX c (rootPt r.1) t ω).toNNReal = A t ω := by
      apply NNReal.eq
      rw [NNReal.coe_add, e]
      ring
    have hcsω : I.chartX c (rootPt r.1) ω =
        stgChart (relChartX (rootPt r.1) c.s (cfRec c.s c.W c.ζ ω)) (fun q => R q ω) (a₀ ω) := rfl
    have hiv := stgChart_inv_image (relChartX (rootPt r.1) c.s (cfRec c.s c.W c.ζ ω)) (hRcA ω) (hR0A ω) (a₀ ω)
      (I.clockX c (rootPt r.1) t ω).toNNReal
    rw [hsum] at hiv
    have hsupp' : tsupport φ ⊆ (I.chartX c (rootPt r.1) ω).2.1 ''
        (H \ fwdHull (fun s : ℝ => I.drvX c (rootPt r.1) s.toNNReal ω)
          ((I.clockX c (rootPt r.1) t ω).toNNReal : ℝ)) := by
      rw [hcsω]
      refine hsupp.trans ?_
      rw [hsh, ← hiv]
      exact subset_rfl
    rw [GW2Omx.integral_moved_eq c.κ (typedRhoL w) (typedRhoR w) hcs.1 hSc hS0 VLp VRp
      (fun ω => (I.clockX c (rootPt r.1) t ω).toNNReal) ch.u₀ ch.σa ch.kc hsupp']
    congr 1
    funext z
    rw [hcsω, hkc, ← e]
    rfl
  have hP := pair_rootX h12 h13 h12₀ h13₀ c r l a hroot hord hs0 hharm hh0 t htpos htcap hloc hloc₀ hGm hGs
    (R := R) (A := A) (a₀ := a₀) (σa := ch.σa) (typedRhoL w) (typedRhoR w) (xL := xL) (xR := xR) (U₀ := U₀)
    (U := U) hθ hread hclaim' hFm hFeq g hg' φ
  filter_upwards [hP] with ω hω hSω hlive hlt hsupp
  have hωG : ω ∈ G := ⟨hlive, hlt, hSω⟩
  rw [hB t] at hsupp
  rw [hω hωG hsupp]
  have e : ((A t ω : ℝ) - a₀ ω) = ((I.clockX c (rootPt r.1) t ω).toNNReal : ℝ) :=
    (coe_toNNReal_stgClockX hGT.1 hs0 hx (historyTime c r l) t (hV ω)).symm
  rw [e]

/-- **The kernel chain at ROOTX's corrected instance** (root `x`, one word type, `0 < t <` the cap). -/
theorem pair_instX (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)
    (hroot : rootPt r.1 = 0 ∨ rootPt r.1 ∈ lowerArcRoots c.κ c.b c.jumps) (hord : (historyProgram c r l).Pairwise (fun
      p q => p.2 < q.2)) (hs0 : 0 < c.s)
    {GT : Set Ω} (hGT : (∀ ω ∈ GT, PhysGoodX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α ω) ∧
      MeasurableSet GT ∧ (∀ᵐ ω ∂c.P, ω ∈ GT ↔ cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s))
    {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    (hA : IsRelVersionXA (rootPt r.1) c.s c.P c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α R V)
    (hV : ∀ ω, V ω ≠ ⊤) (ch : GW2Sdh.SchedChoice Ω) (hu₀ : IsBoundedHarmonicExtension c.b c.jumps ch.u₀)
    (hkc : ch.kc = chiC c.κ)
    (hβm : Measurable ch.β) (hE₀ : MeasurableSet ch.E₀) (w : WordType) (t : ℝ≥0) (htpos : 0 < t)
    (htcap : t < candidateCap c r a)
    (hlife : ∀ᵐ ω ∂c.P, ω ∈ liveEvRec c.κ w ch.β (GW2Rv.schedInstSX c r l a GT hA ch).E
        ((GW2Rv.schedInstSX c r l a GT hA ch).srecX c r l (rootPt r.1)) →
      (GW2Rv.schedInstSX c r l a GT hA ch).clockX c (rootPt r.1) t ω <
        (GW2Rv.schedInstSX c r l a GT hA ch).capX c (rootPt r.1) ω →
      (t : ℝ≥0∞) < candLife c r l a ω)
    (hfar : ∀ᵐ ω ∂c.P, ω ∈ liveEvRec c.κ w ch.β (GW2Rv.schedInstSX c r l a GT hA ch).E
        ((GW2Rv.schedInstSX c r l a GT hA ch).srecX c r l (rootPt r.1)) →
      GW2Wm.FarR (ch.β ((GW2Rv.schedInstSX c r l a GT hA ch).srecX c r l (rootPt r.1) ω))
        (sleLambda (16 / c.κ) - Real.pi * chiC c.κ + candAngle c r l a * chiC c.κ))
    (hclaim : ∀ g₀ : Ω → DistOn upperHalfPlaneOpens,
      IsLocalSetMean ((GW2Rv.schedInstSX c r l a GT hA ch).B 0) (centredField c.h ch.u₀) c.P g₀ →
      ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂c.P,
        ω ∈ liveEvRec c.κ w ch.β (GW2Rv.schedInstSX c r l a GT hA ch).E
          ((GW2Rv.schedInstSX c r l a GT hA ch).srecX c r l (rootPt r.1)) →
        (0 : ℝ≥0∞) < (GW2Rv.schedInstSX c r l a GT hA ch).capX c (rootPt r.1) ω →
        tsupport φ ⊆ H \ (GW2Rv.schedInstSX c r l a GT hA ch).B 0 ω →
        g₀ ω φ = ∫ z, stgMeanRX c.κ (rootPt r.1) c.s (cfRec c.s c.W c.ζ ω) (fun q => R q ω)
          (stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT V (historyTime c r l) ω) 0
          (bheProc c.κ (typedRhoL w) (typedRhoR w) ((GW2Rv.schedInstSX c r l a GT hA ch).drvX c (rootPt r.1))
            (fun i t ω => geomLW canonDrv (fun y => typedXL c.κ w (ch.β y.1)) i t
              ((GW2Rv.schedInstSX c r l a GT hA ch).srecX c r l (rootPt r.1) ω,
                relVar (GW2Rv.schedInstSX c r l a GT hA ch).Hr
                  ((GW2Rv.schedInstSX c r l a GT hA ch).drvX c (rootPt r.1))
                  ((GW2Rv.schedInstSX c r l a GT hA ch).capX c (rootPt r.1)) ω))
            (fun j t ω => geomRW canonDrv (fun y => typedXR c.κ w (ch.β y.1)) j t
              ((GW2Rv.schedInstSX c r l a GT hA ch).srecX c r l (rootPt r.1) ω,
                relVar (GW2Rv.schedInstSX c r l a GT hA ch).Hr
                  ((GW2Rv.schedInstSX c r l a GT hA ch).drvX c (rootPt r.1))
                  ((GW2Rv.schedInstSX c r l a GT hA ch).capX c (rootPt r.1)) ω)) ω 0)
          ch.u₀ ch.σa z * φ z)
    (g : Ω → DistOn upperHalfPlaneOpens)
    (hg : IsLocalSetMean ((GW2Rv.schedInstSX c r l a GT hA ch).B t) (centredField c.h ch.u₀) c.P g)
    (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂c.P, ω ∈ liveEvRec c.κ w ch.β (GW2Rv.schedInstSX c r l a GT hA ch).E
        ((GW2Rv.schedInstSX c r l a GT hA ch).srecX c r l (rootPt r.1)) →
      (GW2Rv.schedInstSX c r l a GT hA ch).clockX c (rootPt r.1) t ω <
        (GW2Rv.schedInstSX c r l a GT hA ch).capX c (rootPt r.1) ω →
      tsupport φ ⊆ H \ (GW2Rv.schedInstSX c r l a GT hA ch).B t ω →
      g ω φ = ∫ z, stgMeanRX c.κ (rootPt r.1) c.s (cfRec c.s c.W c.ζ ω) (fun q => R q ω)
          (stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT V (historyTime c r l) ω)
          (((GW2Rv.schedInstSX c r l a GT hA ch).clockX c (rootPt r.1) t ω).toNNReal : ℝ)
          (bheProc c.κ (typedRhoL w) (typedRhoR w) ((GW2Rv.schedInstSX c r l a GT hA ch).drvX c (rootPt r.1))
            (fun i t ω => geomLW canonDrv (fun y => typedXL c.κ w (ch.β y.1)) i t
              ((GW2Rv.schedInstSX c r l a GT hA ch).srecX c r l (rootPt r.1) ω,
                relVar (GW2Rv.schedInstSX c r l a GT hA ch).Hr
                  ((GW2Rv.schedInstSX c r l a GT hA ch).drvX c (rootPt r.1))
                  ((GW2Rv.schedInstSX c r l a GT hA ch).capX c (rootPt r.1)) ω))
            (fun j t ω => geomRW canonDrv (fun y => typedXR c.κ w (ch.β y.1)) j t
              ((GW2Rv.schedInstSX c r l a GT hA ch).srecX c r l (rootPt r.1) ω,
                relVar (GW2Rv.schedInstSX c r l a GT hA ch).Hr
                  ((GW2Rv.schedInstSX c r l a GT hA ch).drvX c (rootPt r.1))
                  ((GW2Rv.schedInstSX c r l a GT hA ch).capX c (rootPt r.1)) ω)) ω
            ((GW2Rv.schedInstSX c r l a GT hA ch).clockX c (rootPt r.1) t ω).toNNReal)
          ch.u₀ ch.σa z * φ z := by
  filter_upwards [pair_instSX h12 h13 h12₀ h13₀ c r l a hroot hord hs0 hGT hA hV ch hu₀ hkc hβm hE₀ w t htpos htcap
    MeasurableSet.univ (hlife.mono fun _ h _ => h) hfar hclaim g hg φ] with ω h
  exact h trivial

end InteractingSLE.Theorem14.GW2Kx
