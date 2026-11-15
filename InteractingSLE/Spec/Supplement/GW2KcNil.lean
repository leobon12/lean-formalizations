/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2KbWord
import InteractingSLE.Spec.Supplement.GW2PsmClaimS
import InteractingSLE.Spec.Supplement.GW2PsmPairI
import InteractingSLE.Spec.Supplement.GW2PsmTMean
import InteractingSLE.Spec.Supplement.GW2WxMap
import InteractingSLE.Spec.Supplement.GW2BfJ32Start
import InteractingSLE.Spec.Supplement.GW2SdpRoot
import InteractingSLE.Spec.Supplement.GW2SdsTip

/-!
# Claim(k) at ROOTX's instance for the history `l = []` (GEOM2 round 13, D47)

Packet PROVE-GW2-GEOM2, round 13. STAGEMEAN's `GW2Psm.ClaimAt c r [] a GT hA ch w` (the stage-start pairing of ROOTX's
corrected instance) for the history `l = []` at the root `0`, from GEOM2's base `GW2Kb.claim_base_root0_word`, with
every reading discharged at the instance:

* the tip, no contact, the version's regularity: as in STAGEMEAN's `GW2Psm.pair_instS`;
* **(R1)** the shape at every time `u ≤ T` of the root piece: ROOTX's `ae_compl_union_eq_relChartX_all` at the physical
  time `u`, with the clock `capA … 0 u` (`A 0 = 0` by `physClockX_zero`, `A T` = the stage start);
* **(R2)** the stage-start data in word form: the typed data of the word map at clock `0` extend to the base word's
  mean raised by `θa χ` (STAGEMEAN's `eqOn_typed_upW_mean`); the base word on ROOTX's record is the root word's stop
  word at the version's relative record up to the stage start (GEOM2's `baseWordX_augRecX` at `N = 1`); at the root
  `0` the root word is the joint word (`rootWordX_zero`).

* **`claimAt_nil`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped NNReal ENNReal
open LQGMetric (DistOn TestOn)
open QuantumZipper (H chiC fwdHull)

universe u

namespace InteractingSLE.Theorem14.GW2Kc

open GW2Kb GW2Psm GW2Omx Restart Exist Exist.Staged Exist.StagedLaw WholeField LocalSets GW2TipSystem
  GW2TipSystem.RootC24 GW2TipSystem.RootJ31 GW2Schedule GW2Tip GW2Sdi GW2Rd GW2Olm GW2Rz GW2Rv Supp8 Supp8.GB6
  GW2JointKernel Supp8.Q3Stop GW2Sde Restart.DomainMarkov MartChar.RealFlow Sec7.PocketTraversal Supp8.GB6.RelDrv
open Supp8.Q3Rel (invHull)

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **Claim(k) at ROOTX's corrected instance for the history `l = []`** (root `0`, one word type), for GEOM2's word
map with a counterflow word `cw` of the counterflow's data. -/
theorem claimAt_nil (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (a : ℕ) (hr0 : rootPt r.1 = 0) (hs0 : 0 < c.s) {GT : Set Ω}
    (hGT : (∀ ω ∈ GT, PhysGoodX (rootPt r.1) c.s c.W c.ζ (schedW c r [] a) (schedTr c r [] a) c.α ω) ∧
      MeasurableSet GT ∧ (∀ᵐ ω ∂c.P, ω ∈ GT ↔ cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s))
    {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    (hA : IsRelVersionXA (rootPt r.1) c.s c.P c.W c.ζ (schedW c r [] a) (schedTr c r [] a) c.α R V)
    (hV : ∀ ω, V ω ≠ ⊤) (ch : GW2Sdh.SchedChoice Ω) (hu₀ : IsBoundedHarmonicExtension c.b c.jumps ch.u₀)
    {cw : BoundaryWord} (hcw : IsCfWordOf c.κ c.P c.h c.W c.ζ cw)
    (hβ : ch.β = GW2Wm.schedWordMapX c.κ cw (rootPt r.1) c.s (historyProgram c r [])
      ((entryList ([] : List (EntryIdx c.Θ c.Q))).length + 1) (GW2Rd.length_historyProgram c r [])
      (candAngle c r [] a))
    (hσ : ch.σa = specOffset c.κ + candAngle c r [] a * chiC c.κ) (w : WordType) :
    ClaimAt c r [] a GT hA ch w := by
  classical
  intro g₀ hg₀ φ
  have hx : (0 : ℝ) ≤ rootPt r.1 := by rw [hr0]
  set I := schedInstSX c r [] a GT hA ch with hIdef
  set T : ℝ≥0 := historyTime c r [] with hT
  have hB0 : I.B 0 = schedUnionS c r [] a 0 := funext fun ω => schedUnionSX_eq_schedUnionS c r [] a hr0 0 ω
  have hg₀' : IsLocalSetMean (schedUnionS c r [] a 0) (centredField c.h ch.u₀) c.P g₀ := by
    rw [← hB0]; exact hg₀
  have hord : (historyProgram c r []).Pairwise (fun p q => p.2 < q.2) := List.pairwise_singleton _ _
  have hloc₀ := isHistoryAvoidanceLocal_stgF h12 h13 c r [] a hr0 (Gm.timeOrdered_of_pairwise_lt hord) hu₀ 0
  set G : Set Ω := liveEvRec c.κ w ch.β I.E (I.srecX c r [] (rootPt r.1)) ∩
    {ω | (0 : ℝ≥0∞) < I.capX c (rootPt r.1) ω} with hGdef
  have hGs : ∀ ω ∈ G, oldSuccess c r [] ω := fun ω hω =>
    (GW2Sdi.augRec_mem_succRec_iff c r [] _ ω).1 hω.1.1.1.2
  have hver := hA.1
  have hv := hver.1
  have hρ := hA.1.2.choose_spec
  have hfin : ∀ᵐ ω ∂c.P, I.srecX c r [] (rootPt r.1) ω ∈ I.E →
      stgStartMX (rootPt r.1) c.s c.W c.ζ I.W I.GT I.V I.T ω ≠ ⊤ :=
    Eventually.of_forall fun ω _ => ne_top_of_le_ne_top (hV ω) (min_le_right _ _)
  have hEgood := StageInst.E_good_of_recordX I hv hρ.2.1 hρ.2.2 inter_subset_right hfin
  have hGT0 : ∀ ω ∈ GT, PhysGoodX 0 c.s c.W c.ζ (schedW c r [] a) (schedTr c r [] a) c.α ω := by
    rw [← hr0]; exact hGT.1
  have hv0 : IsRelVersionX 0 c.s c.P c.W c.ζ (schedW c r [] a) (schedTr c r [] a) c.α R V := by
    rw [← hr0]; exact hv
  have hcfreg := GW2Later.ae_counterflow_regular h13 c.hκ c.hcf c.hζ
  -- the clock of the root piece, and the stage start
  set A : ℝ≥0 → Ω → ℝ≥0 := fun u ω => capA (rootPt r.1) c.s c.W c.ζ (schedW c r [] a) GT V 0 u ω with hAdef
  have hAT : ∀ ω, A T ω = stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r [] a) GT V T ω := fun ω => by
    rw [← capA_zero T ω]
    show (min (physClockX (rootPt r.1) c.s c.W c.ζ (schedW c r [] a) GT (0 + T) ω) (V ω)).toNNReal =
      (min (physClockX (rootPt r.1) c.s c.W c.ζ (schedW c r [] a) GT (T + 0) ω) (V ω)).toNNReal
    rw [zero_add, add_zero]
  set VLp : Fin w.1 → ℝ≥0 → Ω → ℝ := fun i t ω => geomLW canonDrv (fun y => typedXL c.κ w (ch.β y.1)) i t
    (I.srecX c r [] (rootPt r.1) ω, relVar I.Hr (I.drvX c (rootPt r.1)) (I.capX c (rootPt r.1)) ω) with hVLp
  set VRp : Fin w.2.1 → ℝ≥0 → Ω → ℝ := fun j t ω => geomRW canonDrv (fun y => typedXR c.κ w (ch.β y.1)) j t
    (I.srecX c r [] (rootPt r.1) ω, relVar I.Hr (I.drvX c (rootPt r.1)) (I.capX c (rootPt r.1)) ω) with hVRp
  set U₀ : Ω → ℂ → ℝ := fun ω => bheProc c.κ (typedRhoL w) (typedRhoR w) (I.drvX c (rootPt r.1)) VLp VRp ω 0
    with hU₀
  have hread : ∀ᵐ ω ∂c.P, ω ∈ G →
      c.α ω c.s ∈ H ∧
      (∀ v ∈ Icc 0 c.s, ∀ u ≤ historyTime c r [], c.α ω v * schedTr c r [] a ω u + 1 ≠ 0) ∧
      Continuous (fun u => R u ω) ∧ R 0 ω = 0 ∧ A 0 ω = 0 ∧
      ContinuousOn (fun u => A u ω) (Icc 0 (historyTime c r [])) ∧
      (∀ u ≤ historyTime c r [], H \ (invHull (fun q : ℝ => c.W q.toNNReal ω) c.s ∪
          fwdHull (fun q : ℝ => schedW c r [] a q.toNNReal ω) u) =
        (RelSafeS.relChart (gb6Rec c.s c.W c.ζ ω)).2.1 '' (H \ fwdHull (Ito.rpath fun q => R q ω) (A u ω))) ∧
      ∃ rec' : RecData, rtime rec' = (A (historyTime c r []) ω : ℝ) ∧
        EqOn (rdrv rec') (Ito.rpath fun q => R q ω) (Icc 0 (A (historyTime c r []) ω : ℝ)) ∧
        ∀ z ∈ H, U₀ ω z = (stopWord c.κ (jw c.κ cw c.s c.W c.ζ ω, (rootEntry r.1).1, rec')).mean z +
          candAngle c r [] a * chiC c.κ := by
    filter_upwards [hEgood, hGT.2.2, ae_compl_union_eq_relChartX_all hGT.1 hs0 hx hv,
      ae_noContact_root0 hGT0 hs0 hv0, c.hζ, hcfreg] with ω hEω hGTω hshω hncω hζω hcfω hωG
    obtain ⟨hlive, hcap⟩ := hωG
    have hωGT : ω ∈ GT := hGTω.2 (hEω hlive.1).1
    have hsucc : oldSuccess c r [] ω := hGs ω ⟨hlive, hcap⟩
    have hRc : Continuous fun u => R u ω := hv.2.1 ω
    have hR0 : R 0 ω = 0 := hv.2.2.1 ω
    obtain ⟨γ', -, hWc, hW0, -⟩ := hcfω
    have hsζ : (c.s : ℝ≥0∞) < c.ζ ω := by rw [hζω]; exact ENNReal.coe_lt_top
    -- the stage start is below the cap
    have hstartne : stgStartMX (rootPt r.1) c.s c.W c.ζ (schedW c r [] a) GT V T ω ≠ ⊤ :=
      ne_top_of_le_ne_top (hV ω) (min_le_right _ _)
    have hltT : min (physClockX (rootPt r.1) c.s c.W c.ζ (schedW c r [] a) GT T ω) (V ω) < V ω := by
      have h2 : I.capX c (rootPt r.1) ω = V ω - stgStartMX (rootPt r.1) c.s c.W c.ζ (schedW c r [] a) GT V T ω := by
        show V ω - ((stgStartMX (rootPt r.1) c.s c.W c.ζ (schedW c r [] a) GT V T ω).toNNReal : ℝ≥0∞) = _
        rw [ENNReal.coe_toNNReal hstartne]
      have h3 := hcap
      simp only [mem_ofPred_eq] at h3
      rw [h2] at h3
      exact tsub_pos_iff_lt.1 h3
    have hltu : ∀ u ≤ T, min (physClockX (rootPt r.1) c.s c.W c.ζ (schedW c r [] a) GT u ω) (V ω) < V ω :=
      fun u hu => lt_of_le_of_lt (monotone_min_physClockX hGT.1 hs0 hx (V := V) ω hu) hltT
    have hb : baseRead (rootPt r.1) c.s (cfRec c.s c.W c.ζ ω) = 0 := by
      rw [hr0]; exact baseRead_zero_cfRec c.s c.W c.ζ ω hζω
    refine ⟨(physGoodX_tip_marks (hGT.1 ω hωGT)).1, ?_, hRc, hR0, ?_,
      (continuous_capA hGT.1 hs0 hx 0 (hV ω)).continuousOn, ?_, ?_⟩
    · have hlt0 : min (physClockX 0 c.s c.W c.ζ (schedW c r [] a) GT T ω) (V ω) < V ω := by
        rw [← hr0]; exact hltT
      exact hncω hωGT T hlt0
    · show (min (physClockX (rootPt r.1) c.s c.W c.ζ (schedW c r [] a) GT (0 + 0) ω) (V ω)).toNNReal = 0
      rw [add_zero, physClockX_zero hGT.1 hs0 hx ω, min_eq_left zero_le, ENNReal.toNNReal_zero]
    · intro u hu
      have h := hshω hωGT u (hltu u hu)
      rw [relChartX_of_baseRead_zero hb] at h
      have hid : (fun z : ℂ => z + ((rootPt r.1 : ℝ) : ℂ)) = id := funext fun z => by simp [hr0]
      rw [hid, image_id, show Supp8.Q3Rel.invHull (rdrv (cfRec c.s c.W c.ζ ω)) (c.s : ℝ) =
        invHull (fun q : ℝ => c.W q.toNNReal ω) c.s from
          Supp8.RelSafeS.invHull_record_eq hW0 hWc.continuousOn hsζ] at h
      show _ = _ '' (H \ fwdHull (Ito.rpath fun q => R q ω)
        (min (physClockX (rootPt r.1) c.s c.W c.ζ (schedW c r [] a) GT (0 + u) ω) (V ω)).toNNReal)
      rw [zero_add]
      exact h
    · -- (R2) the stage-start data in word form
      set L := historyProgram c r [] with hLdef
      have hLN : L.length = (entryList ([] : List (EntryIdx c.Θ c.Q))).length + 1 := GW2Rd.length_historyProgram c r []
      set P : Fin ((entryList ([] : List (EntryIdx c.Θ c.Q))).length + 1) → RecData :=
        fun k => stopRec c.hκ c.h12p c.βA c.c₀ c.h (schedSpecOf r.1 []) k ω with hP
      have hagree : ∀ u ≤ T, RootJ31.joinedRead L (fun i => P (Fin.cast hLN i)) u = schedW c r [] a u ω := by
        intro u hu
        have e1 : schedW c r [] a u ω = Gm.futureJoined c r [] a ω u :=
          congrFun (schedW_of_oldSuccess c r [] a hsucc) u
        rw [e1, GW2Bf.futureJoined_eq_histJoined c r [] a ω hu]
        rfl
      have hE0 : (entryList ([] : List (EntryIdx c.Θ c.Q))).length = 0 := rfl
      have hbw := GW2Wm.baseWordX_augRecX (x₀ := rootPt r.1) (sp := c.s) (W := schedW c r [] a) (Wα := c.W)
        (ζα := c.ζ) (GT := GT) (V := V) (T := T) (R := R) (γ := schedTr c r [] a) (α := c.α) c.κ cw hGT.1 hs0 hx
        L _ hLN (xr := stageEncRec c r []) (ω := ω) (P := P) rfl hRc hR0 hωGT (hV ω)
        (fun j hj => by
          have hj0 : j = 0 := by rw [hE0] at hj; omega
          subst hj0
          exact zero_le)
        (fun j hj => by
          have hj0 : j = 0 := by rw [hE0] at hj; omega
          subst hj0
          exact zero_le)
        (fun j h0 h1 => by rw [hE0] at h1; omega) hagree
      have hrw : GW2Wm.rootWordX c.κ cw (rootPt r.1) c.s (cfRec c.s c.W c.ζ ω) = jw c.κ cw c.s c.W c.ζ ω := by
        have hb0 : baseRead 0 c.s (cfRec c.s c.W c.ζ ω) = 0 := baseRead_zero_cfRec c.s c.W c.ζ ω hζω
        rw [hr0]
        exact GW2Sdp.rootWordX_zero c.κ cw c.s _ hb0
      have hdrv : (fun u => GW2Rd.stgDrv (fun q => R q ω) 0 u) = fun q => R q ω := by
        funext q
        simp [GW2Rd.stgDrv, hR0]
      have hbd0 : GW2Wm.trueBdX (rootPt r.1) c.s c.W c.ζ (schedW c r [] a) GT V L
          ((entryList ([] : List (EntryIdx c.Θ c.Q))).length + 1) T ω 0 = 0 := by
        simp [GW2Wm.trueBdX]
      have hbd1 : GW2Wm.trueBdX (rootPt r.1) c.s c.W c.ζ (schedW c r [] a) GT V L
          ((entryList ([] : List (EntryIdx c.Θ c.Q))).length + 1) T ω 1 = A T ω := by
        rw [hAT ω]
        simp [GW2Wm.trueBdX, hE0]
      have hβs : ch.β (I.srecX c r [] (rootPt r.1) ω) = GW2Rd.upW (candAngle c r [] a * chiC c.κ)
          (stopWord c.κ (jw c.κ cw c.s c.W c.ζ ω, (rootEntry r.1).1,
            recOf ((A T ω : ℝ≥0) : ℝ≥0∞) (fun q => R q ω, ⊤))) := by
        rw [hβ]
        show GW2Rd.upW (candAngle c r [] a * chiC c.κ) (GW2Wm.baseWordX c.κ cw (rootPt r.1) c.s L _ hLN
          (GW2Rd.augRec (stageEncRec c r []) (stgPreRecX (rootPt r.1) c.s c.W c.ζ (schedW c r [] a) GT V T R) ω)) = _
        rw [hbw]
        show GW2Rd.upW (candAngle c r [] a * chiC c.κ) (stopWord c.κ
          (GW2Wm.rootWordX c.κ cw (rootPt r.1) c.s (cfRec c.s c.W c.ζ ω), GW2Wm.progAngle L 0,
            recOf (((GW2Wm.trueBdX (rootPt r.1) c.s c.W c.ζ (schedW c r [] a) GT V L _ T ω 1 -
              GW2Wm.trueBdX (rootPt r.1) c.s c.W c.ζ (schedW c r [] a) GT V L _ T ω 0 : ℝ≥0)) : ℝ≥0∞)
              (fun u => GW2Rd.stgDrv (fun q => R q ω)
                (GW2Wm.trueBdX (rootPt r.1) c.s c.W c.ζ (schedW c r [] a) GT V L _ T ω 0) u, ⊤))) = _
        rw [hbd0, hbd1, tsub_zero, hdrv, hrw]
        rfl
      refine ⟨recOf ((A T ω : ℝ≥0) : ℝ≥0∞) (fun q => R q ω, ⊤), ?_, ?_, fun z hz => ?_⟩
      · rw [Exist.StagedLaw.rtime_recOf_coe]
        simp [hT]
      · intro y hy
        have hy' : y.toNNReal ≤ A T ω := Real.toNNReal_le_iff_le_coe.2 hy.2
        have h1 := GW2Sds.rdrv_recOf_top_eq hRc hR0 hy'
        rw [Real.coe_toNNReal _ hy.1] at h1
        rw [h1]
        rfl
      · have hdc : Continuous fun q => I.drvX c (rootPt r.1) q ω := continuous_stgDrv hRc _
        have hd0 : I.drvX c (rootPt r.1) 0 ω = 0 := stgDrv_zero _ _
        have hU := bhe_bheProc_typedX_zero (r := r) (l := []) I (rootPt r.1) w ω hdc hd0
        have hU' := hU
        rw [show I.β (I.srecX c r [] (rootPt r.1) ω) = _ from hβs] at hU'
        have hw : wordType c.κ (ch.β (I.srecX c r [] (rootPt r.1) ω)) = w := hlive.2
        rw [hβs] at hw
        exact eqOn_typed_upW_mean c.hκ _ (isSorted_stopWord _ _) _ hw hU' z hz
  have hbase := claim_base_root0_word c r a h12 h13 hr0 hcw hu₀ hloc₀ (G := G) hGs (R := R) (A := A)
    (θa := candAngle c r [] a) (σa := ch.σa) hσ (U₀ := U₀) hread g₀ hg₀' φ
  filter_upwards [hbase] with ω h hlive hcap hsupp
  rw [hB0] at hsupp
  rw [h ⟨hlive, hcap⟩ hsupp, hAT ω]
  rfl

end InteractingSLE.Theorem14.GW2Kc
