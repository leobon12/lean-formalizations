/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R6SafeMeet
import InteractingSLE.Spec.Sec7.R6SafeInclInf

/-!
# Lemma R.6's face: the common point for the shapes opening at the flow seed

PROVE-R6-SAFE, round 4b. The seed-opening versions of `R6SafeMeet`: the outer half (outer pocket `C` opening at the
flow seed: the current inverse lands at the tip, `HOuter.mem_domain_of_not_mem_fillH_inf`), the inner half for a
contained pocket opening at the flow seed, and the faces `MixedInf` (outer at the seed, bounded inner) and
`MixedInfInf` (both at the seed) reduced to `R6FaceR` near the tip's inner relative time.

## Main results

* `relCapInf_lt_relCapInf_of_visit`, `exists_outer_dom_near_tipInf`, `exists_rat_mem_inner_domInf`;
* `R6FaceSMixedInfRemaining`, **`r6FaceQMixedInfRemaining_of_faceS`**;
* `R6FaceSMixedInfInfRemaining`, **`r6FaceQMixedInfInfRemaining_of_faceS`**.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric
open QuantumZipper (H Hbar)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R6Safe

open Sec6 PocketTraversal Lemma71C PocketJordan PocketCoord PocketCoupling PocketStop PocketStopField HOuter
  PocketWordAssembly PocketSeedOpen

/-! ### The relative capacity increases strictly after a visit (junction at infinity) -/

section StrictInf

variable {W : ℝ → ℝ} {η : ℝ → ℂ} {C : Set ℂ} {α₁ α₂ : ℝ → ℂ} {τ : ℝ} {ψ : ℂ → ℂ}

/-- **The relative capacity increases strictly after a visit** (junction at infinity). -/
theorem relCapInf_lt_relCapInf_of_visit (hP : IsReversePocketInf W η C α₁ α₂ τ)
    (hAC : AttachmentConstancyInf η C α₁ α₂ τ) (hψ : IsJordanCoordInf C (α₁ 0) ψ) {a b : ℝ}
    (ha : τ ≤ a) (hab : a < b) (ha0 : 0 ≤ a) (hv : η a ∈ C) :
    PocketStopMarked.relCapInf η C τ ψ a < PocketStopMarked.relCapInf η C τ ψ b := by
  have haI : a ∈ visitSetInf η C τ := ⟨hP.mem_Ioi_of_mem ha0 hv, hv⟩
  obtain ⟨t', ht', ht'I⟩ := hP.exists_mem_Ioo_of_mem hab ⟨le_rfl, hab.le⟩ haI
  have hne : pocketClockInf η C τ a ≠ pocketClockInf η C τ b := fun h =>
    Set.disjoint_left.1 ((erasureClock_eq_iff hP.isOpen_visitSet hab).1 h) ht' ht'I
  have hlt : pocketClockInf η C τ a < pocketClockInf η C τ b :=
    lt_of_le_of_ne (hP.monotone_clock hab.le) hne
  have hb : τ ≤ b := ha.trans hab.le
  have hL : pocketClockInf η C τ b < clockEnd η C τ := hP.clock_lt_clockEnd hAC hb
  have h0 : 0 ≤ pocketClockInf η C τ a := hP.clock_nonneg ha
  have hrt : PocketStopMarked.relTimeInf η C τ a < PocketStopMarked.relTimeInf η C τ b := by
    unfold PocketStopMarked.relTimeInf
    rw [div_lt_div_iff₀ (sub_pos.2 (hlt.trans hL)) (sub_pos.2 hL)]
    nlinarith
  exact (isDrivenCurve_relCurve_of_isReversePocketInf hP hAC hψ).strictMonoOn_capClock
    (PocketStopMarked.relTimeInf_nonneg hP hAC ha) (PocketStopMarked.relTimeInf_nonneg hP hAC hb) hrt

end StrictInf

/-! ### The two halves of (a3) at infinity -/

section MeetInf

variable {Ω : Type*} {A A' : Set Ω} {R L R' L' : Ω → ℝ≥0 → ℂ} {r r' : ℝ≥0} {W : Ω → ℝ → ℝ}
  {η : Ω → ℝ → ℂ} {ψ ψ' : Ω → ℂ → ℂ} {n n' : Ω → ℤ} {q : ℝ≥0} {ω : Ω}

/-- The fibre end `T_C(q)` of the pocket `C = cfPocket R L r` opening at the flow seed, at relative capacity `q`. -/
def outerFibreEndInf (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (η : Ω → ℝ → ℂ) (ψ : Ω → ℂ → ℂ) (q : ℝ≥0) (ω : Ω) : ℝ :=
  pocketFibreInf (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0))
    (clockOf (clockEnd (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0)))
      (capInv (travAllInf R L r η ψ ω) q))

/-- The relative capacity of the pocket `cfPocket R L r` opening at the flow seed, reached at the ambient time `t`. -/
def innerRelCapInf (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (η : Ω → ℝ → ℂ) (ψ : Ω → ℂ → ℂ) (t : ℝ) (ω : Ω) : ℝ :=
  PocketStopMarked.relCapInf (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0)) (ψ ω) t

/-- **The outer half of (a3)** (outer pocket opening at the flow seed). -/
theorem exists_outer_dom_near_tipInf (hcfg : ∀ ω ∈ A, IsOuterCfgInf (R ω) (L ω) r (W ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω)) (hω : ω ∈ A)
    (hq : (q : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω)) {V : Set ℂ} (hV : IsOpen V)
    (htip : η ω (outerFibreEndInf R L r η ψ q ω) ∈ V)
    (htipC : η ω (outerFibreEndInf R L r η ψ q ω) ∈ cfPocket (R ω) (L ω) r) :
    ∃ z ∈ V, z ∈ ((relChart (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω))
        (travAllInf R L r η ψ) q ω).dom : Set ℂ) ∧
      z ∈ H \ QuantumZipper.fwdHull (W ω) (outerFibreEndInf R L r η ψ q ω) := by
  have hG : ∀ ω ∈ A, IsChangeConfigInc (R ω) (L ω) r := fun ω hω => (hcfg ω hω).conf
  have hCo : ∀ ω ∈ A, IsOpen (cfPocket (R ω) (L ω) r) := fun ω hω =>
    isOpen_image_negInv' (hG ω hω).isOpen_changePocket (hG ω hω).changePocket_subset_H
  have hCH : ∀ ω ∈ A, cfPocket (R ω) (L ω) r ⊆ H := fun ω hω =>
    PocketJordan.image_negInv_subset_H (hG ω hω).changePocket_subset_H
  have hγ : IsDrivenCurve (travAllInf R L r η ψ ω) := ((hcfg ω hω).props (hψ ω hω)).1
  obtain ⟨hc, hdom, hfwd⟩ := R5Phase.shiftChart_dom_facts hCo hCH (fun ω hω => (hψ ω hω).2.2.2.1) n ω hω
  have hO : (relChart (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω))
      (travAllInf R L r η ψ) q ω).IsConformal := PocketStopSide.isConformal_relChart_of_driven hγ hq hc
  set T := outerFibreEndInf R L r η ψ q ω with hTdef
  have hTrace : capTrace (travAllInf R L r η ψ ω) q =
      (shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)).1 (η ω T) := by
    rw [hfwd htipC]
    rfl
  have hlim := PocketStopSide.tendsto_relative_inverse_tip hc hγ hq (p := η ω T)
    (by rw [hdom]; exact htipC) hTrace
  have hNe : (𝓝[H] (0 : ℂ)).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (by
    rw [QuantumZipper.CA.Car.closure_H_eq_Hbar]
    exact mem_Hbar_of_im_eq_zero (by simp))
  obtain ⟨w, hwV, hwH⟩ := ((hlim.eventually_mem (hV.mem_nhds htip)).and
    (self_mem_nhdsWithin : ∀ᶠ w in 𝓝[H] (0 : ℂ), w ∈ H)).exists
  have hzdom := hO.inv_mem_dom hwH
  have hzD : (relChart (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω))
      (travAllInf R L r η ψ) q ω).2.1 w ∈ _ := hzdom
  rw [SetLike.mem_coe.symm, relChart_dom_eq_inter (n := n) hCo hCH (fun ω hω => (hψ ω hω).2.2.2.1) hω hγ hq] at hzD
  have hP := (hcfg ω hω).erase
  have hL := hP.clockEnd_pos
  have hu0 : 0 ≤ capInv (travAllInf R L r η ψ ω) q := capInv_nonneg _ _
  have hv := clockOf_mem_Ico hL hu0
  have hψ' : IsJordanCoordInf (cfPocket (R ω) (L ω) r) (cfArcRInf (R ω) (L ω) r 0) (ψ ω) := by
    rw [IsChangeConfigInc.cfArcRInf_zero]
    exact hψ ω hω
  refine ⟨_, hwV, hzdom, mem_domain_of_not_mem_fillH_inf (W := W ω) hP (hcfg ω hω).trace (hCH ω hω) hψ' hv
    hzD.1 fun hK => hzD.2.2 ?_⟩
  have himg : travAllInf R L r η ψ ω '' Icc 0 (capInv (travAllInf R L r η ψ ω) q) =
      (fun v => ψ ω (erasedPathInf (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0)) v)) ''
        Icc 0 (clockOf (clockEnd (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0)))
          (capInv (travAllInf R L r η ψ ω) q)) := by
    change relCurve (fun v => ψ ω (erasedPathInf (η ω) (cfPocket (R ω) (L ω) r)
      (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0)) v))
      (clockEnd (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0))) '' _ = _
    rw [image_relCurve_Icc _ hL hu0]
  rw [hγ.fwdHull_segDriver q.coe_nonneg (by rw [ENNReal.ofReal_coe_nnreal]; exact hq), himg]
  exact hK

/-- The fibre end of a pocket opening at the flow seed is nonnegative. -/
theorem outerFibreEndInf_nonneg (hcfg : ∀ ω ∈ A, IsOuterCfgInf (R ω) (L ω) r (W ω) (η ω)) (hω : ω ∈ A) :
    0 ≤ outerFibreEndInf R L r η ψ q ω :=
  (hcfg ω hω).erase.fibre_nonneg (clockOf_mem_Ico (hcfg ω hω).erase.clockEnd_pos (capInv_nonneg _ _))

/-- **The inner half of (a3)** (contained pocket opening at the flow seed). -/
theorem exists_rat_mem_inner_domInf (hcfg' : ∀ ω ∈ A', IsCfPocketConfigInf (R' ω) (L' ω) r' (W ω) (η ω))
    (hψ' : ∀ ω ∈ A', IsCfJordanInf (R' ω) (L' ω) r' (ψ' ω)) (hω' : ω ∈ A') {T : ℝ} (hT0 : 0 ≤ T)
    (htip : η ω T ∈ cfPocket (R' ω) (L' ω) r') {z : ℂ} (hzU : z ∈ cfPocket (R' ω) (L' ω) r')
    (hphys : z ∈ H \ QuantumZipper.fwdHull (W ω) T) {ε : ℝ} (hε : 0 < ε) :
    ∃ q' : ℚ, innerRelCapInf R' L' r' η ψ' T ω < q' ∧ (q' : ℝ) < innerRelCapInf R' L' r' η ψ' T ω + ε ∧
      ((StripSys.rt q' : ℝ≥0) : ℝ≥0∞) < capLife (travAllInf R' L' r' η ψ' ω) ∧
      T < R5Ref.leftStopInf R' L' r' η ψ' (StripSys.rt q') ω ∧
      z ∈ ((relChart (fun ω => shiftChart (pChart A' (fun ω => cfPocket (R' ω) (L' ω) r') ψ' ω) (n' ω))
          (travAllInf R' L' r' η ψ') (StripSys.rt q') ω).dom : Set ℂ) := by
  have hG' : ∀ ω ∈ A', IsChangeConfigInc (R' ω) (L' ω) r' := fun ω hω => (hcfg' ω hω).conf
  have hCo' : ∀ ω ∈ A', IsOpen (cfPocket (R' ω) (L' ω) r') := fun ω hω =>
    isOpen_image_negInv' (hG' ω hω).isOpen_changePocket (hG' ω hω).changePocket_subset_H
  have hCH' : ∀ ω ∈ A', cfPocket (R' ω) (L' ω) r' ⊆ H := fun ω hω =>
    PocketJordan.image_negInv_subset_H (hG' ω hω).changePocket_subset_H
  have hswal : ENNReal.ofReal T < QuantumZipper.swallowTime (W ω) z := by
    by_contra hle
    exact hphys.2 ⟨hphys.1, not_lt.1 hle⟩
  obtain ⟨T₁, -, hTT₁, hT₁s⟩ := ENNReal.lt_iff_exists_real_btwn.1 hswal
  have hTT₁' : T < T₁ := (ENNReal.ofReal_lt_ofReal_iff'.1 hTT₁).1
  obtain ⟨hP', hJ'⟩ := R5Ref.pocket_of_cfgInf (hcfg' ω hω') (hψ' ω hω')
  have hAC := (hcfg' ω hω').attach
  have hTI : firstHit (η ω) (cfArcRInf (R' ω) (L' ω) r' 0) ≤ T := (hP'.mem_Ioi_of_mem hT0 htip).le
  have hT₁I : firstHit (η ω) (cfArcRInf (R' ω) (L' ω) r' 0) ≤ T₁ := hTI.trans hTT₁'.le
  have hcapLT := relCapInf_lt_relCapInf_of_visit hP' hAC hJ' hTI hTT₁' hT0 htip
  obtain ⟨q', hq'lo, hq'hi⟩ := exists_rat_btwn (lt_min hcapLT (lt_add_of_pos_right
    (innerRelCapInf R' L' r' η ψ' T ω) hε))
  have hc0 : 0 ≤ innerRelCapInf R' L' r' η ψ' T ω :=
    (isDrivenCurve_relCurve_of_isReversePocketInf hP' hAC hJ').capClock_nonneg
      (PocketStopMarked.relTimeInf_nonneg hP' hAC hTI)
  have hqpos : (0 : ℝ) < q' := hc0.trans_lt hq'lo
  have hrt : ((StripSys.rt q' : ℝ≥0) : ℝ) = q' := Real.coe_toNNReal _ hqpos.le
  have hq'0 : (0 : ℝ) ≤ ((StripSys.rt q' : ℝ≥0) : ℝ) := NNReal.coe_nonneg _
  have hq'T₁ : (q' : ℝ) ≤ innerRelCapInf R' L' r' η ψ' T₁ ω := (hq'hi.trans_le (min_le_left _ _)).le
  have hlive : ENNReal.ofReal ((StripSys.rt q' : ℝ≥0) : ℝ) <
      capLife (PocketStopMarked.travInf (η ω) (cfPocket (R' ω) (L' ω) r')
        (firstHit (η ω) (cfArcRInf (R' ω) (L' ω) r' 0)) (ψ' ω)) := by
    rw [hrt]
    exact (ENNReal.ofReal_le_ofReal hq'T₁).trans_lt (PocketStopMarked.relCapInf_lt_capLife hP' hAC hJ' hT₁I)
  have hlive' : ((StripSys.rt q' : ℝ≥0) : ℝ≥0∞) < capLife (travAllInf R' L' r' η ψ' ω) := by
    rw [← ENNReal.ofReal_coe_nnreal]
    exact hlive
  have hLSlt : T < R5Ref.leftStopInf R' L' r' η ψ' (StripSys.rt q') ω := by
    by_contra hle
    have h := (PocketStopMarked.ambTime0Inf_le_iff hP' hAC hJ' hq'0 hlive hTI).1 (not_lt.1 hle)
    rw [hrt] at h
    exact absurd hq'lo (not_lt.2 h)
  have hLSle : R5Ref.leftStopInf R' L' r' η ψ' (StripSys.rt q') ω ≤ T₁ :=
    (PocketStopMarked.ambTime0Inf_le_iff hP' hAC hJ' hq'0 hlive hT₁I).2 (by rw [hrt]; exact hq'T₁)
  obtain ⟨hcI, hdomI, heqI⟩ := R5Phase.shiftChart_dom_facts hCo' hCH' (fun ω hω => (hψ' ω hω).2.2.2.1) n' ω hω'
  have hLS0 : 0 ≤ R5Ref.leftStopInf R' L' r' η ψ' (StripSys.rt q') ω := hT0.trans hLSlt.le
  refine ⟨q', hq'lo, hq'hi.trans_le (min_le_right _ _), hlive', hLSlt, ?_⟩
  rw [R5Ref.current_dom_eqInf (c := fun ω => shiftChart (pChart A' (fun ω => cfPocket (R' ω) (L' ω) r') ψ' ω)
    (n' ω)) hω' (hcfg' ω hω') (hψ' ω hω') hcI hdomI heqI hlive', ← (hcfg' ω hω').trace.2.2 _ hLS0]
  refine ⟨hzU, hphys.1, fun hK => ?_⟩
  have h1 : QuantumZipper.swallowTime (W ω) z ≤ ENNReal.ofReal T₁ :=
    hK.2.trans (ENNReal.ofReal_le_ofReal hLSle)
  exact absurd hT₁s (not_lt.2 h1)

end MeetInf


/-! ### The faces of shapes `MixedInf` and `MixedInfInf` near the tip's inner relative time -/

section FaceSInf

open MeasureTheory ProbabilityTheory
open LQGMetric (DistOn)
open QuantumZipper (chiC)
open scoped Real
open R6Fin WholeField R7Outer R7Leaves R6Nest R6Rel R6Cert HOuter PocketMarks PocketStopWallsFin PocketStopSide

universe u

/-- **Named, unproved: R.6's face, shape `MixedInf`, near the tip's inner relative time** (as
`R6FaceSMixedRemaining`; the common point and the time ordering are proved, `r6FaceQMixedInfRemaining_of_faceS`). -/
def R6FaceSMixedInfRemaining (k rL rR c c' : ℝ) : Prop :=
  (k / 2 - 4 < rL ∧ rR ≤ k / 2 - 4) ∨ (rL ≤ k / 2 - 4 ∧ k / 2 - 4 < rR) →
  ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistOn upperHalfPlaneOpens) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞)
    (αR βR βL αL : Ω → ℝ≥0 → ℂ) (ζαR ζβR ζβL ζαL : Ω → ℝ≥0∞),
    IsR7OuterConfig k rL rR c c' P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL →
    ∀ (R L : Ω → ℝ≥0 → ℂ) (η : Ω → ℝ → ℂ), IsR7Versions P W' αR αL R L η →
    ∀ MR ML : Ω → ℝ≥0 → ℂ, IsFrontierVersion P βR MR → IsFrontierVersion P βL ML →
    ∀ (r : ℝ≥0) (A A' : Set Ω) (ψ ψ' : Ω → ℂ → ℂ) (n n' : Ω → ℤ) (s q : ℚ),
      (∀ ω ∈ A, IsOuterCfgInf (R ω) (L ω) r (fun t : ℝ => W' t.toNNReal ω) (η ω) ∧
        IsCfJordanInf (R ω) (L ω) r (ψ ω)) →
      (∀ ω ∈ A', IsCfPocketConfig (innerRight k rL R MR ω) (innerLeft k rR L ML ω) (StripSys.rt s)
          (fun t : ℝ => W' t.toNNReal ω) (η ω) ∧
        IsCfJordan (innerRight k rL R MR ω) (innerLeft k rR L ML ω) (StripSys.rt s) (ψ' ω)) →
      ∀ᵐ ω ∂P, ω ∈ A → ω ∈ A' →
        ω ∈ nestRelEventInf R L r η ψ MR ML (innerRight k rL R MR) (innerLeft k rR L ML) s q →
        ∃ ε : ℝ, 0 < ε ∧ ∀ q' : ℚ,
          innerRelCap (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ'
              (outerFibreEndInf R L r η ψ (StripSys.rt q) ω) ω < q' →
          (q' : ℝ) < innerRelCap (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ'
              (outerFibreEndInf R L r η ψ (StripSys.rt q) ω) ω + ε →
          ((StripSys.rt q' : ℝ≥0) : ℝ≥0∞) <
            capLife (travAll (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ' ω) →
          outerFibreEndInf R L r η ψ (StripSys.rt q) ω <
            R5Ref.leftStop (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ' (StripSys.rt q') ω →
          ((relChart (fun ω => shiftChart (pChart A' (fun ω => cfPocket (innerRight k rL R MR ω)
                (innerLeft k rR L ML ω) (StripSys.rt s)) ψ' ω) (n' ω))
              (travAll (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ') (StripSys.rt q')
                ω).dom : Set ℂ) ⊆
            (relChart (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω))
              (travAllInf R L r η ψ) (StripSys.rt q) ω).dom →
          R6FaceR (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) (fun _ : Fin 1 => innerRight k rL rL (k / 2 - 4))
            (fun _ : Fin 1 => innerLeft k rR rR (k / 2 - 4))
            (fun i => geomLW (fun t ω => segDriver (travAllInf R L r η ψ ω) t) (fun _ => LP.twoSeedXL) i
              (StripSys.rt q) ω - segDriver (travAllInf R L r η ψ ω) (StripSys.rt q))
            (fun j => geomRW (fun t ω => segDriver (travAllInf R L r η ψ ω) t) (fun _ => LP.twoSeedXR) j
              (StripSys.rt q) ω - segDriver (travAllInf R L r η ψ ω) (StripSys.rt q))
            (fun i => geomLW (fun t ω => segDriver (travAll (innerRight k rL R MR) (innerLeft k rR L ML)
                (StripSys.rt s) η ψ' ω) t) (fun _ => LP.twoSeedXL) i (StripSys.rt q') ω -
              segDriver (travAll (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ' ω)
                (StripSys.rt q'))
            (fun j => geomRW (fun t ω => segDriver (travAll (innerRight k rL R MR) (innerLeft k rR L ML)
                (StripSys.rt s) η ψ' ω) t) (fun _ => LP.twoSeedXR) j (StripSys.rt q') ω -
              segDriver (travAll (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ' ω)
                (StripSys.rt q'))
            (relChart (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω))
              (travAllInf R L r η ψ) (StripSys.rt q) ω)
            (relChart (fun ω => shiftChart (pChart A' (fun ω => cfPocket (innerRight k rL R MR ω)
                (innerLeft k rR L ML ω) (StripSys.rt s)) ψ' ω) (n' ω))
              (travAll (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ') (StripSys.rt q') ω)
            (pocketSetInf A R L r η ψ n (StripSys.rt q) ω)
            (pocketSet A' (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ' n' (StripSys.rt q') ω)


/-- **`R6FaceQMixedInfRemaining` from the face near the tip's inner relative time**
(`exists_outer_dom_near_tipInf`, `exists_rat_mem_inner_dom`, `dom_subset_of_avoid`). -/
theorem r6FaceQMixedInfRemaining_of_faceS {k rL rR c c' : ℝ} (hS : R6FaceSMixedInfRemaining.{u} k rL rR c c') :
    R6FaceQMixedInfRemaining.{u} k rL rR c c' := by
  intro hmix Ω _ _ P _ h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg R L η hV MR ML hMR hML r A A' ψ ψ' n n' s q hA
    hA'
  filter_upwards [hS hmix P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg R L η hV MR ML hMR hML r A A' ψ ψ' n n' s q
    hA hA'] with ω hω hωA hωA' hωN
  obtain ⟨ε, hε, hR⟩ := hω hωA hωA' hωN
  obtain ⟨hq0, hqlive, -, hsub, u, hu0, hcap, hrel, -⟩ := hωN
  have hγ : IsDrivenCurve (travAllInf R L r η ψ ω) := (((hA ω hωA).1).props (hA ω hωA).2).1
  have hrtq : ((StripSys.rt q : ℝ≥0) : ℝ) = q := Real.coe_toNNReal _ (by exact_mod_cast hq0.le)
  have hinv : capInv (travAllInf R L r η ψ ω) ((StripSys.rt q : ℝ≥0) : ℝ) = u := by
    rw [hrtq, ← hcap]
    exact hγ.capInv_eq hu0
  have htip : η ω (outerFibreEndInf R L r η ψ (StripSys.rt q) ω) ∈
      cfPocket (innerRight k rL R MR ω) (innerLeft k rR L ML ω) (StripSys.rt s) := by
    unfold outerFibreEndInf
    rw [hinv]
    exact hrel
  have hG' : IsChangeConfigInc (innerRight k rL R MR ω) (innerLeft k rR L ML ω) (StripSys.rt s) :=
    ((hA' ω hωA').1).conf
  have hUo : IsOpen (cfPocket (innerRight k rL R MR ω) (innerLeft k rR L ML ω) (StripSys.rt s)) :=
    isOpen_image_negInv' hG'.isOpen_changePocket hG'.changePocket_subset_H
  obtain ⟨z, hzU, hzdom, hphys⟩ := exists_outer_dom_near_tipInf (n := n) (fun ω hω => (hA ω hω).1)
    (fun ω hω => (hA ω hω).2) hωA hqlive hUo htip (hsub htip)
  obtain ⟨q', hlo, hhi, hlive, hLS, hzI⟩ := exists_rat_mem_inner_dom (n' := n') (fun ω hω => (hA' ω hω).1)
    (fun ω hω => (hA' ω hω).2) hωA' (outerFibreEndInf_nonneg (fun ω hω => (hA ω hω).1) hωA) htip hzU hphys hε
  have hmeet := Set.nonempty_of_mem (Set.mem_inter hzI hzdom)
  obtain ⟨hIc, hIsub, hIav⟩ := contained_chart_facts (n := n') (fun ω hω => (hA' ω hω).1)
    (fun ω hω => (hA' ω hω).2) hωA' hlive
  have hincl := dom_subset_of_avoid hIc (hIsub.trans hsub)
    (outer_frontier_subset_traceInf (n := n) (fun ω hω => (hA ω hω).1) (fun ω hω => (hA ω hω).2) hωA hqlive)
    (hIav _ hLS.le) hmeet
  exact ⟨q', hlive, hLS.le, hmeet, hR q' hlo hhi hlive hLS hincl⟩

/-- **Named, unproved: R.6's face, shape `MixedInfInf`, near the tip's inner relative time** (as
`R6FaceSMixedRemaining`; the common point and the time ordering are proved, `r6FaceQMixedInfInfRemaining_of_faceS`). -/
def R6FaceSMixedInfInfRemaining (k rL rR c c' : ℝ) : Prop :=
  (k / 2 - 4 < rL ∧ rR ≤ k / 2 - 4) ∨ (rL ≤ k / 2 - 4 ∧ k / 2 - 4 < rR) →
  ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistOn upperHalfPlaneOpens) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞)
    (αR βR βL αL : Ω → ℝ≥0 → ℂ) (ζαR ζβR ζβL ζαL : Ω → ℝ≥0∞),
    IsR7OuterConfig k rL rR c c' P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL →
    ∀ (R L : Ω → ℝ≥0 → ℂ) (η : Ω → ℝ → ℂ), IsR7Versions P W' αR αL R L η →
    ∀ MR ML : Ω → ℝ≥0 → ℂ, IsFrontierVersion P βR MR → IsFrontierVersion P βL ML →
    ∀ (r : ℝ≥0) (A A' : Set Ω) (ψ ψ' : Ω → ℂ → ℂ) (n n' : Ω → ℤ) (s q : ℚ),
      (∀ ω ∈ A, IsOuterCfgInf (R ω) (L ω) r (fun t : ℝ => W' t.toNNReal ω) (η ω) ∧
        IsCfJordanInf (R ω) (L ω) r (ψ ω)) →
      (∀ ω ∈ A', IsCfPocketConfigInf (innerRight k rL R MR ω) (innerLeft k rR L ML ω) (StripSys.rt s)
          (fun t : ℝ => W' t.toNNReal ω) (η ω) ∧
        IsCfJordanInf (innerRight k rL R MR ω) (innerLeft k rR L ML ω) (StripSys.rt s) (ψ' ω)) →
      ∀ᵐ ω ∂P, ω ∈ A → ω ∈ A' →
        ω ∈ nestRelEventInf R L r η ψ MR ML (innerRight k rL R MR) (innerLeft k rR L ML) s q →
        ∃ ε : ℝ, 0 < ε ∧ ∀ q' : ℚ,
          innerRelCapInf (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ'
              (outerFibreEndInf R L r η ψ (StripSys.rt q) ω) ω < q' →
          (q' : ℝ) < innerRelCapInf (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ'
              (outerFibreEndInf R L r η ψ (StripSys.rt q) ω) ω + ε →
          ((StripSys.rt q' : ℝ≥0) : ℝ≥0∞) <
            capLife (travAllInf (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ' ω) →
          outerFibreEndInf R L r η ψ (StripSys.rt q) ω <
            R5Ref.leftStopInf (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ' (StripSys.rt q') ω →
          ((relChart (fun ω => shiftChart (pChart A' (fun ω => cfPocket (innerRight k rL R MR ω)
                (innerLeft k rR L ML ω) (StripSys.rt s)) ψ' ω) (n' ω))
              (travAllInf (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ') (StripSys.rt q')
                ω).dom : Set ℂ) ⊆
            (relChart (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω))
              (travAllInf R L r η ψ) (StripSys.rt q) ω).dom →
          R6FaceR (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) (fun _ : Fin 1 => innerRight k rL rL (k / 2 - 4))
            (fun _ : Fin 1 => innerLeft k rR rR (k / 2 - 4))
            (fun i => geomLW (fun t ω => segDriver (travAllInf R L r η ψ ω) t) (fun _ => LP.twoSeedXL) i
              (StripSys.rt q) ω - segDriver (travAllInf R L r η ψ ω) (StripSys.rt q))
            (fun j => geomRW (fun t ω => segDriver (travAllInf R L r η ψ ω) t) (fun _ => LP.twoSeedXR) j
              (StripSys.rt q) ω - segDriver (travAllInf R L r η ψ ω) (StripSys.rt q))
            (fun i => geomLW (fun t ω => segDriver (travAllInf (innerRight k rL R MR) (innerLeft k rR L ML)
                (StripSys.rt s) η ψ' ω) t) (fun _ => LP.twoSeedXL) i (StripSys.rt q') ω -
              segDriver (travAllInf (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ' ω)
                (StripSys.rt q'))
            (fun j => geomRW (fun t ω => segDriver (travAllInf (innerRight k rL R MR) (innerLeft k rR L ML)
                (StripSys.rt s) η ψ' ω) t) (fun _ => LP.twoSeedXR) j (StripSys.rt q') ω -
              segDriver (travAllInf (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ' ω)
                (StripSys.rt q'))
            (relChart (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω))
              (travAllInf R L r η ψ) (StripSys.rt q) ω)
            (relChart (fun ω => shiftChart (pChart A' (fun ω => cfPocket (innerRight k rL R MR ω)
                (innerLeft k rR L ML ω) (StripSys.rt s)) ψ' ω) (n' ω))
              (travAllInf (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ') (StripSys.rt q') ω)
            (pocketSetInf A R L r η ψ n (StripSys.rt q) ω)
            (pocketSetInf A' (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ' n' (StripSys.rt q') ω)

/-- **`R6FaceQMixedInfInfRemaining` from the face near the tip's inner relative time**
(`exists_outer_dom_near_tipInf`, `exists_rat_mem_inner_domInf`, `dom_subset_of_avoid`). -/
theorem r6FaceQMixedInfInfRemaining_of_faceS {k rL rR c c' : ℝ} (hS : R6FaceSMixedInfInfRemaining.{u} k rL rR c c') :
    R6FaceQMixedInfInfRemaining.{u} k rL rR c c' := by
  intro hmix Ω _ _ P _ h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg R L η hV MR ML hMR hML r A A' ψ ψ' n n' s q hA
    hA'
  filter_upwards [hS hmix P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg R L η hV MR ML hMR hML r A A' ψ ψ' n n' s q
    hA hA'] with ω hω hωA hωA' hωN
  obtain ⟨ε, hε, hR⟩ := hω hωA hωA' hωN
  obtain ⟨hq0, hqlive, -, hsub, u, hu0, hcap, hrel, -⟩ := hωN
  have hγ : IsDrivenCurve (travAllInf R L r η ψ ω) := (((hA ω hωA).1).props (hA ω hωA).2).1
  have hrtq : ((StripSys.rt q : ℝ≥0) : ℝ) = q := Real.coe_toNNReal _ (by exact_mod_cast hq0.le)
  have hinv : capInv (travAllInf R L r η ψ ω) ((StripSys.rt q : ℝ≥0) : ℝ) = u := by
    rw [hrtq, ← hcap]
    exact hγ.capInv_eq hu0
  have htip : η ω (outerFibreEndInf R L r η ψ (StripSys.rt q) ω) ∈
      cfPocket (innerRight k rL R MR ω) (innerLeft k rR L ML ω) (StripSys.rt s) := by
    unfold outerFibreEndInf
    rw [hinv]
    exact hrel
  have hG' : IsChangeConfigInc (innerRight k rL R MR ω) (innerLeft k rR L ML ω) (StripSys.rt s) :=
    ((hA' ω hωA').1).conf
  have hUo : IsOpen (cfPocket (innerRight k rL R MR ω) (innerLeft k rR L ML ω) (StripSys.rt s)) :=
    isOpen_image_negInv' hG'.isOpen_changePocket hG'.changePocket_subset_H
  obtain ⟨z, hzU, hzdom, hphys⟩ := exists_outer_dom_near_tipInf (n := n) (fun ω hω => (hA ω hω).1)
    (fun ω hω => (hA ω hω).2) hωA hqlive hUo htip (hsub htip)
  obtain ⟨q', hlo, hhi, hlive, hLS, hzI⟩ := exists_rat_mem_inner_domInf (n' := n') (fun ω hω => (hA' ω hω).1)
    (fun ω hω => (hA' ω hω).2) hωA' (outerFibreEndInf_nonneg (fun ω hω => (hA ω hω).1) hωA) htip hzU hphys hε
  have hmeet := Set.nonempty_of_mem (Set.mem_inter hzI hzdom)
  obtain ⟨hIc, hIsub, hIav⟩ := contained_chart_factsInf (n := n') (fun ω hω => (hA' ω hω).1)
    (fun ω hω => (hA' ω hω).2) hωA' hlive
  have hincl := dom_subset_of_avoid hIc (hIsub.trans hsub)
    (outer_frontier_subset_traceInf (n := n) (fun ω hω => (hA ω hω).1) (fun ω hω => (hA ω hω).2) hωA hqlive)
    (hIav _ hLS.le) hmeet
  exact ⟨q', hlive, hLS.le, hmeet, hR q' hlo hhi hlive hLS hincl⟩

end FaceSInf

/-! ### The drop-in with the three mixed faces reduced to `R6FaceR` near the tip's inner relative time -/

section FinalS

open R7Outer R7Leaves R6Nest
open QuantumZipper (chiC)
open scoped Real

universe u

variable {k rL rR : ℝ}

/-- **The two-outer-arm inputs with the mixed faces of `V` reduced to `R6FaceR` near the tip's inner relative time**
(the three faces of shape `Two*` still with one common point). -/
def TwoOuterFaceSInputs (k rL rR : ℝ) : Prop :=
  PhaseCont.R7PhaseWordRemaining.{u} k (innerRight k rL rL (k / 2 - 4))
      (innerLeft k (k / 2 - 4) (k / 2 - 4) (k / 2 - 4))
      (π * chiC (16 / k) + (R7.thetaL k rR - π / 2) * chiC (16 / k) +
        (r7A k (k / 2 - 4) - r7A k (innerLeft k (k / 2 - 4) (k / 2 - 4) (k / 2 - 4))))
      (0 + (r7B k rL - r7B k (innerRight k rL rL (k / 2 - 4)))) ∧
    R6FaceSMixedRemaining.{u} k rL (k / 2 - 4) (π * chiC (16 / k) + (R7.thetaL k rR - π / 2) * chiC (16 / k)) 0 ∧
    R6FaceSMixedInfRemaining.{u} k rL (k / 2 - 4)
      (π * chiC (16 / k) + (R7.thetaL k rR - π / 2) * chiC (16 / k)) 0 ∧
    R6FaceSMixedInfInfRemaining.{u} k rL (k / 2 - 4)
      (π * chiC (16 / k) + (R7.thetaL k rR - π / 2) * chiC (16 / k)) 0 ∧
    R6Rel.R7OuterPhaseContMRemaining.{u} k rL (k / 2 - 4)
      (π * chiC (16 / k) + (R7.thetaL k rR - π / 2) * chiC (16 / k)) 0 ∧
    R6FaceQTwoRemaining.{u} k rL rR (π * chiC (16 / k)) 0 ∧
    R6FaceQTwoInfRemaining.{u} k rL rR (π * chiC (16 / k)) 0 ∧
    R6FaceQTwoInfInfRemaining.{u} k rL rR (π * chiC (16 / k)) 0

/-- The reduced two-outer-arm inputs give `TwoOuterFaceQFullInputs`. -/
theorem twoOuterFaceQFullInputs_of_faceS (h : TwoOuterFaceSInputs.{u} k rL rR) :
    TwoOuterFaceQFullInputs.{u} k rL rR :=
  ⟨h.1, r6FaceQMixedRemaining_of_faceS h.2.1, r6FaceQMixedInfRemaining_of_faceS h.2.2.1,
    r6FaceQMixedInfInfRemaining_of_faceS h.2.2.2.1, h.2.2.2.2⟩

/-- **The outer phase input from R.5 and R.6's faces, the mixed faces reduced to `R6FaceR` near the tip's inner
relative time** (drop-in for `R6Fin.r7OuterPhaseSideRemaining_of_cont_core`, without `hstrip` and `htwo`). -/
theorem r7OuterPhaseSideRemaining_of_cont_faceS_safe (h411 : Sec5.Cond44Ref.Prop411QStatement.{u})
    (h51 : Sec5.Cond44Ref.Prop51QStatement.{u}) (h47 : Sec5.Prop411Q.Lemma47QHitStatement.{u})
    (h47T : ∀ θ : ℝ, -(π / 2) < θ → θ < π / 2 → Sec5.RestartGen.Lemma47QHitTStatement.{u} θ)
    (haux7 : Sec4.Aux7Statement.{u} k) (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    (hA : Sec5.PartAInputsSixteenDivOfClearance)
    (hword : PhaseCont.R7PhaseWordRemaining.{u} k (innerRight k rL rL (k / 2 - 4)) (innerLeft k rR rR (k / 2 - 4))
      (π * chiC (16 / k) + (r7A k rR - r7A k (innerLeft k rR rR (k / 2 - 4))))
      (0 + (r7B k rL - r7B k (innerRight k rL rL (k / 2 - 4)))))
    (hface : R6FaceSMixedRemaining.{u} k rL rR (π * chiC (16 / k)) 0)
    (hfaceI : R6FaceSMixedInfRemaining.{u} k rL rR (π * chiC (16 / k)) 0)
    (hfaceII : R6FaceSMixedInfInfRemaining.{u} k rL rR (π * chiC (16 / k)) 0)
    (hk4 : 4 < k) (hrL : -2 < rL) (hrR : -2 < rR)
    (hcont : OuterPhNext.R7OuterPhaseContRemaining.{u} k rL rR)
    (htwoIn : k / 2 - 4 < rL → k / 2 - 4 < rR → TwoOuterFaceSInputs.{u} k rL rR) :
    OuterIn.R7OuterPhaseSideRemaining.{u} k rL rR :=
  r7OuterPhaseSideRemaining_of_cont_faceQFull_safe h411 h51 h47 h47T haux7 h44 hA hword
    (r6FaceQMixedRemaining_of_faceS hface) (r6FaceQMixedInfRemaining_of_faceS hfaceI)
    (r6FaceQMixedInfInfRemaining_of_faceS hfaceII) hk4 hrL hrR hcont
    fun hdL hdR => twoOuterFaceQFullInputs_of_faceS (htwoIn hdL hdR)

end FinalS

end InteractingSLE.Sec7.R6Safe
