/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.StagedRepJSat
import InteractingSLE.Spec.Sec5.StagedNTrNodeCausal

/-!
# Prop 5.9's later root stages: the saturation of the glued past, and `hRootLater`

Packet PROVE-STAGED-REPJ. `GlueSat` (`StagedRepJSat`) from the causality of PIECES' tree construction, which
PROVE-STAGED-NODETRANSFER proved for every tree (`StagedNTr.TreeData.causal`: at two samples with the same counterflow
chart, root marks and dilation, and the same path of an alive list up to its last switch, the candidate pieces agree
    up to
their switching times, `CanonUpTo`; `StagedNTr.canonQ_le_sepSigma`: then no canonical past event separates the samples):

* `treeSameAt_gamData`: two good points of `Gam` with the same stopped counterflow history see the same root tree data;
* **`gam_causal`**: no event of `Gam`'s canonical past of a reached later list separates two such points whose paths
    of the
  list agree up to the last switch;
* **`glueSat`**: on good window samples with the same stopped data `stopD q` (`q` after the last switch) the staged
  paths agree on `[0, q]` (`alphaD_stopD`, `seedLine_candW`, `qPath_eq_fst`) and the stopped counterflow histories
      agree,
  hence `GlueSat`;
* **`glueSatStatement`**, and **`rootLaterOn_s4Objects`**: `RootLaterOn h44 (s4Objects h44)` from the clearance form of
  Part A alone.

This module imports PROVE-STAGED-NODETRANSFER's modules `StagedNTrUpTo`, `StagedNTrCausal`, `StagedNTrNodeCausal`.
R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal Real
open LQGMetric (DistOn)

namespace InteractingSLE.Sec5.CrossCond.StagedRepJ

open WangWu hiding ratPt exists_ratPt_dist_lt
open WangWu.ImgWord LawUnique GlueCond Cond44Ref Word49 StagedS3 StagedS4 StagedS5 StagedS6
open Restart Exist.StagedLaw Exist.Staged Wire.Night
open Sec7.AdmCode Prop513TreeExtract Prop513Schedule Prop513Target Prop59Pieces Prop59Stage Prop59System
open StagedRepLater StagedKCand StagedKill StagedRep StagedCand
open Sec4 (IsStripGFF IsStripCounterflowDriver)

/-! ### Causality on `Gam` -/

section Root

variable (h44 : Theorem12ParamCond44Statement.{0}) {κ x₀ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
  (hb : IsFig51Bounds κ a b a' b') (r : ℝ≥0)

/-- **Two good points of `Gam` with the same stopped counterflow history** see the same root tree data. -/
theorem treeSameAt_gamData {γ γ' : Gam} (hy : cfStop r γ.2 = cfStop r γ'.2)
    (hG : γ ∈ gamGood h44 hκ hκ4 (x₀ := x₀) hb) (hG' : γ' ∈ gamGood h44 hκ hκ4 (x₀ := x₀) hb) :
    StagedNTr.TreeSameAt (gamData h44 hκ hκ4 (x₀ := x₀) hb r) γ γ' := by
  have e1 : rootLam r γ.2 = rootLam r γ'.2 := by rw [← rootLam_cfStop r γ.2, hy, rootLam_cfStop]
  have e2 : rootXL hκ hb x₀ r γ.2 = rootXL hκ hb x₀ r γ'.2 := by
    rw [← rootXL_cfStop x₀ hκ hb r γ.2, hy, rootXL_cfStop]
  have e3 : rootXR hκ hb x₀ r γ.2 = rootXR hκ hb x₀ r γ'.2 := by
    rw [← rootXR_cfStop x₀ hκ hb r γ.2, hy, rootXR_cfStop]
  refine ⟨e1, ?_, ?_, ?_, ?_, hG, hG'⟩
  · show cfDrv0 r γ.2 = cfDrv0 r γ'.2
    rw [← cfDrv0_cfStop r γ.2, hy, cfDrv0_cfStop]
  · show cfHullQ r γ.2 = cfHullQ r γ'.2
    rw [← cfHullQ_cfStop r γ.2, hy, cfHullQ_cfStop]
  · show (fun i => rootLam r γ.2 * rootXL hκ hb x₀ r γ.2 i) = fun i => rootLam r γ'.2 * rootXL hκ hb x₀ r γ'.2 i
    rw [e1, e2]
  · show (fun k => rootLam r γ.2 * rootXR hκ hb x₀ r γ.2 k) = fun k => rootLam r γ'.2 * rootXR hκ hb x₀ r γ'.2 k
    rw [e1, e3]

/-- **Causality of the root tree on `Gam`.** At two points with the same root tree data and the same stopped
counterflow history, if a later list is reached at the first point and the paths of the list agree up to its last
switch, then no event of the canonical past of the list separates the two points. -/
theorem gam_causal {j : ℕ} {t : Fin (j + 1) → ℝ≥0} {γ γ' : Gam} (hs : StagedNTr.TreeSameAt (gamData h44 hκ hκ4 (x₀ :=
    x₀) hb r) γ γ')
    (hy : cfStop r γ.2 = cfStop r γ'.2)
    (hα : EqOn ((gamData h44 hκ hκ4 (x₀ := x₀) hb r).α (j + 1) t γ) ((gamData h44 hκ hκ4 (x₀ := x₀) hb r).α (j + 1) t
        γ') (Icc 0 (qLast (j + 1) t)))
    (hR : γ ∈ gamR h44 hκ hκ4 (x₀ := x₀) hb r (j + 1) t) :
    ∀ M, MeasurableSet[gamQ h44 hκ hκ4 (x₀ := x₀) hb r (j + 1) t] M → (γ ∈ M ↔ γ' ∈ M) := by
  have hD := isReg_gamData h44 hκ hκ4 (x₀ := x₀) hb r
  have hT := isTree_gamData x₀ h44 hκ hκ4 hb r
  have hpos : ∀ k (t' : Fin (k + 1) → ℝ≥0), (gamData h44 hκ hκ4 (x₀ := x₀) hb r).valid (k + 1) t' → 0 < qLast (k + 1)
      t' := fun k t' hv' => by
    rw [← lastO_eq hv']; exact_mod_cast oTime_pos hv' (Fin.last k)
  have hal := (TreeData.reach (rootNL_pos _) (rootNR_pos _) hD hT (fun _ _ => Iff.rfl) (j + 1) t γ hR).2
    (Nat.succ_pos j)
  obtain ⟨-, -, -, hcanon⟩ := StagedNTr.TreeData.causal hD hT hpos hs (j + 1) t hal hα
  have hbase : gamPast r ≤ StagedNTr.sepSigma γ γ' := by
    rintro _ ⟨B, -, rfl⟩
    show γ ∈ (fun γ : Gam => cfStop r γ.2) ⁻¹' B ↔ γ' ∈ (fun γ : Gam => cfStop r γ.2) ⁻¹' B
    simp only [mem_preimage, hy]
  have hy0 : gamY0 h44 hκ hκ4 (x₀ := x₀) hb r γ = gamY0 h44 hκ hκ4 (x₀ := x₀) hb r γ' := by
    show ((0 : ℝ), (gamData h44 hκ hκ4 (x₀ := x₀) hb r).xL0 γ, (gamData h44 hκ hκ4 (x₀ := x₀) hb r).xR0 γ) = ((0 :
        ℝ), (gamData h44 hκ hκ4 (x₀ := x₀) hb r).xL0 γ', (gamData h44 hκ hκ4 (x₀ := x₀) hb r).xR0 γ')
    rw [hs.xL0, hs.xR0]
  intro M hM
  exact StagedNTr.measurableSet_sepSigma_iff.1
    (StagedNTr.canonQ_le_sepSigma (isRegFam_gamCand h44 hκ hκ4 hb r) (measurable_gamY0 h44 hκ hκ4 hb r)
      StagedNTr.monotone_ratGrid hy0 (fun _ => mem_univ _) hbase (j + 1) t hR hcanon M hM)

end Root

/-! ### The saturation on the glued space -/

section Sat

variable (x₀ : ℝ) (h44 : Theorem12ParamCond44Statement.{0}) {κ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
  (hb : IsFig51Bounds κ a b a' b') {Ω : Type} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ)
  (ζ : Ω → ℝ≥0∞)

omit [StandardBorelSpace Ω] in
/-- **`GlueSat` holds**: good window samples with the same stopped data have the same stopped counterflow history and
the same staged path on `[0, q]`, so (`gam_causal`) no event of `Gam`'s canonical past separates their images. -/
theorem glueSat (hhm : Measurable h) {j : ℕ} {t : Fin (j + 1) → ℝ≥0} (hv : IsValid (j + 1) t) (s : ℝ≥0) :
    GlueSat x₀ h44 hκ hκ4 hb P h W ζ hhm (j + 1) t s := by
  intro q hq p hp p' hp' he hR M hM
  have hy : cfStop s (gZ x₀ (κ := κ) h p).2 = cfStop s (gZ x₀ (κ := κ) h p').2 := congrArg Prod.snd he
  have hs := treeSameAt_gamData h44 hκ hκ4 hb s hy hp.2.2.2 hp'.2.2.2
  have hα : EqOn ((gamData h44 hκ hκ4 (x₀ := x₀) hb s).α (j + 1) t (gZ x₀ (κ := κ) h p)) ((gamData h44 hκ hκ4 (x₀ :=
      x₀) hb s).α (j + 1) t (gZ x₀ (κ := κ) h p')) (Icc 0 (qLast (j + 1) t)) := by
    intro u hu
    have hu' : u ≤ ((q : ℚ) : ℝ) := hu.2.trans (by rw [← lastO_eq hv]; exact_mod_cast hq.le)
    have e1 := alphaD_stopD (s := s) hp.2.1 hu'
    have e2 := alphaD_stopD (s := s) hp'.2.1 hu'
    rw [he] at e1
    show qPath h44 hκ hκ4 (sourceWord (x₀ := x₀) hκ hb) Prod.fst (j + 1) t (gZ x₀ (κ := κ) h p) u =
      qPath h44 hκ hκ4 (sourceWord (x₀ := x₀) hκ hb) Prod.fst (j + 1) t (gZ x₀ (κ := κ) h p') u
    rw [← qPath_eq_fst hκ hκ4 h44 _ (qField x₀ κ h) (j + 1) t p.1 p.2,
      ← qPath_eq_fst hκ hκ4 h44 _ (qField x₀ κ h) (j + 1) t p'.1 p'.2,
      ← seedLine_candW x₀ h44 hκ hκ4 hb h (j + 1) t p.1, ← seedLine_candW x₀ h44 hκ hκ4 hb h (j + 1) t p'.1]
    exact e1.symm.trans e2
  exact gam_causal h44 hκ hκ4 hb s hs hy hα hR M hM

end Sat

/-- **`GlueSatStatement` holds.** -/
theorem glueSatStatement (h44 : Theorem12ParamCond44Statement.{0}) : GlueSatStatement h44 := by
  intro κ x₀ a b a' b' hκ hκ4 hb Ω _ _ P _ h W ζ hG _ q _ j t hv
  exact glueSat x₀ h44 hκ hκ4 hb P h W ζ hG.1 hv _

/-- **`GluePastStatement` holds** (with the clearance form of Part A). -/
theorem gluePastStatement (h44 : Theorem12ParamCond44Statement.{0}) (hA : PartAInputsSixteenDivOfClearance) :
    GluePastStatement h44 :=
  gluePastStatement_of_sat h44 hA (glueSatStatement h44)

/-- **Theorem 1.2's leaf `hRootLater`** (Prop 5.9's later root stages) for the concrete stage objects, from the
clearance form of Part A. -/
theorem rootLaterOn_s4Objects (h44 : Theorem12ParamCond44Statement.{0}) (hA : PartAInputsSixteenDivOfClearance) :
    RootLaterOn h44 (s4Objects h44) :=
  rootLaterOn_s4Objects_of_sat h44 hA (glueSatStatement h44)

end InteractingSLE.Sec5.CrossCond.StagedRepJ
