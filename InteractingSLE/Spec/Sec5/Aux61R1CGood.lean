/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61R1CTrace
import InteractingSLE.Spec.Sec5.Aux61Asm2Build

/-!
# Regular restart records and measurable retractions onto them

Packet PROVE-AUX61-R1CHART. R1's chart theorem needs its regularity hypotheses at **every** record. A record
`y = (counterflow record, own record stopped at q)` is **regular** (`RegRec s q y`) when `q > 0`, the own record
carries the state and trace certificates (`StateCert`, `TraceCert`), the injectivity and interior certificates
(`InjCert`, `ImCert`), and the counterflow hull protects the original target `1` (`1 ∉ closure K_s`). All are Borel
conditions (`measurableSet_regRec`). On a regular record (`RegRec.facts`) R1's own data

* `recU q t y = frozenDrv q y.2 t` (the driver read from the record, frozen at `q`) is continuous from `0`;
* `recη q y = fullTrace q y.2` is a global Loewner trace of it, injective on `[0, q]`, in `ℍ` on `(0, q]`, and equal
  to the trace read from the record on `[0, q]`.

`retr G` is the measurable retraction onto a measurable set `G` (the identity on `G`, a fixed point of `G` off it).
Reading R1's data through it makes every pointwise hypothesis hold at every record, while the data are unchanged on
`G` (the plain record readers there).

Also: membership of a measurable point in an open-valued set with measurable closed-ball tests is measurable
(`measurableSet_mem_of_closedBall`), and the distance to R1's contact obstacle is jointly measurable
(`measurable_infDist_retObs_comp`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull fwdMapInv)

namespace InteractingSLE.Sec5.Aux61R1C

open LawUnique Restart.FlowStopIdentG Aux61Restart Aux61Marks
open Aux61SlitW (rationalTime)

/-! ### Retractions onto a set -/

section Retract

variable {α : Type*} [Nonempty α]

open Classical in
/-- A point of `G` when `G` is nonempty. -/
def pickIn (G : Set α) : α := if h : G.Nonempty then h.some else Classical.arbitrary α

theorem pickIn_mem {G : Set α} (h : G.Nonempty) : pickIn G ∈ G := by
  classical
  simp only [pickIn, h, ↓reduceDIte]
  exact h.some_mem

open Classical in
/-- **The retraction onto `G`**: the identity on `G`, the point `pickIn G` off it. -/
def retr (G : Set α) (y : α) : α := if y ∈ G then y else pickIn G

theorem retr_of_mem {G : Set α} {y : α} (hy : y ∈ G) : retr G y = y := by
  classical
  simp only [retr, hy, ↓reduceIte]

theorem retr_mem {G : Set α} (h : G.Nonempty) (y : α) : retr G y ∈ G := by
  classical
  unfold retr
  split_ifs with hy
  · exact hy
  · exact pickIn_mem h

theorem measurable_retr [MeasurableSpace α] {G : Set α} (hG : MeasurableSet G) : Measurable (retr G) := by
  classical
  exact Measurable.ite hG measurable_id measurable_const

end Retract

/-! ### Two measurability tools -/

/-- **Membership in an open-valued set with measurable closed-ball tests** is measurable at a measurable point. -/
theorem measurableSet_mem_of_closedBall {Ω : Type*} [MeasurableSpace Ω] {D : Ω → Set ℂ}
    (hDo : ∀ ω, IsOpen (D ω)) (hDm : ∀ (c : ℂ) (ρ : ℝ), MeasurableSet {ω | closedBall c ρ ⊆ D ω})
    {x : Ω → ℂ} (hx : Measurable x) : MeasurableSet {ω | x ω ∈ D ω} := by
  set e : ℕ → ℂ := TopologicalSpace.denseSeq ℂ with he
  have hdense : DenseRange e := TopologicalSpace.denseRange_denseSeq ℂ
  have heq : {ω | x ω ∈ D ω} = ⋃ k : ℕ, ⋃ n : ℕ,
      {ω | dist (x ω) (e k) < 1 / ((n : ℝ) + 1)} ∩ {ω | closedBall (e k) (1 / ((n : ℝ) + 1)) ⊆ D ω} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff]
    constructor
    · intro hω
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (hDo ω) (x ω) hω
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show 0 < ε / 2 by positivity)
      obtain ⟨k, hk⟩ := Metric.denseRange_iff.1 hdense (x ω) (1 / ((n : ℝ) + 1)) (by positivity)
      refine ⟨k, n, hk, fun z hz => hball ?_⟩
      rw [mem_closedBall] at hz
      rw [mem_ball]
      calc dist z (x ω) ≤ dist z (e k) + dist (e k) (x ω) := dist_triangle _ _ _
        _ < 1 / ((n : ℝ) + 1) + 1 / ((n : ℝ) + 1) := by
          rw [dist_comm (e k)]; exact add_lt_add_of_le_of_lt hz hk
        _ < ε := by linarith
    · rintro ⟨k, n, hk, hsub⟩
      exact hsub (mem_closedBall.2 hk.le)
  rw [heq]
  refine MeasurableSet.iUnion fun k => MeasurableSet.iUnion fun n => MeasurableSet.inter ?_ (hDm _ _)
  exact measurableSet_lt (hx.dist measurable_const) measurable_const

/-- A Carathéodory function (continuous in the point of `ℂ`, measurable in the sample) at a measurable point is
measurable. -/
theorem measurable_comp_of_continuous_of_measurable {α : Type*} [MeasurableSpace α] {u : ℂ → α → ℝ}
    (h1 : ∀ y, Continuous fun z => u z y) (h2 : ∀ z, Measurable (u z)) {x : α → ℂ} (hx : Measurable x) :
    Measurable fun a => u (x a) a :=
  (measurable_uncurry_of_continuous_of_measurable h1 h2).comp (hx.prodMk measurable_id)

variable {nL nR : ℕ}

/-- **The distance from a measurable point to R1's contact obstacle is measurable** (Carathéodory: continuous in the
point, measurable in the record). -/
theorem measurable_infDist_retObs_comp (s : ℝ≥0) {x : HistorySpace 0 0 × HistorySpace nL nR → ℂ}
    (hx : Measurable x) : Measurable fun y => infDist (x y) (retObs s y) :=
  measurable_comp_of_continuous_of_measurable (u := fun z y => infDist z (retObs s y))
    (fun _ => continuous_infDist_pt _) (fun z => measurable_infDist_retObs s z) hx

/-! ### Regular records -/

/-- The record space of the restart: counterflow record and own record. -/
abbrev Rec (nL nR : ℕ) : Type := HistorySpace 0 0 × HistorySpace nL nR

/-- R1's own driver read from a record (frozen at the restart time). -/
def recU (q : ℚ) (t : ℝ≥0) (y : Rec nL nR) : ℝ := frozenDrv (rationalTime q) y.2 t

/-- R1's own global trace read from a record. -/
def recη (q : ℚ) (y : Rec nL nR) : ℝ → ℂ := fullTrace (rationalTime q) y.2

/-- The counterflow hull of a record. -/
abbrev recHull (s : ℝ≥0) (y : Rec nL nR) : Set ℂ := historyHull s (fun y : Rec nL nR => y.1) y

/-- **Regular records**: positive restart time, the certificates of the own record, and the counterflow hull
protecting the original target. -/
def RegRec (s : ℝ≥0) (q : ℚ) (y : Rec nL nR) : Prop :=
  0 < q ∧ StateCert (rationalTime q) y.2 ∧ TraceCert (rationalTime q) y.2 ∧ InjCert q y.2 ∧ ImCert q y.2 ∧
    (1 : ℂ) ∉ closure (recHull s y)

theorem coe_rationalTime {q : ℚ} (hq : 0 ≤ q) : ((rationalTime q : ℝ≥0) : ℝ) = q :=
  Real.coe_toNNReal _ (by exact_mod_cast hq)

/-- The protection of the original target is a Borel condition on the counterflow record. -/
theorem measurableSet_protected (s : ℝ≥0) :
    MeasurableSet {y : Rec nL nR | (1 : ℂ) ∉ closure (recHull s y)} := by
  have hK := measurable_historyHull (s := s) (Y := fun y : Rec nL nR => y.1)
    ((GlueCond.measurable_cfStop s).comp measurable_fst)
  have heq : {y : Rec nL nR | (1 : ℂ) ∉ closure (recHull s y)} =
      ⋃ n : ℕ, recHull s ⁻¹' {A : Set ℂ | Disjoint A (ball (1 : ℂ) (1 / ((n : ℝ) + 1)) ∩ H)} := by
    ext y
    simp only [mem_ofPred_eq, mem_iUnion, mem_preimage]
    constructor
    · intro hy
      rw [Metric.mem_closure_iff] at hy
      push Not at hy
      obtain ⟨ε, hε, hfar⟩ := hy
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
      refine ⟨n, Set.disjoint_left.2 fun z hz hzB => ?_⟩
      have h1 := hfar z hz
      have h2 : dist z 1 < 1 / ((n : ℝ) + 1) := hzB.1
      rw [dist_comm] at h2
      linarith
    · rintro ⟨n, hn⟩ hmem
      rw [Metric.mem_closure_iff] at hmem
      obtain ⟨z, hz, hdist⟩ := hmem (1 / ((n : ℝ) + 1)) (by positivity)
      have hzH : z ∈ H := historyHull_subset_H s _ y hz
      rw [dist_comm] at hdist
      exact Set.disjoint_left.1 hn hz ⟨hdist, hzH⟩
  rw [heq]
  exact MeasurableSet.iUnion fun n => hK (LocalSets.measurableSet_avoid (isOpen_ball.inter QuantumZipper.isOpen_H)
    inter_subset_right)

/-- **Regular records form a Borel set.** -/
theorem measurableSet_regRec (s : ℝ≥0) (q : ℚ) : MeasurableSet {y : Rec nL nR | RegRec s q y} := by
  refine MeasurableSet.inter (MeasurableSet.const _) ?_
  refine MeasurableSet.inter (measurable_snd (measurableSet_stateCert _)) ?_
  refine MeasurableSet.inter (measurable_snd (measurableSet_traceCert _)) ?_
  refine MeasurableSet.inter (measurable_snd (measurableSet_injCert _)) ?_
  exact MeasurableSet.inter (measurable_snd (measurableSet_imCert _)) (measurableSet_protected s)

theorem measurable_recU (q : ℚ) (t : ℝ≥0) : Measurable (recU (nL := nL) (nR := nR) q t) :=
  (measurable_frozenDrv _ t).comp measurable_snd

theorem recη_of_le {q : ℚ} (hq : 0 ≤ q) (y : Rec nL nR) {t : ℝ} (ht : t ≤ q) :
    recη q y t = recTrace y.2 t :=
  fullTrace_of_le (by rw [coe_rationalTime hq]; exact ht)

theorem measurable_recη {q : ℚ} (hq : 0 ≤ q) {t : ℝ} (ht : t ≤ q) :
    Measurable fun y : Rec nL nR => recη q y t := by
  simp_rw [recη_of_le hq _ ht]
  exact (measurable_recTrace t).comp measurable_snd

/-- **R1's pointwise facts on a regular record.** -/
theorem RegRec.facts {s : ℝ≥0} {q : ℚ} {y : Rec nL nR} (hy : RegRec s q y) :
    0 < (q : ℝ) ∧ Continuous (fun t => recU q t y) ∧ recU q 0 y = 0 ∧
    IsLoewnerTrace (Ito.rpath fun t => recU q t y) (recη q y) ∧
    InjOn (recη q y) (Icc 0 (q : ℝ)) ∧ MapsTo (recη q y) (Ioc 0 (q : ℝ)) H ∧
    ContinuousOn (recη q y) (Icc 0 (q : ℝ)) ∧ recη q y 0 = 0 ∧ (1 : ℂ) ∉ closure (recHull s y) := by
  obtain ⟨hq, hS, hT, hI, hIm, hP⟩ := hy
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hcoe := coe_rationalTime hq.le
  have hr : 0 < rationalTime q := by
    rw [← NNReal.coe_pos, hcoe]; exact hq'
  obtain ⟨hLT, hco⟩ := hS.isLoewnerTraceLT_recTrace hT hr
  rw [hcoe] at hco
  have heq : EqOn (recTrace y.2) (recη q y) (Icc 0 (q : ℝ)) := fun t ht => (recη_of_le hq.le y ht.2).symm
  refine ⟨hq', hS.continuous_frozenDrv, hS.frozenDrv_zero, hS.isLoewnerTrace_fullTrace hT hr,
    (injOn_of_rat hco hI).congr heq, (mapsTo_H_of_rat hco hIm).congr (heq.mono Ioc_subset_Icc_self),
    hco.congr heq.symm, ?_, hP⟩
  rw [← heq ⟨le_rfl, hq'.le⟩]
  exact hLT.1

end InteractingSLE.Sec5.Aux61R1C
