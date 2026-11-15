/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.StagedNodeReach
import InteractingSLE.Spec.Sec5.StagedNodeScale

/-!
# Proposition 5.9's node laws: the path clause, and `NodeLawOn` from the comparison clause

Packet PROVE-STAGED-NODE. The leaf `hNodeLaw : Wire.Night.NodeLawOn h44 objects` of the expanded Theorem 1.2 asks, for
every node experiment, the killed stage law `IsStageLawFarK` (R78) of every node candidate. It splits into the path
clause (`Wire.Night.StagePath`) and the comparison clause (`CompClauseK`, which does not read the noise):

* `NodePathOn`, `NodeCompOn`: the two clauses for all node candidates; **`nodeLawOn_of_path_comp`**;
* `start_ordered_of_mem_canonR`: on the reached event the canonical node start is an ordered strict word;
* `not_threshold_start`: the start is not a threshold configuration (one new mark on the driver on each side, born
  weights `±(2 − κ/2)` or `0`, all `> −2`);
* **`nodePathOn_nodeObjects`**: the path clause for the stage objects with the recovered node noise (named inputs:
  PROVE-STAGED-S6's arc killed word `ArcKilledWordStatement`, and the clearance form of Part A as for the root path);
* **`nodeLawOn_nodeObjects`**: `NodeLawOn h44 (nodeObjects h44)` from the comparison clause `NodeCompOn`.

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Function
open LQGMetric (DistOn)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec5.CrossCond.StagedNode

open Sec4 (IsStripGFF IsStripCounterflowDriver)
open Prop513TreeExtract Prop513Schedule Prop513Target Exist.StagedLaw Exist.Staged Sec7.AdmCode Restart
open Prop59System Prop59Stage Prop59Pieces Prop59Nodes Prop59Sched StagedKCand StagedKill StagedRep StagedRepLater
open Wire.Night LawUnique WangWu GlueCond Word49 Prop59NodeTree StagedS4 StagedCand StagedAdapt
open Sec7.Lemma71C (capClock)

/-! ### The two clauses of the node laws -/

/-- **The path clause of every node law** (clause 1 of `Wire.Night.NodeLaw`). -/
def NodePathOn (h44 : Theorem12ParamCond44Statement.{0}) (objects : StageObjectsOn) : Prop :=
  ∀ {κ x₀ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsFig51Bounds κ a b a' b')
    {Ω : Type} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (γ : Ω → ℝ≥0 → ℂ),
    ∀ hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀},
    ∀ hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ,
    ∀ htr : (∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (γ ω)),
    let d := objects hκ hκ4 hb P h W ζ γ hG hcf htr;
    ∀ (n : ℕ) (q : ℚ), 0 < q → ∀ (j : ℕ) (t : Fin j → ℝ≥0),
      StagePath κ (P.prod d.measure)
        (canonQ (nodeBase x₀ h44 hκ hκ4 hb P h W ζ d.nodeNoise d.nodeBase n q)
          (nodeCand (Ωa := d.Ωa) x₀ h44 hκ hκ4 hb P h W ζ d.nodeNoise n q) ratGrid
          (nodeNL_pos x₀ hκ hb n) (nodeNR_pos x₀ hκ hb n) (nodeStart x₀ h44 hκ hκ4 hb P h W ζ d.nodeNoise n q) j t)
        (canonR (nodeCand (Ωa := d.Ωa) x₀ h44 hκ hκ4 hb P h W ζ d.nodeNoise n q) ratGrid (nodeNL_pos x₀ hκ hb n)
          (nodeNR_pos x₀ hκ hb n) (nodeStart x₀ h44 hκ hκ4 hb P h W ζ d.nodeNoise n q)
          (nodeR0 x₀ h44 hκ hκ4 hb P h W ζ d.nodeNoise n q) j t)
        (stageρL κ (nodeρL κ (sourceWord (x₀ := x₀) hκ hb) (scheduleAt n)) j)
        (stageρR κ (nodeρR κ (sourceWord (x₀ := x₀) hκ hb) (scheduleAt n)) j)
        (farL (Nat.lt_of_lt_of_le (nodeNL_pos x₀ hκ hb n) (Nat.le_add_right _ j)))
        (farR (Nat.lt_of_lt_of_le (nodeNR_pos x₀ hκ hb n) (Nat.le_add_right _ j)))
        (canonY (nodeCand (Ωa := d.Ωa) x₀ h44 hκ hκ4 hb P h W ζ d.nodeNoise n q)
          (nodeStart x₀ h44 hκ hκ4 hb P h W ζ d.nodeNoise n q) j t)
        (nodeCand (Ωa := d.Ωa) x₀ h44 hκ hκ4 hb P h W ζ d.nodeNoise n q j t).W
        (nodeCand (Ωa := d.Ωa) x₀ h44 hκ hκ4 hb P h W ζ d.nodeNoise n q j t).VL
        (nodeCand (Ωa := d.Ωa) x₀ h44 hκ hκ4 hb P h W ζ d.nodeNoise n q j t).VR
        (nodeCand (Ωa := d.Ωa) x₀ h44 hκ hκ4 hb P h W ζ d.nodeNoise n q j t).B
        (nodeCand (Ωa := d.Ωa) x₀ h44 hκ hκ4 hb P h W ζ d.nodeNoise n q j t).ζ

/-- **The comparison clause of every node law** (clause 2 of `Wire.Night.NodeLaw`; it does not read the noise). -/
def NodeCompOn (h44 : Theorem12ParamCond44Statement.{0}) (objects : StageObjectsOn) : Prop :=
  ∀ {κ x₀ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsFig51Bounds κ a b a' b')
    {Ω : Type} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (γ : Ω → ℝ≥0 → ℂ),
    ∀ hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀},
    ∀ hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ,
    ∀ htr : (∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (γ ω)),
    let d := objects hκ hκ4 hb P h W ζ γ hG hcf htr;
    ∀ (n : ℕ) (q : ℚ), 0 < q → ∀ (j : ℕ) (t : Fin j → ℝ≥0),
      CompClauseK κ (P.prod d.measure)
        (canonQ (nodeBase x₀ h44 hκ hκ4 hb P h W ζ d.nodeNoise d.nodeBase n q)
          (nodeCand (Ωa := d.Ωa) x₀ h44 hκ hκ4 hb P h W ζ d.nodeNoise n q) ratGrid
          (nodeNL_pos x₀ hκ hb n) (nodeNR_pos x₀ hκ hb n) (nodeStart x₀ h44 hκ hκ4 hb P h W ζ d.nodeNoise n q) j t)
        (canonR (nodeCand (Ωa := d.Ωa) x₀ h44 hκ hκ4 hb P h W ζ d.nodeNoise n q) ratGrid (nodeNL_pos x₀ hκ hb n)
          (nodeNR_pos x₀ hκ hb n) (nodeStart x₀ h44 hκ hκ4 hb P h W ζ d.nodeNoise n q)
          (nodeR0 x₀ h44 hκ hκ4 hb P h W ζ d.nodeNoise n q) j t)
        (stageρL κ (nodeρL κ (sourceWord (x₀ := x₀) hκ hb) (scheduleAt n)) j)
        (stageρR κ (nodeρR κ (sourceWord (x₀ := x₀) hκ hb) (scheduleAt n)) j)
        (farL (Nat.lt_of_lt_of_le (nodeNL_pos x₀ hκ hb n) (Nat.le_add_right _ j)))
        (farR (Nat.lt_of_lt_of_le (nodeNR_pos x₀ hκ hb n) (Nat.le_add_right _ j)))
        (canonY (nodeCand (Ωa := d.Ωa) x₀ h44 hκ hκ4 hb P h W ζ d.nodeNoise n q)
          (nodeStart x₀ h44 hκ hκ4 hb P h W ζ d.nodeNoise n q) j t)
        (nodeCand (Ωa := d.Ωa) x₀ h44 hκ hκ4 hb P h W ζ d.nodeNoise n q j t).W
        (nodeCand (Ωa := d.Ωa) x₀ h44 hκ hκ4 hb P h W ζ d.nodeNoise n q j t).VL
        (nodeCand (Ωa := d.Ωa) x₀ h44 hκ hκ4 hb P h W ζ d.nodeNoise n q j t).VR
        (nodeCand (Ωa := d.Ωa) x₀ h44 hκ hκ4 hb P h W ζ d.nodeNoise n q j t).ζ

/-- **The node-law leaf from its two clauses.** -/
theorem nodeLawOn_of_path_comp {h44 : Theorem12ParamCond44Statement.{0}} {objects : StageObjectsOn}
    (hP : NodePathOn h44 objects) (hC : NodeCompOn h44 objects) : NodeLawOn h44 objects := by
  intro κ x₀ a b a' b' hκ hκ4 hb Ω _ _ P _ h W ζ γ hG hcf htr d n q hq j t
  exact isStageLawFarK_of_compClauseK (hP hκ hκ4 hb P h W ζ γ hG hcf htr n q hq j t)
    (hC hκ hκ4 hb P h W ζ γ hG hcf htr n q hq j t)

/-! ### The start is not a threshold configuration -/

section Threshold

/-- A start whose marks vanish only at one index on each side, whose weights there exceed `−2`, is not a threshold
configuration. -/
theorem not_threshold_of_unique {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    (iL : Fin nL) (hL : ∀ i, i ≠ iL → xL i ≠ 0) (hρL : -2 < ρL iL) (iR : Fin nR) (hR : ∀ k, k ≠ iR → xR k ≠ 0)
    (hρR : -2 < ρR iR) : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR := by
  have key : ∀ {n : ℕ} (ρ x : Fin n → ℝ) (i₀ : Fin n), (∀ i, i ≠ i₀ → x i ≠ 0) → -2 < ρ i₀ →
      -2 < ∑ i ∈ Finset.univ.filter (fun i => x i = 0), ρ i := by
    intro n ρ x i₀ hx hρ
    have hsub : Finset.univ.filter (fun i => x i = 0) ⊆ {i₀} := fun i hi => by
      rw [Finset.mem_singleton]
      by_contra hne
      exact hx i hne (Finset.mem_filter.1 hi).2
    rcases Finset.subset_singleton_iff.1 hsub with he | he
    · rw [he, Finset.sum_empty]; norm_num
    · rw [he, Finset.sum_singleton]; exact hρ
  unfold ForceWord.ThresholdCondition
  push Not
  exact ⟨key ρL xL iL hL hρL, key ρR xR iR hR hρR⟩

variable {κ : ℝ}

theorem neg_two_lt_newL (hκ : 0 < κ) (hκ4 : κ < 4) (i : ℕ) : -2 < newL κ i := by
  have h1 := angleWeightBound_pos hκ hκ4
  have h2 := angleWeightBound_lt_two hκ
  unfold newL
  rcases neg_one_pow_eq_or ℝ i with h | h <;> rw [h] <;> linarith

theorem neg_two_lt_newR (hκ : 0 < κ) (hκ4 : κ < 4) (i : ℕ) : -2 < newR κ i := by
  have h1 := angleWeightBound_pos hκ hκ4
  have h2 := angleWeightBound_lt_two hκ
  unfold newR
  rcases neg_one_pow_eq_or ℝ i with h | h <;> rw [h] <;> linarith

theorem neg_two_lt_bornL (hκ : 0 < κ) (hκ4 : κ < 4) (fl : ℕ → Bool) (k : ℕ) : -2 < bornL κ fl k := by
  have h1 := angleWeightBound_pos hκ hκ4
  have h2 := angleWeightBound_lt_two hκ
  have e : angleWeightBound κ = π * (QuantumZipper.chiC κ / sleLambda κ) := by
    rw [angleWeightBound, mul_div_assoc]
  unfold bornL flagAngle
  cases fl (k + 1) <;> cases fl k <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> nlinarith

theorem neg_two_lt_bornR (hκ : 0 < κ) (hκ4 : κ < 4) (fl : ℕ → Bool) (k : ℕ) : -2 < bornR κ fl k := by
  have h1 := angleWeightBound_pos hκ hκ4
  have h2 := angleWeightBound_lt_two hκ
  have e : angleWeightBound κ = π * (QuantumZipper.chiC κ / sleLambda κ) := by
    rw [angleWeightBound, mul_div_assoc]
  unfold bornR flagAngle
  cases fl (k + 1) <;> cases fl k <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> nlinarith

/-- The newest weight of a word `consAlt c ρ₀ m` (`m ≥ 1`). -/
theorem consAlt_zero_idx {n₀ : ℕ} (c : ℕ → ℝ) (ρ₀ : Fin n₀ → ℝ) {m : ℕ} (hm : 0 < m) :
    consAlt c ρ₀ m ⟨0, by omega⟩ = c (m - 1) := by
  rw [consAlt_apply]
  simp only [consAltN, hm, ↓reduceIte, Nat.sub_zero]

end Threshold

/-! ### The path clause of the node candidates -/

section Path

theorem isSLEPathUpTo_cast {κ : ℝ} {a b c d : ℕ} (hL : a = b) (hR : c = d) {xL : Fin a → ℝ} {xR : Fin c → ℝ}
    {ρL : Fin a → ℝ} {ρR : Fin c → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin a → ℝ≥0 → ℝ} {vR : Fin c → ℝ≥0 → ℝ}
    {B : ℝ≥0 → ℝ} {τ : ℝ≥0∞} (hp : Sec2.IsSLEPathUpTo κ xL xR ρL ρR w vL vR B τ) :
    Sec2.IsSLEPathUpTo κ (fun i => xL (Fin.cast hL.symm i)) (fun k => xR (Fin.cast hR.symm k))
      (fun i => ρL (Fin.cast hL.symm i)) (fun k => ρR (Fin.cast hR.symm k)) w (fun i => vL (Fin.cast hL.symm i))
      (fun k => vR (Fin.cast hR.symm k)) B τ := by
  subst hL hR
  exact hp

variable (x₀ : ℝ) (h44 : Theorem12ParamCond44Statement.{0}) {κ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
  (hb : IsFig51Bounds κ a b a' b')
  {Ω Ωa : Type} [mΩ : MeasurableSpace Ω] [MeasurableSpace Ωa]
  (P : Measure Ω) (h : Ω → DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞)

include hκ4 in
theorem nodeWL_zero (n j : ℕ) (hi : 0 < rootNL (sourceWord (x₀ := x₀) hκ hb) + (nodeLen (scheduleAt n) + j)) :
    -2 < nodeWL (κ := κ) x₀ hκ hb n (nodeLen (scheduleAt n) + j) ⟨0, hi⟩ := by
  have e := subW_add (nodeLen (scheduleAt n))
    (fun j => stageρL κ (nodeρL κ (sourceWord (x₀ := x₀) hκ hb) (scheduleAt n)) j) j ⟨0, by omega⟩
  have e0 : (Fin.cast (by omega) (⟨0, by omega⟩ : Fin (rootNL (sourceWord (x₀ := x₀) hκ hb) +
      nodeLen (scheduleAt n) + j)) : Fin (rootNL (sourceWord (x₀ := x₀) hκ hb) + (nodeLen (scheduleAt n) + j))) =
      ⟨0, hi⟩ := Fin.ext rfl
  rw [e0] at e
  rw [nodeWL, e]
  rcases Nat.eq_zero_or_pos j with hj | hj
  · subst hj
    show -2 < nodeρL κ (sourceWord (x₀ := x₀) hκ hb) (scheduleAt n) ⟨0, _⟩
    rw [nodeρL, consAlt_zero_idx _ _ nodeLen_pos]
    exact neg_two_lt_bornL hκ hκ4 _ _
  · rw [stageρL, consAlt_zero_idx _ _ hj]
    exact neg_two_lt_newL hκ hκ4 _

include hκ4 in
theorem nodeWR_zero (n j : ℕ) (hi : 0 < rootNR (sourceWord (x₀ := x₀) hκ hb) + (nodeLen (scheduleAt n) + j)) :
    -2 < nodeWR (κ := κ) x₀ hκ hb n (nodeLen (scheduleAt n) + j) ⟨0, hi⟩ := by
  have e := subW_add (nodeLen (scheduleAt n))
    (fun j => stageρR κ (nodeρR κ (sourceWord (x₀ := x₀) hκ hb) (scheduleAt n)) j) j ⟨0, by omega⟩
  have e0 : (Fin.cast (by omega) (⟨0, by omega⟩ : Fin (rootNR (sourceWord (x₀ := x₀) hκ hb) +
      nodeLen (scheduleAt n) + j)) : Fin (rootNR (sourceWord (x₀ := x₀) hκ hb) + (nodeLen (scheduleAt n) + j))) =
      ⟨0, hi⟩ := Fin.ext rfl
  rw [e0] at e
  rw [nodeWR, e]
  rcases Nat.eq_zero_or_pos j with hj | hj
  · subst hj
    show -2 < nodeρR κ (sourceWord (x₀ := x₀) hκ hb) (scheduleAt n) ⟨0, _⟩
    rw [nodeρR, consAlt_zero_idx _ _ nodeLen_pos]
    exact neg_two_lt_bornR hκ hκ4 _ _
  · rw [stageρR, consAlt_zero_idx _ _ hj]
    exact neg_two_lt_newR hκ hκ4 _

end Path

section PathMain

variable (x₀ : ℝ) (h44 : Theorem12ParamCond44Statement.{0}) {κ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
  (hb : IsFig51Bounds κ a b a' b')
  {Ω Ωa : Type} [mΩ : MeasurableSpace Ω] [MeasurableSpace Ωa]
  (P : Measure Ω) (h : Ω → DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞)

/-- **The path clause of a node candidate at a reached sample** with a good counterflow history: the canonical start
is an ordered strict word, and the candidate's processes with the recovered node noise are Definition 2.1's local
integrated path up to the candidate's lifetime. -/
theorem nodePath_of_mem (hArc : ArcKilledWordStatement) (hhm : Measurable h)
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) (n : ℕ) (q : ℚ) (j : ℕ) (t : Fin j → ℝ≥0)
    (ω' : Ω × Ωa) (hgood : Cond44Ref.cfHistory W ζ ω'.1 ∈ goodSet49 (q : ℝ).toNNReal)
    (hR : ω' ∈ canonR (nodeCand (Ωa := Ωa) x₀ h44 hκ hκ4 hb P h W ζ (nodeNoise x₀ h44 hκ hκ4 hb P h W ζ) n q) ratGrid
        (nodeNL_pos x₀ hκ hb n) (nodeNR_pos x₀ hκ hb n) (nodeStart x₀ h44 hκ hκ4 hb P h W ζ (nodeNoise x₀ h44 hκ hκ4
        hb P h W ζ) n q)
      (nodeR0 x₀ h44 hκ hκ4 hb P h W ζ (nodeNoise x₀ h44 hκ hκ4 hb P h W ζ) n q) j t) :
    IsOrderedForceWord (canonY (nodeCand (Ωa := Ωa) x₀ h44 hκ hκ4 hb P h W ζ (nodeNoise x₀ h44 hκ hκ4 hb P h W ζ) n
        q) (nodeStart x₀ h44 hκ hκ4 hb P h W ζ (nodeNoise x₀ h44 hκ hκ4 hb P h W ζ) n q) j t ω').2.1 (canonY
        (nodeCand (Ωa := Ωa) x₀ h44 hκ hκ4 hb P h W ζ (nodeNoise x₀ h44 hκ hκ4 hb P h W ζ) n q) (nodeStart x₀ h44 hκ
        hκ4 hb P h W ζ (nodeNoise x₀ h44 hκ hκ4 hb P h W ζ) n q) j t ω').2.2 ∧
      StrictAnti (canonY (nodeCand (Ωa := Ωa) x₀ h44 hκ hκ4 hb P h W ζ (nodeNoise x₀ h44 hκ hκ4 hb P h W ζ) n q)
          (nodeStart x₀ h44 hκ hκ4 hb P h W ζ (nodeNoise x₀ h44 hκ hκ4 hb P h W ζ) n q) j t ω').2.1 ∧ StrictMono
          (canonY (nodeCand (Ωa := Ωa) x₀ h44 hκ hκ4 hb P h W ζ (nodeNoise x₀ h44 hκ hκ4 hb P h W ζ) n q) (nodeStart
          x₀ h44 hκ hκ4 hb P h W ζ (nodeNoise x₀ h44 hκ hκ4 hb P h W ζ) n q) j t ω').2.2 ∧
      Sec2.IsSLEPathUpTo κ (canonY (nodeCand (Ωa := Ωa) x₀ h44 hκ hκ4 hb P h W ζ (nodeNoise x₀ h44 hκ hκ4 hb P h W ζ)
          n q) (nodeStart x₀ h44 hκ hκ4 hb P h W ζ (nodeNoise x₀ h44 hκ hκ4 hb P h W ζ) n q) j t ω').2.1 (canonY
          (nodeCand (Ωa := Ωa) x₀ h44 hκ hκ4 hb P h W ζ (nodeNoise x₀ h44 hκ hκ4 hb P h W ζ) n q) (nodeStart x₀ h44
          hκ hκ4 hb P h W ζ (nodeNoise x₀ h44 hκ hκ4 hb P h W ζ) n q) j t ω').2.2
        (stageρL κ (nodeρL κ (sourceWord (x₀ := x₀) hκ hb) (scheduleAt n)) j)
        (stageρR κ (nodeρR κ (sourceWord (x₀ := x₀) hκ hb) (scheduleAt n)) j)
        (((nodeCand (Ωa := Ωa) x₀ h44 hκ hκ4 hb P h W ζ (nodeNoise x₀ h44 hκ hκ4 hb P h W ζ) n q) j t).W · ω') (fun i
            u => ((nodeCand (Ωa := Ωa) x₀ h44 hκ hκ4 hb P h W ζ (nodeNoise x₀ h44 hκ hκ4 hb P h W ζ) n q) j t).VL i u
            ω') (fun k u => ((nodeCand (Ωa := Ωa) x₀ h44 hκ hκ4 hb P h W ζ (nodeNoise x₀ h44 hκ hκ4 hb P h W ζ) n q)
            j t).VR k u ω')
        (((nodeCand (Ωa := Ωa) x₀ h44 hκ hκ4 hb P h W ζ (nodeNoise x₀ h44 hκ hκ4 hb P h W ζ) n q) j t).B · ω')
            (((nodeCand (Ωa := Ωa) x₀ h44 hκ hκ4 hb P h W ζ (nodeNoise x₀ h44 hκ hκ4 hb P h W ζ) n q) j t).ζ ω') := by
  set ν := nodeNoise x₀ h44 hκ hκ4 hb P h W ζ with hν
  set D := nodeD x₀ h44 hκ hκ4 hb P h W ζ ν n q with hD
  set C := nodeScale x₀ h44 hκ hκ4 hb P h W ζ ν n q with hC
  have hDr := isReg_nodeD x₀ h44 hκ hκ4 hb P h W ζ ν hhm hcf n q
  have hDt := isTree_nodeD x₀ h44 hκ hκ4 hb P h W ζ ν n q
  have hCpos : 0 < C ω'.1 := nodeScale_pos x₀ h44 hκ hκ4 hb P h W ζ ν n q ω'.1
  obtain ⟨hA, -⟩ := alive_of_mem_canonR x₀ h44 hκ hκ4 hb P h W ζ ν hhm hcf n q j t ω' hR
  -- the root marks are strictly ordered
  have h0 : MarksStrict (D.xL0 ω'.1) (D.xR0 ω'.1) := by
    have hF := Theorem15.isOrderedForceWord_flowLine (sourceWord (x₀ := x₀) hκ hb).fn
      (sourceWord (x₀ := x₀) hκ hb).jumps 0
    have hxLs : StrictAnti (flowLineXL (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps 0) :=
      fun i i' hii => Theorem14.GW0.flowLineXL_lt _ _ 0 hii
    have hxRs : StrictMono (flowLineXR (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps 0) :=
      fun i i' hii => Theorem14.GW0.flowLineXR_lt _ _ 0 hii
    obtain ⟨-, o2, -, o4⟩ := histStart_ordered hF hgood
    obtain ⟨s1, s2⟩ := histStart_strict hF hxLs hxRs hgood
    exact And.intro o2 (And.intro s1 (And.intro o4 s2))
  have hq' : ∀ (k' : ℕ) (t' : Fin (k' + 1) → ℝ≥0), D.valid (k' + 1) t' →
      qLast k' (Fin.init t') < qLast (k' + 1) t' := by
    intro k' t' hv
    have hv' : IsValid (k' + 1) t' := hv.1
    cases k' with
    | zero => exact decode_pos (hv'.2 _).1 (hv'.2 _).2.1
    | succ k' => exact decode_strictMono (hv'.2 _).2.1 (hv'.1 (Fin.castSucc_lt_last (Fin.last k')))
  obtain ⟨hL0, hLs, hR0, hRs⟩ := TreeData.marks_strict hDr hDt hArc hq' ω'.1 h0 _ _ hA
  obtain ⟨hmL, hmR⟩ := canonY_nodeCand_marks x₀ h44 hκ hκ4 hb P h W ζ ν hhm hcf n q j t ω'
  rw [funext hmL, funext hmR]
  refine ⟨⟨fun i i' hii => mul_le_mul_of_nonneg_left (hLs.antitone hii) hCpos.le,
    fun i => mul_nonpos_of_nonneg_of_nonpos hCpos.le (hL0 _),
    fun i i' hii => mul_le_mul_of_nonneg_left (hRs.monotone hii) hCpos.le,
    fun i => mul_nonneg hCpos.le (hR0 _)⟩,
    fun i i' hii => mul_lt_mul_of_pos_left (hLs hii) (NNReal.coe_pos.2 hCpos),
    fun i i' hii => mul_lt_mul_of_pos_left (hRs hii) (NNReal.coe_pos.2 hCpos), ?_⟩
  -- the killed word of the tree candidate's arc piece at this sample
  have hγ := (hDr.isKilledFamily (nodeLen (scheduleAt n) + j) (Fin.append (nodePre (scheduleAt n)) t)).arc ω'.1
  have hSlt := TreeData.startCap_lt_kLife hDr hA
  have hK := hArc (Ω := Unit) (γ := fun _ => D.img _ (Fin.append (nodePre (scheduleAt n)) t) ω'.1)
    (P := fun _ => D.pre _ (Fin.append (nodePre (scheduleAt n)) t) ω'.1)
    (S₀ := fun _ => D.startCap _ (Fin.append (nodePre (scheduleAt n)) t) ω'.1) (fun _ => hγ)
    (xL := fun _ => (D.marks _ (Fin.append (nodePre (scheduleAt n)) t) ω'.1).1)
    (xR := fun _ => (D.marks _ (Fin.append (nodePre (scheduleAt n)) t) ω'.1).2) (fun _ => hL0) (fun _ => hR0)
    (fun _ => hLs.antitone) (fun _ => hRs.monotone)
  have hζ0 : (0 : ℝ≥0∞) < arcζ (fun _ : Unit => D.img _ (Fin.append (nodePre (scheduleAt n)) t) ω'.1)
      (fun _ => D.pre _ (Fin.append (nodePre (scheduleAt n)) t) ω'.1)
      (fun _ => D.startCap _ (Fin.append (nodePre (scheduleAt n)) t) ω'.1) univ () := by
    have h1 := (lt_arcζ_iff (γ := D.img _ (Fin.append (nodePre (scheduleAt n)) t))
      (P := D.pre _ (Fin.append (nodePre (scheduleAt n)) t))
      (S₀ := D.startCap _ (Fin.append (nodePre (scheduleAt n)) t))
      (A := D.alive _ (Fin.append (nodePre (scheduleAt n)) t)) (u := 0) (ω := ω'.1)).2 ⟨hA, by rwa [add_zero]⟩
    rw [arcζ_onePt hA, ENNReal.coe_zero] at h1
    exact h1
  have hVL0 : ∀ i, arcVL (fun _ : Unit => D.img _ (Fin.append (nodePre (scheduleAt n)) t) ω'.1)
      (fun _ => D.pre _ (Fin.append (nodePre (scheduleAt n)) t) ω'.1)
      (fun _ => D.startCap _ (Fin.append (nodePre (scheduleAt n)) t) ω'.1) univ
      (fun _ => (D.marks _ (Fin.append (nodePre (scheduleAt n)) t) ω'.1).1) i 0 () =
      (D.marks _ (Fin.append (nodePre (scheduleAt n)) t) ω'.1).1 i := fun i =>
    arcVL_zero_eq (A := univ) (ω := ()) hγ (mem_univ _) (hL0 i) hSlt
  have hVR0 : ∀ k, arcVR (fun _ : Unit => D.img _ (Fin.append (nodePre (scheduleAt n)) t) ω'.1)
      (fun _ => D.pre _ (Fin.append (nodePre (scheduleAt n)) t) ω'.1)
      (fun _ => D.startCap _ (Fin.append (nodePre (scheduleAt n)) t) ω'.1) univ
      (fun _ => (D.marks _ (Fin.append (nodePre (scheduleAt n)) t) ω'.1).2) k 0 () =
      (D.marks _ (Fin.append (nodePre (scheduleAt n)) t) ω'.1).2 k := fun k =>
    arcVR_zero_eq (A := univ) (ω := ()) hγ (mem_univ _) (hR0 k) hSlt
  have hthr0 : ¬ ForceWord.ThresholdCondition (nodeWL x₀ hκ hb n (nodeLen (scheduleAt n) + j))
      (nodeWR x₀ hκ hb n (nodeLen (scheduleAt n) + j))
      (arcW (fun _ : Unit => D.img _ (Fin.append (nodePre (scheduleAt n)) t) ω'.1)
        (fun _ => D.pre _ (Fin.append (nodePre (scheduleAt n)) t) ω'.1)
        (fun _ => D.startCap _ (Fin.append (nodePre (scheduleAt n)) t) ω'.1) univ 0 ())
      (fun i => arcVL (fun _ : Unit => D.img _ (Fin.append (nodePre (scheduleAt n)) t) ω'.1)
        (fun _ => D.pre _ (Fin.append (nodePre (scheduleAt n)) t) ω'.1)
        (fun _ => D.startCap _ (Fin.append (nodePre (scheduleAt n)) t) ω'.1) univ
        (fun _ => (D.marks _ (Fin.append (nodePre (scheduleAt n)) t) ω'.1).1) i 0 ())
      (fun k => arcVR (fun _ : Unit => D.img _ (Fin.append (nodePre (scheduleAt n)) t) ω'.1)
        (fun _ => D.pre _ (Fin.append (nodePre (scheduleAt n)) t) ω'.1)
        (fun _ => D.startCap _ (Fin.append (nodePre (scheduleAt n)) t) ω'.1) univ
        (fun _ => (D.marks _ (Fin.append (nodePre (scheduleAt n)) t) ω'.1).2) k 0 ()) := by
    rw [arcW_zero']
    simp only [hVL0, hVR0]
    have hnL : 0 < rootNL (sourceWord (x₀ := x₀) hκ hb) + (nodeLen (scheduleAt n) + j) :=
      Nat.lt_of_lt_of_le (rootNL_pos _) (Nat.le_add_right _ _)
    have hnR : 0 < rootNR (sourceWord (x₀ := x₀) hκ hb) + (nodeLen (scheduleAt n) + j) :=
      Nat.lt_of_lt_of_le (rootNR_pos _) (Nat.le_add_right _ _)
    refine not_threshold_of_unique ⟨0, hnL⟩ (fun i hi => ?_) (nodeWL_zero x₀ hκ hκ4 hb n j hnL) ⟨0, hnR⟩
      (fun k hk => ?_) (nodeWR_zero x₀ hκ hκ4 hb n j hnR)
    · have hlt : (⟨0, hnL⟩ : Fin _) < i := by
        rw [Fin.lt_def]; exact Nat.pos_of_ne_zero fun h => hi (Fin.ext h)
      exact ((hLs hlt).trans_le (hL0 _)).ne
    · have hlt : (⟨0, hnR⟩ : Fin _) < k := by
        rw [Fin.lt_def]; exact Nat.pos_of_ne_zero fun h => hk (Fin.ext h)
      exact ((hR0 _).trans_lt (hRs hlt)).ne'
  have hp := hK.isSLEPathUpTo_recNoise (fun _ => hζ0) hκ (nodeWL x₀ hκ hb n (nodeLen (scheduleAt n) + j))
    (nodeWR x₀ hκ hb n (nodeLen (scheduleAt n) + j)) () hthr0
  set tt := Fin.append (nodePre (scheduleAt n)) t with htt
  simp only [hVL0, hVR0] at hp
  simp only [← arcW_onePt (γ := D.img _ tt) (P := D.pre _ tt) (S₀ := D.startCap _ tt) hA,
    ← arcVL_onePt (γ := D.img _ tt) (P := D.pre _ tt) (S₀ := D.startCap _ tt) hA (fun ω => (D.marks _ tt ω).1),
    ← arcVR_onePt (γ := D.img _ tt) (P := D.pre _ tt) (S₀ := D.startCap _ tt) hA (fun ω => (D.marks _ tt ω).2),
    ← arcζ_onePt (γ := D.img _ tt) (P := D.pre _ tt) (S₀ := D.startCap _ tt) hA] at hp
  have hp2 := isSLEPathUpTo_cast (Nat.add_assoc (rootNL (sourceWord (x₀ := x₀) hκ hb)) (nodeLen (scheduleAt n)) j).symm
    (Nat.add_assoc (rootNR (sourceWord (x₀ := x₀) hκ hb)) (nodeLen (scheduleAt n)) j).symm hp
  have hp3 := hp2.dilate hCpos
  have eL : ∀ i, nodeWL x₀ hκ hb n (nodeLen (scheduleAt n) + j) (Fin.cast (Nat.add_assoc _ _ _) i) =
      stageρL κ (nodeρL κ (sourceWord (x₀ := x₀) hκ hb) (scheduleAt n)) j i := fun i =>
    subW_add (nodeLen (scheduleAt n)) (fun j => stageρL κ (nodeρL κ (sourceWord (x₀ := x₀) hκ hb) (scheduleAt n)) j) j i
  have eR : ∀ k, nodeWR x₀ hκ hb n (nodeLen (scheduleAt n) + j) (Fin.cast (Nat.add_assoc _ _ _) k) =
      stageρR κ (nodeρR κ (sourceWord (x₀ := x₀) hκ hb) (scheduleAt n)) j k := fun k =>
    subW_add (nodeLen (scheduleAt n)) (fun j => stageρR κ (nodeρR κ (sourceWord (x₀ := x₀) hκ hb) (scheduleAt n)) j) j k
  simp only [eL, eR] at hp3
  -- the noise of the node candidate is the dilated recovered noise of the tree candidate
  have hB : (fun u => (nodeCand (Ωa := Ωa) x₀ h44 hκ hκ4 hb P h W ζ ν n q j t).B u ω') =
      fun u => (C ω'.1 : ℝ) * recNoise κ (nodeWL x₀ hκ hb n (nodeLen (scheduleAt n) + j))
        (nodeWR x₀ hκ hb n (nodeLen (scheduleAt n) + j)) (D.marks _ tt ω'.1).1 (D.marks _ tt ω'.1).2
        (fun s => (D.cand _ tt).W s ω'.1) (fun i s => (D.cand _ tt).VL i s ω'.1)
        (fun k s => (D.cand _ tt).VR k s ω'.1) (u / C ω'.1 ^ 2) := by
    funext u
    show (C ω'.1 : ℝ) * nodeNoise x₀ h44 hκ hκ4 hb P h W ζ n q _ tt (u / C ω'.1 ^ 2) ω'.1 = _
    unfold nodeNoise
    rw [nodeD_cand_VL_noise x₀ h44 hκ hκ4 hb P h W ζ (fun _ _ _ _ _ _ => 0) ν,
      nodeD_cand_VR_noise x₀ h44 hκ hκ4 hb P h W ζ (fun _ _ _ _ _ _ => 0) ν]
    have h1 : (fun i => (D.cand _ tt).VL i 0 ω'.1) = (D.marks _ tt ω'.1).1 :=
      funext fun i => arcVL_zero_eq (xL := fun ω => (D.marks _ tt ω).1) hγ hA (hL0 i) hSlt
    have h2 : (fun k => (D.cand _ tt).VR k 0 ω'.1) = (D.marks _ tt ω'.1).2 :=
      funext fun k => arcVR_zero_eq (xR := fun ω => (D.marks _ tt ω).2) hγ hA (hR0 k) hSlt
    rw [← h1, ← h2]
    rfl
  rw [hB]
  exact hp3

end PathMain

/-! ### The node-law leaf for the stage objects with the recovered node noise -/

/-- **The path clause of every node law** for `nodeObjects` (named inputs: PROVE-STAGED-S6's arc killed word and the
clearance form of Part A, which gives the good counterflow histories almost surely, as for the root path leaf). -/
theorem nodePathOn_nodeObjects (h44 : Theorem12ParamCond44Statement.{0}) (hArc : ArcKilledWordStatement)
    (hA : PartAInputsSixteenDivOfClearance) : NodePathOn h44 (nodeObjects h44) := by
  intro κ x₀ a b a' b' hκ hκ4 hb Ω _ _ P _ h W ζ γ hG hcf htr d n q hq j t
  have hr : 0 < (q : ℝ).toNNReal := Real.toNNReal_pos.2 (by exact_mod_cast hq)
  have h2 := Sec7.StripMarks.ae_cfHistory_mem_goodSet49_of_clearance hκ hκ4 hb hA hG hcf hr
  have h2' : ∀ᵐ ω' ∂(P.prod (Measure.dirac (0 : ℝ))), Cond44Ref.cfHistory W ζ ω'.1 ∈ goodSet49 (q : ℝ).toNNReal :=
    Measure.quasiMeasurePreserving_fst.ae h2
  show ∀ᵐ ω' ∂(P.prod (Measure.dirac (0 : ℝ))), _
  filter_upwards [h2'] with ω' hω hR
  exact nodePath_of_mem x₀ h44 hκ hκ4 hb P h W ζ hArc hG.1 hcf n q j t ω' hω hR

/-- **The node-law leaf `hNodeLaw` of the expanded Theorem 1.2** for the stage objects with the recovered node noise,
from the comparison clause of the node candidates (`NodeCompOn`, which does not read the noise). -/
theorem nodeLawOn_nodeObjects (h44 : Theorem12ParamCond44Statement.{0}) (hArc : ArcKilledWordStatement)
    (hA : PartAInputsSixteenDivOfClearance) (hC : NodeCompOn h44 (nodeObjects h44)) :
    NodeLawOn h44 (nodeObjects h44) :=
  nodeLawOn_of_path_comp (nodePathOn_nodeObjects h44 hArc hA) hC

end InteractingSLE.Sec5.CrossCond.StagedNode
