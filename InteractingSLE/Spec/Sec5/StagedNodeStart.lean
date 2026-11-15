/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.StagedNodeNoise

/-!
# Proposition 5.9's node experiments: the canonical starts are the dilated tree marks

Packet PROVE-STAGED-NODE. A node candidate at `(j, t)` is the tree candidate at the full depth `m + j` (list
`nodePre s ++ t`) of the node tree, dilated by the node factor `C = nodeScale` (`t ↦ C X(t/C²)`). The canonical start
`canonY` of the node candidates is computed from the dilated pieces (the switch at the dilated clock inverse), while the
tree candidates start from the tree marks `TreeData.marks`. Here:

* `clkInv_dilate`: the clock inverse of a dilated stage is `C²` times the undilated one;
* `TreeData.marks_succ`: the tree marks after a switch are the start formula at the clock inverse;
* **`canonY_nodeCand_marks`**: for every `(j, t)` and sample, the marks of the canonical node start are the
  dilated tree marks at depth `m + j` (indices cast along `rootNL + m + j = rootNL + (m + j)`);
* `canonY_nodeCand_fst_succ`: the absolute driver of the start after a switch.

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
open Wire.Night LawUnique WangWu GlueCond Word49 Prop59NodeTree StagedS4 StagedCand

/-! ### Clock inverses of dilated stages -/

section ClkInv

variable {Ω Ω' : Type*} {nL₀ nR₀ nL' nR' j j' : ℕ}

/-- **The clock inverse of a dilated clock**: if `d.clk ω' u = e.clk ω (u / c²)` with `c > 0` and `e.clk ω` strictly
increasing, then `clkInv d g ω' = c² · clkInv e g ω`. -/
theorem clkInv_dilate {d : StageData Ω' (nL' + j') (nR' + j')} {e : StageData Ω (nL₀ + j) (nR₀ + j)} {ω' : Ω'} {ω :
    Ω} {c : ℝ≥0}
    (hc : 0 < c) (hclk : ∀ u, d.clk ω' u = e.clk ω (u / c ^ 2)) (hm : StrictMono (e.clk ω)) (g : ℝ≥0) :
    clkInv d g ω' = c ^ 2 * clkInv e g ω := by
  classical
  have hc2 : c ^ 2 ≠ 0 := pow_ne_zero 2 hc.ne'
  have hmd : StrictMono (d.clk ω') := fun a b hab => by
    rw [hclk, hclk]
    exact hm ((div_lt_div_iff_of_pos_right (pow_pos hc 2)).2 hab)
  by_cases h : ω ∈ clkHit e g
  · have he := clk_clkInv h
    have hd : d.clk ω' (c ^ 2 * clkInv e g ω) = g := by
      rw [hclk, mul_div_cancel_left₀ _ hc2, he]
    exact (eq_clkInv hmd hd).symm
  · have hd : ω' ∉ clkHit d g := by
      rintro ⟨s, hs⟩
      exact h ⟨s / c ^ 2, by rw [← hclk]; exact hs⟩
    simp only [clkInv, h, hd, ↓reduceDIte, mul_zero]

end ClkInv

/-! ### Tree marks after a switch -/

section Marks

variable {Ω : Type*} {nL₀ nR₀ : ℕ}

/-- **The tree marks after a switch** are the start formula of the parent candidate at its clock inverse. -/
theorem TreeData.marks_succ (D : TreeData Ω nL₀ nR₀) (k : ℕ) (t : Fin (k + 1) → ℝ≥0) (ω : Ω) :
    D.marks (k + 1) t ω =
      (Fin.cons 0 fun i => (D.cand k (Fin.init t)).VL i (candInv D.cand k (Fin.init t) (t (Fin.last k)) ω) ω -
          (D.cand k (Fin.init t)).W (candInv D.cand k (Fin.init t) (t (Fin.last k)) ω) ω,
        Fin.cons 0 fun i => (D.cand k (Fin.init t)).VR i (candInv D.cand k (Fin.init t) (t (Fin.last k)) ω) ω -
          (D.cand k (Fin.init t)).W (candInv D.cand k (Fin.init t) (t (Fin.last k)) ω) ω) :=
  rfl

theorem append_last {α : Type*} {m j : ℕ} (a : Fin m → α) (b : Fin (j + 1) → α) :
    (Fin.append a b : Fin (m + (j + 1)) → α) (Fin.last (m + j)) = b (Fin.last j) := by
  have e : (Fin.last (m + j) : Fin (m + (j + 1))) = Fin.natAdd m (Fin.last j) := Fin.ext rfl
  rw [e, Fin.append_right]

/-- `Fin.cons` read through a cast of the index. -/
theorem cons_cast {n n' : ℕ} (h : n + 1 = n' + 1) (a : ℝ) (f : Fin n' → ℝ) (i : Fin (n + 1)) :
    (Fin.cons a f : Fin (n' + 1) → ℝ) (Fin.cast h i) =
      (Fin.cons a (fun i₀ : Fin n => f (Fin.cast (by omega) i₀)) : Fin (n + 1) → ℝ) i := by
  refine Fin.cases ?_ (fun i₀ => ?_) i
  · have e : (Fin.cast h 0 : Fin (n' + 1)) = 0 := Fin.ext rfl
    rw [e, Fin.cons_zero, Fin.cons_zero]
  · have e : (Fin.cast h i₀.succ : Fin (n' + 1)) = (Fin.cast (by omega) i₀ : Fin n').succ := Fin.ext rfl
    rw [e, Fin.cons_succ, Fin.cons_succ]

end Marks

/-! ### The canonical node starts -/

section Starts

variable (x₀ : ℝ) (h44 : Theorem12ParamCond44Statement.{0}) {κ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
  (hb : IsFig51Bounds κ a b a' b')
  {Ω Ωa : Type} [mΩ : MeasurableSpace Ω] [MeasurableSpace Ωa]
  (P : Measure Ω) (h : Ω → DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞)
  (noise : ℕ → ℚ → (j : ℕ) → (Fin j → ℝ≥0) → ℝ≥0 → Ω → ℝ)

omit [MeasurableSpace Ωa] in
/-- The clock inverse of a node candidate is the dilated clock inverse of its tree candidate. -/
theorem candInv_nodeCand (hhm : Measurable h)
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) (n : ℕ) (q : ℚ) (j : ℕ)
    (t : Fin j → ℝ≥0) (g : ℝ≥0) (ω' : Ω × Ωa) :
    candInv (nodeCand (Ωa := Ωa) x₀ h44 hκ hκ4 hb P h W ζ noise n q) j t g ω' =
      nodeScale x₀ h44 hκ hκ4 hb P h W ζ noise n q ω'.1 ^ 2 *
        candInv (nodeD x₀ h44 hκ hκ4 hb P h W ζ noise n q).cand (nodeLen (scheduleAt n) + j)
          (Fin.append (nodePre (scheduleAt n)) t) g ω'.1 := by
  have hD := isReg_nodeD x₀ h44 hκ hκ4 hb P h W ζ noise hhm hcf n q
  exact clkInv_dilate (nodeScale_pos x₀ h44 hκ hκ4 hb P h W ζ noise n q ω'.1) (fun u => rfl)
    (strictMono_arcClk (hD.isKilledFamily _ _).arc ω'.1) g

omit [MeasurableSpace Ωa] in
/-- **The marks of the canonical node starts are the dilated tree marks** at the full depth `m + j`. -/
theorem canonY_nodeCand_marks (hhm : Measurable h)
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) (n : ℕ) (q : ℚ) (j : ℕ)
    (t : Fin j → ℝ≥0) (ω' : Ω × Ωa) :
    (∀ i, (canonY (nodeCand (Ωa := Ωa) x₀ h44 hκ hκ4 hb P h W ζ noise n q)
        (nodeStart x₀ h44 hκ hκ4 hb P h W ζ noise n q) j t ω').2.1 i =
      (nodeScale x₀ h44 hκ hκ4 hb P h W ζ noise n q ω'.1 : ℝ) *
        ((nodeD x₀ h44 hκ hκ4 hb P h W ζ noise n q).marks (nodeLen (scheduleAt n) + j)
          (Fin.append (nodePre (scheduleAt n)) t) ω'.1).1
          (Fin.cast (m := rootNL (sourceWord (x₀ := x₀) hκ hb) + (nodeLen (scheduleAt n) + j)) (Nat.add_assoc _ _ _)
              i)) ∧
    (∀ k, (canonY (nodeCand (Ωa := Ωa) x₀ h44 hκ hκ4 hb P h W ζ noise n q)
        (nodeStart x₀ h44 hκ hκ4 hb P h W ζ noise n q) j t ω').2.2 k =
      (nodeScale x₀ h44 hκ hκ4 hb P h W ζ noise n q ω'.1 : ℝ) *
        ((nodeD x₀ h44 hκ hκ4 hb P h W ζ noise n q).marks (nodeLen (scheduleAt n) + j)
          (Fin.append (nodePre (scheduleAt n)) t) ω'.1).2
          (Fin.cast (m := rootNR (sourceWord (x₀ := x₀) hκ hb) + (nodeLen (scheduleAt n) + j)) (Nat.add_assoc _ _ _)
              k)) := by
  set D := nodeD x₀ h44 hκ hκ4 hb P h W ζ noise n q with hDdef
  set C := nodeScale x₀ h44 hκ hκ4 hb P h W ζ noise n q with hC
  have hCpos : 0 < C ω'.1 := nodeScale_pos x₀ h44 hκ hκ4 hb P h W ζ noise n q ω'.1
  have hC2 : C ω'.1 ^ 2 ≠ 0 := pow_ne_zero 2 hCpos.ne'
  cases j with
  | zero =>
    have ht : t = Fin.elim0 := funext fun i => i.elim0
    subst ht
    have e := append_elim0 (nodePre (scheduleAt n))
    refine ⟨fun i => ?_, fun k => ?_⟩
    · show (C ω'.1 : ℝ) * (nodeMarks x₀ h44 hκ hκ4 hb P h W ζ noise n q ω'.1).1 i = _
      rw [e]
      rfl
    · show (C ω'.1 : ℝ) * (nodeMarks x₀ h44 hκ hκ4 hb P h W ζ noise n q ω'.1).2 k = _
      rw [e]
      rfl
  | succ j =>
    have hinv := candInv_nodeCand x₀ h44 hκ hκ4 hb P h W ζ noise hhm hcf n q j (Fin.init t) (t (Fin.last j)) ω'
    have hinit := init_append (nodePre (scheduleAt n)) t
    have hlast := append_last (nodePre (scheduleAt n)) t
    have hmk := TreeData.marks_succ D (nodeLen (scheduleAt n) + j)
      (Fin.append (nodePre (scheduleAt n)) t : Fin (nodeLen (scheduleAt n) + (j + 1)) → ℝ≥0) ω'.1
    rw [hinit, hlast] at hmk
    set s := candInv D.cand (nodeLen (scheduleAt n) + j) (Fin.append (nodePre (scheduleAt n)) (Fin.init t))
      (t (Fin.last j)) ω'.1 with hs
    have hsc : candInv (nodeCand (Ωa := Ωa) x₀ h44 hκ hκ4 hb P h W ζ noise n q) j (Fin.init t) (t (Fin.last j)) ω' /
        C ω'.1 ^ 2 = s := by
      rw [hinv, mul_div_cancel_left₀ _ hC2]
    refine ⟨fun i => ?_, fun k => ?_⟩
    · have hm' : D.marks (nodeLen (scheduleAt n) + (j + 1)) (Fin.append (nodePre (scheduleAt n)) t) ω'.1 =
          D.marks (nodeLen (scheduleAt n) + j + 1)
            (Fin.append (nodePre (scheduleAt n)) t : Fin (nodeLen (scheduleAt n) + (j + 1)) → ℝ≥0) ω'.1 := rfl
      rw [hm', hmk]
      show (Fin.cons 0 fun i => (C ω'.1 : ℝ) *
          (D.cand (nodeLen (scheduleAt n) + j) (Fin.append (nodePre (scheduleAt n)) (Fin.init t))).VL _ (candInv
              (nodeCand (Ωa := Ωa) x₀ h44 hκ hκ4 hb P h W ζ
            noise n q) j (Fin.init t) (t (Fin.last j)) ω' / C ω'.1 ^ 2) ω'.1 -
          (C ω'.1 : ℝ) * (D.cand (nodeLen (scheduleAt n) + j) (Fin.append (nodePre (scheduleAt n)) (Fin.init t))).W
              (candInv (nodeCand (Ωa := Ωa) x₀ h44 hκ hκ4
            hb P h W ζ noise n q) j (Fin.init t) (t (Fin.last j)) ω' / C ω'.1 ^ 2) ω'.1 : Fin _ → ℝ) i = _
      rw [hsc]
      dsimp only
      rw [cons_cast]
      refine Fin.cases ?_ (fun i₀ => ?_) i
      · simp only [Fin.cons_zero, mul_zero]
      · simp only [Fin.cons_succ]
        rw [mul_sub]
    · have hm' : D.marks (nodeLen (scheduleAt n) + (j + 1)) (Fin.append (nodePre (scheduleAt n)) t) ω'.1 =
          D.marks (nodeLen (scheduleAt n) + j + 1)
            (Fin.append (nodePre (scheduleAt n)) t : Fin (nodeLen (scheduleAt n) + (j + 1)) → ℝ≥0) ω'.1 := rfl
      rw [hm', hmk]
      show (Fin.cons 0 fun k => (C ω'.1 : ℝ) *
          (D.cand (nodeLen (scheduleAt n) + j) (Fin.append (nodePre (scheduleAt n)) (Fin.init t))).VR _ (candInv
              (nodeCand (Ωa := Ωa) x₀ h44 hκ hκ4 hb P h W ζ
            noise n q) j (Fin.init t) (t (Fin.last j)) ω' / C ω'.1 ^ 2) ω'.1 -
          (C ω'.1 : ℝ) * (D.cand (nodeLen (scheduleAt n) + j) (Fin.append (nodePre (scheduleAt n)) (Fin.init t))).W
              (candInv (nodeCand (Ωa := Ωa) x₀ h44 hκ hκ4
            hb P h W ζ noise n q) j (Fin.init t) (t (Fin.last j)) ω' / C ω'.1 ^ 2) ω'.1 : Fin _ → ℝ) k = _
      rw [hsc]
      dsimp only
      rw [cons_cast]
      refine Fin.cases ?_ (fun k₀ => ?_) k
      · simp only [Fin.cons_zero, mul_zero]
      · simp only [Fin.cons_succ]
        rw [mul_sub]

end Starts

end InteractingSLE.Sec5.CrossCond.StagedNode
