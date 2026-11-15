/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.StagedNTrWire
import InteractingSLE.Spec.Sec5.StagedNodeStart

/-!
# Prop 5.9's node laws: the glued observable from the node marks identity

Packet PROVE-STAGED-NODETRANSFER. `NodeGlueObs` (`StagedNTrBound`) compares, at a glued sample `p` whose node flags'
candidate `nodePre ++ t` is alive and whose pair `gZ p` reaches the node candidate `(j, t)` on `Gam`, the canonical
start and the killed samples of `Gam`'s node candidate with the dilated restarted word of the glued space. Here it is
reduced to the **marks identity** `NodeGlueMarks` (the tree marks of `gamNodeData` at the full depth `nodeLen + j` are
the initial marks of the restarted word in tree order), PROVE-STAGED-REPJ's `GlueMarks` for the node tree:

* **`canonY_gamNodeCand_marks`**: the canonical node starts on `Gam` are the dilated tree marks at the full depth
  (PROVE-STAGED-NODE's `canonY_nodeCand_marks`, rerun on `Gam`);
* `gamNodeAlpha_append`, `seedLine_candWF`, **`gamNodeData_img_eq`**, `gamNodeData_pre_eq`, `gamNodeData_alive`,
  `gamNodeData_startCap_eq`: the node tree's full-depth arc on `Gam` at `gZ p` is the glued restarted arc (undilated:
  the node tree has `lam = 1`);
* `ae_gamNodeGood_glue`: the node good set on `Gam` holds almost surely at `gZ p` (the law of the pair);
* **`nodeGlueObs_of_marks`**.

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal Real
open LQGMetric (DistOn)

namespace InteractingSLE.Sec5.CrossCond.StagedNTr

open WangWu hiding ratPt exists_ratPt_dist_lt
open WangWu.ImgWord LawUnique GlueCond Cond44Ref Word49 StagedS3 StagedS4 StagedS5 StagedS6
open Restart Exist.StagedLaw Exist.Staged
open Sec7.AdmCode Prop513TreeExtract Prop513Schedule Prop513Target Prop59Pieces Prop59Stage Prop59System
open Prop59Nodes Prop59NodeTree StagedRepLater StagedKCand StagedKill StagedRep StagedRepJ StagedNComp StagedCand
open StagedNode
open Sec4 (IsStripGFF IsStripCounterflowDriver)

/-! ### The canonical node starts on `Gam` -/

section Canon

variable (h44 : Theorem12ParamCond44Statement.{0}) {κ x₀ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
  (hb : IsFig51Bounds κ a b a' b') (n : ℕ) (r : ℝ≥0)

/-- The clock inverse of a node candidate on `Gam` is the dilated clock inverse of its tree candidate. -/
theorem candInv_gamNodeCand (j : ℕ) (t : Fin j → ℝ≥0) (g : ℝ≥0) (γ : Gam) :
    candInv (gamNodeCand h44 hκ hκ4 (x₀ := x₀) hb n r) j t g γ =
      gamNodeScale h44 hκ hκ4 (x₀ := x₀) hb n r γ ^ 2 *
        candInv (gamNodeData h44 hκ hκ4 (x₀ := x₀) hb (scheduleAt n) r).cand (nodeLen (scheduleAt n) + j)
          (Fin.append (nodePre (scheduleAt n)) t) g γ :=
  clkInv_dilate (gamNodeScale_pos h44 hκ hκ4 hb n r γ) (fun _ => rfl)
    (strictMono_arcClk ((isReg_gamNodeData h44 hκ hκ4 hb (scheduleAt n) r).isKilledFamily _ _).arc γ) g

/-- **The marks of the canonical node starts on `Gam` are the dilated tree marks** at the full depth `m + j`. -/
theorem canonY_gamNodeCand_marks (j : ℕ) (t : Fin j → ℝ≥0) (γ : Gam) :
    (∀ i, (canonY (gamNodeCand h44 hκ hκ4 (x₀ := x₀) hb n r) (gamNodeStart h44 hκ hκ4 (x₀ := x₀) hb n r) j t
        γ).2.1 i =
      (gamNodeScale h44 hκ hκ4 (x₀ := x₀) hb n r γ : ℝ) *
        ((gamNodeData h44 hκ hκ4 (x₀ := x₀) hb (scheduleAt n) r).marks (nodeLen (scheduleAt n) + j)
          (Fin.append (nodePre (scheduleAt n)) t) γ).1
          (Fin.cast (m := rootNL (sourceWord (x₀ := x₀) hκ hb) + (nodeLen (scheduleAt n) + j)) (Nat.add_assoc _ _ _)
              i)) ∧
    (∀ k, (canonY (gamNodeCand h44 hκ hκ4 (x₀ := x₀) hb n r) (gamNodeStart h44 hκ hκ4 (x₀ := x₀) hb n r) j t
        γ).2.2 k =
      (gamNodeScale h44 hκ hκ4 (x₀ := x₀) hb n r γ : ℝ) *
        ((gamNodeData h44 hκ hκ4 (x₀ := x₀) hb (scheduleAt n) r).marks (nodeLen (scheduleAt n) + j)
          (Fin.append (nodePre (scheduleAt n)) t) γ).2
          (Fin.cast (m := rootNR (sourceWord (x₀ := x₀) hκ hb) + (nodeLen (scheduleAt n) + j)) (Nat.add_assoc _ _ _)
              k)) := by
  set D := gamNodeData h44 hκ hκ4 (x₀ := x₀) hb (scheduleAt n) r with hDdef
  set C := gamNodeScale h44 hκ hκ4 (x₀ := x₀) hb n r with hC
  have hCpos : 0 < C γ := gamNodeScale_pos h44 hκ hκ4 hb n r γ
  have hC2 : C γ ^ 2 ≠ 0 := pow_ne_zero 2 hCpos.ne'
  cases j with
  | zero =>
    have ht : t = Fin.elim0 := funext fun i => i.elim0
    subst ht
    have e := append_elim0 (nodePre (scheduleAt n))
    refine ⟨fun i => ?_, fun k => ?_⟩
    · show (C γ : ℝ) * (gamNodeMarks h44 hκ hκ4 (x₀ := x₀) hb n r γ).1 i = _
      rw [e]
      rfl
    · show (C γ : ℝ) * (gamNodeMarks h44 hκ hκ4 (x₀ := x₀) hb n r γ).2 k = _
      rw [e]
      rfl
  | succ j =>
    have hinv := candInv_gamNodeCand h44 hκ hκ4 (x₀ := x₀) hb n r j (Fin.init t) (t (Fin.last j)) γ
    have hinit := init_append (nodePre (scheduleAt n)) t
    have hlast := append_last (nodePre (scheduleAt n)) t
    have hmk := TreeData.marks_succ D (nodeLen (scheduleAt n) + j)
      (Fin.append (nodePre (scheduleAt n)) t : Fin (nodeLen (scheduleAt n) + (j + 1)) → ℝ≥0) γ
    rw [hinit, hlast] at hmk
    set s := candInv D.cand (nodeLen (scheduleAt n) + j) (Fin.append (nodePre (scheduleAt n)) (Fin.init t))
      (t (Fin.last j)) γ with hs
    have hsc : candInv (gamNodeCand h44 hκ hκ4 (x₀ := x₀) hb n r) j (Fin.init t) (t (Fin.last j)) γ /
        C γ ^ 2 = s := by
      rw [hinv, mul_div_cancel_left₀ _ hC2]
    refine ⟨fun i => ?_, fun k => ?_⟩
    · have hm' : D.marks (nodeLen (scheduleAt n) + (j + 1)) (Fin.append (nodePre (scheduleAt n)) t) γ =
          D.marks (nodeLen (scheduleAt n) + j + 1)
            (Fin.append (nodePre (scheduleAt n)) t : Fin (nodeLen (scheduleAt n) + (j + 1)) → ℝ≥0) γ := rfl
      rw [hm', hmk]
      show (Fin.cons 0 fun i => (C γ : ℝ) *
          (D.cand (nodeLen (scheduleAt n) + j) (Fin.append (nodePre (scheduleAt n)) (Fin.init t))).VL _ (candInv
              (gamNodeCand h44 hκ hκ4 (x₀ := x₀) hb n r) j (Fin.init t) (t (Fin.last j)) γ / C γ ^ 2) γ -
          (C γ : ℝ) * (D.cand (nodeLen (scheduleAt n) + j) (Fin.append (nodePre (scheduleAt n)) (Fin.init t))).W
              (candInv (gamNodeCand h44 hκ hκ4 (x₀ := x₀) hb n r) j (Fin.init t) (t (Fin.last j)) γ / C γ ^ 2) γ :
            Fin _ → ℝ) i = _
      rw [hsc]
      dsimp only
      rw [cons_cast]
      refine Fin.cases ?_ (fun i₀ => ?_) i
      · simp only [Fin.cons_zero, mul_zero]
      · simp only [Fin.cons_succ]
        rw [mul_sub]
    · have hm' : D.marks (nodeLen (scheduleAt n) + (j + 1)) (Fin.append (nodePre (scheduleAt n)) t) γ =
          D.marks (nodeLen (scheduleAt n) + j + 1)
            (Fin.append (nodePre (scheduleAt n)) t : Fin (nodeLen (scheduleAt n) + (j + 1)) → ℝ≥0) γ := rfl
      rw [hm', hmk]
      show (Fin.cons 0 fun k => (C γ : ℝ) *
          (D.cand (nodeLen (scheduleAt n) + j) (Fin.append (nodePre (scheduleAt n)) (Fin.init t))).VR _ (candInv
              (gamNodeCand h44 hκ hκ4 (x₀ := x₀) hb n r) j (Fin.init t) (t (Fin.last j)) γ / C γ ^ 2) γ -
          (C γ : ℝ) * (D.cand (nodeLen (scheduleAt n) + j) (Fin.append (nodePre (scheduleAt n)) (Fin.init t))).W
              (candInv (gamNodeCand h44 hκ hκ4 (x₀ := x₀) hb n r) j (Fin.init t) (t (Fin.last j)) γ / C γ ^ 2) γ :
            Fin _ → ℝ) k = _
      rw [hsc]
      dsimp only
      rw [cons_cast]
      refine Fin.cases ?_ (fun k₀ => ?_) k
      · simp only [Fin.cons_zero, mul_zero]
      · simp only [Fin.cons_succ]
        rw [mul_sub]

end Canon

/-! ### Small dilation identities -/

theorem div_sq_eq_tf_mul {c : ℝ≥0} (hc : 0 < c) (u : ℝ≥0) : u / c ^ 2 = tf (c : ℝ) * u := by
  refine NNReal.eq ?_
  rw [coe_tf_mul (NNReal.coe_pos.2 hc) u]
  push_cast
  rfl

theorem sq_mul_eq_div_tf {c : ℝ≥0} (hc : 0 < c) (z : ℝ≥0∞) :
    ((c ^ 2 : ℝ≥0) : ℝ≥0∞) * z = z / (tf (c : ℝ) : ℝ≥0∞) := by
  have hc2 : c ^ 2 ≠ 0 := pow_ne_zero 2 hc.ne'
  have e : tf (c : ℝ) = (c ^ 2)⁻¹ := by
    refine NNReal.eq ?_
    rw [tf, Real.coe_toNNReal _ (by positivity)]
    push_cast
    rw [inv_pow]
  rw [e, ENNReal.coe_inv hc2, ENNReal.div_eq_inv_mul, inv_inv, mul_comm]

/-! ### The node tree's full-depth arc on `Gam` is the glued restarted arc -/

section Ident

variable (x₀ : ℝ) (h44 : Theorem12ParamCond44Statement.{0}) {κ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
  (hb : IsFig51Bounds κ a b a' b') {Ω : Type} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ)
  (ζ : Ω → ℝ≥0∞)

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
theorem gamNodeAlpha_append (s : Schedule) (j : ℕ) (t : Fin j → ℝ≥0) :
    gamNodeAlpha h44 hκ hκ4 (x₀ := x₀) hb s (nodeLen s + j) (Fin.append (nodePre s) t) =
      qPathF h44 hκ hκ4 (sourceWord (x₀ := x₀) hκ hb) Prod.fst (nodeFlag s) (nodeLen s + j)
        (Fin.append (nodePre s) t) := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · have ht : t = Fin.elim0 := funext fun i => i.elim0
    subst ht
    rw [gamNodeAlpha_of_le h44 hκ hκ4 hb (by omega : nodeLen s + 0 ≤ nodeLen s), append_elim0]
    rfl
  · exact gamNodeAlpha_of_lt h44 hκ hκ4 hb (by omega) _

omit mΩ [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
/-- The staged path of the glued space is the flag candidate path of `qField`. -/
theorem seedLine_candWF (fl : ℕ → Bool) (ℓ : ℕ) (t : Fin ℓ → ℝ≥0) (ω : Ω) :
    seedLine (fun _ => ⊤) (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) ω =
      qPathF h44 hκ hκ4 (sourceWord (x₀ := x₀) hκ hb) (qField x₀ κ h) fl ℓ t ω := by
  have hk : (fun r => killedProc (fun _ : Ω => (⊤ : ℝ≥0∞)) (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) r ω) =
      fun r => candWF x₀ h44 hκ hκ4 hb h fl ℓ t r ω := funext (killedProc_of_eq_top rfl)
  funext u
  simp only [seedLine, hk]
  rfl

variable {x₀ h44 hκ hκ4 hb P h W ζ}

omit [StandardBorelSpace Ω] in
theorem gamNodeData_img_eq {hhm : Measurable h} {n j : ℕ} {t : Fin j → ℝ≥0}
    (hv : IsValid (nodeLen (scheduleAt n) + j) (Fin.append (nodePre (scheduleAt n)) t)) {r : ℝ≥0}
    {p : Ω × HistorySpace 0 0}
    (hpE : p ∈ candEgF x₀ h44 hκ hκ4 hb P h W ζ (nodeFlag (scheduleAt n)) hhm (nodeLen (scheduleAt n) + j)
      (Fin.append (nodePre (scheduleAt n)) t) r)
    (hZ : gZ x₀ (κ := κ) h p ∈ gamNodeGood h44 hκ hκ4 (x₀ := x₀) hb (scheduleAt n)) :
    (gamNodeData h44 hκ hκ4 (x₀ := x₀) hb (scheduleAt n) r).img (nodeLen (scheduleAt n) + j)
        (Fin.append (nodePre (scheduleAt n)) t) (gZ x₀ (κ := κ) h p) =
      gCurve r (fun _ => ⊤) (candWF x₀ h44 hκ hκ4 hb h (nodeFlag (scheduleAt n)) (nodeLen (scheduleAt n) + j)
        (Fin.append (nodePre (scheduleAt n)) t)) (candEgF x₀ h44 hκ hκ4 hb P h W ζ (nodeFlag (scheduleAt n)) hhm
          (nodeLen (scheduleAt n) + j) (Fin.append (nodePre (scheduleAt n)) t) r) p := by
  rw [TreeData.img, tImg_of_mem (show gZ x₀ (κ := κ) h p ∈ (gamNodeData h44 hκ hκ4 (x₀ := x₀) hb (scheduleAt n) r).Gc
    (nodeLen (scheduleAt n) + j) (Fin.append (nodePre (scheduleAt n)) t) from ⟨nodeValid_append hv, hZ⟩),
    gCurve_of_mem hpE, seedLine_candWF]
  funext u
  show ((1 : ℝ) : ℂ) * imgCurve (cfDrv0 r p.2) r (gamNodeAlpha h44 hκ hκ4 (x₀ := x₀) hb (scheduleAt n)
    (nodeLen (scheduleAt n) + j) (Fin.append (nodePre (scheduleAt n)) t) (gZ x₀ (κ := κ) h p)) u = _
  rw [Complex.ofReal_one, one_mul, gamNodeAlpha_append, qPathF_eq_fst hκ hκ4 h44 _ (qField x₀ κ h) _ _ _ p.1 p.2]

omit [StandardBorelSpace Ω] in
theorem gamNodeData_pre_eq {hhm : Measurable h} {n j : ℕ} {t : Fin j → ℝ≥0}
    (hv : IsValid (nodeLen (scheduleAt n) + j) (Fin.append (nodePre (scheduleAt n)) t)) {r : ℝ≥0}
    {p : Ω × HistorySpace 0 0}
    (hpE : p ∈ candEgF x₀ h44 hκ hκ4 hb P h W ζ (nodeFlag (scheduleAt n)) hhm (nodeLen (scheduleAt n) + j)
      (Fin.append (nodePre (scheduleAt n)) t) r)
    (hZ : gZ x₀ (κ := κ) h p ∈ gamNodeGood h44 hκ hκ4 (x₀ := x₀) hb (scheduleAt n)) :
    (gamNodeData h44 hκ hκ4 (x₀ := x₀) hb (scheduleAt n) r).pre (nodeLen (scheduleAt n) + j)
        (Fin.append (nodePre (scheduleAt n)) t) (gZ x₀ (κ := κ) h p) =
      gPre r (fun _ => ⊤) (candWF x₀ h44 hκ hκ4 hb h (nodeFlag (scheduleAt n)) (nodeLen (scheduleAt n) + j)
        (Fin.append (nodePre (scheduleAt n)) t)) (candEgF x₀ h44 hκ hκ4 hb P h W ζ (nodeFlag (scheduleAt n)) hhm
          (nodeLen (scheduleAt n) + j) (Fin.append (nodePre (scheduleAt n)) t) r) p := by
  rw [TreeData.pre, tPre_of_mem (show gZ x₀ (κ := κ) h p ∈ (gamNodeData h44 hκ hκ4 (x₀ := x₀) hb (scheduleAt n) r).Gc
    (nodeLen (scheduleAt n) + j) (Fin.append (nodePre (scheduleAt n)) t) from ⟨nodeValid_append hv, hZ⟩),
    gPre_of_mem hpE, seedLine_candWF]
  show preContact (gamNodeAlpha h44 hκ hκ4 (x₀ := x₀) hb (scheduleAt n) (nodeLen (scheduleAt n) + j)
    (Fin.append (nodePre (scheduleAt n)) t) (gZ x₀ (κ := κ) h p)) (cfHullQ r p.2) = _
  rw [gamNodeAlpha_append, qPathF_eq_fst hκ hκ4 h44 _ (qField x₀ κ h) _ _ _ p.1 p.2]

omit [StandardBorelSpace Ω] in
theorem gamNodeData_alive {hhm : Measurable h} {n j : ℕ} {t : Fin j → ℝ≥0}
    (hv : IsValid (nodeLen (scheduleAt n) + j) (Fin.append (nodePre (scheduleAt n)) t)) {r : ℝ≥0}
    {p : Ω × HistorySpace 0 0} (hpA : p ∈ ndA x₀ h44 hκ hκ4 hb P h W ζ hhm n j t r)
    (hZ : gZ x₀ (κ := κ) h p ∈ gamNodeGood h44 hκ hκ4 (x₀ := x₀) hb (scheduleAt n)) :
    gZ x₀ (κ := κ) h p ∈ (gamNodeData h44 hκ hκ4 (x₀ := x₀) hb (scheduleAt n) r).alive
      (nodeLen (scheduleAt n) + j) (Fin.append (nodePre (scheduleAt n)) t) := by
  refine ⟨⟨nodeValid_append hv, hZ⟩, ?_⟩
  rw [gamNodeData_pre_eq hv hpA.1 hZ, ← lastO_eq hv]
  exact hpA.2

omit [StandardBorelSpace Ω] in
theorem gamNodeData_startCap_eq {hhm : Measurable h} {n j : ℕ} {t : Fin j → ℝ≥0}
    (hv : IsValid (nodeLen (scheduleAt n) + j) (Fin.append (nodePre (scheduleAt n)) t)) {r : ℝ≥0}
    {p : Ω × HistorySpace 0 0} (hpA : p ∈ ndA x₀ h44 hκ hκ4 hb P h W ζ hhm n j t r)
    (hZ : gZ x₀ (κ := κ) h p ∈ gamNodeGood h44 hκ hκ4 (x₀ := x₀) hb (scheduleAt n)) :
    (gamNodeData h44 hκ hκ4 (x₀ := x₀) hb (scheduleAt n) r).startCap (nodeLen (scheduleAt n) + j)
        (Fin.append (nodePre (scheduleAt n)) t) (gZ x₀ (κ := κ) h p) =
      s3Start r (candWF x₀ h44 hκ hκ4 hb h (nodeFlag (scheduleAt n)) (nodeLen (scheduleAt n) + j)
        (Fin.append (nodePre (scheduleAt n)) t)) (candEgF x₀ h44 hκ hκ4 hb P h W ζ (nodeFlag (scheduleAt n)) hhm
          (nodeLen (scheduleAt n) + j) (Fin.append (nodePre (scheduleAt n)) t) r)
        (lastO (nodeLen (scheduleAt n) + j) (Fin.append (nodePre (scheduleAt n)) t) : ℝ) p := by
  classical
  have hal := gamNodeData_alive hv hpA hZ
  have hpA' : p ∈ s3Alive r (candWF x₀ h44 hκ hκ4 hb h (nodeFlag (scheduleAt n)) (nodeLen (scheduleAt n) + j)
      (Fin.append (nodePre (scheduleAt n)) t)) (candEgF x₀ h44 hκ hκ4 hb P h W ζ (nodeFlag (scheduleAt n)) hhm
        (nodeLen (scheduleAt n) + j) (Fin.append (nodePre (scheduleAt n)) t) r)
      (lastO (nodeLen (scheduleAt n) + j) (Fin.append (nodePre (scheduleAt n)) t) : ℝ) := hpA
  simp only [TreeData.startCap, hal, hpA', ↓reduceIte, s3Start]
  rw [gamNodeData_img_eq hv hpA.1 hZ, lastO_eq hv]

end Ident

/-! ### The glued observable from the marks identity -/

section Obs

variable (x₀ : ℝ) (h44 : Theorem12ParamCond44Statement.{0}) {κ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
  (hb : IsFig51Bounds κ a b a' b') {Ω : Type} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ)
  (ζ : Ω → ℝ≥0∞)

/-- **The marks identity of a node candidate** (named statement): almost surely on the alive event and
`gZ⁻¹ gamNodeR`, the tree marks of `gamNodeData` at the full depth `nodeLen + j` (list `nodePre ++ t`) are the initial
marks of the node flags' restarted word in tree order (PROVE-STAGED-REPJ's `GlueMarks` for the node tree, undilated:
`lam = 1`). -/
def NodeGlueMarks (hhm : Measurable h) (n j : ℕ) (t : Fin j → ℝ≥0) (r : ℝ≥0) : Prop :=
  ∀ᵐ p ∂(candMu x₀ (κ := κ) P h W ζ hhm), p ∈ ndA x₀ h44 hκ hκ4 hb P h W ζ hhm n j t r →
    gZ x₀ (κ := κ) h p ∈ gamNodeR h44 hκ hκ4 (x₀ := x₀) hb n r j t →
    (gamNodeData h44 hκ hκ4 (x₀ := x₀) hb (scheduleAt n) r).marks (nodeLen (scheduleAt n) + j)
        (Fin.append (nodePre (scheduleAt n)) t) (gZ x₀ (κ := κ) h p) =
      (fun i => flVL x₀ h44 hκ hκ4 hb P h W ζ (nodeFlag (scheduleAt n)) hhm (nodeLen (scheduleAt n) + j)
          (Fin.append (nodePre (scheduleAt n)) t) r i 0 p,
        fun k => flVR x₀ h44 hκ hκ4 hb P h W ζ (nodeFlag (scheduleAt n)) hhm (nodeLen (scheduleAt n) + j)
          (Fin.append (nodePre (scheduleAt n)) t) r k 0 p)

include hκ4 in
/-- **`Gam`'s node good set holds almost surely on the glued space** (it holds on PIECES' space, clearance form of
Part A, and the pair has the same law on both spaces). -/
theorem ae_gamNodeGood_glue (hA : PartAInputsSixteenDivOfClearance)
    (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) (s : Schedule) :
    ∀ᵐ p ∂(candMu x₀ (κ := κ) P h W ζ hG.1), gZ x₀ (κ := κ) h p ∈ gamNodeGood h44 hκ hκ4 (x₀ := x₀) hb s := by
  have hg := ae_nodeGood_pieceZ x₀ h44 hκ hκ4 hb P (Measure.dirac (0 : ℝ)) h W ζ hA hG hcf s
  have hZ := measurable_pieceZ (Ωa := ℝ) x₀ hG.1 hcf
  have hgamP : ∀ᵐ γ ∂((P.prod (Measure.dirac (0 : ℝ))).map (pieceZ (Ωa := ℝ) x₀ κ h W ζ)),
      γ ∈ gamNodeGood h44 hκ hκ4 (x₀ := x₀) hb s :=
    (ae_map_iff hZ.aemeasurable (measurableSet_gamNodeGood h44 hκ hκ4 hb s)).2 (hg.mono fun _ h' => h'.2)
  rw [map_pieceZ_eq x₀ P (Measure.dirac (0 : ℝ)) h W ζ hG.1 hcf] at hgamP
  exact (ae_map_iff (measurable_gZ x₀ h hG.1).aemeasurable (measurableSet_gamNodeGood h44 hκ hκ4 hb s)).1 hgamP

variable {x₀ h44 hκ hκ4 hb P h W ζ}

omit [StandardBorelSpace Ω] in
/-- **The full-depth tree candidate on `Gam` agrees with the glued restarted word** at a good alive sample with the
marks identity. -/
theorem pieceAt_gamNode_glue {hhm : Measurable h} {n j : ℕ} {t : Fin j → ℝ≥0}
    (hv : IsValid (nodeLen (scheduleAt n) + j) (Fin.append (nodePre (scheduleAt n)) t)) {r : ℝ≥0}
    {p : Ω × HistorySpace 0 0} (hpA : p ∈ ndA x₀ h44 hκ hκ4 hb P h W ζ hhm n j t r)
    (hZ : gZ x₀ (κ := κ) h p ∈ gamNodeGood h44 hκ hκ4 (x₀ := x₀) hb (scheduleAt n))
    (hm : (gamNodeData h44 hκ hκ4 (x₀ := x₀) hb (scheduleAt n) r).marks (nodeLen (scheduleAt n) + j)
        (Fin.append (nodePre (scheduleAt n)) t) (gZ x₀ (κ := κ) h p) =
      (fun i => flVL x₀ h44 hκ hκ4 hb P h W ζ (nodeFlag (scheduleAt n)) hhm (nodeLen (scheduleAt n) + j)
          (Fin.append (nodePre (scheduleAt n)) t) r i 0 p,
        fun k => flVR x₀ h44 hκ hκ4 hb P h W ζ (nodeFlag (scheduleAt n)) hhm (nodeLen (scheduleAt n) + j)
          (Fin.append (nodePre (scheduleAt n)) t) r k 0 p)) :
    (∀ u, ((gamNodeData h44 hκ hκ4 (x₀ := x₀) hb (scheduleAt n) r).cand (nodeLen (scheduleAt n) + j)
        (Fin.append (nodePre (scheduleAt n)) t)).W u (gZ x₀ (κ := κ) h p) =
      flW x₀ h44 hκ hκ4 hb P h W ζ (nodeFlag (scheduleAt n)) hhm (nodeLen (scheduleAt n) + j)
        (Fin.append (nodePre (scheduleAt n)) t) r u p) ∧
    (∀ i u, ((gamNodeData h44 hκ hκ4 (x₀ := x₀) hb (scheduleAt n) r).cand (nodeLen (scheduleAt n) + j)
        (Fin.append (nodePre (scheduleAt n)) t)).VL i u (gZ x₀ (κ := κ) h p) =
      flVL x₀ h44 hκ hκ4 hb P h W ζ (nodeFlag (scheduleAt n)) hhm (nodeLen (scheduleAt n) + j)
        (Fin.append (nodePre (scheduleAt n)) t) r i u p) ∧
    (∀ k u, ((gamNodeData h44 hκ hκ4 (x₀ := x₀) hb (scheduleAt n) r).cand (nodeLen (scheduleAt n) + j)
        (Fin.append (nodePre (scheduleAt n)) t)).VR k u (gZ x₀ (κ := κ) h p) =
      flVR x₀ h44 hκ hκ4 hb P h W ζ (nodeFlag (scheduleAt n)) hhm (nodeLen (scheduleAt n) + j)
        (Fin.append (nodePre (scheduleAt n)) t) r k u p) ∧
    ((gamNodeData h44 hκ hκ4 (x₀ := x₀) hb (scheduleAt n) r).cand (nodeLen (scheduleAt n) + j)
        (Fin.append (nodePre (scheduleAt n)) t)).ζ (gZ x₀ (κ := κ) h p) =
      flζ x₀ h44 hκ hκ4 hb P h W ζ (nodeFlag (scheduleAt n)) hhm (nodeLen (scheduleAt n) + j)
        (Fin.append (nodePre (scheduleAt n)) t) r p := by
  have hEg := candEgF_good x₀ h44 hκ hκ4 hb P h W ζ (nodeFlag (scheduleAt n)) hhm (nodeLen (scheduleAt n) + j)
    (Fin.append (nodePre (scheduleAt n)) t) r
  have hτs := candTsF_bounds (fl := nodeFlag (scheduleAt n)) hv
  have hL : (fun i => flVL x₀ h44 hκ hκ4 hb P h W ζ (nodeFlag (scheduleAt n)) hhm (nodeLen (scheduleAt n) + j)
      (Fin.append (nodePre (scheduleAt n)) t) r i 0 p) =
      fun i => s3XL (flowLineXL (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps 0)
        (candTsF (nodeFlag (scheduleAt n)) (nodeLen (scheduleAt n) + j) (Fin.append (nodePre (scheduleAt n)) t))
        (nodeLen (scheduleAt n) + j) r
        (candWF x₀ h44 hκ hκ4 hb h (nodeFlag (scheduleAt n)) (nodeLen (scheduleAt n) + j)
          (Fin.append (nodePre (scheduleAt n)) t))
        (candEgF x₀ h44 hκ hκ4 hb P h W ζ (nodeFlag (scheduleAt n)) hhm (nodeLen (scheduleAt n) + j)
          (Fin.append (nodePre (scheduleAt n)) t) r)
        (lastO (nodeLen (scheduleAt n) + j) (Fin.append (nodePre (scheduleAt n)) t) : ℝ) p
        (treeIdx (nodeLen (scheduleAt n) + j) _ i) := funext fun i => s6VL_zero hEg hτs p i
  have hR : (fun k => flVR x₀ h44 hκ hκ4 hb P h W ζ (nodeFlag (scheduleAt n)) hhm (nodeLen (scheduleAt n) + j)
      (Fin.append (nodePre (scheduleAt n)) t) r k 0 p) =
      fun k => s3XR (flowLineXR (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps 0)
        (candTsF (nodeFlag (scheduleAt n)) (nodeLen (scheduleAt n) + j) (Fin.append (nodePre (scheduleAt n)) t))
        (nodeLen (scheduleAt n) + j) r
        (candWF x₀ h44 hκ hκ4 hb h (nodeFlag (scheduleAt n)) (nodeLen (scheduleAt n) + j)
          (Fin.append (nodePre (scheduleAt n)) t))
        (candEgF x₀ h44 hκ hκ4 hb P h W ζ (nodeFlag (scheduleAt n)) hhm (nodeLen (scheduleAt n) + j)
          (Fin.append (nodePre (scheduleAt n)) t) r)
        (lastO (nodeLen (scheduleAt n) + j) (Fin.append (nodePre (scheduleAt n)) t) : ℝ) p
        (treeIdx (nodeLen (scheduleAt n) + j) _ k) := funext fun k => s6VR_zero hEg hτs p k
  have hp := pieceAt_arcPiece (B := fun _ _ => (0 : ℝ)) (B' := fun _ _ => (0 : ℝ)) (A' := univ)
    (xL := fun γ' => ((gamNodeData h44 hκ hκ4 (x₀ := x₀) hb (scheduleAt n) r).marks (nodeLen (scheduleAt n) + j)
      (Fin.append (nodePre (scheduleAt n)) t) γ').1)
    (xR := fun γ' => ((gamNodeData h44 hκ hκ4 (x₀ := x₀) hb (scheduleAt n) r).marks (nodeLen (scheduleAt n) + j)
      (Fin.append (nodePre (scheduleAt n)) t) γ').2)
    (xL' := fun p i => s3XL (flowLineXL (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps 0)
        (candTsF (nodeFlag (scheduleAt n)) (nodeLen (scheduleAt n) + j) (Fin.append (nodePre (scheduleAt n)) t))
        (nodeLen (scheduleAt n) + j) r
        (candWF x₀ h44 hκ hκ4 hb h (nodeFlag (scheduleAt n)) (nodeLen (scheduleAt n) + j)
          (Fin.append (nodePre (scheduleAt n)) t))
        (candEgF x₀ h44 hκ hκ4 hb P h W ζ (nodeFlag (scheduleAt n)) hhm (nodeLen (scheduleAt n) + j)
          (Fin.append (nodePre (scheduleAt n)) t) r)
        (lastO (nodeLen (scheduleAt n) + j) (Fin.append (nodePre (scheduleAt n)) t) : ℝ) p
        (treeIdx (nodeLen (scheduleAt n) + j) _ i))
    (xR' := fun p k => s3XR (flowLineXR (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps 0)
        (candTsF (nodeFlag (scheduleAt n)) (nodeLen (scheduleAt n) + j) (Fin.append (nodePre (scheduleAt n)) t))
        (nodeLen (scheduleAt n) + j) r
        (candWF x₀ h44 hκ hκ4 hb h (nodeFlag (scheduleAt n)) (nodeLen (scheduleAt n) + j)
          (Fin.append (nodePre (scheduleAt n)) t))
        (candEgF x₀ h44 hκ hκ4 hb P h W ζ (nodeFlag (scheduleAt n)) hhm (nodeLen (scheduleAt n) + j)
          (Fin.append (nodePre (scheduleAt n)) t) r)
        (lastO (nodeLen (scheduleAt n) + j) (Fin.append (nodePre (scheduleAt n)) t) : ℝ) p
        (treeIdx (nodeLen (scheduleAt n) + j) _ k))
    (gamNodeData_img_eq hv hpA.1 hZ) (gamNodeData_pre_eq hv hpA.1 hZ) (gamNodeData_startCap_eq hv hpA hZ)
    (iff_of_true (gamNodeData_alive hv hpA hZ) (mem_univ p))
    (by rw [hm]; exact hL) (by rw [hm]; exact hR)
  exact ⟨hp.W, hp.VL, hp.VR, hp.ζ⟩

include hκ4 in
omit [StandardBorelSpace Ω] in
/-- **`NodeGlueObs` from the node marks identity** (and the node good set of `Gam` almost surely on the glued
space). -/
theorem nodeGlueObs_of_marks {hhm : Measurable h} {n j : ℕ} {t : Fin j → ℝ≥0}
    (hv : IsValid (nodeLen (scheduleAt n) + j) (Fin.append (nodePre (scheduleAt n)) t)) {r : ℝ≥0}
    (hgam : ∀ᵐ p ∂(candMu x₀ (κ := κ) P h W ζ hhm),
      gZ x₀ (κ := κ) h p ∈ gamNodeGood h44 hκ hκ4 (x₀ := x₀) hb (scheduleAt n))
    (hm : NodeGlueMarks x₀ h44 hκ hκ4 hb P h W ζ hhm n j t r) :
    NodeGlueObs x₀ h44 hκ hκ4 hb P h W ζ hhm n j t r := by
  filter_upwards [hm, hgam] with p hmk hZ hpA hR
  have hmarks := hmk hpA hR
  obtain ⟨hcL, hcR⟩ := canonY_gamNodeCand_marks h44 hκ hκ4 hb n r j t (gZ x₀ (κ := κ) h p)
  obtain ⟨hW, hVL, hVR, hζ⟩ := pieceAt_gamNode_glue hv hpA hZ hmarks
  set γ := gZ x₀ (κ := κ) h p with hγ
  set c := gamNodeScale h44 hκ hκ4 (x₀ := x₀) hb n r γ with hc
  have hc0 : 0 < c := gamNodeScale_pos h44 hκ hκ4 hb n r γ
  have hsq : (√(tf (c : ℝ) : ℝ))⁻¹ = c := sqrt_tf_inv (NNReal.coe_pos.2 hc0)
  refine ⟨Prod.ext (funext fun i => ?_) (funext fun k => ?_), ?_⟩
  · rw [hcL i, hmarks]
    show (c : ℝ) * _ = (√(tf (c : ℝ) : ℝ))⁻¹ * _
    rw [hsq]
  · rw [hcR k, hmarks]
    show (c : ℝ) * _ = (√(tf (c : ℝ) : ℝ))⁻¹ * _
    rw [hsq]
  · have e1 : ∀ u : ℝ≥0, u / c ^ 2 = tf (c : ℝ) * u := div_sq_eq_tf_mul hc0
    simp only [pieceSamp, gamNodeCand, scaleFam, scalePiece, subFam, reindexPiece, ← hc, e1, hW, hVL, hVR, hζ,
      hsq, sq_mul_eq_div_tf hc0]

end Obs

/-! ### Wiring -/

/-- **The marks identities of the node candidates** (named statement, `NodeGlueMarks` everywhere). -/
def NodeGlueMarksStatement (h44 : Theorem12ParamCond44Statement.{0}) : Prop :=
  ∀ {κ x₀ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsFig51Bounds κ a b a' b')
    {Ω : Type} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞)
    (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀}),
    IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ →
    ∀ (n : ℕ) {q : ℚ}, 0 < q → ∀ {j : ℕ} {t : Fin j → ℝ≥0},
      IsValid (nodeLen (scheduleAt n) + j) (Fin.append (nodePre (scheduleAt n)) t) →
      NodeGlueMarks x₀ h44 hκ hκ4 hb P h W ζ hG.1 n j t (q : ℝ).toNNReal

/-- **`NodeGlueObsStatement` from the marks identities** (clearance form of Part A for `Gam`'s good set). -/
theorem nodeGlueObsStatement_of_marks (h44 : Theorem12ParamCond44Statement.{0})
    (hA : PartAInputsSixteenDivOfClearance) (hm : NodeGlueMarksStatement h44) : NodeGlueObsStatement h44 := by
  intro κ x₀ a b a' b' hκ hκ4 hb Ω _ _ P _ h W ζ hG hcf n q hq j t hv
  exact nodeGlueObs_of_marks hv (ae_gamNodeGood_glue x₀ h44 hκ hκ4 hb P h W ζ hA hG hcf _)
    (hm hκ hκ4 hb P h W ζ hG hcf n hq hv)

/-- **PROVE-STAGED-NODECOMP's `NodeTransferStatement` from the glued pasts and the marks identities.** -/
theorem nodeTransferStatement_of_pastMarks (h44 : Theorem12ParamCond44Statement.{0})
    (hA : PartAInputsSixteenDivOfClearance) (hpast : NodeGluePastStatement h44) (hm : NodeGlueMarksStatement h44) :
    StagedNComp.NodeTransferStatement h44 :=
  nodeTransferStatement_of_glue h44 hA hpast (nodeGlueObsStatement_of_marks h44 hA hm)

/-- **`hNodeLaw` for `nodeObjects`** from the glued pasts, the marks identities and Part A's clearance form. -/
theorem nodeLawOn_nodeObjects_of_pastMarks (h44 : Theorem12ParamCond44Statement.{0})
    (hA : PartAInputsSixteenDivOfClearance) (hpast : NodeGluePastStatement h44) (hm : NodeGlueMarksStatement h44) :
    Wire.Night.NodeLawOn h44 (nodeObjects h44) :=
  nodeLawOn_nodeObjects_of_glue h44 hA hpast (nodeGlueObsStatement_of_marks h44 hA hm)

end InteractingSLE.Sec5.CrossCond.StagedNTr
