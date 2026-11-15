/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.StagedRepJFinal
import InteractingSLE.Spec.Sec5.StagedRepJObs

/-!
# Prop 5.9's later root stages: the closed form of the tree marks (towards `GlueMarks`)

Packet PROVE-STAGED-REPJ. The tree marks of PIECES' construction are defined recursively (the parent's marks at the
switch, relative to the driver, with one new mark on each side at the driver), while the glued restarted word starts
from the closed form `imgStageVL` of PROVE-STAGED-S3 (born marks `chartAL` of the shifted driver, flowed root marks) in
tree order. This file collects the deterministic steps:

* **`imgStageVL_succ_treeIdx`**, `imgStageVR_succ_treeIdx`: in tree order the depth-`(k+1)` closed form is the newest
  born mark followed by the depth-`k` closed form;
* `imgBornL_self`, `imgBornR_self`: a mark born at the current capacity sits at the driver.

R48: nothing here uses Theorem 1.2/1.3 or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.CrossCond.StagedRepJ

open StagedFinal StagedS6 StagedS3 MartChar.RealFlow
open Prop59NodeTree (shiftDrv)
open StagedRepLater (scD rightImg_scale)
open WangWu (chartAL chartAR)

section Index

variable {nL nR : ℕ}

/-- **The closed-form marks in tree order at depth `k + 1`**: the newest born mark, then the depth-`k` marks. -/
theorem imgStageVL_succ_treeIdx (xL : Fin nL → ℝ) (ω : ℝ → ℝ) (s : ℝ) (w : ℝ → ℝ) (T : ℝ) (A : ℕ → ℝ) (k : ℕ)
    (i : Fin ((nL + 1) + (k + 1))) :
    imgStageVL xL ω s w T A (k + 1) (treeIdx (k + 1) (nL + 1) i) =
      (Fin.cons (imgBornL w T A (k + 1)) fun i' => imgStageVL xL ω s w T A k (treeIdx k (nL + 1) i') :
        Fin ((nL + 1) + k + 1) → ℝ) i := by
  refine Fin.cases ?_ (fun i' => ?_) i
  · simp only [imgStageVL, Fin.cons_zero]
    rw [append_treeIdx_of_lt _ _ (by simp)]
    congr 2
  · simp only [imgStageVL, Fin.cons_succ]
    by_cases hi : (i' : ℕ) < k
    · rw [append_treeIdx_of_lt _ _ (by simp; omega), append_treeIdx_of_lt _ _ hi]
      congr 2
      simp only [Fin.val_succ]
      omega
    · rw [append_treeIdx_of_ge _ _ (by simp; omega), append_treeIdx_of_ge _ _ (not_lt.1 hi)]
      congr 2
      simp only [Fin.val_succ]
      omega

/-- The right counterpart of `imgStageVL_succ_treeIdx`. -/
theorem imgStageVR_succ_treeIdx (xR : Fin nR → ℝ) (ω : ℝ → ℝ) (s : ℝ) (w : ℝ → ℝ) (T : ℝ) (A : ℕ → ℝ) (k : ℕ)
    (i : Fin ((nR + 1) + (k + 1))) :
    imgStageVR xR ω s w T A (k + 1) (treeIdx (k + 1) (nR + 1) i) =
      (Fin.cons (imgBornR w T A (k + 1)) fun i' => imgStageVR xR ω s w T A k (treeIdx k (nR + 1) i') :
        Fin ((nR + 1) + k + 1) → ℝ) i := by
  refine Fin.cases ?_ (fun i' => ?_) i
  · simp only [imgStageVR, Fin.cons_zero]
    rw [append_treeIdx_of_lt _ _ (by simp)]
    congr 2
  · simp only [imgStageVR, Fin.cons_succ]
    by_cases hi : (i' : ℕ) < k
    · rw [append_treeIdx_of_lt _ _ (by simp; omega), append_treeIdx_of_lt _ _ hi]
      congr 2
      simp only [Fin.val_succ]
      omega
    · rw [append_treeIdx_of_ge _ _ (by simp; omega), append_treeIdx_of_ge _ _ (not_lt.1 hi)]
      congr 2
      simp only [Fin.val_succ]
      omega

/-- A left mark born at the current capacity sits at the driver. -/
theorem imgBornL_self {w : ℝ → ℝ} (hw : Continuous w) (A : ℕ → ℝ) (m : ℕ) : imgBornL w (A m) A m = 0 := by
  simp only [imgBornL, sub_self]
  exact chartAL_zero (QuantumZipper.RS.continuous_shiftDrive hw _) (QuantumZipper.RS.shiftDrive_zero w _)

/-- A right mark born at the current capacity sits at the driver. -/
theorem imgBornR_self {w : ℝ → ℝ} (hw : Continuous w) (A : ℕ → ℝ) (m : ℕ) : imgBornR w (A m) A m = 0 := by
  simp only [imgBornR, sub_self]
  exact chartAR_zero (QuantumZipper.RS.continuous_shiftDrive hw _) (QuantumZipper.RS.shiftDrive_zero w _)

end Index

/-! ### The closed form with arbitrary root marks -/

section CF

variable {n : ℕ} {w : ℝ → ℝ}

/-- The flowed left root marks relative to the driver. -/
def cfRootL (x0 : Fin n → ℝ) (w : ℝ → ℝ) (T : ℝ) : Fin n → ℝ := fun i => -rightImg (fun r => -w r) (-x0 i) T - w T

/-- The flowed right root marks relative to the driver. -/
def cfRootR (x0 : Fin n → ℝ) (w : ℝ → ℝ) (T : ℝ) : Fin n → ℝ := fun i => rightImg w (x0 i) T - w T

/-- **The left closed-form marks** at capacity `T` after `k` switches (born at `A 1, …, A k`), with root marks `x0`:
the born marks `chartAL` of the shifted driver, then the flowed root marks relative to the driver. -/
def cfStageL (x0 : Fin n → ℝ) (w : ℝ → ℝ) (T : ℝ) (A : ℕ → ℝ) (k : ℕ) : Fin (k + n) → ℝ :=
  Fin.append (fun j : Fin k => imgBornL w T A (j + 1)) (cfRootL x0 w T)

/-- The right closed-form marks. -/
def cfStageR (x0 : Fin n → ℝ) (w : ℝ → ℝ) (T : ℝ) (A : ℕ → ℝ) (k : ℕ) : Fin (k + n) → ℝ :=
  Fin.append (fun j : Fin k => imgBornR w T A (j + 1)) (cfRootR x0 w T)

theorem imgStageVL_eq_cfStageL {nL : ℕ} (xL : Fin nL → ℝ) (ω : ℝ → ℝ) (s : ℝ) (w : ℝ → ℝ) (T : ℝ) (A : ℕ → ℝ)
    (k : ℕ) : imgStageVL xL ω s w T A k = cfStageL (GlueImg.imgMarkL xL ω s) w T A k := rfl

theorem imgStageVR_eq_cfStageR {nR : ℕ} (xR : Fin nR → ℝ) (ω : ℝ → ℝ) (s : ℝ) (w : ℝ → ℝ) (T : ℝ) (A : ℕ → ℝ)
    (k : ℕ) : imgStageVR xR ω s w T A k = cfStageR (GlueImg.imgMarkR xR ω s) w T A k := rfl

/-- The left closed form restarted at `S` (all births before `S`). -/
theorem cfStageL_shift (hw : Continuous w) (x0 : Fin n → ℝ) {S r : ℝ} {A : ℕ → ℝ} {k : ℕ}
    (hA : ∀ j : Fin k, A (j + 1) ≤ S) (hS : 0 ≤ S) (hr : 0 ≤ r) (i : Fin (k + n)) :
    -rightImg (shiftDrv (fun s => -w s) S) (-cfStageL x0 w S A k i) r - shiftDrv w S r =
      cfStageL x0 w (S + r) A k i := by
  refine Fin.addCases (fun j => ?_) (fun i' => ?_) i
  · simp only [cfStageL, Fin.append_left, imgBornL]
    exact chartAL_shift hw (hA j) hr
  · simp only [cfStageL, Fin.append_right, cfRootL]
    rw [← relL_shift hw hS hr (-x0 i')]

/-- The right closed form restarted at `S`. -/
theorem cfStageR_shift (hw : Continuous w) (x0 : Fin n → ℝ) {S r : ℝ} {A : ℕ → ℝ} {k : ℕ}
    (hA : ∀ j : Fin k, A (j + 1) ≤ S) (hS : 0 ≤ S) (hr : 0 ≤ r) (i : Fin (k + n)) :
    rightImg (shiftDrv w S) (cfStageR x0 w S A k i) r - shiftDrv w S r = cfStageR x0 w (S + r) A k i := by
  refine Fin.addCases (fun j => ?_) (fun i' => ?_) i
  · simp only [cfStageR, Fin.append_left, imgBornR]
    exact chartAR_shift hw (hA j) hr
  · simp only [cfStageR, Fin.append_right, cfRootR]
    exact relR_shift hw hS hr _

/-- **In tree order the depth-`(k+1)` closed form is the newest born mark followed by the depth-`k` one.** -/
theorem cfStageL_succ_treeIdx (x0 : Fin n → ℝ) (w : ℝ → ℝ) (T : ℝ) (A : ℕ → ℝ) (k : ℕ) (i : Fin (n + (k + 1))) :
    cfStageL x0 w T A (k + 1) (treeIdx (k + 1) n i) =
      (Fin.cons (imgBornL w T A (k + 1)) fun i' => cfStageL x0 w T A k (treeIdx k n i') : Fin (n + k + 1) → ℝ) i := by
  refine Fin.cases ?_ (fun i' => ?_) i
  · simp only [cfStageL, Fin.cons_zero]
    rw [append_treeIdx_of_lt _ _ (by simp)]
    congr 2
  · simp only [cfStageL, Fin.cons_succ]
    by_cases hi : (i' : ℕ) < k
    · rw [append_treeIdx_of_lt _ _ (by simp; omega), append_treeIdx_of_lt _ _ hi]
      congr 2
      simp only [Fin.val_succ]
      omega
    · rw [append_treeIdx_of_ge _ _ (by simp; omega), append_treeIdx_of_ge _ _ (not_lt.1 hi)]
      congr 2
      simp only [Fin.val_succ]
      omega

theorem cfStageR_succ_treeIdx (x0 : Fin n → ℝ) (w : ℝ → ℝ) (T : ℝ) (A : ℕ → ℝ) (k : ℕ) (i : Fin (n + (k + 1))) :
    cfStageR x0 w T A (k + 1) (treeIdx (k + 1) n i) =
      (Fin.cons (imgBornR w T A (k + 1)) fun i' => cfStageR x0 w T A k (treeIdx k n i') : Fin (n + k + 1) → ℝ) i := by
  refine Fin.cases ?_ (fun i' => ?_) i
  · simp only [cfStageR, Fin.cons_zero]
    rw [append_treeIdx_of_lt _ _ (by simp)]
    congr 2
  · simp only [cfStageR, Fin.cons_succ]
    by_cases hi : (i' : ℕ) < k
    · rw [append_treeIdx_of_lt _ _ (by simp; omega), append_treeIdx_of_lt _ _ hi]
      congr 2
      simp only [Fin.val_succ]
      omega
    · rw [append_treeIdx_of_ge _ _ (by simp; omega), append_treeIdx_of_ge _ _ (not_lt.1 hi)]
      congr 2
      simp only [Fin.val_succ]
      omega

/-- At depth `0` and capacity `0` the closed form is the root marks. -/
theorem cfStageL_zero (hw : Continuous w) (hw0 : w 0 = 0) {x0 : Fin n → ℝ} (hx0 : ∀ i, x0 i ≤ 0) (A : ℕ → ℝ)
    (i : Fin (n + 0)) : cfStageL x0 w 0 A 0 (treeIdx 0 n i) = x0 i := by
  rw [cfStageL, append_treeIdx_of_ge _ _ (Nat.zero_le _), cfRootL]
  show -rightImg (fun r => -w r) (-x0 _) 0 - w 0 = x0 i
  rw [rightImg_zero (w := fun r => -w r) hw.neg (by simp [hw0]) (neg_nonneg.2 (hx0 _)), hw0]
  simp only [neg_neg, sub_zero]
  rfl

theorem cfStageR_zero (hw : Continuous w) (hw0 : w 0 = 0) {x0 : Fin n → ℝ} (hx0 : ∀ i, 0 ≤ x0 i) (A : ℕ → ℝ)
    (i : Fin (n + 0)) : cfStageR x0 w 0 A 0 (treeIdx 0 n i) = x0 i := by
  rw [cfStageR, append_treeIdx_of_ge _ _ (Nat.zero_le _), cfRootR]
  show rightImg w (x0 _) 0 - w 0 = x0 i
  rw [rightImg_zero hw hw0 (hx0 _), hw0, sub_zero]
  rfl

end CF

/-! ### Dilation of the closed form -/

section Dil

variable {n : ℕ} {w : ℝ → ℝ} {c : ℝ}

theorem shiftDrive_scD (w : ℝ → ℝ) (hc : 0 < c) (a : ℝ) :
    QuantumZipper.RS.shiftDrive (scD c w) (c ^ 2 * a) = scD c (QuantumZipper.RS.shiftDrive w a) := by
  funext r
  have hc2 : c ^ 2 ≠ 0 := (pow_pos hc 2).ne'
  simp only [QuantumZipper.RS.shiftDrive, scD]
  rw [show (c ^ 2 * a + r) / c ^ 2 = a + r / c ^ 2 by field_simp, show c ^ 2 * a / c ^ 2 = a by field_simp]
  ring

theorem neg_scD (w : ℝ → ℝ) (c : ℝ) : (fun s => -scD c w s) = scD c fun s => -w s := by
  funext s; simp only [scD]; ring

theorem chartAL_scD (hw : Continuous w) (hc : 0 < c) {t : ℝ} (ht : 0 ≤ t) :
    chartAL (scD c w) (c ^ 2 * t) = c * chartAL w t := by
  simp only [chartAL]
  rw [neg_scD, show (0 : ℝ) = c * 0 by ring, rightImg_scale (w := fun s => -w s) hw.neg hc 0 ht]
  simp only [scD, mul_div_cancel_left₀ t (pow_pos hc 2).ne', mul_zero]
  ring

theorem chartAR_scD (hw : Continuous w) (hc : 0 < c) {t : ℝ} (ht : 0 ≤ t) :
    chartAR (scD c w) (c ^ 2 * t) = c * chartAR w t := by
  simp only [chartAR]
  rw [show (0 : ℝ) = c * 0 by ring, rightImg_scale hw hc 0 ht]
  simp only [scD, mul_div_cancel_left₀ t (pow_pos hc 2).ne', mul_zero]
  ring

/-- **The closed form of a dilated driver** (marks `c x`, capacities `c² A`, at `c² T`) is `c` times the closed form. -/
theorem cfStageL_smul (hw : Continuous w) (hc : 0 < c) (x0 : Fin n → ℝ) {T : ℝ} {A : ℕ → ℝ} {k : ℕ}
    (hA : ∀ j : Fin k, A (j + 1) ≤ T) (hT : 0 ≤ T) (i : Fin (k + n)) :
    cfStageL (fun i => c * x0 i) (scD c w) (c ^ 2 * T) (fun m => c ^ 2 * A m) k i = c * cfStageL x0 w T A k i := by
  refine Fin.addCases (fun j => ?_) (fun i' => ?_) i
  · simp only [cfStageL, Fin.append_left, imgBornL]
    rw [← mul_sub, shiftDrive_scD w hc, chartAL_scD (QuantumZipper.RS.continuous_shiftDrive hw _) hc
      (sub_nonneg.2 (hA j))]
  · simp only [cfStageL, Fin.append_right, cfRootL]
    rw [neg_scD, show -(c * x0 i') = c * -x0 i' by ring, rightImg_scale (w := fun s => -w s) hw.neg hc _ hT]
    simp only [scD, mul_div_cancel_left₀ T (pow_pos hc 2).ne']
    ring

theorem cfStageR_smul (hw : Continuous w) (hc : 0 < c) (x0 : Fin n → ℝ) {T : ℝ} {A : ℕ → ℝ} {k : ℕ}
    (hA : ∀ j : Fin k, A (j + 1) ≤ T) (hT : 0 ≤ T) (i : Fin (k + n)) :
    cfStageR (fun i => c * x0 i) (scD c w) (c ^ 2 * T) (fun m => c ^ 2 * A m) k i = c * cfStageR x0 w T A k i := by
  refine Fin.addCases (fun j => ?_) (fun i' => ?_) i
  · simp only [cfStageR, Fin.append_left, imgBornR]
    rw [← mul_sub, shiftDrive_scD w hc, chartAR_scD (QuantumZipper.RS.continuous_shiftDrive hw _) hc
      (sub_nonneg.2 (hA j))]
  · simp only [cfStageR, Fin.append_right, cfRootR]
    rw [rightImg_scale hw hc _ hT]
    simp only [scD, mul_div_cancel_left₀ T (pow_pos hc 2).ne']
    ring

end Dil

/-! ### The tree marks are the closed form -/

section Tree

open Prop59Pieces Prop59System WangWu WangWu.ImgWord StagedNode
open Sec7.Lemma71C (capClock)

/-- The switch own times of a list (`tau t (m+1) = decode (t m)`, `0` elsewhere). -/
def tau {k : ℕ} (t : Fin k → ℝ≥0) (m : ℕ) : ℝ := if h : 0 < m ∧ m ≤ k then decode (t ⟨m - 1, by omega⟩) else 0

theorem tau_self {k : ℕ} (t : Fin k → ℝ≥0) : tau t k = qLast k t := by
  cases k with
  | zero => simp [tau, qLast]
  | succ k =>
    simp only [tau, Nat.succ_pos, le_refl, and_self, ↓reduceDIte, qLast]
    rfl

theorem tau_init {k : ℕ} (t : Fin (k + 1) → ℝ≥0) {m : ℕ} (hm : m ≤ k) : tau (Fin.init t) m = tau t m := by
  unfold tau
  by_cases h0 : 0 < m
  · simp only [h0, hm, and_self, ↓reduceDIte, show m ≤ k + 1 by omega]
    rfl
  · simp only [h0, false_and, ↓reduceDIte]

theorem cfStageL_congr_A {n : ℕ} (x0 : Fin n → ℝ) (w : ℝ → ℝ) (T : ℝ) {A A' : ℕ → ℝ} {k : ℕ}
    (h : ∀ j : Fin k, A (j + 1) = A' (j + 1)) : cfStageL x0 w T A k = cfStageL x0 w T A' k := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun i' => ?_) i
  · simp only [cfStageL, Fin.append_left, imgBornL, h j]
  · simp only [cfStageL, Fin.append_right]

theorem cfStageR_congr_A {n : ℕ} (x0 : Fin n → ℝ) (w : ℝ → ℝ) (T : ℝ) {A A' : ℕ → ℝ} {k : ℕ}
    (h : ∀ j : Fin k, A (j + 1) = A' (j + 1)) : cfStageR x0 w T A k = cfStageR x0 w T A' k := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun i' => ?_) i
  · simp only [cfStageR, Fin.append_left, imgBornR, h j]
  · simp only [cfStageR, Fin.append_right]

variable {Ω : Type*} [MeasurableSpace Ω] {nL₀ nR₀ : ℕ} {D : TreeData Ω nL₀ nR₀}

omit [MeasurableSpace Ω] in
/-- The switch own times of an admissible list are nonnegative and at most its last switch. -/
theorem tau_le_qLast (hT : D.IsTree) :
    ∀ (k : ℕ) (t : Fin k → ℝ≥0), D.valid k t → ∀ m ≤ k, 0 ≤ tau t m ∧ tau t m ≤ qLast k t
  | 0, t, _, m, hm => by
    have : m = 0 := by omega
    subst this
    simp [tau, qLast]
  | k + 1, t, hv, m, hm => by
    obtain ⟨hv', hle, -⟩ := hT.init k t hv
    rcases Nat.lt_or_ge m (k + 1) with hlt | hge
    · have h := tau_le_qLast hT k (Fin.init t) hv' m (by omega)
      rw [tau_init t (by omega)] at h
      exact ⟨h.1, h.2.trans hle⟩
    · have : m = k + 1 := by omega
      subst this
      rw [tau_self]
      exact ⟨hT.qnonneg _ _ hv, le_rfl⟩

/-- **The tree marks are the closed form** of the tree candidate's own chain driver: for an alive list `t` of depth
`k`, and a continuous driver `w` equal to the chain driver of the image curve up to the start capacity, the marks are
the born marks at the switch capacities and the flowed root marks, in tree order. -/
theorem TreeData.marks_eq_cfStage (hD : D.IsReg) (hT : D.IsTree)
    (hpos : ∀ k (t : Fin (k + 1) → ℝ≥0), D.valid (k + 1) t → 0 < qLast (k + 1) t) (ω : Ω)
    (hx0L : ∀ i, D.xL0 ω i ≤ 0) (hx0R : ∀ i, 0 ≤ D.xR0 ω i) :
    ∀ (k : ℕ) (t : Fin k → ℝ≥0), ω ∈ D.alive k t → ∀ (w : ℝ → ℝ), Continuous w →
      EqOn (kPath (D.img k t ω) (D.pre k t ω)) w (Icc 0 (capClock (D.img k t ω) (qLast k t))) →
      D.marks k t ω =
        (fun i => cfStageL (D.xL0 ω) w (capClock (D.img k t ω) (qLast k t))
          (fun m => capClock (D.img k t ω) (tau t m)) k (treeIdx k nL₀ i),
        fun i => cfStageR (D.xR0 ω) w (capClock (D.img k t ω) (qLast k t))
          (fun m => capClock (D.img k t ω) (tau t m)) k (treeIdx k nR₀ i))
  | 0, t, _, w, hw, hEq => by
    have hγ := (hD.isKilledFamily 0 t).arc ω
    have hc0 : capClock (D.img 0 t ω) (qLast 0 t) = 0 := by simp only [qLast, hγ.capClock_zero]
    have hw0 : w 0 = 0 := by
      have h1 := hEq ⟨le_rfl, by rw [hc0]⟩
      rw [← h1]
      simp only [kPath, Real.toNNReal_zero, hγ.kW_zero]
    rw [hc0]
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
    · exact (cfStageL_zero hw hw0 hx0L (fun m => capClock (D.img 0 t ω) (tau t m)) i).symm
    · exact (cfStageR_zero hw hw0 hx0R (fun m => capClock (D.img 0 t ω) (tau t m)) i).symm
  | k + 1, t, hA, w, hw, hEq => by
    have hγ := (hD.isKilledFamily (k + 1) t).arc ω
    have hγ' := (hD.isKilledFamily k (Fin.init t)).arc ω
    have hA' := hT.alive_init hA hγ'
    have hv : D.valid (k + 1) t := hA.1.1
    have hG : ω ∈ D.G := hA.1.2
    obtain ⟨hv', hle, -⟩ := hT.init k t hv
    have hq : qLast (k + 1) t ∈ D.pre (k + 1) t ω := hA.2
    have hS' : qLast (k + 1) t ∈ D.pre k (Fin.init t) ω := (hT.mem_pre_iff hv hG le_rfl).1 hq
    have hagree : EqOn (D.img (k + 1) t ω) (D.img k (Fin.init t) ω) (Icc 0 (qLast (k + 1) t)) := hT.img_eqOn hv hG
    have hS0 := hpos k t hv
    -- the parent's chain driver agrees with `w` up to the switch capacity
    have hkW : EqOn (kPath (D.img k (Fin.init t) ω) (D.pre k (Fin.init t) ω)) w
        (Icc 0 (capClock (D.img (k + 1) t ω) (qLast (k + 1) t))) := by
      intro r hr
      have e := WangWu.kW_eq_of_eqOn hγ hγ' hq hS' hS0 hagree (r := r.toNNReal)
        (by rw [Real.coe_toNNReal _ hr.1]; exact hr.2)
      simp only [kPath]
      rw [← e]
      exact hEq hr
    have htau := tau_le_qLast hT (k + 1) t hv
    have hcapEq : ∀ m ≤ k + 1, capClock (D.img k (Fin.init t) ω) (tau t m) = capClock (D.img (k + 1) t ω) (tau t m) :=
      fun m hm => (Prop59Pieces.capClock_congr (hagree.mono (Icc_subset_Icc le_rfl (htau m hm).2))).symm
    -- the parent's start capacity and the switch
    have hSk : ((D.startCap k (Fin.init t) ω : ℝ≥0) : ℝ) = capClock (D.img (k + 1) t ω) (tau t k) := by
      rw [Prop59NodeTree.TreeData.startCap_coe hD hA', ← tau_self (Fin.init t), tau_init t le_rfl,
        hcapEq k (Nat.le_succ k)]
    have hsum := Prop59NodeTree.TreeData.startCap_succ hD hT hA hA'
    set sw := clkInv (D.clkStage k (Fin.init t)) (t (Fin.last k)) ω with hsw
    have hSk1 : ((D.startCap k (Fin.init t) ω + sw : ℝ≥0) : ℝ) = capClock (D.img (k + 1) t ω) (qLast (k + 1) t) := by
      rw [hsum, Prop59NodeTree.TreeData.startCap_coe hD hA]
    have hmono : capClock (D.img k (Fin.init t) ω) (qLast k (Fin.init t)) ≤
        capClock (D.img (k + 1) t ω) (qLast (k + 1) t) := by
      rw [Prop59Pieces.capClock_congr hagree]
      exact hγ'.strictMonoOn_capClock.monotoneOn hA'.2 hS' hle
    have ih := TreeData.marks_eq_cfStage hD hT hpos ω hx0L hx0R k (Fin.init t) hA' w hw
      (hkW.mono (Icc_subset_Icc le_rfl hmono))
    -- data for the restart formula
    have hr : ((D.startCap k (Fin.init t) ω + sw : ℝ≥0) : WithTop ℝ≥0) <
        kLife (D.img k (Fin.init t) ω) (D.pre k (Fin.init t) ω) := by
      rw [hsum, Prop59NodeTree.TreeData.startCap_eq hA, Prop59Pieces.capClock_congr hagree]
      exact hγ'.lt_kLife hS'
    have hEq' : EqOn (kPath (D.img k (Fin.init t) ω) (D.pre k (Fin.init t) ω)) w
        (Icc 0 ((D.startCap k (Fin.init t) ω + sw : ℝ≥0) : ℝ)) := by rw [hSk1]; exact hkW
    have hpreI : Icc 0 (qLast (k + 1) t) ⊆ D.pre (k + 1) t ω := fun u hu => hγ.icc _ hq hu
    have hAle : ∀ j : Fin k, capClock (D.img (k + 1) t ω) (tau t (j + 1)) ≤ (D.startCap k (Fin.init t) ω : ℝ) := by
      intro j
      rw [hSk]
      have h1 := tau_le_qLast hT k (Fin.init t) hv' (j + 1) (by omega)
      have h2 := tau_le_qLast hT k (Fin.init t) hv' k le_rfl
      rw [tau_init t (by omega)] at h1
      rw [tau_init t le_rfl, ← tau_self (Fin.init t), tau_init t le_rfl] at h2
      have hk1 := htau (j + 1) (by omega)
      have hk2 := htau k (by omega)
      exact hγ.strictMonoOn_capClock.monotoneOn (hpreI ⟨hk1.1, hk1.2⟩) (hpreI ⟨hk2.1, hk2.2⟩) (by
        rw [← tau_self (Fin.init t), tau_init t le_rfl] at h1
        exact h1.2)
    have hAk : ∀ j : Fin k, (fun m => capClock (D.img k (Fin.init t) ω) (tau (Fin.init t) m)) (j + 1) =
        (fun m => capClock (D.img (k + 1) t ω) (tau t m)) (j + 1) := fun j => by
      simp only
      rw [tau_init t (by omega), hcapEq _ (by omega)]
    have hTk : capClock (D.img k (Fin.init t) ω) (qLast k (Fin.init t)) = (D.startCap k (Fin.init t) ω : ℝ) :=
      (Prop59NodeTree.TreeData.startCap_coe hD hA').symm
    have hT1 : capClock (D.img (k + 1) t ω) (qLast (k + 1) t) =
        (fun m => capClock (D.img (k + 1) t ω) (tau t m)) (k + 1) := by simp only [tau_self]
    rw [StagedNode.TreeData.marks_succ]
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
    · dsimp only
      rw [cfStageL_succ_treeIdx, hT1, imgBornL_self hw (fun m => capClock (D.img (k + 1) t ω) (tau t m)) (k + 1)]
      have hfun : (fun i' => (D.cand k (Fin.init t)).VL i' (candInv D.cand k (Fin.init t) (t (Fin.last k)) ω) ω -
          (D.cand k (Fin.init t)).W (candInv D.cand k (Fin.init t) (t (Fin.last k)) ω) ω) =
          fun i' => cfStageL (D.xL0 ω) w ((fun m => capClock (D.img (k + 1) t ω) (tau t m)) (k + 1))
            (fun m => capClock (D.img (k + 1) t ω) (tau t m)) k (treeIdx k nL₀ i') := by
        funext i'
        have e := StagedS3.arcVL_sub_arcW (γ := D.img k (Fin.init t)) (P := D.pre k (Fin.init t))
          (S₀ := D.startCap k (Fin.init t)) (Al := D.alive k (Fin.init t))
          (xL := fun ω => (D.marks k (Fin.init t) ω).1) hA' hr hw hEq' i'
        refine e.trans ?_
        rw [ih]
        simp only
        rw [hTk, cfStageL_congr_A (A := fun m => capClock (D.img k (Fin.init t) ω) (tau (Fin.init t) m))
          (A' := fun m => capClock (D.img (k + 1) t ω) (tau t m)) _ _ _ hAk,
          cfStageL_shift hw _ hAle (NNReal.coe_nonneg _) (NNReal.coe_nonneg _), ← NNReal.coe_add, hSk1, hT1]
      rw [hfun]
    · dsimp only
      rw [cfStageR_succ_treeIdx, hT1, imgBornR_self hw (fun m => capClock (D.img (k + 1) t ω) (tau t m)) (k + 1)]
      have hfun : (fun i' => (D.cand k (Fin.init t)).VR i' (candInv D.cand k (Fin.init t) (t (Fin.last k)) ω) ω -
          (D.cand k (Fin.init t)).W (candInv D.cand k (Fin.init t) (t (Fin.last k)) ω) ω) =
          fun i' => cfStageR (D.xR0 ω) w ((fun m => capClock (D.img (k + 1) t ω) (tau t m)) (k + 1))
            (fun m => capClock (D.img (k + 1) t ω) (tau t m)) k (treeIdx k nR₀ i') := by
        funext i'
        have e := StagedS3.arcVR_sub_arcW (γ := D.img k (Fin.init t)) (P := D.pre k (Fin.init t))
          (S₀ := D.startCap k (Fin.init t)) (Al := D.alive k (Fin.init t))
          (xR := fun ω => (D.marks k (Fin.init t) ω).2) hA' hr hw hEq' i'
        refine e.trans ?_
        rw [ih]
        simp only
        rw [hTk, cfStageR_congr_A (A := fun m => capClock (D.img k (Fin.init t) ω) (tau (Fin.init t) m))
          (A' := fun m => capClock (D.img (k + 1) t ω) (tau t m)) _ _ _ hAk,
          cfStageR_shift hw _ hAle (NNReal.coe_nonneg _) (NNReal.coe_nonneg _), ← NNReal.coe_add, hSk1, hT1]
      rw [hfun]

end Tree

/-! ### The marks identity on the glued space -/

section Glue

open WangWu.ImgWord Prop59System Prop59Stage Prop59Pieces StagedRepLater
open Sec7.Lemma71C (capClock)
open LQGMetric (DistOn)
open scoped Real
open GlueCond Cond44Ref Word49 StagedS4 StagedS5 StagedKill StagedCand
open Restart Exist.StagedLaw Exist.Staged Sec7.AdmCode Prop513TreeExtract Prop513Schedule Prop513Target
open Sec4 (IsStripGFF IsStripCounterflowDriver)
open LawUnique (HistorySpace)

theorem tau_succ {k : ℕ} (t : Fin k → ℝ≥0) (m : Fin k) : tau t (m + 1) = decode (t m) := by
  have hc : 0 < (m : ℕ) + 1 ∧ (m : ℕ) + 1 ≤ k := ⟨Nat.succ_pos _, m.2⟩
  simp only [tau, hc, and_self, ↓reduceDIte]
  rfl

variable (x₀ : ℝ) (h44 : Theorem12ParamCond44Statement.{0}) {κ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
  (hb : IsFig51Bounds κ a b a' b') {Ω : Type} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ)
  (ζ : Ω → ℝ≥0∞)

omit [StandardBorelSpace Ω] in
/-- **The marks identity of a later stage** (`GlueMarks`), everywhere: on the alive event and `gZ⁻¹ gamR`, the tree
marks of `Gam`'s candidate are the closed form of its own chain driver (`TreeData.marks_eq_cfStage`), which is the
`rootLam`-dilation (`cfStageL_smul`) of the closed form of the glued restarted word's initial marks. -/
theorem glueMarks {hhm : Measurable h} {j : ℕ} {t : Fin (j + 1) → ℝ≥0} (hv : IsValid (j + 1) t) (s : ℝ≥0) :
    GlueMarks x₀ h44 hκ hκ4 hb P h W ζ hhm (j + 1) t s := by
  have hEg := candEg_good x₀ h44 hκ hκ4 hb P h W ζ hhm (j + 1) t s
  refine Eventually.of_forall fun p hpA hR => ?_
  have hDr := isReg_gamData h44 hκ hκ4 (x₀ := x₀) hb s
  have hDt := isTree_gamData x₀ h44 hκ hκ4 hb s
  have hal : (gZ x₀ (κ := κ) h p) ∈ (gamData h44 hκ hκ4 (x₀ := x₀) hb s).alive (j + 1) t :=
    (TreeData.reach (rootNL_pos _) (rootNR_pos _) hDr hDt (fun _ _ => Iff.rfl) (j + 1) t (gZ x₀ (κ := κ) h p) hR).2
        (Nat.succ_pos j)
  have hZ : (gZ x₀ (κ := κ) h p) ∈ gamGood h44 hκ hκ4 (x₀ := x₀) hb := hal.1.2
  have hsc := arcScaleAt_gam x₀ h44 hκ hκ4 hb P h W ζ hv hpA hZ
  have hlam := rootLam_pos s p.2
  have hγ : WangWu.IsKilledArc (gCurve s (fun _ => ⊤) (candW x₀ h44 hκ hκ4 hb h (j + 1) t) (candEg x₀ h44 hκ hκ4 hb P
      h W ζ hhm (j + 1) t s) p) (gPre s (fun _ => ⊤) (candW x₀ h44 hκ hκ4 hb h (j + 1) t) (candEg x₀ h44 hκ hκ4 hb P
      h W ζ hhm (j + 1) t s) p) := hsc.arc
  have hq : (lastO (j + 1) t : ℝ) ∈ (gPre s (fun _ => ⊤) (candW x₀ h44 hκ hκ4 hb h (j + 1) t) (candEg x₀ h44 hκ hκ4
      hb P h W ζ hhm (j + 1) t s) p) := hpA.2
  -- the drivers of the two arcs
  have hu0 : ((0 : ℝ≥0) : ℝ≥0∞) < arcζ ((gamData h44 hκ hκ4 (x₀ := x₀) hb s).img (j + 1) t) ((gamData h44 hκ hκ4
      (x₀ := x₀) hb s).pre (j + 1) t) ((gamData h44 hκ hκ4 (x₀ := x₀) hb s).startCap (j + 1) t)
      ((gamData h44 hκ hκ4 (x₀ := x₀) hb s).alive (j + 1) t) (gZ x₀ (κ := κ) h p) := by
    rw [lt_arcζ_iff]
    exact ⟨hal, by simpa using Prop59NodeTree.TreeData.startCap_lt_kLife hDr hal⟩
  obtain ⟨w, hw, hEqg, hEqD⟩ := hsc.exists_drivers hu0
  simp only [mul_zero, add_zero] at hEqg hEqD
  have hEqD' : EqOn (kPath ((gamData h44 hκ hκ4 (x₀ := x₀) hb s).img (j + 1) t (gZ x₀ (κ := κ) h p)) ((gamData h44 hκ
      hκ4 (x₀ := x₀) hb s).pre (j + 1) t (gZ x₀ (κ := κ) h p))) (scD (rootLam s p.2) w)
      (Icc 0 (capClock ((gamData h44 hκ hκ4 (x₀ := x₀) hb s).img (j + 1) t (gZ x₀ (κ := κ) h p)) (qLast (j + 1)
          t))) := by
    rw [← Prop59NodeTree.TreeData.startCap_coe hDr hal]; exact hEqD
  -- the root marks and their signs
  have hpos : ∀ k (t' : Fin (k + 1) → ℝ≥0), (gamData h44 hκ hκ4 (x₀ := x₀) hb s).valid (k + 1) t' → 0 < qLast (k + 1)
      t' := fun k t' hv' => by
    rw [← lastO_eq hv']; exact_mod_cast oTime_pos hv' (Fin.last k)
  obtain ⟨-, -, hjL, hjR, -⟩ := hEg p hpA.1
  have hF := Theorem15.isOrderedForceWord_flowLine (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ
      hb).jumps 0
  have hx0L : ∀ i, (gamData h44 hκ hκ4 (x₀ := x₀) hb s).xL0 (gZ x₀ (κ := κ) h p) i ≤ 0 := fun i =>
    mul_nonpos_of_nonneg_of_nonpos hlam.le (StagedS7.imgMarkL_nonpos hF.2.1 hjL i)
  have hx0R : ∀ i, 0 ≤ (gamData h44 hκ hκ4 (x₀ := x₀) hb s).xR0 (gZ x₀ (κ := κ) h p) i := fun i =>
    mul_nonneg hlam.le (StagedS7.imgMarkR_nonneg hF.2.2.2 hjR i)
  have hm := TreeData.marks_eq_cfStage hDr hDt hpos (gZ x₀ (κ := κ) h p) hx0L hx0R (j + 1) t hal (scD (rootLam s p.2) w)
    (continuous_scD hw _) hEqD'
  -- the capacities
  have hmem : ∀ m : Fin (j + 1), candTs (j + 1) t (m + 1) ∈ (gPre s (fun _ => ⊤) (candW x₀ h44 hκ hκ4 hb h (j + 1) t)
      (candEg x₀ h44 hκ hκ4 hb P h W ζ hhm (j + 1) t s) p) := fun m =>
    hγ.icc _ hq ⟨(candTs_bounds hv m).1, (candTs_bounds hv m).2⟩
  have hGS : ((s3Start s (candW x₀ h44 hκ hκ4 hb h (j + 1) t) (candEg x₀ h44 hκ hκ4 hb P h W ζ hhm (j + 1) t s)
      (lastO (j + 1) t : ℝ) p) : ℝ) = capClock (gCurve s (fun _ => ⊤) (candW x₀ h44 hκ hκ4 hb h (j + 1) t) (candEg x₀
      h44 hκ hκ4 hb P h W ζ hhm (j + 1) t s) p) (lastO (j + 1) t : ℝ) := coe_s3Start_of_alive hEg hpA
  have hAg : ∀ m : Fin (j + 1), 0 ≤ (fun m => capClock (gCurve s (fun _ => ⊤) (candW x₀ h44 hκ hκ4 hb h (j + 1) t)
      (candEg x₀ h44 hκ hκ4 hb P h W ζ hhm (j + 1) t s) p) (candTs (j + 1) t m)) (m + 1) ∧ (fun m => capClock (gCurve
      s (fun _ => ⊤) (candW x₀ h44 hκ hκ4 hb h (j + 1) t) (candEg x₀ h44 hκ hκ4 hb P h W ζ hhm (j + 1) t s) p)
      (candTs (j + 1) t m)) (m + 1) ≤ ((s3Start s (candW x₀ h44 hκ hκ4 hb h (j + 1) t) (candEg x₀ h44 hκ hκ4 hb P h W
      ζ hhm (j + 1) t s) (lastO (j + 1) t : ℝ) p) : ℝ) := fun m => by
    refine ⟨hγ.capClock_nonneg (hmem m), ?_⟩
    rw [hGS]
    exact hγ.strictMonoOn_capClock.monotoneOn (hmem m) hq (candTs_bounds hv m).2
  have hTD : (capClock ((gamData h44 hκ hκ4 (x₀ := x₀) hb s).img (j + 1) t (gZ x₀ (κ := κ) h p)) (qLast (j + 1) t)) =
      rootLam s p.2 ^ 2 * ((s3Start s (candW x₀ h44 hκ hκ4 hb h (j + 1) t) (candEg x₀ h44 hκ hκ4 hb P h W ζ hhm (j +
      1) t s) (lastO (j + 1) t : ℝ) p) : ℝ) := by
    rw [← Prop59NodeTree.TreeData.startCap_coe hDr hal, hsc.start_coe]
  have hAD : ∀ m : Fin (j + 1), (fun m => capClock ((gamData h44 hκ hκ4 (x₀ := x₀) hb s).img (j + 1) t (gZ x₀ (κ :=
      κ) h p)) (tau t m)) (m + 1) = (fun m => rootLam s p.2 ^ 2 * capClock (gCurve s (fun _ => ⊤) (candW x₀ h44 hκ
      hκ4 hb h (j + 1) t) (candEg x₀ h44 hκ hκ4 hb P h W ζ hhm (j + 1) t s) p) (candTs (j + 1) t m)) (m + 1) := fun m
      => by
    simp only
    rw [tau_succ, ← oTime_eq (hv.2 m).2.2, ← candTs_succ hv m, hsc.img, capClock_smul hγ hlam (hmem m)]
  have hcfL : ∀ idx, cfStageL ((gamData h44 hκ hκ4 (x₀ := x₀) hb s).xL0 (gZ x₀ (κ := κ) h p)) (scD (rootLam s p.2) w)
      (capClock ((gamData h44 hκ hκ4 (x₀ := x₀) hb s).img (j + 1) t (gZ x₀ (κ := κ) h p)) (qLast (j + 1) t)) (fun m
      => capClock ((gamData h44 hκ hκ4 (x₀ := x₀) hb s).img (j + 1) t (gZ x₀ (κ := κ) h p)) (tau t m)) (j + 1) idx =
      rootLam s p.2 * imgStageVL (flowLineXL (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps 0)
          (cfDrv0 s p.2) s (kPath (gCurve s (fun _ => ⊤) (candW x₀ h44 hκ hκ4 hb h (j + 1) t) (candEg x₀ h44 hκ hκ4
          hb P h W ζ hhm (j + 1) t s) p) (gPre s (fun _ => ⊤) (candW x₀ h44 hκ hκ4 hb h (j + 1) t) (candEg x₀ h44 hκ
          hκ4 hb P h W ζ hhm (j + 1) t s) p)) ((s3Start s (candW x₀ h44 hκ hκ4 hb h (j + 1) t) (candEg x₀ h44 hκ hκ4
          hb P h W ζ hhm (j + 1) t s) (lastO (j + 1) t : ℝ) p) : ℝ) (fun m => capClock (gCurve s (fun _ => ⊤) (candW
          x₀ h44 hκ hκ4 hb h (j + 1) t) (candEg x₀ h44 hκ hκ4 hb P h W ζ hhm (j + 1) t s) p) (candTs (j + 1) t m)) (j
          + 1) idx := by
    intro idx
    rw [cfStageL_congr_A (A := (fun m => capClock ((gamData h44 hκ hκ4 (x₀ := x₀) hb s).img (j + 1) t (gZ x₀ (κ := κ)
        h p)) (tau t m))) (A' := (fun m => rootLam s p.2 ^ 2 * capClock (gCurve s (fun _ => ⊤) (candW x₀ h44 hκ hκ4
        hb h (j + 1) t) (candEg x₀ h44 hκ hκ4 hb P h W ζ hhm (j + 1) t s) p) (candTs (j + 1) t m))) _ _ _ hAD, hTD,
      imgStageVL_congr hw hEqg (flowLineXL (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps 0) _
          _ hAg (NNReal.coe_nonneg _), imgStageVL_eq_cfStageL]
    exact cfStageL_smul hw hlam _ (fun m => (hAg m).2) (NNReal.coe_nonneg _) idx
  have hcfR : ∀ idx, cfStageR ((gamData h44 hκ hκ4 (x₀ := x₀) hb s).xR0 (gZ x₀ (κ := κ) h p)) (scD (rootLam s p.2) w)
      (capClock ((gamData h44 hκ hκ4 (x₀ := x₀) hb s).img (j + 1) t (gZ x₀ (κ := κ) h p)) (qLast (j + 1) t)) (fun m
      => capClock ((gamData h44 hκ hκ4 (x₀ := x₀) hb s).img (j + 1) t (gZ x₀ (κ := κ) h p)) (tau t m)) (j + 1) idx =
      rootLam s p.2 * imgStageVR (flowLineXR (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps 0)
          (cfDrv0 s p.2) s (kPath (gCurve s (fun _ => ⊤) (candW x₀ h44 hκ hκ4 hb h (j + 1) t) (candEg x₀ h44 hκ hκ4
          hb P h W ζ hhm (j + 1) t s) p) (gPre s (fun _ => ⊤) (candW x₀ h44 hκ hκ4 hb h (j + 1) t) (candEg x₀ h44 hκ
          hκ4 hb P h W ζ hhm (j + 1) t s) p)) ((s3Start s (candW x₀ h44 hκ hκ4 hb h (j + 1) t) (candEg x₀ h44 hκ hκ4
          hb P h W ζ hhm (j + 1) t s) (lastO (j + 1) t : ℝ) p) : ℝ) (fun m => capClock (gCurve s (fun _ => ⊤) (candW
          x₀ h44 hκ hκ4 hb h (j + 1) t) (candEg x₀ h44 hκ hκ4 hb P h W ζ hhm (j + 1) t s) p) (candTs (j + 1) t m)) (j
          + 1) idx := by
    intro idx
    rw [cfStageR_congr_A (A := (fun m => capClock ((gamData h44 hκ hκ4 (x₀ := x₀) hb s).img (j + 1) t (gZ x₀ (κ := κ)
        h p)) (tau t m))) (A' := (fun m => rootLam s p.2 ^ 2 * capClock (gCurve s (fun _ => ⊤) (candW x₀ h44 hκ hκ4
        hb h (j + 1) t) (candEg x₀ h44 hκ hκ4 hb P h W ζ hhm (j + 1) t s) p) (candTs (j + 1) t m))) _ _ _ hAD, hTD,
      imgStageVR_congr hw hEqg (flowLineXR (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps 0) _
          _ hAg (NNReal.coe_nonneg _), imgStageVR_eq_cfStageR]
    exact cfStageR_smul hw hlam _ (fun m => (hAg m).2) (NNReal.coe_nonneg _) idx
  rw [hm]
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
  · dsimp only
    rw [hcfL]
    simp only [gVL, s6VL_zero hEg (candTs_bounds hv) p i]
    simp only [s3XL, hpA, ↓reduceIte]
  · dsimp only
    rw [hcfR]
    simp only [gVR, s6VR_zero hEg (candTs_bounds hv) p i]
    simp only [s3XR, hpA, ↓reduceIte]

end Glue

/-- **`GlueMarksStatement` holds.** -/
theorem glueMarksStatement (h44 : Sec7.AdmCode.Theorem12ParamCond44Statement.{0}) : GlueMarksStatement h44 := by
  intro κ x₀ a b a' b' hκ hκ4 hb Ω _ _ P _ h W ζ hG _ q _ j t hv
  exact glueMarks x₀ h44 hκ hκ4 hb P h W ζ hv _

/-- **Theorem 1.2's leaf `hRootLater`** for the concrete stage objects, from the glued past (and the clearance form of
Part A). -/
theorem rootLaterOn_s4Objects_of_gluePast (h44 : Sec7.AdmCode.Theorem12ParamCond44Statement.{0})
    (hA : PartAInputsSixteenDivOfClearance) (hpast : GluePastStatement h44) :
    Wire.Night.RootLaterOn h44 (StagedS4.s4Objects h44) :=
  rootLaterOn_s4Objects_of_marks h44 hA hpast (glueMarksStatement h44)

end InteractingSLE.Sec5.CrossCond.StagedRepJ
