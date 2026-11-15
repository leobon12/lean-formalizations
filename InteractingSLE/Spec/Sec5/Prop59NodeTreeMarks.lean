/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop59NodeTreeFlow
import InteractingSLE.Spec.Sec5.Prop59NodeTreeChain

/-!
# The far marks at the tip of a node prefix

Packet PROVE-PROP59-NODETREE. Specification §5.2, proof of Proposition 5.9 (p. 143: "Rescale it so that the marked
points `z₋, z₊` in Figure 5.7 satisfy `z₋ ≤ −3` and `z₊ ≥ 3`"). The dilation at a node needs the two far marks at the
node tip strictly on their sides of the driver. Along the node prefix all pieces are pieces of one killed arc (the
joint-chart image of the node path), and the marks of a piece are transported by its relative driver; by the flow
property of the real Loewner equation (`rightImg_shiftDrv`) the far marks at the node tip are the images of the root
far marks under the whole driver, which are strictly separated from it (the arc is simple and lies in `ℍ`, WangWu's
`IsKilledArc.kW_lt_kVRr`, `IsKilledArc.kVLr_lt_kW`).

* `TreeData.alive_of_spine`, `TreeData.startCap_succ`: along a spine of lists sharing one image curve;
* **`TreeData.marks_farR_spine`**, **`TreeData.marks_farL_spine`**: the far marks are the images of the root far marks
  under the whole driver;
* **`TreeData.farGaps_spine`**: the far gaps at the tip of the spine are strictly positive.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Function
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Prop59NodeTree

open WangWu WangWu.ImgWord MartChar.RealFlow Prop59System Prop59Stage Prop59Pieces
open Sec7.Lemma71C (capClock)

section Spine

variable {Ω : Type*} [MeasurableSpace Ω] {nL₀ nR₀ : ℕ} {D : TreeData Ω nL₀ nR₀}

/-- **The hypotheses of a spine** at the sample `ω`: the list `p` of length `m` is admissible and alive, and every
admissible list of length at most `m` has the image curve and pre-contact times of `p` and an earlier last switch. -/
structure IsSpine (D : TreeData Ω nL₀ nR₀) (m : ℕ) (p : Fin m → ℝ≥0) (ω : Ω) : Prop where
  valid : D.valid m p
  alive : ω ∈ D.alive m p
  img : ∀ k t, k ≤ m → D.valid k t → D.img k t ω = D.img m p ω
  pre : ∀ k t, k ≤ m → D.valid k t → D.pre k t ω = D.pre m p ω
  qle : ∀ k t, k ≤ m → D.valid k t → qLast k t ≤ qLast m p

variable {m : ℕ} {p : Fin m → ℝ≥0} {ω : Ω}

/-- Every admissible list along a spine is alive. -/
theorem TreeData.alive_of_spine (hT : D.IsTree) (hS : IsSpine D m p ω) (hD : D.IsReg) {k : ℕ} {t : Fin k → ℝ≥0}
    (hk : k ≤ m) (hv : D.valid k t) : ω ∈ D.alive k t := by
  refine ⟨⟨hv, hS.alive.1.2⟩, ?_⟩
  rw [hS.pre k t hk hv]
  exact (hD.isKilledFamily m p).arc ω |>.icc _ hS.alive.2 ⟨hT.qnonneg k t hv, hS.qle k t hk hv⟩

theorem TreeData.startCap_coe {k : ℕ} {t : Fin k → ℝ≥0} (hD : D.IsReg) (hA : ω ∈ D.alive k t) :
    (D.startCap k t ω : ℝ) = capClock (D.img k t ω) (qLast k t) := by
  classical
  simp only [TreeData.startCap, hA, ↓reduceIte]
  exact Real.coe_toNNReal _ (((hD.isKilledFamily k t).arc ω).capClock_nonneg hA.2)

omit [MeasurableSpace Ω] in
theorem TreeData.startCap_eq {k : ℕ} {t : Fin k → ℝ≥0} (hA : ω ∈ D.alive k t) :
    D.startCap k t ω = (capClock (D.img k t ω) (qLast k t)).toNNReal := by
  classical
  simp only [TreeData.startCap, hA, ↓reduceIte]

/-- The start capacity of an alive list is before the terminal capacity. -/
theorem TreeData.startCap_lt_kLife (hD : D.IsReg) {k : ℕ} {t : Fin k → ℝ≥0} (hA : ω ∈ D.alive k t) :
    ((D.startCap k t ω : ℝ≥0) : WithTop ℝ≥0) < kLife (D.img k t ω) (D.pre k t ω) := by
  rw [TreeData.startCap_eq hA]
  exact ((hD.isKilledFamily k t).arc ω).lt_kLife hA.2

/-- The start capacities along a spine increase by the switch's piece time. -/
theorem TreeData.startCap_succ (hD : D.IsReg) (hT : D.IsTree) {k : ℕ} {t : Fin (k + 1) → ℝ≥0}
    (hA : ω ∈ D.alive (k + 1) t) (hA' : ω ∈ D.alive k (Fin.init t)) :
    D.startCap k (Fin.init t) ω + clkInv (D.clkStage k (Fin.init t)) (t (Fin.last k)) ω = D.startCap (k + 1) t ω := by
  have h1 := D.recStart_eq hD hT (k + 1) t ω hA
  have h2 := D.recStart_eq hD hT k (Fin.init t) ω hA'
  rw [recStart, h2, TreeData.candInv_eq, ← NNReal.coe_add] at h1
  exact NNReal.coe_injective h1

/-- The start capacities along a spine are at most the start capacity of its tip. -/
theorem TreeData.startCap_le_of_spine (hD : D.IsReg) (hT : D.IsTree) (hS : IsSpine D m p ω) {k : ℕ}
    {t : Fin k → ℝ≥0} (hk : k ≤ m) (hv : D.valid k t) : (D.startCap k t ω : ℝ) ≤ D.startCap m p ω := by
  have hA := TreeData.alive_of_spine hT hS hD hk hv
  rw [TreeData.startCap_coe hD hA, TreeData.startCap_coe hD hS.alive, hS.img k t hk hv]
  have hγ := (hD.isKilledFamily m p).arc ω
  have hq : qLast k t ∈ D.pre m p ω := by rw [← hS.pre k t hk hv]; exact hA.2
  exact hγ.strictMonoOn_capClock.monotoneOn hq hS.alive.2 (hS.qle k t hk hv)

variable (hD : D.IsReg) (hT : D.IsTree) (hS : IsSpine D m p ω) {w : ℝ → ℝ} (hw : Continuous w)
  {Cap : ℝ} (hEq : EqOn (kPath (D.img m p ω) (D.pre m p ω)) w (Icc 0 Cap)) (hCap : (D.startCap m p ω : ℝ) ≤ Cap)
include hD hT hS hw hEq hCap

omit hw in
/-- The relative driver of a spine piece, before the next switch, is the shifted driver. -/
theorem TreeData.realPath_arcW_spine {k : ℕ} {t : Fin (k + 1) → ℝ≥0} (hk : k + 1 ≤ m) (hv : D.valid (k + 1) t)
    {r : ℝ} (hr : r ∈ Icc (0 : ℝ) (clkInv (D.clkStage k (Fin.init t)) (t (Fin.last k)) ω)) :
    Bessel.realPath (arcW (D.img k (Fin.init t)) (D.pre k (Fin.init t)) (D.startCap k (Fin.init t))
      (D.alive k (Fin.init t))) ω r = shiftDrv w (D.startCap k (Fin.init t) ω) r := by
  have hv' : D.valid k (Fin.init t) := (hT.init k t hv).1
  have hA := TreeData.alive_of_spine hT hS hD hk hv
  have hA' := TreeData.alive_of_spine hT hS hD (by omega) hv'
  have hsum := TreeData.startCap_succ hD hT hA hA'
  have hle := TreeData.startCap_le_of_spine hD hT hS hk hv
  have hγ := (hD.isKilledFamily m p).arc ω
  have hlife : ((D.startCap (k + 1) t ω : ℝ≥0) : WithTop ℝ≥0) < kLife (D.img m p ω) (D.pre m p ω) :=
    lt_of_le_of_lt (WithTop.coe_le_coe.2 (NNReal.coe_le_coe.1 hle)) (TreeData.startCap_lt_kLife hD hS.alive)
  have hrle : r.toNNReal ≤ clkInv (D.clkStage k (Fin.init t)) (t (Fin.last k)) ω := by
    rw [Real.toNNReal_le_iff_le_coe]; exact hr.2
  have hlt : ((r.toNNReal : ℝ≥0) : ℝ≥0∞) < arcζ (D.img k (Fin.init t)) (D.pre k (Fin.init t))
      (D.startCap k (Fin.init t)) (D.alive k (Fin.init t)) ω := by
    refine lt_arcζ_iff.2 ⟨hA', ?_⟩
    rw [hS.img k _ (by omega) hv', hS.pre k _ (by omega) hv']
    refine lt_of_le_of_lt (WithTop.coe_le_coe.2 ?_) hlife
    rw [← hsum]
    exact add_le_add le_rfl hrle
  have hkw : ∀ u : ℝ≥0, (u : ℝ) ≤ Cap → kW (D.img m p ω) (D.pre m p ω) u = w u := fun u hu =>
    (kPath_coe u).symm.trans (hEq ⟨u.coe_nonneg, hu⟩)
  simp only [Bessel.realPath]
  rw [arcW_of_lt hlt, hS.img k _ (by omega) hv', hS.pre k _ (by omega) hv']
  have hS0 : (D.startCap k (Fin.init t) ω : ℝ) ≤ Cap :=
    (TreeData.startCap_le_of_spine hD hT hS (by omega) hv').trans hCap
  have hS1 : ((D.startCap k (Fin.init t) ω + r.toNNReal : ℝ≥0) : ℝ) ≤ Cap := by
    refine le_trans ?_ (hle.trans hCap)
    rw [← hsum, NNReal.coe_add, NNReal.coe_add]
    exact add_le_add le_rfl (by exact_mod_cast hrle)
  rw [hkw _ hS1, hkw _ hS0, shiftDrv, NNReal.coe_add, Real.coe_toNNReal _ hr.1]

/-- **The right far mark along a spine** is the image of the root far mark under the whole driver. -/
theorem TreeData.marks_farR_spine (hw0 : w 0 = 0) (hnR : 0 < nR₀) (hx : 0 ≤ D.xR0 ω (farR hnR)) :
    ∀ (k : ℕ) (t : Fin k → ℝ≥0), k ≤ m → D.valid k t →
      (D.marks k t ω).2 (farR (Nat.lt_of_lt_of_le hnR (Nat.le_add_right _ _))) =
        rightImg w (D.xR0 ω (farR hnR)) (D.startCap k t ω) - w (D.startCap k t ω)
  | 0, t, _, hv => by
    have hA := TreeData.alive_of_spine hT hS hD (Nat.zero_le _) hv
    have h0 : (D.startCap 0 t ω : ℝ) = 0 := by
      rw [TreeData.startCap_coe hD hA]
      exact ((hD.isKilledFamily 0 t).arc ω).capClock_zero
    rw [h0, rightImg_zero hw hw0 hx, hw0, sub_zero]
    rfl
  | k + 1, t, hk, hv => by
    have hv' : D.valid k (Fin.init t) := (hT.init k t hv).1
    have ih := TreeData.marks_farR_spine hw0 hnR hx k (Fin.init t) (by omega) hv'
    have hA := TreeData.alive_of_spine hT hS hD hk hv
    have hA' := TreeData.alive_of_spine hT hS hD (by omega) hv'
    have hsum := TreeData.startCap_succ hD hT hA hA'
    set σ := clkInv (D.clkStage k (Fin.init t)) (t (Fin.last k)) ω with hσ
    have hle := TreeData.startCap_le_of_spine hD hT hS hk hv
    have hγ := (hD.isKilledFamily m p).arc ω
    have hlife : ((D.startCap (k + 1) t ω : ℝ≥0) : WithTop ℝ≥0) < kLife (D.img m p ω) (D.pre m p ω) :=
      lt_of_le_of_lt (WithTop.coe_le_coe.2 (NNReal.coe_le_coe.1 hle)) (TreeData.startCap_lt_kLife hD hS.alive)
    have hσζ : (σ : ℝ≥0∞) < arcζ (D.img k (Fin.init t)) (D.pre k (Fin.init t)) (D.startCap k (Fin.init t))
        (D.alive k (Fin.init t)) ω := by
      refine lt_arcζ_iff.2 ⟨hA', ?_⟩
      rw [hS.img k _ (by omega) hv', hS.pre k _ (by omega) hv', hsum]
      exact hlife
    have hidx : (farR (Nat.lt_of_lt_of_le hnR (Nat.le_add_right _ _)) : Fin (nR₀ + (k + 1))) =
        Fin.succ (farR (Nat.lt_of_lt_of_le hnR (Nat.le_add_right _ _)) : Fin (nR₀ + k)) :=
      Fin.ext (by simp only [farR, Fin.val_succ]; omega)
    have hcongr : rightImg (Bessel.realPath (arcW (D.img k (Fin.init t)) (D.pre k (Fin.init t))
        (D.startCap k (Fin.init t)) (D.alive k (Fin.init t))) ω)
          ((D.marks k (Fin.init t) ω).2 (farR (Nat.lt_of_lt_of_le hnR (Nat.le_add_right _ _)))) σ =
        rightImg (shiftDrv w (D.startCap k (Fin.init t) ω))
          ((D.marks k (Fin.init t) ω).2 (farR (Nat.lt_of_lt_of_le hnR (Nat.le_add_right _ _)))) σ :=
      Sec7.Lemma71B.rightImg_congr (continuous_shiftDrv hw _) σ.coe_nonneg
        (fun r hr => TreeData.realPath_arcW_spine hD hT hS hEq hCap hk hv hr) _
    have hW := TreeData.realPath_arcW_spine hD hT hS hEq hCap hk hv (r := σ) ⟨σ.coe_nonneg, le_rfl⟩
    simp only [Bessel.realPath, Real.toNNReal_coe] at hW
    rw [hidx]
    simp only [TreeData.marks, Fin.cons_succ]
    simp only [arcVR, ← hσ, hσζ, ↓reduceIte]
    rw [hcongr, hW, ih, rightImg_shiftDrv hw (D.startCap k (Fin.init t) ω).coe_nonneg σ.coe_nonneg, shiftDrv]
    rw [← hsum, NNReal.coe_add]
    ring

/-- **The left far mark along a spine** is the reflected image of the root far mark under the whole driver. -/
theorem TreeData.marks_farL_spine (hw0 : w 0 = 0) (hnL : 0 < nL₀) (hx : D.xL0 ω (farL hnL) ≤ 0) :
    ∀ (k : ℕ) (t : Fin k → ℝ≥0), k ≤ m → D.valid k t →
      (D.marks k t ω).1 (farL (Nat.lt_of_lt_of_le hnL (Nat.le_add_right _ _))) =
        -rightImg (fun r => -w r) (-D.xL0 ω (farL hnL)) (D.startCap k t ω) - w (D.startCap k t ω)
  | 0, t, _, hv => by
    have hA := TreeData.alive_of_spine hT hS hD (Nat.zero_le _) hv
    have h0 : (D.startCap 0 t ω : ℝ) = 0 := by
      rw [TreeData.startCap_coe hD hA]
      exact ((hD.isKilledFamily 0 t).arc ω).capClock_zero
    have hwn : Continuous fun r => -w r := hw.neg
    rw [h0, rightImg_zero hwn (by simp [hw0]) (neg_nonneg.2 hx), hw0, neg_neg, sub_zero]
    rfl
  | k + 1, t, hk, hv => by
    have hv' : D.valid k (Fin.init t) := (hT.init k t hv).1
    have ih := TreeData.marks_farL_spine hw0 hnL hx k (Fin.init t) (by omega) hv'
    have hA := TreeData.alive_of_spine hT hS hD hk hv
    have hA' := TreeData.alive_of_spine hT hS hD (by omega) hv'
    have hsum := TreeData.startCap_succ hD hT hA hA'
    set σ := clkInv (D.clkStage k (Fin.init t)) (t (Fin.last k)) ω with hσ
    have hle := TreeData.startCap_le_of_spine hD hT hS hk hv
    have hγ := (hD.isKilledFamily m p).arc ω
    have hlife : ((D.startCap (k + 1) t ω : ℝ≥0) : WithTop ℝ≥0) < kLife (D.img m p ω) (D.pre m p ω) :=
      lt_of_le_of_lt (WithTop.coe_le_coe.2 (NNReal.coe_le_coe.1 hle)) (TreeData.startCap_lt_kLife hD hS.alive)
    have hσζ : (σ : ℝ≥0∞) < arcζ (D.img k (Fin.init t)) (D.pre k (Fin.init t)) (D.startCap k (Fin.init t))
        (D.alive k (Fin.init t)) ω := by
      refine lt_arcζ_iff.2 ⟨hA', ?_⟩
      rw [hS.img k _ (by omega) hv', hS.pre k _ (by omega) hv', hsum]
      exact hlife
    have hidx : (farL (Nat.lt_of_lt_of_le hnL (Nat.le_add_right _ _)) : Fin (nL₀ + (k + 1))) =
        Fin.succ (farL (Nat.lt_of_lt_of_le hnL (Nat.le_add_right _ _)) : Fin (nL₀ + k)) :=
      Fin.ext (by simp only [farL, Fin.val_succ]; omega)
    have hcongr : rightImg (Bessel.realPath (fun u ω => -arcW (D.img k (Fin.init t)) (D.pre k (Fin.init t))
        (D.startCap k (Fin.init t)) (D.alive k (Fin.init t)) u ω) ω)
          (-(D.marks k (Fin.init t) ω).1 (farL (Nat.lt_of_lt_of_le hnL (Nat.le_add_right _ _)))) σ =
        rightImg (shiftDrv (fun r => -w r) (D.startCap k (Fin.init t) ω))
          (-(D.marks k (Fin.init t) ω).1 (farL (Nat.lt_of_lt_of_le hnL (Nat.le_add_right _ _)))) σ := by
      have hwn : Continuous fun r => -w r := hw.neg
      refine Sec7.Lemma71B.rightImg_congr (continuous_shiftDrv hwn _) σ.coe_nonneg (fun r hr => ?_) _
      have h := TreeData.realPath_arcW_spine hD hT hS hEq hCap hk hv hr
      simp only [Bessel.realPath] at h ⊢
      rw [h, shiftDrv_neg]
    have hW := TreeData.realPath_arcW_spine hD hT hS hEq hCap hk hv (r := σ) ⟨σ.coe_nonneg, le_rfl⟩
    simp only [Bessel.realPath, Real.toNNReal_coe] at hW
    rw [hidx]
    simp only [TreeData.marks, Fin.cons_succ]
    simp only [arcVL, ← hσ, hσζ, ↓reduceIte]
    have harg : -(D.marks k (Fin.init t) ω).1 (farL (Nat.lt_of_lt_of_le hnL (Nat.le_add_right _ _))) =
        rightImg (fun r => -w r) (-D.xL0 ω (farL hnL)) (D.startCap k (Fin.init t) ω) -
          (fun r => -w r) (D.startCap k (Fin.init t) ω) := by
      rw [ih]; ring
    have hwn : Continuous fun r => -w r := hw.neg
    rw [hcongr, hW, harg, rightImg_shiftDrv hwn (D.startCap k (Fin.init t) ω).coe_nonneg σ.coe_nonneg,
      ← hsum, NNReal.coe_add]
    simp only [shiftDrv]
    ring

/-- **The far gaps at the tip of a spine are strictly positive.** -/
theorem TreeData.farGaps_spine (hw0 : w 0 = 0) (hnL : 0 < nL₀) (hnR : 0 < nR₀) (hxL : D.xL0 ω (farL hnL) ≤ 0)
    (hxR : 0 ≤ D.xR0 ω (farR hnR)) (hq0 : 0 < qLast m p) :
    (D.marks m p ω).1 (farL (Nat.lt_of_lt_of_le hnL (Nat.le_add_right _ _))) < 0 ∧
      0 < (D.marks m p ω).2 (farR (Nat.lt_of_lt_of_le hnR (Nat.le_add_right _ _))) := by
  have hγ := (hD.isKilledFamily m p).arc ω
  set Sm := D.startCap m p ω with hSm
  have hSm0 : 0 < Sm := by
    have h := TreeData.startCap_coe hD hS.alive
    have hpos : capClock (D.img m p ω) 0 < capClock (D.img m p ω) (qLast m p) :=
      hγ.strictMonoOn_capClock hγ.zero_mem hS.alive.2 hq0
    rw [hγ.capClock_zero] at hpos
    rw [← NNReal.coe_pos, h]
    exact hpos
  have hlife : ((Sm : ℝ≥0) : WithTop ℝ≥0) < kLife (D.img m p ω) (D.pre m p ω) :=
    TreeData.startCap_lt_kLife hD hS.alive
  have hkw : kW (D.img m p ω) (D.pre m p ω) Sm = w Sm :=
    (kPath_coe Sm).symm.trans (hEq ⟨Sm.coe_nonneg, hCap⟩)
  constructor
  · rw [TreeData.marks_farL_spine hD hT hS hw hEq hCap hw0 hnL hxL m p le_rfl hS.valid]
    have h := hγ.kVLr_lt_kW (xL := fun _ : Fin 1 => D.xL0 ω (farL hnL)) (fun _ => hxL) hSm0 hlife 0
    have hEq' : EqOn (fun r => -kPath (D.img m p ω) (D.pre m p ω) r) (fun r => -w r) (Icc 0 Cap) := fun r hr => by
      simp only [hEq hr]
    have hwn : Continuous fun r => -w r := hw.neg
    rw [kVLr, kImg_eq hwn hEq' hCap, hkw] at h
    linarith
  · rw [TreeData.marks_farR_spine hD hT hS hw hEq hCap hw0 hnR hxR m p le_rfl hS.valid]
    have h := hγ.kW_lt_kVRr (xR := fun _ : Fin 1 => D.xR0 ω (farR hnR)) (fun _ => hxR) hSm0 hlife 0
    rw [kVRr, kImg_eq hw hEq hCap, hkw] at h
    linarith

end Spine

end InteractingSLE.Sec5.Prop59NodeTree
