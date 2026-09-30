import QuantumZipper.Proofs.Zipper.LogShiftW2Main
import QuantumZipper.Proofs.Zipper.UnifClSide
import QuantumZipper.Proofs.Zipper.B5VSide
import QuantumZipper.Proofs.Zipper.UnifClB5
import QuantumZipper.Proofs.Zipper.FlowRegSide
import QuantumZipper.Proofs.Zipper.E1ZFinBasic
import QuantumZipper.Proofs.Zipper.UnifUOPlus
import QuantumZipper.Proofs.RS.RealAlive
import QuantumZipper.Proofs.RS.RohdeSchrammSimple

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# LSL-W2 (3): the boundary positions `a_T(r)`, `b_T(r)` are continuous and strictly monotone

Task LSL-W2. For a continuous driver with simple reverse hulls at every horizon and no real
swallowing (a.s. for `κ ≤ 4`: `RS.rohdeSchrammSimple`, `RS.ae_real_alive`):

* `lswPos_fst_eq_zeroMinus`: `a_T(r) = (lswPos W T r).1 = 0₋^{V}(T − r)` with `V = B2.vrev W T`
  (endpoints: `B5.sideImages_fst_eq_zeroMinus_vrev` and `lswPos_self`; interior:
  `RegUnif.sideImages_fst_shift_eq` at `u = r`, `s = T − r`, whose reverse-flow time is `0`);
  hence `a_T` is continuous and strictly increasing on `[0, T]` (`B5.strictAntiOn_zeroMinus`,
  `B5.continuousOn_zeroMinus_Icc`);
* `lswPos_neg`: `lswPos (−W) T r = (−b_T(r), −a_T(r))` (`F1.sideImages_reflect_swap`, the side
  limits exist for every continuous driver, `F1.exists_tendsto_fwdMap_left/right`), so `b_T` is
  continuous and strictly decreasing (the left result for the Brownian motion `−B`);
* `lswPosStmt_of_trace : LswPosTraceStmt → LswPosStmt`: only the boundary-correspondence identity
  `E_T(a_T(r)) = E_T(b_T(r)) = η(r)` remains.

Sources: Lawler, *Conformally invariant processes in the plane* (2005), §4.1; Rohde–Schramm,
Ann. Math. 161 (2005), Thm 6.1. Own bookkeeping on top of the proved `0₋` facts.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace F1

theorem lswPos_zero_of {W : ℝ → ℝ} (hW0 : W 0 = 0) (hneg : ∀ v ≤ 0, W v = 0) (T : ℝ) :
    lswPos W T 0 = sideImages W T := by
  unfold lswPos
  rw [sub_zero]
  congr 1
  funext v
  rw [zero_add, hW0, sub_zero]
  rcases le_total v 0 with hv | hv
  · rw [max_eq_right hv, hW0, hneg v hv]
  · rw [max_eq_left hv]

/-- **`a_T(r) = 0₋^{B2.vrev W T}(T − r)`** (deterministic). -/
theorem lswPos_fst_eq_zeroMinus {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0)
    (hneg : ∀ v ≤ 0, W v = 0)
    (hK : ∀ s : ℝ, 0 < s → IsSimpleCurveHull (revHull (B2.vrev W s) s))
    (halive : ∀ x : ℝ, x ≠ 0 → ∀ T : ℝ, 0 ≤ T → ∃ v, IsForwardSol W (x : ℂ) T v)
    {T r : ℝ} (hT : 0 < T) (hr : r ∈ Icc 0 T) :
    (lswPos W T r).1 = zeroMinus (B2.vrev W T) (T - r) := by
  have hVc := B2.continuous_vrev hW T
  have hV0 : B2.vrev W T 0 = 0 := B2.vrev_zero hT.le
  rcases eq_or_lt_of_le hr.1 with h0 | h0
  · rw [← h0, lswPos_zero_of hW0 hneg, sub_zero]
    exact B5.sideImages_fst_eq_zeroMinus_vrev hW hW0 hT (hK T hT) fun x hx => halive x hx T hT.le
  rcases eq_or_lt_of_le hr.2 with hT' | hT'
  · rw [hT', lswPos_self, sub_self, B5.zeroMinus_zero_time hVc hV0]
  have hc : zeroMinus (B2.vrev W T) (T - r) < 0 :=
    B5.zeroMinus_neg_of_le hVc hV0 hT (hK T hT) (sub_pos.2 hT') (by linarith)
  unfold lswPos
  rw [RegUnif.sideImages_fst_shift_eq (hW := hW) (hT := hT) (hK := hK T hT) (hKu := hK r h0)
    (hu := h0) (hs := sub_pos.2 hT') (hus := by linarith)]
  rw [show T - r - (T - r) = 0 by ring]
  exact E1.realRevMap_zero_of_ne hV0 hc.ne

/-- Continuity and strict monotonicity of `a_T` (deterministic). -/
theorem lswPos_fst_facts {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0)
    (hneg : ∀ v ≤ 0, W v = 0)
    (hK : ∀ s : ℝ, 0 < s → IsSimpleCurveHull (revHull (B2.vrev W s) s))
    (halive : ∀ x : ℝ, x ≠ 0 → ∀ T : ℝ, 0 ≤ T → ∃ v, IsForwardSol W (x : ℂ) T v)
    {T : ℝ} (hT : 0 ≤ T) :
    ContinuousOn (fun r => (lswPos W T r).1) (Icc 0 T) ∧
      StrictMonoOn (fun r => (lswPos W T r).1) (Icc 0 T) := by
  rcases eq_or_lt_of_le hT with h | hT
  · subst h
    refine ⟨fun r hr => ?_, fun r hr r' hr' hlt => ?_⟩
    · have hr0 : r = 0 := le_antisymm hr.2 hr.1
      subst hr0
      have : Icc (0 : ℝ) 0 = {0} := Icc_self 0
      rw [this]
      exact continuousWithinAt_singleton
    · exact absurd hlt (by linarith [hr.1, hr.2, hr'.1, hr'.2])
  have hVc := B2.continuous_vrev hW T
  have hV0 : B2.vrev W T 0 = 0 := B2.vrev_zero hT.le
  have heq : EqOn (fun r => (lswPos W T r).1) (fun r => zeroMinus (B2.vrev W T) (T - r)) (Icc 0 T) :=
    fun r hr => lswPos_fst_eq_zeroMinus hW hW0 hneg hK halive hT hr
  have hmaps : MapsTo (fun r : ℝ => T - r) (Icc 0 T) (Icc 0 T) := fun r hr =>
    ⟨by linarith [hr.2], by linarith [hr.1]⟩
  refine ⟨ContinuousOn.congr ((B5.continuousOn_zeroMinus_Icc hVc hV0 hT (hK T hT)).comp
    (continuous_const.sub continuous_id).continuousOn hmaps) heq, fun r hr r' hr' hlt => ?_⟩
  rw [heq hr, heq hr']
  exact B5.strictAntiOn_zeroMinus hVc hV0 hT (hK T hT) (hmaps hr') (hmaps hr) (by linarith)

/-- **Reflection of the positions.** -/
theorem lswPos_neg {W : ℝ → ℝ} (hW : Continuous W) {T r : ℝ} (hrT : r ≤ T) :
    lswPos (-W) T r = (-(lswPos W T r).2, -(lswPos W T r).1) := by
  unfold lswPos
  have e : (fun v => (-W) (r + max v 0) - (-W) r) = -(fun v => W (r + max v 0) - W r) := by
    funext v
    simp only [Pi.neg_apply]
    ring
  have hWr : Continuous (fun v => W (r + max v 0) - W r) :=
    (hW.comp (continuous_const.add (continuous_id.max continuous_const))).sub continuous_const
  have hWr0 : (fun v => W (r + max v 0) - W r) 0 = 0 := by simp
  obtain ⟨a, ha⟩ := exists_tendsto_fwdMap_left hWr hWr0 (sub_nonneg.2 hrT)
  obtain ⟨b, hb⟩ := exists_tendsto_fwdMap_right hWr hWr0 (sub_nonneg.2 hrT)
  rw [e]
  exact sideImages_reflect_swap (sub_nonneg.2 hrT) ha hb

/-- **Boundary correspondence at every stage** (the remaining leaf): the boundary extension of
`f_T⁻¹` sends both positions of capacity time `r` to the trace point `η(r)`. -/
def LswPosTraceStmt : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ), IsBrownianReal B P →
    ∀ᵐ ω ∂P, ∀ T : ℝ, 0 ≤ T → ∀ r ∈ Ioc 0 T,
      F2.extInv (drive κ B ω) T ((lswPos (drive κ B ω) T r).1 : ℂ) = trace (drive κ B ω) r ∧
      F2.extInv (drive κ B ω) T ((lswPos (drive κ B ω) T r).2 : ℂ) = trace (drive κ B ω) r

/-- The a.s. hypotheses of `lswPos_fst_facts` for an SLE driver. -/
theorem ae_lswPos_fst_facts {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ ≤ 4) {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) :
    ∀ᵐ ω ∂P, ∀ T : ℝ, 0 ≤ T →
      ContinuousOn (fun r => (lswPos (drive κ B ω) T r).1) (Icc 0 T) ∧
      StrictMonoOn (fun r => (lswPos (drive κ B ω) T r).1) (Icc 0 T) := by
  filter_upwards [RegUnif.ae_forall_isSimpleCurveHull_revHull_Vr RS.rohdeSchrammSimple hκ hκ4 P B
    hB, RS.ae_real_alive hB hκ hκ4, hB.cont, hB.eval_zero_ae_eq_zero] with ω hK hal hc h0 T hT
  have hW : Continuous (drive κ B ω) := by
    unfold drive
    exact continuous_const.mul (hc.comp continuous_real_toNNReal)
  have hW0 : drive κ B ω 0 = 0 := by simp [drive, h0]
  have hneg : ∀ v ≤ 0, drive κ B ω v = 0 := fun v hv => by
    simp [drive, Real.toNNReal_of_nonpos hv, h0]
  exact lswPos_fst_facts hW hW0 hneg hK (fun x hx T hT => hal x hx T hT) hT

/-- **`LswPosStmt` from the boundary correspondence alone.** -/
theorem lswPosStmt_of_trace (h : LswPosTraceStmt) : LswPosStmt := by
  intro κ hκ hκ4 Ω _ P _ B hB
  have hB' : IsBrownianReal (RegUnif.negB B) P := hB.neg
  filter_upwards [ae_lswPos_fst_facts hκ hκ4.le hB, ae_lswPos_fst_facts hκ hκ4.le hB',
    h κ hκ hκ4 P B hB, hB.cont] with ω hL hR htr hc T hT
  have hW : Continuous (drive κ B ω) := by
    unfold drive
    exact continuous_const.mul (hc.comp continuous_real_toNNReal)
  obtain ⟨hLc, hLm⟩ := hL T hT
  obtain ⟨hRc, hRm⟩ := hR T hT
  rw [RegUnif.drive_negB] at hRc hRm
  have e : EqOn (fun r => (lswPos (drive κ B ω) T r).2)
      (fun r => -(lswPos (-drive κ B ω) T r).1) (Icc 0 T) := fun r hr => by
    simp only [lswPos_neg hW hr.2, neg_neg]
  refine ⟨hLc, hRc.neg.congr e, hLm, fun r hr r' hr' hlt => ?_, htr T hT⟩
  rw [e hr, e hr']
  exact neg_lt_neg (hRm hr hr' hlt)

end F1
end QuantumZipper
