/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.AssemblyThreshold
import InteractingSLE.Spec.Sec2.TerminalPath

/-!
# Theorem 2.2 assembly: the solution relation is measurable

Packet PROVE-SEC2-PATCH. `Rel a xL xR ρL ρR ⊆ XCode nL nR` is the set of codes `x` that are `Good`,
satisfy `LimThr` (the dyadic limit at a finite positive lifetime is a threshold state; true almost
surely for every evolution by Aux. lemma 3), and whose decoded paths satisfy the frozen
`IsIntegratedSLEPath`. It is a measurable subset of a standard Borel space (`measurableSet_rel`):
on `Good ∩ LimThr` the frozen predicate is equivalent to the countable conditions `MSet`
(`isIntegratedSLEPath_iff_mem_mSet`): initial values; ordering, integrability and the integrated
equations at dyadic times before `ζ`; null collision sets (measurable by Tonelli); the dyadic
form of "the threshold condition fails before `ζ`" (`AssemblyThreshold`); and the seed clause.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec2

namespace Assembly

/-! ### Measurability helpers -/

section Helpers

variable {α : Type*} [MeasurableSpace α]

theorem measurable_lt' {f g : α → ℝ} (hf : Measurable f) (hg : Measurable g) :
    Measurable fun x => f x < g x := measurableSet_setOfPred.1 (measurableSet_lt hf hg)

theorem measurable_le' {f g : α → ℝ} (hf : Measurable f) (hg : Measurable g) :
    Measurable fun x => f x ≤ g x := measurableSet_setOfPred.1 (measurableSet_le hf hg)

theorem measurable_eq_real {f g : α → ℝ} (hf : Measurable f) (hg : Measurable g) :
    Measurable fun x => f x = g x :=
  measurableSet_setOfPred.1 (measurableSet_eq_fun hf hg)

theorem measurable_coe_lt (d : ℝ≥0) {ζ : α → ℝ≥0∞} (hζ : Measurable ζ) :
    Measurable fun x => (d : ℝ≥0∞) < ζ x :=
  measurableSet_setOfPred.1 (measurableSet_lt measurable_const hζ)

/-- Interval integrability on `[0, d]` of the sections of a jointly measurable function is a
measurable condition. -/
theorem measurable_intervalIntegrable {g : α → ℝ → ℝ}
    (hg : Measurable fun p : α × ℝ => g p.1 p.2) (d : ℝ≥0) :
    Measurable fun x => IntervalIntegrable (g x) volume 0 d := by
  have hsec : ∀ x, Measurable (g x) := fun x => hg.comp (measurable_const.prodMk measurable_id)
  have e : (fun x => IntervalIntegrable (g x) volume 0 d) =
      fun x => ∫⁻ s in Ioc 0 (d : ℝ), ‖g x s‖ₑ < ∞ := by
    funext x
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le d.coe_nonneg]
    exact propext ⟨fun h => h.2, fun h => ⟨(hsec x).aestronglyMeasurable, h⟩⟩
  rw [e]
  have hm : Measurable fun x => ∫⁻ s in Ioc 0 (d : ℝ), ‖g x s‖ₑ :=
    Measurable.lintegral_prod_right' (f := fun p : α × ℝ => ‖g p.1 p.2‖ₑ) hg.enorm
  exact measurableSet_setOfPred.1 (measurableSet_lt hm measurable_const)

/-- Interval integrals over `[0, d]` of the sections of a jointly measurable function are
measurable. -/
theorem measurable_intervalIntegral {g : α → ℝ → ℝ}
    (hg : Measurable fun p : α × ℝ => g p.1 p.2) (d : ℝ≥0) :
    Measurable fun x => ∫ s in (0 : ℝ)..d, g x s := by
  have e : (fun x => ∫ s in (0 : ℝ)..d, g x s) = fun x => ∫ s in Ioc 0 (d : ℝ), g x s :=
    funext fun x => intervalIntegral.integral_of_le d.coe_nonneg
  rw [e]
  exact (hg.stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (Ioc 0 (d : ℝ)))).measurable

theorem measurable_volume_eq_zero {S : Set (α × ℝ)} (hS : MeasurableSet S) :
    Measurable fun x => volume (Prod.mk x ⁻¹' S) = 0 :=
  measurableSet_setOfPred.1 ((measurable_measure_prodMk_left hS) (measurableSet_singleton 0))

/-- `{x | P → x ∈ A}` for a constant proposition `P`. -/
theorem measurable_const_imp (P : Prop) {q : α → Prop} (hq : Measurable q) :
    Measurable fun x => P → q x := measurable_const.imp hq

end Helpers

/-! ### Decoded coordinates and integrands -/

variable {nL nR : ℕ}

theorem measurable_cw_real : Measurable fun p : XCode nL nR × ℝ => cw p.1 p.2.toNNReal :=
  measurable_dec_real measurable_code_w

theorem measurable_cvL_real (i : Fin nL) :
    Measurable fun p : XCode nL nR × ℝ => cvL p.1 i p.2.toNNReal :=
  measurable_dec_real (measurable_code_vL i)

theorem measurable_cvR_real (j : Fin nR) :
    Measurable fun p : XCode nL nR × ℝ => cvR p.1 j p.2.toNNReal :=
  measurable_dec_real (measurable_code_vR j)

theorem measurable_cw_at (t : ℝ≥0) : Measurable fun x : XCode nL nR => cw x t :=
  measurable_dec_at measurable_code_w t

theorem measurable_cvL_at (i : Fin nL) (t : ℝ≥0) :
    Measurable fun x : XCode nL nR => cvL x i t := measurable_dec_at (measurable_code_vL i) t

theorem measurable_cvR_at (j : Fin nR) (t : ℝ≥0) :
    Measurable fun x : XCode nL nR => cvR x j t := measurable_dec_at (measurable_code_vR j) t

theorem measurable_cb_at (t : ℝ≥0) : Measurable fun x : XCode nL nR => cb x t :=
  measurable_dec_at measurable_code_b t

/-- The decoded state at time `t`. -/
def stateAt (x : XCode nL nR) (t : ℝ≥0) : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) :=
  (cw x t, fun i => cvL x i t, fun j => cvR x j t)

theorem measurable_stateAt (t : ℝ≥0) : Measurable fun x : XCode nL nR => stateAt x t :=
  (measurable_cw_at t).prodMk ((measurable_pi_iff.2 fun i => measurable_cvL_at i t).prodMk
    (measurable_pi_iff.2 fun j => measurable_cvR_at j t))

theorem Good.continuousOn_stateAt {x : XCode nL nR} (hx : Good x) :
    ContinuousOn (stateAt x) {t | (t : ℝ≥0∞) < cζ x} :=
  hx.continuousOn_w.prodMk ((continuousOn_pi.2 fun i => hx.continuousOn_vL i).prodMk
    (continuousOn_pi.2 fun j => hx.continuousOn_vR j))

/-- The side ordering of Definition 2.1, as a closed set of states. -/
def ordSet : Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)) :=
  {q | (∀ i j, i ≤ j → q.2.1 j ≤ q.2.1 i) ∧ (∀ i, q.2.1 i ≤ q.1) ∧ (∀ j, q.1 ≤ q.2.2 j) ∧
    ∀ i j, i ≤ j → q.2.2 i ≤ q.2.2 j}

theorem isClosed_ordSet : IsClosed (ordSet : Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ))) := by
  have cL : ∀ i, Continuous fun q : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) => q.2.1 i :=
    fun i => (continuous_apply i).comp continuous_snd.fst
  have cR : ∀ j, Continuous fun q : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) => q.2.2 j :=
    fun j => (continuous_apply j).comp continuous_snd.snd
  unfold ordSet
  simp only [ofPred_and, ofPred_forall]
  exact (isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
    isClosed_le (cL j) (cL i)).inter ((isClosed_iInter fun i => isClosed_le (cL i)
      continuous_fst).inter ((isClosed_iInter fun j => isClosed_le continuous_fst (cR j)).inter
    (isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
      isClosed_le (cR i) (cR j))))

/-- The reciprocal gaps, as functions of a code and a real time. -/
def gapL (x : XCode nL nR) (i : Fin nL) (s : ℝ) : ℝ := (cw x s.toNNReal - cvL x i s.toNNReal)⁻¹
def gapR (x : XCode nL nR) (j : Fin nR) (s : ℝ) : ℝ := (cw x s.toNNReal - cvR x j s.toNNReal)⁻¹

theorem measurable_gapL (i : Fin nL) : Measurable fun p : XCode nL nR × ℝ => gapL p.1 i p.2 :=
  (measurable_cw_real.sub (measurable_cvL_real i)).inv

theorem measurable_gapR (j : Fin nR) : Measurable fun p : XCode nL nR × ℝ => gapR p.1 j p.2 :=
  (measurable_cw_real.sub (measurable_cvR_real j)).inv

/-- Integrability of the reciprocal gaps on `[0, t]`. -/
def IntAt (x : XCode nL nR) (t : ℝ≥0) : Prop :=
  (∀ i, IntervalIntegrable (gapL x i) volume 0 t) ∧ ∀ j, IntervalIntegrable (gapR x j) volume 0 t

theorem measurable_intAt (t : ℝ≥0) : Measurable fun x : XCode nL nR => IntAt x t :=
  (Measurable.forall fun i => measurable_intervalIntegrable (measurable_gapL i) t).and
    (Measurable.forall fun j => measurable_intervalIntegrable (measurable_gapR j) t)

/-- The defects of the integrated equations of Definition 2.1 at time `t`. -/
def defect (a : ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    (x : XCode nL nR) (t : ℝ≥0) : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) :=
  (cw x t - (Real.sqrt a * cb x t
      + (∑ i, ∫ s in (0 : ℝ)..t, ρL i / (cw x s.toNNReal - cvL x i s.toNNReal))
      + (∑ j, ∫ s in (0 : ℝ)..t, ρR j / (cw x s.toNNReal - cvR x j s.toNNReal))),
    fun i => cvL x i t - (xL i + ∫ s in (0 : ℝ)..t, 2 / (cvL x i s.toNNReal - cw x s.toNNReal)),
    fun j => cvR x j t - (xR j + ∫ s in (0 : ℝ)..t, 2 / (cvR x j s.toNNReal - cw x s.toNNReal)))

theorem measurable_defect (a : ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ)
    (ρR : Fin nR → ℝ) (t : ℝ≥0) :
    Measurable fun x : XCode nL nR => defect a xL xR ρL ρR x t := by
  have hL : ∀ i, Measurable fun x : XCode nL nR =>
      ∫ s in (0 : ℝ)..t, ρL i / (cw x s.toNNReal - cvL x i s.toNNReal) := fun i =>
    measurable_intervalIntegral (g := fun x s => ρL i / (cw x s.toNNReal - cvL x i s.toNNReal))
      (measurable_const.div (measurable_cw_real.sub (measurable_cvL_real i))) t
  have hR : ∀ j, Measurable fun x : XCode nL nR =>
      ∫ s in (0 : ℝ)..t, ρR j / (cw x s.toNNReal - cvR x j s.toNNReal) := fun j =>
    measurable_intervalIntegral (g := fun x s => ρR j / (cw x s.toNNReal - cvR x j s.toNNReal))
      (measurable_const.div (measurable_cw_real.sub (measurable_cvR_real j))) t
  have fL : ∀ i, Measurable fun x : XCode nL nR =>
      ∫ s in (0 : ℝ)..t, 2 / (cvL x i s.toNNReal - cw x s.toNNReal) := fun i =>
    measurable_intervalIntegral (g := fun x s => 2 / (cvL x i s.toNNReal - cw x s.toNNReal))
      (measurable_const.div ((measurable_cvL_real i).sub measurable_cw_real)) t
  have fR : ∀ j, Measurable fun x : XCode nL nR =>
      ∫ s in (0 : ℝ)..t, 2 / (cvR x j s.toNNReal - cw x s.toNNReal) := fun j =>
    measurable_intervalIntegral (g := fun x s => 2 / (cvR x j s.toNNReal - cw x s.toNNReal))
      (measurable_const.div ((measurable_cvR_real j).sub measurable_cw_real)) t
  refine ((measurable_cw_at t).sub ((measurable_const.mul (measurable_cb_at t)).add
    (Finset.measurable_sum _ fun i _ => hL i) |>.add
    (Finset.measurable_sum _ fun j _ => hR j))).prodMk
    ((measurable_pi_iff.2 fun i => (measurable_cvL_at i t).sub (measurable_const.add (fL i))).prodMk
      (measurable_pi_iff.2 fun j => (measurable_cvR_at j t).sub (measurable_const.add (fR j))))

/-- The dyadic form of "the threshold condition fails before `ζ`". -/
def NThr (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (x : XCode nL nR) : Prop :=
  ∀ n₀ k₀, (dyad n₀ k₀ : ℝ≥0∞) < cζ x →
    (∀ S : Finset (Fin nL), ∑ i ∈ S, ρL i ≤ -2 → ¬ ∃ p : ℕ, ∀ m : ℕ, ∃ n k,
      dyad n k ≤ dyad n₀ k₀ ∧ NearSide S p m (cw x (dyad n k)) fun i => cvL x i (dyad n k)) ∧
    ∀ S : Finset (Fin nR), ∑ j ∈ S, ρR j ≤ -2 → ¬ ∃ p : ℕ, ∀ m : ℕ, ∃ n k,
      dyad n k ≤ dyad n₀ k₀ ∧ NearSide S p m (cw x (dyad n k)) fun j => cvR x j (dyad n k)

theorem measurable_nearSide {n' : ℕ} (S : Finset (Fin n')) (p m : ℕ) {w : XCode nL nR → ℝ}
    {u : Fin n' → XCode nL nR → ℝ} (hw : Measurable w) (hu : ∀ i, Measurable (u i)) :
    Measurable fun x => NearSide S p m (w x) fun i => u i x := by
  unfold NearSide
  refine (Measurable.forall fun i => measurable_const_imp _ ?_).and
    (Measurable.forall fun i => measurable_const_imp _ ?_)
  · exact measurable_lt' (continuous_abs.measurable.comp ((hu i).sub hw)) measurable_const
  · exact measurable_lt' measurable_const (continuous_abs.measurable.comp ((hu i).sub hw))

theorem measurable_nThr (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) :
    Measurable fun x : XCode nL nR => NThr ρL ρR x := by
  unfold NThr
  refine Measurable.forall fun n₀ => Measurable.forall fun k₀ =>
    (measurable_coe_lt _ measurable_cζ).imp (Measurable.and ?_ ?_)
  · refine Measurable.forall fun S => measurable_const_imp _ (Measurable.not ?_)
    refine Measurable.exists fun p => Measurable.forall fun m => Measurable.exists fun n =>
      Measurable.exists fun k => measurable_const.and ?_
    exact measurable_nearSide S p m (measurable_cw_at _) fun i => measurable_cvL_at i _
  · refine Measurable.forall fun S => measurable_const_imp _ (Measurable.not ?_)
    refine Measurable.exists fun p => Measurable.forall fun m => Measurable.exists fun n =>
      Measurable.exists fun k => measurable_const.and ?_
    exact measurable_nearSide S p m (measurable_cw_at _) fun j => measurable_cvR_at j _

/-! ### The relation -/

/-- The countable conditions that are equivalent, on `Good ∩ LimThr`, to the frozen predicate. -/
def MSet (a : ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) :
    Set (XCode nL nR) :=
  {x | (cw x 0 = 0 ∧ (∀ i, cvL x i 0 = xL i) ∧ ∀ j, cvR x j 0 = xR j) ∧
    (∀ n k, (dyad n k : ℝ≥0∞) < cζ x → stateAt x (dyad n k) ∈ ordSet) ∧
    (∀ n k, (dyad n k : ℝ≥0∞) < cζ x → IntAt x (dyad n k)) ∧
    (∀ n k, (dyad n k : ℝ≥0∞) < cζ x → defect a xL xR ρL ρR x (dyad n k) = 0) ∧
    (∀ i, volume {s : ℝ | 0 ≤ s ∧ (s.toNNReal : ℝ≥0∞) < cζ x ∧
      cw x s.toNNReal = cvL x i s.toNNReal} = 0) ∧
    (∀ j, volume {s : ℝ | 0 ≤ s ∧ (s.toNNReal : ℝ≥0∞) < cζ x ∧
      cw x s.toNNReal = cvR x j s.toNNReal} = 0) ∧
    NThr ρL ρR x ∧ (cζ x = 0 → ForceWord.ThresholdCondition ρL ρR 0 xL xR)}

theorem measurable_collision {f g : XCode nL nR × ℝ → ℝ} (hf : Measurable f)
    (hg : Measurable g) :
    Measurable fun x : XCode nL nR => volume {s : ℝ | 0 ≤ s ∧ (s.toNNReal : ℝ≥0∞) < cζ x ∧
      f (x, s) = g (x, s)} = 0 := by
  have hS : MeasurableSet {p : XCode nL nR × ℝ | 0 ≤ p.2 ∧ (p.2.toNNReal : ℝ≥0∞) < cζ p.1 ∧
      f p = g p} := by
    refine (measurableSet_le measurable_const measurable_snd).inter
      ((measurableSet_lt (measurable_coe_nnreal_ennreal.comp
        (measurable_real_toNNReal.comp measurable_snd)) (measurable_cζ.comp measurable_fst)).inter
      (measurableSet_eq_fun hf hg))
  exact measurable_volume_eq_zero hS

theorem measurableSet_mSet (a : ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ)
    (ρR : Fin nR → ℝ) : MeasurableSet (MSet a xL xR ρL ρR) := by
  refine measurableSet_setOfPred.2 ?_
  refine Measurable.and ?_ (Measurable.and ?_ (Measurable.and ?_ (Measurable.and ?_
    (Measurable.and ?_ (Measurable.and ?_ (Measurable.and ?_ ?_))))))
  · exact (measurable_eq_real (measurable_cw_at 0) measurable_const).and
      ((Measurable.forall fun i => measurable_eq_real (measurable_cvL_at i 0) measurable_const).and
        (Measurable.forall fun j => measurable_eq_real (measurable_cvR_at j 0) measurable_const))
  · exact Measurable.forall fun n => Measurable.forall fun k =>
      (measurable_coe_lt _ measurable_cζ).imp
        (measurableSet_setOfPred.1 (measurable_stateAt _ isClosed_ordSet.measurableSet))
  · exact Measurable.forall fun n => Measurable.forall fun k =>
      (measurable_coe_lt _ measurable_cζ).imp (measurable_intAt _)
  · exact Measurable.forall fun n => Measurable.forall fun k =>
      (measurable_coe_lt _ measurable_cζ).imp
        (measurableSet_setOfPred.1 (measurable_defect a xL xR ρL ρR _ (measurableSet_singleton 0)))
  · exact Measurable.forall fun i => measurable_collision measurable_cw_real (measurable_cvL_real i)
  · exact Measurable.forall fun j => measurable_collision measurable_cw_real (measurable_cvR_real j)
  · exact measurable_nThr ρL ρR
  · exact (measurableSet_setOfPred.1 (measurable_cζ (measurableSet_singleton 0))).imp
      measurable_const

/-- At a finite positive lifetime, the dyadic limit of the state is a threshold state. -/
def LimThr (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (x : XCode nL nR) : Prop :=
  0 < cζ x → cζ x < ⊤ → ForceWord.ThresholdCondition ρL ρR (limW x) (limVL x) (limVR x)

theorem measurable_limThr (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) :
    Measurable fun x : XCode nL nR => LimThr ρL ρR x :=
  (measurableSet_setOfPred.1 (measurableSet_lt measurable_const measurable_cζ)).imp
    ((measurableSet_setOfPred.1 (measurableSet_lt measurable_cζ measurable_const)).imp
      (measurableSet_setOfPred.1 (measurable_limState (measurableSet_thr ρL ρR))))

/-- **The solution relation** on codes. -/
def Rel (a : ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) :
    Set (XCode nL nR) :=
  {x | Good x ∧ LimThr ρL ρR x ∧
    IsIntegratedSLEPath a xL xR ρL ρR (cw x) (cvL x) (cvR x) (cb x) (cζ x)}

section Equiv

variable {a : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}

theorem defect_eq_zero_iff {x : XCode nL nR} {t : ℝ≥0} :
    defect a xL xR ρL ρR x t = 0 ↔
      (cw x t = Real.sqrt a * cb x t
        + (∑ i, ∫ s in (0 : ℝ)..t, ρL i / (cw x s.toNNReal - cvL x i s.toNNReal))
        + (∑ j, ∫ s in (0 : ℝ)..t, ρR j / (cw x s.toNNReal - cvR x j s.toNNReal))) ∧
      (∀ i, cvL x i t = xL i + ∫ s in (0 : ℝ)..t, 2 / (cvL x i s.toNNReal - cw x s.toNNReal)) ∧
      ∀ j, cvR x j t = xR j + ∫ s in (0 : ℝ)..t, 2 / (cvR x j s.toNNReal - cw x s.toNNReal) := by
  unfold defect
  simp only [Prod.ext_iff, Prod.fst_zero, Prod.snd_zero, funext_iff, Pi.zero_apply, sub_eq_zero]

/-- The left side: the marks of `S` at the driver at a time `t < ζ` produce the dyadic
near-configurations. -/
theorem Good.continuousOn_Iic {x : XCode nL nR} (hx : Good x) {n₀ k₀ : ℕ}
    (h : (dyad n₀ k₀ : ℝ≥0∞) < cζ x) :
    ContinuousOn (cw x) (Iic (dyad n₀ k₀)) ∧ (∀ i, ContinuousOn (cvL x i) (Iic (dyad n₀ k₀))) ∧
      ∀ j, ContinuousOn (cvR x j) (Iic (dyad n₀ k₀)) :=
  ⟨(hx.2 n₀ k₀ h).1.continuousOn, fun i => ((hx.2 n₀ k₀ h).2.1 i).continuousOn,
    fun j => ((hx.2 n₀ k₀ h).2.2 j).continuousOn⟩

theorem not_threshold_iff_nThr {x : XCode nL nR} (hx : Good x) :
    (∀ t : ℝ≥0, (t : ℝ≥0∞) < cζ x →
      ¬ ForceWord.ThresholdCondition ρL ρR (cw x t) (fun i => cvL x i t) fun j => cvR x j t) ↔
      NThr ρL ρR x := by
  constructor
  · intro hnt n₀ k₀ hd₀
    obtain ⟨cw', cL', cR'⟩ := hx.continuousOn_Iic hd₀
    refine ⟨fun S hS hex => ?_, fun S hS hex => ?_⟩
    · obtain ⟨t, htT, hat⟩ := (exists_atSide_iff cw' cL').2 hex
      refine hnt t (lt_of_le_of_lt (by exact_mod_cast htT) hd₀) (Or.inl ?_)
      rw [sum_filter_eq_of_atSide ρL hat]; exact hS
    · obtain ⟨t, htT, hat⟩ := (exists_atSide_iff cw' cR').2 hex
      refine hnt t (lt_of_le_of_lt (by exact_mod_cast htT) hd₀) (Or.inr ?_)
      rw [sum_filter_eq_of_atSide ρR hat]; exact hS
  · intro hN t ht hthr
    obtain ⟨n₀, k₀, htd, hd₀⟩ := exists_dyad_btwn ht
    obtain ⟨cw', cL', cR'⟩ := hx.continuousOn_Iic hd₀
    rcases hthr with hthr | hthr
    · refine (hN n₀ k₀ hd₀).1 _ hthr ((exists_atSide_iff cw' cL').1 ⟨t, htd.le, ?_⟩)
      exact atSide_filter _ _
    · refine (hN n₀ k₀ hd₀).2 _ hthr ((exists_atSide_iff cw' cR').1 ⟨t, htd.le, ?_⟩)
      exact atSide_filter _ _

/-- **On `Good ∩ LimThr`, the frozen predicate is the countable condition `MSet`.** -/
theorem isIntegratedSLEPath_iff_mem_mSet {x : XCode nL nR} (hx : Good x)
    (hL : LimThr ρL ρR x) :
    IsIntegratedSLEPath a xL xR ρL ρR (cw x) (cvL x) (cvR x) (cb x) (cζ x) ↔
      x ∈ MSet a xL xR ρL ρR := by
  constructor
  · intro h
    have hp := h.isForcePath
    have hd := h.driverEq
    refine ⟨⟨hp.w_zero, hp.vL_zero, hp.vR_zero⟩, fun n k hk => ?_, fun n k hk => ?_,
      fun n k hk => ?_, hp.volume_collisionL, hp.volume_collisionR,
      (not_threshold_iff_nThr hx).1 fun t ht => hp.not_threshold ht, hp.threshold_of_eq_zero⟩
    · exact ⟨fun i j hij => hp.antitone_vL hk hij, hp.vL_le_w hk, hp.w_le_vR hk,
        fun i j hij => hp.monotone_vR hk hij⟩
    · exact ⟨fun i => hp.integrable_gapL hk i, fun j => hp.integrable_gapR hk j⟩
    · exact defect_eq_zero_iff.2 ⟨hd _ hk, fun i => hp.vL_eq hk i, fun j => hp.vR_eq hk j⟩
  · rintro ⟨⟨h0w, h0L, h0R⟩, hord, hint, hdef, hcL, hcR, hN, hseed⟩
    have hInt : ∀ t : ℝ≥0, (t : ℝ≥0∞) < cζ x → IntAt x t := fun t ht =>
      ⟨fun i => forall_lt_intervalIntegrable (fun n k hk => (hint n k hk).1 i) ht,
        fun j => forall_lt_intervalIntegrable (fun n k hk => (hint n k hk).2 j) ht⟩
    have hOrd : ∀ t : ℝ≥0, (t : ℝ≥0∞) < cζ x → stateAt x t ∈ ordSet := fun t ht =>
      forall_lt_of_forall_dyad hx.continuousOn_stateAt isClosed_ordSet hord ht
    have hprimL : ∀ (c : ℝ) (i : Fin nL), ContinuousOn
        (fun t : ℝ≥0 => ∫ s in (0 : ℝ)..t, c / (cw x s.toNNReal - cvL x i s.toNNReal))
        {t | (t : ℝ≥0∞) < cζ x} := fun c i =>
      continuousOn_primitive fun t ht => by
        simpa only [div_eq_mul_inv, gapL] using ((hInt t ht).1 i).const_mul c
    have hprimR : ∀ (c : ℝ) (j : Fin nR), ContinuousOn
        (fun t : ℝ≥0 => ∫ s in (0 : ℝ)..t, c / (cw x s.toNNReal - cvR x j s.toNNReal))
        {t | (t : ℝ≥0∞) < cζ x} := fun c j =>
      continuousOn_primitive fun t ht => by
        simpa only [div_eq_mul_inv, gapR] using ((hInt t ht).2 j).const_mul c
    have hfL : ∀ i : Fin nL, ContinuousOn
        (fun t : ℝ≥0 => ∫ s in (0 : ℝ)..t, 2 / (cvL x i s.toNNReal - cw x s.toNNReal))
        {t | (t : ℝ≥0∞) < cζ x} := fun i =>
      continuousOn_primitive fun t ht => by
        simpa only [two_div_sub_eq, gapL] using ((hInt t ht).1 i).const_mul (-2)
    have hfR : ∀ j : Fin nR, ContinuousOn
        (fun t : ℝ≥0 => ∫ s in (0 : ℝ)..t, 2 / (cvR x j s.toNNReal - cw x s.toNNReal))
        {t | (t : ℝ≥0∞) < cζ x} := fun j =>
      continuousOn_primitive fun t ht => by
        simpa only [two_div_sub_eq, gapR] using ((hInt t ht).2 j).const_mul (-2)
    have hdefc : ContinuousOn (defect a xL xR ρL ρR x) {t | (t : ℝ≥0∞) < cζ x} := by
      unfold defect
      refine (hx.continuousOn_w.sub ((continuousOn_const.mul hx.continuous_b.continuousOn).add
        (continuousOn_finsetSum _ fun i _ => hprimL (ρL i) i) |>.add
        (continuousOn_finsetSum _ fun j _ => hprimR (ρR j) j))).prodMk
        ((continuousOn_pi.2 fun i => (hx.continuousOn_vL i).sub
          (continuousOn_const.add (hfL i))).prodMk
        (continuousOn_pi.2 fun j => (hx.continuousOn_vR j).sub
          (continuousOn_const.add (hfR j))))
    have hEq : ∀ t : ℝ≥0, (t : ℝ≥0∞) < cζ x → defect a xL xR ρL ρR x t = 0 := fun t ht =>
      forall_lt_of_forall_dyad hdefc isClosed_singleton hdef ht
    have hp : IsForcePath xL xR ρL ρR (cw x) (cvL x) (cvR x) (cζ x) :=
      { w_zero := h0w
        vL_zero := h0L
        vR_zero := h0R
        continuousOn_w := hx.continuousOn_w
        continuousOn_vL := hx.continuousOn_vL
        continuousOn_vR := hx.continuousOn_vR
        antitone_vL := fun {t} ht _ _ hij => (hOrd t ht).1 _ _ hij
        vL_le_w := fun {t} ht => (hOrd t ht).2.1
        w_le_vR := fun {t} ht => (hOrd t ht).2.2.1
        monotone_vR := fun {t} ht _ _ hij => (hOrd t ht).2.2.2 _ _ hij
        integrable_gapL := fun {t} ht => (hInt t ht).1
        integrable_gapR := fun {t} ht => (hInt t ht).2
        vL_eq := fun {t} ht => (defect_eq_zero_iff.1 (hEq t ht)).2.1
        vR_eq := fun {t} ht => (defect_eq_zero_iff.1 (hEq t ht)).2.2
        volume_collisionL := hcL
        volume_collisionR := hcR
        not_threshold := fun {t} ht => (not_threshold_iff_nThr hx).2 hN t ht
        threshold_of_eq_zero := hseed
        threshold_of_tendsto := fun {T} hT hζ {w₀ vL₀ vR₀} hlim => by
          have hq := lim_eq_of_tendsto hT hζ hlim
          have h0 : 0 < cζ x := by rw [← hζ]; exact_mod_cast hT
          have hfin : cζ x < ⊤ := by rw [← hζ]; exact ENNReal.coe_lt_top
          have := hL h0 hfin
          simp only [Prod.mk.injEq] at hq
          obtain ⟨h1, h2, h3⟩ := hq
          rw [h1, h2, h3] at this
          exact this }
    exact IsIntegratedSLEPath.iff_isForcePath_and_driverEq.2
      ⟨hp, fun t ht => (defect_eq_zero_iff.1 (hEq t ht)).1⟩

end Equiv

/-- **The solution relation is measurable.** -/
theorem measurableSet_rel (a : ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ)
    (ρR : Fin nR → ℝ) : MeasurableSet (Rel a xL xR ρL ρR) := by
  have e : Rel a xL xR ρL ρR = ({x : XCode nL nR | Good x} ∩ {x | LimThr ρL ρR x}) ∩
      MSet a xL xR ρL ρR := by
    ext x
    exact ⟨fun ⟨hg, hl, hp⟩ => ⟨⟨hg, hl⟩, (isIntegratedSLEPath_iff_mem_mSet hg hl).1 hp⟩,
      fun ⟨⟨hg, hl⟩, hm⟩ => ⟨hg, hl, (isIntegratedSLEPath_iff_mem_mSet hg hl).2 hm⟩⟩
  rw [e]
  exact (measurableSet_good.inter (measurableSet_setOfPred.2 (measurable_limThr ρL ρR))).inter
    (measurableSet_mSet a xL xR ρL ρR)

end Assembly

end Sec2

end InteractingSLE
