/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2BjExit

/-!
# The near exit rule with labels read from the record (decision D16: the jointly measurable stop)

Packet PROVE-GW2-BUF (round 11). D16 decodes the near family's shape (countable range) and positions (measurable on
each shape cell) from the stage record. So the near stop is the exit rule with record-dependent labels and buffer.
It must be a measurable path rule on `RecData × (ℝ≥0 → ℝ)`.

* **`measurable_rightImgRead_joint`**, **`measurable_imgStateRead_joint`**: the image-state readout is jointly
  measurable in (labels, path). The readout depends on a mark only through `x < q`.
* `bufGaugeRec`, `exitRuleRec`: the buffer gauge and the exit rule with labels `L r`, `R r` read from the record.
  * **`isPathRule_exitRuleRec`** and **`measurable_exitRuleRec`** (for measurable label readers).
  * **`exitRuleRec_eq`**: at each record, `exitRuleRec` IS round 7's `exitRule` with those labels (`hitRule_congr`).
    So `exitRule_spec` and the collision/contact lemmas apply unchanged.
* **`shapeStop`**: the near stop across shape cells (labels padded by `0`, buffer chosen by the shape).
  **`measurable_shapeStop`**, **`isPathRule_shapeStop`**, `shapeStop_eq`.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW2Bh

open Exist.StagedLaw Supp8.GB6 Supp8.GB6.HullId Supp8.GB6.RelDrv.Version MartChar.RealFlow

/-! ### Joint measurability of the readout -/

theorem measurable_rightImgRead_joint (T : ℝ≥0) :
    Measurable fun p : ℝ × (ℝ≥0 → ℝ) => rightImgRead T p.1 p.2 := by
  classical
  refine measurable_ereal_toReal.comp (Measurable.iInf fun q => ?_)
  refine Measurable.ite ?_ (measurable_coe_real_ereal.comp ((measurable_gImgRead T q).comp measurable_snd))
    measurable_const
  exact (measurableSet_lt measurable_fst measurable_const).inter (measurable_snd (measurableSet_aliveRead T q))

theorem measurable_imgStateRead_joint {nL nR : ℕ} (T : ℝ≥0) :
    Measurable fun p : (Fin nL → ℝ) × (Fin nR → ℝ) × (ℝ≥0 → ℝ) => imgStateRead p.1 p.2.1 T p.2.2 := by
  have hneg : Measurable fun w : ℝ≥0 → ℝ => fun u => -w u :=
    measurable_pi_iff.2 fun u => (measurable_pi_apply u).neg
  have hA : ∀ i : Fin nL, Measurable fun p : (Fin nL → ℝ) × (Fin nR → ℝ) × (ℝ≥0 → ℝ) =>
      -rightImgRead T (-p.1 i) (fun u => -p.2.2 u) := fun i => by
    have h1 : Measurable fun p : (Fin nL → ℝ) × (Fin nR → ℝ) × (ℝ≥0 → ℝ) =>
        ((-p.1 i, fun u => -p.2.2 u) : ℝ × (ℝ≥0 → ℝ)) :=
      ((measurable_pi_apply i).comp measurable_fst).neg.prodMk (hneg.comp (measurable_snd.comp measurable_snd))
    exact ((measurable_rightImgRead_joint T).comp h1).neg
  have hB : ∀ j : Fin nR, Measurable fun p : (Fin nL → ℝ) × (Fin nR → ℝ) × (ℝ≥0 → ℝ) =>
      rightImgRead T (p.2.1 j) p.2.2 := fun j => by
    have h1 : Measurable fun p : (Fin nL → ℝ) × (Fin nR → ℝ) × (ℝ≥0 → ℝ) =>
        ((p.2.1 j, p.2.2) : ℝ × (ℝ≥0 → ℝ)) :=
      ((measurable_pi_apply j).comp (measurable_fst.comp measurable_snd)).prodMk (measurable_snd.comp measurable_snd)
    exact (measurable_rightImgRead_joint T).comp h1
  exact ((measurable_pi_apply T).comp (measurable_snd.comp measurable_snd)).prodMk
    ((measurable_pi_iff.2 hA).prodMk (measurable_pi_iff.2 hB))

/-! ### The exit rule with record-read labels -/

/-- The hit rule at a point depends on the readout along that point only. -/
theorem hitRule_congr {G G' : GaugeReadout} {ε : RecData → ℝ} {c : ℝ≥0} {x : RecData × (ℝ≥0 → ℝ)}
    (h : ∀ u, G u x = G' u x) : hitRule G ε c x = hitRule G' ε c x := by
  have hset : ∀ t, (x ∈ prefixHitSet G ε c t ↔ x ∈ prefixHitSet G' ε c t) := fun t => by
    simp only [prefixHitSet, Set.mem_ofPred_eq, h]
  have hinf : hitInf G ε c x = hitInf G' ε c x := by
    unfold hitInf
    congr 1
    ext t
    exact hset t
  classical
  unfold hitRule
  rw [hinf]
  exact if_congr (hset _) rfl rfl

variable {nL nR : ℕ}

/-- **The buffer gauge with labels read from the record.** -/
def bufGaugeRec (L : RecData → Fin nL → ℝ) (R : RecData → Fin nR → ℝ)
    (B : Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ))) (a : ℝ≥0) (b : ℝ) : GaugeReadout :=
  fun u p => Metric.infDist (imgStateRead (L p.1) (R p.1) (a * u) (scaledPath a b p.2)) Bᶜ

/-- **The exit rule with labels read from the record.** -/
def exitRuleRec (L : RecData → Fin nL → ℝ) (R : RecData → Fin nR → ℝ)
    (B : Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ))) (a : ℝ≥0) (b : ℝ) (c : ℝ≥0) :
    RecData × (ℝ≥0 → ℝ) → ℝ≥0∞ :=
  hitRule (bufGaugeRec L R B a b) (fun _ => 0) c

theorem isCausal_bufGaugeRec (L : RecData → Fin nL → ℝ) (R : RecData → Fin nR → ℝ)
    (B : Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ))) {a : ℝ≥0} (ha : 0 < a) (b : ℝ) :
    IsCausal (bufGaugeRec L R B a b) := by
  intro u r w w' h
  show Metric.infDist (imgStateRead (L r) (R r) (a * u) (scaledPath a b w)) Bᶜ =
    Metric.infDist (imgStateRead (L r) (R r) (a * u) (scaledPath a b w')) Bᶜ
  rw [imgStateRead_congr (L r) (R r) (a * u) fun s hs => ?_]
  have hsu : s / a ≤ u := (div_le_iff₀ ha).2 (by rwa [mul_comm])
  simp only [scaledPath, h _ hsu]

theorem measurable_bufGaugeRec {L : RecData → Fin nL → ℝ} {R : RecData → Fin nR → ℝ} (hL : Measurable L)
    (hR : Measurable R) (B : Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ))) (a : ℝ≥0) (b : ℝ) (u : ℝ≥0) :
    Measurable (bufGaugeRec L R B a b u) :=
  (Metric.continuous_infDist_pt _).measurable.comp ((measurable_imgStateRead_joint (a * u)).comp
    ((hL.comp measurable_fst).prodMk ((hR.comp measurable_fst).prodMk
      ((measurable_scaledPath a b).comp measurable_snd))))

theorem isPathRule_exitRuleRec (L : RecData → Fin nL → ℝ) (R : RecData → Fin nR → ℝ)
    (B : Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ))) {a : ℝ≥0} (ha : 0 < a) (b : ℝ) (c : ℝ≥0) :
    IsPathRule (exitRuleRec L R B a b c) :=
  isPathRule_hitRule (isCausal_bufGaugeRec L R B ha b)

theorem measurable_exitRuleRec {L : RecData → Fin nL → ℝ} {R : RecData → Fin nR → ℝ} (hL : Measurable L)
    (hR : Measurable R) (B : Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ))) (a : ℝ≥0) (b : ℝ) (c : ℝ≥0) :
    Measurable (exitRuleRec L R B a b c) :=
  measurable_hitRule (measurable_bufGaugeRec hL hR B a b) measurable_const

/-- **At each record, the record-label exit rule is the exit rule with those labels.** -/
theorem exitRuleRec_eq (L : RecData → Fin nL → ℝ) (R : RecData → Fin nR → ℝ)
    (B : Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ))) (a : ℝ≥0) (b : ℝ) (c : ℝ≥0) (r : RecData) (w : ℝ≥0 → ℝ) :
    exitRuleRec L R B a b c (r, w) = exitRule (L r) (R r) B a b c (r, w) :=
  hitRule_congr fun _ => rfl

/-! ### The near stop across shape cells -/

/-- The shape of a near family: `(nL, nR, mL, mR, goLeft)`. -/
abbrev NearShape := ℕ × ℕ × ℕ × ℕ × Bool

/-- The near stop at a given shape cell, uncurried. -/
def shapeStopF (Bsh : ∀ K : NearShape, Set (ℝ × (Fin K.1 → ℝ) × (Fin K.2.1 → ℝ))) (posL posR : RecData → ℕ → ℝ)
    (a : ℝ≥0) (b : ℝ) (c : ℝ≥0) (q : (RecData × (ℝ≥0 → ℝ)) × NearShape) : ℝ≥0∞ :=
  exitRuleRec (nL := q.2.1) (nR := q.2.2.1) (fun r i => posL r i) (fun r j => posR r j) (Bsh q.2) a b c q.1

/-- **The near stop across shape cells**: the exit rule with the padded positions of the record's shape cell and the
buffer chosen by the shape. -/
def shapeStop (Bsh : ∀ K : NearShape, Set (ℝ × (Fin K.1 → ℝ) × (Fin K.2.1 → ℝ))) (shape : RecData → NearShape)
    (posL posR : RecData → ℕ → ℝ) (a : ℝ≥0) (b : ℝ) (c : ℝ≥0) : RecData × (ℝ≥0 → ℝ) → ℝ≥0∞ :=
  fun p => shapeStopF Bsh posL posR a b c (p, shape p.1)

theorem measurable_shapeStopF (Bsh : ∀ K : NearShape, Set (ℝ × (Fin K.1 → ℝ) × (Fin K.2.1 → ℝ)))
    {posL posR : RecData → ℕ → ℝ} (hL : Measurable posL) (hR : Measurable posR) (a : ℝ≥0) (b : ℝ) (c : ℝ≥0) :
    Measurable (shapeStopF Bsh posL posR a b c) := by
  refine measurable_from_prod_countable_left fun K => ?_
  show Measurable (exitRuleRec (nL := K.1) (nR := K.2.1) (fun r i => posL r i) (fun r j => posR r j) (Bsh K) a b c)
  exact measurable_exitRuleRec (measurable_pi_iff.2 fun i => (measurable_pi_apply (i : ℕ)).comp hL)
    (measurable_pi_iff.2 fun j => (measurable_pi_apply (j : ℕ)).comp hR) (Bsh K) a b c

theorem measurable_shapeStop (Bsh : ∀ K : NearShape, Set (ℝ × (Fin K.1 → ℝ) × (Fin K.2.1 → ℝ)))
    {shape : RecData → NearShape} (hsh : Measurable shape) {posL posR : RecData → ℕ → ℝ} (hL : Measurable posL)
    (hR : Measurable posR) (a : ℝ≥0) (b : ℝ) (c : ℝ≥0) : Measurable (shapeStop Bsh shape posL posR a b c) :=
  (measurable_shapeStopF Bsh hL hR a b c).comp (measurable_id.prodMk (hsh.comp measurable_fst))

theorem isPathRule_shapeStop (Bsh : ∀ K : NearShape, Set (ℝ × (Fin K.1 → ℝ) × (Fin K.2.1 → ℝ)))
    (shape : RecData → NearShape) (posL posR : RecData → ℕ → ℝ) {a : ℝ≥0} (ha : 0 < a) (b : ℝ) (c : ℝ≥0) :
    IsPathRule (shapeStop Bsh shape posL posR a b c) := fun r w w' h =>
  isPathRule_exitRuleRec (nL := (shape r).1) (nR := (shape r).2.1) (fun r i => posL r i) (fun r j => posR r j)
    (Bsh (shape r)) ha b c r w w' h

/-- **At each record, the near stop is the exit rule of that record's cell.** -/
theorem shapeStop_eq (Bsh : ∀ K : NearShape, Set (ℝ × (Fin K.1 → ℝ) × (Fin K.2.1 → ℝ)))
    (shape : RecData → NearShape) (posL posR : RecData → ℕ → ℝ) (a : ℝ≥0) (b : ℝ) (c : ℝ≥0) (r : RecData)
    (w : ℝ≥0 → ℝ) :
    shapeStop Bsh shape posL posR a b c (r, w) =
      exitRule (fun i : Fin (shape r).1 => posL r i) (fun j : Fin (shape r).2.1 => posR r j) (Bsh (shape r)) a b c
        (r, w) :=
  exitRuleRec_eq _ _ _ a b c r w

end InteractingSLE.Theorem14.GW2Bh
