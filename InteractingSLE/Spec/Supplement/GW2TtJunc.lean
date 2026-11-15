/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SdpNear

/-!
# Decision D37: the junctions of a stage word against the cumulative driver displacement

Packet PROVE-GW2-RELDET (round 31). D37 asks for the lower, rightward near structure (`NearStructBot`) on J32's alive
histories. By SDE's `nearStructBot_of_sideInv`, its far-junction clause is `3√s ≤ junctionR` (and, through the mirror
on odd histories, `3√s ≤ −junctionL`). The junctions are the root's two sides carried by the pieces' flows; in
absolute coordinates the right one only moves right and the left one only moves left. So, along a past:

* `pastDrift`: the cumulative displacement of the pieces' drivers after the first (root) piece;
* **`junctionR_first_sub_le`**: `junctionR 1 − drift ≤ junctionR (n + 1)`;
* **`junctionL_le_first_sub`**: `junctionL (n + 1) ≤ junctionL 1 − drift`.

With J32's tests, the sample-frame displacement at every stage start after the root stage is in `(7/4, 9/4)` toward
the side opposite to the next test, so the sample-frame right junction is at least the root prefix's junction on that
side plus `7/4` (sample units). This is the deterministic core of D37's corrected statement (handoff, round 31).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal

universe v

namespace InteractingSLE.Theorem14.GW2Rd

open Restart Exist.Staged Exist.StagedLaw Sec7.StripSideHeightProb GW2TipSystem.RootH10 MartChar.RealFlow GW2Sdp

/-! ### One piece -/

/-- A right point is carried to the right of its position minus the driver's displacement. -/
theorem sub_le_markPos_of_nonneg {w : ℝ → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) {T : ℝ} (hT : 0 ≤ T) {a : ℝ}
    (ha : 0 ≤ a) : a - w T ≤ markPos w T a := by
  have h1 := Sec5.CrossCond.Gen.rightImg_sub_le_markPos_of_nonneg hw hw0 hT ha
  have h2 : a ≤ rightImg w a T := by
    have := rightImg_mono_time hw a le_rfl hT
    rwa [rightImg_zero hw hw0 ha] at this
  linarith

/-- A left point is carried to the left of its position minus the driver's displacement. -/
theorem markPosL_le_sub_of_nonpos {w : ℝ → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) {T : ℝ} (hT : 0 ≤ T) {a : ℝ}
    (ha : a ≤ 0) : markPosL w T a ≤ a - w T := by
  have h1 := Sec5.CrossCond.Gen.rightImg_sub_le_markPos_of_nonneg (w := fun s => -w s) hw.neg (by simp [hw0])
    hT (neg_nonneg.2 ha)
  have h2 : -a ≤ rightImg (fun s => -w s) (-a) T := by
    have := rightImg_mono_time (w := fun s => -w s) hw.neg (-a) le_rfl hT
    rwa [rightImg_zero (w := fun s => -w s) hw.neg (by simp [hw0]) (neg_nonneg.2 ha)] at this
  unfold markPosL
  linarith

/-! ### Along a past -/

variable {S : Type v}

/-- **The cumulative driver displacement after the first piece** of a past. -/
def pastDrift : (n : ℕ) → GW2JDetR5.Past S (n + 1) → ℝ
  | 0 => fun _ => 0
  | n + 1 => fun x => pastDrift n x.1 + rdrv x.2 (rtime x.2)

/-- **The right junction is at least the first piece's right junction minus the later displacement.** -/
theorem junctionR_first_sub_le : ∀ (n : ℕ) (x : GW2JDetR5.Past S (n + 1)),
    junctionR 1 (pastFirst n x) - pastDrift n x ≤ junctionR (n + 1) x
  | 0, x => by
    change junctionR 1 x - 0 ≤ junctionR 1 x
    rw [sub_zero]
  | n + 1, x => by
    have ih := junctionR_first_sub_le n x.1
    have hstep := sub_le_markPos_of_nonneg (continuous_rdrv x.2) (rdrv_zero x.2) (rtime_nonneg x.2)
      (junctionR_nonneg (n + 1) x.1)
    change junctionR 1 (pastFirst n x.1) - (pastDrift n x.1 + rdrv x.2 (rtime x.2)) ≤
      markPos (rdrv x.2) (rtime x.2) (junctionR (n + 1) x.1)
    linarith

/-- **The left junction is at most the first piece's left junction minus the later displacement.** -/
theorem junctionL_le_first_sub : ∀ (n : ℕ) (x : GW2JDetR5.Past S (n + 1)),
    junctionL (n + 1) x ≤ junctionL 1 (pastFirst n x) - pastDrift n x
  | 0, x => by
    change junctionL 1 x ≤ junctionL 1 x - 0
    rw [sub_zero]
  | n + 1, x => by
    have ih := junctionL_le_first_sub n x.1
    have hstep := markPosL_le_sub_of_nonpos (continuous_rdrv x.2) (rdrv_zero x.2) (rtime_nonneg x.2)
      (junctionL_nonpos (n + 1) x.1)
    change markPosL (rdrv x.2) (rtime x.2) (junctionL (n + 1) x.1) ≤
      junctionL 1 (pastFirst n x.1) - (pastDrift n x.1 + rdrv x.2 (rtime x.2))
    linarith

/-- **The far junction of D37 at a stage start, from the root prefix's two junctions**: if both root junctions are at
least `a` away from the tip and the later displacement `d` points away from the side read (`ε = 1`: the right side,
`d ≤ −b`; `ε = −1`: the left side, `d ≥ b`), the junction on that side is at least `a + b` away. -/
theorem far_junction_of_drift (n : ℕ) (x : GW2JDetR5.Past S (n + 1)) {a b : ℝ}
    (hR1 : a ≤ junctionR 1 (pastFirst n x)) (hL1 : a ≤ -junctionL 1 (pastFirst n x)) :
    (pastDrift n x ≤ -b → a + b ≤ junctionR (n + 1) x) ∧ (b ≤ pastDrift n x → a + b ≤ -junctionL (n + 1) x) := by
  have hR := junctionR_first_sub_le n x
  have hL := junctionL_le_first_sub n x
  exact ⟨fun hd => by linarith, fun hd => by linarith⟩

end InteractingSLE.Theorem14.GW2Rd
