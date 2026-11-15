/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2MuStop

/-!
# From the stopped matches to the full code match

Packet PROVE-SB2-LCMEAN, round 13. The relative versions at announced stops match the canonical driver code before
every stop (`Mu.ae_isStopDrvMatch_of_stageVersionS`). If a driver `D` agrees with the frozen drivers before the stops,
the stops increase to `D`'s lifetime, `D` starts at the code's starting value, and the code's lifetime is at most
`D`'s ((I4): the relative lifetime is the threshold), then `D` matches the code:

* **`isDriverCodeMatch_of_stops`** (deterministic);
* `le_of_stops`: the stops' supremum is at most the code's lifetime (the half of the lifetime identity that the stops
  give by themselves).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.SB.Mu

open Sec2.Assembly Restart
open Supp8.GB6.RelDrv (IsStopDrvMatch)

/-- The supremum of the stops is at most the code's lifetime. -/
theorem le_of_stops {p : PCode × ℝ≥0∞} {Wm : ℕ → ℝ≥0 → ℝ} {V : ℕ → ℝ≥0∞}
    (hm : ∀ m, IsStopDrvMatch p (Wm m) (V m)) : ⨆ m, V m ≤ p.2 :=
  iSup_le fun m => (hm m).1

/-- **The stopped matches give the full match** when the stops increase to the driver's lifetime, the driver agrees
with the frozen drivers before the stops, starts at the code's value and the code's lifetime is at most the driver's.
-/
theorem isDriverCodeMatch_of_stops {p : PCode × ℝ≥0∞} {Wm : ℕ → ℝ≥0 → ℝ} {V : ℕ → ℝ≥0∞}
    {D : (ℝ≥0 → ℝ) × ℝ≥0∞} (hm : ∀ m, IsStopDrvMatch p (Wm m) (V m)) (hsup : ⨆ m, V m = D.2)
    (hagree : ∀ m (t : ℝ≥0), (t : ℝ≥0∞) < V m → Wm m t = D.1 t) (h0 : D.1 0 = p.1 0 0)
    (hlife : p.2 ≤ D.2) : IsDriverCodeMatch p D.1 D.2 := by
  refine ⟨le_antisymm (hsup ▸ le_of_stops hm) hlife, h0, fun n k hnk => ?_⟩
  rw [← hsup] at hnk
  obtain ⟨m, hmk⟩ := lt_iSup_iff.1 hnk
  rw [← hagree m _ hmk]
  exact (hm m).2 n k hmk

end InteractingSLE.Theorem14.SB.Mu
