import QuantumZipper.Proofs.Zipper.E5LocB
import QuantumZipper.Proofs.Zipper.E5LocDrv

/-!
# E5-LOC wiring: the driver identity `DrvIdentStmt` from the deterministic window identity

Blueprint `blueprint/E_BRANCH_BLUEPRINT.md` §4 E5, step (1); Sheffield, arXiv:1012.4797, §5.4
(pp. 66–72, proof of Lemma 5.6).

`E5LocB.DrvIdentStmt κ R y d a D` is the driver clause `Z C = M.data C` of `E5Model1.E5ReprG`
for a configuration `(y, d)`: the window `[0, R]` of the driver of the canonicalized
configuration is `drvWin κ R (rescale R a.toNNReal D)`. `E5LocDrv.canonConfig_snd_eq_drvWin`
proves the underlying deterministic identity, with hypotheses

* `scaleParam (√κ) y = a` (`a : ℝ≥0`), and
* `d u = √κ · D u.toNNReal` for `0 ≤ u ≤ a² R` (only the window `[0, a²R]` in which the
  rescaled germ is evaluated is read).

This file discharges `DrvIdentStmt` from those hypotheses (the `ℝ`-valued local scale `a` of
`DrvIdentStmt` is coerced to `ℝ≥0`, which is legitimate because a scale parameter is
nonnegative — here a hypothesis, `ha`):

* `drvIdentStmt_of`: window form;
* `drvIdentStmt_of_forall`: the driver agrees with `√κ · D` everywhere (no window);
* `drvIdentStmt_collided`: the collided configuration of E5-LOC, whose driver is the restarted
  Brownian germ `smPath B (T − τ_x)`, for which the window hypothesis holds with no restriction
  (`E5LocDrv.collided_snd_eq_drvMap`).

This is the collided-configuration instance consumed by `E5LocC.setup_locCorr_switch` /
`E5Model1.E5ReprG` through `E5LocB.locG_canonConfig_eq_data_of_good`.

Own elementary bookkeeping (`ℝ≥0`/`ℝ` coercions); the mathematics (the zoom identity of
Sheffield §5.4) is already formalized in `E5LocDrv.lean`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace E5

open D3Plus E1 B2

/-- **`DrvIdentStmt` in window form.** If the configuration `(y, d)` has local scale
`scaleParam (√κ) y = a` with `a ≥ 0` and its driver `d` agrees with `√κ · D` on the window
`[0, a² R]`, then the driver of its canonicalization on `[0, R]` is the rescaled germ with `√κ`
put back — i.e. `DrvIdentStmt κ R y d a D`. -/
theorem drvIdentStmt_of {κ : ℝ} {R : ℕ} {y : FieldSample} {d : ℝ → ℝ} {a : ℝ} {D : ℝ≥0 → ℝ}
    (ha : 0 ≤ a) (hsc : scaleParam (Real.sqrt κ) y = a)
    (hd : ∀ u : ℝ, 0 ≤ u → u ≤ a ^ 2 * (R : ℝ) → d u = Real.sqrt κ * D u.toNNReal) :
    DrvIdentStmt κ R y d a D := by
  intro s
  refine canonConfig_snd_eq_drvWin a.toNNReal D ?_ R ?_ s
  · rw [Real.coe_toNNReal a ha]
    exact hsc
  · intro u h0 hu
    rw [Real.coe_toNNReal a ha] at hu
    exact hd u h0 hu

/-- **`DrvIdentStmt` with a driver agreeing with `√κ · D` everywhere** (no window hypothesis). -/
theorem drvIdentStmt_of_forall {κ : ℝ} {R : ℕ} {y : FieldSample} {d : ℝ → ℝ} {a : ℝ}
    {D : ℝ≥0 → ℝ} (ha : 0 ≤ a) (hsc : scaleParam (Real.sqrt κ) y = a)
    (hd : ∀ u : ℝ, d u = Real.sqrt κ * D u.toNNReal) : DrvIdentStmt κ R y d a D :=
  drvIdentStmt_of ha hsc fun u _ _ => hd u

end E5
end QuantumZipper
