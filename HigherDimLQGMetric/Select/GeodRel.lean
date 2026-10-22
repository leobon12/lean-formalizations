import HigherDimLQGMetric.Select.MetricBorel
import LQGMetric.Meas.Geod
import Mathlib.Topology.UnitInterval

/-!
# Closed relation of constant-speed geodesics

Packet M3a. Port of LQGMetric `Meas/Geod.lean` from `ℂ` to `Rd d`, retaining the
exact constant-speed convention of MA1 A10. The bound on a path is Euclidean.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Topology unitInterval

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ}

/-- A constant-speed geodesic on `[0,1]`, as in the MA1 probe. -/
def IsConstSpeedGeod (D : ContMetric d) (x y : Rd d) (η : C(unitInterval, Rd d)) : Prop :=
  η 0 = x ∧ η 1 = y ∧ ∀ s t : unitInterval,
    D.1 (η s, η t) = |(s : ℝ) - t| * D.1 (x, y)

/-- The geodesic equations also make sense for an arbitrary continuous two-point function. -/
def IsConstSpeedGeodFn (g : C(Rd d × Rd d, ℝ)) (x y : Rd d)
    (η : C(unitInterval, Rd d)) : Prop :=
  η 0 = x ∧ η 1 = y ∧ ∀ s t : unitInterval,
    g (η s, η t) = |(s : ℝ) - t| * g (x, y)

theorem isConstSpeedGeod_iff (D : ContMetric d) (x y : Rd d)
    (η : C(unitInterval, Rd d)) :
    IsConstSpeedGeod D x y η ↔ IsConstSpeedGeodFn D.1 x y η := Iff.rfl

/-- The closed bounded geodesic relation on the ambient continuous-map space. -/
def geodBoundRel (x y : Rd d) (n : ℕ) :
    Set (C(Rd d × Rd d, ℝ) × C(unitInterval, Rd d)) :=
  {p | IsConstSpeedGeodFn p.1 x y p.2 ∧
    ∀ t : unitInterval, ‖p.2 t‖ ≤ n}

private theorem continuous_geod_eval (s t : unitInterval) :
    Continuous fun p : C(Rd d × Rd d, ℝ) × C(unitInterval, Rd d) =>
      p.1 (p.2 s, p.2 t) :=
  continuous_eval.comp (continuous_fst.prodMk
    (((continuous_eval_const s).comp continuous_snd).prodMk
      ((continuous_eval_const t).comp continuous_snd)))

/-- The bounded geodesic relation is closed before restricting to metrics. -/
theorem isClosed_geodBoundRel (x y : Rd d) (n : ℕ) :
    IsClosed (geodBoundRel x y n) := by
  have he : ∀ s : unitInterval,
      Continuous fun p : C(Rd d × Rd d, ℝ) × C(unitInterval, Rd d) => p.2 s :=
    fun s => (continuous_eval_const s).comp continuous_snd
  have hgeod : IsClosed {p : C(Rd d × Rd d, ℝ) × C(unitInterval, Rd d) |
      IsConstSpeedGeodFn p.1 x y p.2} := by
    simp only [IsConstSpeedGeodFn, ofPred_and, ofPred_forall]
    refine (isClosed_eq (he 0) continuous_const).inter
      ((isClosed_eq (he 1) continuous_const).inter
        (isClosed_iInter fun s => isClosed_iInter fun t => isClosed_eq ?_ ?_))
    · exact continuous_geod_eval s t
    · exact continuous_const.mul ((continuous_eval_const (x, y)).comp continuous_fst)
  have hbound : IsClosed {p : C(Rd d × Rd d, ℝ) × C(unitInterval, Rd d) |
      ∀ t : unitInterval, ‖p.2 t‖ ≤ n} := by
    simp only [ofPred_forall]
    exact isClosed_iInter fun t => isClosed_le (he t).norm continuous_const
  exact hgeod.inter hbound

/-- Scaling a continuous two-point function by a positive constant preserves its geodesics. -/
theorem isConstSpeedGeodFn_smul_iff (g : C(Rd d × Rd d, ℝ)) (x y : Rd d)
    (η : C(unitInterval, Rd d)) (c : ℝ) (hc : 0 < c) :
    IsConstSpeedGeodFn (c • g) x y η ↔ IsConstSpeedGeodFn g x y η := by
  simp only [IsConstSpeedGeodFn, ContinuousMap.smul_apply, smul_eq_mul]
  refine and_congr_right fun _ => and_congr_right fun _ => forall₂_congr fun s t => ?_
  constructor
  · intro h
    apply mul_left_cancel₀ hc.ne'
    calc c * g (η s, η t) = |(s : ℝ) - t| * (c * g (x, y)) := h
      _ = c * (|(s : ℝ) - t| * g (x, y)) := by ring
  · intro h
    rw [h]
    ring

end HigherDimLQGMetric
