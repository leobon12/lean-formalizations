import HigherDimLQGMetric.Amplify.Exit
import HigherDimLQGMetric.Amplify.Geometry

/-! The trial collar confines short geodesics to the trial annulus. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Set
open HigherDimLFPP (Rd)
open scoped ENNReal

variable {d : ℕ}

/-- The two-sphere trial collar confines any shorter path for a metric
dominating `cs` times the base metric. -/
theorem amplify_path_stays_trial_annulus (D E : ContMetric d)
    {s cs C : ℝ} (hs : 0 < s) (w : Rd d)
    {u : Rd d} (hu : u ∈ annCl w s (2 * s))
    {P : ℝ → Rd d} {T : ℝ} (hP : ContinuousOn P (Icc 0 T))
    (hP0 : P 0 = u)
    (hcomp : ∀ x y, cs * D.1 (x, y) ≤ E.1 (x, y))
    (hcoll : ENNReal.ofReal C <
      setDistIn D (ann w (s / 2) (5 * s)) (annCl w s (2 * s))
        (Metric.sphere w (3 * s / 4) ∪ Metric.sphere w (3 * s)))
    (hlen : E.len P 0 T < ENNReal.ofReal cs * ENNReal.ofReal C) :
    ∀ t ∈ Icc (0 : ℝ) T, P t ∈ ann w (3 * s / 4) (3 * s) := by
  let O := ann w (3 * s / 4) (3 * s)
  let J := ann w (s / 2) (5 * s)
  have hfront : frontier O ⊆
      Metric.sphere w (3 * s / 4) ∪ Metric.sphere w (3 * s) :=
    amplify_frontier_open_subset_spheres s w
  have hB := amplify_setDistIn_anti_right D J (annCl w s (2 * s)) hfront
  have hmul : ENNReal.ofReal cs * ENNReal.ofReal C ≤
      ENNReal.ofReal cs * setDistIn D J (annCl w s (2 * s)) (frontier O) := by
    gcongr
    exact hcoll.le.trans hB
  exact amplify_path_stays_of_collar D E (isOpen_ann w _ _)
    (amplify_closure_open_subset_shell hs w) hu
    (amplify_core_subset_open hs w hu) hP hP0 hcomp (hlen.trans_le hmul)

end HigherDimLQGMetric
