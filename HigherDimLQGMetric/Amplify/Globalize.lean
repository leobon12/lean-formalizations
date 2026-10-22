import HigherDimLQGMetric.Amplify.ExitAnnulus
import HigherDimLQGMetric.Amplify.SimpleGeodesic

/-! A collar bound identifies global and annular distances between core points. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Set
open HigherDimLFPP (Rd)
open scoped ENNReal

variable {d : ℕ}

/-- If the global distance between two core points is shorter than the
collar, its minimizing geodesic stays in the trial annulus. -/
theorem amplify_global_eq_internal_of_collar (D : ContMetric d)
    (hD : D.IsLength) [ProperSpace D.Space]
    {s C : ℝ} (hs : 0 < s) (w : Rd d)
    {u v : Rd d} (hu : u ∈ annCl w s (2 * s))
    (hv : v ∈ annCl w s (2 * s))
    (hcoll : ENNReal.ofReal C <
      setDistIn D (ann w (s / 2) (5 * s)) (annCl w s (2 * s))
        (Metric.sphere w (3 * s / 4) ∪ Metric.sphere w (3 * s)))
    (hshort : D.1 (u, v) < C) :
    D.internal (ann w (3 * s / 4) (3 * s)) u v =
      ENNReal.ofReal (D.1 (u, v)) := by
  by_cases huv : u = v
  · subst v
    rw [D.internal_self (amplify_core_subset_open hs w hu), D.apply_self]
    simp
  obtain ⟨γ, hγ, hγ0, hγ1, hlenγ⟩ :=
    amplify_exists_simple_geodesic D hD huv
  have hC : 0 < C := (D.nonneg u v).trans_lt hshort
  have hlen : D.len γ 0 1 < ENNReal.ofReal 1 * ENNReal.ofReal C := by
    rw [hlenγ, ENNReal.ofReal_one, one_mul]
    exact (ENNReal.ofReal_lt_ofReal_iff hC).2 hshort
  have hrange : ∀ t ∈ Icc (0 : ℝ) 1,
      γ t ∈ ann w (3 * s / 4) (3 * s) :=
    amplify_path_stays_trial_annulus D D hs w hu hγ.1 hγ0
      (fun x y => by simp) hcoll hlen
  refine le_antisymm ?_ (D.ofReal_le_internal _ u v)
  calc
    D.internal (ann w (3 * s / 4) (3 * s)) u v =
        D.internal (ann w (3 * s / 4) (3 * s)) (γ 0) (γ 1) := by rw [hγ0, hγ1]
    _ ≤ D.len γ 0 1 := D.internal_le_len zero_le_one hγ.1 hrange
    _ = ENNReal.ofReal (D.1 (u, v)) := hlenγ

end HigherDimLQGMetric
