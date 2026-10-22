import HigherDimLQGMetric.DGZ.NondegCross
import LQGMetric.Prob.PolishContinuousMap

/-!
# A countable family of cubical domains for the DGZ zero-one law

For a fixed shell radius, these are the connected bounded finite unions of lattice boxes used
in the joint limit law. They carry exactly the open-domain topology needed for internal metrics.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set

namespace HigherDimLQGMetric.DGZ

open HigherDimLFPP HigherDimLFPP.Perc
open HigherDimLFPP.DGZ (latPt obox)

variable {d : ℕ}

def nd_gridRadius (r : ℝ) (j : ℕ) : ℝ := r * (2 : ℝ)⁻¹ ^ j

theorem nd_gridRadius_pos {r : ℝ} (hr : 0 < r) (j : ℕ) : 0 < nd_gridRadius r j :=
  mul_pos hr (pow_pos (by norm_num) _)

/-- A finite union of open boxes of radius twice the grid mesh `r 2⁻ʲ`. -/
def nd_boxUnion (r : ℝ) (j : ℕ) (S : Finset (Zd d)) : Set (Rd d) :=
  ⋃ z ∈ S, obox (latPt (nd_gridRadius r j) z) (2 * nd_gridRadius r j)

theorem nd_isOpen_boxUnion (r : ℝ) (j : ℕ) (S : Finset (Zd d)) :
    IsOpen (nd_boxUnion r j S) := by
  unfold nd_boxUnion
  exact isOpen_iUnion fun z => isOpen_iUnion fun _ => HigherDimLFPP.DGZ.isOpen_obox _ _

theorem nd_isBounded_boxUnion (r : ℝ) (j : ℕ) (S : Finset (Zd d)) :
    Bornology.IsBounded (nd_boxUnion r j S) := by
  unfold nd_boxUnion
  exact (Bornology.isBounded_biUnion_finset S).2 fun z _ =>
    isBounded_obox (latPt (nd_gridRadius r j) z) (2 * nd_gridRadius r j)

/-- The admissible domains; connectedness is needed for finite continuous internal distances. -/
def nd_DomainIndex (d : ℕ) (r : ℝ) : Type :=
  {p : ℕ × Finset (Zd d) // IsConnected (nd_boxUnion r p.1 p.2)}

instance (r : ℝ) : Countable (nd_DomainIndex d r) := by
  unfold nd_DomainIndex
  infer_instance

def nd_domain (r : ℝ) (i : nd_DomainIndex d r) : Set (Rd d) :=
  nd_boxUnion r i.1.1 i.1.2

theorem nd_isOpen_domain (r : ℝ) (i : nd_DomainIndex d r) :
    IsOpen (nd_domain r i) :=
  nd_isOpen_boxUnion r i.1.1 i.1.2

theorem nd_isConnected_domain (r : ℝ) (i : nd_DomainIndex d r) :
    IsConnected (nd_domain r i) := i.2

theorem nd_isBounded_domain (r : ℝ) (i : nd_DomainIndex d r) :
    Bornology.IsBounded (nd_domain r i) :=
  nd_isBounded_boxUnion r i.1.1 i.1.2

theorem nd_exists_domain_cbox (r : ℝ) (i : nd_DomainIndex d r) :
    ∃ R : ℝ, 0 ≤ R ∧ nd_domain r i ⊆ HigherDimLFPP.DGZ.cbox (0 : Rd d) R := by
  obtain ⟨R, hR⟩ := (nd_isBounded_domain r i).subset_closedBall (0 : Rd d)
  refine ⟨max R 0, le_max_right _ _, fun z hz k => ?_⟩
  have hnorm : ‖z‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_zero_right] using hR hz
  have hk := HigherDimLFPP.DGZ.abs_apply_le_norm z k
  simp only [PiLp.zero_apply, sub_zero]
  exact hk.trans (hnorm.trans (le_max_left _ _))

end HigherDimLQGMetric.DGZ
