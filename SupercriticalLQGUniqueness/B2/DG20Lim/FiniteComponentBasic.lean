import SupercriticalLQGUniqueness.B2.DG20Lim.LimitMidpoints
import SupercriticalLQGUniqueness.B2.DG20Lim.MetricOfTriangle
import Mathlib.Topology.MetricSpace.Basic

 


set_option autoImplicit false
noncomputable section

open Set Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Lim

def FiniteComponent (D : LSCMetric) (u : ℂ) : Type :=
  {x : D.Space // edist (D.pt u) x < ∞}

instance (D : LSCMetric) (u : ℂ) : EMetricSpace (FiniteComponent D u) :=
  inferInstanceAs (EMetricSpace {x : D.Space // edist (D.pt u) x < ∞})

theorem finiteComponent_edist_ne_top (D : LSCMetric) (u : ℂ)
    (x y : FiniteComponent D u) : edist x y ≠ ∞ := by
  have hx : edist (x.1 : D.Space) (D.pt u) ≠ ∞ := by
    rw [edist_comm]
    exact ne_top_of_lt x.property
  have hy : edist (D.pt u) (y.1 : D.Space) ≠ ∞ := ne_top_of_lt y.property
  have hsum : edist (x.1 : D.Space) (D.pt u) + edist (D.pt u) (y.1 : D.Space) ≠ ∞ :=
    ENNReal.add_ne_top.mpr ⟨hx, hy⟩
  have hle : edist x y ≤
      edist (x.1 : D.Space) (D.pt u) + edist (D.pt u) (y.1 : D.Space) :=
    (edist_triangle (x.1 : D.Space) (D.pt u) (y.1 : D.Space))
  exact ne_top_of_le_ne_top hsum hle

instance (D : LSCMetric) (u : ℂ) : MetricSpace (FiniteComponent D u) :=
  EMetricSpace.toMetricSpace (finiteComponent_edist_ne_top D u)

end SupercriticalLQGUniqueness.B2.DG20Lim
