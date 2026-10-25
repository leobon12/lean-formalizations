import SupercriticalLQGUniqueness.B2.PfeWeyl.CurveOscillation
import SupercriticalLQGUniqueness.B2.PfeWeyl.GeoAnnuli

 









set_option autoImplicit false
noncomputable section

open Set Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeWeyl

 

def IsNonsingular (D : LSCMetric) (z : ℂ) : Prop :=
  ∃ w : ℂ, w ≠ z ∧ D (z, w) < ⊤

 

def IsRationalDoubleAnnulus (A : EuclideanAnnulus) : Prop :=
  ∃ x y r : ℚ, 0 < r ∧
    A.center = Complex.mk (x : ℝ) (y : ℝ) ∧
    A.innerRadius = (r : ℝ) ∧ A.outerRadius = 2 * (r : ℝ)

 




def SmallAnnulusCosts (G : ℕ → LSCMetric) (D : LSCMetric)
    (K' K'' : Set ℂ) : Prop :=
  ∀ z ∈ K', IsNonsingular D z →
    ∀ δ : ℝ, 0 < δ → ∀ ρ : ℝ, 0 < ρ →
      ∃ A : EuclideanAnnulus,
        IsRationalDoubleAnnulus A ∧
        dist z A.center < A.innerRadius ∧
        A.outerRadius < ρ ∧
        A.toSet ⊆ K'' ∧
        ∀ᶠ n in atTop, aroundDist (G n) A < ENNReal.ofReal δ

 




def LateLFPPPathLocalization (G : ℕ → LSCMetric) (D : LSCMetric)
    (ξ : ℝ) (fn : ℕ → C(ℂ, ℝ)) (f : C(ℂ, ℝ))
    (K K' K'' : Set ℂ) : Prop :=
  EndpointLocalization G D ξ fn f K K' K''

end SupercriticalLQGUniqueness.B2.PfeWeyl
