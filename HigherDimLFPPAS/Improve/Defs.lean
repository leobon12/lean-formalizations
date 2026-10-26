import HigherDimLQGMetric.Core.Defs
import HigherDimLQGMetric.Metric.Internal

/-!
# Deterministic comparison data for Proposition 4.1

The annulus `F` in the source is closed: it is compactly contained in the open set `U`.
In particular its boundary spheres are points of the internal metric domain. We use the
repository's `annCl` and `ann` for these two sets.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric
open scoped ENNReal

namespace HigherDimLFPPAS.Improve

open HigherDimLQGMetric
open HigherDimLFPP (Rd)

variable {d : ℕ}

/-- The closed annulus used for a crossing in Definition 3.1. -/
def d4F (z : Rd d) (r : ℝ) : Set (Rd d) := annCl z (3 * r / 4) r

/-- The buffered open annulus used for internal distances in Definition 3.1. -/
def d4U (z : Rd d) (r : ℝ) : Set (Rd d) := ann z (r / 4) (2 * r)

/-- The least internal distance in the closed annulus between the boundary spheres. -/
def d4Crossing (D : ContMetric d) (z : Rd d) (r : ℝ) : ℝ≥0∞ :=
  setDistIn D (d4F z r) (Metric.sphere z (3 * r / 4)) (Metric.sphere z r)

/-- The three deterministic good-annulus properties from Definition 3.1.

The scale factor `c` is assumed positive. The endpoint spheres lie in `d4F`, and `d4F ⊆ d4U`
when `r > 0`.
-/
def d4GoodAt (D M : ContMetric d) (z : Rd d) (r c η A b : ℝ) : Prop :=
  0 < r ∧ 0 < c ∧ 0 < η ∧ 1 ≤ A ∧ 0 < b ∧
  (∀ x ∈ Metric.sphere z (3 * r / 4), ∀ y ∈ Metric.sphere z r,
    M.internal (d4U z r) x y ≤ ENNReal.ofReal ((1 + η) * c) *
      D.internal (d4F z r) x y) ∧
  (∀ x ∈ Metric.sphere z (3 * r / 4), ∀ y ∈ Metric.sphere z r,
    D.internal (d4U z r) x y ≤ ENNReal.ofReal ((1 + η) / c) *
      M.internal (d4F z r) x y) ∧
  (⨆ x ∈ Metric.sphere z (3 * r / 4), ⨆ y ∈ Metric.sphere z (3 * r / 4),
    D.internal (d4U z r) x y) ≤ ENNReal.ofReal A * d4Crossing D z r ∧
  (⨆ x ∈ Metric.sphere z (3 * r / 4), ⨆ y ∈ Metric.sphere z (3 * r / 4),
    M.internal (d4U z r) x y) ≤ ENNReal.ofReal A * d4Crossing M z r ∧
  (∀ x ∈ d4F z r, ∀ w ∈ Metric.ball x b,
    M.internal (d4U z r) x w ≤ ENNReal.ofReal (η * c) * d4Crossing D z r) ∧
  (∀ x ∈ d4F z r, ∀ w ∈ Metric.ball x b,
    D.internal (d4U z r) x w ≤ ENNReal.ofReal (η / c) * d4Crossing M z r)

/-- The directional half of Definition 3.1 used by the deterministic forward implication:
crossings and inner sphere diameters are measured in `D`, while replacements and short endpoint
connectors are measured in `M`. -/
def d4GoodHalf (D M : ContMetric d) (z : Rd d) (r c η A b : ℝ) : Prop :=
  0 < r ∧ 0 < c ∧ 0 < η ∧ 1 ≤ A ∧ 0 < b ∧
  (∀ x ∈ Metric.sphere z (3 * r / 4), ∀ y ∈ Metric.sphere z r,
    M.internal (d4U z r) x y ≤ ENNReal.ofReal ((1 + η) * c) *
      D.internal (d4F z r) x y) ∧
  (⨆ x ∈ Metric.sphere z (3 * r / 4), ⨆ y ∈ Metric.sphere z (3 * r / 4),
    D.internal (d4U z r) x y) ≤ ENNReal.ofReal A * d4Crossing D z r ∧
  (∀ x ∈ d4F z r, ∀ w ∈ Metric.ball x b,
    M.internal (d4U z r) x w ≤ ENNReal.ofReal (η * c) * d4Crossing D z r)

/-- The forward half follows from the complete six-condition version of Definition 3.1. -/
theorem d4GoodAt_toGoodHalf {D M : ContMetric d} {z : Rd d} {r c η A b : ℝ}
    (hgood : d4GoodAt D M z r c η A b) : d4GoodHalf D M z r c η A b := by
  rcases hgood with ⟨hr, hc, hη, hA, hb, hcmp, _, hdiam, _, hshort, _⟩
  exact ⟨hr, hc, hη, hA, hb, hcmp, hdiam, hshort⟩

/-- A length-parametrized minimizing curve for the internal metric on `V`.

The all-pairs distance identity is the unit-speed form of `IsGeodesicCurve` in the internal
metric space. It makes every subinterval a minimizing segment and fixes its length to the time
increment.
-/
def d4InternalGeodesic (D : ContMetric d) (V : Set (Rd d)) (P : ℝ → Rd d) (T : ℝ) : Prop :=
  0 ≤ T ∧ ContinuousOn P (Icc 0 T) ∧ MapsTo P (Icc 0 T) V ∧
    (∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T,
      D.internal V (P s) (P t) = ENNReal.ofReal |t - s|) ∧
    (∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, s ≤ t →
      D.len P s t = ENNReal.ofReal (t - s))

/-- The old comparison property (4.1), with its prescribed endpoint radius and output domain. -/
def d4Comparison (D M : ContMetric d) (R ε q₀ C : ℝ) : Prop :=
  ∀ (P : ℝ → Rd d) (T : ℝ),
    d4InternalGeodesic D (Metric.ball 0 (R + 1)) P T →
    MapsTo P (Icc 0 T) (Metric.ball 0 R) →
    setDistIn M (Metric.ball 0 (R + 2))
      (Metric.ball (P 0) (8 * ε ^ q₀)) (Metric.ball (P T) (8 * ε ^ q₀)) ≤
        ENNReal.ofReal C * D.len P 0 T

/-- A finite mesh covers the path domain at the scale used in Proposition 4.1, and each mesh
point has at least one good radius from the selected deterministic radius set. -/
def d4Covering (D M : ContMetric d) (R rmin rmax η A b : ℝ)
    (mesh : Finset (Rd d)) (radii : Finset ℝ) (c : ℝ → ℝ) : Prop :=
  (∀ x ∈ Metric.ball (0 : Rd d) R,
    ∃ z ∈ mesh, dist x z ≤ rmin / 100) ∧
  (∀ z ∈ mesh, z ∈ Metric.ball (0 : Rd d) (R + 1)) ∧
  (∀ z ∈ mesh, ∃ r ∈ radii, rmin ≤ r ∧ r ≤ rmax ∧ d4GoodAt D M z r (c r) η A b)

/-- The one-direction covering input for the abstract forward form of Proposition 4.1. -/
def d4CoveringHalf (D M : ContMetric d) (R rmin rmax η A b : ℝ)
    (mesh : Finset (Rd d)) (radii : Finset ℝ) (c : ℝ → ℝ) : Prop :=
  (∀ x ∈ Metric.ball (0 : Rd d) R,
    ∃ z ∈ mesh, dist x z ≤ rmin / 100) ∧
  (∀ z ∈ mesh, z ∈ Metric.ball (0 : Rd d) (R + 1)) ∧
  (∀ z ∈ mesh, ∃ r ∈ radii, rmin ≤ r ∧ r ≤ rmax ∧ d4GoodHalf D M z r (c r) η A b)

end HigherDimLFPPAS.Improve
