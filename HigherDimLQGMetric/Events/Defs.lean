import HigherDimLQGMetric.Core.Defs
import HigherDimLQGMetric.Metric.Internal
import HigherDimLQGMetric.Frozen.IsSharpWeakExpMetric

/-!
# Section 5 metric events

The regularity, witness, and ratio events of the corrected source §5. The annuli,
normalizer, internal set distance, and field sigma algebra come from `Core.Defs`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open MeasureTheory Set
open HigherDimLFPP (Rd)
open scoped ENNReal

variable {d : ℕ}

/-- The scales `64^j` in `[ε²R, εR]`. -/
def scaleWin (ε R : ℝ) : Set ℤ :=
  {j | ε ^ 2 * R ≤ (64 : ℝ) ^ j ∧ (64 : ℝ) ^ j ≤ ε * R}

/-- The global distance between two sets. -/
def setDistG (D : ContMetric d) (A B : Set (Rd d)) : ℝ≥0∞ :=
  ⨅ (u ∈ A) (v ∈ B), ENNReal.ofReal (D.1 (u, v))

/-- The diameter of a set in the internal metric of an open region. -/
def diamIn (D : ContMetric d) (V A : Set (Rd d)) : ℝ≥0∞ :=
  ⨆ (u ∈ A) (v ∈ A), D.internal V u v

/-- The regular event `F_r(z)` of source §5. -/
def RegEvent (A B : DistRd d → ContMetric d) (ξ Q U a A₀ ℓ β₀ r : ℝ) (z : Rd d) :
    Set (DistRd d) :=
  {h |
    ENNReal.ofReal (a * sNorm ξ Q h r z) ≤
      setDistG (A h) (Metric.sphere z r) (Metric.sphere z (2 * r)) ∧
    diamIn (A h) (ann z (3 * r / 4) (3 * r)) (annCl z r (2 * r)) ≤
      ENNReal.ofReal (A₀ * sNorm ξ Q h r z) ∧
    (∀ ρ ∈ ({3 * r / 4, 3 * r} : Set ℝ),
      ENNReal.ofReal (4 * max 1 U * ℓ * sNorm ξ Q h r z) <
          setDistIn (A h) (ann z (r / 2) (5 * r)) (annCl z r (2 * r)) (Metric.sphere z ρ) ∧
        ENNReal.ofReal (4 * max 1 U * ℓ * sNorm ξ Q h r z) <
          setDistIn (B h) (ann z (r / 2) (5 * r)) (annCl z r (2 * r)) (Metric.sphere z ρ)) ∧
    (∀ u ∈ annCl z r (2 * r), ∀ v ∈ annCl z r (2 * r), ‖u - v‖ ≤ β₀ * r →
      (A h).internal (ann z (3 * r / 4) (3 * r)) u v <
        ENNReal.ofReal (ℓ / 4 * sNorm ξ Q h r z))}

/-- An internal geodesic on `[0,1]`. -/
def IsGeodIn (D : ContMetric d) (V : Set (Rd d)) (P : ℝ → Rd d) : Prop :=
  ContinuousOn P (Icc 0 1) ∧ (∀ τ ∈ Icc (0 : ℝ) 1, P τ ∈ V) ∧
    D.len P 0 1 = D.internal V (P 0) (P 1)

/-- A global geodesic on `[0,1]`. -/
def IsGeod (D : ContMetric d) (P : ℝ → Rd d) : Prop :=
  ContinuousOn P (Icc 0 1) ∧ D.len P 0 1 = ENNReal.ofReal (D.1 (P 0, P 1))

/-- The witness event `H_{z,r}(t)` of source §5. -/
def WitEvent (A B : DistRd d → ContMetric d) (ξ Q U a A₀ ℓ β₀ t r : ℝ) (z : Rd d) :
    Set (DistRd d) :=
  RegEvent A B ξ Q U a A₀ ℓ β₀ r z ∩
  {h | ∃ P : ℝ → Rd d, (∀ τ ∈ Icc (0 : ℝ) 1, P τ ∈ annCl z r (2 * r)) ∧
    IsGeodIn (A h) (ann z (3 * r / 4) (3 * r)) P ∧
    ENNReal.ofReal (ℓ / 2 * sNorm ξ Q h r z) ≤ (A h).len P 0 1 ∧
    (A h).len P 0 1 ≤ ENNReal.ofReal (ℓ * sNorm ξ Q h r z) ∧
    ENNReal.ofReal t * (A h).len P 0 1 <
      (B h).internal (ann z (3 * r / 4) (3 * r)) (P 0) (P 1)}

/-- The ratio event `G_R(u, β)` of Definition 5.3. -/
def GEvent (A B : DistRd d → ContMetric d) (ξ Q u β R : ℝ) : Set (DistRd d) :=
  {h | ∃ x ∈ Metric.closedBall (0 : Rd d) (2 * R),
    ∃ y ∈ Metric.closedBall (0 : Rd d) (2 * R),
    β * R ≤ ‖x - y‖ ∧ β * sNorm ξ Q h R 0 ≤ (A h).1 (x, y) ∧
    (A h).1 (x, y) ≤ β⁻¹ * sNorm ξ Q h R 0 ∧
    u * (A h).1 (x, y) < (B h).1 (x, y)}

/-- Shell-local events are measurable modulo constants on `A_{r/2,5r}(z)`, up to null sets. -/
def IsShellLocal {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (h : Ω → DistRd d)
    (E : Rd d → ℝ → Set Ω) : Prop :=
  ∀ z r, 0 < r → AEEventIn P (fieldSigma0 h (ann z (r / 2) (5 * r))) (E z r)

/-- The uniform high probability assertion for `F_r(z)` (Lemma R). -/
def RegularEvents (d : ℕ) (ξ Q : ℝ) (A B : DistRd d → ContMetric d) : Prop :=
  ∀ U δ : ℝ, 0 < U → 0 < δ → ∃ a A₀ ℓ β₀ : ℝ,
    0 < a ∧ a < A₀ ∧ 0 < ℓ ∧ ℓ < a / 100 ∧ 0 < β₀ ∧ β₀ < 1 ∧
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistRd d), IsWholeSpaceLGF h P → ∀ r : ℝ, 0 < r → ∀ z : Rd d,
        ENNReal.ofReal (1 - δ) ≤ P (h ⁻¹' RegEvent A B ξ Q U a A₀ ℓ β₀ r z)

/-- Four normalized internal-distance functions on the two trapping shells. -/
abbrev Config (d : ℕ) : Type :=
  (Rd d → Rd d → ℝ≥0∞) × (Rd d → Rd d → ℝ≥0∞) ×
    (Rd d → Rd d → ℝ≥0∞) × (Rd d → Rd d → ℝ≥0∞)

/-- The configuration of two metrics at a scale and center. -/
def config (D Dt : ContMetric d) (s r : ℝ) (z : Rd d) : Config d :=
  (fun u v => ENNReal.ofReal s⁻¹ *
    D.internal (ann z (r / 2) (5 * r)) (r • u + z) (r • v + z),
   fun u v => ENNReal.ofReal s⁻¹ *
    Dt.internal (ann z (r / 2) (5 * r)) (r • u + z) (r • v + z),
   fun u v => ENNReal.ofReal s⁻¹ *
    D.internal (ann z (3 * r / 4) (7 * r / 2)) (r • u + z) (r • v + z),
   fun u v => ENNReal.ofReal s⁻¹ *
    Dt.internal (ann z (3 * r / 4) (7 * r / 2)) (r • u + z) (r • v + z))

end HigherDimLQGMetric
