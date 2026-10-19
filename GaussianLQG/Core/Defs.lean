import LQGDimension.Existence.AssemblyAux1
import LQGMetric.Statement.Metric
import LQGMetric.Blueprint.M2Defs
import LQGMetric.Prob.Median
import LQGMetric.Field.WhiteNoise
import LQGMetric.Statement.Field
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.MeasureTheory.Integral.CircleIntegral
import GaussianLQG.Frozen.SegMeasure
import GaussianLQG.Frozen.MeasPairing

/-!
# Core internal definitions for the small-γ LQG distance formalization

Implementation-level definitions shared by all work packages (blueprint §1.2, §1.4, §1.5). None of
these is a frozen, source-facing declaration; the frozen surface lives in `GaussianLQG/Frozen/`.

* `Coord := ℕ → ℝ` with the product Gaussian measure `LQGDimension.ExistAsm.stdP`
  (blueprint §1.4), and shifts by finitely supported vectors.
* The pinned GFF kernel `kernelG` (blueprint (1.1)) and the logarithmic energy `energy`.
* Regular measures (blueprint Definition 1.1), segment and circle measures.
* GFF frames (blueprint Definition 1.6), the coordinate pairing, and `frameFun`.
* Length measures of constant-speed geodesics, and the Hölder constant and separated infimum of a
  metric function (blueprint (1.10)).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace GaussianLQG

/-! ## Coordinates -/

/-- The coordinate space `ℝ^ℕ` of the field (blueprint §1.4). -/
abbrev Coord : Type := ℕ → ℝ

/-- The product of standard Gaussians on `ℝ^ℕ`. -/
abbrev stdP : Measure Coord := LQGDimension.ExistAsm.stdP

/-- Shift of `ω ∈ ℝ^ℕ` by a finitely supported vector `v`. -/
def shiftBy (ω : Coord) (v : ℕ →₀ ℝ) : Coord := ω + ⇑v

/-! ## Kernel and energy -/

/-- `G(z,w) = -log|z-w| + log|z|₊ + log|w|₊`, the covariance of the whole-plane GFF normalized by
`h₁(0) = 0` (blueprint (1.1)). On the diagonal `Real.log 0 = 0`; the diagonal is null for every
regular measure. -/
def kernelG (z w : ℂ) : ℝ :=
  -Real.log ‖z - w‖ + Real.log (max 1 ‖z‖) + Real.log (max 1 ‖w‖)

/-- The energy `ℰ(μ, ν) = ∬ G dμ dν` of two (positive) measures; signed measures are handled as
formal differences by bilinearity (blueprint Definition 1.2). -/
def energy (μ ν : Measure ℂ) : ℝ := ∫ z, ∫ w, kernelG z w ∂ν ∂μ

/-- Regular measures (blueprint Definition 1.1), positive version: finite, compactly supported,
with a Hölder ball-mass bound `μ(B_r(u)) ≤ C r^α` for `0 < r ≤ 1`. -/
def IsRegular (μ : Measure ℂ) : Prop :=
  IsFiniteMeasure μ ∧ (∃ R : ℝ, μ (Metric.closedBall (0 : ℂ) R)ᶜ = 0) ∧
    ∃ C α : ℝ, 0 < α ∧ ∀ u : ℂ, ∀ r : ℝ, 0 < r → r ≤ 1 →
      (μ (Metric.ball u r)).toReal ≤ C * r ^ α

-- `segMeasure` (blueprint Definition `def:segment`) is the frozen definition
-- `GaussianLQG/Frozen/SegMeasure.lean`.

/-- The uniform probability measure on the circle `∂B_r(z)` (blueprint Definition 1.4). -/
def circleMeasure (z : ℂ) (r : ℝ) : Measure ℂ :=
  (ENNReal.ofReal (2 * Real.pi)⁻¹ • volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))).map
    (circleMap z r)

/-! ## Frames and the coordinate pairing -/

/-- A GFF frame (blueprint Definition 1.6): bounded continuous functions whose coefficient
sequences realize the energy, in polarized form on regular measures. -/
def IsGFFFrame (e : ℕ → ℂ → ℝ) : Prop :=
  (∀ j, Continuous (e j)) ∧ (∀ j, ∃ C : ℝ, ∀ z, |e j z| ≤ C) ∧
    ∀ μ ν : Measure ℂ, IsRegular μ → IsRegular ν →
      HasSum (fun j => (∫ z, e j z ∂μ) * (∫ z, e j z ∂ν)) (energy μ ν)

/-- `f_v = ∑_j v_j e_j` for a finitely supported `v` (blueprint §1.4). -/
def frameFun (e : ℕ → ℂ → ℝ) (v : ℕ →₀ ℝ) : ℂ → ℝ := fun z => v.sum fun j c => c * e j z

/-- `f_v` as a bundled continuous function, given continuity of the frame. -/
def frameFunC (e : ℕ → ℂ → ℝ) (he : ∀ j, Continuous (e j)) (v : ℕ →₀ ℝ) : C(ℂ, ℝ) :=
  ⟨frameFun e v, by
    unfold frameFun Finsupp.sum
    exact continuous_finsetSum _ fun j _ => continuous_const.mul (he j)⟩

/-- The coordinate pairing `(h, μ)(ω) = lim_n ∑_{j<n} ω_j ∫ e_j dμ` (blueprint Lemma `lem:field`). Where
the limit does not exist, `limUnder` returns an unspecified value; this happens only on a null set. -/
def pairing (e : ℕ → ℂ → ℝ) (μ : Measure ℂ) (ω : Coord) : ℝ :=
  limUnder atTop fun n => ∑ j ∈ Finset.range n, ω j * ∫ z, e j z ∂μ

/-! ## The white-noise frame (blueprint Appendix B) -/

/-- The white-noise space `L²(ℝ × ℂ)` of `LQGMetric` (time first). -/
abbrev WNSpace : Type := LQGMetric.WhiteNoise.WNSpace

/-- A "nice" white-noise basis vector: essentially bounded, and supported in a bounded set that
stays a positive distance away from time `0`. -/
def IsNiceWN (g : WNSpace) : Prop :=
  ∃ a b M R : ℝ, 0 < a ∧ (∀ᵐ q ∂(volume : Measure (ℝ × ℂ)), |(g : ℝ × ℂ → ℝ) q| ≤ M) ∧
    ∀ᵐ q ∂(volume : Measure (ℝ × ℂ)), (g : ℝ × ℂ → ℝ) q ≠ 0 →
      a ≤ |q.1| ∧ |q.1| ≤ b ∧ ‖q.2‖ ≤ R

/-- The heat-kernel integrand of `LQGMetric`'s white-noise representation of the field at the point
`u`: `√π 1_{t>0} (p_{t/2}(u,y) - 1_{t>1} p_{t/2}(0,y))`, matching `LQGMetric.GFFExist.kerFun`. -/
def kerPt (u : ℂ) (q : ℝ × ℂ) : ℝ :=
  Real.sqrt Real.pi * (Ioi (0 : ℝ)).indicator
    (fun t => LQGMetric.heatKernel (t / 2) u q.2 -
      (Ioi (1 : ℝ)).indicator (fun _ => LQGMetric.heatKernel (t / 2) 0 q.2) t) q.1

/-- The (unnormalized) field direction `ẽ_g(u) = ⟨kerPt u, g⟩` of a white-noise vector `g`. -/
def frameFun0 (g : WNSpace) (u : ℂ) : ℝ := ∫ q, kerPt u q * (g : ℝ × ℂ → ℝ) q

/-- The direction normalized to have zero average on the unit circle: `e_g = ẽ_g - avg_{∂𝔻} ẽ_g`. -/
def frameFunN (g : WNSpace) (u : ℂ) : ℝ :=
  frameFun0 g u - Real.circleAverage (frameFun0 g) 0 1

/-! ## Pairing of a distribution with a measure -/

-- `measPairing` (blueprint Definition `def:pairing`) is the frozen definition
-- `GaussianLQG/Frozen/MeasPairing.lean`.

/-! ## Geodesics and metric functionals -/

/-- The length measure `ν_P = P_* Leb|_{[0,1]}` of a constant-speed geodesic (blueprint §1.5). -/
def lengthMeasure (η : C(unitInterval, ℂ)) : Measure ℂ :=
  (volume.restrict (Icc (0 : ℝ) 1)).map fun t => η (Set.projIcc 0 1 zero_le_one t)

/-- The `1/2`-Hölder constant `A(K) = sup_{z ≠ w ∈ K} d(z,w)/|z-w|^{1/2}` (blueprint (1.10)),
valued in `[0, ∞]`. -/
def holderConst (d : ℂ × ℂ → ℝ) (K : Set ℂ) : ℝ≥0∞ :=
  ⨆ z ∈ K, ⨆ w ∈ K, ⨆ (_ : z ≠ w), ENNReal.ofReal (d (z, w) / ‖z - w‖ ^ (1 / 2 : ℝ))

/-- The separated infimum `I(K, δ) = inf_{z,w ∈ K, |z-w| ≥ δ} d(z,w)` (blueprint (1.10)), valued
in `[0, ∞]` (`∞` for an empty index set). -/
def sepInf (d : ℂ × ℂ → ℝ) (K : Set ℂ) (δ : ℝ) : ℝ≥0∞ :=
  ⨅ z ∈ K, ⨅ w ∈ K, ⨅ (_ : δ ≤ ‖z - w‖), ENNReal.ofReal (d (z, w))

/-- The annulus crossing distance `L_R = inf {d(x,y) : |x| = R, |y| = 2R}` (blueprint Lemma
`lem:scaling`(d)), valued in `[0, ∞]`. -/
def annulusCross (d : ℂ × ℂ → ℝ) (R : ℝ) : ℝ≥0∞ :=
  ⨅ x ∈ Metric.sphere (0 : ℂ) R, ⨅ y ∈ Metric.sphere (0 : ℂ) (2 * R), ENNReal.ofReal (d (x, y))

end GaussianLQG
