import HigherDimLQGMetric.Core.Defs
import HigherDimLQGMetric.Metric.Internal
import HigherDimLQGMetric.Frozen.RestrictTo
import HigherDimLQGMetric.Frozen.AddConst

/-!
# Shell geometry on Euclidean space

Port of the deterministic shell definitions used in `LQGMetric.Papers.LM` to `Rd d`.
The open shell is the shared `ann` from `Core.Defs`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Set
open HigherDimLFPP (Rd)
open scoped ENNReal

variable {d : ℕ}

/-- The open annulus as an open set. -/
def shellOpens (z : Rd d) (a b : ℝ) : TopologicalSpace.Opens (Rd d) :=
  ⟨ann z a b, isOpen_ann z a b⟩

/-- The image `z + r S`. -/
def affineSet (r : ℝ) (z : Rd d) (S : Set (Rd d)) : Set (Rd d) :=
  (fun x => z + r • x) '' S

/-- Internal diameter of the middle sphere within the larger annulus. -/
def sphereDiam (D : ContMetric d) (z : Rd d) (r : ℝ) : ℝ≥0∞ :=
  ⨆ (u ∈ Metric.sphere z r) (v ∈ Metric.sphere z r),
    D.internal (ann z (r / 2) (2 * r)) u v

/-- Distance between the two boundary spheres of an annulus. -/
def acrossDist (D : ContMetric d) (z : Rd d) (a b : ℝ) : ℝ≥0∞ :=
  ⨅ (u ∈ Metric.sphere z a) (v ∈ Metric.sphere z b),
    ENNReal.ofReal (D.1 (u, v))

/-- A path crossing the closed annulus from its inner to its outer boundary. -/
structure IsShellCrossing (z : Rd d) (a b : ℝ) (P : ℝ → Rd d) : Prop where
  cont : ContinuousOn P (Icc 0 1)
  start : P 0 ∈ Metric.sphere z a
  finish : P 1 ∈ Metric.sphere z b
  inside : MapsTo P (Ioo 0 1) (ann z a b)

/-- Largest internal set-to-set distance between two crossings. -/
def aroundDist (D : ContMetric d) (z : Rd d) (a b : ℝ) : ℝ≥0∞ :=
  ⨆ (P₁ : ℝ → Rd d) (P₂ : ℝ → Rd d) (_ : IsShellCrossing z a b P₁)
    (_ : IsShellCrossing z a b P₂),
    ⨅ (s ∈ Ioo (0 : ℝ) 1) (t ∈ Ioo (0 : ℝ) 1),
      D.internal (ann z a b) (P₁ s) (P₂ t)

/-- Sigma-algebra of the field normalized by its sphere average and restricted to the shell. -/
@[reducible] def shellSigma {Ω : Type*} (h : Ω → DistRd d) (z : Rd d)
    (r a b : ℝ) : MeasurableSpace Ω :=
  MeasurableSpace.comap
    (fun ω => restrictTo (shellOpens z (a * r) (b * r))
      (addConst (h ω) (-(sphereAvg (h ω) r z)))) inferInstance

/-- Grid points `s ℤ^d`. -/
def gridPts (s : ℝ) : Set (Rd d) :=
  {w | ∃ m : Fin d → ℤ, w = WithLp.toLp 2 (fun i => s * m i)}

end HigherDimLQGMetric
