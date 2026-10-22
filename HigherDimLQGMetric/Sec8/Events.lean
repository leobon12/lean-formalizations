import HigherDimLQGMetric.Sec8.Colors
import HigherDimLQGMetric.Sec8.Cover
import HigherDimLQGMetric.ScaleBin.Basic
import HigherDimLQGMetric.Select.GeodSelector

/-!
# Section 8: favorable labeled-set events

The four conditions (C1)–(C4) are defined for a finite set of labels of one
colour. `Exc` records the connected component of a path inside the radius-`4r`
ball by its two boundary times, and evaluates the internal metric at the first
and last visits to the closed collector in that component.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open MeasureTheory Set Metric unitInterval
open HigherDimLFPP (Rd)
open scoped ENNReal

variable {d : ℕ}

/-- A fixed Borel selector of a constant-speed geodesic when one exists. -/
def sec8Sel (x y : Rd d) : C(Rd d × Rd d, ℝ) → C(unitInterval, Rd d) :=
  (exists_measurable_geodSelector x y).choose

theorem measurable_sec8Sel (x y : Rd d) : Measurable (sec8Sel x y) :=
  (exists_measurable_geodSelector x y).choose_spec.1

/-- The collector at center `z` and scale `r`. -/
def sec8Collector (V : Set (Rd d)) (r : ℝ) (z : Rd d) : Set (Rd d) :=
  (fun u => r • u + z) '' V

/-- A radius-`4r` excursion of a continuous path meeting the collector,
with threshold on the original internal distance between its first and last
closed-collector visits. The path endpoints outside the ball ensure its open
components have boundary times as written here. -/
def Exc (η : C(unitInterval, Rd d)) (D : ContMetric d)
    (V : Set (Rd d)) (z : Rd d) (r ϑ : ℝ) : Prop :=
  ∃ α β : unitInterval, α < β ∧
    η α ∉ ball z (4 * r) ∧ η β ∉ ball z (4 * r) ∧
    (∀ t ∈ Ioo α β, η t ∈ ball z (4 * r)) ∧
    (∃ t ∈ Ioo α β, η t ∈ V) ∧
    ENNReal.ofReal ϑ ≤ D.internal (ball z (4 * r))
      (η (sInf {t : unitInterval | t ∈ Ioo α β ∧ η t ∈ closure V}))
      (η (sSup {t : unitInterval | t ∈ Ioo α β ∧ η t ∈ closure V}))

/-- (C1): the comparison gap at the deterministic endpoints. -/
def sec8C1 (D Dt : DistRd d → ContMetric d) (ξ Q Cstar q R : ℝ)
    (x y : Rd d) (g : DistRd d) : Prop :=
  Cstar * (D g).1 (x, y) - q * macroS ξ Q g R ≤ (Dt g).1 (x, y)

/-- (C2): every selected label lies in its trap configuration and scale bin. -/
def sec8C2 (D Dt : DistRd d → ContMetric d) (ξ Q q R r : ℝ)
    (J : ℕ) (N : ℕ → Set (Config d)) (Z : Finset (Rd d × ℕ))
    (g : DistRd d) : Prop :=
  ∀ site ∈ Z, site.2 < J ∧
    config (D g) (Dt g) (sNorm ξ Q g r site.1) r site.1 ∈ N site.2 ∧
    q * macroS ξ Q g R ≤ sNorm ξ Q g r site.1 ∧
    sNorm ξ Q g r site.1 ≤ 2 * q * macroS ξ Q g R

/-- (C3): the selected geodesic for the original metric visits each trap ball. -/
def sec8C3 (D : DistRd d → ContMetric d) (x y : Rd d) (r : ℝ)
    (Z : Finset (Rd d × ℕ)) (g : DistRd d) : Prop :=
  ∀ site ∈ Z, ∃ t : unitInterval,
    sec8Sel x y (D g).1 t ∈ ball site.1 r

/-- (C4): after subtracting all bumps, the selected geodesic has a large
original-distance excursion through every collector. -/
def sec8C4 (D : DistRd d → ContMetric d) (ξ Q b r : ℝ)
    (V : Set (Rd d)) (f : ℕ → C(Rd d, ℝ))
    (x y : Rd d) (Z : Finset (Rd d × ℕ)) (g : DistRd d) : Prop :=
  ∀ site ∈ Z,
    Exc (sec8Sel x y (D (addFun g (-F_Z f r Z))).1)
      (D g) (sec8Collector V r site.1) site.1 r
      (b * sNorm ξ Q g r site.1)

/-- The favorable event `𝓕_Z` from (C1)–(C4), prior to the Borel encoding
of the internal-distance and excursion observables. -/
def FavEvent (D Dt : DistRd d → ContMetric d) (ξ Q Cstar q R r b : ℝ)
    (J : ℕ) (N : ℕ → Set (Config d)) (V : Set (Rd d))
    (f : ℕ → C(Rd d, ℝ)) (x y : Rd d)
    (Z : Finset (Rd d × ℕ)) : Set (DistRd d) :=
  {g | sec8C1 D Dt ξ Q Cstar q R x y g ∧
    sec8C2 D Dt ξ Q q R r J N Z g ∧
    sec8C3 D x y r Z g ∧ sec8C4 D ξ Q b r V f x y Z g}

end HigherDimLQGMetric
