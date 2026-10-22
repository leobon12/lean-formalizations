import HigherDimLQGMetric.Sec4.Basic
import HigherDimLQGMetric.Main.LFPPMedian

/-!
# Path bridge between `lfppDistIn` and `HigherDimLFPP.lfppDistOn` (packet L9b; IA1 "Path bridge obligation")

The B4 interface distance `lfppDistIn κ ξ ε h V x y` is `ℝ≥0∞`-valued and equals `⊤` when no piecewise `C¹` path
in `V` joins `x` to `y`, while HigherDimLFPP's `lfppDistOn` is real-valued with junk value `0` in that case, so the
two agree only for joinable endpoints. This file states the bridge in that form (no openness of `V` is needed),
its almost-sure version for normalized LGFs, and the joinability facts for the domains of `Prop42Shape`
(bounded open connected `U`, its thickenings, and the endpoint balls `B_δ(z)`, `B_δ(w)` with `z, w ∈ U`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd PcwJoined lfppDistOn)

variable {d : ℕ}

section Bridge

variable {κ : Rd d → ℝ} {ξ ε : ℝ} {h : DistRd d} {V : Set (Rd d)} {x y : Rd d}

/-- **Path bridge** (IA1): for endpoints joined by a piecewise `C¹` path in `V`, the extended internal LFPP
distance of the B4 interface is the `ofReal` of HigherDimLFPP's real-valued `lfppDistOn`. -/
theorem lfppDistIn_eq_ofReal_lfppDistOn (hc : Continuous (convMollify κ ε h))
    (hj : PcwJoined V x y) :
    lfppDistIn κ ξ ε h V x y = ENNReal.ofReal (lfppDistOn ξ (convMollify κ ε h) V x y) :=
  fieldDistIn_eq_ofReal hc hj

/-- without an admissible path the B4 distance is `⊤` (where `lfppDistOn` has the junk value `0`) -/
theorem lfppDistIn_eq_top_of_not_pcwJoined (hj : ¬ PcwJoined V x y) :
    lfppDistIn κ ξ ε h V x y = ⊤ :=
  fieldDistIn_eq_top hj

theorem lfppDistIn_lt_top_of_pcwJoined (hc : Continuous (convMollify κ ε h))
    (hj : PcwJoined V x y) : lfppDistIn κ ξ ε h V x y < ⊤ := by
  rw [lfppDistIn_eq_ofReal_lfppDistOn hc hj]
  exact ENNReal.ofReal_lt_top

end Bridge

/-- **Path bridge, almost surely**: for a normalized LGF and `ε > 0`, almost surely the bridge holds for every
domain and every joinable pair (the convolution field is a.s. continuous). -/
theorem ae_lfppDistIn_eq_ofReal_lfppDistOn (hd : 2 ≤ d) {κ : Rd d → ℝ}
    (hκ : HigherDimLFPP.IsLFPPKernel κ) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistRd d} (hh : IsNormalizedLGF h P) (ξ : ℝ) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᵐ ω ∂P, ∀ (V : Set (Rd d)) (x y : Rd d), PcwJoined V x y →
      lfppDistIn κ ξ ε (h ω) V x y =
        ENNReal.ofReal (lfppDistOn ξ (convMollify κ ε (h ω)) V x y) := by
  filter_upwards [l10a_ae_continuous_convMollify hd κ hκ P h hh hε] with ω hc V x y hj
  exact lfppDistIn_eq_ofReal_lfppDistOn hc hj

/-- thickenings of preconnected sets are preconnected -/
theorem l9b_isPreconnected_thickening {U : Set (Rd d)} (hU : IsPreconnected U) (δ : ℝ) :
    IsPreconnected (thickening δ U) := by
  rcases U.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · rw [thickening_empty]
    exact isPreconnected_empty
  by_cases hδ : 0 < δ
  · refine isPreconnected_of_forall x₀ fun y hy => ?_
    obtain ⟨u, hu, hyu⟩ := mem_thickening_iff.1 hy
    refine ⟨U ∪ ball u δ, union_subset (self_subset_thickening hδ U)
      (fun v hv => mem_thickening_iff.2 ⟨u, hu, hv⟩), Or.inl hx₀, Or.inr (mem_ball.2 hyu), ?_⟩
    exact IsPreconnected.union u hu (mem_ball_self hδ) hU (convex_ball u δ).isPreconnected
  · rw [thickening_of_nonpos (not_lt.1 hδ)]
    exact isPreconnected_empty

/-- any two points of a thickening of a preconnected set are joined by a piecewise `C¹` path in it -/
theorem l9b_pcwJoined_thickening {U : Set (Rd d)} (hU : IsPreconnected U) {δ : ℝ} {x y : Rd d}
    (hx : x ∈ thickening δ U) (hy : y ∈ thickening δ U) : PcwJoined (thickening δ U) x y :=
  DGZ.pcwJoined_of_isPreconnected isOpen_thickening (l9b_isPreconnected_thickening hU δ) hx hy

/-- the endpoint balls of `Prop42Shape` are joined inside the thickening -/
theorem l9b_pcwJoined_thickening_ball {U : Set (Rd d)} (hU : IsPreconnected U) {δ : ℝ}
    {z w x y : Rd d} (hz : z ∈ U) (hw : w ∈ U) (hx : x ∈ ball z δ) (hy : y ∈ ball w δ) :
    PcwJoined (thickening δ U) x y :=
  l9b_pcwJoined_thickening hU (mem_thickening_iff.2 ⟨z, hz, hx⟩) (mem_thickening_iff.2 ⟨w, hw, hy⟩)

section Domains

variable {κ : Rd d → ℝ} {ξ ε : ℝ} {h : DistRd d}

/-- the set-distance bridge on the domains of `Prop42Shape` -/
theorem lfppSetDistIn_thickening_eq_ofReal (hc : Continuous (convMollify κ ε h)) {U : Set (Rd d)}
    (hU : IsPreconnected U) (δ : ℝ) {z w : Rd d} (hz : z ∈ U) (hw : w ∈ U) :
    lfppSetDistIn κ ξ ε h (thickening δ U) (ball z δ) (ball w δ) =
      ⨅ (x ∈ ball z δ) (y ∈ ball w δ),
        ENNReal.ofReal (lfppDistOn ξ (convMollify κ ε h) (thickening δ U) x y) := by
  rw [lfppSetDistIn_eq_fieldSetDistIn]
  unfold fieldSetDistIn
  refine iInf_congr fun x => iInf_congr fun hx => iInf_congr fun y => iInf_congr fun hy => ?_
  exact fieldDistIn_eq_ofReal hc (l9b_pcwJoined_thickening_ball hU hz hw hx hy)

/-- the point bridge on an open preconnected `U` -/
theorem lfppDistIn_open_eq_ofReal (hc : Continuous (convMollify κ ε h)) {U : Set (Rd d)}
    (hUo : IsOpen U) (hU : IsPreconnected U) {z w : Rd d} (hz : z ∈ U) (hw : w ∈ U) :
    lfppDistIn κ ξ ε h U z w = ENNReal.ofReal (lfppDistOn ξ (convMollify κ ε h) U z w) :=
  lfppDistIn_eq_ofReal_lfppDistOn hc (DGZ.pcwJoined_of_isPreconnected hUo hU hz hw)

end Domains

end HigherDimLQGMetric
