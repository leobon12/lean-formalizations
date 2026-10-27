import MatedCRTHarmonic.CellFamily.Interfaces
import MatedCRTHarmonic.CellFamily.WaypointIteratedMarkov
import MatedCRTHarmonic.CellFamily.WaypointNet

/-!
# Corrected waypoint strong-Markov interface for the scaled-grid estimate

This is the repaired statement proposed for the owning `CellFamily/Interfaces.lean` file. The environment net covers
the whole annular region containing every rotated polar template. The `⌈11600/s₀⌉` points are chosen separately
from that net for each starting cell and its template. The small-mesh restrictions prevent the vacuous `k = 0`
counterexample, and `mesh^q ≤ s₀ r/100` is the exact diameter-to-confinement scale needed in the waypoint argument.

`GraphConnected` is the landed almost-sure graph hypothesis. Looplessness is also needed because
`RouteM.IsTemplateWalk.adj` is strict adjacency whereas the edge-end walk may stay at a vertex by traversing a loop;
the following-curve argument explicitly restricts its following-curve construction to walks with no loops. The producer of the latter
is the mated-CRT graph identification. This proposition is conditional on these two graph inputs and asks for the
pathwise implication only on outcomes where both graph properties hold.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.CellFamily

/-- The explicit polar net also supplies the ball-containment clause in the fixed interface, since
its centers lie within `1.15r` of `z` and the required radius is `r/100`. -/
theorem waypoint_fixed2_environment_net (z : ℂ) {r s₀ ρ : ℝ}
    (hr : 0 < r) (hs₀ : 0 < s₀) (hs₀le : s₀ ≤ 1 / 10)
    (hball : ball z (2 * r) ⊆ ball (0 : ℂ) ρ) :
    ∃ W : Finset ℂ,
      W.card ≤ ⌈4 * 10 ^ 5 / s₀ ^ 2⌉₊ ∧
      (∀ w ∈ W, 0.85 * r ≤ ‖w - z‖ ∧ ‖w - z‖ ≤ 1.15 * r) ∧
      (∀ y, 0.85 * r ≤ ‖y - z‖ → ‖y - z‖ ≤ 1.15 * r →
        ∃ w ∈ W, ‖w - y‖ ≤ s₀ * r / 200) ∧
      (∀ w ∈ W, ball w (r / 100) ⊆ ball (0 : ℂ) ρ) := by
  obtain ⟨W, hcard, hann, hcover⟩ := exists_waypoint_polar_annular_net z hr hs₀ hs₀le
  refine ⟨W, hcard, ?_, ?_, ?_⟩
  · intro w hw
    have h := hann w hw
    norm_num at h ⊢
    exact h
  · intro y hylo hyhi
    have h₁ : (17 / 20) * r ≤ ‖y - z‖ := by norm_num at hylo ⊢; exact hylo
    have h₂ : ‖y - z‖ ≤ (23 / 20) * r := by norm_num at hyhi ⊢; exact hyhi
    exact hcover y h₁ h₂
  · intro w hw x hx
    have hxw : ‖x - w‖ < r / 100 := by
      simpa [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hx
    have hwz : ‖w - z‖ ≤ (23 / 20) * r := (hann w hw).2
    have hxz : ‖x - z‖ < 2 * r := by
      have htri := norm_sub_le_norm_sub_add_norm_sub x w z
      nlinarith
    apply hball
    simpa [Metric.mem_ball, dist_eq_norm] using hxz

/-- Almost-sure absence of loop edges, as required to turn the edge-end walk's equal-or-adjacent vertex steps into
the strict adjacency demanded by `RouteM.IsTemplateWalk`. Source: the following-curve argument, following-curve construction, which
assumes the vertex walk has no loops. The mated-CRT graph identification supplies this property. -/
def GraphLoopless (F : RandomCellFamily) : Prop :=
  ∀ k, ∀ᵐ ω ∂F.P, ∀ e : F.E k ω, (F.G k ω).src e ≠ (F.G k ω).tgt e

/-- Corrected scaled-grid estimate waypoint input. `W` is the finite environment net of the waypoint construction, with mesh
`s₀ r/200 = r₀/2`; it covers the annulus containing the scaled, rotated template and is independent of the starting
vertex. For an individual start, the proof selects `m₀ = ⌈11600/s₀⌉` waypoints from this net. -/
def WaypointStrongMarkovInputFixed (F : RandomCellFamily) (q ρ : ℝ) : Prop :=
  GraphConnected F → GraphLoopless F →
  ∀ (β₈ A₈ : ℝ), ∃ s₀ βᵢ : ℝ,
    0 < s₀ ∧ s₀ ≤ 1 / 10 ∧ 0 < βᵢ ∧ βᵢ < β₈ ∧ βᵢ < q ∧
    A₈ / Real.sqrt (Real.log s₀⁻¹) ≤ 1 / 2 ∧
    ∀ k (z : ℂ) (r : ℝ),
      mesh k ^ β₈ ≤ r / 100 →
      mesh k ^ β₈ ≤ s₀ →
      mesh k ^ q ≤ s₀ * r / 100 →
      r / 100 ≤ ρ →
      ball z (2 * r) ⊆ ball (0 : ℂ) ρ →
      ∃ W : Finset ℂ,
        W.card ≤ ⌈4 * 10 ^ 5 / s₀ ^ 2⌉₊ ∧
        (∀ w ∈ W, 0.85 * r ≤ ‖w - z‖ ∧ ‖w - z‖ ≤ 1.15 * r) ∧
        (∀ y, 0.85 * r ≤ ‖y - z‖ → ‖y - z‖ ≤ 1.15 * r →
          ∃ w ∈ W, ‖w - y‖ ≤ s₀ * r / 200) ∧
        (∀ w ∈ W, ball w (r / 100) ⊆ ball (0 : ℂ) ρ) ∧
        ∀ ω, (F.G k ω).adj.Connected →
          (∀ e : F.E k ω, (F.G k ω).src e ≠ (F.G k ω).tgt e) →
          ω ∈ DiameterGood F k q ρ →
          (∀ w ∈ W, ω ∈ Lemma38EnvironmentGood F k w (r / 100) β₈ A₈) →
          ω ∈ PolarItineraryGood F k z r s₀

/-- Positive-exponent repair of `WaypointStrongMarkovInputFixed`. The lower scale endpoint and the witness
`0 < βᵢ < β₈` force `β₈ > 0`; likewise `βᵢ < q` forces `q > 0`. Those facts must be hypotheses of the outer
quantifier, since otherwise even a valid geometric producer cannot supply the requested witness. -/
def WaypointStrongMarkovInputFixed2 (F : RandomCellFamily) (q ρ : ℝ) : Prop :=
  GraphConnected F → GraphLoopless F →
  ∀ (β₈ A₈ : ℝ), 0 < β₈ → 0 < q → ∃ s₀ βᵢ : ℝ,
    0 < s₀ ∧ s₀ ≤ 1 / 10 ∧ 0 < βᵢ ∧ βᵢ < β₈ ∧ βᵢ < q ∧
    A₈ / Real.sqrt (Real.log s₀⁻¹) ≤ 1 / 2 ∧
    ∀ k (z : ℂ) (r : ℝ),
      mesh k ^ β₈ ≤ r / 100 →
      mesh k ^ β₈ ≤ s₀ →
      mesh k ^ q ≤ s₀ * r / 100 →
      r / 100 ≤ ρ →
      ball z (2 * r) ⊆ ball (0 : ℂ) ρ →
      ∃ W : Finset ℂ,
        W.card ≤ ⌈4 * 10 ^ 5 / s₀ ^ 2⌉₊ ∧
        (∀ w ∈ W, 0.85 * r ≤ ‖w - z‖ ∧ ‖w - z‖ ≤ 1.15 * r) ∧
        (∀ y, 0.85 * r ≤ ‖y - z‖ → ‖y - z‖ ≤ 1.15 * r →
          ∃ w ∈ W, ‖w - y‖ ≤ s₀ * r / 200) ∧
        (∀ w ∈ W, ball w (r / 100) ⊆ ball (0 : ℂ) ρ) ∧
        ∀ ω, (F.G k ω).adj.Connected →
          (∀ e : F.E k ω, (F.G k ω).src e ≠ (F.G k ω).tgt e) →
          ω ∈ DiameterGood F k q ρ →
          (∀ w ∈ W, ω ∈ Lemma38EnvironmentGood F k w (r / 100) β₈ A₈) →
          ω ∈ PolarItineraryGood F k z r s₀

/-- At the chosen mesoscopic scale, Lemma 3.8's quenched lower bound is at least one half for
every starting vertex in the required four-inner-radii entrance disk. -/
theorem waypoint_lemma38_half
    (F : RandomCellFamily) (k : ℕ) (ω : F.Ω) (z : ℂ) (r s₀ β₈ A₈ : ℝ)
    (hgood : ω ∈ Lemma38EnvironmentGood F k z (r / 100) β₈ A₈)
    (hscale : mesh k ^ β₈ ≤ s₀) (hs₀ : s₀ ≤ 1 / 10)
    (hA : A₈ / Real.sqrt (Real.log s₀⁻¹) ≤ 1 / 2)
    (x : ℤ)
    (hx : x ∈ verticesMeeting (F.H k ω).cell (ball z (4 * s₀ * (r / 100)))) :
    ENNReal.ofReal (1 / 2 : ℝ) ≤
      (F.G k ω).walkLaw x {ω' | HitsBefore (F.H k ω).cell z s₀ (r / 100)
        ((F.G k ω).vertexPath ω')} := by
  have hraw := hgood s₀ ⟨hscale, hs₀⟩ x hx
  have hreal : (1 / 2 : ℝ) ≤ 1 - A₈ / Real.sqrt (Real.log s₀⁻¹) := by linarith
  exact (ENNReal.ofReal_le_ofReal hreal).trans (by
    simpa [Lemma38EnvironmentGood] using hraw)

/-- The scale restriction rules out the former `k = 0` vacuity: for positive `β₈`, `mesh 0 ^ β₈ = 1`,
which cannot be at most `s₀ ≤ 1/10`. -/
theorem waypointFixed2_excludes_zero_mesh_scale {β₈ s₀ : ℝ}
    (hβ₈ : 0 < β₈) (hs₀ : s₀ ≤ 1 / 10) :
    ¬ mesh 0 ^ β₈ ≤ s₀ := by
  have hmesh : mesh 0 = 1 := by norm_num [mesh]
  rw [hmesh, Real.one_rpow]
  linarith

/-- The proposed fixed input is false as currently quantified: its witness requires `0 < βᵢ < β₈`,
but the outer quantifier permits `β₈ = 0`. This contradiction is independent of all walk, cell,
and probability data. The interface should quantify only over positive `β₈` and `q`. -/
theorem not_waypointStrongMarkovInputFixed_of_graph_hypotheses
    (F : RandomCellFamily) (q ρ : ℝ)
    (hconn : GraphConnected F) (hloop : GraphLoopless F) :
    ¬ WaypointStrongMarkovInputFixed F q ρ := by
  intro h
  obtain ⟨s₀, βᵢ, _, _, hβᵢ, hβᵢβ₈, _, _, _⟩ := h hconn hloop 0 0
  exact (not_lt_of_ge (le_of_lt hβᵢβ₈)) hβᵢ

end MatedCRTHarmonic.CellFamily

