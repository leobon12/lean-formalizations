/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2JdChart
import InteractingSLE.Spec.Supplement.SB2LrFwd
import InteractingSLE.Spec.Supplement.SB2LvStep

/-!
# SB2(2)'s joint stage induction (D29): the stage curve's start and end through the relative run chart

Packet PROVE-SB2-LIFTSET (round 19). At a lockstep stage the run-chart stage values at good times are the relative run
chart applied to the lift of the piece. Near the start (the lifted seed, `ι` of B's seed, is the relative current
point) and near the end of a finite piece (the lifted end point, a real point beyond the relative record) the relative
run chart is continuous from `ℍ` (`continuousWithinAt_runChart_fwd`: real points that every earlier relative piece
leaves alive and that stay off the closures of the earlier fills). Hence:

* `stChart_moveAlong_self`: after a connector the chart reads `0` at the new current point;
* **`tendsto_relValp_of_continuousWithinAt`**: the run-chart values along the good times tend to the chart's value at
  the limit of the lifted points;
* **`tendsto_of_dense_eq`**: a continuous curve equal along a set of parameters dense near `∞` to a function with a
  limit there has that limit (the end of a finite stage curve).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.SB.Lk

open Exist Exist.Staged Exist.StagedLaw LuM GW1W GW1Bookkeep

/-- **After a connector the chart reads `0` at the new current point** (a real chart). -/
theorem stChart_moveAlong_self {s : ExplState} (hs : IsRealChart (stChart s)) (r : Bool) (w : ℝ) (mk : Bool) :
    (stChart (ExplState.moveAlong s r w mk)).1 w = 0 := by
  rw [stChart_moveAlong']
  show (stChart s).1 w - (((stChart s).1 w).re : ℂ) = 0
  rw [hs.eq_ofReal w]
  simp

variable {c : Chart} {m : ℝ} {p : ℝ≥0 → ℂ} {L : ℝ≥0∞} {s₂ : ExplState}

/-- **The run-chart values along the good times tend to the chart's value at the lifted limit.** -/
theorem tendsto_relValp_of_continuousWithinAt {G : Set ℝ≥0} {t₀ : ℝ≥0} {w : ℂ}
    (hcw : ContinuousWithinAt (stChart s₂).1 H w)
    (hlift : Tendsto (fun t => liftPt c m (p t)) (𝓝[G] t₀) (𝓝 w))
    (hH : ∀ t ∈ G, liftPt c m (p t) ∈ H) :
    Tendsto (relValp c m p s₂) (𝓝[G] t₀) (𝓝 ((stChart s₂).1 w)) :=
  hcw.tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hlift, eventually_nhdsWithin_of_forall hH⟩)

/-- **A continuous curve equal, on a set of parameters dense near `∞`, to a function with a limit at `∞` has that
limit.** -/
theorem tendsto_of_dense_eq {ρ g : ℝ → ℂ} {G : Set ℝ} {v : ℂ} (hc : ContinuousOn ρ (Ici 0))
    (hdense : ∀ u, 0 ≤ u → u ∈ closure (G ∩ Ici u)) (heq : ∀ u ∈ G, ρ u = g u)
    (hg : Tendsto g (atTop ⊓ 𝓟 G) (𝓝 v)) : Tendsto ρ atTop (𝓝 v) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨U, -, hU⟩ := (Filter.HasBasis.tendsto_iff (atTop_basis.inf_principal G) Metric.nhds_basis_ball).1 hg
    (ε / 2) (half_pos hε)
  refine ⟨max U 0, fun u hu => ?_⟩
  have hu0 : 0 ≤ u := (le_max_right U 0).trans hu
  have hmem := hdense u hu0
  have hcw : ContinuousWithinAt ρ (G ∩ Ici u) u :=
    (hc u (mem_Ici.2 hu0)).mono fun x hx => mem_Ici.2 (hu0.trans hx.2)
  have hcl : ρ u ∈ closure (ρ '' (G ∩ Ici u)) := hcw.mem_closure_image hmem
  have hsub : ρ '' (G ∩ Ici u) ⊆ Metric.closedBall v (ε / 2) := by
    rintro _ ⟨x, ⟨hxG, hxu⟩, rfl⟩
    rw [heq x hxG]
    exact Metric.ball_subset_closedBall (hU x ⟨(le_max_left U 0).trans (hu.trans hxu), hxG⟩)
  have := Metric.isClosed_closedBall.closure_subset_iff.2 hsub hcl
  rw [Metric.mem_closedBall] at this
  linarith

end InteractingSLE.Theorem14.SB.Lk
