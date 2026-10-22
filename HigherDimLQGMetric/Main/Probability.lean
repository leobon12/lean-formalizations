import HigherDimLQGMetric.Main.Existence
import Mathlib.Topology.MetricSpace.Sequences

/-!
# Probability limits used in the final LFPP assembly

Dimension-independent ports of the sub-subsequence and coordinate-evaluation
arguments in `LQGMetric.Papers.GM.S1.Subseq` and `.Median`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- Local uniform convergence in probability implies convergence of one point distance. -/
theorem l10a_tendstoInMeasure_eval {d : ℕ} {Ω ι : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {X : ι → Ω → Rd d × Rd d → ℝ}
    {Y : Ω → Rd d × Rd d → ℝ} {l : Filter ι} {p : Rd d × Rd d}
    {R : ℝ} (hR : 0 < R)
    (hp : p ∈ Metric.closedBall (0 : Rd d) R ×ˢ Metric.closedBall (0 : Rd d) R)
    (h : TendstoInProbLU P X l Y) :
    TendstoInMeasure P (fun i ω => X i ω p) l (fun ω => Y ω p) := by
  rw [tendstoInMeasure_iff_dist]
  intro δ hδ
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (h R hR δ hδ) (fun _ => bot_le) (fun i => measure_mono fun ω hω => ?_)
  have h1 : edist (X i ω p) (Y ω p) ≤
      ⨆ q ∈ Metric.closedBall (0 : Rd d) R ×ˢ Metric.closedBall (0 : Rd d) R,
        edist (X i ω q) (Y ω q) :=
    le_iSup₂ (f := fun q _ => edist (X i ω q) (Y ω q)) p hp
  exact (show ENNReal.ofReal δ ≤ edist (X i ω p) (Y ω p) by
    rw [edist_dist]
    exact ENNReal.ofReal_le_ofReal_iff (by positivity) |>.2 hω).trans h1

/-- An almost-sure change of the limit preserves local uniform convergence in probability. -/
theorem l10a_tip_congr {d : ℕ} {Ω ι : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ι → Ω → Rd d × Rd d → ℝ) (l : Filter ι)
    {Y Y' : Ω → Rd d × Rd d → ℝ}
    (h : TendstoInProbLU P X l Y) (hYY' : ∀ᵐ ω ∂P, Y ω = Y' ω) :
    TendstoInProbLU P X l Y' := by
  intro R hR δ hδ
  refine (h R hR δ hδ).congr fun i => measure_congr ?_
  filter_upwards [hYY'] with ω hω
  simp only [hω]

/-- If every real sequence decreasing to zero has a subsequence with the same
probability limit, the whole real-cutoff family converges. -/
theorem l10a_subseq_principle {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℝ → Ω → Rd d × Rd d → ℝ)
    (Y : Ω → Rd d × Rd d → ℝ)
    (H : ∀ ε : ℕ → ℝ, (∀ n, 0 < ε n) → Tendsto ε atTop (𝓝 0) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        TendstoInProbLU P (fun n => X (ε (φ n))) atTop Y) :
    TendstoInProbLU P X (𝓝[>] 0) Y := by
  intro R hR δ hδ
  refine tendsto_of_subseq_tendsto fun x hx => ?_
  obtain ⟨hx0, hxpos⟩ := tendsto_nhdsWithin_iff.1 hx
  obtain ⟨N, hN⟩ := eventually_atTop.1 hxpos
  obtain ⟨φ, -, hT⟩ := H (fun n => x (n + N))
    (fun n => hN _ (Nat.le_add_left N n))
    ((tendsto_add_atTop_iff_nat N).2 hx0)
  exact ⟨fun n => φ n + N, hT R hR δ hδ⟩

end HigherDimLQGMetric
