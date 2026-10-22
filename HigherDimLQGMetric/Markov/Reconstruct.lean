import HigherDimLQGMetric.Markov.MeasSphere
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-! Reconstructing a continuous exterior process from countably many measurable point values. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric TopologicalSpace Filter
open scoped RealInnerProductSpace Topology
open HigherDimLFPP (Rd)

namespace HigherDimLQGMetric

/-- A continuous process on an open set whose point values have measurable versions in a
smaller sigma algebra has a single measurable version as a full function. -/
theorem markov_exists_measurable_contVersion {d : ℕ} {Ω : Type}
    [m : MeasurableSpace Ω] (P : Measure Ω) (s : MeasurableSpace Ω)
    (O : Opens (Rd d)) (Y : Ω → Rd d → ℝ)
    (hYc : ∀ ω, ContinuousOn (Y ω) O)
    (hY0 : ∀ ω x, x ∉ O → Y ω x = 0)
    (hYm : ∀ x (_hx : x ∈ O),
      AEStronglyMeasurable[s] (fun ω => Y ω x) P) :
    ∃ G : Ω → Rd d → ℝ, Measurable[s] G ∧ Y =ᵐ[P] G := by
  classical
  obtain ⟨D, hDc, hDd⟩ := exists_countable_dense (O : Set (Rd d))
  haveI : Countable D := hDc.to_subtype
  let M : D → Ω → ℝ := fun q =>
    (hYm (q.1 : Rd d) q.1.2).mk (fun ω => Y ω (q.1 : Rd d))
  have hMm (q : D) : Measurable[s] (M q) :=
    (hYm (q.1 : Rd d) q.1.2).measurable_mk
  have hMae (q : D) : (fun ω => Y ω (q.1 : Rd d)) =ᵐ[P] M q :=
    (hYm (q.1 : Rd d) q.1.2).ae_eq_mk
  have hGood : ∀ᵐ ω ∂P, ∀ q : D, M q ω = Y ω (q.1 : Rd d) := by
    rw [ae_all_iff]
    intro q
    filter_upwards [hMae q] with ω hω
    exact hω.symm
  have hSeq (x : O) : ∃ u : ℕ → D,
      Tendsto (fun n => ((u n : D).1 : O)) atTop (𝓝 x) := by
    obtain ⟨u, hu, hux⟩ := mem_closure_iff_seq_limit.mp (hDd x)
    exact ⟨fun n => ⟨u n, hu n⟩, hux⟩
  let u (x : O) : ℕ → D := Classical.choose (hSeq x)
  have hu (x : O) : Tendsto (fun n => ((u x n : D).1 : O)) atTop (𝓝 x) :=
    Classical.choose_spec (hSeq x)
  let G : Ω → Rd d → ℝ := fun ω x =>
    if hx : x ∈ O then limsup (fun n => M (u ⟨x, hx⟩ n) ω) atTop else 0
  have hGm : Measurable[s] G := by
    rw [measurable_pi_iff]
    intro x
    by_cases hx : x ∈ O
    · have hm : Measurable[s] fun ω =>
          limsup (fun n => M (u ⟨x, hx⟩ n) ω) atTop :=
        Measurable.limsup fun n => hMm (u ⟨x, hx⟩ n)
      simpa only [G, dite_eq_left hx] using hm
    · simpa only [G, dite_eq_right hx] using
        (measurable_const : Measurable[s] fun _ : Ω => (0 : ℝ))
  refine ⟨G, hGm, ?_⟩
  filter_upwards [hGood] with ω hω
  funext x
  by_cases hx : x ∈ O
  · have ht : Tendsto (fun n => Y ω ((u ⟨x, hx⟩ n : D).1 : Rd d))
        atTop (𝓝 (Y ω x)) := by
      have hux : Tendsto (fun n => ((u ⟨x, hx⟩ n : D).1 : Rd d))
          atTop (𝓝 x) := by
        exact (continuous_subtype_val.tendsto ⟨x, hx⟩).comp (hu ⟨x, hx⟩)
      exact ((hYc ω).continuousAt (O.isOpen.mem_nhds hx)).tendsto.comp hux
    have ht' : Tendsto (fun n => M (u ⟨x, hx⟩ n) ω)
        atTop (𝓝 (Y ω x)) := by
      simpa only [hω] using ht
    simp only [G, dite_eq_left hx, ht'.limsup_eq]
  · simp [G, hx, hY0 ω x hx]

end HigherDimLQGMetric
