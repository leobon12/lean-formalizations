import InteractingSLE.Spec.Sec5.Aux61RestartMark

/-!
# A countable measurable certificate of current-access incidence

Packet PROVE-AUX61-R1. Incidence in a recorded open subdomain is equivalent
to that subdomain containing points whose own-chart values approach zero.
Dense-point tests make the event measurable using only masked forward maps.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory
open QuantumZipper (H)

namespace InteractingSLE.Sec5.Aux61Restart

/-- The current inverse-chart access meets the specified retained domain. -/
def currentAccessEvent {Ω : Type*} (c : Ω → Chart) (D : Ω → Set ℂ) : Set Ω :=
  {ω | ∃ᶠ w in 𝓝[H] 0, (c ω).2.1 w ∈ D ω}

/-- Current-access incidence is determined by countably many forward-chart
tests in the retained domain. No boundary extension or inverse measurability
is assumed. -/
theorem frequent_inv_mem_iff_dense_chart_values {c : Chart} (hc : c.IsConformal)
    {D : Set ℂ} (hDo : IsOpen D) (hD : D ⊆ c.dom)
    {e : ℕ → ℂ} (he : DenseRange e) :
    (∃ᶠ w in 𝓝[H] 0, c.2.1 w ∈ D) ↔
      ∀ n : ℕ, ∃ j, e j ∈ D ∧ ‖c.1 (e j)‖ < 1 / ((n : ℝ) + 1) := by
  constructor
  · intro h n
    have hε : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have hev : ∀ᶠ w in 𝓝[H] (0 : ℂ), w ∈ ball 0 (1 / ((n : ℝ) + 1)) :=
      mem_nhdsWithin_of_mem_nhds (ball_mem_nhds _ hε)
    obtain ⟨w, ⟨hwD, hwB⟩, hwH⟩ :=
      ((h.and_eventually hev).and_eventually self_mem_nhdsWithin).exists
    have hU := (hc.differentiableOn_fwd.continuousOn.mono hD).isOpen_inter_preimage
      hDo (isOpen_ball (x := (0 : ℂ)) (ε := 1 / ((n : ℝ) + 1)))
    have hwU : c.2.1 w ∈ D ∩ c.1 ⁻¹' ball 0 (1 / ((n : ℝ) + 1)) := by
      refine ⟨hwD, ?_⟩
      rw [mem_preimage, hc.2.2 w hwH]
      exact hwB
    obtain ⟨j, hj⟩ := he.exists_mem_open hU ⟨_, hwU⟩
    exact ⟨j, hj.1, by simpa only [mem_preimage, mem_ball_zero_iff] using hj.2⟩
  · intro h
    choose j hjD hjnorm using h
    have hlim : Tendsto (fun n => c.1 (e (j n))) atTop (𝓝[H] (0 : ℂ)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => hc.fwd_mem (hD (hjD n))⟩
      apply tendsto_iff_dist_tendsto_zero.2
      simpa only [dist_zero_right] using
        (squeeze_zero (fun _ => norm_nonneg _) (fun n => (hjnorm n).le)
          tendsto_one_div_add_atTop_nhds_zero_nat)
    apply hlim.frequently
    exact (Eventually.of_forall fun n => by
      rw [hc.inv_fwd (hD (hjD n))]
      exact hjD n).frequently

/-- The access event is measurable from recorded point membership and masked
forward-chart evaluations alone. -/
theorem measurableSet_currentAccessEvent
    {Ω : Type*} [MeasurableSpace Ω] {c : Ω → Chart} {D : Ω → Set ℂ}
    (hc : ∀ ω, (c ω).IsConformal) (hDo : ∀ ω, IsOpen (D ω))
    (hD : ∀ ω, D ω ⊆ (c ω).dom)
    (hDm : ∀ z, MeasurableSet {ω | z ∈ D ω})
    (hfm : ∀ z, Measurable ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z))
    {e : ℕ → ℂ} (he : DenseRange e) :
    MeasurableSet (currentAccessEvent c D) := by
  classical
  have hm := measurable_indicator_restrict_domain hDm hD hfm
  have heq : currentAccessEvent c D = ⋂ n : ℕ, ⋃ j : ℕ,
      {ω | e j ∈ D ω} ∩
        {ω | ‖({ω | e j ∈ D ω}.indicator fun ω => (c ω).1 (e j)) ω‖ <
          1 / ((n : ℝ) + 1)} := by
    ext ω
    rw [currentAccessEvent, mem_ofPred_eq,
      frequent_inv_mem_iff_dense_chart_values (hc ω) (hDo ω) (hD ω) he]
    simp only [mem_iInter, mem_iUnion, mem_inter_iff, mem_ofPred_eq]
    apply forall_congr'
    intro n
    apply exists_congr
    intro j
    apply and_congr_right
    intro hj
    rw [indicator_of_mem (show ω ∈ {ω | e j ∈ D ω} from hj)]
  rw [heq]
  exact MeasurableSet.iInter fun n => MeasurableSet.iUnion fun j =>
    (hDm (e j)).inter (measurableSet_lt (hm (e j)).norm measurable_const)

end InteractingSLE.Sec5.Aux61Restart
