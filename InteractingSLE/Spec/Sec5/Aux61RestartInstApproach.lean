import InteractingSLE.Spec.Sec5.Aux61RestartMeasTarget

/-!
# Countable approaches selected in a retained chart collar

Packet PROVE-AUX61-R1, ruling R71. Selecting a point close to the physical tip
alone can select the wrong prime end. Instead select it close to zero in the
recorded own chart. The inverse-chart collar then identifies the access.
The same construction applies to a translated counterflow chart at its original
right-target junction. Both selections depend only on the retained records.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory
open QuantumZipper (H)

namespace InteractingSLE.Sec5.Aux61Restart

open Sec7.Lemma71E

/-- Select dense points tending to zero in a recorded chart, rather than only
in physical space. This preserves the access even for a nonsimple boundary. -/
theorem exists_measurable_chart_access_sequence
    {Ω : Type*} [MeasurableSpace Ω] {D : Ω → Set ℂ} {g : Ω → ℂ → ℂ}
    (hDo : ∀ ω, IsOpen (D ω)) (hDm : ∀ z, MeasurableSet {ω | z ∈ D ω})
    (hgc : ∀ ω, ContinuousOn (g ω) (D ω))
    (hgm : ∀ z, Measurable ({ω | z ∈ D ω}.indicator fun ω => g ω z))
    (hgH : ∀ ω, MapsTo (g ω) (D ω) H)
    (hnear : ∀ ω ε, 0 < ε → ∃ z ∈ D ω, ‖g ω z‖ < ε)
    {e : ℕ → ℂ} (he : DenseRange e) :
    ∃ N : ℕ → Ω → ℕ, (∀ n, Measurable (N n)) ∧
      (∀ n ω, e (N n ω) ∈ D ω) ∧
      ∀ ω, Tendsto (fun n => g ω (e (N n ω))) atTop (𝓝[H] 0) := by
  classical
  have hex : ∀ (n : ℕ) (ω : Ω),
      ∃ j, e j ∈ D ω ∧ ‖g ω (e j)‖ < 1 / ((n : ℝ) + 1) := by
    intro n ω
    obtain ⟨z, hz, hzg⟩ := hnear ω (1 / ((n : ℝ) + 1)) (by positivity)
    obtain ⟨j, hj⟩ := he.exists_mem_open
      ((hgc ω).isOpen_inter_preimage (hDo ω) isOpen_ball)
      ⟨z, hz, mem_ball_zero_iff.2 hzg⟩
    exact ⟨j, hj.1, mem_ball_zero_iff.1 hj.2⟩
  refine ⟨fun n ω => Nat.find (hex n ω), fun n => ?_,
    fun n ω => (Nat.find_spec (hex n ω)).1, fun ω => ?_⟩
  · apply measurable_find (hex n)
    intro j
    have heq : {ω | e j ∈ D ω ∧ ‖g ω (e j)‖ < 1 / ((n : ℝ) + 1)} =
        {ω | e j ∈ D ω} ∩ {ω |
          ‖({ω | e j ∈ D ω}.indicator fun ω => g ω (e j)) ω‖ <
            1 / ((n : ℝ) + 1)} := by
      ext ω
      by_cases h : e j ∈ D ω
      · simp only [mem_ofPred_eq, mem_inter_iff, h, indicator_of_mem, true_and]
      · simp only [mem_ofPred_eq, mem_inter_iff, h, false_and]
    rw [heq]
    exact (hDm (e j)).inter (measurableSet_lt (hgm (e j)).norm measurable_const)
  · refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n =>
      hgH ω (Nat.find_spec (hex n ω)).1⟩
    apply tendsto_iff_norm_sub_tendsto_zero.2
    simp only [sub_zero]
    exact squeeze_zero (fun n => norm_nonneg _)
      (fun n => (Nat.find_spec (hex n ω)).2.le)
      tendsto_one_div_add_atTop_nhds_zero_nat

/-- A retained inverse-chart half-disc supplies points at every chart distance
from the seed. Its radius need not be chosen measurably. -/
theorem exists_small_chart_value_of_collar {D : Set ℂ} {g F : ℂ → ℂ}
    (hinv : ∀ w ∈ H, g (F w) = w)
    (hcollar : ∃ δ > 0, MapsTo F (ball 0 δ ∩ H) D) :
    ∀ ε > 0, ∃ z ∈ D, ‖g z‖ < ε := by
  obtain ⟨δ, hδ, hfree⟩ := hcollar
  intro ε hε
  let a := min δ ε / 2
  have ha : 0 < a := half_pos (lt_min hδ hε)
  have haδ : a < δ := (half_lt_self (lt_min hδ hε)).trans_le (min_le_left _ _)
  have haε : a < ε := (half_lt_self (lt_min hδ hε)).trans_le (min_le_right _ _)
  have hwH : (a : ℂ) * I ∈ H := by
    change 0 < ((a : ℂ) * I).im
    simpa only [mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re,
      mul_zero, add_zero] using ha
  have hwn : ‖(a : ℂ) * I‖ = a := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha, norm_I, mul_one]
  have hwball : (a : ℂ) * I ∈ ball 0 δ := by
    rw [mem_ball_zero_iff, hwn]
    exact haδ
  refine ⟨F ((a : ℂ) * I), hfree ⟨hwball, hwH⟩, ?_⟩
  rw [hinv _ hwH, hwn]
  exact haε

/-- Passing from the recorded chart approach to a prime end uses the inverse
of that same chart. It never selects the component by a future path point. -/
theorem tendsto_primeEnd_of_chart_access
    {D : Set ℂ} {g F : ℂ → ℂ} {ψ : HChart D} {p : OnePoint ℝ}
    (haccess : Tendsto (ψ.1 ∘ F) (𝓝[H] 0) (PrimeEnd.approachH p))
    {x : ℕ → ℂ} (hinv : ∀ n, F (g (x n)) = x n)
    (hx : Tendsto (g ∘ x) atTop (𝓝[H] 0)) :
    Tendsto (ψ.1 ∘ x) atTop (PrimeEnd.approachH p) := by
  have h := haccess.comp hx
  exact h.congr' (Eventually.of_forall fun n => congrArg ψ.1 (hinv n))

end InteractingSLE.Sec5.Aux61Restart
