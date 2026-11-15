import InteractingSLE.Spec.Sec7.Lemma71ETop

/-!
# Retaining the derivative branch at a restart

Packet PROVE-AUX61-R1, ruling R71. The inherited analytic logarithm is read
at one recorded interior point. Its integer difference from the measurable
chart lift is then measurable, and correcting that integer preserves the
forward map, inverse, and domain. No principal argument is substituted.
-/

set_option autoImplicit false

noncomputable section

open Complex Set MeasureTheory

namespace InteractingSLE.Sec5.Aux61Restart

open Sec7.Lemma71E

/-- Correct a random chart to its inherited analytic derivative logarithm.
The only measurability needed of that logarithm is its imaginary part at one
recorded interior point. The corrected chart has exactly the inherited lift
throughout the component, including its integer winding. -/
theorem exists_measurable_inherited_shift
    {Ω : Type*} [MeasurableSpace Ω] {c : Ω → Chart} {L : Ω → ℂ → ℂ}
    (hDo : ∀ ω, IsOpen ((c ω).dom : Set ℂ))
    (hDc : ∀ ω, IsPreconnected ((c ω).dom : Set ℂ))
    (hlog : ∀ ω, ∃ L₀ : ℂ → ℂ, IsDerivLog (c ω).1 L₀ (c ω).dom ∧
      ∀ z ∈ (c ω).dom, (c ω).2.2 z = (L₀ z).im)
    (hL : ∀ ω, IsDerivLog (c ω).1 (L ω) (c ω).dom)
    (hdom : ∀ z, MeasurableSet {ω | z ∈ (c ω).dom})
    (hlift : ∀ z, Measurable
      ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z))
    {e : ℕ → ℂ} {N : Ω → ℕ} (hN : Measurable N)
    (hNC : ∀ ω, e (N ω) ∈ (c ω).dom)
    (hLm : Measurable fun ω => (L ω (e (N ω))).im) :
    ∃ n : Ω → ℤ, Measurable n ∧
      (∀ ω z, z ∈ (c ω).dom →
        (shiftLift (c ω) (n ω)).2.2 z = (L ω z).im) ∧
      (∀ z, Measurable ({ω | z ∈ (shiftLift (c ω) (n ω)).dom}.indicator
        fun ω => (shiftLift (c ω) (n ω)).2.2 z)) ∧
      (∀ ω, ContinuousOn (shiftLift (c ω) (n ω)).2.2 (c ω).dom) := by
  have hn : ∀ ω, ∃ n : ℤ, ∀ z ∈ (c ω).dom,
      (L ω z).im = (c ω).2.2 z + 2 * Real.pi * n := by
    intro ω
    obtain ⟨L₀, hL₀, heq⟩ := hlog ω
    obtain ⟨n, hn⟩ := exists_int_eq_lift_add (hDo ω) (hDc ω) hL₀ (hL ω)
    exact ⟨n, fun z hz => by rw [heq z hz]; exact hn z hz⟩
  choose n hn using hn
  have hnm : Measurable n := measurable_int_of_eq_add hLm
    (measurable_at_seq hN hNC hlift) (fun ω => hn ω _ (hNC ω))
  refine ⟨n, hnm, fun ω z hz => (hn ω z hz).symm,
    fun z => measurable_indicator_shiftLift hnm z (hdom z) (hlift z), ?_⟩
  intro ω
  have heq : EqOn (shiftLift (c ω) (n ω)).2.2 (fun z => (L ω z).im)
      ((c ω).dom : Set ℂ) := fun z hz => (hn ω z hz).symm
  exact (Complex.continuous_im.comp_continuousOn (hL ω).1.continuousOn).congr heq

end InteractingSLE.Sec5.Aux61Restart
