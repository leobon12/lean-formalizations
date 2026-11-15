import InteractingSLE.Spec.Sec5.Aux61RestartInstActual

/-!
# The inherited branch for the actual own-history chart

Packet PROVE-AUX61-R1; Astra follow-up 4, section 1.1. In the factorization
`restart = additional ∘ own`, the inherited logarithm is literally
`L_additional ∘ own + logDerivFwd`. Given the additional inherited branch and
its measurable value at one recorded interior point, the measurable chart is
corrected to this exact sum on the whole retained component. There is no
reduction modulo `2π` and no new choice of principal argument.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory
open QuantumZipper (H logDerivFwd fwdHull)
open scoped NNReal

namespace InteractingSLE.Sec5.Aux61Restart

open Sec7.Lemma71E

/-- The original, continuously inherited own derivative logarithm. -/
def ownDerivativeLog {Ω : Type*} (U : ℝ≥0 → Ω → ℝ) (r : ℝ≥0) (ω : Ω) : ℂ → ℂ :=
  logDerivFwd (Ito.rpath (U · ω)) r

/-- The own chart domain is the complement of its actual filled hull. -/
theorem coe_dom_ownHistoryChart {Ω : Type*} {U : ℝ≥0 → Ω → ℝ}
    (hUc : ∀ ω, Continuous fun t => U t ω) (hU0 : ∀ ω, U 0 ω = 0)
    (r : ℝ≥0) (ω : Ω) :
    ((ownHistoryChart U r ω).dom : Set ℂ) = H \ fwdHull (Ito.rpath (U · ω)) r := by
  rw [(Chart.isConformal_loewnerChartAtTime hUc hU0 ω).coe_dom]
  exact QuantumZipper.RS.image_fwdMapInv_H (Chart.continuous_rpath_of_continuous (hUc ω))
    (Chart.rpath_zero_of (hU0 ω)) r.coe_nonneg

/-- The branch used by the original own chart is the hydrodynamic derivative
logarithm of that original prefix, not a principal logarithm chosen at restart. -/
theorem isDerivLog_ownHistoryChart {Ω : Type*} {U : ℝ≥0 → Ω → ℝ}
    (hUc : ∀ ω, Continuous fun t => U t ω) (hU0 : ∀ ω, U 0 ω = 0)
    (r : ℝ≥0) (ω : Ω) :
    IsDerivLog (ownHistoryChart U r ω).1 (ownDerivativeLog U r ω)
      (ownHistoryChart U r ω).dom := by
  rw [coe_dom_ownHistoryChart hUc hU0]
  exact isDerivLog_fwdMap (Chart.continuous_rpath_of_continuous (hUc ω)) r.coe_nonneg

/-- The chart lift records the imaginary part of that exact own branch. -/
theorem ownHistoryChart_lift {Ω : Type*} (U : ℝ≥0 → Ω → ℝ) (r : ℝ≥0)
    (ω : Ω) (z : ℂ) : (ownHistoryChart U r ω).2.2 z = (ownDerivativeLog U r ω z).im := by
  change (logDerivFwd (Ito.rpath (U · ω)) r z).im + 0 = _
  exact add_zero _

/-- Match the restart chart to the actual chain-rule branch. The additional
logarithm is explicit data; constructing its canonical collar normalization
from the retained hull is a separate geometric obligation, not assumed proved
by this conditional adapter. -/
theorem exists_measurable_own_inherited_shift
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {U : ℝ≥0 → Ω → ℝ} {r : ℝ≥0}
    (hUc : ∀ ω, Continuous fun t => U t ω) (hU0 : ∀ ω, U 0 ω = 0)
    (hUm : ∀ t ≤ r, Measurable (U t)) {c : Ω → Chart}
    (hDo : ∀ ω, IsOpen ((c ω).dom : Set ℂ))
    (hDc : ∀ ω, IsPreconnected ((c ω).dom : Set ℂ))
    (hown : ∀ ω, (c ω).dom ≤ (ownHistoryChart U r ω).dom)
    (hlog : ∀ ω, ∃ L : ℂ → ℂ, IsDerivLog (c ω).1 L (c ω).dom ∧
      ∀ z ∈ (c ω).dom, (c ω).2.2 z = (L z).im)
    (hdom : ∀ z, MeasurableSet {ω | z ∈ (c ω).dom})
    (hlift : ∀ z, Measurable
      ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z))
    {G LG : Ω → ℂ → ℂ} {E : Ω → Set ℂ} (hEo : ∀ ω, IsOpen (E ω))
    (hG : ∀ ω, DifferentiableOn ℂ (G ω) (E ω))
    (hLG : ∀ ω, IsDerivLog (G ω) (LG ω) (E ω))
    (hmaps : ∀ ω, MapsTo (ownHistoryChart U r ω).1 (c ω).dom (E ω))
    (hfactor : ∀ ω, EqOn (G ω ∘ (ownHistoryChart U r ω).1) (c ω).1 (c ω).dom)
    {e : ℕ → ℂ} {N : Ω → ℕ} (hN : Measurable N)
    (hNC : ∀ ω, e (N ω) ∈ (c ω).dom)
    (hLGm : Measurable fun ω => (LG ω ((ownHistoryChart U r ω).1 (e (N ω)))).im) :
    ∃ n : Ω → ℤ, Measurable n ∧
      (∀ ω z, z ∈ (c ω).dom → (shiftLift (c ω) (n ω)).2.2 z =
        (LG ω ((ownHistoryChart U r ω).1 z) + ownDerivativeLog U r ω z).im) ∧
      (∀ z, Measurable ({ω | z ∈ (shiftLift (c ω) (n ω)).dom}.indicator
        fun ω => (shiftLift (c ω) (n ω)).2.2 z)) ∧
      (∀ ω, ContinuousOn (shiftLift (c ω) (n ω)).2.2 (c ω).dom) := by
  have hL : ∀ ω, IsDerivLog (c ω).1
      (fun z => LG ω ((ownHistoryChart U r ω).1 z) + ownDerivativeLog U r ω z)
      (c ω).dom := by
    intro ω
    have hO := Chart.isConformal_loewnerChartAtTime (τ := fun _ => r) hUc hU0 ω
    have h := IsDerivLog.comp (hDo ω) (hEo ω) (hG ω)
      (hO.differentiableOn_fwd.mono (hown ω)) (hmaps ω) (hLG ω)
      ((isDerivLog_ownHistoryChart hUc hU0 r ω).mono (hown ω))
    exact IsDerivLog.congr_of_eqOn (hDo ω) h (hfactor ω) (fun _ _ => rfl)
  have hOm := Chart.measurable_indicator_lift_loewnerChartAtTime (le_refl mΩ) hUc hU0
    (τ := fun _ => r) measurable_const (fun t => hUm (min t r) (min_le_right _ _))
  have hanchor := measurable_at_seq hN (fun ω => hown ω (hNC ω)) hOm
  have hLm : Measurable fun ω =>
      (LG ω ((ownHistoryChart U r ω).1 (e (N ω))) +
        ownDerivativeLog U r ω (e (N ω))).im := by
    simp only [add_im]
    exact hLGm.add (by simpa only [ownHistoryChart_lift] using hanchor)
  exact exists_measurable_inherited_shift hDo hDc hlog hL hdom hlift hN hNC hLm

end InteractingSLE.Sec5.Aux61Restart
