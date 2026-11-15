/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FlowStopIdentCMIConvXProof

/-! # Conditional measurability survives bounded limits -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal
namespace InteractingSLE.Restart.FlowStopIdentCMI

/-- If the conditional expectations of a dominated sequence are measurable for
a smaller sigma algebra, the conditional expectation of its limit has the same
property. The ambient measure need not be complete. -/
theorem aestronglyMeasurable_condExp_of_dominated_limit
    {S : Type*} [mS : MeasurableSpace S] {P : Measure S} [IsProbabilityMeasure P]
    {m k : MeasurableSpace S} (hm : m ≤ mS) {f : ℕ → S → ℝ} {g : S → ℝ}
    (hf : ∀ n, AEStronglyMeasurable[mS] (f n) P) (b : S → ℝ) (hb : Integrable b P)
    (hbound : ∀ n, ∀ᵐ ω ∂P, ‖f n ω‖ ≤ b ω)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n => f n ω) atTop (𝓝 (g ω)))
    (hk : ∀ n, AEStronglyMeasurable[k] (P[f n | m]) P) :
    AEStronglyMeasurable[k] (P[g | m]) P := by
  have hL := tendsto_condExpL1_of_dominated_convergence hm b hf hb hbound hlim
  obtain ⟨ns, -, hns⟩ := (tendstoInMeasure_of_tendsto_Lp hL).exists_seq_tendsto_ae
  have hk' : ∀ n, AEStronglyMeasurable[k] (condExpL1 hm P (f n)) P := fun n =>
    (hk n).congr (condExp_ae_eq_condExpL1 hm (f n))
  let v : ℕ → S → ℝ := fun n => (hk' n).mk (condExpL1 hm P (f n))
  have hkg : AEStronglyMeasurable[k] (condExpL1 hm P g) P := by
    refine ⟨fun ω => limsup (fun n => v (ns n) ω) atTop,
      (Measurable.limsup fun n => (hk' (ns n)).measurable_mk).stronglyMeasurable, ?_⟩
    filter_upwards [hns, ae_all_iff.2 (fun n => (hk' n).ae_eq_mk)] with ω hω he
    exact ((hω.congr fun n => he (ns n)).limsup_eq).symm
  exact hkg.congr (condExp_ae_eq_condExpL1 hm g).symm

end InteractingSLE.Restart.FlowStopIdentCMI
