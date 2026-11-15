/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4SafeRConnMean
import InteractingSLE.Spec.Sec7.Aux29CorSide
import InteractingSLE.Spec.Sec7.Aux29CorChart

/-!
# GW4: full-fiber uniqueness in the relative Loewner chart

Apply the landed physical-exception form of Aux. 29. A finite physical
exception set excludes all incident fibers, with no finiteness assumption on
the set of prime ends. The Loewner inverse's limit at infinity is automatic.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped NNReal ENNReal
open QuantumZipper (H Hbar chiC fwdMap fwdMapInv fwdHull logDerivFwd)

namespace InteractingSLE.Theorem14.GW4Fix

open Sec7.PhaseSel Sec7.PocketStopSide Sec7.Aux29Cor

/-- The phase-word Poisson mean follows from incident boundary germs off a
finite physical set. No set of exceptional prime ends is assumed finite. -/
theorem eqOn_couplingMean_of_incident_germs {k : ℝ} (hk : 0 < k) {nL nR : ℕ}
    (ρL : Fin (nL + 1) → ℝ) (ρR : Fin (nR + 1) → ℝ)
    {vL : Fin (nL + 1) → ℝ} {vR : Fin (nR + 1) → ℝ}
    (hL : vL 0 ≤ 0) (hR : 0 ≤ vR 0) (d : ℝ)
    {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) (q : ℝ≥0)
    {F : ℂ → ℂ} (hF : EqOn F (fwdMapInv W q) H) (hFc : ContinuousOn F Hbar)
    {v : ℂ → ℝ} (hv : InnerProductSpace.HarmonicOnNhd v (H \ fwdHull W q))
    {K : ℝ} (hlog : ∀ z ∈ H \ fwdHull W q,
      |v z| ≤ K * (1 + Real.log (1 + ‖z‖) +
        Real.log (1 + 1 / infDist z (H \ fwdHull W q)ᶜ)))
    {E : Set ℂ} (hE : E.Finite)
    (hside : ∀ x : ℝ, x ∉ forceJumpSet vL vR → F x ∉ E →
      Tendsto (fun y => v (fwdMapInv W q y) +
          chiC k * (logDerivFwd W q (fwdMapInv W q y)).im)
        (𝓝[H] (x : ℂ)) (𝓝 (phaseData k ρL ρR vL vR d x))) :
    EqOn v (couplingMean k W q (phaseWordExt k ρL ρR vL vR d)) (H \ fwdHull W q) := by
  let c := Chart.id.loewner W q
  have hc : c.IsConformal := Chart.isConformal_id.loewner hW hW0 q.coe_nonneg
  have hdom : (c.dom : Set ℂ) = H \ fwdHull W q := by
    rw [hc.coe_dom]
    exact QuantumZipper.RS.image_fwdMapInv_H hW hW0 q.coe_nonneg
  have hℓ : IsDerivLog c.1 (logDerivFwd W q) c.dom := by
    rw [hdom]
    exact isDerivLog_fwdMap hW q.coe_nonneg
  have hlift : ∀ z ∈ c.dom, c.2.2 z = (logDerivFwd W q z).im := by
    intro z _
    change (logDerivFwd W q z).im + 0 = _
    exact add_zero _
  have hder := Sec7.Aux2728Pocket.deriv_fwd_eq hℓ hlift 0
  simp only [Int.cast_zero, mul_zero, add_zero] at hder
  have hinf : Tendsto (fun w => mob (c.2.1 w))
      (Bornology.cobounded ℂ ⊓ 𝓟 H) (𝓝 0) :=
    tendsto_mob_cobounded.comp
      ((Sec7.Aux29Cor.tendsto_fwdMapInv_cobounded hW hW0 q).mono_right inf_le_left)
  have heq := eqOn_phaseWordExt_of_landing_germs hk ρL ρR hL hR d hc hF hFc hinf
    (hdom ▸ hv) (hdom ▸ hlog) (Chart.continuousOn_lift_loewner hW hW0 q.coe_nonneg)
    hder hE (fun x hx hxE _ _ => by
      simpa only [c, Chart.id, Chart.loewner, add_zero] using hside x hx hxE)
  intro z hz
  have he := heq z (hdom.symm ▸ hz)
  simpa only [c, Chart.id, Chart.loewner, couplingMean, add_zero] using he

end InteractingSLE.Theorem14.GW4Fix
