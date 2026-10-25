import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCEssentialLoopDisconnect

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Metric
namespace SupercriticalLQGUniqueness.B2.DG20Conc
open LQGMetric

 


theorem laneC_exists_paid_separating_loop
    (D : ContMetric)
    {ρ : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hρ : ContinuousOn ρ (Icc a b))
    {c v : ℂ} {r : ℝ} (hr : 0 < r)
    (hρann : ∀ t ∈ Icc a b,
      r < dist (ρ t) c ∧ dist (ρ t) c < 2 * r)
    (hv : 2 * r ≤ dist v c)
    (hsep : LQGMetric.Disconnects (ρ '' Icc a b)
      (sphere c r) (sphere c (2 * r))) :
    ∃ τ : ℝ → ℂ, ContinuousOn τ (Icc (0 : ℝ) 1) ∧
      (∀ u ∈ Icc (0 : ℝ) 1,
        r < dist (τ u) c ∧ dist (τ u) c < 2 * r) ∧
      τ 0 = τ 1 ∧
      LQGMetric.Disconnects (τ '' Icc (0 : ℝ) 1)
        (sphere c r) (sphere c (2 * r)) ∧
      D.len τ 0 1 ≤ D.len ρ a b := by
  obtain ⟨τ, hτ, hτann, hclosed, hlen, L, hL, hLdef, hdeg⟩ :=
    laneC_exists_paid_essential_loop D hab hρ hr hρann hv hsep
  exact ⟨τ, hτ, hτann, hclosed,
    laneC_essential_loop_disconnects hτann hclosed hL hLdef hdeg,
    hlen⟩

end SupercriticalLQGUniqueness.B2.DG20Conc
