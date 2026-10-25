import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCEssentialLoop
import SupercriticalLQGUniqueness.B2.Strong.LoopSep

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Metric
namespace SupercriticalLQGUniqueness.B2.DG20Conc
open LQGMetric

 

theorem laneC_essential_loop_disconnects
    {τ : ℝ → ℂ} {c : ℂ} {r : ℝ}
    (hτann : ∀ u ∈ Icc (0 : ℝ) 1,
      r < dist (τ u) c ∧ dist (τ u) c < 2 * r)
    (hclosed : τ 0 = τ 1)
    {L : C(unitInterval, ℂ)} (hL : ∀ u, L u ≠ 0)
    (hLdef : ∀ u, L u = τ u - c)
    (hdeg : QuantumZipper.CA.Topo.loopDeg L hL ≠ 0) :
    LQGMetric.Disconnects (τ '' Icc (0 : ℝ) 1)
      (sphere c r) (sphere c (2 * r)) := by
  have hLc : L 0 = L 1 := by
    rw [hLdef, hLdef]
    exact congrArg (fun z : ℂ => z - c) hclosed
  intro x y γ hx hy
  let γc : Path (x - c) (y - c) :=
    γ.map (continuous_id.sub continuous_const)
  have hxnorm : ‖x - c‖ = r := by
    simpa only [mem_sphere, dist_eq_norm, norm_sub_rev] using hx
  have hynorm : ‖y - c‖ = 2 * r := by
    simpa only [mem_sphere, dist_eq_norm, norm_sub_rev] using hy
  have hinner : ∀ u, ‖x - c‖ < ‖L u‖ := by
    intro u
    rw [hLdef, hxnorm]
    simpa only [dist_eq_norm] using (hτann u u.2).1
  have houter : ∀ u, ‖L u‖ < ‖y - c‖ := by
    intro u
    rw [hLdef, hynorm]
    have h := (hτann u u.2).2
    simpa only [dist_eq_norm] using h
  obtain ⟨w, ⟨u, hu⟩, ⟨t, ht⟩⟩ :=
    SupercriticalLQGUniqueness.B2.Strong.loop_meets_path
      L hLc hL hdeg hinner houter γc
  refine ⟨γ u, ⟨u, rfl⟩, ?_⟩
  refine ⟨t, t.2, ?_⟩
  have hsub : γ u - c = τ t - c := by
    calc γ u - c = w := hu
      _ = L t := ht.symm
      _ = τ t - c := hLdef t
  have heq : γ u = τ t := by
    calc γ u = (γ u - c) + c := by simp
      _ = (τ t - c) + c := congrArg (· + c) hsub
      _ = τ t := by simp
  exact heq.symm

end SupercriticalLQGUniqueness.B2.DG20Conc
