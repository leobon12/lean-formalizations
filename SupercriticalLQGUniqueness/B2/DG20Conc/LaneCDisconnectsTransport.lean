import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCAffineMetricLength
import LQGMetric.Topo.Disconnect

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set
namespace SupercriticalLQGUniqueness.B2.DG20Conc
open LQGMetric

theorem laneC_disconnects_image_of_involution
    {f : ℂ → ℂ} (hf : Continuous f) (hff : ∀ z, f (f z) = z)
    {X E F : Set ℂ} (h : LQGMetric.Disconnects X E F) :
    LQGMetric.Disconnects (f '' X) (f '' E) (f '' F) := by
  intro x y γ hx hy
  obtain ⟨x₀, hx₀, rfl⟩ := hx
  obtain ⟨y₀, hy₀, rfl⟩ := hy
  have hx' : f (f x₀) ∈ E := by simpa only [hff] using hx₀
  have hy' : f (f y₀) ∈ F := by simpa only [hff] using hy₀
  obtain ⟨w, hw, hwX⟩ := h (f (f x₀)) (f (f y₀))
    (γ.map hf) hx' hy'
  obtain ⟨t, rfl⟩ := hw
  refine ⟨γ t, mem_range_self t, ?_⟩
  exact ⟨f (γ t), hwX, hff (γ t)⟩

end SupercriticalLQGUniqueness.B2.DG20Conc
