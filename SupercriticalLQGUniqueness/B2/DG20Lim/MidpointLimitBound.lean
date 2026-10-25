import SupercriticalLQGUniqueness.B2.DG20Lim.MidpointTrapped

 


set_option autoImplicit false
noncomputable section

open Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem liminf_approx_midpoint_le_half
    (a b δ : ℕ → ℝ) (hb : ∀ n, 0 ≤ b n)
    (d : ℝ≥0∞) (hd : d ≠ ∞)
    (hconv : Tendsto (fun n => ENNReal.ofReal (b n)) atTop (𝓝 d))
    (hδ : Tendsto δ atTop (𝓝 0))
    (hmid : ∀ n, a n ≤ b n / 2 + δ n) :
    liminf (fun n => ENNReal.ofReal (a n)) atTop ≤
      ENNReal.ofReal (d.toReal / 2) := by
  have hbconv : Tendsto b atTop (𝓝 d.toReal) := by
    have hh := (ENNReal.tendsto_toReal hd).comp hconv
    have heq : (ENNReal.toReal ∘ fun n => ENNReal.ofReal (b n)) = b := by
      funext n
      exact ENNReal.toReal_ofReal (hb n)
    rwa [heq] at hh
  have hboundReal : Tendsto (fun n => b n / 2 + δ n)
      atTop (𝓝 (d.toReal / 2)) := by
    convert (hbconv.div_const 2).add hδ using 1 <;> simp
  have hbound : Tendsto (fun n => ENNReal.ofReal (b n / 2 + δ n))
      atTop (𝓝 (ENNReal.ofReal (d.toReal / 2))) :=
    (ENNReal.continuous_ofReal.tendsto _).comp hboundReal
  have hle : ∀ᶠ n in atTop,
      ENNReal.ofReal (a n) ≤ ENNReal.ofReal (b n / 2 + δ n) :=
    Eventually.of_forall (fun n => ENNReal.ofReal_le_ofReal (hmid n))
  exact (liminf_le_liminf hle).trans_eq hbound.liminf_eq

end SupercriticalLQGUniqueness.B2.DG20Lim
