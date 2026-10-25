import SupercriticalLQGUniqueness.Uniqueness.Measurability.FiniteFieldEvents.ExcursionScaleBridge




 
set_option autoImplicit false
noncomputable section
open Set
namespace SupercriticalLQGUniqueness.Uniqueness.Measurability.FiniteFieldEvents

theorem excursion_total_time_pos (P : ℝ → ℂ) (T : ℝ)
    (O : Set ℂ) (hO : IsOpen O) (V : TopologicalSpace.Opens ℂ)
    (hVO : closure (V : Set ℂ) ⊆ O) (a b c d : ℝ)
    (hex : EndSaving.Interfaces.Excursion P T O V a b c d) : 0 < T := by
  rcases hex with ⟨h0, hab, hbc, hcd, hdT, hf, _, _, hV, _, _, _⟩
  have hT : 0 ≤ T := h0.trans (hab.trans (hbc.trans (hcd.trans hdT)))
  by_contra hn
  have hzero : T = 0 := le_antisymm (le_of_not_gt hn) hT
  have ha : a = 0 := le_antisymm (hab.trans (hbc.trans (hcd.trans (hdT.trans_eq hzero)))) h0
  have hb : b = 0 := le_antisymm (hbc.trans (hcd.trans (hdT.trans_eq hzero))) (h0.trans hab)
  have hsame : P a = P b := by rw [ha, hb]
  have hdisj : Disjoint (frontier O) O := (disjoint_frontier_iff_isOpen).2 hO
  exact (Set.disjoint_left.mp hdisj) hf (hsame ▸ hVO hV)

end SupercriticalLQGUniqueness.Uniqueness.Measurability.FiniteFieldEvents
