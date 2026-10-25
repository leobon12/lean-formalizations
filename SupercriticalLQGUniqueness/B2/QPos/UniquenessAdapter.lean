import SupercriticalLQGUniqueness.B2.Iface.Statements
import SupercriticalLQGUniqueness.Exponent.Uniqueness

 


set_option autoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.QPos

theorem positive_of_unique_witness (ξ : Set.Ioi (0 : ℝ))
    (Q₀ Q : ℝ) (h₀ : IsLFPPExponent ξ Q₀) (hQ : IsLFPPExponent ξ Q)
    (hpos : 0 < Q₀) : 0 < Q := by
  have heq := Exponent.isLFPPExponent_unique ξ Q₀ Q h₀ hQ
  exact heq ▸ hpos

 


theorem dg20ExponentPositive_of_witnesses
    (h : ∀ ξ : Set.Ioi (0 : ℝ), ∃ Q : ℝ,
      IsLFPPExponent ξ Q ∧ 0 < Q) :
    Iface.DG20ExponentPositive := by
  intro ξ Q hQ
  obtain ⟨Q₀, h₀, hp⟩ := h ξ
  exact positive_of_unique_witness ξ Q₀ Q h₀ hQ hp

end SupercriticalLQGUniqueness.B2.QPos
