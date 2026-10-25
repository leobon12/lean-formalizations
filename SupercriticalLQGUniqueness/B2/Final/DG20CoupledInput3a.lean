import SupercriticalLQGUniqueness.B2.Final.DG20CoupledSmallAnnuliR32
import SupercriticalLQGUniqueness.B2.Final.OpenInputs4

 







set_option autoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.Final

 
theorem dg20CouplingSmallAnnuliCoords_proved : DG20CouplingSmallAnnuliCoords :=
  fun hI ξ Q hQ m hm ε hε => exists_dg20CouplingData_coords_smallAnnuli hI ξ Q hQ m hm ε hε

 
theorem dg20CouplingSmallAnnuli_proved : DG20CouplingSmallAnnuli := by
  intro hI ξ Q hQ m hm ε hε
  obtain ⟨φ₁, hφ₁, c, V, Ω', M', SB', P', hP', h', hN, L, hB, hS, -⟩ :=
    exists_dg20CouplingData_coords_smallAnnuli hI ξ Q hQ m hm ε hε
  exact ⟨φ₁, hφ₁, c, V, Ω', M', SB', P', hP', h', hN, L, hB, hS⟩

end SupercriticalLQGUniqueness.B2.Final
