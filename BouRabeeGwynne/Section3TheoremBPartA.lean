import BouRabeeGwynne.Section3PlanarTarget
import BouRabeeGwynne.Section3CaseIITarget
import BouRabeeGwynne.Section3CaseIIITarget

/-! Theorem B(a) from the three actual geometric regularity cases. -/

namespace BouRabeeGwynne

/-- The approved Theorem B(a) statement, with actual tilings, continuum
harmonic functions and finite discrete Dirichlet solutions throughout. -/
theorem theoremB_part_a : TheoremBPartAStatement := by
  intro d G N U hC hd _hDomain hU hUD happrox hreg hh
  rcases hreg with hI | hII | hIII
  · have hd2 : d = 2 := hI
    subst d
    exact theoremB_part_a_planar G N U hC hU hUD happrox hh
  · exact theoremB_part_a_caseII hd G N U hC hU hUD happrox hII hh
  · exact theoremB_part_a_caseIII hd G N U hC hU hUD happrox hIII hh

end BouRabeeGwynne
