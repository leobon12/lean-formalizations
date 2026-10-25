import SupercriticalLQGUniqueness.B2.DG20Lim.InterfaceC
import SupercriticalLQGUniqueness.B2.PfeAxioms.InputsDG20SkSB
import SupercriticalLQGUniqueness.B2.PfeAxioms.VaryingJointCoordLaw

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology LQGMetric

namespace SupercriticalLQGUniqueness.B2.DG20Lim

 

theorem dg20LimitSkC_of_standardBorel_topological
    (hSB : B2.PfeAxioms.Inputs.DG20LimitSkSB) : DG20LimitSkC := by
  intro ξ Q hQ m hm ε hε
  obtain ⟨φ, hφ, c, hc, hCouple⟩ := hSB ξ Q hQ m hm ε hε
  refine ⟨φ, hφ, c, hc, ?_⟩
  intro Ω _ P _ h hh X hX
  obtain ⟨Ω', M', SB', P', hP', h', hN, F, L,
    hLm, hh', hLaw, hField, hFc, hLsc, hRat, hGeom⟩ :=
    hCouple P h hh X hX
  refine ⟨Ω', M', SB', P', hP', h', hN, F, L,
    hLm, hh', hLaw, ?_, hFc, hLsc, hRat, hGeom⟩
  filter_upwards [hField] with ω hω
  exact ((B2.PfeAxioms.continuous_pairJ_top.tendsto _).comp hω)

end SupercriticalLQGUniqueness.B2.DG20Lim
