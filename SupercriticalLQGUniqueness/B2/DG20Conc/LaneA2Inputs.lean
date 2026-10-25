import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCRepairedInputs

 





set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SupercriticalLQGUniqueness.B2.DG20Conc.LaneBInputs

 


def C1UnitBlockGeometry : Prop :=
  LaneCRepairedInputs.UnitBlockGeometry
    laneCUnitUcross laneCUnitUaround laneCUnitInner laneCUnitOuter

end SupercriticalLQGUniqueness.B2.DG20Conc.LaneBInputs
