import SupercriticalLQGUniqueness.B2.Polylog.P6CompareSubset
import SupercriticalLQGUniqueness.B2.Polylog.P11Assembly

 










set_option autoImplicit false

namespace SupercriticalLQGUniqueness.B2.Polylog

 

theorem plCompareSubset_of_dg20 (hPerc : Iface.DG20PercEstimate')
    (hExp : Iface.DG20ExponentRelation) (hPos : Iface.DG20ExponentPositive) :
    PLCompareSubset :=
  plCompareSubset_of_inputs hPerc (DG20Pt.dg20Section4_of_inputs hPerc hExp hPos)

 

theorem iface_plThm19Limit_of_dg20 (hPerc : Iface.DG20PercEstimate')
    (hExp : Iface.DG20ExponentRelation) (hPos : Iface.DG20ExponentPositive) :
    Iface.PLThm19Limit :=
  iface_plThm19Limit_of_inputs hPerc hExp hPos (plCompareSubset_of_dg20 hPerc hExp hPos)

 

theorem iface_plThm19_of_dg20 (hPerc : Iface.DG20PercEstimate')
    (hExp : Iface.DG20ExponentRelation) (hPos : Iface.DG20ExponentPositive)
    (hNorm : LFPPNormalizerExists) : Iface.PLThm19 :=
  iface_plThm19_of_inputs hPerc hExp hPos (plCompareSubset_of_dg20 hPerc hExp hPos) hNorm

end SupercriticalLQGUniqueness.B2.Polylog
