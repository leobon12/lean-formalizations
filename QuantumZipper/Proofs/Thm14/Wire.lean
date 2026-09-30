import QuantumZipper.Proofs.Thm14.OptB
import QuantumZipper.Proofs.Loewner.CaraR8
import QuantumZipper.Proofs.LQG.RevCouplingReg

/-!
# THM14-WIRE: Theorem 1.4(a) with the proved literature facts plugged in

Sheffield, *Conformal weldings of random surfaces* (arXiv:1012.4797), Theorem 1.4 and its proof
(§1.4, pp. 16–17). `Thm14OptB.theorem1_4a_of_theorem1_3'` derives Theorem 1.4(a) from
Theorem 1.3 and the blueprint facts `RevMapCaratheodory`, `RohdeSchrammSimple`,
`RevCouplingBoundaryMeasureRegular`. Two of these are now proved:

* `CaraR.revMapCaratheodory` (Carathéodory boundary extension of the reverse Loewner map of a
  simple curve hull);
* `RevCouplingReg.revCouplingBoundaryMeasureRegular` (the boundary measure of the reverse
  coupling field is a.s. atom free, positive on intervals and locally finite).

Removability of the doubled hull enters through Option B (Jones–Smirnov, Ark. Mat. 38 (2000),
Cor. 2, through its proof; Rohde–Schramm, Ann. of Math. 161 (2005), Thm 5.2), already inside
`theorem1_4a_of_theorem1_3'`. The only remaining hypotheses are Theorem 1.3 and
`Blueprint.RohdeSchrammSimple` (Rohde–Schramm, Thm 6.1: SLE_κ is a simple curve for `κ ≤ 4`).
-/

namespace QuantumZipper

namespace Thm14Wire

/-- **Theorem 1.4(a)** from Theorem 1.3 and Rohde–Schramm simplicity. -/
theorem theorem1_4a_of_theorem1_3_rss (h13 : theorem1_3)
    (hRSS : Blueprint.RohdeSchrammSimple) : theorem1_4a :=
  Thm14OptB.theorem1_4a_of_theorem1_3' h13 CaraR.revMapCaratheodory hRSS
    RevCouplingReg.revCouplingBoundaryMeasureRegular

end Thm14Wire

end QuantumZipper
