import QuantumZipper.Proofs.LQG.CoordChangeAreaPull
import QuantumZipper.Proofs.Section5.Prop16MarkovMask2Final

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Coordinate change of the quantum area measure for fields of GFF type (COORD-CHANGE, D98)

Duplantier–Sheffield, *Liouville quantum gravity and KPZ*, Invent. Math. 185 (2011),
Proposition 2.1 (arXiv:0808.1560, p. 12), for fields known only through a local coupling with
the free field:

* `CoordChangeArea.ae_map_qAreaMeasureOn_coordChange_of_coupling` (**general form**): let `X` be
  a random field on any probability space whose circle averages inside an open `W ⊆ ℍ` have the
  same joint law as those of a field `Y` which, on a standard Borel space, is coupled with a free
  boundary GFF `X_f` so that a.s. `Y = X_f + φ` on the dyadic circles in `W` (`φ` continuous on
  `W`). Then for every deterministic conformal map `ψ : ℍ → ℍ`, every continuous `h₀` on `W`,
  and open `U ⊆ ℍ`, `V ⊆ W` with `ψ(U) ⊆ V`, almost surely
    `ψ_* μ^U_{(h₀ + X) ∘ ψ + Q log|ψ'|} = μ^V_{h₀ + X} |_{ψ(U)}`.
  (The log singularity `-α log|· − x|` at a boundary point `x ∉ W` is such an `h₀`.)
* `CoordChangeArea.ae_map_qAreaMeasureOn_coordChange_mixed`: the mixed GFF of Proposition 1.6
  (zero boundary values on `∂D`, free on the arc `[c,d]`), through the local coupling
  `Prop16Asm.prop16MixedFreeLocCoupling_mm` (`W = D`).

The law transfer is the one of `Prop16Asm.prop16LocGoodStmt_of_coupling` (Prop16LocGood.lean),
`Prop16Asm.locGood_ae_exists_of_map_eq`: a.e. sample of `X` has the circle averages of a good
coupled sample. Own bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Function Metric
open scoped Topology ENNReal

namespace QuantumZipper
namespace CoordChangeArea

open SWCore GoodSample G1Side

/-- Adding a function continuous on `W` to both sides of a local agreement. -/
theorem circAgree_ofFun_add_open {W : Set ℂ} {x y : FieldSample} {φ h0 : ℂ → ℝ}
    (hφ : ContinuousOn φ W) (hh0 : ContinuousOn h0 W)
    (h : Prop16Area.G.CircAgree W x (y + ofFun φ)) :
    Prop16Area.G.CircAgree W (ofFun h0 + x) (y + ofFun (fun z => φ z + h0 z)) := by
  intro n k z hz hW
  have hc := CircleCont.dyadicRoundC_mem_Hbar hz n
  rw [Pi.add_apply, h n k z hz hW, Pi.add_apply, Pi.add_apply]
  simp only [ofFun]
  rw [integral_add (Prop16Area.G.integrable_fc_of_continuousOn hc (radius_pos k) (hφ.mono hW))
    (Prop16Area.G.integrable_fc_of_continuousOn hc (radius_pos k) (hh0.mono hW))]
  ring

end CoordChangeArea
end QuantumZipper
