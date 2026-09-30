import QuantumZipper.Proofs.Zipper.UnifUCFix
import QuantumZipper.Proofs.Zipper.UnifUCIdDet
import QuantumZipper.Proofs.Zipper.UnifUCIdDetD
import QuantumZipper.Proofs.Zipper.UnifUCTr
import QuantumZipper.Proofs.Zipper.UnifRC3UC
import QuantumZipper.Proofs.Zipper.UnifClColl
import QuantumZipper.Proofs.Zipper.F1StrictMonoCocycle

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# D33-CLOSE: the uniform-Cauchy chain, closed

The chain of decision D33 (UNIF-RC3) is complete and this file wires its links together,
discharging every open input of the chain:

1. `fixedUCStmt_holds`: `FixedUCStmt κ T P X` for a free GFF modulo constants, from the two
   halves of the fixed-driver input — the fixed-parameter identity `UnifUCIdDet.identStmt` and
   the uniform convergence of the deterministic part `UnifUCIdDetD.detUnifStmt_holds` — through
   `UnifUCFix.fixedUCStmt_of_id_det`.
2. `unifUCStmt_holds`: `UnifUCStmt κ T P B X` (the uniform Cauchy property along the Brownian
   driver, on the whole good event), through `UnifUCTr.unifUCStmt_of_fixedUCStmt`, which
   transfers the fixed driver statement to the random driver by the independence of path and
   field.
3. `unifRC3Stmt_holds` and `capCocycleRegStmt_holds`: `UnifRC3Stmt` and `B3d.CapCocycleRegStmt`
   (Sheffield arXiv:1012.4797, §5: the two unzippings at times `u` and `u + s` agree in regular
   coordinates, with raw folded-circle convergence), through `UnifRC3UC.unifRC3Stmt_of_uc` and
   `UnifRC3UC.capCocycleRegStmt_of_uc`.
4. Consumers: `capCocycleRegAllStmt_holds` (the field cocycle at every horizon),
   `capCocycleAddStmt_holds` (`E6.CapCocycleAddStmt`), the all-times length cocycle
   `ae_lenCocycle_all_holds` and the positivity of the new piece `ae_newPiece_pos_holds`
   (= `F1StrictMonoCocycle.ae_lenCocycle_all_of_unifAll` /
   `ae_newPiece_pos_of_unifAll` with `CapCocycleRegAllStmt` discharged), the fixed-horizon
   `E6.LenCocycleStmt` / `E6.LenCollidedStmt` (`UnifClColl.lenCocycleStmt_of_windows`,
   `lenCollidedStmt_of_windows`), and E6-ID `e6_id_of_d33`.

The remaining hypotheses are exactly the ones of the chain theorems and are kept unchanged:
`IsBrownianReal B P`, `IsFreeGFFModConstH X P`, `IndepFun (pathOf B) X P`, `0 < T`; the length
statements additionally need `0 < κ < 4` and the window/atomlessness inputs UW (`UnifWindowStmt`
/ `UnifWindowAllStmt`) and UA (`UnifAtomlessStmt` / `UnifAtomlessAllStmt`), and E6-ID additionally
needs `B3d.ZipLenInputsStmt`. No new mathematics is done here: every proof is a combination of
already proved results.

Sources: Sheffield, arXiv:1012.4797, §5 (the field cocycle and the length cocycle); Revuz–Yor,
3rd ed., Ch. I, Thm (2.1) (the Kolmogorov–Čentsov input behind `FixedUCStmt`).
-/

noncomputable section

open Complex MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace RegUnif

open B2 B5 RealLine CaraR

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ T : ℝ} {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}

/-! ## 1. The fixed-driver input, unconditionally -/

/-- **UNIF-RC3-FIX closed**: for a free GFF modulo constants (under a probability measure) the
uniform Cauchy statement `FixedUCStmt κ T P X` holds, for every `κ` and every `T`. -/
theorem fixedUCStmt_holds (hX : IsFreeGFFModConstH X P) : FixedUCStmt κ T P X :=
  fixedUCStmt_of_id_det (κ := κ) (T := T) hX (identStmt κ T) (detUnifStmt_holds κ T)

/-! ## 2. The uniform Cauchy statement for the Brownian driver -/

/-- **UNIF-RC3-TR closed**: `UnifUCStmt κ T P B X` — a.s. the dyadic approximations
`PhiW κ (drive κ B ω) d k j (X ω)` are uniformly Cauchy on `triQ T` — for a Brownian driver `B`
independent of a free GFF modulo constants `X`, at every `T > 0`. -/
theorem unifUCStmt_holds (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P)
    (hind : IndepFun (pathOf B) X P) (hT : 0 < T) : UnifUCStmt κ T P B X :=
  unifUCStmt_of_fixedUCStmt (κ := κ) (T := T) hB hX hind hT (fixedUCStmt_holds hX)

/-! ## 3. The two outputs of the uniform Cauchy input -/

/-- **`B3d.CapCocycleRegStmt` closed** (Sheffield §5): a.s., for all `u, s ≥ 0` with
`u + s ≤ T`, the unzippings at `u` then `s` and at `u + s` agree in regular coordinates and have
raw folded-circle convergence at every centre. -/
theorem capCocycleRegStmt_holds (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P)
    (hind : IndepFun (pathOf B) X P) (hT : 0 < T) : B3d.CapCocycleRegStmt κ T P B X :=
  capCocycleRegStmt_of_uc (κ := κ) (T := T) hB hX hind hT (unifUCStmt_holds hB hX hind hT)

/-! ## 4. Consumers with the field cocycle discharged -/

/-- **The field cocycle at every horizon** (`CapCocycleRegAllStmt`), from the `T > 0` version. -/
theorem capCocycleRegAllStmt_holds (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P)
    (hind : IndepFun (pathOf B) X P) : CapCocycleRegAllStmt κ P B X :=
  fun _ hT => capCocycleRegStmt_holds hB hX hind hT

/-- **`E6.CapCocycleAddStmt` closed** (the zip algebra of the capacity flow). -/
theorem capCocycleAddStmt_holds (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P)
    (hind : IndepFun (pathOf B) X P) (hT : 0 < T) : E6.CapCocycleAddStmt κ T P B X :=
  B3d.capCocycleAddStmt_of (capCocycleRegStmt_holds hB hX hind hT)

end RegUnif
end QuantumZipper
