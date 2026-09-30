import QuantumZipper.Proofs.Thm18.R18G4Nodes
import QuantumZipper.Proofs.Thm18.G4
import QuantumZipper.Proofs.Zipper.LocRichBasic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R18 T9 (transfer part): clause (3) for `t > 0` from E6, the round trip and a reading node

Sheffield, arXiv:1012.4797, Theorem 1.8 (p. 26), (1) and (3): `Z^LEN_t`, `t > 0`, is the inverse
of `Z^LEN_{−t}`, whose law invariance is E6; hence `Z^LEN_t` preserves the law. The paper gives no
separate argument; this is the abstract law transfer of `G4FactorRead.lean`
(`Cor15Group.map_comp_eq_of_factor`, `E6.map_eq_of_coord_ae`) on the masked data of
`configLawOff` (D74), for area-carrying configurations (D76).

Because `zipLenA` reads the carried area, the reading node `G4ZipReadAStmt` asks the masked data of
`Z_t x` to be a measurable function `Φ` of the masked data of `x` **almost surely along the two
configurations used** (`c` and `Z_{−t} c`), not for every `x`: on those two, the carried area is
a.s. the area read off the masked field (zero area of the curve, T1; unzipping area rule, T3),
which is task T6. Own elementary argument (pushforward algebra).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace R18

open Thm18Asm

/-- The masked data of a configuration (`configLawOff c P = P.map (offData ∘ c)`). -/
def offData (x : FieldSample × (ℝ → ℝ)) : E6.FullData :=
  (lawDataOff x, fun t : ℝ≥0 => x.2 t)

theorem configLawOff_eq_map_offData {Ω : Type*} [MeasurableSpace Ω]
    (c : Ω → FieldSample × (ℝ → ℝ)) (P : Measure Ω) :
    configLawOff c P = P.map fun ω => offData (c ω) := rfl

/-- **Raw masked round trip, coordinate by coordinate** (`t > 0`): the masked circle coordinates,
and each masked test pairing separately, of `Z^LEN_t (Z^LEN_{−t} c)` agree a.s. with those of `c`. -/
def G4RoundRawAStmt : Prop :=
  ∀ (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample),
    Thm18Setting γ P B Y → Thm18Inputs γ P B Y → E6ALaw γ P B Y → LenEqArc γ P B Y →
    ∀ t : ℝ, 0 < t →
      (∀ᵐ ω ∂P, (offData (zipLenA γ t (zipLenDownA γ t (wedgeAConfig γ B Y ω))).toPair).1.1 =
        (offData (wedgeAConfig γ B Y ω).toPair).1.1) ∧
      ∀ ρ : TestFun H, ∀ᵐ ω ∂P,
        (offData (zipLenA γ t (zipLenDownA γ t (wedgeAConfig γ B Y ω))).toPair).1.2 ρ =
          (offData (wedgeAConfig γ B Y ω).toPair).1.2 ρ

end R18
end QuantumZipper
