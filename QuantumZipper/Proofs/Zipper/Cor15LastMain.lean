import QuantumZipper.Proofs.Zipper.Cor15LastRaw
import QuantumZipper.Proofs.Zipper.Cor15RegZy
import QuantumZipper.Proofs.RS.RohdeSchrammSimple

/-!
# COR15-LAST: Corollary 1.5(a) for `t > 0`, assembled

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Corollary 1.5(a)
(pp. 17–18; no proof in the paper). Own assembly of `theorem1_5a_pos_of_coords` with
* `hZc` = `aemeasurable_mod0Data_zipCapUp_c` (`Cor15LastZc`, proved),
* `hZy` = `aemeasurable_mod0Data_zipCapUp_y` (`Cor15RegZy`, proved),
* `hF` = `cor15WeldRead` (`Cor15RegWire`, proved),
* `hpair` = `cor15PairRead_of_reg` (`Cor15LastPair`, from `Cor15PairRegStmt`),
* `hraw` = `hraw_of_reg` (`Cor15LastRaw`, from `Cor15RawRegStmt`),
* Rohde–Schramm = `RS.rohdeSchrammSimple` (proved).

The one remaining input, `Cor15TdensRegStmt`, is regularity of the unzipped field at the
pushforwards `(tdens (±ρ)).map (revMapInv (vrev (√κ B) t) t)` of the signed parts of each test
function: `RegShift` (convergence form) and `evalReg` = raw value. It is the analogue, for the
measures `tdens (±ρ)`, of `Cor15RezipRegStmt` (proved for folded circles in `Cor15RezipFin2`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory

namespace QuantumZipper
namespace Cor15Group

/-- **Remaining input** (not proved): the regularity of the unzipped field at the pushed signed
parts of every test function, for every admissible setup. -/
def Cor15TdensRegStmt : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ t : ℝ, 0 < t →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : NNReal → Ω → ℝ) (X : Ω → FieldSample),
    IsBrownianReal B P → IsFreeGFFModConstH X P → IndepFun (pathOf B) X P →
    Cor15PairRegStmt κ t P B X ∧ Cor15RawRegStmt κ t P B X

/-- **Corollary 1.5(a) for `t > 0`**, from Theorem 1.3 and `Cor15TdensRegStmt`. -/
theorem theorem1_5a_pos_of_theorem1_3_of_tdensReg (h13 : theorem1_3)
    (hT : Cor15TdensRegStmt) :
    ∀ κ : ℝ, 0 < κ → κ < 4 →
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (B : NNReal → Ω → ℝ) (X : Ω → FieldSample),
      IsBrownianReal B P → IsFreeGFFModConstH X P → IndepFun (pathOf B) X P →
      ∀ t : ℝ, 0 < t →
      configLawMod0 (fun ω => zipCap (Real.sqrt κ) t (ofFun (h0rev κ) + X ω, drive κ B ω)) P =
        configLawMod0 (fun ω => (ofFun (h0rev κ) + X ω, drive κ B ω)) P := by
  intro κ hκ hκ4 Ω _ P _ B X hB hX hind t ht
  have hRSS := RS.rohdeSchrammSimple
  obtain ⟨hPR, hRR⟩ := hT κ hκ hκ4 t ht P B X hB hX hind
  exact theorem1_5a_pos_of_coords h13 hRSS hκ hκ4 hB hX hind ht
    (aemeasurable_mod0Data_zipCapUp_c h13 hRSS hκ hκ4 hB hX hind ht)
    (aemeasurable_mod0Data_zipCapUp_y h13 hRSS hκ hκ4 hB hX hind ht)
    (hraw_of_reg h13 hRSS hκ hκ4 hB hX hind ht hRR)
    (cor15WeldRead h13 hRSS hκ hκ4 hB hX hind ht)
    (cor15PairRead_of_reg h13 hRSS hκ hκ4 hB hX hind ht hPR)

end Cor15Group
end QuantumZipper
