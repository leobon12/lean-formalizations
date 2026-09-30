import QuantumZipper.Proofs.Zipper.Cor15BCases
import QuantumZipper.Proofs.Zipper.Cor15TdensMain
import QuantumZipper.Proofs.Zipper.Cor15Partial
import QuantumZipper.Proofs.Zipper.Cor15GroupZero
import QuantumZipper.Statements.Thm15

/-!
# COR15-B: final assembly of Corollary 1.5

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Corollary 1.5
(pp. 17–18; no proof in the paper). Own assembly:

* (a), `t ≤ 0`: `theorem1_5a_nonpos` (unconditional);
* (a), `t > 0`: `theorem1_5a_pos_of_theorem1_3_of_tdensReg h13 cor15TdensRegStmt` (Theorem 1.3);
* (b), `s, t ≤ 0`: `theorem1_5b_nonpos` (unconditional);
* (b), `s ≥ 0, t = 0`: `theorem1_5b_nonneg_zero` (unconditional);
* (b), `s > 0, s + t = 0`: `theorem1_5b_pos_cancel` (Theorem 1.3);
* (b), the other cases with a positive time: the three named inputs of `Cor15BCases`.

So Corollary 1.5(a) is proved from Theorem 1.3 alone (`theorem1_5a_of_theorem1_3`), and the
full corollary from Theorem 1.3 and `Cor15ZipUnzipMixStmt`, `Cor15UnzipZipStmt`,
`Cor15ZipZipStmt` (`theorem1_5_of_theorem1_3_of_posGroup`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory

namespace QuantumZipper
namespace Cor15Group

/-- **Corollary 1.5(a) for every `t ∈ ℝ`**, from Theorem 1.3. -/
theorem theorem1_5a_of_theorem1_3 (h13 : theorem1_3) :
    ∀ κ : ℝ, 0 < κ → κ < 4 →
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (B : NNReal → Ω → ℝ) (X : Ω → FieldSample),
      IsBrownianReal B P → IsFreeGFFModConstH X P → IndepFun (pathOf B) X P →
      ∀ t : ℝ,
      configLawMod0 (fun ω => zipCap (Real.sqrt κ) t (ofFun (h0rev κ) + X ω, drive κ B ω)) P =
        configLawMod0 (fun ω => (ofFun (h0rev κ) + X ω, drive κ B ω)) P := by
  intro κ hκ hκ4 Ω _ P _ B X hB hX hind t
  rcases le_or_gt t 0 with ht | ht
  · exact Cor15Partial.theorem1_5a_nonpos κ hκ hκ4 P B X hB hX hind t ht
  · exact theorem1_5a_pos_of_theorem1_3_of_tdensReg h13 cor15TdensRegStmt κ hκ hκ4 P B X
      hB hX hind t ht

/-- **Corollary 1.5**, from Theorem 1.3 and the three remaining positive-time group
identities of `Cor15BCases`. -/
theorem theorem1_5_of_theorem1_3_of_posGroup (h13 : theorem1_3)
    (hM : Cor15ZipUnzipMixStmt) (hU : Cor15UnzipZipStmt) (hZ : Cor15ZipZipStmt) :
    theorem1_5 := by
  intro κ hκ hκ4 Ω _ P _ B X hB hX hind
  refine ⟨theorem1_5a_of_theorem1_3 h13 κ hκ hκ4 P B X hB hX hind, fun s t => ?_⟩
  rcases le_or_gt s 0 with hs | hs
  · rcases le_or_gt t 0 with ht | ht
    · exact theorem1_5b_nonpos κ P B X hB hX hind hs ht
    · rcases hs.lt_or_eq with hs | rfl
      · exact theorem1_5b_neg_pos hU hκ hκ4 hB hX hind hs ht
      · exact theorem1_5b_nonneg_pos hZ hκ hκ4 hB hX hind le_rfl ht
  · rcases lt_trichotomy t 0 with ht | rfl | ht
    · exact theorem1_5b_pos_neg h13 hM hκ hκ4 hB hX hind hs ht
    · exact theorem1_5b_nonneg_zero hB hX hs.le
    · exact theorem1_5b_nonneg_pos hZ hκ hκ4 hB hX hind hs.le ht

end Cor15Group
end QuantumZipper
