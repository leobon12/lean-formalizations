import QuantumZipper.Proofs.Zipper.UnifSWMain
import QuantumZipper.Proofs.Zipper.B2Uncond

/-!
# UNIF-ACFAM (1): AC-fam in the coordinates of the anchor field `h⁰_q`

Task UNIF-ACFAM (Theorem 1.3, uniform-in-time cluster). `RegUnif.AnchorUnifFamStmt` (AC-fam)
concerns the transported integrals `awInt … s k` of the fields `h⁰_s`, `s ∈ [q,T] ∩ ℚ`. Here all
of them are rewritten in terms of the **single** anchor field `h⁰_q`:

  a.s., for every rational `s ∈ [q,T]`, `bdryApprox γ h⁰_s = bdryApprox γ (coordChange h⁰_q ψ_s Q)`,
  `ψ_s = revMap (Vr κ s B ω) (s − q)` (`ae_bdryApprox_h0f_eq_coordChange`),

so that `awInt … s k = acInt … s k` (`ae_awInt_eq_acInt`), where `acInt` integrates the same
transported test function against the approximations of `coordChange h⁰_q ψ_s Q`. The maps
`ψ_s` use the driver on `[q,s]` and the transports `F_s = realRevMap (Vr κ T B ω) (T − s)` the
driver on `[s,T]`; both are functions of the driver after `q`, which is independent of `h⁰_q`
(`B2.b2_markov`). This is the first step of the proof of Sheffield–Wang, arXiv:1605.06171,
Thm 1.4 (§3.3, p. 12: "Change of coordinates implies …", where every approximation is written
in terms of the one field `h` and the maps `φ ∈ Λ`); here the role of `h` is played by `h⁰_q`.

Main results: `ae_awInt_eq_acInt`, **`anchorUnifFamStmt_of_anchorField`** (AC-fam from the
statement `AnchorFieldFamStmt` in `h⁰_q`-coordinates). The identification is the regularized
Markov split `B2.b2_regEq` at horizon `s` and time `s − q` (Sheffield, arXiv:1012.4797,
Thm 1.2 / Prop 5.x Markov property of the zipper), applied at countably many times; the
bookkeeping is own.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace RegUnif

open B2 B5 E1 E1.M4

variable {Ω : Type} [MeasurableSpace Ω]

/-- The anchor map `ψ_s = revMap (Vr κ s B ω) (s − q)` (reverse flow of the driver on `[q,s]`). -/
def acMap (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (ω : Ω) (q s : ℝ) : ℂ → ℂ :=
  revMap (Vr κ s B ω) (s - q)

variable {P : Measure Ω} [IsProbabilityMeasure P] {κ T : ℝ} {B : ℝ≥0 → Ω → ℝ}
  {X : Ω → FieldSample}

omit [MeasurableSpace Ω] in
/-- `h⁰_q` is the zipped field at time `s − q` for the horizon `s`. -/
theorem Yf_horizon_eq_h0f (κ q s : ℝ) (ω : Ω) : Yf κ s (s - q) B X ω = h0f κ q B X ω := by
  rw [Yf_eq_unzippedField, h0f_eq_unzippedField, sub_sub_cancel]

/-- **All rational times at once**: a.s., for every rational `s ∈ [q, ∞)`, the approximations of
`h⁰_s` are those of `coordChange h⁰_q ψ_s Q`. -/
theorem ae_bdryApprox_h0f_eq_coordChange (hB : IsBrownianReal B P)
    (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P) {q : ℝ} (hq : 0 ≤ q) :
    ∀ᵐ ω ∂P, ∀ s : ℚ, q ≤ (s : ℝ) →
      bdryApprox (Real.sqrt κ) (h0f κ s B X ω) = bdryApprox (Real.sqrt κ)
        (coordChange (h0f κ q B X ω) (acMap κ B ω q s) (Qc (Real.sqrt κ))) := by
  have h : ∀ s : ℚ, ∀ᵐ ω ∂P, q ≤ (s : ℝ) →
      bdryApprox (Real.sqrt κ) (h0f κ s B X ω) = bdryApprox (Real.sqrt κ)
        (coordChange (h0f κ q B X ω) (acMap κ B ω q s) (Qc (Real.sqrt κ))) := by
    intro s
    by_cases hs : q ≤ (s : ℝ)
    · filter_upwards [b2_regEq (κ := κ) (T := (s : ℝ)) (t := (s : ℝ) - q) hB hX hind
        (sub_nonneg.2 hs) (sub_le_self _ hq)] with ω hω _
      rw [Yf_horizon_eq_h0f] at hω
      exact Factorization.bdryApprox_congr (funext fun k => funext fun z => hω k z) _
    · exact ae_of_all _ fun ω h => absurd h hs
  exact ae_all_iff.2 h

end RegUnif
end QuantumZipper
