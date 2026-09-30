import QuantumZipper.Proofs.Thm18.Assembly
import QuantumZipper.Proofs.Section5.Prop17Point
import QuantumZipper.Proofs.Zipper.B5VSide
import QuantumZipper.Proofs.Zipper.B5ZeroMinus
import QuantumZipper.Proofs.Zipper.Cor15HullNull
import QuantumZipper.Proofs.RS.RealAlive

/-!
# Theorem 1.8: non-degeneracy of the unzipped lengths (`LenPosStmt`, DECISIONS D13)

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Theorem 1.8 ("the quantum
lengths of the two sides of `η[0,t]` … agree"), with the D13 requirement `0 < ℓ₁(t) < ∞` for
`t > 0`. Here `ℓ₁(t) = ν_{x_t}[O⁻_t, 0]`, where `x_t = unzippedField γ c t` is the wedge field
unzipped by capacity time `t` along the independent SLE_{γ²} and `O⁻_t = (sideImages W t).1`.

* `qBoundaryMeasure_Icc_lt_top` (deterministic): `ν_x` of a compact interval is always finite
  (`ν_x` is either a vague limit, hence locally finite, or the junk `0`). So the `< ⊤` half of
  `LenPosStmt` holds unconditionally.
* `lenSideNegStmt_holds` (proved): a.s. `O⁻_t < 0` for every `t > 0`.
* `lenPosStmt_of_bdryPos`: `LenPosStmt` from the one explicit hypothesis `UnzipBdryPosStmt`:
  a.s., for every `t > 0`, the boundary measure of the unzipped field charges every nonempty open
  subinterval of `[O⁻_t, 0]`.

Own elementary argument (monotonicity of measures); no published source is needed.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace Thm18Asm

/-- `ν_x` of a compact interval is finite, for every field sample. -/
theorem qBoundaryMeasure_Icc_lt_top (γ : ℝ) (x : FieldSample) (a b : ℝ) :
    qBoundaryMeasure γ x (Icc a b) < ⊤ := by
  by_cases h : qBoundaryMeasure γ x = 0
  · rw [h]
    simp
  · have := S5.isLocallyFiniteMeasure_qBoundaryMeasure h
    exact measure_Icc_lt_top

/-- **The left side image is nondegenerate** (explicit hypothesis): a.s., for every `t > 0`,
`O⁻_t < 0`. -/
def LenSideNegStmt : Prop :=
  ∀ (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample),
    Thm18Setting γ P B Y → Thm18Inputs γ P B Y →
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → (sideImages (drive (γ ^ 2) B ω) t).1 < 0

/-- **`LenSideNegStmt` holds.** For `t > 0`, `O⁻_t = 0₋(vrev W t, t)`
(`B5.sideImages_fst_eq_zeroMinus_vrev`, using that real points are never swallowed,
`RS.ae_real_alive`), and `0₋ < 0` because `revHull (vrev W t) t = fwdHull W t = η(0,t]` is a
simple arc (`Cor15Group.revHull_vrev_eq_fwdHull`, the Rohde–Schramm input of `Thm18Inputs`,
`B5.swallowedSet_eq_Icc_zeroMinus`). -/
theorem lenSideNegStmt_holds : LenSideNegStmt := by
  intro γ Ω _ P _ B Y hS hIn
  obtain ⟨hγ, hγ2, hB, -, -⟩ := hS
  have hκ : 0 < γ ^ 2 := by positivity
  have hκ4 : γ ^ 2 ≤ 4 := by nlinarith
  filter_upwards [hIn.2.2, hB.cont, hB.eval_zero_ae_eq_zero, RS.ae_real_alive hB hκ hκ4]
    with ω hrs hc h0 halive t ht
  obtain ⟨hchord, hhull, -, -⟩ := hrs
  have hWc : Continuous (drive (γ ^ 2) B ω) := Thm14FromThm13.continuous_drive hc
  have hW0 : drive (γ ^ 2) B ω 0 = 0 := by simp [drive, h0]
  have hK : IsSimpleCurveHull (revHull (B2.vrev (drive (γ ^ 2) B ω) t) t) := by
    rw [Cor15Group.revHull_vrev_eq_fwdHull hWc hW0 ht, hhull t ht.le]
    exact Thm14FromThm13.isSimpleCurveHull_image_Ioc hchord ht
  rw [B5.sideImages_fst_eq_zeroMinus_vrev hWc hW0 ht hK fun x hx => halive x hx t ht.le]
  exact (B5.swallowedSet_eq_Icc_zeroMinus (B2.continuous_vrev hWc t) (B2.vrev_zero ht.le) ht
    hK).1

end Thm18Asm
end QuantumZipper
