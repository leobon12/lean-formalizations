import QuantumZipper.Proofs.Zipper.E6NodeMain
import QuantumZipper.Proofs.Zipper.LocLenStmts

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R5a (D75): open-arc statements of the E6 identity and of the Palm regularity set

Open-arc copies (substitution rule of `handoff/FOLLOW-PAPER-13.md` §1) of

* `E6.LenCollidedStmt` / `E6.LenCollidedAllStmt` (E6Id.lean:202, E6NodeAsm.lean:49):
  `unzipLengths ↦ unzipLengthsArc`; the reading in the fixed chart `T` (`h0f κ T`) stays global
  (L1); it is read on the open preimage arc `Ioo` (as in `B5UniformArcStmt`; the fixed-chart
  measure is atomless, `B5.ae_nu0_regular`, so `Ioo`/`Icc` agree there);
* `E6.CanonZipRawStmt` / `E6.CanonZipRawAllStmt` (LocRichId.lean:42, E6NodeAsm.lean:56):
  `unzipLengths ↦ unzipLengthsArc`, `zipLenDown ↦ zipLenDownArc`;
(the Palm regularity set `RegDetArc` / `E6PalmRegArcStmt` is in `LocLenR5aPalm.lean`, on top of
the open-arc local readers of R5c, `LocLenR5cRead.lean` / `LocLenR5cMain.lean`).

Sources: Sheffield, arXiv:1012.4797, §5.4 pp. 70–72 (E6 identity, locality); Berestycki–Powell,
arXiv:2404.16642, Def 6.41 p. 229 (lengths of open boundary arcs).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace LocLen

open B2 E1 D3Plus E6 MeasUnzip CharFun

/-! ## E6-ID, length part -/

/-- Open-arc copy of `E6.LenCollidedStmt`. -/
def LenCollidedArcStmt (κ T : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) : Prop :=
  ∀ᵐ ω ∂P, ∀ u s : ℝ, 0 ≤ u → 0 ≤ s → u + s ≤ T →
    (unzipLengthsArc (Real.sqrt κ) (zipCapDown (Real.sqrt κ) u (cfg κ B X ω)) s).1 =
      qBoundaryMeasure (Real.sqrt κ) (h0f κ T B X ω)
        (Ioo (zeroMinus (Vr κ T B ω) (T - u)) (zeroMinus (Vr κ T B ω) (T - u - s)))

/-- Open-arc copy of `E6.LenCollidedAllStmt`. -/
def LenCollidedAllArcStmt : Prop :=
  ∀ (κ T : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample), 0 < κ → κ < 4 → 0 < T →
    IsBrownianReal B P → IsFreeGFFModConstH X P → IndepFun (pathOf B) X P →
    LenCollidedArcStmt κ T P B X

/-! ## E6-ID, raw zip algebra -/

/-- Open-arc copy of `E6.CanonZipRawStmt`. -/
def CanonZipRawArcStmt (κ T : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) : Prop :=
  ∀ᵐ ω ∂P, ∀ u t₀ k ℓ : ℝ, 0 ≤ u → 0 ≤ t₀ → u + t₀ ≤ T → 0 < ℓ →
    t₀ = sInf {s : ℝ | 0 ≤ s ∧ ENNReal.ofReal ℓ ≤
      ENNReal.ofReal (Real.exp (Real.sqrt κ * k / 2)) *
        (unzipLengthsArc (Real.sqrt κ) (zipCapDown (Real.sqrt κ) u (cfg κ B X ω)) s).1} →
    RawEq
      (zipLenDownArc (Real.sqrt κ) ℓ (canonConfig (Real.sqrt κ)
        (addConst (zipCapDown (Real.sqrt κ) u (cfg κ B X ω)).1 k,
          (zipCapDown (Real.sqrt κ) u (cfg κ B X ω)).2)))
      (canonConfig (Real.sqrt κ)
        (addConst (zipCapDown (Real.sqrt κ) (u + t₀) (cfg κ B X ω)).1 k,
          (zipCapDown (Real.sqrt κ) (u + t₀) (cfg κ B X ω)).2))

/-- Open-arc copy of `E6.CanonZipRawAllStmt`. -/
def CanonZipRawAllArcStmt : Prop :=
  ∀ (κ T : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample), 0 < κ → κ < 4 → 0 < T →
    IsBrownianReal B P → IsFreeGFFModConstH X P → IndepFun (pathOf B) X P →
    CanonZipRawArcStmt κ T P B X

end LocLen
end QuantumZipper
