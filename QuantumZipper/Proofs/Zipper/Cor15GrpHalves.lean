import QuantumZipper.Proofs.Zipper.Cor15GrpCore
import QuantumZipper.Proofs.RS.TraceShift

/-!
# D35: splitting the two halves of the core `Cor15GenuineStmt`

Sheffield, arXiv:1012.4797, Corollary 1.5 (pp. 17–18). Own bookkeeping (decision D35).

* `Cor15MarkovStmt` ⇐ `Cor15MarkovFieldStmt`: the Brownian half of the Markov property is the
  weak Markov property (mathlib `IsBrownianReal.shift`, `RS.drive_shift`): the driver of `D_a c`
  is `√κ` times the shifted Brownian motion `B(a + ·) − B(a)`, exactly on `[0,∞)`. What remains
  is the field: a free field `X'` (modulo constants) independent of the shifted path with
  `RegEq (D_a c).1 (𝔥₀ + X')` a.s.
* `Cor15ZipOntoStmt` ⇐ `Cor15UnzipZipSelfStmt` (round trip `D_a U_a c ≈ c`) and
  `Cor15ZipGenuineStmt` (`U_a c` is a.s. `ConfigEq` to a genuine configuration).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

namespace QuantumZipper
namespace Cor15Group

/-- **Markov property, field part.** The unzipped field is a.s. `RegEq` to `𝔥₀ + X'` for a
free field `X'` modulo constants, independent of the shifted Brownian path `B(a + ·) − B(a)`. -/
def Cor15MarkovFieldStmt : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample), IsGrpSetup P B X →
    ∀ a : ℝ, 0 < a → ∃ X' : Ω → FieldSample, IsFreeGFFModConstH X' P ∧
      IndepFun (pathOf fun u ω => B (a.toNNReal + u) ω - B a.toNNReal ω) X' P ∧
      ∀ᵐ ω ∂P, RegEq (zipCapDown (Real.sqrt κ) a (grpCfg κ B X ω)).1 (ofFun (h0rev κ) + X' ω)

/-- **Round trip, other direction**: `D_a (U_a c) ≈ c` a.s. (the case `b = t` of
`Cor15UnzipZipStmt`). -/
def Cor15UnzipZipSelfStmt : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample), IsGrpSetup P B X →
    ∀ a : ℝ, 0 < a → ∀ᵐ ω ∂P,
      ConfigEq (zipCapDown (Real.sqrt κ) a (zipCapUp (Real.sqrt κ) a (grpCfg κ B X ω)))
        (grpCfg κ B X ω)

theorem cor15MarkovStmt_of_field (h : Cor15MarkovFieldStmt) : Cor15MarkovStmt := by
  intro κ hκ hκ4 Ω _ P _ B X hS a ha
  obtain ⟨X', hX', hind', hreg⟩ := h κ hκ hκ4 P B X hS a ha
  refine ⟨fun u ω => B (a.toNNReal + u) ω - B a.toNNReal ω, X', ⟨hS.1.shift _, hX', hind'⟩, ?_⟩
  filter_upwards [hreg] with ω hω
  refine ⟨hω, fun u hu => ?_⟩
  show drive κ B ω (a + max u 0) - drive κ B ω a =
    drive κ (fun r ω => B (a.toNNReal + r) ω - B a.toNNReal ω) ω u
  rw [RS.drive_shift κ B a.toNNReal ω hu, Real.coe_toNNReal a ha.le, max_eq_left hu]

end Cor15Group
end QuantumZipper
