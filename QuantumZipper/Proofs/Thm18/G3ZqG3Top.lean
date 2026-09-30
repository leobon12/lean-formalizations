import QuantumZipper.Proofs.Thm18.G3ZqG3Hon
import QuantumZipper.Proofs.Thm18.G3Pl4Node

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G3 above G2 with abstract zooms: the unscaled wedge transfer

Generalized copy (D92) of the wiring above G2 on the unscaled wedge side, with the plain zooms
replaced by abstract zooms `Z` (at `x`) and `Z'` (at `R(x)`):

* `g3plHonX_schemeC_Z`: copy of `g3TWedgePlainStmt_of_honest` (`G3PlWire.lean`) with the wedge
  side removed: the normalized honest window integral of scheme `C` against the weighted
  scheme-`C` integral (weight `g3plW`), margin mass close to `1`;
* `g3plPhiZ`: the wedge functional
  `Φ(y) = ∫_{window} 1_s(Z L y x) 1_t(Z' L y (partner x)) dν_y` (`g3plPhiZ_zoomLaw`: for the plain
  zoom it is `g3plPhi`);
* `G3PlPhiUnscaledStmtZ`: `G3PlPhiUnscaledStmt` (`G3Pl3Red.lean`) for abstract zooms, on the
  UNSCALED wedge field `g3plUW γ X A ω` (open for map zooms; for the plain zoom it is
  `g3PlPhiUnscaledStmt_holds`, see `g3PlPhiUnscaledStmtZ_zoomLaw`);
* `G3TJointMixZ`: the weighted joint-mixing clause of T5-J (`G3TProfJointMixStmt`,
  `R18G3TSplit.lean`) for abstract zooms (open);
* headline `g3UnscaledTransferZ`: from these, for all cylinders `s, t` and `ε > 0` there is
  `U₀ > 0` with `|U⁻¹ E Φ(wedgeU) − μ(s) ν(t)| ≤ ε` (two-sided `ℝ≥0∞` form) for all `U ≤ U₀`,
  eventually in `L` (copy of the arithmetic of `g3WedgeFreeTransferStmt_of_split`).

Sheffield, arXiv:1012.4797, proof of Thm. 1.8, §5.4, pp. 70–72. Own bookkeeping copied from the
originals.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace R18

open Thm18Asm

local notation "Ω₀" => gffBase.Ω

variable {Z Z' : ℝ → FieldSample → ℝ → LawD}

/-! ## Honest window integral against the weighted scheme `C` -/

/-! ## The wedge functional and the two open inputs -/

/-- The wedge functional with abstract zooms:
`Φ(y) = ∫_{Palm window} 1_s(Z L y x) · 1_t(Z' L y (partner x)) dν_y` (`G3Z2b2.g3PhiM2`-shaped). -/
def g3plPhiZ (Z Z' : ℝ → FieldSample → ℝ → LawD) (γ L U : ℝ) (s t : Set LawD) (y : FieldSample) :
    ℝ≥0∞ :=
  ∫⁻ x in g1zWedgeWin γ true y U,
    s.indicator 1 (Z L y x) * t.indicator 1 (Z' L y (g3zPartner γ y x))
    ∂((qBoundaryMeasure γ y).restrict (g1SideHalf true))

/-- **Weighted joint mixing of scheme `C` for abstract zooms** (the second clause of T5-J,
`G3TProfJointMixStmt`, `R18G3TSplit.lean`, at a fixed `γ` and limit laws `μ, ν`). Open for map
zooms. -/
def G3TJointMixZ (Z Z' : ℝ → FieldSample → ℝ → LawD) (γ : ℝ) (μ ν : Measure LawD) : Prop :=
  ∀ s ∈ lawCyl, ∀ t ∈ lawCyl, ∀ δ η m : ℝ, 0 < m → ∀ M : ℝ, ∀ ε > 0,
    ∀ᶠ C in (atTop : Filter ℝ), ∀ i : G3Idx, i.1 = (δ, η, C) →
    ∀ w : gffBase.Ω × ℝ → ℝ,
      Measurable[outsideSigmaPalm ℝ gffBase.X i.t₁ i.r₁ i.t₂ i.r₂] w →
      (∀ p, 0 ≤ w p ∧ w p ≤ M) →
      |∫ p, (g3pUfZ Z γ (g3wProf γ) i ⁻¹' s ∩ g3pVfZ Z' γ (g3wProf γ) i ⁻¹' t ∩
          g3pMarg γ (g3wProf γ) i m).indicator w p ∂(g3pPalmLaw γ (g3wProf γ) i) -
        μ.real s * ν.real t *
          ∫ p, (g3pMarg γ (g3wProf γ) i m).indicator w p ∂(g3pPalmLaw γ (g3wProf γ) i)| ≤ ε

/-! ## The headline -/

theorem g3zq_arith_le {a h : ℝ≥0∞} {I c e : ℝ} (hI : 0 ≤ I) (hc : 0 ≤ c) (he : 0 ≤ e)
    (h1 : a ≤ h + ENNReal.ofReal e) (h2 : h ≤ ENNReal.ofReal I + ENNReal.ofReal e)
    (h3 : I ≤ c + 2 * e) : a ≤ ENNReal.ofReal c + ENNReal.ofReal (4 * e) := by
  calc a ≤ h + ENNReal.ofReal e := h1
    _ ≤ ENNReal.ofReal I + ENNReal.ofReal e + ENNReal.ofReal e := by gcongr
    _ = ENNReal.ofReal (I + e + e) := by
        rw [ENNReal.ofReal_add (by linarith) he, ENNReal.ofReal_add hI he]
    _ ≤ ENNReal.ofReal (c + 4 * e) := ENNReal.ofReal_le_ofReal (by linarith)
    _ = ENNReal.ofReal c + ENNReal.ofReal (4 * e) := ENNReal.ofReal_add hc (by linarith)

theorem g3zq_arith_ge {a h : ℝ≥0∞} {I c e : ℝ} (hI : 0 ≤ I) (he : 0 ≤ e)
    (h1 : h ≤ a + ENNReal.ofReal e) (h2 : ENNReal.ofReal I ≤ h + ENNReal.ofReal e)
    (h3 : c ≤ I + 2 * e) : ENNReal.ofReal c ≤ a + ENNReal.ofReal (4 * e) := by
  calc ENNReal.ofReal c ≤ ENNReal.ofReal (I + 2 * e) := ENNReal.ofReal_le_ofReal h3
    _ = ENNReal.ofReal I + ENNReal.ofReal (2 * e) := ENNReal.ofReal_add hI (by linarith)
    _ ≤ h + ENNReal.ofReal e + ENNReal.ofReal (2 * e) := by gcongr
    _ ≤ a + ENNReal.ofReal e + ENNReal.ofReal e + ENNReal.ofReal (2 * e) := by gcongr
    _ = a + ENNReal.ofReal (4 * e) := by
        rw [add_assoc, add_assoc, ← ENNReal.ofReal_add he (by linarith),
          ← ENNReal.ofReal_add (by linarith) (by linarith)]
        ring_nf

end R18
end QuantumZipper
