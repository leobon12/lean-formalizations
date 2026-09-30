import QuantumZipper.Proofs.Thm18.G1RCRaw
import QuantumZipper.Proofs.Thm18.G1RegRepRed

/-!
# G1-RC, part 6: `G1RegRepRC2Stmt` (and every-circle RC3) from two sharper inputs

`G1RegRepRC2Stmt` (G1RegRepRed.lean) asks: for a.e. path and both sides, the canonical wedge
representative pulled back by the selected inverse uniformizer `ψ = Ψ left a` is a.s. a regular
sample. This file reduces it (`G1RC.g1RegRepRC2Stmt_of`) to

* `G1RC.G1PsiExtStmt` (**analytic input, per path**): `ψ` agrees on `ℍ` with a map `ψe`
  continuous on `Hbar`, `ψe(Hbar) ⊆ Hbar`, whose smoothed pushed-circle family has the
  Kolmogorov bounds `PushFamBounds ψe β` (support, log-potential, variance modulus in
  `(d, r, s, t)`; for SLE side domains: Carathéodory extension, Hölder boundary (Rohde–Schramm
  Thm 5.2), Frostman bounds for the pushed circles);
* `G1RC.G1RawSmoothStmt` (**raw identification of the wedge field**): for every regular version
  `G` of `X`, there is a random `D`, a.s. continuous on `Hbar × (0,∞)` and smoothing-symmetric,
  such that a.s., for every folded circle, the raw value of the pulled-back field is
  `L + D(d, r)` whenever `∫ G(u, S 2^{-k}) d((S ψe)_* fc(d, r))(u) → L` (`k → ∞`), where
  `S = scaleParam γ w₀` is the random canonical scale of `w₀ = wedgeField (lateralPart X) A Q`
  (and `S > 0` a.s.). The intended `D` is
  `∫ wedgeProfile d((S ψe)_* fc(d, r)) + Q log S + Q ∫ log |ψ'| dfc(d, r)`: the unwinding of
  `coordChange`, `rescale` (scale consistency), `wedgeField` and `lateralPart`
  (cf. `WedgeRC3AllBasic.evalReg_wedgeField_fc_of_gap`).

The same inputs give RC3 at every folded circle (`G1RC.ae_rc3_of`), the first clause of
`G1.CoreRest`; the measurable-set packaging of `G1RegRepRestStmt` and PAIR-LIM are not done here.

Source: Duplantier–Sheffield, Invent. Math. 185 (2011), Prop. 3.1 (through G1RC{Kolm,Eval,
Circle,Comm,Raw}); the reduction is own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Metric Set Function Real
open scoped ENNReal NNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G1RC

open WedgeTK

/-- A continuous extension of `ψ` from `ℍ` to `Hbar` with the Kolmogorov bounds. -/
def PsiExt (ψ : ℂ → ℂ) : Prop :=
  ∃ ψe : ℂ → ℂ, Measurable ψe ∧ ContinuousOn ψe Hbar ∧ MapsTo ψe Hbar Hbar ∧ EqOn ψ ψe H ∧
    ∃ β : ℝ, 0 < β ∧ PushFamBounds ψe β

/-- **Analytic input**: for a.e. path, both selected maps have a `PsiExt`. -/
def G1PsiExtStmt : Prop :=
  G1RepSetting fun γ _ _ P B _ _ _ _ _ => ∀ Ψ, G1PsiSel γ Ψ →
    ∀ᵐ a ∂(P.map (pathOf B)), ∀ left : Bool, PsiExt (Ψ left a)

/-- The unscaled wedge field `w₀ = wedgeField (lateralPart X) A Q` of the representative. -/
def wedge0 (γ : ℝ) {Ω' : Type} (X : Ω' → FieldSample) (A : ℝ → Ω' → ℝ) (ω' : Ω') :
    FieldSample :=
  wedgeField (lateralPart (X ω')) (fun t => A t ω') (Qc γ)

/-- **Raw identification input** for the pulled-back canonical wedge field. -/
def G1RawSmoothStmt : Prop :=
  G1RepSetting fun γ _ _ P B Ω' _ P' X A => ∀ Ψ, G1PsiSel γ Ψ →
    ∀ᵐ a ∂(P.map (pathOf B)), ∀ left : Bool, ∀ ψe : ℂ → ℂ, EqOn (Ψ left a) ψe H →
      ∀ G : Ω' → ℂ × ℝ → ℝ, IsRegVersion X P' G →
      ∃ D : Ω' → ℂ × ℝ → ℝ,
        (∀ᵐ ω' ∂P', 0 < scaleParam γ (wedge0 γ X A ω') ∧
          ContinuousOn (D ω') (Hbar ×ˢ Ioi 0) ∧
          ∀ w ∈ Hbar, ∀ r ρ : ℝ, 0 < r → 0 < ρ →
            ∫ u, D ω' (u, ρ) ∂foldedCircle w r = ∫ v, D ω' (v, r) ∂foldedCircle w ρ) ∧
        ∀ᵐ ω' ∂P', ∀ d ∈ Hbar, ∀ r : ℝ, 0 < r → ∀ L : ℝ,
          Tendsto (fun k : ℕ => ∫ u, G ω' (u, scaleParam γ (wedge0 γ X A ω') * radius k)
              ∂((foldedCircle d r).map fun z => (scaleParam γ (wedge0 γ X A ω') : ℂ) * ψe z))
            atTop (𝓝 L) →
          coordChange (wedgeRep γ X A ω') (Ψ left a) (Qc γ) (foldedCircle d r) =
            L + D ω' (d, r)

/-- The common core: RC2 and every-circle RC3, a.s., for a.e. path and both sides. -/
theorem ae_rc_of (h1 : G1PsiExtStmt) (h2 : G1RawSmoothStmt) (γ : ℝ) (hγ : 0 < γ)
    (hγ2 : γ < 2) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P) {Ω' : Type} [MeasurableSpace Ω']
    (P' : Measure Ω') [IsProbabilityMeasure P'] (X : Ω' → FieldSample) (A : ℝ → Ω' → ℝ)
    (hX : IsFreeGFFModConstH X P') (hA : IsWedgeProcess (γ - 2 / γ) (Qc γ) A P')
    (hXA : IndepFun X (fun ω t => A t ω) P') (Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ)
    (hΨ : G1PsiSel γ Ψ) :
    ∀ᵐ a ∂(P.map (pathOf B)), ∀ left : Bool, ∀ᵐ ω' ∂P',
      IsRegularSample (coordChange (wedgeRep γ X A ω') (Ψ left a) (Qc γ)) ∧
      ∀ d ∈ Hbar, ∀ r : ℝ, 0 < r →
        evalReg (coordChange (wedgeRep γ X A ω') (Ψ left a) (Qc γ)) (foldedCircle d r) =
          coordChange (wedgeRep γ X A ω') (Ψ left a) (Qc γ) (foldedCircle d r) := by
  obtain ⟨G, hG⟩ := exists_isRegVersion hX
  filter_upwards [h1 γ hγ hγ2 P B hB P' X A hX hA hXA Ψ hΨ,
    h2 γ hγ hγ2 P B hB P' X A hX hA hXA Ψ hΨ] with a ha1 ha2 left
  obtain ⟨ψe, hψm, hψc, hψH, heq, β, hβ, hBd⟩ := ha1 left
  obtain ⟨D, hD, hlim⟩ := ha2 left ψe heq G hG
  exact ae_rc_of_smoothing (x := fun ω' => coordChange (wedgeRep γ X A ω') (Ψ left a) (Qc γ))
    (S := fun ω' => scaleParam γ (wedge0 γ X A ω')) hψm hψc hψH hβ hBd hX hG hD hlim

/-- **`G1RegRepRC2Stmt` from the analytic input and the raw identification.** -/
theorem g1RegRepRC2Stmt_of (h1 : G1PsiExtStmt) (h2 : G1RawSmoothStmt) : G1RegRepRC2Stmt := by
  intro γ hγ hγ2 Ω _ P _ B hB Ω' _ P' _ X A hX hA hXA Ψ hΨ
  filter_upwards [ae_rc_of h1 h2 γ hγ hγ2 P B hB P' X A hX hA hXA Ψ hΨ] with a ha left
  filter_upwards [ha left] with ω' h using h.1

/-- **RC3 at every folded circle** (the first clause of `G1.CoreRest`), a.s., from the same
inputs. -/
theorem ae_rc3_of (h1 : G1PsiExtStmt) (h2 : G1RawSmoothStmt) :
    G1RepSetting fun γ _ _ P B _ _ P' X A => ∀ Ψ, G1PsiSel γ Ψ →
      ∀ᵐ a ∂(P.map (pathOf B)), ∀ left : Bool, ∀ᵐ ω' ∂P', ∀ d ∈ Hbar, ∀ r : ℝ, 0 < r →
        evalReg (coordChange (wedgeRep γ X A ω') (Ψ left a) (Qc γ)) (foldedCircle d r) =
          coordChange (wedgeRep γ X A ω') (Ψ left a) (Qc γ) (foldedCircle d r) := by
  intro γ hγ hγ2 Ω _ P _ B hB Ω' _ P' _ X A hX hA hXA Ψ hΨ
  filter_upwards [ae_rc_of h1 h2 γ hγ hγ2 P B hB P' X A hX hA hXA Ψ hΨ] with a ha left
  filter_upwards [ha left] with ω' h using h.2

end G1RC
end Thm18Asm
end QuantumZipper
