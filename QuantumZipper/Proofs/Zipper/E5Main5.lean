import QuantumZipper.Proofs.Zipper.E5Main4
import QuantumZipper.Proofs.Zipper.EWire
import QuantumZipper.Proofs.Zipper.LocRichE6

/-!
# E5-MAIN, part 5: the E5 node from D3⁺(i), D3⁺(ii) and two identification inputs

Blueprint `blueprint/E_BRANCH_BLUEPRINT.md` §4, node **E5** (steps (1)–(5)); Sheffield,
arXiv:1012.4797, proof of Lemma 5.6 / Thm 1.3 (§5.4, pp. 66–72).

The probabilistic core of E5 (steps (2)–(5): LSC, D3⁺(iii), E5a/E5-DENS, D3⁺(i)) is proved in
`E5Main4.tvNear_model` on an abstract **zoom model** (`ZoomModel`). What remains open is stated
as two exact Props, generic in the local field readout `fr` (`locG fr` is `locData` for
`fr = TV.locField` and `locRich` for `fr = locFieldFull`, decision D25):

* `E5ModelStmtG fr` (steps (1) and (3), the concrete identification): given E4, for every E5 setup,
  `δ > 0` and `R`, there are a Brownian coordinate measure `W` and a zoom model (a probability
  space carrying a free field `X'`, conditioning data `Ξ`, the true correction `g` and the
  germ-free correction `g₀` of step (2), the germ `D` with the E-SM(b) Bayes structure
  `Q = Rr.withDensity w`, and the measurability data of E5-DENS) such that E5's left side is
  TV-near `p ·` (the model functional).
* `E5TargetStmtG fr` (the right side; **proved** in `E5Main6`): for `Y ⊥ B'` with `B'` Brownian, the `P_*` functional of
  `locData R` equals `E_{P'} E_W Γ(locField R Y, √κ b(min · R))` for every Brownian coordinate
  measure `W`.

`e5G_of_d3`, `e5Rich_of_d3` (target `E6.E5StmtRich`), `e5Node_of_d3` (target
`Thm13Asm.E5NodeStmt D3Plus.locData`).
The Palm mass is finite by Z-FIN (`EWire.zfin`), so the constant `p` can be carried through.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace E5

open LengthMarkov.GermDensity D3Plus B2 E1

/-- **The zoom model** at `γ = √κ`, `α = α₀ = √κ − 2/√κ`, window `R`, Wiener measure `W`: all
the data and hypotheses of `tvNear_model` except D3⁺(i), (ii) and the target wedge. -/
structure ZoomModel {F : Type} [MeasurableSpace F] (fr : ℕ → FieldSample → F) (κ : ℝ) (R : ℕ)
    (W : Measure (ℝ≥0 → ℝ)) where
  Ω₁ : Type
  [mΩ₁ : MeasurableSpace Ω₁]
  Q : Measure Ω₁
  [hQp : IsProbabilityMeasure Q]
  X' : Ω₁ → FieldSample
  E' : Type
  [mE' : MeasurableSpace E']
  Ξ : Ω₁ → E'
  r : ℝ
  ρ₀ : Measure ℂ
  g : Ω₁ → ℂ → ℝ
  g₀ : Ω₁ → ℂ → ℝ
  hS : D3Plus.Setup (Real.sqrt κ) (Real.sqrt κ - 2 / Real.sqrt κ) r ρ₀ Q X' Ξ g
  hS₀ : D3Plus.Setup (Real.sqrt κ) (Real.sqrt κ - 2 / Real.sqrt κ) r ρ₀ Q X' Ξ g₀
  hm : ∀ C, Measurable fun ω =>
    zScale (Real.sqrt κ) (Real.sqrt κ - 2 / Real.sqrt κ) r ρ₀ C (X' ω) (g ω)
  hm₀ : ∀ C, Measurable fun ω =>
    zScale (Real.sqrt κ) (Real.sqrt κ - 2 / Real.sqrt κ) r ρ₀ C (X' ω) (g₀ ω)
  hbadm : ∀ K : ℝ, MeasurableSet[condSigma Ξ X' r] (gBad r g g₀ K)
  hbad : ∀ ε : ℝ≥0∞, 0 < ε → ∃ K : ℝ, 0 ≤ K ∧ Q (gBad r g g₀ K) ≤ ε
  Rr : Measure Ω₁
  [hRr : IsProbabilityMeasure Rr]
  w : Ω₁ → ℝ≥0∞
  hw1 : ∫⁻ ω, w ω ∂Rr = 1
  hQ : Q = Rr.withDensity w
  𝕍 : Type
  [m𝕍 : MeasurableSpace 𝕍]
  V : Ω₁ → 𝕍
  hV : Measurable V
  D : Ω₁ → ℝ≥0 → ℝ
  hD : Measurable D
  hDm : Measurable[condSigma Ξ X' r] D
  hDc : ∀ ω, Continuous (D ω)
  u₀ : ℝ≥0
  hu₀ : 0 < u₀
  hind : IndepFun V (fun ω => pathRestr u₀ (D ω)) Rr
  hDW : Rr.map (fun ω => pathRestr u₀ (D ω)) = W.map (pathRestr u₀)
  a : ℝ → 𝕍 → ℝ
  ha : ∀ C, Measurable (a C)
  y : ℝ → 𝕍 → F
  hy : ∀ C, Measurable (y C)
  hay : ∀ C ω,
    zScale (Real.sqrt κ) (Real.sqrt κ - 2 / Real.sqrt κ) r ρ₀ C (X' ω) (g₀ ω) = a C (V ω) ∧
      zLoc fr (Real.sqrt κ) (Real.sqrt κ - 2 / Real.sqrt κ) r ρ₀ R C (X' ω) (g₀ ω) = y C (V ω)

attribute [instance] ZoomModel.mΩ₁ ZoomModel.hQp ZoomModel.mE' ZoomModel.hRr ZoomModel.m𝕍

/-- The model functional of a zoom model. -/
def ZoomModel.fn {F : Type} [MeasurableSpace F] {fr : ℕ → FieldSample → F} {κ : ℝ} {R : ℕ}
    {W : Measure (ℝ≥0 → ℝ)} (M : ZoomModel fr κ R W) :
    ℝ → (F × (ℝ≥0 → ℝ) → ℝ≥0∞) → ℝ≥0∞ := fun C Γ =>
  ∫⁻ ω, modelInt fr κ (Real.sqrt κ) (Real.sqrt κ - 2 / Real.sqrt κ) M.r M.ρ₀ R M.X' M.g M.D C Γ ω
    ∂M.Q

/-- The local data map read by `fr`: `(fr R c.1, s ↦ c.2 (min s R))` (`locData` for
`fr = TV.locField`, `locRich` for `fr = locFieldFull`). -/
def locG {F : Type} (fr : ℕ → FieldSample → F) (R : ℕ) (c : FieldSample × (ℝ → ℝ)) :
    F × (ℝ≥0 → ℝ) :=
  (fr R c.1, fun s => c.2 (min (s : ℝ) R))

/-- Z-FIN: the Palm mass of E5 is finite. -/
theorem pmass_ne_top {κ T : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample} {ϖ : Measure ℂ}
    (hS : Setup κ T P B X ϖ) {δ : ℝ} (hδ : 0 < δ) : pmass κ T P B X ϖ δ ≠ ⊤ := by
  obtain ⟨hκ, hκ4, hT, hB, hX, hind, hϖ⟩ := hS
  refine ne_top_of_le_ne_top (EWire.zfin hκ hκ4 hT hδ hB hX hind hϖ (ϖ := ϖ)).2.2.ne ?_
  exact lintegral_mono fun ω => measure_mono fun x hx => hx.1

end E5
end QuantumZipper
