import QuantumZipper.Proofs.Thm18.G3ZcDyad
import QuantumZipper.Proofs.Zipper.HeadlineWire2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ZOOM-C (c): the fixed-point two-point core

`G3TwoPointFixedStmt` (proved, `g3TwoPointFixedStmt_holds`): on one probability space let
`(X₁, Ξ₁, g₁)` and `(X₂, Ξ₂, g₂)` be D3⁺ `Setup` data (exponents `α₁`, `α₂`, radii `r₁`, `r₂`), and
`Zf₁ L`, `Zf₂ L` two families of fields that a.s. agree near `0` with the respective D3⁺ models
(`AgreeNear`; e.g. the zooms of one free field at two points, `exists_g0Setup_two`, or the Palm
zooms of ZOOM-A). Assume the **separation clause**: for every level `L` the dyadic data of `Zf₂ L`
inside `ball 0 r₂` are a.s. a measurable function of `Ξ₁` (the field near the second point is read
from the conditioning variables of the first point; for the free field this is `FarPair`,
G3ZcFar). Then for measurable `Γ₁, Γ₂ ∈ [0,1]`

  `E[Γ₂(loc canonical Zf₂ L) · Γ₁(loc canonical Zf₁ L)] → E Γ₂(wedge α₂) · E Γ₁(wedge α₁)`.

Proof (Sheffield, arXiv:1012.4797, p. 71: conditionally on the field outside the first half-disc,
the first zoom converges to a wedge, and the second zoom is read from the outside):
* on the event where the second model's local scale lies in `(0, r₂/(R+1))` the second functional
  equals `Γ₂(dyadT(dyadData(Zf₂ L)))` (`locFieldFull_canonicalOn_eq_dyad`), hence a.s. the
  `σ(Ξ₁)`-measurable `F' = Γ₂(dyadT(f_L(Ξ₁)))`; the complementary event has probability `→ 0`
  (D3⁺(iii));
* `E F' → c₂` (D3⁺(i) at the second point, `d3_transfer_of_agree`);
* `E[F' Γ₁(Zf₁)] → c₂ c₁` (`twoPoint_of_agree`).

Own bookkeeping (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace G3Cv

open D3Plus

/-- The bad-scale event of a D3⁺ setup has vanishing probability (D3⁺(iii)). -/
theorem tendsto_bad_setup {γ α r : ℝ} {ρ₀ : Measure ℂ}
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → FieldSample} {E' : Type} [MeasurableSpace E'] {Ξ : Ω → E'} {g : Ω → ℂ → ℝ}
    (hS : Setup γ α r ρ₀ P X Ξ g) (R : ℕ) :
    (∀ L, AEMeasurable ({ω | 0 < scaleParamOn γ (zoomModel γ α L ρ₀ (X ω) (g ω)) (halfDisc r) ∧
        scaleParamOn γ (zoomModel γ α L ρ₀ (X ω) (g ω)) (halfDisc r) * R < r}ᶜ.indicator
          (1 : Ω → ℝ≥0∞)) P) ∧
    Tendsto (fun L => ∫⁻ ω, {ω | 0 < scaleParamOn γ (zoomModel γ α L ρ₀ (X ω) (g ω))
        (halfDisc r) ∧ scaleParamOn γ (zoomModel γ α L ρ₀ (X ω) (g ω)) (halfDisc r) * R < r}ᶜ.indicator
          (1 : Ω → ℝ≥0∞) ω ∂P) atTop (𝓝 0) := by
  have hr : 0 < r := hS.hr
  set a : ℝ → Ω → ℝ := fun L ω =>
    scaleParamOn γ (zoomModel γ α L ρ₀ (X ω) (g ω)) (halfDisc r) with ha
  set good : ℝ → Set Ω := fun L => {ω | 0 < a L ω ∧ a L ω * R < r} with hgood
  set F : ℝ → Ω → ℝ≥0∞ := fun L => (good L)ᶜ.indicator 1 with hF
  have hFm : ∀ L, AEMeasurable (F L) P := by
    intro L
    have hm := Prop16Asm.aemeasurable_scaleParamOn_zoomModel_mm hS L
    have hns : NullMeasurableSet (good L) P := by
      have h1 : NullMeasurableSet {ω | 0 < a L ω} P :=
        nullMeasurableSet_lt aemeasurable_const hm
      have h2 : NullMeasurableSet {ω | a L ω * R < r} P :=
        nullMeasurableSet_lt (hm.mul_const _) aemeasurable_const
      exact h1.inter h2
    exact (aemeasurable_const.indicator₀ hns.compl)
  refine ⟨hFm, ?_⟩
  have hRr : 0 < r / (R + 1) := by positivity
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun L => F L ω) atTop (𝓝 0) := by
    filter_upwards [d3PlusIII_holds γ α r ρ₀ P X Ξ g hS] with ω hω
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hω _ hRr] with L hL
    have hmem : ω ∈ good L := by
      refine ⟨hL.1, ?_⟩
      have h1 : a L ω * R ≤ a L ω * (R + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) hL.1.le
      have h2 : a L ω * (R + 1) < r := by
        have := hL.2
        rw [lt_div_iff₀ (by positivity)] at this
        linarith
      linarith
    simp [hF, hmem]
  have := tendsto_lintegral_filter_of_dominated_convergence' (μ := P)
    (fun _ => (1 : ℝ≥0∞)) (Eventually.of_forall hFm)
    (Eventually.of_forall fun L => ae_of_all _ fun ω => by
      simp only [hF]; exact Set.indicator_le (fun _ _ => le_rfl) ω)
    (by simp) hlim
  simpa using this

end G3Cv
end QuantumZipper
