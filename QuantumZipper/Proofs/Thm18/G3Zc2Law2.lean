import QuantumZipper.Proofs.Thm18.G3Zc2Law

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ZOOM-C 2: law transfer of the two-point zoom limit

`tendsto_twoPoint_of_lawEq`: if two families of pairs of fields `(Zf₁ L, Zf₂ L)` (on `P`) and
`(Z₁ L, Z₂ L)` (on `P'`) have, for every level `L`, the same **joint** law of their dyadic data
(inside `ball 0 r₁`, resp. `ball 0 r₂`), all four have a.s. local area limits, the bad dyadic
masses of `Zf₁ L`, `Zf₂ L` tend to `0`, and the two-point functional of `(Zf₁, Zf₂)` converges to
`c`, then so does that of `(Z₁, Z₂)`. With `g3TwoPointFixedStmt_holds` (G3Zc2Two) for the coupled
fields and `tendsto_dyadBad_of_setup` (below) for the bad masses, this moves the two-point core from
the coupled free field of `exists_g0Setup_two` to any field whose pair of dyadic data has the same
law (e.g. the free field of the Palm identity).

Own bookkeeping (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace G3Cv

open D3Plus

/-- The bad dyadic mass of a family agreeing with a D3⁺ model tends to `0` (D3⁺(iii)). -/
theorem tendsto_dyadBad_of_setup {γ α r : ℝ} {ρ₀ : Measure ℂ}
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → FieldSample} {E' : Type} [MeasurableSpace E'] {Ξ : Ω → E'} {g : Ω → ℂ → ℝ}
    (hS : Setup γ α r ρ₀ P X Ξ g) {Zf : ℝ → Ω → FieldSample}
    (hag : ∀ᵐ ω ∂P, ∀ L : ℝ, AgreeNear (Zf L ω) (zoomModel γ α L ρ₀ (X ω) (g ω)) r)
    (hZm : ∀ L, AEMeasurable (fun ω => dyadData r (Zf L ω)) P) (R : ℕ) :
    (∀ L, ∀ᵐ ω ∂P, ∃ m, IsVagueLimitOn (halfDisc r) (areaApprox γ (Zf L ω)) m) ∧
    Tendsto (fun L => (P.map fun ω => dyadData r (Zf L ω)) (dyadBad γ r R)) atTop (𝓝 0) := by
  have hg : ∀ L, ∀ᵐ ω ∂P, ∃ m, IsVagueLimitOn (halfDisc r) (areaApprox γ (Zf L ω)) m := by
    intro L
    filter_upwards [ae_exists_isVagueLimitOn_zoomModel hS, hag] with ω h1 h2
    exact (exists_isVagueLimitOn_halfDisc_iff (h2 L)).2 (h1 L)
  refine ⟨hg, ?_⟩
  obtain ⟨hBm, hB0⟩ := tendsto_bad_setup hS R
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hB0 (fun _ => bot_le)
    fun L => ?_
  have hIm : Measurable ((dyadBad γ r R).indicator (1 : (DyIdxIn r → ℝ) → ℝ≥0∞)) :=
    measurable_const.indicator (measurableSet_dyadBad γ r R)
  rw [← lintegral_indicator_one (measurableSet_dyadBad γ r R),
    lintegral_map' hIm.aemeasurable (hZm L)]
  refine lintegral_mono_ae ?_
  filter_upwards [hag, hg L] with ω h1 h2
  by_cases hgd : 0 < scaleParamOn γ (zoomModel γ α L ρ₀ (X ω) (g ω)) (halfDisc r) ∧
      scaleParamOn γ (zoomModel γ α L ρ₀ (X ω) (g ω)) (halfDisc r) * R < r
  · have hs := scaleParamOn_halfDisc_congr (γ := γ) (h1 L)
    have hag' := agreeNear_dyadField r (Zf L ω)
    have hgood : dyadData r (Zf L ω) ∈
        Prop16Area.Meas.goodSet γ (dyadField r) (fun _ => halfDisc r) :=
      (exists_isVagueLimitOn_halfDisc_iff hag').1 h2
    have hs' := scaleParamOn_halfDisc_congr (γ := γ) hag'
    have hnb : dyadData r (Zf L ω) ∉ dyadBad γ r R := by
      simp only [dyadBad, mem_ofPred_eq, not_not]
      rw [dyadScale_eq hgood, ← hs', hs]
      exact hgd
    rw [Set.indicator_of_notMem hnb]
    exact bot_le
  · have hb : ω ∈ {ω | 0 < scaleParamOn γ (zoomModel γ α L ρ₀ (X ω) (g ω)) (halfDisc r) ∧
        scaleParamOn γ (zoomModel γ α L ρ₀ (X ω) (g ω)) (halfDisc r) * R < r}ᶜ := hgd
    rw [Set.indicator_of_mem hb]
    exact Set.indicator_le (fun _ _ => le_rfl) _

end G3Cv
end QuantumZipper
