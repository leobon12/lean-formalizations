import QuantumZipper.Proofs.Zipper.D3PlusN2TmZRad
import QuantumZipper.Proofs.Wire5
import QuantumZipper.Proofs.LQG.ZoomRadialMain

/-!
# N2-zero, heart, step 2: the radial part of the embedded model converges in TV

Task N2-TMZERO. The re-centred radial path of the model at its circle-average embedding,
`s ↦ zoomRadial α Q (zRadB X r) (n2Lev γ α L r) ω (max s (−S))`, is TV-close on every window
`[−S, ∞)` to the wedge's radial process `A`, uniformly over measurable path sets, with an error
`2 P''(∃ u ∈ [0,S], c_L ≤ A(−u)) → 0` as `L → ∞`.

Source: Duplantier–Miller–Sheffield arXiv:1409.7055, proof of Prop. 4.7 (p. 78, claims (a)–(c)
and "if we take a limit as `C → ∞`"); Sheffield arXiv:1012.4797 p. 25. Lean inputs:
`Wire5.abs_prob_zoomRadial_sub_le_uncond` (radial comparison, unconditional),
`ZoomRadial.tendsto_prob_wedge_high`, and `isBrownianReal_zRadB` (`D3PlusN2TmZRad.lean`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace D3Plus

theorem tendsto_n2Lev {γ : ℝ} (hγ : 0 < γ) (α r : ℝ) :
    Tendsto (fun L => n2Lev γ α L r) atTop atTop := by
  have h : Tendsto (fun L : ℝ => L / γ + -((α - Qc γ) * Real.log r)) atTop atTop :=
    tendsto_atTop_add_const_right _ _ (tendsto_id.atTop_div_const hγ)
  refine h.congr fun L => ?_
  simp only [n2Lev, sub_eq_add_neg]

/-- **Radial step of the heart.** -/
theorem n2_radial_tv {γ α r : ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → FieldSample} {Ω'' : Type} [MeasurableSpace Ω'']
    {P'' : Measure Ω''} [IsProbabilityMeasure P''] {A : ℝ → Ω'' → ℝ} (hγ : 0 < γ)
    (hα : α < Qc γ) (hr : 0 < r) (hX : IsFreeGFFModConstH X P)
    (hA : IsWedgeProcess α (Qc γ) A P'') {S : ℝ} (hS : 0 ≤ S) :
    Tendsto (fun L => 2 * (P'' {ω | ∃ u ∈ Icc 0 S, n2Lev γ α L r ≤ A (-u) ω}).toReal) atTop
      (𝓝 0) ∧
    ∀ L, 0 < n2Lev γ α L r → ∀ E : Set (ℝ → ℝ), MeasurableSet E →
      |(P {ω | (fun s => ZoomRadial.zoomRadial α (Qc γ) (zRadB X r) (n2Lev γ α L r) ω
          (max s (-S))) ∈ E}).toReal -
        (P'' {ω | (fun s => A (max s (-S)) ω) ∈ E}).toReal| ≤
      2 * (P'' {ω | ∃ u ∈ Icc 0 S, n2Lev γ α L r ≤ A (-u) ω}).toReal := by
  refine ⟨?_, fun L hL E hE =>
    Wire5.abs_prob_zoomRadial_sub_le_uncond hα (isBrownianReal_zRadB hX hr) hA hL hS hE⟩
  have h1 := (ZoomRadial.tendsto_prob_wedge_high hA hα S).comp (tendsto_n2Lev hγ α r)
  have h2 := ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h1).const_mul 2
  simpa using h2

end D3Plus
end QuantumZipper
