import QuantumZipper.Proofs.Zipper.SWCoreA9Unif
import QuantumZipper.Proofs.Zipper.SWCoreA9Rand
import QuantumZipper.Proofs.Zipper.SWCoreA8Wedge
import QuantumZipper.Proofs.Zipper.SWCoreB7bAddOn
import QuantumZipper.Proofs.Zipper.RegUnif

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-A9 (3): the offset distortion bound for the `Γ⁰` field (pathwise)

`a9_pushErrR_path`: for a regular free sample `X₀`, the field `x = 𝔥₀ + X₀`, a continuous driver
`W` with `W 0 = 0`, the offset flow data `A9Data X₀ W` at rational parameters (SWCoreA9Rand) and
a jointly continuous witness `Zh(t, ·)` of the regularity of the unzipped fields
`y_t = x ∘ f_t⁻¹ + Q log|(f_t⁻¹)'|` (JointMod) which agrees with the raw values of `y_t` at the
rational parameters: for every `η > 0`, eventually in `k`, uniformly in `t ∈ [0,T]`,
`α ∈ [1,2]` and `z` in the rectangle, `|pushErrR γ x f_t⁻¹ (α 2^{-k}) z| ≤ η`.

Proof. At rational `(t, z, α)` the circle average of `y_t` is the raw value
`evalReg x (fc(z, α 2^{-k}).map f_t⁻¹) + Q log|(f_t⁻¹)'(z)|` (mean value property of the harmonic
`log|ψ'|`); the `𝔥₀` add-on (`Thm18Asm.G1Z3.evalReg_add_ofFun_of_ae_z3` with the continuous
cutoff `h0cut`, as `SWCoreB7bAddOn`/`SWCoreA8Add`) reduces the error to the free-field bound of
`A9Data` plus two circle-average errors of `h0cut` (`addon_circle_unif`). The error is a
continuous function of `(t, z, α)` (continuity of the witnesses and of the flow), so the bound
passes from the rational points to all parameters (`a9_le_of_rat`).

Sheffield–Wang, arXiv:1605.06171, proof of Thm 1.4, (3.5)–(3.7); own bookkeeping, mirrors
`a8_pushErr_wedge` with the radius factor `α` and the regular witness in place of `avgReg`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function Metric
open scoped Topology NNReal

namespace QuantumZipper
namespace SWCore

/-- **Density of rational parameters** in `[0,T] × rect × [1,2]`. -/
theorem a9_le_of_rat {Tq A B C D : ℚ} (hT : (0 : ℝ) ≤ Tq) (hAB : (A : ℝ) ≤ B)
    (hCD : (C : ℝ) ≤ D) {g : ℝ × ℂ × ℝ → ℝ}
    (hg : ContinuousOn g (Icc (0 : ℝ) Tq ×ˢ (rectC (A : ℝ) B C D ×ˢ Icc (1 : ℝ) 2))) {ε : ℝ}
    (hD : ∀ q : ℚ, (q : ℝ) ∈ Icc (0 : ℝ) Tq → ∀ z : ℚ × ℚ, zQ z ∈ rectC (A : ℝ) B C D →
      ∀ α : ℚ, (α : ℝ) ∈ Icc (1 : ℝ) 2 → g ((q : ℝ), zQ z, (α : ℝ)) ≤ ε) :
    ∀ p ∈ Icc (0 : ℝ) Tq ×ˢ (rectC (A : ℝ) B C D ×ˢ Icc (1 : ℝ) 2), g p ≤ ε := by
  rintro ⟨t, z, α⟩ ⟨ht, hz, hα⟩
  obtain ⟨u, hu, hut⟩ := a8_ratSeq (a := 0) (b := Tq) (by simpa using hT)
    (x := t) (by simpa using ht)
  obtain ⟨v, hv, hvt⟩ := a8_ratSeq hAB hz.1
  obtain ⟨w, hw, hwt⟩ := a8_ratSeq hCD hz.2
  obtain ⟨e, he, het⟩ := a8_ratSeq (a := 1) (b := 2) (by norm_num) (x := α) (by simpa using hα)
  have hmem : ∀ n, zQ (v n, w n) ∈ rectC (A : ℝ) B C D := fun n => by
    refine ⟨?_, ?_⟩ <;> simp only [zQ]
    · exact hv n
    · exact hw n
  have hu' : ∀ n, ((u n : ℚ) : ℝ) ∈ Icc (0 : ℝ) Tq := fun n => by simpa using hu n
  have he' : ∀ n, ((e n : ℚ) : ℝ) ∈ Icc (1 : ℝ) 2 := fun n => by simpa using he n
  have hzt : Tendsto (fun n => zQ (v n, w n)) atTop (𝓝 z) := by
    simp_rw [zQ_eq]
    have := (Complex.continuous_ofReal.tendsto _).comp hvt |>.add
      (((Complex.continuous_ofReal.tendsto _).comp hwt).mul_const Complex.I)
    rwa [Complex.re_add_im] at this
  have hs : Tendsto (fun n => (((u n : ℚ) : ℝ), zQ (v n, w n), ((e n : ℚ) : ℝ))) atTop
      (𝓝[Icc (0 : ℝ) Tq ×ˢ (rectC (A : ℝ) B C D ×ˢ Icc (1 : ℝ) 2)] (t, z, α)) :=
    tendsto_nhdsWithin_iff.2 ⟨hut.prodMk_nhds (hzt.prodMk_nhds het),
      Eventually.of_forall fun n => ⟨hu' n, hmem n, he' n⟩⟩
  exact le_of_tendsto' ((hg (t, z, α) ⟨ht, hz, hα⟩).tendsto.comp hs) fun n =>
    hD _ (hu' n) _ (hmem n) _ (he' n)

/-- **The `𝔥₀` add-on for `evalReg`** on a probability measure carried at height `≥ 3δ`. -/
theorem a9_evalReg_h0_add (κ : ℝ) {X0 : FieldSample} {FX : ℂ × ℝ → ℝ}
    (hFX : IsRegularWith X0 FX) {δ : ℝ} (hδ : 0 < δ) {ν : Measure ℂ} [IsProbabilityMeasure ν]
    {Kψ : Set ℂ} (hK : IsCompact Kψ) (hKim : ∀ u ∈ Kψ, 3 * δ ≤ u.im) (hν : ∀ᵐ u ∂ν, u ∈ Kψ)
    {L : ℝ} (hL : Tendsto (fun j => ∫ u, avgReg X0 j u ∂ν) atTop (𝓝 L)) :
    evalReg (ofFun (h0rev κ) + X0) ν = evalReg X0 ν + ∫ u, h0cut κ δ u ∂ν := by
  have hcth := a8_cth_im hδ hKim
  rw [add_comm]
  exact Thm18Asm.G1Z3.evalReg_add_ofFun_of_ae_z3 hFX (continuous_h0cut κ hδ).continuousOn hK
    (fun u hu => show 0 ≤ u.im by linarith [hKim u hu, hδ]) hδ
    (fun u hu => h0cut_eq ((hcth u hu).trans (Complex.im_le_norm u))) hν hL

end SWCore
end QuantumZipper
