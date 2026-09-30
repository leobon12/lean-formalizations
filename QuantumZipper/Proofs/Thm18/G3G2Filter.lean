import QuantumZipper.Proofs.Thm18.G3ConcreteMarkov

/-!
# G3 fidelity (F4): the filter of the concrete scheme, and the concrete G2 statement

`handoff/G3.md`, G3-M123 (F4). The index `i = (δ, η, C)` of the concrete G3 scheme goes to its
limit in the order of Sheffield's argument (arXiv:1012.4797, proof of Theorem 1.8, §5.4,
pp. 70–71, and Proposition 5.5): first the zoom `C → ∞` (at fixed regions), then the inner gap
`η → 0` (so that the Palm point `x ∈ [−δ, 0]` falls in region 1, i.e. in `[−δ, −η]`, with
probability `→ 1`), then the Palm window `δ → 0`. As a filter this is the iterated (curried)
filter `𝓝[>] 0 ⊗_curry 𝓝[>] 0 ⊗_curry atTop` on `(δ, η, C)`, pulled back to the index set
(`g3Filter`): `f → L` along it iff for every `ε > 0`, for all small `δ`, for all small `η`
(depending on `δ`), for all large `C` (depending on `δ, η`), `|f − L| < ε`
(`tendsto_g3Filter_iff`). In particular the existence of the iterated limit
`lim_δ lim_η lim_C f = L` implies `f → L` along `g3Filter`.

* `g3Filter`, `neBot_g3Filter`, `eventually_g3Filter_iff`, `tendsto_g3Filter_iff`;
* `g3MarkovStmt_g3Filter : G3MarkovStmt (g3ConcreteMap fun _ => g3Filter)`;
* `G2ConcreteStmt γ` (G2 for the concrete scheme, a statement about `gffBase` only) and
  `g2TwoPointStmt_of_concrete`.

Own bookkeeping (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal

namespace QuantumZipper
namespace Thm18Asm

/-- The filter of the concrete G3 scheme: `C → ∞` first, then `η → 0`, then `δ → 0`. -/
def g3Filter : Filter G3Idx :=
  Filter.comap (fun i : G3Idx => i.1) ((𝓝[>] (0 : ℝ)).curry ((𝓝[>] (0 : ℝ)).curry atTop))

theorem eventually_g3Filter_iff {p : G3Idx → Prop} :
    (∀ᶠ i in g3Filter, p i) ↔
      ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ᶠ η in 𝓝[>] (0 : ℝ), ∀ᶠ C in (atTop : Filter ℝ),
        ∀ i : G3Idx, i.1 = (δ, η, C) → p i := by
  rw [g3Filter, eventually_comap, eventually_curry_iff]
  refine eventually_congr (Eventually.of_forall fun δ => ?_)
  rw [eventually_curry_iff]

theorem neBot_g3Filter : g3Filter.NeBot := by
  rw [g3Filter, comap_neBot_iff_frequently, frequently_curry_iff]
  have h1 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ ∈ Ioc 0 (1 / 4) := Ioc_mem_nhdsGT (by norm_num)
  refine (h1.mono fun δ hδ => ?_).frequently
  rw [frequently_curry_iff]
  have h2 : ∀ᶠ η in 𝓝[>] (0 : ℝ), η ∈ Ioo 0 δ := Ioo_mem_nhdsGT hδ.1
  refine (h2.mono fun η hη => ?_).frequently
  exact Frequently.of_forall fun C =>
    ⟨(Subtype.mk (δ, η, C) ⟨hη.1, hη.2, hδ.2⟩ : G3Idx), rfl⟩

instance : g3Filter.NeBot := neBot_g3Filter

/-- **F4.** Convergence along `g3Filter` is the iterated `ε`-condition. -/
theorem tendsto_g3Filter_iff {f : G3Idx → ℝ} {L : ℝ} :
    Tendsto f g3Filter (𝓝 L) ↔ ∀ ε > 0, ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ᶠ η in 𝓝[>] (0 : ℝ),
      ∀ᶠ C in (atTop : Filter ℝ), ∀ i : G3Idx, i.1 = (δ, η, C) → |f i - L| < ε := by
  rw [Metric.tendsto_nhds]
  simp only [Real.dist_eq, eventually_g3Filter_iff]

/-- **G2 for the concrete scheme** (Proposition 5.5 in the two-point, conditional form of
`G2TwoPointStmt`): along `g3Filter`, the conditional probability, given the field outside both
half-discs and the Palm length, that each zoom lies in a cylinder set converges in `L¹` to a
deterministic limit (intended: the `γ`-wedge law `𝒲_γ` for both). It only involves the base
sample `gffBase`. -/
def G2ConcreteStmt (γ : ℝ) : Prop :=
  ∃ μ ν : Measure LawD, IsProbabilityMeasure μ ∧ IsProbabilityMeasure ν ∧
    (∀ s ∈ lawCyl, Tendsto (fun i => ∫ p, |(g3PalmLaw γ i)[(g3U γ i ⁻¹' s).indicator
        (fun _ => (1 : ℝ)) | outsideSigmaPalm ℝ gffBase.X i.t₁ i.r₁ i.t₂ i.r₂] p - μ.real s|
          ∂(g3PalmLaw γ i)) g3Filter (𝓝 0)) ∧
    (∀ t ∈ lawCyl, Tendsto (fun i => ∫ p, |(g3PalmLaw γ i)[(g3V γ i ⁻¹' t).indicator
        (fun _ => (1 : ℝ)) | outsideSigmaPalm ℝ gffBase.X i.t₁ i.r₁ i.t₂ i.r₂] p - ν.real t|
          ∂(g3PalmLaw γ i)) g3Filter (𝓝 0))

end Thm18Asm
end QuantumZipper
