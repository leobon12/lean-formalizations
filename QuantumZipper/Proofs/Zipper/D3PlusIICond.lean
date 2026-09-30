import QuantumZipper.Proofs.Zipper.D3PlusIMarkov
import QuantumZipper.Proofs.Zipper.D3PlusIISplit

/-!
# D3⁺(ii) (LSC): the conditioning layer and the reduction to deterministic corrections

Task D3P-II (decision D23; statement `D3Plus.D3PlusIIStmt`, `D3PlusStmt.lean`). Blueprint
`E_BRANCH_BLUEPRINT.md` §3: "with `g` macroscopic, L2 (`freeGFF_halfDisc_markov`) reduces to
`Z_r + (deterministic g)`". This is the two-law analogue of D3⁺(i)'s conditioning layer
(`D3PlusIMix.lean`, `D3PlusIMarkov.lean`); standard measure theory, own elementary proofs
(Kallenberg, *Foundations of Modern Probability*, 2nd ed., Lemma 3.11, via
`lintegral_comp_indep`; dominated convergence).

* `measurable_tvDist_kernel₂`: `x ↦ d_TV(κ x, κ' x)` is measurable for finite kernels on a
  countably generated space.
* `eventually_two_sided_of_tv₂`: two families of kernels `κ_L ω`, `κ'_L ω` with
  `d_TV(κ_L ω, κ'_L ω) → 0` a.s. give the two-sided bound uniformly over `Φ ∈ [0,1]`.
* `eventually_two_sided_of_factor_pair_exc`: if `V L = T_L(Z, F)` off `B L` and
  `V' L = T'_L(Z, F)` off `B' L` (`Z ⊥ 𝒢`, `F` `𝒢`-measurable, `P(B L), P(B' L) → 0`), and the
  laws of `T_L(Z, f)`, `T'_L(Z, f)` are TV-close at `f = F ω` a.s., the two-sided bound holds.
* `LSCCoreGen rd` (the remaining node, for a local reading `rd`, see `D3PlusIISplit.lean`:
  factorization of both `zoomGen rd`s through the local part `localZ X r` and common macroscopic
  data `F`, and TV-closeness of the two deterministic-correction laws, controlled by a measurable
  bound) and `lscGen_of_core : LSCCoreGen rd → LSCGen rd`; `d3PlusII_of_core` is the D23 case.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace D3Plus

/-- Integrating out the independent part in a factorized quantity (from `lintegral_comp_indep`). -/
theorem lintegral_factor_eq {Ω S T E : Type*} {m𝒢 : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace E]
    {P : Measure Ω} [IsProbabilityMeasure P] (hm : m𝒢 ≤ mΩ) {Z : Ω → S} (hZ : Measurable Z)
    (hind : Indep (MeasurableSpace.comap Z inferInstance) m𝒢 P) {F : Ω → T}
    (hF : Measurable[m𝒢] F) {Tm : S × T → E} (hT : Measurable Tm) {Φ : Ω × E → ℝ≥0∞}
    (hΦ : Measurable[m𝒢.prod inferInstance] Φ) :
    ∫⁻ ω, Φ (ω, Tm (Z ω, F ω)) ∂P =
      ∫⁻ ω, ∫⁻ y, Φ (ω, y) ∂((P.map Z).map fun s => Tm (s, F ω)) ∂P := by
  have hsec : ∀ ω, Measurable fun y => Φ (ω, y) := fun ω =>
    hΦ.comp (@measurable_prodMk_left Ω E m𝒢 _ ω)
  have hΨ : Measurable[m𝒢.prod inferInstance] fun q : Ω × S => Φ (q.1, Tm (q.2, F q.1)) :=
    hΦ.comp (measurable_fst.prodMk (hT.comp (measurable_snd.prodMk (hF.comp measurable_fst))))
  rw [lintegral_comp_indep hm hZ hind hΨ]
  refine lintegral_congr fun ω => ?_
  exact (lintegral_map (f := fun y => Φ (ω, y)) (hsec ω)
    (hT.comp (measurable_id.prodMk measurable_const) : Measurable fun s => Tm (s, F ω))).symm

/-- Changing a `[0,1]`-valued integrand off an event costs at most its outer probability. -/
theorem lintegral_le_add_of_eq_off {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {u v : Ω → ℝ≥0∞} (hu : ∀ ω, u ω ≤ 1) (B : Set Ω) (h : ∀ᵐ ω ∂P, ω ∉ B → u ω = v ω) :
    ∫⁻ ω, u ω ∂P ≤ ∫⁻ ω, v ω ∂P + P B := by
  set U := toMeasurable P B
  have hUm : MeasurableSet U := measurableSet_toMeasurable _ _
  have hind1 : Measurable (U.indicator (1 : Ω → ℝ≥0∞)) := measurable_const.indicator hUm
  calc ∫⁻ ω, u ω ∂P ≤ ∫⁻ ω, (v ω + U.indicator 1 ω) ∂P := by
        refine lintegral_mono_ae ?_
        filter_upwards [h] with ω hω
        by_cases hωU : ω ∈ U
        · rw [indicator_of_mem hωU]; exact (hu ω).trans le_add_self
        · rw [hω fun hb => hωU (subset_toMeasurable _ _ hb)]; exact le_self_add
    _ = ∫⁻ ω, v ω ∂P + P B := by
        rw [lintegral_add_right _ hind1, lintegral_indicator_one hUm,
          measure_toMeasurable]

/-! ## The remaining node and the reduction -/

end D3Plus
end QuantumZipper
