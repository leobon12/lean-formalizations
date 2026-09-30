import QuantumZipper.Proofs.Zipper.E4LimBasic

/-!
# E4-LIM: iterated dominated convergence and the pointwise limits of the grid integrands

`handoff/E4.md`, item E4-LIM (tools).

* `tendsto_iter_lintegral`: dominated convergence for `∫⁻ ω, ∫⁻ x in S, a_n ω x ∂ν ω ∂P` with
  `a_n ≤ 1`, `∫⁻ ω, ν ω S ∂P < ∞`; it also returns the a.e.-measurability of the limit (inner and
  outer), so that it can be iterated (`n → ∞`, then `ε → 0`). The integrands are only assumed
  a.e.-measurable (the lower integral `∫⁻` of a non-measurable function is not continuous).
* `tendsto_grid_ind` (`n → ∞`): the grid indicator `1{dyUp n σ_ε < T₀, live} K(dyUp n σ_ε)`
  tends to `1{σ_ε < T₀} K(σ_ε)` when `K` is right-continuous at `σ_ε` (for `x < V 0`, `ε > 0`).
* `tendsto_sigEps_ind` (`ε ↓ 0`): `1{σ_ε < T₀} K(σ_ε) → 1{τ_x ≤ T₀} c` when `K(s) → c` as
  `s ↑ τ_x` (whenever `τ_x ≤ T₀`).

Own elementary arguments (standard dominated convergence, mathlib
`tendsto_lintegral_of_dominated_convergence'`); they fill in the limiting step of the dyadic
approximation in the proof of Sheffield, arXiv:1012.4797, Lemma 5.6 (pp. 66–68).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace E4Grid

open E1 RealLine

section DCT

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- Iterated dominated convergence with the measurability of the limit. -/
theorem tendsto_iter_lintegral {ν : Ω → Measure ℝ} {S : Set ℝ} (hfin : ∀ ω, ν ω S < ⊤)
    (hint : ∫⁻ ω, ν ω S ∂P ≠ ⊤) {a : ℕ → Ω → ℝ → ℝ≥0∞} {b : Ω → ℝ → ℝ≥0∞}
    (hle : ∀ n ω x, a n ω x ≤ 1)
    (hxm : ∀ᵐ ω ∂P, ∀ n, AEMeasurable (a n ω) ((ν ω).restrict S))
    (hωm : ∀ n, AEMeasurable (fun ω => ∫⁻ x in S, a n ω x ∂ν ω) P)
    (hlim : ∀ᵐ ω ∂P, ∀ᵐ x ∂(ν ω).restrict S, Tendsto (fun n => a n ω x) atTop (𝓝 (b ω x))) :
    Tendsto (fun n => ∫⁻ ω, ∫⁻ x in S, a n ω x ∂ν ω ∂P) atTop
        (𝓝 (∫⁻ ω, ∫⁻ x in S, b ω x ∂ν ω ∂P)) ∧
      AEMeasurable (fun ω => ∫⁻ x in S, b ω x ∂ν ω) P ∧
      ∀ᵐ ω ∂P, AEMeasurable (b ω) ((ν ω).restrict S) := by
  have hin : ∀ᵐ ω ∂P, Tendsto (fun n => ∫⁻ x in S, a n ω x ∂ν ω) atTop
      (𝓝 (∫⁻ x in S, b ω x ∂ν ω)) := by
    filter_upwards [hxm, hlim] with ω hm hl
    refine tendsto_lintegral_of_dominated_convergence' (fun _ => 1) hm
      (fun n => Eventually.of_forall (hle n ω)) ?_ hl
    rw [lintegral_one, Measure.restrict_apply_univ]
    exact (hfin ω).ne
  refine ⟨tendsto_lintegral_of_dominated_convergence' (fun ω => ν ω S) hωm
    (fun n => Eventually.of_forall fun ω => ?_) hint hin,
    aemeasurable_of_tendsto_metrizable_ae' hωm hin, ?_⟩
  · exact (lintegral_mono fun x => hle n ω x).trans_eq
      (by rw [lintegral_one, Measure.restrict_apply_univ])
  · filter_upwards [hxm, hlim] with ω hm hl
    exact aemeasurable_of_tendsto_metrizable_ae' hm hl

end DCT

variable {V : ℝ → ℝ} {x T₀ : ℝ}

/-- **`n → ∞`.** The grid indicator converges to the indicator at the entrance time. -/
theorem tendsto_grid_ind (hV : Continuous V) (hx : x < V 0) (hT₀ : 0 < T₀) {ε : ℝ}
    (hε : 0 < ε) {K : ℝ → ℝ → ℝ≥0∞}
    (hK : sigEps V T₀ ε x < T₀ →
      ContinuousWithinAt (K x) (Ici (sigEps V T₀ ε x)) (sigEps V T₀ ε x)) :
    Tendsto (fun n => {y | dyUp n (sigEps V T₀ ε y) < T₀ ∧
        IsLive V (dyUp n (sigEps V T₀ ε y)) y}.indicator
          (fun y => K y (dyUp n (sigEps V T₀ ε y))) x) atTop
      (𝓝 ({y | sigEps V T₀ ε y < T₀}.indicator (fun y => K y (sigEps V T₀ ε y)) x)) := by
  simp only [indicator_apply, mem_setOf_eq]
  set σ := sigEps V T₀ ε x
  by_cases hσ : σ < T₀
  · rw [if_pos hσ]
    have hl := isLive_sigEps hV hx hT₀.le hε (T₀ := T₀)
    have hev := eventually_dyUp_lt_live hl hσ
    refine ((hK hσ).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨tendsto_dyUp σ,
      Eventually.of_forall fun n => le_dyUp n σ⟩)).congr' ?_
    filter_upwards [hev] with n hn
    exact (if_pos hn).symm
  · rw [if_neg hσ]
    exact tendsto_const_nhds.congr fun n =>
      (if_neg fun h => hσ ((le_dyUp n σ).trans_lt h.1)).symm

/-- **`ε ↓ 0`.** The entrance-time indicator converges to the collision indicator. -/
theorem tendsto_sigEps_ind (hV : Continuous V) (hx : x < V 0) (hT₀ : 0 < T₀)
    {K : ℝ → ℝ → ℝ≥0∞} {C : ℝ → ℝ≥0∞}
    (hK : ∀ τ, realHitTime V x = ENNReal.ofReal τ → τ ≤ T₀ →
      Tendsto (K x) (𝓝[<] τ) (𝓝 (C x))) :
    Tendsto (fun ε => {y | sigEps V T₀ ε y < T₀}.indicator (fun y => K y (sigEps V T₀ ε y)) x)
      (𝓝[>] 0) (𝓝 ({y | realHitTime V y ≤ ENNReal.ofReal T₀}.indicator C x)) := by
  simp only [indicator_apply, mem_setOf_eq]
  by_cases h : realHitTime V x ≤ ENNReal.ofReal T₀
  · obtain ⟨τ, hτ⟩ : ∃ τ, realHitTime V x = ENNReal.ofReal τ :=
      ⟨(realHitTime V x).toReal, (ENNReal.ofReal_toReal (ne_top_of_le_ne_top
        ENNReal.ofReal_ne_top h)).symm⟩
    have hτT : τ ≤ T₀ := by
      rw [hτ] at h; exact (ENNReal.ofReal_le_ofReal_iff hT₀.le).1 h
    rw [if_pos h]
    have hσ : Tendsto (fun ε => sigEps V T₀ ε x) (𝓝[>] 0) (𝓝[<] τ) :=
      tendsto_nhdsWithin_iff.2 ⟨tendsto_sigEps_hit hV hx hτ hτT, by
        filter_upwards [self_mem_nhdsWithin] with ε hε
        exact sigEps_lt_hit hV hx hτ hT₀.le hε⟩
    refine ((hK τ hτ hτT).comp hσ).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (if_pos ((sigEps_lt_hit hV hx hτ hT₀.le hε).trans_le hτT)).symm
  · push Not at h
    rw [if_neg (not_le.2 h)]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_sigEps_eq_cap hV hT₀.le h] with ε hε
    exact (if_neg (by rw [hε]; exact lt_irrefl T₀)).symm

end E4Grid
end QuantumZipper
