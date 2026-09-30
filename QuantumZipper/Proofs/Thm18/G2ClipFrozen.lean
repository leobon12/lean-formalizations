import QuantumZipper.Proofs.Thm18.G2ClipTV
import Mathlib.MeasureTheory.Measure.Prod

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G2 clipped-shift node: the frozen-coefficient estimate

Sheffield (arXiv:1012.4797, proof of Prop. 5.5, p. 66): with `h = α φ + h₀`, `α` Gaussian and
independent of `h₀`, conditionally on `ξ = (h₀, root)` the length is `L = f_ξ(α)` with `f_ξ`
smooth and strictly increasing, and the clipped length is `L − d(ξ)` with `0 ≤ d(ξ) ≤ ρ`
independent of `α`. The joint law of `(ξ, α)` is then a product `Q ⊗ N` (`N` Gaussian), and the
claim is that the `Q ⊗ N`-measure of `{(ξ, L) ∈ S}` and of `{(ξ, L − d) ∈ S}` differ by at most
`ε`, uniformly in the event `S` and in the shift `d`, once `ρ` is small.

`g2clip_frozen` proves exactly this, for any finite `Q`, any `N ≪ Leb` and any jointly
measurable family `f_ξ` of differentiable maps with `f_ξ' > 0`: per `ξ` the shift costs at most
the translation modulus `g2clipMod N f_ξ ρ` (`g2clip_tv_shift`, which tends to `0`), and the
moduli are averaged by dominated convergence (`g2clip_lintegral_tendsto_zero`).

Own elementary bookkeeping (AGENT_GUIDE cost rule); the probabilistic content is Sheffield's.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace Thm18Asm

/-- The translation modulus of the law of `f(α)`, `α ∼ N`, at scale `ρ`:
`sup_{|d| < ρ} sup_E |N{f ∈ E} − N{f + d ∈ E}|`. -/
def g2clipMod (N : Measure ℝ) (f : ℝ → ℝ) (ρ : ℝ) : ℝ≥0∞ :=
  ⨆ (d : ℝ) (_ : |d| < ρ) (E : Set ℝ) (_ : MeasurableSet E),
    ENNReal.ofReal |N.real (f ⁻¹' E) - N.real ((fun a => f a + d) ⁻¹' E)|

theorem g2clipMod_le_one (N : Measure ℝ) [IsProbabilityMeasure N] (f : ℝ → ℝ) (ρ : ℝ) :
    g2clipMod N f ρ ≤ 1 := by
  refine iSup₂_le fun d _ => iSup₂_le fun E _ => ?_
  rw [← ENNReal.ofReal_one]
  refine ENNReal.ofReal_le_ofReal ?_
  have h1 : ∀ s : Set ℝ, N.real s ≤ 1 := fun s =>
    (measureReal_mono (subset_univ s)).trans_eq (by simp)
  have h2 : ∀ s : Set ℝ, 0 ≤ N.real s := fun s => measureReal_nonneg
  have := h1 (f ⁻¹' E); have := h1 ((fun a => f a + d) ⁻¹' E)
  have := h2 (f ⁻¹' E); have := h2 ((fun a => f a + d) ⁻¹' E)
  rw [abs_sub_le_iff]; constructor <;> linarith

theorem g2clipMod_mem (N : Measure ℝ) (f : ℝ → ℝ) {ρ d : ℝ} (hd : |d| < ρ) {E : Set ℝ}
    (hE : MeasurableSet E) :
    ENNReal.ofReal |N.real (f ⁻¹' E) - N.real ((fun a => f a + d) ⁻¹' E)| ≤ g2clipMod N f ρ :=
  le_iSup₂_of_le (f := fun (d : ℝ) (_ : |d| < ρ) => ⨆ (E : Set ℝ) (_ : MeasurableSet E),
    ENNReal.ofReal |N.real (f ⁻¹' E) - N.real ((fun a => f a + d) ⁻¹' E)|) d hd
    (le_iSup₂_of_le (f := fun (E : Set ℝ) (_ : MeasurableSet E) =>
      ENNReal.ofReal |N.real (f ⁻¹' E) - N.real ((fun a => f a + d) ⁻¹' E)|) E hE le_rfl)

/-- The modulus tends to `0` (`g2clip_tv_shift`). -/
theorem g2clipMod_tendsto {N : Measure ℝ} [IsFiniteMeasure N] (hN : N ≪ volume) {f : ℝ → ℝ}
    (hf : Differentiable ℝ f) (hpos : ∀ x, 0 < deriv f x) :
    Tendsto (fun n : ℕ => g2clipMod N f (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  by_cases htop : ε = ⊤
  · exact Eventually.of_forall fun _ => htop ▸ le_top
  have hε' : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' htop
  obtain ⟨ρ, hρ, h⟩ := g2clip_tv_shift hN hf hpos hε'
  filter_upwards [(tendsto_one_div_add_atTop_nhds_zero_nat).eventually (gt_mem_nhds hρ)]
    with n hn
  refine iSup₂_le fun d hd => iSup₂_le fun E hE => ?_
  rw [← ENNReal.ofReal_toReal htop]
  exact ENNReal.ofReal_le_ofReal (h d (hd.trans hn) E hE)

theorem g2clip_abs_toReal_sub_le {a b c : ℝ≥0∞} (ha : a ≠ ⊤) (hb : b ≠ ⊤) (hc : c ≠ ⊤)
    (h1 : a ≤ b + c) (h2 : b ≤ a + c) : |a.toReal - b.toReal| ≤ c.toReal := by
  have e1 := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hb, hc⟩) h1
  have e2 := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨ha, hc⟩) h2
  rw [ENNReal.toReal_add hb hc] at e1
  rw [ENNReal.toReal_add ha hc] at e2
  rw [abs_sub_le_iff]
  constructor <;> linarith

theorem g2clip_measure_le_add (N : Measure ℝ) [IsFiniteMeasure N] {A B : Set ℝ} {β : ℝ≥0∞}
    (h : ENNReal.ofReal |N.real A - N.real B| ≤ β) : N A ≤ N B + β := by
  rw [← ofReal_measureReal (measure_ne_top N A), ← ofReal_measureReal (measure_ne_top N B)]
  calc ENNReal.ofReal (N.real A) ≤ ENNReal.ofReal (N.real B + |N.real A - N.real B|) :=
        ENNReal.ofReal_le_ofReal (by linarith [le_abs_self (N.real A - N.real B)])
    _ ≤ ENNReal.ofReal (N.real B) + ENNReal.ofReal |N.real A - N.real B| :=
        ENNReal.ofReal_add_le
    _ ≤ _ := add_le_add le_rfl h

/-- **The frozen-coefficient shift estimate** (Sheffield, arXiv:1012.4797, proof of Prop. 5.5,
p. 66): under a product law `Q ⊗ N` of the rest `ξ` and the coefficient `α ∼ N ≪ Leb`, with the
length `L = f ξ α` smooth and strictly increasing in `α`, a shift of `L` by an `α`-independent
amount `d(ξ)`, `|d| < ρ`, changes the measure of `{(ξ, L) ∈ S}` by at most `ε`, uniformly in `S`
and `d`, for `ρ` small. -/
theorem g2clip_frozen {Ξ : Type*} [MeasurableSpace Ξ] (Q : Measure Ξ) [IsFiniteMeasure Q]
    {N : Measure ℝ} [IsProbabilityMeasure N] (hN : N ≪ volume) (f : Ξ → ℝ → ℝ)
    (hfm : Measurable (Function.uncurry f)) (hf : ∀ ξ, Differentiable ℝ (f ξ))
    (hpos : ∀ ξ a, 0 < deriv (f ξ) a) {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ > 0, ∀ S : Set (Ξ × ℝ), MeasurableSet S → ∀ d : Ξ → ℝ, Measurable d →
      (∀ ξ, |d ξ| < ρ) →
      |(Q.prod N).real {p | (p.1, f p.1 p.2) ∈ S} -
        (Q.prod N).real {p | (p.1, f p.1 p.2 + d p.1) ∈ S}| ≤ ε := by
  set β : ℕ → Ξ → ℝ≥0∞ := fun n ξ => g2clipMod N (f ξ) (1 / ((n : ℝ) + 1)) with hβ
  have hlim := g2clip_lintegral_tendsto_zero Q β (fun n ξ => g2clipMod_le_one N _ _)
    (fun ξ => g2clipMod_tendsto hN (hf ξ) (hpos ξ))
  have hεpos : (0 : ℝ≥0∞) < ENNReal.ofReal ε := ENNReal.ofReal_pos.2 hε
  obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds hεpos)).exists
  refine ⟨1 / ((n : ℝ) + 1), by positivity, fun S hS d hd hdρ => ?_⟩
  set T₁ : Set (Ξ × ℝ) := {p | (p.1, f p.1 p.2) ∈ S}
  set T₂ : Set (Ξ × ℝ) := {p | (p.1, f p.1 p.2 + d p.1) ∈ S}
  have hT₁ : MeasurableSet T₁ := (measurable_fst.prodMk hfm) hS
  have hT₂ : MeasurableSet T₂ :=
    (measurable_fst.prodMk (hfm.add (hd.comp measurable_fst))) hS
  have hg₁ : Measurable fun ξ => N (Prod.mk ξ ⁻¹' T₁) := measurable_measure_prodMk_left hT₁
  have hg₂ : Measurable fun ξ => N (Prod.mk ξ ⁻¹' T₂) := measurable_measure_prodMk_left hT₂
  have hpt : ∀ ξ, ENNReal.ofReal |N.real (Prod.mk ξ ⁻¹' T₁) - N.real (Prod.mk ξ ⁻¹' T₂)| ≤
      β n ξ := fun ξ =>
    g2clipMod_mem N (f ξ) (hdρ ξ) (E := Prod.mk ξ ⁻¹' S) (measurable_prodMk_left hS)
  have hpt' : ∀ ξ, ENNReal.ofReal |N.real (Prod.mk ξ ⁻¹' T₂) - N.real (Prod.mk ξ ⁻¹' T₁)| ≤
      β n ξ := fun ξ => by rw [abs_sub_comm]; exact hpt ξ
  have key : ∀ {A B : Set (Ξ × ℝ)}, MeasurableSet A → MeasurableSet B →
      (∀ ξ, N (Prod.mk ξ ⁻¹' A) ≤ N (Prod.mk ξ ⁻¹' B) + β n ξ) →
      (Q.prod N) A ≤ (Q.prod N) B + ENNReal.ofReal ε := by
    intro A B hA hB h
    calc (Q.prod N) A = ∫⁻ ξ, N (Prod.mk ξ ⁻¹' A) ∂Q := Measure.prod_apply hA
      _ ≤ ∫⁻ ξ, (N (Prod.mk ξ ⁻¹' B) + β n ξ) ∂Q := lintegral_mono h
      _ = ∫⁻ ξ, N (Prod.mk ξ ⁻¹' B) ∂Q + ∫⁻ ξ, β n ξ ∂Q :=
          lintegral_add_left (measurable_measure_prodMk_left hB) _
      _ ≤ (Q.prod N) B + ENNReal.ofReal ε := by
          rw [Measure.prod_apply hB]; exact add_le_add le_rfl hn.le
  have k1 := key hT₁ hT₂ (fun ξ => g2clip_measure_le_add N (hpt ξ))
  have k2 := key hT₂ hT₁ (fun ξ => g2clip_measure_le_add N (hpt' ξ))
  have := g2clip_abs_toReal_sub_le (measure_ne_top _ _) (measure_ne_top _ _)
    ENNReal.ofReal_ne_top k1 k2
  rwa [ENNReal.toReal_ofReal hε.le] at this

end Thm18Asm
end QuantumZipper
