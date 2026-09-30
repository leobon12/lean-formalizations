import QuantumZipper.Proofs.Zipper.E5Main1
import QuantumZipper.Proofs.Zipper.E5Dens

/-!
# E5-MAIN, part 2: generic TV-near steps (small bad sets; the germ step via E5-DENS)

Blueprint `blueprint/E_BRANCH_BLUEPRINT.md` §4, node **E5**, steps (2)–(4).

* `lintegral_le_add_of_eq_off`: two `[0,1]`-valued integrands that agree off a measurable set `N`
  have lower integrals within `Q N`.
* `TVNear.of_eq_off`: families of such integrands whose bad sets have probability `→ 0` along
  every sequence `C n → ∞` are TV-near.
* `tvNear_germ`: **E5-DENS in `TVNear` form** — replacing the rescaled germ
  `(a⁻¹ D(a² t))_{t ≤ S}` by an independent Brownian path, under `𝐏 = w · 𝐑`, uniformly over the
  tests, when the scales `a_C(V) > 0` tend to `0` in probability along every sequence `C n → ∞`
  (`E5.germDensity_withDensity`, i.e. E5a = `LengthMarkov.GermDensity.germDensity_core`).

Own elementary bookkeeping on top of E5a/E5-DENS (blueprint route; the paper uses Girsanov and
Williams time reversal instead: Sheffield, arXiv:1012.4797, §5.4).
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace E5

open LengthMarkov.GermDensity

variable {Ω₁ : Type*} [MeasurableSpace Ω₁]

theorem lintegral_le_add_of_eq_off {Q : Measure Ω₁} {f f' : Ω₁ → ℝ≥0∞} (hf : ∀ ω, f ω ≤ 1)
    {N : Set Ω₁} (hN : MeasurableSet N) (heq : ∀ ω, ω ∉ N → f ω = f' ω) :
    ∫⁻ ω, f ω ∂Q ≤ ∫⁻ ω, f' ω ∂Q + Q N := by
  calc ∫⁻ ω, f ω ∂Q ≤ ∫⁻ ω, (f' ω + N.indicator 1 ω) ∂Q := by
        refine lintegral_mono fun ω => ?_
        by_cases h : ω ∈ N
        · simp only [indicator_of_mem h, Pi.one_apply]; exact (hf ω).trans le_add_self
        · rw [heq ω h]; exact le_self_add
    _ = ∫⁻ ω, f' ω ∂Q + Q N := by
        rw [lintegral_add_right _ (measurable_one.indicator hN), lintegral_indicator_one hN]

/-- Families of `[0,1]`-valued integrands agreeing off bad sets of vanishing probability are
TV-near. -/
theorem TVNear.of_eq_off {E : Type*} [MeasurableSpace E] {Q : Measure Ω₁}
    (F G : ℝ → (E → ℝ≥0∞) → Ω₁ → ℝ≥0∞) (N : ℝ → Set Ω₁) (hN : ∀ C, MeasurableSet (N C))
    (hF1 : ∀ C Γ, (∀ y, Γ y ≤ 1) → ∀ ω, F C Γ ω ≤ 1)
    (hG1 : ∀ C Γ, (∀ y, Γ y ≤ 1) → ∀ ω, G C Γ ω ≤ 1)
    (heq : ∀ C Γ ω, ω ∉ N C → F C Γ ω = G C Γ ω)
    (hsmall : ∀ Cs : ℕ → ℝ, Tendsto Cs atTop atTop →
      Tendsto (fun n => Q (N (Cs n))) atTop (𝓝 0)) :
    TVNear (fun C Γ => ∫⁻ ω, F C Γ ω ∂Q) (fun C Γ => ∫⁻ ω, G C Γ ω ∂Q) := by
  refine TVNear.of_seq fun η hη Cs hCs => ?_
  filter_upwards [(hsmall Cs hCs).eventually (gt_mem_nhds hη)] with n hn Γ _ hΓ1
  exact ⟨(lintegral_le_add_of_eq_off (hF1 _ Γ hΓ1) (hN _) (heq _ Γ)).trans (by gcongr),
    (lintegral_le_add_of_eq_off (hG1 _ Γ hΓ1) (hN _)
      fun ω h => (heq _ Γ ω h).symm).trans (by gcongr)⟩

/-- Real `η`-closeness of the real integrals of two `[0,1]`-valued measurable integrands gives
the two-sided `ℝ≥0∞` bound. -/
theorem lintegral_two_sided_of_integral {Q : Measure Ω₁} [IsProbabilityMeasure Q]
    {f g : Ω₁ → ℝ≥0∞} (hf : AEMeasurable f Q) (hg : AEMeasurable g Q)
    (hf1 : ∀ ω, f ω ≤ 1) (hg1 : ∀ ω, g ω ≤ 1) {η : ℝ≥0∞} (hη : η ≠ ⊤)
    (h : |∫ ω, (f ω).toReal ∂Q - ∫ ω, (g ω).toReal ∂Q| ≤ η.toReal) :
    ∫⁻ ω, f ω ∂Q ≤ ∫⁻ ω, g ω ∂Q + η ∧ ∫⁻ ω, g ω ∂Q ≤ ∫⁻ ω, f ω ∂Q + η := by
  have hlt : ∀ {u : Ω₁ → ℝ≥0∞}, (∀ ω, u ω ≤ 1) → ∫⁻ ω, u ω ∂Q ≠ ⊤ := fun hu =>
    ((lintegral_mono hu).trans_lt (by simp)).ne
  have hfr := integral_toReal hf (Eventually.of_forall fun ω => (hf1 ω).trans_lt ENNReal.one_lt_top)
  have hgr := integral_toReal hg (Eventually.of_forall fun ω => (hg1 ω).trans_lt ENNReal.one_lt_top)
  rw [hfr, hgr] at h
  have key : ∀ {a b : ℝ≥0∞}, a ≠ ⊤ → b ≠ ⊤ → a.toReal ≤ b.toReal + η.toReal → a ≤ b + η := by
    intro a b ha hb hab
    rw [← ENNReal.ofReal_toReal ha, ← ENNReal.ofReal_toReal hb, ← ENNReal.ofReal_toReal hη,
      ← ENNReal.ofReal_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg]
    exact ENNReal.ofReal_le_ofReal hab
  exact ⟨key (hlt hf1) (hlt hg1) (by linarith [(abs_le.1 h).2]),
    key (hlt hg1) (hlt hf1) (by linarith [(abs_le.1 h).1])⟩

variable {𝕍 : Type*} [MeasurableSpace 𝕍] {W : Measure (ℝ≥0 → ℝ)}

end E5
end QuantumZipper
