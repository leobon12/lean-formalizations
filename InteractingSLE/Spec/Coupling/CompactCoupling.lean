import InteractingSLE.Spec.Coupling.CompactLimit
import Mathlib.Probability.Kernel.Disintegration.StandardBorel

/-!
# The compactness step for couplings of a driving law with a field law

Packet PROVE-T11-ASM (Theorem 1.1, Astra §1 p. 6, "One compactness step, with no Kolmogorov extension theorem").
Let `(Ω₀, P₀)` be any probability space (it carries the driving evolution), `X` a standard Borel space (the field) with
a law `α`, and `G : Ω₀ → Y` a measurable map into a standard Borel space (countably many recorded history
coordinates). A sequence of couplings `μₙ` of `P₀` and `α` on `Ω₀ × X` has a subsequence and a limit coupling `μ` of
`P₀` and `α` such that

  `∫ g(G ω) f(x) dμ_{φ n} → ∫ g(G ω) f(x) dμ`

for **all** bounded measurable `g` on `Y` and `f` on `X` (`exists_limit_coupling`). Hence every constraint of the form
`∫_{G⁻¹A × X} f dμₙ = c(A, f)`, holding for all large `n`, holds for `μ`.

Proof: push the couplings to `Y × X`, where both marginals are fixed laws on Polish spaces; Prokhorov
(`exists_subseq_tendsto_of_marginals`) and the coupling bound (`tendsto_integral_mul_of_tendsto`) on `Y × X`; lift the
limit `π` back to `Ω₀ × X` as `P₀ ⊗ (π.condKernel ∘ G)`, whose image under `(G, id)` is `π` (disintegration).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal

namespace InteractingSLE

namespace Coupling

variable {Ω₀ Y X : Type*} [MeasurableSpace Ω₀] [MeasurableSpace Y] [MeasurableSpace X]

/-- The lifted coupling `P₀ ⊗ (κ ∘ G)` has image `(P₀.map G) ⊗ κ` under `(G, id)`. -/
theorem map_compProd_comap {P₀ : Measure Ω₀} [IsProbabilityMeasure P₀] {G : Ω₀ → Y}
    (hG : Measurable G) (κ : Kernel Y X) [IsMarkovKernel κ] :
    (P₀ ⊗ₘ κ.comap G hG).map (fun p : Ω₀ × X => (G p.1, p.2)) = (P₀.map G) ⊗ₘ κ := by
  have hΨ : Measurable fun p : Ω₀ × X => (G p.1, p.2) := (hG.comp measurable_fst).prodMk measurable_snd
  ext S hS
  rw [Measure.map_apply hΨ hS, Measure.compProd_apply (hΨ hS), Measure.compProd_apply hS,
    lintegral_map (Kernel.measurable_kernel_prodMk_left hS) hG]
  rfl

variable [StandardBorelSpace Y] [StandardBorelSpace X] [Nonempty X]

/-- **The compactness step.** Every sequence of couplings of `P₀` and `α` on `Ω₀ × X` has a subsequence and a limit
coupling of `P₀` and `α` against which `∫ g(G ω) f(x)` converges, for all bounded measurable `g`, `f`. -/
theorem exists_limit_coupling {P₀ : Measure Ω₀} [IsProbabilityMeasure P₀] {α : Measure X}
    [IsProbabilityMeasure α] {G : Ω₀ → Y} (hG : Measurable G) (μ : ℕ → Measure (Ω₀ × X))
    [hμ : ∀ n, IsProbabilityMeasure (μ n)] (hfst : ∀ n, (μ n).map Prod.fst = P₀)
    (hsnd : ∀ n, (μ n).map Prod.snd = α) :
    ∃ (μ' : Measure (Ω₀ × X)) (φ : ℕ → ℕ), IsProbabilityMeasure μ' ∧ μ'.map Prod.fst = P₀ ∧
      μ'.map Prod.snd = α ∧ StrictMono φ ∧
      ∀ (g : Y → ℂ) (f : X → ℂ), Measurable g → Measurable f → (∃ Cg, ∀ y, ‖g y‖ ≤ Cg) →
        (∃ Cf, ∀ x, ‖f x‖ ≤ Cf) →
        Tendsto (fun n => ∫ p, g (G p.1) * f p.2 ∂(μ (φ n))) atTop
          (𝓝 (∫ p, g (G p.1) * f p.2 ∂μ')) := by
  let _ := upgradeStandardBorel Y
  let _ := upgradeStandardBorel X
  set Ψ : Ω₀ × X → Y × X := fun p => (G p.1, p.2) with hΨdef
  have hΨ : Measurable Ψ := (hG.comp measurable_fst).prodMk measurable_snd
  set β : Measure Y := P₀.map G with hβdef
  have hβp : IsProbabilityMeasure β := inferInstance
  set πs : ℕ → ProbabilityMeasure (Y × X) := fun n =>
    ⟨(μ n).map Ψ, inferInstance⟩ with hπs
  have hβs : ∀ n, (πs n : Measure (Y × X)).map Prod.fst = β := fun n => by
    simp only [hπs, ProbabilityMeasure.coe_mk]
    rw [Measure.map_map measurable_fst hΨ, hβdef, ← hfst n, Measure.map_map hG measurable_fst]
    rfl
  have hαs : ∀ n, (πs n : Measure (Y × X)).map Prod.snd = α := fun n => by
    simp only [hπs, ProbabilityMeasure.coe_mk]
    rw [Measure.map_map measurable_snd hΨ, ← hsnd n]
    rfl
  obtain ⟨π, φ, hφ, hlim, hπβ, hπα⟩ := exists_subseq_tendsto_of_marginals πs hβs hαs
  set κ : Kernel Y X := (π : Measure (Y × X)).condKernel with hκ
  set μ' : Measure (Ω₀ × X) := P₀ ⊗ₘ κ.comap G hG with hμ'
  have hμ'Ψ : μ'.map Ψ = (π : Measure (Y × X)) := by
    rw [hμ', map_compProd_comap hG κ, ← hβdef, ← hπβ]
    exact (π : Measure (Y × X)).disintegrate (π : Measure (Y × X)).condKernel
  have hμ'p : IsProbabilityMeasure μ' := by rw [hμ']; infer_instance
  refine ⟨μ', φ, hμ'p, ?_, ?_, hφ, ?_⟩
  · exact Measure.fst_compProd P₀ (κ.comap G hG)
  · have : μ'.map Prod.snd = (μ'.map Ψ).map Prod.snd := by
      rw [Measure.map_map measurable_snd hΨ]; rfl
    rw [this, hμ'Ψ, hπα]
  · rintro g f hg hf ⟨Cg, hgb⟩ ⟨Cf, hfb⟩
    have hF : ∀ ν : Measure (Ω₀ × X), ∫ p, g (G p.1) * f p.2 ∂ν =
        ∫ q, g q.1 * f q.2 ∂(ν.map Ψ) := fun ν => by
      have hm : AEStronglyMeasurable (fun q : Y × X => g q.1 * f q.2) (ν.map Ψ) :=
        ((hg.comp measurable_fst).mul (hf.comp measurable_snd)).aestronglyMeasurable
      exact (integral_map hΨ.aemeasurable hm).symm
    have key := tendsto_integral_mul_of_tendsto hlim (fun n => hβs (φ n)) (fun n => hαs (φ n))
      hπβ hπα hg hf hgb hfb
    simp only [hF, hμ'Ψ]
    exact key

end Coupling

end InteractingSLE
