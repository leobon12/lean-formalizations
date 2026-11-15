import InteractingSLE.Foundations.Measure.Tightness
import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-!
# Weak limits of couplings with fixed marginals

Packet PROVE-T11-ASM (Theorem 1.1, the compactness step of Astra §1, p. 6: "The resulting laws are couplings of two
fixed probability measures ... These marginal laws are tight, so the couplings are uniformly tight. Prokhorov gives a
weakly convergent subsequence. Each prescribed restricted-field/history joint law passes to the limit").

For couplings `π` of two fixed laws `β` on `Y` and `α` on `X` (Polish spaces), the pairing
`∫ g(y) f(x) dπ` with **bounded measurable** (not necessarily continuous) `g`, `f` is controlled by the marginal
`L¹` distances to bounded continuous approximants (`norm_integral_mul_sub_le`), uniformly in the coupling. Hence:

* `tendsto_integral_mul_of_tendsto`: if couplings of `β` and `α` converge weakly, then `∫ g(y) f(x) dπₙ` converges for
  all bounded measurable `g`, `f` (bounded continuous functions are dense in `L¹` of a finite Borel measure on a
  metric space);
* `exists_subseq_tendsto_of_marginals`: every sequence of couplings of `β` and `α` has a weakly convergent subsequence
  (Prokhorov), and the limit is again a coupling of `β` and `α`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped ENNReal NNReal BoundedContinuousFunction

namespace InteractingSLE

namespace Coupling

variable {Y X : Type*} [MeasurableSpace Y] [MeasurableSpace X]

theorem integrable_of_bound' {Z E : Type*} [MeasurableSpace Z] [NormedAddCommGroup E] {μ : Measure Z}
    [IsFiniteMeasure μ] {F : Z → E} (hF : AEStronglyMeasurable F μ) {C : ℝ} (hC : ∀ z, ‖F z‖ ≤ C) : Integrable F μ :=
  Integrable.of_bound hF C (ae_of_all _ hC)

/-- **The coupling bound.** For a finite measure `π` on `Y × X` with marginals `β`, `α`, bounded measurable `g`,
`f` and bounded measurable `g'`, `f'` (`‖g‖ ≤ Cg`, `‖f'‖ ≤ Cf'`):
`‖∫ g f dπ − ∫ g' f' dπ‖ ≤ Cf' ∫ ‖g − g'‖ dβ + Cg ∫ ‖f − f'‖ dα`. -/
theorem norm_integral_mul_sub_le {π : Measure (Y × X)} [IsFiniteMeasure π] {β : Measure Y}
    {α : Measure X} (hβ : π.map Prod.fst = β) (hα : π.map Prod.snd = α) {g g' : Y → ℂ}
    {f f' : X → ℂ} (hg : Measurable g) (hg' : Measurable g') (hf : Measurable f)
    (hf' : Measurable f') {Cg Cg' Cf Cf' : ℝ} (hgb : ∀ y, ‖g y‖ ≤ Cg) (hg'b : ∀ y, ‖g' y‖ ≤ Cg')
    (hfb : ∀ x, ‖f x‖ ≤ Cf) (hf'b : ∀ x, ‖f' x‖ ≤ Cf') :
    ‖∫ p, g p.1 * f p.2 ∂π - ∫ p, g' p.1 * f' p.2 ∂π‖ ≤
      Cf' * ∫ y, ‖g y - g' y‖ ∂β + Cg * ∫ x, ‖f x - f' x‖ ∂α := by
  have hβf : IsFiniteMeasure β := hβ ▸ inferInstance
  have hαf : IsFiniteMeasure α := hα ▸ inferInstance
  have hA : Integrable (fun p : Y × X => g p.1 * f p.2) π :=
    integrable_of_bound' ((hg.comp measurable_fst).mul (hf.comp measurable_snd)).aestronglyMeasurable
      (C := Cg * Cf) fun p => by
        rw [norm_mul]
        exact mul_le_mul (hgb _) (hfb _) (norm_nonneg _) ((norm_nonneg _).trans (hgb p.1))
  have hB : Integrable (fun p : Y × X => g' p.1 * f' p.2) π :=
    integrable_of_bound' ((hg'.comp measurable_fst).mul (hf'.comp measurable_snd)).aestronglyMeasurable
      (C := Cg' * Cf') fun p => by
        rw [norm_mul]
        exact mul_le_mul (hg'b _) (hf'b _) (norm_nonneg _) ((norm_nonneg _).trans (hg'b p.1))
  have hpt : ∀ p : Y × X, ‖g p.1 * f p.2 - g' p.1 * f' p.2‖ ≤
      Cf' * ‖g p.1 - g' p.1‖ + Cg * ‖f p.2 - f' p.2‖ := fun p => by
    have e : g p.1 * f p.2 - g' p.1 * f' p.2 =
        (g p.1 - g' p.1) * f' p.2 + g p.1 * (f p.2 - f' p.2) := by ring
    rw [e]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (hf'b _) (norm_nonneg _)
    · rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hgb _) (norm_nonneg _)
  have h1 : Integrable (fun p : Y × X => ‖g p.1 - g' p.1‖) π :=
    integrable_of_bound' (C := Cg + Cg') ((hg.sub hg').norm.comp measurable_fst).aestronglyMeasurable
      fun p => by
        rw [norm_norm]
        exact (norm_sub_le _ _).trans (add_le_add (hgb _) (hg'b _))
  have h2 : Integrable (fun p : Y × X => ‖f p.2 - f' p.2‖) π :=
    integrable_of_bound' (C := Cf + Cf') ((hf.sub hf').norm.comp measurable_snd).aestronglyMeasurable
      fun p => by
        rw [norm_norm]
        exact (norm_sub_le _ _).trans (add_le_add (hfb _) (hf'b _))
  have e1 : ∫ p, ‖g p.1 - g' p.1‖ ∂π = ∫ y, ‖g y - g' y‖ ∂β := by
    rw [← hβ]
    exact (integral_map measurable_fst.aemeasurable
      ((hg.sub hg').norm.aestronglyMeasurable)).symm
  have e2 : ∫ p, ‖f p.2 - f' p.2‖ ∂π = ∫ x, ‖f x - f' x‖ ∂α := by
    rw [← hα]
    exact (integral_map measurable_snd.aemeasurable
      ((hf.sub hf').norm.aestronglyMeasurable)).symm
  have hsub : ∫ p, g p.1 * f p.2 ∂π - ∫ p, g' p.1 * f' p.2 ∂π =
      ∫ p, (g p.1 * f p.2 - g' p.1 * f' p.2) ∂π := (integral_sub hA hB).symm
  rw [hsub]
  refine (norm_integral_le_integral_norm _).trans ?_
  refine (integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _)
    ((h1.const_mul Cf').add (h2.const_mul Cg)) (ae_of_all _ hpt)).trans_eq ?_
  simp only [Pi.add_apply]
  rw [integral_add (h1.const_mul Cf') (h2.const_mul Cg), integral_const_mul, integral_const_mul,
    e1, e2]

section Polish

variable [TopologicalSpace Y] [PolishSpace Y] [BorelSpace Y] [TopologicalSpace X] [PolishSpace X]
  [BorelSpace X]

/-- **Weak limits of couplings with fixed marginals, tested against bounded measurable products.** If couplings
`πₙ` of `β` and `α` converge weakly to a coupling `π` of `β` and `α`, then `∫ g(y) f(x) dπₙ → ∫ g(y) f(x) dπ` for all
bounded measurable `g`, `f`. -/
theorem tendsto_integral_mul_of_tendsto {β : Measure Y} {α : Measure X} [IsProbabilityMeasure β]
    [IsProbabilityMeasure α] {πs : ℕ → ProbabilityMeasure (Y × X)} {π : ProbabilityMeasure (Y × X)}
    (hlim : Tendsto πs atTop (𝓝 π)) (hβs : ∀ n, (πs n : Measure (Y × X)).map Prod.fst = β)
    (hαs : ∀ n, (πs n : Measure (Y × X)).map Prod.snd = α)
    (hβ : (π : Measure (Y × X)).map Prod.fst = β) (hα : (π : Measure (Y × X)).map Prod.snd = α)
    {g : Y → ℂ} {f : X → ℂ} (hg : Measurable g) (hf : Measurable f) {Cg Cf : ℝ}
    (hgb : ∀ y, ‖g y‖ ≤ Cg) (hfb : ∀ x, ‖f x‖ ≤ Cf) :
    Tendsto (fun n => ∫ p, g p.1 * f p.2 ∂(πs n : Measure (Y × X))) atTop
      (𝓝 (∫ p, g p.1 * f p.2 ∂(π : Measure (Y × X)))) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hfi : Integrable f α := integrable_of_bound' hf.aestronglyMeasurable hfb
  have hgi : Integrable g β := integrable_of_bound' hg.aestronglyMeasurable hgb
  have hCg : 0 < |Cg| + 1 := by positivity
  obtain ⟨f', hf'1, -⟩ := hfi.exists_boundedContinuous_integral_sub_le
    (ε := ε / (8 * (|Cg| + 1))) (by positivity)
  have hCf' : 0 < ‖f'‖ + 1 := by positivity
  obtain ⟨g', hg'1, -⟩ := hgi.exists_boundedContinuous_integral_sub_le
    (ε := ε / (8 * (‖f'‖ + 1))) (by positivity)
  set F : Y × X →ᵇ ℂ := g'.compContinuous ⟨Prod.fst, continuous_fst⟩ *
    f'.compContinuous ⟨Prod.snd, continuous_snd⟩ with hF
  have hFapp : ∀ p : Y × X, F p = g' p.1 * f' p.2 := fun p => rfl
  have hw := (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).1 hlim F
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hw (ε / 4) (by positivity)
  -- the approximation error for any coupling of `β` and `α`
  have hbound : ∀ ρ : Measure (Y × X), IsFiniteMeasure ρ → ρ.map Prod.fst = β →
      ρ.map Prod.snd = α →
      ‖∫ p, g p.1 * f p.2 ∂ρ - ∫ p, F p ∂ρ‖ ≤ ε / 4 := fun ρ _ h1 h2 => by
    simp only [hFapp]
    have := norm_integral_mul_sub_le h1 h2 hg g'.continuous.measurable hf f'.continuous.measurable
      hgb (fun y => g'.norm_coe_le_norm y) hfb (fun x => f'.norm_coe_le_norm x)
    refine this.trans ?_
    have e1 : ‖f'‖ * ∫ y, ‖g y - g' y‖ ∂β ≤ ε / 8 := by
      calc ‖f'‖ * ∫ y, ‖g y - g' y‖ ∂β ≤ (‖f'‖ + 1) * (ε / (8 * (‖f'‖ + 1))) :=
            mul_le_mul (by linarith) hg'1 (integral_nonneg fun _ => norm_nonneg _) hCf'.le
        _ = ε / 8 := by field_simp
    have e2 : Cg * ∫ x, ‖f x - f' x‖ ∂α ≤ ε / 8 := by
      calc Cg * ∫ x, ‖f x - f' x‖ ∂α ≤ (|Cg| + 1) * (ε / (8 * (|Cg| + 1))) :=
            mul_le_mul (by linarith [le_abs_self Cg]) hf'1 (integral_nonneg fun _ => norm_nonneg _)
              hCg.le
        _ = ε / 8 := by field_simp
    linarith
  refine ⟨N, fun n hn => ?_⟩
  have h1 := hbound (πs n) inferInstance (hβs n) (hαs n)
  have h2 := hbound π inferInstance hβ hα
  have h3 := hN n hn
  rw [dist_eq_norm] at h3 ⊢
  have t1 := norm_sub_le_norm_sub_add_norm_sub (∫ p, g p.1 * f p.2 ∂(πs n : Measure (Y × X)))
    (∫ p, F p ∂(πs n : Measure (Y × X))) (∫ p, g p.1 * f p.2 ∂(π : Measure (Y × X)))
  have t2 := norm_sub_le_norm_sub_add_norm_sub (∫ p, F p ∂(πs n : Measure (Y × X)))
    (∫ p, F p ∂(π : Measure (Y × X))) (∫ p, g p.1 * f p.2 ∂(π : Measure (Y × X)))
  rw [norm_sub_rev (∫ p, F p ∂(π : Measure (Y × X)))] at t2
  linarith

/-- **Prokhorov for couplings with fixed marginals.** A sequence of couplings of `β` and `α` has a weakly convergent
subsequence, whose limit is a coupling of `β` and `α`. -/
theorem exists_subseq_tendsto_of_marginals {β : Measure Y} {α : Measure X} [IsProbabilityMeasure β]
    [IsProbabilityMeasure α] (πs : ℕ → ProbabilityMeasure (Y × X))
    (hβs : ∀ n, (πs n : Measure (Y × X)).map Prod.fst = β)
    (hαs : ∀ n, (πs n : Measure (Y × X)).map Prod.snd = α) :
    ∃ (π : ProbabilityMeasure (Y × X)) (φ : ℕ → ℕ), StrictMono φ ∧
      Tendsto (πs ∘ φ) atTop (𝓝 π) ∧ (π : Measure (Y × X)).map Prod.fst = β ∧
      (π : Measure (Y × X)).map Prod.snd = α := by
  have ht : IsTightMeasureSet (range fun n => (πs n : Measure (Y × X))) := by
    refine IsTightMeasureSet.prodMk ((isTightMeasureSet_singleton (μ := β)).subset ?_)
      ((isTightMeasureSet_singleton (μ := α)).subset ?_)
    · rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩; exact hβs n
    · rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩; exact hαs n
  obtain ⟨π, φ, hφ, hlim⟩ := Prokhorov.exists_subseq_tendsto_of_isTightMeasureSet πs ht
  refine ⟨π, φ, hφ, hlim, ?_, ?_⟩
  · have hc := ((ProbabilityMeasure.continuous_map continuous_fst).tendsto π).comp hlim
    have hconst : ∀ n, ((πs ∘ φ) n).map Prod.fst = ⟨β, inferInstance⟩ := fun n => by
      apply Subtype.ext; exact hβs (φ n)
    have := tendsto_nhds_unique hc (tendsto_const_nhds.congr fun n => (hconst n).symm)
    exact congrArg (fun ν : ProbabilityMeasure Y => (ν : Measure Y)) this
  · have hc := ((ProbabilityMeasure.continuous_map continuous_snd).tendsto π).comp hlim
    have hconst : ∀ n, ((πs ∘ φ) n).map Prod.snd = ⟨α, inferInstance⟩ := fun n => by
      apply Subtype.ext; exact hαs (φ n)
    have := tendsto_nhds_unique hc (tendsto_const_nhds.congr fun n => (hconst n).symm)
    exact congrArg (fun ν : ProbabilityMeasure X => (ν : Measure X)) this

end Polish

end Coupling

end InteractingSLE
