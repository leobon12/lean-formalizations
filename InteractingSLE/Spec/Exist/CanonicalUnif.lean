/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Exist.CanonicalLaw

/-!
# A uniform variable built from the field, independent of the history on `{ζ < ∞}`

Packet PROVE-FLOWEXIST3 (AUD-3c N1). Let `Ψ` be the Borel history code of the frozen coupling (`Ψ(h₀)` almost surely
in `DetSet` and the frozen code of the killed history), and `μ` the law of the field. With `n(x) = ⌈cζ x⌉`, the
conditional law `κₙ(x)` of `(h, φₙ)` given `Ψ = x` has no atoms for almost every `x` with `cζ x ≤ n`
(`Exist.ae_noAtom_condDistrib`, `Exist.ae_noAtom_condDistrib_zero`), so the conditional probability integral transform

`U(f) = F_{κ_{n(Ψ f)}(Ψ f)}((f, φ_{n(Ψ f)}))`

is uniform on `[0, 1]` and independent of `Ψ` on `{cζ(Ψ) < ∞}` (**`exists_uniform_field`**): for every Borel set `A` of
codes and `0 ≤ u ≤ 1`, `μ{Ψ ∈ A, cζ(Ψ) < ∞, U ≤ u} = μ{Ψ ∈ A, cζ(Ψ) < ∞} · u`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Exist

open LQGMetric Sec2.Assembly

variable {nL nR : ℕ}

/-- The level `⌈cζ x⌉` of a code. -/
def capN (x : XCode nL nR) : ℕ := ⌈(cζ x).toReal⌉₊

theorem measurable_capN : Measurable (capN : XCode nL nR → ℕ) :=
  Nat.measurable_ceil.comp (ENNReal.measurable_toReal.comp measurable_cζ)

theorem le_capN {x : XCode nL nR} (hx : cζ x ≠ ⊤) : cζ x ≤ capN x := by
  rw [← ENNReal.ofReal_toReal hx, capN, ← ENNReal.ofReal_natCast]
  exact ENNReal.ofReal_le_ofReal (Nat.le_ceil _)

theorem measurable_eval_dist (φ : TestOn upperHalfPlaneOpens) :
    Measurable fun f : DistOn upperHalfPlaneOpens => f φ :=
  measurable_eval_field (h := id) measurable_id φ

universe u

variable {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}

/-- **A uniform variable from the field, independent of the history on `{ζ < ∞}`.** -/
theorem exists_uniform_field (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h) (hκ : 0 < κ)
    {B' : ℝ≥0 → Ω → ℝ} {Ψ : DistOn upperHalfPlaneOpens → XCode nL nR} (hΨm : Measurable Ψ)
    (hX₀ : ∀ᵐ ω ∂P, Ψ (h ω) ∈ DetSet κ xL xR ρL ρR ∧ Ψ (h ω) = frz (codeOf xL xR B' W VL VR ζ ω)) :
    ∃ U : DistOn upperHalfPlaneOpens → ℝ, Measurable U ∧ (∀ f, 0 ≤ U f ∧ U f ≤ 1) ∧
      ∀ A : Set (XCode nL nR), MeasurableSet A → ∀ u : ℝ, 0 ≤ u → u ≤ 1 →
        (P.map h) {f | Ψ f ∈ A ∧ cζ (Ψ f) < ⊤ ∧ U f ≤ u} =
          (P.map h) {f | Ψ f ∈ A ∧ cζ (Ψ f) < ⊤} * ENNReal.ofReal u := by
  have hhm : Measurable h := hC.2.1
  set X₀ : Ω → XCode nL nR := fun ω => Ψ (h ω) with hX₀def
  have hX₀m : Measurable X₀ := hΨm.comp hhm
  set κn : ℕ → Kernel (XCode nL nR) ℝ := fun n => condDistrib (fun ω => h ω (highBump n)) X₀ P with hκn
  have hna : ∀ n : ℕ, ∀ᵐ x ∂(P.map X₀), cζ x ≤ n → ∀ a, κn n x {a} = 0 := by
    intro n
    by_cases hseed : ForceWord.ThresholdCondition ρL ρR 0 xL xR
    · filter_upwards [ae_noAtom_condDistrib_zero hC hseed hX₀m (hX₀.mono fun ω hω => hω.2) n] with x hx _
      exact hx
    · exact ae_noAtom_condDistrib hC hκ hseed hX₀m hX₀ n
  set F : DistOn upperHalfPlaneOpens × ℕ → ℝ := fun p => cdf (κn p.2 (Ψ p.1)) (p.1 (highBump p.2)) with hF
  have hFm : Measurable F := by
    refine measurable_from_prod_countable_left fun n => ?_
    exact (measurable_cdf_kernel (κn n)).comp (hΨm.prodMk (measurable_eval_dist (highBump n)))
  set U : DistOn upperHalfPlaneOpens → ℝ := fun f => F (f, capN (Ψ f)) with hU
  have hUm : Measurable U := hFm.comp (measurable_id.prodMk (measurable_capN.comp hΨm))
  refine ⟨U, hUm, fun f => ⟨cdf_nonneg _ _, cdf_le_one _ _⟩, fun A hA u hu0 hu1 => ?_⟩
  set E : ℕ → Set (XCode nL nR) := fun n => A ∩ {x | cζ x < ⊤ ∧ capN x = n} with hE
  have hEm : ∀ n, MeasurableSet (E n) := fun n =>
    hA.inter ((measurableSet_lt measurable_cζ measurable_const).inter
      (measurable_capN (measurableSet_singleton n)))
  -- decompositions over the level
  have hd1 : {f | Ψ f ∈ A ∧ cζ (Ψ f) < ⊤ ∧ U f ≤ u} =
      ⋃ n, {f | Ψ f ∈ E n ∧ cdf (κn n (Ψ f)) (f (highBump n)) ≤ u} := by
    ext f
    simp only [mem_ofPred_eq, mem_iUnion, hE, mem_inter_iff, hU, hF]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨capN (Ψ f), ⟨h1, h2, rfl⟩, h3⟩
    · rintro ⟨n, ⟨h1, h2, rfl⟩, h3⟩
      exact ⟨h1, h2, h3⟩
  have hd2 : {f | Ψ f ∈ A ∧ cζ (Ψ f) < ⊤} = ⋃ n, Ψ ⁻¹' E n := by
    ext f
    simp only [mem_ofPred_eq, mem_iUnion, hE, mem_inter_iff, mem_preimage]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨capN (Ψ f), h1, h2, rfl⟩
    · rintro ⟨n, h1, h2, -⟩
      exact ⟨h1, h2⟩
  have hdisj : Pairwise (Function.onFun Disjoint fun n => Ψ ⁻¹' E n) := by
    intro m n hmn
    refine Set.disjoint_left.2 fun f hm hn => hmn ?_
    exact hm.2.2.symm.trans hn.2.2
  have hdisj1 : Pairwise (Function.onFun Disjoint
      fun n => {f | Ψ f ∈ E n ∧ cdf (κn n (Ψ f)) (f (highBump n)) ≤ u}) := by
    intro m n hmn
    refine Set.disjoint_left.2 fun f hm hn => hmn ?_
    exact hm.1.2.2.symm.trans hn.1.2.2
  have hm1 : ∀ n, MeasurableSet {f | Ψ f ∈ E n ∧ cdf (κn n (Ψ f)) (f (highBump n)) ≤ u} := fun n =>
    (hΨm (hEm n)).inter (measurableSet_le ((measurable_cdf_kernel (κn n)).comp
      (hΨm.prodMk (measurable_eval_dist _))) measurable_const)
  rw [hd1, hd2, measure_iUnion hdisj1 hm1, measure_iUnion hdisj fun n => hΨm (hEm n),
    ← ENNReal.tsum_mul_right]
  refine tsum_congr fun n => ?_
  -- one level
  have hjoint : (P.map h).map (fun f => (Ψ f, f (highBump n))) = P.map X₀ ⊗ₘ κn n := by
    rw [Measure.map_map (hΨm.prodMk (measurable_eval_dist _)) hhm,
      compProd_map_condDistrib hX₀m.aemeasurable (measurable_eval_field hhm _).aemeasurable]
    rfl
  have hset : MeasurableSet {p : XCode nL nR × ℝ | p.1 ∈ E n ∧ cdf (κn n p.1) p.2 ≤ u} :=
    (measurable_fst (hEm n)).inter (measurableSet_le (measurable_cdf_kernel (κn n)) measurable_const)
  have e1 : (P.map h) {f | Ψ f ∈ E n ∧ cdf (κn n (Ψ f)) (f (highBump n)) ≤ u} =
      (P.map X₀ ⊗ₘ κn n) {p | p.1 ∈ E n ∧ cdf (κn n p.1) p.2 ≤ u} := by
    rw [← hjoint, Measure.map_apply (hΨm.prodMk (measurable_eval_dist _)) hset]
    rfl
  have hnaE : ∀ᵐ x ∂(P.map X₀), x ∈ E n → ∀ a, κn n x {a} = 0 := by
    filter_upwards [hna n] with x hx hxE
    refine hx ?_
    have := le_capN (ne_of_lt hxE.2.1)
    rwa [hxE.2.2] at this
  rw [e1, compProd_cdf_le (P.map X₀) (κn n) (hEm n) hnaE hu0 hu1,
    Measure.map_apply hX₀m (hEm n), Measure.map_apply hhm (hΨm (hEm n))]
  rfl

end Exist

end InteractingSLE
