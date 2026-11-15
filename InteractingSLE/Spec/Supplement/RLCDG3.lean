/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.FlowLocal
import InteractingSLE.Spec.Sec7.Lemma78MeanWordMeas

/-!
# Lemma G3 from flow-line locality and Theorems 1.2–1.3

Packet PROVE-RLC-D, part (1). Source: Lemma G3 and its proof (supplement §7.3, `source/spec/p481-528.md` L290–L320,
pp. 492–493).

* `exists_isFlowLine_of_param`: on every probability space, every GFF with piecewise constant data has an angle-`θ`
  flow line from every seed — the decoded canonical flow code (`Restart.flowCode`, realization from Theorem 1.2 in its
  word-measurable form and Theorem 1.3);
* **`g3ChartComparisonStatement_of_locality`**: PROVE-RLC-A's named input `RLC.G3ChartComparisonStatement` from the
  flow-line locality input `RLC.FlowLocalityStatement` and Theorems 1.2 (param) / 1.3. The density and the shifted
  field are `RLC.exists_shift_isGFFWithBoundaryData` (proved) for the compact `closure V`; the reference flow lines
  are the canonical ones of the shifted field under the weighted law; locality gives the stopped agreement.

R43/R48: this serves Theorem 1.5 only (Lemma G3 is an input of W5), so Theorems 1.2–1.3 are used as their frozen types;
it must not be fed back into the chains of Theorems 1.2–1.3.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open LQGMetric

namespace InteractingSLE

namespace RLC

/-- **Flow lines of every GFF with piecewise constant data exist on its own space** (from Theorems 1.2 (param) and
1.3): the decoded canonical flow code of the field is the angle-`θ` flow line from `y`. -/
theorem exists_isFlowLine_of_param (h12p : Exist.Staged.Theorem12ParamStatement.{0})
    (h13 : Exist.Theorem13Statement.{0}) {κ : ℝ} (hκ : 0 < κ) {b : ℝ → ℝ} {J : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b J) (y θ : ℝ) {S : Type} [MeasurableSpace S] {Q : Measure S}
    [IsProbabilityMeasure Q] {Ĥ : S → DistOn upperHalfPlaneOpens} (hĤ : IsGFFWithBoundaryData Q Ĥ b J) :
    ∃ (α : S → ℝ≥0 → ℂ) (ζ : S → ℝ≥0∞), IsFlowLine κ b J y θ Q Ĥ α ζ := by
  obtain ⟨c, hcm, hcJ, hcb⟩ := Restart.BoundaryWord.exists_fn_eq_strictMonoOn hb
  have hcs : c.IsSorted := fun i j hij hj =>
    hcm.monotoneOn (show i < c.1 from lt_of_le_of_lt hij hj) (show j < c.1 from hj) hij
  have hgff : IsGFFWithBoundaryData Q Ĥ c.fn c.jumps :=
    (Restart.BoundaryWord.isGFFWithBoundaryData_fn_iff hcJ hcb Q Ĥ).2 hĤ
  set F := fun x => Restart.flowCode h12p hκ θ ((c, y), Ĥ x) with hF
  have hFm : Measurable F := (Restart.measurable_flowCode h12p hκ θ).comp (measurable_const.prodMk hĤ.1)
  refine ⟨fun x => Restart.decPath (F x), fun x => (F x).2, ?_⟩
  exact (Restart.BoundaryWord.isFlowLine_fn_iff hcJ hcb).1
    (Restart.isFlowLine_of_codeMatch_flowCode h12p hκ θ h13 c y hgff (measurable_snd.comp hFm)
      (ae_of_all _ fun _ => ⟨rfl, fun _ _ => rfl⟩))

/-- **Lemma G3 (`RLC.G3ChartComparisonStatement`) from flow-line locality and Theorems 1.2 (param) / 1.3.** -/
theorem g3ChartComparisonStatement_of_locality (h12p : Exist.Staged.Theorem12ParamStatement.{0})
    (h13 : Exist.Theorem13Statement.{0}) (hloc : FlowLocalityStatement.{0}) : G3ChartComparisonStatement.{0} := by
  intro κ hκ hκ4 b bR J Ĵ hb hbR O hO hbO _hJO V hV hVb hVO y₁ y₂ θ₁ θ₂ S _ Q₀ _ H₀ hH Γ₁ Γ₂ U₁ U₂ h₁ h₂
  obtain ⟨Z, T, N, hNo, hKN, hNO, hZm, hZpos, hZ1, hĤ, hT0⟩ :=
    exists_shift_isGFFWithBoundaryData hb hbR hO hbO hVb.isCompact_closure hVO Q₀ hH
  set Q := Q₀.withDensity fun x => ENNReal.ofReal (Z x) with hQ
  have hint : Integrable Z Q₀ := Integrable.of_integral_ne_zero (by rw [hZ1]; exact one_ne_zero)
  have hQprob : IsProbabilityMeasure Q := by
    constructor
    rw [hQ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hint (hZpos.mono fun x hx => hx.le), hZ1, ENNReal.ofReal_one]
  have hPQ : Q₀ ≪ Q := by
    refine withDensity_absolutelyContinuous' (ENNReal.measurable_ofReal.comp hZm).aemeasurable ?_
    filter_upwards [hZpos] with x hx
    exact (ENNReal.ofReal_pos.2 hx).ne'
  have hQP : Q ≪ Q₀ := withDensity_absolutelyContinuous _ _
  obtain ⟨α₁, ζ₁, hα₁⟩ := exists_isFlowLine_of_param h12p h13 hκ hbR y₁ θ₁ hĤ
  obtain ⟨α₂, ζ₂, hα₂⟩ := exists_isFlowLine_of_param h12p h13 hκ hbR y₂ θ₂ hĤ
  have hag : ∀ (x : S) (φ : TestOn upperHalfPlaneOpens), tsupport φ ⊆ N → (H₀ x + T) φ = H₀ x φ :=
    fun x φ hφ => by rw [add_apply, hT0 φ hφ, add_zero]
  refine ⟨Z, fun x => H₀ x + T, α₁, α₂, ζ₁, ζ₂, hZm.aemeasurable, hZpos, hZ1, hĤ, hα₁, hα₂, ?_⟩
  filter_upwards [hloc κ hκ hκ4 b bR J Ĵ hb hbR O hO hbO N hNo hNO V hV hVb hKN y₁ θ₁ Q₀ Q hPQ hQP H₀ _ hH hĤ
      hag Γ₁ α₁ U₁ ζ₁ h₁ hα₁,
    hloc κ hκ hκ4 b bR J Ĵ hb hbR O hO hbO N hNo hNO V hV hVb hKN y₂ θ₂ Q₀ Q hPQ hQP H₀ _ hH hĤ
      hag Γ₂ α₂ U₂ ζ₂ h₂ hα₂] with x hx₁ hx₂
  exact ⟨hx₁, hx₂⟩

end RLC

end InteractingSLE
