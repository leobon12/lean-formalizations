/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CfGivenTransfer

/-!
# The fixed-time chart clause: null modifications of the data and of the filtration

Packet PROVE-CFCHART. Two generic moves of `CfGiven.IsChartCanon` needed to bring the clause proved on the given
space (`exists_chartCanon_omega`) to the exact form of `CfGivenChartStatement`:

* **null modifications of the data** (`IsChartCanon.congr_ae`): the processes, lifetime and chart may be changed as
  long as, at each fixed time and test function, almost surely the new event is contained in the old one and the two
  right-hand sides agree on it (same filtration, same field);
* **null-equivalent filtrations** (`IsChartCanon.of_le_aeSigma`): the filtration may be enlarged by sets that agree
  almost surely with sets of the old one (`aeSigma`), e.g. by a conull event or by a variable that is almost surely a
  function of the old filtration; the conditional expectations do not change (`condExp_ae_eq_of_le_aeSigma`).

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open LQGMetric (TestOn DistOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.CfChart

open CfGiven

/-! ### Null modifications of the data -/

section Congr

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {nL nR : ℕ} {κ : ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin nR → ℝ} {𝓐 : Filtration ℝ≥0 mΩ} {W W₂ : ℝ≥0 → Ω → ℝ} {VL VL₂ : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR VR₂ : Fin nR → ℝ≥0 → Ω → ℝ} {ζ ζ₂ : Ω → ℝ≥0∞} {c c₂ : Ω → Chart} {a k : ℝ}
  {h : Ω → DistOn upperHalfPlaneOpens}

/-- **The chart clause under null modifications of the data.** -/
theorem IsChartCanon.congr_ae (hcan : IsChartCanon κ ρL ρR P 𝓐 W VL VR ζ c a k h)
    (hev : ∀ (t : ℝ≥0) (φ : TestOn upperHalfPlaneOpens), ∀ᵐ ω ∂P, ω ∈ chartEv ζ₂ W₂ c₂ t φ →
      ω ∈ chartEv ζ W c t φ ∧ chartRhs κ W₂ c₂ a k (canonU κ ρL ρR W₂ VL₂ VR₂ t) t φ ω =
        chartRhs κ W c a k (canonU κ ρL ρR W VL VR t) t φ ω) :
    IsChartCanon κ ρL ρR P 𝓐 W₂ VL₂ VR₂ ζ₂ c₂ a k h := fun t φ => by
  filter_upwards [hcan t φ, hev t φ] with ω h1 h2 hE
  obtain ⟨hE', he⟩ := h2 hE
  rw [he]
  exact h1 hE'

end Congr

/-! ### Null-equivalent filtrations -/

section Null

variable {Ω : Type*}

/-- **The sets that agree almost surely with an `m`-measurable set.** -/
@[instance_reducible]
def aeSigma [MeasurableSpace Ω] (P : Measure Ω) (m : MeasurableSpace Ω) : MeasurableSpace Ω where
  MeasurableSet' s := ∃ s', MeasurableSet[m] s' ∧ s =ᵐ[P] s'
  measurableSet_empty := ⟨∅, @MeasurableSet.empty _ m, ae_eq_refl _⟩
  measurableSet_compl s := by
    rintro ⟨s', hs', h⟩
    exact ⟨s'ᶜ, hs'.compl, h.compl⟩
  measurableSet_iUnion f := by
    intro hf
    choose g hg h using hf
    exact ⟨⋃ i, g i, MeasurableSet.iUnion hg, EventuallyEqSet.countable_iUnion h⟩

theorem le_aeSigma (m : MeasurableSpace Ω) [MeasurableSpace Ω] (P : Measure Ω) : m ≤ aeSigma P m :=
  fun s hs => ⟨s, hs, ae_eq_refl _⟩

/-- A conull (or null) event is in `aeSigma`. -/
theorem measurableSet_aeSigma_of_ae {m : MeasurableSpace Ω} [MeasurableSpace Ω] {P : Measure Ω} {A : Set Ω}
    (hA : ∀ᵐ ω ∂P, ω ∈ A) : MeasurableSet[aeSigma P m] A :=
  ⟨univ, @MeasurableSet.univ _ m, by filter_upwards [hA] with ω hω; simp [hω]⟩

/-- A variable that is almost surely an `m`-measurable variable generates sets of `aeSigma P m`. -/
theorem comap_le_aeSigma {m : MeasurableSpace Ω} [MeasurableSpace Ω] {P : Measure Ω} {β : Type*}
    [MeasurableSpace β] {f g : Ω → β} (hg : Measurable[m] g) (hfg : ∀ᵐ ω ∂P, f ω = g ω) :
    MeasurableSpace.comap f inferInstance ≤ aeSigma P m := by
  rintro s ⟨B, hB, rfl⟩
  refine ⟨g ⁻¹' B, hg hB, ?_⟩
  filter_upwards [hfg] with ω hω
  simp only [mem_preimage, hω]

variable {m₁ m₂ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P] {E : Type*}
  [NormedAddCommGroup E]
  [NormedSpace ℝ E] [CompleteSpace E]

/-- **Conditional expectations do not see null-equivalent enlargements**: if `m₁ ≤ m₂ ≤ aeSigma P m₁`, then
`P[f | m₂] = P[f | m₁]` almost surely. -/
theorem condExp_ae_eq_of_le_aeSigma (h12 : m₁ ≤ m₂) (h2 : m₂ ≤ mΩ)
    (h2a : m₂ ≤ aeSigma P m₁) {f : Ω → E} (hf : Integrable f P) : P[f | m₂] =ᵐ[P] P[f | m₁] := by
  have h1 : m₁ ≤ mΩ := h12.trans h2
  refine (ae_eq_condExp_of_forall_setIntegral_eq h2 hf (fun s _ _ => integrable_condExp.integrableOn)
    (fun s hs _ => ?_) (stronglyMeasurable_condExp.mono h12).aestronglyMeasurable).symm
  obtain ⟨s', hs', hss'⟩ := h2a s hs
  rw [setIntegral_congr_set hss', setIntegral_condExp h1 hf hs', setIntegral_congr_set hss'.symm]

end Null

section Filt

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {nL nR : ℕ} {κ : ℝ}
  {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {c : Ω → Chart} {a k : ℝ} {h : Ω → DistOn upperHalfPlaneOpens}

/-- **The chart clause passes to a null-equivalent larger filtration.** -/
theorem IsChartCanon.of_le_aeSigma {𝓐 𝓑 : Filtration ℝ≥0 mΩ} (hcan : IsChartCanon κ ρL ρR P 𝓐 W VL VR ζ c a k h)
    (hh : Measurable h) (h𝓐𝓑 : ∀ t, 𝓐 t ≤ 𝓑 t) (h𝓑 : ∀ t, 𝓑 t ≤ aeSigma P (𝓐 t)) :
    IsChartCanon κ ρL ρR P 𝓑 W VL VR ζ c a k h := fun t φ => by
  filter_upwards [hcan t φ, condExp_ae_eq_of_le_aeSigma (h𝓐𝓑 t) (𝓑.le t) (h𝓑 t)
    (integrable_cexp_apply (P := P) hh φ)] with ω h1 h2 hE
  rw [h2]
  exact h1 hE

end Filt

/-! ### A constant shift of the field -/

section Shift

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {nL nR : ℕ} {κ : ℝ}
  {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {𝓐 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {c : Ω → Chart} {a k : ℝ} {h h₂ : Ω → DistOn upperHalfPlaneOpens}

/-- **The chart clause under a constant shift of the field**: if `(h₂, φ) = (h, φ) + c₀ ∫ φ`, the clause for `h` with
the constant `a` is the clause for `h₂` with the constant `a − c₀` (given the integrability of the chart-mean
integrand on the event). -/
theorem IsChartCanon.shift_field (c₀ : ℝ) (hcan : IsChartCanon κ ρL ρR P 𝓐 W VL VR ζ c a k h)
    (hshift : ∀ ω (φ : TestOn upperHalfPlaneOpens), h₂ ω φ = h ω φ + c₀ * ∫ z, φ z)
    (hint : ∀ (t : ℝ≥0) (φ : TestOn upperHalfPlaneOpens), ∀ᵐ ω ∂P, ω ∈ chartEv ζ W c t φ →
      Integrable fun z => (couplingMean κ (fun s : ℝ => W s.toNNReal ω) (t : ℝ) (canonU κ ρL ρR W VL VR t ω)
        ((c ω).1 z) - a - k * (c ω).2.2 z) * φ z) :
    IsChartCanon κ ρL ρR P 𝓐 W VL VR ζ c (a - c₀) k h₂ := fun t φ => by
  set e : ℂ := Complex.exp (Complex.I * ((c₀ * ∫ z, φ z : ℝ) : ℂ)) with he
  have hfun : (fun ω' => Complex.exp (Complex.I * (h₂ ω' φ : ℂ))) =
      e • fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ)) := by
    funext ω'
    rw [Pi.smul_apply, smul_eq_mul, hshift, he, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hce := condExp_smul (μ := P) e (fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ))) (𝓐 t)
  filter_upwards [hcan t φ, hce, hint t φ] with ω h1 h2 h3 hE
  rw [hfun, h2, Pi.smul_apply, smul_eq_mul, h1 hE]
  have hφi : Integrable fun z => φ z := φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
  have hsplit : (∫ z, (couplingMean κ (fun s : ℝ => W s.toNNReal ω) (t : ℝ) (canonU κ ρL ρR W VL VR t ω)
      ((c ω).1 z) - (a - c₀) - k * (c ω).2.2 z) * φ z) =
      (∫ z, (couplingMean κ (fun s : ℝ => W s.toNNReal ω) (t : ℝ) (canonU κ ρL ρR W VL VR t ω)
        ((c ω).1 z) - a - k * (c ω).2.2 z) * φ z) + c₀ * ∫ z, φ z := by
    rw [← integral_const_mul, ← integral_add (h3 hE) (hφi.const_mul c₀)]
    congr 1
    funext z
    ring
  unfold chartRhs
  rw [hsplit, he, ← Complex.exp_add]
  congr 1
  push_cast
  ring

end Shift

end InteractingSLE.Sec5.CfChart
