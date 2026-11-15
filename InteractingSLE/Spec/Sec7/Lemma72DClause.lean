/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma72DUnit
import InteractingSLE.Spec.Sec7.Lemma71DChart

/-!
# Lemma 7.1's chart clause conditionally on the exterior record, at fixed times

Packet PROVE-LEMMA72D (the conditional clause of `Lemma72C.PocketCondStatement`). Let the chart coupling clause hold
at fixed times for a raw filtration `𝓐` (`Lemma71D.IsChartCouplingCharFunConst`, PROVE-LEMMA71K's input), and let
`𝒬` be the σ-algebra of the exterior record. Suppose that at every time `t` there is a σ-algebra `𝒢_t ⊇ 𝓐_t ∨ 𝒬`
given which, on the event `{t < ζ, supp φ ⊆ ψ⁻¹(ℍ ∖ K_t)}`, the field paired with `φ` is Gaussian with the zero-boundary
variance of `ψ⁻¹(ℍ ∖ K_t)` (the germ law of the marked union `B_t`, history-marked locality) — only the **modulus**
`exp(−½ G(φ, φ))` of its conditional characteristic function is used. Then the clause holds at fixed times for the
filtration `𝓐_t ∨ 𝒬` under `P[· | G]` for every `G ∈ 𝒬` of positive probability:

* `supConst 𝓐 𝒬`: the filtration `t ↦ 𝓐_t ∨ 𝒬`;
* `norm_condExp_cexp_of_isCondZeroBoundaryGFF`: the modulus of the conditional characteristic function of a field
  `h = Z + R` with `Z` a conditional zero-boundary GFF on `O` and `R` measurable for the conditioning σ-algebra;
* **`isChartCouplingCharFunConst_cond`**: the conditional clause (`Lemma72D.ae_condExp_eq_on_of_norm_eq`: equal moduli
  force `E[X | 𝒢_t] = E[X | 𝓐_t]` on the clause events, which are covered by countably many events of `𝓐_t`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

open QuantumZipper (H fwdHull zeroGFFTestCov)
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.Sec7.Lemma72D

/-! ### The joined filtration -/

/-- The filtration `t ↦ 𝓐_t ∨ 𝒬`. -/
def supConst {Ω : Type*} {mΩ : MeasurableSpace Ω} (𝓐 : Filtration ℝ≥0 mΩ) (𝒬 : MeasurableSpace Ω)
    (h𝒬 : 𝒬 ≤ mΩ) : Filtration ℝ≥0 mΩ where
  seq t := 𝓐 t ⊔ 𝒬
  mono' _ _ hst := sup_le_sup_right (𝓐.mono hst) _
  le' t := sup_le (𝓐.le t) h𝒬

theorem supConst_apply {Ω : Type*} {mΩ : MeasurableSpace Ω} (𝓐 : Filtration ℝ≥0 mΩ) (𝒬 : MeasurableSpace Ω)
    (h𝒬 : 𝒬 ≤ mΩ) (t : ℝ≥0) : supConst 𝓐 𝒬 h𝒬 t = 𝓐 t ⊔ 𝒬 := rfl

theorem le_supConst {Ω : Type*} {mΩ : MeasurableSpace Ω} (𝓐 : Filtration ℝ≥0 mΩ) (𝒬 : MeasurableSpace Ω)
    (h𝒬 : 𝒬 ≤ mΩ) : 𝓐 ≤ supConst 𝓐 𝒬 h𝒬 := fun _ => le_sup_left

/-! ### The modulus of a conditional Gaussian law -/

section Modulus

variable {Ω : Type*} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **The modulus of the conditional characteristic function.** If `h = Z + R` with `Z` a conditional zero-boundary
GFF on `O` given `𝒢` and `R(φ)` `𝒢`-measurable, then `|E[e^{i h(φ)} | 𝒢]| = exp(−½ G_O(φ, φ))` almost surely. -/
theorem norm_condExp_cexp_of_isCondZeroBoundaryGFF (h𝒢 : 𝒢 ≤ mΩ) {h Z : Ω → DistOn upperHalfPlaneOpens}
    {O : Ω → Set ℂ} (hZm : Measurable Z) (hZ : IsCondZeroBoundaryGFF P 𝒢 O Z) {R : Ω → ℝ}
    (φ : TestOn upperHalfPlaneOpens) (hR : Measurable[𝒢] R) (hhZR : ∀ ω, h ω φ = Z ω φ + R ω) :
    ∀ᵐ ω ∂P, ‖P[fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ)) | 𝒢] ω‖ =
      Real.exp (-(1 / 2) * zeroGFFTestCov (O ω) φ φ) := by
  set U : Ω → ℂ := fun ω => Complex.exp (Complex.I * (R ω : ℂ)) with hUdef
  have hUm : StronglyMeasurable[𝒢] U := (measurable_cexp_I_mul hR).stronglyMeasurable
  have hZφ : Integrable (fun ω => Complex.exp (Complex.I * (Z ω φ : ℂ))) P :=
    GFF.integrable_exp_I_mul ((LQGMetric.measurable_distOn_apply φ).comp hZm)
  have hUi : Integrable (fun ω => U ω * Complex.exp (Complex.I * (Z ω φ : ℂ))) P :=
    hZφ.bdd_mul (hUm.mono h𝒢).aestronglyMeasurable (Eventually.of_forall fun ω => by
      simp only [hUdef]; rw [mul_comm]; exact (Complex.norm_exp_ofReal_mul_I _).le)
  have e : (fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ))) =
      fun ω' => U ω' * Complex.exp (Complex.I * (Z ω' φ : ℂ)) := by
    funext ω'
    rw [hhZR, hUdef]
    simp only
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hpull := condExp_bilin_of_stronglyMeasurable_left (ContinuousLinearMap.mul ℝ ℂ) hUm
    (by simpa [ContinuousLinearMap.mul_apply'] using hUi) hZφ
  simp only [ContinuousLinearMap.mul_apply'] at hpull
  rw [e]
  filter_upwards [hpull, hZ φ] with ω h1 h2
  rw [h1, h2, norm_mul, hUdef]
  simp only
  rw [mul_comm Complex.I, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]

end Modulus

/-! ### The conditional clause at fixed times -/

section Clause

variable {nL nR : ℕ} {κ : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {Ω : Type*} {𝒬 : MeasurableSpace Ω}
  [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {𝓐 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {c : Ω → Chart} {a k : ℝ}
  {h : Ω → DistOn upperHalfPlaneOpens}

omit mΩ [IsProbabilityMeasure P] in
/-- The clause event `{t < ζ, supp φ ⊆ inv(ℍ ∖ K_t)}`. -/
def clauseEvent (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (c : Ω → Chart) (t : ℝ≥0) (φ : TestOn upperHalfPlaneOpens) :
    Set Ω :=
  {ω | (t : ℝ≥0∞) < ζ ω ∧ tsupport φ ⊆ (c ω).2.1 '' (H \ fwdHull (fun s : ℝ => W s.toNNReal ω) (t : ℝ))}

/-- **The chart clause conditionally on the exterior record, at fixed times.** Hypotheses: the clause at fixed times
for `𝓐` under `P`; `𝒬 ≤ mΩ`; σ-algebras `𝒢_t ⊇ 𝓐_t ∨ 𝒬` given which the conditional characteristic function of
`h(φ)` has modulus `exp(−½ G(φ, φ))` on the clause event (with the zero-boundary variance of `inv(ℍ ∖ K_t)`); the
clause events covered by countably many events of `𝓐_t` inside them. Then the clause holds at fixed times for
`𝓐 ∨ 𝒬` under `P[· | G]` for every `G ∈ 𝒬` with `P G ≠ 0`. -/
theorem isChartCouplingCharFunConst_cond (hh : Measurable h) (h𝒬 : 𝒬 ≤ mΩ)
    (𝒢 : ℝ≥0 → MeasurableSpace Ω) (h𝒢 : ∀ t, 𝒢 t ≤ mΩ) (h𝓐𝒢 : ∀ t, 𝓐 t ≤ 𝒢 t) (h𝒬𝒢 : ∀ t, 𝒬 ≤ 𝒢 t)
    (hmod : ∀ t φ, ∀ᵐ ω ∂P, ω ∈ clauseEvent W ζ c t φ →
      ‖P[fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ)) | 𝒢 t] ω‖ =
        Real.exp (-(1 / 2) * zeroGFFTestCov ((c ω).2.1 '' (H \ fwdHull (fun s : ℝ => W s.toNNReal ω) (t : ℝ)))
          φ φ))
    (hcov : ∀ t φ, ∃ E : ℕ → Set Ω, (∀ j, MeasurableSet[𝓐 t] (E j)) ∧ (∀ j, E j ⊆ clauseEvent W ζ c t φ) ∧
      clauseEvent W ζ c t φ ⊆ ⋃ j, E j)
    (hcf : Lemma71D.IsChartCouplingCharFunConst κ ρL ρR P 𝓐 W VL VR ζ c a k h)
    {G : Set Ω} (hG : MeasurableSet[𝒬] G) (hPG : P G ≠ 0) :
    Lemma71D.IsChartCouplingCharFunConst κ ρL ρR (P[|G]) (supConst 𝓐 𝒬 h𝒬) W VL VR ζ c a k h := by
  intro t u hu φ
  set X : Ω → ℂ := fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ)) with hXdef
  have hXm : Measurable X := GFF.measurable_exp_I_mul ((LQGMetric.measurable_distOn_apply φ).comp hh)
  have hXb : ∀ ω, ‖X ω‖ ≤ 1 := fun ω => by
    simp only [hXdef]; rw [mul_comm]; exact (Complex.norm_exp_ofReal_mul_I _).le
  have hX := hcf t u hu φ
  obtain ⟨E, hEm, hEsub, hEcov⟩ := hcov t φ
  have hac : P[|G] ≪ P := cond_absolutelyContinuous
  have h𝓐Q : 𝓐 t ≤ supConst 𝓐 𝒬 h𝒬 t := le_sup_left
  have hQ𝒢 : supConst 𝓐 𝒬 h𝒬 t ≤ 𝒢 t := sup_le (h𝓐𝒢 t) (h𝒬𝒢 t)
  -- on each piece
  have hpiece : ∀ j, ∀ᵐ ω ∂(P[|G]), ω ∈ E j → (P[|G])[X | supConst 𝓐 𝒬 h𝒬 t] ω = P[X | 𝓐 t] ω := by
    intro j
    have hn : ∀ᵐ ω ∂P, ω ∈ E j → ‖P[X | 𝒢 t] ω‖ = ‖P[X | 𝓐 t] ω‖ := by
      filter_upwards [hmod t φ, hX] with ω h1 h2 hω
      have hω' := hEsub j hω
      rw [h1 hω', h2 hω'.1 hω'.2, Complex.norm_exp]
      simp only [Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.ofReal_re, zero_mul, Complex.I_im,
        Complex.ofReal_im, mul_zero, sub_self, zero_sub]
      congr 1
      ring
    have h1 := ae_condExp_eq_on_of_norm_eq (h𝓐𝒢 t) (h𝒢 t) hXm hXb (hEm j) hn
    have h2 := Sec6.condExp_ae_eq_on_of_le hQ𝒢 (h𝒢 t)
      (Integrable.of_bound hXm.aestronglyMeasurable 1 (Eventually.of_forall hXb))
      (stronglyMeasurable_condExp.mono h𝓐Q) integrable_condExp (h𝓐Q _ (hEm j)) h1
    exact ae_condExp_cond_eq_on ((supConst 𝓐 𝒬 h𝒬).le t) hXm hXb (stronglyMeasurable_condExp.mono h𝓐Q)
      integrable_condExp (h𝓐Q _ (hEm j)) h2 (le_sup_right (a := 𝓐 t) _ hG) hPG
  filter_upwards [ae_all_iff.2 hpiece, hac.ae_le hX] with ω hω hXω hlt hsupp
  obtain ⟨j, hj⟩ := mem_iUnion.1 (hEcov ⟨hlt, hsupp⟩)
  rw [hω j hj, hXω hlt hsupp]

end Clause

end InteractingSLE.Sec7.Lemma72D
