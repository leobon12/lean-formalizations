/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec6.Prop65DDSProd
import InteractingSLE.Frozen.Spec.IsFilteredBrownianReal

/-!
# A stopped Brownian motion continued by an independent one is Brownian in the product filtration

Packet PROVE-WHOLEFIELD5 (follow-up note C.2/(WF7), `ig1_followup_proofs.txt` L1527–1550; the route of
`planning/handoffs/PROVE-WHOLEFIELD4.md` §4.1: "append an independent Brownian motion after `S` on `Ω × Ω'`").

The germ filtration of the whole-field identification makes the driving noise a Brownian motion only up to the
lifetime: `e^{a N_u − a² ℓ_u / 2}` is a martingale with the clock `ℓ_u = u ∧ ζ`. On `Ω × Ω₀`, with an independent
Brownian motion `B` of a filtration `𝓦` on `Ω₀`,

  `β_u = N_u + B_u − B_{ℓ_u}`

is a Brownian motion **of the product filtration** `𝓗_u ⊗ 𝓦_u` (`IsTCExpMartingale.isFilteredBrownianReal_complNoise`).
This is the filtered form of `Sec6.Prop65.IsTCExpMartingale.exists_isBrownianReal_completion` (packet PROVE-SEC6-E,
whose conclusion records only the Brownian law); the proof is that one, for a general filtration `𝓦` of `B`, with
MathFin's `isFilteredPreBrownian_of_expMartingale` added at the end. The filtration matters here: the restart law of
Theorem 2.2 (`Sec2.Restart.measure_restart_killedState`) is applied in it, and it contains the germ σ-algebras.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal NNReal

namespace InteractingSLE

namespace WholeField

open Sec6.Prop65

universe u v

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {Ω₀ : Type v} [m₀ : MeasurableSpace Ω₀]
  {P₀ : Measure Ω₀}

/-- The product filtration `𝓗_u ⊗ 𝓦_u` on `Ω × Ω₀`. -/
def prodFiltration (𝓗 : Filtration ℝ≥0 mΩ) (𝓦 : Filtration ℝ≥0 m₀) :
    Filtration ℝ≥0 (inferInstance : MeasurableSpace (Ω × Ω₀)) where
  seq u := @Prod.instMeasurableSpace Ω Ω₀ (𝓗 u) (𝓦 u)
  mono' _ _ huv := sup_le_sup (MeasurableSpace.comap_mono (𝓗.mono huv))
    (MeasurableSpace.comap_mono (𝓦.mono huv))
  le' u := sup_le_sup (MeasurableSpace.comap_mono (𝓗.le u)) (MeasurableSpace.comap_mono (𝓦.le u))

theorem prodFiltration_apply (𝓗 : Filtration ℝ≥0 mΩ) (𝓦 : Filtration ℝ≥0 m₀) (u : ℝ≥0) :
    prodFiltration 𝓗 𝓦 u = (𝓗 u).comap Prod.fst ⊔ (𝓦 u).comap Prod.snd := rfl

/-- The first factor of the product filtration. -/
theorem comap_fst_le_prodFiltration (𝓗 : Filtration ℝ≥0 mΩ) (𝓦 : Filtration ℝ≥0 m₀) (u : ℝ≥0) :
    (𝓗 u).comap Prod.fst ≤ prodFiltration 𝓗 𝓦 u := le_sup_left

/-- **The completed noise** `β_u = N_u + B_u − B_{ℓ_u}` on `Ω × Ω₀`. -/
def complNoise (N : ℝ≥0 → Ω → ℝ) (ℓ : ℝ≥0 → Ω → ℝ≥0) (B : ℝ≥0 → Ω₀ → ℝ) (u : ℝ≥0) (p : Ω × Ω₀) : ℝ :=
  N u p.1 + B u p.2 - B (ℓ u p.1) p.2

omit mΩ m₀ in
/-- Before the clock stops (`ℓ_u = u`) the completed noise is the original one. -/
theorem complNoise_of_eq {N : ℝ≥0 → Ω → ℝ} {ℓ : ℝ≥0 → Ω → ℝ≥0} {B : ℝ≥0 → Ω₀ → ℝ} {u : ℝ≥0}
    {p : Ω × Ω₀} (h : ℓ u p.1 = u) : complNoise N ℓ B u p = N u p.1 := by
  simp only [complNoise, h, add_sub_cancel_right]

namespace IsTCExpMartingale

variable {𝓗 : Filtration ℝ≥0 mΩ} {N : ℝ≥0 → Ω → ℝ} {ℓ : ℝ≥0 → Ω → ℝ≥0}

/-- **Completion by an independent Brownian motion, filtered form.** Under `IsTCExpMartingale P 𝓗 N ℓ`, for a
Brownian motion `B` of a filtration `𝓦` on `Ω₀` with every path continuous and `B₀ = 0`, the completed noise
`β_u = N_u + B_u − B_{ℓ_u}` is a Brownian motion of the product filtration `𝓗 ⊗ 𝓦` under `P ⊗ P₀`, with every
path continuous. -/
theorem isFilteredBrownianReal_complNoise [IsProbabilityMeasure P] [IsProbabilityMeasure P₀]
    (h : IsTCExpMartingale P 𝓗 N ℓ) {𝓦 : Filtration ℝ≥0 m₀} {B : ℝ≥0 → Ω₀ → ℝ}
    (hFB : IsFilteredPreBrownian B 𝓦 P₀) (hBc : ∀ w, Continuous fun r => B r w) (hB0 : ∀ w, B 0 w = 0) :
    IsFilteredBrownianReal (prodFiltration 𝓗 𝓦) (complNoise N ℓ B) (P.prod P₀) ∧
      ∀ p, Continuous fun u => complNoise N ℓ B u p := by
  have hBad : ∀ r, Measurable[𝓦 r] (B r) := fun r => (hFB.stronglyAdapted r).measurable
  have hBm : ∀ r, Measurable (B r) := fun r => (hBad r).mono (𝓦.le r) le_rfl
  set Q : Measure (Ω × Ω₀) := P.prod P₀ with hQ
  set β : ℝ≥0 → Ω × Ω₀ → ℝ := complNoise N ℓ B with hβ
  have hβc : ∀ p, Continuous fun u => β u p := fun p =>
    ((h.cont p.1).add (hBc p.2)).sub ((hBc p.2).comp (h.continuous_ℓ p.1))
  set 𝓖 := prodFiltration 𝓗 𝓦 with h𝓖
  have hβm : ∀ u, Measurable[𝓖 u] (β u) := by
    intro u
    have hBu : ∀ w, Continuous fun r => B (min r u) w := fun w =>
      (hBc w).comp (continuous_id.min continuous_const)
    have hBum : ∀ r, Measurable[𝓦 u] (B (min r u)) := fun r =>
      (hBad _).mono (𝓦.mono (min_le_right _ _)) le_rfl
    have := @measurable_completion Ω Ω₀ (𝓗 u) (𝓦 u) (N u) (h.measurable_N u) (ℓ u)
      (h.measurable_ℓ u) (fun r w => B (min r u) w) hBu hBum u
    have e : β u = fun p : Ω × Ω₀ => N u p.1 + B (min u u) p.2 - B (min (ℓ u p.1) u) p.2 := by
      funext p
      simp only [hβ, complNoise, min_self, min_eq_left (h.le u p.1)]
    rw [e]
    exact this
  have hβm' : ∀ u, Measurable (β u) := fun u => (hβm u).mono (𝓖.le u) le_rfl
  -- the integrand `e^{aβ_r − a² r/2}`
  set f : ℝ → ℝ≥0 → Ω × Ω₀ → ℝ≥0∞ :=
    fun a r p => ENNReal.ofReal (Real.exp (a * β r p - a ^ 2 * (r : ℝ) / 2)) with hf
  have hfm : ∀ a r, Measurable (f a r) := fun a r =>
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (((hβm' r).const_mul a).sub_const _))
  have hbmEm : ∀ a r x, Measurable (bmE B a r x) := fun a r x =>
    (((hBm r).sub (hBm _)).const_mul a).sub_const _
  -- Fubini on boxes
  have hbox : ∀ (a : ℝ) (r : ℝ≥0) {B₁ : Set Ω} {B₂ : Set Ω₀}, MeasurableSet B₁ →
      MeasurableSet B₂ → ∫⁻ p in B₁ ×ˢ B₂, f a r p ∂Q =
        ∫⁻ ω in B₁, ENNReal.ofReal (Real.exp (a * N r ω - a ^ 2 * (ℓ r ω : ℝ) / 2)) *
          ∫⁻ w in B₂, ENNReal.ofReal (Real.exp (bmE B a r (ℓ r ω) w)) ∂P₀ ∂P := by
    intro a r B₁ B₂ _ _
    rw [hQ, ← Measure.prod_restrict, lintegral_prod _ (hfm a r).aemeasurable]
    refine lintegral_congr fun ω => ?_
    rw [← lintegral_const_mul (f := fun w => ENNReal.ofReal (Real.exp (bmE B a r (ℓ r ω) w))) _
      (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hbmEm a r (ℓ r ω))))]
    refine lintegral_congr fun w => ?_
    simp only [hf, hβ, complNoise, bmE, min_eq_right (h.le r ω)]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 2
    ring
  -- the Brownian integral as a function of the clock value
  set Ψ : ℝ → ℝ≥0 → Set Ω₀ → ℝ≥0 → ℝ≥0∞ :=
    fun a s B₂ y => ∫⁻ w in B₂, ENNReal.ofReal (Real.exp (bmE B a s y w)) ∂P₀ with hΨ
  have hΨm : ∀ a s {B₂ : Set Ω₀}, MeasurableSet B₂ → Measurable (Ψ a s B₂) := by
    intro a s B₂ hB₂
    have h2 : Measurable fun q : ℝ≥0 × Ω₀ => B (min s q.1) q.2 :=
      (measurable_uncurry_of_continuous_of_measurable (u := fun y w => B (min s y) w)
        (fun w => (hBc w).comp (continuous_const.min continuous_id)) fun y => hBm _)
    have h3 : Measurable fun q : ℝ≥0 × Ω₀ => (((min s q.1 : ℝ≥0)) : ℝ) :=
      (NNReal.continuous_coe.comp (continuous_const.min continuous_id)).measurable.comp
        measurable_fst
    have hj : Measurable fun q : ℝ≥0 × Ω₀ => bmE B a s q.1 q.2 :=
      ((((hBm s).comp measurable_snd).sub h2).const_mul a).sub
        (((measurable_const.sub h3).const_mul _).div_const _)
    have hj' : Measurable fun q : ℝ≥0 × Ω₀ => (Prod.snd ⁻¹' B₂).indicator
        (fun q => ENNReal.ofReal (Real.exp (bmE B a s q.1 q.2))) q :=
      (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hj)).indicator
        (measurable_snd hB₂)
    have e : Ψ a s B₂ = fun y => ∫⁻ w, (Prod.snd ⁻¹' B₂).indicator
        (fun q => ENNReal.ofReal (Real.exp (bmE B a s q.1 q.2))) (y, w) ∂P₀ := by
      funext y
      simp only [hΨ]
      rw [← lintegral_indicator hB₂]
      rfl
    rw [e]
    exact hj'.lintegral_prod_right'
  have hind1 : ∀ {B₂ : Set Ω₀}, MeasurableSet B₂ → ∀ g : Ω₀ → ℝ≥0∞,
      ∫⁻ w in B₂, g w ∂P₀ = ∫⁻ w, B₂.indicator (fun _ => (1 : ℝ≥0∞)) w * g w ∂P₀ := by
    intro B₂ hB₂ g
    rw [← lintegral_indicator hB₂]
    refine lintegral_congr fun w => ?_
    by_cases hw : w ∈ B₂ <;> simp [hw]
  -- the box identity
  have hboxeq : ∀ (a : ℝ) {s t : ℝ≥0}, s ≤ t → ∀ {B₁ : Set Ω} {B₂ : Set Ω₀},
      MeasurableSet[𝓗 s] B₁ → MeasurableSet[𝓦 s] B₂ →
        ∫⁻ p in B₁ ×ˢ B₂, f a t p ∂Q = ∫⁻ p in B₁ ×ˢ B₂, f a s p ∂Q := by
    intro a s t hst B₁ B₂ hB₁ hB₂
    have hB₁' : MeasurableSet B₁ := 𝓗.le s _ hB₁
    have hB₂' : MeasurableSet B₂ := 𝓦.le s _ hB₂
    rw [hbox a t hB₁' hB₂', hbox a s hB₁' hB₂']
    have hin : ∀ r : ℝ≥0, s ≤ r → ∀ ω, ∫⁻ w in B₂, ENNReal.ofReal (Real.exp
        (bmE B a r (ℓ r ω) w)) ∂P₀ = Ψ a s B₂ (ℓ s ω) := by
      intro r hsr ω
      have h1B : Measurable[𝓦 s] (B₂.indicator (fun _ => (1 : ℝ≥0∞))) :=
        measurable_const.indicator hB₂
      rw [hind1 hB₂', lintegral_mul_exp_bmE hFB a hsr (ℓ r ω) h1B, ← hind1 hB₂', hΨ]
      simp only
      rw [h.min_eq s r ω hsr]
      refine lintegral_congr fun w => ?_
      rw [bmE_min]
    simp only [hin t hst, hin s le_rfl]
    set W : Ω → ℝ≥0∞ := B₁.indicator fun ω => Ψ a s B₂ (ℓ s ω) with hW
    have hWm : Measurable[𝓗 s] W := ((hΨm a s hB₂').comp (h.measurable_ℓ s)).indicator hB₁
    have hconv : ∀ r : ℝ≥0, ∫⁻ ω in B₁, ENNReal.ofReal (Real.exp (a * N r ω -
        a ^ 2 * (ℓ r ω : ℝ) / 2)) * Ψ a s B₂ (ℓ s ω) ∂P = ∫⁻ ω, W ω *
          ENNReal.ofReal (Real.exp (a * N r ω - a ^ 2 * (ℓ r ω : ℝ) / 2)) ∂P := by
      intro r
      rw [← lintegral_indicator hB₁']
      refine lintegral_congr fun ω => ?_
      by_cases hω : ω ∈ B₁
      · simp only [hW, indicator_of_mem hω, mul_comm]
      · simp only [hW, indicator_of_notMem hω, zero_mul]
    rw [hconv t, hconv s, h.exp a s t hst W hWm]
  -- total mass
  have htot : ∀ a r, ∫⁻ p, f a r p ∂Q = 1 := by
    intro a r
    have := hboxeq a (zero_le (a := r)) (B₁ := univ) (B₂ := univ) (@MeasurableSet.univ _ (𝓗 0))
      (@MeasurableSet.univ _ (𝓦 0))
    simp only [univ_prod_univ, Measure.restrict_univ] at this
    rw [this]
    have h0 : ∀ p, f a 0 p = 1 := fun p => by
      simp [hf, hβ, complNoise, h.zero, h.ℓ_zero, hB0]
    simp only [h0, lintegral_const, measure_univ, mul_one]
  -- every set of `𝓖_s`
  have hall : ∀ (a : ℝ) {s t : ℝ≥0}, s ≤ t → ∀ A, MeasurableSet[𝓖 s] A →
      ∫⁻ p in A, f a t p ∂Q = ∫⁻ p in A, f a s p ∂Q := by
    intro a s t hst A hA
    refine MeasurableSpace.induction_on_inter
      (C := fun A _ => ∫⁻ p in A, f a t p ∂Q = ∫⁻ p in A, f a s p ∂Q)
      (@generateFrom_prod Ω Ω₀ (𝓗 s) (𝓦 s)).symm (@isPiSystem_prod Ω Ω₀ (𝓗 s) (𝓦 s))
      ?_ ?_ ?_ ?_ A hA
    · simp
    · rintro _ ⟨B₁, hB₁, B₂, hB₂, rfl⟩
      exact hboxeq a hst hB₁ hB₂
    · intro A' hA' hC
      have hA'm : MeasurableSet A' := 𝓖.le s _ hA'
      have h1 := lintegral_add_compl (μ := Q) (f a t) hA'm
      have h2 := lintegral_add_compl (μ := Q) (f a s) hA'm
      rw [htot] at h1 h2
      have hfin : ∫⁻ p in A', f a s p ∂Q ≠ ∞ :=
        ne_top_of_le_ne_top ENNReal.one_ne_top (h2 ▸ le_self_add)
      rw [hC] at h1
      exact (ENNReal.add_right_inj hfin).1 (h1.trans h2.symm)
    · intro g hdisj hgm hC
      have hgm' : ∀ i, MeasurableSet (g i) := fun i => 𝓖.le s _ (hgm i)
      rw [lintegral_iUnion hgm' hdisj, lintegral_iUnion hgm' hdisj]
      exact tsum_congr hC
  have hmart : ∀ (a : ℝ) {s t : ℝ≥0}, s ≤ t → ∀ {A : Set (Ω × Ω₀)}, MeasurableSet[𝓖 s] A →
      ∫ p in A, Real.exp (a * β t p - a ^ 2 * (t : ℝ) / 2) ∂Q =
        ∫ p in A, Real.exp (a * β s p - a ^ 2 * (s : ℝ) / 2) ∂Q := by
    intro a s t hst A hA
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun p => (Real.exp_pos _).le)
      (Real.measurable_exp.comp (((hβm' t).const_mul a).sub_const _)).aestronglyMeasurable,
      integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun p => (Real.exp_pos _).le)
      (Real.measurable_exp.comp (((hβm' s).const_mul a).sub_const _)).aestronglyMeasurable]
    exact congrArg ENNReal.toReal (hall a hst A hA)
  have hdata : ∀ T, MathFin.IsExpQMartingale Q 𝓖 β T := fun T =>
    ⟨fun u => (hβm u).stronglyMeasurable, ae_of_all _ fun p => by
        simp [hβ, complNoise, h.zero, h.ℓ_zero, hB0],
      fun a s t hst _ A hA => hmart a hst hA⟩
  have hpre := MathFin.isFilteredPreBrownian_of_expMartingale hdata
  exact ⟨⟨MathFin.isBrownianReal_of_expMartingale hdata (ae_of_all _ hβc), hβm,
    fun s t hst => hpre.indep s t hst⟩, hβc⟩

end IsTCExpMartingale

end WholeField

end InteractingSLE
