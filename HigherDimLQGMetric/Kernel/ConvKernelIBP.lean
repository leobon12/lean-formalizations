import HigherDimLQGMetric.Kernel.ConvKernelGlobalIntegrable
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# Integration by parts with a puncture at the origin

The usual Mathlib theorem requires differentiability everywhere. Here the inner one-dimensional
integrations run along transverse lines; the line through the origin is null when the ambient
dimension is at least two. This is the A2.5 Fubini argument.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory Measure Module Topology Set
namespace HigherDimLQGMetric

private theorem integral_bilinear_line_ae_aux1
    {E F G W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    [MeasurableSpace E] {μ : Measure E} [SigmaFinite μ]
    {f f' : E × ℝ → F} {g g' : E × ℝ → G}
    {B : F →L[ℝ] G →L[ℝ] W}
    (hf'g : Integrable (fun x => B (f' x) (g x)) (μ.prod volume))
    (hfg' : Integrable (fun x => B (f x) (g' x)) (μ.prod volume))
    (hfg : Integrable (fun x => B (f x) (g x)) (μ.prod volume))
    (hf : ∀ z, HasLineDerivAt ℝ f (f' z) z (0, 1))
    (hg : ∀ᵐ x ∂μ, ∀ t : ℝ,
      HasLineDerivAt ℝ g (g' (x,t)) (x,t) (0,1)) :
    ∫ z, B (f z) (g' z) ∂(μ.prod volume) =
      - ∫ z, B (f' z) (g z) ∂(μ.prod volume) := calc
  _ = ∫ x, (∫ t, B (f (x,t)) (g' (x,t))) ∂μ := integral_prod _ hfg'
  _ = ∫ x, (- ∫ t, B (f' (x,t)) (g (x,t))) ∂μ := by
    apply integral_congr_ae
    filter_upwards [hf'g.prod_right_ae, hfg'.prod_right_ae,
      hfg.prod_right_ae, hg] with x hf'gx hfg'x hfgx hgx
    apply integral_bilinear_hasDerivAt_right_eq_neg_left_of_integrable
      ?_ ?_ hfg'x hf'gx hfgx
    · intro t _
      convert! (hf (x,t)).scomp_of_eq t
        ((hasDerivAt_id t).add (hasDerivAt_const t (-t)))
        (by simp) <;> simp
    · intro t _
      convert! (hgx t).scomp_of_eq t
        ((hasDerivAt_id t).add (hasDerivAt_const t (-t)))
        (by simp) <;> simp
  _ = _ := by rw [integral_neg, integral_prod _ hf'g]

private theorem integral_bilinear_line_ae_aux2
    {E F G W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {μ : Measure (E × ℝ)} [IsAddHaarMeasure μ]
    {f f' : E × ℝ → F} {g g' : E × ℝ → G}
    {B : F →L[ℝ] G →L[ℝ] W}
    (hf'g : Integrable (fun x => B (f' x) (g x)) μ)
    (hfg' : Integrable (fun x => B (f x) (g' x)) μ)
    (hfg : Integrable (fun x => B (f x) (g x)) μ)
    (hf : ∀ z, HasLineDerivAt ℝ f (f' z) z (0,1))
    (hg : ∀ᵐ x ∂(addHaar : Measure E), ∀ t : ℝ,
      HasLineDerivAt ℝ g (g' (x,t)) (x,t) (0,1)) :
    ∫ z, B (f z) (g' z) ∂μ = - ∫ z, B (f' z) (g z) ∂μ := by
  let ν : Measure E := addHaar
  have A : ν.prod volume = (addHaarScalarFactor (ν.prod volume) μ) • μ :=
    isAddLeftInvariant_eq_smul _ _
  have Hf'g : Integrable (fun z => B (f' z) (g z)) (ν.prod volume) := by
    rw [A]; exact hf'g.smul_measure_nnreal
  have Hfg' : Integrable (fun z => B (f z) (g' z)) (ν.prod volume) := by
    rw [A]; exact hfg'.smul_measure_nnreal
  have Hfg : Integrable (fun z => B (f z) (g z)) (ν.prod volume) := by
    rw [A]; exact hfg.smul_measure_nnreal
  rw [isAddLeftInvariant_eq_smul μ (ν.prod volume)]
  simp [integral_bilinear_line_ae_aux1 Hf'g Hfg' Hfg hf hg]

/-- Integration by parts for an integrable directional derivative that may be singular at the
origin, provided the ambient dimension is at least two. -/
theorem integral_bilinear_line_except_zero
    {E F G W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {μ : Measure E} [IsAddHaarMeasure μ]
    {f f' : E → F} {g g' : E → G} {v : E}
    {B : F →L[ℝ] G →L[ℝ] W}
    (hd : 2 ≤ finrank ℝ E)
    (hf'g : Integrable (fun x => B (f' x) (g x)) μ)
    (hfg' : Integrable (fun x => B (f x) (g' x)) μ)
    (hfg : Integrable (fun x => B (f x) (g x)) μ)
    (hv : v ≠ 0)
    (hf : ∀ x, HasLineDerivAt ℝ f (f' x) x v)
    (hg : ∀ x : E, x ≠ 0 → HasLineDerivAt ℝ g (g' x) x v) :
    ∫ x, B (f x) (g' x) ∂μ = - ∫ x, B (f' x) (g x) ∂μ := by
  by_cases hW : CompleteSpace W; swap
  · simp [integral, hW]
  have : Nontrivial E := nontrivial_iff.2 ⟨v, 0, hv⟩
  let n := finrank ℝ E
  let E' := Fin (n - 1) → ℝ
  obtain ⟨L, hL⟩ : ∃ L : E ≃L[ℝ] (E' × ℝ), L v = (0,1) := by
    have : finrank ℝ (E' × ℝ) = n := by
      simpa [this, E'] using Nat.sub_add_cancel (by omega : 0 < n)
    have L₀ : E ≃L[ℝ] (E' × ℝ) := (ContinuousLinearEquiv.ofFinrankEq this).symm
    obtain ⟨M, hM⟩ : ∃ M : (E' × ℝ) ≃L[ℝ] (E' × ℝ), M (L₀ v) = (0,1) := by
      apply SeparatingDual.exists_continuousLinearEquiv_apply_eq
      · simpa using hv
      · simp
    exact ⟨L₀.trans M, by simp [hM]⟩
  let ν := Measure.map L μ
  suffices H : ∫ (x : E' × ℝ), B (f (L.symm x)) (g' (L.symm x)) ∂ν =
      -∫ (x : E' × ℝ), B (f' (L.symm x)) (g (L.symm x)) ∂ν by
    have hμ : μ = Measure.map L.symm ν := by
      simp [ν, Measure.map_map L.symm.continuous.measurable L.continuous.measurable]
    have hLemb : IsClosedEmbedding L.symm := L.symm.toHomeomorph.isClosedEmbedding
    simpa [hμ, hLemb.integral_map] using H
  have L_emb : MeasurableEmbedding L := L.toHomeomorph.measurableEmbedding
  apply integral_bilinear_line_ae_aux2
  · simpa [ν, L_emb.integrable_map_iff, Function.comp_def] using hf'g
  · simpa [ν, L_emb.integrable_map_iff, Function.comp_def] using hfg'
  · simpa [ν, L_emb.integrable_map_iff, Function.comp_def] using hfg
  · intro x
    have heq : f = (f ∘ L.symm) ∘ (L : E →ₗ[ℝ] E' × ℝ) := by ext y; simp
    have h := hf (L.symm x)
    rw [heq] at h
    convert! h.of_comp using 1
    · simp
    · simp [← hL]
  · have hne : ∀ᵐ x : E' ∂(addHaar : Measure E'), x ≠ 0 := by
      let : Nontrivial E' := Module.nontrivial_of_finrank_pos (R := ℝ) (by
        have hpos : 0 < n - 1 := by dsimp [n]; omega
        simpa [E'] using hpos)
      exact Measure.ae_ne (addHaar : Measure E') 0
    filter_upwards [hne] with x hx
    intro t
    have hxt : L.symm (x,t) ≠ 0 := by
      intro he
      have hh := congrArg L he
      simp only [map_zero, L.apply_symm_apply] at hh
      exact hx (Prod.mk.inj hh).1
    have heq : g = (g ∘ L.symm) ∘ (L : E →ₗ[ℝ] E' × ℝ) := by ext y; simp
    have h := hg (L.symm (x,t)) hxt
    rw [heq] at h
    convert! h.of_comp using 1
    · simp
    · simp [← hL]

end HigherDimLQGMetric
