import HigherDimLQGContinuity.Core.Interfaces

/-!
# Passage from the Weyl parameter to the LQG parameter

Packet E4. The homeomorphism in `Prop18Stmt` transports the jointly measurable
version and its locally uniform continuity to the `γ` parameter.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open HigherDimLQGMetric
open HigherDimLFPP (Rd)

namespace HigherDimLQGContinuity

/-- The target exponent at an interior `γ` is strictly subcritical. -/
theorem e4_gammaQ_gt (d : ℕ) {γ : ℝ} (h0 : 0 < γ)
    (h1 : γ < Real.sqrt (2 * d)) :
    Real.sqrt (2 * d) < (d : ℝ) / γ + γ / 2 := by
  set s := Real.sqrt (2 * d) with hs
  have hs2 : s ^ 2 = 2 * d := Real.sq_sqrt (by positivity)
  have key : (d : ℝ) / γ + γ / 2 - s = (γ - s) ^ 2 / (2 * γ) := by
    field_simp
    nlinarith [hs2]
  have hpos : 0 < (γ - s) ^ 2 / (2 * γ) := by
    apply div_pos _ (by positivity)
    have : γ - s ≠ 0 := by linarith
    positivity
  linarith

/-- The `γ` statement follows by composing the `ξ` version with the parameter
homeomorphism, extended by zero outside its domain. -/
theorem theorem11_of (h₁ : Theorem11XiStmt) (h₂ : Prop18Stmt) : Theorem11Stmt := by
  intro d hd
  obtain ⟨D', hmeas, h0, hver, hcont⟩ := h₁ d hd
  obtain ⟨Ξ, hΞ0, -, hΞc, hΞim, hΞiff, -⟩ := (h₂ d hd).2.2.2
  set I : Set ℝ := Ico 0 (Real.sqrt (2 * d)) with hI
  have ha : 0 < Real.sqrt (2 * d) := Real.sqrt_pos.2 (by positivity)
  have h0I : (0 : ℝ) ∈ I := ⟨le_rfl, ha⟩
  let Ξ' : ℝ → ℝ := I.piecewise Ξ (fun _ => 0)
  have hΞ'm : Measurable Ξ' :=
    hΞc.measurable_piecewise continuousOn_const measurableSet_Ico
  have hΞ'eq : ∀ γ ∈ I, Ξ' γ = Ξ γ :=
    fun γ hγ => Set.piecewise_eq_of_mem _ _ _ hγ
  refine ⟨fun γ => D' (Ξ' γ), ?_, ?_, ?_, ?_⟩
  · have heq : Function.uncurry (fun γ => D' (Ξ' γ)) =
        Function.uncurry D' ∘ (fun p : ℝ × DistRd d => (Ξ' p.1, p.2)) := rfl
    rw [heq]
    exact hmeas.comp ((hΞ'm.comp measurable_fst).prodMk measurable_snd)
  · intro g
    simp only [hΞ'eq 0 h0I, hΞ0, h0]
  · intro γ hγ0 hγ1 ξ hξ hQ E hE hE1 Ω _ P _ h hh
    have hξeq : ξ = Ξ γ := (hΞiff γ ⟨hγ0, hγ1⟩ ξ hξ).1 hQ
    have hsub : Real.sqrt (2 * d) < distExp d ξ := hQ ▸ e4_gammaQ_gt d hγ0 hγ1
    have hΞ' : Ξ' γ = ξ := by rw [hΞ'eq γ ⟨hγ0.le, hγ1⟩, hξeq]
    simpa only [hΞ'] using hver ξ hξ hsub E hE hE1 P h hh
  · intro Ω _ P _ h hh
    filter_upwards [hcont P h hh] with ω hω
    intro γ₀ hγ₀ R hR
    have hmem : Ξ γ₀ ∈ xiRange d := hΞim ▸ Set.mem_image_of_mem Ξ hγ₀
    have hT : Tendsto Ξ' (𝓝[I] γ₀) (𝓝[xiRange d] (Ξ γ₀)) := by
      apply tendsto_nhdsWithin_iff.2
      constructor
      · have h1 : Tendsto Ξ (𝓝[I] γ₀) (𝓝 (Ξ γ₀)) := hΞc γ₀ hγ₀
        exact h1.congr' (eventually_nhdsWithin_of_forall fun γ hγ =>
          (hΞ'eq γ hγ).symm)
      · filter_upwards [self_mem_nhdsWithin] with γ hγ
        rw [hΞ'eq γ hγ, ← hΞim]
        exact Set.mem_image_of_mem Ξ hγ
    have hc := (hω (Ξ γ₀) hmem R hR).comp hT
    simpa only [Function.comp_def, hΞ'eq γ₀ hγ₀] using hc

end HigherDimLQGContinuity
