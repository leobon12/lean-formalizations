import HigherDimLQGMetric.Locality.StableJoint

/-! Measurable observations of the fixed field can be adjoined to stable metric convergence. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BoundedContinuousFunction

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l7a_stable_adjoin_field {d : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : Measurable h)
    (X : ℕ → Ω → C(Rd d × Rd d, ℝ))
    (Y : Ω → C(Rd d × Rd d, ℝ))
    (hX : ∀ n, Measurable (X n)) (hY : Measurable Y)
    (hstable : StablyTendstoLU P h X Y)
    {A : Type*} [TopologicalSpace A] [MeasurableSpace A]
    [OpensMeasurableSpace A] [SecondCountableTopology A]
    (Φ : (CoordJ → ℝ) → A) (hΦ : Measurable Φ) :
    Tendsto (β := ProbabilityMeasure (A × C(Rd d × Rd d, ℝ)))
      (fun n => (⟨P.map (fun ω => (Φ (pairJ ⊤ (h ω)), X n ω)),
        (Measure.isProbabilityMeasure_map_iff
          ((hΦ.comp ((measurable_pairJ ⊤).comp hh)).prodMk (hX n)).aemeasurable).2
            inferInstance⟩ : ProbabilityMeasure (A × C(Rd d × Rd d, ℝ))))
      atTop
      (𝓝 (⟨P.map (fun ω => (Φ (pairJ ⊤ (h ω)), Y ω)),
        (Measure.isProbabilityMeasure_map_iff
          ((hΦ.comp ((measurable_pairJ ⊤).comp hh)).prodMk hY).aemeasurable).2
            inferInstance⟩ : ProbabilityMeasure (A × C(Rd d × Rd d, ℝ)))) := by
  let H : Ω → CoordJ → ℝ := fun ω => pairJ ⊤ (h ω)
  have hH : Measurable H := (measurable_pairJ ⊤).comp hh
  have hlim := l7a_stable_joint_law P h hh X Y hX hY hstable
  have htest : ∀ φ : (CoordJ → ℝ) × C(Rd d × Rd d, ℝ) → ℝ,
      Continuous φ → (∃ C, ∀ x, |φ x| ≤ C) →
      Tendsto (fun n => ∫ ω, φ (H ω, X n ω) ∂P) atTop
        (𝓝 (∫ ω, φ (H ω, Y ω) ∂P)) := by
    intro φ hφ ⟨C, hC⟩
    let F : ((CoordJ → ℝ) × C(Rd d × Rd d, ℝ)) →ᵇ ℝ :=
      BoundedContinuousFunction.mkOfBound ⟨φ, hφ⟩ (2 * C)
        (fun x y => by
          rw [Real.dist_eq]
          have h1 := abs_le.1 (hC x)
          have h2 := abs_le.1 (hC y)
          show |φ x - φ y| ≤ 2 * C
          rw [abs_le]
          constructor <;> linarith)
    have ht := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hlim) F
    have hFn (n : ℕ) :
        ∫ p, F p ∂(P.map (fun ω => (H ω, X n ω))) =
        ∫ ω, φ (H ω, X n ω) ∂P := by
      rw [integral_map (hH.prodMk (hX n)).aemeasurable
        F.continuous.measurable.aestronglyMeasurable]
      rfl
    have hFY :
        ∫ p, F p ∂(P.map (fun ω => (H ω, Y ω))) =
        ∫ ω, φ (H ω, Y ω) ∂P := by
      rw [integral_map (hH.prodMk hY).aemeasurable
        F.continuous.measurable.aestronglyMeasurable]
      rfl
    change Tendsto (fun n => ∫ p, F p ∂(P.map (fun ω => (H ω, X n ω))))
      atTop (𝓝 (∫ p, F p ∂(P.map (fun ω => (H ω, Y ω))))) at ht
    simpa only [hFn, hFY] using ht
  exact LQGMetric.DFGPS.L217.tendsto_law_of_fixed_marginal
    hH hH rfl hX hY htest hΦ

end HigherDimLQGMetric
