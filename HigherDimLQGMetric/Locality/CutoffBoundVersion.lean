import HigherDimLQGMetric.Locality.CutoffH

/-! A bounded measurable version of a compactly supported Markov correction. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory Set

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- An almost surely measurable continuous cutoff can be chosen globally
bounded on every sample, including the exceptional samples. -/
theorem l7a_exists_bounded_measurable_cutoffH_version {d : ℕ}
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (M : MeasurableSpace Ω) {U : Set (Rd d)} (hU : IsOpen U)
    (φ : C(Rd d, ℝ)) (hsup : tsupport φ ⊆ U)
    (hφc : HasCompactSupport φ)
    (H G : Ω → Rd d → ℝ)
    (hHc : ∀ ω, ContinuousOn (H ω) U)
    (hGm : Measurable[M] G) (hHG : H =ᵐ[P] G) :
    ∃ K : Set (Rd d), IsCompact K ∧
      ∃ F : Ω → C(Rd d, ℝ), Measurable[M] F ∧
      (∀ ω, tsupport (F ω) ⊆ K) ∧
      (∀ ω, ∃ B : ℝ, ∀ x, |F ω x| ≤ B) ∧
      (fun ω => (⟨fun x => φ x * H ω x,
        l7a_continuous_cutoffH hU φ (H ω) (hHc ω) hsup⟩ : C(Rd d, ℝ))) =ᵐ[P] F := by
  letI : MeasurableSpace Ω := mΩ
  obtain ⟨F₀, hF₀m, hF₀ae⟩ :=
    l7a_exists_measurable_cutoffH_version P M hU φ hsup H G hHc hGm hHG
  obtain ⟨ψ, U₁, _, hψc, _, _, hK, hψ1, _, _⟩ :=
    l7a_exists_cutoff_of_isCompact hφc.isCompact hU hsup
  let F : Ω → C(Rd d, ℝ) := fun ω => ψ * F₀ ω
  have hFm : Measurable[M] F := by
    letI : MeasurableSpace Ω := M
    exact measurable_const.mul hF₀m
  have hψφ (x : Rd d) : ψ x * φ x = φ x := by
    by_cases hx : x ∈ tsupport φ
    · rw [hψ1 x (hK hx), one_mul]
    · have hφ0 : φ x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [hφ0]
  refine ⟨tsupport ψ, hψc.isCompact, F, hFm, ?_, ?_, ?_⟩
  · intro ω
    exact tsupport_mul_subset_left
  · intro ω
    exact l7a_bounded_cutoffH isOpen_univ ψ (F₀ ω)
      (F₀ ω).continuous.continuousOn (subset_univ _) hψc
  · filter_upwards [hF₀ae] with ω hω
    apply ContinuousMap.ext
    intro x
    have hpoint := congrArg (fun f : C(Rd d, ℝ) => f x) hω
    change φ x * H ω x = ψ x * F₀ ω x
    rw [← hpoint]
    change φ x * H ω x = ψ x * (φ x * H ω x)
    rw [← mul_assoc, hψφ]

end HigherDimLQGMetric
