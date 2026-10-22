import HigherDimLQGMetric.Locality.StageFiniteVersion

/-! A compactly supported measurable mark defined on every field coordinate,
agreeing with the Markov cutoff on the original field law. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory Set Topology

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l7a_exists_clipped_mark {d : ℕ}
    {Ω : Type*} (h : Ω → DistRd d) (ρ : ℝ) (z₀ : Rd d)
    (K : Set (Rd d)) (hK : IsCompact K)
    (F : Ω → C(Rd d, ℝ)) (hFsup : ∀ ω, tsupport (F ω) ⊆ K)
    (V : TopologicalSpace.Opens (Rd d))
    (Φ : (CoordJ → ℝ) → C(Rd d, ℝ) × DistOn (extOpen V))
    (hΦm : Measurable Φ)
    (hΦeq : ∀ ω, (Φ (pairJ ⊤ (h ω))).1 = F ω) :
    ∃ K' : Set (Rd d), IsCompact K' ∧
      ∃ Ψ : (CoordJ → ℝ) → ℝ × C(Rd d, ℝ),
        Measurable Ψ ∧
        (∀ x z, z ∉ K' → (Ψ x).2 z = 0) ∧
        (∀ ω, Ψ (pairJ ⊤ (h ω)) =
          (sphereAvg (h ω) ρ z₀, F ω)) := by
  obtain ⟨ψ, U₁, _, hψc, _, _, hKU, hψ1, _, _⟩ :=
    l7a_exists_cutoff_of_isCompact hK isOpen_univ (subset_univ K)
  let K' := tsupport ψ
  have hK' : IsCompact K' := hψc.isCompact
  let Ψ : (CoordJ → ℝ) → ℝ × C(Rd d, ℝ) := fun x =>
    (sphereAvg (pairJInv ⊤ x) ρ z₀, ψ * (Φ x).1)
  have hψmul : Continuous (fun f : C(Rd d, ℝ) => ψ * f) := by fun_prop
  have hΨm : Measurable Ψ :=
    ((measurable_sphereAvg_left ρ z₀).comp (measurable_pairJInv ⊤)).prodMk
      (hψmul.measurable.comp (measurable_fst.comp hΦm))
  refine ⟨K', hK', Ψ, hΨm, ?_, ?_⟩
  · intro x z hz
    have hψz : ψ z = 0 := by
      by_contra hne
      exact hz (subset_tsupport ψ hne)
    simp only [Ψ, ContinuousMap.mul_apply, hψz, zero_mul]
  · intro ω
    apply Prod.ext
    · simp only [Ψ, pairJInv_pairJ]
    · apply ContinuousMap.ext
      intro z
      change ψ z * (Φ (pairJ ⊤ (h ω))).1 z = F ω z
      rw [hΦeq ω]
      by_cases hz : z ∈ K
      · rw [hψ1 z (hKU hz), one_mul]
      · have hFz : F ω z = 0 := by
          by_contra hne
          exact hz (hFsup ω (subset_tsupport (F ω) hne))
        rw [hFz, mul_zero]

end HigherDimLQGMetric
