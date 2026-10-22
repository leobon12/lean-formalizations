import HigherDimLQGMetric.Amplify.Collar

/-! Choice of the small coarse-field oscillation threshold. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Filter Topology Set

/-- The two strict numerical margins in Lemma 6.1 hold for some positive
coarse-field oscillation threshold. -/
theorem amplify_exists_delta {ξ c1 c2 : ℝ} (_hξ : 0 < ξ)
    (_hc1 : 0 < c1) (hc : c1 < c2) :
    ∃ δ : ℝ, 0 < δ ∧ Real.exp (4 * ξ * δ) * c1 < c2 ∧
      Real.exp (4 * ξ * δ) < 2 := by
  have hcont : ContinuousAt (fun δ : ℝ => Real.exp (4 * ξ * δ)) 0 := by fun_prop
  have hlim : Tendsto (fun δ : ℝ => Real.exp (4 * ξ * δ)) (𝓝[>] 0) (𝓝 1) := by
    convert hcont.tendsto.mono_left nhdsWithin_le_nhds using 1
    norm_num
  have hlim₁ : Tendsto (fun δ : ℝ => Real.exp (4 * ξ * δ) * c1)
      (𝓝[>] 0) (𝓝 c1) := by
    simpa only [one_mul] using hlim.mul_const c1
  have hgood : ∀ᶠ δ : ℝ in 𝓝[>] 0,
      Real.exp (4 * ξ * δ) * c1 < c2 ∧ Real.exp (4 * ξ * δ) < 2 :=
    (hlim₁.eventually (eventually_lt_nhds hc)).and
      (hlim.eventually (eventually_lt_nhds (by norm_num : (1 : ℝ) < 2)))
  have hpos : ∀ᶠ δ : ℝ in 𝓝[>] 0, δ ∈ Ioi (0 : ℝ) :=
    self_mem_nhdsWithin
  obtain ⟨δ, hδ, hsmall⟩ := (hpos.and hgood).exists
  exact ⟨δ, hδ, hsmall.1, hsmall.2⟩

end HigherDimLQGMetric
