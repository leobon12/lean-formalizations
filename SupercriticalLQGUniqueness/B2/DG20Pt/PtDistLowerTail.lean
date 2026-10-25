import SupercriticalLQGUniqueness.B2.DG20Pt.PtDistAnnulusLower
import SupercriticalLQGUniqueness.B2.DG20Pt.PtDistAcrossGeometry

 


set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Metric TopologicalSpace
open scoped ENNReal
open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.LFPP

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem pt_dist_point_lower_tail_of_inputs
    (hPerc : SupercriticalLQGUniqueness.B2.Iface.DG20PercEstimate')
    (ξ : Ioi (0 : ℝ)) (z w : ℂ) (hzw : z ≠ w) :
    ∃ c₀ c₁ : ℝ, 0 < c₀ ∧ 0 < c₁ ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (W : WNSpace → Ω → ℝ),
        IsWhiteNoise P W → ∀ n : ℕ, ∀ T : ℝ, 3 < T →
          P {ω | lfppDOn (ξ : ℝ) (fun u => phiMN W P 0 n u ω) univ z w <
            ENNReal.ofReal (T⁻¹ * lambdaN ξ W P n)} ≤
          ENNReal.ofReal (c₀ * Real.exp (-c₁ * (Real.log T) ^ 2)) := by
  let d : ℝ := dist z w
  have hd : 0 < d := dist_pos.mpr hzw
  let U : Opens ℂ := ⟨ball z d, isOpen_ball⟩
  let K₁ : Set ℂ := sphere z (d / 4)
  let K₂ : Set ℂ := sphere z (d / 2)
  have hnt₁ : K₁.Nontrivial := Strong.nontrivial_sphere z (by positivity)
  have hnt₂ : K₂.Nontrivial := Strong.nontrivial_sphere z (by positivity)
  have hc₁ : IsConnected K₁ :=
    ⟨hnt₁.nonempty, LQGMetric.TopoCircle.isPreconnected_sphere_complex _ (by positivity)⟩
  have hc₂ : IsConnected K₂ :=
    ⟨hnt₂.nonempty, LQGMetric.TopoCircle.isPreconnected_sphere_complex _ (by positivity)⟩
  have hs₁ : K₁ ⊆ U := by
    intro u hu
    change u ∈ ball z d
    have h := mem_sphere.mp hu
    apply mem_ball.mpr
    rw [h]
    linarith
  have hs₂ : K₂ ⊆ U := by
    intro u hu
    change u ∈ ball z d
    have h := mem_sphere.mp hu
    apply mem_ball.mpr
    rw [h]
    linarith
  have hdis : Disjoint K₁ K₂ := by
    apply Set.disjoint_left.mpr
    intro u hu₁ hu₂
    have h₁ := mem_sphere.mp hu₁
    have h₂ := mem_sphere.mp hu₂
    linarith
  have hUc : IsConnected (U : Set ℂ) :=
    (convex_ball z d).isConnected (nonempty_ball.mpr hd)
  obtain ⟨c₀, c₁, hc₀, hc₁', htail⟩ := hPerc ξ U K₁ K₂
    (isCompact_sphere _ _) (isCompact_sphere _ _) hc₁ hc₂ hnt₁ hnt₂
    hs₁ hs₂ hdis hUc
  refine ⟨c₀, c₁, hc₀, hc₁', ?_⟩
  intro Ω _ P _ W hW n T hT
  have hsubset :
      {ω | lfppDOn (ξ : ℝ) (fun u => phiMN W P 0 n u ω) univ z w <
        ENNReal.ofReal (T⁻¹ * lambdaN ξ W P n)} ⊆
      {ω | crossLenIn (ξ : ℝ) (fun u => phiMN W P 0 n u ω) U K₁ K₂ <
        ENNReal.ofReal (T⁻¹ * lambdaN ξ W P n)} := by
    intro ω hω
    exact (pt_dist_annulus_cross_le_point (ξ : ℝ)
      (fun u => phiMN W P 0 n u ω) z w hzw).trans_lt hω
  exact (measure_mono hsubset).trans ((htail P W hW n T hT).1)

end SupercriticalLQGUniqueness.B2.DG20Pt
