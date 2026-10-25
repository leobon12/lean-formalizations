import SupercriticalLQGUniqueness.B2.DG20Lim.NormalizedAroundFourPoint
import SupercriticalLQGUniqueness.B2.DG20Pt.AroundPolarData
import SupercriticalLQGUniqueness.B2.Iface.Statements

 

set_option autoImplicit false
noncomputable section

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
open LQGMetric LQGMetric.DDDF

namespace SupercriticalLQGUniqueness.B2.DG20Lim

 

theorem exists_polar_point_tightness_of_section4
    (hS4 : B2.Iface.DG20Section4)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (hm : ∀ ε, IsLFPPNormalizer ξ ε (m ε))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (X : Ioi (0 : ℝ) → Ω → C(ℂ, ℝ))
    (hX : ∀ ε, IsHeatSmoothing P h ε (X ε))
    (A : EuclideanAnnulus) :
    ∃ z w : Fin 4 → ℂ,
      (∀ j, z j ∈ B2.Strong.cfgSet₁ A j) ∧
      (∀ j, w j ∈ B2.Strong.cfgSet₂ A j) ∧
      (∀ j, IsTwoSidedTight P
        (fun (ε : Ioo (0 : ℝ) 1) ω =>
          ENNReal.ofReal ((m ⟨(ε : ℝ), ε.property.1⟩ : ℝ)⁻¹) *
            crossLenIn (ξ : ℝ) (X ⟨(ε : ℝ), ε.property.1⟩ ω)
              (B2.Strong.cfgOpens A j) {z j} {w j})) := by
  have hEach : ∀ j : Fin 4, ∃ z w : ℂ,
      z ∈ B2.Strong.cfgSet₁ A j ∧
      w ∈ B2.Strong.cfgSet₂ A j ∧
      IsTwoSidedTight P
        (fun (ε : Ioo (0 : ℝ) 1) ω =>
          ENNReal.ofReal ((m ⟨(ε : ℝ), ε.property.1⟩ : ℝ)⁻¹) *
            crossLenIn (ξ : ℝ) (X ⟨(ε : ℝ), ε.property.1⟩ ω)
              (B2.Strong.cfgOpens A j) {z} {w}) := by
    intro j
    obtain ⟨_, _, _, _, _, hnt₁, hnt₂, hsub₁, hsub₂, hdisj, hconn⟩ :=
      B2.DG20Pt.around_polar_data A j
    obtain ⟨z, hz, _, _, _⟩ := hnt₁
    obtain ⟨w, hw, _, _, _⟩ := hnt₂
    have hzw : z ≠ w := by
      intro heq
      exact (Set.disjoint_left.mp hdisj) hz (heq ▸ hw)
    exact ⟨z, w, hz, hw,
      (hS4 ξ Q hQ m hm).1 P h hh X hX
        (B2.Strong.cfgOpens A j) hconn z w
        (hsub₁ hz) (hsub₂ hw) hzw⟩
  choose z w hz hw hT using hEach
  exact ⟨z, w, hz, hw, hT⟩

end SupercriticalLQGUniqueness.B2.DG20Lim
