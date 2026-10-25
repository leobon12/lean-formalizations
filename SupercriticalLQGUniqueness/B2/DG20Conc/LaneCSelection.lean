import LQGMetric.Papers.DDDF.S6P21Ratio
import LQGMetric.Papers.DDDF.T20CDefs

 








set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {W : WNSpace → Ω → ℝ}

 


theorem laneC_exists_nearGeodSel_meas_visits
    (hW : IsWhiteNoise P W) (Q : PsiParams) (ξ : ℝ)
    {η : ℝ} (hη : 0 < η) :
    ∃ γ : ℕ → Ω → ℝ → ℂ,
      T20.IsNearGeodSel ξ Q W P η γ ∧
      ∀ n K b s, MeasurableSet {ω : Ω | (ω, ω) ∈ T20C.visSet γ n K b s} := by
  have h : ∀ n : ℕ, ∃ (Qn : ℕ → ℝ → ℂ) (J : Ω → ℕ),
      (∀ j, AdmPath (rectAB 1 1).toSet (rectAB 1 1).side₁
        (rectAB 1 1).side₂ (Qn j)) ∧ Measurable J ∧
      ∀ ω, lfppLen ξ (fun x => psiMN Q W P 0 n x ω) (Qn (J ω)) <
        (1 + ENNReal.ofReal η) *
          rectLen ξ (fun x => psiMN Q W P 0 n x ω) (rectAB 1 1) := by
    intro n
    have hψ := isPsiVersion_psiMN (Q := Q) hW (Nat.zero_le n)
    obtain ⟨Qn, hQa, -, -, -, hJ⟩ := exists_nearGeodesic
      (ξ := ξ) (rectAB 1 1) (by norm_num [rectAB])
      (by norm_num [rectAB]) hψ.cont hψ.meas
      (ENNReal.ofReal_pos.2 hη)
    obtain ⟨J, hJm, hJ⟩ := hJ (by simp [rectAB, MarkedRect.crossWidth])
    exact ⟨Qn, J, hQa, hJm, hJ⟩
  choose Qn J hQa hJm hJ using h
  refine ⟨fun n ω => Qn n (J n ω),
    ⟨fun n ω => hQa n _, fun n ω => ?_, fun n K b => ?_⟩,
    fun n K b s => ?_⟩
  · refine (hJ n ω).le.trans (le_of_eq ?_)
    rw [ENNReal.ofReal_add zero_le_one hη.le, ENNReal.ofReal_one]
  · exact hJm n (DiscreteMeasurableSpace.forall_measurableSet
      {j | b ∈ T20.coarseBlocks K (Qn n j)})
  · have hevent :
        {ω : Ω | (ω, ω) ∈ T20C.visSet
          (fun n ω => Qn n (J n ω)) n K b s} =
        (J n) ⁻¹' {j : ℕ | ∃ t ∈ Icc (0 : ℝ) 1,
          Qn n j t ∉ T20B.farSet (T20B.hoBlock K b) s} := by
      ext ω
      rfl
    rw [hevent]
    exact hJm n (DiscreteMeasurableSpace.forall_measurableSet _)

 


def laneCVisitLimsup (γ : ℕ → ℕ → Ω → ℝ → ℂ)
    (n K : ℕ) (b : ℤ × ℤ) (s : ℝ) : Set Ω :=
  ⋂ N : ℕ, ⋃ j : ℕ, {ω | N ≤ j ∧ (ω, ω) ∈ T20C.visSet (γ j) n K b s}

 

theorem laneC_exists_nearGeodSel_sequence
    (hW : IsWhiteNoise P W) (Q : PsiParams) (ξ : ℝ) :
    ∃ γ : ℕ → ℕ → Ω → ℝ → ℂ,
      (∀ j : ℕ, T20.IsNearGeodSel ξ Q W P (((j : ℝ) + 1)⁻¹) (γ j)) ∧
      (∀ j n K b s,
        MeasurableSet {ω : Ω | (ω, ω) ∈ T20C.visSet (γ j) n K b s}) ∧
      ∀ n K b s, MeasurableSet (laneCVisitLimsup γ n K b s) := by
  have h : ∀ j : ℕ, ∃ γ : ℕ → Ω → ℝ → ℂ,
      T20.IsNearGeodSel ξ Q W P (((j : ℝ) + 1)⁻¹) γ ∧
      ∀ n K b s, MeasurableSet
        {ω : Ω | (ω, ω) ∈ T20C.visSet γ n K b s} := by
    intro j
    exact laneC_exists_nearGeodSel_meas_visits hW Q ξ (by positivity)
  choose γ hγ using h
  refine ⟨γ, (fun j => (hγ j).1), (fun j => (hγ j).2), ?_⟩
  intro n K b s
  unfold laneCVisitLimsup
  refine MeasurableSet.iInter fun N => MeasurableSet.iUnion fun j => ?_
  have hconst : MeasurableSet {ω : Ω | N ≤ j} := by
    by_cases hNj : N ≤ j <;> simp [hNj]
  exact hconst.inter ((hγ j).2 n K b s)

end SupercriticalLQGUniqueness.B2.DG20Conc
