import SupercriticalLQGUniqueness.Uniqueness.Objects.BlockCoding.ShieldFarPath
import SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.Barrier.Barrier




 


set_option autoImplicit false
noncomputable section

open Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.BlockCoding

theorem exists_euclidean_path_of_finite_curve (D : LSCMetric)
    (hB : BiLipschitz.Barrier.Barrier D) (hL : D.IsLengthSpace)
    (P : ℝ → ℂ) (a b : ℝ) (hP : D.IsCurve P a b) :
    ∃ γ : Path (P a) (P b), D.IsCurve γ.extend 0 1 ∧
      D.len γ.extend 0 1 = D.len P a b := by
  obtain ⟨δ, hδlen, -⟩ :=
    LQGMetric.MetricGeometry.exists_path_of_curve hP.1 hP.2
  let hforget : Continuous (BiLipschitz.Barrier.forget D) :=
    BiLipschitz.Barrier.continuous_forget_of_barrier D hB hL
  let γ : Path (P a) (P b) := δ.map hforget
  have hEq : ∀ s ∈ Icc (0 : ℝ) 1,
      (D.pt ∘ γ.extend) s = δ.extend s := by
    intro s hs
    change D.pt (γ.extend s) = δ.extend s
    rw [Path.extend_apply γ hs, Path.extend_apply δ hs]
    rfl
  refine ⟨γ, ?_, ?_⟩
  · refine ⟨zero_le_one, ?_⟩
    exact δ.continuous_extend.continuousOn.congr (fun s hs => (hEq s hs).symm)
  · rw [D.len_eq_curveLength, D.len_eq_curveLength]
    exact (LQGMetric.MetricGeometry.curveLength_congr hEq).trans hδlen

end SupercriticalLQGUniqueness.Uniqueness.Objects.BlockCoding
