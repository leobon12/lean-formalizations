import SupercriticalLQGUniqueness.B2.PfeWeyl.FiniteChain

 




set_option autoImplicit false
noncomputable section

open Set Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeWeyl

def euclidForget (D : LSCMetric) : D.Space → ℂ := id

def chainWeightMinus (ξ : ℝ) (f : C(ℂ, ℝ)) (θ : ℝ) (z : ℂ) : ENNReal :=
  ENNReal.ofReal (Real.exp (ξ * (f z - θ)))

private theorem weightedChain_eq {X : Type*} [PseudoEMetricSpace X]
    (weight : X → ℝ) (P : ℝ → X) (t : ℕ → ℝ) (ht : Monotone t) (N : ℕ) :
    (∑ j ∈ Finset.range N,
      HigherDimLQGMetric.weightedLength weight P (t j) (t (j + 1))) =
      HigherDimLQGMetric.weightedLength weight P (t 0) (t N) := by
  induction N with
  | zero => simp only [Finset.range_zero, Finset.sum_empty,
      HigherDimLQGMetric.weightedLength_self]
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      exact HigherDimLQGMetric.weightedLength_add
        (ht (Nat.zero_le N)) (ht (Nat.le_succ N))

 


theorem weighted_chain_le_weyl_cost
    (D : LSCMetric) (ξ : ℝ) (hξ : 0 ≤ ξ) (f : C(ℂ, ℝ))
    (hforget : Continuous (euclidForget D))
    {P : ℝ → ℂ} {L : ℝ}
    (hP : D.IsCurve P 0 L)
    (hu : HasUnitSpeedOn (D.pt ∘ P) (Icc 0 L))
    (t : ℕ → ℝ) (ht : Monotone t) (N : ℕ)
    (ht0 : t 0 = 0) (htN : t N = L) (θ : ℝ)
    (hfield : ∀ j < N, ∀ s ∈ Icc (t j) (t (j + 1)),
      f (P (t j)) - θ ≤ f (P s)) :
    (∑ j ∈ Finset.range N,
        chainWeightMinus ξ f θ (P (t j)) * D (P (t j), P (t (j + 1)))) ≤
      ∫⁻ s in Icc 0 L, ENNReal.ofReal (Real.exp (ξ * f (P s))) := by
  let weight : D.Space → ℝ := fun x => Real.exp (ξ * f (euclidForget D x))
  have hweight : Continuous weight :=
    Real.continuous_exp.comp
      (continuous_const.mul (f.continuous.comp hforget))
  have hcweight : ContinuousOn (fun s => weight ((D.pt ∘ P) s)) (Icc 0 L) :=
    hweight.continuousOn.comp hP.2 (fun _ _ => Set.mem_univ _)
  have hpiece (j : ℕ) (hj : j < N) :
      chainWeightMinus ξ f θ (P (t j)) * D (P (t j), P (t (j + 1))) ≤
        HigherDimLQGMetric.weightedLength weight (D.pt ∘ P)
          (t j) (t (j + 1)) := by
    have htime : t j ≤ t (j + 1) := ht (Nat.le_succ j)
    have hdist : D (P (t j), P (t (j + 1))) ≤
        LQGMetric.MetricGeometry.curveLength (D.pt ∘ P) (t j) (t (j + 1)) :=
      LQGMetric.MetricGeometry.edist_le_curveLength (D.pt ∘ P) htime
    have hlo : ∀ s ∈ Icc (t j) (t (j + 1)),
        Real.exp (ξ * (f (P (t j)) - θ)) ≤ weight ((D.pt ∘ P) s) := by
      intro s hs
      exact Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left (hfield j hj s hs) hξ)
    have hlen := HigherDimLQGMetric.ofReal_mul_curveLength_le_weightedLength
      (w := weight) (P := D.pt ∘ P) htime hlo
    exact (mul_le_mul' le_rfl hdist).trans hlen
  calc
    _ ≤ ∑ j ∈ Finset.range N,
          HigherDimLQGMetric.weightedLength weight (D.pt ∘ P)
            (t j) (t (j + 1)) :=
      Finset.sum_le_sum (fun j hj => hpiece j (Finset.mem_range.mp hj))
    _ = HigherDimLQGMetric.weightedLength weight (D.pt ∘ P) 0 L := by
      rw [weightedChain_eq weight (D.pt ∘ P) t ht N, ht0, htN]
    _ = _ := by
      rw [HigherDimLQGMetric.weightedLength_of_hasUnitSpeedOn hP.1 hu hcweight]
      rfl

end SupercriticalLQGUniqueness.B2.PfeWeyl
