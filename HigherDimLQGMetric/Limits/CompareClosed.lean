import HigherDimLQGMetric.Limits.CompareJoint

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory Set Topology Filter
namespace HigherDimLQGMetric
open HigherDimLFPP (Rd)

/-- Closed relation of uniformly comparable pseudo metrics. -/
def l6c_compareClosed {d : ℕ} (N : ℝ) :
    Set (C(Rd d × Rd d, ℝ) × C(Rd d × Rd d, ℝ)) :=
  {q | q.2 ∈ metricAlgSet_select ∧ ∀ p : Rd d × Rd d,
    Real.exp (-N) * q.1 p ≤ q.2 p ∧
    q.2 p ≤ Real.exp N * q.1 p}

theorem l6c_compareClosed_isClosed {d : ℕ} (N : ℝ) :
    IsClosed (l6c_compareClosed (d := d) N) := by
  unfold l6c_compareClosed
  apply IsClosed.inter
  · exact (isClosed_metricAlgSet_select d).preimage continuous_snd
  · have hA : IsClosed
        {q : C(Rd d × Rd d, ℝ) × C(Rd d × Rd d, ℝ) |
          ∀ p : Rd d × Rd d,
            Real.exp (-N) * q.1 p ≤ q.2 p ∧ q.2 p ≤ Real.exp N * q.1 p} := by
      simp only [ofPred_forall]
      apply isClosed_iInter
      intro p
      apply IsClosed.inter
      · change IsClosed {q : C(Rd d × Rd d, ℝ) × C(Rd d × Rd d, ℝ) |
          Real.exp (-N) * q.1 p ≤ q.2 p}
        exact isClosed_le
          (continuous_const.mul ((continuous_eval_const p).comp continuous_fst))
          ((continuous_eval_const p).comp continuous_snd)
      · change IsClosed {q : C(Rd d × Rd d, ℝ) × C(Rd d × Rd d, ℝ) |
          q.2 p ≤ Real.exp N * q.1 p}
        exact isClosed_le
          ((continuous_eval_const p).comp continuous_snd)
          (continuous_const.mul ((continuous_eval_const p).comp continuous_fst))
    exact hA

/-- A positive mass event of small random comparison constants lies in the
corresponding closed comparison relation. -/
theorem l6c_compareClosed_mass {d : ℕ}
    {ι Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (A B : ι → Ω → C(Rd d × Rd d, ℝ))
    (M : Ω → ℝ) (_hM : Measurable M)
    (i : ι)
    (hAm : AEMeasurable (A i) P) (hBm : AEMeasurable (B i) P)
    (hAalg : ∀ᵐ ω ∂P, A i ω ∈ metricAlgSet_select)
    (hBalg : ∀ᵐ ω ∂P, B i ω ∈ metricAlgSet_select)
    (hcmp : ∀ᵐ ω ∂P, ∀ p : Rd d × Rd d,
      Real.exp (-M ω) * A i ω p ≤ B i ω p ∧
      B i ω p ≤ Real.exp (M ω) * A i ω p)
    (N : ℝ) :
    P {ω | M ω ≤ N} ≤
      (P.map (fun ω => (A i ω, B i ω))) (l6c_compareClosed N) := by
  have hpair : AEMeasurable (fun ω => (A i ω, B i ω)) P :=
    hAm.prodMk hBm
  rw [Measure.map_apply₀ hpair
    (l6c_compareClosed_isClosed N).measurableSet.nullMeasurableSet]
  apply measure_mono_ae
  filter_upwards [hAalg, hBalg, hcmp] with ω hAω hBω hbound
  intro hMN
  refine ⟨hBω, fun p => ?_⟩
  have hnonneg : 0 ≤ A i ω p := by
    have htri := hAω.2.2 p.1 p.2 p.1
    rw [hAω.1, hAω.2.1 p.2 p.1] at htri
    linarith
  have hleft : Real.exp (-N) ≤ Real.exp (-M ω) :=
    Real.exp_le_exp.mpr (by linarith)
  have hright : Real.exp (M ω) ≤ Real.exp N := Real.exp_le_exp.mpr hMN
  exact ⟨(mul_le_mul_of_nonneg_right hleft hnonneg).trans (hbound p).1,
    (hbound p).2.trans (mul_le_mul_of_nonneg_right hright hnonneg)⟩

end HigherDimLQGMetric
