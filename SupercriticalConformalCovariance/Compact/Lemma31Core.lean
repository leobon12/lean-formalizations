import SupercriticalLQGUniqueness.Uniqueness.Toolkit.MovingEndpoints.JointCompact

set_option autoImplicit false
noncomputable section
open Filter Topology TopologicalSpace SupercriticalLQGUniqueness
open scoped ENNReal

namespace SupercriticalConformalCovariance.Compact

/-- Multiplicative errors tending to one preserve epigraph convergence.
This includes points where the limiting distance is infinity. -/
theorem lscTendsto_of_multiplicative_sandwich
    {α : Type*} [TopologicalSpace α] [FirstCountableTopology α]
    (F : α × α → ℝ≥0∞) (hF : LowerSemicontinuous F)
    (G : ℕ → α × α → ℝ≥0∞) (a b : ℕ → ℝ≥0∞)
    (ha : Tendsto a atTop (nhds 1)) (hb : Tendsto b atTop (nhds 1))
    (hbound : ∀ n p, a n * F p ≤ G n p ∧ G n p ≤ b n * F p) :
    SupercriticalLQGUniqueness.LSCTendsto
      (fun n p => (G n p : EReal)) (fun p => (F p : EReal)) := by
  constructor
  · intro p q hp
    have hFlsc : F q ≤ liminf (fun n => F (p n)) atTop :=
      (SupercriticalLQGUniqueness.lowerSemicontinuous_iff_seq.1 hF) p q hp
    have hmul : F q ≤ liminf (fun n => a n * F (p n)) atTop := by
      calc F q ≤ liminf (fun n => F (p n)) atTop := hFlsc
        _ = (liminf a atTop) * liminf (fun n => F (p n)) atTop := by
          rw [ha.liminf_eq, one_mul]
        _ ≤ liminf (fun n => a n * F (p n)) atTop := ENNReal.le_liminf_mul
    have hliminf : F q ≤ liminf (fun n => G n (p n)) atTop :=
      hmul.trans (liminf_le_liminf (Eventually.of_forall fun n => (hbound n (p n)).1))
    have hc (w : ℕ → ℝ≥0∞) : ((liminf w atTop : ℝ≥0∞) : EReal) =
        liminf (fun n => (w n : EReal)) atTop :=
      EReal.coe_ennreal_strictMono.monotone.map_liminf_of_continuousAt w
        continuous_coe_ennreal_ereal.continuousAt
    exact (EReal.coe_ennreal_le_coe_ennreal_iff.mpr hliminf).trans_eq (hc _)
  · intro q
    refine ⟨fun _ => q, tendsto_const_nhds, ?_⟩
    have hleft : Tendsto (fun n => a n * F q) atTop (nhds (F q)) := by
      convert ENNReal.Tendsto.mul ha (Or.inl (by norm_num : (1 : ℝ≥0∞) ≠ 0))
        tendsto_const_nhds (Or.inr (by simp : (1 : ℝ≥0∞) ≠ ∞)) using 1; simp
    have hright : Tendsto (fun n => b n * F q) atTop (nhds (F q)) := by
      convert ENNReal.Tendsto.mul hb (Or.inl (by norm_num : (1 : ℝ≥0∞) ≠ 0))
        tendsto_const_nhds (Or.inr (by simp : (1 : ℝ≥0∞) ≠ ∞)) using 1; simp
    have hmid : Tendsto (fun n => G n q) atTop (nhds (F q)) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le hleft hright
        (fun n => (hbound n q).1) (fun n => (hbound n q).2)
    exact continuous_coe_ennreal_ereal.tendsto (F q) |>.comp hmid

end SupercriticalConformalCovariance.Compact
