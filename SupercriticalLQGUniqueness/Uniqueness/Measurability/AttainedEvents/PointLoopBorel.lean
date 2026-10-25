import SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36Events.PointLoop




 


set_option autoImplicit false
noncomputable section

open Set Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Measurability.AttainedEvents

abbrev LoopInput := LSCMetric × (ℂ × ENNReal)

private def pointParam (R : ℝ) (p : LoopInput) : LSCMetric × (ℂ × ℝ) :=
  (p.1, (p.2.1, R))

private theorem pointParam_measurable (R : ℝ) :
    Measurable (pointParam R) := by
  have hc : Measurable (fun p : LoopInput => p.2.1) :=
    measurable_fst.comp measurable_snd
  have hpair : Measurable (fun p : LoopInput => (p.2.1, R)) :=
    hc.prodMk measurable_const
  exact measurable_fst.prodMk hpair

private theorem pointCost_measurable (R : ℝ) :
    Measurable (fun p : LoopInput => TwoScale.S36Events.pointSphereDist p.1 p.2.1 R) := by
  let f : LSCMetric × (ℂ × ℝ) → ENNReal :=
    fun p => TwoScale.S36Events.pointSphereDist p.1 p.2.1 p.2.2
  have hf : Measurable f := TwoScale.S36Events.pointSphereDist_joint_measurable
  have hc : Measurable (pointParam R) := pointParam_measurable R
  have hcomp : Measurable (f ∘ pointParam R) := hf.comp hc
  exact hcomp

private theorem endpointCost_measurable :
    Measurable (fun p : LoopInput => p.2.2) :=
  measurable_snd.comp measurable_snd

private theorem pointBound_measurable (r θ : ℝ) (q : ℚ) :
    MeasurableSet {p : LoopInput |
      TwoScale.S36Events.pointSphereDist p.1 p.2.1 ((q : ℝ) * r) ≤
        ENNReal.ofReal ((q : ℝ) ^ θ) * p.2.2} := by
  have hc := pointCost_measurable ((q : ℝ) * r)
  have hb : Measurable (fun p : LoopInput =>
      ENNReal.ofReal ((q : ℝ) ^ θ) * p.2.2) :=
    measurable_const.mul endpointCost_measurable
  exact measurableSet_le hc hb

private theorem rationalPointLoop_measurable (r θ δ₀ : ℝ) :
    MeasurableSet {p : LoopInput |
      ∀ q : ℚ, 0 < (q : ℝ) → (q : ℝ) ≤ δ₀ →
        TwoScale.S36Events.pointSphereDist p.1 p.2.1 ((q : ℝ) * r) ≤
          ENNReal.ofReal ((q : ℝ) ^ θ) * p.2.2} := by
  have hi : MeasurableSet (⋂ q : ℚ,
      {p : LoopInput | 0 < (q : ℝ) → (q : ℝ) ≤ δ₀ →
        TwoScale.S36Events.pointSphereDist p.1 p.2.1 ((q : ℝ) * r) ≤
          ENNReal.ofReal ((q : ℝ) ^ θ) * p.2.2}) := by
    apply MeasurableSet.iInter
    intro q
    by_cases hq : 0 < (q : ℝ) ∧ (q : ℝ) ≤ δ₀
    · have h : {p : LoopInput | 0 < (q : ℝ) → (q : ℝ) ≤ δ₀ →
        TwoScale.S36Events.pointSphereDist p.1 p.2.1 ((q : ℝ) * r) ≤
          ENNReal.ofReal ((q : ℝ) ^ θ) * p.2.2} =
        {p : LoopInput | TwoScale.S36Events.pointSphereDist p.1 p.2.1 ((q : ℝ) * r) ≤
          ENNReal.ofReal ((q : ℝ) ^ θ) * p.2.2} := by
        ext p
        exact ⟨fun hp => hp hq.1 hq.2, fun hp _ _ => hp⟩
      rw [h]
      exact pointBound_measurable r θ q
    · have h : {p : LoopInput | 0 < (q : ℝ) → (q : ℝ) ≤ δ₀ →
        TwoScale.S36Events.pointSphereDist p.1 p.2.1 ((q : ℝ) * r) ≤
          ENNReal.ofReal ((q : ℝ) ^ θ) * p.2.2} = Set.univ := by
        ext p
        exact ⟨fun _ => trivial, fun _ hq0 hqδ => False.elim (hq ⟨hq0, hqδ⟩)⟩
      rw [h]
      exact MeasurableSet.univ
  convert hi using 1
  ext p
  simp only [Set.mem_ofPred_eq, Set.mem_iInter]

theorem pointLoopClause_measurable (r θ δ₀ : ℝ) (hθ : 0 < θ) :
    MeasurableSet {p : LoopInput | p.2.2 ≠ ⊤ ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
        TwoScale.S36Events.pointSphereDist p.1 p.2.1 (δ * r) ≤
          ENNReal.ofReal (δ ^ θ) * p.2.2} := by
  have hfin : MeasurableSet {p : LoopInput | p.2.2 ≠ ⊤} :=
    (measurableSet_eq_fun endpointCost_measurable measurable_const).compl
  have hrat := rationalPointLoop_measurable r θ δ₀
  have heq : {p : LoopInput | p.2.2 ≠ ⊤ ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
        TwoScale.S36Events.pointSphereDist p.1 p.2.1 (δ * r) ≤
          ENNReal.ofReal (δ ^ θ) * p.2.2} =
      {p : LoopInput | p.2.2 ≠ ⊤ ∧
      ∀ q : ℚ, 0 < (q : ℝ) → (q : ℝ) ≤ δ₀ →
        TwoScale.S36Events.pointSphereDist p.1 p.2.1 ((q : ℝ) * r) ≤
          ENNReal.ofReal ((q : ℝ) ^ θ) * p.2.2} := by
    ext p
    constructor
    · rintro ⟨hp, hall⟩
      exact ⟨hp, (TwoScale.S36Events.point_loop_forall_iff_rat p.1 p.2.1 hθ hp).mp hall⟩
    · rintro ⟨hp, hall⟩
      exact ⟨hp, (TwoScale.S36Events.point_loop_forall_iff_rat p.1 p.2.1 hθ hp).mpr hall⟩
  rw [heq]
  exact hfin.inter hrat

end SupercriticalLQGUniqueness.Uniqueness.Measurability.AttainedEvents
