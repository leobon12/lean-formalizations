import SupercriticalLQGUniqueness.Uniqueness.Objects.Network.EventNetwork
import SupercriticalLQGUniqueness.Uniqueness.Objects.TubeLoops.Loop
import LQGMetric.Topo.Shortcut




 





set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Network
open SupercriticalLQGUniqueness.Uniqueness.Objects.CorrectedEvent

 
theorem range_pathOfIcc_eq (P : ℝ → ℂ) {a b : ℝ} (hab : a ≤ b)
    (hP : ContinuousOn P (Icc a b)) :
    range (LQGMetric.pathOfIcc P hab hP) = P '' Icc a b := by
  refine Subset.antisymm (LQGMetric.range_pathOfIcc_subset P hab hP) ?_
  rintro z ⟨s, hs, rfl⟩
  by_cases heq : a = b
  · have hsa : s = a := le_antisymm (heq ▸ hs.2) hs.1
    subst s
    refine ⟨0, ?_⟩
    simp [LQGMetric.pathOfIcc]
  · have hlt : a < b := lt_of_le_of_ne hab heq
    have hden : 0 < b-a := sub_pos.mpr hlt
    let v : unitInterval := ⟨(s-a)/(b-a), by
      constructor
      · exact div_nonneg (sub_nonneg.mpr hs.1) hden.le
      · exact (div_le_one hden).mpr (by linarith [hs.2])⟩
    refine ⟨v, ?_⟩
    change P (a + (b-a) * ((v : unitInterval) : ℝ)) = P s
    congr 1
    dsimp [v]
    field_simp
    ring


 


theorem paid_separators_meet (D : LSCMetric)
    {x x' : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hd1 : ρ ≤ dist x x') (hd2 : dist x x' ≤ 2*ρ)
    {P P' : ℝ → ℂ} {a b a' b' : ℝ}
    (hCurve' : D.IsCurve P' a' b')
    (hEucl' : ContinuousOn P' (Icc a' b'))
    (hAnn' : P' '' Icc a' b' ⊆ ann x' ρ (2*ρ))
    (hSep : LQGMetric.Disconnects (P '' Icc a b)
      (sphere x ρ) (sphere x (2*ρ)))
    (hSep' : LQGMetric.Disconnects (P' '' Icc a' b')
      (sphere x' ρ) (sphere x' (2*ρ))) :
    ((P '' Icc a b) ∩ (P' '' Icc a' b')).Nonempty := by
  let π := LQGMetric.pathOfIcc P' hCurve'.1 hEucl'
  have hRange : range π = P' '' Icc a' b' :=
    range_pathOfIcc_eq P' hCurve'.1 hEucl'
  have hA : ∀ t, ρ < dist (π t) x' ∧ dist (π t) x' < 2*ρ := by
    intro t
    exact hAnn' (hRange ▸ ⟨t, rfl⟩)
  have hD : LQGMetric.Disconnects (range π)
      (sphere x' ρ) (sphere x' (2*ρ)) := by
    rw [hRange]
    exact hSep'
  obtain ⟨p, hp, hp'⟩ := Objects.TubeLoops.loops_meet hρ hd1 hd2 hSep π hA hD
  exact ⟨p, hp, hRange ▸ hp'⟩


 



theorem event_linked_paid_traces {C : Constants} {T : TubeData}
    {hData : DataMatch C T} {F : ℂ → LQGMetric.DistC → Prop}
    {D D' : LQGMetric.DistC → LSCMetric} {g : LQGMetric.DistC}
    (h : correctedEvent C T hData F D D' g)
    (hU : tubeSet T ⊆ ball 0 (2.5*C.r))
    (hEucl : ∀ (P : ℝ → ℂ) (a b : ℝ),
      (D g).IsCurve P a b → ((D g).len P a b < ∞) →
        ContinuousOn P (Icc a b)) :
    ∃ (P : T.netSites → ℝ → ℂ) (t u : T.netSites → ℝ),
      (∀ x : T.netSites,
        (D g).IsCurve (P x) (t x) (u x) ∧
        (P x) '' Icc (t x) (u x) ⊆
          ann (x : ℂ) T.netRadius (2*T.netRadius) ∧
        (P x) '' Icc (t x) (u x) ⊆ tubeSet T ∧
        LQGMetric.Disconnects ((P x) '' Icc (t x) (u x))
          (sphere (x : ℂ) T.netRadius)
          (sphere (x : ℂ) (2*T.netRadius)) ∧
        (D g).len (P x) (t x) (u x) <
          ENNReal.ofReal (C.A_internal / (2*T.netSites.card)) *
            normalizer C g C.r 0) ∧
      LQGMetric.Disconnects
        (⋃ x : T.netSites, (P x) '' Icc (t x) (u x))
        (closedBall 0 (1.5*C.r)) (ball 0 (2.5*C.r))ᶜ ∧
      (∀ y ∈ closure (tubeSet T),
        ∃ p ∈ ⋃ x : T.netSites, (P x) '' Icc (t x) (u x),
          dist y p < C.A_set*C.r) ∧
      (∀ x y : T.netSites,
        T.netRadius < dist (x : ℂ) y →
        dist (x : ℂ) y < 2*T.netRadius →
        (((P x) '' Icc (t x) (u x)) ∩
          ((P y) '' Icc (t y) (u y))).Nonempty) := by
  obtain ⟨P, t, u, hTrace, hBarrier, hDense⟩ :=
    event_paid_trace_barrier h hU
  refine ⟨P, t, u, hTrace, hBarrier, hDense, ?_⟩
  have hρ : 0 < T.netRadius := by
    unfold DataMatch at hData
    tauto
  have hBudget : ENNReal.ofReal (C.A_internal / (2*T.netSites.card)) *
      normalizer C g C.r 0 < ∞ := by
    apply ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    unfold normalizer
    exact ENNReal.ofReal_lt_top
  intro x y hxy1 hxy2
  have hcont : ContinuousOn (P y) (Icc (t y) (u y)) :=
    hEucl (P y) (t y) (u y) (hTrace y).1
      ((hTrace y).2.2.2.2.trans hBudget)
  exact paid_separators_meet (D g) hρ hxy1.le hxy2.le
    (hTrace y).1 hcont (hTrace y).2.1
    (hTrace x).2.2.2.1 (hTrace y).2.2.2.1


end SupercriticalLQGUniqueness.Uniqueness.Objects.Network
