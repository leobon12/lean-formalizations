import SupercriticalLQGUniqueness.Uniqueness.Objects.BlockCoding.ShieldPathInternal




 


set_option autoImplicit false
noncomputable section

open Set Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.BlockCoding

 

theorem internal_lt_len_of_far_path (D : LSCMetric) (z : ℂ) (t : ℝ)
    (ht : 0 < t) (W : Set ℂ) (hW : ball z (3 * t) ⊆ W)
    (hcheap : Objects.CorrectedEvent.around D z t (2 * t) < Objects.CorrectedEvent.acr D z (2 * t) (3 * t))
    {x y : ℂ} (hx : x ∈ closedBall z t) (hy : y ∈ closedBall z t)
    (γ : Path x y) (hγ : D.IsCurve γ.extend 0 1)
    (hfin : D.len γ.extend 0 1 < ⊤)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Icc (0 : ℝ) 1)
    (hfar : 3 * t ≤ dist (γ.extend t₀) z) :
    D.internal W
      (⟨x, hW (by rw [mem_ball]; exact (mem_closedBall.mp hx).trans_lt (by linarith))⟩,
       ⟨y, hW (by rw [mem_ball]; exact (mem_closedBall.mp hy).trans_lt (by linarith))⟩) <
      D.len γ.extend 0 1 := by
  obtain ⟨π, a, b, hπ, hπtrace, hπdis, hπlen⟩ :=
    exists_shield_loop D z t hcheap
  let T : Set ℂ := π '' Icc a b
  have hTclosed : IsClosed T := hπ.isClosed_image
  have hTann : T ⊆ {w | t < dist w z ∧ dist w z < 2 * t} := by
    intro w hw
    exact hπtrace hw
  obtain ⟨τa, τb, h0a, hat₀, ht₀b, hb1, hhitA, hhitB,
      hbefore, hafter, c, d, hac, hcd, hdt₀, hc2, hd3, hcrossTrace⟩ :=
    Objects.Blocks.shield_hits ht hTclosed hTann hπdis γ hx hy ht₀ hfar
  have h0b : 0 ≤ τb := le_trans h0a (le_trans (le_of_lt hat₀) (le_of_lt ht₀b))
  have hab : τa ≤ τb := (le_of_lt hat₀).trans (le_of_lt ht₀b)
  have hτa1 : τa ≤ 1 := hab.trans hb1
  have hτb0 : 0 ≤ τb := h0b
  have hW2 : ball z (2 * t) ⊆ W := by
    intro w hw
    apply hW
    rw [mem_ball] at hw ⊢
    exact hw.trans (by linarith)
  have hπW : ∀ s ∈ Icc a b, π s ∈ W := by
    intro s hs
    apply hW2
    rw [mem_ball]
    exact (hTann (show π s ∈ T from ⟨s, hs, rfl⟩)).2
  obtain ⟨σa, hσa, hσaEq⟩ := hhitA
  obtain ⟨σb, hσb, hσbEq⟩ := hhitB
  have hAin : γ.extend τa ∈ W := hW2 (mem_ball.mpr
    (hTann (show γ.extend τa ∈ T from ⟨σa, hσa, hσaEq⟩)).2)
  have hBin : γ.extend τb ∈ W := hW2 (mem_ball.mpr
    (hTann (show γ.extend τb ∈ T from ⟨σb, hσb, hσbEq⟩)).2)
  have hloop : D.internal W
      (⟨γ.extend τa, hAin⟩, ⟨γ.extend τb, hBin⟩) ≤ D.len π a b := by
    simpa only [hσaEq, hσbEq] using
      (internal_le_loop_length D W π a b hπ hπW hσa hσb)
  have hprecurve : D.IsCurve γ.extend 0 τa :=
    isCurve_subinterval D γ.extend hγ le_rfl h0a hτa1
  have hpretrace : ∀ s ∈ Icc 0 τa, γ.extend s ∈ W :=
    fun s hs => hW2 (mem_ball.mpr (hbefore s hs))
  have hpre : D.internal W
      (⟨x, hW (by rw [mem_ball]; exact (mem_closedBall.mp hx).trans_lt (by linarith))⟩,
       ⟨γ.extend τa, hAin⟩) ≤ D.len γ.extend 0 τa := by
    simpa only [γ.extend_zero] using
      (internal_le_len_curve D W γ.extend 0 τa hprecurve hpretrace)
  have hsufcurve : D.IsCurve γ.extend τb 1 :=
    isCurve_subinterval D γ.extend hγ hτb0 hb1 le_rfl
  have hsuftrace : ∀ s ∈ Icc τb 1, γ.extend s ∈ W :=
    fun s hs => hW2 (mem_ball.mpr (hafter s hs))
  have hsuf : D.internal W
      (⟨γ.extend τb, hBin⟩,
       ⟨y, hW (by rw [mem_ball]; exact (mem_closedBall.mp hy).trans_lt (by linarith))⟩) ≤
      D.len γ.extend τb 1 := by
    simpa only [γ.extend_one] using
      (internal_le_len_curve D W γ.extend τb 1 hsufcurve hsuftrace)
  have hcrosscurve : D.IsCurve γ.extend c d :=
    isCurve_subinterval D γ.extend hγ
      (h0a.trans hac) hcd.le (hdt₀.trans (le_of_lt ht₀b) |>.trans hb1)
  have hcrossCarrier : γ.extend '' Icc c d ⊆ Objects.CorrectedEvent.cann z (2 * t) (3 * t) := by
    rintro w ⟨s, hs, rfl⟩
    exact hcrossTrace s hs
  have hcrossCost : Objects.CorrectedEvent.acr D z (2 * t) (3 * t) ≤
      D.len γ.extend c d := by
    apply acr_le_crossing D z t γ.extend c d hcrosscurve hcrossCarrier
    · exact mem_sphere.mpr hc2
    · exact mem_sphere.mpr hd3
  have hcrossFull : Objects.CorrectedEvent.acr D z (2 * t) (3 * t) ≤
      D.len γ.extend τa τb :=
    hcrossCost.trans (len_subinterval_le D γ.extend hac hcd.le
      (hdt₀.trans (le_of_lt ht₀b)))
  have hpaid : D.len γ.extend 0 τa + D.len γ.extend τa τb +
      D.len γ.extend τb 1 = D.len γ.extend 0 1 := by
    change LQGMetric.MetricGeometry.curveLength (D.pt ∘ γ.extend) 0 τa +
      LQGMetric.MetricGeometry.curveLength (D.pt ∘ γ.extend) τa τb +
      LQGMetric.MetricGeometry.curveLength (D.pt ∘ γ.extend) τb 1 =
      LQGMetric.MetricGeometry.curveLength (D.pt ∘ γ.extend) 0 1
    rw [add_assoc,
      LQGMetric.MetricGeometry.curveLength_add _ hab hb1,
      LQGMetric.MetricGeometry.curveLength_add _ h0a (hab.trans hb1)]
  have hlocal : D.internal W
      (⟨x, hW (by rw [mem_ball]; exact (mem_closedBall.mp hx).trans_lt (by linarith))⟩,
       ⟨y, hW (by rw [mem_ball]; exact (mem_closedBall.mp hy).trans_lt (by linarith))⟩) ≤
      D.len γ.extend 0 τa + D.len π a b + D.len γ.extend τb 1 :=
    three_costs (D.internal W) (D.isExtMetric_internal W)
      _ _ _ _ _ _ _ hpre hloop hsuf
  exact hlocal.trans_lt (strict_surgery_sum hfin hπlen hcrossFull hpaid.le)

end SupercriticalLQGUniqueness.Uniqueness.Objects.BlockCoding
