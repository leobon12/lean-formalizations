import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCOrientedCornerCrosscutOriented
import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCCornerPaidCrosscut

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Metric
namespace SupercriticalLQGUniqueness.B2.DG20Conc
open LQGMetric LQGMetric.DDDF

 



theorem laneC_upper_left_paid_square_crosscut_oriented
    (D : ContMetric) {ρ : ℝ → ℂ} {a b : ℝ}
    (hab : a ≤ b) (hρ : ContinuousOn ρ (Icc a b))
    {c v : ℂ} {r : ℝ} (hr : 0 < r)
    (hρann : ∀ x ∈ Icc a b,
      r < dist (ρ x) c ∧ dist (ρ x) c < 2 * r)
    (hv : 2 * r ≤ dist v c)
    (hsep : LQGMetric.Disconnects (ρ '' Icc a b)
      (sphere c r) (sphere c (2 * r)))
    (hcre0 : 0 ≤ c.re) (hcreNear : c.re ≤ r)
    (hcim1 : c.im ≤ 1) (hTopNear : 1 - c.im ≤ r)
    (hbelow : 2 * r ≤ c.im) (hright : c.re + 2 * r ≤ 1) :
    ∃ α : ℝ → ℂ,
      ContinuousOn α (Icc (0 : ℝ) 1) ∧
      (∀ u ∈ Icc (0 : ℝ) 1,
        r < dist (α u) c ∧ dist (α u) c < 2 * r ∧
          α u ∈ (rectAB 1 1).toSet) ∧
      α 0 ∈ (rectAB 1 1).side₁ ∧
      (α 1).im = 1 ∧
      (α 0).im ≤ c.im ∧ c.re ≤ (α 1).re ∧
      D.len α 0 1 ≤ D.len ρ a b := by
  obtain ⟨τ, hτ, hτann, hτclosed, hτcost, G, hG, hGdef, hGdeg⟩ :=
    laneC_exists_paid_essential_loop D hab hρ hr hρann hv hsep
  obtain ⟨M, hMexp⟩ := QuantumZipper.CA.Topo.exists_lift_exp G hG
  have hGclosed : G 0 = G 1 := by
    rw [hGdef, hGdef]
    simpa using congrArg (fun z : ℂ => z - c) hτclosed
  have hperiod := laneC_nonzero_loop_lift_period
    G hG hGclosed hGdeg M.continuous hMexp
  let Mr : C(ℝ, ℂ) := ContinuousMap.IccExtend (zero_le_one' ℝ) M
  have hMr : ContinuousOn (fun x : ℝ => Mr x) (Icc (0 : ℝ) 1) :=
    Mr.continuous.continuousOn
  have hMrexp : ∀ x ∈ Icc (0 : ℝ) 1,
      Complex.exp (Mr x) = τ x - c := by
    intro x hx
    have hval : Mr x = M ⟨x, hx⟩ :=
      Set.IccExtend_of_mem (zero_le_one' ℝ) M hx
    rw [hval, hMexp, hGdef]
  have hMr0 : Mr 0 = M 0 := by
    change Set.IccExtend (zero_le_one' ℝ) M 0 = M 0
    exact Set.IccExtend_of_mem (zero_le_one' ℝ) M
      (show (0 : ℝ) ∈ Icc 0 1 by simp)
  have hMr1 : Mr 1 = M 1 := by
    change Set.IccExtend (zero_le_one' ℝ) M 1 = M 1
    exact Set.IccExtend_of_mem (zero_le_one' ℝ) M
      (show (1 : ℝ) ∈ Icc 0 1 by simp)
  have hperiodr : 2 * Real.pi ≤ (Mr 1 - Mr 0).im ∨
      (Mr 1 - Mr 0).im ≤ -(2 * Real.pi) := by
    simpa only [hMr0, hMr1] using hperiod
  obtain ⟨α, hα, hαann, hαleft, hαtop, hαbelow, hαright, hαcost⟩ :=
    laneC_oriented_corner_paid_crosscut_oriented D hτ hτclosed hτann
      hcre0 hcreNear hcim1 hTopNear hbelow hright hMr hMrexp hperiodr
  exact ⟨α, hα, hαann, hαleft, hαtop, hαbelow, hαright, hαcost.trans hτcost⟩

end SupercriticalLQGUniqueness.B2.DG20Conc
