/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SfPullback
import InteractingSLE.Spec.Supplement.GW2RdTop

/-!
# Bad-boundary avoidance in GW2's retained coordinates

Packet PROVE-GW2-SAFE. The returned initial data and the untouched-boundary
word formula identify the physical and relative bad-boundary obstruction.
The argument includes real seed and junction points by closure.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex MeasureTheory
open QuantumZipper (H Hbar chiC)
open LQGMetric (DistOn)

namespace InteractingSLE.Theorem14.GW2Sf

open Restart Exist.StagedLaw Sec7.StripSysField Supp8 Supp8.GB6 Supp8.GB6.CoordB Q3Rel GW2Rd

/-- The bad-boundary set has no interior points. -/
theorem notMem_hitSet_of_mem_H {κ θ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {p : ℂ}
    (hp : p ∈ H) : p ∉ hitSet κ b J θ := by
  intro h
  obtain ⟨y, -, rfl⟩ := exists_real_of_mem_closure_ofReal h
  simp only [QuantumZipper.H, mem_ofPred_eq, ofReal_im, lt_self_iff_false] at hp

/-- Returned boundary data preserve bad-boundary avoidance under the
extended chart, including at the finitely many exceptional coordinates. -/
theorem notMem_hitSet_relBdry_of_returnData {κ k θ : ℝ} (hκ : 0 < κ) (hk : 0 < k)
    {b : ℝ → ℝ} {J : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b J)
    (c : BoundaryWord) (r : RecData)
    (hdata : ∀ x : ℝ, x ∉ J → x ≠ 0 → -x⁻¹ ∉ c.jumps →
      b x = returnData (Real.pi * chiC k) (chiC k) c.fn x)
    {p : ℂ} (hp : p ∈ relSafe (rdrv r) (rtime r)) (hbad : p ∉ hitSet κ b J θ) :
    relBdry (rdrv r) (rtime r) p ∉
      hitSet κ (upW (θ * chiC κ) (gb6WordOfRec k 0 c r)).fn
        (upW (θ * chiC κ) (gb6WordOfRec k 0 c r)).jumps 0 := by
  have hU := continuous_rdrv r
  have hU0 := rdrv_zero r
  have hs := rtime_nonneg r
  by_cases hpH : p ∈ H
  · exact notMem_hitSet_of_mem_H ((relBdry_mem_H_iff hU hU0 hs hp).2 hpH)
  have him : p.im = 0 := le_antisymm (not_lt.1 hpH) hp.1
  have he : p = (p.re : ℂ) := Complex.ext rfl (by simpa only [ofReal_im] using him)
  rw [he] at hp hbad ⊢
  obtain ⟨δ, hδ, hδball⟩ := Metric.isOpen_iff.1
    ((isClosed_closure (s := invHull (rdrv r) (rtime r))).union
      (isClosed_hitSet (κ := κ) (b := b) (J := J) (θ := θ))).isOpen_compl
    (p.re : ℂ) (not_or.2 ⟨hp.2, hbad⟩)
  have hA : ball (p.re : ℂ) δ ⊆ (closure (invHull (rdrv r) (rtime r)))ᶜ :=
    fun z hz h => hδball hz (Or.inl h)
  have hB : ball (p.re : ℂ) δ ⊆ (hitSet κ b J θ)ᶜ :=
    fun z hz h => hδball hz (Or.inr h)
  let E : Set ℝ := ({0} ∪ (J : Set ℝ)) ∪ (fun y : ℝ => -y⁻¹) '' (c.jumps : Set ℝ)
  have hE : E.Finite := ((finite_singleton 0).union J.finite_toSet).union (c.jumps.finite_toSet.image _)
  have hE0 : (0 : ℝ) ∈ E := Or.inl (Or.inl rfl)
  have hEJ : (J : Set ℝ) ⊆ E := fun _ hy => Or.inl (Or.inr hy)
  have hEInv {u : ℝ} (hu : u ∉ E) : -u⁻¹ ∉ c.jumps := by
    intro h
    exact hu (Or.inr ⟨-u⁻¹, h, neg_inv_neg_inv_real u⟩)
  refine notMem_hitSet_of_boundary_chart hκ hb (upW (θ * chiC κ) (gb6WordOfRec k 0 c r)).isPiecewiseConstantBoundaryData
    hδ (isRealBoundaryConformal_relBdry hU hU0 hs hA) hB hE hEJ ?_ ?_
  · intro u huI huE
    have hu0 : u ≠ 0 := fun h => huE (h.symm ▸ hE0)
    exact relBdry_real_sign hU hU0 hs hu0
      (hA (Sec7.Aux37Side.ofReal_mem_ball_iff.2 huI))
  · intro u huI huE huJR
    have hu0 : u ≠ 0 := fun h => huE (h.symm ▸ hE0)
    change (gb6WordOfRec k 0 c r).fn (relBdry (rdrv r) (rtime r) u).re + θ * chiC κ = _
    rw [gb6WordOfRec_fn_relBdry hk c r hu0
      (hA (Sec7.Aux37Side.ofReal_mem_ball_iff.2 huI)) (hEInv huE) huJR,
      ← hdata u (fun h => huE (hEJ h)) hu0 (hEInv huE)]

/-- The original flow data are the return of the counterflow data. This is
the existing GFF boundary-data identity at the dual parameter. -/
theorem data_eq_returnData_gw2 {κ : ℝ} (hκ : 0 < κ)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h h' : Ω → DistOn upperHalfPlaneOpens} {b b' : ℝ → ℝ} {J J' : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b J) (hG : IsGFFWithBoundaryData P h b J)
    (hb' : IsPiecewiseConstantBoundaryData b' J') (hG' : IsGFFWithBoundaryData P h' b' J')
    (hT : ∀ ω, IsChartTransport infinitySourceChart (-1) (-(Real.pi * chiC κ))
      (chiC (16 / κ)) (h ω) (h' ω))
    (c' : BoundaryWord) (hc'J : c'.jumps = J') (hc'b : ∀ y ∉ J', c'.fn y = b' y)
    {x : ℝ} (hxJ : x ∉ J) (hx0 : x ≠ 0) (hxJ' : -x⁻¹ ∉ c'.jumps) :
    b x = returnData (Real.pi * chiC (16 / κ)) (chiC (16 / κ)) c'.fn x := by
  have hk : 0 < 16 / κ := by positivity
  have hd := data_eq_returnData hk hb' hG' hb hG (fun ω => GW2Fb.isChartTransport_dual hκ (hT ω))
    hxJ hx0 (hc'J ▸ hxJ')
  rw [returnData] at hd ⊢
  rw [hc'b _ (hc'J ▸ hxJ')]
  exact hd

end InteractingSLE.Theorem14.GW2Sf
