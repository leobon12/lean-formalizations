/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBS3PrimeAlphabet
import InteractingSLE.Spec.Supplement.SB2WdLaunch

/-!
# S3: physical provenance through a stopped word

Interior boundary landings inherit old side heights or one of the two new
side heights. The old coordinate is selected off its finite marks using
continuity of the physical readout and real Loewner flow. The exact boundary
transport identity remains an explicit deterministic hypothesis; the theorem
does not infer physical provenance from the numerical alphabet alone.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H IsForwardSol fwdMap chiC)

namespace InteractingSLE.Theorem14.SB.S3

open Exist Exist.Staged Exist.StagedLaw Restart GW1W GW1Conn

/-- At an unmarked stopped-word coordinate with an alive old preimage,
physical interior provenance transfers from an unmarked nearby old point.
The nearby point avoids even redundant old marks. -/
theorem stopWord_interior_of_alive {κ : ℝ} (hκ : 0 < κ) {c : BoundaryWord}
    {θ : ℝ} {r : RecData} {P : ℝ → Prop} {gOld gNew : ℝ → ℂ}
    (hgc : Continuous gOld)
    (hOld : ∀ x ∉ c.jumps, gOld x ∈ H → P (c.fn x))
    (hBoundaryTransport : ∀ x : ℝ, x ≠ 0 →
      (∃ u, IsForwardSol (rdrv r) (x : ℂ) (rtime r) u) →
        gOld x = gNew (fwdMap (rdrv r) (rtime r) x).re)
    {x y : ℝ} (hx : x ≠ 0)
    (hAlive : ∃ u, IsForwardSol (rdrv r) (x : ℂ) (rtime r) u)
    (hxy : (fwdMap (rdrv r) (rtime r) x).re = y)
    (hy : y ∉ (stopWord κ (c, θ, r)).jumps) (hyH : gNew y ∈ H) :
    P ((stopWord κ (c, θ, r)).fn y) := by
  let f : ℝ → ℝ := fun t => (fwdMap (rdrv r) (rtime r) t).re
  have hfc : ContinuousAt f x := by
    obtain ⟨u, hu⟩ := hAlive
    have he := ZhanGT4.A1G3L2.continuousAt_fwdMap_of_isForwardSol
      (show rtime r < rtime r + 1 by linarith) (rtime_nonneg r)
      (continuous_rdrv r).continuousOn hu
    exact Complex.continuous_re.continuousAt.comp
      (he.comp Complex.continuous_ofReal.continuousAt)
  have hxH : gOld x ∈ H := by rw [hBoundaryTransport x hx hAlive, hxy]; exact hyH
  have hH : ∀ᶠ t in 𝓝 x, gOld t ∈ H :=
    hgc.continuousAt.eventually (QuantumZipper.isOpen_H.mem_nhds hxH)
  have hvalue : ∀ᶠ t in 𝓝 x,
      f t ∉ (stopWord κ (c, θ, r)).jumps ∧
        (stopWord κ (c, θ, r)).fn (f t) = (stopWord κ (c, θ, r)).fn y := by
    have hJ := hfc.eventually
      (((stopWord κ (c, θ, r)).jumps.finite_toSet.isClosed.isOpen_compl).mem_nhds
        (by change f x ∉ _; rw [show f x = y from hxy]; exact hy))
    have hv := hfc.eventually (by
      rw [show f x = y from hxy]
      exact (stopWord κ (c, θ, r)).isPiecewiseConstantBoundaryData y hy)
    exact hJ.and hv
  have hAvoid : ∀ᶠ t in 𝓝[≠] x, t ∉ c.jumps :=
    eventually_notMem_of_finite c.jumps.finite_toSet x
  have finish : ∀ t : ℝ, t ≠ 0 →
      (∃ u, IsForwardSol (rdrv r) (t : ℂ) (rtime r) u) → t ∉ c.jumps →
      gOld t ∈ H → f t ∉ (stopWord κ (c, θ, r)).jumps →
      (stopWord κ (c, θ, r)).fn (f t) = (stopWord κ (c, θ, r)).fn y →
      P ((stopWord κ (c, θ, r)).fn y) := by
    intro t ht htA htJ htH hftJ hval
    have he : (stopWord κ (c, θ, r)).fn (f t) = c.fn t := by
      rcases ht.lt_or_gt with ht0 | ht0
      · exact stopWord_fn_fwdMap_neg hκ c θ r ht0 htA htJ hftJ
      · exact stopWord_fn_fwdMap hκ c θ r ht0 htA htJ hftJ
    rw [← hval, he]
    exact hOld t htJ htH
  rcases hx.lt_or_gt with hx0 | hx0
  · have hEv : ∀ᶠ t in 𝓝[<] x, gOld t ∈ H ∧
        (f t ∉ (stopWord κ (c, θ, r)).jumps ∧
          (stopWord κ (c, θ, r)).fn (f t) = (stopWord κ (c, θ, r)).fn y) ∧ t ∉ c.jumps :=
      by
        simpa only [and_assoc] using
          (((hH.and hvalue).filter_mono nhdsWithin_le_nhds).and
            (hAvoid.filter_mono (nhdsWithin_mono x (show Iio x ⊆ ({x}ᶜ : Set ℝ) from fun _ ht => ne_of_lt ht))))
    obtain ⟨t, ⟨htH, ⟨hftJ, hval⟩, htJ⟩, htx⟩ := (hEv.and self_mem_nhdsWithin).exists
    have ht0 : t < 0 := htx.trans hx0
    have htA : ∃ u, IsForwardSol (rdrv r) (t : ℂ) (rtime r) u := by
      have hn := (isRealFlow_fwd (continuous_rdrv r) (rdrv_zero r) (rtime_nonneg r)).2
      have ha : ∃ u, IsForwardSol (rdrv r) (((-(-x) : ℝ)) : ℂ) (rtime r) u := by
        simpa only [neg_neg] using hAlive
      have hb := hn.2.1 (-x) (-t) (by linarith) (by linarith) ha
      simpa only [neg_neg] using hb
    exact finish t ht0.ne htA htJ htH hftJ hval
  · have hEv : ∀ᶠ t in 𝓝[>] x, gOld t ∈ H ∧
        (f t ∉ (stopWord κ (c, θ, r)).jumps ∧
          (stopWord κ (c, θ, r)).fn (f t) = (stopWord κ (c, θ, r)).fn y) ∧ t ∉ c.jumps :=
      by
        simpa only [and_assoc] using
          (((hH.and hvalue).filter_mono nhdsWithin_le_nhds).and
            (hAvoid.filter_mono (nhdsWithin_mono x (show Ioi x ⊆ ({x}ᶜ : Set ℝ) from fun _ ht => ne_of_gt ht))))
    obtain ⟨t, ⟨htH, ⟨hftJ, hval⟩, htJ⟩, htx⟩ := (hEv.and self_mem_nhdsWithin).exists
    have ht0 : 0 < t := hx0.trans htx
    have htA := (isRealHalf_of (continuous_rdrv r) (rdrv_zero r) (rtime_nonneg r)).2.1
      x t hx0 htx hAlive
    exact finish t ht0.ne' htA htJ htH hftJ hval

/-- Physical provenance for every nonzero unmarked stopped-word coordinate.
Either its value is a new side height, or it comes from an alive old point.
The physical readout identity is used before excluding original real data. -/
theorem stopWord_interior_values {κ : ℝ} (hκ : 0 < κ) {c : BoundaryWord}
    {θ : ℝ} {r : RecData} {P : ℝ → Prop} {gOld gNew : ℝ → ℂ}
    (hgc : Continuous gOld)
    (hOld : ∀ x ∉ c.jumps, gOld x ∈ H → P (c.fn x))
    (hBoundaryTransport : ∀ x : ℝ, x ≠ 0 →
      (∃ u, IsForwardSol (rdrv r) (x : ℂ) (rtime r) u) →
        gOld x = gNew (fwdMap (rdrv r) (rtime r) x).re)
    (hL : P (-sleLambda κ - θ * chiC κ)) (hR : P (sleLambda κ - θ * chiC κ))
    {y : ℝ} (hy0 : y ≠ 0) (hy : y ∉ (stopWord κ (c, θ, r)).jumps)
    (hyH : gNew y ∈ H) : P ((stopWord κ (c, θ, r)).fn y) := by
  rcases hy0.lt_or_gt with hy0 | hy0
  · by_cases hfirst : ∀ i < flowLineNL c.fn c.jumps 0,
        markPosL (rdrv r) (rtime r) ((padFL 0 0 c.fn c.jumps).1.1 i) < y
    · exact (stopWord_fn_first c θ r hy0 hy hfirst) ▸ hL
    · push Not at hfirst
      obtain ⟨i, hi, hiy⟩ := hfirst
      have hlt : y < markPosL (rdrv r) (rtime r) ((padFL 0 0 c.fn c.jumps).1.1 i) :=
        lt_of_le_of_ne hiy fun he => hy (he ▸ markPosL_mem_jumps_stopWord (κ := κ) c θ r hi)
      obtain ⟨q, hq, hqA, hqy⟩ := exists_rat_lt_of_lt_markPosL
        (continuous_rdrv r) (rdrv_zero r) (rtime_nonneg r) hlt
      have hq0 : (q : ℝ) < 0 := hq.trans_le (padFL_fst_fst_nonpos c hi)
      obtain ⟨x, hxq, hxA, hxy⟩ := exists_alive_eq_of_lt_re
        (continuous_rdrv r) (rdrv_zero r) (rtime_nonneg r) hq0 hqA hqy
      exact stopWord_interior_of_alive hκ hgc hOld hBoundaryTransport
        (hxq.trans hq0).ne hxA hxy hy hyH
  · rcases SB.Lh.stopWord_fn_pos_cases c θ r hy0 with he | hmark
    · exact he ▸ hR
    · obtain ⟨x, hx, hxA, hxy⟩ := SB.Lh.exists_alive_eq_of_markPos_lt
        (continuous_rdrv r) (rdrv_zero r) (rtime_nonneg r) hmark
      exact stopWord_interior_of_alive hκ hgc hOld hBoundaryTransport hx.ne' hxA hxy hy hyH

end InteractingSLE.Theorem14.SB.S3
