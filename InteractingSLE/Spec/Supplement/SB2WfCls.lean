/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2WfTip

/-!
# The real boundary values of the inverse Loewner map

Packet PROVE-T14-SB2WORD (round 3, the junction fact of E7). For a Loewner trace `γ` of a continuous driver `W` from
`0`, continuous on `[0, τ]` (`τ > 0`), every real boundary value `z = F̄_τ(r)` of the inverse map at a real point `r`
is either an alive real point (a forward solution from `z` survives to `τ`, with value `r` at `τ`: `r = f_τ(z)`) or a
real point of the trace `γ([0, τ])` (`bdry_cases`).

Proof: `z` is a limit of points of `ℍ \ K_τ`. If it lies in the closed hull `closure (fill γ[0, τ])`, it is a frontier
point there, hence on the trace (Yuan's `mem_of_mem_closure_of_mem_frontier`). Otherwise it is alive, and the forward
map, continuous at `z` from `ℍ`, sends the values `F_τ(w)` back to `w → r`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Set Topology Metric
open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull IsForwardSol)

namespace InteractingSLE.Theorem14.SB.Wf

/-- **Alive or on the trace.** -/
theorem bdry_cases {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {τ : ℝ} (hτ : 0 < τ) {γ : ℝ → ℂ}
    (hγ : IsLoewnerTraceLT W τ γ) (hγc : ContinuousOn γ (Icc 0 τ)) {r : ℝ}
    (hreal : (extendFrom H (fwdMapInv W τ) r).im = 0) :
    ((extendFrom H (fwdMapInv W τ) r).re ≠ 0 ∧
      ∃ v : ℝ → ℂ, IsForwardSol W ((extendFrom H (fwdMapInv W τ) r).re : ℂ) τ v ∧ v τ = r) ∨
      extendFrom H (fwdMapInv W τ) r ∈ γ '' Icc 0 τ := by
  set z := extendFrom H (fwdMapInv W τ) r with hz
  have hB := TraceClose.hasBdryLimits_of_isLoewnerTraceLT hγ hW hW0 hτ hγc
  have hlim : Tendsto (fwdMapInv W τ) (𝓝[H] (r : ℂ)) (𝓝 z) := hB.tendsto (show ((r : ℂ)) ∈ Hbar by simp [Hbar])
  have hNr : (𝓝[H] (r : ℂ)).NeBot := Theorem14.GW1P.neBot_nhdsWithin_H (by simp [Hbar])
  have hzr : z = ((z.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hreal])
  have hzc : z ∈ closure (H \ fwdHull W τ) :=
    mem_closure_of_tendsto hlim (eventually_nhdsWithin_of_forall fun w hw =>
      QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hW hW0 hτ.le hw)
  have hKeq := TraceClose.fwdHull_eq_fillH_of_isLoewnerTraceLT hγ hW hW0 hτ hγc
  have hPc : IsClosed (γ '' Icc 0 τ) := (isCompact_Icc.image_of_continuousOn hγc).isClosed
  by_cases hK : z ∈ closure (fwdHull W τ)
  · right
    rw [hKeq] at hK hzc
    refine YuanCharacterisation.mem_of_mem_closure_of_mem_frontier hPc hreal hK ⟨hzc, fun hint => ?_⟩
    have := (interior_subset hint).1
    exact absurd hreal (ne_of_gt this)
  · by_cases hz0 : z.re = 0
    · right
      have hz0' : z = γ 0 := by rw [hzr, hz0, hγ.1]; simp
      exact ⟨0, ⟨le_rfl, hτ.le⟩, hz0'.symm⟩
    · left
      refine ⟨hz0, ?_⟩
      obtain ⟨v, hv⟩ := Supp8.BHMean.exists_isForwardSol_of_notMem_closure hW hW0 hτ.le
        (by rw [← hzr]; exact hK) hz0
      refine ⟨v, hv, ?_⟩
      have hY := tendsto_fwdMap_of_isForwardSol_real hW hW0 hτ.le hv
      have hlimH : Tendsto (fwdMapInv W τ) (𝓝[H] (r : ℂ)) (𝓝[H] ((z.re : ℝ) : ℂ)) :=
        tendsto_nhdsWithin_iff.2 ⟨by rw [← hzr]; exact hlim, eventually_nhdsWithin_of_forall fun w hw =>
          QuantumZipper.RS.fwdMapInv_mem_H hW hW0 hτ.le hw⟩
      have h1 : Tendsto (fun w => fwdMap W τ (fwdMapInv W τ w)) (𝓝[H] (r : ℂ)) (𝓝 (v τ)) := hY.comp hlimH
      have h2 : Tendsto (fun w => fwdMap W τ (fwdMapInv W τ w)) (𝓝[H] (r : ℂ)) (𝓝 (r : ℂ)) :=
        (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).congr'
          (eventually_nhdsWithin_of_forall fun w hw => (QuantumZipper.RS.fwdMap_fwdMapInv hW hW0 hτ.le hw).symm)
      exact tendsto_nhds_unique h1 h2

end InteractingSLE.Theorem14.SB.Wf
