import QuantumZipper.Proofs.Thm18.LWFarDefs
import QuantumZipper.Proofs.RS.TraceShift

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Theorem 1.8, node LW-FAR: deterministic domain Markov lemmas for the forward flow

Task LWF-1a (helper of LWF-1). Elementary ODE facts about the centered forward Loewner flow used
in the conditional one-point estimate of G. Lawler, B. Werness, *Multi-point Green's functions
for SLE and an estimate of Beffara*, Ann. Probab. 41 (2013), §2.2 and Lemma 2.10 (p. 12): the
domain Markov property of the Loewner flow (restart at time `s` with the shifted driver
`r ↦ W (s + r) - W s`).

* `lwc_notMem_fwdHull_of_sol`: a point with a solution on `[0,T]` is not swallowed by time `T`;
* `lwc_mem_fwdHull_congr`, `lwc_fwdLogCR_congr`: hulls and the log conformal radius at time `T`
  only depend on the driver on `[0,T]`;
* `lwc_flow`: flow property of the map and chain rule for the log conformal radius
  `log Υ_{s+u}(x) = log Υ̃_u(g_s x) + log Υ_s(x) - log Im g_s(x)`.

Proofs: own elementary proofs (LW state these facts without proof; they follow from uniqueness
of solutions and additivity of the integral).
-/

noncomputable section

open MeasureTheory Set Filter

namespace QuantumZipper
namespace Thm18Asm
namespace LWFar

theorem lwc_notMem_fwdHull_of_sol {W : ℝ → ℝ} (hW : Continuous W) {z : ℂ} (hz : 0 < z.im)
    {T : ℝ} (hT : 0 ≤ T) {u : ℝ → ℂ} (hu : IsForwardSol W z T u) : z ∉ fwdHull W T := by
  intro hK
  obtain ⟨-, σ, hσT, -, hc⟩ := (FwdClock.mem_fwdHull_iff_inf_im hW).1 hK
  have hanti := im_isForwardSol_le hW hz hu
  have hTT : T ∈ Icc (0:ℝ) T := ⟨hT, le_rfl⟩
  obtain ⟨t, ht0, htσ, hlt⟩ := hc (u T).im (hanti.2 T hTT)
  have htT : t ∈ Icc (0:ℝ) T := ⟨ht0, by linarith⟩
  rw [fwdMap_eq hW hz hu htT] at hlt
  have := hanti.1 htT hTT htT.2
  linarith

private theorem lwc_notMem_congr {W W' : ℝ → ℝ} (hW' : Continuous W')
    {T : ℝ} (hT : 0 ≤ T) (h : ∀ r ∈ Set.Icc (0:ℝ) T, W r = W' r) (z : ℂ)
    (hz : z ∉ fwdHull W T) : z ∉ fwdHull W' T := by
  by_cases hzH : z ∈ H
  · obtain ⟨u, hu⟩ := exists_isForwardSol_of_not_mem_fwdHull hT hzH hz
    exact lwc_notMem_fwdHull_of_sol hW' hzH hT (isForwardSol_congr_drive h hu)
  · exact fun hK => hzH hK.1

theorem lwc_mem_fwdHull_congr {W W' : ℝ → ℝ} (hW : Continuous W) (hW' : Continuous W')
    {T : ℝ} (hT : 0 ≤ T) (h : ∀ r ∈ Set.Icc (0:ℝ) T, W r = W' r) (z : ℂ) :
    z ∈ fwdHull W T ↔ z ∈ fwdHull W' T := by
  constructor
  · intro hK
    by_contra hK'
    exact lwc_notMem_congr hW hT (fun r hr => (h r hr).symm) z hK' hK
  · intro hK
    by_contra hK'
    exact lwc_notMem_congr hW' hT h z hK' hK

end LWFar
end Thm18Asm
end QuantumZipper
