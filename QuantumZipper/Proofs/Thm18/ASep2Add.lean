import QuantumZipper.Proofs.Thm18.ASepDetA
import QuantumZipper.Proofs.Zipper.RegContMain
import QuantumZipper.Proofs.Zipper.JointModComm
import QuantumZipper.Proofs.GFF.CoordRegLog
import QuantumZipper.Proofs.Thm18.ASepPathDefs
import QuantumZipper.Proofs.Thm18.G1Z3AddFun
import QuantumZipper.Proofs.LQG.RegularSample

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ASEP2 (D1, layer 1): the unzipped field of `profile + free field`, profile by profile

The wedge sample is `ofFun prof_ω + X ω` with a profile `prof_ω` that depends on `X ω`
(ASepWedgeCongr). The fixed-profile free theorem (`ae_concl0_free`) therefore has to be upgraded
to a statement holding for **every** profile simultaneously. The first layer is the field identity
on the pushed dyadic circles: almost surely (fixed driver), for every profile `g` continuous off
`0` and every time `s ≥ 0`,

`coordChange (ofFun g + X) f_s⁻¹ Q (fc(d, 2^{-k})) = coordChange X f_s⁻¹ Q (fc(d, 2^{-k})) + ∫ g d ν_s`

whenever the pushed circle `ν_s = fc(d, 2^{-k}).map f_s⁻¹` stays in a compact subset of `Hbar`
avoiding `0` (`ae_coordChange_ofFun_add_all`). Inputs:

* the dyadic regularization of the free field converges at every pushed dyadic circle and every
  time (`tendsto_PsiK_of_uc`, from the uniform Cauchy property `RegCont.ae_UCq`: this is the
  first half of the proof of `ASep.continuousOn_evalReg_logAdd_of_uc`);
* additivity `evalReg (ofFun g + x) ν = evalReg x ν + ∫ g dν` for a regular sample `x`
  (`G1Z3.evalReg_add_ofFun_of_ae_z3`) with a continuous cutoff of `g` near `0` (`cutoffProf`).

Sources: Duplantier–Sheffield, Invent. Math. 185 (2011), Prop. 3.1 (through `RegCont.ae_UCq`);
the rest is own elementary bookkeeping (the paper treats `h + φ` for a continuous `φ` without
comment, Sheffield arXiv:1012.4797 §1.6).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology

namespace QuantumZipper
namespace ASep

open RegCont TwoPoint CoordReg FrostmanReg

/-! ## Convergence of the dyadic regularization at every pushed circle -/

/-- **Deterministic**: under the uniform Cauchy property over rational times, the dyadic
regularization of `x` converges at the pushed circle `ν_s` for **every** `s ∈ [0, T]`. -/
theorem tendsto_PsiK_of_uc {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ}
    (hT : 0 < T) (w : ℂ) {r : ℝ} (hr : 0 < r) {x : FieldSample} (hx : RegAvgGood x)
    (huc : UCq W w r T x) {s : ℝ} (hs : s ∈ Icc 0 T) :
    Tendsto (fun k => ∫ z, avgReg x k z ∂νT W w r s) atTop (𝓝 (evalReg x (νT W w r s))) := by
  set S := Icc (0 : ℝ) T with hS
  set Ψ : ℕ → ℝ → ℝ := fun k s => PsiK W w r s k x with hΨ
  have hΨc : ∀ k, ContinuousOn (Ψ k) S := fun k =>
    continuousOn_integral_νT hW hW0 T w hr (RegClosure.measurable_avgReg_slice x k) (hx k).1
  have hUC : ∀ n : ℕ, ∃ N : ℕ, ∀ k, N ≤ k → ∀ k', N ≤ k' → ∀ s ∈ S,
      |Ψ k s - Ψ k' s| ≤ 1 / ((n : ℝ) + 1) := by
    intro n
    obtain ⟨N, hN⟩ := huc n
    refine ⟨N, fun k hk k' hk' s hs => ?_⟩
    have hcont : ContinuousOn (fun s => |Ψ k s - Ψ k' s|) S := ((hΨc k).sub (hΨc k')).abs
    refine ContinuousWithinAt.closure_le (Icc_subset_closure_rat hT hs)
      ((hcont s hs).mono (inter_subset_left.trans Ioo_subset_Icc_self)) continuousWithinAt_const ?_
    rintro y ⟨hy, q, rfl⟩
    exact hN k hk k' hk' q (Ioo_subset_Icc_self hy)
  have hUCS : UniformCauchySeqOn Ψ atTop S := by
    rw [Metric.uniformCauchySeqOn_iff]
    intro ε hε
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    obtain ⟨N, hN⟩ := hUC n
    exact ⟨N, fun k hk k' hk' s hs => by rw [Real.dist_eq]; exact (hN k hk k' hk' s hs).trans_lt hn⟩
  exact (hUCS.cauchySeq hs).tendsto_limUnder

/-! ## Additivity for a profile continuous off `0` -/

/-- A continuous cutoff of a profile near `0`: `χ g` with `χ = 0` on `B(0, η/2)`, `χ = 1` off
`B(0, η)`. -/
def cutoffProf (g : ℂ → ℝ) (η : ℝ) : ℂ → ℝ :=
  fun v => min 1 (max 0 (2 * ‖v‖ / η - 1)) * g v

theorem cutoffProf_eq {g : ℂ → ℝ} {η : ℝ} (hη : 0 < η) {v : ℂ} (hv : η ≤ ‖v‖) :
    cutoffProf g η v = g v := by
  unfold cutoffProf
  have h1 : 1 ≤ 2 * ‖v‖ / η - 1 := by
    rw [le_sub_iff_add_le, le_div_iff₀ hη]; linarith
  rw [max_eq_right (by linarith), min_eq_left h1, one_mul]

theorem continuous_cutoffProf {g : ℂ → ℝ} (hg : ContinuousOn g {0}ᶜ) {η : ℝ} (hη : 0 < η) :
    Continuous (cutoffProf g η) := by
  have hχ : Continuous fun v : ℂ => min 1 (max 0 (2 * ‖v‖ / η - 1)) :=
    continuous_const.min (continuous_const.max
      (((continuous_const.mul continuous_norm).div_const η).sub continuous_const))
  rw [continuous_iff_continuousAt]
  intro v
  by_cases hv : ‖v‖ < η / 2
  · have hev : ∀ᶠ u in 𝓝 v, cutoffProf g η u = 0 := by
      filter_upwards [(continuous_norm.tendsto v).eventually (gt_mem_nhds hv)] with u hu
      unfold cutoffProf
      have : 2 * ‖u‖ / η - 1 ≤ 0 := by
        rw [sub_nonpos, div_le_one hη]; linarith
      rw [max_eq_left this, min_eq_right zero_le_one, zero_mul]
    have h0 : cutoffProf g η v = 0 := hev.self_of_nhds
    rw [ContinuousAt, h0]
    exact tendsto_const_nhds.congr' (hev.mono fun u hu => hu.symm)
  · have hv0 : v ≠ 0 := by
      intro h; rw [h, norm_zero] at hv; exact hv (by linarith)
    exact hχ.continuousAt.mul
      (hg.continuousAt (isOpen_compl_singleton.mem_nhds hv0))

end ASep
end QuantumZipper
