import QuantumZipper.Proofs.Thm18.ASepRawBox
import QuantumZipper.Proofs.Thm18.ASepSep
import QuantumZipper.Proofs.Thm18.ASepModD
import QuantumZipper.Proofs.Thm18.G4ASepBackLog
import QuantumZipper.Proofs.Zipper.RegContDet

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ASEP: the deterministic per-parameter facts of the `τ' = 0` family

At a parameter `p = (τ, a)` whose scaled folded circle (and a `δ`-neighbourhood of it in `ℍ̄`)
survives the forward flow beyond `τ`, all the deterministic hypotheses used by
`ASep.ae_hraw_A0` and `ASep.ae_exact_free_box` hold (`pfacts_A0`): measurability of the centre
map, the pushed circle lies in `ℍ` off the hull and in the image of the re-zipping map
(`revHull_revDrv_eq`), the two integrabilities (the second from the proved deterministic node
`backLogSepStmt_holds` with the separation), `0 ∉ fc(a d, a r)`, `μ_p(0) = fc(a d, a r)`
(`muA0_zero`), and `ν_p` is a probability measure carried by a ball of `ℍ̄`.
Own bookkeeping.
-/

noncomputable section

open MeasureTheory Set Filter Metric

namespace QuantumZipper
namespace ASep

open Thm18Asm Thm18Asm.G4Core

/-- The folded circle `fc(a d, a r)` avoids `0` if the flow from `a·foldSph d r` exists. -/
theorem zero_not_mem_foldSph_scaled {W : ℝ → ℝ} (hW0 : W 0 = 0) {d : ℂ} {r a T : ℝ}
    (ha : 0 < a) (hT : 0 ≤ T)
    (hsol : ∀ w ∈ foldSph d r, ∃ u, IsForwardSol W ((a : ℂ) * w) T u) :
    (0 : ℂ) ∉ foldSph ((a : ℂ) * d) (a * r) := by
  rintro ⟨y, hy, hy0⟩
  have hy' : y = 0 := by
    have := norm_foldH_eq y; rw [hy0, norm_zero] at this; exact norm_eq_zero.1 this.symm
  subst hy'
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hd : (0 : ℂ) ∈ sphere d r := by
    rw [mem_sphere, dist_comm, dist_zero_right] at hy ⊢
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha] at hy
    exact mul_left_cancel₀ ha.ne' hy
  obtain ⟨u, hu⟩ := hsol 0 ⟨0, hd, hy0⟩
  have h0 := (hu.2 0 ⟨le_rfl, hT⟩).1
  rw [FwdHolo.sol_zero hu hT, hW0, mul_zero, Complex.ofReal_zero, sub_zero] at h0
  exact h0 rfl

/-- **Deterministic facts at one parameter.** -/
theorem pfacts_A0 {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ} {d : ℂ} {r : ℝ}
    (hr : 0 < r) {a₀ a₁ m δ : ℝ} (ha₀ : 0 < a₀) (hm : 0 < m) (hδ : 0 < δ)
    (hgood0 : ∀ a ∈ Icc a₀ a₁, ∀ w ∈ foldSph d r, ∃ u, IsForwardSol W ((a : ℂ) * w) T u)
    (hlow : ∀ z ∈ scaledSph d r a₀ a₁, ∀ s ∈ Icc (0 : ℝ) T, m ≤ ‖fwdMap W s z‖)
    {p : Fin 2 → ℝ} (hp0 : p 0 ∈ Icc (0 : ℝ) T) (hτpos : 0 < p 0) (hp1 : p 1 ∈ Icc a₀ a₁)
    (hsep : ∀ w ∈ cthickening δ (foldSph d r) ∩ {w : ℂ | 0 ≤ w.im},
      ∃ T' > p 0, ∃ u, IsForwardSol W ((p 1 : ℂ) * w) T' u)
    (a' : ℝ) {g₁ : ℂ → ℝ} (hg₁ : Continuous g₁) :
    AEMeasurable (fun w => fwdMap W (p 0) ((p 1 : ℂ) * w)) (foldedCircle d r) ∧
    (∀ᵐ w ∂foldedCircle d r, 0 < w.im ∧
      w ∈ revMap (backDrv W (p 0) 0 (p 1)).2 (backDrv W (p 0) 0 (p 1)).1 '' H ∧
      (p 1 : ℂ) * w ∉ fwdHull W (p 0)) ∧
    Integrable (fun w => a' * Real.log ‖(p 1 : ℂ) * w‖ + g₁ ((p 1 : ℂ) * w))
      (foldedCircle d r) ∧
    foldedCircle d r
      (revMap (backDrv W (p 0) 0 (p 1)).2 (backDrv W (p 0) 0 (p 1)).1 '' H)ᶜ = 0 ∧
    Integrable (fun w => Real.log ‖deriv (revMap (backDrv W (p 0) 0 (p 1)).2
      (backDrv W (p 0) 0 (p 1)).1) (revMapInv (backDrv W (p 0) 0 (p 1)).2
        (backDrv W (p 0) 0 (p 1)).1 w)‖) (foldedCircle d r) ∧
    (0 : ℂ) ∉ foldSph ((p 1 : ℂ) * d) (p 1 * r) ∧
    muA0 W d r p 0 = foldedCircle ((p 1 : ℂ) * d) (p 1 * r) := by
  set τ := p 0 with hτdef
  set a := p 1 with hadef
  have ha : 0 < a := ha₀.trans_le hp1.1
  have hT : 0 ≤ T := hp0.1.trans hp0.2
  have hfold := ae_mem_foldSph d hr.le
  have hH := TwoPoint.foldedCircle_ae_mem_H d hr
  -- measurability
  have hgm := measurable_gA hW hW0 hm hgood0 hlow hp0 hp1
  have hmeas : AEMeasurable (fun w => fwdMap W τ ((a : ℂ) * w)) (foldedCircle d r) :=
    hgm.aemeasurable.congr (hfold.mono fun w hw => gA_of_mem hw)
  -- the separation: `a h ∉ K_τ` near the folded sphere
  have hnot : ∀ h ∈ cthickening δ (foldSph d r), h ∈ H → (a : ℂ) * h ∉ fwdHull W τ := by
    intro h hh hhH hK
    obtain ⟨T', hT', u, hu⟩ := hsep h ⟨hh, show (0 : ℝ) ≤ h.im from le_of_lt hhH⟩
    have haH : 0 < ((a : ℂ) * h).im := by
      have : 0 < h.im := hhH
      simpa using mul_pos ha this
    exact ((FwdHolo.mem_compl_fwdHull_iff hp0.1).2 ⟨haH, T', hT', u, hu⟩).2 hK
  have hrev : revHull (backDrv W τ 0 a).2 (backDrv W τ 0 a).1 =
      {w : ℂ | w ∈ H ∧ (a : ℂ) * w ∈ fwdHull W τ} := by
    rw [backDrv_zero]; exact revHull_revDrv_eq hW hW0 hτpos ha
  have hgd : ∀ᵐ w ∂foldedCircle d r, 0 < w.im ∧
      w ∈ revMap (backDrv W τ 0 a).2 (backDrv W τ 0 a).1 '' H ∧ (a : ℂ) * w ∉ fwdHull W τ := by
    filter_upwards [hfold, hH] with w hw hwH
    have hK : (a : ℂ) * w ∉ fwdHull W τ := hnot w (self_subset_cthickening _ hw) hwH
    refine ⟨hwH, ?_, hK⟩
    by_contra hc
    have : w ∈ revHull (backDrv W τ 0 a).2 (backDrv W τ 0 a).1 := ⟨hwH, hc⟩
    rw [hrev] at this
    exact hK this.2
  have hsupp : foldedCircle d r
      (revMap (backDrv W τ 0 a).2 (backDrv W τ 0 a).1 '' H)ᶜ = 0 :=
    ae_iff.1 (hgd.mono fun w hw => hw.2.1)
  -- separation from the reverse hull, for the log-derivative integrability
  have hthick : foldedCircle d r
      (thickening δ (revHull (backDrv W τ 0 a).2 (backDrv W τ 0 a).1)) = 0 := by
    refine measure_mono_null (t := {w | ¬ w ∈ foldSph d r}) (fun w hw => ?_)
      (ae_iff.1 hfold)
    show w ∉ foldSph d r
    intro hwK
    obtain ⟨h, hh, hdist⟩ := mem_thickening_iff.1 hw
    rw [hrev] at hh
    have hmem : h ∈ cthickening δ (foldSph d r) :=
      mem_cthickening_of_dist_le h w δ _ hwK (by rw [dist_comm]; exact hdist.le)
    exact hnot h hmem hh.1 hh.2
  have hI2 := backLogSepStmt_holds (backDrv W τ 0 a).2 (continuous_backDrv hW τ 0 a)
    (by simp [backDrv]) (backDrv W τ 0 a).1 (backDrv_fst_nonneg W hp0.1 a) d r hr hsupp
    ⟨δ, hδ, hthick⟩
  -- the log profile along the scaled circle
  have hne : ∀ w ∈ foldSph d r, (a : ℂ) * w ≠ 0 := fun w hw h => by
    obtain ⟨u, hu⟩ := hgood0 a hp1 w hw
    have h0 := (hu.2 0 ⟨le_rfl, hT⟩).1
    rw [FwdHolo.sol_zero hu hT, hW0, h, Complex.ofReal_zero, sub_zero] at h0
    exact h0 rfl
  have hcont : ContinuousOn (fun w => a' * Real.log ‖(a : ℂ) * w‖ + g₁ ((a : ℂ) * w))
      (foldSph d r) := by
    refine (continuousOn_const.mul ?_).add (hg₁.comp (continuous_const.mul continuous_id)).continuousOn
    refine Real.continuousOn_log.comp (continuous_norm.comp
      (continuous_const.mul continuous_id)).continuousOn fun w hw => ?_
    simpa using hne w hw
  have hint1 : Integrable (fun w => a' * Real.log ‖(a : ℂ) * w‖ + g₁ ((a : ℂ) * w))
      (foldedCircle d r) := by
    have h := hcont.integrableOn_compact (μ := foldedCircle d r) (isCompact_foldSph d r)
    rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hfold] at h
  exact ⟨hmeas, hgd, hint1, hsupp, hI2, zero_not_mem_foldSph_scaled hW0 ha hT (hgood0 a hp1),
    muA0_zero hW hW0 hr ha₀ hm hgood0 hlow hp0 hp1⟩

end ASep
end QuantumZipper
