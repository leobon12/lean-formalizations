import QuantumZipper.Proofs.Zipper.WedgeUnzipCore
import QuantumZipper.Proofs.GFF.CoordRegEnergy

/-!
# D29 (wedge unzipping), part 5: unzipping commutes with adding a continuous function

Proof of `WedgeUnzip.UnzipAddFunStmt` (deterministic). For a regular sample `x` (witness `F`), a
continuous `g`, and `ν = (f_t⁻¹)_* fc(d, r)` (a probability measure carried by a bounded part of
`ℍ`, `RegCont.νT_facts`):

* `avgReg x k = F(·, 2^{-k})` and `avgReg (x + g) k = F(·, 2^{-k}) + (circle average of g)` on
  `ℍ̄` (`GoodSample.gs_add_ofFun`);
* the circle averages of `g` converge boundedly to `g` on the support of `ν`
  (`CoordReg.tendsto_integral_fc_of_continuousOn`, dominated convergence);
* hence, when `∫ F(·, ρ) dν` converges as `ρ → 0⁺`, `evalReg (x + g) ν = evalReg x ν + ∫ g dν`,
  and `∫ g dν = ∫ g ∘ E_t d fc(d, r)`.

This is the global form of the field identity `F2.Step3FieldIdStmt` (Sheffield, arXiv:1012.4797,
§5.1: `coordChange` is affine in the field). Own elementary argument.
-/

noncomputable section

open MeasureTheory Filter Set Function
open scoped Topology

namespace QuantumZipper
namespace WedgeUnzip

theorem avgReg_eq_of_regularWith {x : FieldSample} {F : ℂ × ℝ → ℝ} (hF : IsRegularWith x F)
    (k : ℕ) {w : ℂ} (hw : w ∈ Hbar) : avgReg x k w = F (w, radius k) :=
  (hF.2.1 k w hw).limUnder_eq

/-- Circle averages of a continuous function on a bounded set are bounded. -/
theorem abs_smoothFun_le {g : ℂ → ℝ} {M R : ℝ} (hM : ∀ z : ℂ, ‖z‖ ≤ R → |g z| ≤ M)
    {w : ℂ} {ρ : ℝ} (hρ : 0 ≤ ρ) (hwR : ‖w‖ + ρ ≤ R) :
    |GoodSample.smoothFun g w ρ| ≤ M := by
  unfold GoodSample.smoothFun
  have h := norm_integral_le_of_norm_le_const (μ := foldedCircle w ρ) (C := M)
    ((TwoPoint.foldedCircle_ae_norm_le w hρ).mono fun z hz => by
      rw [Real.norm_eq_abs]; exact hM z (hz.trans hwR))
  simpa [Real.norm_eq_abs] using h

theorem unzipAddFun : UnzipAddFunStmt := by
  intro γ x g W t ht hW hW0 hg hx hcont d hd r hr
  obtain ⟨F, hF⟩ := hx
  set ψ := fwdMapInv W t
  set ν : Measure ℂ := (foldedCircle d r).map ψ with hν_def
  obtain ⟨_C, B, _hC, _hB, hfacts⟩ := RegCont.νT_facts hW hW0 t d hr
  obtain ⟨hνP, -, hνB⟩ := hfacts t ⟨ht, le_rfl⟩
  have : IsProbabilityMeasure ν := hνP
  obtain ⟨hint, L, hL⟩ := hcont d hd r hr
  have hgc : ContinuousOn g Hbar := hg.continuousOn
  have hHb : ∀ {w : ℂ}, w ∈ H → w ∈ Hbar := fun {w} (hw : w ∈ H) =>
    (show 0 ≤ w.im from le_of_lt (show 0 < w.im from hw))
  set F' : ℂ × ℝ → ℝ := fun q => F q + ∫ v, g v ∂foldedCircle q.1 q.2
  have hF' : IsRegularWith (x + ofFun g) F' := GoodSample.gs_add_ofFun hF hgc
  -- the sequence for `x`
  have ha : ∀ k : ℕ, ∫ w, avgReg x k w ∂ν = ∫ u, evalReg x (foldedCircle u (radius k)) ∂ν :=
    fun k => integral_congr_ae (hνB.mono fun w hw => by
      show avgReg x k w = evalReg x (foldedCircle w (radius k))
      rw [avgReg_eq_of_regularWith hF k (hHb hw.1),
        hF.evalReg_fc_of_mem (hHb hw.1) (radius_pos k)])
  have hxlim : Tendsto (fun k : ℕ => ∫ w, avgReg x k w ∂ν) atTop (𝓝 L) := by
    simp_rw [ha]; exact hL.comp RegClosure.tendsto_radius_nhdsGT
  -- the circle averages of `g`
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) (B + 1)).exists_bound_of_continuousOn
    hg.continuousOn
  have hM' : ∀ z : ℂ, ‖z‖ ≤ B + 1 → |g z| ≤ M := fun z hz => by
    have := hM z (by rw [Metric.mem_closedBall, dist_zero_right]; exact hz)
    rwa [Real.norm_eq_abs] at this
  have hsm : ∀ k : ℕ, Continuous fun w => GoodSample.smoothFun g w (radius k) := fun k =>
    GoodSample.continuous_smoothFun hgc _
  have hsint : ∀ k : ℕ, Integrable (fun w => GoodSample.smoothFun g w (radius k)) ν := fun k =>
    (integrable_const M).mono' (hsm k).aestronglyMeasurable (hνB.mono fun w hw => by
      rw [Real.norm_eq_abs]
      exact abs_smoothFun_le hM' (radius_pos k).le (by linarith [hw.2, RegCont.radius_le_one k]))
  have hglim : Tendsto (fun k : ℕ => ∫ w, GoodSample.smoothFun g w (radius k) ∂ν) atTop
      (𝓝 (∫ w, g w ∂ν)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => M)
      (fun k => (hsm k).aestronglyMeasurable) (integrable_const M) (fun k => hνB.mono fun w hw => by
        rw [Real.norm_eq_abs]
        exact abs_smoothFun_le hM' (radius_pos k).le (by linarith [hw.2, RegCont.radius_le_one k]))
      (hνB.mono fun w hw => ?_)
    have h1 := CoordReg.tendsto_integral_fc_of_continuousOn hg.measurable hg.continuousOn hw.1
      (fun ρ hρ hρ1 => (integrable_const M).mono' hg.aestronglyMeasurable
        ((TwoPoint.foldedCircle_ae_norm_le w hρ.le).mono fun z hz => by
          rw [Real.norm_eq_abs]; exact hM' z (by linarith [hw.2])))
    exact h1.comp RegClosure.tendsto_radius_nhdsGT
  -- the sequence for `x + g`
  have hintA : ∀ k : ℕ, Integrable (fun w => avgReg x k w) ν := fun k =>
    (hint (radius k) (radius_pos k)).congr (hνB.mono fun w hw => by
      show evalReg x (foldedCircle w (radius k)) = avgReg x k w
      rw [avgReg_eq_of_regularWith hF k (hHb hw.1),
        hF.evalReg_fc_of_mem (hHb hw.1) (radius_pos k)])
  have hb : ∀ k : ℕ, ∫ w, avgReg (x + ofFun g) k w ∂ν =
      ∫ w, avgReg x k w ∂ν + ∫ w, GoodSample.smoothFun g w (radius k) ∂ν := fun k => by
    rw [← integral_add (hintA k) (hsint k)]
    refine integral_congr_ae (hνB.mono fun w hw => ?_)
    show avgReg (x + ofFun g) k w = avgReg x k w + GoodSample.smoothFun g w (radius k)
    rw [avgReg_eq_of_regularWith hF' k (hHb hw.1), avgReg_eq_of_regularWith hF k (hHb hw.1)]
    rfl
  have hE1 : evalReg x ν = L := hxlim.limUnder_eq
  have hE2 : evalReg (x + ofFun g) ν = L + ∫ w, g w ∂ν :=
    ((hxlim.add hglim).congr fun k => (hb k).symm).limUnder_eq
  have hgE : ∫ z, (g ∘ F2.extInv W t) z ∂foldedCircle d r = ∫ w, g w ∂ν := by
    rw [hν_def, integral_map (RegCont.aemeasurable_fwdMapInv hW hW0 ht d hr)
      hg.aestronglyMeasurable]
    refine integral_congr_ae ((TwoPoint.foldedCircle_ae_mem_H d hr).mono fun z hz => ?_)
    have hz' : 0 < z.im := hz
    simp [F2.extInv, hz']
  show evalReg (x + ofFun g) ν + Qc γ * ∫ z, Real.log ‖deriv ψ z‖ ∂foldedCircle d r =
    (evalReg x ν + Qc γ * ∫ z, Real.log ‖deriv ψ z‖ ∂foldedCircle d r) +
      ∫ z, (g ∘ F2.extInv W t) z ∂foldedCircle d r
  rw [hE1, hE2, hgE]
  ring

end WedgeUnzip
end QuantumZipper
