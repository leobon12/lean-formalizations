/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GInstMean
import InteractingSLE.Spec.Sec6.Prop61BGlobal
import InteractingSLE.Spec.Supplement.Aux10FullTD

/-!
# Deterministic growth and boundary data of the canonical restart mean

Packet PROVE-AUX61-GLUEINST. The arbitrary harmonic correction cancels from
the relative mean. The remaining Green correction is bounded, and the
derivative argument has the existing logarithmic disk bound. Boundary limits
reuse the active Green potential's boundary theorem.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv)
open QuantumZipper.CA (cayleyInv)
open scoped NNReal ENNReal ComplexConjugate

namespace InteractingSLE.Sec5.Aux61GInst

open Restart.FlowStopIdentCMI (CMCut)
open Restart.FlowLocalityGen
open Aux61Win (IsCutoffOn meanF)
open Aux61Fib (FibData FibCode fibW)
open Aux61UnionK (canonMean bhe_canonExt)

universe u

/-- The hydrodynamic derivative argument has logarithmic growth in the disk
chart of the slit domain. -/
theorem exists_abs_logDerivFwd_comp_le_log {w : ℝ → ℝ} (hw : Continuous w)
    (hw0 : w 0 = 0) {t : ℝ} (ht : 0 ≤ t) :
    ∃ C : ℝ, ∀ ζ ∈ ball (0 : ℂ) 1,
      |(QuantumZipper.logDerivFwd w t (fwdMapInv w t (cayleyInv ζ))).im| ≤
        C * (1 + Real.log (1 / (1 - ‖ζ‖))) := by
  have hU := QuantumZipper.FwdHolo.isOpen_compl_fwdHull hw ht
  have hf := isConformalBijection_comp (isConformalBijection_fwdMapInv hw hw0 ht)
    isConformalBijection_cayleyInv
  refine Sec6.exists_abs_arg_comp_le_log hU hf (Aux10.isConformalBijection_fwdMap hw hw0 ht)
    (Complex.continuous_im.comp_continuousOn (isDerivLog_fwdMap hw ht).1.continuousOn) ?_
  intro z hz
  dsimp only [Function.comp_apply]
  rw [Ito.deriv_fwdMap_eq_exp hw ht hz, Complex.norm_exp, Complex.ofReal_exp,
    ← Complex.exp_add, Complex.re_add_im]

/-- Logarithmic growth of the explicit mean relative to its initial mean.
Only the two reference extensions must be bounded; the correction `q` may
have arbitrary growth and arbitrary old boundary singularities. -/
theorem exists_abs_meanF_sub_le_log {κ : ℝ} {v v₀ q : ℂ → ℝ}
    (hv : ∃ C : ℝ, ∀ z ∈ H, |v z| ≤ C) (hv₀ : ∃ C : ℝ, ∀ z ∈ H, |v₀ z| ≤ C)
    {F : CMCut} {N : Set ℂ} {O : Set ℝ} (hF : IsCutoffOn F q N O)
    {w : ℝ → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) {t : ℝ} (ht : 0 ≤ t)
    (hKN : closure (fwdHull w t) ⊆ N) :
    ∃ C : ℝ, ∀ ζ ∈ ball (0 : ℂ) 1,
      |meanF κ v q F w t (fwdMapInv w t (cayleyInv ζ)) -
          (v₀ (fwdMapInv w t (cayleyInv ζ)) + q (fwdMapInv w t (cayleyInv ζ)))| ≤
        C * (1 + Real.log (1 / (1 - ‖ζ‖))) := by
  obtain ⟨A, hA⟩ := hv
  obtain ⟨A₀, hA₀⟩ := hv₀
  obtain ⟨B, hB⟩ := exists_abs_aliveGreenPot_le F
  obtain ⟨C, hC⟩ := F.compact.exists_bound_of_continuous F.smooth.continuous
  obtain ⟨D, hD⟩ := exists_abs_logDerivFwd_comp_le_log hw hw0 ht
  refine ⟨|A| + |A₀| + |B| + |C| + |QuantumZipper.chiC κ| * |D|, fun ζ hζ => ?_⟩
  have hξ : cayleyInv ζ ∈ H := isConformalBijection_cayleyInv.2.mapsTo hζ
  have hz : fwdMapInv w t (cayleyInv ζ) ∈ H \ fwdHull w t :=
    QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hw hw0 ht hξ
  have hfz := QuantumZipper.FwdHolo.mapsTo_fwdMap hw ht hz
  have hL : 0 ≤ Real.log (1 / (1 - ‖ζ‖)) :=
    WangWu.log_one_div_nonneg (sub_pos.2 (mem_ball_zero_iff.1 hζ)) (by linarith [norm_nonneg ζ])
  set L := 1 + Real.log (1 / (1 - ‖ζ‖))
  have hL1 : 1 ≤ L := by dsimp only [L]; linarith only [hL]
  have hDa := (hD ζ hζ).trans (mul_le_mul_of_nonneg_right (le_abs_self D) (by linarith only [hL1]))
  have hba := (hB w hw t ht _ hz).trans (le_abs_self B)
  have hca : |F.f (fwdMapInv w t (cayleyInv ζ))| ≤ |C| := by
    have hc : |F.f (fwdMapInv w t (cayleyInv ζ))| ≤ C := by
      simpa only [Real.norm_eq_abs] using hC (fwdMapInv w t (cayleyInv ζ))
    exact hc.trans (le_abs_self C)
  rw [meanF, greenPot_eq_aliveGreenPot hF hKN, couplingMean]
  have he : v (fwdMap w t (fwdMapInv w t (cayleyInv ζ))) -
      QuantumZipper.chiC κ * (QuantumZipper.logDerivFwd w t (fwdMapInv w t (cayleyInv ζ))).im +
      aliveGreenPot F w t (fwdMapInv w t (cayleyInv ζ)) +
      (q (fwdMapInv w t (cayleyInv ζ)) - F.f (fwdMapInv w t (cayleyInv ζ))) -
      (v₀ (fwdMapInv w t (cayleyInv ζ)) + q (fwdMapInv w t (cayleyInv ζ))) =
      (v (fwdMap w t (fwdMapInv w t (cayleyInv ζ))) - v₀ (fwdMapInv w t (cayleyInv ζ))) +
      (aliveGreenPot F w t (fwdMapInv w t (cayleyInv ζ)) - F.f (fwdMapInv w t (cayleyInv ζ))) -
      QuantumZipper.chiC κ * (QuantumZipper.logDerivFwd w t (fwdMapInv w t (cayleyInv ζ))).im := by ring
  rw [he]
  refine ((abs_sub _ _).trans (add_le_add ((abs_add_le _ _).trans
    (add_le_add (abs_sub _ _) (abs_sub _ _))) le_rfl)).trans ?_
  rw [abs_mul]
  have h1 := (hA _ hfz).trans (le_abs_self A)
  have h2 := (hA₀ _ hz.1).trans (le_abs_self A₀)
  calc |v (fwdMap w t (fwdMapInv w t (cayleyInv ζ)))| + |v₀ (fwdMapInv w t (cayleyInv ζ))| +
        (|aliveGreenPot F w t (fwdMapInv w t (cayleyInv ζ))| + |F.f (fwdMapInv w t (cayleyInv ζ))|) +
        |QuantumZipper.chiC κ| * |(QuantumZipper.logDerivFwd w t (fwdMapInv w t (cayleyInv ζ))).im|
      ≤ |A| + |A₀| + (|B| + |C|) + |QuantumZipper.chiC κ| * (|D| * L) := by
        gcongr
    _ ≤ (|A| + |A₀| + |B| + |C| + |QuantumZipper.chiC κ| * |D|) * L := by
      nlinarith only [hL1, abs_nonneg A, abs_nonneg A₀, abs_nonneg B, abs_nonneg C]

/-- The canonical mean has the relative logarithmic growth needed for
finite-exception uniqueness; its arbitrary correction cancels. -/
theorem exists_abs_canonMean_sub_le_log {d : FibData} {F : CMCut} {N : Set ℂ}
    (hF : IsCutoffOn F d.q N d.O₀) (s : ULift.{u} FibCode) (t : ℝ≥0)
    (hKN : closure (fwdHull (Ito.rpath (fibW · s)) t) ⊆ N) :
    ∃ C : ℝ, ∀ ζ ∈ ball (0 : ℂ) 1,
      |canonMean d F s t (fwdMapInv (Ito.rpath (fibW · s)) t (cayleyInv ζ)) -
          Aux61GlueK.fibMean0 d (fwdMapInv (Ito.rpath (fibW · s)) t (cayleyInv ζ))| ≤
        C * (1 + Real.log (1 / (1 - ‖ζ‖))) := by
  exact exists_abs_meanF_sub_le_log (bhe_canonExt d s t).2.1 (Aux61GlueK.refMean0_ext d).2.1 hF
    ((FibCode.continuous_driver s.down).comp continuous_real_toNNReal)
    (by simpa only [Function.comp_apply, Real.toNNReal_zero] using FibCode.driver_zero s.down)
    t.coe_nonneg hKN

end InteractingSLE.Sec5.Aux61GInst
