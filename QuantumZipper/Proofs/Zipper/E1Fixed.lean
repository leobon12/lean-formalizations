import QuantumZipper.Proofs.Zipper.E1Window2
import QuantumZipper.Proofs.Zipper.E1Glue

/-!
# E1-FIX (part 1): the boundary measure of `hFix` on the whole live set `liveNeg`

`handoff/E1-PLAN.md`, sub-node **E1-FIX**. The statement of E1-FIX integrates against
`qBoundaryMeasureOn √κ (addConst (hFix …) (−m)) (liveNeg v t)`, so the local vague limit on the
open set `liveNeg v t` must exist. Here:

* `ae_exists_isVagueLimitOnR_hFix`: a.s. the local limit of `hFix` exists on each live negative
  window (the x-side of E1-CC: M4-T4 transported to the reverse map plus the additive rule for
  `𝔥₀ ∘ ψ`, `E1CoordChange2`);
* `ae_exists_isVagueLimitOnR_hFix_liveNeg`: a.s. it exists on `liveNeg v t` (gluing the countably
  many rational windows, `E1Glue.exists_isVagueLimitOnR_of_winW`);
* `qBoundaryMeasureOn_restrict_winW`: the measure on `liveNeg` restricted to a window is the
  measure on the window (uniqueness of local limits).

Sources: as `E1CoordChange2` (Sheffield arXiv:1012.4797 Thm 1.2/(1.3); Duplantier–Sheffield
arXiv:0808.1560 Prop. 3.1); the gluing is the sheaf property of Radon measures (own formalization).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace E1

open RevMapExtension

variable {Ω : Type*} [MeasurableSpace Ω] {P' : Measure Ω}
variable {κ t a b : ℝ} {v : ℝ → ℝ} {X' : Ω → FieldSample}

/-- A.s. the local boundary measure of `hFix` exists on a live negative window. -/
theorem ae_exists_isVagueLimitOnR_hFix [IsProbabilityMeasure P'] (hκ : 0 < κ) (hκ4 : κ < 4)
    (hX : IsFreeGFFModConstH X' P') (hv : Continuous v) (hv0 : v 0 = 0) (ht : 0 ≤ t)
    (hab : a < b) (hw : ∀ x ∈ Icc a b, x < 0 ∧ IsLive v t x) :
    ∀ᵐ ω ∂P', ∃ ν, IsVagueLimitOnR (Ioo a b)
      (bdryApprox (Real.sqrt κ) (hFix κ v t (X' ω))) ν := by
  set γ := Real.sqrt κ with hγdef
  have hγ : 0 < γ := Real.sqrt_pos.2 hκ
  have hγ2 : γ < 2 := by
    rw [hγdef, show (2 : ℝ) = Real.sqrt 4 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt hκ.le hκ4
  obtain ⟨U, hUo, hJU, hdiff, hH, hreal, him, hne⟩ :=
    exists_revMapExt_window hv ht (a := a) (b := b) fun x hx => (hw x hx).2
  set ψ := revMapExt v t with hψdef
  have hmono : StrictMonoOn (fun x : ℝ => (ψ x).re) (Icc a b) := by
    intro x hx y hy hxy
    simp only [hreal x hx, hreal y hy, Complex.ofReal_re]
    exact RealLine.strictMonoOn_realRevMap hv ht (exists_isRealRevSol_of_isLive (hw x hx).2)
      (exists_isRealRevSol_of_isLive (hw y hy).2) hxy
  have hFneg : ∀ x ∈ Icc a b, realRevMap v t x < 0 := fun x hx =>
    realRevMap_neg hv hv0 ht (hw x hx).1 (hw x hx).2
  have hA := CoordChange.ae_isVagueLimitOnR_coordChange hX hγ hγ2 hab hUo hJU hdiff him hmono hne
  filter_upwards [hA, CoordReg.ae_isRegularSample_coordChange_revMap' hv ht hX 0
      (g₁ := fun _ => 0) continuous_const (Qc γ), ae_avgReg_hFix_eq (κ := κ) hX hv ht hH]
    with ω hlim hregY havg
  set Y := coordChange (X' ω) (revMap v t) (Qc γ) with hYdef
  have hzero : ofFun (fun v : ℂ => (0 : ℝ) * Real.log ‖v‖ + (fun _ => (0 : ℝ)) v) + X' ω = X' ω := by
    funext μ; simp [ofFun]
  rw [hzero] at hregY
  obtain ⟨ν, hlimY⟩ : ∃ ν, IsVagueLimitOnR (Ioo a b) (bdryApprox γ Y) ν := by
    have e : bdryApprox γ Y = bdryApprox γ (coordChange (X' ω) ψ (Qc γ)) := funext fun k =>
      (bdryApprox_coordChange_revMapExt hH γ (X' ω) (Qc γ) k).symm
    rw [e]; exact ⟨_, hlim⟩
  set W : Set ℂ := U ∩ ψ ⁻¹' {z | z ≠ 0} with hWdef
  have hWo : IsOpen W := hdiff.continuousOn.isOpen_inter_preimage hUo isOpen_ne
  have hUW : ∀ x ∈ Ioo a b, (x : ℂ) ∈ W := fun x hx =>
    ⟨hJU x (Ioo_subset_Icc_self hx), by
      show ψ x ≠ 0
      rw [hreal x (Ioo_subset_Icc_self hx)]
      exact_mod_cast (hFneg x (Ioo_subset_Icc_self hx)).ne⟩
  have hφc : ContinuousOn (fun u => h0rev κ (ψ u)) (W ∩ Hbar) :=
    (continuousOn_h0rev κ).comp (hdiff.continuousOn.mono fun z hz => hz.1.1) fun z hz => hz.1.2
  have e1 : bdryApprox γ (hFix κ v t (X' ω)) = bdryApprox γ (Y + ofFun fun u => h0rev κ (ψ u)) :=
    funext fun k => by unfold bdryApprox; simp_rw [havg k]
  rw [e1]
  exact ⟨_, LocalRule.isVagueLimitOnR_add_ofFun hregY isOpen_Ioo hlimY hWo hUW hφc⟩

/-- A.s. the local boundary measure of `hFix` exists on the whole live set `liveNeg v t`. -/
theorem ae_exists_isVagueLimitOnR_hFix_liveNeg [IsProbabilityMeasure P'] (hκ : 0 < κ)
    (hκ4 : κ < 4) (hX : IsFreeGFFModConstH X' P') (hv : Continuous v) (hv0 : v 0 = 0)
    (ht : 0 ≤ t) :
    ∀ᵐ ω ∂P', ∃ ν, IsVagueLimitOnR (liveNeg v t)
      (bdryApprox (Real.sqrt κ) (hFix κ v t (X' ω))) ν := by
  have hW : ∀ n, ∀ᵐ ω ∂P', ∃ ν, IsVagueLimitOnR (winW (liveNeg v t) n)
      (bdryApprox (Real.sqrt κ) (hFix κ v t (X' ω))) ν := fun n => by
    by_cases hpq : ((winPQ n).1 : ℝ) < (winPQ n).2
    · by_cases h : Icc ((winPQ n).1 : ℝ) (winPQ n).2 ⊆ liveNeg v t
      · filter_upwards [ae_exists_isVagueLimitOnR_hFix hκ hκ4 hX hv hv0 ht hpq
          fun x hx => h hx] with ω hω
        exact exists_isVagueLimitOnR_winW n fun _ => hω
      · exact ae_of_all _ fun ω => exists_isVagueLimitOnR_winW n fun h' => absurd h' h
    · refine ae_of_all _ fun ω => exists_isVagueLimitOnR_winW n fun _ => ⟨0, ?_⟩
      rw [Ioo_eq_empty hpq]
      exact ⟨by simp, fun _ _ _ => by simp, fun f _ _ hfU => by
        have : f = 0 := funext fun t => image_eq_zero_of_notMem_tsupport fun ht => hfU ht
        subst this; simp⟩
  filter_upwards [ae_all_iff.2 hW, CoordReg.ae_isRegularSample_coordChange_h0rev' hv ht hX κ
    (Qc (Real.sqrt κ))] with ω hω hreg
  exact exists_isVagueLimitOnR_of_winW (isOpen_liveNeg hv t)
    (LogSing.isFiniteMeasureOnCompacts_bdryApprox hreg _) hω

/-- If the local limit exists on `V`, its chosen value restricted to an open `W ⊆ V` is the chosen
local limit on `W`. -/
theorem qBoundaryMeasureOn_restrict_of_subset {γ : ℝ} {x : FieldSample} {V W : Set ℝ}
    (hV : IsOpen V) (hW : IsOpen W) (hWV : W ⊆ V)
    (hex : ∃ ν, IsVagueLimitOnR V (bdryApprox γ x) ν) :
    (qBoundaryMeasureOn γ x V).restrict W = qBoundaryMeasureOn γ x W := by
  obtain ⟨ν, hν⟩ := hex
  rw [LocalRule.qBoundaryMeasureOn_eq hV hν,
    LocalRule.qBoundaryMeasureOn_eq hW (isVagueLimitOnR_restrict_open hν hW hWV)]

end E1
end QuantumZipper
