import QuantumZipper.Proofs.Zipper.BaseFin2Defs
import QuantumZipper.Proofs.Zipper.LocLenF2Step4
import QuantumZipper.Proofs.Zipper.LocLenAddConst
import QuantumZipper.Proofs.RS.TransienceScale

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# X1 (D75): the scaling step `BaseScaleStmt`

For `a = 2^{-k}` and the scaled pair `(B^{(k)}, X^{(k)}) = (scB k B, scNrmR κ a X)`:
* `λ_k ≥ a λ^{(k)}_0` (Brownian scaling of the trace, `RS.ae_sleTrace_scale`);
* `L^±(a²) = e^{(γ/2) C} L^{(k)±}(1)` with `C = scConst κ a X`: the open-arc lengths are scale
  equivariant (`LocLen.unzipLengthsArc_scale`, with the scale geometry
  `LocLen.scaleGeomAeLoc_of_yMergeOffTip`), the scaled field differs from `h⁰ + X^{(k)}` by the
  constant `C` at dyadic circles (`F2.ae_rawRescale_fc_dyadic`), and a constant multiplies both
  open-arc lengths by `e^{(γ/2) C}` (rule (5.1) for constants, as `LocLen.agree_addConst_dy_arc`,
  with the regularity of `RegUnif.gaugeRegDyStmt_holds`).
Hence `term_k ≤ a^{−κ/2} e^{(γ/2)C} term^{(k)}_0 = scFac κ a X · term^{(k)}_0`.

Main result: `baseScale_of_yMergeOffTip : WedgeUnzip.YMergeOffTipStmt → BaseScaleStmt`. The input
`YMergeOffTipStmt` (Sheffield–Wang merging off the tip) is already a leaf of the Theorem 1.3
headline. Own elementary bookkeeping (Sheffield arXiv:1012.4797, §5.1, pp. 60–62, scaling rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace BaseFin2

open WedgeUnzip

/-- **Rule (5.1) for constants, open-arc lengths** (the length half of
`LocLen.agree_addConst_dy_arc`). -/
theorem bf2_unzipLengthsArc_addConst {γ c t : ℝ} {x : FieldSample} {W : ℝ → ℝ}
    (h : ∀ k : ℕ, ∀ d ∈ RegUnif.Dy,
      E1.RegShift x ((foldedCircle d (radius k)).map (fwdMapInv W t)))
    (hbc : Cor15Group.BdryConvAE (unzippedField γ (x, W) t)) :
    LocLen.unzipLengthsArc γ (addConst x c, W) t =
      (ENNReal.ofReal (Real.exp (γ * c / 2)) * (LocLen.unzipLengthsArc γ (x, W) t).1,
        ENNReal.ofReal (Real.exp (γ * c / 2)) * (LocLen.unzipLengthsArc γ (x, W) t).2) := by
  have hav : avgReg (unzippedField γ (addConst x c, W) t) =
      avgReg (addConst (unzippedField γ (x, W) t) c) :=
    RegUnif.avgReg_coordChange_addConst_dy (ψ := fwdMapInv W t) (Q := Qc γ) h
  have hb : bdryApprox γ (unzippedField γ (addConst x c, W) t) =
      fun k => ENNReal.ofReal (Real.exp (γ * c / 2)) • bdryApprox γ (unzippedField γ (x, W) t) k :=
    funext fun k => by
      rw [← Cor15Group.bdryApprox_addConst_ae hbc γ c k]
      unfold bdryApprox; rw [hav]
  have hC0 := LocalRule.ofReal_exp_ne_zero (γ * c / 2)
  exact Prod.ext (LocLen.arcLen_smul_of_bdryApprox hC0 ENNReal.ofReal_ne_top hb _ _)
    (LocLen.arcLen_smul_of_bdryApprox hC0 ENNReal.ofReal_ne_top hb _ _)

variable {Ω : Type} [MeasurableSpace Ω]

theorem bf2_scB_eq_fun (k : ℕ) (B : ℝ≥0 → Ω → ℝ) :
    scB k B = fun t ω => (√(((radius k ^ 2).toNNReal : ℝ≥0) : ℝ))⁻¹ *
      B ((radius k ^ 2).toNNReal * t) ω := by
  rw [scB_eq]
  funext t ω
  rw [sqrt_toNNReal_radius_sq]
  ring

/-- **Scaling of the window minimum**: `a λ^{(k)}_0 ≤ λ_k`, given the trace scaling. -/
theorem bf2_winLam_scale_le {κ : ℝ} {B : ℝ≥0 → Ω → ℝ} {ω : Ω} (k : ℕ)
    (htr : ∀ s : ℝ, 0 ≤ s → sleTrace κ (scB k B) ω s =
      sleTrace κ B ω (radius k ^ 2 * s) / radius k) :
    ENNReal.ofReal (radius k) * winLam κ (scB k B) ω 0 ≤ winLam κ B ω k := by
  set a := radius k with hadef
  have ha : 0 < a := radius_pos k
  have ha2 : 0 < a ^ 2 := pow_pos ha 2
  refine le_iInf₂ fun r hr => ?_
  have hr1 : radius (0 + 1) ^ 2 ≤ r / a ^ 2 ∧ r / a ^ 2 ≤ radius 0 ^ 2 := by
    have e1 : radius (k + 1) = a / 2 := by simp only [hadef, radius, pow_succ]; ring
    have e0 : radius (0 + 1) ^ 2 = 1 / 4 := by norm_num [radius]
    have e0' : radius 0 ^ 2 = 1 := by norm_num [radius]
    rw [e0, e0']
    rw [e1] at hr
    constructor
    · rw [le_div_iff₀ ha2]; nlinarith [hr.1]
    · rw [div_le_iff₀ ha2]; nlinarith [hr.2]
  have hw : winLam κ (scB k B) ω 0 ≤ ENNReal.ofReal ‖sleTrace κ (scB k B) ω (r / a ^ 2)‖ :=
    iInf₂_le (f := fun r (_ : r ∈ Icc (radius (0 + 1) ^ 2) (radius 0 ^ 2)) =>
      ENNReal.ofReal ‖sleTrace κ (scB k B) ω r‖) (r / a ^ 2) hr1
  have hs : sleTrace κ (scB k B) ω (r / a ^ 2) = sleTrace κ B ω r / a := by
    rw [htr _ (div_nonneg (le_trans (by positivity) hr.1) ha2.le), mul_div_cancel₀ _ ha2.ne']
  rw [hs] at hw
  calc ENNReal.ofReal a * winLam κ (scB k B) ω 0
      ≤ ENNReal.ofReal a * ENNReal.ofReal ‖sleTrace κ B ω r / a‖ := mul_le_mul' le_rfl hw
    _ = ENNReal.ofReal ‖sleTrace κ B ω r‖ := by
        rw [← ENNReal.ofReal_mul ha.le, norm_div, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos ha, mul_div_cancel₀ _ ha.ne']

/-- `λ^{(k)}_0 < ⊤`. -/
theorem bf2_winLam_ne_top (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (ω : Ω) (k : ℕ) : winLam κ B ω k ≠ ⊤ := by
  refine ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (iInf₂_le (f := fun r (_ : r ∈ Icc (radius (k + 1) ^ 2) (radius k ^ 2)) =>
      ENNReal.ofReal ‖sleTrace κ B ω r‖) (radius k ^ 2) ⟨?_, le_rfl⟩)
  have : radius (k + 1) ≤ radius k := by
    unfold radius; exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_succ k)
  exact pow_le_pow_left₀ (radius_pos _).le this 2

/-- **The scaling step, conditional on the Sheffield–Wang merging leaf.** -/
theorem baseScale_of_yMergeOffTip (hYO : WedgeUnzip.YMergeOffTipStmt) : BaseScaleStmt := by
  intro κ hκ hκ4 Ω _ P _ B X hB hX hind k
  set a := radius k with hadef
  have ha : 0 < a := radius_pos k
  have hγ : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  obtain ⟨hB', hX', hind', -⟩ := scPairR_props (κ := κ) hB hX hind k
  have hG := LocLen.scaleGeomAeLoc_of_yMergeOffTip hYO κ hκ hκ4 P B X hB hX hind a ha
  have hRS := RegUnif.gaugeRegDyStmt_holds (κ := κ) (T := 1) hB' hX' hind' one_pos
  have hTr := RS.ae_sleTrace_scale hB hκ (by linarith) ha
  filter_upwards [hG, hRS, hTr, F2.ae_rawRescale_fc_dyadic hX (Qc (Real.sqrt κ)) ha]
    with ω hg hrs htr hraw
  set W := drive κ B ω with hW
  set W' := drive κ (scB k B) ω with hW'
  have hWW : W' = fun s => W (a ^ 2 * s) / a := by rw [hW', drive_scB]; rfl
  set z : FieldSample := ofFun (h0rev κ) + scNrmR κ a (X ω) with hz
  set C : ℝ := scConst κ a (X ω) with hC
  -- (A) scale equivariance
  obtain ⟨hgood, hL, hR, hEq⟩ := hg 1 zero_le_one
  have hA := LocLen.unzipLengthsArc_scale (x := ofFun (h0rev κ) + X ω)
    (x' := ofFun (h0rev κ) + addConst (rescale (X ω) (Qc (Real.sqrt κ)) a)
      (2 / Real.sqrt κ * Real.log a)) hγ ha zero_le_one hL hR hgood hEq
  rw [mul_one] at hA
  -- (B) the scaled field is `z + C` at dyadic circles
  have hav : avgReg (ofFun (h0rev κ) + addConst (rescale (X ω) (Qc (Real.sqrt κ)) a)
      (2 / Real.sqrt κ * Real.log a)) = avgReg (addConst z C) := by
    refine F2.avgReg_eq_of_fc_dyadic fun j n w => ?_
    have h1 := hraw j n w
    have h0 := hraw 0 0 0
    rw [CoordsFull.dyadicRoundC_zero] at h0
    simp only [hz, hC, scConst, scNrmR, B1Full.nrm, addConst, Pi.add_apply, measure_univ,
      ENNReal.toReal_one, mul_one, FSMeas.sfTrunc_apply, h1]
    simp only [radius, pow_zero] at h0
    rw [h0]
    ring
  have hB2 := LocLen.unzipLengthsArc_congr_avgReg (Real.sqrt κ) hav W' 1
  -- (C) the constant
  obtain ⟨hrs1, hbc⟩ := hrs 1 ⟨zero_le_one, le_rfl⟩
  rw [B2.h0f_eq_unzippedField] at hbc
  have hC2 := bf2_unzipLengthsArc_addConst (c := C) hrs1 hbc
  -- (D) assemble the lengths
  have hlen : lenArc κ B X ω (radius k ^ 2) =
      (ENNReal.ofReal (Real.exp (Real.sqrt κ * C / 2)) *
          (lenArc κ (scB k B) (fun ω => scNrmR κ (radius k) (X ω)) ω 1).1,
        ENNReal.ofReal (Real.exp (Real.sqrt κ * C / 2)) *
          (lenArc κ (scB k B) (fun ω => scNrmR κ (radius k) (X ω)) ω 1).2) := by
    have e1 : lenArc κ B X ω (radius k ^ 2) =
        LocLen.unzipLengthsArc (Real.sqrt κ) (ofFun (h0rev κ) + X ω, W) (a ^ 2) := rfl
    rw [e1, ← hA, ← hWW, hB2]
    exact hC2
  -- (E) the window minimum
  have htr' : ∀ s : ℝ, 0 ≤ s → sleTrace κ (scB k B) ω s =
      sleTrace κ B ω (radius k ^ 2 * s) / radius k := by
    intro s hs
    rw [bf2_scB_eq_fun]
    exact htr s hs
  have hwl := bf2_winLam_scale_le (κ := κ) (B := B) (ω := ω) k htr'
  have hwt := bf2_winLam_ne_top κ (scB k B) ω 0
  have hpow : winLam κ B ω k ^ (-(κ / 2)) ≤
      ENNReal.ofReal a ^ (-(κ / 2)) * winLam κ (scB k B) ω 0 ^ (-(κ / 2)) := by
    rw [← ENNReal.mul_rpow_of_ne_top ENNReal.ofReal_ne_top hwt, ENNReal.rpow_neg,
      ENNReal.rpow_neg, ← ENNReal.inv_rpow, ← ENNReal.inv_rpow]
    exact ENNReal.rpow_le_rpow (ENNReal.inv_le_inv.2 hwl) (by linarith)
  -- (F) the factor
  have hfac : scFac κ a (X ω) =
      ENNReal.ofReal a ^ (-(κ / 2)) * ENNReal.ofReal (Real.exp (Real.sqrt κ * C / 2)) := by
    unfold scFac
    rw [ENNReal.ofReal_mul (Real.rpow_nonneg ha.le _), ENNReal.ofReal_rpow_of_pos ha]
  refine ⟨?_, ?_⟩
  · unfold termL
    rw [hlen, hfac]
    calc winLam κ B ω k ^ (-(κ / 2)) * (ENNReal.ofReal (Real.exp (Real.sqrt κ * C / 2)) *
          (lenArc κ (scB k B) (fun ω => scNrmR κ (radius k) (X ω)) ω 1).1)
        ≤ (ENNReal.ofReal a ^ (-(κ / 2)) * winLam κ (scB k B) ω 0 ^ (-(κ / 2))) *
          (ENNReal.ofReal (Real.exp (Real.sqrt κ * C / 2)) *
            (lenArc κ (scB k B) (fun ω => scNrmR κ (radius k) (X ω)) ω 1).1) :=
          mul_le_mul' hpow le_rfl
      _ = _ := by
          have h1 : radius 0 ^ 2 = (1 : ℝ) := by simp [radius]
          rw [h1]; ring
  · unfold termR
    rw [hlen, hfac]
    calc winLam κ B ω k ^ (-(κ / 2)) * (ENNReal.ofReal (Real.exp (Real.sqrt κ * C / 2)) *
          (lenArc κ (scB k B) (fun ω => scNrmR κ (radius k) (X ω)) ω 1).2)
        ≤ (ENNReal.ofReal a ^ (-(κ / 2)) * winLam κ (scB k B) ω 0 ^ (-(κ / 2))) *
          (ENNReal.ofReal (Real.exp (Real.sqrt κ * C / 2)) *
            (lenArc κ (scB k B) (fun ω => scNrmR κ (radius k) (X ω)) ω 1).2) :=
          mul_le_mul' hpow le_rfl
      _ = _ := by
          have h1 : radius 0 ^ 2 = (1 : ℝ) := by simp [radius]
          rw [h1]; ring

end BaseFin2
end QuantumZipper
