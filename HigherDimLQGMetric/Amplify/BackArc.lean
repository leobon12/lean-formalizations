import HigherDimLQGMetric.Amplify.BackRaw
import HigherDimLQGMetric.Amplify.Arc
import HigherDimLQGMetric.Amplify.Collar

/-! A successful returned trial gives a simple arc with quantitative bounds. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace HigherDimLQGMetric

open Set
open HigherDimLFPP (Rd)
open LQGMetric.MetricGeometry
open scoped ENNReal

variable {d : ℕ}

/-- The deterministic arc conclusion at its trial scale. -/
theorem amplify_backEvent_to_arc (D Dt : ContMetric d)
    (hD : D.IsLength) [ProperSpace D.Space]
    (hDt : Dt.IsLength) [ProperSpace Dt.Space]
    {ξ Q cs c1 ℓ δ s : ℝ} (hcs : 0 < cs) (hc1 : 0 < c1)
    (hℓ : 0 < ℓ) (hs : 0 < s) (hβ : 0 ≤ ξ * δ)
    (hδsmall : Real.exp (4 * ξ * δ) < 2)
    (w : Rd d) (H : DistRd d)
    (hcomp : ∀ x y, cs * D.1 (x, y) ≤ Dt.1 (x, y))
    (hback : AmplifyBackEvent D Dt ξ Q cs c1 ℓ δ s w H) :
    ∃ γ : ℝ → Rd d, IsSimpleArc γ ∧
      (∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ ann w (3 * s / 4) (3 * s)) ∧
      Dt.len γ 0 1 ≤ ENNReal.ofReal (Real.exp (4 * ξ * δ) * c1) *
        ENNReal.ofReal (D.1 (γ 0, γ 1)) ∧
      ENNReal.ofReal (Real.exp (-2 * ξ * δ) * (ℓ / (2 * c1)) *
        sNorm ξ Q H s w) ≤ ENNReal.ofReal (D.1 (γ 0, γ 1)) ∧
      D.len γ 0 1 ≤ ENNReal.ofReal
        (cs⁻¹ * Real.exp (2 * ξ * δ) * ℓ * sNorm ξ Q H s w) := by
  let sn := sNorm ξ Q H s w
  let x := Real.exp (2 * ξ * δ)
  let C := Real.exp (-2 * ξ * δ) * (4 * max 1 cs⁻¹ * ℓ) * sn
  let L := Real.exp (2 * ξ * δ) * ℓ * sn
  have hsn : 0 < sn := sNorm_pos ξ Q H hs w
  have hx : 0 < x := Real.exp_pos _
  have hx1 : 1 ≤ x := (Real.one_le_exp_iff).2 (by nlinarith [hβ])
  have hx2 : x * x < 2 := by
    dsimp [x]
    rw [← Real.exp_add]
    convert hδsmall using 1; ring
  have hxinv : x⁻¹ = Real.exp (-2 * ξ * δ) := by
    dsimp [x]
    calc
      (Real.exp (2 * ξ * δ))⁻¹ = Real.exp (-(2 * ξ * δ)) :=
        (Real.exp_neg _).symm
      _ = _ := by congr 1; ring
  have hL : 0 < L := by dsimp [L]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hm := amplify_collar_margin hcs hℓ hx1 hx2
  have hmargin : cs⁻¹ * L < C := by
    calc
      cs⁻¹ * L = (cs⁻¹ * x * ℓ) * sn := by dsimp [L, x]; ring
      _ < (x⁻¹ * (4 * max 1 cs⁻¹ * ℓ)) * sn := mul_lt_mul_of_pos_right hm hsn
      _ = C := by rw [hxinv]
  have hmarginDt : L < cs * C := by
    have hci : cs⁻¹ * cs = 1 := inv_mul_cancel₀ hcs.ne'
    have hmul := mul_lt_mul_of_pos_left hmargin hcs
    nlinarith [hci]
  obtain ⟨hcoll, P, hPc, hPK, hlow, hhigh, hratio⟩ := hback
  let u := P 0
  let v := P 1
  have hu : u ∈ annCl w s (2 * s) := hPK 0 (by norm_num)
  have hv : v ∈ annCl w s (2 * s) := hPK 1 (by norm_num)
  have hnot : u ≠ v := by
    intro heq
    have hpos : 0 < Real.exp (-2 * ξ * δ) * (ℓ / (2 * c1)) * sn := by
      positivity
    have hz : D.internal (ann w (3 * s / 4) (3 * s)) u u = 0 :=
      D.internal_self (amplify_core_subset_open hs w hu)
    change ENNReal.ofReal _ ≤ D.internal _ u v at hlow
    rw [← heq, hz] at hlow
    exact (not_le.mpr (ENNReal.ofReal_pos.mpr hpos)) hlow
  have hDtLE : ENNReal.ofReal (Dt.1 (u, v)) ≤ ENNReal.ofReal L := by
    calc
      ENNReal.ofReal (Dt.1 (u, v)) ≤ Dt.len P 0 1 := by
        rw [← Dt.edist_pt]
        exact edist_le_curveLength (Dt.pt ∘ P) zero_le_one
      _ ≤ ENNReal.ofReal L := hhigh
  have hDtL : Dt.1 (u, v) ≤ L :=
    (ENNReal.ofReal_le_ofReal_iff hL.le).1 hDtLE
  have hDL : D.1 (u, v) ≤ cs⁻¹ * L := by
    have hci : cs⁻¹ * cs = 1 := inv_mul_cancel₀ hcs.ne'
    calc
      D.1 (u, v) = cs⁻¹ * (cs * D.1 (u, v)) := by rw [← mul_assoc, hci, one_mul]
      _ ≤ cs⁻¹ * Dt.1 (u, v) := by gcongr; exact hcomp u v
      _ ≤ cs⁻¹ * L := by gcongr
  have hshortD : D.1 (u, v) < C := hDL.trans_lt hmargin
  have hshortDt : ENNReal.ofReal (Dt.1 (u, v)) <
      ENNReal.ofReal cs * ENNReal.ofReal C := by
    rw [← ENNReal.ofReal_mul hcs.le]
    exact hDtLE.trans_lt ((ENNReal.ofReal_lt_ofReal_iff
      (mul_pos hcs hC)).2 hmarginDt)
  obtain ⟨γ, hγ, hγ0, hγ1, hγrange, hγratio, hγlow, hγupper⟩ :=
    amplify_short_witness_to_arc D Dt hD hDt hs w hu hv hnot
      rfl rfl hcomp hcoll hshortD hshortDt hlow hratio hhigh
  refine ⟨γ, hγ, hγrange, ?_, ?_, ?_⟩
  · simpa only [hγ0, hγ1] using hγratio
  · simpa only [hγ0, hγ1] using hγlow
  · have hci : ENNReal.ofReal cs⁻¹ * ENNReal.ofReal cs = 1 := by
      rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hcs.le), inv_mul_cancel₀ hcs.ne']
      norm_num
    calc
      D.len γ 0 1 = ENNReal.ofReal cs⁻¹ *
          (ENNReal.ofReal cs * D.len γ 0 1) := by rw [← mul_assoc, hci, one_mul]
      _ ≤ ENNReal.ofReal cs⁻¹ * ENNReal.ofReal L := by gcongr
      _ = ENNReal.ofReal (cs⁻¹ * L) := by rw [ENNReal.ofReal_mul (inv_nonneg.mpr hcs.le)]
      _ ≤ _ := by
        apply le_of_eq
        congr 1
        dsimp [L]
        ring

end HigherDimLQGMetric
