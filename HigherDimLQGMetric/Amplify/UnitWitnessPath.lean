import HigherDimLQGMetric.Amplify.UnitWitness

/-! Physical-coordinate witness obtained from a unit-scale witness. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace HigherDimLQGMetric

open Set
open HigherDimLFPP (Rd)
open scoped ENNReal

variable {d : ℕ}

/-- Reading a unit witness back at an arbitrary center and scale. -/
theorem amplify_witEvent_of_unitWit
    (ξ Q U a A₀ ℓ β₀ t : ℝ)
    (A B : DistRd d → ContMetric d) (X : DistRd d)
    {r : ℝ} (hr : 0 < r) (z : Rd d)
    (hunit : AmplifyUnitWit
      (weakScaledMetric ξ A (fun x => x ^ (ξ * Q)) X hr z
        (Real.rpow_pos_of_pos hr _))
      (weakScaledMetric ξ B (fun x => x ^ (ξ * Q)) X hr z
        (Real.rpow_pos_of_pos hr _)) U a A₀ ℓ β₀ t) :
    X ∈ WitEvent A B ξ Q U a A₀ ℓ β₀ t r z := by
  let MA := weakScaledMetric ξ A (fun x => x ^ (ξ * Q)) X hr z
    (Real.rpow_pos_of_pos hr _)
  let MB := weakScaledMetric ξ B (fun x => x ^ (ξ * Q)) X hr z
    (Real.rpow_pos_of_pos hr _)
  let sn := sNorm ξ Q X r z
  have hsn : 0 < sn := sNorm_pos ξ Q X hr z
  have hcoef0 : ENNReal.ofReal sn⁻¹ ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (inv_pos.mpr hsn)).ne'
  have hcoefT : ENNReal.ofReal sn⁻¹ ≠ ⊤ := ENNReal.ofReal_ne_top
  rcases hunit with ⟨hreg, P, hPI, hgeo, hlow, hhigh, hratio⟩
  let R : ℝ → Rd d := fun u => r • P u + z
  have hRcont : ContinuousOn R (Icc (0 : ℝ) 1) := by
    have hm : ContinuousOn (fun u => r • P u) (Icc (0 : ℝ) 1) :=
      (continuousOn_const : ContinuousOn (fun _ : ℝ => r) (Icc 0 1)).smul hgeo.1
    exact hm.add continuousOn_const
  have hRI : ∀ τ ∈ Icc (0 : ℝ) 1, R τ ∈ annCl z r (2 * r) := by
    intro τ hτ
    have hi := image_annCl_affine hr z 1 2
    have hx : R τ ∈ (fun x : Rd d => r • x + z) '' annCl 0 1 2 :=
      ⟨P τ, hPI τ hτ, rfl⟩
    convert hi ▸ hx using 1; all_goals ring
  have hRO : ∀ τ ∈ Icc (0 : ℝ) 1,
      R τ ∈ ann z (3 * r / 4) (3 * r) := by
    intro τ hτ
    have h := hgeo.2.1 τ hτ
    have hi := image_ann_affine hr z (3 / 4) 3
    have hx : R τ ∈ (fun x : Rd d => r • x + z) '' ann 0 (3 / 4) 3 :=
      ⟨P τ, h, rfl⟩
    convert hi ▸ hx using 1; all_goals ring
  have hlen : MA.len P 0 1 = ENNReal.ofReal sn⁻¹ * (A X).len R 0 1 := by
    exact amplify_len_sharpScaledMetric ξ Q A X hr z P
  have hIA : MA.internal (ann 0 (3 / 4) 3) (P 0) (P 1) =
      ENNReal.ofReal sn⁻¹ *
        (A X).internal (ann z (3 * r / 4) (3 * r)) (R 0) (R 1) := by
    rw [sharpScaledMetric_internal, image_ann_affine hr z]
    congr 3 <;> ring
  have hIB : MB.internal (ann 0 (3 / 4) 3) (P 0) (P 1) =
      ENNReal.ofReal sn⁻¹ *
        (B X).internal (ann z (3 * r / 4) (3 * r)) (R 0) (R 1) := by
    rw [sharpScaledMetric_internal, image_ann_affine hr z]
    congr 3 <;> ring
  have hgeoscale : ENNReal.ofReal sn⁻¹ * (A X).len R 0 1 =
      ENNReal.ofReal sn⁻¹ *
        (A X).internal (ann z (3 * r / 4) (3 * r)) (R 0) (R 1) := by
    rw [← hlen, ← hIA]
    exact hgeo.2.2
  have hRgeo : IsGeodIn (A X) (ann z (3 * r / 4) (3 * r)) R := by
    refine ⟨hRcont, hRO, ?_⟩
    apply le_antisymm
    · exact (ENNReal.mul_le_mul_iff_right hcoef0 hcoefT).1 hgeoscale.le
    · exact (ENNReal.mul_le_mul_iff_right hcoef0 hcoefT).1 hgeoscale.ge
  have hRegFull := regEvent_of_unitReg ξ Q U a A₀ ℓ β₀ A B X hr z hreg
  refine ⟨hRegFull, R, hRI, hRgeo, ?_, ?_, ?_⟩
  · exact (amplify_scale_lower_iff hsn).2 (hlen ▸ hlow)
  · exact (amplify_scale_upper_iff hsn).2 (hlen ▸ hhigh)
  · have hs : ENNReal.ofReal sn⁻¹ *
        (ENNReal.ofReal t * (A X).len R 0 1) <
        ENNReal.ofReal sn⁻¹ *
          (B X).internal (ann z (3 * r / 4) (3 * r)) (R 0) (R 1) := by
      calc
        ENNReal.ofReal sn⁻¹ * (ENNReal.ofReal t * (A X).len R 0 1) =
            ENNReal.ofReal t * MA.len P 0 1 := by rw [hlen]; ac_rfl
        _ < MB.internal (ann 0 (3 / 4) 3) (P 0) (P 1) := hratio
        _ = ENNReal.ofReal sn⁻¹ *
            (B X).internal (ann z (3 * r / 4) (3 * r)) (R 0) (R 1) := hIB
    exact (ENNReal.mul_lt_mul_iff_right hcoef0 hcoefT).1 hs

/-- The witness hypothesis can conversely be read as a unit-scale statement
about the two centered metrics. -/
theorem amplify_unitWit_of_witEvent
    (ξ Q U a A₀ ℓ β₀ t : ℝ)
    (A B : DistRd d → ContMetric d) (X : DistRd d)
    {r : ℝ} (hr : 0 < r) (z : Rd d)
    (hW : X ∈ WitEvent A B ξ Q U a A₀ ℓ β₀ t r z) :
    AmplifyUnitWit
      (weakScaledMetric ξ A (fun x => x ^ (ξ * Q)) X hr z
        (Real.rpow_pos_of_pos hr _))
      (weakScaledMetric ξ B (fun x => x ^ (ξ * Q)) X hr z
        (Real.rpow_pos_of_pos hr _)) U a A₀ ℓ β₀ t := by
  let MA := weakScaledMetric ξ A (fun x => x ^ (ξ * Q)) X hr z
    (Real.rpow_pos_of_pos hr _)
  let MB := weakScaledMetric ξ B (fun x => x ^ (ξ * Q)) X hr z
    (Real.rpow_pos_of_pos hr _)
  let sn := sNorm ξ Q X r z
  have hsn : 0 < sn := sNorm_pos ξ Q X hr z
  rcases hW with ⟨hreg, R, hRI, hgeo, hlow, hhigh, hratio⟩
  let P : ℝ → Rd d := fun u => r⁻¹ • (R u - z)
  have hpoint (u : ℝ) : r • P u + z = R u := by
    simp only [P, smul_smul, mul_inv_cancel₀ hr.ne', one_smul, sub_add_cancel]
  have hPcont : ContinuousOn P (Icc (0 : ℝ) 1) := by
    have hsub : ContinuousOn (fun u => R u - z) (Icc (0 : ℝ) 1) :=
      hgeo.1.sub continuousOn_const
    exact (continuousOn_const : ContinuousOn (fun _ : ℝ => r⁻¹) (Icc 0 1)).smul hsub
  have hnorm (u : ℝ) : ‖P u‖ = r⁻¹ * ‖R u - z‖ := by
    change ‖r⁻¹ • (R u - z)‖ = _
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr]
  have hPI : ∀ τ ∈ Icc (0 : ℝ) 1, P τ ∈ annCl 0 1 2 := by
    intro τ hτ
    have h := hRI τ hτ
    dsimp [annCl] at h ⊢
    rw [sub_zero, hnorm, inv_mul_eq_div]
    exact ⟨(le_div_iff₀ hr).2 (by nlinarith [h.1]),
      (div_le_iff₀ hr).2 (by nlinarith [h.2])⟩
  have hPO : ∀ τ ∈ Icc (0 : ℝ) 1, P τ ∈ ann 0 (3 / 4) 3 := by
    intro τ hτ
    have h := hgeo.2.1 τ hτ
    dsimp [ann] at h ⊢
    rw [sub_zero, hnorm, inv_mul_eq_div]
    exact ⟨(lt_div_iff₀ hr).2 (by nlinarith [h.1]),
      (div_lt_iff₀ hr).2 (by nlinarith [h.2])⟩
  have hlen : MA.len P 0 1 = ENNReal.ofReal sn⁻¹ * (A X).len R 0 1 := by
    rw [amplify_len_sharpScaledMetric]
    have hf : (fun u => r • P u + z) = R := funext hpoint
    rw [hf]
  have hIA : MA.internal (ann 0 (3 / 4) 3) (P 0) (P 1) =
      ENNReal.ofReal sn⁻¹ *
        (A X).internal (ann z (3 * r / 4) (3 * r)) (R 0) (R 1) := by
    rw [sharpScaledMetric_internal, image_ann_affine hr z]
    simp only [hpoint]
    congr 3 <;> ring
  have hIB : MB.internal (ann 0 (3 / 4) 3) (P 0) (P 1) =
      ENNReal.ofReal sn⁻¹ *
        (B X).internal (ann z (3 * r / 4) (3 * r)) (R 0) (R 1) := by
    rw [sharpScaledMetric_internal, image_ann_affine hr z]
    simp only [hpoint]
    congr 3 <;> ring
  have hRegUnit := amplify_unitReg_of_regEvent ξ Q U a A₀ ℓ β₀ A B X hr z hreg
  refine ⟨hRegUnit, P, hPI, ⟨hPcont, hPO, ?_⟩, ?_, ?_, ?_⟩
  · rw [hlen, hIA]
    exact congrArg (fun v : ℝ≥0∞ => ENNReal.ofReal sn⁻¹ * v) hgeo.2.2
  · rw [hlen]
    exact (amplify_scale_lower_iff hsn).1 hlow
  · rw [hlen]
    exact (amplify_scale_upper_iff hsn).1 hhigh
  · rw [hlen, hIB]
    have hm := ENNReal.mul_lt_mul_left
      (ENNReal.ofReal_pos.mpr (inv_pos.mpr hsn)).ne'
      ENNReal.ofReal_ne_top hratio
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hm

end HigherDimLQGMetric
