import QuantumZipper.Proofs.Zipper.F1PStarShiftRegDet

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Theorem 1.3, node F1 (D29): the three clauses of `PStarShiftRegStmt`, pointwise

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, §5.1 (rule (5.1)) and §5.4
(pp. 70–72). Own elementary bookkeeping.

Deterministic setting of one realization (core P): `Z` a regular sample with
`b = scaleParam γ Z > 0`, `W''` a continuous driver with `W'' 0 = 0`, the continuum limit
(core W-C) of `Z` along every pushed circle of `W''`, `Y` a regular sample `avgReg`-equal to
`canonical γ Z`, and `W = W''(b² ·)/b` (the driver of `canonConfig γ (Z, W'')`). Then, for every
constant `k`:

* (i) `unzippedField γ (Y + k, W) t` is `RegEq` to `unzippedField γ (Y, W) t + k`;
* (ii) `Y + k` is scale consistent at the pushed circles of its canonicalized driver;
* (iii) (with W-G regularity and W-X exactness of the unzipped `Z`-fields) the field unzipped
  from `(Y + k, W)` is exact at folded circles.
-/

noncomputable section

open MeasureTheory Filter Set Function
open scoped Topology

namespace QuantumZipper
namespace F1

section Pt

variable {γ : ℝ} {Z Y : FieldSample} {W'' W : ℝ → ℝ}

/-- `RegShift` of `Y` at the pushed folded circles of `W`, from W-C for `Z`. -/
theorem regShift_pt (hZ : IsRegularSample Z) (hb : 0 < scaleParam γ Z)
    (hW'' : Continuous W'') (hW''0 : W'' 0 = 0)
    (hWdef : W = fun u => W'' (scaleParam γ Z ^ 2 * u) / scaleParam γ Z)
    (hC : ∀ t : ℝ, 0 ≤ t → ∀ (c : ℂ) (r : ℝ), 0 < r →
      ContData Z ((foldedCircle c r).map (fwdMapInv W'' t)))
    (hY : IsRegularSample Y) (havg : avgReg Y = avgReg (canonical γ Z))
    {t : ℝ} (ht : 0 ≤ t) (d : ℂ) {r : ℝ} (hr : 0 < r) :
    E1.RegShift Y ((foldedCircle d r).map (fwdMapInv W t)) := by
  set b := scaleParam γ Z with hbdef
  have hWc : Continuous W := by rw [hWdef]; fun_prop
  have hW0 : W 0 = 0 := by rw [hWdef]; simp [hW''0]
  obtain ⟨hfin, hν⟩ := fc_map_fwdMapInv_props hWc hW0 ht d hr
  refine regShift_of_contData hY hν (contData_of_dilate hb hν (C := Qc γ * Real.log b + 0)
    (fun u hu ρ hρ => evalReg_fc_of_avgReg_rescale hZ (Qc γ) hb 0
      (by rw [addConst_zero']; exact havg) hu hρ) ?_)
  rw [hWdef, WedgeUnzip.map_mul_fc_map_fwdMapInv_scale hW'' hW''0 hb ht d hr]
  exact hC _ (mul_nonneg (sq_nonneg _) ht) _ _ (mul_pos hb hr)

/-- **Clause (i)**: unzipping commutes with the constant shift. -/
theorem clause1_pt (hZ : IsRegularSample Z) (hb : 0 < scaleParam γ Z)
    (hW'' : Continuous W'') (hW''0 : W'' 0 = 0)
    (hWdef : W = fun u => W'' (scaleParam γ Z ^ 2 * u) / scaleParam γ Z)
    (hC : ∀ t : ℝ, 0 ≤ t → ∀ (c : ℂ) (r : ℝ), 0 < r →
      ContData Z ((foldedCircle c r).map (fwdMapInv W'' t)))
    (hY : IsRegularSample Y) (havg : avgReg Y = avgReg (canonical γ Z)) (k : ℝ)
    {t : ℝ} (ht : 0 ≤ t) :
    RegEq (unzippedField γ (addConst Y k, W) t) (addConst (unzippedField γ (Y, W) t) k) :=
  regEq_unzippedField_addConst_of_regShift fun d _ _ hr =>
    regShift_pt hZ hb hW'' hW''0 hWdef hC hY havg ht d hr

/-- **Clause (ii)**: scale consistency of `Y + k` at the pushed circles of its canonicalized
driver. -/
theorem clause2_pt (hZ : IsRegularSample Z) (hb : 0 < scaleParam γ Z)
    (hW'' : Continuous W'') (hW''0 : W'' 0 = 0)
    (hWdef : W = fun u => W'' (scaleParam γ Z ^ 2 * u) / scaleParam γ Z)
    (hWmax : ∀ s, W (max s 0) = W s)
    (hC : ∀ t : ℝ, 0 ≤ t → ∀ (c : ℂ) (r : ℝ), 0 < r →
      ContData Z ((foldedCircle c r).map (fwdMapInv W'' t)))
    (hY : IsRegularSample Y) (havg : avgReg Y = avgReg (canonical γ Z)) (k : ℝ)
    (ha : 0 < scaleParam γ (addConst Y k)) {s : ℝ} (hs : 0 ≤ s) (d : ℂ) {r : ℝ} (hr : 0 < r) :
    Thm18Asm.G1.ScaleConsistentAt (addConst Y k) (Qc γ) (scaleParam γ (addConst Y k))
      ((foldedCircle d r).map (fwdMapInv (canonConfig γ (addConst Y k, W)).2 s)) := by
  set b := scaleParam γ Z with hbdef
  set a := scaleParam γ (addConst Y k) with hadef
  have hWc : Continuous W := by rw [hWdef]; fun_prop
  have hW0 : W 0 = 0 := by rw [hWdef]; simp [hW''0]
  have has : 0 ≤ a ^ 2 * s := mul_nonneg (sq_nonneg a) hs
  have hcZ : IsRegularSample (canonical γ Z) := hZ.rescale' (Qc γ) hb
  have havgk : avgReg (addConst Y k) = avgReg (addConst (rescale Z (Qc γ) b) k) :=
    avgReg_addConst_congr_of_isRegularSample hY hcZ havg k
  obtain ⟨hfin, hμ⟩ := fc_map_fwdMapInv_props hWc hW0 has ((a : ℂ) * d) (mul_pos ha hr)
  have hZ' : ContData Z
      (((foldedCircle ((a : ℂ) * d) (a * r)).map (fwdMapInv W (a ^ 2 * s))).map
        fun z => (b : ℂ) * z) := by
    rw [hWdef, WedgeUnzip.map_mul_fc_map_fwdMapInv_scale hW'' hW''0 hb has _ (mul_pos ha hr)]
    exact hC _ (mul_nonneg (sq_nonneg _) has) _ _ (mul_pos hb (mul_pos ha hr))
  obtain ⟨hint, hcont⟩ := contData_of_dilate hb hμ (C := Qc γ * Real.log b + k)
    (fun u hu ρ hρ => evalReg_fc_of_avgReg_rescale hZ (Qc γ) hb k havgk hu hρ) hZ'
  rw [B3d.canonConfig_snd_of_max hWmax]
  exact WedgeUnzip.scaleConsistent_of_continuum (hY.addConst' k) (Qc γ) hWc hW0 ha hs d hr
    hint hcont

/-- **Clause (iii)**: exactness of the fields unzipped from `(Y + k, W)` at folded circles. -/
theorem clause3_pt (hZ : IsRegularSample Z) (hb : 0 < scaleParam γ Z)
    (hW'' : Continuous W'') (hW''0 : W'' 0 = 0) (hW''max : ∀ s, W'' (max s 0) = W'' s)
    (hcfg : canonConfig γ (Z, W'') = (canonical γ Z, W))
    (hWdef : W = fun u => W'' (scaleParam γ Z ^ 2 * u) / scaleParam γ Z)
    (hC : ∀ t : ℝ, 0 ≤ t → ∀ (c : ℂ) (r : ℝ), 0 < r →
      ContData Z ((foldedCircle c r).map (fwdMapInv W'' t)))
    (hG : ∀ t : ℝ, 0 ≤ t → IsRegularSample (unzippedField γ (Z, W'') t))
    (hE : ∀ t : ℝ, 0 ≤ t → ∀ d ∈ Hbar, ∀ r > 0,
      evalReg (unzippedField γ (Z, W'') t) (foldedCircle d r) =
        unzippedField γ (Z, W'') t (foldedCircle d r))
    (hY : IsRegularSample Y) (havg : avgReg Y = avgReg (canonical γ Z)) (k : ℝ)
    {τ : ℝ} (hτ : 0 ≤ τ) {d : ℂ} (hd : d ∈ Hbar) {r : ℝ} (hr : 0 < r) :
    evalReg (unzippedField γ (addConst Y k, W) τ) (foldedCircle d r) =
      unzippedField γ (addConst Y k, W) τ (foldedCircle d r) := by
  set b := scaleParam γ Z with hbdef
  have hbτ : 0 ≤ b ^ 2 * τ := mul_nonneg (sq_nonneg b) hτ
  set Uz := unzippedField γ (Z, W'') (b ^ 2 * τ) with hUz
  -- the unshifted `P_*` unzipped field agrees with `rescale Uz` on folded circles
  have e1 : unzippedField γ (Y, W) τ = unzippedField γ (canonConfig γ (Z, W'')) τ := by
    rw [hcfg]
    exact Factorization.coordChange_congr havg _ _
  have hraw : ∀ (d : ℂ) (r : ℝ), 0 < r → unzippedField γ (Y, W) τ (foldedCircle d r) =
      rescale Uz (Qc γ) b (foldedCircle d r) := by
    rw [e1]
    refine WedgeUnzip.unzippedField_canonConfig_fc hW'' hW''0 hW''max hb hτ
      (fun d r hr => ?_) (hE _ hbτ)
    rw [B3d.canonConfig_snd_of_max hW''max]
    have hC' := hC _ hbτ ((b : ℂ) * d) _ (mul_pos hb hr)
    exact WedgeUnzip.scaleConsistent_of_continuum hZ _ hW'' hW''0 hb hτ d hr hC'.1 hC'.2
  -- raw value of the shifted field
  have hUfc : unzippedField γ (addConst Y k, W) τ (foldedCircle d r) =
      unzippedField γ (Y, W) τ (foldedCircle d r) + k :=
    F2.coordChange_addConst_fc k (regShift_pt hZ hb hW'' hW''0 hWdef hC hY havg hτ d hr)
  -- regularized value of the shifted field
  have h1 : evalReg (unzippedField γ (addConst Y k, W) τ) =
      evalReg (addConst (unzippedField γ (Y, W) τ) k) :=
    Factorization.evalReg_congr
      (B3d.avgReg_eq_of_regEq (clause1_pt hZ hb hW'' hW''0 hWdef hC hY havg k hτ))
  have h2 : evalReg (addConst (unzippedField γ (Y, W) τ) k) =
      evalReg (addConst (rescale Uz (Qc γ) b) k) := by
    refine Factorization.evalReg_congr (B3d.avgReg_eq_of_regEq
      (S5.FieldShift.regEq_of_fc fun d' _ r' hr' => ?_))
    simp only [addConst]
    rw [hraw d' r' hr']
  have h3 := evalReg_fc_of_avgReg_rescale (hG _ hbτ) (Qc γ) hb k rfl hd hr
  have h4 : rescale Uz (Qc γ) b (foldedCircle d r) =
      evalReg Uz (foldedCircle ((b : ℂ) * d) (b * r)) + Qc γ * Real.log b := by
    rw [Thm18Asm.G1.rescale_fc_apply Uz (Qc γ) hb d r,
      CircleFubini.foldH_of_mem' (RegClosure.mapsTo_mul_pos hb hd)]
  rw [h1, h2, h3, hUfc, hraw d r hr, h4]
  ring

end Pt

end F1
end QuantumZipper
