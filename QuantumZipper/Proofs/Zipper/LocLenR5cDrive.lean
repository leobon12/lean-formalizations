import QuantumZipper.Proofs.Zipper.LocLenR5cComap

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R5c (D75): B5 locality for `zipLenDownArc` from local hitting time and scale

Open-arc copy (`handoff/FOLLOW-PAPER-13.md`, task R5c) of `MeasUnzipDrive.lean:40–105`,
`LocRichComapField.lean:229–243`, `LocRichComapMain.lean` and `LocRichComapPath.lean:166`, with
`zipLenDown ↦ zipLenDownArc`, `tHit ↦ lenTimeArc`, `unzipLengths ↦ unzipLengthsArc`. The only
changed analytic input is `LocLen.unzipLengthsArc_eq_of_drive_eqOn`.

Main results: `LocHitScaleArcStmt`, `locRichComapAEArc_of_hitScale`,
**`localAbsRichArcStmt_of_hitScale`**. Own elementary bookkeeping, as for the originals
(Sheffield arXiv:1012.4797 §5.4, pp. 70–72, asserts the locality without proof).
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped NNReal ENNReal Topology

namespace QuantumZipper.LocLen.R5c

open E6 D3Plus MeasUnzip CharFun Factorization

theorem locRich_zipLenDownArc_eq (γ ℓ : ℝ) (R : ℕ) (c : FieldSample × (ℝ → ℝ)) :
    locRich R (zipLenDownArc γ ℓ c) =
      (locFieldFull R (rescale (unzippedField γ c (lenTimeArc γ ℓ c)) (Qc γ)
        (scaleParam γ (unzippedField γ c (lenTimeArc γ ℓ c)))),
        fun s : ℝ≥0 => (c.2 (lenTimeArc γ ℓ c +
          scaleParam γ (unzippedField γ c (lenTimeArc γ ℓ c)) ^ 2 *
          max (min (s : ℝ) R) 0) - c.2 (lenTimeArc γ ℓ c)) /
          scaleParam γ (unzippedField γ c (lenTimeArc γ ℓ c))) := rfl

/-- Copy of the first steps of `MeasUnzip.locRich_zipLenDown_congr_drive`: the open-arc hitting
time only sees the driver on `[0,T]`. -/
theorem lenTimeArc_congr_drive {γ ℓ T : ℝ} (x : FieldSample) {W W' : ℝ → ℝ}
    (hW : Continuous W) (hW' : Continuous W') (hW0 : W 0 = 0) (hW0' : W' 0 = 0)
    (h : ∀ r ∈ Icc (0 : ℝ) T, W r = W' r)
    (hreach : ∃ s ∈ Icc (0 : ℝ) T, ENNReal.ofReal ℓ ≤ (unzipLengthsArc γ (x, W) s).1) :
    lenTimeArc γ ℓ (x, W') = lenTimeArc γ ℓ (x, W) ∧ lenTimeArc γ ℓ (x, W) ∈ Icc (0 : ℝ) T := by
  obtain ⟨s0, hs0, hl0⟩ := hreach
  have hT : 0 ≤ T := hs0.1.trans hs0.2
  have hL : ∀ s ∈ Icc (0 : ℝ) T, unzipLengthsArc γ (x, W) s = unzipLengthsArc γ (x, W') s :=
    fun s hs => unzipLengthsArc_eq_of_drive_eqOn x hW hW' hW0 hW0' hs.1
      fun r hr => h r ⟨hr.1, hr.2.trans hs.2⟩
  have hmin : ∀ s : ℝ, 0 ≤ s → min s T ∈ Icc (0 : ℝ) T := fun s hs =>
    ⟨le_min hs hT, min_le_right _ _⟩
  have e1 := sInf_hit_min_eq (L := fun s => (unzipLengthsArc γ (x, W) s).1)
    (ℓ := ENNReal.ofReal ℓ) hT ⟨s0, hs0, hl0⟩
  have e2 := sInf_hit_min_eq (L := fun s => (unzipLengthsArc γ (x, W') s).1)
    (ℓ := ENNReal.ofReal ℓ) hT ⟨s0, hs0, by rw [← hL s0 hs0]; exact hl0⟩
  have e3 : {s : ℝ | 0 ≤ s ∧ ENNReal.ofReal ℓ ≤ (unzipLengthsArc γ (x, W) (min s T)).1} =
      {s : ℝ | 0 ≤ s ∧ ENNReal.ofReal ℓ ≤ (unzipLengthsArc γ (x, W') (min s T)).1} := by
    ext s
    constructor
    · rintro ⟨hs, hl⟩; exact ⟨hs, by rw [← hL _ (hmin s hs)]; exact hl⟩
    · rintro ⟨hs, hl⟩; exact ⟨hs, by rw [hL _ (hmin s hs)]; exact hl⟩
  refine ⟨?_, ?_⟩
  · simp only [lenTimeArc]
    rw [← e1, ← e2, e3]
  · have hmem : s0 ∈ {s : ℝ | 0 ≤ s ∧ ENNReal.ofReal ℓ ≤ (unzipLengthsArc γ (x, W) s).1} :=
      ⟨hs0.1, hl0⟩
    exact ⟨le_csInf ⟨s0, hmem⟩ fun s hs => hs.1, (csInf_le ⟨0, fun _ h => h.1⟩ hmem).trans hs0.2⟩

/-- Unzipped fields at a common time `t ≤ T` of two drivers agreeing on `[0,T]` have the same
regularized averages (step of `MeasUnzip.locRich_zipLenDown_congr_drive`). -/
theorem avgReg_unzippedField_congr_drive {γ T t : ℝ} (x : FieldSample) {W W' : ℝ → ℝ}
    (hW : Continuous W) (hW' : Continuous W') (hW0 : W 0 = 0) (hW0' : W' 0 = 0)
    (h : ∀ r ∈ Icc (0 : ℝ) T, W r = W' r) (hti : t ∈ Icc (0 : ℝ) T) :
    avgReg (unzippedField γ (x, W) t) = avgReg (unzippedField γ (x, W') t) := by
  have hψ := ESM.fwdMapInv_eqOn_of_drive_eqOn hW hW' hW0 hW0' hti.1
    fun r hr => h r ⟨hr.1, hr.2.trans hti.2⟩
  funext k z
  unfold avgReg
  congr 1
  funext n
  exact UnzipInvariance.coordChange_congr_of_eqOn hψ
    (ESM.foldedCircle_compl_H_eq_zero _ (radius_pos k)) x (Qc γ)

/-- Copy of `E6.tHit_scale_congr_drive` (LocRichComapMain.lean:32). -/
theorem lenTimeArc_scale_congr_drive {γ ℓ T : ℝ} (x : FieldSample) {W W' : ℝ → ℝ}
    (hW : Continuous W) (hW' : Continuous W') (hW0 : W 0 = 0) (hW0' : W' 0 = 0)
    (h : ∀ r ∈ Icc (0 : ℝ) T, W r = W' r)
    (hreach : ∃ s ∈ Icc (0 : ℝ) T, ENNReal.ofReal ℓ ≤ (unzipLengthsArc γ (x, W) s).1) :
    lenTimeArc γ ℓ (x, W') = lenTimeArc γ ℓ (x, W) ∧
      scaleParam γ (unzippedField γ (x, W') (lenTimeArc γ ℓ (x, W))) =
        scaleParam γ (unzippedField γ (x, W) (lenTimeArc γ ℓ (x, W))) := by
  obtain ⟨hτ, hti⟩ := lenTimeArc_congr_drive x hW hW' hW0 hW0' h hreach
  exact ⟨hτ, (scaleParam_congr
    (avgReg_unzippedField_congr_drive x hW hW' hW0 hW0' h hti) γ).symm⟩

/-- Copy of `MeasUnzip.locRich_zipLenDown_congr_drive` (MeasUnzipDrive.lean:49). -/
theorem locRich_zipLenDownArc_congr_drive {γ ℓ T : ℝ} (R : ℕ) (x : FieldSample)
    {W W' : ℝ → ℝ}
    (hW : Continuous W) (hW' : Continuous W') (hW0 : W 0 = 0) (hW0' : W' 0 = 0)
    (h : ∀ r ∈ Icc (0 : ℝ) T, W r = W' r)
    (hreach : ∃ s ∈ Icc (0 : ℝ) T, ENNReal.ofReal ℓ ≤ (unzipLengthsArc γ (x, W) s).1)
    (hRT : lenTimeArc γ ℓ (x, W) +
      scaleParam γ (unzippedField γ (x, W) (lenTimeArc γ ℓ (x, W))) ^ 2 * R ≤ T) :
    locRich R (zipLenDownArc γ ℓ (x, W)) = locRich R (zipLenDownArc γ ℓ (x, W')) := by
  obtain ⟨hτ, hti⟩ := lenTimeArc_congr_drive x hW hW' hW0 hW0' h hreach
  set t := lenTimeArc γ ℓ (x, W) with htdef
  have hav := avgReg_unzippedField_congr_drive (γ := γ) x hW hW' hW0 hW0' h hti
  have hsc := scaleParam_congr hav γ
  have hr := coordChange_congr hav
    (fun z => ((scaleParam γ (unzippedField γ (x, W) t) : ℝ) : ℂ) * z) (Qc γ)
  rw [locRich_zipLenDownArc_eq, locRich_zipLenDownArc_eq, hτ, ← hsc]
  refine Prod.ext ?_ (funext fun s => ?_)
  · show locFieldFull R (rescale _ _ _) = locFieldFull R (rescale _ _ _)
    unfold rescale
    rw [hr]
  · have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg R
    have hm0 : 0 ≤ max (min (s : ℝ) R) 0 := le_max_right _ _
    have hmR : max (min (s : ℝ) R) 0 ≤ R := max_le (min_le_right _ _) hR0
    have ha2 : 0 ≤ scaleParam γ (unzippedField γ (x, W) t) ^ 2 := sq_nonneg _
    have hin : t + scaleParam γ (unzippedField γ (x, W) t) ^ 2 * max (min (s : ℝ) R) 0 ∈
        Icc (0 : ℝ) T :=
      ⟨add_nonneg hti.1 (mul_nonneg ha2 hm0),
        le_trans (add_le_add_right (mul_le_mul_of_nonneg_left hmR ha2) t) hRT⟩
    show (W _ - W t) / _ = (W' _ - W' t) / _
    rw [h _ hin, h t hti]

/-- Copy of `E6.locRich_zipLenDown_eq_loc` (LocRichComapField.lean:229). -/
theorem locRich_zipLenDownArc_eq_loc {T : ℝ} (hT : 0 ≤ T) {γ κ : ℝ} {R R' : ℕ} {ℓ : ℝ}
    {f : C(Icc (0 : ℝ) T, ℝ)} (hf : f ∈ PZ hT κ)
    (x : FieldSample) {t a : ℝ} (ht : lenTimeArc γ ℓ (x, Wof κ T hT f) = t)
    (hti : t ∈ Icc (0 : ℝ) T)
    (ha : scaleParam γ (unzippedField γ (x, Wof κ T hT f) t) = a) (ha0 : 0 < a)
    (hflow : ∀ u ∈ H, ‖u‖ ≤ a * R + 3 → ‖fwdMapInv (Wof κ T hT f) t u‖ + 3 ≤ R') :
    locRich R (zipLenDownArc γ ℓ (x, Wof κ T hT f)) =
      (locFieldFull R (rescale (ufJ hT γ κ ((f, locField R' (locFieldFull R' x)), t)) (Qc γ) a),
        drvJ hT κ R (f, t, a)) := by
  rw [locRich_zipLenDownArc_eq, ht, ha]
  refine Prod.ext ?_ rfl
  show locFieldFull R (rescale (unzippedField γ (x, Wof κ T hT f) t) (Qc γ) a) = _
  rw [locFieldFull_rescale_ufJ_locField hT hf hti x ha0 hflow]
  have hr : rescale (ufJ hT γ κ ((f, x), t)) (Qc γ) a =
      rescale (unzippedField γ (x, Wof κ T hT f) t) (Qc γ) a :=
    Factorization.coordChange_congr (avgReg_ufJ hT γ κ hf hti x) _ _
  rw [hr]

variable {Ω' : Type*} [MeasurableSpace Ω']

/-- Copy of `E6.LocHitScaleStmt` (LocRichComapMain.lean:93) with open-arc lengths. -/
def LocHitScaleArcStmt (γ ℓ : ℝ) (P' : Measure Ω') (c' : Ω' → Cfg) : Prop :=
  ∀ R : ℕ, ∀ ε : ℝ≥0∞, 0 < ε → ∃ T R' : ℕ, ∃ M : ℝ, ∃ A : Set FullData,
    ∃ τ' a' : FullData → ℝ, T ≤ R' ∧ MeasurableSet A ∧ Measurable τ' ∧ Measurable a' ∧
    P' {ω' | locRich R' (c' ω') ∉ A} ≤ ε ∧
    ∀ᵐ ω' ∂P', locRich R' (c' ω') ∈ A →
      (∀ r ∈ Icc (0 : ℝ) T, |(c' ω').2 r| ≤ M) ∧
      (∃ s ∈ Icc (0 : ℝ) T, ENNReal.ofReal ℓ ≤ (unzipLengthsArc γ (c' ω') s).1) ∧
      0 < lenTimeArc γ ℓ (c' ω') ∧ τ' (locRich R' (c' ω')) = lenTimeArc γ ℓ (c' ω') ∧
      0 < scaleParam γ (unzippedField γ (c' ω') (lenTimeArc γ ℓ (c' ω'))) ∧
      a' (locRich R' (c' ω')) =
        scaleParam γ (unzippedField γ (c' ω') (lenTimeArc γ ℓ (c' ω'))) ∧
      lenTimeArc γ ℓ (c' ω') +
          scaleParam γ (unzippedField γ (c' ω') (lenTimeArc γ ℓ (c' ω'))) ^ 2 * R ≤ T ∧
      scaleParam γ (unzippedField γ (c' ω') (lenTimeArc γ ℓ (c' ω'))) * R + 6 * M +
          6 * Real.sqrt T + 6 ≤ R'

/-- Copy of `E6.locRichComapAE_of_hitScale` (LocRichComapMain.lean:110). -/
theorem locRichComapAEArc_of_hitScale {γ κ ℓ : ℝ} {P' : Measure Ω'} {c' : Ω' → Cfg}
    {π : ∀ T : ℕ, (ℝ≥0 → ℝ) → C(Icc (0 : ℝ) T, ℝ)} (hπ : PathExtract κ π)
    (hc : ∀ᵐ ω' ∂P', Continuous (c' ω').2) (h0 : ∀ᵐ ω' ∂P', (c' ω').2 0 = 0)
    (hS : LocHitScaleArcStmt γ ℓ P' c') : LocRichComapAEArcStmt γ ℓ P' c' := by
  intro R ε hε
  obtain ⟨T, R', M, A, τ', a', hTR, hA, hτm, ham, hPA, hgood⟩ := hS R ε hε
  have hT : (0 : ℝ) ≤ T := Nat.cast_nonneg T
  have hTR' : (T : ℝ) ≤ R' := by exact_mod_cast hTR
  set G : FullData → FullData := fun d => outLoc hT γ κ R R' (π T) (d, τ' d, a' d) with hGdef
  have hG : Measurable G :=
    (measurable_outLoc hT γ κ R R' (hπ.1 T)).comp (measurable_id.prodMk (hτm.prodMk ham))
  refine ⟨R', A, fun y => G (locRich R' y), hA, hPA, hG.comp (comap_measurable _), ?_⟩
  filter_upwards [hgood, hc, h0] with ω' hω hcω h0ω hωA
  obtain ⟨hM, hreach, ht0, hτ, ha0, ha, hRT, hR'⟩ := hω hωA
  generalize c' ω' = y at hM hreach ht0 hτ ha0 ha hRT hR' hcω h0ω ⊢
  obtain ⟨x, W⟩ := y
  simp only at hM hreach ht0 hτ ha0 ha hRT hR' hcω h0ω ⊢
  set f := π T (locRich R' (x, W)).2 with hfdef
  set t := lenTimeArc γ ℓ (x, W) with htdef
  set a := scaleParam γ (unzippedField γ (x, W) t) with hadef
  have hWf : ∀ r ∈ Icc (0 : ℝ) T, Wof κ T hT f r = W r :=
    hπ.2 T _ W hcω fun s hs => by
      show W (min (s : ℝ) R') = W s
      rw [min_eq_left (hs.trans hTR')]
  have hWof0 : Wof κ T hT f 0 = 0 := (hWf 0 ⟨le_rfl, hT⟩).trans h0ω
  have hf : f ∈ PZ hT κ := hWof0
  have hcWof := continuous_Wof κ T hT f
  obtain ⟨hτ', hsc'⟩ := lenTimeArc_scale_congr_drive x hcω hcWof h0ω hWof0
    (fun r hr => (hWf r hr).symm) hreach
  have step1 := locRich_zipLenDownArc_congr_drive R x hcω hcWof h0ω hWof0
    (fun r hr => (hWf r hr).symm) hreach hRT
  have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg R
  have hti : t ∈ Icc (0 : ℝ) T :=
    ⟨ht0.le, le_trans (le_add_of_nonneg_right (by positivity)) hRT⟩
  have hflow : ∀ u ∈ H, ‖u‖ ≤ a * R + 3 → ‖fwdMapInv (Wof κ T hT f) t u‖ + 3 ≤ R' := by
    intro u hu hub
    have hb := B5.norm_fwdMapInv_sub_le hcWof hWof0 ht0 (M := M) (fun r hr => by
      rw [hWf r ⟨hr.1, hr.2.trans hti.2⟩]; exact hM r ⟨hr.1, hr.2.trans hti.2⟩) hu
    have h1 := norm_sub_norm_le (fwdMapInv (Wof κ T hT f) t u) u
    have h2 : Real.sqrt t ≤ Real.sqrt T := Real.sqrt_le_sqrt hti.2
    linarith
  rw [step1, locRich_zipLenDownArc_eq_loc hT hf x hτ' hti hsc' ha0 hflow]
  show _ = outLoc hT γ κ R R' (π T)
    (locRich R' (x, W), τ' (locRich R' (x, W)), a' (locRich R' (x, W)))
  rw [hτ, ha]
  rfl

/-- Copy of `E6.localAbsRichStmt_of_hitScale` (LocRichComapPath.lean:166). -/
theorem localAbsRichArcStmt_of_hitScale
    (h : ∀ (κ : ℝ) {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
      (Y : Ω' → FieldSample) (B' : ℝ≥0 → Ω' → ℝ), Thm13Asm.IsPStarSample κ P' Y B' →
      ∀ ℓ₁ : ℝ, 0 < ℓ₁ →
        LocHitScaleArcStmt (Real.sqrt κ) ℓ₁ P' (fun ω' => (Y ω', drive κ B' ω'))) :
    LocalAbsRichArcStmt := by
  refine localAbsRichArcStmt_of_ae ?_
  intro κ Ω' _ P' _ Y B' hP ℓ₁ hℓ
  have hB := hP.2.2.2.1
  refine locRichComapAEArc_of_hitScale (exists_pathExtract hP.1) ?_ ?_ (h κ P' Y B' hP ℓ₁ hℓ)
  · filter_upwards [hB.cont] with ω hω
    show Continuous (drive κ B' ω)
    exact continuous_const.mul (hω.comp continuous_real_toNNReal)
  · filter_upwards [hB.toIsPreBrownianReal.eval_zero_ae_eq_zero] with ω hω
    show drive κ B' ω 0 = 0
    simp [drive, hω]

end QuantumZipper.LocLen.R5c
