import QuantumZipper.Proofs.Thm18.ZqTA3

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ZQ-TYP (A4): Palm transfer for the free field on windows beyond the unit disc

The free field `h = 𝔥₀ + X − X(S)` has the coordinates of `normAt S (ofFun (Lf (−2/γ)) + X)`
(`𝔥₀ = (2/γ) log|·| = Lf (−2/γ)`, `coords_normAt_free`). Hence the rooted-measure (Palm) formula
`palm_formula_norm_local` applies on every window `[a, b] ⊆ [−N, N]` avoiding `0` (as in
`ae_typ_of_palm_V`), not only inside `(−1, 1)` as `ae_hν_of_palm_null`: `ae_typ_of_palm_free`.
With it, the far-right node `G3ZqTFreeFarStmt` follows from the fixed-Palm-point certificate on
`(1, ∞)` (`G3ZqTFreeFarPalmStmt`, the analog beyond the unit disc of the proved
`G3ZqLPalmCertStmt`): `g3ZqTFreeFarStmt_of`.

Duplantier–Sheffield, arXiv:0808.1560, §3.3 (rooted measure); Sheffield, arXiv:1012.4797, proof
of Prop. 5.5, p. 65. Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace ZqT

open R18 PalmNorm G3Zq G3Z2b2 G3ZqL Factorization

variable {Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ}

theorem integral_log_norm_g3zS : ∫ u, Real.log ‖u‖ ∂g3zS = 0 := by
  refine (integral_congr_ae ?_).trans (integral_zero ℂ ℝ)
  filter_upwards [ae_norm_refS] with u hu
  simp [hu]

/-- The free field in `normAt` form. -/
theorem coords_normAt_free {γ : ℝ} (hγ : 0 < γ) (ω : gffBase.Ω) :
    coords (normAt g3zS (ofFun (LogSingGood.Lf (-2 / γ)) + gffBase.X ω)) =
      coords (normField γ gffBase.X ω) := by
  funext j
  have hS : ofFun (LogSingGood.Lf (-2 / γ)) g3zS = 0 := by
    simp only [ofFun, LogSingGood.Lf, integral_const_mul, integral_neg, integral_log_norm_g3zS,
      neg_zero, mul_zero]
  simp only [coords, normAt, addConst, normField, Pi.add_apply, hS, measure_univ,
    ENNReal.toReal_one, mul_one]
  simp only [ofFun, h0rev, LogSingGood.Lf, integral_const_mul, integral_neg, Real.sqrt_sq hγ.le]
  ring

theorem bdryApprox_eq_of_coords {γ : ℝ} {y y' : FieldSample} (h : coords y = coords y') :
    bdryApprox γ y = bdryApprox γ y' := by
  funext k
  unfold bdryApprox
  rw [← avgReg_reconstruct_coords y, h, avgReg_reconstruct_coords]

theorem qBM_eq_of_coords {γ : ℝ} {y y' : FieldSample} (h : coords y = coords y') :
    qBoundaryMeasure γ y = qBoundaryMeasure γ y' := by
  rw [← WedgeBdry.qBoundaryMeasure_reconstruct γ y, h, WedgeBdry.qBoundaryMeasure_reconstruct]

/-- **Palm transfer of null events for the free field on a window avoiding `0`.** -/
theorem ae_typ_of_palm_free {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {E : Set ((ℕ → ℝ) × ℝ)} (hE : MeasurableSet E) {a b : ℝ} {N : ℕ}
    (hab : Icc a b ⊆ Icc (-(N : ℝ)) N) (h0 : (0 : ℝ) ∉ Icc a b)
    (hP : ∀ᵐ x ∂(volume.restrict (Ioo a b)), ∀ᵐ ω ∂gffBase.P,
      (coords (normAt g3zS (ofFun (shiftFun γ (LogSingGood.Lf (-2 / γ)) g3zS x) +
        gffBase.X ω)), x) ∉ E) :
    ∀ᵐ ω ∂gffBase.P, ∀ᵐ x ∂((qBoundaryMeasure γ (normField γ gffBase.X ω)).restrict (Ioo a b)),
      (coords (normField γ gffBase.X ω), x) ∉ E := by
  set α : ℝ := -2 / γ with hα
  obtain ⟨m, hm, hmab⟩ := g3z_exists_margin h0
  set h' : ℂ → ℝ := fun v => α * -Real.log (max ‖v‖ m) with hh'
  have hh'c : Continuous h' := by
    refine continuous_const.mul (Continuous.neg ?_)
    exact Real.continuousOn_log.comp_continuous (continuous_norm.max continuous_const)
      fun v => by
        simp only [mem_compl_iff, mem_singleton_iff]
        exact ne_of_gt (lt_of_lt_of_le hm (le_max_right _ _))
  set W : Set ℂ := {v | m < ‖v‖} with hWdef
  have hW : IsOpen W := isOpen_lt continuous_const continuous_norm
  have habW : ∀ t ∈ Icc a b, (t : ℂ) ∈ W := fun t ht => by
    show m < ‖(t : ℂ)‖
    rw [Complex.norm_real, Real.norm_eq_abs]; exact hmab t ht
  have hEq : EqOn (LogSingGood.Lf α) h' W := fun v hv => by
    simp only [hh', LogSingGood.Lf, max_eq_left (le_of_lt (show m < ‖v‖ from hv))]
  have hϖ : IsAdmissibleH g3zS := isAdmissibleH_foldedCircle (by simp [Hbar]) one_pos
  have hϖ1 : g3zS univ = 1 := measure_univ
  set μc : ℕ → Measure ℂ := fun j => foldedCircle (dyadicIndex j).1 (radius (dyadicIndex j).2)
    with hμc
  have hμ : ∀ j, IsAdmissibleH (μc j) := fun j =>
    D3Plus.isAdmissibleH_foldedCircle' _ (radius_pos _)
  have hint : ∀ (d : ℂ) (ρ : ℝ), Integrable (LogSingGood.Lf α) (foldedCircle d ρ) := fun d ρ =>
    (CoordReg.integrable_log_norm_foldedCircle d ρ).neg.const_mul α
  have hgV := ae_isLQGGood_normField gffBase.gff hγ hγ2
  have hN := coords_normAt_free hγ
  have hex : ∀ᵐ ω ∂gffBase.P, ∃ ν, IsVagueLimitR
      (bdryApprox γ (normAt g3zS (ofFun (LogSingGood.Lf α) + gffBase.X ω))) ν := by
    filter_upwards [hgV] with ω hg
    rw [bdryApprox_eq_of_coords (hN ω)]
    exact ⟨_, isVagueLimitR_qBoundaryMeasure_of_isLQGGood hg⟩
  -- the weight
  set w : ℝ → ℝ := fun x => max 0 (min (x - a) (b - x)) with hwdef
  have hw : Continuous w := continuous_const.max
    ((continuous_id.sub continuous_const).min (continuous_const.sub continuous_id))
  have hw0 : ∀ x, 0 ≤ w x := fun x => le_max_left _ _
  have hwout : ∀ x ∉ Ioo a b, w x = 0 := by
    intro x hx
    simp only [mem_Ioo, not_and_or, not_lt] at hx
    refine max_eq_left ?_
    rcases hx with hx | hx
    · exact (min_le_left _ _).trans (by linarith)
    · exact (min_le_right _ _).trans (by linarith)
  have hwab : ∀ x ∉ Icc a b, w x = 0 := fun x hx => hwout x fun h => hx (Ioo_subset_Icc_self h)
  have hwpos : ∀ x ∈ Ioo a b, 0 < w x := fun x hx =>
    lt_max_of_lt_right (lt_min (by linarith [hx.1]) (by linarith [hx.2]))
  have hwc : HasCompactSupport w := HasCompactSupport.intro isCompact_Icc hwab
  set φ : (ℕ → ℝ) → ℝ → ℝ≥0∞ := fun c x => E.indicator 1 (c, x) with hφdef
  have hφ : Measurable (Function.uncurry φ) := measurable_one.indicator hE
  have H := palm_formula_norm_local (P := gffBase.P) (μ := μc) gffBase.gff hγ hγ2 hab hh'c hW
    habW hEq hϖ hϖ1 hμ (hint 0 1) (fun j => hint _ _) hex hw hwc hw0 hwab hφ
  have hR : ∫⁻ x, ENNReal.ofReal (w x * rhoNorm γ (LogSingGood.Lf α) g3zS x) *
      ∫⁻ ω, φ (fun j => normAt g3zS (ofFun (shiftFun γ (LogSingGood.Lf α) g3zS x) +
        gffBase.X ω) (μc j)) x ∂gffBase.P = 0 := by
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    rw [ae_restrict_iff' measurableSet_Ioo] at hP
    filter_upwards [hP] with x hx
    by_cases hxI : x ∈ Ioo a b
    · have h0' : ∫⁻ ω, φ (fun j => normAt g3zS (ofFun (shiftFun γ (LogSingGood.Lf α) g3zS x) +
          gffBase.X ω) (μc j)) x ∂gffBase.P = 0 := by
        refine (lintegral_congr_ae ?_).trans lintegral_zero
        filter_upwards [hx hxI] with ω hω
        exact indicator_of_notMem hω _
      rw [h0', mul_zero]
    · rw [hwout x hxI, zero_mul, ENNReal.ofReal_zero, zero_mul]
  rw [hR] at H
  have hcm : Measurable fun ω => coords (normField γ gffBase.X ω) :=
    measurable_coords.comp (measurable_normField_g3 γ)
  have hF'm : Measurable fun ω => ∫⁻ x, ENNReal.ofReal (w x) *
      φ (coords (normField γ gffBase.X ω)) x ∂(bdryMc γ (coords (normField γ gffBase.X ω))) :=
    measurable_lintegral_family (H := fun q : gffBase.Ω × ℝ => ENNReal.ofReal (w q.2) *
        φ (coords (normField γ gffBase.X q.1)) q.2)
      ((measurable_bdryMc γ).comp hcm) (fun ω N => bdryM_Icc_ne_top γ _ _ _)
      ((ENNReal.measurable_ofReal.comp (hw.measurable.comp measurable_snd)).mul
        (hφ.comp ((hcm.comp measurable_fst).prodMk measurable_snd)))
  have hFF : (fun ω => ∫⁻ x, ENNReal.ofReal (w x) *
      φ (fun j => normAt g3zS (ofFun (LogSingGood.Lf α) + gffBase.X ω) (μc j)) x
        ∂(qBoundaryMeasure γ (normAt g3zS (ofFun (LogSingGood.Lf α) + gffBase.X ω)))) =ᵐ[gffBase.P]
      fun ω => ∫⁻ x, ENNReal.ofReal (w x) * φ (coords (normField γ gffBase.X ω)) x
        ∂(bdryMc γ (coords (normField γ gffBase.X ω))) := by
    filter_upwards [hgV] with ω hg
    rw [qBM_eq_of_coords (hN ω), bdryMc_coords_of_good hg]
    have e : (fun j => normAt g3zS (ofFun (LogSingGood.Lf α) + gffBase.X ω) (μc j)) =
        coords (normField γ gffBase.X ω) := hN ω
    rw [e]
  rw [lintegral_congr_ae hFF] at H
  filter_upwards [(lintegral_eq_zero_iff hF'm).1 H, hgV] with ω hω hg
  have hZ : ∀ᵐ x ∂(bdryMc γ (coords (normField γ gffBase.X ω))),
      ENNReal.ofReal (w x) * φ (coords (normField γ gffBase.X ω)) x = 0 :=
    (lintegral_eq_zero_iff ((ENNReal.measurable_ofReal.comp hw.measurable).mul
      (hφ.comp (measurable_const.prodMk measurable_id)))).1 hω
  rw [bdryMc_coords_of_good hg] at hZ
  rw [ae_restrict_iff' measurableSet_Ioo]
  filter_upwards [hZ] with x hx hxI hmem
  have hw' : ENNReal.ofReal (w x) ≠ 0 := (ENNReal.ofReal_pos.2 (hwpos x hxI)).ne'
  have h1 : φ (coords (normField γ gffBase.X ω)) x = 1 := indicator_of_mem hmem _
  rw [h1, mul_one] at hx
  exact hw' hx

/-- The two forms of the free Palm field agree on folded circles. -/
theorem coords_normAt_xPalm {γ : ℝ} (hγ : 0 < γ) (x : ℝ) (ω : gffBase.Ω) :
    coords (normAt g3zS (ofFun (shiftFun γ (LogSingGood.Lf (-2 / γ)) g3zS x) + gffBase.X ω)) =
      coords (normField γ (xPalm γ x) ω) := by
  have hLh : LogSingGood.Lf (-2 / γ) = h0rev (γ ^ 2) := funext fun u => by
    simp only [LogSingGood.Lf, h0rev, Real.sqrt_sq hγ.le]; ring
  have hsf : shiftFun γ (LogSingGood.Lf (-2 / γ)) g3zS x =
      fun u => h0rev (γ ^ 2) u + g2PalmPsi γ x u := funext fun u => by
    simp only [shiftFun, g2PalmPsi, hLh]
  have hS : ∫ u, (h0rev (γ ^ 2) u + g2PalmPsi γ x u) ∂g3zS = ∫ u, g2PalmPsi γ x u ∂refS :=
    integral_congr_ae (ae_norm_refS.mono fun u hu => by simp [h0rev, hu])
  funext j
  set c := (dyadicIndex j).1
  set s := radius (dyadicIndex j).2
  have hs : 0 < s := radius_pos _
  have hI1 : Integrable (h0rev (γ ^ 2)) (foldedCircle c s) :=
    (CoordReg.integrable_log_norm_foldedCircle c s).const_mul _
  have hI2 : Integrable (g2PalmPsi γ x) (foldedCircle c s) := by
    have hN := D3Plus.integrable_neumannH_right_adm
      (G3Cv.isAdmissibleH_foldedCircle_g3cv2 c hs) (x : ℂ)
    have hK := E5.integrable_foldedCircle_of_continuousOn (r := ‖c‖ + s + 1)
      G3ZqF.continuous_kPot_refS.continuousOn c s hs (by linarith)
    show Integrable (fun u => γ / 2 * (neumannH (x : ℂ) u - PalmNorm.kPot refS u)) _
    exact (hN.sub hK).const_mul _
  simp only [coords, normAt, addConst, normField, xPalm, Pi.add_apply, hsf, measure_univ,
    ENNReal.toReal_one, mul_one]
  simp only [ofFun]
  rw [hS, integral_add hI1 hI2]
  ring

/-- **Node: the certificate of the pulled-back free Palm field at Lebesgue-a.e. fixed point of
`(1, ∞)`** (`G3ZqLPalmCertStmt` beyond the unit disc; the proved `ZqR.ae_locCertC_palm` needs
`|x| < 1`). -/
def G3ZqTFreeFarPalmStmt : Prop :=
  ∀ (γ : ℝ), 0 < γ → γ < 2 → ∀ Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ, G1PsiSel γ Ψ →
  ∀ a : ℝ≥0 → ℝ, G3ZqGoodPath γ a →
    ∀ᵐ x ∂(volume.restrict (Ioi (1 : ℝ))), ∀ᵐ ω ∂gffBase.P,
      LocCertC γ (g3coordsM γ 0 Ψ false (normField γ (xPalm γ x) ω, a, 1, x))

theorem iUnion_Ioo_one : (⋃ n : ℕ, Ioo (1 : ℝ) ((n : ℝ) + 2)) = Ioi 1 := by
  ext x
  simp only [mem_iUnion, mem_Ioo, mem_Ioi]
  constructor
  · rintro ⟨n, h1, -⟩; exact h1
  · intro hx
    obtain ⟨n, hn⟩ := exists_nat_gt x
    exact ⟨n, hx, by linarith⟩

/-- **`G3ZqTFreeFarStmt` from the fixed Palm points beyond the unit disc.** -/
theorem g3ZqTFreeFarStmt_of (hF : G3ZqTFreeFarPalmStmt) : G3ZqTFreeFarStmt := by
  intro γ hγ hγ2 Ψ hsel a ha
  have hn : ∀ n : ℕ, ∀ᵐ ω ∂gffBase.P, ∀ᵐ x ∂((qBoundaryMeasure γ
      (normField γ gffBase.X ω)).restrict (Ioo (1 : ℝ) ((n : ℝ) + 2))),
      (coords (normField γ gffBase.X ω), x) ∉ badSet γ Ψ false a := by
    intro n
    have hsub : Icc (1 : ℝ) ((n : ℝ) + 2) ⊆ Icc (-((n + 2 : ℕ) : ℝ)) ((n + 2 : ℕ) : ℝ) :=
      fun t ht => by push_cast; exact ⟨by linarith [ht.1], ht.2⟩
    have h0 : (0 : ℝ) ∉ Icc (1 : ℝ) ((n : ℝ) + 2) := fun h => by linarith [h.1]
    refine ae_typ_of_palm_free hγ hγ2 (measurableSet_badSet hsel false a) hsub h0 ?_
    filter_upwards [ae_restrict_of_ae_restrict_of_subset
      (show Ioo (1 : ℝ) ((n : ℝ) + 2) ⊆ Ioi 1 from fun t ht => ht.1)
      (hF γ hγ hγ2 Ψ hsel a ha)] with x hx
    filter_upwards [hx] with ω hω
    intro hb
    exact hb.2 (by rw [coords_normAt_xPalm hγ, g3coordsM_reconstruct_coords]; exact hω)
  filter_upwards [ae_all_iff.2 hn, G3Fid.ae_normField_good gffBase.gff hγ hγ2] with ω hω hgood
  have hall : ∀ᵐ x ∂((qBoundaryMeasure γ (normField γ gffBase.X ω)).restrict
      (⋃ n : ℕ, Ioo (1 : ℝ) ((n : ℝ) + 2))),
      (coords (normField γ gffBase.X ω), x) ∉ badSet γ Ψ false a :=
    (ae_restrict_iUnion_iff _ _).2 hω
  rw [iUnion_Ioo_one, ae_restrict_iff' measurableSet_Ioi] at hall
  have hat : qBoundaryMeasure γ (normField γ gffBase.X ω) {1} = 0 := hgood.2.2 1
  filter_upwards [hall, measure_eq_zero_iff_ae_notMem.1 hat] with x hx hx1 h1x
  have hx1' : 1 < x := lt_of_le_of_ne h1x fun h => hx1 (by rw [← h]; rfl)
  by_contra hn'
  have hxs : x ∈ g1SideHalf false := by
    simp only [g1SideHalf, Bool.false_eq_true, if_false, mem_Ioi]; linarith
  exact hx hx1' ⟨hxs, by rw [g3coordsM_reconstruct_coords]; exact hn'⟩

end ZqT
end Thm18Asm
end QuantumZipper
