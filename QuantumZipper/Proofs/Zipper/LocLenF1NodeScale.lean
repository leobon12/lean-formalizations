import QuantumZipper.Proofs.Zipper.LocLenStmtsF1Node
import QuantumZipper.Proofs.Zipper.LocLenPStarGood
import QuantumZipper.Proofs.Zipper.LocLenCanonRegGeo
import QuantumZipper.Proofs.Zipper.LocLenRules
import QuantumZipper.Proofs.Zipper.F1LenScale
import QuantumZipper.Proofs.Zipper.F1CanonLaw
import QuantumZipper.Proofs.Zipper.WedgeRC3All2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# D75, node B4(c): `LenScaleArcStmt` (scaling of `F` with open-arc lengths)

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, §5.4, proof of Theorem 1.3
(p. 71, "by scaling": `F(ns)/n` has the law of `F(s)`). Open-arc copy of
`F1.lenScaleStmt_of` (F1LenScale.lean), with `unzipLengths ↦ unzipLengthsArc`,
`lenF/leftTime ↦ lenFArc/leftTimeArc`:

* `lenFArc_of_scaled`: copy of `F1.lenF_of_scaled` (first-passage times absorb the time change);
* `unzipLengthsArc_canon_addConst`: copy of `F1.unzipLengths_canon_addConst`. Adding `k`
  multiplies the open-arc lengths by `e^{γk/2}` (rule (5.1), `HasBdryLimitOn.addConst`), and the
  canonical rescaling (B3(d)) is read off the local limit on the two open arcs
  (`arcLen_rescale_of_hasBdryLimitOn`); the arcs avoid `offSet` (`Ioo_left/right_disjoint_offSet`),
  so goodness off `offSet` suffices.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace LocLen

open F1

/-- **Scaling of `F` with open-arc lengths, deterministic** (copy of `F1.lenF_of_scaled`). -/
theorem lenFArc_of_scaled {γ : ℝ} {c c' : FieldSample × (ℝ → ℝ)} {n : ℕ} (hn : 1 ≤ n) {b : ℝ}
    (hb : 0 < b)
    (h1 : ∀ u, 0 ≤ u →
      (unzipLengthsArc γ c' u).1 = (n : ℝ≥0∞)⁻¹ * (unzipLengthsArc γ c (b * u)).1)
    (h2 : ∀ u, 0 ≤ u →
      (unzipLengthsArc γ c' u).2 = (n : ℝ≥0∞)⁻¹ * (unzipLengthsArc γ c (b * u)).2)
    (s : ℝ) : lenFArc γ c' s = lenFArc γ c (n * s) / n := by
  have hn0 : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hnT : (n : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top n
  have hT : leftTimeArc γ c' s = leftTimeArc γ c (n * s) / b := by
    unfold leftTimeArc lenTimeArc
    rw [← B3d.sInf_scale hb]
    congr 1
    ext u
    simp only [mem_ofPred_eq]
    refine and_congr_right fun hu => ?_
    rw [h1 u hu, ← ENNReal.div_eq_inv_mul, ENNReal.le_div_iff_mul_le (Or.inl hn0) (Or.inl hnT),
      ENNReal.ofReal_mul (Nat.cast_nonneg n), ENNReal.ofReal_natCast, mul_comm]
  have hT0 : 0 ≤ leftTimeArc γ c (n * s) := Real.sInf_nonneg fun u hu => hu.1
  rw [lenFArc, hT, h2 _ (div_nonneg hT0 hb.le), mul_div_cancel₀ _ hb.ne', ENNReal.toReal_mul,
    ENNReal.toReal_inv, ENNReal.toReal_natCast, lenFArc, inv_mul_eq_div]

/-- **Both open-arc lengths of `canonConfig γ (x + k, W)`** (copy of
`F1.unzipLengths_canon_addConst`, with goodness only off `offSet`): with
`a = scaleParam γ (x + k) > 0`, `L'(s) = e^{γk/2} L(a² s)` on both open arcs. -/
theorem unzipLengthsArc_canon_addConst {γ k : ℝ} {x : FieldSample} {W : ℝ → ℝ} (hγ : 0 < γ)
    (ha : 0 < scaleParam γ (addConst x k)) (hW : Continuous W) (hW0 : W 0 = 0)
    (hWmax : ∀ s, W (max s 0) = W s) {s : ℝ} (hs : 0 ≤ s)
    (hL : ∃ l, Tendsto (fun r : ℝ => (fwdMap W (scaleParam γ (addConst x k) ^ 2 * s) r).re)
      (𝓝[<] (0 : ℝ)) (𝓝 l))
    (hR : ∃ l, Tendsto (fun r : ℝ => (fwdMap W (scaleParam γ (addConst x k) ^ 2 * s) r).re)
      (𝓝[>] (0 : ℝ)) (𝓝 l))
    (hgood : IsLQGGoodOff γ (unzippedField γ (x, W) (scaleParam γ (addConst x k) ^ 2 * s))
      (offSet W (scaleParam γ (addConst x k) ^ 2 * s)))
    (hfield : RegEq (unzippedField γ (canonConfig γ (addConst x k, W)) s)
      (rescale (addConst (unzippedField γ (x, W) (scaleParam γ (addConst x k) ^ 2 * s)) k)
        (Qc γ) (scaleParam γ (addConst x k)))) :
    (unzipLengthsArc γ (canonConfig γ (addConst x k, W)) s).1 =
        ENNReal.ofReal (Real.exp (γ * k / 2)) *
          (unzipLengthsArc γ (x, W) (scaleParam γ (addConst x k) ^ 2 * s)).1 ∧
      (unzipLengthsArc γ (canonConfig γ (addConst x k, W)) s).2 =
        ENNReal.ofReal (Real.exp (γ * k / 2)) *
          (unzipLengthsArc γ (x, W) (scaleParam γ (addConst x k) ^ 2 * s)).2 := by
  set a := scaleParam γ (addConst x k) with ha_def
  set t := a ^ 2 * s with ht_def
  have ht : 0 ≤ t := mul_nonneg (sq_nonneg _) hs
  obtain ⟨l, hl⟩ := hL
  obtain ⟨m, hm'⟩ := hR
  obtain ⟨hreg, ⟨ν, hν⟩, -⟩ := hgood
  have hm0 := sideImages_fst_nonpos_of_cont hW hW0 ht
  have hp0 := sideImages_snd_nonneg_of_cont hW hW0 ht
  have hsubL : Ioo (sideImages W t).1 0 ⊆ (offSet W t)ᶜ := fun u hu =>
    disjoint_left.1 (Ioo_left_disjoint_offSet W t hp0) hu
  have hsubR : Ioo 0 (sideImages W t).2 ⊆ (offSet W t)ᶜ := fun u hu =>
    disjoint_left.1 (Ioo_right_disjoint_offSet W t hm0) hu
  have e1 : (sideImages W t).1 = l := hl.limUnder_eq
  have e2 : (sideImages W t).2 = m := hm'.limUnder_eq
  rw [e1] at hsubL
  rw [e2] at hsubR
  have hνk := hν.addConst hreg k
  have hregk := hreg.addConst' k
  have havg := B3d.avgReg_eq_of_regEq hfield
  have hsub1 : Ioo (a * (l / a)) (a * 0) ⊆ (offSet W t)ᶜ := by
    rw [mul_div_cancel₀ _ ha.ne', mul_zero]; exact hsubL
  have hsub2 : Ioo (a * 0) (a * (m / a)) ⊆ (offSet W t)ᶜ := by
    rw [mul_div_cancel₀ _ ha.ne', mul_zero]; exact hsubR
  unfold unzipLengthsArc
  simp only
  rw [B3d.canonConfig_snd_of_max hWmax, B3d.sideImages_fst_scale W ha hs hl,
    B3d.sideImages_snd_scale W ha hs hm', e1, e2]
  rw [arcLen_congr havg, arcLen_congr havg,
    arcLen_rescale_of_hasBdryLimitOn hregk hγ ha hνk hsub1,
    arcLen_rescale_of_hasBdryLimitOn hregk hγ ha hνk hsub2,
    arcLen_eq_of_hasBdryLimitOn hreg hν hsubL,
    arcLen_eq_of_hasBdryLimitOn hreg hν hsubR,
    mul_div_cancel₀ _ ha.ne', mul_div_cancel₀ _ ha.ne', mul_zero,
    Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul]
  exact ⟨rfl, rfl⟩

/-- **`LenScaleArcStmt` from B4(c) (`PStarCanonLawStmt`) and the off-`offSet` field inputs**
(open-arc copy of `F1.lenScaleStmt_of`; Sheffield p. 71), with
`c' = canonConfig γ (Y − (2/γ) log n, √κ B')`. -/
theorem lenScaleArc_of (hlaw : F1.PStarCanonLawStmt) (hin : PStarZipLenInputsLocStmt) :
    LenScaleArcStmt := by
  intro κ Ω' _ P' _ Y B' hP n hn
  have hγ : 0 < Real.sqrt κ := Real.sqrt_pos.2 hP.1
  set k : ℝ := -(2 / Real.sqrt κ) * Real.log n with hk
  obtain ⟨hl, hm⟩ := hlaw κ P' Y B' hP k
  refine ⟨scCfg κ k Y B', hl, hm, ?_, ?_⟩
  · filter_upwards [hP.2.2.2.1.cont] with ω hc
    have hW := continuous_drive_of κ hc
    refine ⟨?_, fun s => ?_⟩
    · simp only [scCfg, canonConfig]
      exact (hW.comp (continuous_const.mul (continuous_id.max continuous_const))).div_const _
    · simp only [scCfg, canonConfig, Real.coe_toNNReal', max_eq_left (le_max_right s 0)]
  · filter_upwards [hin κ P' Y B' hP k, hP.2.2.2.1.cont,
      hP.2.2.2.1.toIsPreBrownianReal.eval_zero_ae_eq_zero] with ω hω hc h0 s _
    obtain ⟨ha, hL, hR, hg, hf⟩ := hω
    have hW := continuous_drive_of κ hc
    have hW0 : drive κ B' ω 0 = 0 := by simp [drive, h0]
    have hsc := ofReal_exp_scale hγ hn
    rw [← hk] at hsc
    have key := fun u (hu : 0 ≤ u) => unzipLengthsArc_canon_addConst hγ ha hW hW0
      (drive_max κ B' ω) hu (hL _ (mul_nonneg (sq_nonneg _) hu))
      (hR _ (mul_nonneg (sq_nonneg _) hu)) (hg _ (mul_nonneg (sq_nonneg _) hu)) (hf u hu)
    refine lenFArc_of_scaled hn (b := scaleParam (Real.sqrt κ) (addConst (Y ω) k) ^ 2)
      (pow_pos ha 2) (fun u hu => ?_) (fun u hu => ?_) s
    · have := (key u hu).1
      rw [hsc] at this
      exact this
    · have := (key u hu).2
      rw [hsc] at this
      exact this

/-- **`LenScaleArcStmt` from the off-tip boundary merging** (`WedgeUnzip.YMergeOffTipStmt`), with
B4(c) proved (`F1.pStarCanonLawStmt_of F1.wedgeAddConstLawStmt_holds`). -/
theorem lenScaleArc_of_yMergeOffTip (hYO : WedgeUnzip.YMergeOffTipStmt) : LenScaleArcStmt :=
  lenScaleArc_of (F1.pStarCanonLawStmt_of F1.wedgeAddConstLawStmt_holds)
    (pStarZipLenInputsLoc_of_yMergeOffTip hYO)

end LocLen
end QuantumZipper
