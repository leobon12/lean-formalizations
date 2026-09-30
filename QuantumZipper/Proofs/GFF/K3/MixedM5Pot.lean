import QuantumZipper.Proofs.GFF.K3.MixedM5Weak

/-!
# Circle averages of admissible measures (GFF-K3 node M5, preparation)

For `μ_t := μ.bind (foldedCircle · t)`:

* `lintegral_negLog_circleUnif_le_max`: `⨍_{∂B(z,r)} log⁻|x − y| ≤ log⁻ max(r, |z − y|) + r`
  (mean value property of `log` plus `log⁺(m + r) ≤ log⁺ m + r`);
* `lintegral_negLog_bind_le`: the logarithmic potential of `μ_t` is bounded by
  `2C + 2t μ(ℂ)`, uniformly in `t`, if that of `μ` is bounded by `C`;
* `isAdmissibleH_bind`, `bind_cthickening_compl`: admissibility and support of `μ_t`;
* `norm_rieszVec_le_of_sq_le`: a pairing bound gives a bound on the Riesz vector.

Own elementary arguments (cost rule); the mean value property is
`integral_log_norm_sub_circleUnif`.
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Real Topology ComplexConjugate ENNReal NNReal RealInnerProductSpace

namespace QuantumZipper.K3

theorem log_add_le_posPart {m r : ℝ} (hr : 0 < r) (hm : r ≤ m) :
    -Real.log m + max 0 (Real.log (m + r)) ≤ max 0 (-Real.log m) + r := by
  have hm0 : 0 < m := hr.trans_le hm
  rcases le_total (Real.log (m + r)) 0 with h | h
  · rw [max_eq_left h]; linarith [le_max_right 0 (-Real.log m)]
  · rw [max_eq_right h]
    rcases le_total 1 m with h1 | h1
    · have hlog : Real.log (m + r) - Real.log m ≤ r := by
        rw [← Real.log_div (by linarith) hm0.ne']
        refine (Real.log_le_sub_one_of_pos (by positivity)).trans ?_
        rw [div_sub_one hm0.ne', add_sub_cancel_left, div_le_iff₀ hm0]
        nlinarith
      linarith [le_max_left 0 (-Real.log m)]
    · have hlog := Real.log_le_sub_one_of_pos (show 0 < m + r by linarith)
      have hneg : 0 ≤ -Real.log m := by
        have := Real.log_nonpos hm0.le h1; linarith
      rw [max_eq_right hneg]
      linarith

/-- Circle average of `log⁻ |· − y|`. -/
theorem lintegral_negLog_circleUnif_le_max (z y : ℂ) {r : ℝ} (hr : 0 < r) :
    ∫⁻ x, ENNReal.ofReal (-Real.log ‖x - y‖) ∂(circleUnif z r) ≤
      ENNReal.ofReal (-Real.log (max r ‖z - y‖)) + ENNReal.ofReal r := by
  set m := max r ‖z - y‖ with hm
  have hrm : r ≤ m := le_max_left _ _
  have hint := CircleMV.integrable_log_norm_sub_circleUnif z y r
  have hpos : Integrable (fun x => max 0 (Real.log ‖x - y‖)) (circleUnif z r) :=
    (integrable_const 0).sup hint
  set g : ℂ → ℝ := fun x => -Real.log ‖x - y‖ + max 0 (Real.log ‖x - y‖) with hg
  have hneg : Integrable (fun x => -Real.log ‖x - y‖) (circleUnif z r) := hint.neg
  have hgint : Integrable g (circleUnif z r) := hneg.add hpos
  have hsplit : ∫ x, g x ∂(circleUnif z r) = -(∫ x, Real.log ‖x - y‖ ∂(circleUnif z r)) +
      ∫ x, max 0 (Real.log ‖x - y‖) ∂(circleUnif z r) := by
    rw [← integral_neg]; exact integral_add hneg hpos
  have hg0 : ∀ x, 0 ≤ g x := fun x => by
    simp only [hg]; linarith [le_max_right 0 (Real.log ‖x - y‖)]
  have hpt : ∀ x, ENNReal.ofReal (-Real.log ‖x - y‖) ≤ ENNReal.ofReal (g x) := fun x =>
    ENNReal.ofReal_le_ofReal (by simp only [hg]; linarith [le_max_left 0 (Real.log ‖x - y‖)])
  have hbound : ∀ᵐ x ∂(circleUnif z r), max 0 (Real.log ‖x - y‖) ≤ max 0 (Real.log (m + r)) := by
    filter_upwards [CircleMV.ae_circleUnif z r] with x hx
    have hxy : ‖x - y‖ ≤ m + r := by
      calc ‖x - y‖ ≤ ‖x - z‖ + ‖z - y‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ m + r := by rw [hx, abs_of_pos hr]; linarith [le_max_right r ‖z - y‖, hm]
    rcases eq_or_lt_of_le (norm_nonneg (x - y)) with h0 | h0
    · rw [← h0, Real.log_zero, max_self]; exact le_max_left _ _
    · exact max_le_max le_rfl (Real.log_le_log h0 hxy)
  have hIg : ∫ x, g x ∂(circleUnif z r) ≤ max 0 (-Real.log m) + r := by
    rw [hsplit, integral_log_norm_sub_circleUnif z y hr]
    have h2 : ∫ x, max 0 (Real.log ‖x - y‖) ∂(circleUnif z r) ≤ max 0 (Real.log (m + r)) := by
      calc ∫ x, max 0 (Real.log ‖x - y‖) ∂(circleUnif z r)
          ≤ ∫ _x, max 0 (Real.log (m + r)) ∂(circleUnif z r) :=
            integral_mono_ae hpos (integrable_const _) hbound
        _ = max 0 (Real.log (m + r)) := by simp
    linarith [log_add_le_posPart hr hrm]
  calc ∫⁻ x, ENNReal.ofReal (-Real.log ‖x - y‖) ∂(circleUnif z r)
      ≤ ∫⁻ x, ENNReal.ofReal (g x) ∂(circleUnif z r) := lintegral_mono hpt
    _ = ENNReal.ofReal (∫ x, g x ∂(circleUnif z r)) :=
        (ofReal_integral_eq_lintegral_ofReal hgint (ae_of_all _ hg0)).symm
    _ ≤ ENNReal.ofReal (max 0 (-Real.log m) + r) := ENNReal.ofReal_le_ofReal hIg
    _ = ENNReal.ofReal (-Real.log m) + ENNReal.ofReal r := by
        rw [ENNReal.ofReal_add (le_max_left _ _) hr.le, CircleFubini.ofReal_max_zero]

/-- Folded version. -/
theorem lintegral_negLog_foldedCircle_le_max (z y : ℂ) {r : ℝ} (hr : 0 < r) :
    ∫⁻ x, ENNReal.ofReal (-Real.log ‖x - y‖) ∂(foldedCircle z r) ≤
      ENNReal.ofReal (-Real.log (max r ‖z - y‖)) + ENNReal.ofReal (-Real.log (max r ‖z - conj y‖)) +
        2 * ENNReal.ofReal r := by
  have hm : Measurable fun x : ℂ => ENNReal.ofReal (-Real.log ‖x - y‖) := by fun_prop
  rw [foldedCircle, lintegral_map hm measurable_foldH]
  calc ∫⁻ w, ENNReal.ofReal (-Real.log ‖foldH w - y‖) ∂(circleUnif z r)
      ≤ ∫⁻ w, (ENNReal.ofReal (-Real.log ‖w - y‖) +
          ENNReal.ofReal (-Real.log ‖w - conj y‖)) ∂(circleUnif z r) := by
        refine lintegral_mono fun w => ?_
        unfold foldH
        split_ifs
        · exact le_self_add
        · rw [CircleMV.norm_foldH_sub_conj]; exact le_add_self
    _ = _ := lintegral_add_left hm _
    _ ≤ _ := add_le_add (lintegral_negLog_circleUnif_le_max z y hr)
        (lintegral_negLog_circleUnif_le_max z (conj y) hr)
    _ = _ := by rw [two_mul]; ring

theorem ofReal_negLog_max_le {r a : ℝ} (ha : 0 < a) :
    ENNReal.ofReal (-Real.log (max r a)) ≤ ENNReal.ofReal (-Real.log a) :=
  ENNReal.ofReal_le_ofReal (neg_le_neg (Real.log_le_log ha (le_max_right _ _)))

/-- **Uniform potential bound for `μ_t`.** -/
theorem lintegral_negLog_bind_le {μ : Measure ℂ} (hμ : IsAdmissibleH μ) {C : ℝ≥0∞}
    (hC : ∀ y, ∫⁻ x, ENNReal.ofReal (-Real.log ‖x - y‖) ∂μ ≤ C) {t : ℝ} (ht : 0 < t) (y : ℂ) :
    ∫⁻ x, ENNReal.ofReal (-Real.log ‖x - y‖) ∂(μ.bind fun w => foldedCircle w t) ≤
      2 * C + 2 * ENNReal.ofReal t * μ univ := by
  have hμf := hμ.1
  rw [Measure.lintegral_bind (CircleFubini.measurable_foldedCircle' t).aemeasurable
    (CircleFubini.measurable_logPot y).aemeasurable]
  have hy : ∀ᵐ z ∂μ, z ≠ y := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp (noAtoms_of_isAdmissibleH hμ y)] with z hz
    exact fun h => hz (by rw [h]; rfl)
  have hy' : ∀ᵐ z ∂μ, z ≠ conj y := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp (noAtoms_of_isAdmissibleH hμ (conj y))]
      with z hz
    exact fun h => hz (by rw [h]; rfl)
  calc ∫⁻ z, ∫⁻ x, ENNReal.ofReal (-Real.log ‖x - y‖) ∂foldedCircle z t ∂μ
      ≤ ∫⁻ z, (ENNReal.ofReal (-Real.log ‖z - y‖) + ENNReal.ofReal (-Real.log ‖z - conj y‖) +
          2 * ENNReal.ofReal t) ∂μ := by
        refine lintegral_mono_ae ?_
        filter_upwards [hy, hy'] with z hz hz'
        refine (lintegral_negLog_foldedCircle_le_max z y ht).trans ?_
        exact add_le_add (add_le_add (ofReal_negLog_max_le (norm_pos_iff.mpr (sub_ne_zero.mpr hz)))
          (ofReal_negLog_max_le (norm_pos_iff.mpr (sub_ne_zero.mpr hz')))) le_rfl
    _ = ∫⁻ z, ENNReal.ofReal (-Real.log ‖z - y‖) ∂μ +
          ∫⁻ z, ENNReal.ofReal (-Real.log ‖z - conj y‖) ∂μ + 2 * ENNReal.ofReal t * μ univ := by
        rw [lintegral_add_right _ measurable_const, lintegral_add_left
          (CircleFubini.measurable_logPot y), lintegral_const]
    _ ≤ C + C + 2 * ENNReal.ofReal t * μ univ := by gcongr <;> exact hC _
    _ = _ := by ring

/-- The support of `μ_t`. -/
theorem bind_cthickening_compl {μ : Measure ℂ} [IsFiniteMeasure μ] {K : Set ℂ}
    (hK : IsCompact K) (hKH : K ⊆ Hbar) (hμK : μ Kᶜ = 0) {t s : ℝ} (ht : 0 ≤ t) (hts : t ≤ s) :
    (μ.bind fun w => foldedCircle w t) (cthickening s K ∩ Hbar)ᶜ = 0 := by
  have hmeas : MeasurableSet (cthickening s K ∩ Hbar) :=
    isClosed_cthickening.measurableSet.inter isClosed_Hbar.measurableSet
  rw [CircleFubini.bind_circle_apply μ hmeas.compl]
  have hae : ∀ᵐ w ∂μ, w ∈ K := mem_ae_iff.mpr hμK
  have : ∀ᵐ w ∂μ, foldedCircle w t (cthickening s K ∩ Hbar)ᶜ = 0 := by
    filter_upwards [hae] with w hw
    refine measure_mono_null (compl_subset_compl.mpr ?_) (foldedCircle_compl_eq_zero (hKH hw) ht)
    exact inter_subset_inter_left _
      ((closedBall_subset_closedBall hts).trans (closedBall_subset_cthickening hw s))
  rw [lintegral_congr_ae this, lintegral_zero]

/-- Admissibility of `μ_t`. -/
theorem isAdmissibleH_bind {μ : Measure ℂ} (hμ : IsAdmissibleH μ) {t : ℝ} (ht : 0 < t) :
    IsAdmissibleH (μ.bind fun w => foldedCircle w t) := by
  obtain ⟨hμf, ⟨K, hK, hKH, hμK⟩, C, hC, hbd⟩ := id hμ
  have := CircleFubini.isFiniteMeasure_bind_circle (r := t) μ
  refine ⟨this, ⟨cthickening t K ∩ Hbar, hK.cthickening.inter_right isClosed_Hbar,
    inter_subset_right, bind_cthickening_compl hK hKH hμK ht.le le_rfl⟩,
    2 * C + 2 * ENNReal.ofReal t * μ univ, ?_, lintegral_negLog_bind_le hμ hbd ht⟩
  have h1 : C ≠ ⊤ := hC.ne
  have h2 : μ univ ≠ ⊤ := measure_ne_top _ _
  exact lt_top_iff_ne_top.mpr (by finiteness)

/-- Local discs around the points of the closed `s`-neighbourhood of `K`. -/
theorem localBall_cthickening {D S K : Set ℂ} (hK : IsCompact K) {R s : ℝ}
    (hKloc : ∀ z ∈ K, LocalBall D S z (2 * R)) (hs : 0 ≤ s) (hsR : s < 2 * R) :
    ∀ w ∈ cthickening s K ∩ Hbar, LocalBall D S w (2 * ((2 * R - s) / 2)) := by
  rintro w ⟨hw, hwH⟩
  rw [hK.cthickening_eq_biUnion_closedBall hs] at hw
  obtain ⟨z, hz, hwz⟩ := mem_iUnion₂.mp hw
  exact (hKloc z hz).mono hwH (by linarith) (by rw [mem_closedBall] at hwz; linarith)

/-- A pairing bound gives a bound on the Riesz vector. -/
theorem norm_rieszVec_le_of_sq_le {D S : Set ℂ} {ν : Measure ℂ}
    (hν : IsAdmissibleDual D (mixedSpace D S) ν) {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ f ∈ mixedSpace D S, (∫ x, f x ∂ν) ^ 2 ≤ M * ∫ w in D, ‖fderiv ℝ f w‖ ^ 2) :
    ‖rieszVec D (mixedSpace D S) ν‖ ≤ Real.sqrt (M * (2 * π)) := by
  obtain ⟨hνf, ⟨K, hK, -, hνK⟩, hfin⟩ := hν
  have := hνf
  have hdn := dualNormSq_eq_norm_rieszVec (isDNSpace_mixedSpace D S) ⟨K, hK, hνK⟩ hfin
  have hle : dualNormSq D (mixedSpace D S) ν ≤ ENNReal.ofReal (M * (2 * π)) := by
    unfold dualNormSq
    refine iSup₂_le fun f hf => ENNReal.ofReal_le_ofReal ?_
    rw [div_le_iff₀ hf.2]
    have hE : dirichletEnergyOn D f = (2 * π)⁻¹ * ∫ z in D, ‖fderiv ℝ f z‖ ^ 2 := rfl
    have hπ : (2 * π) ≠ 0 := by positivity
    calc (∫ x, f x ∂ν) ^ 2 ≤ M * ∫ z in D, ‖fderiv ℝ f z‖ ^ 2 := h f hf.1
      _ = M * (2 * π) * dirichletEnergyOn D f := by
          rw [hE, ← mul_assoc, mul_assoc M (2 * π) (2 * π)⁻¹, mul_inv_cancel₀ hπ, mul_one]
  rw [hdn] at hle
  exact Real.le_sqrt_of_sq_le ((ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hle)

end QuantumZipper.K3
