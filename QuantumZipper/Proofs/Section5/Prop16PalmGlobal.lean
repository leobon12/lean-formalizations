import QuantumZipper.Proofs.Section5.Prop16PalmGlobalMeas
import QuantumZipper.Proofs.Section5.Prop16PalmGlobalTag
import QuantumZipper.Proofs.Section5.Prop16ActReg
import QuantumZipper.Proofs.Section5.Prop16ActRegBdryLoc

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Proposition 1.6, node `Prop16PalmGlobalStmt`: the global window Palm formula

`prop16PalmGlobalStmt_of_bdryL1 : Prop16BdryL1Stmt → Prop16PalmGlobalStmt` (and the variant from
the local form `Prop16BdryL1LocStmt`): for coordinates `μ_j` carried by compacts of `D ∪ (a,b)`,
`E ∫_{(a',b')} G((h0 + X)(μ_·), x) ν(dx) = ∫_{(a',b')} E G((h0 + X + (γ/2) G_D(x,·))(μ_·), x)
d(E ν)(x)`.

Source: the Palm (rooted-measure) formula for Gaussian multiplicative chaos, Duplantier–Sheffield,
*Liouville quantum gravity and KPZ*, arXiv:0808.1560, §3.3 (p. 22), used in Sheffield,
arXiv:1012.4797, proof of Proposition 1.6 (p. 25); abstract form
`PalmNorm.palm_lintegral_coords`. Route (own bookkeeping):

* the boundary measure is built from the window-masked field `maskK Kw X` (regularity:
  `prop16ActReg_holds`; `L¹` convergence: `Prop16BdryL1Stmt`), exactly as in
  `palm_formula_prop16_window'`;
* the coordinates `X(μ_j)` are attached at tags (`tagField`, `Prop16PalmGlobalTag.lean`), and the
  covariance with the circle averages is computed with the M6 kernel of the compact
  `Kw ∪ L_j` (`L_j` carrying `μ_j`), so the Cameron–Martin shift is `(γ/2) G_D(x, ·)(μ_j)`;
* the density `ρ` of the Palm formula is identified with the mean measure on the window by the
  case `G(y, x) = f(x)` (as in `palm_formula_prop16_window_mean`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal

namespace QuantumZipper

namespace Prop16Asm

/-- The kernel read at the tags: on the strip of index `j`, the mixed Green kernel of the
`j`-th compact, translated back. -/
def tagKernel (L : ℕ → Set ℂ) (kk : ℕ → ℂ → ℂ → ℝ) (ρ0 : ℝ) (x : ℝ) (w : ℂ) : ℝ :=
  mixedGreenK (L (tagIndex (ρ0 + 2) w)) (kk (tagIndex (ρ0 + 2) w)) x
    (w - tagShift ρ0 (ρ0 + 2) (tagIndex (ρ0 + 2) w))

theorem measurable_tagKernel {L : ℕ → Set ℂ} {kk : ℕ → ℂ → ℂ → ℝ} {ρ0 : ℝ}
    (hL : ∀ j, IsClosed (L j)) (hk : ∀ j, ContinuousOn (Function.uncurry (kk j)) (L j ×ˢ L j)) :
    Measurable (Function.uncurry (tagKernel L kk ρ0)) := by
  have hj : ∀ j : ℕ, Measurable (Function.uncurry (mixedGreenK (L j) (kk j)) ∘
      fun p : ℝ × ℂ => (p.1, p.2 - tagShift ρ0 (ρ0 + 2) j)) := fun j =>
    (measurable_mixedGreenK (hL j) (hk j)).comp
      (measurable_fst.prodMk (measurable_snd.sub_const (tagShift ρ0 (ρ0 + 2) j)))
  have H : Measurable fun q : (ℝ × ℂ) × ℕ => (Function.uncurry (mixedGreenK (L q.2) (kk q.2)) ∘
      fun p : ℝ × ℂ => (p.1, p.2 - tagShift ρ0 (ρ0 + 2) q.2)) q.1 :=
    measurable_from_prod_countable_left hj
  have hJ : Measurable fun w : ℂ => tagIndex (ρ0 + 2) w :=
    Nat.measurable_floor.comp (Complex.measurable_im.neg.div_const _)
  have e : Function.uncurry (tagKernel L kk ρ0) =
      (fun q : (ℝ × ℂ) × ℕ => (Function.uncurry (mixedGreenK (L q.2) (kk q.2)) ∘
        fun p : ℝ × ℂ => (p.1, p.2 - tagShift ρ0 (ρ0 + 2) q.2)) q.1) ∘
        fun p : ℝ × ℂ => (p, tagIndex (ρ0 + 2) p.2) := by
    funext p
    simp only [Function.comp_apply, Function.uncurry_apply_pair, tagKernel]
    rfl
  rw [e]
  exact H.comp (measurable_id.prodMk (hJ.comp measurable_snd))

theorem measurable_remK_diag_pg {K : Set ℂ} {k : ℂ → ℂ → ℝ} (hK : IsClosed K)
    (hk : ContinuousOn (Function.uncurry k) (K ×ˢ K)) :
    Measurable fun x : ℝ => remK K k (x : ℂ) (x : ℂ) :=
  (measurable_remK hK hk).comp
    (Complex.continuous_ofReal.measurable.prodMk Complex.continuous_ofReal.measurable)

theorem measurable_rhoLim_pg {γ : ℝ} {m : ℂ → ℝ} (hm : Continuous m) {ctil : ℝ → ℝ}
    (hctil : Measurable ctil) : Measurable (Palm.rhoLim γ m ctil) := by
  unfold Palm.rhoLim
  exact Real.measurable_exp.comp ((((hm.measurable.comp Complex.measurable_ofReal).const_mul
    γ).div_const 2).add ((hctil.const_mul (γ ^ 2)).div_const 8))

/-- **Core: the global Palm formula against Lebesgue measure with a density.** -/
theorem palm_global_core (hB : Prop16BdryL1Stmt) {γ : ℝ} {D : Set ℂ} {c d a b : ℝ}
    {h0 : ℂ → ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}
    (hH : Prop16PalmHyp γ D c d a b h0 P X) {μ : ℕ → Measure ℂ} (hμ : ∀ j, LocAdm D a b (μ j))
    {a' b' : ℝ} (ha : a < a') (hb : b' < b) :
    ∃ ρ : ℝ → ℝ, Measurable ρ ∧ ∀ G : (ℕ → ℝ) × ℝ → ℝ≥0∞, Measurable G →
      ∫⁻ ω, ∫⁻ x in Ioo a' b', G (rawCoords h0 X μ ω, x) ∂(prop16Nu γ h0 a b (X ω)) ∂P =
        ∫⁻ x in Ioo a' b', ENNReal.ofReal (ρ x) *
          ∫⁻ ω, G (palmRawCoords γ D c d h0 X μ (ω, x), x) ∂P := by
  obtain ⟨-, -, hgeom, -, hca, hbd, hh0, hP, hX, -, hfinab⟩ := hH.1
  have hν := hH.2.1
  obtain ⟨g0, hg0, hgap0⟩ := exists_gap_lower hgeom hca hbd ha hb
  obtain ⟨g, hg, hgg, hnd⟩ := exists_nondyadic_scale hg0
  have hgap : ∀ t ∈ Icc a' b', g ≤ palmGap D a b t := fun t ht => hgg.trans (hgap0 t ht)
  have hL := mixedLocalHyp_palmWinK hgeom hca hbd hg hgap
  have hKsub : palmWinK a' b' g ⊆ D ∪ realSet (Ioo a b) := palmWinK_subset hg hgap
  obtain ⟨k, hk, hkc⟩ := K3.mixedLocalKernel hgeom hL
  obtain ⟨m, hm, hmK⟩ := exists_continuous_eqOn (isCompact_palmWinK a' b' g).isClosed
    (hh0.mono hKsub)
  -- the compacts `Kw ∪ L_j` and their M6 kernels
  have hfam : ∀ j, ∃ (L : Set ℂ) (R : ℝ) (kk : ℂ → ℂ → ℝ), μ j Lᶜ = 0 ∧
      palmWinK a' b' g ⊆ L ∧ K3.MixedLocalHyp D (realSet (Icc c d)) L R ∧
      ContinuousOn (Function.uncurry kk) (L ×ˢ L) ∧
      ∀ μ ν : Measure ℂ, IsAdmissibleH μ → μ Lᶜ = 0 → IsAdmissibleH ν → ν Lᶜ = 0 →
        dualCov D (mixedSpace D (realSet (Icc c d))) μ ν =
          kernelCov (fun x y => neumannH x y + kk x y) μ ν := by
    intro j
    obtain ⟨-, L, hLc, hLsub, hLμ⟩ := hμ j
    obtain ⟨R, -, hLR⟩ := exists_mixedLocalHyp_pg hgeom hca hbd
      ((isCompact_palmWinK a' b' g).union hLc) (union_subset hKsub hLsub)
    obtain ⟨kk, hkk, hkkc⟩ := K3.mixedLocalKernel hgeom hLR
    exact ⟨_, R, kk, measure_mono_null (compl_subset_compl.2 subset_union_right) hLμ,
      subset_union_left, hLR, hkk, hkkc⟩
  choose L R' kk hLμ hKwL hLR hkk hkkc using hfam
  -- the band `0 ≤ Im ≤ ρ0` carrying all coordinates
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 hgeom.2.2.1
  obtain ⟨ρ0, hρ0, hρ0C⟩ : ∃ ρ0 : ℝ, 0 ≤ ρ0 ∧ C ≤ ρ0 := ⟨max C 0, le_max_right _ _,
    le_max_left _ _⟩
  have hband : ∀ j, μ j (tagBand ρ0)ᶜ = 0 := by
    intro j
    obtain ⟨-, L0, -, hLsub, hL0⟩ := hμ j
    refine measure_mono_null (compl_subset_compl.2 fun z hz => ?_) hL0
    rcases hLsub hz with h | ⟨t, -, rfl⟩
    · have h1 : 0 < z.im := hgeom.2.2.2.1 h
      exact ⟨h1.le, ((le_abs_self _).trans (Complex.abs_im_le_norm z)).trans
        ((hC z h).trans hρ0C)⟩
    · exact ⟨by simp, by simpa using hρ0⟩
  have hinj : ∀ i j, tagMeas ρ0 (ρ0 + 2) μ i = tagMeas ρ0 (ρ0 + 2) μ j → μ i = μ j :=
    fun i j h => tagMeas_inj hρ0 hband h
  have hadm : ∀ j, IsAdmissibleDual D (mixedSpace D (realSet (Icc c d))) (μ j) := fun j =>
    isAdmissibleDual_of_localHyp (hLR j) (hμ j).1 (hLμ j)
  have hZ := isCenteredGaussianField_tagField (ι := tagMeas ρ0 (ρ0 + 2) μ) hL hX hadm
  have hZfc : ∀ ω z r, tagField (palmWinK a' b' g) X (tagMeas ρ0 (ρ0 + 2) μ) μ ω
      (foldedCircle z r) = maskK (palmWinK a' b' g) X ω (foldedCircle z r) := fun ω z r =>
    tagField_of_not (fun j => tagMeas_ne_foldedCircle hρ0 hband j z r) ω
  have hZfcK : ∀ ω x n, tagField (palmWinK a' b' g) X (tagMeas ρ0 (ρ0 + 2) μ) μ ω
      (Palm.fcK x n) = maskK (palmWinK a' b' g) X ω (Palm.fcK x n) := fun ω x n =>
    hZfc ω _ _
  have havg : ∀ ω n z, avgReg (ofFun m + tagField (palmWinK a' b' g) X
      (tagMeas ρ0 (ρ0 + 2) μ) μ ω) n z = avgReg (ofFun m + maskK (palmWinK a' b' g) X ω) n z := by
    intro ω n z
    unfold avgReg
    simp only [Pi.add_apply, hZfc]
  have hbdry : ∀ ω n, bdryApprox γ (ofFun m + tagField (palmWinK a' b' g) X
      (tagMeas ρ0 (ρ0 + 2) μ) μ ω) n = bdryApprox γ (ofFun m + maskK (palmWinK a' b' g) X ω) n := by
    intro ω n
    unfold bdryApprox
    simp only [havg]
  -- the tag kernel
  set cK : ℝ → ℂ → ℝ := tagKernel L kk ρ0 with hcKdef
  have hc : Measurable (Function.uncurry cK) :=
    measurable_tagKernel (fun j => (hLR j).compact.isClosed) hkk
  have hcint : ∀ j x, ∫ w, cK x w ∂(tagMeas ρ0 (ρ0 + 2) μ j) =
      ∫ z, mixedGreenK (L j) (kk j) x z ∂(μ j) := by
    intro j x
    have hcx : Measurable fun w => cK x w := hc.comp (measurable_const.prodMk measurable_id)
    rw [tagMeas, integral_map (measurable_add_tagShift ρ0 _ j).aemeasurable
      hcx.aestronglyMeasurable]
    refine integral_congr_ae ?_
    have hb' : ∀ᵐ z ∂(μ j), z ∈ tagBand ρ0 := by rw [ae_iff]; exact hband j
    filter_upwards [hb'] with z hz
    simp only [hcKdef, tagKernel, tagIndex_add ρ0 hρ0 hz, add_sub_cancel_right]
  -- window facts
  have hxK : ∀ x ∈ Icc a' b', (x : ℂ) ∈ palmWinK a' b' g := fun x hx => ofReal_mem_palmWinK hx
  have hev : ∀ x ∈ Icc a' b', ∀ᶠ n in atTop, Palm.fcK x n (palmWinK a' b' g)ᶜ = 0 :=
    fun x hx => (tendsto_radius_zero_nodeB.eventually
      (ge_mem_nhds (show (0 : ℝ) < g / 2 by positivity))).mono
        fun n hn => foldedCircle_palmWinK_compl hx (radius_pos n).le hn
  have hevL : ∀ j, ∀ x ∈ Icc a' b', ∀ᶠ n in atTop, Palm.fcK x n (L j)ᶜ = 0 := fun j x hx =>
    (hev x hx).mono fun n hn => measure_mono_null (compl_subset_compl.2 (hKwL j)) hn
  have hregM := hreg_maskK_of_actual hm hmK hg hnd (hact_of_actReg prop16ActReg_holds hH ha hb hgap)
  have hreg : ∀ n, ∀ x ∈ Icc a' b', ∀ᵐ ω ∂P,
      avgReg (ofFun m + tagField (palmWinK a' b' g) X (tagMeas ρ0 (ρ0 + 2) μ) μ ω) n (x : ℂ) =
        (ofFun m + tagField (palmWinK a' b' g) X (tagMeas ρ0 (ρ0 + 2) μ) μ ω) (Palm.fcK x n) := by
    intro n x hx
    filter_upwards [hregM n x hx] with ω hω
    rw [havg, hω, Pi.add_apply, Pi.add_apply, hZfcK]
  obtain ⟨M, hM0, hM⟩ := exists_bound_remK hL.compact hk
  have hvarbd : ∀ n, ∀ x ∈ Icc a' b', Palm.varK (tagField (palmWinK a' b' g) X
      (tagMeas ρ0 (ρ0 + 2) μ) μ) P x n + 2 * Real.log (radius n) ≤ M := by
    intro n x _
    have := var_maskK_fc_add_log_le hL hk hkc hX hM0 hM x n
    simpa only [Palm.varK, hZfcK] using this
  have hvar : ∀ x ∈ Icc a' b', Tendsto (fun n => Palm.varK (tagField (palmWinK a' b' g) X
      (tagMeas ρ0 (ρ0 + 2) μ) μ) P x n + 2 * Real.log (radius n)) atTop
      (𝓝 (remK (palmWinK a' b' g) k (x : ℂ) (x : ℂ))) := by
    intro x hx
    have := tendsto_var_maskK hL hk hkc hX (hxK x hx) (hev x hx)
    rw [← remK_of_mem (k := k) (hxK x hx) (hxK x hx)] at this
    simpa only [Palm.varK, hZfcK] using this
  have hcov : ∀ x ∈ Icc a' b', ∀ j, Tendsto (fun n =>
      cov[fun ω => tagField (palmWinK a' b' g) X (tagMeas ρ0 (ρ0 + 2) μ) μ ω
        (tagMeas ρ0 (ρ0 + 2) μ j), fun ω => tagField (palmWinK a' b' g) X
          (tagMeas ρ0 (ρ0 + 2) μ) μ ω (Palm.fcK x n); P]) atTop
      (𝓝 (∫ w, cK x w ∂(tagMeas ρ0 (ρ0 + 2) μ j))) := by
    intro x hx j
    rw [hcint]
    refine (tendsto_cov_mixed_fc (hLR j) (hkk j) (hkkc j) hX (hμ j).1 (hLμ j)
      (hKwL j (hxK x hx)) (hevL j x hx)).congr' ?_
    filter_upwards [hev x hx] with n hn
    simp only [tagField_tag hinj, hZfcK,
      maskK_of_KAdm (show KAdm (palmWinK a' b' g) (Palm.fcK x n) from ⟨isAdmissibleH_fcK x n, hn⟩)]
  have hfin : ∫⁻ ω, prop16Nu γ h0 a b (X ω) (Icc a' b') ∂P < ∞ :=
    lt_of_le_of_lt (lintegral_mono fun ω => measure_mono (Icc_subset_Icc ha.le hb.le)) hfinab
  have hL1 : PalmFree.BdryL1ConvCc γ m (tagField (palmWinK a' b' g) X (tagMeas ρ0 (ρ0 + 2) μ) μ)
      P (fun ω => prop16Nu γ h0 a b (X ω)) a' b' := by
    intro f hf hfc hfab
    simp only [hbdry]
    exact bdryL1ConvCc_maskK hmK hg (hB γ D c d a b h0 P X hH a' b' ha hb) f hf hfc hfab
  have hctil : Measurable fun x : ℝ => remK (palmWinK a' b' g) k (x : ℂ) (x : ℂ) :=
    measurable_remK_diag_pg (isCompact_palmWinK a' b' g).isClosed hk
  have hρm : Measurable (Palm.rhoLim γ m fun x => remK (palmWinK a' b' g) k (x : ℂ) (x : ℂ)) :=
    measurable_rhoLim_pg hm hctil
  refine ⟨_, hρm, fun G hG => ?_⟩
  haveI := hP
  haveI : ∀ j, IsFiniteMeasure (μ j) := fun j => (hμ j).1.1
  haveI : ∀ j, IsFiniteMeasure (tagMeas ρ0 (ρ0 + 2) μ j) := fun j => by
    unfold tagMeas; infer_instance
  set v : ℕ → ℝ := fun j => ofFun m (tagMeas ρ0 (ρ0 + 2) μ j) with hv
  set u : ℕ → ℝ := fun j => ofFun h0 (μ j) with hu
  set G' : (ℕ → ℝ) × ℝ → ℝ≥0∞ := fun q => G (q.1 - v + u, q.2) with hG'def
  have hG' : Measurable G' :=
    hG.comp (((measurable_fst.sub_const v).add_const u).prodMk measurable_snd)
  have hcoL : ∀ ω, Palm.coords m (tagField (palmWinK a' b' g) X (tagMeas ρ0 (ρ0 + 2) μ) μ)
      (tagMeas ρ0 (ρ0 + 2) μ) ω - v + u = rawCoords h0 X μ ω := by
    intro ω; funext j
    simp only [Pi.add_apply, Pi.sub_apply, Palm.coords, rawCoords, tagField_tag hinj, hv, hu]
    ring
  have hcoR : ∀ x ∈ Icc a' b', ∀ ω,
      Palm.coords m (tagField (palmWinK a' b' g) X (tagMeas ρ0 (ρ0 + 2) μ) μ)
        (tagMeas ρ0 (ρ0 + 2) μ) ω + Palm.shiftLim γ cK (tagMeas ρ0 (ρ0 + 2) μ) x - v + u =
        palmRawCoords γ D c d h0 X μ (ω, x) := by
    intro x hx ω; funext j
    simp only [Pi.add_apply, Pi.sub_apply, Palm.coords, Palm.shiftLim, palmRawCoords,
      palmMixedField, Pi.smul_apply, smul_eq_mul, tagField_tag hinj, hv, hu]
    rw [hcint, ← mixedGreenSample_eq (hLR j) (hkk j) (hkkc j) (hμ j).1 (hLμ j)
      (hKwL j (hxK x hx)) (hevL j x hx)]
    ring
  have hA : Measurable fun p : Ω × ℝ => G (rawCoords h0 X μ p.1, p.2) :=
    hG.comp (((measurable_coords_mixed hX h0 μ).comp measurable_fst).prodMk measurable_snd)
  have hBm : Measurable fun x => ENNReal.ofReal (Palm.rhoLim γ m
      (fun x => remK (palmWinK a' b' g) k (x : ℂ) (x : ℂ)) x) *
        ∫⁻ ω, G (palmRawCoords γ D c d h0 X μ (ω, x), x) ∂P :=
    hρm.ennreal_ofReal.mul (hG.comp ((measurable_palmRawCoords hX.measurable_coord μ).prodMk
      measurable_snd)).lintegral_prod_left'
  have hfin' : ∀ᵐ ω ∂P, prop16Nu γ h0 a b (X ω) (Icc a' b') < ∞ :=
    ae_lt_top' ((Measure.measurable_coe measurableSet_Icc).comp_aemeasurable hν) hfin.ne
  refine lintegral_Ioo_of_bump hν hfin' hA hBm fun n => ?_
  have hwab : ∀ x ∉ Icc a' b', LQGMeas.openBump (Ioo a' b') n x = 0 := fun x hx => by
    by_contra hne
    exact hx (Ioo_subset_Icc_self
      (LQGMeas.tsupport_openBump_subset (Ioo a' b') n (subset_tsupport _ hne)))
  have H := PalmNorm.palm_lintegral_coords (γ := γ) (a := a') (b := b')
    (μ := tagMeas ρ0 (ρ0 + 2) μ) (ν := fun ω => prop16Nu γ h0 a b (X ω)) hZ hm (Cv := M) hctil
    hc hreg hvarbd hvar hcov hν hfin hL1 (LQGMeas.continuous_openBump _ n)
    (LQGMeas.hasCompactSupport_openBump (isBounded_Ioo a' b') n) (LQGMeas.openBump_nonneg _ n)
    hwab hG'
  refine (lintegral_congr fun ω => lintegral_congr fun x => ?_).trans
    (H.trans (lintegral_congr fun x => ?_))
  · simp only [hG'def, hcoL]
  · by_cases hx : x ∈ Icc a' b'
    · rw [ENNReal.ofReal_mul (LQGMeas.openBump_nonneg _ n x), mul_assoc]
      congr 2
      refine lintegral_congr fun ω => ?_
      simp only [hG'def, hcoR x hx ω]
    · simp only [hwab x hx, zero_mul, ENNReal.ofReal_zero]

/-- **The global window Palm formula from the `L¹` node.** -/
theorem prop16PalmGlobalStmt_of_bdryL1 (hB : Prop16BdryL1Stmt) : Prop16PalmGlobalStmt := by
  intro γ D c d a b h0 Ω _ P X hH μ hμ
  refine ⟨measurable_palmRawCoords hH.1.2.2.2.2.2.2.2.2.1.measurable_coord μ,
    fun a' b' ha hb G hG => ?_⟩
  obtain ⟨ρ, -, H⟩ := palm_global_core hB hH hμ ha hb
  haveI : IsProbabilityMeasure P := hH.1.2.2.2.2.2.2.2.1
  have hmean : ∀ f : ℝ → ℝ≥0∞, Measurable f →
      ∫⁻ x in Ioo a' b', f x ∂palmMean P (fun ω => prop16Nu γ h0 a b (X ω)) a b =
        ∫⁻ x in Ioo a' b', ENNReal.ofReal (ρ x) * f x := by
    intro f hf
    rw [setLIntegral_palmMean hH.2.1 ha.le hb.le hf]
    have := H (fun q => f q.2) (hf.comp measurable_snd)
    simp only [lintegral_const, measure_univ, mul_one] at this
    exact this
  have hHm : Measurable fun x => ∫⁻ ω, G (palmRawCoords γ D c d h0 X μ (ω, x), x) ∂P :=
    (hG.comp ((measurable_palmRawCoords hH.1.2.2.2.2.2.2.2.2.1.measurable_coord μ).prodMk
      measurable_snd)).lintegral_prod_left'
  rw [hmean _ hHm, H G hG]

/-- **The global window Palm formula from the local `L¹` node.** -/
theorem prop16PalmGlobalStmt_of_bdryL1Loc (hB : Prop16BdryL1LocStmt) : Prop16PalmGlobalStmt :=
  prop16PalmGlobalStmt_of_bdryL1 (prop16BdryL1Stmt_of_loc hB)

end Prop16Asm

end QuantumZipper
