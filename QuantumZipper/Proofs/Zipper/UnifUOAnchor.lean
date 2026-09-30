import QuantumZipper.Proofs.Zipper.UnifUOFixed

/-!
# UNIF-UO (2): extended anchored windows (all live windows, anchors `q ≥ 0`, atomless limits)

Task UNIF-UO (decision D26). `AnchorWindowStmt` (AW) covers only windows `0₋(T) < u < v <
0₋(T − q)` of the fully unzipped picture (the unzipped curve), anchors `q > 0`, and records
masses only. For `UnifOffTipStmt` we need:

* all windows live at `q`: `u < v < 0₋(T − q)`, including the outer real line `v ≤ 0₋(T)` and
  windows straddling `0₋(T)` (whose images straddle `O⁻_s = F_s(0₋(T))`);
* the anchor `q = 0` (for times `s` near `0`);
* the local limit itself, as the pushforward of `ν_{h⁰_T}|_{(u,v)}`, so that atomlessness of
  `ν_{h⁰_T}` (`Wire2.ae_nu0_regular`) transfers.

The analytic input is **`AnchorUnifFamExtStmt`** (AC-fam-ext, open, a hypothesis): literally
`AnchorUnifFamStmt` (UnifSWMain) with the lower bound `0₋(T) < u` dropped and `q = 0` allowed
(`0 ≤ q < T`). It is the same Sheffield–Wang uniform convergence (arXiv:1605.06171, (3.5) p. 12,
boundary version Thm 4.3) for the field `h⁰_q` (independent of the driver after `q`) and the
maps `F_s`, `s ∈ [q,T]`, on a window live at `q`.

* `anchorApproxContExt` (AC-cont on all live windows, `q ≥ 0`): proved; the proof of
  `anchorApproxContStmt_holds` never uses `0₋(T) < u` nor `q > 0` (only liveness).
* `eq_const_of_rat_pos`, **`det_anchor_ext`**: `det_anchor` with the rational-time inputs needed
  only at rational `r > 0`, returning an atomless local limit.
* **`ae_anchor_ext`**: AC-fam-ext ⇒ a.s., for all rational `0 ≤ q < T` and rational live windows,
  for all `s ∈ [q,T]` an atomless local vague limit on `F_s(u,v)`.

All reductions are own bookkeeping (as in UnifAWDet/UnifSWRat/UnifSWMain).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace RegUnif

open B2 B5 E1 E1.M4

variable {Ω : Type} [MeasurableSpace Ω]

/-- **AC-fam-ext** (open analytic core, extended): `AnchorUnifFamStmt` for all windows live at
`q` (no lower bound `0₋(T) < u`) and anchors `0 ≤ q < T`. -/
def AnchorUnifFamExtStmt (κ T : ℝ) (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) :
    Prop :=
  ∀ q : ℚ, (0 : ℝ) ≤ q → (q : ℝ) < T → ∀ u v : ℚ, ∀ i : ℕ, ∀ a b c d : ℚ, ∀ᵐ ω ∂P,
    (u : ℝ) < a → a < b → b < c → c < d → (d : ℝ) < v →
    (v : ℝ) < zeroMinus (Vr κ T B ω) (T - q) →
      UniformCauchySeqOn (fun k s => awInt κ T B X ω u v (swFam i a b c d) s k) atTop
        (Icc (q : ℝ) T ∩ range ((↑) : ℚ → ℝ))

/-- A function continuous on `[q,T]` (`0 ≤ q < T`) equal to `c` at the positive rational points
of `[q,T]` is `c` on `[q,T]`. -/
theorem eq_const_of_rat_pos {q : ℚ} {T : ℝ} (hq : (0 : ℝ) ≤ q) (hqT : (q : ℝ) < T) {L : ℝ → ℝ}
    {c : ℝ} (hL : ContinuousOn L (Icc (q : ℝ) T))
    (hr : ∀ r : ℚ, (r : ℝ) ∈ Icc (q : ℝ) T → (0 : ℝ) < r → L r = c) :
    ∀ s ∈ Icc (q : ℝ) T, L s = c := by
  intro s hs
  refine eq_of_forall_dist_le fun ε hε => ?_
  obtain ⟨δ, hδ, hδL⟩ := Metric.continuousWithinAt_iff.1 (hL s hs) ε hε
  have key : ∃ r : ℚ, (r : ℝ) ∈ Icc (q : ℝ) T ∧ (0 : ℝ) < r ∧ dist (r : ℝ) s < δ := by
    rcases hs.2.lt_or_eq with h | h
    · obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (lt_min (lt_add_of_pos_right s hδ) h)
      refine ⟨r, ⟨hs.1.trans hr1.le, hr2.le.trans (min_le_right _ _)⟩,
        hq.trans_lt (hs.1.trans_lt hr1), ?_⟩
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith [min_le_left (s + δ) T]
    · obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (max_lt (sub_lt_self s hδ) (h ▸ hqT : (q : ℝ) < s))
      refine ⟨r, ⟨(le_max_right _ _).trans hr1.le, hr2.le.trans hs.2⟩,
        hq.trans_lt ((le_max_right _ _).trans_lt hr1), ?_⟩
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith [le_max_left (s - δ) (q : ℝ)]
  obtain ⟨r, hrm, hr0, hd⟩ := key
  have := hδL hrm hd
  rw [hr r hrm hr0, dist_comm] at this
  exact this.le

/-- **Deterministic core, extended**: `det_anchor` with rational-time inputs at `r > 0` only,
returning an atomless local limit when `νT` is atomless. -/
theorem det_anchor_ext {q : ℚ} {T : ℝ} (hq : (0 : ℝ) ≤ q) (hqT : (q : ℝ) < T) {u v : ℚ}
    (huv : (u : ℝ) < v) {A : ℝ → ℕ → Measure ℝ}
    {ν : ℝ → Measure ℝ} {νT : Measure ℝ} (hfin : νT (Ioo (u : ℝ) v) < ∞)
    (hat : ∀ x, νT {x} = 0) {F : ℝ → ℝ → ℝ}
    (hΦ : ∀ s ∈ Icc (q : ℝ) T, ∃ Φ : ℝ ≃o ℝ, ∀ y ∈ Icc (u : ℝ) v, Φ y = F s y)
    (hlim : ∀ r : ℚ, (r : ℝ) ∈ Icc (q : ℝ) T → (0 : ℝ) < r → IsVagueLimitR (A r) (ν r))
    (hwin : ∀ r : ℚ, (r : ℝ) ∈ Icc (q : ℝ) T → (0 : ℝ) < r → ∀ a b : ℚ, (u : ℝ) ≤ a →
      (a : ℝ) < b → (b : ℝ) ≤ v → νT (Ioo a b) = ν r (Ioo (F r a) (F r b)))
    (hconv : ∀ f : ℝ → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ Ioo (u : ℝ) v →
      ∃ L : ℝ → ℝ, ContinuousOn L (Icc (q : ℝ) T) ∧ ∀ s ∈ Icc (q : ℝ) T,
        Tendsto (fun k => ∫ x, awTest (F s) u v f x ∂A s k) atTop (𝓝 (L s))) :
    ∀ s ∈ Icc (q : ℝ) T, ∃ μ : Measure ℝ, IsVagueLimitOnR (Ioo (F s u) (F s v)) (A s) μ ∧
      ∀ x, μ {x} = 0 := by
  have hconst : ∀ f : ℝ → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ Ioo (u : ℝ) v →
      ∀ s ∈ Icc (q : ℝ) T, Tendsto (fun k => ∫ x, awTest (F s) u v f x ∂A s k) atTop
        (𝓝 (∫ x, f x ∂νT)) := by
    intro f hf hfc hfs
    obtain ⟨L, hLc, hLt⟩ := hconv f hf hfc hfs
    have hr : ∀ r : ℚ, (r : ℝ) ∈ Icc (q : ℝ) T → (0 : ℝ) < r → L r = ∫ x, f x ∂νT := by
      intro r hr hr0
      obtain ⟨Φ, hΦr⟩ := hΦ r hr
      have hg := awTest_eq hΦr hfs
      have hlimr := (hlim r hr hr0).2 (awTest (F r) u v f)
        (by rw [hg]; exact hf.comp Φ.symm.continuous)
        (by rw [hg]; exact hasCompactSupport_comp_orderIso hfc Φ.symm)
      refine (tendsto_nhds_unique (hLt r hr) hlimr).trans ?_
      rw [hg]
      exact (integral_eq_of_windows huv hΦr hfin (hwin r hr hr0) hf hfs).symm
    intro s hs
    rw [← eq_const_of_rat_pos hq hqT hLc hr s hs]
    exact hLt s hs
  intro s hs
  obtain ⟨Φ, hΦs⟩ := hΦ s hs
  have hFu : F s u = Φ u := (hΦs u ⟨le_rfl, huv.le⟩).symm
  have hFv : F s v = Φ v := (hΦs v ⟨huv.le, le_rfl⟩).symm
  have hm : Measurable Φ := Φ.continuous.measurable
  have hpre : Φ ⁻¹' Ioo (F s u) (F s v) = Ioo (u : ℝ) v := by
    rw [hFu, hFv, OrderIso.preimage_Ioo, OrderIso.symm_apply_apply, OrderIso.symm_apply_apply]
  set μ := (νT.restrict (Ioo (u : ℝ) v)).map Φ with hμ
  refine ⟨μ, ⟨?_, fun K _ _ => ?_, fun g hg hgc hgs => ?_⟩, fun x => ?_⟩
  · rw [hμ, Measure.map_apply hm measurableSet_Ioo.compl, preimage_compl, hpre,
      Measure.restrict_apply measurableSet_Ioo.compl]
    simp
  · calc μ K ≤ μ univ := measure_mono (subset_univ _)
      _ < ∞ := by
        rw [hμ, Measure.map_apply hm MeasurableSet.univ, preimage_univ,
          Measure.restrict_apply_univ]
        exact hfin
  · set f := g ∘ Φ with hfdef
    have hfc : Continuous f := hg.comp Φ.continuous
    have hfcs : HasCompactSupport f := hasCompactSupport_comp_orderIso hgc Φ
    have hfs : tsupport f ⊆ Ioo (u : ℝ) v :=
      (tsupport_comp_subset_preimage' Φ.continuous).trans (by rw [← hpre]; exact preimage_mono hgs)
    have hg' : awTest (F s) u v f = g := by
      rw [awTest_eq hΦs hfs]
      funext x
      simp [f]
    have hint : ∫ t, g t ∂μ = ∫ x, f x ∂νT := by
      rw [hμ, integral_map hm.aemeasurable hg.aestronglyMeasurable]
      exact (integral_eq_restrict_of_support fun x hx =>
        image_eq_zero_of_notMem_tsupport fun h => hx (hfs h)).symm
    have := hconst f hfc hfcs hfs s hs
    rw [hg'] at this
    rw [hint]
    exact this
  · rw [hμ, Measure.map_apply hm (measurableSet_singleton x)]
    have : Φ ⁻¹' {x} = {Φ.symm x} := by
      ext y; simp [OrderIso.eq_symm_apply]
    rw [this]
    exact nonpos_iff_eq_zero.1 ((Measure.restrict_apply_le _ _).trans (hat _).le)

variable {P : Measure Ω} [IsProbabilityMeasure P] {κ T : ℝ} {B : ℝ≥0 → Ω → ℝ}
  {X : Ω → FieldSample}

/-- **AC-cont on all live windows, anchors `q ≥ 0`** (proof of `anchorApproxContStmt_holds`). -/
theorem anchorApproxContExt (hκ : 0 < κ) (hκ4 : κ < 4) (hT : 0 < T)
    (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P) :
    ∀ q : ℚ, (0 : ℝ) ≤ q → (q : ℝ) ≤ T → ∀ u v : ℚ, ∀ᵐ ω ∂P,
      (u : ℝ) < v → (v : ℝ) < zeroMinus (Vr κ T B ω) (T - q) →
      ∀ f : ℝ → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ Ioo (u : ℝ) v →
        ∀ k : ℕ, ContinuousOn (fun s => awInt κ T B X ω u v f s k) (Icc (q : ℝ) T) := by
  intro q hq hqT u v
  filter_upwards [ae_forall_isRegularWith_joint (κ := κ) (γ := Real.sqrt κ) hB hX hind hT,
    ae_zeroMinus_Vr_facts RS.rohdeSchrammSimple hκ hκ4.le hT P B hB, hB.cont,
    ae_isSimpleCurveHull_revHull_Vr RS.rohdeSchrammSimple hκ hκ4.le hT P B hB]
    with ω hG hzm hcont hK huv hv f hf hfc hfs k
  obtain ⟨G, hGc, hGr⟩ := hG
  obtain ⟨-, -, hanti, -, -, -⟩ := hzm
  set V := Vr κ T B ω with hVdef
  have hVc : Continuous V := continuous_vrev (drive_continuous hcont) T
  have hV0 : V 0 = 0 := vrev_zero hT.le
  set γ := Real.sqrt κ with hγ
  set S := Icc (q : ℝ) T with hS
  have hzmle : ∀ r ∈ S, zeroMinus V (T - q) ≤ zeroMinus V (T - r) := fun r hr =>
    hanti.antitoneOn ⟨by linarith [hr.2], by linarith [hr.1, hq]⟩
      ⟨by linarith, by linarith⟩ (by linarith [hr.1])
  have hlive : ∀ r ∈ S, ∀ x ∈ Icc (u : ℝ) v, IsLive V (T - r) x := fun r hr x hx =>
    (mem_liveNeg_of_lt_zeroMinus hVc hV0 hT hK (by linarith [hr.2]) (by linarith [hr.1, hq])
      ((hx.2.trans_lt hv).trans_le (hzmle r hr))).2
  set F : ℝ → ℝ → ℝ := fun s => realRevMap V (T - s) with hFdef
  have hΦ : ∀ s ∈ S, ∃ Φ : ℝ ≃o ℝ, ∀ y ∈ Icc (u : ℝ) v, Φ y = F s y := fun s hs =>
    exists_orderIso_eq_realRevMap hVc (by linarith [hs.2]) huv (hlive s hs)
  have hFc : ∀ y ∈ Icc (u : ℝ) v, ContinuousOn (fun s => F s y) S := by
    intro y hy
    obtain ⟨w, hw⟩ := exists_isRealRevSol_of_isLive (hlive q ⟨le_rfl, hqT⟩ y hy)
    have hm : MapsTo (fun s : ℝ => T - s) S (Icc 0 (T - q)) := fun s hs =>
      ⟨by linarith [hs.2], by linarith [hs.1]⟩
    refine (hw.1.comp (continuousOn_const.sub continuousOn_id) hm).congr fun s hs => ?_
    exact RealLine.realRevMap_eq hVc hw (hm hs).1 (hm hs).2
  -- a fixed interval containing all image windows
  obtain ⟨Mu, hMu⟩ := isCompact_Icc.exists_bound_of_continuousOn (hFc u ⟨le_rfl, huv.le⟩)
  obtain ⟨Mv, hMv⟩ := isCompact_Icc.exists_bound_of_continuousOn (hFc v ⟨huv.le, le_rfl⟩)
  set M := max Mu Mv
  have hsupp : ∀ s ∈ S, ∀ x, x ∉ Icc (-M) M → awTest (F s) u v f x = 0 := by
    intro s hs x hx
    obtain ⟨Φ, hΦs⟩ := hΦ s hs
    refine awTest_eq_zero_of_not_mem hΦs fun hmem => hx ⟨?_, ?_⟩
    · have := hMu s hs
      rw [Real.norm_eq_abs, abs_le] at this
      linarith [hmem.1, le_max_left Mu Mv]
    · have := hMv s hs
      rw [Real.norm_eq_abs, abs_le] at this
      linarith [hmem.2, le_max_right Mu Mv]
  obtain ⟨Cf, hCf⟩ := hf.bounded_above_of_compact_support hfc
  -- the regularized averages via the joint witness
  have hS0 : ∀ s ∈ S, s ∈ Icc (0 : ℝ) T := fun s hs => ⟨hq.trans hs.1, hs.2⟩
  have havg : ∀ s ∈ S, ∀ x : ℝ, avgReg (h0f κ s B X ω) k (x : ℂ) = G (s, ((x : ℂ), radius k)) := by
    intro s hs x
    rw [h0f_eq_unzippedField]
    exact (hGr s (hS0 s hs)).avgReg_eq k (ofReal_mem_Hbar_ug x)
  have hGx : ∀ x : ℝ, ContinuousOn (fun s => G (s, ((x : ℂ), radius k))) S := fun x =>
    hGc.comp (continuousOn_id.prodMk continuousOn_const) fun s hs =>
      ⟨hS0 s hs, ofReal_mem_Hbar_ug x, radius_pos k⟩
  obtain ⟨CG, hCG⟩ := (isCompact_Icc.prod (isCompact_Icc (a := -M) (b := M))).exists_bound_of_continuousOn
    (f := fun p : ℝ × ℝ => G (p.1, ((p.2 : ℂ), radius k)))
    (hGc.comp ((continuous_fst.prodMk ((Complex.continuous_ofReal.comp continuous_snd).prodMk
      continuous_const)).continuousOn) fun p hp =>
        ⟨hS0 p.1 hp.1, ofReal_mem_Hbar_ug p.2, radius_pos k⟩)
  set dens : ℝ → ℝ → ℝ := fun s x =>
    radius k ^ (γ ^ 2 / 4) * Real.exp (γ / 2 * avgReg (h0f κ s B X ω) k (x : ℂ)) with hdens
  have hint : ∀ s, awInt κ T B X ω u v f s k = ∫ x, awTest (F s) u v f x * dens s x := by
    intro s
    unfold awInt
    rw [BdryExist.integral_bdryApprox_eq γ _ k MeasurableSet.univ (fun t ht => absurd trivial ht),
      Measure.restrict_univ]
  simp_rw [hint]
  set bnd : ℝ → ℝ := (Icc (-M) M).indicator fun _ =>
    Cf * (radius k ^ (γ ^ 2 / 4) * Real.exp (γ / 2 * CG)) with hbnd
  refine continuousOn_of_dominated (bound := bnd) ?_ ?_ ?_ ?_
  · intro s hs
    obtain ⟨Φ, hΦs⟩ := hΦ s hs
    rw [awTest_eq hΦs hfs]
    have hm := measurable_avgReg_ofReal_sw (h0f κ s B X ω) k
    have hd : Measurable (dens s) := by
      rw [hdens]
      exact measurable_const.mul ((hm.const_mul _).exp)
    exact ((hf.comp Φ.symm.continuous).measurable.mul hd).aestronglyMeasurable
  · intro s hs
    refine Eventually.of_forall fun x => ?_
    by_cases hx : x ∈ Icc (-M) M
    · rw [hbnd, indicator_of_mem hx, norm_mul]
      have hd0 : 0 ≤ dens s x := mul_nonneg (Real.rpow_nonneg (radius_pos k).le _) (Real.exp_pos _).le
      refine mul_le_mul (abs_awTest_le hCf x) ?_ (norm_nonneg _) ((norm_nonneg _).trans (hCf 0))
      rw [Real.norm_eq_abs, abs_of_nonneg hd0]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (Real.rpow_nonneg (radius_pos k).le _)
      have h1 := hCG (s, x) ⟨hs, hx⟩
      rw [Real.norm_eq_abs, abs_le] at h1
      rw [havg s hs x]
      exact mul_le_mul_of_nonneg_left h1.2 (by positivity)
    · rw [hbnd, indicator_of_notMem hx, hsupp s hs x hx, zero_mul, norm_zero]
  · exact (integrableOn_const measure_Icc_lt_top.ne).integrable_indicator measurableSet_Icc
  · refine Eventually.of_forall fun x => ?_
    refine (continuousOn_awTest hΦ hFc hf hfs x).mul ?_
    have hc : ContinuousOn (fun s => radius k ^ (γ ^ 2 / 4) *
        Real.exp (γ / 2 * G (s, ((x : ℂ), radius k)))) S :=
      continuousOn_const.mul ((continuousOn_const.mul (hGx x)).rexp)
    refine hc.congr fun s hs => ?_
    simp only [hdens, havg s hs x]

/-- **Extended anchored windows (a.s.)**: from AC-fam-ext, for all rational `0 ≤ q < T` and all
rational windows `u < v < 0₋(T − q)`, for every `s ∈ [q,T]` the approximations of `h⁰_s` have an
atomless local vague limit on `F_s(u,v)`. -/
theorem ae_anchor_ext (hκ : 0 < κ) (hκ4 : κ < 4) (hT : 0 < T)
    (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P)
    (hF : AnchorUnifFamExtStmt κ T P B X) :
    ∀ᵐ ω ∂P, ∀ q u v : ℚ, (0 : ℝ) ≤ q → (q : ℝ) < T → (u : ℝ) < v →
      (v : ℝ) < zeroMinus (Vr κ T B ω) (T - q) → ∀ s ∈ Icc (q : ℝ) T,
        ∃ μ : Measure ℝ, IsVagueLimitOnR (Ioo (realRevMap (Vr κ T B ω) (T - s) u)
          (realRevMap (Vr κ T B ω) (T - s) v)) (bdryApprox (Real.sqrt κ) (h0f κ s B X ω)) μ ∧
          ∀ x, μ {x} = 0 := by
  refine ae_all_iff.2 fun q => ae_all_iff.2 fun u => ae_all_iff.2 fun v => ?_
  by_cases hqq : (0 : ℝ) ≤ q ∧ (q : ℝ) < T
  swap
  · exact Eventually.of_forall fun ω h1 h2 => absurd ⟨h1, h2⟩ hqq
  obtain ⟨hq, hqT⟩ := hqq
  have hall : ∀ᵐ ω ∂P, ∀ i : ℕ, ∀ a b c d : ℚ,
      (u : ℝ) < a → a < b → b < c → c < d → (d : ℝ) < v →
      (v : ℝ) < zeroMinus (Vr κ T B ω) (T - q) →
        UniformCauchySeqOn (fun k s => awInt κ T B X ω u v (swFam i a b c d) s k) atTop
          (Icc (q : ℝ) T ∩ range ((↑) : ℚ → ℝ)) :=
    ae_all_iff.2 fun i => ae_all_iff.2 fun a => ae_all_iff.2 fun b => ae_all_iff.2 fun c =>
      ae_all_iff.2 fun d => hF q hq hqT u v i a b c d
  filter_upwards [hall, anchorApproxContExt hκ hκ4 hT hB hX hind q hq hqT.le u v,
    ae_forall_isRegularWith_joint (κ := κ) (γ := Real.sqrt κ) hB hX hind hT,
    ae_zeroMinus_Vr_facts RS.rohdeSchrammSimple hκ hκ4.le hT P B hB, hB.cont,
    ae_isSimpleCurveHull_revHull_Vr RS.rohdeSchrammSimple hκ hκ4.le hT P B hB,
    ae_windows_rat_ext hκ hκ4 hT hB hX hind, ae_global_rat hκ hκ4 hT hB hX hind,
    Wire2.ae_nu0_regular hκ hκ4 hT hB hX hind]
    with ω hfam hAC hG hzm hcont hK hw hGl hν _ _ huv hv
  obtain ⟨G, hGc, hGr⟩ := hG
  obtain ⟨-, -, hanti, -, -, -⟩ := hzm
  set V := Vr κ T B ω with hVdef
  have hVc : Continuous V := continuous_vrev (drive_continuous hcont) T
  have hV0 : V 0 = 0 := vrev_zero hT.le
  set γ := Real.sqrt κ with hγ
  have hzmle : ∀ r ∈ Icc (q : ℝ) T, zeroMinus V (T - q) ≤ zeroMinus V (T - r) := fun r hr =>
    hanti.antitoneOn ⟨by linarith [hr.2], by linarith [hr.1, hq]⟩
      ⟨by linarith, by linarith⟩ (by linarith [hr.1])
  have hlive : ∀ r ∈ Icc (q : ℝ) T, ∀ x ∈ Icc (u : ℝ) v, IsLive V (T - r) x := fun r hr x hx =>
    (mem_liveNeg_of_lt_zeroMinus hVc hV0 hT hK (by linarith [hr.2]) (by linarith [hr.1, hq])
      ((hx.2.trans_lt hv).trans_le (hzmle r hr))).2
  have hΦ : ∀ s ∈ Icc (q : ℝ) T, ∃ Φ : ℝ ≃o ℝ, ∀ y ∈ Icc (u : ℝ) v,
      Φ y = realRevMap V (T - s) y := fun s hs =>
    exists_orderIso_eq_realRevMap hVc (by linarith [hs.2]) huv (hlive s hs)
  have hfin : ∀ s ∈ Icc (q : ℝ) T, ∀ k,
      IsLocallyFiniteMeasure (bdryApprox γ (h0f κ s B X ω) k) := by
    intro s hs k
    have hs0 : s ∈ Icc (0 : ℝ) T := ⟨hq.trans hs.1, hs.2⟩
    have havg : ∀ x : ℝ, avgReg (h0f κ s B X ω) k (x : ℂ) = G (s, ((x : ℂ), radius k)) := by
      intro x
      rw [h0f_eq_unzippedField]
      exact (hGr s hs0).avgReg_eq k (ofReal_mem_Hbar_ug x)
    have he : bdryApprox γ (h0f κ s B X ω) k = volume.withDensity fun t : ℝ =>
        ENNReal.ofReal (radius k ^ (γ ^ 2 / 4) * Real.exp (γ / 2 * G (s, ((t : ℂ), radius k)))) := by
      unfold bdryApprox
      simp_rw [havg]
    rw [he]
    have hc : Continuous fun t : ℝ => G (s, ((t : ℂ), radius k)) :=
      hGc.comp_continuous (continuous_const.prodMk (Complex.continuous_ofReal.prodMk
        continuous_const)) fun t => ⟨hs0, ofReal_mem_Hbar_ug t, radius_pos k⟩
    exact IsLocallyFiniteMeasure.withDensity_ofReal
      (continuous_const.mul ((continuous_const.mul hc).rexp))
  -- uniform Cauchy for every test function, then time-continuous limits
  have hconv : ∀ f : ℝ → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ Ioo (u : ℝ) v →
      ∃ L : ℝ → ℝ, ContinuousOn L (Icc (q : ℝ) T) ∧ ∀ s ∈ Icc (q : ℝ) T,
        Tendsto (fun k => ∫ x, awTest (realRevMap V (T - s)) u v f x
          ∂bdryApprox γ (h0f κ s B X ω) k) atTop (𝓝 (L s)) := by
    intro f hf hfc hfs
    have hUf : UniformCauchySeqOn (fun k s => awInt κ T B X ω u v f s k) atTop
        (Icc (q : ℝ) T) :=
      ucs_of_fam (F := fun s => realRevMap V (T - s))
        (A := fun s k => bdryApprox γ (h0f κ s B X ω) k) hΦ hfin
        (fun f hf hfc hfs k => hAC huv hv f hf hfc hfs k)
        (fun i a b c d h1 h2 h3 h4 h5 => hfam i a b c d h1 h2 h3 h4 h5 hv) hf hfc hfs
    have hlim : ∀ s ∈ Icc (q : ℝ) T, Tendsto (fun k => awInt κ T B X ω u v f s k) atTop
        (𝓝 (limUnder atTop fun k => awInt κ T B X ω u v f s k)) := fun s hs =>
      (hUf.cauchySeq hs).tendsto_limUnder
    exact ⟨fun s => limUnder atTop fun k => awInt κ T B X ω u v f s k,
      (hUf.tendstoUniformlyOn_of_tendsto hlim).continuousOn
        (Frequently.of_forall fun k => hAC huv hv f hf hfc hfs k), hlim⟩
  have hνT := isVagueLimitR_qBoundaryMeasure hGl.2
  have := hνT.1
  exact det_anchor_ext (q := q) (T := T) hq hqT huv
    (A := fun s => bdryApprox γ (h0f κ s B X ω)) (ν := fun r => qBoundaryMeasure γ (h0f κ r B X ω))
    (νT := qBoundaryMeasure γ (h0f κ T B X ω)) measure_Ioo_lt_top hν.1
    (F := fun s => realRevMap V (T - s)) hΦ
    (fun r _ hr0 => isVagueLimitR_qBoundaryMeasure (hGl.1 r hr0))
    (fun r hr hr0 a b ha hab hb => hw r hr0 hr.2 a b hab
      ((hb.trans_lt hv).trans_le (hzmle r hr)))
    hconv

end RegUnif
end QuantumZipper
