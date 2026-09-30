import QuantumZipper.Proofs.Zipper.UnifSWRat
import QuantumZipper.Proofs.Zipper.UnifUGTip
import QuantumZipper.Proofs.LQG.BoundaryExistence
import QuantumZipper.Proofs.LQG.RegularClosure

/-!
# UNIF-SW (2): AC-cont (`AnchorApproxContStmt`) holds

Task UNIF-SW (decision D26). At a fixed dyadic scale `k`, the transported test integral
`awInt s k = ∫ (f ∘ F_s⁻¹) d(bdryApprox γ h⁰_s k)` is continuous in `s ∈ [q,T]`.

* `continuousOn_awTest` (deterministic): if `F_s` agrees on `[u,v]` with an order isomorphism for
  every `s ∈ S` and `s ↦ F_s y` is continuous on `S` for every `y ∈ [u,v]`, then for every `x`,
  `s ↦ awTest (F s) u v f x` is continuous on `S` (`f` continuous, `tsupport f ⊆ (u,v)`).
  Own elementary argument (continuity of the inverse of a monotone family, pointwise in `x`).
* **`anchorApproxContStmt_holds`**: AC-cont, unconditionally. Proof: on the event of
  `ae_forall_isRegularWith_joint` (JOINTMOD: a witness `G` jointly continuous in
  `(s, z, r)` with `avgReg h⁰_s k z = G (s,(z, 2^{-k}))` for all `s ∈ [0,T]`), the integrand is
  continuous in `s` for each `x`, vanishes off a fixed compact interval and is bounded there, so
  dominated convergence (`continuousOn_of_dominated`) applies. The window `(u,v)` is live at time
  `q`, hence at all `s ∈ [q,T]`, and `s ↦ F_s y` is the (continuous) real reverse-flow solution.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace RegUnif

open B2 B5 E1 E1.M4

/-- **Continuity of the transported test function in the parameter** (own elementary argument). -/
theorem continuousOn_awTest {S : Set ℝ} {F : ℝ → ℝ → ℝ} {u v : ℝ}
    (hΦ : ∀ s ∈ S, ∃ Φ : ℝ ≃o ℝ, ∀ y ∈ Icc u v, Φ y = F s y)
    (hc : ∀ y ∈ Icc u v, ContinuousOn (fun s => F s y) S)
    {f : ℝ → ℝ} (hf : Continuous f) (hfs : tsupport f ⊆ Ioo u v) (x : ℝ) :
    ContinuousOn (fun s => awTest (F s) u v f x) S := by
  intro s0 hs0
  obtain ⟨Φ0, hΦ0⟩ := hΦ s0 hs0
  have hval : ∀ s ∈ S, ∃ Φ : ℝ ≃o ℝ, (∀ y ∈ Icc u v, Φ y = F s y) ∧
      awTest (F s) u v f x = f (Φ.symm x) := fun s hs => by
    obtain ⟨Φ, hΦs⟩ := hΦ s hs
    exact ⟨Φ, hΦs, by rw [awTest_eq hΦs hfs]; rfl⟩
  have hg0 : awTest (F s0) u v f x = f (Φ0.symm x) := by rw [awTest_eq hΦ0 hfs]; rfl
  have hzero : ∀ y, y ∉ Ioo u v → f y = 0 := fun y hy =>
    image_eq_zero_of_notMem_tsupport fun h => hy (hfs h)
  have hev : ∀ a ∈ Icc u v, ∀ c : ℝ → Prop, (∀ᶠ z in 𝓝 (F s0 a), c z) →
      ∀ᶠ s in 𝓝[S] s0, c (F s a) := fun a ha c h => (hc a ha s0 hs0).eventually h
  rw [ContinuousWithinAt, Metric.tendsto_nhds]
  intro ε hε
  by_cases huv : ¬ u < v
  · have hf0 : ∀ y, f y = 0 := fun y => hzero y fun h => huv (h.1.trans h.2)
    filter_upwards [self_mem_nhdsWithin] with s hs
    obtain ⟨Φ, -, hgs⟩ := hval s hs
    rw [hgs, hg0, hf0, hf0]
    simpa using hε
  push Not at huv
  set y0 := Φ0.symm x with hy0
  have hx0 : Φ0 y0 = x := by simp [y0]
  rcases lt_or_ge u y0 with huy | hyu
  · rcases lt_or_ge y0 v with hyv | hvy
    · -- interior case
      obtain ⟨δ, hδ, hfδ⟩ := Metric.continuous_iff.1 hf y0 ε hε
      set a := max u (y0 - δ / 2)
      set b := min v (y0 + δ / 2)
      have ha : a ∈ Icc u v := ⟨le_max_left _ _, max_le (huy.trans hyv).le (by linarith)⟩
      have hb : b ∈ Icc u v := ⟨le_min (huy.trans hyv).le (by linarith), min_le_left _ _⟩
      have hay : a < y0 := max_lt huy (by linarith)
      have hyb : y0 < b := lt_min hyv (by linarith)
      have h1 : F s0 a < x := by rw [← hΦ0 a ha, ← hx0]; exact Φ0.strictMono hay
      have h2 : x < F s0 b := by rw [← hΦ0 b hb, ← hx0]; exact Φ0.strictMono hyb
      filter_upwards [self_mem_nhdsWithin, hev a ha (· < x) (eventually_lt_nhds h1),
        hev b hb (x < ·) (eventually_gt_nhds h2)] with s hs hsa hsb
      obtain ⟨Φ, hΦs, hgs⟩ := hval s hs
      rw [hgs, hg0]
      have h3 : a < Φ.symm x := by rw [Φ.lt_symm_apply, hΦs a ha]; exact hsa
      have h4 : Φ.symm x < b := by rw [Φ.symm_apply_lt, hΦs b hb]; exact hsb
      apply hfδ
      rw [Real.dist_eq, abs_lt]
      constructor
      · linarith [le_max_right u (y0 - δ / 2)]
      · linarith [min_le_right v (y0 + δ / 2)]
    · -- right exterior case: `y0 ≥ v`
      have hv : v ∉ tsupport f := fun h => (hfs h).2.false
      obtain ⟨ε', hε', hball⟩ := Metric.isOpen_iff.1 (isClosed_tsupport f).isOpen_compl v hv
      set a := max u (v - ε' / 2)
      have ha : a ∈ Icc u v := ⟨le_max_left _ _, max_le huv.le (by linarith)⟩
      have hav : a < v := max_lt huv (by linarith)
      have h1 : x < F s0 a → False := fun h => by
        rw [← hΦ0 a ha, ← hx0] at h; exact absurd (Φ0.strictMono.lt_iff_lt.1 h) (by linarith)
      have h1' : F s0 a < x := lt_of_not_ge fun h => by
        rcases h.lt_or_eq with h | h
        · exact h1 h
        · rw [← hΦ0 a ha, ← hx0] at h
          exact absurd (Φ0.injective h) (by linarith)
      filter_upwards [self_mem_nhdsWithin, hev a ha (· < x) (eventually_lt_nhds h1')]
        with s hs hsa
      obtain ⟨Φ, hΦs, hgs⟩ := hval s hs
      rw [hgs, hg0, hzero y0 fun h => by linarith [h.2]]
      have h3 : a < Φ.symm x := by rw [Φ.lt_symm_apply, hΦs a ha]; exact hsa
      have hz : f (Φ.symm x) = 0 := image_eq_zero_of_notMem_tsupport fun h => by
        have hm := hfs h
        refine hball ?_ h
        rw [Metric.mem_ball, Real.dist_eq, abs_lt]
        constructor <;> linarith [le_max_right u (v - ε' / 2), hm.2]
      rw [hz]
      simpa using hε
  · -- left exterior case: `y0 ≤ u`
    have hu : u ∉ tsupport f := fun h => (hfs h).1.false
    obtain ⟨ε', hε', hball⟩ := Metric.isOpen_iff.1 (isClosed_tsupport f).isOpen_compl u hu
    · set b := min v (u + ε' / 2)
      have hb : b ∈ Icc u v := ⟨le_min huv.le (by linarith), min_le_left _ _⟩
      have hub : u < b := lt_min huv (by linarith)
      have h2 : x < F s0 b := by
        rw [← hΦ0 b hb, ← hx0]; exact Φ0.strictMono (hyu.trans_lt hub)
      filter_upwards [self_mem_nhdsWithin, hev b hb (x < ·) (eventually_gt_nhds h2)]
        with s hs hsb
      obtain ⟨Φ, hΦs, hgs⟩ := hval s hs
      rw [hgs, hg0, hzero y0 fun h => by linarith [h.1]]
      have h4 : Φ.symm x < b := by rw [Φ.symm_apply_lt, hΦs b hb]; exact hsb
      have hz : f (Φ.symm x) = 0 := image_eq_zero_of_notMem_tsupport fun h => by
        have hm := hfs h
        refine hball ?_ h
        rw [Metric.mem_ball, Real.dist_eq, abs_lt]
        constructor <;> linarith [min_le_right v (u + ε' / 2), hm.1]
      rw [hz]
      simpa using hε

/-- `awTest` vanishes off the image window. -/
theorem awTest_eq_zero_of_not_mem {F : ℝ → ℝ} {u v : ℝ} {Φ : ℝ ≃o ℝ}
    (hΦ : ∀ y ∈ Icc u v, Φ y = F y) {f : ℝ → ℝ} {x : ℝ} (hx : x ∉ Ioo (F u) (F v)) :
    awTest F u v f x = 0 := by
  unfold awTest
  rw [dif_neg]
  rintro ⟨y, hy, rfl⟩
  apply hx
  rw [← hΦ y (Ioo_subset_Icc_self hy), ← hΦ u ⟨le_rfl, (hy.1.trans hy.2).le⟩,
    ← hΦ v ⟨(hy.1.trans hy.2).le, le_rfl⟩]
  exact ⟨Φ.strictMono hy.1, Φ.strictMono hy.2⟩

/-- `|awTest| ≤ C` when `|f| ≤ C`. -/
theorem abs_awTest_le {F : ℝ → ℝ} {u v : ℝ} {f : ℝ → ℝ} {C : ℝ} (hC : ∀ y, ‖f y‖ ≤ C) (x : ℝ) :
    ‖awTest F u v f x‖ ≤ C := by
  unfold awTest
  split_ifs
  · exact hC _
  · simpa using (norm_nonneg _).trans (hC 0)

theorem measurable_avgReg_ofReal_sw (x : FieldSample) (k : ℕ) :
    Measurable (fun t : ℝ => avgReg x k (t : ℂ)) :=
  (measurable_avgReg k).comp (measurable_const.prodMk Complex.continuous_ofReal.measurable)

variable {Ω : Type} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P] {κ T : ℝ} {B : ℝ≥0 → Ω → ℝ}
  {X : Ω → FieldSample}

/-- **AC-cont holds** (no hypotheses beyond the `Γ⁰` setup). -/
theorem anchorApproxContStmt_holds (hκ : 0 < κ) (hκ4 : κ < 4) (hT : 0 < T)
    (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P) :
    AnchorApproxContStmt κ T P B X := by
  intro q hq hqT u v
  filter_upwards [ae_forall_isRegularWith_joint (κ := κ) (γ := Real.sqrt κ) hB hX hind hT,
    ae_zeroMinus_Vr_facts RS.rohdeSchrammSimple hκ hκ4.le hT P B hB, hB.cont,
    ae_isSimpleCurveHull_revHull_Vr RS.rohdeSchrammSimple hκ hκ4.le hT P B hB]
    with ω hG hzm hcont hK hu huv hv f hf hfc hfs k
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
  have hS0 : ∀ s ∈ S, s ∈ Icc (0 : ℝ) T := fun s hs => ⟨hq.le.trans hs.1, hs.2⟩
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

end RegUnif
end QuantumZipper
