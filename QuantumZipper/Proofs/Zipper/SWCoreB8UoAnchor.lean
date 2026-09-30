import QuantumZipper.Proofs.Zipper.SWCoreB8UoCauchy
import QuantumZipper.Proofs.Zipper.UnifUOAnchor
import QuantumZipper.Proofs.Zipper.SWCoreB8Dil
import QuantumZipper.Proofs.Zipper.YBdryMerge2Tip

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-B8 (d), part 2: offset anchored windows (offset form of `UnifUOAnchor`)

Offset form of the D26 anchored-window step (`RegUnif.ae_anchor_ext`). The radii `2^{-k}` of the
dyadic chain are replaced by the radii `c 2^{-k}`, indexed by `j = (k, c)` along `goodFilter`
(`goodRad j = c 2^{-k}`, uniformly in `c ∈ [1,2]`):

* `awIntOff`: the transported test integral `∫ awTest(F_s) f dν_{c 2^{-k}}(h⁰_s)`;
* **`AnchorUnifFamOffStmt`** (the analytic input, a hypothesis here): for rational anchors
  `0 ≤ q < T`, rational live windows and the countable family `swFam`, `awIntOff` is Cauchy along
  `goodFilter` uniformly in the rational times `s ∈ [q,T]`. This is Sheffield–Wang
  arXiv:1605.06171 Thm 4.3 (with Thm 1.4 for the continuous radius), applied at the anchor field
  `h⁰_q` with the maps `F_s`, and with the dilation `z ↦ c z` as one more parameter of the map
  family (`SWCoreB8Dil`, `SWCoreB8Class`): the limit `∫ f ∘ F_s⁻¹ dν` does not depend on `c`,
  hence Cauchy along `goodFilter` (not only for each fixed `c`);
* `anchorApproxContOff`: at each fixed index `(k, c)`, `c > 0`, `awIntOff` is continuous in `s`
  (as `anchorApproxContExt`, with the regular witness read at radius `c 2^{-k}`);
* **`ae_anchor_off`**: a.s., for every rational anchor and live window and every `s ∈ [q,T]`, the
  offset approximations of `h⁰_s` merge with the dyadic ones (`bdryMergeDiff → 0` along
  `goodFilter`) for test functions supported in `F_s(u,v)`.

Unlike the dyadic chain, no identification of the limit is needed: Cauchy along `goodFilter`
compares the radius `c 2^{-k}` with `2^{-k}` directly. Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace RegUnif

open B2 B5 E1 E1.M4

variable {Ω : Type} [MeasurableSpace Ω]

/-- The offset transported test integral `∫ (f ∘ F_s⁻¹) dν_{c 2^{-k}}(h⁰_s)`, `j = (k, c)`. -/
def awIntOff (κ T : ℝ) (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) (ω : Ω) (u v : ℝ)
    (f : ℝ → ℝ) (s : ℝ) (j : ℕ × ℝ) : ℝ :=
  ∫ x, awTest (realRevMap (Vr κ T B ω) (T - s)) u v f x
    ∂bdryR (Real.sqrt κ) (h0f κ s B X ω) (goodRad j)

/-- **AC-fam-ext, offset form** (analytic input): `AnchorUnifFamExtStmt` with the dyadic index
`k` (`atTop`) replaced by the offset index `(k, c)` along `goodFilter`. -/
def AnchorUnifFamOffStmt (κ T : ℝ) (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) :
    Prop :=
  ∀ q : ℚ, (0 : ℝ) ≤ q → (q : ℝ) < T → ∀ u v : ℚ, ∀ i : ℕ, ∀ a b c d : ℚ, ∀ᵐ ω ∂P,
    (u : ℝ) < a → a < b → b < c → c < d → (d : ℝ) < v →
    (v : ℝ) < zeroMinus (Vr κ T B ω) (T - q) →
      OffCauchyOn goodFilter (fun j s => awIntOff κ T B X ω u v (swFam i a b c d) s j)
        (Icc (q : ℝ) T ∩ range ((↑) : ℚ → ℝ))

variable {P : Measure Ω} [IsProbabilityMeasure P] {κ T : ℝ} {B : ℝ≥0 → Ω → ℝ}
  {X : Ω → FieldSample}

/-- **AC-cont, offset form**: at each index `(k, c)` with `c > 0`, the offset transported test
integral is continuous in `s ∈ [q,T]` (proof of `anchorApproxContExt` at radius `c 2^{-k}`). -/
theorem anchorApproxContOff (hκ : 0 < κ) (hκ4 : κ < 4) (hT : 0 < T)
    (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P) :
    ∀ q : ℚ, (0 : ℝ) ≤ q → (q : ℝ) ≤ T → ∀ u v : ℚ, ∀ᵐ ω ∂P,
      (u : ℝ) < v → (v : ℝ) < zeroMinus (Vr κ T B ω) (T - q) →
      ∀ f : ℝ → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ Ioo (u : ℝ) v →
        ∀ j : ℕ × ℝ, 0 < j.2 →
          ContinuousOn (fun s => awIntOff κ T B X ω u v f s j) (Icc (q : ℝ) T) := by
  intro q hq hqT u v
  filter_upwards [ae_forall_isRegularWith_joint (κ := κ) (γ := Real.sqrt κ) hB hX hind hT,
    ae_zeroMinus_Vr_facts RS.rohdeSchrammSimple hκ hκ4.le hT P B hB, hB.cont,
    ae_isSimpleCurveHull_revHull_Vr RS.rohdeSchrammSimple hκ hκ4.le hT P B hB]
    with ω hG hzm hcont hK huv hv f hf hfc hfs j hj
  obtain ⟨G, hGc, hGr⟩ := hG
  obtain ⟨-, -, hanti, -, -, -⟩ := hzm
  set V := Vr κ T B ω with hVdef
  have hVc : Continuous V := continuous_vrev (drive_continuous hcont) T
  have hV0 : V 0 = 0 := vrev_zero hT.le
  set γ := Real.sqrt κ with hγ
  set S := Icc (q : ℝ) T with hS
  set r := goodRad j with hrdef
  have hr : 0 < r := mul_pos hj (radius_pos _)
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
  have hS0 : ∀ s ∈ S, s ∈ Icc (0 : ℝ) T := fun s hs => ⟨hq.trans hs.1, hs.2⟩
  have hGx : ∀ x : ℝ, ContinuousOn (fun s => G (s, ((x : ℂ), r))) S := fun x =>
    hGc.comp (continuousOn_id.prodMk continuousOn_const) fun s hs =>
      ⟨hS0 s hs, ofReal_mem_Hbar_ug x, hr⟩
  obtain ⟨CG, hCG⟩ := (isCompact_Icc.prod (isCompact_Icc (a := -M) (b := M))).exists_bound_of_continuousOn
    (f := fun p : ℝ × ℝ => G (p.1, ((p.2 : ℂ), r)))
    (hGc.comp ((continuous_fst.prodMk ((Complex.continuous_ofReal.comp continuous_snd).prodMk
      continuous_const)).continuousOn) fun p hp =>
        ⟨hS0 p.1 hp.1, ofReal_mem_Hbar_ug p.2, hr⟩)
  set dens : ℝ → ℝ → ℝ := fun s x =>
    r ^ (γ ^ 2 / 4) * Real.exp (γ / 2 * G (s, ((x : ℂ), r))) with hdens
  have hint : ∀ s ∈ S, awIntOff κ T B X ω u v f s j = ∫ x, awTest (F s) u v f x * dens s x := by
    intro s hs
    have hreg : IsRegularWith (h0f κ s B X ω) (fun p => G (s, p)) := by
      rw [h0f_eq_unzippedField]; exact hGr s (hS0 s hs)
    unfold awIntOff
    rw [SWCore.integral_bdryR_eq_dens γ hreg r hr]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [bdryDens, hdens, hreg.evalReg_fc_of_mem (ofReal_mem_Hbar_ug x) hr]
    rfl
  refine ContinuousOn.congr ?_ (fun s hs => hint s hs)
  set bnd : ℝ → ℝ := (Icc (-M) M).indicator fun _ =>
    Cf * (r ^ (γ ^ 2 / 4) * Real.exp (γ / 2 * CG)) with hbnd
  refine continuousOn_of_dominated (bound := bnd) ?_ ?_ ?_ ?_
  · intro s hs
    obtain ⟨Φ, hΦs⟩ := hΦ s hs
    rw [awTest_eq hΦs hfs]
    have hd : Continuous (dens s) := by
      rw [hdens]
      exact continuous_const.mul ((continuous_const.mul (hGc.comp_continuous
        (continuous_const.prodMk (Complex.continuous_ofReal.prodMk continuous_const))
        fun x => ⟨hS0 s hs, ofReal_mem_Hbar_ug x, hr⟩)).rexp)
    exact ((hf.comp Φ.symm.continuous).mul hd).aestronglyMeasurable
  · intro s hs
    refine Eventually.of_forall fun x => ?_
    by_cases hx : x ∈ Icc (-M) M
    · rw [hbnd, indicator_of_mem hx, norm_mul]
      have hd0 : 0 ≤ dens s x := mul_nonneg (Real.rpow_nonneg hr.le _) (Real.exp_pos _).le
      refine mul_le_mul (abs_awTest_le hCf x) ?_ (norm_nonneg _) ((norm_nonneg _).trans (hCf 0))
      rw [Real.norm_eq_abs, abs_of_nonneg hd0]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (Real.rpow_nonneg hr.le _)
      have h1 := hCG (s, x) ⟨hs, hx⟩
      rw [Real.norm_eq_abs, abs_le] at h1
      exact mul_le_mul_of_nonneg_left h1.2 (by positivity)
    · rw [hbnd, indicator_of_notMem hx, hsupp s hs x hx, zero_mul, norm_zero]
  · exact (integrableOn_const measure_Icc_lt_top.ne).integrable_indicator measurableSet_Icc
  · refine Eventually.of_forall fun x => ?_
    exact (continuousOn_awTest hΦ hFc hf hfs x).mul
      (continuousOn_const.mul ((continuousOn_const.mul (hGx x)).rexp))

theorem eventually_snd_pos_goodFilter : ∀ᶠ j in goodFilter, (0 : ℝ) < j.2 := by
  have h : ∀ᶠ c in 𝓟 (Icc (1 : ℝ) 2), (0 : ℝ) < c :=
    eventually_principal.2 fun c hc => by linarith [hc.1]
  exact (tendsto_snd (f := (atTop : Filter ℕ))).eventually h

/-- **Offset anchored windows (a.s.)**: from the offset input, for all rational `0 ≤ q < T` and
rational windows `u < v < 0₋(T − q)`, for every `s ∈ [q,T]` and every test function supported in
`F_s(u,v)`, the offset approximations of `h⁰_s` merge with the dyadic ones along `goodFilter`. -/
theorem ae_anchor_off (hκ : 0 < κ) (hκ4 : κ < 4) (hT : 0 < T)
    (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P)
    (hF : AnchorUnifFamOffStmt κ T P B X) :
    ∀ᵐ ω ∂P, ∀ q u v : ℚ, (0 : ℝ) ≤ q → (q : ℝ) < T → (u : ℝ) < v →
      (v : ℝ) < zeroMinus (Vr κ T B ω) (T - q) → ∀ s ∈ Icc (q : ℝ) T,
        ∀ g : ℝ → ℝ, Continuous g → HasCompactSupport g →
          tsupport g ⊆ Ioo (realRevMap (Vr κ T B ω) (T - s) u)
            (realRevMap (Vr κ T B ω) (T - s) v) →
          Tendsto (WedgeUnzip.bdryMergeDiff (Real.sqrt κ) (h0f κ s B X ω) g) goodFilter
            (𝓝 0) := by
  refine ae_all_iff.2 fun q => ae_all_iff.2 fun u => ae_all_iff.2 fun v => ?_
  by_cases hqq : (0 : ℝ) ≤ q ∧ (q : ℝ) < T
  swap
  · exact Eventually.of_forall fun ω h1 h2 => absurd ⟨h1, h2⟩ hqq
  obtain ⟨hq, hqT⟩ := hqq
  have hall : ∀ᵐ ω ∂P, ∀ i : ℕ, ∀ a b c d : ℚ,
      (u : ℝ) < a → a < b → b < c → c < d → (d : ℝ) < v →
      (v : ℝ) < zeroMinus (Vr κ T B ω) (T - q) →
        OffCauchyOn goodFilter (fun j s => awIntOff κ T B X ω u v (swFam i a b c d) s j)
          (Icc (q : ℝ) T ∩ range ((↑) : ℚ → ℝ)) :=
    ae_all_iff.2 fun i => ae_all_iff.2 fun a => ae_all_iff.2 fun b => ae_all_iff.2 fun c =>
      ae_all_iff.2 fun d => hF q hq hqT u v i a b c d
  filter_upwards [hall, anchorApproxContOff hκ hκ4 hT hB hX hind q hq hqT.le u v,
    ae_forall_isRegularWith_joint (κ := κ) (γ := Real.sqrt κ) hB hX hind hT,
    ae_zeroMinus_Vr_facts RS.rohdeSchrammSimple hκ hκ4.le hT P B hB, hB.cont,
    ae_isSimpleCurveHull_revHull_Vr RS.rohdeSchrammSimple hκ hκ4.le hT P B hB]
    with ω hfam hAC hG hzm hcont hK _ _ huv hv s hs g hg hgc hgs
  obtain ⟨G, -, hGr⟩ := hG
  obtain ⟨-, -, hanti, -, -, -⟩ := hzm
  have hVc : Continuous (Vr κ T B ω) := continuous_vrev (drive_continuous hcont) T
  have hV0 : Vr κ T B ω 0 = 0 := vrev_zero hT.le
  have hzmle : ∀ r ∈ Icc (q : ℝ) T,
      zeroMinus (Vr κ T B ω) (T - q) ≤ zeroMinus (Vr κ T B ω) (T - r) := fun r hr =>
    hanti.antitoneOn ⟨by linarith [hr.2], by linarith [hr.1, hq]⟩
      ⟨by linarith, by linarith⟩ (by linarith [hr.1])
  have hlive : ∀ r ∈ Icc (q : ℝ) T, ∀ x ∈ Icc (u : ℝ) v, IsLive (Vr κ T B ω) (T - r) x :=
    fun r hr x hx =>
    (mem_liveNeg_of_lt_zeroMinus hVc hV0 hT hK (by linarith [hr.2]) (by linarith [hr.1, hq])
      ((hx.2.trans_lt hv).trans_le (hzmle r hr))).2
  have hΦ : ∀ s ∈ Icc (q : ℝ) T, ∃ Φ : ℝ ≃o ℝ, ∀ y ∈ Icc (u : ℝ) v,
      Φ y = realRevMap (Vr κ T B ω) (T - s) y := fun s hs =>
    exists_orderIso_eq_realRevMap hVc (by linarith [hs.2]) huv (hlive s hs)
  have hreg : ∀ s ∈ Icc (q : ℝ) T, IsRegularWith (h0f κ s B X ω) (fun p => G (s, p)) :=
    fun s hs => by
      rw [h0f_eq_unzippedField]; exact hGr s ⟨hq.trans hs.1, hs.2⟩
  have hfin : ∀ᶠ j in goodFilter, ∀ s ∈ Icc (q : ℝ) T,
      IsLocallyFiniteMeasure (bdryR (Real.sqrt κ) (h0f κ s B X ω) (goodRad j)) := by
    filter_upwards [eventually_snd_pos_goodFilter] with j hj s hs
    have hr : 0 < goodRad j := mul_pos hj (radius_pos _)
    have : IsFiniteMeasureOnCompacts (bdryR (Real.sqrt κ) (h0f κ s B X ω) (goodRad j)) :=
      ⟨fun K hK => GoodSample.bdryR_lt_top _ (hreg s hs) hr hK⟩
    infer_instance
  have hbd : ∀ f : ℝ → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ Ioo (u : ℝ) v →
      ∀ᶠ j in goodFilter, ∃ C : ℝ, ∀ s ∈ Icc (q : ℝ) T,
        |∫ x, awTest (realRevMap (Vr κ T B ω) (T - s)) u v f x
          ∂bdryR (Real.sqrt κ) (h0f κ s B X ω) (goodRad j)| ≤ C := by
    intro f hf hfc hfs
    filter_upwards [eventually_snd_pos_goodFilter] with j hj
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (hAC huv hv f hf hfc hfs j hj)
    exact ⟨C, fun s hs => by rw [← Real.norm_eq_abs]; exact hC s hs⟩
  obtain ⟨Φ, hΦs⟩ := hΦ s hs
  set f := g ∘ Φ with hfdef
  have hfc : Continuous f := hg.comp Φ.continuous
  have hfcs : HasCompactSupport f := hasCompactSupport_comp_orderIso hgc Φ
  have hpre : Φ ⁻¹' Ioo (realRevMap (Vr κ T B ω) (T - s) u)
      (realRevMap (Vr κ T B ω) (T - s) v) = Ioo (u : ℝ) v := by
    rw [← hΦs u ⟨le_rfl, huv.le⟩, ← hΦs v ⟨huv.le, le_rfl⟩, OrderIso.preimage_Ioo,
      OrderIso.symm_apply_apply, OrderIso.symm_apply_apply]
  have hfs : tsupport f ⊆ Ioo (u : ℝ) v :=
    (tsupport_comp_subset_preimage' Φ.continuous).trans (by rw [← hpre]; exact preimage_mono hgs)
  have hg' : awTest (realRevMap (Vr κ T B ω) (T - s)) u v f = g := by
    rw [awTest_eq hΦs hfs]
    funext x
    simp [f]
  have hUf : OffCauchyOn goodFilter (fun j s => awIntOff κ T B X ω u v f s j)
      (Icc (q : ℝ) T) :=
    offCauchy_of_fam (F := fun s => realRevMap (Vr κ T B ω) (T - s))
      (A := fun s j => bdryR (Real.sqrt κ) (h0f κ s B X ω) (goodRad j)) hΦ hfin hbd
      (fun i a b c d h1 h2 h3 h4 h5 => offCauchy_of_rat
        (eventually_snd_pos_goodFilter.mono fun j hj => hAC huv hv _
          (continuous_swFam i a b c d)
          (hasCompactSupport_of_tsupport_Icc
            (tsupport_swFam_subset (by exact_mod_cast h2) (by exact_mod_cast h4)))
          ((tsupport_swFam_subset (by exact_mod_cast h2) (by exact_mod_cast h4)).trans
            fun x hx => ⟨h1.trans_le hx.1, hx.2.trans_lt h5⟩) j hj)
        (hfam i a b c d h1 h2 h3 h4 h5 hv)) hfc hfcs hfs
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hmap : Tendsto (fun j : ℕ × ℝ => (j, (j.1, (1 : ℝ)))) goodFilter
      (goodFilter ×ˢ goodFilter) :=
    tendsto_id.prodMk WedgeUnzip.tendsto_fst_one_goodFilter
  filter_upwards [hmap.eventually (hUf ε hε)] with j hj
  have h := hj s hs
  have hr1 : goodRad (j.1, (1 : ℝ)) = radius j.1 := by simp [goodRad]
  have e1 : awIntOff κ T B X ω u v f s j =
      ∫ t, g t ∂bdryR (Real.sqrt κ) (h0f κ s B X ω) (goodRad j) := by
    unfold awIntOff
    exact congrArg (fun φ => ∫ t, φ t ∂bdryR (Real.sqrt κ) (h0f κ s B X ω) (goodRad j)) hg'
  have e2 : awIntOff κ T B X ω u v f s (j.1, 1) =
      ∫ t, g t ∂bdryR (Real.sqrt κ) (h0f κ s B X ω) (radius j.1) := by
    unfold awIntOff
    rw [hr1]
    exact congrArg (fun φ => ∫ t, φ t ∂bdryR (Real.sqrt κ) (h0f κ s B X ω) (radius j.1)) hg'
  rw [Real.dist_eq, sub_zero]
  simp only [WedgeUnzip.bdryMergeDiff]
  rw [← e1, ← e2]
  exact h

end RegUnif
end QuantumZipper
