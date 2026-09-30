import QuantumZipper.Proofs.Zipper.Cor15RezipRegGood
import QuantumZipper.Proofs.Zipper.Cor15RezipFin
import QuantumZipper.Proofs.Zipper.E1TransferRep

/-!
# COR15-TDENS (2): good drivers for a general measure; measurability of the `RegShift` event

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Corollary 1.5 (pp. 17–18).

* `ae_rezip_good_gen`: `ae_rezip_good` (`Cor15RezipRegGood`) with the folded circle replaced by any
  finite measure `σ` carried by `ℍ` with `∫ Im^{-1/4} dσ < ∞`, and the Hölder radius
  `‖w₀‖ + r₀` replaced by an arbitrary `R₀` (same proof: Rohde–Schramm Hölder bound
  `RS.ae_revMap_holder`, the hull is the SLE trace, and the a.s. polynomial mass of hull
  neighbourhoods `ae_measure_infDist_le_pow`, all generic in `σ`);
* `lintegral_im_rpow_tdens_ne_top`: the integrability input for `σ = tdens a`;
* `measurableSet_regShift_raw`: `{a | RegShift (y a) (μ.map (f a))}` is measurable when the raw
  dyadic folded-circle values of `y` are jointly measurable (as `measurableSet_regShift_param`,
  `Cor15LastPair`, without the coordinate form);
* `measurable_raw_finY`: joint measurability of the raw dyadic values of the unzipped field
  in `((path, field), z)`.

**Own elementary arguments** (bookkeeping around the cited results).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace Cor15Group

open CharFun B2

section Good

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}

/-- **Almost every driver is good**, for a general finite measure `σ` and radius `R₀`. -/
theorem ae_rezip_good_gen (hB : IsBrownianReal B P) (hind : IndepFun (pathOf B) X P) {κ : ℝ}
    (hκ : 0 < κ) (hκ4 : κ < 4) {t : ℝ} (ht : 0 < t) {σ : Measure ℂ} [IsFiniteMeasure σ]
    (hσH : ∀ᵐ z ∂σ, z ∈ H) (hσI : ∫⁻ z, ENNReal.ofReal (z.im ^ (-(1 / 4 : ℝ))) ∂σ ≠ ⊤)
    (R₀ : ℝ) :
    ∃ β : ℝ, 0 < β ∧ ∀ᵐ ω ∂P,
      Continuous (vrev (drive κ B ω) t) ∧ vrev (drive κ B ω) t 0 = 0 ∧
      H \ revMap (vrev (drive κ B ω) t) t '' H ⊆ sleTrace κ B ω '' Ici 0 ∧
      σ (H \ revMap (vrev (drive κ B ω) t) t '' H) = 0 ∧
      (∃ c : ℝ, 0 ≤ c ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        σ {z | infDist z (sleTrace κ B ω '' Ici 0) ≤ ε} ≤
          ENNReal.ofReal (c * ε ^ (1 / 8 : ℝ))) ∧
      ∃ M : ℝ, (∀ r ∈ Icc (0 : ℝ) t, |vrev (drive κ B ω) t r| ≤ M) ∧
        ∃ C : ℝ, 0 < C ∧ ∀ z ∈ H, ∀ w ∈ H, ‖z‖ ≤ R₀ + (12 * M + 8 * Real.sqrt t) →
          ‖w‖ ≤ R₀ + (12 * M + 8 * Real.sqrt t) →
          ‖revMap (vrev (drive κ B ω) t) t z - revMap (vrev (drive κ B ω) t) t w‖ ≤
            C * ‖z - w‖ ^ β := by
  obtain ⟨B', hB', -, -, -, hEq⟩ := UnzipFull.exists_unzip_driver κ hB hind ht.le
  obtain ⟨β, hβ, hHol⟩ := RS.ae_revMap_holder hB' hκ hκ4 ht
  refine ⟨β, hβ, ?_⟩
  filter_upwards [hB.cont, hB.eval_zero_ae_eq_zero, hEq, hHol,
    RS.ae_fwdHull_eq_sleTrace_image_of_le_four hB hκ hκ4.le,
    ae_measure_infDist_le_pow hB hκ hκ4 hσH hσI] with ω hc h0 hEqω hHolω hHull hmass
  have hWc : Continuous (drive κ B ω) := drive_continuous hc
  have hW0 : drive κ B ω 0 = 0 := drive_zero h0
  have hVc : Continuous (vrev (drive κ B ω) t) := continuous_vrev hWc t
  have hV0 : vrev (drive κ B ω) t 0 = 0 := by simp [vrev, ht.le]
  have hS : H \ revMap (vrev (drive κ B ω) t) t '' H ⊆ sleTrace κ B ω '' Ici 0 := by
    change revHull (vrev (drive κ B ω) t) t ⊆ _
    rw [rezip_revHull_vrev_eq_fwdHull hWc hW0 ht, hHull t ht.le]
    exact image_mono fun x hx => mem_Ici.2 (le_of_lt hx.1)
  obtain ⟨c₀, hc₀⟩ := hmass
  set c := max c₀ 0 with hcdef
  have hc : ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      σ {z | infDist z (sleTrace κ B ω '' Ici 0) ≤ ε} ≤
        ENNReal.ofReal (c * ε ^ (1 / 8 : ℝ)) := fun ε hε hε1 =>
    (hc₀ ε hε hε1).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)))
  have hK : σ (H \ revMap (vrev (drive κ B ω) t) t '' H) = 0 := by
    have hle : ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        σ (H \ revMap (vrev (drive κ B ω) t) t '' H) ≤
          ENNReal.ofReal (c * ε ^ (1 / 8 : ℝ)) := by
      intro ε hε hε1
      refine (measure_mono fun z hz => ?_).trans (hc ε hε hε1)
      show infDist z (sleTrace κ B ω '' Ici 0) ≤ ε
      rw [infDist_zero_of_mem (hS hz)]
      exact hε.le
    have hlim : Tendsto (fun ε : ℝ => ENNReal.ofReal (c * ε ^ (1 / 8 : ℝ))) (𝓝[>] 0)
        (𝓝 (ENNReal.ofReal (c * (0 : ℝ) ^ (1 / 8 : ℝ)))) :=
      (ENNReal.continuous_ofReal.tendsto _).comp
        (((continuous_const.mul (Real.continuous_rpow_const (by norm_num))).tendsto 0).mono_left
          nhdsWithin_le_nhds)
    rw [Real.zero_rpow (by norm_num), mul_zero, ENNReal.ofReal_zero] at hlim
    refine le_antisymm (ge_of_tendsto hlim ?_) bot_le
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
    exact hle ε hε.1 hε.2.le
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := t)).exists_bound_of_continuousOn
    hVc.continuousOn
  obtain ⟨C₀, hC₀⟩ := hHolω (R₀ + (12 * M + 8 * Real.sqrt t))
  refine ⟨hVc, hV0, hS, hK, ⟨c, le_max_right _ _, hc⟩, M,
    fun r hr => by simpa [Real.norm_eq_abs] using hM r hr, max C₀ 1,
    lt_max_of_lt_right one_pos, ?_⟩
  intro z hz w hw hzρ hwρ
  rw [← fwdMapInv_eq_revMap_vrev hWc hW0 ht.le hz, ← fwdMapInv_eq_revMap_vrev hWc hW0 ht.le hw,
    hEqω hz, hEqω hw]
  exact (hC₀ z hz w hw hzρ hwρ).trans
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))

end Good

/-- `∫ Im^{-1/4} d(tdens a) < ∞`: `Im > δ` on the support. -/
theorem lintegral_im_rpow_tdens_ne_top {a : ℂ → ℝ} {K : Set ℂ} {Md δ : ℝ} (hd : Dens a K Md δ) :
    ∫⁻ z, ENNReal.ofReal (z.im ^ (-(1 / 4 : ℝ))) ∂tdens a ≠ ⊤ := by
  have : IsFiniteMeasure (tdens a) := hd.admissible.1
  have hKae : ∀ᵐ z ∂tdens a, z ∈ K := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hd.tdens_compl] with z hz
    simpa using hz
  refine ne_top_of_le_ne_top (b := ∫⁻ _, ENNReal.ofReal (δ ^ (-(1 / 4 : ℝ))) ∂tdens a) ?_
    (lintegral_mono_ae ?_)
  · rw [lintegral_const]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
  · filter_upwards [hKae] with z hz
    have h1 : δ < z.im := hd.sub hz
    exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_nonpos hd.delta h1.le (by norm_num))

/-- **Measurability of the `RegShift` event** for a family with jointly measurable raw dyadic
values. -/
theorem measurableSet_regShift_raw {α : Type*} [MeasurableSpace α] {y : α → FieldSample}
    (hy : ∀ n k : ℕ, Measurable fun q : α × ℂ =>
      y q.1 (foldedCircle (dyadicRoundC n q.2) (radius k)))
    {f : α → ℂ → ℂ} (hf : Measurable fun p : α × ℂ => f p.1 p.2)
    (μ : Measure ℂ) [SFinite μ] :
    MeasurableSet {a | E1.RegShift (y a) (μ.map (f a))} := by
  have hfa : ∀ a, Measurable (f a) := fun a => hf.comp (measurable_const.prodMk measurable_id)
  have hq : Measurable fun p : α × ℂ => ((p.1, f p.1 p.2) : α × ℂ) := measurable_fst.prodMk hf
  have hya : ∀ (a : α) (n k : ℕ), Measurable fun z : ℂ =>
      y a (foldedCircle (dyadicRoundC n z) (radius k)) := fun a n k =>
    (hy n k).comp (f := fun z : ℂ => ((a, z) : α × ℂ)) (measurable_const.prodMk measurable_id)
  set T : Set (α × ℂ) := {p | ∀ k : ℕ, ∃ l, Tendsto (fun n =>
    y p.1 (foldedCircle (dyadicRoundC n (f p.1 p.2)) (radius k))) atTop (𝓝 l)} with hTdef
  have hT : MeasurableSet T := by
    have e : T = ⋂ k : ℕ, {p : α × ℂ | ∃ l, Tendsto (fun n =>
        y p.1 (foldedCircle (dyadicRoundC n (f p.1 p.2)) (radius k))) atTop (𝓝 l)} := by
      ext p; simp [hTdef]
    rw [e]
    exact MeasurableSet.iInter fun k => measurableSet_exists_tendsto fun n =>
      (hy n k).comp hq
  have hJ : ∀ k, Measurable fun p : α × ℂ => avgReg (y p.1) k (f p.1 p.2) := fun k =>
    (StronglyMeasurable.limUnder fun n => ((hy n k).comp hq).stronglyMeasurable).measurable
  have hA : ∀ a k, Measurable fun z => avgReg (y a) k z := fun a k =>
    (StronglyMeasurable.limUnder fun n => (hya a n k).stronglyMeasurable).measurable
  have e : {a | E1.RegShift (y a) (μ.map (f a))} =
      ({a | μ (Prod.mk a ⁻¹' Tᶜ) = 0} ∩
        ⋂ k : ℕ, {a | ∫⁻ w, ‖avgReg (y a) k (f a w)‖ₑ ∂μ < ⊤}) ∩
      {a | ∃ L, Tendsto (fun k => ∫ w, avgReg (y a) k (f a w) ∂μ) atTop (𝓝 L)} := by
    ext a
    have hS : MeasurableSet {z : ℂ | ∀ k : ℕ, ∃ l,
        Tendsto (fun n => y a (foldedCircle (dyadicRoundC n z) (radius k))) atTop (𝓝 l)} := by
      have e2 : {z : ℂ | ∀ k : ℕ, ∃ l,
          Tendsto (fun n => y a (foldedCircle (dyadicRoundC n z) (radius k))) atTop (𝓝 l)} =
          ⋂ k : ℕ, {z : ℂ | ∃ l,
            Tendsto (fun n => y a (foldedCircle (dyadicRoundC n z) (radius k))) atTop (𝓝 l)} := by
        ext z; simp
      rw [e2]
      exact MeasurableSet.iInter fun k => measurableSet_exists_tendsto fun n => hya a n k
    have i1 : (∀ᵐ z ∂(μ.map (f a)), ∀ k : ℕ, ∃ l,
        Tendsto (fun n => y a (foldedCircle (dyadicRoundC n z) (radius k))) atTop (𝓝 l)) ↔
        μ (Prod.mk a ⁻¹' Tᶜ) = 0 := by
      rw [ae_map_iff (hfa a).aemeasurable hS, ae_iff]
      rfl
    have i2 : ∀ k : ℕ, Integrable (fun z => avgReg (y a) k z) (μ.map (f a)) ↔
        ∫⁻ w, ‖avgReg (y a) k (f a w)‖ₑ ∂μ < ⊤ := by
      intro k
      refine ⟨fun h => ?_, fun h => ⟨(hA a k).aestronglyMeasurable, ?_⟩⟩
      · have h' := h.2
        unfold HasFiniteIntegral at h'
        rwa [lintegral_map (hA a k).enorm (hfa a)] at h'
      · unfold HasFiniteIntegral
        rwa [lintegral_map (hA a k).enorm (hfa a)]
    have i3 : ∀ k : ℕ, ∫ z, avgReg (y a) k z ∂(μ.map (f a)) = ∫ w, avgReg (y a) k (f a w) ∂μ :=
      fun k => integral_map (hfa a).aemeasurable (hA a k).aestronglyMeasurable
    show (_ ∧ _ ∧ _) ↔ _
    rw [i1, forall_congr' i2]
    simp only [i3, mem_inter_iff, mem_iInter, Set.mem_ofPred_eq]
    exact and_assoc.symm
  rw [e]
  refine (MeasurableSet.inter ?_ (MeasurableSet.iInter fun k => ?_)).inter ?_
  · exact measurableSet_eq_fun (measurable_measure_prodMk_left hT.compl) measurable_const
  · exact measurableSet_lt ((hJ k).enorm.lintegral_prod_right') measurable_const
  · exact measurableSet_exists_tendsto fun k =>
      (hJ k).stronglyMeasurable.integral_prod_right'.measurable

theorem measurable_dyadicRoundC_td (n : ℕ) : Measurable (dyadicRoundC n) := by
  have hR : Measurable (dyadicRound n) := by
    unfold dyadicRound
    exact ((measurable_from_top : Measurable (Int.cast : ℤ → ℝ)).div_const ((2 : ℝ) ^ n)).comp
      (Measurable.floor (measurable_id.const_mul ((2 : ℝ) ^ n)))
  have hrw : dyadicRoundC n
      = fun z : ℂ => (dyadicRound n z.re : ℂ) + (dyadicRound n z.im : ℂ) * Complex.I := by
    funext z
    apply Complex.ext <;> simp [dyadicRoundC]
  rw [hrw]
  exact (Complex.continuous_ofReal.measurable.comp (hR.comp Complex.measurable_re)).add
    ((Complex.continuous_ofReal.measurable.comp (hR.comp Complex.measurable_im)).mul_const
      Complex.I)

/-- A function of `(b, dyadicRoundC n z)` measurable in `b` for each `d` is jointly measurable. -/
theorem measurable_comp_dyadicRoundC {β : Type*} [MeasurableSpace β] {Φ : β → ℂ → ℝ}
    (hΦ : ∀ d, Measurable fun b => Φ b d) (n : ℕ) :
    Measurable fun q : β × ℂ => Φ q.1 (dyadicRoundC n q.2) := by
  have hc : (Set.range (dyadicRoundC n)).Countable := by
    refine (Set.countable_range fun p : ℤ × ℤ => CircleCont.lpt n p.1 p.2).mono ?_
    rintro _ ⟨z, rfl⟩
    exact ⟨(⌊(2 : ℝ) ^ n * z.re⌋, ⌊(2 : ℝ) ^ n * z.im⌋), (CircleCont.dyadicRoundC_eq_lpt n z).symm⟩
  have : Countable (Set.range (dyadicRoundC n)) := hc.to_subtype
  have hG : Measurable fun q : β × Set.range (dyadicRoundC n) => Φ q.1 (q.2 : ℂ) :=
    measurable_from_prod_countable_left fun d => hΦ d
  have hm : Measurable fun q : β × ℂ =>
      ((q.1, ⟨dyadicRoundC n q.2, Set.mem_range_self _⟩) : β × Set.range (dyadicRoundC n)) :=
    measurable_fst.prodMk ((measurable_dyadicRoundC_td n).comp measurable_snd).subtype_mk
  exact hG.comp hm

/-- Raw dyadic folded-circle values of the unzipped field of the reversed path, jointly in
`((path, field), z)`. -/
theorem measurable_raw_finY (κ : ℝ) {t : ℝ} (ht : 0 < t) (Q : ℝ) (n k : ℕ) :
    Measurable fun q : (C(Icc (0 : ℝ) t, ℝ) × FieldSample) × ℂ =>
      coordChange (ofFun (h0rev κ) + q.1.2) (revMap (Wof κ t ht.le (finRevPath ht.le q.1.1)) t) Q
        (foldedCircle (dyadicRoundC n q.2) (radius k)) := by
  refine measurable_comp_dyadicRoundC (β := C(Icc (0 : ℝ) t, ℝ) × FieldSample)
    (Φ := fun p d => coordChange (ofFun (h0rev κ) + p.2)
      (revMap (Wof κ t ht.le (finRevPath ht.le p.1)) t) Q (foldedCircle d (radius k))) (fun d => ?_) n
  have h1 := CoordReg.measurable_coordChange_fc κ ht.le (h0rev κ) Q d (radius_pos k)
  exact h1.comp (f := fun p : C(Icc (0 : ℝ) t, ℝ) × FieldSample => (finRevPath ht.le p.1, p.2))
    (((measurable_finRevPath ht.le).comp measurable_fst).prodMk measurable_snd)

end Cor15Group
end QuantumZipper
