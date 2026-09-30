import QuantumZipper.Proofs.Thm18.G1Z2MeasScale

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1Z2-MEAS, part 3: scale invariance of the rerooted canonical side data

For a field `x` which is regular, has an area limit on `ℍ` (finite near boundary points, infinite
in total), a side boundary limit along all radii `a 2^{-k}` (`G1Z2SideBdryLim`), and whose
translates are scale consistent at dilated test measures (the pairing clause of
`G1.ChoiceRegular`, at translated fields), the rerooted local canonical data of every `W` with
the regularized averages of `rescale x Q b` equal those of `x` (`g1z2_rerootData_rescale`).

Steps: the side boundary measure of `rescale x Q b` is `ν.map (· / b)` (the proof of
`GoodTransforms.hasBdryLimit_rescale`, on the side half-line), so the quantile point is divided by
`b` (`g1z2_sidePt_of_map`); `translate (rescale x Q b) (p / b)` and `rescale (translate x p) Q b`
have the same raw folded-circle values (witness computation, `IsRegularWith.rescale'`,
`IsRegularWith.translate'`); the canonical description of a rescaled field is unchanged
(`g1z2_canonical_rescale_apply`). Own elementary arguments.
-/

noncomputable section

open MeasureTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm

open D3Plus Factorization

/-- Side boundary limit of `x` along all radii `a 2^{-k}`, `a ∈ [1,2]` (the side-half-line
analogue of `HasBdryLimit`). -/
def G1Z2SideBdryLim (γ : ℝ) (left : Bool) (x : FieldSample) (ν : Measure ℝ) : Prop :=
  ν (g1SideHalf left)ᶜ = 0 ∧ (∀ K, IsCompact K → K ⊆ g1SideHalf left → ν K < ⊤) ∧
    ∀ f : ℝ → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ g1SideHalf left →
      Tendsto (fun i => ∫ t, f t ∂bdryR γ x (goodRad i)) goodFilter (𝓝 (∫ t, f t ∂ν))

/-- The regularity package of a pulled-back side field used for the scale invariance. -/
def G1Z2Good (γ : ℝ) (left : Bool) (x : FieldSample) : Prop :=
  IsRegularSample x ∧
  (∃ μ : Measure ℂ, HasAreaLimit γ x μ ∧
    (∀ p : ℝ, ∃ a : ℝ, 0 < a ∧ μ (Metric.ball (p : ℂ) a ∩ H) < 1) ∧ μ H = ⊤) ∧
  (∃ ν : Measure ℝ, G1Z2SideBdryLim γ left x ν) ∧
  ∀ p : ℝ, ∀ b : ℝ, 0 < b → ∀ c : ℝ, 0 < c → ∀ ρ : TestFun H, ∀ σ : ℂ → ℝ,
    (σ = ρ.1 ∨ σ = fun z => -ρ.1 z) →
    G1.ScaleConsistentAt (translate x (p : ℂ)) (Qc γ) b ((G1.tmeas σ).map fun z => (c : ℂ) * z)

theorem g1z2_mem_sideHalf_div {b : ℝ} (hb : 0 < b) (left : Bool) (u : ℝ) :
    u / b ∈ g1SideHalf left ↔ u ∈ g1SideHalf left := by
  cases left <;> simp [g1SideHalf, div_lt_iff₀ hb, lt_div_iff₀ hb]

theorem g1z2_tsupport_comp {f g : ℝ → ℝ} (hg : Continuous g) :
    tsupport (f ∘ g) ⊆ g ⁻¹' tsupport f :=
  closure_minimal (fun _ hu => subset_tsupport f hu) ((isClosed_tsupport f).preimage hg)

theorem g1z2_isOpen_sideHalf (left : Bool) : IsOpen (g1SideHalf left) := by
  cases left
  · exact isOpen_Ioi
  · exact isOpen_Iio

/-- The side boundary limit of the rescaled field, along the dyadic radii. -/
theorem g1z2_isVagueLimitOnR_rescale {γ : ℝ} (hγ : 0 < γ) {left : Bool} {x : FieldSample}
    {F : ℂ × ℝ → ℝ} (hF : IsRegularWith x F) {ν : Measure ℝ} (hν : G1Z2SideBdryLim γ left x ν)
    {b : ℝ} (hb : 0 < b) :
    IsVagueLimitOnR (g1SideHalf left) (bdryApprox γ (rescale x (Qc γ) b))
      (ν.map fun u => u / b) := by
  set S := g1SideHalf left with hSdef
  have hSo : IsOpen S := by
    cases left
    · exact isOpen_Ioi
    · exact isOpen_Iio
  set h : ℝ ≃ₜ ℝ := Homeomorph.mulRight₀ b⁻¹ (inv_ne_zero hb.ne') with hh
  have hhc : ∀ u, h u = u / b := fun u => by simp [hh, div_eq_mul_inv]
  have hfun : (fun u : ℝ => u / b) = h := funext fun u => (hhc u).symm
  have hmeas : Measurable fun u : ℝ => u / b := measurable_id.div_const b
  refine ⟨?_, fun K hK hKS => ?_, fun f hf hfc hfS => ?_⟩
  · rw [Measure.map_apply hmeas hSo.measurableSet.compl]
    have : (fun u : ℝ => u / b) ⁻¹' Sᶜ = Sᶜ := by
      ext u; simp only [mem_preimage, mem_compl_iff]; rw [g1z2_mem_sideHalf_div hb]
    rw [this]; exact hν.1
  · rw [Measure.map_apply hmeas hK.isClosed.measurableSet]
    refine hν.2.1 _ ?_ fun u hu => (g1z2_mem_sideHalf_div hb left u).1 (hKS hu)
    rw [hfun]; exact h.isCompact_preimage.2 hK
  · have hg : Continuous fun u : ℝ => f (u / b) := hf.comp (continuous_id.div_const b)
    have hgc : HasCompactSupport fun u : ℝ => f (u / b) := by
      have := hfc.comp_homeomorph h
      rwa [← hfun] at this
    have hgS : tsupport (fun u : ℝ => f (u / b)) ⊆ S := fun u hu =>
      (g1z2_mem_sideHalf_div hb left u).1
        (hfS (g1z2_tsupport_comp (f := f) (continuous_id.div_const b) hu))
    have hlim : Tendsto (fun r => ∫ t, f (t / b) ∂bdryR γ x r) (𝓝[>] 0)
        (𝓝 (∫ t, f (t / b) ∂ν)) := by
      refine ((hν.2.2 _ hg hgc hgS).comp GoodTransforms.tendsto_idx).congr' ?_
      filter_upwards [(Ioo_mem_nhdsGT one_pos : Ioo (0 : ℝ) 1 ∈ 𝓝[>] 0)] with r hr
      simp only [Function.comp, (GoodTransforms.idx_spec ⟨hr.1, hr.2.le⟩).1]
    have hrad : Tendsto (fun k : ℕ => b * radius k) atTop (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun k => mul_pos hb (radius_pos k)⟩
      have := (tendsto_nhdsWithin_iff.1 RegClosure.tendsto_radius_nhdsGT).1.const_mul b
      rwa [mul_zero] at this
    rw [integral_map hmeas.aemeasurable hf.aestronglyMeasurable]
    refine (hlim.comp hrad).congr fun k => ?_
    simp only [Function.comp]
    rw [← GoodSample.bdryR_radius γ (hF.rescale' (Qc γ) hb) k, one_mul,
      GoodTransforms.integral_bdryR_rescale hF hγ hb (radius_pos k) f]

/-- The side boundary measure of the rescaled field. -/
theorem g1z2_sideNu_rescale {γ : ℝ} (hγ : 0 < γ) {left : Bool} {x : FieldSample}
    {F : ℂ × ℝ → ℝ} (hF : IsRegularWith x F) {ν : Measure ℝ} (hν : G1Z2SideBdryLim γ left x ν)
    {b : ℝ} (hb : 0 < b) :
    g1SideNu γ left (rescale x (Qc γ) b) = ν.map fun u => u / b :=
  LocalRule.qBoundaryMeasureOn_eq (g1z2_isOpen_sideHalf left)
    (g1z2_isVagueLimitOnR_rescale hγ hF hν hb)

/-- The side boundary measure of the field itself. -/
theorem g1z2_sideNu_eq {γ : ℝ} {left : Bool} {x : FieldSample}
    {F : ℂ × ℝ → ℝ} (hF : IsRegularWith x F) {ν : Measure ℝ} (hν : G1Z2SideBdryLim γ left x ν) :
    g1SideNu γ left x = ν := by
  have hSo : IsOpen (g1SideHalf left) := by
    cases left
    · exact isOpen_Ioi
    · exact isOpen_Iio
  unfold g1SideNu
  refine LocalRule.qBoundaryMeasureOn_eq hSo ⟨hν.1, hν.2.1, fun f hf hfc hfS => ?_⟩
  refine ((hν.2.2 f hf hfc hfS).comp GoodSample.tendsto_one_goodFilter).congr fun k => ?_
  simp only [Function.comp, goodRad, GoodSample.bdryR_radius γ hF k]

/-- `translate (rescale x Q b) (p / b)` and `rescale (translate x p) Q b` have the same
regularized averages. -/
theorem g1z2_regEq_translate_rescale {x : FieldSample} {F : ℂ × ℝ → ℝ} (hF : IsRegularWith x F)
    (Q : ℝ) {b : ℝ} (hb : 0 < b) (p : ℝ) :
    RegEq (translate (rescale x Q b) ((p / b : ℝ) : ℂ)) (rescale (translate x (p : ℂ)) Q b) := by
  have hb' : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  have key : ∀ d : ℂ, ∀ r > 0, translate (rescale x Q b) ((p / b : ℝ) : ℂ) (foldedCircle d r) =
      rescale (translate x (p : ℂ)) Q b (foldedCircle d r) := by
    intro d r hr
    have hV := hF.rescale' Q hb
    have hy := hF.translate' p
    show evalReg (rescale x Q b) ((foldedCircle d r).map (· + ((p / b : ℝ) : ℂ))) = _
    rw [IndepParams.fc_map_add_real, hV.evalReg_fc _ hr, G1.rescale_fc_apply _ Q hb,
      hy.evalReg_fc _ (mul_pos hb hr), RegClosure.foldH_add_real,
      CircleFubini.foldH_of_mem' (CircleFubini.foldH_mem_Hbar' _), RegClosure.foldH_mul_pos d hb]
    have e : (b : ℂ) * (foldH d + ((p / b : ℝ) : ℂ)) = (b : ℂ) * foldH d + (p : ℂ) := by
      rw [mul_add, Complex.ofReal_div, mul_div_cancel₀ _ hb']
    simp only [e]
  intro k z
  unfold avgReg
  simp_rw [key _ _ (radius_pos k)]

/-- Scale consistency of a regular sample at dilated folded circles. -/
theorem g1z2_scaleConsistent_fc {y : FieldSample} {F : ℂ × ℝ → ℝ} (hF : IsRegularWith y F)
    (Q : ℝ) {b c : ℝ} (hb : 0 < b) (hc : 0 < c) (w : ℂ) {r : ℝ} (hr : 0 < r) :
    G1.ScaleConsistentAt y Q b ((foldedCircle w r).map fun z => (c : ℂ) * z) := by
  unfold G1.ScaleConsistentAt
  rw [WedgeTK.fc_map_mul w r hc, WedgeTK.fc_map_mul _ _ hb,
    (hF.rescale' Q hb).evalReg_fc _ (mul_pos hc hr), hF.evalReg_fc _ (mul_pos hb (mul_pos hc hr)),
    RegClosure.foldH_mul_pos _ hb, probReal_univ, mul_one]

theorem g1z2_preimage_sub_ball (p : ℝ) (a : ℝ) :
    (fun z : ℂ => z - (p : ℂ)) ⁻¹' (Metric.ball (0 : ℂ) a ∩ H) = Metric.ball (p : ℂ) a ∩ H := by
  ext z
  simp only [mem_preimage, mem_inter_iff, Metric.mem_ball, dist_eq_norm, sub_zero]
  constructor <;> rintro ⟨h1, h2⟩ <;> refine ⟨h1, ?_⟩
  · have : 0 < (z - (p : ℂ)).im := h2
    show 0 < z.im
    simpa using this
  · show 0 < (z - (p : ℂ)).im
    have : 0 < z.im := h2
    simpa using this

/-- Mass bounds of the translated area limit. -/
theorem g1z2_translate_mass {μ : Measure ℂ} (p : ℝ)
    (hsmall : ∃ a : ℝ, 0 < a ∧ μ (Metric.ball (p : ℂ) a ∩ H) < 1) (htop : μ H = ⊤) :
    (∃ a₀ : ℝ, 0 < a₀ ∧ (μ.map fun z => z - (p : ℂ)) (Metric.ball (0 : ℂ) a₀ ∩ H) < 1) ∧
    (∃ a₁ : ℝ, 0 < a₁ ∧ 1 ≤ (μ.map fun z => z - (p : ℂ)) (Metric.ball (0 : ℂ) a₁ ∩ H)) := by
  have hmeas : Measurable fun z : ℂ => z - (p : ℂ) := measurable_id.sub_const _
  have hm : ∀ a : ℝ, (μ.map fun z => z - (p : ℂ)) (Metric.ball (0 : ℂ) a ∩ H) =
      μ (Metric.ball (p : ℂ) a ∩ H) := fun a => by
    rw [Measure.map_apply hmeas (Metric.isOpen_ball.inter isOpen_H).measurableSet,
      g1z2_preimage_sub_ball]
  refine ⟨?_, ?_⟩
  · obtain ⟨a, ha, h⟩ := hsmall
    exact ⟨a, ha, by rw [hm]; exact h⟩
  · set s : ℕ → Set ℂ := fun n => Metric.ball (p : ℂ) ((n : ℝ) + 1) ∩ H with hs
    have hmono : Monotone s := fun m n hmn => inter_subset_inter_left _
      (Metric.ball_subset_ball (by have : (m : ℝ) ≤ n := by exact_mod_cast hmn
                                   linarith))
    have hU : μ (⋃ n, s n) = ⊤ := by
      refine top_unique (htop ▸ measure_mono fun z hz => ?_)
      obtain ⟨n, hn⟩ := exists_nat_gt (dist z (p : ℂ))
      exact mem_iUnion.2 ⟨n, Metric.mem_ball.2 (by linarith), hz⟩
    have ht := tendsto_measure_iUnion_atTop (μ := μ) hmono
    rw [hU] at ht
    obtain ⟨n, hn⟩ := (ht.eventually (lt_mem_nhds ENNReal.one_lt_top)).exists
    exact ⟨(n : ℝ) + 1, by positivity, by rw [hm]; exact hn.le⟩

/-- **Scale invariance of the rerooted canonical side data.** -/
theorem g1z2_rerootData_rescale {γ : ℝ} (hγ : 0 < γ) {left : Bool} {x : FieldSample}
    (hx : G1Z2Good γ left x) {b : ℝ} (hb : 0 < b) {W : FieldSample}
    (hW : RegEq W (rescale x (Qc γ) b)) (R : ℕ) (ℓ : ℝ) :
    locFieldFull R (canonical γ (translate W (g1SidePt γ left W ℓ : ℂ))) =
      locFieldFull R (canonical γ (translate x (g1SidePt γ left x ℓ : ℂ))) := by
  obtain ⟨⟨F, hF⟩, ⟨μ, hμ, hsmall, htop⟩, ⟨ν, hν⟩, hsc⟩ := hx
  have havg : avgReg W = avgReg (rescale x (Qc γ) b) := funext fun k => funext fun z => hW k z
  have hbd : bdryApprox γ W = bdryApprox γ (rescale x (Qc γ) b) := by
    funext k; unfold bdryApprox; rw [havg]
  have hnuW : g1SideNu γ left W = (g1SideNu γ left x).map fun u => u / b := by
    rw [g1z2_sideNu_eq hF hν, ← g1z2_sideNu_rescale hγ hF hν hb]
    unfold g1SideNu qBoundaryMeasureOn
    rw [hbd]
  rw [g1z2_sidePt_of_map hb hnuW ℓ]
  set p := g1SidePt γ left x ℓ with hp
  have htr : translate W ((p / b : ℝ) : ℂ) = translate (rescale x (Qc γ) b) ((p / b : ℝ) : ℂ) := by
    funext μ'; unfold translate; rw [evalReg_congr havg]
  rw [htr, Factorization.canonical_congr (funext fun k => funext fun z =>
    g1z2_regEq_translate_rescale hF (Qc γ) hb p k z) γ]
  have hyF := hF.translate' p
  have hyr : IsRegularSample (translate x (p : ℂ)) := ⟨_, hyF⟩
  have hμy := GoodTransforms.hasAreaLimit_translate ⟨F, hF⟩ hμ p
  obtain ⟨hs1, hs2⟩ := g1z2_translate_mass p (hsmall p) htop
  have hs := g1z2_scaleParam_pos hyr hμy hs1 hs2
  have hsb := div_pos hs hb
  have happ : ∀ ν' : Measure ℂ, G1.ScaleConsistentAt (translate x (p : ℂ)) (Qc γ) b
      (ν'.map fun z => ((scaleParam γ (translate x (p : ℂ)) / b : ℝ) : ℂ) * z) →
      canonical γ (rescale (translate x (p : ℂ)) (Qc γ) b) ν' =
        canonical γ (translate x (p : ℂ)) ν' :=
    fun ν' h => g1z2_canonical_rescale_apply hγ hyr hμy hb hs ν' h
  unfold locFieldFull
  congr 1
  · funext i
    split_ifs
    · exact happ _ (g1z2_scaleConsistent_fc hyF (Qc γ) hb hsb _
        (by unfold CoordsFull.fullIndex; positivity))
    · rfl
  · funext ρ
    split_ifs
    · unfold pairRaw
      rw [happ _ (hsc p b hb _ hsb ρ ρ.1 (Or.inl rfl)),
        happ _ (hsc p b hb _ hsb ρ _ (Or.inr rfl))]
    · rfl

end Thm18Asm
end QuantumZipper
