import QuantumZipper.Proofs.Zipper.LocLenR5aStmts
import QuantumZipper.Proofs.Zipper.LocLenRules
import QuantumZipper.Proofs.Zipper.E6FlowPair
import QuantumZipper.Proofs.Zipper.ZipLenMain

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R5a (D75): deterministic zip algebra of E6-ID with open-arc lengths

Open-arc copies of the deterministic lemmas behind `E6.CanonZipRawAllStmt`:

* `zipLenDownArc_eq_canonConfig_r5a` (copy of `zipLenDown_eq_canonConfig`, LengthZip.lean:73);
* `unzipLengthsArc_canon_fst` (copy of `B3d.unzipLengths_canon_fst`, B3dDet.lean:129): only a
  boundary limit off the chart tip `{0}` is used (`arcLen_rescale_of_hasBdryLimitOn`,
  `arcLen_addConst`);
* `zipLenDownArc_canonConfig_addConst` (copy of `B3d.zipLenDown_canonConfig_addConst`);
* `rawCircRegular_zipLenDownArc_canon`, `rawPairRegular_zipLenDownArc_canon` (copies of
  `E6.rawCircRegular_zipLenDown_canon`, `E6.rawPairRegular_zipLenDown_canon`).

Everywhere `IsLQGGood` of the unzipped fields is replaced by `IsLQGGoodOff … {0}` (good off the
chart tip); the area statements use only regularity and the area limit
(`scaleParam_rescale_r5a`, `canonical_rescale_regEq_r5a`, `qAreaMeasure_addConst_off`).
Sources: Sheffield arXiv:1012.4797 §5.4 pp. 70–72 (E6 identity, zipping by quantum length);
B-P arXiv:2404.16642 Def 6.41 p. 229. Own bookkeeping, verbatim copies of the old proofs.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal Pointwise

namespace QuantumZipper
namespace LocLen

open B2 E1 D3Plus E6

variable {γ : ℝ}

/-! ## Area statements from regularity and the area limit -/

theorem qAreaMeasure_addConst_off {x : FieldSample} {S : Set ℝ} (hx : IsLQGGoodOff γ x S)
    (c : ℝ) :
    qAreaMeasure γ (addConst x c) = ENNReal.ofReal (Real.exp (γ * c)) • qAreaMeasure γ x := by
  obtain ⟨hr, -, μ, hμ⟩ := hx
  have hμ' : HasAreaLimit γ x (qAreaMeasure γ x) := by
    rw [GoodSample.qAreaMeasure_eq_of_hasAreaLimit hr hμ]; exact hμ
  rw [GoodSample.addConst_eq_add_ofFun,
    GoodSample.qAreaMeasure_eq_of_hasAreaLimit (GoodSample.gs_add_ofFun_sample hr continuousOn_const)
      (GoodSample.hasAreaLimit_add_ofFun hr hμ' continuousOn_const), withDensity_const]

/-- Copy of `B3d.ZipLen.scaleParam_addConst_pos_of_area` with goodness off `S`. -/
theorem scaleParam_addConst_pos_off {x : FieldSample} {S : Set ℝ} (hx : IsLQGGoodOff γ x S)
    (hfin : ∀ a : ℝ, qAreaMeasure γ x (Metric.ball 0 a ∩ H) < ⊤)
    (hinf : qAreaMeasure γ x H = ⊤) (k : ℝ) : 0 < scaleParam γ (addConst x k) := by
  have hc : ENNReal.ofReal (Real.exp (γ * k)) ≠ 0 :=
    (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
  refine E6.scaleParam_pos_of_area (fun a => ?_) ?_
  · rw [qAreaMeasure_addConst_off hx k, Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hfin a)
  · rw [qAreaMeasure_addConst_off hx k, Measure.smul_apply, smul_eq_mul, hinf]
    exact ENNReal.mul_eq_top.2 (Or.inl ⟨hc, rfl⟩)

/-- Copy of `GoodTransforms.scaleParam_rescale` from regularity and the area limit only. -/
theorem scaleParam_rescale_r5a {x : FieldSample} (hx : IsRegularSample x)
    {μ : Measure ℂ} (hμ : HasAreaLimit γ x μ) (hγ : 0 < γ) {b : ℝ} (hb : 0 < b) :
    scaleParam γ (rescale x (Qc γ) b) = scaleParam γ x / b := by
  have hq : qAreaMeasure γ (rescale x (Qc γ) b) =
      (qAreaMeasure γ x).map fun z : ℂ => z / (b : ℂ) := by
    rw [GoodSample.qAreaMeasure_eq_of_hasAreaLimit (hx.rescale' (Qc γ) hb)
      (GoodTransforms.hasAreaLimit_rescale hx hγ hμ hb),
      GoodSample.qAreaMeasure_eq_of_hasAreaLimit hx hμ]
  unfold scaleParam
  rw [hq]
  have hmeas : Measurable (fun z : ℂ => z / (b : ℂ)) := measurable_id.div_const _
  have e : {a : ℝ | 0 < a ∧ 1 ≤ ((qAreaMeasure γ x).map fun z : ℂ => z / (b : ℂ))
      (Metric.ball (0 : ℂ) a ∩ H)} =
      b⁻¹ • {a : ℝ | 0 < a ∧ 1 ≤ qAreaMeasure γ x (Metric.ball (0 : ℂ) a ∩ H)} := by
    ext a
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ (inv_ne_zero hb.ne'), inv_inv, smul_eq_mul]
    simp only [mem_setOf_eq]
    rw [Measure.map_apply hmeas (Metric.isOpen_ball.inter isOpen_H).measurableSet,
      GoodTransforms.preimage_div_ball_inter_H hb, mul_comm b a]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨mul_pos h1 hb, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨pos_of_mul_pos_left h1 hb.le, h2⟩
  rw [e, Real.sInf_smul_of_nonneg (inv_nonneg.2 hb.le), smul_eq_mul, div_eq_inv_mul]

/-- Copy of `GoodTransforms.canonical_rescale_regEq` from regularity and the area limit. -/
theorem canonical_rescale_regEq_r5a {x : FieldSample} (hx : IsRegularSample x)
    {μ : Measure ℂ} (hμ : HasAreaLimit γ x μ) (hγ : 0 < γ) {b : ℝ} (hb : 0 < b)
    (hs : 0 < scaleParam γ x) :
    RegEq (canonical γ (rescale x (Qc γ) b)) (canonical γ x) := by
  unfold canonical
  rw [scaleParam_rescale_r5a hx hμ hγ hb]
  have h := hx.regEq_rescale_rescale (Qc γ) hb (div_pos hs hb)
  rwa [mul_div_cancel₀ _ hb.ne'] at h

/-! ## Zipping by open-arc length -/

theorem zipLenDownArc_eq_canonConfig_r5a (γ ℓ : ℝ) (c : FieldSample × (ℝ → ℝ)) :
    zipLenDownArc γ ℓ c = canonConfig γ (zipCapDown γ (lenTimeArc γ ℓ c) c) := by
  simp only [zipLenDownArc, canonConfig, zipCapDown, canonical]
  refine Prod.ext rfl ?_
  funext s
  simp only
  rw [max_eq_left (mul_nonneg (sq_nonneg _) (le_max_right s 0))]

/-- **Left open-arc length of the canonicalized configuration** (copy of
`B3d.unzipLengths_canon_fst`). -/
theorem unzipLengthsArc_canon_fst (hγ : 0 < γ) {x : FieldSample} {W : ℝ → ℝ} {k : ℝ}
    (ha : 0 < scaleParam γ (addConst x k))
    (hWmax : ∀ s, W (max s 0) = W s) {s : ℝ} (hs : 0 ≤ s)
    (hside : ∃ l, Tendsto (fun r : ℝ => (fwdMap W (scaleParam γ (addConst x k) ^ 2 * s) r).re)
      (𝓝[<] (0 : ℝ)) (𝓝 l))
    (hgood : IsLQGGoodOff γ (unzippedField γ (x, W) (scaleParam γ (addConst x k) ^ 2 * s)) {0})
    (hfield : RegEq (unzippedField γ (canonConfig γ (addConst x k, W)) s)
      (rescale (addConst (unzippedField γ (x, W) (scaleParam γ (addConst x k) ^ 2 * s)) k)
        (Qc γ) (scaleParam γ (addConst x k)))) :
    (unzipLengthsArc γ (canonConfig γ (addConst x k, W)) s).1 =
      ENNReal.ofReal (Real.exp (γ * k / 2)) *
        (unzipLengthsArc γ (x, W) (scaleParam γ (addConst x k) ^ 2 * s)).1 := by
  set a := scaleParam γ (addConst x k) with ha_def
  set F := unzippedField γ (x, W) (a ^ 2 * s) with hF
  obtain ⟨l, hl⟩ := hside
  obtain ⟨hreg, ⟨ν, hν⟩, -⟩ := hgood.addConst k
  have hsub : Ioo l 0 ⊆ ({0} : Set ℝ)ᶜ := fun z hz hz0 => by
    rw [mem_singleton_iff] at hz0; linarith [hz.2]
  have e1 : (sideImages W (a ^ 2 * s)).1 = l := hl.limUnder_eq
  show arcLen γ (unzippedField γ (canonConfig γ (addConst x k, W)) s)
      (sideImages (canonConfig γ (addConst x k, W)).2 s).1 0 =
    ENNReal.ofReal (Real.exp (γ * k / 2)) * arcLen γ F (sideImages W (a ^ 2 * s)).1 0
  rw [arcLen_congr (B3d.avgReg_eq_of_regEq hfield), B3d.canonConfig_snd_of_max hWmax,
    B3d.sideImages_fst_scale W ha hs hl, e1,
    arcLen_rescale_of_hasBdryLimitOn hreg hγ ha hν
      (by rw [mul_div_cancel₀ _ ha.ne', mul_zero]; exact hsub),
    mul_div_cancel₀ _ ha.ne', mul_zero, ← arcLen_eq_of_hasBdryLimitOn hreg hν hsub,
    arcLen_addConst hgood.1.rawConverges]

/-- The length time of the canonicalized configuration (the `hτ` step of
`B3d.zipLenDown_canonConfig_addConst`). -/
theorem lenTimeArc_canon (hγ : 0 < γ) {x : FieldSample} {W : ℝ → ℝ} {k ℓ t₀ : ℝ}
    (ha : 0 < scaleParam γ (addConst x k)) (hWmax : ∀ s, W (max s 0) = W s)
    (hside : ∀ t, 0 ≤ t → ∃ l, Tendsto (fun r : ℝ => (fwdMap W t r).re) (𝓝[<] (0 : ℝ)) (𝓝 l))
    (hgood : ∀ t, 0 ≤ t → IsLQGGoodOff γ (unzippedField γ (x, W) t) {0})
    (hfield : ∀ s, 0 ≤ s → RegEq (unzippedField γ (canonConfig γ (addConst x k, W)) s)
      (rescale (addConst (unzippedField γ (x, W) (scaleParam γ (addConst x k) ^ 2 * s)) k)
        (Qc γ) (scaleParam γ (addConst x k))))
    (ht₀ : t₀ = sInf {s : ℝ | 0 ≤ s ∧ ENNReal.ofReal ℓ ≤
      ENNReal.ofReal (Real.exp (γ * k / 2)) * (unzipLengthsArc γ (x, W) s).1}) :
    lenTimeArc γ ℓ (canonConfig γ (addConst x k, W)) =
      t₀ / scaleParam γ (addConst x k) ^ 2 := by
  set a := scaleParam γ (addConst x k) with ha_def
  have ha2 : 0 < a ^ 2 := by positivity
  have hset : {s : ℝ | 0 ≤ s ∧ ENNReal.ofReal ℓ ≤
        (unzipLengthsArc γ (canonConfig γ (addConst x k, W)) s).1} =
      {s : ℝ | 0 ≤ s ∧ ENNReal.ofReal ℓ ≤
        ENNReal.ofReal (Real.exp (γ * k / 2)) * (unzipLengthsArc γ (x, W) (a ^ 2 * s)).1} := by
    ext s
    simp only [mem_ofPred_eq]
    constructor
    · rintro ⟨hs, h⟩
      refine ⟨hs, ?_⟩
      rwa [← unzipLengthsArc_canon_fst hγ ha hWmax hs (hside _ (by positivity))
        (hgood _ (by positivity)) (hfield s hs)]
    · rintro ⟨hs, h⟩
      refine ⟨hs, ?_⟩
      rwa [unzipLengthsArc_canon_fst hγ ha hWmax hs (hside _ (by positivity))
        (hgood _ (by positivity)) (hfield s hs)]
  unfold lenTimeArc
  rw [hset, B3d.sInf_scale (L := fun t => ENNReal.ofReal (Real.exp (γ * k / 2)) *
    (unzipLengthsArc γ (x, W) t).1) ha2, ← ht₀]

/-- **Zip algebra at one configuration, open arcs** (copy of
`B3d.zipLenDown_canonConfig_addConst`). -/
theorem zipLenDownArc_canonConfig_addConst (hγ : 0 < γ) {x : FieldSample} {W : ℝ → ℝ}
    {k : ℝ} (ha : 0 < scaleParam γ (addConst x k)) (hWmax : ∀ s, W (max s 0) = W s)
    (hside : ∀ t, 0 ≤ t → ∃ l, Tendsto (fun r : ℝ => (fwdMap W t r).re) (𝓝[<] (0 : ℝ)) (𝓝 l))
    (hgood : ∀ t, 0 ≤ t → IsLQGGoodOff γ (unzippedField γ (x, W) t) {0})
    (hfield : ∀ s, 0 ≤ s → RegEq (unzippedField γ (canonConfig γ (addConst x k, W)) s)
      (rescale (addConst (unzippedField γ (x, W) (scaleParam γ (addConst x k) ^ 2 * s)) k)
        (Qc γ) (scaleParam γ (addConst x k))))
    {ℓ t₀ : ℝ}
    (ht₀ : t₀ = sInf {s : ℝ | 0 ≤ s ∧ ENNReal.ofReal ℓ ≤
      ENNReal.ofReal (Real.exp (γ * k / 2)) * (unzipLengthsArc γ (x, W) s).1})
    (hb : 0 < scaleParam γ (addConst (unzippedField γ (x, W) t₀) k)) :
    ConfigEq (zipLenDownArc γ ℓ (canonConfig γ (addConst x k, W)))
      (canonConfig γ (addConst (zipCapDown γ t₀ (x, W)).1 k, (zipCapDown γ t₀ (x, W)).2)) := by
  set a := scaleParam γ (addConst x k) with ha_def
  set c' := canonConfig γ (addConst x k, W) with hc'
  have ha2 : 0 < a ^ 2 := by positivity
  have ht0 : 0 ≤ t₀ := ht₀ ▸ Real.sInf_nonneg fun s hs => hs.1
  have hτ := lenTimeArc_canon hγ ha hWmax hside hgood hfield ht₀
  rw [zipLenDownArc_eq_canonConfig_r5a, hτ]
  set τ := t₀ / a ^ 2 with hτdef
  have hτ0 : 0 ≤ τ := div_nonneg ht0 ha2.le
  have haτ : a ^ 2 * τ = t₀ := by rw [hτdef]; field_simp
  set G := addConst (unzippedField γ (x, W) t₀) k with hG
  obtain ⟨hGr, -, μG, hμG⟩ := (hgood t₀ ht0).addConst k
  have hU : avgReg (zipCapDown γ τ c').1 = avgReg (rescale G (Qc γ) a) := by
    have := B3d.avgReg_eq_of_regEq (hfield τ hτ0)
    rw [haτ] at this
    exact this
  have hsc : scaleParam γ (zipCapDown γ τ c').1 = scaleParam γ G / a := by
    rw [Factorization.scaleParam_congr hU, scaleParam_rescale_r5a hGr hμG hγ ha]
  refine ⟨?_, fun u hu => ?_⟩
  · show RegEq (canonical γ (zipCapDown γ τ c').1) (canonical γ G)
    rw [Factorization.canonical_congr hU]
    exact canonical_rescale_regEq_r5a hGr hμG hγ ha hb
  · have hbpos : 0 < scaleParam γ G := hb
    have hL : (canonConfig γ (zipCapDown γ τ c')).2 u =
        (zipCapDown γ τ c').2 (scaleParam γ (zipCapDown γ τ c').1 ^ 2 * max u 0) /
          scaleParam γ (zipCapDown γ τ c').1 := rfl
    have hR : (canonConfig γ (G, (zipCapDown γ t₀ (x, W)).2)).2 u =
        (zipCapDown γ t₀ (x, W)).2 (scaleParam γ G ^ 2 * max u 0) / scaleParam γ G := rfl
    refine hL.trans (Eq.trans ?_ hR.symm)
    have hc2 : c'.2 = fun r => W (a ^ 2 * r) / a := B3d.canonConfig_snd_of_max hWmax
    have hzd : ∀ v, (zipCapDown γ τ c').2 v = c'.2 (τ + max v 0) - c'.2 τ := fun v => rfl
    have hzd' : ∀ v, (zipCapDown γ t₀ (x, W)).2 v = W (t₀ + max v 0) - W t₀ := fun v => rfl
    rw [hzd, hzd', hc2, hsc]
    generalize scaleParam γ G = b at hbpos ⊢
    have hmu : max u 0 = u := max_eq_left hu
    have h1 : 0 ≤ (b / a) ^ 2 * u := by positivity
    have h2 : 0 ≤ b ^ 2 * u := by positivity
    rw [hmu, max_eq_left h1, max_eq_left h2]
    have e1 : a ^ 2 * (τ + (b / a) ^ 2 * u) = t₀ + b ^ 2 * u := by
      rw [mul_add, haτ]; field_simp
    beta_reduce
    rw [e1, haτ]
    field_simp

/-! ## Raw regularity of the left side -/

/-- Copy of `E6.rawCircRegular_zipLenDown_canon` (open arcs, goodness off the tip). -/
theorem rawCircRegular_zipLenDownArc_canon {k ℓ : ℝ} (hγ : 0 < γ)
    {c : FieldSample × (ℝ → ℝ)}
    (ha : 0 < scaleParam γ (addConst c.1 k))
    (hb : ∀ t, 0 ≤ t → 0 < scaleParam γ (addConst (unzippedField γ c t) k))
    (hgood : ∀ t, 0 ≤ t → IsLQGGoodOff γ (unzippedField γ c t) {0})
    (hfield : ∀ s, 0 ≤ s → RegEq (unzippedField γ (canonConfig γ (addConst c.1 k, c.2)) s)
      (rescale (addConst (unzippedField γ c (scaleParam γ (addConst c.1 k) ^ 2 * s)) k) (Qc γ)
        (scaleParam γ (addConst c.1 k)))) :
    RawCircRegular (zipLenDownArc γ ℓ (canonConfig γ (addConst c.1 k, c.2))).1 := by
  rw [zipLenDownArc_eq_canonConfig_r5a]
  set c' := canonConfig γ (addConst c.1 k, c.2) with hc'
  set τ := lenTimeArc γ ℓ c' with hτ
  have hτ0 : 0 ≤ τ := Real.sInf_nonneg fun s hs => hs.1
  set a := scaleParam γ (addConst c.1 k) with ha_def
  have hτa : 0 ≤ a ^ 2 * τ := by positivity
  set G := addConst (unzippedField γ c (a ^ 2 * τ)) k with hG
  obtain ⟨hGr, -, μG, hμG⟩ := (hgood _ hτa).addConst k
  have hU : avgReg (zipCapDown γ τ c').1 = avgReg (rescale G (Qc γ) a) :=
    B3d.avgReg_eq_of_regEq (hfield τ hτ0)
  show RawCircRegular (rescale (zipCapDown γ τ c').1 (Qc γ) (scaleParam γ (zipCapDown γ τ c').1))
  rw [Factorization.scaleParam_congr hU, B3d.rescale_congr_avgReg hU,
    scaleParam_rescale_r5a hGr hμG hγ ha]
  exact rawCircRegular_rescale (hGr.rescale' (Qc γ) ha) _ (div_pos (hb _ hτa) ha)

/-- Copy of `E6.rawPairRegular_zipLenDown_canon` (open arcs, goodness off the tip). -/
theorem rawPairRegular_zipLenDownArc_canon {k ℓ t₀ : ℝ} (hγ : 0 < γ)
    {c : FieldSample × (ℝ → ℝ)} (hWmax : ∀ s, c.2 (max s 0) = c.2 s)
    (ha : 0 < scaleParam γ (addConst c.1 k))
    (hb : ∀ t, 0 ≤ t → 0 < scaleParam γ (addConst (unzippedField γ c t) k))
    (hside : ∀ t, 0 ≤ t → ∃ l, Tendsto (fun r : ℝ => (fwdMap c.2 t r).re) (𝓝[<] (0 : ℝ)) (𝓝 l))
    (hgood : ∀ t, 0 ≤ t → IsLQGGoodOff γ (unzippedField γ c t) {0})
    (hfield : ∀ s, 0 ≤ s → RegEq (unzippedField γ (canonConfig γ (addConst c.1 k, c.2)) s)
      (rescale (addConst (unzippedField γ c (scaleParam γ (addConst c.1 k) ^ 2 * s)) k) (Qc γ)
        (scaleParam γ (addConst c.1 k))))
    (ht₀ : t₀ = sInf {s : ℝ | 0 ≤ s ∧ ENNReal.ofReal ℓ ≤
      ENNReal.ofReal (Real.exp (γ * k / 2)) * (unzipLengthsArc γ c s).1})
    {y : FieldSample} (hy : IsRegularSample y)
    (hyc : avgReg (addConst y k) = avgReg (addConst (unzippedField γ c t₀) k))
    (hD : ∀ b : ℝ, 0 < b → DensPair y b) :
    RawPairRegular (zipLenDownArc γ ℓ (canonConfig γ (addConst c.1 k, c.2))).1 := by
  have ht : 0 ≤ t₀ := ht₀ ▸ Real.sInf_nonneg fun s hs => hs.1
  have hτeq : lenTimeArc γ ℓ (canonConfig γ (addConst c.1 k, c.2)) =
      t₀ / scaleParam γ (addConst c.1 k) ^ 2 :=
    lenTimeArc_canon (x := c.1) (W := c.2) hγ ha hWmax hside hgood hfield ht₀
  rw [zipLenDownArc_eq_canonConfig_r5a]
  set c' := canonConfig γ (addConst c.1 k, c.2) with hc'
  set a := scaleParam γ (addConst c.1 k) with ha_def
  have ha2 : 0 < a ^ 2 := by positivity
  set τ := lenTimeArc γ ℓ c' with hτ
  have hτ0 : 0 ≤ τ := by rw [hτeq]; exact div_nonneg ht ha2.le
  have hat : a ^ 2 * τ = t₀ := by rw [hτeq]; field_simp
  set G := addConst (unzippedField γ c (a ^ 2 * τ)) k with hG
  obtain ⟨hGr, -, μG, hμG⟩ := (hgood (a ^ 2 * τ) (by positivity)).addConst k
  have hU : avgReg (zipCapDown γ τ c').1 = avgReg (rescale G (Qc γ) a) :=
    B3d.avgReg_eq_of_regEq (hfield τ hτ0)
  show RawPairRegular (rescale (zipCapDown γ τ c').1 (Qc γ) (scaleParam γ (zipCapDown γ τ c').1))
  rw [Factorization.scaleParam_congr hU, B3d.rescale_congr_avgReg hU,
    scaleParam_rescale_r5a hGr hμG hγ ha]
  have ha'' : 0 < scaleParam γ G / a := div_pos (hb _ (by positivity)) ha
  obtain ⟨F, hF⟩ := hGr.rescale' (Qc γ) ha
  refine rawPairRegular_rescale hF _ ha'' (densPair_rescale hGr _ ha ha'' ?_)
  have hGB : avgReg (addConst y k) = avgReg G := by
    rw [hG, hat]
    exact hyc
  exact densPair_congr hGB (densPair_addConst hy (mul_pos ha ha'') (hD _ (mul_pos ha ha'')) k)

end LocLen
end QuantumZipper
