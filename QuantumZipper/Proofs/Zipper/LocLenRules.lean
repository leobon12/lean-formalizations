import QuantumZipper.Proofs.Zipper.LocLenDefs
import QuantumZipper.Proofs.LQG.GoodTransforms

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Follow-the-paper campaign (D75): transformation rules for local boundary limits

Local copies of the global transformation rules for the offset-uniform boundary limit, with the
support condition `tsupport f ⊆ U` added to every test function:

1. **Rescaling** (copy of `GoodTransforms.hasBdryLimit_rescale`): `HasBdryLimitOn.rescale`,
   `IsLQGGoodOff.rescale`, `arcLen_rescale_of_hasBdryLimitOn`.
2. **Additive constants** (copy of `IsLQGGood.addConst` and `LocalRule.qBoundaryMeasureOn_addConst`):
   `HasBdryLimitOn.addConst`, `IsLQGGoodOff.addConst`, `arcLen_addConst`.
3. **Adding a function continuous near `U`** (copy of `GoodSample.hasBdryLimit_add_ofFun`,
   localized as `LocalRule.isVagueLimitOnR_add_ofFun`): `HasBdryLimitOn.add_ofFun`.
4. **Congruence**: `hasBdryLimitOn_congr`, `hasBdryLimitOn_congr_avg`, `arcLen_congr`.

Sources: Sheffield, arXiv:1012.4797, eq. (1.3) (coordinate change) and eq. (5.1) p. 56
(the `e^{γφ/2}` rule for adding a continuous function); Duplantier–Sheffield, *Liouville quantum
gravity and KPZ*, Invent. Math. 185 (2011), Prop. 2.1 (the rescaling rule); Berestycki–Powell
arXiv:2404.16642, Def 6.41 p. 229 (the boundary measure is local). The Lean proofs are verbatim
localizations of the global proofs cited above.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace QuantumZipper
namespace LocLen

open GoodSample GoodTransforms LocalRule RegClosure GaussTK

variable {γ : ℝ} {x : FieldSample}

/-! ## Limits along all radii `r → 0⁺` -/

/-- A local offset-uniform limit is a limit along all radii `r → 0⁺` (copy of
`GoodTransforms.HasBdryLimit.tendsto_nhdsGT`). -/
theorem HasBdryLimitOn.tendsto_nhdsGT {U : Set ℝ} {ν : Measure ℝ} (h : HasBdryLimitOn γ x U ν)
    {f : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) (hfU : tsupport f ⊆ U) :
    Tendsto (fun r => ∫ t, f t ∂bdryR γ x r) (𝓝[>] 0) (𝓝 (∫ t, f t ∂ν)) := by
  refine ((h.2.2 f hf hfc hfU).comp tendsto_idx).congr' ?_
  filter_upwards [(Ioo_mem_nhdsGT one_pos : Ioo (0 : ℝ) 1 ∈ 𝓝[>] 0)] with r hr
  simp only [Function.comp, (idx_spec ⟨hr.1, hr.2.le⟩).1]

/-! ## 1. Rescaling -/

/-- The division by `a` as a homeomorphism. -/
theorem div_eq_homeo {a : ℝ} (ha : 0 < a) :
    (fun u : ℝ => u / a) = ⇑(Homeomorph.mulRight₀ a⁻¹ (inv_ne_zero ha.ne')) := by
  funext u; simp [div_eq_mul_inv]

/-- **Rescaling rule, local** (copy of `GoodTransforms.hasBdryLimit_rescale`). -/
theorem HasBdryLimitOn.rescale (hx : IsRegularSample x) (hγ : 0 < γ) {U : Set ℝ}
    {ν : Measure ℝ} (h : HasBdryLimitOn γ x U ν) {a : ℝ} (ha : 0 < a) :
    HasBdryLimitOn γ (rescale x (Qc γ) a) ((fun u => a * u) ⁻¹' U) (ν.map fun u => u / a) := by
  obtain ⟨F, hF⟩ := hx
  set e := Homeomorph.mulRight₀ a⁻¹ (inv_ne_zero ha.ne') with he
  have hdiv := div_eq_homeo ha
  have hme : MeasurableEmbedding (fun u : ℝ => u / a) := by
    rw [hdiv]; exact e.measurableEmbedding
  have hback : ∀ u : ℝ, a * (u / a) = u := fun u => mul_div_cancel₀ u ha.ne'
  refine ⟨?_, fun K hKc hKU => ?_, fun f hf hfc hfU => ?_⟩
  · rw [hme.map_apply]
    refine measure_mono_null (fun u hu => ?_) h.1
    intro huU
    exact hu (show a * (u / a) ∈ U by rw [hback]; exact huU)
  · rw [hme.map_apply]
    refine h.2.1 _ ?_ (fun u hu => ?_)
    · rw [hdiv]; exact e.isCompact_preimage.2 hKc
    · have := hKU hu
      simp only [mem_preimage] at this
      rwa [hback] at this
  · rw [hme.integral_map]
    have hfc' : HasCompactSupport (fun u => f (u / a)) := by
      have := hfc.comp_homeomorph e
      rw [← hdiv] at this; exact this
    have hfU' : tsupport (fun u => f (u / a)) ⊆ U := by
      intro u hu
      have h1 := tsupport_comp_subset_preimage f (continuous_id.div_const a) hu
      have h2 := hfU h1
      simp only [mem_preimage] at h2
      rwa [hback] at h2
    have ht := (h.tendsto_nhdsGT (hf.comp (continuous_id.div_const a)) hfc' hfU').comp
      (tendsto_mul_goodRad ha)
    refine ht.congr' (eventually_goodRad_pos.mono fun i hi => ?_)
    exact (integral_bdryR_rescale hF hγ ha hi f).symm

/-- **Rescaling preserves goodness off a set** (the set is rescaled by `1/a`). -/
theorem IsLQGGoodOff.rescale {S : Set ℝ} (hx : IsLQGGoodOff γ x S) (hγ : 0 < γ) {a : ℝ}
    (ha : 0 < a) : IsLQGGoodOff γ (rescale x (Qc γ) a) ((fun u => a * u) ⁻¹' S) := by
  obtain ⟨hr, ⟨ν, hν⟩, ⟨μ, hμ⟩⟩ := hx
  refine ⟨hr.rescale' (Qc γ) ha, ⟨ν.map fun u => u / a, ?_⟩,
    ⟨_, hasAreaLimit_rescale hr hγ hμ ha⟩⟩
  have := hν.rescale hr hγ ha
  rwa [preimage_compl] at this

/-- **Open-arc length after rescaling**: read off the local limit of `x` on `(ap, aq)`. -/
theorem arcLen_rescale_of_hasBdryLimitOn (hx : IsRegularSample x) (hγ : 0 < γ) {a : ℝ}
    (ha : 0 < a) {U : Set ℝ} {ν : Measure ℝ} (h : HasBdryLimitOn γ x U ν) {p q : ℝ}
    (hpq : Ioo (a * p) (a * q) ⊆ U) :
    arcLen γ (rescale x (Qc γ) a) p q = ν (Ioo (a * p) (a * q)) := by
  have hr := h.rescale hx hγ ha
  have hsub : Ioo p q ⊆ (fun u => a * u) ⁻¹' U := fun u hu =>
    hpq ⟨mul_lt_mul_of_pos_left hu.1 ha, mul_lt_mul_of_pos_left hu.2 ha⟩
  have hloc := hr.mono isOpen_Ioo hsub
  unfold arcLen
  rw [qBoundaryMeasureOn_eq_of_hasBdryLimitOn (hx.rescale' (Qc γ) ha) isOpen_Ioo hloc,
    Measure.restrict_apply_self,
    Measure.map_apply (by fun_prop : Measurable fun u : ℝ => u / a) measurableSet_Ioo]
  congr 1
  ext u
  simp only [mem_preimage, mem_Ioo]
  rw [lt_div_iff₀ ha, div_lt_iff₀ ha, mul_comm p, mul_comm q]

/-! ## 2. Additive constants -/

/-- Adding a constant multiplies the approximate boundary measures by `e^{γc/2}` (copy of
`bdryR_addConst_eq`, WedgeTipSmallZero.lean). -/
theorem bdryR_addConst_loc {G : ℂ × ℝ → ℝ} (hG : IsRegularWith x G) (c : ℝ) {r : ℝ}
    (hr : 0 < r) :
    bdryR γ (addConst x c) r = ENNReal.ofReal (Real.exp (γ * c / 2)) • bdryR γ x r := by
  unfold bdryR
  rw [← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  funext t
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
  congr 1
  unfold bdryDens
  rw [(hG.addConst' c).evalReg_fc _ hr, hG.evalReg_fc _ hr]
  have e : γ / 2 * (G (foldH (t : ℂ), r) + c) = γ / 2 * G (foldH (t : ℂ), r) + γ * c / 2 := by
    ring
  rw [e, Real.exp_add]
  ring

/-- **Constants, local**: `ν_{x+c} = e^{γc/2} ν_x` on `U`. -/
theorem HasBdryLimitOn.addConst (hx : IsRegularSample x) {U : Set ℝ} {ν : Measure ℝ}
    (h : HasBdryLimitOn γ x U ν) (c : ℝ) :
    HasBdryLimitOn γ (addConst x c) U (ENNReal.ofReal (Real.exp (γ * c / 2)) • ν) := by
  obtain ⟨F, hF⟩ := hx
  obtain ⟨h0, hK, ht⟩ := h
  refine ⟨by rw [Measure.smul_apply, h0, smul_zero], fun K hKc hKU => ?_, fun f hf hfc hfU => ?_⟩
  · rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hK K hKc hKU)
  · rw [integral_smul_measure]
    refine ((ht f hf hfc hfU).const_smul _).congr' (eventually_goodRad_pos.mono fun i hi => ?_)
    show _ = ∫ t, f t ∂bdryR γ (QuantumZipper.addConst x c) (goodRad i)
    rw [bdryR_addConst_loc hF c hi, integral_smul_measure]

/-- **Constants preserve goodness off a set.** -/
theorem IsLQGGoodOff.addConst {S : Set ℝ} (hx : IsLQGGoodOff γ x S) (c : ℝ) :
    IsLQGGoodOff γ (addConst x c) S := by
  obtain ⟨hr, ⟨ν, hν⟩, ⟨μ, hμ⟩⟩ := hx
  refine ⟨hr.addConst' c, ⟨_, hν.addConst hr c⟩, ?_⟩
  rw [addConst_eq_add_ofFun]
  exact ⟨_, hasAreaLimit_add_ofFun hr hμ continuousOn_const⟩

/-- **Open-arc length, constants**: exact, with no convergence assumption. -/
theorem arcLen_addConst (hx : RawConverges x Hbar) (c a b : ℝ) :
    arcLen γ (addConst x c) a b = ENNReal.ofReal (Real.exp (γ * c / 2)) * arcLen γ x a b := by
  unfold arcLen
  rw [qBoundaryMeasureOn_addConst hx γ c isOpen_Ioo, Measure.smul_apply, smul_eq_mul]

/-! ## 3. Adding a function continuous near `U` -/

/-- Locality of `bdryDens`: if `φ' = φ` on the `δ`-thickening of `Kc`, then at radii `r < δ/2`
the boundary densities of `x + φ` and `x + φ'` agree at points of `Kc`. -/
theorem bdryDens_add_ofFun_local {φ φ' : ℂ → ℝ} {Kc : Set ℂ} {δ : ℝ}
    (heq : EqOn φ' φ (Metric.cthickening δ Kc)) {t : ℝ} (ht : (t : ℂ) ∈ Kc) {r : ℝ}
    (hr : 0 < r) (hrδ : r < δ / 2) :
    bdryDens γ (x + ofFun φ) r t = bdryDens γ (x + ofFun φ') r t := by
  have hrad : ∀ᶠ k in atTop, radius k < δ / 4 :=
    (tendsto_radius_nhdsGT.mono_right nhdsWithin_le_nhds).eventually
      (gt_mem_nhds (by linarith))
  have hev : (fun k => ∫ w, avgReg (x + ofFun φ) k w ∂foldedCircle (t : ℂ) r) =ᶠ[atTop]
      (fun k => ∫ w, avgReg (x + ofFun φ') k w ∂foldedCircle (t : ℂ) r) := by
    filter_upwards [hrad] with k hk
    refine integral_congr_ae ?_
    filter_upwards [ae_fc_mem_closedBall (ofReal_mem_Hbar t) hr, fc_ae_mem_Hbar (t : ℂ) r]
      with w hw hwH
    refine avgReg_congr_local k (ρ := δ / 4) (by linarith) (fun c hc hcw => ?_) hwH
    simp only [Pi.add_apply]
    rw [ofFun_fc_congr hc (radius_pos k) (fun u hu => ?_)]
    have h1 := Metric.mem_closedBall.1 hu
    have h2 := Metric.mem_closedBall.1 hw
    have hut : dist u (t : ℂ) ≤ δ := by
      have := dist_triangle4 u c w (t : ℂ)
      linarith
    exact (heq (Metric.mem_cthickening_of_dist_le u _ δ Kc ht hut)).symm
  have he : evalReg (x + ofFun φ) (foldedCircle (t : ℂ) r) =
      evalReg (x + ofFun φ') (foldedCircle (t : ℂ) r) := by
    unfold evalReg limUnder
    rw [Filter.map_congr hev]
  unfold bdryDens
  rw [he]

/-- **Rule (5.1), local** (copy of `GoodSample.hasBdryLimit_add_ofFun`, localized as
`LocalRule.isVagueLimitOnR_add_ofFun`): for `φ` continuous on `W ∩ Hbar` with `W ⊇ U` open,
`ν_{x+φ} = e^{γφ/2} ν_x` on `U`. -/
theorem HasBdryLimitOn.add_ofFun (hx : IsRegularSample x) {U : Set ℝ} (hU : IsOpen U)
    {ν : Measure ℝ} (h : HasBdryLimitOn γ x U ν) {φ : ℂ → ℝ} {W : Set ℂ} (hW : IsOpen W)
    (hUW : ∀ t ∈ U, (t : ℂ) ∈ W) (hφ : ContinuousOn φ (W ∩ Hbar)) :
    HasBdryLimitOn γ (x + ofFun φ) U
      (ν.withDensity fun t => ENNReal.ofReal (Real.exp (γ / 2 * φ t))) := by
  obtain ⟨F, hF⟩ := hx
  obtain ⟨h0, hK, ht⟩ := h
  have hcont : ContinuousOn (fun t : ℝ => γ / 2 * φ t) U :=
    continuousOn_const.mul (hφ.comp Complex.continuous_ofReal.continuousOn
      fun t ht => ⟨hUW t ht, ofReal_mem_Hbar t⟩)
  refine ⟨withDensity_absolutelyContinuous _ _ h0,
    fun K hKc hKU => withDensity_lt_top hKc (hK K hKc hKU) (hcont.rexp.mono hKU),
    fun f hf hfc hfU => ?_⟩
  rw [integral_withDensity_exp_of_continuousOn hU h0 hcont]
  set L := tsupport f with hLdef
  have hL : IsCompact L := hfc
  have hLm : MeasurableSet L := hL.isClosed.measurableSet
  set Lc : Set ℂ := (fun t : ℝ => (t : ℂ)) '' L with hLcdef
  have hLc : IsCompact Lc := hL.image Complex.continuous_ofReal
  have hLcW : Lc ⊆ W := by rintro _ ⟨t, ht, rfl⟩; exact hUW t (hfU ht)
  obtain ⟨δ, hδ, φ', hφ', heq⟩ := exists_cutoff hW hφ hLc hLcW
  have hsmall : ∀ᶠ i in goodFilter, goodRad i < δ / 2 :=
    (tendsto_goodRad.mono_right nhdsWithin_le_nhds).eventually (gt_mem_nhds (by linarith))
  have hoff : ∀ t ∉ L, f t = 0 := fun t ht => image_eq_zero_of_notMem_tsupport ht
  have hid : ∀ᶠ i in goodFilter,
      ∫ t, Real.exp (γ / 2 * smoothFun φ' t (goodRad i)) * f t ∂bdryR γ x (goodRad i) =
        ∫ t, f t ∂bdryR γ (x + ofFun φ) (goodRad i) := by
    filter_upwards [eventually_goodRad_pos, hsmall] with i hi hiδ
    have hs : ∀ μ : Measure ℝ, ∫ t in L, f t ∂μ = ∫ t, f t ∂μ := fun μ =>
      setIntegral_eq_integral_of_forall_compl_eq_zero hoff
    have hmeq : (bdryR γ (x + ofFun φ') (goodRad i)).restrict L =
        (bdryR γ (x + ofFun φ) (goodRad i)).restrict L := by
      unfold bdryR
      rw [restrict_withDensity hLm, restrict_withDensity hLm]
      refine withDensity_congr_ae ?_
      filter_upwards [ae_restrict_mem hLm] with t htL
      rw [bdryDens_add_ofFun_local heq ⟨t, htL, rfl⟩ hi hiδ]
    rw [← integral_bdryR_add_ofFun γ hF hφ' hi f, ← hs (bdryR γ (x + ofFun φ') (goodRad i)),
      ← hs (bdryR γ (x + ofFun φ) (goodRad i)), hmeq]
  have key := tendsto_integral_exp_mul (L := goodFilter) hU
    (νs := fun i => bdryR γ x (goodRad i)) (ν := ν)
    (eventually_goodRad_pos.mono fun i hi K hK _ => bdryR_lt_top γ hF hi hK) ht
    (v := fun i t => γ / 2 * smoothFun φ' t (goodRad i)) (v0 := fun t => γ / 2 * φ' t)
    (continuous_const.mul (continuous_ofReal_comp hφ')).continuousOn
    (Eventually.of_forall fun i => (continuous_const.mul
      ((continuous_smoothFun hφ' _).comp Complex.continuous_ofReal)).continuousOn)
    (fun K hK _ ε hε => by
      have := smooth_unif_good hφ' (γ / 2) (hK.image Complex.continuous_ofReal)
        (fun _ ⟨t, _, ht⟩ => ht ▸ ofReal_mem_Hbar t) ε hε
      filter_upwards [this] with i hi t ht
      exact hi _ ⟨t, ht, rfl⟩)
    hf hfc hfU
  have hlim : ∫ t, Real.exp (γ / 2 * φ' t) * f t ∂ν = ∫ t, Real.exp (γ / 2 * φ t) * f t ∂ν := by
    congr 1
    funext t
    by_cases htL : t ∈ L
    · rw [heq (Metric.self_subset_cthickening _ ⟨t, htL, rfl⟩)]
    · rw [hoff t htL, mul_zero, mul_zero]
  rw [← hlim]
  exact key.congr' hid

/-! ## 4. Congruence -/

/-- Local limits only read the approximate measures `bdryR` at positive radii. -/
theorem hasBdryLimitOn_congr {y : FieldSample} (h : ∀ r, 0 < r → bdryR γ x r = bdryR γ y r)
    {U : Set ℝ} {ν : Measure ℝ} : HasBdryLimitOn γ x U ν ↔ HasBdryLimitOn γ y U ν := by
  have key : ∀ f : ℝ → ℝ, (fun i => ∫ t, f t ∂bdryR γ x (goodRad i)) =ᶠ[goodFilter]
      (fun i => ∫ t, f t ∂bdryR γ y (goodRad i)) := fun f =>
    eventually_goodRad_pos.mono fun i hi => by simp only [h _ hi]
  constructor
  · rintro ⟨h0, hK, ht⟩
    exact ⟨h0, hK, fun f hf hfc hfU => (tendsto_congr' (key f)).1 (ht f hf hfc hfU)⟩
  · rintro ⟨h0, hK, ht⟩
    exact ⟨h0, hK, fun f hf hfc hfU => (tendsto_congr' (key f)).2 (ht f hf hfc hfU)⟩

/-- Local limits only read `avgReg` (copy of `bdryR_congr_avg`, G1Z5Bm.lean). -/
theorem hasBdryLimitOn_congr_avg {y : FieldSample} (h : avgReg x = avgReg y) {U : Set ℝ}
    {ν : Measure ℝ} : HasBdryLimitOn γ x U ν ↔ HasBdryLimitOn γ y U ν :=
  hasBdryLimitOn_congr fun r _ => by unfold bdryR bdryDens evalReg; rw [h]

/-- Open-arc lengths only read `avgReg` (as `Factorization.qBoundaryMeasure_congr`). -/
theorem arcLen_congr {y : FieldSample} (h : avgReg x = avgReg y) (a b : ℝ) :
    arcLen γ x a b = arcLen γ y a b := by
  unfold arcLen qBoundaryMeasureOn bdryApprox
  rw [h]

end LocLen
end QuantumZipper
