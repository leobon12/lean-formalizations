import QuantumZipper.Proofs.LQG.PositivityArea
import QuantumZipper.LQG.Local

/-!
# Local rule (5.1) along the dyadic radii

The transformation rule for adding a continuous function, localized to an open set and along the
dyadic radii `2^{-k}` only, **without** `IsLQGGood` (compare `GoodSample.qBoundaryMeasure_add_ofFun`,
which needs the uniform-in-offset limits and the area limit).

* `isVagueLimitOnR_add_ofFun`: `x` regular, `bdryApprox γ x → ν` vaguely on an open `U ⊆ ℝ`,
  `φ` continuous on `W ∩ Hbar` for an open `W ⊇ U`: then `bdryApprox γ (x + ofFun φ) → e^{γφ/2} ν`
  vaguely on `U`. `isVagueLimitR_add_ofFun` is the case `U = ℝ`.
* `isVagueLimitOn_add_ofFun`: the same for `areaApprox` on an open `U ⊆ H`, density `e^{γφ}`.
  (`continuousOn_of_local` turns "continuous on a neighbourhood in `Hbar` of every point" into
  the `W` form.)
* Constants: `bdryApprox_addConst`, `areaApprox_addConst` (exact, whenever the raw dyadic circle
  averages converge, e.g. for regular samples) and the identities for `qBoundaryMeasure`,
  `qBoundaryMeasureOn`, `qAreaMeasure`, `qAreaMeasureOn`.
* Corollaries for `qBoundaryMeasureOn`, `qAreaMeasureOn`, `qBoundaryMeasure`, `qAreaMeasure` of
  `x + ofFun φ`.

Route: on a compact `K ⊆ U`, replace `φ` by a cutoff `φ'` continuous on `Hbar` and equal to `φ`
on a thickening of `K`; for `2^{-k}` small the dyadic circle averages of `x + ofFun φ` and
`x + ofFun φ'` agree near `K`, the densities differ from those of `x` by `e^{γ ∫ φ' dfc/2}`, which
converges to `e^{γφ/2}` uniformly on `K`, and `GoodSample.tendsto_integral_exp_mul` concludes.

Note on constants: the statement "exactly for every `x`" is false with the junk convention of
`limUnder`: if the raw values `x(fc(d_n z, 2^{-k}))` diverge for every `z`, then
`avgReg (addConst x c) = avgReg x` (both are the same junk constant), so
`bdryApprox γ (addConst x c) = bdryApprox γ x ≠ e^{γc/2} • bdryApprox γ x` for `c ≠ 0`. We
therefore assume the raw averages converge (true for regular samples).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace LocalRule

open GoodSample Positivity GaussTK

/-! ### Folded circles near their centre, and local congruence of `avgReg` -/

theorem ae_fc_mem_closedBall {c : ℂ} (hc : c ∈ Hbar) {r : ℝ} (hr : 0 < r) :
    ∀ᵐ u ∂foldedCircle c r, u ∈ Metric.closedBall c r := by
  unfold foldedCircle
  refine (ae_map_iff measurable_foldH.aemeasurable
    (measurableSet_closedBall (x := c) (ε := r))).2 ?_
  filter_upwards [KernelId.ae_norm_sub_center c hr] with u hu
  rw [dist_eq_norm]
  calc ‖foldH u - c‖ = ‖foldH u - foldH c‖ := by rw [CircleFubini.foldH_of_mem' hc]
    _ ≤ ‖u - c‖ := RegSample.norm_foldH_sub_le u c
    _ = r := hu

theorem ofFun_fc_congr {φ ψ : ℂ → ℝ} {c : ℂ} (hc : c ∈ Hbar) {r : ℝ} (hr : 0 < r)
    (h : EqOn φ ψ (Metric.closedBall c r)) :
    ofFun φ (foldedCircle c r) = ofFun ψ (foldedCircle c r) := by
  unfold ofFun
  exact integral_congr_ae ((ae_fc_mem_closedBall hc hr).mono fun u hu => h hu)

theorem avgReg_congr_local {x y : FieldSample} (k : ℕ) {z : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (h : ∀ c ∈ Hbar, dist c z < ρ →
      x (foldedCircle c (radius k)) = y (foldedCircle c (radius k)))
    (hz : z ∈ Hbar) : avgReg x k z = avgReg y k z := by
  unfold avgReg
  have hev : (fun n => x (foldedCircle (dyadicRoundC n z) (radius k))) =ᶠ[atTop]
      (fun n => y (foldedCircle (dyadicRoundC n z) (radius k))) := by
    filter_upwards [(RegClosure.tendsto_dyadicRoundC z).eventually (Metric.ball_mem_nhds z hρ)]
      with n hn
    exact h _ (dyadicRoundC_mem_Hbar n hz) hn
  unfold limUnder
  rw [Filter.map_congr hev]

/-! ### Cutoff of a locally continuous function -/

theorem exists_cutoff {W : Set ℂ} (hW : IsOpen W) {φ : ℂ → ℝ} (hφ : ContinuousOn φ (W ∩ Hbar))
    {Kc : Set ℂ} (hK : IsCompact Kc) (hKW : Kc ⊆ W) :
    ∃ δ > 0, ∃ φ' : ℂ → ℝ, ContinuousOn φ' Hbar ∧ EqOn φ' φ (Metric.cthickening δ Kc) := by
  classical
  obtain ⟨δ, hδ, hδW⟩ := hK.exists_cthickening_subset_open hW hKW
  have hN : IsCompact (Metric.cthickening (δ / 2) Kc) := hK.cthickening
  have hNW : Metric.cthickening (δ / 2) Kc ⊆ W :=
    (Metric.cthickening_mono (by linarith) _).trans hδW
  obtain ⟨χ, hχc, -, hχW, hχ1, -⟩ := exists_bump hN hW hNW
  refine ⟨δ / 2, by linarith, fun u => if u ∈ W then χ u * φ u else 0, ?_, ?_⟩
  · intro u hu
    by_cases huW : u ∈ W
    · have h1 : ContinuousWithinAt φ (W ∩ Hbar) u := hφ u ⟨huW, hu⟩
      have h2 : ContinuousWithinAt φ Hbar u :=
        h1.mono_of_mem_nhdsWithin (inter_mem (mem_nhdsWithin_of_mem_nhds (hW.mem_nhds huW))
          self_mem_nhdsWithin)
      have hcw : ContinuousWithinAt (fun v => χ v * φ v) Hbar u :=
        hχc.continuousWithinAt.mul h2
      refine hcw.congr_of_eventuallyEq ?_ (by simp [huW])
      filter_upwards [mem_nhdsWithin_of_mem_nhds (hW.mem_nhds huW)] with v hv
      simp [hv]
    · have hu' : u ∉ tsupport χ := fun h => huW (hχW h)
      refine (continuousWithinAt_const (b := (0 : ℝ))).congr_of_eventuallyEq ?_ (by simp [huW])
      filter_upwards [mem_nhdsWithin_of_mem_nhds
        ((isClosed_tsupport χ).isOpen_compl.mem_nhds hu')] with v hv
      by_cases hvW : v ∈ W
      · simp [hvW, image_eq_zero_of_notMem_tsupport hv]
      · simp [hvW]
  · intro u hu
    have huW : u ∈ W := hNW hu
    have h1 : χ u = 1 := by simpa using hχ1 hu
    simp [huW, h1]

/-! ### The local rule on `ℝ` -/

theorem tendsto_integral_bdryApprox_add_ofFun {x : FieldSample} {F : ℂ × ℝ → ℝ}
    (hF : IsRegularWith x F) (γ : ℝ) {U : Set ℝ} (hU : IsOpen U) {ν : Measure ℝ}
    (hν : ∀ f : ℝ → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ U →
      Tendsto (fun k => ∫ t, f t ∂bdryApprox γ x k) atTop (𝓝 (∫ t, f t ∂ν)))
    {φ : ℂ → ℝ} {W : Set ℂ} (hW : IsOpen W) (hUW : ∀ t ∈ U, (t : ℂ) ∈ W)
    (hφ : ContinuousOn φ (W ∩ Hbar)) {f : ℝ → ℝ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (hfU : tsupport f ⊆ U) :
    Tendsto (fun k => ∫ t, f t ∂bdryApprox γ (x + ofFun φ) k) atTop
      (𝓝 (∫ t, Real.exp (γ / 2 * φ t) * f t ∂ν)) := by
  set K := tsupport f with hKdef
  have hK : IsCompact K := hfc
  set Kc : Set ℂ := (fun t : ℝ => (t : ℂ)) '' K with hKcdef
  have hKc : IsCompact Kc := hK.image Complex.continuous_ofReal
  have hKcW : Kc ⊆ W := by rintro _ ⟨t, ht, rfl⟩; exact hUW t (hfU ht)
  obtain ⟨δ, hδ, φ', hφ', heq⟩ := exists_cutoff hW hφ hKc hKcW
  have hF' := gs_add_ofFun hF hφ'
  have hrad : ∀ᶠ k in atTop, radius k < δ / 2 :=
    (RegClosure.tendsto_radius_nhdsGT.mono_right nhdsWithin_le_nhds).eventually
      (gt_mem_nhds (by linarith))
  -- agreement of the averages near `K`
  have havg : ∀ k, radius k < δ / 2 → ∀ t ∈ K,
      avgReg (x + ofFun φ) k t = avgReg x k t + smoothFun φ' (t : ℂ) (radius k) := by
    intro k hk t ht
    have htK : (t : ℂ) ∈ Kc := ⟨t, ht, rfl⟩
    have e1 : avgReg (x + ofFun φ) k t = avgReg (x + ofFun φ') k t := by
      refine avgReg_congr_local k (by linarith : 0 < δ / 2) (fun c hc hct => ?_)
        (ofReal_mem_Hbar t)
      simp only [Pi.add_apply]
      rw [ofFun_fc_congr hc (radius_pos k) (fun u hu => ?_)]
      have hut : dist u (t : ℂ) ≤ δ := by
        have := dist_triangle u c (t : ℂ)
        have := Metric.mem_closedBall.1 hu
        linarith
      exact (heq (Metric.mem_cthickening_of_dist_le u _ δ Kc htK hut)).symm
    rw [e1, hF'.avgReg_eq k (ofReal_mem_Hbar t), hF.avgReg_eq k (ofReal_mem_Hbar t)]
    rfl
  -- the integral identity
  have hm : ∀ (y : FieldSample) (k : ℕ), Measurable fun t : ℝ =>
      radius k ^ (γ ^ 2 / 4) * Real.exp (γ / 2 * avgReg y k t) := fun y k =>
    measurable_const.mul (((RegClosure.measurable_avgReg_slice y k).comp
      Complex.continuous_ofReal.measurable).const_mul _).exp
  have hd0 : ∀ (y : FieldSample) (k : ℕ) (t : ℝ),
      0 ≤ radius k ^ (γ ^ 2 / 4) * Real.exp (γ / 2 * avgReg y k t) := fun y k t =>
    mul_nonneg (Real.rpow_nonneg (radius_pos k).le _) (Real.exp_pos _).le
  have hid : ∀ᶠ k in atTop, ∫ t, Real.exp (γ / 2 * smoothFun φ' (t : ℂ) (radius k)) * f t
      ∂bdryApprox γ x k = ∫ t, f t ∂bdryApprox γ (x + ofFun φ) k := by
    filter_upwards [hrad] with k hk
    unfold bdryApprox
    rw [integral_withDensity_ofReal (hm _ k) (hd0 _ k), integral_withDensity_ofReal (hm _ k)
      (hd0 _ k)]
    congr 1
    funext t
    by_cases ht : t ∈ K
    · rw [havg k hk t ht, mul_add, Real.exp_add]; ring
    · rw [image_eq_zero_of_notMem_tsupport ht]; ring
  -- apply the exponential-weight lemma
  have key := tendsto_integral_exp_mul (L := atTop) hU (νs := bdryApprox γ x) (ν := ν)
    (Eventually.of_forall fun k K' hK' _ => by
      rw [← bdryR_radius γ hF k]
      exact bdryR_lt_top γ hF (by rw [one_mul]; exact radius_pos k) hK')
    hν (v := fun k t => γ / 2 * smoothFun φ' (t : ℂ) (radius k))
    (v0 := fun t => γ / 2 * φ' t)
    (continuous_const.mul (continuous_ofReal_comp hφ')).continuousOn
    (Eventually.of_forall fun k => (continuous_const.mul
      ((continuous_smoothFun hφ' _).comp Complex.continuous_ofReal)).continuousOn)
    (fun K' hK' _ ε hε => by
      have hu := smooth_unif hφ' (hK'.image Complex.continuous_ofReal)
        (fun _ ⟨t, _, ht⟩ => ht ▸ ofReal_mem_Hbar t) (ε / (|γ / 2| + 1)) (by positivity)
      filter_upwards [RegClosure.tendsto_radius_nhdsGT.eventually hu] with k hk t ht
      have h1 := hk _ ⟨t, ht, rfl⟩
      rw [← mul_sub, abs_mul]
      calc |γ / 2| * |smoothFun φ' (t : ℂ) (radius k) - φ' t|
          ≤ |γ / 2| * (ε / (|γ / 2| + 1)) := mul_le_mul_of_nonneg_left h1.le (abs_nonneg _)
        _ < ε := by
          rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
          nlinarith [abs_nonneg (γ / 2)])
    hf hfc hfU
  have hlim : ∫ t, Real.exp (γ / 2 * φ' t) * f t ∂ν = ∫ t, Real.exp (γ / 2 * φ t) * f t ∂ν := by
    congr 1
    funext t
    by_cases ht : t ∈ K
    · rw [heq (Metric.self_subset_cthickening _ ⟨t, ht, rfl⟩)]
    · rw [image_eq_zero_of_notMem_tsupport ht, mul_zero, mul_zero]
  rw [← hlim]
  exact key.congr' hid

theorem integral_withDensity_exp_of_continuousOn {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] {U : Set X} (hU : IsOpen U) {ν : Measure X}
    (h0 : ν Uᶜ = 0) {w : X → ℝ} (hw : ContinuousOn w U) (f : X → ℝ) :
    ∫ t, f t ∂ν.withDensity (fun t => ENNReal.ofReal (Real.exp (w t))) =
      ∫ t, Real.exp (w t) * f t ∂ν := by
  have hr : ν.restrict U = ν := Measure.restrict_eq_self_of_ae_mem (by rw [ae_iff]; exact h0)
  have hm : AEMeasurable (fun t => ENNReal.ofReal (Real.exp (w t))) ν := by
    rw [← hr]
    exact ENNReal.measurable_ofReal.comp_aemeasurable
      (hw.rexp.aemeasurable hU.measurableSet)
  rw [integral_withDensity_eq_integral_toReal_smul₀ hm
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  congr 1
  funext t
  rw [ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul]

/-- **Local rule (5.1), boundary, along the dyadic radii.** -/
theorem isVagueLimitOnR_add_ofFun {x : FieldSample} (hx : IsRegularSample x) {γ : ℝ}
    {U : Set ℝ} (hU : IsOpen U) {ν : Measure ℝ} (hν : IsVagueLimitOnR U (bdryApprox γ x) ν)
    {φ : ℂ → ℝ} {W : Set ℂ} (hW : IsOpen W) (hUW : ∀ t ∈ U, (t : ℂ) ∈ W)
    (hφ : ContinuousOn φ (W ∩ Hbar)) :
    IsVagueLimitOnR U (bdryApprox γ (x + ofFun φ))
      (ν.withDensity fun t => ENNReal.ofReal (Real.exp (γ / 2 * φ t))) := by
  obtain ⟨F, hF⟩ := hx
  obtain ⟨h0, hK, ht⟩ := hν
  have hcont : ContinuousOn (fun t : ℝ => γ / 2 * φ t) U :=
    continuousOn_const.mul (hφ.comp Complex.continuous_ofReal.continuousOn
      fun t ht => ⟨hUW t ht, ofReal_mem_Hbar t⟩)
  refine ⟨withDensity_absolutelyContinuous _ _ h0, fun K hKc hKU => ?_, fun f hf hfc hfU => ?_⟩
  · exact withDensity_lt_top hKc (hK K hKc hKU) (hcont.rexp.mono hKU)
  · rw [integral_withDensity_exp_of_continuousOn hU h0 hcont]
    exact tendsto_integral_bdryApprox_add_ofFun hF γ hU ht hW hUW hφ hf hfc hfU

theorem isVagueLimitOnR_univ_iff {νs : ℕ → Measure ℝ} {ν : Measure ℝ} :
    IsVagueLimitOnR univ νs ν ↔ IsVagueLimitR νs ν := by
  constructor
  · intro h
    have : IsFiniteMeasureOnCompacts ν := ⟨fun K hK => h.2.1 K hK (subset_univ _)⟩
    exact ⟨inferInstance, fun f hf hfc => h.2.2 f hf hfc (subset_univ _)⟩
  · intro h
    have := h.1
    exact ⟨by simp, fun K hK _ => hK.measure_lt_top, fun f hf hfc _ => h.2 f hf hfc⟩

/-- **Local rule (5.1), boundary, `U = ℝ`.** -/
theorem isVagueLimitR_add_ofFun {x : FieldSample} (hx : IsRegularSample x) {γ : ℝ}
    {ν : Measure ℝ} (hν : IsVagueLimitR (bdryApprox γ x) ν) {φ : ℂ → ℝ} {W : Set ℂ}
    (hW : IsOpen W) (hUW : ∀ t : ℝ, (t : ℂ) ∈ W) (hφ : ContinuousOn φ (W ∩ Hbar)) :
    IsVagueLimitR (bdryApprox γ (x + ofFun φ))
      (ν.withDensity fun t => ENNReal.ofReal (Real.exp (γ / 2 * φ t))) :=
  isVagueLimitOnR_univ_iff.1 (isVagueLimitOnR_add_ofFun hx isOpen_univ
    (isVagueLimitOnR_univ_iff.2 hν) hW (fun t _ => hUW t) hφ)

/-! ### The local rule on `H` -/

theorem tendsto_integral_areaApprox_add_ofFun {x : FieldSample} {F : ℂ × ℝ → ℝ}
    (hF : IsRegularWith x F) (γ : ℝ) {U : Set ℂ} (hU : IsOpen U) (hUH : U ⊆ H)
    {μ : Measure ℂ}
    (hμ : ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ U →
      Tendsto (fun k => ∫ z, f z ∂areaApprox γ x k) atTop (𝓝 (∫ z, f z ∂μ)))
    {φ : ℂ → ℝ} {W : Set ℂ} (hW : IsOpen W) (hUW : U ⊆ W)
    (hφ : ContinuousOn φ (W ∩ Hbar)) {f : ℂ → ℝ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (hfU : tsupport f ⊆ U) :
    Tendsto (fun k => ∫ z, f z ∂areaApprox γ (x + ofFun φ) k) atTop
      (𝓝 (∫ z, Real.exp (γ * φ z) * f z ∂μ)) := by
  set K := tsupport f with hKdef
  have hK : IsCompact K := hfc
  obtain ⟨δ, hδ, φ', hφ', heq⟩ := exists_cutoff hW hφ hK (hfU.trans hUW)
  have hF' := gs_add_ofFun hF hφ'
  have hUHb : U ⊆ Hbar := hUH.trans H_subset_Hbar
  have hrad : ∀ᶠ k in atTop, radius k < δ / 2 :=
    (RegClosure.tendsto_radius_nhdsGT.mono_right nhdsWithin_le_nhds).eventually
      (gt_mem_nhds (by linarith))
  have havg : ∀ k, radius k < δ / 2 → ∀ z ∈ K,
      avgReg (x + ofFun φ) k z = avgReg x k z + smoothFun φ' z (radius k) := by
    intro k hk z hz
    have hzH : z ∈ Hbar := hUHb (hfU hz)
    have e1 : avgReg (x + ofFun φ) k z = avgReg (x + ofFun φ') k z := by
      refine avgReg_congr_local k (by linarith : 0 < δ / 2) (fun c hc hcz => ?_) hzH
      simp only [Pi.add_apply]
      rw [ofFun_fc_congr hc (radius_pos k) (fun u hu => ?_)]
      have huz : dist u z ≤ δ := by
        have := dist_triangle u c z
        have := Metric.mem_closedBall.1 hu
        linarith
      exact (heq (Metric.mem_cthickening_of_dist_le u _ δ K hz huz)).symm
    rw [e1, hF'.avgReg_eq k hzH, hF.avgReg_eq k hzH]
    rfl
  have hm : ∀ (y : FieldSample) (k : ℕ), Measurable fun z : ℂ =>
      radius k ^ (γ ^ 2 / 2) * Real.exp (γ * avgReg y k z) := fun y k =>
    measurable_const.mul ((RegClosure.measurable_avgReg_slice y k).const_mul _).exp
  have hd0 : ∀ (y : FieldSample) (k : ℕ) (z : ℂ),
      0 ≤ radius k ^ (γ ^ 2 / 2) * Real.exp (γ * avgReg y k z) := fun y k z =>
    mul_nonneg (Real.rpow_nonneg (radius_pos k).le _) (Real.exp_pos _).le
  have hid : ∀ᶠ k in atTop, ∫ z, Real.exp (γ * smoothFun φ' z (radius k)) * f z
      ∂areaApprox γ x k = ∫ z, f z ∂areaApprox γ (x + ofFun φ) k := by
    filter_upwards [hrad] with k hk
    unfold areaApprox
    rw [integral_withDensity_ofReal (hm _ k) (hd0 _ k), integral_withDensity_ofReal (hm _ k)
      (hd0 _ k)]
    congr 1
    funext z
    by_cases hz : z ∈ K
    · rw [havg k hk z hz, mul_add, Real.exp_add]; ring
    · rw [image_eq_zero_of_notMem_tsupport hz]; ring
  have key := tendsto_integral_exp_mul (L := atTop) hU (νs := areaApprox γ x) (ν := μ)
    (Eventually.of_forall fun k K' hK' _ => by
      rw [← areaR_radius γ hF k]
      exact areaR_lt_top γ hF (by rw [one_mul]; exact radius_pos k) hK')
    hμ (v := fun k z => γ * smoothFun φ' z (radius k)) (v0 := fun z => γ * φ' z)
    (continuousOn_const.mul (hφ'.mono hUHb))
    (Eventually.of_forall fun k =>
      (continuous_const.mul (continuous_smoothFun hφ' _)).continuousOn)
    (fun K' hK' hK'U ε hε => by
      have hu := smooth_unif hφ' hK' (hK'U.trans hUHb) (ε / (|γ| + 1)) (by positivity)
      filter_upwards [RegClosure.tendsto_radius_nhdsGT.eventually hu] with k hk z hz
      have h1 := hk z hz
      rw [← mul_sub, abs_mul]
      calc |γ| * |smoothFun φ' z (radius k) - φ' z|
          ≤ |γ| * (ε / (|γ| + 1)) := mul_le_mul_of_nonneg_left h1.le (abs_nonneg _)
        _ < ε := by
          rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
          nlinarith [abs_nonneg γ])
    hf hfc hfU
  have hlim : ∫ z, Real.exp (γ * φ' z) * f z ∂μ = ∫ z, Real.exp (γ * φ z) * f z ∂μ := by
    congr 1
    funext z
    by_cases hz : z ∈ K
    · rw [heq (Metric.self_subset_cthickening _ hz)]
    · rw [image_eq_zero_of_notMem_tsupport hz, mul_zero, mul_zero]
  rw [← hlim]
  exact key.congr' hid

/-- **Local rule (5.1), area, along the dyadic radii.** -/
theorem isVagueLimitOn_add_ofFun {x : FieldSample} (hx : IsRegularSample x) {γ : ℝ}
    {U : Set ℂ} (hU : IsOpen U) (hUH : U ⊆ H) {μ : Measure ℂ}
    (hμ : IsVagueLimitOn U (areaApprox γ x) μ) {φ : ℂ → ℝ} {W : Set ℂ} (hW : IsOpen W)
    (hUW : U ⊆ W) (hφ : ContinuousOn φ (W ∩ Hbar)) :
    IsVagueLimitOn U (areaApprox γ (x + ofFun φ))
      (μ.withDensity fun z => ENNReal.ofReal (Real.exp (γ * φ z))) := by
  obtain ⟨F, hF⟩ := hx
  obtain ⟨h0, hK, ht⟩ := hμ
  have hcont : ContinuousOn (fun z : ℂ => γ * φ z) U :=
    continuousOn_const.mul (hφ.mono fun z hz => ⟨hUW hz, H_subset_Hbar (hUH hz)⟩)
  refine ⟨withDensity_absolutelyContinuous _ _ h0, fun K hKc hKU => ?_, fun f hf hfc hfU => ?_⟩
  · exact withDensity_lt_top hKc (hK K hKc hKU) (hcont.rexp.mono hKU)
  · rw [integral_withDensity_exp_of_continuousOn hU h0 hcont]
    exact tendsto_integral_areaApprox_add_ofFun hF γ hU hUH ht hW hUW hφ hf hfc hfU

/-! ### Uniqueness of local vague limits on `ℝ` -/

theorem isVagueLimitOnR_unique {U : Set ℝ} (hU : IsOpen U) {μs : ℕ → Measure ℝ}
    {μ μ' : Measure ℝ} (h : IsVagueLimitOnR U μs μ) (h' : IsVagueLimitOnR U μs μ') :
    μ = μ' := by
  obtain ⟨h0, hK, ht⟩ := h
  obtain ⟨h0', hK', ht'⟩ := h'
  have hUm : MeasurableSet U := hU.measurableSet
  have hr : μ.restrict U = μ := Measure.restrict_eq_self_of_ae_mem (by
    rw [ae_iff]; exact h0)
  have hr' : μ'.restrict U = μ' := Measure.restrict_eq_self_of_ae_mem (by
    rw [ae_iff]; exact h0')
  have : LocallyCompactSpace U := hU.locallyCompactSpace
  let ν : Measure U := Measure.comap Subtype.val μ
  let ν' : Measure U := Measure.comap Subtype.val μ'
  have : IsFiniteMeasureOnCompacts ν := ⟨fun K hKc => by
    rw [comap_subtype_coe_apply hUm]
    exact hK _ (hKc.image continuous_subtype_val) (Subtype.coe_image_subset _ _)⟩
  have : IsFiniteMeasureOnCompacts ν' := ⟨fun K hKc => by
    rw [comap_subtype_coe_apply hUm]
    exact hK' _ (hKc.image continuous_subtype_val) (Subtype.coe_image_subset _ _)⟩
  have hνν' : ν = ν' := by
    refine Measure.ext_of_integral_eq_on_compactlySupported fun g => ?_
    set G : ℝ → ℝ := Subtype.val.extend g 0
    have hGc : Continuous G := HasCompactSupport.continuous_extend_zero hU
      (map_continuous g) g.hasCompactSupport
    have hGs : HasCompactSupport G := g.hasCompactSupport.extend_zero continuous_subtype_val
    have hGU : tsupport G ⊆ U :=
      (g.hasCompactSupport.tsupport_extend_zero_subset continuous_subtype_val).trans
        (Subtype.coe_image_subset _ _)
    have key : ∀ m : Measure ℝ,
        ∫ z, G z ∂(m.restrict U) = ∫ x, g x ∂(Measure.comap Subtype.val m) := by
      intro m
      rw [← integral_subtype_comap hUm]
      simp_rw [G, Subtype.val_injective.extend_apply]
    have e1 := key μ
    have e2 := key μ'
    rw [hr] at e1
    rw [hr'] at e2
    rw [← e1, ← e2]
    exact tendsto_nhds_unique (ht G hGc hGs hGU) (ht' G hGc hGs hGU)
  rw [← hr, ← hr', ← map_comap_subtype_coe hUm, ← map_comap_subtype_coe hUm]
  exact congrArg (Measure.map Subtype.val) hνν'

theorem qBoundaryMeasureOn_eq {γ : ℝ} {x : FieldSample} {U : Set ℝ} (hU : IsOpen U)
    {ν : Measure ℝ} (hν : IsVagueLimitOnR U (bdryApprox γ x) ν) :
    qBoundaryMeasureOn γ x U = ν := by
  have hex : ∃ ν', IsVagueLimitOnR U (bdryApprox γ x) ν' := ⟨ν, hν⟩
  unfold qBoundaryMeasureOn
  rw [dif_pos hex]
  exact isVagueLimitOnR_unique hU hex.choose_spec hν

theorem qAreaMeasureOn_eq {γ : ℝ} {x : FieldSample} {U : Set ℂ} (hU : IsOpen U)
    {μ : Measure ℂ} (hμ : IsVagueLimitOn U (areaApprox γ x) μ) :
    qAreaMeasureOn γ x U = μ := by
  have hex : ∃ μ', IsVagueLimitOn U (areaApprox γ x) μ' := ⟨μ, hμ⟩
  unfold qAreaMeasureOn
  rw [dif_pos hex]
  exact isVagueLimitOn_unique hU hex.choose_spec hμ

/-! ### Corollaries for the chosen limits -/

theorem qBoundaryMeasureOn_add_ofFun {x : FieldSample} (hx : IsRegularSample x) {γ : ℝ}
    {U : Set ℝ} (hU : IsOpen U) (hex : ∃ ν, IsVagueLimitOnR U (bdryApprox γ x) ν)
    {φ : ℂ → ℝ} {W : Set ℂ} (hW : IsOpen W) (hUW : ∀ t ∈ U, (t : ℂ) ∈ W)
    (hφ : ContinuousOn φ (W ∩ Hbar)) :
    qBoundaryMeasureOn γ (x + ofFun φ) U =
      (qBoundaryMeasureOn γ x U).withDensity fun t => ENNReal.ofReal (Real.exp (γ / 2 * φ t)) := by
  obtain ⟨ν, hν⟩ := hex
  rw [qBoundaryMeasureOn_eq hU hν]
  exact qBoundaryMeasureOn_eq hU (isVagueLimitOnR_add_ofFun hx hU hν hW hUW hφ)

theorem qBoundaryMeasure_add_ofFun' {x : FieldSample} (hx : IsRegularSample x) {γ : ℝ}
    (hex : ∃ ν, IsVagueLimitR (bdryApprox γ x) ν) {φ : ℂ → ℝ} {W : Set ℂ} (hW : IsOpen W)
    (hUW : ∀ t : ℝ, (t : ℂ) ∈ W) (hφ : ContinuousOn φ (W ∩ Hbar)) :
    qBoundaryMeasure γ (x + ofFun φ) =
      (qBoundaryMeasure γ x).withDensity fun t => ENNReal.ofReal (Real.exp (γ / 2 * φ t)) := by
  obtain ⟨ν, hν⟩ := hex
  rw [qBoundaryMeasure_eq hν]
  exact qBoundaryMeasure_eq (isVagueLimitR_add_ofFun hx hν hW hUW hφ)

theorem qAreaMeasure_add_ofFun' {x : FieldSample} (hx : IsRegularSample x) {γ : ℝ}
    (hex : ∃ μ, IsVagueLimitOn H (areaApprox γ x) μ) {φ : ℂ → ℝ} {W : Set ℂ} (hW : IsOpen W)
    (hUW : H ⊆ W) (hφ : ContinuousOn φ (W ∩ Hbar)) :
    qAreaMeasure γ (x + ofFun φ) =
      (qAreaMeasure γ x).withDensity fun z => ENNReal.ofReal (Real.exp (γ * φ z)) := by
  obtain ⟨μ, hμ⟩ := hex
  rw [qAreaMeasure_eq hμ]
  exact qAreaMeasure_eq (isVagueLimitOn_add_ofFun hx isOpen_H subset_rfl hμ hW hUW hφ)

/-! ### Additive constants -/

/-- The raw dyadic circle averages of `x` converge at every point of `S`, at every level. -/
def RawConverges (x : FieldSample) (S : Set ℂ) : Prop :=
  ∀ k : ℕ, ∀ z ∈ S, ∃ l, Tendsto (fun n => x (foldedCircle (dyadicRoundC n z) (radius k))) atTop
    (𝓝 l)

theorem _root_.QuantumZipper.IsRegularSample.rawConverges {x : FieldSample}
    (hx : IsRegularSample x) : RawConverges x Hbar := by
  obtain ⟨F, hF⟩ := hx
  exact fun k z hz => ⟨_, hF.2.1 k z hz⟩

theorem avgReg_addConst_of_tendsto {x : FieldSample} {k : ℕ} {z : ℂ}
    (h : ∃ l, Tendsto (fun n => x (foldedCircle (dyadicRoundC n z) (radius k))) atTop (𝓝 l))
    (c : ℝ) : avgReg (addConst x c) k z = avgReg x k z + c := by
  obtain ⟨l, hl⟩ := h
  have h2 : Tendsto (fun n => addConst x c (foldedCircle (dyadicRoundC n z) (radius k))) atTop
      (𝓝 (l + c)) := by
    simpa [addConst, measure_univ] using hl.add_const c
  unfold avgReg
  rw [h2.limUnder_eq, hl.limUnder_eq]

theorem bdryApprox_addConst {x : FieldSample} (hx : RawConverges x Hbar) (γ c : ℝ) (k : ℕ) :
    bdryApprox γ (addConst x c) k =
      ENNReal.ofReal (Real.exp (γ * c / 2)) • bdryApprox γ x k := by
  unfold bdryApprox
  rw [← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  funext t
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [avgReg_addConst_of_tendsto (hx k _ (ofReal_mem_Hbar t)), ← ENNReal.ofReal_mul
    (Real.exp_pos _).le]
  congr 1
  rw [mul_add, Real.exp_add]
  ring_nf

theorem areaApprox_addConst {x : FieldSample} (hx : RawConverges x H) (γ c : ℝ) (k : ℕ) :
    areaApprox γ (addConst x c) k = ENNReal.ofReal (Real.exp (γ * c)) • areaApprox γ x k := by
  unfold areaApprox
  rw [← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
  refine withDensity_congr_ae ?_
  filter_upwards [ae_restrict_mem isOpen_H.measurableSet] with z hz
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [avgReg_addConst_of_tendsto (hx k z hz), ← ENNReal.ofReal_mul (Real.exp_pos _).le]
  congr 1
  rw [mul_add, Real.exp_add]
  ring

theorem IsVagueLimitOnR.const_smul {U : Set ℝ} {νs : ℕ → Measure ℝ} {ν : Measure ℝ}
    (h : IsVagueLimitOnR U νs ν) {c : ℝ≥0∞} (hc : c ≠ ⊤) :
    IsVagueLimitOnR U (fun k => c • νs k) (c • ν) := by
  obtain ⟨h0, hK, ht⟩ := h
  refine ⟨by rw [Measure.smul_apply, h0, smul_zero], fun K hKc hKU => ?_, fun f hf hfc hfU => ?_⟩
  · rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top hc.lt_top (hK K hKc hKU)
  · simp_rw [integral_smul_measure]
    exact (ht f hf hfc hfU).const_smul _

theorem IsVagueLimitOn.const_smul {U : Set ℂ} {μs : ℕ → Measure ℂ} {μ : Measure ℂ}
    (h : IsVagueLimitOn U μs μ) {c : ℝ≥0∞} (hc : c ≠ ⊤) :
    IsVagueLimitOn U (fun k => c • μs k) (c • μ) := by
  obtain ⟨h0, hK, ht⟩ := h
  refine ⟨by rw [Measure.smul_apply, h0, smul_zero], fun K hKc hKU => ?_, fun f hf hfc hfU => ?_⟩
  · rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top hc.lt_top (hK K hKc hKU)
  · simp_rw [integral_smul_measure]
    exact (ht f hf hfc hfU).const_smul _

theorem ofReal_exp_ne_zero (a : ℝ) : ENNReal.ofReal (Real.exp a) ≠ 0 :=
  (ENNReal.ofReal_pos.2 (Real.exp_pos a)).ne'

/-- Constants, `qBoundaryMeasureOn`: exact, with no convergence assumption on `bdryApprox`. -/
theorem qBoundaryMeasureOn_addConst {x : FieldSample} (hx : RawConverges x Hbar) (γ c : ℝ)
    {U : Set ℝ} (hU : IsOpen U) :
    qBoundaryMeasureOn γ (addConst x c) U =
      ENNReal.ofReal (Real.exp (γ * c / 2)) • qBoundaryMeasureOn γ x U := by
  set C := ENNReal.ofReal (Real.exp (γ * c / 2))
  have hC0 : C ≠ 0 := ofReal_exp_ne_zero _
  have hCT : C ≠ ⊤ := ENNReal.ofReal_ne_top
  have he : bdryApprox γ (addConst x c) = fun k => C • bdryApprox γ x k :=
    funext (bdryApprox_addConst hx γ c)
  by_cases hex : ∃ ν, IsVagueLimitOnR U (bdryApprox γ x) ν
  · obtain ⟨ν, hν⟩ := hex
    rw [qBoundaryMeasureOn_eq hU hν]
    refine qBoundaryMeasureOn_eq hU ?_
    rw [he]; exact IsVagueLimitOnR.const_smul hν ENNReal.ofReal_ne_top
  · have hex' : ¬∃ ν, IsVagueLimitOnR U (bdryApprox γ (addConst x c)) ν := by
      rintro ⟨ν, hν⟩
      refine hex ⟨C⁻¹ • ν, ?_⟩
      have := IsVagueLimitOnR.const_smul hν (c := C⁻¹) (ENNReal.inv_ne_top.2 (ofReal_exp_ne_zero _))
      rw [he] at this
      simpa only [smul_smul, ENNReal.inv_mul_cancel hC0 hCT,
        one_smul] using this
    unfold qBoundaryMeasureOn
    rw [dif_neg hex, dif_neg hex', smul_zero]

/-- Constants, `qBoundaryMeasure`. -/
theorem qBoundaryMeasure_addConst' {x : FieldSample} (hx : RawConverges x Hbar) (γ c : ℝ) :
    qBoundaryMeasure γ (addConst x c) =
      ENNReal.ofReal (Real.exp (γ * c / 2)) • qBoundaryMeasure γ x := by
  set C := ENNReal.ofReal (Real.exp (γ * c / 2))
  have hC0 : C ≠ 0 := ofReal_exp_ne_zero _
  have hCT : C ≠ ⊤ := ENNReal.ofReal_ne_top
  have he : bdryApprox γ (addConst x c) = fun k => C • bdryApprox γ x k :=
    funext (bdryApprox_addConst hx γ c)
  by_cases hex : ∃ ν, IsVagueLimitR (bdryApprox γ x) ν
  · obtain ⟨ν, hν⟩ := hex
    rw [qBoundaryMeasure_eq hν]
    refine qBoundaryMeasure_eq ?_
    rw [he]; exact BdryVague.IsVagueLimitR.const_smul hν ENNReal.ofReal_ne_top
  · have hex' : ¬∃ ν, IsVagueLimitR (bdryApprox γ (addConst x c)) ν := by
      rintro ⟨ν, hν⟩
      refine hex ⟨C⁻¹ • ν, ?_⟩
      have := BdryVague.IsVagueLimitR.const_smul hν (c := C⁻¹)
        (ENNReal.inv_ne_top.2 (ofReal_exp_ne_zero _))
      rw [he] at this
      simpa only [smul_smul, ENNReal.inv_mul_cancel hC0 hCT,
        one_smul] using this
    unfold qBoundaryMeasure
    rw [dif_neg hex, dif_neg hex', smul_zero]

/-- Constants, `qAreaMeasure`. -/
theorem qAreaMeasure_addConst' {x : FieldSample} (hx : RawConverges x H) (γ c : ℝ) :
    qAreaMeasure γ (addConst x c) = ENNReal.ofReal (Real.exp (γ * c)) • qAreaMeasure γ x := by
  set C := ENNReal.ofReal (Real.exp (γ * c))
  have hC0 : C ≠ 0 := ofReal_exp_ne_zero _
  have hCT : C ≠ ⊤ := ENNReal.ofReal_ne_top
  have he : areaApprox γ (addConst x c) = fun k => C • areaApprox γ x k :=
    funext (areaApprox_addConst hx γ c)
  by_cases hex : ∃ μ, IsVagueLimitOn H (areaApprox γ x) μ
  · obtain ⟨μ, hμ⟩ := hex
    rw [qAreaMeasure_eq hμ]
    refine qAreaMeasure_eq ?_
    rw [he]; exact IsVagueLimitOn.const_smul hμ ENNReal.ofReal_ne_top
  · have hex' : ¬∃ μ, IsVagueLimitOn H (areaApprox γ (addConst x c)) μ := by
      rintro ⟨μ, hμ⟩
      refine hex ⟨C⁻¹ • μ, ?_⟩
      have := IsVagueLimitOn.const_smul hμ (c := C⁻¹) (ENNReal.inv_ne_top.2 (ofReal_exp_ne_zero _))
      rw [he] at this
      simpa only [smul_smul, ENNReal.inv_mul_cancel hC0 hCT,
        one_smul] using this
    unfold qAreaMeasure
    rw [dif_neg hex, dif_neg hex', smul_zero]

end LocalRule
end QuantumZipper
