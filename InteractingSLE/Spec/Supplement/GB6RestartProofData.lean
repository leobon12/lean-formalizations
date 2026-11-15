/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB6RestartProofWord
import InteractingSLE.Spec.Sec6.Prop61Mean
import InteractingSLE.Spec.Sec7.StripSideHeightProbSide
import InteractingSLE.Impl.PiecewiseConstant
import InteractingSLE.Spec.Supplement.GW2aPieceChart
import InteractingSLE.Spec.Supplement.GB6LifeBase

/-!
# Proposition GB6, step (d): the counterflow data, admissibility, and the seed images at an interior tip

Packet PROVE-GB6-RESTART. Three facts that GB6's conditional word needs from the setting of the proposition:

* **the counterflow data is the returned flow data** (`data_eq_returnData`): the counterflow parameter field `h′` is
  the `R`-transport of `h` (frozen `IsChartTransport infinitySourceChart (−1) (−πχ) χ(16/κ)`), so its boundary data
  `b′` is `returnData πχ χ b` off finitely many points (two GFF descriptions of the same field have the same data,
  `data_eq_of_isGFFWithBoundaryData`);
* **the data form of the counterflow's admissibility** (`neg_bigLambda_lt_of_admR`, `lt_bigLambda_of_admL`): every
  right partial sum `> −2` gives `b′ > −Λ` right of `0`, every left one `b′ < Λ` left of `0`; together with the
  first fact these are the hypotheses of `isGB6AdmData_gb6WordOfRec` (`gb6_admL`, `gb6_admR`);
* **the seed images are nondegenerate at an interior tip** (`baseR_pos_of_tip`, `baseL_neg_of_tip`): if `V̂^{0,R} = 0`
  the boundary extension of `f_s⁻¹` is real right of `0` and continuous at `0`, so the tip would be real; and the record
  positions of the seeds are the geometric images (`markPos_zero_eq_baseR`, `markPosL_zero_eq_baseL`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Finset
open scoped NNReal ENNReal
open QuantumZipper (H Hbar chiC)
open LQGMetric (TestOn DistOn)

namespace InteractingSLE

namespace Supp8

namespace GB6

open Restart Exist.StagedLaw Sec7.StripSysField Theorem14.GW2JointKernel MartChar.RealFlow

/-! ### Two GFF descriptions of the same field -/

section DataEq

/-- **Two GFF descriptions of one field have the same data** off the exceptional sets (the mean of the field is the
bounded harmonic extension of either datum, and the boundary limits of one harmonic function are unique). -/
theorem data_eq_of_isGFFWithBoundaryData {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} {g₁ g₂ : ℝ → ℝ} {S₁ S₂ : Finset ℝ}
    (hg₁ : IsPiecewiseConstantBoundaryData g₁ S₁) (hg₂ : IsPiecewiseConstantBoundaryData g₂ S₂)
    (h₁ : IsGFFWithBoundaryData P h g₁ S₁) (h₂ : IsGFFWithBoundaryData P h g₂ S₂) {x : ℝ} (hx₁ : x ∉ S₁)
    (hx₂ : x ∉ S₂) : g₁ x = g₂ x := by
  obtain ⟨u₁, hu₁, -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension hg₁
  obtain ⟨u₂, hu₂, -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension hg₂
  have hX₁ := h₁.2 u₁ hu₁
  have hX₂ := h₂.2 u₂ hu₂
  have hmean : ∀ φ : TestOn upperHalfPlaneOpens, ∫ z, u₁ z * φ z = ∫ z, u₂ z * φ z := by
    intro φ
    have i₁ : Integrable (fun ω => h ω φ - ∫ z, u₁ z * φ z) P :=
      (hX₁.gaussian.hasGaussianLaw_eval φ).memLp_two.integrable one_le_two
    have i₀ : Integrable (fun ω => h ω φ) P := by
      have := i₁.add (integrable_const (∫ z, u₁ z * φ z))
      refine this.congr (Eventually.of_forall fun ω => ?_)
      simp only [Pi.add_apply, sub_add_cancel]
    have c₁ := hX₁.centered φ
    have c₂ := hX₂.centered φ
    rw [integral_sub i₀ (integrable_const _), integral_const, probReal_univ, one_smul] at c₁ c₂
    linarith
  have hEq : EqOn u₁ u₂ H :=
    Sec6.eqOn_of_integral_mul_eq QuantumZipper.isOpen_H subset_rfl hu₁.1 hu₂.1 fun φ _ => hmean φ
  have t₁ := hu₁.2.2 x hx₁
  have t₂ : Tendsto u₁ (𝓝[H] (x : ℂ)) (𝓝 (g₂ x)) :=
    (hu₂.2.2 x hx₂).congr' (eventually_nhdsWithin_of_forall fun z hz => (hEq hz).symm)
  have : (𝓝[H] (x : ℂ)).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (by
    rw [closure_H]; show (0 : ℝ) ≤ (x : ℂ).im; simp)
  exact tendsto_nhds_unique t₁ t₂

/-- The field read through `R` with the frozen counterflow coefficients is the return field. -/
theorem eq_returnField_of_isChartTransport_R {κ : ℝ} (hκ : 0 < κ) {h h' : DistOn upperHalfPlaneOpens}
    (hT : IsChartTransport infinitySourceChart (-1) (-(Real.pi * chiC κ)) (chiC (16 / κ)) h h') :
    h' = returnField (Real.pi * chiC κ) (chiC κ) h := by
  have h₃ := isChartTransport_infinitySourceChart_returnField (Real.pi * chiC κ) (chiC κ) h
  have e₁ : Real.pi * chiC κ - 2 * Real.pi * chiC κ = -(Real.pi * chiC κ) := by ring
  have e₂ : -chiC κ = chiC (16 / κ) := by rw [Sec4.chiC_sixteen_div hκ]
  rw [e₁, e₂] at h₃
  exact hT.unique Chart.isConformal_infinitySourceChart h₃

theorem notMem_returnExcept {S : Finset ℝ} {x : ℝ} (hx0 : x ≠ 0) (hxS : -x⁻¹ ∉ S) : x ∉ returnExcept S := by
  intro hx
  rcases Finset.mem_insert.1 hx with h | h
  · exact hx0 h
  · obtain ⟨w, hw, hwx⟩ := Finset.mem_image.1 h
    apply hxS
    rw [← hwx, inv_neg, inv_inv, neg_neg]
    exact hw

/-- **The counterflow data is the returned flow data** off finitely many points. -/
theorem data_eq_returnData {κ : ℝ} (hκ : 0 < κ) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h h' : Ω → DistOn upperHalfPlaneOpens} {b b' : ℝ → ℝ} {J J' : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b J) (hG : IsGFFWithBoundaryData P h b J)
    (hb' : IsPiecewiseConstantBoundaryData b' J') (hG' : IsGFFWithBoundaryData P h' b' J')
    (hT : ∀ ω, IsChartTransport infinitySourceChart (-1) (-(Real.pi * chiC κ)) (chiC (16 / κ)) (h ω) (h' ω))
    {x : ℝ} (hxJ' : x ∉ J') (hx0 : x ≠ 0) (hxJ : -x⁻¹ ∉ J) :
    b' x = returnData (Real.pi * chiC κ) (chiC κ) b x := by
  have he : h' = fun ω => returnField (Real.pi * chiC κ) (chiC κ) (h ω) :=
    funext fun ω => eq_returnField_of_isChartTransport_R hκ (hT ω)
  obtain ⟨u, hu, -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension hb
  have hR := isGFFWithBoundaryData_returnField (Real.pi * chiC κ) (chiC κ) ⟨u, hu⟩ hG
  rw [← he] at hR
  exact data_eq_of_isGFFWithBoundaryData hb' (isPiecewiseConstant_returnData _ _ hb) hG' hR hxJ'
    (notMem_returnExcept hx0 hxJ)

end DataEq

/-! ### The data form of the counterflow's admissibility -/

section AdmData

variable {κ : ℝ}

/-- A nonempty downward-closed set of indices is the set of indices below its maximum. -/
theorem filter_eq_filter_le_max' {n : ℕ} (F : Finset (Fin n)) (hne : F.Nonempty)
    (hdown : ∀ i ∈ F, ∀ j ≤ i, j ∈ F) : F = univ.filter fun l => l ≤ F.max' hne := by
  ext l
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun hl => F.le_max' l hl, fun hl => hdown _ (F.max'_mem hne) l hl⟩

/-- **Data form of the right admissibility** (Remark 4.1): every right partial sum of the counterflow word `> −2`
gives `b′ > −Λ` right of `0`. -/
theorem neg_bigLambda_lt_of_admR (hκ : 0 < κ) {b' : ℝ → ℝ} {J' : Finset ℝ}
    (hb' : IsPiecewiseConstantBoundaryData b' J')
    (hadmR : ∀ i : Fin (flowLineNR b' J' 0),
      -2 < ∑ l ∈ Finset.univ.filter (fun l => l ≤ i), flowLineRhoR (16 / κ) b' J' 0 0 l)
    {y : ℝ} (hy : 0 < y) (hyJ : y ∉ J') : -bigLambda κ < b' y := by
  classical
  have hk : 0 < 16 / κ := by positivity
  have hord := Theorem15.isOrderedForceWord_flowLine b' J' 0
  rw [← Sec4.forceBoundaryData_flowLine hk hb' hy.ne' hyJ, Sec4.forceBoundaryData_of_nonneg _ _ _ _ hy.le]
  set F := univ.filter fun j : Fin (flowLineNR b' J' 0) => flowLineXR b' J' 0 j ≤ y with hF
  have hne : F.Nonempty := ⟨⟨0, zero_lt_flowLineNR b' J'⟩, Finset.mem_filter.2 ⟨mem_univ _, by
    rw [Sec4.flowLineXR_zero]; exact hy.le⟩⟩
  have hdown : ∀ i ∈ F, ∀ j ≤ i, j ∈ F := fun i hi j hji => by
    rw [hF, Finset.mem_filter] at hi ⊢
    exact ⟨mem_univ _, (hord.2.2.1 hji).trans hi.2⟩
  rw [filter_eq_filter_le_max' F hne hdown]
  have h2 := hadmR (F.max' hne)
  have hΛ : 0 < sleLambda (16 / κ) := Sec4.sleLambda_pos hk
  change -sleLambda (16 / κ) < _
  nlinarith

/-- **Data form of the left admissibility**: every left partial sum `> −2` gives `b′ < Λ` left of `0`. -/
theorem lt_bigLambda_of_admL (hκ : 0 < κ) {b' : ℝ → ℝ} {J' : Finset ℝ}
    (hb' : IsPiecewiseConstantBoundaryData b' J')
    (hadmL : ∀ i : Fin (flowLineNL b' J' 0),
      -2 < ∑ l ∈ Finset.univ.filter (fun l => l ≤ i), flowLineRhoL (16 / κ) b' J' 0 0 l)
    {y : ℝ} (hy : y < 0) (hyJ : y ∉ J') : b' y < bigLambda κ := by
  classical
  have hk : 0 < 16 / κ := by positivity
  have hord := Theorem15.isOrderedForceWord_flowLine b' J' 0
  rw [← Sec4.forceBoundaryData_flowLine hk hb' hy.ne hyJ, Sec4.forceBoundaryData_of_neg _ _ _ _ hy]
  set F := univ.filter fun i : Fin (flowLineNL b' J' 0) => y < flowLineXL b' J' 0 i with hF
  have hne : F.Nonempty := ⟨⟨0, zero_lt_flowLineNL b' J'⟩, Finset.mem_filter.2 ⟨mem_univ _, by
    rw [Sec4.flowLineXL_zero]; exact hy⟩⟩
  have hdown : ∀ i ∈ F, ∀ j ≤ i, j ∈ F := fun i hi j hji => by
    rw [hF, Finset.mem_filter] at hi ⊢
    exact ⟨mem_univ _, hi.2.trans_le (hord.1 hji)⟩
  rw [filter_eq_filter_le_max' F hne hdown]
  have h2 := hadmL (F.max' hne)
  have hΛ : 0 < sleLambda (16 / κ) := Sec4.sleLambda_pos hk
  change _ < sleLambda (16 / κ)
  nlinarith

theorem negInv_negInv (u : ℝ) : -(-u⁻¹)⁻¹ = u := by rw [inv_neg, inv_inv, neg_neg]

/-- **The left hypothesis of `isGB6AdmData_gb6WordOfRec`** from the counterflow's right admissibility: left of `0`
the returned launch word `−c + πχ` is the counterflow data at `−1/u > 0`. -/
theorem gb6_admL (hκ : 0 < κ) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h h' : Ω → DistOn upperHalfPlaneOpens} {b b' : ℝ → ℝ} {J J' : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b J) (hG : IsGFFWithBoundaryData P h b J)
    (hb' : IsPiecewiseConstantBoundaryData b' J') (hG' : IsGFFWithBoundaryData P h' b' J')
    (hT : ∀ ω, IsChartTransport infinitySourceChart (-1) (-(Real.pi * chiC κ)) (chiC (16 / κ)) (h ω) (h' ω))
    (hadmR : ∀ i : Fin (flowLineNR b' J' 0),
      -2 < ∑ l ∈ Finset.univ.filter (fun l => l ≤ i), flowLineRhoR (16 / κ) b' J' 0 0 l)
    {c : BoundaryWord} (hcJ : c.jumps = J) (hcb : ∀ y ∉ J, c.fn y = b y) :
    ∀ u, u < 0 → u ∉ J'.image (fun w => -w⁻¹) → u ∉ c.jumps →
      -bigLambda κ < -c.fn u + Real.pi * chiC κ := by
  intro u hu huE huJ
  rw [hcJ] at huJ
  have hx : 0 < -u⁻¹ := neg_pos.2 (inv_lt_zero.2 hu)
  have hxJ' : -u⁻¹ ∉ J' := fun h => huE (Finset.mem_image.2 ⟨_, h, negInv_negInv u⟩)
  have he := data_eq_returnData hκ hb hG hb' hG' hT hxJ' hx.ne' (by rw [negInv_negInv]; exact huJ)
  rw [returnData, negInv_negInv, liftBoundary_of_pos hx] at he
  rw [hcb u huJ]
  have := neg_bigLambda_lt_of_admR hκ hb' hadmR hx hxJ'
  linarith

/-- **The right hypothesis of `isGB6AdmData_gb6WordOfRec`** from the counterflow's left admissibility. -/
theorem gb6_admR (hκ : 0 < κ) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h h' : Ω → DistOn upperHalfPlaneOpens} {b b' : ℝ → ℝ} {J J' : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b J) (hG : IsGFFWithBoundaryData P h b J)
    (hb' : IsPiecewiseConstantBoundaryData b' J') (hG' : IsGFFWithBoundaryData P h' b' J')
    (hT : ∀ ω, IsChartTransport infinitySourceChart (-1) (-(Real.pi * chiC κ)) (chiC (16 / κ)) (h ω) (h' ω))
    (hadmL : ∀ i : Fin (flowLineNL b' J' 0),
      -2 < ∑ l ∈ Finset.univ.filter (fun l => l ≤ i), flowLineRhoL (16 / κ) b' J' 0 0 l)
    {c : BoundaryWord} (hcJ : c.jumps = J) (hcb : ∀ y ∉ J, c.fn y = b y) :
    ∀ u, 0 < u → u ∉ J'.image (fun w => -w⁻¹) → u ∉ c.jumps →
      -c.fn u - Real.pi * chiC κ < bigLambda κ := by
  intro u hu huE huJ
  rw [hcJ] at huJ
  have hx : -u⁻¹ < 0 := neg_neg_of_pos (inv_pos.2 hu)
  have hxJ' : -u⁻¹ ∉ J' := fun h => huE (Finset.mem_image.2 ⟨_, h, negInv_negInv u⟩)
  have he := data_eq_returnData hκ hb hG hb' hG' hT hxJ' hx.ne (by rw [negInv_negInv]; exact huJ)
  rw [returnData, negInv_negInv, liftBoundary_of_neg hx] at he
  rw [hcb u huJ]
  have := lt_bigLambda_of_admL hκ hb' hadmL hx hxJ'
  linarith

end AdmData

/-! ### The seed images at an interior tip -/

section Tip

theorem baseR_nonneg {U : ℝ → ℝ} (hU : Continuous U) {s : ℝ} (hs : 0 ≤ s) : 0 ≤ baseR U s := by
  have := le_rightImg hU 0 hs
  unfold baseR
  linarith

theorem baseL_nonpos {U : ℝ → ℝ} (hU : Continuous U) {s : ℝ} (hs : 0 ≤ s) : baseL U s ≤ 0 := by
  have := le_rightImg (w := fun r => -U r) (by fun_prop) 0 hs
  beta_reduce at this
  unfold baseL
  linarith

/-- The boundary extension of `f_s⁻¹` at `0` is the tip. -/
theorem extendFrom_zero_eq_tip {U : ℝ → ℝ} {s : ℝ} {p : ℂ}
    (htip : Tendsto (QuantumZipper.fwdMapInv U s) (𝓝[H] 0) (𝓝 p)) :
    extendFrom H (QuantumZipper.fwdMapInv U s) 0 = p :=
  extendFrom_eq (by rw [closure_H]; show (0 : ℝ) ≤ (0 : ℂ).im; simp) htip

/-- **At an interior tip the right seed image is nondegenerate**, `V̂^{0,R}_s > 0`: otherwise the boundary extension
of `f_s⁻¹` takes real values at the points `1/(n+1)` right of the base and tends to the tip, which would be real. -/
theorem baseR_pos_of_tip {U : ℝ → ℝ} (hU : Continuous U) (hU0 : U 0 = 0) {s : ℝ} (hs : 0 ≤ s)
    (hB : HasBdryLimits (QuantumZipper.fwdMapInv U s)) {p : ℂ} (hp : p ∈ H)
    (htip : Tendsto (QuantumZipper.fwdMapInv U s) (𝓝[H] 0) (𝓝 p)) : 0 < baseR U s := by
  rcases (baseR_nonneg hU hs).lt_or_eq with h | h
  · exact h
  exfalso
  have hreal : ∀ n : ℕ,
      (extendFrom H (QuantumZipper.fwdMapInv U s) ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)).im = 0 := fun n => by
    obtain ⟨x₀, hx₀, -⟩ := exists_extendFrom_eq_alive_of_gt hU hU0 hs hB (y := 1 / ((n : ℝ) + 1))
      (by rw [← h]; positivity)
    rw [hx₀, Complex.ofReal_im]
  have hlim := tendsto_extendFrom_of_real hB (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  rw [Complex.ofReal_zero, extendFrom_zero_eq_tip htip] at hlim
  have him := (Complex.continuous_im.tendsto p).comp hlim
  have h0 : p.im = 0 := tendsto_nhds_unique him (by
    simp only [Function.comp_def, hreal]
    exact tendsto_const_nhds)
  exact (show (0 : ℝ) < p.im from hp).ne' h0

/-- **At an interior tip the left seed image is nondegenerate**, `V̂^{0,L}_s < 0`. -/
theorem baseL_neg_of_tip {U : ℝ → ℝ} (hU : Continuous U) (hU0 : U 0 = 0) {s : ℝ} (hs : 0 ≤ s)
    (hB : HasBdryLimits (QuantumZipper.fwdMapInv U s)) {p : ℂ} (hp : p ∈ H)
    (htip : Tendsto (QuantumZipper.fwdMapInv U s) (𝓝[H] 0) (𝓝 p)) : baseL U s < 0 := by
  rcases (baseL_nonpos hU hs).lt_or_eq with h | h
  · exact h
  exfalso
  have hreal : ∀ n : ℕ,
      (extendFrom H (QuantumZipper.fwdMapInv U s) ((-(1 / ((n : ℝ) + 1)) : ℝ) : ℂ)).im = 0 := fun n => by
    obtain ⟨x₀, hx₀, -⟩ := exists_extendFrom_eq_of_lt_baseL hU hU0 hs hB (y := -(1 / ((n : ℝ) + 1)))
      (by rw [h]; have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
          linarith)
    rw [hx₀, Complex.ofReal_im]
  have hc : Tendsto (fun n : ℕ => -(1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    simpa only [neg_zero] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).neg
  have hlim := tendsto_extendFrom_of_real hB hc
  rw [Complex.ofReal_zero, extendFrom_zero_eq_tip htip] at hlim
  have him := (Complex.continuous_im.tendsto p).comp hlim
  have h0 : p.im = 0 := tendsto_nhds_unique him (by
    simp only [Function.comp_def, hreal]
    exact tendsto_const_nhds)
  exact (show (0 : ℝ) < p.im from hp).ne' h0

/-- **The record position of `0⁺` is the geometric image**: `markPos w T 0 = V̂^{0,R}_T`. -/
theorem markPos_zero_eq_baseR {w : ℝ → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) {T : ℝ} (hT : 0 ≤ T) :
    markPos w T 0 = baseR w T := by
  refine le_antisymm ?_ (Sec7.StripSideHeightProb.rightImg_sub_le_markPos hw hw0 hT)
  have key : markPos w T 0 + w T ≤ rightImg w 0 T := by
    refine le_csInf (imgSet_nonempty hw 0 hT) ?_
    rintro g ⟨y, hy0, hya, rfl⟩
    refine le_of_forall_pos_lt_add fun ε hε => ?_
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show y < y + ε by linarith)
    have hqa : Alive w q T := hya.of_le hw hq1.le hT
    have hu := WangWu.isForwardSol_of_alive hw hqa
    have h1 := Theorem14.GW1W.markPos_le_rat hw hw0 hT le_rfl (show (0 : ℝ) < q by linarith) ⟨_, hu⟩
    rw [fwdMap_eq_of_isForwardSol hw hu ⟨hT, le_rfl⟩, Complex.ofReal_re] at h1
    have h2 := abs_gImg_sub_le hw hT hya hqa
    have h3 : gImg w q T - gImg w y T ≤ q - y :=
      (le_abs_self _).trans (h2.trans_eq (abs_of_pos (by linarith)))
    have h4 : gImg w q T = w T + cflow w q T := rfl
    linarith
  unfold baseR
  linarith

/-- **The record position of `0⁻` is the geometric image**: `markPosL w T 0 = V̂^{0,L}_T`. -/
theorem markPosL_zero_eq_baseL {w : ℝ → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) {T : ℝ} (hT : 0 ≤ T) :
    markPosL w T 0 = baseL w T := by
  unfold markPosL baseL
  rw [neg_zero, markPos_zero_eq_baseR (w := fun s => -w s) (by fun_prop) (by simp [hw0]) hT]
  unfold baseR
  ring

end Tip

end GB6

end Supp8

end InteractingSLE
