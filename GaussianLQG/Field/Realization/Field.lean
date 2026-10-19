import GaussianLQG.Field.Realization.Uniform
import GaussianLQG.Field.FrameFun
import LQGMetric.Field.ExistGFF
import LQGMetric.Field.CircleAvgCont

/-!
# The coordinate realization of the normalized whole-plane GFF (blueprint Prop. 1.9 (a), (b))

Let `b` be a Hilbert basis of `L²(ℝ × ℂ)` of nice vectors. With the continuous version `Yfield b`
of the antiderivative field (`Uniform.lean`), put

* `tildeField b ω := gffOf (Yfield b) ω`, i.e. `⟨h̃, φ⟩ = ∫ Y ∂_re ∂_im φ`: a whole-plane GFF
  (`isWholePlaneGFF_tildeField`, the proof pattern of `LQGMetric.GFFExist.exists_wholePlaneGFF`);
* `field0 b ω := h̃(ω) - h̃_1(0)(ω)`: a normalized whole-plane GFF (`isNormalizedWPGFF_field0`).

The frame identity `∫ F_k ∂_re ∂_im φ = ∫ φ ẽ_k` (`integral_d12_mul_rectCoef`, from
`LQGMetric`'s Fubini step `integral_d12_mul_inner_rectL2` and the heat-kernel Fubini lemma
`integral_mul_frameFun0` of `GaussianLQG.Field.FrameFun`) turns the coordinate shift `ω ↦ ω + v` into the Cameron–Martin shift by
`∑_k v_k ẽ_k` (`tildeField_shift`), and the circle normalization turns `ẽ_k = frameFun0 (b k)`
into `e_k = frameFunN (b k)` (`field0_shift`). Both hold on the measurable, shift-invariant,
full-measure set `goodW b`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped RealInnerProductSpace

namespace GaussianLQG
namespace Realization

open LQGMetric LQGMetric.GFFExist

/-! ### The frame identity -/

variable (b : HilbertBasis ℕ ℝ WNSpace)

/-- **Frame identity**: `∫ F_k ∂_re ∂_im φ = ∫ φ ẽ_k` with `ẽ_k = frameFun0 (b k)`. -/
theorem integral_d12_mul_rectCoef (φ : TestC) {k : ℕ} (hk : IsNiceWN (b k)) :
    ∫ x, d12 φ x * rectCoef b x k = ∫ u, φ u * frameFun0 (b k) u := by
  have e : (fun x => d12 φ x * rectCoef b x k) = fun x => d12 φ x * ⟪rectL2 x, b k⟫ := rfl
  rw [e, integral_d12_mul_inner_rectL2]
  exact (integral_mul_frameFun0 hk (GFFInv.integrable_test φ)).symm

/-! ### The whole-plane GFF -/

/-- `⟨h̃(ω), φ⟩ = ∫ Y(ω) ∂_re ∂_im φ`. -/
def tildeField (ω : Coord) : DistC := gffOf (Yfield b) (continuous_Yfield b) ω

lemma tildeField_apply (ω : Coord) (φ : TestC) :
    tildeField b ω φ = ∫ x, d12 φ x * Yfield b x ω :=
  gffOf_apply _ _ _ _

lemma measurable_tildeField : Measurable (tildeField b) :=
  measurable_gffOf _ _ (measurable_Yfield b)

lemma measurable_tildeField_apply (φ : TestC) : Measurable fun ω => tildeField b ω φ :=
  GFFInv.measurable_distC_iff.mp (measurable_tildeField b) φ

/-- **The coordinate field is a whole-plane GFF.** -/
theorem isWholePlaneGFF_tildeField : IsWholePlaneGFF (tildeField b) stdP := by
  have hW := isWhiteNoise_wnOf b
  have hae : ∀ φ : TestC, (fun ω => tildeField b ω φ) =ᵐ[stdP] wnOf b (testL2 φ) := fun φ => by
    simpa only [tildeField_apply] using ae_integral_d12_mul_eq hW (continuous_Yfield b)
      (measurable_Yfield b) (ae_Yfield_eq b) φ
  have hmean : ∀ φ : TestC, ∫ ω, tildeField b ω φ ∂stdP = 0 := fun φ => by
    rw [integral_congr_ae (hae φ),
      QuantumZipper.GFFExist.gs_integral_eq_zero (hW.hasLaw_single _)]
  refine ⟨measurable_tildeField b, ?_, fun φ => hmean φ.1, ?_⟩
  · exact (hW.isGaussianProcess_comp (fun φ : TestC0 => testL2 φ.1)).congr
      (fun φ => (hae φ.1).symm)
  · intro φ ψ
    have hm1 := (wn_memLp hW (testL2 φ.1)).ae_eq (hae φ.1).symm
    have hm2 := (wn_memLp hW (testL2 ψ.1)).ae_eq (hae ψ.1).symm
    rw [covariance_eq_sub hm1 hm2, hmean φ.1, zero_mul, sub_zero,
      integral_congr_ae ((hae φ.1).mul (hae ψ.1))]
    have := wn_integral_mul hW (testL2 φ.1) (testL2 ψ.1)
    simp only [Pi.mul_apply]
    rw [this, inner_testL2_testL2 φ.1 ψ.1 φ.2 ψ.2]

/-- The normalized field `h₀ = h̃ - h̃_1(0)`. -/
def field0 (ω : Coord) : DistC := addConst (tildeField b ω) (-circleAvg (tildeField b ω) 1 0)

lemma measurable_circleAvg_tildeField : Measurable fun ω => circleAvg (tildeField b ω) 1 0 :=
  (measurable_circleAvg_left 1 0).comp (measurable_tildeField b)

theorem isWholePlaneGFF_field0 : IsWholePlaneGFF (field0 b) stdP :=
  (isWholePlaneGFF_tildeField b).addConst (measurable_circleAvg_tildeField b).neg

theorem measurable_field0 : Measurable (field0 b) := (isWholePlaneGFF_field0 b).measurable

/-- **The coordinate field, normalized, is a normalized whole-plane GFF.** -/
theorem isNormalizedWPGFF_field0 : IsNormalizedWPGFF (field0 b) stdP := by
  refine ⟨isWholePlaneGFF_field0 b, ?_⟩
  filter_upwards [CircleAvg.ae_circleAvg_addConst_one_zero (isWholePlaneGFF_tildeField b)]
    with ω hω
  rw [field0, hω, add_neg_cancel]

/-! ### Shift compatibility -/

variable (hb : ∀ j, IsNiceWN (b j))
include hb

/-- `f̃_v = ∑_k v_k ẽ_k` as a continuous function. -/
def frameShift0 (v : ℕ →₀ ℝ) : C(ℂ, ℝ) :=
  frameFunC (fun k => frameFun0 (b k)) (fun k => continuous_frameFun0 (hb k)) v

omit hb in
lemma integrable_test_mul_cont (φ : TestC) {f : ℂ → ℝ} (hf : Continuous f) :
    Integrable fun x => φ x * f x :=
  (φ.continuous.mul hf).integrable_of_hasCompactSupport φ.hasCompactSupport.mul_right

/-- **Shift compatibility of the unnormalized field**: `h̃(ω + v) = h̃(ω) + f̃_v`. -/
theorem tildeField_shift {ω : Coord} (hω : ω ∈ goodSet b) (v : ℕ →₀ ℝ) :
    tildeField b (shiftBy ω v) = tildeField b ω + ofCont (frameShift0 b hb v) := by
  ext φ
  rw [add_apply, tildeField_apply, tildeField_apply, ofCont_apply]
  simp_rw [Yfield_shift b hω v, mul_add]
  have hY : Integrable fun x => d12 φ x * Yfield b x ω :=
    integrable_d12_mul_slice φ _ (continuous_Yfield b ω)
  have hsum : ∀ k, Continuous fun x => rectCoef b x k := continuous_rectCoef b
  have hS : Integrable fun x => d12 φ x * v.sum fun k c => c * rectCoef b x k := by
    refine integrable_d12_mul_slice φ _ ?_
    unfold Finsupp.sum
    exact continuous_finsetSum _ fun k _ => continuous_const.mul (hsum k)
  rw [integral_add hY hS]
  congr 1
  -- `∫ ∂₁₂φ · ∑ v_k F_k = ∫ φ · ∑ v_k ẽ_k`
  have e1 : ∀ x, d12 φ x * (v.sum fun k c => c * rectCoef b x k) =
      ∑ k ∈ v.support, v k * (d12 φ x * rectCoef b x k) := fun x => by
    unfold Finsupp.sum
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  have e2 : ∀ x, φ x * frameShift0 b hb v x =
      ∑ k ∈ v.support, v k * (φ x * frameFun0 (b k) x) := fun x => by
    simp only [frameShift0, frameFunC, ContinuousMap.coe_mk, frameFun, Finsupp.sum]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  simp_rw [e1, e2]
  rw [integral_finsetSum _ fun k _ =>
      (integrable_d12_mul_slice φ _ (hsum k)).const_mul (v k),
    integral_finsetSum _ fun k _ =>
      (integrable_test_mul_cont φ (continuous_frameFun0 (hb k))).const_mul (v k)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_const_mul, integral_const_mul, integral_d12_mul_rectCoef b φ (hb k)]

omit hb in
/-- The event that the circle average of `h̃` on `∂𝔻` exists. -/
def circSet : Set Coord :=
  {ω | ∃ a, Tendsto (fun n => CircleAvg.mollAvg (tildeField b ω) n 0 1) atTop (𝓝 a)}

omit hb in
lemma measurableSet_circSet : MeasurableSet (circSet b) := by
  refine measurableSet_exists_tendsto fun n => ?_
  simp_rw [CircleAvg.mollAvg_eq]
  exact measurable_tildeField_apply b _

omit hb in
lemma ae_mem_circSet : ∀ᵐ ω ∂stdP, ω ∈ circSet b :=
  CircleAvg.ae_tendsto_mollAvg (isWholePlaneGFF_tildeField b) 0 one_pos

lemma shiftBy_mem_circSet {ω : Coord} (hω : ω ∈ goodSet b) (hc : ω ∈ circSet b)
    (v : ℕ →₀ ℝ) : shiftBy ω v ∈ circSet b := by
  obtain ⟨a, ha⟩ := hc
  refine ⟨a + Real.circleAverage (frameShift0 b hb v) 0 1, ?_⟩
  have h := ha.add (CircleAvg.tendsto_mollAvg_ofCont (frameShift0 b hb v) 1 0)
  refine h.congr fun n => ?_
  rw [tildeField_shift b hb hω v, CircleAvg.mollAvg_eq, CircleAvg.mollAvg_eq,
    CircleAvg.mollAvg_eq, add_apply]

omit hb in
/-- The good set of the realization: locally uniform convergence and existence of `h̃_1(0)`. -/
def goodW : Set Coord := goodSet b ∩ circSet b

omit hb in
lemma measurableSet_goodW : MeasurableSet (goodW b) :=
  (measurableSet_goodSet b).inter (measurableSet_circSet b)

omit hb in
lemma ae_mem_goodW : ∀ᵐ ω ∂stdP, ω ∈ goodW b := by
  filter_upwards [ae_mem_goodSet b, ae_mem_circSet b] with ω h1 h2
  exact ⟨h1, h2⟩

lemma shiftBy_mem_goodW {ω : Coord} (hω : ω ∈ goodW b) (v : ℕ →₀ ℝ) :
    shiftBy ω v ∈ goodW b :=
  ⟨shiftBy_mem_goodSet b hω.1 v, shiftBy_mem_circSet b hb hω.1 hω.2 v⟩

/-- `f_v = f̃_v - avg_{∂𝔻} f̃_v` pointwise. -/
lemma frameFun_frameFunN_eq (v : ℕ →₀ ℝ) (z : ℂ) :
    frameFun (fun j => frameFunN (b j)) v z =
      frameShift0 b hb v z - Real.circleAverage (frameShift0 b hb v) 0 1 := by
  have hci : ∀ k ∈ v.support, CircleIntegrable (fun z => v k * frameFun0 (b k) z) 0 1 :=
    fun k _ => (continuous_const.mul (continuous_frameFun0 (hb k))).continuousOn.circleIntegrable'
  have hA : Real.circleAverage (frameShift0 b hb v) 0 1 =
      ∑ k ∈ v.support, v k * Real.circleAverage (frameFun0 (b k)) 0 1 := by
    have e : (frameShift0 b hb v : ℂ → ℝ) = fun z => ∑ k ∈ v.support, v k * frameFun0 (b k) z := by
      funext z
      simp only [frameShift0, frameFunC, ContinuousMap.coe_mk, frameFun, Finsupp.sum]
    rw [e, Real.circleAverage_fun_sum hci]
    refine Finset.sum_congr rfl fun k _ => ?_
    have e2 : (fun z => v k * frameFun0 (b k) z) = v k • frameFun0 (b k) := rfl
    rw [e2, Real.circleAverage_smul, smul_eq_mul]
  rw [hA]
  simp only [frameShift0, frameFunC, ContinuousMap.coe_mk, frameFun, Finsupp.sum, frameFunN]
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- **Shift compatibility of the normalized field** (blueprint Prop. 1.9 (b)):
`h₀(ω + v) = h₀(ω) + f_v` for `ω` in the shift-invariant good set. -/
theorem field0_shift (hcont : ∀ j, Continuous (frameFunN (b j))) {ω : Coord}
    (hω : ω ∈ goodW b) (v : ℕ →₀ ℝ) :
    field0 b (shiftBy ω v) = addFun (field0 b ω) (frameFunC (fun j => frameFunN (b j)) hcont v) := by
  obtain ⟨a, ha⟩ := hω.2
  set T := tildeField b ω with hT
  set F := frameShift0 b hb v with hF
  have hshift : tildeField b (shiftBy ω v) = T + ofCont F := tildeField_shift b hb hω.1 v
  have hsub : T + ofCont F - ofCont F = T := add_sub_cancel_right _ _
  have hcirc : circleAvg (tildeField b (shiftBy ω v)) 1 0 =
      circleAvg T 1 0 + Real.circleAverage F 0 1 := by
    rw [hshift]
    have ha' : Tendsto (fun n => CircleAvg.mollAvg (T + ofCont F - ofCont F) n 0 1) atTop
        (𝓝 a) := by rw [hsub]; exact ha
    rw [(CircleAvg.circleAvg_eq_sub_ofCont_add ha').2, hsub]
  simp only [field0, addConst, addFun]
  rw [hcirc, hshift]
  ext φ
  simp only [add_apply, ofCont_apply, ContinuousMap.const_apply]
  rw [← hT]
  have hφ : Integrable fun x => φ x :=
    φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
  have hF' : Integrable fun x => φ x * F x := integrable_test_mul_cont φ F.continuous
  set A := Real.circleAverage F 0 1 with hA
  set c := circleAvg T 1 0 with hc
  have e1 : ∫ x, φ x * frameFunC (fun j => frameFunN (b j)) hcont v x =
      (∫ x, φ x * F x) - A * ∫ x, φ x := by
    have e : (fun x => φ x * frameFunC (fun j => frameFunN (b j)) hcont v x) =
        fun x => φ x * F x - A * φ x := by
      funext x
      simp only [frameFunC, ContinuousMap.coe_mk]
      rw [frameFun_frameFunN_eq b hb v x]
      ring
    rw [e, integral_sub hF' (hφ.const_mul A), integral_const_mul]
  have e2 : ∫ x, φ x * -(c + A) = -(c + A) * ∫ x, φ x := by
    rw [← integral_const_mul]; congr 1; funext x; ring
  have e3 : ∫ x, φ x * -c = -c * ∫ x, φ x := by
    rw [← integral_const_mul]; congr 1; funext x; ring
  rw [e1, e2, e3]
  ring

end Realization
end GaussianLQG
