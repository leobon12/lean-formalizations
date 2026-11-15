/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.FlowDilateCoupling
import InteractingSLE.Spec.Supplement.FlowDilateCov
import InteractingSLE.Spec.Sec7.FlowReflectFlow

/-!
# Flow lines under the affine map `A(z) = a z + m` (`a > 0`)

Packet PROVE-RLC-J, item (g): Lemma G8's "positive affine normalization" (supplement p. 501). If `η` is the
angle-`θ` flow line from `x` of a GFF `h` with piecewise-constant data `b` (jump candidates `J`), then
`t ↦ A(η(t/a²))` is the angle-`θ` flow line from `A(x)` of `h ∘ A⁻¹` (data `y ↦ b((y − m)/a)`, jump candidates
`A(J)`), with lifetime `a² ζ` (**`IsFlowLine.affine`**). With `IsGFFWithBoundaryData.affine` (`FlowDilateCov`) this
transports a whole coupling of a field with its flow lines; the inverse map transports back.

* the data: `affData`, `affJumps`, piecewise constancy, one-sided limits and genuine jumps;
* the flow-line word: same numbers of marks, positions multiplied by `a` (`flowLineXL_affData_apply`,
  `flowLineXR_affData_apply`), same weights (`flowLineRhoL_affData_apply`, `flowLineRhoR_affData_apply`);
* the translated field: `IsTranslateAddConst.affine` (`h' = h(· + x) + c` gives `h' ∘ (·/a)` for `h ∘ A⁻¹` at `A(x)`);
* the coupling of the translated field: Aux. lemma 126's `Sec7.Lemma725RefFull.IsOptionalHullCoupling.dilate`
  (through `FlowDilateCoupling`), the trace: `IsGeneratingTrace.dilate` (Aux. lemma 126).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal

open QuantumZipper (H)
open LQGMetric (TestOn DistOn)
universe u

namespace InteractingSLE

open PiecewiseConstantBoundaryData (leftLim rightLim jumpSet)

namespace FlowDilate

open Sec7.Dilation

variable {a m : ℝ}

/-! ### The data -/

/-- The jump candidates `A(J)`. -/
def affJumps (a m : ℝ) (J : Finset ℝ) : Finset ℝ := J.image (raff a m)

theorem raff_eq_iff (ha : a ≠ 0) {x y : ℝ} : raff a m x = y ↔ x = (y - m) / a := by
  simp only [raff]
  constructor
  · rintro rfl; field_simp; ring
  · rintro rfl; field_simp; ring

theorem mem_affJumps (ha : a ≠ 0) {J : Finset ℝ} {y : ℝ} : y ∈ affJumps a m J ↔ (y - m) / a ∈ J := by
  simp only [affJumps, Finset.mem_image]
  constructor
  · rintro ⟨x, hx, e⟩
    rwa [(raff_eq_iff ha).1 e] at hx
  · intro h
    exact ⟨_, h, raff_div ha y⟩

theorem card_affJumps (ha : a ≠ 0) (J : Finset ℝ) : (affJumps a m J).card = J.card :=
  Finset.card_image_of_injective _ (raff_injective ha)

variable {b : ℝ → ℝ} {J : Finset ℝ}

theorem tendsto_div_aff (y : ℝ) : Tendsto (fun z : ℝ => (z - m) / a) (𝓝 y) (𝓝 ((y - m) / a)) :=
  ((continuous_id.sub continuous_const).div_const a).tendsto y

theorem isPiecewiseConstantBoundaryData_affData (ha : 0 < a) (hb : IsPiecewiseConstantBoundaryData b J) :
    IsPiecewiseConstantBoundaryData (affData a m b) (affJumps a m J) := by
  intro y hy
  have h := (tendsto_div_aff (a := a) (m := m) y).eventually (hb _ fun h => hy ((mem_affJumps ha.ne').2 h))
  filter_upwards [h] with z hz
  simp only [affData, hz]

theorem leftLim_affData (ha : 0 < a) (hb : IsPiecewiseConstantBoundaryData b J) (y : ℝ) :
    leftLim (affData a m b) y = leftLim b ((y - m) / a) := by
  obtain ⟨δ, hδ, h⟩ := Supp7.exists_pos_eq_lims hb ((y - m) / a)
  refine Sec4.leftLim_eq_of_forall (by nlinarith : y - a * δ < y) fun t ht => ?_
  have hε : 0 < (y - t) / a := div_pos (by linarith [ht.2]) ha
  have hεδ : (y - t) / a < δ := by rw [div_lt_iff₀ ha]; linarith [ht.1]
  obtain ⟨-, -, -, hl⟩ := h _ hε hεδ
  simp only [affData]
  rw [← hl]
  congr 1
  field_simp
  ring

theorem rightLim_affData (ha : 0 < a) (hb : IsPiecewiseConstantBoundaryData b J) (y : ℝ) :
    rightLim (affData a m b) y = rightLim b ((y - m) / a) := by
  obtain ⟨δ, hδ, h⟩ := Supp7.exists_pos_eq_lims hb ((y - m) / a)
  refine Sec4.rightLim_eq_of_forall (by nlinarith : y < y + a * δ) fun t ht => ?_
  have hε : 0 < (t - y) / a := div_pos (by linarith [ht.1]) ha
  have hεδ : (t - y) / a < δ := by rw [div_lt_iff₀ ha]; linarith [ht.2]
  obtain ⟨-, -, hr, -⟩ := h _ hε hεδ
  simp only [affData]
  rw [← hr]
  congr 1
  field_simp
  ring

theorem mem_jumpSet_affData (ha : 0 < a) (hb : IsPiecewiseConstantBoundaryData b J) {y : ℝ} :
    y ∈ jumpSet (affData a m b) (affJumps a m J) ↔ (y - m) / a ∈ jumpSet b J := by
  simp only [PiecewiseConstantBoundaryData.jumpSet, Finset.mem_filter, mem_affJumps ha.ne', leftLim_affData ha hb,
    rightLim_affData ha hb]

theorem div_lt_iff_raff (ha : 0 < a) {x y : ℝ} : (y - m) / a < x ↔ y < raff a m x := by
  rw [div_lt_iff₀ ha, raff]; constructor <;> intro h <;> linarith

theorem lt_div_iff_raff (ha : 0 < a) {x y : ℝ} : x < (y - m) / a ↔ raff a m x < y := by
  rw [lt_div_iff₀ ha, raff]; constructor <;> intro h <;> linarith

theorem filter_lt_affData (ha : 0 < a) (hb : IsPiecewiseConstantBoundaryData b J) (x : ℝ) :
    (jumpSet (affData a m b) (affJumps a m J)).filter (· < raff a m x) =
      ((jumpSet b J).filter (· < x)).image (raff a m) := by
  ext y
  simp only [Finset.mem_filter, Finset.mem_image, mem_jumpSet_affData ha hb]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨_, ⟨h1, (div_lt_iff_raff ha).2 h2⟩, raff_div ha.ne' y⟩
  · rintro ⟨w, ⟨h1, h2⟩, rfl⟩
    have e : (raff a m w - m) / a = w := ((raff_eq_iff ha.ne').1 rfl).symm
    rw [e]
    exact ⟨h1, by simp only [raff]; nlinarith⟩

theorem filter_gt_affData (ha : 0 < a) (hb : IsPiecewiseConstantBoundaryData b J) (x : ℝ) :
    (jumpSet (affData a m b) (affJumps a m J)).filter (raff a m x < ·) =
      ((jumpSet b J).filter (x < ·)).image (raff a m) := by
  ext y
  simp only [Finset.mem_filter, Finset.mem_image, mem_jumpSet_affData ha hb]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨_, ⟨h1, (lt_div_iff_raff ha).2 h2⟩, raff_div ha.ne' y⟩
  · rintro ⟨w, ⟨h1, h2⟩, rfl⟩
    have e : (raff a m w - m) / a = w := ((raff_eq_iff ha.ne').1 rfl).symm
    rw [e]
    exact ⟨h1, by simp only [raff]; nlinarith⟩

theorem raff_strictMono (ha : 0 < a) : StrictMono (raff a m) := fun x y h => by
  simp only [raff]; nlinarith

/-- The increasing enumeration of `A(S)` is `A` of the increasing enumeration of `S`. -/
theorem orderEmbOfFin_image_raff (ha : 0 < a) {A A' : Finset ℝ} (hA : A' = A.image (raff a m)) {k k' : ℕ}
    (h : A.card = k) (h' : A'.card = k') (e : k' = k) (i : Fin k') :
    A'.orderEmbOfFin h' i = raff a m (A.orderEmbOfFin h (Fin.cast e i)) := by
  subst e hA
  have hf := Finset.orderEmbOfFin_unique h' (f := fun j => raff a m (A.orderEmbOfFin h j))
    (fun j => Finset.mem_image_of_mem _ (A.orderEmbOfFin_mem h _))
    (fun j j' hjj' => raff_strictMono ha ((A.orderEmbOfFin h).strictMono hjj'))
  rw [← hf]
  rfl

theorem card_filter_lt_affData (ha : 0 < a) (hb : IsPiecewiseConstantBoundaryData b J) (x : ℝ) :
    ((jumpSet (affData a m b) (affJumps a m J)).filter (· < raff a m x)).card =
      ((jumpSet b J).filter (· < x)).card := by
  rw [filter_lt_affData ha hb, Finset.card_image_of_injective _ (raff_injective ha.ne')]

theorem card_filter_gt_affData (ha : 0 < a) (hb : IsPiecewiseConstantBoundaryData b J) (x : ℝ) :
    ((jumpSet (affData a m b) (affJumps a m J)).filter (raff a m x < ·)).card =
      ((jumpSet b J).filter (x < ·)).card := by
  rw [filter_gt_affData ha hb, Finset.card_image_of_injective _ (raff_injective ha.ne')]

theorem flowLineNL_affData (ha : 0 < a) (hb : IsPiecewiseConstantBoundaryData b J) (x : ℝ) :
    flowLineNL (affData a m b) (affJumps a m J) (raff a m x) = flowLineNL b J x := by
  unfold flowLineNL
  rw [card_filter_lt_affData ha hb]

theorem flowLineNR_affData (ha : 0 < a) (hb : IsPiecewiseConstantBoundaryData b J) (x : ℝ) :
    flowLineNR (affData a m b) (affJumps a m J) (raff a m x) = flowLineNR b J x := by
  unfold flowLineNR
  rw [card_filter_gt_affData ha hb]

/-! ### The flow-line word -/

/-- Re-indexing a `Fin.cons` along `k' = k`, with a factor. -/
theorem cons_cast_mul {k k' : ℕ} (e : k' = k) {r a₀ a₀' : ℝ} {f : Fin k → ℝ} {f' : Fin k' → ℝ} (ha : a₀' = r * a₀)
    (hf : ∀ i, f' i = r * f (Fin.cast e i)) (e' : k' + 1 = k + 1) (j : Fin (k' + 1)) :
    (Fin.cons a₀' f' : Fin (k' + 1) → ℝ) j = r * (Fin.cons a₀ f : Fin (k + 1) → ℝ) (Fin.cast e' j) := by
  subst e
  refine Fin.cases ?_ (fun i => ?_) j
  · simp only [Fin.cast_eq_self, Fin.cons_zero, ha]
  · simp only [Fin.cast_eq_self, Fin.cons_succ, hf]

theorem raff_sub_raff (a m x y : ℝ) : raff a m y - raff a m x = a * (y - x) := by
  simp only [raff]; ring

theorem raff_div_self (ha : a ≠ 0) (x : ℝ) : (raff a m x - m) / a = x := ((raff_eq_iff ha).1 rfl).symm

variable (b J) in
theorem flowLineXL_affData_apply (ha : 0 < a) (hb : IsPiecewiseConstantBoundaryData b J) (x : ℝ)
    (j : Fin (flowLineNL (affData a m b) (affJumps a m J) (raff a m x))) :
    flowLineXL (affData a m b) (affJumps a m J) (raff a m x) j =
      a * flowLineXL b J x (Fin.cast (flowLineNL_affData ha hb x) j) := by
  unfold flowLineXL
  refine cons_cast_mul (card_filter_lt_affData ha hb x) (by ring) (fun i => ?_) _ j
  rw [orderEmbOfFin_image_raff ha (filter_lt_affData ha hb x) rfl rfl (card_filter_lt_affData ha hb x),
    Fin.cast_rev, raff_sub_raff]

variable (b J) in
theorem flowLineXR_affData_apply (ha : 0 < a) (hb : IsPiecewiseConstantBoundaryData b J) (x : ℝ)
    (j : Fin (flowLineNR (affData a m b) (affJumps a m J) (raff a m x))) :
    flowLineXR (affData a m b) (affJumps a m J) (raff a m x) j =
      a * flowLineXR b J x (Fin.cast (flowLineNR_affData ha hb x) j) := by
  unfold flowLineXR
  refine cons_cast_mul (card_filter_gt_affData ha hb x) (by ring) (fun i => ?_) _ j
  rw [orderEmbOfFin_image_raff ha (filter_gt_affData ha hb x) rfl rfl (card_filter_gt_affData ha hb x),
    raff_sub_raff]

variable (b J) in
theorem flowLineRhoL_affData_apply (ha : 0 < a) (hb : IsPiecewiseConstantBoundaryData b J) (κ x θ : ℝ)
    (j : Fin (flowLineNL (affData a m b) (affJumps a m J) (raff a m x))) :
    flowLineRhoL κ (affData a m b) (affJumps a m J) (raff a m x) θ j =
      flowLineRhoL κ b J x θ (Fin.cast (flowLineNL_affData ha hb x) j) := by
  unfold flowLineRhoL
  refine Sec7.FlowReflect.cons_cast (card_filter_lt_affData ha hb x) ?_ (fun i => ?_) _ j
  · rw [leftLim_affData ha hb, raff_div_self ha.ne']
  · simp only []
    rw [orderEmbOfFin_image_raff ha (filter_lt_affData ha hb x) rfl rfl (card_filter_lt_affData ha hb x),
      leftLim_affData ha hb, rightLim_affData ha hb, raff_div_self ha.ne', Fin.cast_rev]

variable (b J) in
theorem flowLineRhoR_affData_apply (ha : 0 < a) (hb : IsPiecewiseConstantBoundaryData b J) (κ x θ : ℝ)
    (j : Fin (flowLineNR (affData a m b) (affJumps a m J) (raff a m x))) :
    flowLineRhoR κ (affData a m b) (affJumps a m J) (raff a m x) θ j =
      flowLineRhoR κ b J x θ (Fin.cast (flowLineNR_affData ha hb x) j) := by
  unfold flowLineRhoR
  refine Sec7.FlowReflect.cons_cast (card_filter_gt_affData ha hb x) ?_ (fun i => ?_) _ j
  · rw [rightLim_affData ha hb, raff_div_self ha.ne']
  · simp only []
    rw [orderEmbOfFin_image_raff ha (filter_gt_affData ha hb x) rfl rfl (card_filter_gt_affData ha hb x),
      leftLim_affData ha hb, rightLim_affData ha hb, raff_div_self ha.ne']

/-! ### The translated field -/

theorem aff_add_raff (a m x : ℝ) (z : ℂ) : aff a 0 z + ((raff a m x : ℝ) : ℂ) = aff a m (z + (x : ℂ)) := by
  simp only [aff, raff, Complex.real_smul, Complex.ofReal_zero, add_zero]
  push_cast
  ring

theorem integral_affTest_zero (ha : 0 < a) (φ : TestOn upperHalfPlaneOpens) :
    ∫ z, affTest 0 ha φ z = ∫ z, φ z := by
  simp only [affTest_apply]
  rw [integral_const_mul, integral_comp_aff ha, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]

/-- **The translated field under `A`**: `h' = h(· + x) + c` gives, for `h ∘ A⁻¹` at the seed `A(x)`, the translated
field `h' ∘ (· / a)`. -/
theorem _root_.InteractingSLE.IsTranslateAddConst.affine (ha : 0 < a) {x c : ℝ} {f f' : DistOn upperHalfPlaneOpens}
    (ht : IsTranslateAddConst x c f f') :
    IsTranslateAddConst (raff a m x) c (affField m ha f) (affField 0 ha f') := by
  intro φ φ' hφ
  have h := ht (affTest m ha φ) (affTest 0 ha φ') fun z => by
    simp only [affTest_apply, hφ, aff_add_raff]
  rw [affField_apply, affField_apply, h, integral_affTest_zero]

/-! ### Flow lines -/

/-- The time change `c = a⁻²` of the space dilation by `a`. -/
def cDil (a : ℝ) : ℝ≥0 := (a⁻¹ ^ 2).toNNReal

theorem cDil_ne_zero (ha : 0 < a) : cDil a ≠ 0 := by
  rw [cDil]; exact (Real.toNNReal_pos.2 (by positivity)).ne'

theorem inv_sqrt_cDil (ha : 0 < a) : (√((cDil a : ℝ≥0) : ℝ))⁻¹ = a := by
  rw [cDil, Real.coe_toNNReal _ (by positivity), Real.sqrt_sq (by positivity), inv_inv]

theorem affField_eq_of_eq {a a' : ℝ} (e : a = a') (ha : 0 < a) (ha' : 0 < a') (h : DistOn upperHalfPlaneOpens) :
    affField m ha h = affField m ha' h := by
  subst e; rfl

/-- **Flow lines under `A(z) = a z + m`** (`a > 0`): if `η` is the angle-`θ` flow line from `x` of a field `h` with
piecewise-constant data `b`, then `t ↦ A(η(t/a²))` is the angle-`θ` flow line from `A(x)` of `h ∘ A⁻¹` (data
`y ↦ b((y − m)/a)`, jump candidates `A(J)`), with lifetime `a² ζ`. -/
theorem _root_.InteractingSLE.IsFlowLine.affine (ha : 0 < a) {κ x θ : ℝ} {Ω : Type u} [MeasurableSpace Ω]
    {P : Measure Ω} {h : Ω → DistOn upperHalfPlaneOpens} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    (hb : IsPiecewiseConstantBoundaryData b J) (hfl : IsFlowLine κ b J x θ P h η ζ) :
    IsFlowLine κ (affData a m b) (affJumps a m J) (raff a m x) θ P (fun ω => affField m ha (h ω))
      (fun ω t => aff a m (η ω (cDil a * t))) (fun ω => ζ ω / cDil a) := by
  obtain ⟨h', 𝓕, W, VL, VR, B, htr, hc, hgen⟩ := hfl
  have hc0 := cDil_ne_zero ha
  have hsq := inv_sqrt_cDil ha
  have hcd := isOptionalHullCoupling_dilate_affField hc0 (inv_pos.2 (sqrt_pos_of_ne hc0)) hc
  have hf : ∀ ω, affField 0 (inv_pos.2 (sqrt_pos_of_ne hc0)) (h' ω) = affField 0 ha (h' ω) := fun ω =>
    affField_eq_of_eq hsq _ _ _
  simp only [hf] at hcd
  rw [hsq] at hcd
  have hc' := Sec7.FlowReflect.IsOptionalHullCoupling.castR (flowLineNR_affData (m := m) ha hb x)
    (Sec7.FlowReflect.IsOptionalHullCoupling.castL (flowLineNL_affData (m := m) ha hb x) hcd)
  refine ⟨fun ω => affField 0 ha (h' ω), dilFiltration (cDil a) 𝓕, dilProc (cDil a) W,
    fun i => dilProc (cDil a) (VL (Fin.cast (flowLineNL_affData (m := m) ha hb x) i)),
    fun i => dilProc (cDil a) (VR (Fin.cast (flowLineNR_affData (m := m) ha hb x) i)), dilProc (cDil a) B,
    fun ω => IsTranslateAddConst.affine ha (htr ω), ?_, ?_⟩
  · have eXL := funext (flowLineXL_affData_apply (m := m) b J ha hb x)
    have eXR := funext (flowLineXR_affData_apply (m := m) b J ha hb x)
    have eRL := funext (flowLineRhoL_affData_apply (m := m) b J ha hb κ x θ)
    have eRR := funext (flowLineRhoR_affData_apply (m := m) b J ha hb κ x θ)
    rw [eXL, eXR, eRL, eRR]
    exact hc'
  · filter_upwards [hgen] with ω hω
    have h1 := hω.dilate hc0
    rw [hsq] at h1
    convert h1 using 2
    all_goals first
      | rfl
      | (simp only [aff, raff, Complex.real_smul]; push_cast; ring)

/-- **The GFF under `A`, with finite jump candidates**: data `y ↦ b((y − m)/a)` off `A(J)`. -/
theorem _root_.InteractingSLE.IsGFFWithBoundaryData.affine_finset (ha : 0 < a) {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b J) :
    IsGFFWithBoundaryData P (fun ω => affField m ha (h ω)) (affData a m b) (affJumps a m J) := by
  have e : ((affJumps a m J : Finset ℝ) : Set ℝ) = raff a m '' (J : Set ℝ) := by
    rw [affJumps, Finset.coe_image]
  rw [e]
  exact hh.affine ha

/-! ### The inverse map -/

theorem affData_inv (ha : a ≠ 0) (b : ℝ → ℝ) : affData a⁻¹ (-m / a) (affData a m b) = b := by
  funext y
  simp only [affData]
  congr 1
  field_simp
  ring

theorem affJumps_inv (ha : a ≠ 0) (J : Finset ℝ) : affJumps a⁻¹ (-m / a) (affJumps a m J) = J := by
  rw [affJumps, affJumps, Finset.image_image]
  have e : raff a⁻¹ (-m / a) ∘ raff a m = id := by
    funext x; simp only [Function.comp_apply, raff, id]; field_simp; ring
  rw [e, Finset.image_id]

theorem raff_inv (ha : a ≠ 0) (x : ℝ) : raff a⁻¹ (-m / a) (raff a m x) = x := by
  simp only [raff]; field_simp; ring

theorem cDil_mul_cDil_inv (ha : 0 < a) : cDil a * cDil a⁻¹ = 1 := by
  rw [← NNReal.coe_inj, NNReal.coe_mul, NNReal.coe_one, cDil, cDil, Real.coe_toNNReal _ (by positivity),
    Real.coe_toNNReal _ (by positivity), inv_inv]
  field_simp

/-- The inverse affine picture of the image curve is the original curve. -/
theorem aff_inv_comp (ha : 0 < a) (η : ℝ≥0 → ℂ) (t : ℝ≥0) :
    aff a⁻¹ (-m / a) ((fun t => aff a m (η (cDil a * t))) (cDil a⁻¹ * t)) = η t := by
  simp only
  rw [← mul_assoc, cDil_mul_cDil_inv ha, one_mul]
  exact affInv_aff ha.ne' (η t)

theorem div_cDil_div_cDil_inv (ha : 0 < a) (ζ₀ : ℝ≥0∞) : ζ₀ / cDil a / cDil a⁻¹ = ζ₀ := by
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_assoc,
    ← ENNReal.mul_inv (Or.inr ENNReal.coe_ne_top) (Or.inl ENNReal.coe_ne_top), ← ENNReal.coe_mul,
    cDil_mul_cDil_inv ha, ENNReal.coe_one, inv_one, mul_one]

end FlowDilate

end InteractingSLE
