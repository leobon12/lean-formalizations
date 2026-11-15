/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.FlowReflectCoupling
import InteractingSLE.Spec.Supplement.G12Statement
import InteractingSLE.Frozen.Spec.IsFlowLine
import InteractingSLE.Frozen.Spec.IsGFFWithBoundaryData
import InteractingSLE.Frozen.Spec.IsPiecewiseConstantBoundaryData

/-!
# Flow lines under the reflection `R(z) = −z̄`

Packet PROVE-LEMMA76C (specification p. 270: "Reflection and exchange of the path labels"). The reflection of the
field `h` with boundary data `b` is `−h ∘ R` with data `y ↦ −b(−y)` (`reflData`) and jump candidates `−J`
(`reflJumps`). Under it, the angle-`θ` flow line from `x` becomes the angle-`(−θ)` flow line from `−x`:

* `isPiecewiseConstantBoundaryData_reflData`, `leftLim_reflData`, `rightLim_reflData`, `jumpSet_reflData`;
* the flow-line word: `flowLineNL_reflData` (`= flowLineNR`), `flowLineXL_reflData` (`= −flowLineXR` after the index
  cast), `flowLineRhoL_reflData` (`= flowLineRhoR`), and the mirror statements;
* `IsOptionalHullCoupling.castL`, `castR`: re-indexing a side of a coupling along `n' = n`;
* **`IsGFFWithBoundaryData.reflect`** and **`IsFlowLine.reflect`**: the reflected field is a GFF with data
  `reflData b`, and `R ∘ η` is its flow line of angle `−θ` from `−x`, with the same lifetime.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal ComplexConjugate

open QuantumZipper (H)
open LQGMetric (TestOn DistOn)
universe u

namespace InteractingSLE

namespace Sec7

namespace FlowReflect

open LP (reflectC)
open PiecewiseConstantBoundaryData (leftLim rightLim jumpSet)

/-! ### Reflected boundary data -/

/-- The reflected boundary data `y ↦ −b(−y)`. -/
def reflData (b : ℝ → ℝ) : ℝ → ℝ := fun y => -b (-y)

/-- The reflected jump candidates `−J`. -/
def reflJumps (J : Finset ℝ) : Finset ℝ := J.map (Equiv.neg ℝ).toEmbedding

theorem mem_reflJumps {J : Finset ℝ} {y : ℝ} : y ∈ reflJumps J ↔ -y ∈ J := by
  rw [reflJumps, Finset.mem_map_equiv]
  rfl

theorem card_reflJumps (J : Finset ℝ) : (reflJumps J).card = J.card := Finset.card_map _

variable {b : ℝ → ℝ} {J : Finset ℝ}

theorem isPiecewiseConstantBoundaryData_reflData (hb : IsPiecewiseConstantBoundaryData b J) :
    IsPiecewiseConstantBoundaryData (reflData b) (reflJumps J) := by
  intro y hy
  have h := (continuous_neg.tendsto y).eventually (hb (-y) (fun h => hy (mem_reflJumps.2 h)))
  filter_upwards [h] with z hz
  simp only [reflData, hz]

theorem leftLim_reflData (hb : IsPiecewiseConstantBoundaryData b J) (y : ℝ) :
    leftLim (reflData b) y = -rightLim b (-y) := by
  obtain ⟨δ, hδ, h⟩ := Supp7.exists_pos_eq_lims hb (-y)
  refine Sec4.leftLim_eq_of_forall (by linarith : y - δ < y) fun t ht => ?_
  obtain ⟨-, -, hr, -⟩ := h (y - t) (by linarith [ht.2]) (by linarith [ht.1])
  simp only [reflData]
  rw [← hr]
  congr 2
  ring

theorem rightLim_reflData (hb : IsPiecewiseConstantBoundaryData b J) (y : ℝ) :
    rightLim (reflData b) y = -leftLim b (-y) := by
  obtain ⟨δ, hδ, h⟩ := Supp7.exists_pos_eq_lims hb (-y)
  refine Sec4.rightLim_eq_of_forall (by linarith : y < y + δ) fun t ht => ?_
  obtain ⟨-, -, -, hl⟩ := h (t - y) (by linarith [ht.1]) (by linarith [ht.2])
  simp only [reflData]
  rw [← hl]
  congr 2
  ring

theorem mem_jumpSet_reflData (hb : IsPiecewiseConstantBoundaryData b J) {y : ℝ} :
    y ∈ jumpSet (reflData b) (reflJumps J) ↔ -y ∈ jumpSet b J := by
  simp only [PiecewiseConstantBoundaryData.jumpSet, Finset.mem_filter, mem_reflJumps, leftLim_reflData hb,
    rightLim_reflData hb, ne_eq, neg_inj]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun h => h2 h.symm⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun h => h2 h.symm⟩

/-! ### Ordered marks -/

/-- The increasing enumeration of `−A` is minus the reversed enumeration of `A`. -/
theorem orderEmbOfFin_neg {A A' : Finset ℝ} (hA : ∀ y, y ∈ A' ↔ -y ∈ A) {k k' : ℕ} (h : A.card = k)
    (h' : A'.card = k') (e : k' = k) (i : Fin k') :
    A'.orderEmbOfFin h' (Fin.rev i) = -(A.orderEmbOfFin h (Fin.cast e i)) := by
  subst e
  have hf := Finset.orderEmbOfFin_unique h' (f := fun j => -(A.orderEmbOfFin h (Fin.rev j)))
    (fun j => (hA _).2 (by rw [neg_neg]; exact A.orderEmbOfFin_mem h _))
    (fun j j' hjj' => neg_lt_neg ((A.orderEmbOfFin h).strictMono (Fin.rev_lt_rev.2 hjj')))
  rw [← hf]
  simp only [Fin.rev_rev]
  rfl

variable (b J) in
/-- The left marks of the reflected word are the reflected right marks. -/
theorem filter_lt_neg_iff (hb : IsPiecewiseConstantBoundaryData b J) (x y : ℝ) :
    y ∈ (jumpSet (reflData b) (reflJumps J)).filter (· < -x) ↔ -y ∈ (jumpSet b J).filter (x < ·) := by
  simp only [Finset.mem_filter, mem_jumpSet_reflData hb]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith⟩

variable (b J) in
theorem filter_gt_neg_iff (hb : IsPiecewiseConstantBoundaryData b J) (x y : ℝ) :
    y ∈ (jumpSet (reflData b) (reflJumps J)).filter (-x < ·) ↔ -y ∈ (jumpSet b J).filter (· < x) := by
  simp only [Finset.mem_filter, mem_jumpSet_reflData hb]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith⟩

theorem card_filter_lt_neg (hb : IsPiecewiseConstantBoundaryData b J) (x : ℝ) :
    ((jumpSet (reflData b) (reflJumps J)).filter (· < -x)).card = ((jumpSet b J).filter (x < ·)).card := by
  have e : (jumpSet (reflData b) (reflJumps J)).filter (· < -x) = reflJumps ((jumpSet b J).filter (x < ·)) := by
    ext y
    rw [filter_lt_neg_iff b J hb, mem_reflJumps]
  rw [e, card_reflJumps]

theorem card_filter_gt_neg (hb : IsPiecewiseConstantBoundaryData b J) (x : ℝ) :
    ((jumpSet (reflData b) (reflJumps J)).filter (-x < ·)).card = ((jumpSet b J).filter (· < x)).card := by
  have e : (jumpSet (reflData b) (reflJumps J)).filter (-x < ·) = reflJumps ((jumpSet b J).filter (· < x)) := by
    ext y
    rw [filter_gt_neg_iff b J hb, mem_reflJumps]
  rw [e, card_reflJumps]

theorem flowLineNL_reflData (hb : IsPiecewiseConstantBoundaryData b J) (x : ℝ) :
    flowLineNL (reflData b) (reflJumps J) (-x) = flowLineNR b J x := by
  unfold flowLineNL flowLineNR
  rw [card_filter_lt_neg hb]

theorem flowLineNR_reflData (hb : IsPiecewiseConstantBoundaryData b J) (x : ℝ) :
    flowLineNR (reflData b) (reflJumps J) (-x) = flowLineNL b J x := by
  unfold flowLineNL flowLineNR
  rw [card_filter_gt_neg hb]

theorem orderEmbOfFin_neg' {A A' : Finset ℝ} (hA : ∀ y, y ∈ A' ↔ -y ∈ A) {k k' : ℕ} (h : A.card = k)
    (h' : A'.card = k') (e : k' = k) (i : Fin k') :
    A'.orderEmbOfFin h' i = -(A.orderEmbOfFin h (Fin.rev (Fin.cast e i))) := by
  have h1 := orderEmbOfFin_neg hA h h' e (Fin.rev i)
  rw [Fin.rev_rev] at h1
  rw [h1]
  congr 3
  ext
  simp only [Fin.val_cast, Fin.val_rev]
  omega

/-! ### The flow-line word -/

/-- Re-indexing a `Fin.cons` along `m' = m`, with a sign. -/
theorem cons_cast_neg {m m' : ℕ} (e : m' = m) {a a' : ℝ} {f : Fin m → ℝ} {f' : Fin m' → ℝ} (ha : a' = -a)
    (hf : ∀ i, f' i = -f (Fin.cast e i)) (e' : m' + 1 = m + 1) (j : Fin (m' + 1)) :
    (Fin.cons a' f' : Fin (m' + 1) → ℝ) j = -(Fin.cons a f : Fin (m + 1) → ℝ) (Fin.cast e' j) := by
  subst e
  refine Fin.cases ?_ (fun i => ?_) j
  · simp only [Fin.cast_eq_self, Fin.cons_zero, ha]
  · simp only [Fin.cast_eq_self, Fin.cons_succ, hf]

/-- Re-indexing a `Fin.cons` along `m' = m`. -/
theorem cons_cast {m m' : ℕ} (e : m' = m) {a a' : ℝ} {f : Fin m → ℝ} {f' : Fin m' → ℝ} (ha : a' = a)
    (hf : ∀ i, f' i = f (Fin.cast e i)) (e' : m' + 1 = m + 1) (j : Fin (m' + 1)) :
    (Fin.cons a' f' : Fin (m' + 1) → ℝ) j = (Fin.cons a f : Fin (m + 1) → ℝ) (Fin.cast e' j) := by
  subst e
  refine Fin.cases ?_ (fun i => ?_) j
  · simp only [Fin.cast_eq_self, Fin.cons_zero, ha]
  · simp only [Fin.cast_eq_self, Fin.cons_succ, hf]

variable (b J) in
theorem flowLineXL_reflData_apply (hb : IsPiecewiseConstantBoundaryData b J) (x : ℝ)
    (j : Fin (flowLineNL (reflData b) (reflJumps J) (-x))) :
    flowLineXL (reflData b) (reflJumps J) (-x) j = -flowLineXR b J x (Fin.cast (flowLineNL_reflData hb x) j) := by
  unfold flowLineXL flowLineXR
  refine cons_cast_neg (card_filter_lt_neg hb x) (neg_zero (G := ℝ)).symm (fun i => ?_) _ j
  rw [orderEmbOfFin_neg (fun y => filter_lt_neg_iff b J hb x y) rfl rfl (card_filter_lt_neg hb x) i]
  ring

variable (b J) in
theorem flowLineXR_reflData_apply (hb : IsPiecewiseConstantBoundaryData b J) (x : ℝ)
    (j : Fin (flowLineNR (reflData b) (reflJumps J) (-x))) :
    flowLineXR (reflData b) (reflJumps J) (-x) j = -flowLineXL b J x (Fin.cast (flowLineNR_reflData hb x) j) := by
  unfold flowLineXL flowLineXR
  refine cons_cast_neg (card_filter_gt_neg hb x) (neg_zero (G := ℝ)).symm (fun i => ?_) _ j
  rw [orderEmbOfFin_neg' (fun y => filter_gt_neg_iff b J hb x y) rfl rfl (card_filter_gt_neg hb x) i]
  ring

variable (b J) in
theorem flowLineRhoL_reflData_apply (hb : IsPiecewiseConstantBoundaryData b J) (κ x θ : ℝ)
    (j : Fin (flowLineNL (reflData b) (reflJumps J) (-x))) :
    flowLineRhoL κ (reflData b) (reflJumps J) (-x) (-θ) j =
      flowLineRhoR κ b J x θ (Fin.cast (flowLineNL_reflData hb x) j) := by
  unfold flowLineRhoL flowLineRhoR
  refine cons_cast (card_filter_lt_neg hb x) ?_ (fun i => ?_) _ j
  · rw [leftLim_reflData hb, neg_neg]
    ring
  · simp only []
    rw [orderEmbOfFin_neg (fun y => filter_lt_neg_iff b J hb x y) rfl rfl (card_filter_lt_neg hb x) i,
      leftLim_reflData hb, rightLim_reflData hb, neg_neg]
    ring

variable (b J) in
theorem flowLineRhoR_reflData_apply (hb : IsPiecewiseConstantBoundaryData b J) (κ x θ : ℝ)
    (j : Fin (flowLineNR (reflData b) (reflJumps J) (-x))) :
    flowLineRhoR κ (reflData b) (reflJumps J) (-x) (-θ) j =
      flowLineRhoL κ b J x θ (Fin.cast (flowLineNR_reflData hb x) j) := by
  unfold flowLineRhoL flowLineRhoR
  refine cons_cast (card_filter_gt_neg hb x) ?_ (fun i => ?_) _ j
  · rw [rightLim_reflData hb, neg_neg]
    ring
  · simp only []
    rw [orderEmbOfFin_neg' (fun y => filter_gt_neg_iff b J hb x y) rfl rfl (card_filter_gt_neg hb x) i,
      leftLim_reflData hb, rightLim_reflData hb, neg_neg]
    ring

/-! ### Re-indexing a side of a coupling -/

section Cast

variable {κ : ℝ} {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}

theorem IsOptionalHullCoupling.castL {n n' nR : ℕ} (e : n' = n) {xL ρL : Fin n → ℝ} {xR ρR : Fin nR → ℝ}
    {VL : Fin n → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    (hc : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h) :
    IsOptionalHullCoupling κ (fun i : Fin n' => xL (Fin.cast e i)) xR (fun i => ρL (Fin.cast e i)) ρR P 𝓕 W
      (fun i => VL (Fin.cast e i)) VR B ζ h := by
  subst e
  exact hc

theorem IsOptionalHullCoupling.castR {n n' nL : ℕ} (e : n' = n) {xL ρL : Fin nL → ℝ} {xR ρR : Fin n → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin n → ℝ≥0 → Ω → ℝ}
    (hc : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h) :
    IsOptionalHullCoupling κ xL (fun i : Fin n' => xR (Fin.cast e i)) ρL (fun i => ρR (Fin.cast e i)) P 𝓕 W
      VL (fun i => VR (Fin.cast e i)) B ζ h := by
  subst e
  exact hc

end Cast

/-! ### Fields and flow lines -/

/-- The reflected field shifted: `h' = h(· + x) + c` gives `−h' ∘ R = (−h ∘ R)(· − x) − c`. -/
theorem IsTranslateAddConst.reflect {x c : ℝ} {f f' : DistOn upperHalfPlaneOpens} (ht : IsTranslateAddConst x c f f') :
    IsTranslateAddConst (-x) (-c) (reflField f) (reflField f') := by
  intro φ φ' hφ
  have h := ht (reflTest φ) (reflTest φ') fun z => by
    simp only [reflTest_apply, hφ]
    congr 1
    simp only [LP.reflectC, map_add, Complex.conj_ofReal]
    push_cast
    ring
  have hi : ∫ z, reflTest φ' z = ∫ z, φ' z := integral_comp_reflectC (fun z => φ' z)
  rw [reflField_apply, reflField_apply, h, hi]
  ring

/-- The pairing with a reflected mean: `∫ (−u ∘ R)(φ ∘ R) = −∫ u φ`. -/
theorem integral_refl_mean (u : ℂ → ℝ) (φ : TestOn upperHalfPlaneOpens) :
    ∫ z, (fun y => -u (reflectC y)) z * reflTest φ z = -∫ z, u z * φ z := by
  rw [← integral_neg, ← integral_comp_reflectC (fun z => -(u z * φ z))]
  congr 1
  funext z
  simp only [reflTest_apply, neg_mul]

/-- The GFF process of the reflected field with the reflected mean. -/
theorem isZBGFFProcess_reflField {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistOn upperHalfPlaneOpens}
    {u : ℂ → ℝ}
    (hX : LQGMetric.IsZBGFFProcess upperHalfPlaneOpens
      (fun φ ω => h ω φ - ∫ z, (fun y => -u (reflectC y)) z * φ z) P) :
    LQGMetric.IsZBGFFProcess upperHalfPlaneOpens (fun φ ω => reflField (h ω) φ - ∫ z, u z * φ z) P := by
  have hZ := isZBGFFProcess_refl hX
  have e : (fun φ ω => reflField (h ω) φ - ∫ z, u z * φ z) = fun φ ω =>
      -(h ω (reflTest φ) - ∫ z, (fun y => -u (reflectC y)) z * reflTest φ z) := by
    funext φ ω
    rw [integral_refl_mean, reflField_apply]
    ring
  rw [e]
  exact hZ

/-- **The reflected GFF**: if `h` is a GFF on `ℍ` with piecewise-constant data `b`, then `−h ∘ R` is a GFF with data
`y ↦ −b(−y)` (jump candidates `−J`). -/
theorem IsGFFWithBoundaryData.reflect {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b J) :
    IsGFFWithBoundaryData P (fun ω => reflField (h ω)) (reflData b) (reflJumps J : Set ℝ) := by
  refine ⟨measurable_reflField.comp hh.1, fun u hu => isZBGFFProcess_reflField (hh.2 _ ?_)⟩
  refine IsBoundedHarmonicExtension.reflect hu fun y hy => ⟨fun h => hy ?_, ?_⟩
  · have h' : -y ∈ reflJumps J := h
    rw [mem_reflJumps, neg_neg] at h'
    exact h'
  · simp only [reflData, neg_neg]

/-- **Flow lines under `R(z) = −z̄`**: if `η` is the angle-`θ` flow line from `x` of a field `h` with
piecewise-constant data `b`, then `R ∘ η` is the angle-`(−θ)` flow line from `−x` of `−h ∘ R` (data `y ↦ −b(−y)`),
with the same lifetime. -/
theorem IsFlowLine.reflect {κ x θ : ℝ} {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistOn upperHalfPlaneOpens} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    (hb : IsPiecewiseConstantBoundaryData b J) (hfl : IsFlowLine κ b J x θ P h η ζ) :
    IsFlowLine κ (reflData b) (reflJumps J) (-x) (-θ) P (fun ω => reflField (h ω))
      (fun ω t => LP.reflectC (η ω t)) ζ := by
  obtain ⟨h', 𝓕, W, VL, VR, B, htr, hc, hgen⟩ := hfl
  have hc' := IsOptionalHullCoupling.castR (flowLineNR_reflData hb x)
    (IsOptionalHullCoupling.castL (flowLineNL_reflData hb x) (IsOptionalHullCoupling.reflect hc))
  refine ⟨fun ω => reflField (h' ω), 𝓕, -W, fun i => fun t ω => -VR (Fin.cast (flowLineNL_reflData hb x) i) t ω,
    fun i => fun t ω => -VL (Fin.cast (flowLineNR_reflData hb x) i) t ω, -B, fun ω => ?_, ?_, ?_⟩
  · have h1 := IsTranslateAddConst.reflect (htr ω)
    rwa [← neg_mul] at h1
  · have eXL := funext (flowLineXL_reflData_apply b J hb x)
    have eXR := funext (flowLineXR_reflData_apply b J hb x)
    have eRL := funext (flowLineRhoL_reflData_apply b J hb κ x θ)
    have eRR := funext (flowLineRhoR_reflData_apply b J hb κ x θ)
    rw [eXL, eXR, eRL, eRR]
    exact hc'
  · filter_upwards [hgen] with ω hω
    have h1 := LP.isGeneratingTrace_reflect hω
    convert h1 using 2 with t
    all_goals first
      | rfl
      | (simp only [LP.reflectC, map_sub, Complex.conj_ofReal, Complex.ofReal_neg]; ring)

end FlowReflect

end Sec7

end InteractingSLE
