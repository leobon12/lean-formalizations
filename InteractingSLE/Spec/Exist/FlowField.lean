/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec4.Prob41Flow
import InteractingSLE.Frozen.Spec.forceBoundaryData
import InteractingSLE.Frozen.Spec.forceJumpSet
import InteractingSLE.Frozen.Spec.IsTranslateAddConst
import InteractingSLE.Frozen.Spec.IsGFFWithBoundaryData
import InteractingSLE.GFF.PushforwardLaw
import InteractingSLE.Foundations.Harmonic.MaxPrinciple
import InteractingSLE.Impl.PiecewiseConstant
import InteractingSLE.Spec.Coupling.MartMeans2Chart

/-!
# The field of a flow line: `h(· + x) + θχ`, its boundary data and its law

Packet PROVE-FLOWEXIST, step 1 of `exists_isFlowLine` (Theorem 1.5's non-vacuity companion). The frozen
`IsFlowLine κ b jumps x θ P h η ζ` couples the flow-line driving evolution with the field `h' = h(· + x) + θχ`
(`IsTranslateAddConst x (θχ) h h'`), whose boundary data is the force-word data of the flow-line word
(`flowLineXL`, `flowLineXR`, `flowLineRhoL`, `flowLineRhoR` at seed `x` and angle `θ`). This file:

* **`forceBoundaryData_flowLine_seed`**: off the seed and the translated jump candidates, the force-word boundary data
  of the flow-line word from `x` at angle `θ` is `b(· + x) + θχ` (the identity asserted in the frozen docstrings of
  `flowLineRhoL`/`flowLineRhoR`; PROVE-SEC4's `Sec4.forceBoundaryData_flowLine` is the case `x = 0`, `θ = 0`);
* `shiftChart x = Chart.id.recenter x` (the real translation `z ↦ z − x`) and **`flowField x a h`**, the distribution
  `h(· + x) + a`, built as PROVE-PUSHFWD's chart transport; `isTranslateAddConst_flowField`, `measurable_flowField`;
* **`isGFFWithBoundaryData_flowField`**: if `h` is a GFF on `ℍ` with piecewise-constant data `b`, then
  `h(· + x) + θχ` is a GFF with the force-word data of the flow-line word (translation invariance of the zero-boundary
  covariance, through PROVE-PUSHFWD's conformal invariance);
* **`map_eq_of_isGFFWithBoundaryData`**: two GFFs with the same boundary data have the same law on `𝒟'(ℍ)`
  (LQGMetric's `IsZBGFFProcess.map_eq`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Finset
open QuantumZipper (H isOpen_H)
open LQGMetric (TestOn DistOn)
open TopologicalSpace (Opens)
open scoped Laplacian

namespace InteractingSLE

namespace Exist

open PiecewiseConstantBoundaryData (leftLim rightLim jumpSet)

variable {b : ℝ → ℝ} {J : Finset ℝ}

/-! ### Translating piecewise-constant data -/

theorem map_add_const_nhdsLT (x z : ℝ) : Filter.map (· + x) (𝓝[<] z) = 𝓝[<] (z + x) := by
  have h := (Homeomorph.addRight x).isEmbedding.map_nhdsWithin_eq (Set.Iio z) z
  simpa only [Homeomorph.coe_addRight, Set.image_add_const_Iio] using h

theorem map_add_const_nhdsGT (x z : ℝ) : Filter.map (· + x) (𝓝[>] z) = 𝓝[>] (z + x) := by
  have h := (Homeomorph.addRight x).isEmbedding.map_nhdsWithin_eq (Set.Ioi z) z
  simpa only [Homeomorph.coe_addRight, Set.image_add_const_Ioi] using h

theorem leftLim_comp_add (b : ℝ → ℝ) (x z : ℝ) : leftLim (fun y => b (y + x)) z = leftLim b (z + x) := by
  show lim (Filter.map (b ∘ (· + x)) (𝓝[<] z)) = lim (Filter.map b (𝓝[<] (z + x)))
  rw [← Filter.map_map, map_add_const_nhdsLT]

theorem rightLim_comp_add (b : ℝ → ℝ) (x z : ℝ) :
    rightLim (fun y => b (y + x)) z = rightLim b (z + x) := by
  show lim (Filter.map (b ∘ (· + x)) (𝓝[>] z)) = lim (Filter.map b (𝓝[>] (z + x)))
  rw [← Filter.map_map, map_add_const_nhdsGT]

theorem isPiecewiseConstant_comp_add (hb : IsPiecewiseConstantBoundaryData b J) (x : ℝ) :
    IsPiecewiseConstantBoundaryData (fun y => b (y + x)) (J.image (· - x)) := by
  intro y hy
  have hyx : y + x ∉ J := fun h => hy (Finset.mem_image.2 ⟨y + x, h, by ring⟩)
  exact (((continuous_id.add continuous_const : Continuous fun z : ℝ => z + x)).tendsto y).eventually
    (hb (y + x) hyx)

/-- Reindexing a sum over the translated jump candidates. -/
theorem sum_filter_image_sub (x : ℝ) (P : ℝ → Prop) [DecidablePred P] :
    ∑ z ∈ (J.image (· - x)).filter P,
        (rightLim (fun y => b (y + x)) z - leftLim (fun y => b (y + x)) z) =
      ∑ z ∈ J.filter (fun z => P (z - x)), (rightLim b z - leftLim b z) := by
  rw [Finset.filter_image, Finset.sum_image fun a _ c _ h => by simpa using h]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [rightLim_comp_add, leftLim_comp_add, sub_add_cancel]

/-- **Left telescoping to a seed `x`.** For `y < x` off the jump candidates,
`b y = b(x⁻) − ∑_{z ∈ J ∩ (y, x)} (b(z⁺) − b(z⁻))`. -/
theorem eq_leftLim_sub_sum_seed (hb : IsPiecewiseConstantBoundaryData b J) {x y : ℝ} (hy : y < x)
    (hyJ : y ∉ J) :
    b y = leftLim b x - ∑ z ∈ J.filter (fun z => y < z ∧ z < x), (rightLim b z - leftLim b z) := by
  have hyJ' : y - x ∉ J.image (· - x) := fun h => by
    obtain ⟨z, hz, hzy⟩ := Finset.mem_image.1 h
    have : z = y := by linarith
    exact hyJ (this ▸ hz)
  have h := Sec4.eq_leftLim_sub_sum_of_isPiecewiseConstant (isPiecewiseConstant_comp_add hb x)
    (x := y - x) (by linarith) hyJ'
  rw [sub_add_cancel, leftLim_comp_add, zero_add, sum_filter_image_sub] at h
  rw [h]
  congr 2
  exact Finset.filter_congr fun z _ => by constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- **Right telescoping from a seed `x`.** For `y > x` off the jump candidates,
`b y = b(x⁺) + ∑_{z ∈ J ∩ (x, y)} (b(z⁺) − b(z⁻))`. -/
theorem eq_rightLim_add_sum_seed (hb : IsPiecewiseConstantBoundaryData b J) {x y : ℝ} (hy : x < y)
    (hyJ : y ∉ J) :
    b y = rightLim b x + ∑ z ∈ J.filter (fun z => x < z ∧ z < y), (rightLim b z - leftLim b z) := by
  have hyJ' : y - x ∉ J.image (· - x) := fun h => by
    obtain ⟨z, hz, hzy⟩ := Finset.mem_image.1 h
    have : z = y := by linarith
    exact hyJ (this ▸ hz)
  have h := Sec4.eq_rightLim_add_sum_of_isPiecewiseConstant (isPiecewiseConstant_comp_add hb x)
    (x := y - x) (by linarith) hyJ'
  rw [sub_add_cancel, rightLim_comp_add, zero_add, sum_filter_image_sub] at h
  rw [h]
  congr 2
  exact Finset.filter_congr fun z _ => by constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-! ### The flow-line word from `x` at angle `θ` reproduces `b(· + x) + θχ` -/

/-- Left prefix sums of the flow-line word from `x` at angle `θ`. -/
theorem sum_filter_flowLineXL_seed {κ : ℝ} (x θ : ℝ) {y : ℝ} (hy : y < 0) :
    ∑ i ∈ univ.filter (fun i => y < flowLineXL b J x i), flowLineRhoL κ b J x θ i =
      (-(leftLim b x + θ * QuantumZipper.chiC κ) / sleLambda κ - 1) +
        (∑ z ∈ J.filter (fun z => y + x < z ∧ z < x), (rightLim b z - leftLim b z)) / sleLambda κ := by
  unfold flowLineXL flowLineRhoL flowLineNL
  rw [Sec4.sum_filter_lt_cons]
  simp only [hy, ↓reduceIte]
  have h := Sec4.sum_filter_orderEmbOfFin_rev ((jumpSet b J).filter (· < x)) (fun z => y < z - x)
    (fun z => (rightLim b z - leftLim b z) / sleLambda κ)
  rw [h, ← Finset.sum_div, Finset.filter_filter, Sec4.sum_jumpSet_filter]
  congr 3
  exact Finset.filter_congr fun z _ => by constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- Right prefix sums of the flow-line word from `x` at angle `θ`, at a point `y > 0` with `y + x` off the jump
candidates. -/
theorem sum_filter_flowLineXR_seed {κ : ℝ} (x θ : ℝ) {y : ℝ} (hy : 0 < y) (hyJ : y + x ∉ J) :
    ∑ i ∈ univ.filter (fun i => flowLineXR b J x i ≤ y), flowLineRhoR κ b J x θ i =
      ((rightLim b x + θ * QuantumZipper.chiC κ) / sleLambda κ - 1) +
        (∑ z ∈ J.filter (fun z => x < z ∧ z < y + x), (rightLim b z - leftLim b z)) / sleLambda κ := by
  unfold flowLineXR flowLineRhoR flowLineNR
  rw [Sec4.sum_filter_le_cons]
  simp only [hy.le, ↓reduceIte]
  have h := Sec4.sum_filter_orderEmbOfFin ((jumpSet b J).filter (x < ·)) (fun z => z - x ≤ y)
    (fun z => (rightLim b z - leftLim b z) / sleLambda κ)
  rw [h, ← Finset.sum_div, Finset.filter_filter, Sec4.sum_jumpSet_filter]
  congr 3
  refine Finset.filter_congr fun z hz => ?_
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, lt_of_le_of_ne (by linarith) fun he => hyJ (he ▸ hz)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by linarith⟩

/-- **The flow-line word from `x` at angle `θ` reproduces the boundary data**: off the seed and the translated jump
candidates, the force-word boundary data of Theorem 1.1 of the flow-line word is `b(· + x) + θχ` (the identity of
the frozen `flowLineRhoL`/`flowLineRhoR` docstrings). -/
theorem forceBoundaryData_flowLine_seed {κ : ℝ} (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b J)
    (x θ : ℝ) {y : ℝ} (hy0 : y ≠ 0) (hyJ : y + x ∉ J) :
    forceBoundaryData κ (flowLineRhoL κ b J x θ) (flowLineRhoR κ b J x θ) (flowLineXL b J x)
      (flowLineXR b J x) y = b (y + x) + θ * QuantumZipper.chiC κ := by
  have hΛ : sleLambda κ ≠ 0 := (Sec4.sleLambda_pos hκ).ne'
  have hL : Real.pi / Real.sqrt κ = sleLambda κ := rfl
  unfold forceBoundaryData
  rw [hL]
  rcases lt_or_gt_of_ne hy0 with hy | hy
  · simp only [hy, ↓reduceIte]
    rw [sum_filter_flowLineXL_seed x θ hy, eq_leftLim_sub_sum_seed hb (x := x) (y := y + x) (by linarith) hyJ]
    field_simp
    ring
  · simp only [not_lt.2 hy.le, ↓reduceIte]
    rw [sum_filter_flowLineXR_seed x θ hy hyJ, eq_rightLim_add_sum_seed hb (x := x) (y := y + x) (by linarith) hyJ]
    field_simp
    ring

/-! ### The translated field `h(· + x) + a` -/

/-- The real translation chart `z ↦ z − x` of `ℍ` (inverse `w ↦ w + x`, lift `0`). -/
def shiftChart (x : ℝ) : Chart := Chart.id.recenter x

theorem isConformal_shiftChart (x : ℝ) : (shiftChart x).IsConformal := Chart.isConformal_id.recenter x

theorem shiftChart_dom (x : ℝ) : (shiftChart x).dom = upperHalfPlaneOpens := by
  rw [shiftChart, Chart.dom_recenter]
  ext z
  change z ∈ interior ((fun w : ℂ => w) '' H) ↔ z ∈ H
  rw [Set.image_id', isOpen_H.interior_eq]

/-- **The field `h(· + x) + a`** (PROVE-PUSHFWD's chart transport by the translation chart). -/
def flowField (x a : ℝ) (h : DistOn upperHalfPlaneOpens) : DistOn upperHalfPlaneOpens :=
  Chart.chartTransport (isConformal_shiftChart x) 1 a 0 h

theorem notMem_H_sub {z : ℂ} (hz : z ∉ H) (x : ℝ) : z - x ∉ H := fun h => hz <| by
  change 0 < z.im
  have : 0 < (z - x).im := h
  simpa only [Complex.sub_im, Complex.ofReal_im, sub_zero] using this

theorem pushTest_shiftChart_apply (x : ℝ) (φ : TestOn upperHalfPlaneOpens) (z : ℂ) :
    Chart.pushTest (isConformal_shiftChart x) φ z = φ (z - x) := by
  rw [Chart.coe_pushTest, shiftChart_dom]
  by_cases hz : z ∈ H
  · rw [indicator_of_mem (show z ∈ ((upperHalfPlaneOpens : Opens ℂ) : Set ℂ) from hz)]
    change ‖deriv (fun w : ℂ => w - x) z‖ ^ 2 * φ (z - x) = φ (z - x)
    rw [deriv_sub_const, deriv_id'', norm_one, one_pow, one_mul]
  · rw [indicator_of_notMem (show z ∉ ((upperHalfPlaneOpens : Opens ℂ) : Set ℂ) from hz)]
    exact (φ.zero_on_compl (show z - x ∈ ((upperHalfPlaneOpens : Set ℂ))ᶜ from notMem_H_sub hz x)).symm

theorem flowField_apply (x a : ℝ) (h : DistOn upperHalfPlaneOpens) (φ : TestOn upperHalfPlaneOpens) :
    flowField x a h φ = h (Chart.pushTest (isConformal_shiftChart x) φ) + a * ∫ w, φ w := by
  rw [flowField, Chart.chartTransport_apply', Chart.oneDist_apply]
  ring

/-- `flowField x a h` is `h(· + x) + a` in the sense of the frozen `IsTranslateAddConst`. -/
theorem isTranslateAddConst_flowField (x a : ℝ) (h : DistOn upperHalfPlaneOpens) :
    IsTranslateAddConst x a h (flowField x a h) := by
  intro φ φ' hφ
  rw [flowField_apply]
  congr 2
  ext z
  rw [pushTest_shiftChart_apply, hφ, sub_add_cancel]

theorem measurable_flowField (x a : ℝ) : Measurable (flowField x a) :=
  Chart.measurable_chartTransport _ 1 a 0

/-- Translation preserves harmonicity (as QuantumZipper's `Prop16Asm.harmonicAt_comp_add_const_mm`). -/
theorem harmonicAt_comp_add_const {f : ℂ → ℝ} {z a : ℂ} (h : InnerProductSpace.HarmonicAt f (z + a)) :
    InnerProductSpace.HarmonicAt (fun w => f (w + a)) z := by
  have hΔ : Δ (fun w => f (w + a)) = fun w => Δ f (w + a) := by
    rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis,
      InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
    funext w
    simp only [iteratedFDeriv_comp_add_right]
  refine ⟨h.1.comp z (contDiffAt_id.add contDiffAt_const), ?_⟩
  rw [hΔ]
  exact h.2.comp_tendsto ((continuous_id.add continuous_const).tendsto z)

theorem add_real_mem_H {z : ℂ} (hz : z ∈ H) (x : ℝ) : z + x ∈ H := by
  change 0 < (z + x).im
  rw [Complex.add_im, Complex.ofReal_im, add_zero]
  exact hz

/-- **The translated field of a GFF with mean `m`** is a GFF with mean `m(· + x) + a`. -/
theorem isZBGFFProcess_flowField {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistOn upperHalfPlaneOpens} {m : ℂ → ℝ}
    (hX : LQGMetric.IsZBGFFProcess upperHalfPlaneOpens (fun φ ω => h ω φ - ∫ z, m z * φ z) P) (x a : ℝ)
    (hmi : ∀ φ : TestOn upperHalfPlaneOpens, Integrable (fun w => m (w + x) * φ w)) :
    LQGMetric.IsZBGFFProcess upperHalfPlaneOpens
      (fun φ ω => flowField x a (h ω) φ - ∫ w, (m (w + x) + a) * φ w) P := by
  have key : ∀ U : Opens ℂ, U = upperHalfPlaneOpens → LQGMetric.IsZBGFFProcess U
      (fun ψ ω => h ω (GFF.testIncl U upperHalfPlaneOpens ψ) - ∫ z, m z * ψ z) P := by
    rintro U rfl
    have hid : ∀ ψ : TestOn upperHalfPlaneOpens,
        GFF.testIncl upperHalfPlaneOpens upperHalfPlaneOpens ψ = ψ := fun ψ => by
      ext z
      exact congrFun (GFF.coe_testIncl le_rfl ψ) z
    simp only [hid]
    exact hX
  have hℓ : LocallyIntegrableOn (fun w => (shiftChart x).2.2 ((shiftChart x).2.1 w)) H :=
    Chart.locallyIntegrableOn_of_continuousOn (Chart.continuousOn_recenter_lift Chart.continuousOn_id_lift)
  have h1 := Chart.isZBGFFProcess_chartTransport (isConformal_shiftChart x) hℓ (m := m) 0
    (key _ (shiftChart_dom x))
  convert h1 using 2 with φ
  funext ω
  have hφi : Integrable (fun w => a * φ w) :=
    (φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport).const_mul a
  have e : ∫ w, (m (w + x) + a) * φ w = (∫ w, m (w + x) * φ w) + a * ∫ w, φ w := by
    rw [← integral_const_mul, ← integral_add (hmi φ) hφi]
    congr 1
    funext w
    ring
  rw [flowField_apply, e, Chart.chartTransport_apply', Chart.oneDist_apply]
  change _ = _ - ((∫ w, m (w + x) * φ w) + 0 * _)
  ring

/-! ### The boundary data of the flow-line field -/

/-- The finite exceptional set of the flow-line field: the seed, the marks and the translated jump candidates. -/
def flowExcept (b : ℝ → ℝ) (J : Finset ℝ) (x : ℝ) : Finset ℝ :=
  insert 0 ((univ.image (flowLineXL b J x) ∪ univ.image (flowLineXR b J x)) ∪ J.image (· - x))

theorem notMem_forceJumpSet_of_notMem_flowExcept {x t : ℝ} (ht : t ∉ flowExcept b J x) :
    t ∉ forceJumpSet (flowLineXL b J x) (flowLineXR b J x) := by
  rintro (h0 | ⟨i, hi⟩ | ⟨i, hi⟩)
  · exact ht (Finset.mem_insert.2 (Or.inl h0))
  · exact ht (Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_image.2 ⟨i, Finset.mem_univ _, hi⟩))))
  · exact ht (Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_image.2 ⟨i, Finset.mem_univ _, hi⟩))))

theorem ne_zero_of_notMem_flowExcept {x t : ℝ} (ht : t ∉ flowExcept b J x) : t ≠ 0 := fun h =>
  ht (Finset.mem_insert.2 (Or.inl h))

theorem add_notMem_of_notMem_flowExcept {x t : ℝ} (ht : t ∉ flowExcept b J x) : t + x ∉ J := fun h =>
  ht (Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image.2 ⟨t + x, h, by ring⟩)))

theorem tendsto_add_real_nhdsWithin_H (t x : ℝ) :
    Tendsto (fun z : ℂ => z + x) (𝓝[H] (t : ℂ)) (𝓝[H] ((t + x : ℝ) : ℂ)) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun z hz => add_real_mem_H hz x⟩
  have h := ((continuous_id.add continuous_const : Continuous fun z : ℂ => z + x).tendsto (t : ℂ))
  rw [Complex.ofReal_add]
  exact h.mono_left nhdsWithin_le_nhds

/-- **The bounded harmonic extension of the flow-line data** is `u₀(· + x) + θχ` on `ℍ`, for the bounded harmonic
extension `u₀` of `b`. -/
theorem eqOn_flowLine_harmonicExtension {κ : ℝ} (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b J)
    (x θ : ℝ) {u₀ u : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b J u₀)
    (hu : IsBoundedHarmonicExtension (forceBoundaryData κ (flowLineRhoL κ b J x θ) (flowLineRhoR κ b J x θ)
      (flowLineXL b J x) (flowLineXR b J x)) (forceJumpSet (flowLineXL b J x) (flowLineXR b J x)) u) :
    EqOn u (fun z => u₀ (z + x) + θ * QuantumZipper.chiC κ) H := by
  have hharm : InnerProductSpace.HarmonicOnNhd (fun z => u₀ (z + x) + θ * QuantumZipper.chiC κ) H :=
    fun z hz => (harmonicAt_comp_add_const (hu₀.1 _ (add_real_mem_H hz x))).add
      (InnerProductSpace.harmonicAt_const _)
  have hbdd : ∀ {v : ℂ → ℝ}, (∃ C : ℝ, ∀ z ∈ H, |v z| ≤ C) → Bornology.IsBounded (v '' H) := by
    rintro v ⟨C, hC⟩
    exact isBounded_iff_forall_norm_le.2 ⟨C, by rintro _ ⟨z, hz, rfl⟩; exact (hC z hz)⟩
  obtain ⟨C₀, hC₀⟩ := hu₀.2.1
  refine eqOn_of_tendsto_sub_H (flowExcept b J x) hu.1 hharm (hbdd hu.2.1)
    (hbdd ⟨C₀ + |θ * QuantumZipper.chiC κ|, fun z hz => (abs_add_le _ _).trans (by
      have := hC₀ _ (add_real_mem_H hz x)
      linarith)⟩) ?_
  intro t ht
  have h1 := hu.2.2 t (notMem_forceJumpSet_of_notMem_flowExcept ht)
  have h2 := (hu₀.2.2 (t + x) (add_notMem_of_notMem_flowExcept ht)).comp (tendsto_add_real_nhdsWithin_H t x)
  have h3 := h1.sub (h2.add_const (θ * QuantumZipper.chiC κ))
  rw [forceBoundaryData_flowLine_seed hκ hb x θ (ne_zero_of_notMem_flowExcept ht)
    (add_notMem_of_notMem_flowExcept ht), sub_self] at h3
  exact h3

/-- **The flow-line field `h(· + x) + θχ` of a GFF with piecewise-constant data `b` is a GFF with the force-word
boundary data of the flow-line word** (the second clause of the frozen `IsOptionalHullCoupling` for the field of the
frozen `IsFlowLine`). -/
theorem isGFFWithBoundaryData_flowField {κ : ℝ} (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b J)
    (x θ : ℝ) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b J) :
    IsGFFWithBoundaryData P (fun ω => flowField x (θ * QuantumZipper.chiC κ) (h ω))
      (forceBoundaryData κ (flowLineRhoL κ b J x θ) (flowLineRhoR κ b J x θ) (flowLineXL b J x)
        (flowLineXR b J x)) (forceJumpSet (flowLineXL b J x) (flowLineXR b J x)) := by
  refine ⟨(measurable_flowField x _).comp hh.1, fun u hu => ?_⟩
  obtain ⟨u₀, hu₀, -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension hb
  have hmi : ∀ φ : TestOn upperHalfPlaneOpens, Integrable (fun w => u₀ (w + x) * φ w) := fun φ =>
    Coupling.MartMeans2.integrable_mul_test_of_continuousOn (S := H)
      ((hu₀.1.continuousOn).comp (continuousOn_id.add continuousOn_const) fun z hz => add_real_mem_H hz x) φ
      φ.tsupport_subset
  have hX := isZBGFFProcess_flowField (hh.2 u₀ hu₀) x (θ * QuantumZipper.chiC κ) hmi
  have heq := eqOn_flowLine_harmonicExtension hκ hb x θ hu₀ hu
  convert hX using 4 with φ ω
  congr 1
  funext z
  by_cases hz : z ∈ H
  · rw [heq hz]
  · have h0 : φ z = 0 := φ.zero_on_compl (show z ∈ ((upperHalfPlaneOpens : Set ℂ))ᶜ from hz)
    rw [h0, mul_zero, mul_zero]

/-- **Two GFFs on `ℍ` with the same boundary data have the same law** on `𝒟'(ℍ)`, as soon as the data has a bounded
harmonic extension. -/
theorem map_eq_of_isGFFWithBoundaryData {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} {h : Ω → DistOn upperHalfPlaneOpens}
    {h' : Ω' → DistOn upperHalfPlaneOpens} {g : ℝ → ℝ} {S : Set ℝ}
    (hh : IsGFFWithBoundaryData P h g S) (hh' : IsGFFWithBoundaryData P' h' g S) {u : ℂ → ℝ}
    (hu : IsBoundedHarmonicExtension g S u) : P.map h = P'.map h' := by
  have hX := hh.2 u hu
  have hX' := hh'.2 u hu
  have e := hX.map_eq hX'
  set c : TestOn upperHalfPlaneOpens → ℝ := fun φ => ∫ z, u z * φ z with hc
  have hm : Measurable (LQGMetric.zbPath (fun φ ω => h ω φ - ∫ z, u z * φ z)) :=
    measurable_pi_iff.2 hX.measurable
  have hm' : Measurable (LQGMetric.zbPath (fun φ ω => h' ω φ - ∫ z, u z * φ z)) :=
    measurable_pi_iff.2 hX'.measurable
  have hshift : Measurable (fun f : TestOn upperHalfPlaneOpens → ℝ => f + c) :=
    measurable_pi_iff.2 fun φ => (measurable_pi_apply φ).add_const _
  have e1 : (fun ω => fun φ : TestOn upperHalfPlaneOpens => h ω φ) =
      (fun f => f + c) ∘ LQGMetric.zbPath (fun φ ω => h ω φ - ∫ z, u z * φ z) := by
    funext ω φ
    simp [LQGMetric.zbPath, hc]
  have e2 : (fun ω => fun φ : TestOn upperHalfPlaneOpens => h' ω φ) =
      (fun f => f + c) ∘ LQGMetric.zbPath (fun φ ω => h' ω φ - ∫ z, u z * φ z) := by
    funext ω φ
    simp [LQGMetric.zbPath, hc]
  ext s hs
  obtain ⟨t, ht, rfl⟩ := hs
  rw [Measure.map_apply hh.1 (MeasurableSpace.measurableSet_comap.2 ⟨t, ht, rfl⟩),
    Measure.map_apply hh'.1 (MeasurableSpace.measurableSet_comap.2 ⟨t, ht, rfl⟩)]
  have h1 := congrArg (fun μ : Measure (TestOn upperHalfPlaneOpens → ℝ) => μ ((fun f => f + c) ⁻¹' t)) e
  rw [Measure.map_apply hm (hshift ht), Measure.map_apply hm' (hshift ht)] at h1
  rw [← Set.preimage_comp, ← Set.preimage_comp]
  change P ((fun ω => fun φ : TestOn upperHalfPlaneOpens => h ω φ) ⁻¹' t) =
    P' ((fun ω => fun φ : TestOn upperHalfPlaneOpens => h' ω φ) ⁻¹' t)
  rw [e1, e2, Set.preimage_comp, Set.preimage_comp]
  exact h1

end Exist

end InteractingSLE
