import QuantumZipper.Proofs.Zipper.LocRichComapMain

/-!
# LOCRICH-COMAP (4): measurable path extraction from the driver window

The driver window `w : ℝ≥0 → ℝ` of `locRich R'` carries the product σ-algebra, for which
"continuous on `[0,T]`" is not a measurable condition. The continuous path is therefore read off
the dyadic values: `w` is *dyadically uniformly continuous* (`UCd`, a countable, measurable
condition), and then the path is the continuous extension (mathlib `Dense.extend`,
`uniformContinuous_uniformly_extend`) of `w` from the dyadic points of `[0,T]`, divided by `√κ`
(junk `0` otherwise). Its values are limits along dyadic approximations, hence measurable
(`ContinuousMap.measurable_iff_eval`); for a window of a continuous driver it reproduces the
driver (`Dense.extend_unique`). Main result: `exists_pathExtract`.

Own elementary construction (standard: continuous modification from the values on a countable
dense set).
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped NNReal ENNReal Topology

namespace QuantumZipper.E6

open CharFun

namespace PathX

variable (T : ℕ)

theorem hT : (0 : ℝ) ≤ T := Nat.cast_nonneg T

/-- The dyadic points of `[0,T]`. -/
def dy : Set (Icc (0 : ℝ) T) :=
  range fun p : ℕ × ℕ => projIcc (0 : ℝ) T (hT T) ((p.1 : ℝ) / 2 ^ p.2)

instance countable_dy : Countable (dy T) := (countable_range _).to_subtype

/-- The dyadic approximation from below at level `n`. -/
def seqPt (n : ℕ) (r : Icc (0 : ℝ) T) : Icc (0 : ℝ) T :=
  projIcc (0 : ℝ) T (hT T) ((⌊r.1 * 2 ^ n⌋₊ : ℝ) / 2 ^ n)

theorem seqPt_mem (n : ℕ) (r : Icc (0 : ℝ) T) : seqPt T n r ∈ dy T := ⟨(⌊r.1 * 2 ^ n⌋₊, n), rfl⟩

theorem tendsto_seqPt (r : Icc (0 : ℝ) T) : Tendsto (fun n => seqPt T n r) atTop (𝓝 r) := by
  have hr0 : 0 ≤ r.1 := r.2.1
  have hlim : Tendsto (fun n : ℕ => (⌊r.1 * 2 ^ n⌋₊ : ℝ) / 2 ^ n) atTop (𝓝 r.1) := by
    have hup : ∀ n : ℕ, (⌊r.1 * 2 ^ n⌋₊ : ℝ) / 2 ^ n ≤ r.1 := fun n =>
      (div_le_iff₀ (by positivity)).2 (Nat.floor_le (by positivity))
    have hlow : ∀ n : ℕ, r.1 - (1 / 2 : ℝ) ^ n ≤ (⌊r.1 * 2 ^ n⌋₊ : ℝ) / 2 ^ n := by
      intro n
      have h1 := Nat.lt_floor_add_one (r.1 * 2 ^ n)
      rw [le_div_iff₀ (by positivity), sub_mul, one_div_pow, one_div,
        inv_mul_cancel₀ (by positivity)]
      linarith
    have ht : Tendsto (fun n : ℕ => r.1 - (1 / 2 : ℝ) ^ n) atTop (𝓝 r.1) := by
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num)).const_sub r.1
      simpa using this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le ht tendsto_const_nhds hlow hup
  have := (continuous_projIcc (a := (0 : ℝ)) (b := T) (h := hT T)).tendsto r.1 |>.comp hlim
  simpa [seqPt, Function.comp_def, projIcc_val] using this

theorem dense_dy : Dense (dy T) := fun r =>
  mem_closure_of_tendsto (tendsto_seqPt T r) (Eventually.of_forall fun n => seqPt_mem T n r)

/-- The window read at the dyadic points. -/
def phi (w : ℝ≥0 → ℝ) : dy T → ℝ := fun r => w r.1.1.toNNReal

/-- Dyadic uniform continuity (countable form). -/
def UCd (w : ℝ≥0 → ℝ) : Prop :=
  ∀ m : ℕ, ∃ N : ℕ, ∀ p q : dy T, dist p q < 1 / ((N : ℝ) + 1) →
    dist (phi T w p) (phi T w q) < 1 / ((m : ℝ) + 1)

theorem measurableSet_UCd : MeasurableSet {w : ℝ≥0 → ℝ | UCd T w} := by
  have e : {w : ℝ≥0 → ℝ | UCd T w} = ⋂ m : ℕ, ⋃ N : ℕ, ⋂ p : dy T, ⋂ q : dy T,
      {w | dist p q < 1 / ((N : ℝ) + 1) → dist (phi T w p) (phi T w q) < 1 / ((m : ℝ) + 1)} := by
    ext w; simp only [UCd, mem_setOf_eq, mem_iInter, mem_iUnion]
  rw [e]
  refine MeasurableSet.iInter fun m => MeasurableSet.iUnion fun N =>
    MeasurableSet.iInter fun p => MeasurableSet.iInter fun q => ?_
  by_cases hpq : dist p q < 1 / ((N : ℝ) + 1)
  · simp only [hpq, true_implies]
    exact measurableSet_lt ((measurable_pi_apply _).dist (measurable_pi_apply _))
      measurable_const
  · simp only [hpq, false_implies, setOf_true, MeasurableSet.univ]

theorem uniformContinuous_phi {w : ℝ≥0 → ℝ} (h : UCd T w) : UniformContinuous (phi T w) := by
  refine Metric.uniformContinuous_iff.2 fun ε hε => ?_
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
  obtain ⟨N, hN⟩ := h m
  refine ⟨1 / ((N : ℝ) + 1), by positivity, ?_⟩
  intro a b hpq
  exact (hN a b hpq).trans hm

/-- The continuous extension of the dyadic values. -/
def ext (w : ℝ≥0 → ℝ) : Icc (0 : ℝ) T → ℝ := (dense_dy T).extend (phi T w)

theorem uniformContinuous_ext {w : ℝ≥0 → ℝ} (h : UCd T w) : UniformContinuous (ext T w) :=
  uniformContinuous_uniformly_extend (isUniformInducing_val _) (dense_dy T).denseRange_val
    (uniformContinuous_phi T h)

theorem ext_eq_limUnder {w : ℝ≥0 → ℝ} (h : UCd T w) (r : Icc (0 : ℝ) T) :
    ext T w r = limUnder atTop fun n => w (seqPt T n r).1.toNNReal := by
  have hc := (uniformContinuous_ext T h).continuous
  have ht := (hc.tendsto r).comp (tendsto_seqPt T r)
  have hv : ∀ n, ext T w (seqPt T n r) = w (seqPt T n r).1.toNNReal := fun n =>
    uniformly_extend_of_ind (isUniformInducing_val _) (dense_dy T).denseRange_val
      (uniformContinuous_phi T h) ⟨seqPt T n r, seqPt_mem T n r⟩
  simp only [Function.comp_def, hv] at ht
  exact ht.limUnder_eq.symm

end PathX

open PathX

open Classical in
/-- The path extraction (junk `0` off `UCd`). -/
def pathX (κ : ℝ) (T : ℕ) (w : ℝ≥0 → ℝ) : C(Icc (0 : ℝ) T, ℝ) :=
  if h : UCd T w then
    ⟨fun r => (Real.sqrt κ)⁻¹ * ext T w r,
      continuous_const.mul (uniformContinuous_ext T h).continuous⟩
  else 0

open Classical in
theorem measurable_pathX (κ : ℝ) (T : ℕ) : Measurable (pathX κ T) := by
  refine ContinuousMap.measurable_iff_eval.2 fun r => ?_
  have e : (fun w => pathX κ T w r) = fun w => if UCd T w then
      (Real.sqrt κ)⁻¹ * limUnder atTop (fun n => w (seqPt T n r).1.toNNReal) else 0 := by
    funext w
    by_cases h : UCd T w
    · simp only [pathX, dif_pos h, if_pos h, ContinuousMap.coe_mk, ext_eq_limUnder T h r]
    · simp only [pathX, dif_neg h, if_neg h, ContinuousMap.zero_apply]
  rw [e]
  refine Measurable.ite (measurableSet_UCd T) (Measurable.const_mul ?_ _) measurable_const
  exact (StronglyMeasurable.limUnder fun n =>
    (measurable_pi_apply (X := fun _ : ℝ≥0 => ℝ)
      (seqPt T n r).1.toNNReal).stronglyMeasurable).measurable

/-- **A measurable path extraction exists** (for `κ > 0`). -/
theorem exists_pathExtract {κ : ℝ} (hκ : 0 < κ) : PathExtract κ (pathX κ) := by
  refine ⟨measurable_pathX κ, fun T w W hW hwW r hr => ?_⟩
  have hwW' : ∀ p : dy T, phi T w p = W p.1.1 := by
    intro p
    have hp0 : (0 : ℝ) ≤ p.1.1 := p.1.2.1
    simp only [phi]
    rw [hwW _ (by rw [Real.coe_toNNReal _ hp0]; exact p.1.2.2), Real.coe_toNNReal _ hp0]
  have hg : Continuous fun q : Icc (0 : ℝ) T => W q.1 := hW.comp continuous_subtype_val
  have hUC : UCd T w := by
    intro m
    have hu := CompactSpace.uniformContinuous_of_continuous hg
    obtain ⟨δ, hδ, hδu⟩ := Metric.uniformContinuous_iff.1 hu (1 / ((m : ℝ) + 1)) (by positivity)
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
    refine ⟨N, fun p q hpq => ?_⟩
    rw [hwW' p, hwW' q]
    exact hδu (lt_trans hpq hN)
  have hext : ext T w = fun q : Icc (0 : ℝ) T => W q.1 :=
    (dense_dy T).extend_unique (fun p => (hwW' p).symm) hg
  have hs : Real.sqrt κ ≠ 0 := (Real.sqrt_pos.2 hκ).ne'
  simp only [Wof, pathX, dif_pos hUC, ContinuousMap.coe_mk, hext, projIcc_of_mem _ hr]
  field_simp

end QuantumZipper.E6
