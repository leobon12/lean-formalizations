import QuantumZipper.Proofs.LQG.GoodTransforms
import QuantumZipper.Proofs.LQG.RegularClosure
import QuantumZipper.Proofs.RS.TraceShift
import QuantumZipper.Statements.Thm18Off

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R18-AREANULL, part 3: the canonical rescaling does not change the area of the curve

Deterministic step. For a good field `x` with `a = scaleParam γ x > 0`, and a driver `W` whose
trace exists at all times `t ≥ 0` and is continuous on `[0,∞)`, the canonicalized configuration
`(canonical γ x, W(a² ·)/a)` (Sheffield (1.8), p. 21) satisfies
`μ_{canonical x}(η') = μ_x(η)` with `η = curveOf W`, `η' = curveOf (W(a² ·)/a)`
(`qAreaMeasure_canonical_curveOf_scale`): the area pushes forward by `z ↦ z/a`
(`GoodTransforms.hasAreaLimit_rescale`) and `η' = η/a` (Brownian/Loewner scaling
`RS.trace_scale`, node P3(d) of EXT-RS; Sheffield p. 21, rescaling (1.8)).

This is the step behind Sheffield's use (arXiv:1012.4797, §4.1 p. 48; Thm 1.8 p. 26 with the
canonical description) of "η is a measure zero set independent of h": the canonical description is
the unscaled field rescaled by `scaleParam`, and the SLE curve rescales with it. Own elementary
bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace R18

/-- **Area of a rescaled good field**: `μ_{rescale x Q b} = (z ↦ z/b)_* μ_x`. -/
theorem qAreaMeasure_rescale_map {γ : ℝ} (hγ : 0 < γ) {x : FieldSample} (hx : IsLQGGood γ x)
    {b : ℝ} (hb : 0 < b) :
    qAreaMeasure γ (rescale x (Qc γ) b) = (qAreaMeasure γ x).map fun z : ℂ => z / (b : ℂ) := by
  obtain ⟨hreg, -, μ, hμ⟩ := hx
  rw [GoodSample.qAreaMeasure_eq_of_hasAreaLimit (hreg.rescale' (Qc γ) hb)
    (GoodTransforms.hasAreaLimit_rescale hreg hγ hμ hb),
    GoodSample.qAreaMeasure_eq_of_hasAreaLimit hreg hμ]

/-- Nonnegative rational multiples of `c > 0` are dense in `[0,∞)`. -/
theorem Ici_subset_closure_range_mul {c : ℝ} (hc : 0 < c) :
    Ici (0 : ℝ) ⊆ closure (range fun q : ℚ≥0 => c * (q : ℝ)) := by
  intro x hx
  refine Metric.mem_closure_iff.2 fun ε hε => ?_
  obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (show x / c < x / c + ε / c by
    have : 0 < ε / c := div_pos hε hc
    linarith)
  have hr0 : (0 : ℝ) ≤ r := le_trans (div_nonneg hx hc.le) hr1.le
  have hr0' : (0 : ℚ) ≤ r := by exact_mod_cast hr0
  refine ⟨c * ((r.toNNRat : ℚ≥0) : ℝ), ⟨r.toNNRat, rfl⟩, ?_⟩
  have hcast : ((r.toNNRat : ℚ≥0) : ℝ) = (r : ℝ) := by
    rw [show (r : ℝ) = ((r.toNNRat : ℚ) : ℝ) by rw [Rat.coe_toNNRat r hr0']]
    norm_cast
  rw [hcast, Real.dist_eq, abs_lt]
  have h1 : x < c * r := by rw [div_lt_iff₀ hc] at hr1; linarith
  have h2 : c * r < x + ε := by
    have := (lt_div_iff₀ hc).1 (show (r : ℝ) < (x + ε) / c by rw [add_div]; exact hr2)
    linarith
  constructor <;> linarith

/-- A function continuous on `[0,∞)` has the same closure of values on a dense subset. -/
theorem closure_image_eq_of_dense {f : ℝ → ℂ} (hf : ContinuousOn f (Ici 0)) {s : Set ℝ}
    (hs : s ⊆ Ici 0) (hd : Ici (0 : ℝ) ⊆ closure s) :
    closure (f '' s) = closure (f '' Ici 0) := by
  refine Subset.antisymm (closure_mono (image_mono hs))
    (closure_minimal ?_ isClosed_closure)
  rintro _ ⟨x, hx, rfl⟩
  exact ((hf x hx).mono hs).mem_closure_image (hd hx)

/-- **Scaling of the curve**: `curveOf (W(a² ·)/a) = curveOf W / a`, for a driver whose trace
exists at every time `t ≥ 0` (radial limit) and is continuous on `[0,∞)`. -/
theorem curveOf_scale {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {a : ℝ} (ha : 0 < a)
    (hlim : ∀ t : ℝ, 0 ≤ t → ∃ p : ℂ,
      Tendsto (fun y : ℝ => fwdMapInv W t (y * Complex.I)) (𝓝[>] 0) (𝓝 p))
    (hc : ContinuousOn (trace W) (Ici 0)) :
    curveOf (fun r => W (a ^ 2 * r) / a) = (fun z : ℂ => z / (a : ℂ)) '' curveOf W := by
  have htr : ∀ q : ℚ≥0, trace (fun r => W (a ^ 2 * r) / a) (q : ℝ) =
      trace W (a ^ 2 * (q : ℝ)) / (a : ℂ) := by
    intro q
    obtain ⟨p, hp⟩ := hlim (a ^ 2 * (q : ℝ)) (by positivity)
    exact (RS.trace_scale hW hW0 ha (by positivity) hp).2
  have ha0 : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ha.ne'
  set h : ℂ ≃ₜ ℂ := Homeomorph.mulRight₀ ((a : ℂ)⁻¹) (inv_ne_zero ha0) with hh
  have hhf : (fun z : ℂ => z / (a : ℂ)) = h := by
    funext z; simp [hh, div_eq_mul_inv]
  have e1 : (range fun q : ℚ≥0 => trace W (a ^ 2 * (q : ℝ)) / (a : ℂ)) =
      h '' (trace W '' range fun q : ℚ≥0 => a ^ 2 * (q : ℝ)) := by
    rw [← hhf, image_image, ← range_comp]; rfl
  have e2 : (range fun q : ℚ≥0 => trace W (q : ℝ)) =
      trace W '' range fun q : ℚ≥0 => 1 * (q : ℝ) := by
    rw [← range_comp]; simp [Function.comp_def]
  have hsub : ∀ c : ℝ, 0 < c → (range fun q : ℚ≥0 => c * (q : ℝ)) ⊆ Ici 0 := by
    rintro c hc _ ⟨q, rfl⟩
    exact mul_nonneg hc.le (by positivity)
  unfold curveOf
  simp_rw [htr]
  rw [e1, e2, ← h.image_closure, hhf,
    closure_image_eq_of_dense hc (hsub _ (by positivity)) (Ici_subset_closure_range_mul
      (by positivity)),
    closure_image_eq_of_dense hc (hsub 1 one_pos) (Ici_subset_closure_range_mul one_pos)]

/-- **The canonical rescaling preserves the area of the curve.** -/
theorem qAreaMeasure_canonical_curveOf_scale {γ : ℝ} (hγ : 0 < γ) {x : FieldSample}
    (hx : IsLQGGood γ x) (ha : 0 < scaleParam γ x) {W : ℝ → ℝ} (hW : Continuous W)
    (hW0 : W 0 = 0)
    (hlim : ∀ t : ℝ, 0 ≤ t → ∃ p : ℂ,
      Tendsto (fun y : ℝ => fwdMapInv W t (y * Complex.I)) (𝓝[>] 0) (𝓝 p))
    (hc : ContinuousOn (trace W) (Ici 0)) :
    qAreaMeasure γ (canonical γ x)
        (curveOf fun r => W (scaleParam γ x ^ 2 * r) / scaleParam γ x) =
      qAreaMeasure γ x (curveOf W) := by
  set a := scaleParam γ x with hadef
  have ha0 : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ha.ne'
  have hmeas : Measurable fun z : ℂ => z / (a : ℂ) := measurable_id.div_const _
  have hcl : MeasurableSet (curveOf fun r => W (a ^ 2 * r) / a) :=
    isClosed_closure.measurableSet
  rw [show canonical γ x = rescale x (Qc γ) a from rfl, qAreaMeasure_rescale_map hγ hx ha,
    Measure.map_apply hmeas hcl, curveOf_scale hW hW0 ha hlim hc]
  congr 1
  ext z
  simp only [mem_preimage, mem_image]
  constructor
  · rintro ⟨w, hw, hwz⟩
    have : w = z := by
      field_simp at hwz
      exact hwz
    exact this ▸ hw
  · intro hz
    exact ⟨z, hz, rfl⟩

end R18
end QuantumZipper
