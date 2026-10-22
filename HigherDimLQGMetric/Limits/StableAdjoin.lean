import HigherDimLQGMetric.Limits.StableLaw
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

/-!
# Adjoining a measurable field observable to stable convergence

Stable convergence permits bounded measurable functions of the fixed field.
We first prove the continuous-test identity for a finite-valued observable;
general measurable observables are approximated by simple functions.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

private theorem l6c_finite_stable_adjoin {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistRd d)
    (hh : Measurable h)
    (X : ℕ → Ω → C(Rd d × Rd d, ℝ)) (Y : Ω → C(Rd d × Rd d, ℝ))
    (hX : ∀ n, AEMeasurable (X n) P) (hY : AEMeasurable Y P)
    (hstable : StablyTendstoLU P h X Y)
    (s : SimpleFunc (DistRd d) ℝ)
    (F : ℝ × C(Rd d × Rd d, ℝ) → ℝ) (hF : Continuous F)
    (hFb : ∃ C, ∀ x, |F x| ≤ C) :
    Tendsto (fun n => ∫ ω, F (s (h ω), X n ω) ∂P) atTop
      (𝓝 (∫ ω, F (s (h ω), Y ω) ∂P)) := by
  classical
  let R := s.range
  let g : ℝ → DistRd d → ℝ := fun b x => if s x = b then 1 else 0
  let φ : ℝ → C(Rd d × Rd d, ℝ) → ℝ := fun b D => F (b, D)
  have hgm (b : ℝ) : Measurable (g b) := by
    exact (measurable_const.ite (s.measurable (measurableSet_singleton b)) measurable_const)
  have hgb (b : ℝ) : ∃ C, ∀ x, |g b x| ≤ C :=
    ⟨1, fun x => by dsimp [g]; split <;> simp⟩
  have hφc (b : ℝ) : Continuous (φ b) :=
    hF.comp (continuous_const.prodMk continuous_id)
  have hφb (b : ℝ) : ∃ C, ∀ D, |φ b D| ≤ C :=
    ⟨hFb.choose, fun D => hFb.choose_spec _⟩
  have ht (b : ℝ) :
      Tendsto (fun n => ∫ ω, g b (h ω) * φ b (X n ω) ∂P) atTop
        (𝓝 (∫ ω, g b (h ω) * φ b (Y ω) ∂P)) :=
    hstable (g b) (hgm b) (hgb b) (φ b) (hφc b) (hφb b)
  have hpoint (ω : Ω) (D : C(Rd d × Rd d, ℝ)) :
      F (s (h ω), D) = ∑ b ∈ R, g b (h ω) * φ b D := by
    have hmem : s (h ω) ∈ R := s.mem_range_self _
    simp only [g, φ, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq]
    simp only [hmem, ↓reduceIte]
  have hint (Z : Ω → C(Rd d × Rd d, ℝ)) (hZ : AEMeasurable Z P) (b : ℝ) :
      Integrable (fun ω => g b (h ω) * φ b (Z ω)) P := by
    have hm : AEStronglyMeasurable (fun ω => g b (h ω) * φ b (Z ω)) P :=
      ((hgm b).comp hh).aestronglyMeasurable.mul
        ((hφc b).measurable.comp_aemeasurable hZ).aestronglyMeasurable
    refine Integrable.of_bound hm (hFb.choose) (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs]
    by_cases hg : s (h ω) = b
    · simpa only [g, hg, ↓reduceIte, one_mul] using hFb.choose_spec (b, Z ω)
    · simp only [g, hg, ↓reduceIte, zero_mul, abs_zero]
      exact le_trans (abs_nonneg _) (hFb.choose_spec (b, Z ω))
  have hsum (Z : Ω → C(Rd d × Rd d, ℝ)) (hZ : AEMeasurable Z P) :
      ∫ ω, F (s (h ω), Z ω) ∂P =
        ∑ b ∈ R, ∫ ω, g b (h ω) * φ b (Z ω) ∂P := by
    simp_rw [hpoint]
    exact integral_finsetSum R (fun b _ => hint Z hZ b)
  simp_rw [hsum (X _) (hX _), hsum Y hY]
  exact tendsto_finsetSum R (fun b _ => ht b)

/-- Stable convergence permits adjoining a measurable scalar observable of the
fixed field when testing against bounded functions Lipschitz in that scalar.
The simple-function approximation has an error uniform in the metric index. -/
theorem l6c_stable_adjoin_scalar_test {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistRd d)
    (hh : Measurable h)
    (X : ℕ → Ω → C(Rd d × Rd d, ℝ)) (Y : Ω → C(Rd d × Rd d, ℝ))
    (hX : ∀ n, AEMeasurable (X n) P) (hY : AEMeasurable Y P)
    (hstable : StablyTendstoLU P h X Y)
    (a : DistRd d → ℝ) (ha : Measurable a)
    (F : ℝ × C(Rd d × Rd d, ℝ) → ℝ) (hFc : Continuous F)
    (B L : ℝ) (hB : 0 ≤ B) (hL : 0 ≤ L)
    (hFb : ∀ q, |F q| ≤ B)
    (hLip : ∀ a a' D, |F (a,D) - F (a',D)| ≤ L * |a - a'|) :
    Tendsto (fun n => ∫ ω, F (a (h ω), X n ω) ∂P) atTop
      (𝓝 (∫ ω, F (a (h ω), Y ω) ∂P)) := by
  let sm := ha.stronglyMeasurable
  let s : ℕ → SimpleFunc (DistRd d) ℝ := sm.approx
  have hs (x : DistRd d) : Tendsto (fun m => s m x) atTop (𝓝 (a x)) :=
    sm.tendsto_approx x
  have hfinite (m : ℕ) :
      Tendsto (fun n => ∫ ω, F (s m (h ω), X n ω) ∂P) atTop
        (𝓝 (∫ ω, F (s m (h ω), Y ω) ∂P)) :=
    l6c_finite_stable_adjoin P h hh X Y hX hY hstable (s m) F hFc
      ⟨B, hFb⟩
  let e : ℕ → ℝ := fun m => ∫ ω,
    min (2 * B) (L * |s m (h ω) - a (h ω)|) ∂P
  have he : Tendsto e atTop (𝓝 0) := by
    have hzero : (0 : ℝ) = ∫ ω, (0 : ℝ) ∂P := by simp
    rw [hzero]
    refine tendsto_integral_of_dominated_convergence (fun _ => 2 * B)
      (fun m => ?_) (integrable_const _) (fun m => Filter.Eventually.of_forall fun ω => ?_) ?_
    · exact ((continuous_const.min (continuous_const.mul continuous_abs)).measurable.comp_aemeasurable
        (((s m).measurable.comp hh).aemeasurable.sub (ha.comp hh).aemeasurable)).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (le_min (by linarith) (by positivity))]
      exact min_le_left _ _
    · filter_upwards [] with ω
      have ht : Tendsto (fun m => L * |s m (h ω) - a (h ω)|) atTop (𝓝 0) := by
        have := ((hs (h ω)).sub_const (a (h ω))).abs.const_mul L
        simpa using this
      have ht' := (tendsto_const_nhds (x := 2 * B)).min ht
      simpa only [min_eq_right (by linarith : (0 : ℝ) ≤ 2 * B)] using ht'
  have hint (Z : Ω → C(Rd d × Rd d, ℝ)) (hZ : AEMeasurable Z P) :
      Integrable (fun ω => F (a (h ω), Z ω)) P := by
    have hm : AEStronglyMeasurable (fun ω => F (a (h ω), Z ω)) P :=
      (hFc.measurable.comp_aemeasurable ((ha.comp hh).aemeasurable.prodMk hZ)).aestronglyMeasurable
    exact Integrable.of_bound hm B (Filter.Eventually.of_forall fun ω => by
      simpa only [Real.norm_eq_abs] using hFb (a (h ω), Z ω))
  have hintS (m : ℕ) (Z : Ω → C(Rd d × Rd d, ℝ)) (hZ : AEMeasurable Z P) :
      Integrable (fun ω => F (s m (h ω), Z ω)) P := by
    have hm : AEStronglyMeasurable (fun ω => F (s m (h ω), Z ω)) P :=
      (hFc.measurable.comp_aemeasurable ((((s m).measurable.comp hh).aemeasurable).prodMk hZ)).aestronglyMeasurable
    exact Integrable.of_bound hm B (Filter.Eventually.of_forall fun ω => by
      simpa only [Real.norm_eq_abs] using hFb (s m (h ω), Z ω))
  have hei (m : ℕ) : Integrable (fun ω =>
      min (2 * B) (L * |s m (h ω) - a (h ω)|)) P := by
    have hm : AEStronglyMeasurable (fun ω =>
        min (2 * B) (L * |s m (h ω) - a (h ω)|)) P :=
      ((continuous_const.min (continuous_const.mul continuous_abs)).measurable.comp_aemeasurable
        (((s m).measurable.comp hh).aemeasurable.sub (ha.comp hh).aemeasurable)).aestronglyMeasurable
    exact Integrable.of_bound hm (2 * B) (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min (by linarith) (by positivity))]
      exact min_le_left _ _)
  have herr (m : ℕ) (Z : Ω → C(Rd d × Rd d, ℝ)) (hZ : AEMeasurable Z P) :
      |(∫ ω, F (a (h ω), Z ω) ∂P) -
        (∫ ω, F (s m (h ω), Z ω) ∂P)| ≤ e m := by
    rw [← integral_sub (hint Z hZ) (hintS m Z hZ)]
    refine (abs_integral_le_integral_abs).trans ?_
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => abs_nonneg _)
      (hei m) (Filter.Eventually.of_forall fun ω => ?_)
    exact le_min (by
      have h1 := hFb (a (h ω), Z ω)
      have h2 := hFb (s m (h ω), Z ω)
      have htri : |F (a (h ω), Z ω) - F (s m (h ω), Z ω)| ≤
          |F (a (h ω), Z ω)| + |F (s m (h ω), Z ω)| := by
        simpa only [sub_zero, zero_sub, abs_neg] using
          (abs_sub_le (F (a (h ω), Z ω)) 0 (F (s m (h ω), Z ω)))
      linarith)
      (by simpa only [abs_sub_comm (a (h ω)) (s m (h ω))] using
        hLip (a (h ω)) (s m (h ω)) (Z ω))
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨m, hm⟩ := ((he.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < ε / 4))).exists)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 (hfinite m) (ε / 4) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have h1 := herr m (X n) (hX n)
  have h2 := herr m Y hY
  rw [abs_sub_comm] at h2
  have h3 := hN n hn
  rw [Real.dist_eq] at h3 ⊢
  have ht := abs_sub_le (∫ ω, F (a (h ω), X n ω) ∂P)
    (∫ ω, F (s m (h ω), X n ω) ∂P)
    (∫ ω, F (a (h ω), Y ω) ∂P)
  have ht' := abs_sub_le (∫ ω, F (s m (h ω), X n ω) ∂P)
    (∫ ω, F (s m (h ω), Y ω) ∂P)
    (∫ ω, F (a (h ω), Y ω) ∂P)
  have : e m < ε / 4 := hm
  linarith

/-- Stable convergence jointly with any measurable real-valued observable of
the fixed field.  The observable need not be continuous on distributions. -/
theorem l6c_stable_adjoin_scalar {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistRd d)
    (hh : Measurable h)
    (X : ℕ → Ω → C(Rd d × Rd d, ℝ)) (Y : Ω → C(Rd d × Rd d, ℝ))
    (hX : ∀ n, AEMeasurable (X n) P) (hY : AEMeasurable Y P)
    (hstable : StablyTendstoLU P h X Y)
    (a : DistRd d → ℝ) (ha : Measurable a) :
    TendstoInDistribution (fun n ω => (a (h ω), X n ω)) atTop
      (fun ω => (a (h ω), Y ω)) (fun _ => P) P := by
  let _ : PseudoMetricSpace C(Rd d × Rd d, ℝ) :=
    TopologicalSpace.pseudoMetrizableSpacePseudoMetric _
  refine ⟨fun n => ((ha.comp hh).aemeasurable).prodMk (hX n),
    ((ha.comp hh).aemeasurable).prodMk hY, ?_⟩
  refine (tendsto_iff_forall_lipschitz_integral_tendsto
    (Ω := ℝ × C(Rd d × Rd d, ℝ))).2 ?_
  intro F hFb hFl
  obtain ⟨C, hC⟩ := hFb
  obtain ⟨L, hL⟩ := hFl
  obtain ⟨D0⟩ : Nonempty C(Rd d × Rd d, ℝ) := inferInstance
  let q0 : ℝ × C(Rd d × Rd d, ℝ) := (0, D0)
  have hFbd (q : ℝ × C(Rd d × Rd d, ℝ)) : |F q| ≤ |F q0| + max C 0 := by
    have hh := hC q q0
    rw [Real.dist_eq] at hh
    have ht := abs_sub_abs_le_abs_sub (F q) (F q0)
    linarith [le_max_left C 0]
  have hFLip (x y : ℝ) (D : C(Rd d × Rd d, ℝ)) :
      |F (x, D) - F (y, D)| ≤ (L : ℝ) * |x - y| := by
    have ht := hL.dist_le_mul (x, D) (y, D)
    simpa only [Real.dist_eq, Prod.dist_eq, dist_self,
      max_eq_left (abs_nonneg (x - y))] using ht
  have htest := l6c_stable_adjoin_scalar_test P h hh X Y hX hY hstable a ha F
    hL.continuous (|F q0| + max C 0) L (by positivity) (by positivity) hFbd hFLip
  have hmap (Z : Ω → ℝ × C(Rd d × Rd d, ℝ)) (hZ : AEMeasurable Z P) :
      ∫ q, F q ∂(P.map Z) = ∫ ω, F (Z ω) ∂P :=
    integral_map hZ hL.continuous.measurable.aestronglyMeasurable
  change Tendsto (fun n => ∫ q, F q ∂(P.map (fun ω => (a (h ω), X n ω)))) atTop
    (𝓝 (∫ q, F q ∂(P.map (fun ω => (a (h ω), Y ω)))))
  have hmapX (n : ℕ) :
      (∫ q, F q ∂(P.map (fun ω => (a (h ω), X n ω)))) =
        ∫ ω, F (a (h ω), X n ω) ∂P :=
    hmap _ (((ha.comp hh).aemeasurable).prodMk (hX n))
  have hmapY :
      (∫ q, F q ∂(P.map (fun ω => (a (h ω), Y ω)))) =
        ∫ ω, F (a (h ω), Y ω) ∂P :=
    hmap _ (((ha.comp hh).aemeasurable).prodMk hY)
  simpa only [hmapX, hmapY] using htest

end HigherDimLQGMetric
