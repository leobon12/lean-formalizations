import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Blueprint A7: Jensen rigidity (replaces Birkhoff's ergodic theorem)

Let `F : Ω → ℝ → ℝ` be a random function which is a.s. continuous and nondecreasing on
`[0, ∞)` with `F 0 = 0`. Suppose that for every rational `λ > 0`
(a) each increment `F (kλ) - F ((k-1)λ)`, `k ≥ 1`, has the law of `F λ`, and
(b) `F (nλ) / n` has the law of `F λ` for every `n ≥ 1`.
Then a.s. `F s = s * F 1` for all `s ≥ 0`.

Proof: pointwise `exp (-F(nλ)/n) ≤ n⁻¹ ∑ₖ exp (-Yₖ)` (Jensen), both sides have the same
expectation, hence equality holds a.s., and strict convexity forces all `Yₖ` to be equal.
Continuity finishes. No integrability of `F 1` is needed.
-/

namespace QuantumZipper.JensenRigidity

open MeasureTheory Real Finset Filter Topology

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Telescoping of the increments. -/
lemma jr_telescope (f : ℝ → ℝ) (h0 : f 0 = 0) (t : ℝ) (n : ℕ) :
    ∑ k ∈ range n, (f (((k : ℝ) + 1) * t) - f ((k : ℝ) * t)) = f ((n : ℝ) * t) := by
  have := Finset.sum_range_sub (fun i : ℕ => f ((i : ℝ) * t)) n
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_mul, h0, sub_zero] at this
  exact this

/-- One step: for a fixed `t > 0` and `n ≥ 1`, all increments are a.s. equal. -/
lemma jr_increments_ae_eq {t : ℝ} (ht : 0 < t) {n : ℕ} (hn : 1 ≤ n) (F : Ω → ℝ → ℝ)
    (hmeas : ∀ s, Measurable fun ω => F ω s)
    (hgood : ∀ᵐ ω ∂P, ContinuousOn (F ω) (Set.Ici 0) ∧ MonotoneOn (F ω) (Set.Ici 0) ∧ F ω 0 = 0)
    (hinc : ∀ k : ℕ, P.map (fun ω => F ω (((k : ℝ) + 1) * t) - F ω ((k : ℝ) * t))
      = P.map (fun ω => F ω t))
    (hscale : P.map (fun ω => F ω ((n : ℝ) * t) / n) = P.map (fun ω => F ω t)) :
    ∀ᵐ ω ∂P, ∀ k < n, F ω (((k : ℝ) + 1) * t) - F ω ((k : ℝ) * t) = F ω t := by
  set Y : ℕ → Ω → ℝ := fun k ω => F ω (((k : ℝ) + 1) * t) - F ω ((k : ℝ) * t) with hY
  have hYm : ∀ k, Measurable (Y k) := fun k => (hmeas _).sub (hmeas _)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hYnn : ∀ᵐ ω ∂P, ∀ k, 0 ≤ Y k ω := by
    filter_upwards [hgood] with ω hω k
    have := hω.2.1 (show (0 : ℝ) ≤ (k : ℝ) * t by positivity)
      (show (0 : ℝ) ≤ ((k : ℝ) + 1) * t by positivity) (by nlinarith)
    simp only [hY]; linarith
  have hint : ∀ X : Ω → ℝ, Measurable X → (∀ᵐ ω ∂P, 0 ≤ X ω) →
      Integrable (fun ω => exp (-X ω)) P := by
    intro X hX hnn
    refine Integrable.mono' (integrable_const (1 : ℝ))
      (measurable_exp.comp hX.neg).aestronglyMeasurable ?_
    filter_upwards [hnn] with ω h
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
    exact exp_le_one_iff.mpr (by linarith)
  have hlaw : ∀ X : Ω → ℝ, Measurable X → P.map X = P.map (fun ω => F ω t) →
      ∫ ω, exp (-X ω) ∂P = ∫ ω, exp (-F ω t) ∂P := by
    intro X hX h
    have h1 := integral_map (μ := P) hX.aemeasurable (f := fun y : ℝ => exp (-y))
      (Continuous.aestronglyMeasurable (by fun_prop))
    have h2 := integral_map (μ := P) (hmeas t).aemeasurable (f := fun y : ℝ => exp (-y))
      (Continuous.aestronglyMeasurable (by fun_prop))
    rw [h] at h1
    exact h1.symm.trans h2
  have hL : ∫ ω, exp (-(F ω ((n : ℝ) * t) / n)) ∂P = ∫ ω, exp (-F ω t) ∂P :=
    hlaw _ ((hmeas _).div_const _) hscale
  have hYl : ∀ k, ∫ ω, exp (-Y k ω) ∂P = ∫ ω, exp (-F ω t) ∂P :=
    fun k => hlaw _ (hYm k) (hinc k)
  have hw1 : ∑ _k ∈ range n, (1 / (n : ℝ)) = 1 := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; field_simp
  have he : ∀ ω, F ω 0 = 0 →
      ∑ k ∈ range n, 1 / (n : ℝ) * -Y k ω = -(F ω ((n : ℝ) * t) / n) := by
    intro ω h0
    rw [← Finset.mul_sum, Finset.sum_neg_distrib]
    simp only [hY]
    rw [jr_telescope (F ω) h0 t n]; ring
  set R : Ω → ℝ := fun ω => ∑ k ∈ range n, 1 / (n : ℝ) * exp (-Y k ω) with hR
  set L : Ω → ℝ := fun ω => exp (-(F ω ((n : ℝ) * t) / n)) with hLdef
  have hRint : Integrable R P :=
    integrable_finsetSum _ (fun k _ => (hint _ (hYm k) (hYnn.mono fun ω h => h k)).const_mul _)
  have hLnn : ∀ᵐ ω ∂P, 0 ≤ F ω ((n : ℝ) * t) / n := by
    filter_upwards [hYnn, hgood] with ω h hω
    rw [← jr_telescope (F ω) hω.2.2 t n]
    exact div_nonneg (sum_nonneg fun k _ => h k) hnpos.le
  have hLint : Integrable L P := hint _ ((hmeas _).div_const _) hLnn
  have hRL : ∫ ω, (R ω - L ω) ∂P = 0 := by
    rw [integral_sub hRint hLint, hR, integral_finsetSum _ (fun k _ =>
      (hint _ (hYm k) (hYnn.mono fun ω h => h k)).const_mul _)]
    simp_rw [integral_const_mul, hYl]
    rw [hLdef]; simp only
    rw [hL, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp; ring
  have hLR : ∀ᵐ ω ∂P, L ω ≤ R ω := by
    filter_upwards [hgood] with ω hω
    have := convexOn_exp.map_sum_le (t := range n) (w := fun _ => 1 / (n : ℝ))
      (p := fun k => -Y k ω) (fun _ _ => by positivity) hw1 (fun _ _ => Set.mem_univ _)
    simp only [smul_eq_mul] at this
    rw [he ω hω.2.2] at this
    exact this
  have hEq : ∀ᵐ ω ∂P, R ω - L ω = 0 := by
    have := (integral_eq_zero_iff_of_nonneg_ae (hLR.mono fun ω h => sub_nonneg.mpr h)
      (hRint.sub hLint)).mp hRL
    filter_upwards [this] with ω h
    simpa using h
  filter_upwards [hEq, hgood] with ω h hω k hk
  have := strictConvexOn_exp.eq_of_le_map_sum (t := range n) (w := fun _ => 1 / (n : ℝ))
    (p := fun k => -Y k ω) (fun _ _ => by positivity) hw1 (fun _ _ => Set.mem_univ _)
    (by simp only [smul_eq_mul]; rw [he ω hω.2.2]; exact (sub_eq_zero.mp h).le)
    (mem_range.mpr hk) (mem_range.mpr (show 0 < n by omega))
  simp only [hY, neg_inj, Nat.cast_zero, zero_add, one_mul, zero_mul, hω.2.2, sub_zero] at this
  exact this

/-- **Blueprint A7 (Jensen rigidity).** -/
theorem jensen_rigidity (F : Ω → ℝ → ℝ) (hmeas : ∀ s, Measurable fun ω => F ω s)
    (hgood : ∀ᵐ ω ∂P, ContinuousOn (F ω) (Set.Ici 0) ∧ MonotoneOn (F ω) (Set.Ici 0) ∧ F ω 0 = 0)
    (hinc : ∀ q : ℚ, 0 < q → ∀ k : ℕ, 1 ≤ k →
      P.map (fun ω => F ω ((k : ℝ) * q) - F ω (((k : ℝ) - 1) * q)) = P.map (fun ω => F ω q))
    (hscale : ∀ q : ℚ, 0 < q → ∀ n : ℕ, 1 ≤ n →
      P.map (fun ω => F ω ((n : ℝ) * q) / n) = P.map (fun ω => F ω q)) :
    ∀ᵐ ω ∂P, ∀ s, 0 ≤ s → F ω s = s * F ω 1 := by
  set u : ℕ → ℝ := fun m => 1 / ((m : ℝ) + 1) with hu
  have hall : ∀ᵐ ω ∂P, ∀ m n : ℕ, ∀ k < n + 1,
      F ω (((k : ℝ) + 1) * u m) - F ω ((k : ℝ) * u m) = F ω (u m) := by
    rw [ae_all_iff]; intro m; rw [ae_all_iff]; intro n
    have hq : (0 : ℚ) < 1 / ((m : ℚ) + 1) := by positivity
    have hcast : (((1 / ((m : ℚ) + 1) : ℚ)) : ℝ) = u m := by simp [hu]
    refine jr_increments_ae_eq (by positivity) (n := n + 1) (by omega) F hmeas hgood
      (fun k => ?_) ?_
    · have := hinc _ hq (k + 1) (by omega)
      rw [hcast] at this
      simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using this
    · have := hscale _ hq (n + 1) (by omega)
      rw [hcast] at this
      exact this
  filter_upwards [hall, hgood] with ω h hω s hs
  have hup : ∀ m, 0 < u m := fun m => by positivity
  -- linearity on the grid `k * u m`
  have hlin : ∀ m k : ℕ, F ω ((k : ℝ) * u m) = k * F ω (u m) := by
    intro m k
    rw [← jr_telescope (F ω) hω.2.2 (u m) k]
    rw [Finset.sum_congr rfl (fun i hi => h m k i (by simp at hi; omega))]
    simp
  have hgrid : ∀ m k : ℕ, F ω ((k : ℝ) * u m) = ((k : ℝ) * u m) * F ω 1 := by
    intro m k
    have h1 := hlin m (m + 1)
    have e : ((m + 1 : ℕ) : ℝ) * u m = 1 := by simp [hu]; field_simp
    rw [e] at h1
    rw [hlin m k, h1]; push_cast; simp only [hu]; field_simp
  -- approximate `s` from below by grid points
  set x : ℕ → ℝ := fun m => (⌊s * ((m : ℝ) + 1)⌋₊ : ℝ) * u m with hx
  have hxle : ∀ m, x m ≤ s := by
    intro m
    simp only [hx, hu, mul_one_div]
    rw [div_le_iff₀ (by positivity)]
    exact Nat.floor_le (by positivity)
  have hxge : ∀ m, s - u m ≤ x m := by
    intro m
    have := Nat.lt_floor_add_one (s * ((m : ℝ) + 1))
    simp only [hx, hu]
    have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    rw [sub_le_iff_le_add, show ((⌊s * ((m : ℝ) + 1)⌋₊ : ℕ) : ℝ) * (1 / ((m : ℝ) + 1))
        + 1 / ((m : ℝ) + 1) = (((⌊s * ((m : ℝ) + 1)⌋₊ : ℕ) : ℝ) + 1) / ((m : ℝ) + 1) by ring,
      le_div_iff₀ hm]
    linarith
  have hx0 : ∀ m, 0 ≤ x m := fun m => by simp only [hx]; exact mul_nonneg (by positivity) (hup m).le
  have hlim : Tendsto x atTop (𝓝 s) := by
    have hu0 : Tendsto u atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    have : Tendsto (fun m => s - u m) atTop (𝓝 s) := by simpa using hu0.const_sub s
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le this tendsto_const_nhds hxge hxle
  have hF : Tendsto (fun m => F ω (x m)) atTop (𝓝 (F ω s)) :=
    (hω.1 s hs).tendsto.comp (tendsto_nhdsWithin_iff.mpr ⟨hlim, Eventually.of_forall hx0⟩)
  have hF' : Tendsto (fun m => F ω (x m)) atTop (𝓝 (s * F ω 1)) := by
    have e : (fun m => F ω (x m)) = fun m => x m * F ω 1 := by
      funext m; simp only [hx]; exact hgrid m _
    rw [e]; exact hlim.mul_const _
  exact tendsto_nhds_unique hF hF'

end QuantumZipper.JensenRigidity
