import MeshRates.ExitTime

/-!
# The expected exit time is the torsion function (MR §6, (74)–(76))

`G(y) = E_y τ_S` vanishes off `S` and solves `m⁻¹ Δ G = -1` on `S`. Proof: the survival
probability is the killed heat flow `u(t) = exp(t Q_S) 1_S`; integrate Kolmogorov's equation
`u' = Q_S u` on `[0, b]` and let `b → ∞`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal NNReal
open MeasureTheory Filter Topology

namespace BouRabeeGwynne.MeshRates

open Classical in
/-- `P_x(τ_S > t)` is the killed heat flow of the constant `1` (any start `x`). -/
theorem survivalProb_eq_killedHeatFlow {d : ℕ} (T : OrthogonalTiling d) (R : Set T.V)
    [Fintype R] [MeasurableSpace R] [MeasurableSingletonClass R] (S : Set R) (x : R)
    (t : ℝ≥0) :
    survivalProb T R S x t = (T.finiteNetwork R).killedHeatFlow
      (fun v : R => (T.cell v).volume.toReal) S (fun _ => 1) t x := by
  set N := T.finiteNetwork R
  set m : R → ℝ := fun v => (T.cell v).volume.toReal
  have hm : ∀ v, 0 < m v := fun v => cellVolume_toReal_pos T v
  unfold survivalProb
  calc _ = ∑ y ∈ S.toFinset, (N.poissonizedUniformizedLaw m hm S x t {y}).toReal := by
        simpa only [measureReal_def, Set.coe_toFinset] using
          (sum_measureReal_singleton (μ := N.poissonizedUniformizedLaw m hm S x t)
            S.toFinset).symm
    _ = ∑ y ∈ S.toFinset, N.killedHeatMatrix m S t x y := by
        apply Finset.sum_congr rfl
        intro y hy
        exact N.poissonizedUniformizedLaw_singleton m hm S x (Set.mem_toFinset.mp hy) t
    _ = _ := by
        simp only [FiniteConductanceNetwork.killedHeatFlow, Matrix.mulVec, dotProduct,
          Set.indicator_apply, mul_ite, mul_one, mul_zero]
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
        congr 1
        ext y; simp

open Classical in
/-- The expected exit time is the torsion function of `S`: it vanishes off `S` and
`L G = -1` on `S`, where `L = m⁻¹Δ` is the generator MR (27) (`massGenerator`). -/
theorem expectedExitTime_torsion {d : ℕ} (T : OrthogonalTiling d) (R : Set T.V) [Fintype R]
    [MeasurableSpace R] [MeasurableSingletonClass R] (S : Set R)
    (hfin : ∀ x ∈ S, expectedExitTime T R S x ≠ ∞)
    (hdecay : ∀ x ∈ S, Filter.Tendsto (fun t : ℝ≥0 => survivalProb T R S x t) Filter.atTop
      (nhds 0)) :
    (∀ x ∉ S, expectedExitTime T R S x = 0) ∧
    ∀ x ∈ S, (T.finiteNetwork R).massGenerator (fun v : R => (T.cell v).volume.toReal)
        (fun y => (expectedExitTime T R S y).toReal) x = -1 := by
  set N := T.finiteNetwork R
  set m : R → ℝ := fun v => (T.cell v).volume.toReal
  set F : ℝ → R → ℝ := N.killedHeatFlow m S (fun _ => 1) with hF
  set Q := N.killedGeneratorMatrix m S
  have hsurv : ∀ x (t : ℝ), 0 ≤ t → survivalProb T R S x t.toNNReal = F t x := by
    intro x t ht
    rw [survivalProb_eq_killedHeatFlow, Real.coe_toNNReal t ht]
  have hFnn : ∀ x (t : ℝ), 0 ≤ t → 0 ≤ F t x := by
    intro x t ht; rw [← hsurv x t ht]; exact ENNReal.toReal_nonneg
  have hE : ∀ x, expectedExitTime T R S x = ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (F t x) := by
    intro x
    unfold expectedExitTime
    refine setLIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    rw [hsurv x t (le_of_lt ht)]
  have hout : ∀ x ∉ S, expectedExitTime T R S x = 0 := by
    intro x hx
    rw [hE]
    simp [hF, N.killedHeatFlow_eq_zero_of_not_mem m S _ _ hx]
  have hderiv : ∀ x (t : ℝ), HasDerivAt (fun s => F s x) (∑ y, Q x y * F t y) t := by
    intro x t
    have h := N.hasDerivAt_killedHeatFlow_apply m S (fun _ => 1) t x
    rw [← N.killedGeneratorMatrix_mulVec] at h
    simpa [Matrix.mulVec, dotProduct] using h
  have hcont : ∀ y, Continuous (fun s => F s y) := fun y =>
    continuous_iff_continuousAt.2 fun t => (hderiv y t).continuousAt
  have hfin' : ∀ y, expectedExitTime T R S y ≠ ∞ := by
    intro y
    by_cases hy : y ∈ S
    · exact hfin y hy
    · simp [hout y hy]
  -- `∫_0^b u(y) → G(y)`
  have hlim : ∀ y, Tendsto (fun b => ∫ t in (0 : ℝ)..b, F t y) atTop
      (𝓝 (expectedExitTime T R S y).toReal) := by
    intro y
    have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))] fun t => F t y :=
      ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht => hFnn y t (le_of_lt ht))
    have hint : IntegrableOn (fun t => F t y) (Set.Ioi (0 : ℝ)) := by
      refine ⟨(hcont y).aestronglyMeasurable, ?_⟩
      rw [hasFiniteIntegral_iff_ofReal hnn, ← hE]
      exact lt_top_iff_ne_top.2 (hfin' y)
    have h := intervalIntegral_tendsto_integral_Ioi 0 hint tendsto_id
    rwa [integral_eq_lintegral_of_nonneg_ae hnn (hcont y).aestronglyMeasurable, ← hE] at h
  refine ⟨hout, fun x hx => ?_⟩
  -- FTC: `u(b) - 1 = Σ_y Q x y ∫_0^b u(y)`
  have hftc : ∀ b, F b x - 1 = ∑ y, Q x y * ∫ t in (0 : ℝ)..b, F t y := by
    intro b
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := b)
      (fun t _ => hderiv x t)
      ((continuous_finsetSum _ fun y _ => (hcont y).const_mul (Q x y)).intervalIntegrable _ _)
    rw [intervalIntegral.integral_finsetSum (fun y _ =>
      ((hcont y).const_mul (Q x y)).intervalIntegrable _ _)] at h
    simp only [intervalIntegral.integral_const_mul] at h
    rw [h]
    simp [hF, hx]
  have hdec : Tendsto (fun b : ℝ => F b x) atTop (𝓝 0) := by
    refine ((hdecay x hx).comp tendsto_real_toNNReal_atTop).congr' ?_
    filter_upwards [eventually_ge_atTop 0] with b hb
    exact hsurv x b hb
  have h1 : Tendsto (fun b => F b x - 1) atTop (𝓝 (0 - 1)) := hdec.sub_const 1
  have h2 : Tendsto (fun b => F b x - 1) atTop
      (𝓝 (∑ y, Q x y * (expectedExitTime T R S y).toReal)) := by
    simp_rw [hftc]
    exact tendsto_finsetSum _ fun y _ => (hlim y).const_mul (Q x y)
  have heq := tendsto_nhds_unique h2 h1
  have hG : S.indicator (fun y => (expectedExitTime T R S y).toReal) =
      fun y => (expectedExitTime T R S y).toReal := by
    ext y
    by_cases hy : y ∈ S
    · simp [hy]
    · simp [hy, hout y hy]
  have hmv := congrFun (N.killedGeneratorMatrix_mulVec m S
    (fun y => (expectedExitTime T R S y).toReal)) x
  simp only [Matrix.mulVec, dotProduct, FiniteConductanceNetwork.killedMassGenerator, hG,
    Set.indicator_of_mem hx] at hmv
  rw [← hmv]
  simpa using heq

end BouRabeeGwynne.MeshRates
