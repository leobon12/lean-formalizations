import QuantumZipper.Proofs.Zipper.RegContRandom

/-!
# UNIF-RC: convergence of the regularized values along `ν_t` at all times at once

For a fixed folded circle `fc(w, r)` and `ν_t = (f_t⁻¹)_* fc(w, r)` (`RegCont.νT`), the
regularized values `Ψ_k(t) = ∫ avgReg X k dν_t` of the free field converge as `k → ∞`
**simultaneously for all `t ≥ 0`**, almost surely (`ae_forall_tendsto_dyadic`, all dyadic folded
circles at once). This is the uniform-in-time form of RC1 (`CoordReg.ae_evalReg_h0rev_eq_frostman'`
gives the convergence at one fixed deterministic measure).

The probabilistic input is the two-parameter `(t, ρ)` Kolmogorov step of REG-CONT
(`RegCont.ae_UCq`, `RegCont.ae_fibre`: `Ψ_k` is uniformly Cauchy over rational times); uniform
Cauchy over all times then follows from the continuity of `Ψ_k` in `t` (as inside
`RegCont.continuousOn_evalReg_of_uc`), and the transfer to the Brownian driver is that of
`RegCont.ae_continuousOn_unzippedField`.

The deterministic evaluation `evalReg_logMul_add_of_tendsto` is the coefficient-generic form of
`RegUnif.evalReg_h0rev_add_of_tendsto` (the regularization of `a log|·|` converges to its
integral on the Frostman measure `ν_t`).

Sources: Duplantier–Sheffield, *Liouville quantum gravity and KPZ*, Invent. Math. 185 (2011),
Prop. 3.1 (arXiv:0808.1560, p. 18) via `RegCont`; the passage "uniformly Cauchy on rational
times ⇒ convergent at all times" is an own elementary argument (continuity + density).
-/

noncomputable section

open Complex Filter MeasureTheory ProbabilityTheory Set
open scoped Topology Real ENNReal NNReal

namespace QuantumZipper
namespace RegUnif

open CharFun TwoPoint UnzipInvariance RegCont

/-- Coefficient-generic form of `RegCont.avgReg_h0rev_add`. -/
theorem avgReg_logMul_add (a : ℝ) {x : FieldSample} (hx : RegAvgGood x) (k : ℕ) {z : ℂ}
    (hz : z ∈ Hbar) :
    avgReg (ofFun (fun v => a * Real.log ‖v‖) + x) k z =
      a * Real.log (max (radius k) ‖z‖) + avgReg x k z := by
  have hraw : ∀ d : ℂ, (ofFun (fun v => a * Real.log ‖v‖) + x) (foldedCircle d (radius k)) =
      a * Real.log (max (radius k) ‖d‖) + x (foldedCircle d (radius k)) := by
    intro d
    simp only [Pi.add_apply, ofFun]
    rw [integral_const_mul, integral_log_norm_fc d (radius_pos k)]
  unfold avgReg
  simp_rw [hraw]
  have hc : Continuous fun d : ℂ => a * Real.log (max (radius k) ‖d‖) :=
    continuous_const.mul (Continuous.log (continuous_const.max continuous_norm) fun d =>
      ((radius_pos k).trans_le (le_max_left _ _)).ne')
  exact ((hc.tendsto z).comp (RegClosure.tendsto_dyadicRoundC z)).add ((hx k).2 z hz)
    |>.limUnder_eq

/-- **Evaluation of `a log|·| + x` at `ν_t`**, given convergence of the regularized values of
`x` (coefficient-generic form of `evalReg_h0rev_add_of_tendsto`). -/
theorem evalReg_logMul_add_of_tendsto {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ}
    (ht : 0 ≤ t) (w : ℂ) {r : ℝ} (hr : 0 < r) (a : ℝ) {x : FieldSample} (hx : RegAvgGood x)
    {L : ℝ} (hL : Tendsto (fun k => ∫ z, avgReg x k z ∂νT W w r t) atTop (𝓝 L)) :
    evalReg (ofFun (fun v => a * Real.log ‖v‖) + x) (νT W w r t) =
      a * (∫ z, Real.log ‖z‖ ∂νT W w r t) + L := by
  obtain ⟨C, B, hC, hB, hfacts⟩ := νT_facts hW hW0 t w hr
  obtain ⟨hP, hF, hae⟩ := hfacts t ⟨ht, le_rfl⟩
  have hK : IsCompact (Metric.closedBall (0 : ℂ) B ∩ Hbar) :=
    (isCompact_closedBall _ _).inter_right isClosed_Hbar
  have hνK : νT W w r t (Metric.closedBall (0 : ℂ) B ∩ Hbar)ᶜ = 0 := by
    have h1 : ∀ᵐ z ∂νT W w r t, z ∈ Metric.closedBall (0 : ℂ) B ∩ Hbar :=
      hae.mono fun z hz => ⟨mem_closedBall_zero_iff.2 hz.2, (show (0 : ℝ) < z.im from hz.1).le⟩
    exact ae_iff.1 h1
  have hint : ∀ G : ℂ → ℝ, ContinuousOn G Hbar → Integrable G (νT W w r t) := fun G hG =>
    FrostmanReg.integrable_of_continuousOn_frostman hK inter_subset_right hνK hG
  have e : ∀ k, ∫ z, avgReg (ofFun (fun v => a * Real.log ‖v‖) + x) k z ∂νT W w r t =
      a * (∫ z, Real.log (max (radius k) ‖z‖) ∂νT W w r t) +
        ∫ z, avgReg x k z ∂νT W w r t := by
    intro k
    rw [integral_congr_ae (hae.mono fun z hz =>
        avgReg_logMul_add a hx k ((show (0 : ℝ) < z.im from hz.1).le)),
      integral_add ((hint _ (Continuous.log (continuous_const.max continuous_norm) fun d =>
        ((radius_pos k).trans_le (le_max_left _ _)).ne').continuousOn).const_mul _)
        (hint _ (hx k).1), integral_const_mul]
  have hlog : Tendsto (fun k => ∫ z, Real.log (max (radius k) ‖z‖) ∂νT W w r t) atTop
      (𝓝 (∫ z, Real.log ‖z‖ ∂νT W w r t)) := by
    have ht3 := (tendsto_rpow_radius_zero (a := 1 / 3) (by norm_num)).const_mul (3 * C)
    rw [mul_zero] at ht3
    refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun k => norm_nonneg _)
      (fun k => ?_) ht3)
    rw [Real.norm_eq_abs]
    exact (integral_log_max_sub_le hF (hae.mono fun z hz h => by subst h; simp [H] at hz)
      (hae.mono fun z hz => hz.2) (radius_pos k) (radius_le_one k)).2
  unfold evalReg
  simp_rw [e]
  exact ((hlog.const_mul _).add hL).limUnder_eq

/-- **Uniformly Cauchy over rational times ⇒ convergent at every time** of `[0, T]` (own
elementary argument; the uniform-Cauchy step is that of `continuousOn_evalReg_of_uc`). -/
theorem tendsto_PsiK_of_uc {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ}
    (hT : 0 < T) (w : ℂ) {r : ℝ} (hr : 0 < r) {x : FieldSample} (hx : RegAvgGood x)
    (huc : UCq W w r T x) :
    ∀ s ∈ Icc (0 : ℝ) T, ∃ L, Tendsto (fun k => ∫ z, avgReg x k z ∂νT W w r s) atTop (𝓝 L) := by
  set S := Icc (0 : ℝ) T with hS
  set Ψ : ℕ → ℝ → ℝ := fun k s => PsiK W w r s k x with hΨ
  have hΨc : ∀ k, ContinuousOn (Ψ k) S := fun k =>
    continuousOn_integral_νT hW hW0 T w hr (RegClosure.measurable_avgReg_slice x k) (hx k).1
  have hUC : ∀ n : ℕ, ∃ N : ℕ, ∀ k, N ≤ k → ∀ k', N ≤ k' → ∀ s ∈ S,
      |Ψ k s - Ψ k' s| ≤ 1 / ((n : ℝ) + 1) := by
    intro n
    obtain ⟨N, hN⟩ := huc n
    refine ⟨N, fun k hk k' hk' s hs => ?_⟩
    have hcont : ContinuousOn (fun s => |Ψ k s - Ψ k' s|) S := ((hΨc k).sub (hΨc k')).abs
    refine ContinuousWithinAt.closure_le (Icc_subset_closure_rat hT hs)
      ((hcont s hs).mono (inter_subset_left.trans Ioo_subset_Icc_self)) continuousWithinAt_const ?_
    rintro y ⟨hy, q, rfl⟩
    exact hN k hk k' hk' q (Ioo_subset_Icc_self hy)
  have hUCS : UniformCauchySeqOn Ψ atTop S := by
    rw [Metric.uniformCauchySeqOn_iff]
    intro ε hε
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    obtain ⟨N, hN⟩ := hUC n
    exact ⟨N, fun k hk k' hk' s hs => by rw [Real.dist_eq]; exact (hN k hk k' hk' s hs).trans_lt hn⟩
  intro s hs
  exact ⟨_, (hUCS.cauchySeq hs).tendsto_limUnder⟩

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

/-- **Convergence of the regularized values at all times of `[0, T]`**, fixed circle, Brownian
driver (transfer as in `RegCont.ae_continuousOn_unzippedField`). -/
theorem ae_forall_tendsto_PsiK [IsProbabilityMeasure P] (κ : ℝ) {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P)
    {T : ℝ} (hT : 0 < T) (w : ℂ) {r : ℝ} (hr : 0 < r) :
    ∀ᵐ ω ∂P, ∀ s ∈ Icc (0 : ℝ) T, ∃ L,
      Tendsto (fun k => ∫ z, avgReg (X ω) k z ∂νT (drive κ B ω) w r s) atTop (𝓝 L) := by
  obtain ⟨B', hB'm, hB'c, hB'eq⟩ := exists_good_version hB
  have hXm : Measurable X := measurable_pi_iff.2 hX.measurable_coord
  have hpath : pathOf B =ᵐ[P] pathOf B' := hB'eq.mono fun ω h => funext fun t => (h t).symm
  have hind' : IndepFun (pathC T B' hB'c) X P :=
    indepFun_pathC T (hind.congr hpath (ae_eq_refl _)) hB'c
  set a : ℝ := 1 / 3
  have hE := ae_indep (measurable_pathC T hB'm hB'c) hXm hind'
    ((measurableSet_GoodP hT.le a).compl.prod MeasurableSet.univ |>.union
      (measurableSet_UCm hT.le κ w r)) (fun f => by
        filter_upwards [ae_fibre hX hT κ (a := a) (by norm_num) (by norm_num) w hr f] with ω h
        rcases h with h | h
        · exact Or.inl ⟨h, trivial⟩
        · exact Or.inr h)
  have hgood : ∀ᵐ ω ∂P, pathC T B' hB'c ω ∈ GoodP hT.le a := by
    filter_upwards [RS.bm_holder hB (a := a) (by norm_num), hB.eval_zero_ae_eq_zero, hB'eq]
      with ω hH h0 heq
    refine pathC_mem_GoodP hT.le hB'c (by rw [heq]; exact h0) ?_
    obtain ⟨C, hC⟩ := hH T.toNNReal
    exact ⟨C, fun t ht s hs0 hs1 => by rw [heq, heq]; exact hC t ht s hs0 hs1⟩
  have hreg : ∀ᵐ ω ∂P, RegAvgGood (X ω) := by
    exact ae_all_iff.2 fun k => FrostmanReg.ae_circleAvg_tendsto_frostman hX k
  filter_upwards [hE, hgood, hreg, hB'eq] with ω hE hgood hreg heq
  set f := pathC T B' hB'c ω
  have hf0 := Wof_zero_of_GoodP hT.le κ hgood
  have huc : UCq (Wof κ T hT.le f) w r T (X ω) := by
    rcases hE with h | h
    · exact absurd hgood h.1
    · exact (UCm_iff hT.le κ w hr f hf0 (X ω)).1 h
  have hdrive : drive κ B ω = drive κ B' ω := funext fun t => by simp [drive, heq]
  have hdc : Continuous (drive κ B ω) := by
    rw [hdrive]; exact continuous_const.mul ((hB'c ω).comp continuous_real_toNNReal)
  have hEq : EqOn (drive κ B ω) (Wof κ T hT.le f) (Icc 0 T) := by
    intro t ht
    rw [hdrive]
    simp only [drive, Wof, f, pathC, ContinuousMap.coe_mk, projIcc_of_mem hT.le ht]
  have hd0 : drive κ B ω 0 = 0 := (hEq ⟨le_rfl, hT.le⟩).trans hf0
  intro s hs
  obtain ⟨L, hL⟩ := tendsto_PsiK_of_uc (continuous_Wof κ T hT.le f) hf0 hT w hr hreg huc s hs
  have hν : νT (drive κ B ω) w r s = νT (Wof κ T hT.le f) w r s :=
    Measure.map_congr ((foldedCircle_ae_mem_H w hr).mono fun z hz =>
      fwdMapInv_congr hdc hd0 (continuous_Wof κ T hT.le f) hf0 hEq hs hz)
  exact ⟨L, by rw [hν]; exact hL⟩

/-- **All dyadic folded circles, all times `t ≥ 0`.** Almost surely, for every `t ≥ 0` and every
dyadic folded circle `fc(lpt n a b, 2^{-k})`, the regularized values `∫ avgReg X j dν_t` converge
as `j → ∞`. -/
theorem ae_forall_tendsto_dyadic [IsProbabilityMeasure P] (κ : ℝ) {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → ∀ (n : ℕ) (a b : ℤ) (k : ℕ), ∃ L,
      Tendsto (fun j => ∫ z, avgReg (X ω) j z
        ∂νT (drive κ B ω) (CircleCont.lpt n a b) (radius k) t) atTop (𝓝 L) := by
  have h : ∀ m : ℕ, ∀ᵐ ω ∂P, ∀ (n : ℕ) (a b : ℤ) (k : ℕ), ∀ s ∈ Icc (0 : ℝ) ((m : ℝ) + 1),
      ∃ L, Tendsto (fun j => ∫ z, avgReg (X ω) j z
        ∂νT (drive κ B ω) (CircleCont.lpt n a b) (radius k) s) atTop (𝓝 L) := fun m => by
    simp only [ae_all_iff]
    intro n a b k
    exact ae_forall_tendsto_PsiK κ hB hX hind (Nat.cast_add_one_pos m) _ (radius_pos k)
  filter_upwards [ae_all_iff.2 h] with ω hω t ht n a b k
  obtain ⟨m, hm⟩ := exists_nat_ge t
  exact hω m n a b k t ⟨ht, hm.trans (by linarith)⟩

end RegUnif
end QuantumZipper
