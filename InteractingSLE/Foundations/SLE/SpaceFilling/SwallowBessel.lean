import InteractingSLE.Foundations.SLE.SpaceFilling.SwallowReal
import QuantumZipper.Proofs.Probability.BMMoments
import QuantumZipper.Proofs.RS.OnePointState
import InteractingSLE.Foundations.SLE.SpaceFilling.Density

/-!
# Swallowing of real points by SLE_κ, `4 < κ < 8`: hitting and swallowing at once

Packet `planning/packets/PROVE-RS05-74b.md`. The probabilistic inputs of [RS05, Lemma 7.3] for
`4 < κ < 8`: for `x > 0`, `X_t = g_t(x) − W_t` solves `dX = (2/X) dt − √κ dB`, a scaled Bessel
process of dimension `1 + 4/κ < 2`.

* `ae_exists_not_alive`: real points are swallowed, `T_x < ∞` a.s. ([Law] Prop. 6.8, second
  item, from Prop. 1.21). The scale function `y^{1−4/κ}` (QuantumZipper's `dynkinGen_rpow`) gives
  `P(X reaches M before δ) ≤ (x/M)^{1−4/κ}`; while `X ∈ [δ, M]` the drift `2/X ≥ 2/M` pushes
  `√κ B_T ≥ x − M + 2T/M`, which is unlikely by the second moment of `B_T`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open QuantumZipper QuantumZipper.RS

namespace InteractingSLE

section Hitting

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

omit mΩ in
/-- `drive κ B ω` is QuantumZipper's `sDrive (√κ) B ω`. -/
theorem drive_eq_sDrive (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (ω : Ω) : drive κ B ω = sDrive (√κ) B ω := rfl

omit mΩ in
/-- The integral equation of the tamed real flow driven by `s B`, in the form required by
QuantumZipper's local Dynkin formula. -/
theorem realTamed_sDrive_eq (hBc : ∀ ω, Continuous (B · ω)) (s : ℝ) {c : ℝ} (hc : 0 < c) (x : ℝ)
    (ω : Ω) (t : ℝ≥0) :
    realTamed (sDrive s B ω) c x t =
      x + (∫ r in (0 : ℝ)..t, realDrift c (realTamed (sDrive s B ω) c x (r.toNNReal : ℝ))) +
        B t ω • (-s) := by
  have hWc := continuous_sDrive hBc s ω
  rw [realTamed_eq hWc hc x t.coe_nonneg]
  have hint : (∫ r in (0 : ℝ)..t, realDrift c (realTamed (sDrive s B ω) c x r)) =
      ∫ r in (0 : ℝ)..t, realDrift c (realTamed (sDrive s B ω) c x (r.toNNReal : ℝ)) := by
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [uIcc_of_le t.coe_nonneg] at hr
    simp only [Real.coe_toNNReal _ hr.1]
  rw [hint, smul_eq_mul]
  simp only [sDrive, Real.toNNReal_coe]
  ring

/-- **Exit through the top.** For `0 < c < δ < x < M`, `G ≥ 0` harmonic for the tamed generator
on `[δ, M]`: `G(M) · P(the tamed flow reaches M before δ, by time T) ≤ G(x)`. -/
theorem exit_top_bound (hB : IsPreBrownianReal B P) (hBm : ∀ r, Measurable (B r))
    (hBc : ∀ ω, Continuous (B · ω)) (hB0 : ∀ ω, B 0 ω = 0) (s : ℝ) {x δ M c : ℝ}
    (hc : 0 < c) (hcδ : c < δ) (hδx : δ < x) (hxM : x < M) (T : ℝ≥0)
    {G : ℝ → ℝ} (hG : ContDiffOn ℝ 3 G (Ioi 0))
    (hLG : ∀ y ∈ Icc δ M, dynkinGen (realDrift c) (-s) G y = 0)
    (hG0 : ∀ y ∈ Icc δ M, 0 ≤ G y) :
    G M * P.real {ω | ∃ t ∈ Icc (0 : ℝ) T, M ≤ realTamed (sDrive s B ω) c x t ∧
      ∀ r ∈ Icc (0 : ℝ) t, δ < realTamed (sDrive s B ω) c x r} ≤ G x := by
  have hP : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hWc := continuous_sDrive hBc s
  set U : ℝ≥0 → Ω → ℝ := fun t ω => realTamed (sDrive s B ω) c x t with hU_def
  have hU : ∀ ω (t : ℝ≥0),
      U t ω = x + (∫ r in (0 : ℝ)..t, realDrift c (U r.toNNReal ω)) + B t ω • (-s) :=
    fun ω t => realTamed_sDrive_eq hBc s hc x ω t
  set Cl : Set ℝ := Iic δ ∪ Ici M with hCl_def
  set K : Set ℝ := Icc δ M with hK_def
  have hCl : IsClosed Cl := isClosed_Iic.union isClosed_Ici
  have hK : IsClosed K := isClosed_Icc
  have hKO : K ⊆ Ioi 0 := fun y hy => (hc.trans hcδ).trans_le hy.1
  have hbc : Continuous (realDrift c) := (lipschitz_realDrift hc).continuous
  have hbM : ∀ y, ‖realDrift c y‖ ≤ 2 / c := fun y => by
    rw [Real.norm_eq_abs]; exact abs_realDrift_le hc y
  have hUc : ∀ ω, Continuous (U · ω) := Dynkin.continuous_of_integralEq hBc hbc hbM hU
  have hU0 : ∀ ω, U 0 ω = x := fun ω => by rw [hU ω 0]; simp [hB0 ω]
  have hUK : ∀ ω (t : ℝ≥0), t ≤ T → (∀ s < t, U s ω ∉ Cl) → U t ω ∈ K := by
    intro ω t _ ht
    refine mem_of_forall_lt_real hK (hUc ω) (by rw [hU0]; exact ⟨hδx.le, hxM.le⟩) fun q hq => ?_
    have := ht q hq
    simp only [hCl_def, mem_union, mem_Iic, mem_Ici, not_or, not_le] at this
    exact ⟨this.1.le, this.2.le⟩
  obtain ⟨Mb, hMb⟩ := isCompact_Icc.exists_bound_of_continuousOn (hG.continuousOn.mono hKO)
  have hFM : ∀ y ∈ K, |G y| ≤ Mb := fun y hy => by rw [← Real.norm_eq_abs]; exact hMb y hy
  have hmart := FrozenMart.martingale_localDynkin_stopped hB hBc (NonSwallow.bmFilt hBm)
    (NonSwallow.bmFilt_adapted hBm) (NonSwallow.bmFilt_le_past hBm) (lipschitz_realDrift hc) hbM
    hU isOpen_Ioi hCl hK hKO hG (fun y hy _ => hLG y hy) T hUK hFM
  set τ := hittingBtwn U Cl 0 T with hτ_def
  have hint := hmart.setIntegral_eq (zero_le : (0 : ℝ≥0) ≤ T) MeasurableSet.univ
  simp only [setIntegral_univ] at hint
  have hleft : ∫ ω, G (U (min 0 (τ ω)) ω) ∂P = G x := by
    have : ∀ ω, G (U (min 0 (τ ω)) ω) = G x := fun ω => by rw [min_eq_left (zero_le), hU0]
    rw [integral_congr_ae (ae_of_all _ this)]
    simp
  have hτT : ∀ ω, τ ω ≤ T := fun ω => hittingBtwn_le ω
  have hfK : ∀ ω, U (min T (τ ω)) ω ∈ K := fun ω => by
    rw [min_eq_right (hτT ω)]
    exact hUK ω _ (hτT ω) fun q hq => notMem_of_lt_hittingBtwn hq (zero_le)
  have hmarkov := mul_meas_ge_le_integral_of_nonneg (μ := P)
    (f := fun ω => G (U (min T (τ ω)) ω))
    (ae_of_all _ fun ω => hG0 _ (hfK ω)) (hmart.integrable T) (G M)
  rw [← hint, hleft] at hmarkov
  refine le_trans (mul_le_mul_of_nonneg_left (measureReal_mono ?_)
    (hG0 M ⟨(hδx.trans hxM).le, le_rfl⟩)) hmarkov
  rintro ω ⟨t, ht, htM, hδ⟩
  show G M ≤ G (U (min T (τ ω)) ω)
  have htT : t.toNNReal ≤ T := (Real.toNNReal_le_iff_le_coe).2 ht.2
  have hex : ∃ j ∈ Icc (0 : ℝ≥0) T, U j ω ∈ Cl :=
    ⟨t.toNNReal, ⟨zero_le, htT⟩, Or.inr (by
      show M ≤ U t.toNNReal ω
      simp only [hU_def, Real.coe_toNNReal _ ht.1]; exact htM)⟩
  have hmem := hittingBtwn_mem_real hCl (hUc ω) hex
  have hτt : τ ω ≤ t.toNNReal := hittingBtwn_le_of_mem zero_le htT (by
    show U t.toNNReal ω ∈ Cl
    exact Or.inr (by simp only [hU_def, Real.coe_toNNReal _ ht.1]; exact htM))
  have hK' := hfK ω
  rw [min_eq_right (hτT ω)] at hK' ⊢
  have hgt : δ < U (τ ω) ω := by
    have := hδ (τ ω) ⟨(τ ω).coe_nonneg, by
      have := NNReal.coe_le_coe.2 hτt; rwa [Real.coe_toNNReal _ ht.1] at this⟩
    simpa [hU_def] using this
  have heq : U (τ ω) ω = M := by
    rcases hmem with h | h
    · exact absurd h (not_le.2 hgt)
    · exact le_antisymm hK'.2 h
  rw [heq]

/-- **Second-moment bound** for `s B_T`: `P(a ≤ s B_T) ≤ s² T / a²`. -/
theorem measureReal_le_mul_le (hB : IsPreBrownianReal B P) {s a : ℝ} (hs : 0 < s) (ha : 0 < a)
    (T : ℝ≥0) : P.real {ω | a ≤ s * B T ω} ≤ s ^ 2 * T / a ^ 2 := by
  have hP : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hint : Integrable (fun ω => B T ω ^ 2) P := by
    have := QuantumZipper.integrable_pow hB T 2
    simpa [sq_abs] using this
  have hm := mul_meas_ge_le_integral_of_nonneg (μ := P) (f := fun ω => B T ω ^ 2)
    (ae_of_all _ fun ω => sq_nonneg _) hint ((a / s) ^ 2)
  rw [QuantumZipper.integral_sq hB T] at hm
  have hsub : {ω | a ≤ s * B T ω} ⊆ {ω | (a / s) ^ 2 ≤ B T ω ^ 2} := fun ω hω => by
    have h1 : a / s ≤ B T ω := by
      rw [div_le_iff₀ hs]; have : a ≤ s * B T ω := hω; linarith
    exact pow_le_pow_left₀ (by positivity) h1 2
  have hpos : 0 < (a / s) ^ 2 := by positivity
  calc P.real {ω | a ≤ s * B T ω} ≤ P.real {ω | (a / s) ^ 2 ≤ B T ω ^ 2} := measureReal_mono hsub
    _ ≤ T / (a / s) ^ 2 := by rw [le_div_iff₀ hpos]; linarith
    _ = s ^ 2 * T / a ^ 2 := by field_simp

/-- **Survival bound.** For `κ > 4`, `0 < x < M` and `a = x − M + 2T/M > 0`, the probability that
`x` is still alive at time `T` is at most `(x/M)^{1−4/κ} + κT/a²`. -/
theorem measureReal_alive_le (hB : IsBrownianReal B P) (hBm : ∀ r, Measurable (B r))
    (hBc : ∀ ω, Continuous (B · ω)) (hB0 : ∀ ω, B 0 ω = 0) {κ : ℝ} (hκ : 4 < κ) {x M : ℝ}
    (hx : 0 < x) (hxM : x < M) (T : ℝ≥0) (ha : 0 < x - M + 2 * T / M) :
    P.real {ω | ∃ v, IsForwardSol (drive κ B ω) (x : ℂ) T v} ≤
      (x / M) ^ (1 - 4 / κ) + κ * T / (x - M + 2 * T / M) ^ 2 := by
  have hP : IsProbabilityMeasure P := hB.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  have hκ0 : 0 < κ := by linarith
  set s := √κ with hsdef
  have hs : 0 < s := Real.sqrt_pos.2 hκ0
  have hs2 : s ^ 2 = κ := Real.sq_sqrt hκ0.le
  have he : -s * -s = κ := by rw [neg_mul_neg, ← sq, hs2]
  set α := 1 - 4 / κ with hαdef
  have hα : 0 < α := by
    have : 4 / κ < 1 := (div_lt_one hκ0).2 hκ
    linarith
  set a := x - M + 2 * T / M with hadef
  set bound := (x / M) ^ α + κ * T / a ^ 2 with hbound
  set A : ℕ → Set Ω := fun k => {ω | ∃ v, IsForwardSol (drive κ B ω) (x : ℂ) T v ∧
    ∀ t ∈ Icc (0 : ℝ) T, 1 / ((k : ℝ) + 1) ≤ (v t).re} with hAdef
  have hAmono : Monotone A := by
    intro k l hkl ω ⟨v, hv, hle⟩
    refine ⟨v, hv, fun t ht => le_trans ?_ (hle t ht)⟩
    gcongr
  have hunion : {ω | ∃ v, IsForwardSol (drive κ B ω) (x : ℂ) T v} = ⋃ k, A k := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion, hAdef]
    constructor
    · rintro ⟨v, hv⟩
      obtain ⟨m, hm, hmle⟩ := exists_pos_le_re_of_isForwardSol (drive_continuous (hBc ω))
        (by simp [drive, hB0 ω]) hx T.coe_nonneg hv
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt hm
      exact ⟨k, v, hv, fun t ht => hk.le.trans (hmle t ht)⟩
    · rintro ⟨k, v, hv, -⟩
      exact ⟨v, hv⟩
  have hAk : ∀ k, P.real (A k) ≤ bound := by
    intro k
    set δ₀ := 1 / ((k : ℝ) + 1) with hδ₀def
    have hδ₀ : 0 < δ₀ := by positivity
    set δ := min δ₀ x / 2 with hδdef
    have hδ : 0 < δ := by positivity
    have hδδ₀ : δ < δ₀ := by have := min_le_left δ₀ x; linarith
    have hδx : δ < x := by have := min_le_right δ₀ x; linarith
    set c := δ / 2 with hcdef
    have hc : 0 < c := by positivity
    have hcδ : c < δ := by linarith
    set E : Set Ω := {ω | ∃ t ∈ Icc (0 : ℝ) T, M ≤ realTamed (sDrive s B ω) c x t ∧
      ∀ r ∈ Icc (0 : ℝ) t, δ < realTamed (sDrive s B ω) c x r} with hEdef
    have hsub : A k ⊆ E ∪ {ω | a ≤ s * B T ω} := by
      rintro ω ⟨v, hv, hvle⟩
      have hWc : Continuous (sDrive s B ω) := continuous_sDrive hBc s ω
      have hW0 : sDrive s B ω 0 = 0 := by simp [sDrive, hB0 ω]
      have hagree := realTamed_eq_re_of_isForwardSol hWc hW0 hc hv
        (fun t ht => by linarith [hvle t ht])
      have hge : ∀ t ∈ Icc (0 : ℝ) T, δ₀ ≤ realTamed (sDrive s B ω) c x t := fun t ht => by
        rw [hagree t ht]; exact hvle t ht
      by_cases hM : ∃ t ∈ Icc (0 : ℝ) T, M ≤ realTamed (sDrive s B ω) c x t
      · obtain ⟨t, ht, htM⟩ := hM
        exact Or.inl ⟨t, ht, htM, fun r hr => by
          linarith [hge r ⟨hr.1, hr.2.trans ht.2⟩]⟩
      · push Not at hM
        refine Or.inr ?_
        show a ≤ s * B T ω
        have heq := realTamed_sDrive_eq hBc s hc x ω T
        have hlow : 2 * T / M ≤
            ∫ r in (0 : ℝ)..T, realDrift c (realTamed (sDrive s B ω) c x (r.toNNReal : ℝ)) := by
          have hcont : Continuous fun r : ℝ =>
              realDrift c (realTamed (sDrive s B ω) c x (r.toNNReal : ℝ)) := by
            have h1 := (lipschitz_realDrift hc).continuous
            have h2 : Continuous fun r : ℝ => realTamed (sDrive s B ω) c x (r.toNNReal : ℝ) := by
              have := Dynkin.continuous_of_integralEq hBc h1
                (fun y => by rw [Real.norm_eq_abs]; exact abs_realDrift_le hc y)
                (fun ω t => realTamed_sDrive_eq hBc s hc x ω t) ω
              exact this.comp continuous_real_toNNReal
            exact h1.comp h2
          have hconst : (∫ r in (0 : ℝ)..T, (2 / M : ℝ)) = 2 * T / M := by
            rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero]; ring
          rw [← hconst]
          refine intervalIntegral.integral_mono_on T.coe_nonneg (by simp)
            (hcont.intervalIntegrable _ _) fun r hr => ?_
          have hr' : (r.toNNReal : ℝ) ∈ Icc (0 : ℝ) T := by
            rw [Real.coe_toNNReal _ hr.1]; exact hr
          have hU1 := hge _ hr'
          have hU2 := hM _ hr'
          rw [realDrift_of_le (by linarith)]
          exact div_le_div_of_nonneg_left zero_le_two (by linarith) hU2.le
        have hUT := hM T ⟨T.coe_nonneg, le_rfl⟩
        rw [heq, smul_eq_mul] at hUT
        linarith
    have hEb : P.real E ≤ (x / M) ^ α := by
      have h := exit_top_bound hB.toIsPreBrownianReal hBm hBc hB0 s hc hcδ hδx hxM T
        (G := fun z => z ^ α)
        (fun y hy => (Real.contDiffAt_rpow_const_of_ne (mem_Ioi.1 hy).ne').contDiffWithinAt)
        (fun y hy => dynkinGen_rpow hκ0 he hc (hcδ.le.trans hy.1))
        (fun y hy => Real.rpow_nonneg ((hδ.trans_le hy.1).le) _)
      have hMα : 0 < M ^ α := Real.rpow_pos_of_pos (hx.trans hxM) α
      rw [Real.div_rpow hx.le (hx.trans hxM).le, le_div_iff₀ hMα]
      simpa only [mul_comm] using h
    have hCb := measureReal_le_mul_le hB.toIsPreBrownianReal hs ha T
    rw [hs2] at hCb
    calc P.real (A k) ≤ P.real (E ∪ {ω | a ≤ s * B T ω}) := measureReal_mono hsub
      _ ≤ P.real E + P.real {ω | a ≤ s * B T ω} := measureReal_union_le _ _
      _ ≤ bound := add_le_add hEb hCb
  rw [hunion, measureReal_def, Monotone.measure_iUnion hAmono]
  have hb0 : 0 ≤ bound := add_nonneg (Real.rpow_nonneg (div_nonneg hx.le (hx.trans hxM).le) _)
    (div_nonneg (mul_nonneg hκ0.le T.coe_nonneg) (sq_nonneg _))
  refine ENNReal.toReal_le_of_le_ofReal hb0 (iSup_le fun k => ?_)
  rw [← ENNReal.ofReal_toReal (measure_ne_top P (A k))]
  exact ENNReal.ofReal_le_ofReal (hAk k)

/-- **Real points are swallowed** ([Law] Prop. 6.8, second item; [RS05] Lemma 6.1): for `κ > 4`
and `x > 0`, almost surely `x` is not alive at some (integer) time. -/
theorem ae_exists_not_alive (hB : IsBrownianReal B P) (hBm : ∀ r, Measurable (B r))
    (hBc : ∀ ω, Continuous (B · ω)) (hB0 : ∀ ω, B 0 ω = 0) {κ : ℝ} (hκ : 4 < κ) {x : ℝ}
    (hx : 0 < x) : ∀ᵐ ω ∂P, ∃ n : ℕ, ¬ ∃ v, IsForwardSol (drive κ B ω) (x : ℂ) n v := by
  have hP : IsProbabilityMeasure P := hB.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  have hκ0 : 0 < κ := by linarith
  set α := 1 - 4 / κ with hαdef
  have hα : 0 < α := by
    have : 4 / κ < 1 := (div_lt_one hκ0).2 hκ
    linarith
  set D : Set Ω := ⋂ n : ℕ, {ω | ∃ v, IsForwardSol (drive κ B ω) (x : ℂ) n v} with hDdef
  suffices hD : P D = 0 by
    rw [ae_iff]
    refine measure_mono_null (fun ω hω => ?_) hD
    refine mem_iInter.2 fun n => ?_
    by_contra hn
    exact hω ⟨n, hn⟩
  have hDM : ∀ M : ℝ, x < M → P.real D ≤ (x / M) ^ α := by
    intro M hxM
    have hM0 : 0 < M := hx.trans hxM
    have hev : ∀ᶠ n : ℕ in atTop,
        P.real D ≤ (x / M) ^ α + κ * (n : ℝ) / (x - M + 2 * (n : ℝ) / M) ^ 2 := by
      filter_upwards [eventually_gt_atTop ⌈M * (M - x)⌉₊] with n hn
      have hn' : M * (M - x) < n := (Nat.lt_of_ceil_lt hn)
      have ha : 0 < x - M + 2 * ((n : ℝ≥0) : ℝ) / M := by
        rw [NNReal.coe_natCast]
        have : M - x < n / M := by rw [lt_div_iff₀ hM0]; linarith
        have e2 : 2 * (n : ℝ) / M = 2 * ((n : ℝ) / M) := by ring
        have hMx : 0 < M * (M - x) := mul_pos hM0 (sub_pos.2 hxM)
        have h2 : 0 < (n : ℝ) / M := div_pos (by linarith) hM0
        linarith
      have h := measureReal_alive_le hB hBm hBc hB0 hκ hx hxM (n : ℝ≥0) ha
      rw [NNReal.coe_natCast] at h
      exact (measureReal_mono (iInter_subset _ n)).trans h
    have hlim : Tendsto (fun n : ℕ => (x / M) ^ α + κ * (n : ℝ) / (x - M + 2 * (n : ℝ) / M) ^ 2)
        atTop (𝓝 ((x / M) ^ α + 0)) := by
      refine tendsto_const_nhds.add ?_
      have hbound : ∀ᶠ n : ℕ in atTop,
          κ * (n : ℝ) / (x - M + 2 * (n : ℝ) / M) ^ 2 ≤ κ * M ^ 2 / n := by
        filter_upwards [eventually_gt_atTop ⌈M * (M - x)⌉₊] with n hn
        have hn' : M * (M - x) < n := (Nat.lt_of_ceil_lt hn)
        have hnpos : (0 : ℝ) < n := by
          have : (0 : ℝ) ≤ M * (M - x) := by nlinarith
          linarith
        have hle : (n : ℝ) / M ≤ x - M + 2 * (n : ℝ) / M := by
          have : M - x ≤ n / M := by rw [le_div_iff₀ hM0]; linarith
          have e2 : 2 * (n : ℝ) / M = 2 * ((n : ℝ) / M) := by ring
          linarith
        have hpos : 0 < (n : ℝ) / M := div_pos hnpos hM0
        calc κ * (n : ℝ) / (x - M + 2 * (n : ℝ) / M) ^ 2 ≤ κ * (n : ℝ) / ((n : ℝ) / M) ^ 2 :=
              div_le_div_of_nonneg_left (by positivity) (by positivity)
                (pow_le_pow_left₀ hpos.le hle 2)
          _ = κ * M ^ 2 / n := by field_simp
      refine squeeze_zero' (Eventually.of_forall fun n => ?_) hbound
        (tendsto_const_div_atTop_nhds_zero_nat _)
      exact div_nonneg (mul_nonneg hκ0.le n.cast_nonneg) (sq_nonneg _)
    rw [add_zero] at hlim
    exact ge_of_tendsto hlim hev
  have hlimM : Tendsto (fun M : ℝ => (x / M) ^ α) atTop (𝓝 0) := by
    have h1 : Tendsto (fun M : ℝ => x / M) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    have h2 := (Real.continuousAt_rpow_const 0 α (Or.inr hα.le)).tendsto.comp h1
    rwa [Real.zero_rpow hα.ne'] at h2
  have h0 : P.real D ≤ 0 :=
    ge_of_tendsto hlimM ((eventually_gt_atTop x).mono fun M hM => hDM M hM)
  exact (measureReal_eq_zero_iff).1 (le_antisymm h0 measureReal_nonneg)

/-- **Every positive real point has a finite swallowing time**, almost surely. -/
theorem ae_exists_realSwallowAt (hB : IsBrownianReal B P) (hBm : ∀ r, Measurable (B r))
    (hBc : ∀ ω, Continuous (B · ω)) (hB0 : ∀ ω, B 0 ω = 0) {κ : ℝ} (hκ : 4 < κ) {x : ℝ}
    (hx : 0 < x) : ∀ᵐ ω ∂P, ∃ σ, RealSwallowAt (drive κ B ω) x σ := by
  filter_upwards [ae_exists_not_alive hB hBm hBc hB0 hκ hx] with ω ⟨n, hn⟩
  obtain ⟨σ, -, hσ⟩ := exists_realSwallowAt (drive_continuous (hBc ω)) (by simp [drive, hB0 ω])
    hx n.cast_nonneg hn
  exact ⟨σ, hσ⟩

end Hitting

/-! ### The scale function of `w = Y/(Y − X)` -/

section Scale

variable {κ : ℝ}

/-- The density `(v² − v)^{−4/κ}` of the scale function of `w = Y/(Y − X)`, for two real flows
`0 < X < Y` (the ratio `R = X/Y = 1 − 1/w` has scale density `R^{−4/κ}(1 − R)^{8/κ − 2}`,
[Law] Prop. 1.21, [RS05] Lemma 6.6). -/
def wScaleDens (κ v : ℝ) : ℝ := (v ^ 2 - v) ^ (-(4 / κ))

/-- The scale function `Ψ(w) = ∫₂^w (v² − v)^{−4/κ} dv`, `w > 1`. -/
def wScale (κ w : ℝ) : ℝ := ∫ v in (2 : ℝ)..w, wScaleDens κ v

theorem wScaleDens_pos {v : ℝ} (hv : 1 < v) : 0 < wScaleDens κ v :=
  Real.rpow_pos_of_pos (by nlinarith) _

theorem wScaleDens_nonneg {v : ℝ} (hv : 1 ≤ v) : 0 ≤ wScaleDens κ v :=
  Real.rpow_nonneg (by nlinarith) _

theorem continuousAt_wScaleDens {v : ℝ} (hv : 1 < v) : ContinuousAt (wScaleDens κ) v :=
  ContinuousAt.rpow_const (by fun_prop) (Or.inl (by nlinarith))

theorem continuousOn_wScaleDens : ContinuousOn (wScaleDens κ) (Ioi 1) :=
  fun _ hv => (continuousAt_wScaleDens hv).continuousWithinAt

theorem hasDerivAt_wScaleDens {v : ℝ} (hv : 1 < v) :
    HasDerivAt (wScaleDens κ) ((2 * v - 1) * -(4 / κ) * (v ^ 2 - v) ^ (-(4 / κ) - 1)) v := by
  have h : HasDerivAt (fun v : ℝ => v ^ 2 - v) (2 * v - 1) v :=
    ((hasDerivAt_pow 2 v).sub (hasDerivAt_id' v)).congr_deriv (by norm_num)
  exact h.rpow_const (Or.inl (by nlinarith))

theorem contDiffOn_wScaleDens : ContDiffOn ℝ 2 (wScaleDens κ) (Ioi 1) :=
  (by fun_prop : ContDiffOn ℝ 2 (fun v : ℝ => v ^ 2 - v) (Ioi 1)).rpow_const_of_ne
    fun v hv => by have : (1 : ℝ) < v := hv; nlinarith

theorem intervalIntegrable_wScaleDens {a b : ℝ} (ha : 1 < a) (hb : 1 < b) :
    IntervalIntegrable (wScaleDens κ) volume a b :=
  (continuousOn_wScaleDens.mono fun v hv => by
    have := hv.1
    simp only [mem_Ioi]
    exact lt_of_lt_of_le (lt_min ha hb) this).intervalIntegrable

/-- The density is integrable at `1` (exponent `−4/κ > −1`). -/
theorem intervalIntegrable_wScaleDens_one (hκ : 4 < κ) :
    IntervalIntegrable (wScaleDens κ) volume 1 2 := by
  have hκ0 : 0 < κ := by linarith
  have hr : -1 < -(4 / κ) := by
    have : 4 / κ < 1 := (div_lt_one hκ0).2 hκ
    linarith
  have h1 : IntervalIntegrable (fun v : ℝ => (v - 1) ^ (-(4 / κ))) volume 1 2 := by
    have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) hr).comp_sub_right 1
    simpa [one_add_one_eq_two] using this
  have h2 : ContinuousOn (fun v : ℝ => v ^ (-(4 / κ))) (uIcc 1 2) := fun v hv => by
    rw [uIcc_of_le (by norm_num)] at hv
    exact (Real.continuousAt_rpow_const _ _ (Or.inl (by linarith [hv.1]))).continuousWithinAt
  refine (h1.continuousOn_mul h2).congr fun v hv => ?_
  rw [uIoc_of_le (by norm_num)] at hv
  simp only [wScaleDens]
  rw [show v ^ 2 - v = v * (v - 1) by ring, Real.mul_rpow (by linarith [hv.1]) (by linarith [hv.1])]

theorem hasDerivAt_wScale {w : ℝ} (hw : 1 < w) : HasDerivAt (wScale κ) (wScaleDens κ w) w :=
  intervalIntegral.integral_hasDerivAt_right (intervalIntegrable_wScaleDens (by norm_num) hw)
    (continuousOn_wScaleDens.stronglyMeasurableAtFilter isOpen_Ioi w hw)
    (continuousAt_wScaleDens hw)

theorem deriv_wScale_eventuallyEq {w : ℝ} (hw : 1 < w) :
    deriv (wScale κ) =ᶠ[𝓝 w] wScaleDens κ := by
  filter_upwards [Ioi_mem_nhds hw] with v hv
  exact (hasDerivAt_wScale hv).deriv

theorem contDiffOn_wScale : ContDiffOn ℝ 3 (wScale κ) (Ioi 1) := by
  rw [show (3 : WithTop ℕ∞) = 2 + 1 from rfl, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
  refine ⟨fun w hw => (hasDerivAt_wScale hw).differentiableAt.differentiableWithinAt,
    by simp, ?_⟩
  exact contDiffOn_wScaleDens.congr fun w hw => (hasDerivAt_wScale hw).deriv

/-- `Ψ(w) − Ψ(1) = ∫₁^w (v² − v)^{−4/κ} dv`. -/
theorem wScale_sub_wScale_one (hκ : 4 < κ) {w : ℝ} (hw : 1 ≤ w) :
    wScale κ w - wScale κ 1 = ∫ v in (1 : ℝ)..w, wScaleDens κ v := by
  have h12 := intervalIntegrable_wScaleDens_one (κ := κ) hκ
  have h2w : IntervalIntegrable (wScaleDens κ) volume 2 w := by
    rcases hw.eq_or_lt with h | h
    · rw [← h]; exact h12.symm
    · exact intervalIntegrable_wScaleDens (by norm_num) h
  exact intervalIntegral.integral_interval_sub_left h2w h12.symm

theorem wScale_one_le (hκ : 4 < κ) {w : ℝ} (hw : 1 ≤ w) : wScale κ 1 ≤ wScale κ w := by
  have := wScale_sub_wScale_one hκ hw
  have h0 : 0 ≤ ∫ v in (1 : ℝ)..w, wScaleDens κ v :=
    intervalIntegral.integral_nonneg hw fun v hv => wScaleDens_nonneg hv.1
  linarith

theorem wScale_one_lt (hκ : 4 < κ) {w : ℝ} (hw : 1 < w) : wScale κ 1 < wScale κ w := by
  have := wScale_sub_wScale_one hκ hw.le
  have hi : IntervalIntegrable (wScaleDens κ) volume 1 w := by
    have h12 := intervalIntegrable_wScaleDens_one (κ := κ) hκ
    rcases le_or_gt w 2 with h | h
    · refine h12.mono_set ?_
      rw [uIcc_of_le hw.le, uIcc_of_le (by norm_num)]
      exact Icc_subset_Icc_right h
    · exact h12.trans (intervalIntegrable_wScaleDens (by norm_num) (by linarith))
  have h0 := intervalIntegral.intervalIntegral_pos_of_pos_on hi
    (fun v hv => wScaleDens_pos hv.1) hw
  linarith

theorem tendsto_wScale_one (hκ : 4 < κ) :
    Tendsto (wScale κ) (𝓝[>] 1) (𝓝 (wScale κ 1)) := by
  have hc := intervalIntegral.continuousOn_primitive_interval'
    (intervalIntegrable_wScaleDens_one (κ := κ) hκ) (a := 2)
    (by rw [uIcc_of_le (by norm_num)]; exact ⟨by norm_num, le_rfl⟩)
  rw [uIcc_of_le (by norm_num)] at hc
  have h1 := (hc 1 ⟨le_rfl, by norm_num⟩).mono (Ioo_subset_Icc_self (a := (1 : ℝ)) (b := 2))
  rw [ContinuousWithinAt, nhdsWithin_Ioo_eq_nhdsGT (by norm_num : (1 : ℝ) < 2)] at h1
  exact h1

/-- **The scale function is bounded at `∞`** (`κ < 8`): `Ψ(w) ≤ 2^{4/κ} 2^{1−8/κ}/(8/κ − 1)`. -/
theorem wScale_le (hκ : 4 < κ) (hκ8 : κ < 8) {w : ℝ} (hw : 1 ≤ w) :
    wScale κ w ≤ 2 ^ (4 / κ) * 2 ^ (1 - 8 / κ) / (8 / κ - 1) := by
  have hκ0 : 0 < κ := by linarith
  have h81 : 0 < 8 / κ - 1 := by
    have : 1 < 8 / κ := (one_lt_div hκ0).2 hκ8
    linarith
  have hB : 0 ≤ 2 ^ (4 / κ) * 2 ^ (1 - 8 / κ) / (8 / κ - 1) := by positivity
  rcases le_or_gt w 2 with h2 | h2
  · have : wScale κ w ≤ 0 := by
      have e : wScale κ w = -∫ v in w..(2 : ℝ), wScaleDens κ v := intervalIntegral.integral_symm _ _
      rw [e, neg_nonpos]
      exact intervalIntegral.integral_nonneg h2 fun v hv => wScaleDens_nonneg (hw.trans hv.1)
    linarith
  · have hle : ∀ v ∈ Icc (2 : ℝ) w, wScaleDens κ v ≤ 2 ^ (4 / κ) * v ^ (-(8 / κ)) := by
      intro v hv
      have hv2 : (2 : ℝ) ≤ v := hv.1
      have hpos : 0 < v ^ 2 / 2 := by positivity
      have hle1 : v ^ 2 / 2 ≤ v ^ 2 - v := by nlinarith
      calc wScaleDens κ v = (v ^ 2 - v) ^ (-(4 / κ)) := rfl
        _ ≤ (v ^ 2 / 2) ^ (-(4 / κ)) :=
          Real.rpow_le_rpow_of_nonpos hpos hle1 (by have := div_pos four_pos hκ0; linarith)
        _ = 2 ^ (4 / κ) * v ^ (-(8 / κ)) := by
          rw [Real.div_rpow (by positivity) zero_le_two, ← Real.rpow_natCast,
            ← Real.rpow_mul (by linarith), Real.rpow_neg zero_le_two]
          field_simp
          ring_nf
    have hint := intervalIntegral.integral_mono_on h2.le (intervalIntegrable_wScaleDens
      (by norm_num) (by linarith)) ((continuousOn_const.mul (fun v hv =>
        (Real.continuousAt_rpow_const _ _ (Or.inl (by
          rw [uIcc_of_le h2.le] at hv; linarith [hv.1]))).continuousWithinAt)).intervalIntegrable)
      hle
    have hcomp : ∫ v in (2 : ℝ)..w, 2 ^ (4 / κ) * v ^ (-(8 / κ)) =
        2 ^ (4 / κ) * ((w ^ (-(8 / κ) + 1) - 2 ^ (-(8 / κ) + 1)) / (-(8 / κ) + 1)) := by
      rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inr ⟨by linarith, by
        rw [uIcc_of_le h2.le]; intro h; linarith [h.1]⟩)]
    calc wScale κ w ≤ _ := hint
      _ = 2 ^ (4 / κ) * ((w ^ (-(8 / κ) + 1) - 2 ^ (-(8 / κ) + 1)) / (-(8 / κ) + 1)) := hcomp
      _ ≤ 2 ^ (4 / κ) * 2 ^ (1 - 8 / κ) / (8 / κ - 1) := by
        rw [show -(8 / κ) + 1 = -(8 / κ - 1) by ring, div_neg,
          show 1 - 8 / κ = -(8 / κ - 1) by ring,
          mul_div_assoc]
        gcongr
        have hw0 : 0 ≤ w ^ (-(8 / κ - 1)) := Real.rpow_nonneg (by linarith) _
        rw [← neg_div, neg_sub, div_le_div_iff_of_pos_right h81]
        linarith

end Scale

/-! ### The two-point harmonic function -/

section TwoPoint

variable {κ : ℝ}

/-- The domain `0 < X < Y` of two ordered positive real flows. -/
def twoPointDom : Set (ℝ × ℝ) := {q | 0 < q.1 ∧ q.1 < q.2}

/-- **The two-point harmonic function** `F(X, Y) = Ψ(Y/(Y − X))`. -/
def twoPointF (κ : ℝ) (q : ℝ × ℝ) : ℝ := wScale κ (q.2 / (q.2 - q.1))

/-- The tamed two-point drift `(2/max(X, c), 2/max(Y, c))`. -/
def twoPointDrift (c : ℝ) (q : ℝ × ℝ) : ℝ × ℝ := (realDrift c q.1, realDrift c q.2)

theorem isOpen_twoPointDom : IsOpen twoPointDom :=
  (isOpen_lt continuous_const continuous_fst).inter (isOpen_lt continuous_fst continuous_snd)

theorem one_lt_div_of_mem_twoPointDom {q : ℝ × ℝ} (hq : q ∈ twoPointDom) :
    1 < q.2 / (q.2 - q.1) := by
  rw [one_lt_div (by linarith [hq.2])]; linarith [hq.1]

theorem contDiffOn_twoPointF : ContDiffOn ℝ 3 (twoPointF κ) twoPointDom := by
  have hg : ContDiffOn ℝ 3 (fun q : ℝ × ℝ => q.2 / (q.2 - q.1)) twoPointDom :=
    contDiffOn_snd.div (contDiffOn_snd.sub contDiffOn_fst) fun q hq => by
      have := hq.2; exact (sub_pos.2 this).ne'
  exact contDiffOn_wScale.comp hg fun q hq => one_lt_div_of_mem_twoPointDom hq

theorem lipschitzWith_twoPointDrift {c : ℝ} (hc : 0 < c) :
    LipschitzWith (Real.toNNReal (2 / c ^ 2)) (twoPointDrift c) :=
  LipschitzWith.prodMk ((lipschitz_realDrift hc).comp LipschitzWith.prod_fst)
    ((lipschitz_realDrift hc).comp LipschitzWith.prod_snd) |>.weaken (by simp)

theorem norm_twoPointDrift_le {c : ℝ} (hc : 0 < c) (q : ℝ × ℝ) :
    ‖twoPointDrift c q‖ ≤ 2 / c := by
  rw [Prod.norm_def, max_le_iff, Real.norm_eq_abs, Real.norm_eq_abs]
  exact ⟨abs_realDrift_le hc _, abs_realDrift_le hc _⟩

/-- **`F` is harmonic for the two-point generator** (`dX = 2/X dt − √κ dB`,
`dY = 2/Y dt − √κ dB`, same `B`): along the noise direction `w = Y/(Y − X)` moves affinely, and
`Ψ'' = −(4/κ)(2w − 1)Ψ'/(w² − w)` cancels the drift `(4w − 2)Ψ'/(w(w − 1))`. -/
theorem dynkinGen_twoPointF (hκ : 0 < κ) {c s : ℝ} (hs : s * s = κ) {q : ℝ × ℝ}
    (hq : q ∈ twoPointDom) (hcq : c ≤ q.1) :
    dynkinGen (twoPointDrift c) (-s, -s) (twoPointF κ) q = 0 := by
  obtain ⟨a, b⟩ := q
  obtain ⟨ha, hab⟩ := hq
  simp only at ha hab hcq
  have hb : 0 < b := ha.trans hab
  have hba : 0 < b - a := sub_pos.2 hab
  have hd : ContDiffAt ℝ 3 (twoPointF κ) (a, b) :=
    contDiffOn_twoPointF.contDiffAt (isOpen_twoPointDom.mem_nhds ⟨ha, hab⟩)
  set w := b / (b - a) with hwdef
  have hw : 1 < w := one_lt_div_of_mem_twoPointDom (q := (a, b)) ⟨ha, hab⟩
  have hdrift : twoPointDrift c (a, b) = (2 / a, 2 / b) := by
    simp only [twoPointDrift]
    rw [realDrift_of_le hcq, realDrift_of_le (hcq.trans hab.le)]
  rw [dynkinGen, hdrift, FrozenMart.fderiv_apply_eq_deriv_line (hd.differentiableAt (by simp)),
    FrozenMart.iteratedFDeriv_two_eq_deriv_deriv_line (hd.of_le (by norm_num))]
  -- first order term
  set g : ℝ → ℝ := fun r => (b + r * (2 / b)) / ((b + r * (2 / b)) - (a + r * (2 / a))) with hgdef
  have hline1 : (fun r : ℝ => twoPointF κ ((a, b) + r • (2 / a, 2 / b))) =
      fun r => wScale κ (g r) := by
    funext r; simp [twoPointF, hgdef]
  have hg0 : g 0 = w := by simp [hgdef, hwdef]
  have hg : HasDerivAt g (((2 / b) * (b - a) - b * (2 / b - 2 / a)) / (b - a) ^ 2) 0 := by
    have hc1 : HasDerivAt (fun r : ℝ => b + r * (2 / b)) (2 / b) 0 := by
      simpa using ((hasDerivAt_id' (0 : ℝ)).mul_const (2 / b)).const_add b
    have hc2 : HasDerivAt (fun r : ℝ => a + r * (2 / a)) (2 / a) 0 := by
      simpa using ((hasDerivAt_id' (0 : ℝ)).mul_const (2 / a)).const_add a
    have h := hc1.div (hc1.sub hc2) (by simp; exact hba.ne')
    refine h.congr_deriv ?_
    simp
  have hfirst : deriv (fun r : ℝ => wScale κ (g r)) 0 =
      wScaleDens κ w * (((2 / b) * (b - a) - b * (2 / b - 2 / a)) / (b - a) ^ 2) := by
    have h := (hasDerivAt_wScale (κ := κ) (hg0 ▸ hw)).comp 0 hg
    rw [hg0] at h
    exact h.deriv
  -- second order term
  set h : ℝ → ℝ := fun r => w - r * (s / (b - a)) with hhdef
  have hline2 : (fun r : ℝ => twoPointF κ ((a, b) + r • (-s, -s))) = fun r => wScale κ (h r) := by
    funext r
    simp only [twoPointF, hhdef, Prod.smul_mk, smul_eq_mul, Prod.mk_add_mk]
    congr 1
    have e : b + r * -s - (a + r * -s) = b - a := by ring
    rw [e, hwdef]
    field_simp
    ring
  have hh0 : h 0 = w := by simp [hhdef]
  have hhc : ContDiffAt ℝ 2 h 0 := by fun_prop
  have hΨc : ContDiffAt ℝ 2 (wScale κ) (h 0) := by
    rw [hh0]
    exact (contDiffOn_wScale.contDiffAt (Ioi_mem_nhds hw)).of_le (by norm_num)
  have hsecond := RS.deriv_deriv_comp_zero hΨc hhc
  have hdh : deriv h = fun _ => -(s / (b - a)) := by
    funext r
    have : HasDerivAt h (-(s / (b - a))) r := by
      simpa using ((hasDerivAt_id' r).mul_const (s / (b - a))).const_sub w
    exact this.deriv
  have hddh : deriv (deriv h) 0 = 0 := by rw [hdh]; simp
  have hdΨ : deriv (wScale κ) w = wScaleDens κ w := (hasDerivAt_wScale hw).deriv
  have hddΨ : deriv (deriv (wScale κ)) w =
      (2 * w - 1) * -(4 / κ) * (w ^ 2 - w) ^ (-(4 / κ) - 1) := by
    rw [(deriv_wScale_eventuallyEq hw).deriv_eq]
    exact (hasDerivAt_wScaleDens hw).deriv
  rw [hline1, hfirst, hline2, hsecond, hh0, hddh, hdΨ, hddΨ, hdh]
  have hww : w ^ 2 - w ≠ 0 := by nlinarith
  rw [Real.rpow_sub_one hww]
  simp only [wScaleDens]
  set P := (w ^ 2 - w) ^ (-(4 / κ)) with hPdef
  have hw1 : w - 1 = a / (b - a) := by rw [hwdef]; field_simp; ring
  have hwsq : w ^ 2 - w = a * b / (b - a) ^ 2 := by
    rw [show w ^ 2 - w = w * (w - 1) by ring, hw1, hwdef]; field_simp
  have h2w : 2 * w - 1 = (b + a) / (b - a) := by rw [hwdef]; field_simp; ring
  rw [hwsq, h2w]
  have hs2 : s ^ 2 = κ := by rw [sq]; exact hs
  field_simp
  rw [hs2]
  ring

theorem monotoneOn_wScale : MonotoneOn (wScale κ) (Ioi 1) :=
  monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioi 1)
    (fun _ hw => (hasDerivAt_wScale hw).continuousAt.continuousWithinAt)
    (fun _ hw => (hasDerivAt_wScale (interior_subset hw)).hasDerivWithinAt)
    (fun _ hw => (wScaleDens_pos (interior_subset hw)).le)

/-- Bounds of the two-point function on its domain. -/
theorem twoPointF_mem_Icc (hκ : 4 < κ) (hκ8 : κ < 8) {q : ℝ × ℝ} (hq : q ∈ twoPointDom) :
    twoPointF κ q ∈ Icc (wScale κ 1) (2 ^ (4 / κ) * 2 ^ (1 - 8 / κ) / (8 / κ - 1)) := by
  have hw := one_lt_div_of_mem_twoPointDom hq
  exact ⟨wScale_one_le hκ hw.le, wScale_le hκ hκ8 hw.le⟩

end TwoPoint

/-! ### Helpers -/

/-- A continuous path that stays in a closed set before `t` is in it at `t`. -/
theorem mem_of_forall_lt_of_isClosed {E : Type*} [TopologicalSpace E] {X : ℝ≥0 → E} {K : Set E}
    (hK : IsClosed K) (hc : Continuous X) {t : ℝ≥0} (h0 : X 0 ∈ K) (hlt : ∀ s < t, X s ∈ K) :
    X t ∈ K := by
  rcases eq_or_ne t 0 with h0' | hne
  · rw [h0']; exact h0
  have hsub : Ico 0 t ⊆ {r | X r ∈ K} := fun r hr => hlt r hr.2
  have hcl := closure_minimal hsub (hK.preimage hc)
  have : t ∈ closure (Ico 0 t) := by
    rw [closure_Ico (Ne.symm hne)]; exact ⟨zero_le, le_rfl⟩
  exact hcl this

/-- The interval integral of a pair of continuous functions. -/
theorem intervalIntegral_prodMk {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) (a b : ℝ) :
    (∫ r in a..b, (f r, g r)) = (∫ r in a..b, f r, ∫ r in a..b, g r) := by
  have hfg : IntervalIntegrable (fun r => (f r, g r)) volume a b :=
    (hf.prodMk hg).intervalIntegrable a b
  refine Prod.ext ?_ ?_
  · exact ((ContinuousLinearMap.fst ℝ ℝ ℝ).intervalIntegral_comp_comm hfg).symm
  · exact ((ContinuousLinearMap.snd ℝ ℝ ℝ).intervalIntegral_comp_comm hfg).symm

/-- The natural filtration of `B` is contained in the σ-algebra of the whole path. -/
theorem bmFilt_le_comap {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ}
    (hBm : ∀ r, Measurable (B r)) (t : ℝ≥0) :
    NonSwallow.bmFilt hBm t ≤
      MeasurableSpace.comap (fun ω (r : ℝ≥0) => B r ω) MeasurableSpace.pi := by
  refine (NonSwallow.bmFilt_le_past hBm t).trans ?_
  intro A hA
  obtain ⟨S, hS, rfl⟩ := hA
  have hmeas : Measurable (fun (f : ℝ≥0 → ℝ) (r : Set.Iic t) => f r) :=
    measurable_pi_iff.2 fun r => measurable_pi_apply (r : ℝ≥0)
  exact ⟨_, hmeas hS, rfl⟩

/-! ### Swallowing an interval at once -/

/-- The stopping region at level `L`: `X ≥ 1/L`, `Y ≤ L`, `Y/(Y − X) ≤ L`. -/
def twoPointK (L : ℝ) : Set (ℝ × ℝ) := {q | 1 / L ≤ q.1 ∧ q.2 ≤ L ∧ q.2 ≤ L * (q.2 - q.1)}

/-- The exit set at level `L`. -/
def twoPointCl (L : ℝ) : Set (ℝ × ℝ) :=
  {q | q.1 ≤ 1 / L} ∪ {q | L ≤ q.2} ∪ {q | L * (q.2 - q.1) ≤ q.2}

theorem isClosed_twoPointK (L : ℝ) : IsClosed (twoPointK L) :=
  (isClosed_le continuous_const continuous_fst).inter ((isClosed_le continuous_snd
    continuous_const).inter (isClosed_le continuous_snd
      (continuous_const.mul (continuous_snd.sub continuous_fst))))

theorem isClosed_twoPointCl (L : ℝ) : IsClosed (twoPointCl L) :=
  ((isClosed_le continuous_fst continuous_const).union (isClosed_le continuous_const
    continuous_snd)).union (isClosed_le (continuous_const.mul (continuous_snd.sub continuous_fst))
      continuous_snd)

theorem compl_twoPointCl_subset (L : ℝ) : (twoPointCl L)ᶜ ⊆ twoPointK L := by
  intro q hq
  simp only [twoPointCl, mem_compl_iff, mem_union, mem_ofPred_eq, not_or, not_le] at hq
  exact ⟨hq.1.1.le, hq.1.2.le, hq.2.le⟩

theorem twoPointK_subset {L : ℝ} (hL : 1 < L) : twoPointK L ⊆ twoPointDom := by
  intro q hq
  obtain ⟨h1, h2, h3⟩ := hq
  have hq1 : 0 < q.1 := lt_of_lt_of_le (by positivity) h1
  refine ⟨hq1, ?_⟩
  by_contra h
  push Not at h
  nlinarith

/-- **Pathwise identification of the stopped two-point value.** Let `x` be swallowed at `σ`,
`y > x` alive on `[0, σ]` (solution `wy`), and let the level `L` exceed `Y` and `Y/(Y − X)` on
`[0, σ)`. Then the tamed two-point path at level `c ≤ 1/L` first leaves the region at a time
`τ < σ` with `X_τ = 1/L` and `Y_τ = Re wy(τ)`. -/
theorem stopped_twoPoint_eq {Ω : Type*} {W : ℝ → ℝ} (hW : Continuous W)
    {x y σ L c : ℝ} (hσ : RealSwallowAt W x σ) {wy : ℝ → ℂ}
    (hwy : IsForwardSol W (y : ℂ) σ wy) (hL : 1 < L) (hc : 0 < c) (hcL : c ≤ 1 / L)
    {T : ℝ≥0} (hσT : σ < T) (hYL : ∀ t ∈ Icc (0 : ℝ) σ, (wy t).re < L)
    (hDL : ∀ t ∈ Ico (0 : ℝ) σ, (wy t).re < L * ((wy t).re - (fwdMap W t x).re))
    {V : ℝ≥0 → Ω → ℝ × ℝ} {ω : Ω} (hV : ∀ t : ℝ≥0, V t ω = (realTamed W c x t, realTamed W c y t))
    (hVc : Continuous fun t => V t ω) (hV0 : V 0 ω ∈ twoPointK L) :
    ((hittingBtwn V (twoPointCl L) 0 T ω : ℝ≥0) : ℝ) < σ ∧
      (V (hittingBtwn V (twoPointCl L) 0 T ω) ω).1 = 1 / L ∧
      (V (hittingBtwn V (twoPointCl L) 0 T ω) ω).2 =
        (wy ((hittingBtwn V (twoPointCl L) 0 T ω : ℝ≥0) : ℝ)).re := by
  set τ := hittingBtwn V (twoPointCl L) 0 T ω with hτdef
  have hσ0 := hσ.1
  have hK : ∀ t ≤ τ, V t ω ∈ twoPointK L := by
    intro t ht
    refine mem_of_forall_lt_of_isClosed (isClosed_twoPointK L) hVc hV0 fun r hr => ?_
    exact compl_twoPointCl_subset L (notMem_of_lt_hittingBtwn (hr.trans_le ht) zero_le)
  have hge : ∀ t : ℝ, t ∈ Icc (0 : ℝ) τ → 1 / L ≤ realTamed W c x t ∧
      realTamed W c x t < realTamed W c y t := by
    intro t ht
    have h := hK t.toNNReal ((Real.toNNReal_le_iff_le_coe).2 ht.2)
    rw [hV, Real.coe_toNNReal _ ht.1] at h
    have hdom := twoPointK_subset hL h
    exact ⟨h.1, hdom.2⟩
  have hsolx : IsForwardSol W (x : ℂ) τ (fun t => (realTamed W c x t : ℂ)) :=
    isForwardSol_realTamed hW hc τ.coe_nonneg fun t ht => hcL.trans (hge t ht).1
  have hsoly : IsForwardSol W (y : ℂ) τ (fun t => (realTamed W c y t : ℂ)) :=
    isForwardSol_realTamed hW hc τ.coe_nonneg fun t ht =>
      (hcL.trans (hge t ht).1).trans (hge t ht).2.le
  have hτσ : (τ : ℝ) < σ := by
    by_contra h
    push Not at h
    exact hσ.2.2 ⟨_, isForwardSol_restrict hsolx hσ0.le h⟩
  have hτmem : (τ : ℝ) ∈ Icc (0 : ℝ) τ := ⟨τ.coe_nonneg, le_rfl⟩
  have hYτ : realTamed W c y τ = (wy τ).re := by
    have h1 := fwdMap_eq_of_isForwardSol hW hsoly hτmem
    have h2 := fwdMap_eq_of_isForwardSol hW hwy ⟨τ.coe_nonneg, hτσ.le⟩
    rw [h1] at h2
    have := congrArg Complex.re h2
    simpa using this
  have hXτ : realTamed W c x τ = (fwdMap W τ x).re := by
    rw [fwdMap_eq_of_isForwardSol hW hsolx hτmem]; simp
  have hex : ∃ j ∈ Icc (0 : ℝ≥0) T, V j ω ∈ twoPointCl L := by
    by_contra hne
    push Not at hne
    have hgeT : ∀ t ∈ Icc (0 : ℝ) T, c ≤ realTamed W c x t := by
      intro t ht
      have h := compl_twoPointCl_subset L (hne t.toNNReal ⟨zero_le,
        (Real.toNNReal_le_iff_le_coe).2 ht.2⟩)
      rw [hV, Real.coe_toNNReal _ ht.1] at h
      exact hcL.trans h.1
    exact hσ.2.2 ⟨_, isForwardSol_restrict (isForwardSol_realTamed hW hc T.coe_nonneg hgeT)
      hσ0.le hσT.le⟩
  have hmem := hittingBtwn_mem_of_isClosed' (isClosed_twoPointCl L) hVc hex
  rw [← hτdef, hV] at hmem
  have hKτ := hK τ le_rfl
  rw [hV] at hKτ
  refine ⟨hτσ, ?_, ?_⟩
  · rw [hV]
    rcases hmem with (h | h) | h
    · exact le_antisymm h hKτ.1
    · exfalso
      have := hYL τ ⟨τ.coe_nonneg, hτσ.le⟩
      simp only [mem_ofPred_eq] at h
      linarith
    · exfalso
      have := hDL τ ⟨τ.coe_nonneg, hτσ⟩
      simp only [mem_ofPred_eq] at h
      rw [hXτ, hYτ] at h
      linarith
  · rw [hV]; exact hYτ

/-- If `x` is swallowed at `σ` while `y > x` is still alive at `σ`, the gap `Y − X` stays
bounded below on `[0, σ)` (it tends to `Y_σ > 0`). -/
theorem exists_pos_le_sub_of_alive {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {x y σ : ℝ}
    (hx : 0 < x) (hxy : x < y) (hσ : RealSwallowAt W x σ) {wy : ℝ → ℂ}
    (hwy : IsForwardSol W (y : ℂ) σ wy) :
    ∃ d > 0, ∀ t ∈ Ico (0 : ℝ) σ, d ≤ (wy t).re - (fwdMap W t x).re := by
  have hσ0 := hσ.1
  obtain ⟨m, hm, hmle⟩ := exists_pos_le_re_of_isForwardSol hW hW0 (hx.trans hxy) hσ0.le hwy
  have hlim := tendsto_fwdMap_of_realSwallowAt hW hW0 hx hσ
  have hev : ∀ᶠ t in 𝓝[<] σ, ‖fwdMap W t x‖ < m / 2 :=
    hlim.norm.eventually (gt_mem_nhds (by simpa using half_pos hm))
  obtain ⟨σ₁, hσ₁, hsub⟩ := (mem_nhdsLT_iff_exists_Ioo_subset).1 hev
  set σ₂ := max σ₁ 0 with hσ₂def
  have hσ₂ : σ₂ < σ := max_lt hσ₁ hσ0
  obtain ⟨v, hv⟩ := hσ.2.1 σ₂ ⟨le_max_right _ _, hσ₂⟩
  have hwy₂ : IsForwardSol W (y : ℂ) σ₂ wy := isForwardSol_restrict hwy (le_max_right _ _) hσ₂.le
  have hlt := re_lt_of_isForwardSol hW hW0 hx hxy hv hwy₂
  obtain ⟨t₀, ht₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 (le_max_right σ₁ 0))
    ((Complex.continuous_re.comp_continuousOn hwy₂.1).sub
      (Complex.continuous_re.comp_continuousOn hv.1))
  set d₁ := (wy t₀).re - (v t₀).re with hd₁
  have hd₁pos : 0 < d₁ := by have := hlt t₀ ht₀; simp only [hd₁]; linarith
  refine ⟨min d₁ (m / 2), lt_min hd₁pos (half_pos hm), fun t ht => ?_⟩
  rcases le_or_gt t σ₂ with h | h
  · have htm : t ∈ Icc 0 σ₂ := ⟨ht.1, h⟩
    rw [fwdMap_eq_of_isForwardSol hW hv htm]
    exact (min_le_left _ _).trans (hmin htm)
  · have h1 := hsub ⟨(le_max_left σ₁ 0).trans_lt h, ht.2⟩
    have h2 := Complex.re_le_norm (fwdMap W t x)
    have h3 := hmle t ⟨ht.1, ht.2.le⟩
    simp only [mem_ofPred_eq] at h1
    linarith [min_le_right d₁ (m / 2)]

section AtOnce

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- **An interval is swallowed at once with positive probability** ([RS05] Lemma 6.6; [Law]
Prop. 6.8, fourth item, from Prop. 1.21). For `4 < κ < 8` and `0 < x < y` there is an event `E`,
measurable for the σ-algebra of the driving Brownian path, with `P(E) > 0`, on which (almost
surely) `x` and `y` are swallowed at the same time.

Proof: `F(X, Y) = Ψ(Y/(Y − X))` is harmonic for the two-point process (`dynkinGen_twoPointF`) and
bounded between `Ψ(1)` and `L₁` (`κ < 8`). QuantumZipper's local Dynkin formula, stopped on leaving
`{X ≥ 1/L, Y ≤ L, Y/(Y − X) ≤ L}`, gives `E g_L = F(x, y) > Ψ(1)` for the stopped values `g_L`. If
`x` is swallowed at `σ` (a.s., `ae_exists_realSwallowAt`) but `y` is not, then `g_L → Ψ(1)`
(`stopped_twoPoint_eq`); dominated convergence on the event where `g_L → Ψ(1)` bounds the
probability of the complement below by `(F(x, y) − Ψ(1))/(L₁ − Ψ(1))`. -/
theorem exists_measurableSet_realSwallowAt_pair (hB : IsBrownianReal B P)
    (hBm : ∀ r, Measurable (B r)) (hBc : ∀ ω, Continuous (B · ω)) (hB0 : ∀ ω, B 0 ω = 0)
    {κ : ℝ} (hκ : 4 < κ) (hκ8 : κ < 8) {x y : ℝ} (hx : 0 < x) (hxy : x < y) :
    ∃ E : Set Ω,
      MeasurableSet[MeasurableSpace.comap (fun ω (r : ℝ≥0) => B r ω) MeasurableSpace.pi] E ∧
      0 < P E ∧ ∀ᵐ ω ∂P, ω ∈ E →
        ∃ σ, RealSwallowAt (drive κ B ω) x σ ∧ RealSwallowAt (drive κ B ω) y σ := by
  have hP : IsProbabilityMeasure P := hB.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  have hκ0 : 0 < κ := by linarith
  set s := √κ with hsdef
  have hs : s * s = κ := Real.mul_self_sqrt hκ0.le
  have hmB : MeasurableSpace.comap (fun ω (r : ℝ≥0) => B r ω) MeasurableSpace.pi ≤ mΩ :=
    (measurable_pi_iff.2 hBm).comap_le
  set L₀ := wScale κ 1 with hL₀
  set L₁ := 2 ^ (4 / κ) * 2 ^ (1 - 8 / κ) / (8 / κ - 1) with hL₁
  have hyx : 0 < y - x := sub_pos.2 hxy
  set A₀ := max (1 / x) (max y (y / (y - x))) with hA₀
  set lev : ℕ → ℝ := fun n => (⌈A₀⌉₊ : ℝ) + 2 + n with hlev
  have hlevA : ∀ n, A₀ + 2 ≤ lev n := fun n => by
    simp only [hlev]; linarith [Nat.le_ceil A₀, (n.cast_nonneg : (0 : ℝ) ≤ n)]
  have hA₀pos : 0 ≤ A₀ := (le_max_left _ _).trans' (by positivity)
  have hlev1 : ∀ n, 1 < lev n := fun n => by linarith [hlevA n]
  have hlevpos : ∀ n, 0 < lev n := fun n => by linarith [hlev1 n]
  set c : ℕ → ℝ := fun n => 1 / (2 * lev n) with hcdef
  have hc : ∀ n, 0 < c n := fun n => by have := hlevpos n; positivity
  have hcL : ∀ n, c n ≤ 1 / lev n := fun n => by
    have := hlevpos n
    simp only [hcdef]
    rw [div_le_div_iff₀ (by positivity) this]; linarith
  set T : ℕ → ℝ≥0 := fun n => (lev n).toNNReal with hTdef
  have hTlev : ∀ n, (T n : ℝ) = lev n := fun n => Real.coe_toNNReal _ (hlevpos n).le
  set U : ℕ → ℝ≥0 → Ω → ℝ × ℝ := fun n t ω =>
    (realTamed (sDrive s B ω) (c n) x t, realTamed (sDrive s B ω) (c n) y t) with hUdef
  have hcont1 : ∀ n ω (z : ℝ), Continuous fun r : ℝ =>
      realDrift (c n) (realTamed (sDrive s B ω) (c n) z (r.toNNReal : ℝ)) := by
    intro n ω z
    have h1 := (lipschitz_realDrift (hc n)).continuous
    have h2 : Continuous fun r : ℝ => realTamed (sDrive s B ω) (c n) z (r.toNNReal : ℝ) :=
      (Dynkin.continuous_of_integralEq hBc h1
        (fun y => by rw [Real.norm_eq_abs]; exact abs_realDrift_le (hc n) y)
        (fun ω t => realTamed_sDrive_eq hBc s (hc n) z ω t) ω).comp continuous_real_toNNReal
    exact h1.comp h2
  have hUeq : ∀ n ω (t : ℝ≥0), U n t ω = (x, y) +
      (∫ r in (0 : ℝ)..t, twoPointDrift (c n) (U n r.toNNReal ω)) + B t ω • ((-s, -s) : ℝ × ℝ) := by
    intro n ω t
    have hI := intervalIntegral_prodMk (hcont1 n ω x) (hcont1 n ω y) 0 t
    simp only [hUdef, twoPointDrift]
    rw [hI, realTamed_sDrive_eq hBc s (hc n) x ω t, realTamed_sDrive_eq hBc s (hc n) y ω t]
    simp only [Prod.mk_add_mk, Prod.smul_mk, smul_eq_mul]
  have hUc : ∀ n ω, Continuous (U n · ω) := fun n =>
    Dynkin.continuous_of_integralEq hBc (lipschitzWith_twoPointDrift (hc n)).continuous
      (norm_twoPointDrift_le (hc n)) (hUeq n)
  have hU0 : ∀ n ω, U n 0 ω = (x, y) := fun n ω => by rw [hUeq n ω 0]; simp [hB0 ω]
  have hxyK : ∀ n, (x, y) ∈ twoPointK (lev n) := by
    intro n
    have hA := hlevA n
    refine ⟨?_, ?_, ?_⟩
    · show 1 / lev n ≤ x
      rw [div_le_iff₀ (hlevpos n)]
      have : 1 / x ≤ lev n := by linarith [le_max_left (1 / x) (max y (y / (y - x)))]
      rw [div_le_iff₀ hx] at this
      linarith
    · show y ≤ lev n
      linarith [le_max_left y (y / (y - x)), le_max_right (1 / x) (max y (y / (y - x)))]
    · show y ≤ lev n * (y - x)
      have : y / (y - x) ≤ lev n := by
        linarith [le_max_right y (y / (y - x)), le_max_right (1 / x) (max y (y / (y - x)))]
      rwa [div_le_iff₀ hyx] at this
  set Cl : ℕ → Set (ℝ × ℝ) := fun n => twoPointCl (lev n) with hCldef
  set K : ℕ → Set (ℝ × ℝ) := fun n => twoPointK (lev n) with hKdef
  have hUK : ∀ n ω (t : ℝ≥0), t ≤ T n → (∀ r < t, U n r ω ∉ Cl n) → U n t ω ∈ K n :=
    fun n ω t _ ht => mem_of_forall_lt_of_isClosed (isClosed_twoPointK _) (hUc n ω)
      (by rw [hU0]; exact hxyK n) fun r hr => compl_twoPointCl_subset _ (ht r hr)
  set Mb := max |L₀| |L₁| with hMb
  have hFbd : ∀ q ∈ twoPointDom, |twoPointF κ q| ≤ Mb := fun q hq => by
    have h := twoPointF_mem_Icc hκ hκ8 hq
    exact abs_le_max_abs_abs h.1 h.2
  have hmart : ∀ n, Martingale (fun t ω => twoPointF κ (U n (min t
      (hittingBtwn (U n) (Cl n) 0 (T n) ω)) ω)) (NonSwallow.bmFilt hBm) P := fun n =>
    FrozenMart.martingale_localDynkin_stopped hB.toIsPreBrownianReal hBc (NonSwallow.bmFilt hBm)
      (NonSwallow.bmFilt_adapted hBm) (NonSwallow.bmFilt_le_past hBm)
      (lipschitzWith_twoPointDrift (hc n)) (norm_twoPointDrift_le (hc n)) (hUeq n)
      isOpen_twoPointDom (isClosed_twoPointCl _) (isClosed_twoPointK _)
      (twoPointK_subset (hlev1 n)) contDiffOn_twoPointF
      (fun q hq _ => dynkinGen_twoPointF hκ0 hs (twoPointK_subset (hlev1 n) hq)
        ((hcL n).trans hq.1))
      (T n) (hUK n) fun q hq => hFbd q (twoPointK_subset (hlev1 n) hq)
  set τ : ℕ → Ω → ℝ≥0 := fun n => hittingBtwn (U n) (Cl n) 0 (T n) with hτdef
  set g : ℕ → Ω → ℝ := fun n ω => twoPointF κ (U n (min (T n) (τ n ω)) ω) with hgdef
  have hgint : ∀ n, ∫ ω, g n ω ∂P = twoPointF κ (x, y) := by
    intro n
    have h := (hmart n).setIntegral_eq (zero_le : (0 : ℝ≥0) ≤ T n) MeasurableSet.univ
    simp only [setIntegral_univ] at h
    have hleft : ∫ ω, twoPointF κ (U n (min 0 (τ n ω)) ω) ∂P = twoPointF κ (x, y) := by
      have : ∀ ω, twoPointF κ (U n (min 0 (τ n ω)) ω) = twoPointF κ (x, y) := fun ω => by
        rw [min_eq_left zero_le, hU0]
      rw [integral_congr_ae (ae_of_all _ this)]
      simp
    rw [hleft] at h
    exact h.symm
  have hgK : ∀ n ω, U n (min (T n) (τ n ω)) ω ∈ K n := fun n ω => by
    rw [min_eq_right (hittingBtwn_le ω)]
    exact hUK n ω _ (hittingBtwn_le ω) fun q hq => notMem_of_lt_hittingBtwn hq zero_le
  have hgbd : ∀ n ω, g n ω ∈ Icc L₀ L₁ := fun n ω =>
    twoPointF_mem_Icc hκ hκ8 (twoPointK_subset (hlev1 n) (hgK n ω))
  have hgmeas : ∀ n, Measurable[MeasurableSpace.comap (fun ω (r : ℝ≥0) => B r ω)
      MeasurableSpace.pi] (g n) := fun n =>
    (((hmart n).1 (T n)).measurable).mono (bmFilt_le_comap hBm _) le_rfl
  set E : Set Ω := ⋃ k : ℕ, ⋂ N : ℕ, ⋃ n : ℕ, ⋃ (_ : N ≤ n),
    {ω | L₀ + 1 / ((k : ℝ) + 1) ≤ g n ω} with hEdef
  have hEm : MeasurableSet[MeasurableSpace.comap (fun ω (r : ℝ≥0) => B r ω)
      MeasurableSpace.pi] E :=
    MeasurableSet.iUnion fun k => MeasurableSet.iInter fun N => MeasurableSet.iUnion fun n =>
      MeasurableSet.iUnion fun _ => measurableSet_le measurable_const (hgmeas n)
  have hEm' : MeasurableSet E := hmB _ hEm
  have hEc : ∀ ω ∈ Eᶜ, Tendsto (fun n => g n ω) atTop (𝓝 L₀) := by
    intro ω hω
    have hω' : ∀ k : ℕ, ∃ N : ℕ, ∀ n, N ≤ n → g n ω < L₀ + 1 / ((k : ℝ) + 1) := by
      intro k
      by_contra hcon
      push Not at hcon
      exact hω (mem_iUnion.2 ⟨k, mem_iInter.2 fun N => by
        obtain ⟨n, hn, hgn⟩ := hcon N
        exact mem_iUnion₂.2 ⟨n, hn, hgn⟩⟩)
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
    obtain ⟨N, hN⟩ := hω' k
    refine ⟨N, fun n hn => ?_⟩
    have h1 := hN n hn
    have h2 := (hgbd n ω).1
    rw [Real.dist_eq, abs_of_nonneg (by linarith)]
    linarith
  -- the probability of `E`
  have hFxy : L₀ < twoPointF κ (x, y) :=
    wScale_one_lt hκ (one_lt_div_of_mem_twoPointDom (q := (x, y)) ⟨hx, hxy⟩)
  have hgi : ∀ n, Integrable (g n) P := fun n => (hmart n).integrable (T n) |>.congr
    (ae_of_all _ fun ω => rfl)
  have hlim : Tendsto (fun n => ∫ ω in Eᶜ, g n ω ∂P) atTop (𝓝 (∫ ω in Eᶜ, L₀ ∂P)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => Mb)
      (fun n => ((hgmeas n).mono hmB le_rfl).aestronglyMeasurable) (integrable_const _)
      (fun n => ae_of_all _ fun ω => ?_) (ae_restrict_of_forall_mem hEm'.compl hEc)
    rw [Real.norm_eq_abs]
    exact abs_le_max_abs_abs (hgbd n ω).1 (hgbd n ω).2
  have hle : ∀ n, twoPointF κ (x, y) ≤ L₁ * P.real E + ∫ ω in Eᶜ, g n ω ∂P := by
    intro n
    rw [← hgint n, ← integral_add_compl hEm' (hgi n)]
    gcongr
    calc ∫ ω in E, g n ω ∂P ≤ ∫ ω in E, L₁ ∂P :=
          setIntegral_mono (hgi n).integrableOn (integrable_const _) fun ω => (hgbd n ω).2
      _ = L₁ * P.real E := by rw [setIntegral_const, smul_eq_mul, mul_comm]
  have hfin : twoPointF κ (x, y) ≤ L₁ * P.real E + L₀ * P.real Eᶜ := by
    have h := ge_of_tendsto' (hlim.const_add (L₁ * P.real E)) hle
    rw [setIntegral_const, smul_eq_mul] at h
    linarith
  rw [probReal_compl_eq_one_sub hEm'] at hfin
  have hL₀₁ : L₀ ≤ L₁ := by
    have h := twoPointF_mem_Icc hκ hκ8 (q := (x, y)) ⟨hx, hxy⟩
    exact h.1.trans h.2
  have hpos : 0 < P.real E := by
    by_contra h
    push Not at h
    have h0 : P.real E = 0 := le_antisymm h measureReal_nonneg
    rw [h0] at hfin
    linarith
  have hPE : 0 < P E := by
    refine pos_iff_ne_zero.2 fun h => ?_
    rw [measureReal_def, h, ENNReal.toReal_zero] at hpos
    exact lt_irrefl _ hpos
  refine ⟨E, hEm, hPE, ?_⟩
  -- pathwise: on `E`, `y` is swallowed together with `x`
  filter_upwards [ae_exists_realSwallowAt hB hBm hBc hB0 hκ hx] with ω ⟨σ, hσ⟩ hωE
  refine ⟨σ, hσ, ?_⟩
  by_contra hny
  set W := drive κ B ω with hWdef
  have hW : Continuous W := drive_continuous (hBc ω)
  have hW0 : W 0 = 0 := by simp [hWdef, drive, hB0 ω]
  have hσ0 := hσ.1
  obtain ⟨wy, hwy⟩ : ∃ wy, IsForwardSol W (y : ℂ) σ wy := by
    by_contra h
    refine hny ⟨hσ0, fun t ht => ?_, h⟩
    obtain ⟨v, hv⟩ := hσ.2.1 t ht
    exact exists_isForwardSol_of_lt hW ht.1 (by rw [hW0]; exact hx) hxy hv
  obtain ⟨m, hm, hmle⟩ := exists_pos_le_re_of_isForwardSol hW hW0 (hx.trans hxy) hσ0.le hwy
  obtain ⟨MY, hMY⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (Complex.continuous_re.comp_continuousOn hwy.1)
  obtain ⟨d, hd, hdle⟩ := exists_pos_le_sub_of_alive hW hW0 hx hxy hσ hwy
  -- eventually the level exceeds all the bounds
  have hlevtop : Tendsto lev atTop atTop :=
    tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop
  have hev : ∀ᶠ n in atTop, max (max MY (MY / d)) (max σ (1 / m)) < lev n :=
    hlevtop.eventually (eventually_gt_atTop _)
  have hbnd : ∀ᶠ n in atTop, g n ω ≤ wScale κ (m / (m - 1 / lev n)) := by
    filter_upwards [hev] with n hn
    have h1 : MY < lev n := lt_of_le_of_lt ((le_max_left _ _).trans (le_max_left _ _)) hn
    have h2 : MY / d < lev n := lt_of_le_of_lt ((le_max_right _ _).trans (le_max_left _ _)) hn
    have h3 : σ < lev n := lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hn
    have h4 : 1 / m < lev n := lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) hn
    have hYL : ∀ t ∈ Icc (0 : ℝ) σ, (wy t).re < lev n := fun t ht => by
      have hY : |(wy t).re| ≤ MY := by simpa [Real.norm_eq_abs] using hMY t ht
      linarith [le_abs_self (wy t).re]
    have hDL : ∀ t ∈ Ico (0 : ℝ) σ, (wy t).re < lev n * ((wy t).re - (fwdMap W t x).re) := by
      intro t ht
      have hY : |(wy t).re| ≤ MY := by simpa [Real.norm_eq_abs] using hMY t ⟨ht.1, ht.2.le⟩
      have hdt := hdle t ht
      have : MY < lev n * d := by rwa [div_lt_iff₀ hd] at h2
      have hmul := mul_le_mul_of_nonneg_left hdt (hlevpos n).le
      linarith [le_abs_self (wy t).re]
    obtain ⟨hτσ, hX, hY⟩ := stopped_twoPoint_eq (Ω := Ω) (V := U n) (ω := ω) hW hσ hwy (hlev1 n)
      (hc n) (hcL n) (by rw [hTlev]; exact h3) hYL hDL (fun t => rfl) (hUc n ω)
      (by rw [hU0]; exact hxyK n)
    have hmin : min (T n) (τ n ω) = τ n ω := min_eq_right (hittingBtwn_le ω)
    simp only [hgdef, hmin, twoPointF]
    rw [hX, hY]
    set Yτ := (wy (τ n ω : ℝ)).re with hYτ
    have hYm : m ≤ Yτ := hmle _ ⟨(τ n ω).coe_nonneg, hτσ.le⟩
    have hε : 1 / lev n < m := by
      rw [div_lt_iff₀ (hlevpos n)]; rw [div_lt_iff₀ hm] at h4; linarith
    have hε0 : 0 < 1 / lev n := by have := hlevpos n; positivity
    refine monotoneOn_wScale ?_ ?_ ?_
    · show 1 < Yτ / (Yτ - 1 / lev n)
      rw [one_lt_div (by linarith)]; linarith
    · show 1 < m / (m - 1 / lev n)
      rw [one_lt_div (by linarith)]; linarith
    · rw [div_le_div_iff₀ (by linarith) (by linarith)]
      nlinarith
  have hbtend : Tendsto (fun n => wScale κ (m / (m - 1 / lev n))) atTop (𝓝 L₀) := by
    refine (tendsto_wScale_one hκ).comp (tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩)
    · have h1 : Tendsto (fun n => 1 / lev n) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop hlevtop
      have h2 := (tendsto_const_nhds (x := m)).div (tendsto_const_nhds.sub h1)
        (by rw [sub_zero]; exact hm.ne')
      rw [sub_zero, div_self hm.ne'] at h2
      exact h2
    · filter_upwards [hev] with n hn
      have h4 : 1 / m < lev n := lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) hn
      have hε : 1 / lev n < m := by
        rw [div_lt_iff₀ (hlevpos n)]; rw [div_lt_iff₀ hm] at h4; linarith
      have hε0 : 0 < 1 / lev n := by have := hlevpos n; positivity
      show 1 < m / (m - 1 / lev n)
      rw [one_lt_div (by linarith)]; linarith
  have hgt : Tendsto (fun n => g n ω) atTop (𝓝 L₀) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbtend
      (Eventually.of_forall fun n => (hgbd n ω).1) hbnd
  -- contradiction with `ω ∈ E`
  obtain ⟨k, hk⟩ := mem_iUnion.1 hωE
  have hev2 : ∀ᶠ n in atTop, g n ω < L₀ + 1 / ((k : ℝ) + 1) :=
    hgt.eventually (gt_mem_nhds (by have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
                                    linarith))
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev2
  obtain ⟨n, hn, hgn⟩ := mem_iUnion₂.1 (mem_iInter.1 hk N)
  have := hN n hn
  simp only [mem_ofPred_eq] at hgn
  linarith

end AtOnce

end InteractingSLE
