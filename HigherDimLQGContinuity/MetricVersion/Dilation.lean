import HigherDimLQGContinuity.MetricVersion.Nondeg
import HigherDimLQGContinuity.Norm.Scaling

/-!
# Metric-valued versions (packet E5): dyadic dilations and common barriers

Part C, `c:lem-opt-dilation` and `c:lem-opt-proper` ((5.12)–(5.13)). Under the unit pin, the dyadic dilation
`T_j g = g(2^j ·) - g_{2^j}(0)` (`recentre 1 (2^j) 0`) preserves `P = normLGFLaw d` (`map_dilationTwoPow`), and at every
rational positive subcritical `q`, almost surely for all `x, y` (`ae_version_dilationTwoPow`, from the exact scaling
`rho_scaling_of` and the version clause at `g` and at `T_j g`):

  `X(q)(g)(2^j x, 2^j y) = 2^{j ϕ(q)} e^{q g_{2^j}(0)} X(q)(T_j g)(x, y)`.

**Barrier** (`ae_barrier_version`): fix a rational window `J = [c, c'] ⊆ S_d` and put
`G_k = {g : X(q)(g)(∂B_1 × ∂B_2) ≥ 1/(k+1) for all rational q ∈ J}`; by `c:lem-opt-nondeg` and compactness,
`P(⋃_k G_k) = 1`. With `m = min_J ϕ > 0`, `ε = m log 2 / (2c')` and `Sm_j = {|g_{2^j}(0)| ≤ ε j}`, Chebyshev
(`Var g_{2^j}(0) ≤ j log 2 + K`) gives `P(Sm_jᶜ) → 0`, so `P(T_j⁻¹ G_k ∩ Sm_j)` is eventually `≥ P(G_k) - δ`, and the
reverse Fatou inequality (`mv_le_measure_limsup`) gives `P(T_j⁻¹ G_k ∩ Sm_j infinitely often) ≥ P(G_k) → 1`. On that
event, for those `j`, every rational `q ∈ J` has `X(q)(g)(∂B_{2^j} × ∂B_{2^{j+1}}) ≥ e^{j m log 2 / 2}/(k+1)`, and by
continuity every `ξ ∈ J` does.

Route changes (recorded in the handoff; same conclusion): the dilations `T_j` are applied directly (no iterates of
`T = T_1` and no telescoping of sphere averages), and Poincaré recurrence plus Borel–Cantelli are replaced by the
reverse Fatou inequality for the events `T_j⁻¹ G_k ∩ Sm_j` and Chebyshev's inequality.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric ProbabilityTheory
open scoped ENNReal NNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd)

variable {d : ℕ}

/-! ## The dyadic dilations -/

/-- The dyadic dilation `T_j g = g(2^j ·) - g_{2^j}(0)` (Part C `c:lem-opt-dilation`, applied at the scale `2^j`). -/
def dilationTwoPow (d : ℕ) (j : ℕ) : DistRd d → DistRd d :=
  recentre 1 ((2 : ℝ) ^ j) 0

theorem measurable_dilationTwoPow (j : ℕ) : Measurable (dilationTwoPow d j) :=
  measurable_recentre 1 _ 0

/-- `c:lem-opt-dilation`, the law: `T_j` preserves the normalized law. -/
theorem map_dilationTwoPow (hd : 2 ≤ d) (j : ℕ) :
    (normLGFLaw d).map (dilationTwoPow d j) = normLGFLaw d := by
  have h := recentre_law hd (s := 1) (s₀ := 1) one_pos one_pos (pow_pos two_pos j) (0 : Rd d)
  rwa [pinLaw_one hd] at h

theorem measurePreserving_dilationTwoPow (hd : 2 ≤ d) (j : ℕ) :
    MeasurePreserving (dilationTwoPow d j) (normLGFLaw d) (normLGFLaw d) :=
  ⟨measurable_dilationTwoPow j, map_dilationTwoPow hd j⟩

/-- **`c:lem-opt-dilation`**, the exact covariance at the rational parameters: almost surely, for all `j`, every
rational positive subcritical `q` and all `x, y`, `X(q)(g)(2^j x, 2^j y) = S_q(2^j) X(q)(T_j g)(x, y)` with
`S_q(2^j) = 2^{j ϕ(q)} e^{q g_{2^j}(0)}` (`scaleS`). -/
theorem ae_version_dilationTwoPow (hd : 3 ≤ d) {X : ℝ → DistRd d → C(Rd d × Rd d, ℝ)}
    (hX : PosVersionStmt d X) :
    ∀ᵐ g ∂(normLGFLaw d), ∀ j : ℕ, ∀ q : MVRatParam d, ∀ x y : Rd d,
      X q g ((2 : ℝ) ^ j • x, (2 : ℝ) ^ j • y) =
        scaleS d q 1 ((2 : ℝ) ^ j) 0 g * X q (dilationTwoPow d j g) (x, y) := by
  have hd2 : 2 ≤ d := by omega
  rw [ae_all_iff]
  intro j
  rw [ae_all_iff]
  intro q
  obtain ⟨D, hD⟩ := mv_exists_strong hd q.2
  have hr : (0 : ℝ) < (2 : ℝ) ^ j := pow_pos two_pos j
  have hsc := rho_scaling_of hd2 q.2.1 hD (s := 1) (s₀ := 1) one_pos hr (0 : Rd d)
  have hv := hX.2.1 q q.2.1 q.2.2 D hD
  have hv' : ∀ᵐ g ∂(pinLaw d 1), X q g = (rho D g).1 := by rwa [pinLaw_one hd2]
  have hvT := ae_recentre_of_ae hd2 (s := 1) (s₀ := 1) (r := (2 : ℝ) ^ j) one_pos one_pos hr (0 : Rd d) hv'
  rw [pinLaw_one hd2] at hsc hvT
  filter_upwards [hsc, hv, hvT] with g hg1 hg2 hg3 x y
  have := hg1.1 x y
  simp only [add_zero] at this
  rw [hg2, this, dilationTwoPow, hg3]

/-! ## The dilation `T` of the blueprint and its iterates -/

/-- The blueprint's dilation `T g = g(2 ·) - g_2(0)` (`recentre 1 2 0`; Part C `c:lem-opt-dilation`). -/
def dilationTwo (d : ℕ) : DistRd d → DistRd d :=
  recentre 1 2 0

theorem dilationTwo_eq_dilationTwoPow_one : dilationTwo d = dilationTwoPow d 1 := by
  rw [dilationTwo, dilationTwoPow, pow_one]

theorem measurePreserving_dilationTwo (hd : 2 ≤ d) :
    MeasurePreserving (dilationTwo d) (normLGFLaw d) (normLGFLaw d) := by
  rw [dilationTwo_eq_dilationTwoPow_one]
  exact measurePreserving_dilationTwoPow hd 1

/-- Almost surely `T(T_j g) = T_{j+1} g` for all `j` (the sphere-average rescaling of ruling M17 at the factor `2`). -/
theorem ae_dilationTwo_dilationTwoPow (hd : 2 ≤ d) :
    ∀ᵐ g ∂(normLGFLaw d), ∀ j : ℕ, dilationTwo d (dilationTwoPow d j g) = dilationTwoPow d (j + 1) g := by
  have hspec := normLGFLaw_spec_holds d hd
  have := hspec.1
  have hlgf : IsWholeSpaceLGF (id : DistRd d → DistRd d) (normLGFLaw d) := hspec.2.1.1
  rw [ae_all_iff]
  intro j
  have hr0 : (0 : ℝ) < (2 : ℝ) ^ j := pow_pos two_pos j
  have h1 := hlgf.ae_sphereAvg_affineComp hd hr0 (0 : Rd d) two_pos (0 : Rd d)
  have h2 := (hlgf.affineComp hr0 (0 : Rd d)).ae_exists_tendsto_sphereAvgSeq hd two_pos (0 : Rd d)
  filter_upwards [h1, h2] with g hg1 hg2
  obtain ⟨a, ha⟩ := hg2
  simp only [id_eq, smul_zero, add_zero] at hg1 ha
  simp only [dilationTwo, dilationTwoPow, recentre, one_mul]
  rw [affineComp_addConst two_pos, affineComp_affineComp, smul_zero, add_zero,
    sphereAvg_addConst_of_tendsto (by omega) ha, hg1, addConst_addConst, pow_succ]
  congr 1
  ring

/-- Almost surely the iterates of `T` are the dyadic dilations: `T^j g = T_j g` for all `j`. -/
theorem ae_dilationTwo_iterate (hd : 2 ≤ d) :
    ∀ᵐ g ∂(normLGFLaw d), ∀ j : ℕ, (dilationTwo d)^[j] g = dilationTwoPow d j g := by
  have hspec := normLGFLaw_spec_holds d hd
  have hlgf : IsWholeSpaceLGF (id : DistRd d → DistRd d) (normLGFLaw d) := hspec.2.1.1
  filter_upwards [ae_dilationTwo_dilationTwoPow hd, hspec.2.1.2,
    hlgf.ae_exists_tendsto_sphereAvgSeq hd one_pos (0 : Rd d)] with g hg hg1 hconv j
  induction j with
  | zero =>
    obtain ⟨a, ha⟩ := hconv
    simp only [id_eq] at hg1 ha
    simp only [Function.iterate_zero, id_eq, dilationTwoPow, pow_zero, recentre, one_mul,
      affineComp_one_zero, hg1, neg_zero, addConst_zero]
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih, hg j]

/-- **`c:lem-opt-dilation`** (exact covariance at every parameter): almost surely, for all `j`, every positive
subcritical `ξ` and all `x, y`, `X(ξ)(g)(2^j x, 2^j y) = 2^{j ϕ(ξ)} e^{ξ g_{2^j}(0)} X(ξ)(T^j g)(x, y)`. -/
theorem ae_version_dilationTwo_iterate (hd : 3 ≤ d) {X : ℝ → DistRd d → C(Rd d × Rd d, ℝ)}
    (hX : PosVersionStmt d X) :
    ∀ᵐ g ∂(normLGFLaw d), ∀ j : ℕ, ∀ ξ ∈ subcritSet d, ∀ x y : Rd d,
      X ξ g ((2 : ℝ) ^ j • x, (2 : ℝ) ^ j • y) =
        (2 : ℝ) ^ ((j : ℝ) * phiXi d ξ) * Real.exp (ξ * sphereAvg g ((2 : ℝ) ^ j) 0) *
          X ξ ((dilationTwo d)^[j] g) (x, y) := by
  have hd2 : 2 ≤ d := by omega
  have hS : IsOpen (subcritSet d) := mv_isOpen_subcritSet hd2
  have hcT : ∀ j : ℕ, ∀ᵐ g ∂(normLGFLaw d),
      ContinuousOn (fun ξ => X ξ (dilationTwoPow d j g)) (subcritSet d) := by
    intro j
    have h := hX.2.2
    rw [← pinLaw_one hd2] at h ⊢
    exact ae_recentre_of_ae hd2 one_pos one_pos (pow_pos two_pos j) (0 : Rd d) h
  filter_upwards [hX.2.2, ae_all_iff.2 hcT, ae_version_dilationTwoPow hd hX, ae_dilationTwo_iterate hd2]
    with g hcg hcTg hsc hit j ξ hξ x y
  rw [hit j]
  have hr : (0 : ℝ) < (2 : ℝ) ^ j := pow_pos two_pos j
  -- the factor as `scaleS`
  have hfac : ∀ η : ℝ, (2 : ℝ) ^ ((j : ℝ) * phiXi d η) * Real.exp (η * sphereAvg g ((2 : ℝ) ^ j) 0) =
      scaleS d η 1 ((2 : ℝ) ^ j) 0 g := by
    intro η
    rw [scaleS, one_mul, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  rw [hfac]
  -- extension from the rational parameters
  have hcs : Continuous fun η : ℝ => scaleS d η 1 ((2 : ℝ) ^ j) 0 g := by
    have e : (fun η : ℝ => scaleS d η 1 ((2 : ℝ) ^ j) 0 g) = fun η =>
        Real.exp (phiXi d η * Real.log ((2 : ℝ) ^ j) + η * sphereAvg g (1 * (2 : ℝ) ^ j) 0) :=
      funext fun η => scaleS_eq_exp d η 1 hr 0 g
    rw [e]
    exact Real.continuous_exp.comp (((phiXi_continuous hd2).mul continuous_const).add
      (continuous_id.mul continuous_const))
  have hf : ContinuousOn (fun η => (X η g ((2 : ℝ) ^ j • x, (2 : ℝ) ^ j • y),
      scaleS d η 1 ((2 : ℝ) ^ j) 0 g * X η (dilationTwoPow d j g) (x, y))) (subcritSet d) :=
    (mv_continuousOn_eval hcg _).prodMk (hcs.continuousOn.mul (mv_continuousOn_eval (hcTg j) _))
  exact mv_mem_of_rat hS hf (isClosed_eq continuous_fst continuous_snd)
    (fun q hq => hsc j ⟨q, hq⟩ x y) ξ hξ

/-! ## Chebyshev for the dyadic sphere averages -/

/-- `P(|g_{2^j}(0)| > ε j) → 0` (Chebyshev, `Var g_{2^j}(0) ≤ j log 2 + K`). -/
theorem mv_tendsto_prob_sphereAvg_large (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun j : ℕ => normLGFLaw d {g | ε * j < |sphereAvg g ((2 : ℝ) ^ j) 0|}) atTop (𝓝 0) := by
  have := (normLGFLaw_spec_holds d hd).1
  obtain ⟨K, hK⟩ := exists_variance_sphereAvg_le hd
  set C : ℝ := (Real.log 2 + |K|) / ε ^ 2 with hC
  have hbound : ∀ j : ℕ, 1 ≤ j →
      normLGFLaw d {g | ε * j < |sphereAvg g ((2 : ℝ) ^ j) 0|} ≤ ENNReal.ofReal (C / j) := by
    intro j hj
    have hr : (0 : ℝ) < (2 : ℝ) ^ j := pow_pos two_pos j
    obtain ⟨hG, h0⟩ := hasGaussianLaw_sphereAvg_normLGFLaw hd hr
    have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
    have hεj : 0 < ε * j := mul_pos hε hj0
    have hcheb := meas_ge_le_variance_div_sq hG.memLp_two hεj
    rw [h0] at hcheb
    simp only [sub_zero] at hcheb
    refine (measure_mono fun g hg => ?_).trans (hcheb.trans (ENNReal.ofReal_le_ofReal ?_))
    · show ε * j ≤ |sphereAvg g ((2 : ℝ) ^ j) 0|
      exact le_of_lt hg
    · have hvar := hK _ hr
      rw [Real.log_pow, abs_of_nonneg (mul_nonneg (Nat.cast_nonneg j) (Real.log_nonneg one_le_two))]
        at hvar
      have hlog : 0 ≤ Real.log 2 := Real.log_nonneg one_le_two
      have h1 : (j : ℝ) * Real.log 2 + K ≤ (j : ℝ) * (Real.log 2 + |K|) := by
        have : K ≤ (j : ℝ) * |K| :=
          (le_abs_self K).trans (le_mul_of_one_le_left (abs_nonneg K) (by exact_mod_cast hj))
        linarith
      rw [div_le_div_iff₀ (pow_pos hεj 2) hj0, hC]
      calc Var[fun g : DistRd d => sphereAvg g ((2 : ℝ) ^ j) 0; normLGFLaw d] * (j : ℝ)
          ≤ ((j : ℝ) * (Real.log 2 + |K|)) * j :=
            mul_le_mul_of_nonneg_right (hvar.trans h1) hj0.le
        _ = (Real.log 2 + |K|) / ε ^ 2 * (ε * j) ^ 2 := by
            field_simp
  have hlim : Tendsto (fun j : ℕ => ENNReal.ofReal (C / j)) atTop (𝓝 0) := by
    have := ENNReal.tendsto_ofReal (tendsto_const_div_atTop_nhds_zero_nat C)
    rwa [ENNReal.ofReal_zero] at this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun j => zero_le) ?_
  filter_upwards [eventually_ge_atTop 1] with j hj
  exact hbound j hj

/-! ## Reverse Fatou -/

/-- **Reverse Fatou for events**: if `a ≤ μ(s n) + δ` eventually, for every `δ > 0`, then `a ≤ μ(s n i.o.)`. -/
theorem mv_le_measure_limsup {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {s : ℕ → Set Ω} (hs : ∀ n, MeasurableSet (s n)) {a : ℝ≥0∞}
    (h : ∀ δ : ℝ≥0, 0 < δ → ∀ᶠ n in atTop, a ≤ μ (s n) + δ) :
    a ≤ μ (⋂ N : ℕ, ⋃ n : ℕ, ⋃ (_ : N ≤ n), s n) := by
  set B : ℕ → Set Ω := fun N => ⋃ n : ℕ, ⋃ (_ : N ≤ n), s n with hB
  have hBm : ∀ N, MeasurableSet (B N) := fun N =>
    MeasurableSet.iUnion fun n => MeasurableSet.iUnion fun _ => hs n
  have hanti : Antitone B := fun N N' hNN' x hx => by
    simp only [hB, mem_iUnion] at hx ⊢
    obtain ⟨n, hn, hxn⟩ := hx
    exact ⟨n, hNN'.trans hn, hxn⟩
  have hlim := tendsto_measure_iInter_atTop (μ := μ) (fun N => (hBm N).nullMeasurableSet) hanti
    ⟨0, measure_ne_top μ _⟩
  refine ENNReal.le_of_forall_pos_le_add fun δ hδ _ => ?_
  have hlimδ : Tendsto (fun N => μ (B N) + (δ : ℝ≥0∞)) atTop (𝓝 (μ (⋂ N, B N) + δ)) :=
    hlim.add tendsto_const_nhds
  refine ge_of_tendsto' hlimδ fun N => ?_
  obtain ⟨n, hle, hn⟩ := ((h δ hδ).and (eventually_ge_atTop N)).exists
  calc a ≤ μ (s n) + δ := hle
    _ ≤ μ (B N) + δ := by
      gcongr
      exact fun x hx => mem_iUnion₂.2 ⟨n, hn, hx⟩

end HigherDimLQGContinuity
