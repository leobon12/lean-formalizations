/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.WholeField9Prob
import InteractingSLE.Spec.Coupling.MartMeansCond
import InteractingSLE.WangWu.NonBoundaryKernel

/-!
# C.5 in conditional-mean form: the reconstruction across a thin set

Packet PROVE-WHOLEFIELD9 (follow-up note C.5, (WF12)–(WF13), `source/external/AstraIG1/ig1_followup_proofs.txt`
L1705–1840; specification Proposition R1, pp. 448–449).

Wang–Wu's Corollary 4.23 (`WangWu.ae_condExp_exp_eq_gaussCF`) passes the Gaussian kernel from the tests avoiding a thin
set `A` to every test, for a **bounded** mean. For `κ ≠ 4` the mean is unbounded near the trace, and the follow-up note
only claims that the means of the reconstruction sums converge ("its Gaussian mean `μ_{n_j} − μ_{n_k}` must tend to
zero"). Here the means are the conditional means `μ_j = E[Y_j | 𝒢]` of the reconstruction sums `Y_j`, and:

* `ae_condExp_exp_offSum_cm`: given the kernel off `A` in conditional-mean form, `E[e^{itY_j} | 𝒢] =
  exp(i t μ_j − ½ t² q_j)` (finitely many cases);
* `μ_j` is almost surely bounded, by the median bound (`ae_bddAbove_of_median`), since `Y_j` converges;
* for every rational `t`, `E[e^{itY_j} | 𝒢] → E[e^{itF(φ)} | 𝒢]` almost surely (`ae_tendsto_condExp_of_tendsto_bdd`),
  so `e^{itμ_j}` converges and `μ_j → μ_∞` (`tendsto_of_bdd_of_tendsto_exp`);
* then `E[e^{itF(φ)} | 𝒢] = exp(i t μ_∞ − ½ t² q)` for every real `t`, and `μ_∞ = E[F(φ) | 𝒢]`.

**`ae_condExp_exp_eq_gaussCF_condMean`** is the resulting abstract reconstruction theorem.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric Complex
open scoped NNReal ENNReal Real

namespace InteractingSLE

namespace WholeField

open LQGMetric QuantumZipper WangWu

section Offsum

variable {Ω : Type*} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Ω → DistOn upperHalfPlaneOpens} {A : Ω → Set ℂ}

open Classical in
/-- **The conditional law of a reconstruction sum, in conditional-mean form.** If the conditional Gaussian kernel holds
off `A` in conditional-mean form (`hker`, variance `Q ω ψ`), then for every `t`,
`E[e^{itY} | 𝒢] = exp(i t E[Y | 𝒢] − ½ t² Q(f_n))`, `Y = offSum`, `f_n = goodTest`. -/
theorem ae_condExp_exp_offSum_cm (h𝒢 : 𝒢 ≤ mΩ)
    (hA𝒢 : ∀ ψ : TestOn upperHalfPlaneOpens, MeasurableSet[𝒢] {ω | Disjoint (tsupport ψ) (A ω)})
    (hFm : ∀ ψ : TestOn upperHalfPlaneOpens, Measurable fun ω => F ω ψ)
    (hFi : ∀ ψ : TestOn upperHalfPlaneOpens, Integrable (fun ω => F ω ψ) P)
    {Q : Ω → (ℂ → ℝ) → ℝ}
    (hker : ∀ (ψ : TestOn upperHalfPlaneOpens) (t : ℝ), ∀ᵐ ω ∂P, Disjoint (tsupport ψ) (A ω) →
      P[fun ω' => cexp (I * ((t * F ω' ψ : ℝ) : ℂ)) | 𝒢] ω =
        gaussCF (t * (P[fun ω' => F ω' ψ | 𝒢]) ω) (t ^ 2 * Q ω ψ))
    (φ : TestOn upperHalfPlaneOpens) (R : ℝ) (n : ℕ) (t : ℝ) :
    ∀ᵐ ω ∂P, P[fun ω' => cexp (I * ((t * offSum A F φ R n ω' : ℝ) : ℂ)) | 𝒢] ω =
      gaussCF (t * (P[offSum A F φ R n | 𝒢]) ω) (t ^ 2 * Q ω (goodTest φ n (goodSet (A ω) φ R n))) := by
  set Ix := pouIdx (scaleIdx R n) with hIx
  set Xe : Finset (ℤ × ℤ) → Ω → ℂ := fun S ω => cexp (I * ((t * F ω (goodTest φ n S) : ℝ) : ℂ)) with hXe
  set Xr : Finset (ℤ × ℤ) → Ω → ℝ := fun S ω => F ω (goodTest φ n S) with hXr
  set E : Finset (ℤ × ℤ) → Set Ω := fun S => {ω | goodSet (A ω) φ R n = S} with hE
  have hgood : ∀ ω, goodSet (A ω) φ R n ∈ Ix.powerset := fun ω =>
    Finset.mem_powerset.2 (Finset.filter_subset _ _)
  have hpt : (fun ω => cexp (I * ((t * offSum A F φ R n ω : ℝ) : ℂ))) = ∑ S ∈ Ix.powerset, (E S).indicator (Xe S) := by
    funext ω
    rw [Finset.sum_apply, Finset.sum_eq_single (goodSet (A ω) φ R n)]
    · rw [indicator_of_mem (show ω ∈ E (goodSet (A ω) φ R n) from rfl), offSum_eq_goodTest]
    · intro S _ hS
      exact indicator_of_notMem (fun h => hS h.symm) _
    · exact fun h => absurd (hgood ω) h
  have hptr : offSum A F φ R n = ∑ S ∈ Ix.powerset, (E S).indicator (Xr S) := by
    funext ω
    rw [Finset.sum_apply, Finset.sum_eq_single (goodSet (A ω) φ R n)]
    · rw [indicator_of_mem (show ω ∈ E (goodSet (A ω) φ R n) from rfl), offSum_eq_goodTest]
    · intro S _ hS
      exact indicator_of_notMem (fun h => hS h.symm) _
    · exact fun h => absurd (hgood ω) h
  have hEm : ∀ S ∈ Ix.powerset, MeasurableSet[𝒢] (E S) := fun S hS =>
    measurableSet_setOf_goodSet hA𝒢 φ R n (Finset.mem_powerset.1 hS)
  have hXei : ∀ S, Integrable (Xe S) P := fun S => by
    refine Integrable.of_bound ?_ 1 (Eventually.of_forall fun ω => by rw [Complex.norm_exp_I_mul_ofReal])
    exact (Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp
      (measurable_const.mul (hFm _))))).aestronglyMeasurable
  have hint : ∀ S ∈ Ix.powerset, Integrable ((E S).indicator (Xe S)) P := fun S hS =>
    (hXei S).indicator (h𝒢 _ (hEm S hS))
  have hintr : ∀ S ∈ Ix.powerset, Integrable ((E S).indicator (Xr S)) P := fun S hS =>
    (hFi _).indicator (h𝒢 _ (hEm S hS))
  have hsum := condExp_finsetSum (μ := P) hint 𝒢
  have hsumr := condExp_finsetSum (μ := P) hintr 𝒢
  have hind : ∀ᵐ ω ∂P, ∀ S ∈ Ix.powerset,
      P[(E S).indicator (Xe S) | 𝒢] ω = (E S).indicator (P[Xe S | 𝒢]) ω :=
    (eventually_all_finset _).2 fun S hS => condExp_indicator (hXei S) (hEm S hS)
  have hindr : ∀ᵐ ω ∂P, ∀ S ∈ Ix.powerset,
      P[(E S).indicator (Xr S) | 𝒢] ω = (E S).indicator (P[Xr S | 𝒢]) ω :=
    (eventually_all_finset _).2 fun S hS => condExp_indicator (hFi _) (hEm S hS)
  have hkerS : ∀ᵐ ω ∂P, ∀ S ∈ Ix.powerset, Disjoint (tsupport (goodTest φ n S)) (A ω) →
      P[Xe S | 𝒢] ω = gaussCF (t * (P[Xr S | 𝒢]) ω) (t ^ 2 * Q ω (goodTest φ n S)) :=
    (eventually_all_finset _).2 fun S _ => hker (goodTest φ n S) t
  rw [hpt, hptr]
  filter_upwards [hsum, hsumr, hind, hindr, hkerS] with ω h1 h1r h2 h2r h3
  rw [h1, h1r, Finset.sum_apply, Finset.sum_apply, Finset.sum_eq_single (goodSet (A ω) φ R n),
    Finset.sum_eq_single (goodSet (A ω) φ R n)]
  · rw [h2 _ (hgood ω), h2r _ (hgood ω), indicator_of_mem (show ω ∈ E (goodSet (A ω) φ R n) from rfl),
      indicator_of_mem (show ω ∈ E (goodSet (A ω) φ R n) from rfl)]
    exact h3 _ (hgood ω) (disjoint_goodTest_goodSet _ φ R n)
  · intro S hS hne
    rw [h2r S hS, indicator_of_notMem (fun h => hne h.symm)]
  · exact fun h => absurd (hgood ω) h
  · intro S hS hne
    rw [h2 S hS, indicator_of_notMem (fun h => hne h.symm)]
  · exact fun h => absurd (hgood ω) h

end Offsum

section Main

variable {Ω : Type*} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Ω → DistOn upperHalfPlaneOpens} {A : Ω → Set ℂ}

theorem gaussCF_eq_mul (a q : ℝ) :
    gaussCF a q = cexp (I * (a : ℂ)) * ((Real.exp (-(1 / 2) * q) : ℝ) : ℂ) := by
  rw [gaussCF, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1; push_cast; ring

theorem norm_gaussCF_le {a q : ℝ} (hq : 0 ≤ q) : ‖gaussCF a q‖ ≤ 1 := by
  rw [gaussCF_eq_mul, norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
  nlinarith

open Classical in
/-- **Proposition R1 / (WF12)–(WF13) in conditional-mean form.** Let `h` be a zero-boundary GFF on `ℍ`, `F = h + m`
with `m` bounded, `𝒢 ≤ mΩ` containing every avoidance event `{tsupport ψ ∩ A = ∅}`, and `G` a measurable kernel with
`0 ≤ G ≤ G_ℍ` off the diagonal. Suppose that the conditional Gaussian kernel holds off `A` with the conditional mean:
`E[e^{itF(ψ)} | 𝒢] = exp(i t E[F(ψ) | 𝒢] − ½ t² Q_G(ψ))` on `{tsupport ψ ∩ A = ∅}`. If `A` has the covering property
(R1.1) on `tsupport φ`, then for every real `t`, almost surely
`E[e^{itF(φ)} | 𝒢] = exp(i t E[F(φ) | 𝒢] − ½ t² Q_G(φ))`. No bound on the mean is used. -/
theorem ae_condExp_exp_eq_gaussCF_condMean (h𝒢 : 𝒢 ≤ mΩ) {h : Ω → DistOn upperHalfPlaneOpens}
    {m : ℂ → ℝ} {Mm : ℝ} (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hm : ∀ z ∈ H, |m z| ≤ Mm) (hF : ∀ ω ψ, F ω ψ = h ω ψ + ∫ z, m z * ψ z)
    (hA𝒢 : ∀ ψ : TestOn upperHalfPlaneOpens, MeasurableSet[𝒢] {ω | Disjoint (tsupport ψ) (A ω)})
    {G : Ω → ℂ → ℂ → ℝ} (hGm : ∀ ω, Measurable (Function.uncurry (G ω)))
    (hG : ∀ ω a b, a ∈ H → b ∈ H → a ≠ b → 0 ≤ G ω a b ∧ G ω a b ≤ greenH a b)
    (hker : ∀ (ψ : TestOn upperHalfPlaneOpens) (t : ℝ), ∀ᵐ ω ∂P, Disjoint (tsupport ψ) (A ω) →
      P[fun ω' => cexp (I * ((t * F ω' ψ : ℝ) : ℂ)) | 𝒢] ω =
        gaussCF (t * (P[fun ω' => F ω' ψ | 𝒢]) ω) (t ^ 2 * greenForm (G ω) ψ))
    (φ : TestOn upperHalfPlaneOpens) {ns : ℕ → ℕ} (hns : Tendsto ns atTop atTop)
    (hcov : ∀ᵐ ω ∂P, Tendsto (fun j => (Dimension.dyadicCount (ns j) (A ω ∩ tsupport φ) : ℝ) *
      (ns j + 1) / 4 ^ ns j) atTop (𝓝 0)) (t : ℝ) :
    ∀ᵐ ω ∂P, P[fun ω' => cexp (I * ((t * F ω' φ : ℝ) : ℂ)) | 𝒢] ω =
      gaussCF (t * (P[fun ω' => F ω' φ | 𝒢]) ω) (t ^ 2 * greenForm (G ω) φ) := by
  have hFm : ∀ ψ : TestOn upperHalfPlaneOpens, Measurable fun ω => F ω ψ := fun ψ => by
    simp_rw [hF]; exact (hh.process.measurable ψ).add_const _
  have hFi : ∀ ψ : TestOn upperHalfPlaneOpens, Integrable (fun ω => F ω ψ) P := fun ψ => by
    simp_rw [hF]
    exact ((hh.process.gaussian.hasGaussianLaw_eval ψ).memLp_two.integrable one_le_two).add
      (integrable_const _)
  -- support radius and sup bound
  obtain ⟨R₀, hR₀⟩ := φ.hasCompactSupport.isCompact.isBounded.subset_closedBall 0
  set R := max R₀ 1 with hRdef
  have hR : 0 < R := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hRsub : tsupport φ ⊆ closedBall 0 R :=
    hR₀.trans (closedBall_subset_closedBall (le_max_left _ _))
  obtain ⟨Bφ, hB'⟩ := φ.continuous.bounded_above_of_compact_support φ.hasCompactSupport
  have hB : ∀ z, |φ z| ≤ Bφ := fun z => by simpa [Real.norm_eq_abs] using hB' z
  have hφH : ∀ z, z ∉ H ∩ closedBall 0 R → φ z = 0 := fun z hz =>
    image_eq_zero_of_notMem_tsupport fun ht => hz ⟨φ.tsupport_subset ht, hRsub ht⟩
  -- the reconstruction sums, their conditional means and variances
  set Y : ℕ → Ω → ℝ := fun j => offSum A F φ R (ns j) with hYdef
  set μ : ℕ → Ω → ℝ := fun j => P[Y j | 𝒢] with hμdef
  set fj : ℕ → Ω → TestOn upperHalfPlaneOpens :=
    fun j ω => goodTest φ (ns j) (goodSet (A ω) φ R (ns j)) with hfj
  set q : ℕ → Ω → ℝ := fun j ω => greenForm (G ω) (fj j ω) with hqdef
  have hYm : ∀ j, Measurable (Y j) := fun j => measurable_offSum_ambient h𝒢 hA𝒢 hFm φ R (ns j)
  have hμm : ∀ j, Measurable[𝒢] (μ j) := fun j => stronglyMeasurable_condExp.measurable
  have hK1 : ∀ (j : ℕ) (t : ℝ), ∀ᵐ ω ∂P, P[fun ω' => cexp (I * ((t * Y j ω' : ℝ) : ℂ)) | 𝒢] ω =
      gaussCF (t * μ j ω) (t ^ 2 * q j ω) := fun j t =>
    ae_condExp_exp_offSum_cm h𝒢 hA𝒢 hFm hFi (Q := fun ω ψ => greenForm (G ω) ψ) hker φ R (ns j) t
  have hYlim := ae_tendsto_offSum hh hm hF φ hR.le hRsub hns hcov
  -- the variances converge
  have hqlim : ∀ᵐ ω ∂P, Tendsto (fun j => q j ω) atTop (𝓝 (greenForm (G ω) φ)) := by
    filter_upwards [hcov] with ω hω
    set U : ℕ → Set ℂ := fun j =>
      badBalls (ns j) (pouIdx (scaleIdx R (ns j)) \ goodSet (A ω) φ R (ns j)) with hU
    have hUm : ∀ j, MeasurableSet (U j) := fun j => measurableSet_badBalls _ _
    have hUle' : ∀ j, volume (U j) ≤ ((pouIdx (scaleIdx R (ns j)) \ goodSet (A ω) φ R (ns j)).card : ℝ≥0∞) *
        ENNReal.ofReal (4 * π / 4 ^ ns j) := fun j => volume_badBalls_le _ _
    have hUf : ∀ j, volume (U j) ≠ ⊤ := fun j =>
      ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.ofReal_ne_top) (hUle' j)
    have hUle : ∀ j, (volume (U j)).toReal ≤ 36 * π *
        ((Dimension.dyadicCount (ns j) (A ω ∩ tsupport φ) : ℝ) * (ns j + 1) / 4 ^ ns j) := by
      intro j
      have hcard : ((pouIdx (scaleIdx R (ns j)) \ goodSet (A ω) φ R (ns j)).card : ℝ) ≤
          9 * Dimension.dyadicCount (ns j) (A ω ∩ tsupport φ) := by
        have h1 := card_bad_le φ (A ω) (ns j) (scaleIdx R (ns j))
        rw [Finset.filter_not] at h1
        exact_mod_cast h1
      have h4 : (0 : ℝ) < 4 ^ ns j := by positivity
      refine (ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.ofReal_ne_top)
        (hUle' j)).trans ?_
      rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_ofReal (by positivity)]
      have hn1 : (1 : ℝ) ≤ ns j + 1 := by linarith [(Nat.cast_nonneg (ns j) : (0 : ℝ) ≤ ns j)]
      have hN0 : (0 : ℝ) ≤ Dimension.dyadicCount (ns j) (A ω ∩ tsupport φ) := Nat.cast_nonneg _
      calc ((pouIdx (scaleIdx R (ns j)) \ goodSet (A ω) φ R (ns j)).card : ℝ) * (4 * π / 4 ^ ns j)
          ≤ 9 * Dimension.dyadicCount (ns j) (A ω ∩ tsupport φ) * (4 * π / 4 ^ ns j) :=
            mul_le_mul_of_nonneg_right hcard (by positivity)
        _ = 36 * π * ((Dimension.dyadicCount (ns j) (A ω ∩ tsupport φ) : ℝ) * 1 / 4 ^ ns j) := by ring
        _ ≤ 36 * π * ((Dimension.dyadicCount (ns j) (A ω ∩ tsupport φ) : ℝ) * (ns j + 1) / 4 ^ ns j) := by
            gcongr
    have hU0 : Tendsto (fun j => (volume (U j)).toReal) atTop (𝓝 0) :=
      squeeze_zero (fun j => ENNReal.toReal_nonneg) hUle (by simpa using hω.const_mul (36 * π))
    have hfjb : ∀ j z, |fj j ω z| ≤ Bφ := fun j z =>
      abs_goodTest_le hRsub hB _ (Finset.filter_subset _ _) z
    have hfjH : ∀ j z, z ∉ H ∩ closedBall 0 R → fj j ω z = 0 := fun j z hz =>
      goodTest_eq_zero_of_notMem _ _ fun ht => hz ⟨φ.tsupport_subset ht, hRsub ht⟩
    have hfjU : ∀ j z, z ∉ U j → φ z = fj j ω z := fun j z hz =>
      goodTest_eq_of_notMem_badBalls hRsub _ (Finset.filter_subset _ _) hz
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun j => norm_nonneg _) (fun j => ?_)
      (by simpa using hU0.const_mul (256 * π * R ^ 2 * Bφ ^ 2))
    rw [Real.norm_eq_abs, abs_sub_comm]
    exact abs_greenForm_sub_le (hGm ω) (hG ω) hR φ.continuous.measurable
      (fj j ω).continuous.measurable hB (hfjb j) hφH (hfjH j) (hUm j) (hUf j) (hfjU j)
  -- the conditional means are bounded (the median bound)
  have hYb : ∀ᵐ ω ∂P, BddAbove (range fun j => |Y j ω|) := by
    filter_upwards [hYlim] with ω hω
    obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall 0).1
      (Metric.isBounded_range_of_tendsto _ hω)
    refine ⟨r, ?_⟩
    rintro _ ⟨j, rfl⟩
    have := hr ⟨j, rfl⟩
    simpa [Real.dist_eq] using this
  have hcf : ∀ j (t : ℝ), P[fun ω => cexp (I * ((t * Y j ω : ℝ) : ℂ)) | 𝒢] =ᵐ[P]
      fun ω => cexp (I * ((t * μ j ω : ℝ) : ℂ)) * ((Real.exp (-(1 / 2) * (t ^ 2 * q j ω)) : ℝ) : ℂ) :=
    fun j t => (hK1 j t).mono fun ω hω => by rw [hω, gaussCF_eq_mul]
  have hμb := ae_bddAbove_of_median h𝒢 hYm hμm
    (fun j G hG => measure_le_two_mul_abs_le_of_condCharFun h𝒢 (hYm j) (hμm j) (hcf j) hG) hYb
  -- conditional dominated convergence of the characteristic functions
  have hexpm : ∀ (t : ℝ) {Z : Ω → ℝ}, Measurable Z → Measurable fun ω => cexp (I * ((t * Z ω : ℝ) : ℂ)) :=
    fun t Z hZ => Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp
      (measurable_const.mul hZ)))
  have hDCT : ∀ t : ℝ, ∀ᵐ ω ∂P, Tendsto (fun j => (P[fun ω' => cexp (I * ((t * Y j ω' : ℝ) : ℂ)) | 𝒢]) ω)
      atTop (𝓝 ((P[fun ω' => cexp (I * ((t * F ω' φ : ℝ) : ℂ)) | 𝒢]) ω)) := fun t =>
    ae_tendsto_condExp_of_tendsto_bdd h𝒢 (fun j => hexpm t (hYm j)) (hexpm t (hFm φ))
      (fun j ω => by rw [Complex.norm_exp_I_mul_ofReal]) (fun ω => by rw [Complex.norm_exp_I_mul_ofReal])
      (hYlim.mono fun ω hω => ((by fun_prop : Continuous fun x : ℝ => cexp (I * ((t * x : ℝ) : ℂ))).tendsto
        _).comp hω)
  -- the conditional means converge
  have hconv : ∀ᵐ ω ∂P, ∃ ℓ : ℝ, Tendsto (fun j => μ j ω) atTop (𝓝 ℓ) := by
    filter_upwards [hμb, ae_all_iff.2 fun c : ℚ => hDCT c,
      ae_all_iff.2 fun j => ae_all_iff.2 fun c : ℚ => hK1 j c, hqlim] with ω hb hd hk hql
    refine tendsto_of_bdd_of_tendsto_exp hb fun c => ⟨(P[fun ω' => cexp (I * (((c : ℝ) * F ω' φ : ℝ) : ℂ)) | 𝒢]) ω *
      ((Real.exp (1 / 2 * ((c : ℝ) ^ 2 * greenForm (G ω) φ)) : ℝ) : ℂ), ?_⟩
    have h2 : Tendsto (fun j => ((Real.exp (1 / 2 * ((c : ℝ) ^ 2 * q j ω)) : ℝ) : ℂ)) atTop
        (𝓝 ((Real.exp (1 / 2 * ((c : ℝ) ^ 2 * greenForm (G ω) φ)) : ℝ) : ℂ)) :=
      ((Complex.continuous_ofReal.comp Real.continuous_exp).tendsto _).comp
        ((hql.const_mul ((c : ℝ) ^ 2)).const_mul (1 / 2))
    refine ((hd c).mul h2).congr fun j => ?_
    rw [hk j c, gaussCF_eq_mul, mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
    rw [show -(1 / 2) * ((c : ℝ) ^ 2 * q j ω) + 1 / 2 * ((c : ℝ) ^ 2 * q j ω) = 0 by ring, Real.exp_zero,
      Complex.ofReal_one, mul_one]
  set μinf : Ω → ℝ := fun ω => limUnder atTop fun j => μ j ω with hμinf
  have hfin : ∀ t : ℝ, ∀ᵐ ω ∂P, P[fun ω' => cexp (I * ((t * F ω' φ : ℝ) : ℂ)) | 𝒢] ω =
      gaussCF (t * μinf ω) (t ^ 2 * greenForm (G ω) φ) := by
    intro t
    filter_upwards [hDCT t, ae_all_iff.2 fun j => hK1 j t, hconv, hqlim] with ω hd hk hc hql
    obtain ⟨ℓ, hℓ⟩ := hc
    have hlim : Tendsto (fun j => μ j ω) atTop (𝓝 (μinf ω)) := by
      rw [hμinf]; exact tendsto_nhds_limUnder ⟨ℓ, hℓ⟩
    refine tendsto_nhds_unique hd ?_
    have := (continuous_gaussCF.tendsto _).comp ((hlim.const_mul t).prodMk_nhds (hql.const_mul (t ^ 2)))
    refine this.congr fun j => ?_
    simp only [Function.comp_apply]
    exact (hk j).symm
  have hmean : P[fun ω => F ω φ | 𝒢] =ᵐ[P] μinf :=
    Coupling.MartMeans.condExp_ae_eq_of_condCharFun (hFi φ) (v := fun ω => greenForm (G ω) φ)
      fun c => (hfin c).mono fun ω hω => by rw [hω, gaussCF]
  filter_upwards [hfin t, hmean] with ω h1 h2
  rw [h1, h2]

end Main

end WholeField

end InteractingSLE
