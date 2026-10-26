import HigherDimLQGMetric.Main.Cor104

/-!
# Local boundedness of the LFPP normalizer `𝔞_δ` (packet L9b; MA6 P11, second part)

MA6 P11: "the same argument bounds the medians `𝔞_δ` for `δ ∈ [a, b] ⊂ (0, 1]`". Proof used here (simpler than a
tightness argument): almost surely `(δ, x) ↦ h*_δ(x)` is continuous on `(0, ∞) × ℝ^d` (L2b), hence bounded on the
compact `[a, b] × B̄_1(0)`. Choose `n` with `P[sup_{[a,b] × B̄_1} |h*_δ| ≤ n] > 1/2` (a measurable version of the event
through a countable dense subset). On that event, for every `δ ∈ [a, b]`, the straight segment gives
`D^δ(0, e₁) ≤ e^{|ξ| n}` and the exit from `B̄_1(0)` gives `D^δ(0, e₁) ≥ e^{-|ξ| n}`, so the lower median satisfies
`e^{-|ξ| n} ≤ 𝔞_δ ≤ e^{|ξ| n}`. Any `0 < a` (and any `b`) is allowed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd e₁ lfppDistOn)

variable {d : ℕ}

/-- deterministic two-sided bound of the LFPP point distance `D(0, e₁)` by the supremum of `|φ|` on `B̄_1(0)` -/
theorem l9b_lfppDist_e₁_bounds (hd : 0 < d) {ξ : ℝ} {φ : Rd d → ℝ} (hφ : Continuous φ) {n : ℝ}
    (hn : ∀ x ∈ closedBall (0 : Rd d) 1, |φ x| ≤ n) :
    Real.exp (-(|ξ| * n)) ≤ lfppDistOn ξ φ univ 0 (e₁ d) ∧
      lfppDistOn ξ φ univ 0 (e₁ d) ≤ Real.exp (|ξ| * n) := by
  have he : ‖e₁ d - 0‖ = 1 := by rw [sub_zero, HigherDimLFPP.norm_e₁ hd]
  have hxi : ∀ x ∈ closedBall (0 : Rd d) 1, |ξ * φ x| ≤ |ξ| * n := fun x hx => by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hn x hx) (abs_nonneg ξ)
  have he1 : e₁ d ∈ closedBall (0 : Rd d) 1 := by
    rw [mem_closedBall, dist_zero_right, HigherDimLFPP.norm_e₁ hd]
  have h0 : (0 : Rd d) ∈ closedBall (0 : Rd d) 1 := mem_closedBall_self zero_le_one
  have hseg := HigherDimLFPP.mapsTo_segPath (convex_closedBall (0 : Rd d) 1) h0 he1
  constructor
  · have hm : ∀ z ∈ closedBall (0 : Rd d) 1, -(|ξ| * n) ≤ ξ * φ z := fun z hz => by
      have := hxi z hz
      rw [abs_le] at this
      exact this.1
    have := HigherDimLFPP.exp_mul_le_lfppDistOn hφ
      (HigherDimLFPP.PcwJoined.of_convex convex_univ (mem_univ (0 : Rd d)) (mem_univ (e₁ d)))
      he.ge hm
    rwa [mul_one] at this
  · have := HigherDimLFPP.lfppDistOn_le_of_segment hφ (hseg.mono_right (subset_univ _))
      (B := Real.exp (|ξ| * n)) fun u hu => Real.exp_le_exp.2 (le_of_abs_le (hxi _ (hseg hu)))
    rwa [he, mul_one] at this

/-- the lower median `𝔞_ε` is at most any `t` with `P[D^ε(0, e₁) ≤ t] ≥ 1/2` -/
theorem l9b_aEps_le {κ : Rd d → ℝ} {ξ ε t : ℝ}
    (ht : (2 : ℝ≥0∞)⁻¹ ≤ normLGFLaw d {h | lfppDist κ ξ ε h (0, e₁ d) ≤ t}) :
    aEps κ ξ ε ≤ t := by
  unfold aEps
  refine csInf_le ⟨0, fun m hm => ?_⟩ ht
  by_contra hneg
  push Not at hneg
  have hempty : {h : DistRd d | lfppDist κ ξ ε h (0, e₁ d) ≤ m} = ∅ := by
    refine eq_empty_iff_forall_notMem.2 fun h hh => ?_
    have h0 : 0 ≤ lfppDist κ ξ ε h (0, e₁ d) := HigherDimLFPP.lfppDistOn_nonneg _ _ _ _ _
    have h1 : lfppDist κ ξ ε h (0, e₁ d) ≤ m := hh
    linarith
  have hm' : (2 : ℝ≥0∞)⁻¹ ≤ normLGFLaw d {h | lfppDist κ ξ ε h (0, e₁ d) ≤ m} := hm
  rw [hempty, measure_empty] at hm'
  exact absurd hm' (by simp)

/-- the lower median `𝔞_ε` is at least any `t` with `P[D^ε(0, e₁) < t] < 1/2` -/
theorem l9b_le_aEps {κ : Rd d → ℝ} {ξ ε s t : ℝ}
    (hs : (2 : ℝ≥0∞)⁻¹ ≤ normLGFLaw d {h | lfppDist κ ξ ε h (0, e₁ d) ≤ s})
    (ht : normLGFLaw d {h | lfppDist κ ξ ε h (0, e₁ d) < t} < (2 : ℝ≥0∞)⁻¹) :
    t ≤ aEps κ ξ ε := by
  unfold aEps
  refine le_csInf ⟨s, hs⟩ fun m hm => ?_
  by_contra hlt
  push Not at hlt
  have hm' : (2 : ℝ≥0∞)⁻¹ ≤ normLGFLaw d {h | lfppDist κ ξ ε h (0, e₁ d) ≤ m} := hm
  have hmono : normLGFLaw d {h | lfppDist κ ξ ε h (0, e₁ d) ≤ m} ≤
      normLGFLaw d {h | lfppDist κ ξ ε h (0, e₁ d) < t} :=
    measure_mono fun h (hh : lfppDist κ ξ ε h (0, e₁ d) ≤ m) =>
      (show lfppDist κ ξ ε h (0, e₁ d) < t from lt_of_le_of_lt hh hlt)
  exact absurd (hm'.trans hmono) (not_le.2 ht)

/-- **Local boundedness of `𝔞_δ`** (MA6 P11): for `0 < a`, `𝔞_δ` is bounded above and below by positive constants
on `[a, b]`. -/
theorem l9b_aEps_locBdd (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ) (ξ : ℝ)
    {a b : ℝ} (ha : 0 < a) :
    ∃ B : ℝ, 0 < B ∧ ∀ δ ∈ Icc a b, B⁻¹ ≤ aEps κ ξ δ ∧ aEps κ ξ δ ≤ B := by
  have hprob : IsProbabilityMeasure (normLGFLaw d) := (normLGFLaw_spec_holds d hd).1
  have hnorm : IsNormalizedLGF id (normLGFLaw d) := (normLGFLaw_spec_holds d hd).2.1
  set P : Measure (DistRd d) := normLGFLaw d with hP
  set K : Set (ℝ × Rd d) := Icc a b ×ˢ closedBall (0 : Rd d) 1 with hK
  obtain ⟨T, hTc, hTK, hKT⟩ := TopologicalSpace.exists_countable_dense_subset K
  let E : ℕ → Set (DistRd d) := fun n => ⋂ p ∈ T, {g | |convMollify κ p.1 g p.2| ≤ n}
  have hEm : ∀ n, MeasurableSet (E n) := fun n =>
    MeasurableSet.biInter hTc fun p _ =>
      measurableSet_le (continuous_abs.measurable.comp (l10a_measurable_convMollify_apply κ p.1 p.2))
        measurable_const
  have hEmono : Monotone E := by
    intro m n hmn g hg
    refine mem_iInter₂.2 fun p hp => ?_
    have h1 : |convMollify κ p.1 g p.2| ≤ m := mem_iInter₂.1 hg p hp
    have h2 : (m : ℝ) ≤ n := by exact_mod_cast hmn
    exact h1.trans h2
  have hjoint := l2b_ae_convMollify_continuousOn d hd κ hκ P id hnorm
  have hKsub : K ⊆ Ioi 0 ×ˢ univ :=
    prod_mono (fun δ hδ => mem_Ioi.2 (ha.trans_le hδ.1)) (subset_univ _)
  have hKc : IsCompact K := isCompact_Icc.prod (isCompact_closedBall 0 1)
  have hcover : ∀ᵐ g ∂P, g ∈ ⋃ n, E n := by
    filter_upwards [hjoint] with g hg
    obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn (hg.mono hKsub)
    obtain ⟨n, hn⟩ := exists_nat_ge M
    refine mem_iUnion.2 ⟨n, mem_iInter₂.2 fun p hp => ?_⟩
    have h1 := hM p (hTK hp)
    rw [Real.norm_eq_abs] at h1
    show |convMollify κ p.1 g p.2| ≤ n
    exact h1.trans hn
  have hfull : P (⋃ n, E n) = 1 := by
    have hset : (⋃ n, E n) =ᵐ[P] (univ : Set (DistRd d)) :=
      hcover.mono fun g hg => propext ⟨fun _ => mem_univ g, fun _ => hg⟩
    rw [measure_congr hset, measure_univ]
  have hlim := tendsto_measure_iUnion_atTop (μ := P) hEmono
  rw [hfull] at hlim
  have hhalf : (2 : ℝ≥0∞)⁻¹ < 1 := ENNReal.inv_lt_one.2 (by norm_num)
  obtain ⟨n, hn⟩ := (hlim.eventually (Ioi_mem_nhds hhalf)).exists
  have hn' : (2 : ℝ≥0∞)⁻¹ < P (E n) := hn
  -- the complement of the good event has probability `< 1/2`
  have hcompl : P (E n)ᶜ < (2 : ℝ≥0∞)⁻¹ := by
    rw [prob_compl_eq_one_sub (hEm n)]
    refine ENNReal.sub_lt_of_lt_add prob_le_one ?_
    calc (1 : ℝ≥0∞) = 2⁻¹ + 2⁻¹ := ENNReal.inv_two_add_inv_two.symm
      _ < 2⁻¹ + P (E n) := ENNReal.add_lt_add_left (by simp) hn'
  refine ⟨Real.exp (|ξ| * n), Real.exp_pos _, fun δ hδ => ?_⟩
  have hδ0 : 0 < δ := ha.trans_le hδ.1
  -- on the good event, the two-sided bound holds at `δ`
  have hgood : ∀ᵐ g ∂P, g ∈ E n → Real.exp (-(|ξ| * n)) ≤ lfppDist κ ξ δ g (0, e₁ d) ∧
      lfppDist κ ξ δ g (0, e₁ d) ≤ Real.exp (|ξ| * n) := by
    filter_upwards [hjoint] with g hg hgE
    have hc : Continuous (convMollify κ δ g) := by
      have hc' : Continuous fun z : Rd d => (δ, z) := continuous_const.prodMk continuous_id
      have hf := hg.comp_continuous hc' (fun _ => ⟨hδ0, mem_univ _⟩)
      simpa only [Function.comp_def, id_eq] using hf
    have hbd : ∀ x ∈ closedBall (0 : Rd d) 1, |convMollify κ δ g x| ≤ n := by
      intro x hx
      have hpK : (δ, x) ∈ K := ⟨hδ, hx⟩
      have hcw : ContinuousWithinAt (fun p : ℝ × Rd d => |convMollify κ p.1 (id g) p.2|) T (δ, x) :=
        ((hg (δ, x) (hKsub hpK)).mono (hTK.trans hKsub)).abs
      exact hcw.closure_le (hKT hpK) continuousWithinAt_const fun p hp => mem_iInter₂.1 hgE p hp
    exact l9b_lfppDist_e₁_bounds (by omega) hc hbd
  have hup : (2 : ℝ≥0∞)⁻¹ ≤ P {g | lfppDist κ ξ δ g (0, e₁ d) ≤ Real.exp (|ξ| * n)} :=
    hn'.le.trans (measure_mono_ae (hgood.mono fun g hg hgE => (hg hgE).2))
  have hlow : P {g | lfppDist κ ξ δ g (0, e₁ d) < Real.exp (-(|ξ| * n))} < (2 : ℝ≥0∞)⁻¹ :=
    lt_of_le_of_lt (measure_mono_ae (hgood.mono fun g hg
      (hlt : lfppDist κ ξ δ g (0, e₁ d) < Real.exp (-(|ξ| * n))) =>
        (fun hgE : g ∈ E n => absurd hlt (not_lt.2 (hg hgE).1) : g ∉ E n))) hcompl
  refine ⟨?_, l9b_aEps_le hup⟩
  rw [← Real.exp_neg]
  exact l9b_le_aEps hup hlow

end HigherDimLQGMetric
