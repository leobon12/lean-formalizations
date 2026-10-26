import SupercriticalLFPPAS.Local.Lemma32
import SupercriticalLFPPAS.Local.Transfer
import NV1Evidence

/-!
# Lemma 3.2 for the localized field `H_{δ,L}`, uniformly over `L ≥ log δ⁻¹` (packet P32)

Paper `source/almost-sure-supercritical-lfpp.txt`, Lemma 3.2, l. 253 ("The same holds for `X_δ`
constructed from `H_{δ,L}`, uniformly over `L ≥ log δ⁻¹`") and l. 274–275 of the proof; planning
audit `planning/audits/SB1-sections-1-3.md` A12, step 8.

The input is the uniform localization estimate (2.3) of Lemma 2.1 (packet D5c1, in progress), in
its qualitative almost-sure form `UniformLocalizedApprox`: almost surely `H_{δ,L} → h*_δ` uniformly
on a compact set and uniformly over `L ≥ log δ⁻¹`. Following the packet, (2.3) is a hypothesis of
the helper `lemma_3_2_loc_of_approx` until it lands.

The conclusion is the uniform form needed in §3.3 (planning audit SB2, D4): for every `θ > 0` there
is `δ₀ > 0` such that for all `δ < δ₀` and all `L ≥ log δ⁻¹`, the event of Lemma 3.2 for
`(D, Y_{δ,L})` fails with probability at most `θ`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal
open LQGMetric (DistC heatMollify)
open SupercriticalLQGUniqueness

namespace SupercriticalLFPPAS.Local

/-- **(2.3), qualitative almost-sure form.** Almost surely, `H_{δ,L} → h*_δ` uniformly on `K` and
uniformly over `L ≥ log δ⁻¹`, as `δ → 0` (`H_{δ,L}` is the localized field of cutoff radius `δL`,
`Field.uniformLocalizedHeatField`). -/
def UniformLocalizedApprox {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (h : Ω → DistC)
    (K : Set ℂ) : Prop :=
  ∀ᵐ ω ∂P, ∀ σ : ℝ, 0 < σ → ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ hδ : δ ∈ Ioo (0 : ℝ) 1, ∀ L : ℝ,
    Real.log δ⁻¹ ≤ L → ∀ z ∈ K,
      |B2.Polylog.plMollify (Field.uniformLocalizationExponent δ L) δ hδ (h ω) z -
        heatMollify δ (h ω) z| ≤ σ

/-- **Adapter for (2.3).** A quantitative almost-sure bound `|H_{δ,L} − h*_δ| ≤ C·r(δ)` on `K`,
uniform over `L ≥ log δ⁻¹` for small `δ`, with a deterministic rate `r(δ) → 0`, gives
`UniformLocalizedApprox`. -/
theorem uniformLocalizedApprox_of_rate {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistC} {K : Set ℂ} {r : ℝ → ℝ} (hr : Tendsto r (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hb : ∀ᵐ ω ∂P, ∃ C : ℝ, ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ hδ : δ ∈ Ioo (0 : ℝ) 1, ∀ L : ℝ,
      Real.log δ⁻¹ ≤ L → ∀ z ∈ K,
        |B2.Polylog.plMollify (Field.uniformLocalizationExponent δ L) δ hδ (h ω) z -
          heatMollify δ (h ω) z| ≤ C * r δ) :
    UniformLocalizedApprox P h K := by
  filter_upwards [hb] with ω hω
  obtain ⟨C, hC⟩ := hω
  intro σ hσ
  have hCr : Tendsto (fun δ => C * r δ) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using hr.const_mul C
  filter_upwards [hC, hCr.eventually (eventually_le_nhds hσ)] with δ h1 h2 hδ L hL z hz
  exact (h1 hδ L hL z hz).trans h2

/-- The measurable approximation-failure event: `|H_{δ,L} − h*_δ| > σ` at some point of a fixed
countable dense set inside `U₁`. -/
def approxFailure {Ω : Type*} (h : Ω → DistC) (δ : ℝ) (hδ : δ ∈ Ioo (0 : ℝ) 1) (L σ : ℝ) :
    Set Ω :=
  {ω | ∃ k : ℕ, TopologicalSpace.denseSeq ℂ k ∈ nbhdU ∧
    σ < |B2.Polylog.plMollify (Field.uniformLocalizationExponent δ L) δ hδ (h ω)
      (TopologicalSpace.denseSeq ℂ k) - heatMollify δ (h ω) (TopologicalSpace.denseSeq ℂ k)|}

theorem measurableSet_approxFailure {Ω : Type*} [MeasurableSpace Ω] {h : Ω → DistC}
    (hhm : Measurable h) (δ : ℝ) (hδ : δ ∈ Ioo (0 : ℝ) 1) (L σ : ℝ) :
    MeasurableSet (approxFailure h δ hδ L σ) := by
  have hF : ∀ k : ℕ, Measurable fun ω =>
      |B2.Polylog.plMollify (Field.uniformLocalizationExponent δ L) δ hδ (h ω)
        (TopologicalSpace.denseSeq ℂ k) - heatMollify δ (h ω) (TopologicalSpace.denseSeq ℂ k)| :=
    fun k => ((measurable_const.mul ((LQGMetric.measurable_distOn_apply _).comp hhm)).sub
      ((LQGMetric.measurable_heatMollify_left δ _).comp hhm)).abs
  have heq : approxFailure h δ hδ L σ = ⋃ k : ℕ, {ω | TopologicalSpace.denseSeq ℂ k ∈ nbhdU ∧
      σ < |B2.Polylog.plMollify (Field.uniformLocalizationExponent δ L) δ hδ (h ω)
        (TopologicalSpace.denseSeq ℂ k) - heatMollify δ (h ω) (TopologicalSpace.denseSeq ℂ k)|} := by
    ext ω
    simp only [approxFailure, mem_iUnion, mem_ofPred_eq]
  rw [heq]
  refine MeasurableSet.iUnion fun k => ?_
  by_cases hk : TopologicalSpace.denseSeq ℂ k ∈ nbhdU
  · simp only [hk, true_and]
    exact measurableSet_lt measurable_const (hF k)
  · simp only [hk, false_and]
    exact MeasurableSet.empty

/-- Outside the approximation-failure event, the two continuous fields are `σ`-close on all of
`U₁`. -/
theorem abs_sub_le_of_not_mem_approxFailure {Ω : Type*} {h : Ω → DistC} {δ : ℝ}
    {hδ : δ ∈ Ioo (0 : ℝ) 1} {L σ : ℝ} {ω : Ω} (hω : ω ∉ approxFailure h δ hδ L σ)
    (φ : C(ℂ, ℝ)) (hφ : ∀ z, φ z = heatMollify δ (h ω) z) :
    ∀ z ∈ nbhdU, |B2.Polylog.plMollifyC (Field.uniformLocalizationExponent δ L) δ hδ (h ω) z -
      φ z| ≤ σ := by
  set F : ℂ → ℝ := fun z =>
    |B2.Polylog.plMollifyC (Field.uniformLocalizationExponent δ L) δ hδ (h ω) z - φ z|
  have hF : Continuous F := ((ContinuousMap.continuous _).sub φ.continuous).abs
  have hclosed : IsClosed {z | F z ≤ σ} := isClosed_le hF continuous_const
  have hsub : nbhdU ∩ range (TopologicalSpace.denseSeq ℂ) ⊆ {z | F z ≤ σ} := by
    rintro z ⟨hzU, k, rfl⟩
    by_contra hcon
    apply hω
    refine ⟨k, hzU, ?_⟩
    have h1 : σ < F (TopologicalSpace.denseSeq ℂ k) := not_le.1 hcon
    have e : F (TopologicalSpace.denseSeq ℂ k) =
        |B2.Polylog.plMollify (Field.uniformLocalizationExponent δ L) δ hδ (h ω)
          (TopologicalSpace.denseSeq ℂ k) - heatMollify δ (h ω) (TopologicalSpace.denseSeq ℂ k)| := by
      simp only [F, hφ]
      rfl
    rw [e] at h1
    exact h1
  intro z hz
  have hz' := (TopologicalSpace.denseRange_denseSeq ℂ).open_subset_closure_inter isOpen_nbhdU hz
  exact hclosed.closure_subset_iff.2 hsub hz'

/-- (2.3) makes the approximation-failure events small, uniformly over `L ≥ log δ⁻¹`. -/
theorem eventually_measure_approxFailure_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {h : Ω → DistC} (hhm : Measurable h) {K : Set ℂ} (hUK : nbhdU ⊆ K)
    (hA : UniformLocalizedApprox P h K) {σ θ : ℝ} (hσ : 0 < σ) (hθ : 0 < θ) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ hδ : δ ∈ Ioo (0 : ℝ) 1, ∀ L : ℝ, Real.log δ⁻¹ ≤ L →
      P (approxFailure h δ hδ L σ) ≤ ENNReal.ofReal θ := by
  by_contra hcon
  rw [not_eventually] at hcon
  obtain ⟨x, hx, hxbad⟩ := exists_seq_forall_of_frequently hcon
  simp only [not_forall, not_le] at hxbad
  choose hδn Ln hLn hPn using hxbad
  let A : ℕ → Set Ω := fun n => approxFailure h (x n) (hδn n) (Ln n) σ
  have hAm : ∀ n, NullMeasurableSet (A n) P := fun n =>
    (measurableSet_approxFailure hhm _ _ _ _).nullMeasurableSet
  have hae : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ω ∉ A n := by
    filter_upwards [hA] with ω hω
    filter_upwards [hx.eventually (hω σ hσ)] with n hn
    rintro ⟨k, hk, hlt⟩
    have := hn (hδn n) (Ln n) (hLn n) _ (hUK hk)
    linarith
  have hlim := tendsto_measure_of_ae_eventually_not_mem hAm hae
  obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 hθ))).exists
  exact (lt_asymm hn) (hPn n)

/-- **Lemma 3.2 for `H_{δ,L}`, from (2.3)** (`UniformLocalizedApprox` on `closedBall 0 17`): for
every `M < ∞`, `η, ν > 0` and `θ > 0` there is `δ₀ > 0` such that for all `δ < δ₀` and all
`L ≥ log δ⁻¹` the event of Lemma 3.2 for `(D, Y_{δ,L})` fails with probability at most `θ`. -/
theorem lemma_3_2_loc_of_approx (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (D : DistC → LSCMetric) (hD : IsStrongLQGMetric ξ Q D)
    (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)) (hm : ∀ ε, IsLFPPNormalizer ξ ε (m ε))
    (hDlim : IsLFPPLimit ξ m D)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (hA : UniformLocalizedApprox P h (closedBall (0 : ℂ) 17))
    (M η ν : ℝ) (hη : 0 < η) (hν : 0 < ν) :
    ∀ θ : ℝ, 0 < θ → ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ (δ : ℝ) (hδ : δ ∈ Ioo (0 : ℝ) 1), δ < δ₀ →
      ∀ L : ℝ, Real.log δ⁻¹ ≤ L →
        P {ω | ¬ Lemma32Event (D (h ω)) (locMetric (ξ : ℝ) m δ L hδ (h ω)) η ν M} ≤
          ENNReal.ofReal θ := by
  intro θ hθ
  have hξ : (0 : ℝ) < ξ := ξ.2
  have hhm : Measurable h := hh.1.measurable
  -- normalized parameters
  set η' : ℝ := min η (1 / 10)
  set ν' : ℝ := min ν 1
  set M' : ℝ := max M 0
  have hη' : 0 < η' := lt_min hη (by norm_num)
  have hν' : 0 < ν' := lt_min hν one_pos
  have hν'1 : ν' ≤ 1 := min_le_right _ _
  have hM' : 0 ≤ M' := le_max_right _ _
  -- the closeness threshold
  set σ : ℝ := Real.log (1 + ν' / (4 * (M' + 1))) / ξ with hσdef
  have hσ : 0 < σ := div_pos (Real.log_pos (by
    have : 0 < ν' / (4 * (M' + 1)) := by positivity
    linarith)) hξ
  have he : Real.exp (|(ξ : ℝ)| * σ) = 1 + ν' / (4 * (M' + 1)) := by
    rw [abs_of_pos hξ, hσdef, mul_div_cancel₀ _ hξ.ne', Real.exp_log (by positivity)]
  have hσ2 : Real.exp (|(ξ : ℝ)| * σ) ≤ 2 := by
    rw [he]
    have : ν' / (4 * (M' + 1)) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith
    linarith
  have hσν : (Real.exp (|(ξ : ℝ)| * σ) - 1) * (M' + 1) ≤ ν' / 4 := by
    rw [he, add_sub_cancel_left, div_mul_eq_mul_div, mul_comm 4 (M' + 1), ← div_div,
      mul_div_cancel_right₀ _ (by positivity : M' + 1 ≠ 0)]
  -- canonical heat versions
  have hver : ∀ ε : Set.Ioi (0 : ℝ), ∃ Y : Ω → C(ℂ, ℝ),
      (∀ᵐ ω ∂P, ∀ z : ℂ, Y ω z = heatMollify (ε : ℝ) (h ω) z) ∧ IsHeatSmoothing P h ε Y :=
    fun ε => exists_heatVersion hh (ε : ℝ) ε.2
  choose X hXeq hX using hver
  -- Lemma 3.2 for `X_δ`, error `ν'/2`, height `2M'`
  have hL32 := lemma_3_2 ξ Q hQ D hD m hm hDlim P h hh X hX (2 * M') η' (ν' / 2) hη'
    (by positivity)
  obtain ⟨r₁, hr₁, hr₁P⟩ := exists_pos_of_eventually_comap
    (hL32.eventually (eventually_le_nhds (ENNReal.ofReal_pos.2 (half_pos hθ))))
  -- the approximation events
  have happrox := eventually_measure_approxFailure_le (P := P) hhm
    (fun z hz => by
      rw [mem_closedBall, dist_zero_right]
      exact hz.2.le) hA hσ (half_pos hθ)
  obtain ⟨r₂, hr₂, hr₂P⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 happrox
  refine ⟨min r₁ r₂, lt_min hr₁ hr₂, fun δ hδ hδ₀ L hL => ?_⟩
  set δ' : Set.Ioi (0 : ℝ) := ⟨δ, hδ.1⟩
  have hP1 := hr₁P δ' (lt_of_lt_of_le hδ₀ (min_le_left _ _))
  have hP2 := hr₂P ⟨hδ.1, lt_of_lt_of_le hδ₀ (min_le_right _ _)⟩ hδ L hL
  set N : Set Ω := {ω | ¬ ∀ z : ℂ, X δ' ω z = heatMollify δ (h ω) z}
  have hN : P N = 0 := by
    rw [← ae_iff]
    exact hXeq δ'
  have hsub : {ω | ¬ Lemma32Event (D (h ω)) (locMetric (ξ : ℝ) m δ L hδ (h ω)) η ν M} ⊆
      {ω | ¬ Lemma32Event (D (h ω)) (B2.Median.lfppMetric (ξ : ℝ) (m δ') (X δ' ω)) η' (ν' / 2)
        (2 * M')} ∪ approxFailure h δ hδ L σ ∪ N := by
    intro ω hω
    by_contra hnot
    simp only [mem_union, not_or, mem_ofPred_eq, not_not, N] at hnot
    obtain ⟨⟨hE, hAω⟩, hXω⟩ := hnot
    apply hω
    have hclose := abs_sub_le_of_not_mem_approxFailure hAω (X δ' ω) hXω
    have hT := lemma32Event_transfer (ξ := (ξ : ℝ)) (m δ') (φ := X δ' ω)
      (ψ := B2.Polylog.plMollifyC (Field.uniformLocalizationExponent δ L) δ hδ (h ω))
      hν' hν'1 hM' hσ.le hσ2 hσν hclose hE
    exact hT.mono (min_le_left _ _) (min_le_left _ _) (le_max_left _ _)
  calc P {ω | ¬ Lemma32Event (D (h ω)) (locMetric (ξ : ℝ) m δ L hδ (h ω)) η ν M}
      ≤ P ({ω | ¬ Lemma32Event (D (h ω)) (B2.Median.lfppMetric (ξ : ℝ) (m δ') (X δ' ω)) η'
          (ν' / 2) (2 * M')} ∪ approxFailure h δ hδ L σ ∪ N) := measure_mono hsub
    _ ≤ P {ω | ¬ Lemma32Event (D (h ω)) (B2.Median.lfppMetric (ξ : ℝ) (m δ') (X δ' ω)) η'
          (ν' / 2) (2 * M')} + P (approxFailure h δ hδ L σ) + P N := by
        refine (measure_union_le _ _).trans ?_
        gcongr
        exact measure_union_le _ _
    _ ≤ ENNReal.ofReal (θ / 2) + ENNReal.ofReal (θ / 2) + 0 := by
        rw [hN]
        gcongr
    _ = ENNReal.ofReal θ := by
        rw [add_zero, ← ENNReal.ofReal_add (by positivity) (by positivity), add_halves]

end SupercriticalLFPPAS.Local
