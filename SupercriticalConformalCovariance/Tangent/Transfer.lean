import QuantumZipper.Proofs.Section5.TVLocal
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Topology.Metrizable.Uniformity
import Mathlib.Topology.UnitInterval

/-!
# Lemma 3.3, steps 3 and 7: transfer of a measurable functional under total variation

Paper l. 218–221 (maximal coupling plus Lemma 3.1) and l. 231–236 (the joint-law identification:
"the transformed field is the deterministic affine transform `h^a` of the original field. The
metric is a measurable functional of that field"). The functional is only measurable, not
continuous, so convergence of the fields alone identifies nothing; what makes the printed argument
work is that the convergence of the normalized transformed fields to `h^a` holds **both** almost
surely on the original space (GM Lemma 2.4 (2.5), deterministic) **and** in total variation
(GM (2.6)). The following measure-theoretic lemma is the rigorous content of the two steps
together (source gap `domain-measurable-functional`):

> `X_n → Y` almost surely in a pseudometrizable space `E`, `TV(law X_n, law Y) → 0`, and
> `Φ : E → L` Borel with `L` compact metric. Then `Φ(X_n) → Φ(Y)` in probability.

Proof: approximate each bounded coordinate `min(dist(Φ ·, t_m), 1)` in `L¹(law Y)` by a bounded
continuous function (Mathlib, weak regularity); total variation controls the error under
`law X_n`, and dominated convergence the continuous part; a finite net of the compact `L` finishes.
No coupling and no Lusin theorem are needed.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal
open QuantumZipper.TV

namespace SupercriticalConformalCovariance.Tangent

variable {Ω E : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  [TopologicalSpace E] [TopologicalSpace.PseudoMetrizableSpace E] [MeasurableSpace E]
  [BorelSpace E]

theorem measurable_abs_sub {α : Type*} [MeasurableSpace α] {f g : α → ℝ} (hf : Measurable f)
    (hg : Measurable g) : Measurable fun x => |f x - g x| :=
  continuous_abs.measurable.comp (hf.sub hg)

/-- Clamp to `[-1, 1]`. -/
def clamp1 (t : ℝ) : ℝ := (projIcc (-1 : ℝ) 1 (by norm_num) t : ℝ)

theorem continuous_clamp1 : Continuous clamp1 :=
  continuous_subtype_val.comp continuous_projIcc

theorem abs_clamp1_le (t : ℝ) : |clamp1 t| ≤ 1 := by
  have h := (projIcc (-1 : ℝ) 1 (by norm_num) t).2
  exact abs_le.2 ⟨h.1, h.2⟩

theorem abs_clamp1_sub_le (s t : ℝ) : |clamp1 s - clamp1 t| ≤ |s - t| :=
  Set.abs_projIcc_sub_projIcc _

theorem clamp1_of_abs_le {t : ℝ} (ht : |t| ≤ 1) : clamp1 t = t := by
  unfold clamp1
  rw [projIcc_of_mem _ ⟨(abs_le.1 ht).1, (abs_le.1 ht).2⟩]

/-- **Step 1.** A bounded measurable real observable of `X_n` converges in `L¹` to the same
observable of `Y`, when `X_n → Y` a.s. and in total variation. -/
theorem tendsto_integral_abs_sub_of_tvDist {φ : E → ℝ} (hφ : Measurable φ)
    (hφb : ∀ x, |φ x| ≤ 1) {X : ℕ → Ω → E} {Y : Ω → E} (hX : ∀ n, Measurable (X n))
    (hY : Measurable Y) (hXY : ∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop (𝓝 (Y ω)))
    (hTV : Tendsto (fun n => tvDist (P.map (X n)) (P.map Y)) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω, |φ (X n ω) - φ (Y ω)| ∂P) atTop (𝓝 0) := by
  set μ : Measure E := P.map Y with hμ
  have hφi : ∀ ν : Measure E, IsFiniteMeasure ν → Integrable φ ν := fun ν _ =>
    Integrable.of_bound hφ.aestronglyMeasurable 1 (Eventually.of_forall fun x => by
      simpa [Real.norm_eq_abs] using hφb x)
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- bounded continuous approximation in `L¹(μ)`, then clamped to `[-1, 1]`
  obtain ⟨g, hg, -⟩ := (hφi μ inferInstance).exists_boundedContinuous_integral_sub_le
    (by positivity : (0 : ℝ) < ε / 4)
  set g' : E → ℝ := fun x => clamp1 (g x) with hg'
  have hg'c : Continuous g' := continuous_clamp1.comp g.continuous
  have hg'm : Measurable g' := hg'c.measurable
  have hg'b : ∀ x, |g' x| ≤ 1 := fun x => abs_clamp1_le _
  have hcl : ∀ x, |φ x - g' x| ≤ |φ x - g x| := by
    intro x
    have := abs_clamp1_sub_le (φ x) (g x)
    rwa [clamp1_of_abs_le (hφb x)] at this
  set k : E → ℝ := fun x => |φ x - g' x| with hk
  have hkm : Measurable k := measurable_abs_sub hφ hg'm
  have hkb : ∀ x, |k x| ≤ 2 := by
    intro x
    rw [abs_abs]
    calc |φ x - g' x| ≤ |φ x| + |g' x| := abs_sub _ _
      _ ≤ 2 := by linarith [hφb x, hg'b x]
  have hki : ∀ ν : Measure E, IsFiniteMeasure ν → Integrable k ν := fun ν _ =>
    Integrable.of_bound hkm.aestronglyMeasurable 2 (Eventually.of_forall fun x => by
      simpa [Real.norm_eq_abs] using hkb x)
  have hkμ : ∫ x, k x ∂μ ≤ ε / 4 :=
    calc ∫ x, k x ∂μ ≤ ∫ x, ‖φ x - g x‖ ∂μ :=
          integral_mono (hki μ inferInstance) ((hφi μ inferInstance).sub
            (Integrable.of_bound g.continuous.aestronglyMeasurable ‖g‖
              (Eventually.of_forall fun x => g.norm_coe_le_norm x))).norm
            fun x => by simpa [Real.norm_eq_abs] using hcl x
      _ ≤ ε / 4 := hg
  -- total variation controls `∫ k` under the law of `X n`
  have hkTV : ∀ n, ∫ x, k x ∂(P.map (X n)) ≤ ε / 4 + 4 * (tvDist (P.map (X n)) μ).toReal := by
    intro n
    have h := abs_integral_sub_le (μ := P.map (X n)) (ν := μ) (g := fun x => k x / 2)
      (hkm.div_const 2) (fun x => by rw [abs_div]; norm_num; linarith [hkb x])
    rw [integral_div, integral_div] at h
    have := (abs_le.1 h).2
    linarith
  -- dominated convergence for the continuous part
  have hcont : Tendsto (fun n => ∫ ω, |g' (X n ω) - g' (Y ω)| ∂P) atTop (𝓝 0) := by
    have := tendsto_integral_of_dominated_convergence (μ := P) (fun _ => (2 : ℝ))
      (F := fun n ω => |g' (X n ω) - g' (Y ω)|) (f := fun _ => (0 : ℝ))
      (fun n => (measurable_abs_sub (hg'm.comp (hX n)) (hg'm.comp hY)).aestronglyMeasurable)
      (integrable_const _) (fun n => Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_abs]
        calc |g' (X n ω) - g' (Y ω)| ≤ |g' (X n ω)| + |g' (Y ω)| := abs_sub _ _
          _ ≤ 2 := by linarith [hg'b (X n ω), hg'b (Y ω)])
      (hXY.mono fun ω hω => by
        have h := ((hg'c.tendsto (Y ω)).comp hω).sub_const (g' (Y ω))
        simpa using h.abs)
    simpa using this
  have hTV' : Tendsto (fun n => (tvDist (P.map (X n)) μ).toReal) atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hTV
    simpa [Function.comp_def] using this
  obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.1 hcont (ε / 4) (by positivity)
  obtain ⟨N₂, hN₂⟩ := Metric.tendsto_atTop.1 hTV' (ε / 16) (by positivity)
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  have h1 := hN₁ n (le_of_max_le_left hn)
  have h2 := hN₂ n (le_of_max_le_right hn)
  rw [Real.dist_eq, sub_zero] at h1 h2
  have hint : ∀ n, Integrable (fun ω => |φ (X n ω) - φ (Y ω)|) P := fun n =>
    Integrable.of_bound (measurable_abs_sub (hφ.comp (hX n)) (hφ.comp hY)).aestronglyMeasurable 2
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_abs]
        calc |φ (X n ω) - φ (Y ω)| ≤ |φ (X n ω)| + |φ (Y ω)| := abs_sub _ _
          _ ≤ 2 := by linarith [hφb (X n ω), hφb (Y ω)])
  have hnn : 0 ≤ ∫ ω, |φ (X n ω) - φ (Y ω)| ∂P := integral_nonneg fun _ => abs_nonneg _
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn]
  -- the three-term bound
  have hkX : ∫ ω, k (X n ω) ∂P = ∫ x, k x ∂(P.map (X n)) :=
    (integral_map (hX n).aemeasurable hkm.aestronglyMeasurable).symm
  have hkY : ∫ ω, k (Y ω) ∂P = ∫ x, k x ∂μ :=
    (integral_map hY.aemeasurable hkm.aestronglyMeasurable).symm
  have hkXi : Integrable (fun ω => k (X n ω)) P :=
    (hki _ inferInstance).comp_measurable (hX n)
  have hkYi : Integrable (fun ω => k (Y ω)) P := (hki _ inferInstance).comp_measurable hY
  have hgi : Integrable (fun ω => |g' (X n ω) - g' (Y ω)|) P :=
    Integrable.of_bound (measurable_abs_sub (hg'm.comp (hX n)) (hg'm.comp hY)).aestronglyMeasurable 2
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_abs]
        calc |g' (X n ω) - g' (Y ω)| ≤ |g' (X n ω)| + |g' (Y ω)| := abs_sub _ _
          _ ≤ 2 := by linarith [hg'b (X n ω), hg'b (Y ω)])
  have hpt : ∀ ω, |φ (X n ω) - φ (Y ω)| ≤
      k (X n ω) + |g' (X n ω) - g' (Y ω)| + k (Y ω) := by
    intro ω
    simp only [hk]
    calc |φ (X n ω) - φ (Y ω)|
        = |(φ (X n ω) - g' (X n ω)) + (g' (X n ω) - g' (Y ω)) - (φ (Y ω) - g' (Y ω))| := by
          ring_nf
      _ ≤ |φ (X n ω) - g' (X n ω)| + |g' (X n ω) - g' (Y ω)| + |φ (Y ω) - g' (Y ω)| := by
          refine (abs_sub _ _).trans ?_
          gcongr
          exact abs_add_le _ _
  have hle : ∫ ω, |φ (X n ω) - φ (Y ω)| ∂P ≤
      ∫ ω, k (X n ω) ∂P + ∫ ω, |g' (X n ω) - g' (Y ω)| ∂P + ∫ ω, k (Y ω) ∂P := by
    calc ∫ ω, |φ (X n ω) - φ (Y ω)| ∂P
        ≤ ∫ ω, (k (X n ω) + |g' (X n ω) - g' (Y ω)| + k (Y ω)) ∂P :=
          integral_mono (hint n) ((hkXi.add hgi).add hkYi) hpt
      _ = ∫ ω, (k (X n ω) + |g' (X n ω) - g' (Y ω)|) ∂P + ∫ ω, k (Y ω) ∂P :=
          integral_add (hkXi.add hgi) hkYi
      _ = _ := by rw [integral_add hkXi hgi]
  have hTVn := hkTV n
  have habs1 : |∫ ω, |g' (X n ω) - g' (Y ω)| ∂P| = ∫ ω, |g' (X n ω) - g' (Y ω)| ∂P :=
    abs_of_nonneg (integral_nonneg fun _ => abs_nonneg _)
  have habs2 : |(tvDist (P.map (X n)) μ).toReal| = (tvDist (P.map (X n)) μ).toReal :=
    abs_of_nonneg ENNReal.toReal_nonneg
  rw [habs1] at h1
  rw [habs2] at h2
  rw [hkX, hkY] at hle
  linarith

/-- **Step 2: the transfer lemma.** If `X_n → Y` almost surely and in total variation, then for
every Borel map `Φ` into a compact metric space, `Φ(X_n) → Φ(Y)` in probability. -/
theorem tendstoInMeasure_comp_of_tvDist {L : Type*} [MetricSpace L] [CompactSpace L]
    [MeasurableSpace L] [BorelSpace L] {Φ : E → L} (hΦ : Measurable Φ)
    {X : ℕ → Ω → E} {Y : Ω → E} (hX : ∀ n, Measurable (X n)) (hY : Measurable Y)
    (hXY : ∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop (𝓝 (Y ω)))
    (hTV : Tendsto (fun n => tvDist (P.map (X n)) (P.map Y)) atTop (𝓝 0)) :
    TendstoInMeasure P (fun n ω => Φ (X n ω)) atTop (fun ω => Φ (Y ω)) := by
  intro η hη
  -- a real radius `r ∈ (0, 1/2)` with `3 r ≤ η`
  obtain ⟨r, hr0, hr1, hrη⟩ : ∃ r : ℝ, 0 < r ∧ r < 1 / 2 ∧ ENNReal.ofReal (3 * r) ≤ η := by
    rcases eq_or_ne η ⊤ with h | h
    · exact ⟨1 / 4, by norm_num, by norm_num, h ▸ le_top⟩
    · refine ⟨min (η.toReal / 3) (1 / 4), lt_min (by
        have := ENNReal.toReal_pos hη.ne' h; positivity) (by norm_num),
        (min_le_right _ _).trans_lt (by norm_num), ?_⟩
      calc ENNReal.ofReal (3 * min (η.toReal / 3) (1 / 4))
          ≤ ENNReal.ofReal (3 * (η.toReal / 3)) := by
            gcongr; exact min_le_left _ _
        _ = η := by rw [mul_div_cancel₀ _ (by norm_num : (3 : ℝ) ≠ 0), ENNReal.ofReal_toReal h]
  -- a finite `r`-net of `L`
  obtain ⟨t, -, htf, hcov⟩ := finite_cover_balls_of_compact (isCompact_univ : IsCompact
    (univ : Set L)) hr0
  set φ : L → E → ℝ := fun m x => min (dist (Φ x) m) 1 with hφdef
  have hφm : ∀ m, Measurable (φ m) := fun m =>
    ((continuous_id.dist continuous_const).measurable.comp hΦ).min measurable_const
  have hφb : ∀ m x, |φ m x| ≤ 1 := fun m x => by
    rw [abs_of_nonneg (le_min dist_nonneg zero_le_one)]
    exact min_le_right _ _
  -- the set inclusion
  have hsub : ∀ n, {ω | η ≤ edist (Φ (X n ω)) (Φ (Y ω))} ⊆
      ⋃ m ∈ htf.toFinset, {ω | r ≤ |φ m (X n ω) - φ m (Y ω)|} := by
    intro n ω hω
    have hd : 3 * r ≤ dist (Φ (X n ω)) (Φ (Y ω)) := by
      have h3 : ENNReal.ofReal (3 * r) ≤ edist (Φ (X n ω)) (Φ (Y ω)) := hrη.trans hω
      rw [edist_dist] at h3
      exact (ENNReal.ofReal_le_ofReal_iff dist_nonneg).1 h3
    obtain ⟨m, hm, hYm⟩ := mem_iUnion₂.1 (hcov (mem_univ (Φ (Y ω))))
    refine mem_iUnion₂.2 ⟨m, htf.mem_toFinset.2 hm, ?_⟩
    have hYm' : dist (Φ (Y ω)) m < r := mem_ball.1 hYm
    have hXm : 2 * r ≤ dist (Φ (X n ω)) m := by
      have := dist_triangle (Φ (X n ω)) m (Φ (Y ω))
      rw [dist_comm m] at this
      linarith
    have hφX : 2 * r ≤ φ m (X n ω) := le_min hXm (by linarith)
    have hφY : φ m (Y ω) < r := (min_le_left _ _).trans_lt hYm'
    show r ≤ |φ m (X n ω) - φ m (Y ω)|
    rw [abs_of_nonneg (by linarith)]
    linarith
  -- Markov for each coordinate
  have hmark : ∀ m, Tendsto (fun n => P {ω | r ≤ |φ m (X n ω) - φ m (Y ω)|}) atTop (𝓝 0) := by
    intro m
    have hL1 := tendsto_integral_abs_sub_of_tvDist (hφm m) (hφb m) hX hY hXY hTV
    have hbound : ∀ n, P {ω | r ≤ |φ m (X n ω) - φ m (Y ω)|} ≤
        ENNReal.ofReal ((∫ ω, |φ m (X n ω) - φ m (Y ω)| ∂P) / r) := by
      intro n
      have hint : Integrable (fun ω => |φ m (X n ω) - φ m (Y ω)|) P :=
        Integrable.of_bound (measurable_abs_sub ((hφm m).comp (hX n)) ((hφm m).comp hY)).aestronglyMeasurable
          2 (Eventually.of_forall fun ω => by
            rw [Real.norm_eq_abs, abs_abs]
            calc |φ m (X n ω) - φ m (Y ω)| ≤ |φ m (X n ω)| + |φ m (Y ω)| := abs_sub _ _
              _ ≤ 2 := by linarith [hφb m (X n ω), hφb m (Y ω)])
      have h := mul_meas_ge_le_integral_of_nonneg
        (Eventually.of_forall fun ω => abs_nonneg (φ m (X n ω) - φ m (Y ω)) :
          (0 : Ω → ℝ) ≤ᵐ[P] fun ω => |φ m (X n ω) - φ m (Y ω)|) hint r
      rw [measureReal_def] at h
      rw [ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (by
        have := integral_nonneg (μ := P) (f := fun ω => |φ m (X n ω) - φ m (Y ω)|)
          fun ω => abs_nonneg (φ m (X n ω) - φ m (Y ω))
        positivity)]
      rw [le_div_iff₀ hr0, mul_comm]
      exact h
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_
      (fun _ => zero_le) hbound
    have h0 : Tendsto (fun n => (∫ ω, |φ m (X n ω) - φ m (Y ω)| ∂P) / r) atTop (𝓝 0) := by
      simpa using hL1.div_const r
    have := (ENNReal.continuous_ofReal.tendsto 0).comp h0
    simpa [Function.comp_def] using this
  -- finite union bound
  have hsum : Tendsto (fun n => ∑ m ∈ htf.toFinset, P {ω | r ≤ |φ m (X n ω) - φ m (Y ω)|})
      atTop (𝓝 0) := by
    simpa using tendsto_finsetSum htf.toFinset fun m _ => hmark m
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => zero_le) fun n => ?_
  exact (measure_mono (hsub n)).trans (measure_biUnion_finset_le _ _)

/-- **The transfer lemma, topological form.** For a compact metrizable target, every subsequence
of `Φ(X_n)` has a further subsequence converging to `Φ(Y)` almost surely. -/
theorem exists_subseq_ae_tendsto_comp_of_tvDist {L : Type*} [TopologicalSpace L]
    [CompactSpace L] [TopologicalSpace.MetrizableSpace L] [MeasurableSpace L] [BorelSpace L]
    {Φ : E → L} (hΦ : Measurable Φ) {X : ℕ → Ω → E} {Y : Ω → E} (hX : ∀ n, Measurable (X n))
    (hY : Measurable Y) (hXY : ∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop (𝓝 (Y ω)))
    (hTV : Tendsto (fun n => tvDist (P.map (X n)) (P.map Y)) atTop (𝓝 0))
    (ns : ℕ → ℕ) (hns : StrictMono ns) :
    ∃ ms : ℕ → ℕ, StrictMono ms ∧
      ∀ᵐ ω ∂P, Tendsto (fun k => Φ (X (ns (ms k)) ω)) atTop (𝓝 (Φ (Y ω))) := by
  let _ : MetricSpace L := TopologicalSpace.metrizableSpaceMetric L
  have h := tendstoInMeasure_comp_of_tvDist (P := P) hΦ (fun n => hX (ns n)) hY
    (hXY.mono fun ω hω => hω.comp hns.tendsto_atTop) (hTV.comp hns.tendsto_atTop)
  exact h.exists_seq_tendsto_ae

end SupercriticalConformalCovariance.Tangent
