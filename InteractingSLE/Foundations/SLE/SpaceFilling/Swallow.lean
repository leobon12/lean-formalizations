import InteractingSLE.Foundations.SLE.SpaceFilling.SwallowBoundary
import InteractingSLE.Foundations.SLE.SpaceFilling.SwallowBessel

/-!
# [RS05, Lemma 7.3] for `4 < κ < 8`

Packet `planning/packets/PROVE-RS05-74b.md`; completes `planning/handoffs/PROVE-RS05-74.md` (R1)
for `4 < κ < 8`. Source: S. Rohde, O. Schramm, *Basic properties of SLE*, Ann. Math. 161 (2005),
Lemma 7.3 (pinned `source/external/RS05/arxiv-latex/SLEcont.tex`, lines 2304–2340).

* `exists_measure_hullContainsHalfBall_ne_zero_of_lt_eight`: positivity, `∃ t₀ > 0`,
  `P(K_{t₀} ⊇ ℍ ∩ B(0, ε) for some ε > 0) ≠ 0`.
* `ae_forall_sleHull_halfBall_of_lt_eight`: **[RS05, Lemma 7.3] for `4 < κ < 8`**, in the
  specification's form (almost surely, for every `t > 0`, `K_t` contains a half-neighbourhood
  of `0`), from positivity and the zero-one law `ae_forall_sleHull_halfBall_of_measure_ne_zero`.

## Proof of positivity (the route of [RS05], with the cluster set replaced by a monotone angle)

1. A.s. the real point `1` is swallowed at a time `τ < ∞` (`ae_exists_realSwallowAt`).
2. At `τ`, points `z ∈ ℍ \ K_τ` near `0` are sent by `f_τ` to real part in `[−R, −δ]`
   (`exists_re_fwdMap_mem_of_realSwallowAt`), and the same holds at every time `t₁` shortly after
   `τ` (`exists_clusterCond_of_realSwallowAt`); take `t₁` rational.
3. By the Markov property at the deterministic time `t₁`, the future driver is a Brownian motion
   independent of the past; with positive probability it swallows an interval `[a, b] ⊇ [−R, −δ]`
   (`b < 0`) at once (`exists_measurableSet_realSwallowAt_pair`, reflected).
4. On both events, `K_{t₁ + σ}` contains a half-neighbourhood of `0`
   (`hullContainsHalfBall_of_clusterCond`).

The event of step 2 is replaced by a countable condition on tamed flows (`ClusterCondQ`), which
is measurable for the driving past (`measurableSet_clusterCondQ`).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open QuantumZipper QuantumZipper.RS

namespace InteractingSLE

/-! ### Dependence on the driver on `[0, ∞)` only -/

section Congr

variable {V₁ V₂ : ℝ → ℝ}

theorem isForwardSol_congr_drive (h : ∀ t, 0 ≤ t → V₁ t = V₂ t) {z : ℂ} {T : ℝ}
    {u : ℝ → ℂ} : IsForwardSol V₁ z T u ↔ IsForwardSol V₂ z T u := by
  unfold IsForwardSol
  refine and_congr Iff.rfl (forall₂_congr fun t ht => ?_)
  rw [h t ht.1]

theorem fwdHull_congr_drive (h : ∀ t, 0 ≤ t → V₁ t = V₂ t) (T : ℝ) :
    fwdHull V₁ T = fwdHull V₂ T := by
  have hs : ∀ z, swallowTime V₁ z = swallowTime V₂ z := fun z => by
    unfold swallowTime
    congr 2
    ext T'
    simp only [mem_ofPred_eq, isForwardSol_congr_drive h]
  ext z
  simp only [fwdHull, mem_ofPred_eq, hs]

theorem realSwallowAt_congr_drive (h : ∀ t, 0 ≤ t → V₁ t = V₂ t) {x σ : ℝ} :
    RealSwallowAt V₁ x σ ↔ RealSwallowAt V₂ x σ := by
  simp only [RealSwallowAt, isForwardSol_congr_drive h]

theorem isLoewnerTrace_congr_drive (h : ∀ t, 0 ≤ t → V₁ t = V₂ t) {η : ℝ → ℂ} :
    IsLoewnerTrace V₁ η ↔ IsLoewnerTrace V₂ η := by
  simp only [IsLoewnerTrace, fwdHull_congr_drive h]

end Congr

/-! ### The cluster condition and its countable tamed form -/

section Cluster

variable {W : ℝ → ℝ}

/-- **The cluster condition** at time `t₁`: every `z ∈ ℍ \ K_{t₁}` with `‖z‖ < ε` has
`Re f_{t₁}(z) ∈ [−R, −δ]`. -/
def ClusterCond (W : ℝ → ℝ) (t₁ ε R δ : ℝ) : Prop :=
  ∀ z ∈ H \ fwdHull W t₁, ‖z‖ < ε → -R ≤ (fwdMap W t₁ z).re ∧ (fwdMap W t₁ z).re ≤ -δ

/-- **Countable tamed form of the cluster condition**, tested on the points of a dense sequence
with QuantumZipper's tamed flows at levels `1/(k + 1)` (measurable in the driving past). -/
def ClusterCondQ (W : ℝ → ℝ) (t₁ ε R δ : ℝ) : Prop :=
  ∀ m k : ℕ, TopologicalSpace.denseSeq ℂ m ∈ H → ‖TopologicalSpace.denseSeq ℂ m‖ < ε →
    TopologicalSpace.denseSeq ℂ m ∉ fwdHull W t₁ →
    (∀ q : ℚ, 0 ≤ (q : ℝ) → (q : ℝ) ≤ t₁ →
      1 / ((k : ℝ) + 1) ≤ (tamedZ W (1 / ((k : ℝ) + 1)) (TopologicalSpace.denseSeq ℂ m) q).im) →
    1 / ((k : ℝ) + 1) ≤ (tamedZ W (1 / ((k : ℝ) + 1)) (TopologicalSpace.denseSeq ℂ m) t₁).im →
    -R ≤ (tamedZ W (1 / ((k : ℝ) + 1)) (TopologicalSpace.denseSeq ℂ m) t₁).re ∧
      (tamedZ W (1 / ((k : ℝ) + 1)) (TopologicalSpace.denseSeq ℂ m) t₁).re ≤ -δ

/-- A continuous function that is `≥ c` at the rationals of `[0, t₁)` and at `t₁` is `≥ c` on
`[0, t₁]`. -/
theorem ge_of_ge_rat {f : ℝ → ℝ} {t₁ c : ℝ} (ht₁ : 0 ≤ t₁) (hf : ContinuousOn f (Icc 0 t₁))
    (hq : ∀ q : ℚ, 0 ≤ (q : ℝ) → (q : ℝ) ≤ t₁ → c ≤ f q) (hend : c ≤ f t₁) :
    ∀ t ∈ Icc (0 : ℝ) t₁, c ≤ f t := by
  rcases ht₁.eq_or_lt with h0 | hpos
  · intro t ht
    have : t = t₁ := le_antisymm (ht.2) (h0 ▸ ht.1)
    rw [this]; exact hend
  have hS : IsClosed (Icc (0 : ℝ) t₁ ∩ f ⁻¹' Ici c) :=
    hf.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have hsub : Ioo (0 : ℝ) t₁ ∩ range ((↑) : ℚ → ℝ) ⊆ Icc (0 : ℝ) t₁ ∩ f ⁻¹' Ici c := by
    rintro t ⟨ht, q, rfl⟩
    exact ⟨Ioo_subset_Icc_self ht, hq q ht.1.le ht.2.le⟩
  have hcl : Icc (0 : ℝ) t₁ ⊆ closure (Ioo (0 : ℝ) t₁ ∩ range ((↑) : ℚ → ℝ)) := by
    rw [← closure_Ioo hpos.ne]
    exact closure_minimal (Rat.denseRange_cast.open_subset_closure_inter isOpen_Ioo)
      isClosed_closure
  intro t ht
  exact (closure_minimal hsub hS (hcl ht)).2

/-- The true cluster condition (open bounds) gives the countable tamed one. -/
theorem clusterCondQ_of_forall (hW : Continuous W) {t₁ ε R δ : ℝ} (ht₁ : 0 ≤ t₁)
    (h : ∀ z ∈ H \ fwdHull W t₁, ‖z‖ < ε → -R < (fwdMap W t₁ z).re ∧ (fwdMap W t₁ z).re < -δ) :
    ClusterCondQ W t₁ ε R δ := by
  intro m k hmH hmε hmK hq hend
  set c := 1 / ((k : ℝ) + 1) with hcdef
  have hc : 0 < c := by positivity
  set z := TopologicalSpace.denseSeq ℂ m with hzdef
  have him : ∀ t ∈ Icc (0 : ℝ) t₁, c ≤ (tamedZ W c z t).im :=
    ge_of_ge_rat ht₁ (Complex.continuous_im.comp_continuousOn (continuousOn_tamedZ hW hc ht₁ z))
      hq hend
  obtain ⟨-, heq⟩ := fwdMap_eq_tamedZ hW hc ht₁ hmH him
  have h1 := h z ⟨hmH, hmK⟩ hmε
  rw [heq t₁ ⟨ht₁, le_rfl⟩] at h1
  exact ⟨h1.1.le, h1.2.le⟩

/-- The countable tamed cluster condition gives the true one (closed bounds): approximate
`z ∈ ℍ \ K_{t₁}` by points of the dense sequence, where the tamed flow is the true flow
(`QuantumZipper.tamedZ_eq_fwdMap`), and use the continuity of `f_{t₁}` on `ℍ \ K_{t₁}`. -/
theorem clusterCond_of_clusterCondQ (hW : Continuous W) {t₁ ε R δ : ℝ} (ht₁ : 0 ≤ t₁)
    (h : ClusterCondQ W t₁ ε R δ) : ClusterCond W t₁ ε R δ := by
  intro z hz hzε
  set O := H \ fwdHull W t₁ with hOdef
  have hO : IsOpen O := FwdHolo.isOpen_compl_fwdHull hW ht₁
  have hfc : ContinuousOn (fwdMap W t₁) O := (FwdHolo.differentiableOn_fwdMap hW ht₁).continuousOn
  set w₀ := fwdMap W t₁ z with hw₀
  have hw₀H : 0 < w₀.im := FwdHolo.mapsTo_fwdMap hW ht₁ hz
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt (half_pos hw₀H)
  set c := 1 / ((k : ℝ) + 1) with hcdef
  have hc : 0 < c := by positivity
  -- a bound valid up to an arbitrary error `ρ`
  have key : ∀ ρ > 0, ρ < w₀.im / 2 → -R - ρ ≤ w₀.re ∧ w₀.re ≤ -δ + ρ := by
    intro ρ hρ hρw
    have hU : IsOpen (O ∩ Metric.ball 0 ε ∩ (O ∩ fwdMap W t₁ ⁻¹' Metric.ball w₀ ρ)) :=
      (hO.inter Metric.isOpen_ball).inter (hfc.isOpen_inter_preimage hO Metric.isOpen_ball)
    obtain ⟨m, hm⟩ := (TopologicalSpace.denseRange_denseSeq ℂ).exists_mem_open hU
      ⟨z, ⟨hz, by rwa [Metric.mem_ball, dist_zero_right]⟩, hz, by
        rw [mem_preimage, Metric.mem_ball, ← hw₀, dist_self]; exact hρ⟩
    obtain ⟨⟨hdO, hdε⟩, -, hdw⟩ := hm
    set d := TopologicalSpace.denseSeq ℂ m with hddef
    rw [Metric.mem_ball, dist_zero_right] at hdε
    simp only [mem_preimage, Metric.mem_ball, dist_eq_norm] at hdw
    have hdim : w₀.im - ρ < (fwdMap W t₁ d).im := by
      have := Complex.abs_im_le_norm (fwdMap W t₁ d - w₀)
      rw [Complex.sub_im] at this
      linarith [(abs_lt.1 (this.trans_lt hdw)).1]
    obtain ⟨u, hu⟩ := exists_isForwardSol_of_not_mem_fwdHull ht₁ hdO.1 hdO.2
    have hanti := (im_isForwardSol_le hW hdO.1 hu).1
    have himd : ∀ t ∈ Icc (0 : ℝ) t₁, c ≤ (fwdMap W t d).im := by
      intro t ht
      rw [fwdMap_eq hW hdO.1 hu ht]
      have h1 := hanti ht ⟨ht₁, le_rfl⟩ ht.2
      simp only at h1
      rw [← fwdMap_eq hW hdO.1 hu ⟨ht₁, le_rfl⟩] at h1
      linarith
    have htz := tamedZ_eq_fwdMap hW hc ht₁ hdO.1 ⟨u, hu⟩ himd
    have hh := h m k hdO.1 hdε hdO.2
      (fun q hq0 hqt => by rw [htz q ⟨hq0, hqt⟩]; exact himd q ⟨hq0, hqt⟩)
      (by rw [htz t₁ ⟨ht₁, le_rfl⟩]; exact himd t₁ ⟨ht₁, le_rfl⟩)
    rw [htz t₁ ⟨ht₁, le_rfl⟩] at hh
    have hre := Complex.abs_re_le_norm (fwdMap W t₁ d - w₀)
    rw [Complex.sub_re] at hre
    have := abs_le.1 (hre.trans hdw.le)
    constructor <;> linarith [hh.1, hh.2, this.1, this.2]
  constructor
  · refine le_of_forall_pos_lt_add fun e he => ?_
    have := key (min (e / 2) (w₀.im / 4)) (by positivity) (by
      have := min_le_right (e / 2) (w₀.im / 4); linarith)
    linarith [min_le_left (e / 2) (w₀.im / 4)]
  · refine le_of_forall_pos_lt_add fun e he => ?_
    have := key (min (e / 2) (w₀.im / 4)) (by positivity) (by
      have := min_le_right (e / 2) (w₀.im / 4); linarith)
    linarith [min_le_left (e / 2) (w₀.im / 4)]

/-- **Measurability of the countable cluster condition** for every σ-algebra making the driving
coordinates `B r`, `r ≤ t₁`, measurable. -/
theorem measurableSet_clusterCondQ {Ω : Type*} {m : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ}
    (hBc : ∀ ω, Continuous fun t => B t ω) (κ : ℝ) {t₁ : ℝ} (ht₁ : 0 ≤ t₁)
    (hBm : ∀ r : ℝ≥0, (r : ℝ) ≤ t₁ → Measurable[m] (B r)) (ε R δ : ℝ) :
    MeasurableSet[m] {ω | ClusterCondQ (drive κ B ω) t₁ ε R δ} := by
  have htz : ∀ (k : ℕ) (z : ℂ) (t : ℝ), 0 ≤ t → t ≤ t₁ →
      Measurable[m] fun ω => tamedZ (drive κ B ω) (1 / ((k : ℝ) + 1)) z t := by
    intro k z t ht0 htt
    have h := (@measurable_tamed_drive Ω m κ (1 / ((k : ℝ) + 1)) (by positivity) B hBc t ht0
      fun r hr => hBm r (hr.trans htt)).1
    exact h.comp measurable_prodMk_left
  have e : {ω | ClusterCondQ (drive κ B ω) t₁ ε R δ} = ⋂ (n : ℕ) (k : ℕ),
      ({ω | TopologicalSpace.denseSeq ℂ n ∈ H → ‖TopologicalSpace.denseSeq ℂ n‖ < ε →
        TopologicalSpace.denseSeq ℂ n ∉ fwdHull (drive κ B ω) t₁ →
        (∀ q : ℚ, 0 ≤ (q : ℝ) → (q : ℝ) ≤ t₁ → 1 / ((k : ℝ) + 1) ≤
          (tamedZ (drive κ B ω) (1 / ((k : ℝ) + 1)) (TopologicalSpace.denseSeq ℂ n) q).im) →
        1 / ((k : ℝ) + 1) ≤
          (tamedZ (drive κ B ω) (1 / ((k : ℝ) + 1)) (TopologicalSpace.denseSeq ℂ n) t₁).im →
        -R ≤ (tamedZ (drive κ B ω) (1 / ((k : ℝ) + 1)) (TopologicalSpace.denseSeq ℂ n) t₁).re ∧
          (tamedZ (drive κ B ω) (1 / ((k : ℝ) + 1)) (TopologicalSpace.denseSeq ℂ n) t₁).re ≤
            -δ}) := by
    ext ω
    simp only [ClusterCondQ, mem_ofPred_eq, mem_iInter]
  rw [e]
  refine MeasurableSet.iInter fun n => MeasurableSet.iInter fun k => ?_
  set z := TopologicalSpace.denseSeq ℂ n
  by_cases hzH : z ∈ H
  · by_cases hzε : ‖z‖ < ε
    · have hK := measurableSet_mem_fwdHull_drive (m := m) hBc κ ht₁ hBm z
      have hq : MeasurableSet[m] {ω | ∀ q : ℚ, 0 ≤ (q : ℝ) → (q : ℝ) ≤ t₁ →
          1 / ((k : ℝ) + 1) ≤ (tamedZ (drive κ B ω) (1 / ((k : ℝ) + 1)) z q).im} := by
        simp only [ofPred_forall]
        exact MeasurableSet.iInter fun q => MeasurableSet.iInter fun hq0 =>
          MeasurableSet.iInter fun hqt => measurableSet_le measurable_const
            (Complex.measurable_im.comp (htz k z q hq0 hqt))
      have hend : MeasurableSet[m] {ω | 1 / ((k : ℝ) + 1) ≤
          (tamedZ (drive κ B ω) (1 / ((k : ℝ) + 1)) z t₁).im} :=
        measurableSet_le measurable_const (Complex.measurable_im.comp (htz k z t₁ ht₁ le_rfl))
      have hconc : MeasurableSet[m] {ω |
          -R ≤ (tamedZ (drive κ B ω) (1 / ((k : ℝ) + 1)) z t₁).re ∧
            (tamedZ (drive κ B ω) (1 / ((k : ℝ) + 1)) z t₁).re ≤ -δ} :=
        (measurableSet_le measurable_const (Complex.measurable_re.comp
          (htz k z t₁ ht₁ le_rfl))).inter (measurableSet_le (Complex.measurable_re.comp
            (htz k z t₁ ht₁ le_rfl)) measurable_const)
      have e2 : {ω | z ∈ H → ‖z‖ < ε → z ∉ fwdHull (drive κ B ω) t₁ →
          (∀ q : ℚ, 0 ≤ (q : ℝ) → (q : ℝ) ≤ t₁ → 1 / ((k : ℝ) + 1) ≤
            (tamedZ (drive κ B ω) (1 / ((k : ℝ) + 1)) z q).im) →
          1 / ((k : ℝ) + 1) ≤ (tamedZ (drive κ B ω) (1 / ((k : ℝ) + 1)) z t₁).im →
          -R ≤ (tamedZ (drive κ B ω) (1 / ((k : ℝ) + 1)) z t₁).re ∧
            (tamedZ (drive κ B ω) (1 / ((k : ℝ) + 1)) z t₁).re ≤ -δ} =
          {ω | z ∈ fwdHull (drive κ B ω) t₁} ∪ ({ω | ∀ q : ℚ, 0 ≤ (q : ℝ) → (q : ℝ) ≤ t₁ →
            1 / ((k : ℝ) + 1) ≤ (tamedZ (drive κ B ω) (1 / ((k : ℝ) + 1)) z q).im}ᶜ ∪
          ({ω | 1 / ((k : ℝ) + 1) ≤ (tamedZ (drive κ B ω) (1 / ((k : ℝ) + 1)) z t₁).im}ᶜ ∪
          {ω | -R ≤ (tamedZ (drive κ B ω) (1 / ((k : ℝ) + 1)) z t₁).re ∧
            (tamedZ (drive κ B ω) (1 / ((k : ℝ) + 1)) z t₁).re ≤ -δ})) := by
        ext ω
        simp only [mem_ofPred_eq, mem_union, mem_compl_iff, hzH, hzε, true_imp_iff]
        tauto
      rw [e2]
      exact hK.union (hq.compl.union (hend.compl.union hconc))
    · simp [hzε]
  · simp [hzH]

end Cluster

/-! ### Choice of rational parameters -/

/-- **Rational parameters of the cluster condition.** If the real point `1` is swallowed at `τ`,
there are rationals `t₁ > 0`, `ε > 0`, `0 < δ < R` with the countable cluster condition at `t₁`. -/
theorem exists_rat_clusterCondQ {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {η : ℝ → ℂ}
    (hη : IsLoewnerTrace W η) {τ : ℝ} (hsw : RealSwallowAt W 1 τ) :
    ∃ p : ℚ × ℚ × ℚ × ℚ, (0 : ℝ) < p.1 ∧ (0 : ℝ) < p.2.1 ∧ (0 : ℝ) < p.2.2.2 ∧
      (p.2.2.2 : ℝ) < p.2.2.1 ∧ ClusterCondQ W p.1 p.2.1 p.2.2.1 p.2.2.2 := by
  obtain ⟨r₀, hr₀, ε, hε, δ, hδ, R, hR, hcl⟩ :=
    exists_clusterCond_of_realSwallowAt hη hW hW0 one_pos hsw
  obtain ⟨t₁, ht₁a, ht₁b⟩ := exists_rat_btwn (show τ < τ + r₀ by linarith)
  obtain ⟨ε', hε'a, hε'b⟩ := exists_rat_btwn hε
  obtain ⟨δ', hδ'a, hδ'b⟩ := exists_rat_btwn hδ
  obtain ⟨R', hR'⟩ := exists_rat_gt (max R δ)
  have hτ := hsw.1
  refine ⟨(t₁, ε', R', δ'), by simp only; linarith, hε'a, hδ'a,
    by simp only; linarith [le_max_right R δ], ?_⟩
  refine clusterCondQ_of_forall hW (by simp only; linarith) fun z hz hzn => ?_
  have h := hcl t₁ ⟨by linarith, ht₁b.le⟩ z hz (hzn.trans hε'b)
  constructor <;> linarith [le_max_left R δ, h.1, h.2]

/-! ### Positivity and Lemma 7.3 -/

section Positivity

/-- The reflected form of `exists_measurableSet_realSwallowAt_pair`: an interval `[a, b]` with
`b < 0` is swallowed at once with positive probability. -/
theorem exists_measurableSet_realSwallowAt_pair_neg {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (hBm : ∀ r, Measurable (B r))
    (hBc : ∀ ω, Continuous (B · ω)) (hB0 : ∀ ω, B 0 ω = 0) {κ : ℝ} (hκ : 4 < κ) (hκ8 : κ < 8)
    {a b : ℝ} (hab : a < b) (hb : b < 0) :
    ∃ E : Set Ω,
      MeasurableSet[MeasurableSpace.comap (fun ω (r : ℝ≥0) => B r ω) MeasurableSpace.pi] E ∧
      0 < P E ∧ ∀ᵐ ω ∂P, ω ∈ E →
        ∃ σ, RealSwallowAt (drive κ B ω) a σ ∧ RealSwallowAt (drive κ B ω) b σ := by
  obtain ⟨E, hEm, hEP, hE⟩ := exists_measurableSet_realSwallowAt_pair hB.neg
    (fun r => (hBm r).neg) (fun ω => (hBc ω).neg) (fun ω => by simp [hB0 ω]) hκ hκ8
    (x := -b) (y := -a) (by linarith) (by linarith)
  refine ⟨E, ?_, hEP, ?_⟩
  · obtain ⟨S, hS, rfl⟩ := hEm
    exact ⟨(fun f : ℝ≥0 → ℝ => fun r => -f r) ⁻¹' S, measurable_neg hS, rfl⟩
  · filter_upwards [hE] with ω hω hωE
    obtain ⟨σ, h1, h2⟩ := hω hωE
    have hdrive : drive κ (-B) ω = fun t => -drive κ B ω t := by
      funext t; simp [drive]
    rw [hdrive] at h1 h2
    exact ⟨σ, realSwallowAt_neg_iff.1 h2, realSwallowAt_neg_iff.1 h1⟩

/-- For `κ < 8` the SLE trace is a continuous Loewner trace of the driver, almost surely
(QuantumZipper's `rohdeSchrammTraceGen_of_lt_eight`, `isLoewnerTrace_of_forall_bound`). -/
theorem ae_isLoewnerTrace_of_lt_eight {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) {κ : ℝ} (hκ : 0 < κ)
    (hκ8 : κ < 8) : ∀ᵐ ω ∂P, IsLoewnerTrace (drive κ B ω) (sleTrace κ B ω) := by
  filter_upwards [rohdeSchrammTraceGen_of_lt_eight hκ hκ8 P B hB] with ω ⟨h0, hc, hg⟩
  exact isLoewnerTrace_of_forall_bound h0 hc hg

/-- **Positivity in [RS05, Lemma 7.3] for `4 < κ < 8`**, for a Brownian motion with measurable
coordinates, continuous paths and `B 0 = 0` everywhere, on a probability space in `Type`. -/
theorem exists_measure_hullContainsHalfBall_ne_zero_of_good {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (hBm : ∀ r, Measurable (B r))
    (hBc : ∀ ω, Continuous (B · ω)) (hB0 : ∀ ω, B 0 ω = 0) {κ : ℝ} (hκ : 4 < κ) (hκ8 : κ < 8) :
    ∃ t₀ > (0 : ℝ), P {ω | HullContainsHalfBall (drive κ B ω) t₀} ≠ 0 := by
  have hP : IsProbabilityMeasure P := hB.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  have hκ0 : 0 < κ := by linarith
  -- steps 1–2: rational parameters of the cluster condition, with positive probability
  set A : ℚ × ℚ × ℚ × ℚ → Set Ω := fun p =>
    {ω | ClusterCondQ (drive κ B ω) p.1 p.2.1 p.2.2.1 p.2.2.2} with hAdef
  set Good : ℚ × ℚ × ℚ × ℚ → Prop := fun p => (0 : ℝ) < p.1 ∧ (0 : ℝ) < p.2.1 ∧
      (0 : ℝ) < p.2.2.2 ∧ (p.2.2.2 : ℝ) < p.2.2.1 with hGooddef
  have hgood : ∀ᵐ ω ∂P, ω ∈ ⋃ p, ⋃ (_ : Good p), A p := by
    filter_upwards [ae_isLoewnerTrace_of_lt_eight hB hκ0 hκ8,
      ae_exists_realSwallowAt hB hBm hBc hB0 hκ one_pos] with ω hη ⟨τ, hτ⟩
    obtain ⟨p, h1, h2, h3, h4, h5⟩ := exists_rat_clusterCondQ (drive_continuous (hBc ω))
      (by simp [drive, hB0 ω]) hη hτ
    exact mem_iUnion₂.2 ⟨p, ⟨h1, h2, h3, h4⟩, h5⟩
  obtain ⟨p, hp, hpA⟩ : ∃ p, Good p ∧ P (A p) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hnull : P (⋃ p, ⋃ (_ : Good p), A p) = 0 :=
      measure_iUnion_null fun p => measure_iUnion_null fun hp => hcon p hp
    have hc : P (⋃ p, ⋃ (_ : Good p), A p)ᶜ = 0 := by
      rw [ae_iff] at hgood; exact hgood
    have h1 := measure_univ_le_add_compl (μ := P) (⋃ p, ⋃ (_ : Good p), A p)
    rw [hnull, hc, measure_univ, add_zero] at h1
    exact absurd h1 (by simp)
  obtain ⟨ht₁, hε, hδ, hδR⟩ := hp
  set t₁ : ℝ := (p.1 : ℝ) with ht₁def
  set ε : ℝ := (p.2.1 : ℝ) with hεdef
  set R : ℝ := (p.2.2.1 : ℝ) with hRdef
  set δ : ℝ := (p.2.2.2 : ℝ) with hδdef
  -- step 3: the future after the deterministic time `t₁`
  set s : ℝ≥0 := t₁.toNNReal with hsdef
  have hs : (s : ℝ) = t₁ := Real.coe_toNNReal _ ht₁.le
  obtain ⟨hB', hind, hdrive⟩ := isBrownianReal_shift_indep hB κ s
  set B' : ℝ≥0 → Ω → ℝ := fun u ω => B (s + u) ω - B s ω with hB'def
  have hB'm : ∀ r, Measurable (B' r) := fun r => (hBm _).sub (hBm _)
  have hB'c : ∀ ω, Continuous (B' · ω) := fun ω =>
    ((hBc ω).comp (continuous_const.add continuous_id)).sub continuous_const
  have hB'0 : ∀ ω, B' 0 ω = 0 := fun ω => by simp [hB'def]
  obtain ⟨E, hEm, hEP, hE⟩ := exists_measurableSet_realSwallowAt_pair_neg hB' hB'm hB'c hB'0 hκ
    hκ8 (a := -R - 1) (b := -δ / 4) (by linarith) (by linarith)
  have hApast : MeasurableSet[MeasurableSpace.comap (fun ω (r : Set.Iic s) => B r ω)
      MeasurableSpace.pi] (A p) := by
    refine measurableSet_clusterCondQ hBc κ ht₁.le (fun r hr => ?_) ε R δ
    have hrs : r ≤ s := by rw [← NNReal.coe_le_coe, hs]; exact hr
    have hproj : Measurable fun f : Set.Iic s → ℝ => f ⟨r, hrs⟩ := measurable_pi_apply _
    exact hproj.comp (comap_measurable (fun ω (r : Set.Iic s) => B r ω))
  have hindep : P (A p ∩ E) = P (A p) * P E := by
    obtain ⟨SA, hSA, hSAe⟩ := hApast
    obtain ⟨SE, hSE, hSEe⟩ := hEm
    rw [← hSAe, ← hSEe, inter_comm, hind.measure_inter_preimage_eq_mul _ _ hSE hSA, mul_comm]
  have hpos : P (A p ∩ E) ≠ 0 := by
    rw [hindep]; exact mul_ne_zero hpA hEP.ne'
  -- step 4: on `A ∩ E`, the half-ball event holds at some time
  have hgoodω : ∀ᵐ ω ∂P, ω ∈ A p ∩ E →
      ∃ n : ℕ, HullContainsHalfBall (drive κ B ω) ((n : ℝ) + 1) := by
    filter_upwards [ae_isLoewnerTrace_of_lt_eight hB hκ0 hκ8,
      ae_isLoewnerTrace_of_lt_eight hB' hκ0 hκ8, hE] with ω hη hη' hEω hω
    obtain ⟨hωA, hωE⟩ := hω
    obtain ⟨σ, hsa, hsb⟩ := hEω hωE
    set W := drive κ B ω with hWdef
    have hW : Continuous W := drive_continuous (hBc ω)
    have hW0 : W 0 = 0 := by simp [hWdef, drive, hB0 ω]
    have hagree : ∀ u, 0 ≤ u → drive κ B' ω u = shiftDrive W t₁ u := fun u hu => by
      rw [← hs]; exact hdrive ω u hu
    have hη'' := (isLoewnerTrace_congr_drive hagree).1 hη'
    have hsa' := (realSwallowAt_congr_drive hagree).1 hsa
    have hsb' := (realSwallowAt_congr_drive hagree).1 hsb
    have hcl := clusterCond_of_clusterCondQ hW ht₁.le hωA
    have hcl' : ∀ z ∈ H \ fwdHull W t₁, ‖z‖ < ε →
        -(R + 1 / 2) < (fwdMap W t₁ z).re ∧ (fwdMap W t₁ z).re < -(δ / 2) := fun z hz hzn => by
      have h := hcl z hz hzn
      constructor <;> linarith [h.1, h.2]
    have hHB := hullContainsHalfBall_of_clusterCond hW hW0 hη ht₁.le hη'' hε hcl'
      (a := -R - 1) (b := -δ / 4) (by linarith) (by linarith) (by linarith) hsa' hsb'
    refine ⟨⌈t₁ + σ⌉₊, hHB.mono ?_⟩
    linarith [Nat.le_ceil (t₁ + σ)]
  have hU : P (⋃ n : ℕ, {ω | HullContainsHalfBall (drive κ B ω) ((n : ℝ) + 1)}) ≠ 0 := by
    intro h0
    refine hpos (measure_mono_null_ae ?_ h0)
    filter_upwards [hgoodω] with ω h hω
    obtain ⟨n, hn⟩ := h hω
    exact mem_iUnion.2 ⟨n, hn⟩
  obtain ⟨n, hn⟩ : ∃ n : ℕ, P {ω | HullContainsHalfBall (drive κ B ω) ((n : ℝ) + 1)} ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hU (measure_iUnion_null hcon)
  exact ⟨(n : ℝ) + 1, by positivity, hn⟩

end Positivity

/-- **Positivity in [RS05, Lemma 7.3] for `4 < κ < 8`**, for every Brownian motion (on a
probability space in any universe): for some `t₀ > 0`, with positive probability `K_{t₀}`
contains a half-neighbourhood of `0`. Transfer through the canonical path space
(`exists_measure_hullContainsHalfBall_ne_zero_of`). -/
theorem exists_measure_hullContainsHalfBall_ne_zero_of_lt_eight {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) {κ : ℝ} (hκ : 4 < κ)
    (hκ8 : κ < 8) : ∃ t₀ > (0 : ℝ), P {ω | HullContainsHalfBall (drive κ B ω) t₀} ≠ 0 := by
  have hP : IsProbabilityMeasure P := hB.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  obtain ⟨G0, hG0m, hG0c, -, hG0br, -⟩ := exists_good_version0 hB
  have hm := measurable_toCPath hG0m hG0c
  have hcan : IsBrownianReal canonBM (P.map (toCPath G0 hG0c)) :=
    isBrownianReal_canonBM hG0br.toIsPreBrownianReal hG0m hG0c
  obtain ⟨G1, hG1m, hG1c, hG10, hG1br, -⟩ := exists_good_version0 hcan
  exact exists_measure_hullContainsHalfBall_ne_zero_of hG1br hB
    (exists_measure_hullContainsHalfBall_ne_zero_of_good hG1br hG1m hG1c hG10 hκ hκ8)

/-- **[RS05, Lemma 7.3] for `4 < κ < 8`** (the specification's form, simultaneously for all
`t > 0`): almost surely, for every `t > 0`, the SLE_κ hull `K_t` contains an upper
half-neighbourhood `{z ∈ ℍ : |z| < ε}` of the starting point `0`. -/
theorem ae_forall_sleHull_halfBall_of_lt_eight {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) {κ : ℝ} (hκ : 4 < κ) (hκ8 : κ < 8) :
    ∀ᵐ ω ∂P, ∀ t > (0 : ℝ), ∃ ε > (0 : ℝ), ∀ z ∈ H, ‖z‖ < ε → z ∈ sleHull κ B ω t :=
  ae_forall_sleHull_halfBall_of_measure_ne_zero hB κ
    (exists_measure_hullContainsHalfBall_ne_zero_of_lt_eight hB hκ hκ8)

end InteractingSLE
