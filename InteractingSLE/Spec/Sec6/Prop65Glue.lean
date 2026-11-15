/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec6.Prop65Point

/-!
# Proposition 6.5, part 4: the continuous local martingale at a fixed point

Packet PROVE-SEC6-B (specification §6.1, `source/spec/p145-192.md`, `#prop-6.5`, pp. 157–159).

The localized versions of `Prop65Point` (levels `c_n = 1/(n+1)`, horizons `R_n = n`) are glued on an
almost sure event `Ω₀ ∈ 𝓕₀` on which they agree on overlaps (they are continuous and agree at a
countable dense set of times). The glued process `M` is continuous on the lifetime `{t : r_t(z) > 0}`,
is a modification of `H_t(z) − H_0(z)` there, and the hitting times `τ_n` of the levels `c_n` (capped at
`n`) form a localizing sequence exhausting the lifetime along which `M^{τ_n}` and
`(M^{τ_n})² − (log r_0(z) − log r_{·∧τ_n}(z))` are martingales: `M` is a continuous local martingale on
the lifetime with quadratic variation `a_t(z) = log r_0(z) − log r_t(z)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric Complex
open scoped ENNReal NNReal

namespace InteractingSLE.Sec6.Prop65

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}

/-! ### Martingale algebra -/

/-- A martingale multiplied by an `𝓕₀`-measurable factor (with integrable products) is a martingale. -/
theorem martingale_mul_left_of_measurable {f : ℝ≥0 → Ω → ℝ} (hf : Martingale f 𝓕 P)
    {Y : Ω → ℝ} (hY : StronglyMeasurable[𝓕 0] Y) (hYf : ∀ t, Integrable (fun ω => Y ω * f t ω) P) :
    Martingale (fun t ω => Y ω * f t ω) 𝓕 P := by
  refine ⟨fun t => (hY.mono (𝓕.mono (zero_le (a := t)))).mul (hf.stronglyAdapted t),
    fun s t hst => ?_⟩
  have h1 := condExp_mul_of_stronglyMeasurable_left (m := 𝓕 s) (μ := P) (f := Y) (g := f t)
    (hY.mono (𝓕.mono (zero_le (a := s)))) (hYf t) (hf.integrable t)
  filter_upwards [h1, hf.condExp_ae_eq hst] with ω h1 h2
  change (P[Y * f t | 𝓕 s]) ω = Y ω * f s ω
  rw [h1, Pi.mul_apply, h2]

/-- An `𝓕₀`-indicator times a martingale is a martingale. -/
theorem martingale_indicator_of_measurable {f : ℝ≥0 → Ω → ℝ} (hf : Martingale f 𝓕 P)
    {E : Set Ω} (hE : MeasurableSet[𝓕 0] E) : Martingale (fun t => E.indicator (f t)) 𝓕 P := by
  have hY : StronglyMeasurable[𝓕 0] (E.indicator fun _ => (1 : ℝ)) :=
    stronglyMeasurable_const.indicator hE
  have := martingale_mul_left_of_measurable hf hY fun t =>
    ((hf.integrable t).indicator (𝓕.le 0 _ hE)).congr (Eventually.of_forall fun ω => by
      by_cases hω : ω ∈ E <;> simp [hω])
  refine this.congr (fun t => (hf.stronglyAdapted t).indicator (𝓕.mono (zero_le (a := t)) _ hE))
    fun t => Eventually.of_forall fun ω => ?_
  by_cases hω : ω ∈ E <;> simp [hω]

/-- An adapted process that vanishes almost surely at each time is a martingale. -/
theorem martingale_of_ae_eq_zero {f : ℝ≥0 → Ω → ℝ} (hf : StronglyAdapted 𝓕 f)
    (h0 : ∀ t, f t =ᵐ[P] 0) : Martingale f 𝓕 P :=
  (martingale_zero ℝ 𝓕 P).congr hf fun t => (h0 t).symm

/-! ### The localized family -/

/-- The levels `c_n = 1/(n+1)`. -/
def lev (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

lemma lev_pos (n : ℕ) : 0 < lev n := by unfold lev; positivity

lemma lev_anti {n k : ℕ} (hnk : n ≤ k) : lev k ≤ lev n := by
  unfold lev
  gcongr

lemma exists_lev_lt {x : ℝ} (hx : 0 < x) : ∃ n : ℕ, lev n < x := by
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hx
  exact ⟨n, hn⟩

open QuantumZipper (H zeroGFFTestCov)
open LQGMetric (DistOn TestOn)

namespace Setting

variable {h : Ω → DistOn upperHalfPlaneOpens} {F : ℂ → ℝ} {Z : ℝ≥0 → Ω → Set ℂ}
  {Hc : ℝ≥0 → Ω → ℂ → ℝ} {r : ℝ≥0 → Ω → ℂ → ℝ}

/-- The localizing times `ρ_n`: the first time `r_t(z) ≤ 1/(n+1)`, capped at `n`. -/
def rhoN (r : ℝ≥0 → Ω → ℂ → ℝ) (z : ℂ) (n : ℕ) : Ω → ℝ≥0 := locTime r z (lev n) n

/-- The events `G_n = {r₀(z) > 1/(n+1)}`. -/
def evN (r : ℝ≥0 → Ω → ℂ → ℝ) (z : ℂ) (n : ℕ) : Set Ω := startEv r z (lev n)

omit mΩ in
theorem evN_mono {r : ℝ≥0 → Ω → ℂ → ℝ} {z : ℂ} {n k : ℕ} (hnk : n ≤ k) :
    evN r z n ⊆ evN r z k := fun _ hω => (lev_anti hnk).trans_lt hω

theorem rhoN_mono (S : Setting P 𝓕 h F Z Hc r) {z : ℂ} (hz : 0 < z.im) {n k : ℕ} (hnk : n ≤ k)
    (ω : Ω) : rhoN r z n ω ≤ rhoN r z k ω :=
  hitLe_mono (fun ω => S.radius_cont ω z hz) (lev_anti hnk) (by exact_mod_cast hnk) ω

theorem measurable_rhoN (S : Setting P 𝓕 h F Z Hc r) {z : ℂ} (hz : 0 < z.im) (n : ℕ) :
    Measurable (rhoN r z n) := by
  have := (S.isStoppingTime_locTime hz (lev n) n).measurable'
  exact (WithTop.measurable_untopD 0).comp this

/-- **Exhaustion of the lifetime**: if `r_t(z) > 0`, then `ω ∈ G_n` and `t < ρ_n` for some `n`. -/
theorem exists_lt_rhoN (S : Setting P 𝓕 h F Z Hc r) {z : ℂ} (hz : 0 < z.im) {t : ℝ≥0} {ω : Ω}
    (hr : 0 < r t ω z) : ∃ n, ω ∈ evN r z n ∧ t < rhoN r z n ω := by
  have hcont := S.radius_cont ω z hz
  -- positivity up to `t`
  have hpos : ∀ s ≤ t, 0 < r s ω z := fun s hs =>
    S.r_pos hz fun hzZ => S.notMem_of_r_pos hr (S.mono ω hs hzZ)
  -- and a little beyond
  obtain ⟨δ, hδ, hδr⟩ : ∃ δ > (0 : ℝ≥0), ∀ s, t ≤ s → s ≤ t + δ → 0 < r s ω z := by
    have := (hcont.tendsto t).eventually (lt_mem_nhds (half_lt_self hr))
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 this
    refine ⟨(ε / 2).toNNReal, by simpa using hε, fun s hts hsδ => ?_⟩
    have hd : dist s t < ε := by
      rw [NNReal.dist_eq, abs_of_nonneg (sub_nonneg.2 (NNReal.coe_le_coe.2 hts))]
      have : (s : ℝ) ≤ t + (ε / 2) := by
        have := NNReal.coe_le_coe.2 hsδ
        rw [NNReal.coe_add, Real.coe_toNNReal _ (by linarith)] at this
        exact this
      linarith
    have := hball hd
    have h2 : 0 < r t ω z / 2 := by linarith
    linarith
  set t₁ := t + δ
  have hpos₁ : ∀ s ≤ t₁, 0 < r s ω z := fun s hs => by
    rcases le_total s t with h | h
    · exact hpos s h
    · exact hδr s h hs
  -- the minimum on `[0, t₁]`
  obtain ⟨s₀, hs₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 (zero_le (a := t₁)))
    hcont.continuousOn
  have hm : 0 < r s₀ ω z := hpos₁ s₀ hs₀.2
  obtain ⟨n₁, hn₁⟩ := exists_lev_lt hm
  obtain ⟨n₂, hn₂⟩ := exists_nat_ge (t₁ : ℝ)
  refine ⟨max n₁ n₂, ?_, ?_⟩
  · exact (lev_anti (le_max_left _ _)).trans_lt (hn₁.trans_le (hmin ⟨le_rfl, zero_le⟩))
  · have hle : t₁ ≤ rhoN r z (max n₁ n₂) ω := by
      refine le_hitLe_of_forall (fun ω => S.radius_cont ω z hz) ?_ fun s hs => ?_
      · have : (t₁ : ℝ) ≤ (max n₁ n₂ : ℕ) := hn₂.trans (by exact_mod_cast le_max_right _ _)
        exact_mod_cast this
      · exact (lev_anti (le_max_left _ _)).trans_lt (hn₁.trans_le (hmin ⟨zero_le, hs⟩))
    exact (lt_add_of_pos_right t hδ).trans_le hle

/-- A countable dense set of times. -/
def denseTimes : Set ℝ≥0 := (TopologicalSpace.exists_countable_dense ℝ≥0).choose

lemma countable_denseTimes : denseTimes.Countable :=
  (TopologicalSpace.exists_countable_dense ℝ≥0).choose_spec.1

lemma dense_denseTimes : Dense denseTimes :=
  (TopologicalSpace.exists_countable_dense ℝ≥0).choose_spec.2

section Family

variable [IsProbabilityMeasure P] (S : Setting P 𝓕 h F Z Hc r)
  (hnull : ∀ s, MeasurableSet s → P s = 0 → MeasurableSet[𝓕 0] s) {z : ℂ} (hz : 0 < z.im)

/-- The localized continuous versions at the levels `1/(n+1)`. -/
def locM (n : ℕ) : ℝ≥0 → Ω → ℝ :=
  (S.exists_local_version hnull hz (lev_pos n) (n : ℝ≥0)).choose

theorem locM_spec (n : ℕ) :
    (∀ ω, Continuous fun t => S.locM hnull hz n t ω) ∧ (∀ t, Measurable (S.locM hnull hz n t)) ∧
      (∀ ω t, rhoN r z n ω ≤ t → S.locM hnull hz n t ω = S.locM hnull hz n (rhoN r z n ω) ω) ∧
      (∀ (σ : Ω → ℝ≥0) (_hσ : IsStoppingTime 𝓕 fun ω => (σ ω : WithTop ℝ≥0)),
        (∀ ω, σ ω ≤ rhoN r z n ω) →
          (fun ω => S.locM hnull hz n (σ ω) ω) =ᵐ[P] (evN r z n).indicator (fun ω => Hc (σ ω) ω z)) ∧
      Martingale (S.locM hnull hz n) 𝓕 P ∧
      Martingale (fun t ω => S.locM hnull hz n t ω ^ 2 +
        varV (evN r z n) r hz (lev_pos n) (min t (rhoN r z n ω)) ω) 𝓕 P :=
  (S.exists_local_version hnull hz (lev_pos n) (n : ℝ≥0)).choose_spec

theorem measurable_locM_at (n : ℕ) {σ : Ω → ℝ≥0} (hσ : Measurable σ) :
    Measurable fun ω => S.locM hnull hz n (σ ω) ω := by
  have hj : Measurable (Function.uncurry (S.locM hnull hz n)) :=
    measurable_uncurry_of_continuous_of_measurable (S.locM_spec hnull hz n).1
      (S.locM_spec hnull hz n).2.1
  exact hj.comp (hσ.prodMk measurable_id)

/-- The event on which the localized versions agree on their common time ranges (at the dense times). -/
def consSet : Set Ω :=
  {ω | ∀ n k, n ≤ k → ω ∈ evN r z n → ∀ q ∈ denseTimes,
    S.locM hnull hz k (min q (rhoN r z n ω)) ω = S.locM hnull hz n (min q (rhoN r z n ω)) ω}

theorem measurableSet_consSet : MeasurableSet (S.consSet hnull hz) := by
  have e : S.consSet hnull hz = ⋂ n : ℕ, ⋂ k : ℕ, ⋂ (_ : n ≤ k), ⋂ q : denseTimes,
      ((evN r z n)ᶜ ∪ {ω | S.locM hnull hz k (min (q : ℝ≥0) (rhoN r z n ω)) ω =
        S.locM hnull hz n (min (q : ℝ≥0) (rhoN r z n ω)) ω}) := by
    ext ω
    simp only [consSet, mem_ofPred_eq, mem_iInter, mem_union, mem_compl_iff, Subtype.forall]
    constructor
    · intro h n k hnk q hq
      by_cases hG : ω ∈ evN r z n
      · exact Or.inr (h n k hnk hG q hq)
      · exact Or.inl hG
    · intro h n k hnk hG q hq
      exact (h n k hnk q hq).resolve_left (not_not.2 hG)
  rw [e]
  have : Countable denseTimes := countable_denseTimes.to_subtype
  refine MeasurableSet.iInter fun n => MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ =>
    MeasurableSet.iInter fun q => ?_
  refine (𝓕.le 0 _ (S.measurableSet_startEv hz (lev n))).compl.union ?_
  have hσ : Measurable fun ω => min (q : ℝ≥0) (rhoN r z n ω) :=
    measurable_const.min (S.measurable_rhoN hz n)
  exact measurableSet_eq_fun (S.measurable_locM_at hnull hz k hσ) (S.measurable_locM_at hnull hz n hσ)

theorem ae_mem_consSet : ∀ᵐ ω ∂P, ω ∈ S.consSet hnull hz := by
  have : Countable denseTimes := countable_denseTimes.to_subtype
  have h : ∀ n k : ℕ, ∀ q : denseTimes, ∀ᵐ ω ∂P, n ≤ k → ω ∈ evN r z n →
      S.locM hnull hz k (min (q : ℝ≥0) (rhoN r z n ω)) ω =
        S.locM hnull hz n (min (q : ℝ≥0) (rhoN r z n ω)) ω := by
    intro n k q
    by_cases hnk : n ≤ k
    · have hσ : IsStoppingTime 𝓕 fun ω => ((min (q : ℝ≥0) (rhoN r z n ω) : ℝ≥0) : WithTop ℝ≥0) :=
        isStoppingTime_min_coe (S := fun _ => (q : ℝ≥0)) (isStoppingTime_const 𝓕 _)
          (S.isStoppingTime_locTime hz (lev n) n)
      have h1 := (S.locM_spec hnull hz k).2.2.2.1 _ hσ fun ω =>
        (min_le_right _ _).trans (S.rhoN_mono hz hnk ω)
      have h2 := (S.locM_spec hnull hz n).2.2.2.1 _ hσ fun ω => min_le_right _ _
      filter_upwards [h1, h2] with ω h1 h2 _ hG
      rw [h1, h2, indicator_of_mem (evN_mono hnk hG), indicator_of_mem hG]
    · exact Eventually.of_forall fun ω h => absurd h hnk
  filter_upwards [ae_all_iff.2 fun n => ae_all_iff.2 fun k => ae_all_iff.2 fun q => h n k q]
    with ω hω n k hnk hG q hq
  exact hω n k ⟨q, hq⟩ hnk hG

theorem measurableSet_consSet_zero : MeasurableSet[𝓕 0] (S.consSet hnull hz) := by
  have h1 := hnull _ (S.measurableSet_consSet hnull hz).compl (ae_iff.1 (S.ae_mem_consSet hnull hz))
  simpa using h1.compl

/-- On the consistency event, the localized versions agree for all times. -/
theorem locM_eq_of_mem_consSet {ω : Ω} (hω : ω ∈ S.consSet hnull hz) {n k : ℕ} (hnk : n ≤ k)
    (hG : ω ∈ evN r z n) (t : ℝ≥0) :
    S.locM hnull hz k (min t (rhoN r z n ω)) ω = S.locM hnull hz n (min t (rhoN r z n ω)) ω := by
  have hc : ∀ m, Continuous fun t => S.locM hnull hz m (min t (rhoN r z n ω)) ω := fun m =>
    ((S.locM_spec hnull hz m).1 ω).comp (continuous_id.min continuous_const)
  have := Continuous.ext_on dense_denseTimes (hc k) (hc n) fun q hq => hω n k hnk hG q hq
  exact congrFun this t

/-- **The glued process.** -/
def glued (t : ℝ≥0) (ω : Ω) : ℝ :=
  (S.consSet hnull hz).indicator (fun ω => limsup (fun n => (evN r z n).indicator
    (fun ω => S.locM hnull hz n (min t (rhoN r z n ω)) ω - S.locM hnull hz n 0 ω) ω) atTop) ω

theorem glued_eq {ω : Ω} (hω : ω ∈ S.consSet hnull hz) {n : ℕ} (hG : ω ∈ evN r z n) {t : ℝ≥0}
    (ht : t ≤ rhoN r z n ω) :
    S.glued hnull hz t ω = S.locM hnull hz n t ω - S.locM hnull hz n 0 ω := by
  rw [glued, indicator_of_mem hω]
  have hev : (fun k => (evN r z k).indicator (fun ω => S.locM hnull hz k (min t (rhoN r z k ω)) ω -
      S.locM hnull hz k 0 ω) ω) =ᶠ[atTop]
      fun _ => S.locM hnull hz n t ω - S.locM hnull hz n 0 ω := by
    filter_upwards [eventually_ge_atTop n] with k hk
    rw [indicator_of_mem (evN_mono hk hG), min_eq_left (ht.trans (S.rhoN_mono hz hk ω))]
    have c1 := S.locM_eq_of_mem_consSet hnull hz hω hk hG t
    have c0 := S.locM_eq_of_mem_consSet hnull hz hω hk hG 0
    rw [min_eq_left ht] at c1
    rw [min_eq_left (zero_le (a := rhoN r z n ω))] at c0
    rw [c1, c0]
  rw [Filter.limsup_congr hev, limsup_const]

theorem glued_zero (ω : Ω) : S.glued hnull hz 0 ω = 0 := by
  by_cases hω : ω ∈ S.consSet hnull hz
  · rw [glued, indicator_of_mem hω]
    have : (fun k => (evN r z k).indicator (fun ω => S.locM hnull hz k (min 0 (rhoN r z k ω)) ω -
        S.locM hnull hz k 0 ω) ω) = fun _ => 0 := by
      funext k
      simp
    rw [this, limsup_const]
  · rw [glued, indicator_of_notMem hω]

omit [IsProbabilityMeasure P] in
/-- Off `G_n` the localizing time vanishes. -/
theorem rhoN_eq_zero (S : Setting P 𝓕 h F Z Hc r) {z : ℂ} (hz : 0 < z.im) {n : ℕ} {ω : Ω}
    (hG : ω ∉ evN r z n) : rhoN r z n ω = 0 :=
  hitLe_eq_zero (fun ω => S.radius_cont ω z hz) (not_lt.1 hG)

/-- The stopped glued process, explicitly. -/
theorem glued_stop (n : ℕ) (t : ℝ≥0) (ω : Ω) :
    S.glued hnull hz (min t (rhoN r z n ω)) ω = (S.consSet hnull hz ∩ evN r z n).indicator
      (fun ω => S.locM hnull hz n t ω - S.locM hnull hz n 0 ω) ω := by
  by_cases hω : ω ∈ S.consSet hnull hz
  · by_cases hG : ω ∈ evN r z n
    · rw [S.glued_eq hnull hz hω hG (min_le_right _ _), indicator_of_mem (mem_inter hω hG)]
      rcases le_total t (rhoN r z n ω) with h | h
      · rw [min_eq_left h]
      · rw [min_eq_right h, ← (S.locM_spec hnull hz n).2.2.1 ω t h]
    · rw [S.rhoN_eq_zero hz hG, min_eq_right (zero_le (a := t)), S.glued_zero hnull hz,
        indicator_of_notMem fun h => hG h.2]
  · rw [glued, indicator_of_notMem hω, indicator_of_notMem fun h => hω h.1]

theorem memLp_locM (n : ℕ) (t : ℝ≥0) : MemLp (S.locM hnull hz n t) 2 P := by
  have hi := ((S.locM_spec hnull hz n).2.2.2.2.2).integrable t
  have hv : Integrable (fun ω => varV (evN r z n) r hz (lev_pos n) (min t (rhoN r z n ω)) ω) P := by
    refine Integrable.of_bound ?_ (|varK hz (lev_pos n)|) (Eventually.of_forall fun ω => ?_)
    · exact (stronglyMeasurable_comp_stoppingTime (S.continuous_varV hz (lev_pos n))
        (S.measurable_varV (S.measurableSet_startEv hz (lev n)) hz (lev_pos n)) (isStoppingTime_min_coe (S := fun _ => t)
          (isStoppingTime_const 𝓕 t) (S.isStoppingTime_locTime hz (lev n) n))).aestronglyMeasurable.mono
          (IsStoppingTime.measurableSpace_le _)
    · have hcr : ω ∈ evN r z n → lev n ≤ r (min t (rhoN r z n ω)) ω z := fun hG =>
        S.le_r_of_le_locTime hz hG (min_le_right _ _)
      rw [Real.norm_eq_abs, abs_of_nonneg (S.varV_nonneg hz (lev_pos n) hcr)]
      exact (S.varV_le hz (lev_pos n) hcr).trans (le_abs_self _)
  have hsq : Integrable (fun ω => S.locM hnull hz n t ω ^ 2) P :=
    (hi.sub hv).congr (Eventually.of_forall fun ω => by simp)
  exact (memLp_two_iff_integrable_sq ((S.locM_spec hnull hz n).2.1 t).aestronglyMeasurable).2 hsq

end Family

/-- **Proposition 6.5, time part at a fixed point** (the continuous local martingale and its
quadratic variation). Let `z ∈ ℍ`. There is a process `M` with `M₀ = 0`, continuous on the lifetime
`{t : r_t(z) > 0}` for every `ω`, which is a modification of `H_t(z) − H_0(z)` on the lifetime, and
stopping times `τ_n` (nondecreasing, strictly inside the lifetime when `r₀(z) > 0`, exhausting it)
such that every stopped process `M^{τ_n}` is a continuous martingale and
`(M^{τ_n})² − (log r₀(z) − log r_{·∧τ_n}(z))` is a martingale. -/
theorem exists_localMartingale [IsProbabilityMeasure P] (S : Setting P 𝓕 h F Z Hc r)
    (hnull : ∀ s, MeasurableSet s → P s = 0 → MeasurableSet[𝓕 0] s) {z : ℂ} (hz : 0 < z.im) :
    ∃ M : ℝ≥0 → Ω → ℝ,
      (∀ ω, ContinuousOn (fun t => M t ω) {t | 0 < r t ω z}) ∧ (∀ ω, M 0 ω = 0) ∧
      (∀ t, ∀ᵐ ω ∂P, 0 < r t ω z → M t ω = Hc t ω z - Hc 0 ω z) ∧
      ∃ τ : ℕ → Ω → ℝ≥0, (∀ n, IsStoppingTime 𝓕 fun ω => (τ n ω : WithTop ℝ≥0)) ∧
        (∀ ω, Monotone fun n => τ n ω) ∧ (∀ n ω, 0 < r 0 ω z → 0 < r (τ n ω) ω z) ∧
        (∀ ω t, 0 < r t ω z → ∃ n, t < τ n ω) ∧
        (∀ n ω, Continuous fun t => M (min t (τ n ω)) ω) ∧
        (∀ n, Martingale (fun t ω => M (min t (τ n ω)) ω) 𝓕 P) ∧
        (∀ n, Martingale (fun t ω => M (min t (τ n ω)) ω ^ 2 -
          (Real.log (r 0 ω z) - Real.log (r (min t (τ n ω)) ω z))) 𝓕 P) := by
  set M := S.glued hnull hz with hMdef
  have hspec := S.locM_spec hnull hz
  have hΩ₀ := S.measurableSet_consSet_zero hnull hz
  have hG0 : ∀ n, MeasurableSet[𝓕 0] (evN r z n) := fun n => S.measurableSet_startEv hz (lev n)
  refine ⟨M, fun ω => ?_, S.glued_zero hnull hz, fun t => ?_, rhoN r z,
    fun n => S.isStoppingTime_locTime hz (lev n) n, fun ω n k hnk => S.rhoN_mono hz hnk ω,
    fun n ω h0 => ?_, fun ω t ht => ?_, fun n ω => ?_, fun n => ?_, fun n => ?_⟩
  · -- continuity on the lifetime
    intro t₀ ht₀
    by_cases hω : ω ∈ S.consSet hnull hz
    · obtain ⟨n, hG, hlt⟩ := S.exists_lt_rhoN hz ht₀
      refine ContinuousAt.continuousWithinAt ?_
      have hc : Continuous fun t => S.locM hnull hz n t ω - S.locM hnull hz n 0 ω :=
        ((hspec n).1 ω).sub continuous_const
      refine hc.continuousAt.congr ?_
      filter_upwards [Iio_mem_nhds hlt] with t ht
      exact (S.glued_eq hnull hz hω hG ht.le).symm
    · have : (fun t => M t ω) = fun _ => 0 := funext fun t => by
        rw [hMdef, glued, indicator_of_notMem hω]
      rw [this]; exact continuousWithinAt_const
  · -- modification
    have hσ : ∀ n, IsStoppingTime 𝓕 fun ω => ((min t (rhoN r z n ω) : ℝ≥0) : WithTop ℝ≥0) :=
      fun n => isStoppingTime_min_coe (S := fun _ => t) (isStoppingTime_const 𝓕 t)
        (S.isStoppingTime_locTime hz (lev n) n)
    have h1 : ∀ᵐ ω ∂P, ∀ n, S.locM hnull hz n (min t (rhoN r z n ω)) ω =
        (evN r z n).indicator (fun ω => Hc (min t (rhoN r z n ω)) ω z) ω :=
      ae_all_iff.2 fun n => (hspec n).2.2.2.1 _ (hσ n) fun ω => min_le_right _ _
    have h0 : ∀ᵐ ω ∂P, ∀ n, S.locM hnull hz n 0 ω = (evN r z n).indicator (fun ω => Hc 0 ω z) ω :=
      ae_all_iff.2 fun n => (hspec n).2.2.2.1 (fun _ => 0) (isStoppingTime_const 𝓕 0)
        fun ω => zero_le
    filter_upwards [S.ae_mem_consSet hnull hz, h1, h0] with ω hω h1 h0 hr
    obtain ⟨n, hG, hlt⟩ := S.exists_lt_rhoN hz hr
    rw [hMdef, S.glued_eq hnull hz hω hG hlt.le]
    have := h1 n
    rw [indicator_of_mem hG, min_eq_left hlt.le] at this
    rw [this, h0 n, indicator_of_mem hG]
  · -- the localizing times stay inside the lifetime
    by_cases hG : ω ∈ evN r z n
    · exact (lev_pos n).trans_le (S.le_r_of_le_locTime hz hG le_rfl)
    · rw [S.rhoN_eq_zero hz hG]; exact h0
  · obtain ⟨n, -, hlt⟩ := S.exists_lt_rhoN hz ht
    exact ⟨n, hlt⟩
  · -- continuity of the stopped paths
    have e : (fun t => M (min t (rhoN r z n ω)) ω) = fun t => (S.consSet hnull hz ∩ evN r z n).indicator
        (fun ω => S.locM hnull hz n t ω - S.locM hnull hz n 0 ω) ω :=
      funext fun t => S.glued_stop hnull hz n t ω
    rw [e]
    by_cases hω : ω ∈ S.consSet hnull hz ∩ evN r z n
    · simp only [indicator_of_mem hω]; exact ((hspec n).1 ω).sub continuous_const
    · simp only [indicator_of_notMem hω]; exact continuous_const
  · -- the stopped process is a martingale
    have e : (fun t ω => M (min t (rhoN r z n ω)) ω) = fun t => (S.consSet hnull hz ∩ evN r z n).indicator
        (fun ω => S.locM hnull hz n t ω - S.locM hnull hz n 0 ω) :=
      funext fun t => funext fun ω => S.glued_stop hnull hz n t ω
    rw [e]
    have hm0 : Martingale (fun _ => S.locM hnull hz n 0) 𝓕 P :=
      martingale_const_fun 𝓕 P ((hspec n).2.2.2.2.1.stronglyAdapted 0)
        ((hspec n).2.2.2.2.1.integrable 0)
    exact martingale_indicator_of_measurable ((hspec n).2.2.2.2.1.sub hm0) (hΩ₀.inter (hG0 n))
  · -- the quadratic variation
    set E := S.consSet hnull hz ∩ evN r z n with hEdef
    have hτ : ∀ t, IsStoppingTime 𝓕 fun ω => ((min t (rhoN r z n ω) : ℝ≥0) : WithTop ℝ≥0) := fun t =>
      isStoppingTime_min_coe (S := fun _ => t) (isStoppingTime_const 𝓕 t)
        (S.isStoppingTime_locTime hz (lev n) n)
    have hτle : ∀ t, (hτ t).measurableSpace ≤ 𝓕 t := fun t => by
      have := IsStoppingTime.measurableSpace_mono (hτ t) (isStoppingTime_const 𝓕 t)
        fun ω => WithTop.coe_le_coe.2 (min_le_left t (rhoN r z n ω))
      rwa [IsStoppingTime.measurableSpace_const] at this
    -- the pointwise decomposition
    have e : (fun t ω => M (min t (rhoN r z n ω)) ω ^ 2 - (Real.log (r 0 ω z) - Real.log (r (min t (rhoN r z n ω)) ω z)))
        = fun t => E.indicator (fun ω => (S.locM hnull hz n t ω - S.locM hnull hz n 0 ω) ^ 2 - (varV (evN r z n) r hz (lev_pos n) 0 ω - varV (evN r z n) r hz (lev_pos n) (min t (rhoN r z n ω)) ω)) +
          (S.consSet hnull hz)ᶜ.indicator
            (fun ω => -(Real.log (r 0 ω z) - Real.log (r (min t (rhoN r z n ω)) ω z))) := by
      funext t ω
      simp only [Pi.add_apply]
      by_cases hω : ω ∈ S.consSet hnull hz
      · rw [indicator_of_notMem (notMem_compl_iff.2 hω), add_zero]
        by_cases hG : ω ∈ evN r z n
        · rw [hMdef, S.glued_stop hnull hz n t ω, indicator_of_mem (mem_inter hω hG),
            indicator_of_mem (mem_inter hω hG)]
          have h0 : lev n ≤ r 0 ω z := S.le_r_of_le_locTime (R := (n : ℝ≥0)) hz hG zero_le
          have h1 : lev n ≤ r (min t (rhoN r z n ω)) ω z := S.le_r_of_le_locTime hz hG (min_le_right _ _)
          simp only [varV, indicator_of_mem hG, max_eq_left h0, max_eq_left h1]
          ring
        · rw [indicator_of_notMem fun h => hG h.2, S.rhoN_eq_zero hz hG,
            min_eq_right (zero_le (a := t)), hMdef, S.glued_zero hnull hz]
          ring
      · rw [indicator_of_notMem fun h => hω h.1, indicator_of_mem (mem_compl hω), zero_add, hMdef,
          glued, indicator_of_notMem hω]
        ring
    rw [e]
    refine Martingale.add ?_ ?_
    · -- the martingale on `E`
      have hL := (hspec n).2.2.2.2.1
      have hA := (hspec n).2.2.2.2.2
      have hL0m : StronglyMeasurable[𝓕 0] (S.locM hnull hz n 0) := hL.stronglyAdapted 0
      have hB := martingale_mul_left_of_measurable hL hL0m fun t =>
        (S.memLp_locM hnull hz n 0).integrable_mul (S.memLp_locM hnull hz n t)
      have hv0 : Measurable[𝓕 0] (varV (evN r z n) r hz (lev_pos n) 0) :=
        S.measurable_varV (S.measurableSet_startEv hz (lev n)) hz (lev_pos n) 0
      have hC : Martingale (fun _ ω => S.locM hnull hz n 0 ω ^ 2 - varV (evN r z n) r hz (lev_pos n) 0 ω) 𝓕 P := by
        refine martingale_const_fun 𝓕 P ((hL0m.pow 2).sub hv0.stronglyMeasurable) ?_
        refine (S.memLp_locM hnull hz n 0).integrable_sq.sub ?_
        refine Integrable.of_bound (hv0.mono (𝓕.le 0) le_rfl).aestronglyMeasurable
          (|varK hz (lev_pos n)|) (Eventually.of_forall fun ω => ?_)
        have hcr : ω ∈ evN r z n → lev n ≤ r 0 ω z := fun hG =>
          S.le_r_of_le_locTime (R := (n : ℝ≥0)) hz hG zero_le
        rw [Real.norm_eq_abs, abs_of_nonneg (S.varV_nonneg hz (lev_pos n) hcr)]
        exact (S.varV_le hz (lev_pos n) hcr).trans (le_abs_self _)
      have hQ : Martingale (fun t ω => (S.locM hnull hz n t ω - S.locM hnull hz n 0 ω) ^ 2 -
          (varV (evN r z n) r hz (lev_pos n) 0 ω - varV (evN r z n) r hz (lev_pos n) (min t (rhoN r z n ω)) ω)) 𝓕 P := by
        have := (hA.sub (hB.smul (2 : ℝ))).add hC
        refine this.congr ?_ fun t => Eventually.of_forall fun ω => ?_
        · intro t
          refine (((hL.stronglyAdapted t).sub (hL0m.mono (𝓕.mono (zero_le (a := t))))).pow 2).sub
            (((hv0.mono (𝓕.mono (zero_le (a := t))) le_rfl).stronglyMeasurable).sub ?_)
          exact (stronglyMeasurable_comp_stoppingTime (S.continuous_varV hz (lev_pos n))
            (S.measurable_varV (S.measurableSet_startEv hz (lev n)) hz (lev_pos n)) (hτ t)).mono (hτle t)
        · simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
          ring
      exact martingale_indicator_of_measurable hQ (hΩ₀.inter (hG0 n))
    · -- the null part
      refine martingale_of_ae_eq_zero (fun t => ?_) fun t => ?_
      · have hr0 : Measurable[𝓕 t] fun ω => r 0 ω z :=
          (S.radius_adapted 0 z hz).mono (𝓕.mono (zero_le (a := t))) le_rfl
        have hrt : Measurable[𝓕 t] fun ω => r (min t (rhoN r z n ω)) ω z :=
          ((stronglyMeasurable_comp_stoppingTime (fun ω => S.radius_cont ω z hz)
            (fun s => S.radius_adapted s z hz) (hτ t)).mono (hτle t)).measurable
        exact ((hr0.log.sub hrt.log).neg.indicator
          (𝓕.mono (zero_le (a := t)) _ hΩ₀.compl)).stronglyMeasurable
      · have hnul : P (S.consSet hnull hz)ᶜ = 0 := ae_iff.1 (S.ae_mem_consSet hnull hz)
        filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnul] with ω hω
        rw [indicator_of_notMem hω, Pi.zero_apply]

end Setting

end InteractingSLE.Sec6.Prop65
