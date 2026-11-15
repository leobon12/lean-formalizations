/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.GirsanovDensity
import InteractingSLE.Frozen.Spec.AdaptedBefore

/-!
# A progressive cut-off drift built from processes that live before a lifetime

Packet PROVE-SEC2-GIR. The coordinates of an evolution (Definition 2.1, frozen `IsIntegratedSLEEvolution`) are
only adapted before the lifetime `ζ` (`AdaptedBefore`) and continuous on `[0, ζ)` almost surely. To apply
Girsanov's theorem (`isFilteredBrownianReal_girsanov`) to a drift `F(W_t, U_t)` stopped at a stopping time
`τ ≤ ζ`, this file builds a bounded *progressive* version of `1{t < τ} F(W_t, U_t)`:

* `killed ζ X`: the process killed at `ζ` (value `0` from `ζ` on), adapted (`measurable_killed`);
* `cutIntegrand`: `1{t < τ} F(killed W, killed U)`, adapted;
* `cutDrift`: the `limsup` of its left-point dyadic values, progressive (`isStronglyProgressive_cutDrift`),
  equal to `F(W_t, U_t)` before `τ` and to `0` after `τ` on the continuity event;
* `girsanov_cutDrift`: Girsanov's theorem for this drift, with the pathwise identity
  `B̃_t = B_t + ∫₀ᵗ F(W_s, U_s) ds` for `t ≤ τ`.
-/

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

noncomputable section

namespace InteractingSLE

namespace Girsanov

/-! ### Measurability of dyadic left-point evaluations -/

section AuxMeas

variable {Ω : Type*} [MeasurableSpace Ω]

theorem measurable_gridEval_aux (t : ℝ≥0) {G : ℝ≥0 → Ω → ℝ} (hG : ∀ s, s ≤ t → Measurable (G s))
    (n : ℕ) : Measurable fun p : Set.Iic t × Ω => G (grid n (stepIdx n (p.1 : ℝ))) p.2 := by
  have hK : Measurable fun q : Ω × ℕ => G (min (grid n q.2) t) q.1 :=
    measurable_from_prod_countable_left fun k => by
      exact hG (min (grid n k) t) (min_le_right _ _)
  have hφ : Measurable fun p : Set.Iic t × Ω => (p.2, stepIdx n ((p.1 : ℝ≥0) : ℝ)) :=
    measurable_snd.prodMk ((measurable_stepIdx n).comp
      (measurable_coe_nnreal_real.comp (measurable_subtype_coe.comp measurable_fst)))
  convert hK.comp hφ using 1
  funext p
  simp only [Function.comp_apply]
  rw [min_eq_left]
  rw [← NNReal.coe_le_coe]
  exact (coe_grid_stepIdx_le (NNReal.coe_nonneg _)).trans (by exact_mod_cast p.1.2)

theorem measurable_limsup_gridEval_aux (t : ℝ≥0) {G : ℝ≥0 → Ω → ℝ}
    (hG : ∀ s, s ≤ t → Measurable (G s)) :
    Measurable fun p : Set.Iic t × Ω =>
      limsup (fun n => G (grid n (stepIdx n (p.1 : ℝ))) p.2) atTop :=
  Measurable.limsup fun n => measurable_gridEval_aux t hG n

theorem measurable_comp_pair_aux {m : ℕ} {F : ℝ → (Fin m → ℝ) → ℝ}
    (hF : Continuous fun p : ℝ × (Fin m → ℝ) => F p.1 p.2) {f : Ω → ℝ} {g : Fin m → Ω → ℝ}
    (hf : Measurable f) (hg : ∀ j, Measurable (g j)) :
    Measurable fun ω => F (f ω) (fun j => g j ω) :=
  hF.measurable.comp (hf.prodMk (measurable_pi_iff.2 hg))

end AuxMeas

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {m : ℕ}

/-! ### Killed processes and the cut integrand -/

/-- The process `X` killed at `ζ`: `X_t` for `t < ζ` and `0` from `ζ` on. -/
def killed (ζ : Ω → ℝ≥0∞) (X : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  if (t : ℝ≥0∞) < ζ ω then X t ω else 0

theorem killed_of_lt {ζ : Ω → ℝ≥0∞} {X : ℝ≥0 → Ω → ℝ} {t : ℝ≥0} {ω : Ω} (h : (t : ℝ≥0∞) < ζ ω) :
    killed ζ X t ω = X t ω := by simp [killed, h]

theorem measurable_killed {ζ : Ω → ℝ≥0∞} {X : ℝ≥0 → Ω → ℝ} (hX : AdaptedBefore 𝓕 ζ X)
    (t : ℝ≥0) : Measurable[𝓕 t] (killed ζ X t) := by
  intro A hA
  have h1 := hX t A hA
  have h2 : MeasurableSet[𝓕 t] {ω | (t : ℝ≥0∞) < ζ ω} := by
    simpa using hX t Set.univ MeasurableSet.univ
  by_cases h0 : (0 : ℝ) ∈ A
  · have : killed ζ X t ⁻¹' A = {ω | (t : ℝ≥0∞) < ζ ω ∧ X t ω ∈ A} ∪ {ω | (t : ℝ≥0∞) < ζ ω}ᶜ := by
      ext ω
      simp only [killed, Set.mem_preimage, Set.mem_union, Set.mem_ofPred_eq, Set.mem_compl_iff]
      split_ifs with h <;> tauto
    rw [this]
    exact h1.union h2.compl
  · have : killed ζ X t ⁻¹' A = {ω | (t : ℝ≥0∞) < ζ ω ∧ X t ω ∈ A} := by
      ext ω
      simp only [killed, Set.mem_preimage, Set.mem_ofPred_eq]
      split_ifs with h <;> tauto
    rw [this]
    exact h1

/-- The cut integrand `1{t < τ} F(W_t, U_t)` (with the killed coordinates). -/
def cutIntegrand (τ ζ : Ω → ℝ≥0∞) (F : ℝ → (Fin m → ℝ) → ℝ) (W : ℝ≥0 → Ω → ℝ)
    (U : Fin m → ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  if (t : ℝ≥0∞) < τ ω then F (killed ζ W t ω) (fun j => killed ζ (U j) t ω) else 0

/-- The progressive cut drift: the `limsup` of the left-point dyadic values of the cut integrand. -/
def cutDrift (τ ζ : Ω → ℝ≥0∞) (F : ℝ → (Fin m → ℝ) → ℝ) (W : ℝ≥0 → Ω → ℝ)
    (U : Fin m → ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  limsup (fun n => cutIntegrand τ ζ F W U (grid n (stepIdx n (t : ℝ))) ω) atTop

variable {τ ζ : Ω → ℝ≥0∞} {F : ℝ → (Fin m → ℝ) → ℝ} {W : ℝ≥0 → Ω → ℝ} {U : Fin m → ℝ≥0 → Ω → ℝ}

theorem measurable_cutIntegrand (hF : Continuous fun p : ℝ × (Fin m → ℝ) => F p.1 p.2)
    (hW : AdaptedBefore 𝓕 ζ W) (hU : ∀ j, AdaptedBefore 𝓕 ζ (U j))
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕 s] {ω | τ ω ≤ s}) (t : ℝ≥0) :
    Measurable[𝓕 t] (cutIntegrand τ ζ F W U t) := by
  have hpair : Measurable[𝓕 t] fun ω => F (killed ζ W t ω) (fun j => killed ζ (U j) t ω) :=
    @measurable_comp_pair_aux Ω (𝓕 t) m F hF _ _ (measurable_killed hW t)
      (fun j => measurable_killed (hU j) t)
  have hset : MeasurableSet[𝓕 t] {ω | (t : ℝ≥0∞) < τ ω} := by
    have := (hτ t).compl
    convert this using 1
    ext ω
    simp [not_le]
  exact Measurable.ite hset hpair measurable_const

theorem isStronglyProgressive_cutDrift (hF : Continuous fun p : ℝ × (Fin m → ℝ) => F p.1 p.2)
    (hW : AdaptedBefore 𝓕 ζ W) (hU : ∀ j, AdaptedBefore 𝓕 ζ (U j))
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕 s] {ω | τ ω ≤ s}) :
    IsStronglyProgressive 𝓕 (cutDrift τ ζ F W U) := fun t =>
  (@measurable_limsup_gridEval_aux Ω (𝓕 t) t (cutIntegrand τ ζ F W U)
    (fun s hs => (measurable_cutIntegrand hF hW hU hτ s).mono (𝓕.mono hs) le_rfl)).stronglyMeasurable

theorem abs_cutIntegrand_le {M : ℝ} (hFb : ∀ w u, |F w u| ≤ M) (t : ℝ≥0) (ω : Ω) :
    |cutIntegrand τ ζ F W U t ω| ≤ M := by
  unfold cutIntegrand
  split_ifs
  · exact hFb _ _
  · simpa using (abs_nonneg _).trans (hFb 0 0)

theorem abs_cutDrift_le {M : ℝ} (hFb : ∀ w u, |F w u| ≤ M) (t : ℝ≥0) (ω : Ω) :
    |cutDrift τ ζ F W U t ω| ≤ M := by
  have hb := fun n => abs_le.1 (abs_cutIntegrand_le (τ := τ) (ζ := ζ) (W := W) (U := U) hFb
    (grid n (stepIdx n (t : ℝ))) ω)
  rw [abs_le]
  constructor
  · refine le_limsup_of_le (isBoundedUnder_of ⟨M, fun n => (hb n).2⟩) fun b hb' => ?_
    obtain ⟨n, hn⟩ := hb'.exists
    exact (hb n).1.trans hn
  · exact limsup_le_of_le (isCoboundedUnder_le_of_le atTop fun n => (hb n).1)
      (Eventually.of_forall fun n => (hb n).2)

/-! ### Values of the cut drift -/

theorem grid_stepIdx_le (n : ℕ) (t : ℝ≥0) : grid n (stepIdx n (t : ℝ)) ≤ t := by
  rw [← NNReal.coe_le_coe]
  exact coe_grid_stepIdx_le (NNReal.coe_nonneg t)

theorem tendsto_grid_stepIdx (t : ℝ≥0) :
    Tendsto (fun n => grid n (stepIdx n (t : ℝ))) atTop (𝓝 t) := by
  rw [← NNReal.tendsto_coe]
  exact tendsto_coe_grid_stepIdx (NNReal.coe_nonneg t)

theorem cutDrift_eq_zero {t : ℝ≥0} {ω : Ω} (h : τ ω < t) : cutDrift τ ζ F W U t ω = 0 := by
  have hev : ∀ᶠ n in atTop, τ ω < (grid n (stepIdx n (t : ℝ)) : ℝ≥0∞) :=
    ((ENNReal.tendsto_coe.2 (tendsto_grid_stepIdx t)).eventually (lt_mem_nhds h))
  have h0 : ∀ᶠ n in atTop, cutIntegrand τ ζ F W U (grid n (stepIdx n (t : ℝ))) ω = 0 :=
    hev.mono fun n hn => by simp [cutIntegrand, not_lt.2 hn.le]
  rw [cutDrift, limsup_congr h0, limsup_const]

theorem tendsto_of_continuousOn_lt {X : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (hX : ContinuousOn (fun s => X s ω) {s | (s : ℝ≥0∞) < ζ ω}) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < ζ ω) : ContinuousAt (fun s => X s ω) t :=
  hX.continuousAt ((isOpen_lt ENNReal.continuous_coe continuous_const).mem_nhds ht)

/-- On the continuity event, the cut drift is `F(W_t, U_t)` before `τ`. -/
theorem cutDrift_eq_of_lt (hF : Continuous fun p : ℝ × (Fin m → ℝ) => F p.1 p.2) {ω : Ω}
    (hτζ : τ ω ≤ ζ ω) (hWc : ContinuousOn (fun s => W s ω) {s | (s : ℝ≥0∞) < ζ ω})
    (hUc : ∀ j, ContinuousOn (fun s => U j s ω) {s | (s : ℝ≥0∞) < ζ ω}) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < τ ω) : cutDrift τ ζ F W U t ω = F (W t ω) (fun j => U j t ω) := by
  have hle : ∀ n, ((grid n (stepIdx n (t : ℝ)) : ℝ≥0) : ℝ≥0∞) < τ ω := fun n =>
    (ENNReal.coe_le_coe.2 (grid_stepIdx_le n t)).trans_lt ht
  have heq : ∀ n, cutIntegrand τ ζ F W U (grid n (stepIdx n (t : ℝ))) ω
      = F (W (grid n (stepIdx n (t : ℝ))) ω) (fun j => U j (grid n (stepIdx n (t : ℝ))) ω) :=
    fun n => by
      simp only [cutIntegrand, hle n, ↓reduceIte, killed_of_lt ((hle n).trans_le hτζ)]
  have htζ : (t : ℝ≥0∞) < ζ ω := ht.trans_le hτζ
  have hW := (tendsto_of_continuousOn_lt hWc htζ).tendsto.comp (tendsto_grid_stepIdx t)
  have hU := fun j => (tendsto_of_continuousOn_lt (hUc j) htζ).tendsto.comp (tendsto_grid_stepIdx t)
  have hlim := (hF.tendsto (W t ω, fun j => U j t ω)).comp (hW.prodMk_nhds (tendsto_pi_nhds.2 hU))
  rw [cutDrift, (hlim.congr fun n => (heq n).symm).limsup_eq]

theorem ae_ne_real (c : ℝ) : ∀ᵐ u ∂(volume : Measure ℝ), u ≠ c := by
  rw [ae_iff]
  simp only [ne_eq, not_not, Set.ofPred_eq_eq_singleton, Real.volume_singleton]

/-- The cut drift is left-continuous at every time other than `τ`, on the continuity event. -/
theorem isRiemannRegular_cutDrift (hF : Continuous fun p : ℝ × (Fin m → ℝ) => F p.1 p.2)
    (hτζ : ∀ ω, τ ω ≤ ζ ω)
    (hcont : ∀ᵐ ω ∂P, ContinuousOn (fun s => W s ω) {s | (s : ℝ≥0∞) < ζ ω} ∧
      ∀ j, ContinuousOn (fun s => U j s ω) {s | (s : ℝ≥0∞) < ζ ω}) :
    IsRiemannRegular P (cutDrift τ ζ F W U) := by
  filter_upwards [hcont] with ω ⟨hWc, hUc⟩
  filter_upwards [ae_ne_real (τ ω).toReal] with u hu
  rcases le_or_gt u 0 with h0 | h0
  · have hI : Set.Iic u.toNNReal = {u.toNNReal} := by
      ext r
      simp only [Set.mem_Iic, Set.mem_singleton_iff, Real.toNNReal_of_nonpos h0, nonpos_iff_eq_zero]
    rw [hI]
    exact continuousWithinAt_singleton
  · set s := u.toNNReal
    have hs : (s : ℝ) = u := Real.coe_toNNReal _ h0.le
    rcases lt_trichotomy (s : ℝ≥0∞) (τ ω) with h | h | h
    · refine ContinuousAt.continuousWithinAt ?_
      have hg : ContinuousAt (fun r => F (W r ω) (fun j => U j r ω)) s :=
        (hF.tendsto _).comp ((tendsto_of_continuousOn_lt hWc (h.trans_le (hτζ ω))).prodMk_nhds
          (tendsto_pi_nhds.2 fun j => tendsto_of_continuousOn_lt (hUc j) (h.trans_le (hτζ ω))))
      refine hg.congr ?_
      filter_upwards [(isOpen_lt ENNReal.continuous_coe continuous_const).mem_nhds h] with r hr
      exact (cutDrift_eq_of_lt hF (hτζ ω) hWc hUc hr).symm
    · exfalso
      apply hu
      rw [← h, ← hs, ENNReal.coe_toReal]
    · refine ContinuousAt.continuousWithinAt ?_
      refine (continuousAt_const (y := (0 : ℝ))).congr ?_
      filter_upwards [(isOpen_lt continuous_const ENNReal.continuous_coe).mem_nhds h] with r hr
      exact (cutDrift_eq_zero hr).symm

/-- On the continuity event, `∫₀ᵗ g(θ_s) ds = ∫₀ᵗ g(F(W_s, U_s)) ds` for the cut drift `θ` and `t ≤ τ`. -/
theorem integral_comp_cutDrift_eq (hF : Continuous fun p : ℝ × (Fin m → ℝ) => F p.1 p.2)
    (g : ℝ → ℝ) {ω : Ω} (hτζ : τ ω ≤ ζ ω)
    (hWc : ContinuousOn (fun s => W s ω) {s | (s : ℝ≥0∞) < ζ ω})
    (hUc : ∀ j, ContinuousOn (fun s => U j s ω) {s | (s : ℝ≥0∞) < ζ ω}) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) ≤ τ ω) :
    ∫ s in (0 : ℝ)..(t : ℝ), g (cutDrift τ ζ F W U s.toNNReal ω)
      = ∫ s in (0 : ℝ)..(t : ℝ), g (F (W s.toNNReal ω) (fun j => U j s.toNNReal ω)) := by
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [ae_ne_real (t : ℝ)] with s hst hs
  rw [Set.uIoc_of_le (NNReal.coe_nonneg t)] at hs
  have hlt : s < t := lt_of_le_of_ne hs.2 hst
  have h1 : (s.toNNReal : ℝ≥0∞) < τ ω := by
    refine lt_of_lt_of_le ?_ ht
    rw [ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe, Real.coe_toNNReal _ hs.1.le]
    exact hlt
  rw [cutDrift_eq_of_lt hF hτζ hWc hUc h1]

/-- On the continuity event, the drift of the cut drift up to `t ≤ τ` is `∫₀ᵗ F(W_s, U_s) ds`. -/
theorem drift_cutDrift_eq (hF : Continuous fun p : ℝ × (Fin m → ℝ) => F p.1 p.2) {ω : Ω}
    (hτζ : τ ω ≤ ζ ω) (hWc : ContinuousOn (fun s => W s ω) {s | (s : ℝ≥0∞) < ζ ω})
    (hUc : ∀ j, ContinuousOn (fun s => U j s ω) {s | (s : ℝ≥0∞) < ζ ω}) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) ≤ τ ω) :
    drift (cutDrift τ ζ F W U) t ω
      = ∫ s in (0 : ℝ)..(t : ℝ), F (W s.toNNReal ω) (fun j => U j s.toNNReal ω) :=
  integral_comp_cutDrift_eq hF id hτζ hWc hUc ht

/-! ### Girsanov's theorem for the cut drift -/

/-- **Girsanov's theorem for a drift `F(W, U)` cut at a bounded stopping time before the lifetime.**
Let `B` be a Brownian motion of `𝓕` (Definition 2.1), `W`, `U` processes adapted before `ζ` and continuous
on `[0, ζ)` almost surely, `F` bounded and continuous, and `τ ≤ ζ ∧ T` a stopping time. With
`θ = cutDrift τ ζ F W U` and `Q = Z_{T+1} · P`: `Q` is a probability measure equivalent to `P`, the process
`B̃ = B + ∫₀^· θ` is a Brownian motion of `𝓕` under `Q`, and almost surely
`B̃_t = B_t + ∫₀ᵗ F(W_s, U_s) ds` for every `t ≤ τ`. -/
theorem girsanov_cutDrift [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hBF : IsFilteredBrownianReal 𝓕 B P)
    (hF : Continuous fun p : ℝ × (Fin m → ℝ) => F p.1 p.2) {M : ℝ} (hFb : ∀ w u, |F w u| ≤ M)
    (hW : AdaptedBefore 𝓕 ζ W) (hU : ∀ j, AdaptedBefore 𝓕 ζ (U j))
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕 s] {ω | τ ω ≤ s}) (hτζ : ∀ ω, τ ω ≤ ζ ω) {T : ℝ≥0}
    (hτT : ∀ ω, τ ω ≤ T)
    (hcont : ∀ᵐ ω ∂P, ContinuousOn (fun s => W s ω) {s | (s : ℝ≥0∞) < ζ ω} ∧
      ∀ j, ContinuousOn (fun s => U j s ω) {s | (s : ℝ≥0∞) < ζ ω}) :
    MathFin.IsEquivProbMeasure P (girsanovMeasure P 𝓕 B (cutDrift τ ζ F W U) (T + 1)) ∧
    IsFilteredBrownianReal 𝓕 (girsanovProcess B (cutDrift τ ζ F W U))
      (girsanovMeasure P 𝓕 B (cutDrift τ ζ F W U) (T + 1)) ∧
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ τ ω →
      girsanovProcess B (cutDrift τ ζ F W U) t ω
        = B t ω + ∫ s in (0 : ℝ)..(t : ℝ), F (W s.toNNReal ω) (fun j => U j s.toNNReal ω) := by
  have hθ := isStronglyProgressive_cutDrift hF hW hU hτ
  have hθb := abs_cutDrift_le (τ := τ) (ζ := ζ) (W := W) (U := U) hFb
  have hθreg := isRiemannRegular_cutDrift (P := P) hF hτζ hcont
  have hθT : ∀ t ω, T + 1 ≤ t → cutDrift τ ζ F W U t ω = 0 := fun t ω ht => by
    refine cutDrift_eq_zero ((hτT ω).trans_lt ?_)
    rw [ENNReal.coe_lt_coe]
    exact (lt_add_one T).trans_le ht
  have := isFilteredPreBrownian_of_isFilteredBrownianReal hBF
  refine ⟨isEquivProbMeasure_girsanovMeasure (B := B) hθ.stronglyAdapted hθb hθreg _,
    isFilteredBrownianReal_girsanov hBF hθ hθb hθreg hθT, ?_⟩
  filter_upwards [hcont] with ω ⟨hWc, hUc⟩ t ht
  rw [girsanovProcess, drift_cutDrift_eq hF (hτζ ω) hWc hUc ht]

end Girsanov

end InteractingSLE
