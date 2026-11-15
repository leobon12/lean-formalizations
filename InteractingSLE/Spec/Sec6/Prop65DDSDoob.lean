/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec6.Prop65DDSExp
import InteractingSLE.Spec.Sec6.Prop65Path

/-!
# Proposition 6.5, Brownian representation, part 4: exhausting the localizations

Packet PROVE-SEC6-E (specification §6.1, `source/spec/p145-192.md`, `#prop-6.5`, pp. 157–159).

Proposition 6.5 localizes on `𝓕₀`-events `G_n` and up to stopping times `ρ_n` (Koebe's theorem keeps a
fixed disc in the unexplored component). `IsDDSLevels` records a sequence of conditionally Gaussian
explorations `(X_n, v_n, ρ_n)` with versions `Y_n`, consistent with one global clock `a` and one global
process `M`:
`v_n(0) − v_n(t) = a_t` on `G_n` for `t ≤ ρ_n`, and `M_t = Y_n(t) − Y_n(0)` on `G_n` for `t ≤ ρ_n`.

The time-changed means `N^n` of `Prop65DDSExp` are consistent across levels and converge uniformly on
compact time intervals along a subsequence (`exists_subseq_ae_cauchy`): for `m ≤ n` the difference
`N^n − N^m` is, on `G_m`, the continuous martingale `D_u = E[X_n − E[X_n | 𝓕_{ρ_m}] | 𝓕_{σ^n_u}]` of
the time-changed filtration, and Doob's `L⁴` inequality with the quartic bound of the conditional
Gaussian law gives `E sup_{u ≤ U} |D_u|⁴ ≤ (4/3)⁴ · 6U · (c_n − c_m)`, `c_k = E[ℓ^k_U]` increasing and
bounded by `U`. A fast subsequence and Borel–Cantelli finish (this replaces the terminal-value step
"if the clock has a finite terminal value" without any martingale convergence theorem).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal NNReal

namespace InteractingSLE.Sec6.Prop65

section Clock

variable {Ω : Type*}

/-- Level times of two clocks that agree up to the first one's stopping time are ordered. -/
lemma IsClockAt.lvl_le_lvl {A A' : ℝ≥0 → Ω → ℝ} {ρ ρ' : Ω → ℝ≥0} {ω : Ω} (hA : IsClockAt A ρ ω)
    (hA' : IsClockAt A' ρ' ω) (hρ : ρ ω ≤ ρ' ω) (hAA : ∀ t, t ≤ ρ ω → A' t ω = A t ω)
    (L : Ω → ℝ) : lvl A ρ L ω ≤ lvl A' ρ' L ω := by
  by_cases hL : L ω ≤ A (ρ ω) ω
  · have hL' : L ω ≤ A' (ρ' ω) ω := by
      have := hA'.mono hρ
      simp only at this
      rw [hAA _ le_rfl] at this
      exact hL.trans this
    simp only [lvl, hL, hL', ↓reduceIte]
    refine csInf_le_csInf (OrderBot.bddBelow _) ⟨ρ' ω, hL'⟩ fun t ht => ?_
    simp only [mem_ofPred_eq] at ht ⊢
    rcases le_total t (ρ ω) with htρ | hρt
    · rwa [← hAA t htρ]
    · rwa [hA.stop t hρt]
  · rw [IsClockAt.lvl_of_not_le hL]
    push Not at hL
    by_contra hlt
    push Not at hlt
    by_cases hL' : L ω ≤ A' (ρ' ω) ω
    · have h1 := hA'.le_clock_lvl hL'
      rw [hAA _ hlt.le] at h1
      have h3 : A (lvl A' ρ' L ω) ω ≤ A (ρ ω) ω := hA.mono hlt.le
      linarith
    · rw [IsClockAt.lvl_of_not_le hL'] at hlt
      exact absurd (hlt.trans_le hρ) (lt_irrefl _)

end Clock

section Sup

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- A supremum of a continuous function over a dense set is its supremum. -/
lemma iSup_eq_iSup_dense {X : Type*} [TopologicalSpace X] {g : X → ℝ≥0∞} (hg : Continuous g)
    {D : Set X} (hD : Dense D) : ⨆ x, g x = ⨆ x ∈ D, g x := by
  refine le_antisymm (iSup_le fun x => ?_) (iSup₂_le fun x _ => le_iSup g x)
  have hcl : IsClosed {y | g y ≤ ⨆ x ∈ D, g x} := isClosed_le hg continuous_const
  have hsub : D ⊆ {y | g y ≤ ⨆ x ∈ D, g x} := fun y hy => le_iSup₂ (f := fun x _ => g x) y hy
  have := hcl.closure_subset_iff.2 hsub
  rw [hD.closure_eq] at this
  exact this (mem_univ x)

/-- The supremum over `[0, U]` of a process with continuous paths is measurable. -/
lemma measurable_iSup_Icc {f : ℝ≥0 → Ω → ℝ≥0∞} (hc : ∀ ω, Continuous fun u => f u ω)
    (hm : ∀ u, Measurable (f u)) (U : ℝ≥0) :
    Measurable fun ω => ⨆ u : Icc (0 : ℝ≥0) U, f u ω := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (Icc (0 : ℝ≥0) U)
  have e : (fun ω => ⨆ u : Icc (0 : ℝ≥0) U, f u ω) = fun ω => ⨆ u ∈ D, f u ω := by
    funext ω
    exact iSup_eq_iSup_dense ((hc ω).comp continuous_subtype_val) hDd
  rw [e]
  exact Measurable.biSup D hDc fun u _ => hm u

end Sup

section Levels

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}

/-- A full-measure `𝓕₀`-event on which an almost sure property holds (`𝓕₀` containing the null sets). -/
theorem exists_measurableSet_zero_of_ae
    (hnull : ∀ s, MeasurableSet s → P s = 0 → MeasurableSet[𝓕 0] s) {p : Ω → Prop}
    (h : ∀ᵐ ω ∂P, p ω) : ∃ E : Set Ω, MeasurableSet[𝓕 0] E ∧ P Eᶜ = 0 ∧ ∀ ω ∈ E, p ω := by
  set Nn := toMeasurable P {ω | ¬ p ω}
  have hN0 : P Nn = 0 := by rw [measure_toMeasurable]; exact ae_iff.1 h
  refine ⟨Nnᶜ, (hnull _ (measurableSet_toMeasurable _ _) hN0).compl, by rwa [compl_compl], ?_⟩
  intro ω hω
  by_contra hp
  exact hω (subset_toMeasurable P _ hp)

/-- A sequence of localizations of one exploration, consistent with one clock `a` and one process
`M`: `v_n(0) − v_n(t) = a_t` and `M_t = Y_n(t) − Y_n(0)` on `G_n` for `t ≤ ρ_n`. -/
structure IsDDSLevels (P : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ) (X : ℕ → Ω → ℝ)
    (v : ℕ → ℝ≥0 → Ω → ℝ) (ρ : ℕ → Ω → ℝ≥0) (K : ℕ → ℝ) (G : ℕ → Set Ω)
    (Y : ℕ → ℝ≥0 → Ω → ℝ) (a : ℝ≥0 → Ω → ℝ) (M : ℝ≥0 → Ω → ℝ) : Prop where
  gauss : ∀ n, IsGaussianExploration P 𝓕 (X n) (v n) (ρ n) (K n)
  version : ∀ n, IsMeanVersion P 𝓕 (X n) (ρ n) (Y n)
  measurableSet_G : ∀ n, MeasurableSet[𝓕 0] (G n)
  mono_G : Monotone G
  mono_ρ : ∀ ω, Monotone fun n => ρ n ω
  ρ_off : ∀ n ω, ω ∉ G n → ρ n ω = 0
  v_off : ∀ n ω, ω ∉ G n → ∀ t, v n t ω = v n 0 ω
  clock : ∀ n ω, ω ∈ G n → ∀ t, t ≤ ρ n ω → v n 0 ω - v n t ω = a t ω
  path : ∀ n, ∀ᵐ ω ∂P, ω ∈ G n → ∀ t, t ≤ ρ n ω → M t ω = Y n t ω - Y n 0 ω

namespace IsDDSLevels

variable {X : ℕ → Ω → ℝ} {v : ℕ → ℝ≥0 → Ω → ℝ} {ρ : ℕ → Ω → ℝ≥0} {K : ℕ → ℝ} {G : ℕ → Set Ω}
  {Y : ℕ → ℝ≥0 → Ω → ℝ} {a : ℝ≥0 → Ω → ℝ} {M : ℝ≥0 → Ω → ℝ}

theorem clockA_eq (L : IsDDSLevels P 𝓕 X v ρ K G Y a M) {n : ℕ} {ω : Ω} (hω : ω ∈ G n)
    (t : ℝ≥0) : clockA (v n) (ρ n) t ω = a (min t (ρ n ω)) ω :=
  L.clock n ω hω _ (min_le_right _ _)

theorem clockA_off (L : IsDDSLevels P 𝓕 X v ρ K G Y a M) {n : ℕ} {ω : Ω} (hω : ω ∉ G n)
    (t : ℝ≥0) : clockA (v n) (ρ n) t ω = 0 := by
  simp only [clockA, L.v_off n ω hω, sub_self]

theorem clockA_agree (L : IsDDSLevels P 𝓕 X v ρ K G Y a M) {m n : ℕ} (hmn : m ≤ n) (ω : Ω)
    {t : ℝ≥0} (ht : t ≤ ρ m ω) : clockA (v n) (ρ n) t ω = clockA (v m) (ρ m) t ω := by
  by_cases hω : ω ∈ G m
  · have hωn : ω ∈ G n := L.mono_G hmn hω
    rw [L.clockA_eq hωn, L.clockA_eq hω, min_eq_left (ht.trans (L.mono_ρ ω hmn)), min_eq_left ht]
  · have h0 : t = 0 := le_antisymm (ht.trans (L.ρ_off m ω hω).le) zero_le
    subst h0
    rw [IsGaussianExploration.clockA_zero, IsGaussianExploration.clockA_zero]

theorem lvlTime_mono_level (L : IsDDSLevels P 𝓕 X v ρ K G Y a M) {m n : ℕ} (hmn : m ≤ n)
    (u : ℝ≥0) (ω : Ω) : lvlTime (v m) (ρ m) u ω ≤ lvlTime (v n) (ρ n) u ω :=
  ((L.gauss m).isClockAt ω).lvl_le_lvl ((L.gauss n).isClockAt ω) (L.mono_ρ ω hmn)
    (fun _ ht => L.clockA_agree hmn ω ht) _

theorem tcFilt_mono_level (L : IsDDSLevels P 𝓕 X v ρ K G Y a M) {m n : ℕ} (hmn : m ≤ n)
    (u : ℝ≥0) : (L.gauss m).tcFilt u ≤ (L.gauss n).tcFilt u :=
  IsStoppingTime.measurableSpace_mono ((L.gauss m).isStoppingTime_lvlTime u)
    ((L.gauss n).isStoppingTime_lvlTime u) fun ω =>
      WithTop.coe_le_coe.2 (L.lvlTime_mono_level hmn u ω)

theorem tcL_mono_level (L : IsDDSLevels P 𝓕 X v ρ K G Y a M) {m n : ℕ} (hmn : m ≤ n)
    (u : ℝ≥0) (ω : Ω) : tcL (v m) (ρ m) u ω ≤ tcL (v n) (ρ n) u ω := by
  rw [(L.gauss m).tcL_eq, (L.gauss n).tcL_eq, ← L.clockA_agree hmn ω le_rfl]
  exact min_le_min le_rfl (((L.gauss n).isClockAt ω).mono (L.mono_ρ ω hmn))

/-- The clock of level `n` at `σ^n_u ∧ ρ_m` (`m ≤ n`) equals the clock of level `m` at `σ^m_u`. -/
theorem clockA_min_lvlTime (L : IsDDSLevels P 𝓕 X v ρ K G Y a M) {m n : ℕ} (hmn : m ≤ n)
    (u : ℝ≥0) (ω : Ω) :
    clockA (v n) (ρ n) (min (lvlTime (v n) (ρ n) u ω) (ρ m ω)) ω = tcL (v m) (ρ m) u ω := by
  have hA := (L.gauss n).isClockAt ω
  rw [hA.mono.map_min, (L.gauss m).tcL_eq, ← L.clockA_agree hmn ω le_rfl]
  change min (tcL (v n) (ρ n) u ω) _ = _
  rw [(L.gauss n).tcL_eq, min_assoc, min_eq_right (hA.mono (L.mono_ρ ω hmn))]

/-- The clock of level `n` at `σ^m_u` (`m ≤ n`) equals that of level `m`. -/
theorem clockA_lvlTime_level (L : IsDDSLevels P 𝓕 X v ρ K G Y a M) {m n : ℕ} (hmn : m ≤ n)
    (u : ℝ≥0) (ω : Ω) :
    clockA (v n) (ρ n) (lvlTime (v m) (ρ m) u ω) ω = tcL (v m) (ρ m) u ω :=
  L.clockA_agree hmn ω (IsGaussianExploration.lvlTime_le u ω)

/-! ### The Doob martingale of a pair of levels -/

/-- On `S`, `Y_n(σ^n_u) − Y_n(σ^n_u ∧ ρ_m)`. -/
def doobD (v : ℕ → ℝ≥0 → Ω → ℝ) (ρ : ℕ → Ω → ℝ≥0) (Y : ℕ → ℝ≥0 → Ω → ℝ) (S : Set Ω)
    (m n : ℕ) (u : ℝ≥0) (ω : Ω) : ℝ :=
  S.indicator (fun ω => Y n (lvlTime (v n) (ρ n) u ω) ω -
    Y n (min (lvlTime (v n) (ρ n) u ω) (ρ m ω)) ω) ω

theorem measurable_version_comp (L : IsDDSLevels P 𝓕 X v ρ K G Y a M) (n : ℕ)
    {T : Ω → ℝ≥0} (hT : IsStoppingTime 𝓕 fun ω => (T ω : WithTop ℝ≥0)) :
    Measurable fun ω => Y n (T ω) ω :=
  (measurable_uncurry_of_continuous_of_measurable (L.version n).cont (L.version n).meas).comp
    ((IsGaussianExploration.measurable_of_isStoppingTime hT).prodMk measurable_id)

theorem martingale_doobD [IsProbabilityMeasure P] (L : IsDDSLevels P 𝓕 X v ρ K G Y a M)
    (hnull : ∀ s, MeasurableSet s → P s = 0 → MeasurableSet[𝓕 0] s) {S : Set Ω}
    (hS : MeasurableSet[𝓕 0] S) {m n : ℕ} (hmn : m ≤ n) :
    Martingale (doobD v ρ Y S m n) (L.gauss n).tcFilt P := by
  have hρm := (L.gauss m).stopping
  set Z : Ω → ℝ := S.indicator (fun ω => X n ω - P[X n | hρm.measurableSpace] ω) with hZ
  have hXi : Integrable (X n) P := (L.gauss n).integrable.integrable one_le_two
  have hσρ : ∀ u ω, min (lvlTime (v n) (ρ n) u ω) (ρ m ω) ≤ ρ n ω := fun u ω =>
    (min_le_right _ _).trans (L.mono_ρ ω hmn)
  have hAd : StronglyAdapted (L.gauss n).tcFilt (doobD v ρ Y S m n) := by
    intro u
    have hσ := (L.gauss n).isStoppingTime_lvlTime u
    have hσm := isStoppingTime_min_coe hσ hρm
    have h0 := IsGaussianExploration.zero_le_measurableSpace hσ
    have hnσ : ∀ s, MeasurableSet s → P s = 0 → MeasurableSet[hσ.measurableSpace] s :=
      fun s hs hs0 => h0 _ (hnull s hs hs0)
    have hle : hσm.measurableSpace ≤ hσ.measurableSpace :=
      IsStoppingTime.measurableSpace_mono hσm hσ fun ω => WithTop.coe_le_coe.2 (min_le_left _ _)
    have h1 : Measurable[hσ.measurableSpace] fun ω => Y n (lvlTime (v n) (ρ n) u ω) ω :=
      IsGaussianExploration.measurable_of_ae_eq_of_null hnσ (L.measurable_version_comp n hσ)
        stronglyMeasurable_condExp.measurable hσ.measurableSpace_le
        ((L.version n).eq _ hσ (IsGaussianExploration.lvlTime_le u))
    have h2 : Measurable[hσ.measurableSpace]
        fun ω => Y n (min (lvlTime (v n) (ρ n) u ω) (ρ m ω)) ω :=
      IsGaussianExploration.measurable_of_ae_eq_of_null hnσ (L.measurable_version_comp n hσm)
        (stronglyMeasurable_condExp.measurable.mono hle le_rfl) hσ.measurableSpace_le
        ((L.version n).eq _ hσm (hσρ u))
    exact ((h1.sub h2).indicator (h0 _ hS)).stronglyMeasurable
  refine (martingale_condExp Z (L.gauss n).tcFilt P).congr hAd fun u => ?_
  have hσ := (L.gauss n).isStoppingTime_lvlTime u
  have hσm := isStoppingTime_min_coe hσ hρm
  have hS' : MeasurableSet[hσ.measurableSpace] S := IsGaussianExploration.zero_le_measurableSpace hσ _ hS
  have e1 := condExp_indicator (m := hσ.measurableSpace)
    (f := fun ω => X n ω - P[X n | hρm.measurableSpace] ω)
    (hXi.sub (integrable_condExp (m := hρm.measurableSpace) (f := X n))) hS'
  have e2 := condExp_sub hXi (integrable_condExp (m := hρm.measurableSpace) (f := X n))
    hσ.measurableSpace
  have e3 := (L.version n).eq _ hσ (IsGaussianExploration.lvlTime_le u)
  have e4 := condExp_condExp_stoppingTime (P := P) hσ hρm (X n)
  have e5 := (L.version n).eq _ hσm (hσρ u)
  rw [IsGaussianExploration.measurableSpace_congr (hσ.min hρm) hσm (funext fun ω => (WithTop.coe_min _ _).symm)] at e4
  filter_upwards [e1, e2, e3, e4, e5] with ω h1 h2 h3 h4 h5
  change P[Z | hσ.measurableSpace] ω = _
  rw [hZ, h1]
  by_cases hω : ω ∈ S
  · simp only [doobD, indicator_of_mem hω]
    have h2' : P[fun ω => X n ω - P[X n | hρm.measurableSpace] ω | hσ.measurableSpace] ω =
        P[X n | hσ.measurableSpace] ω - P[P[X n | hρm.measurableSpace] | hσ.measurableSpace] ω :=
      h2
    rw [h2', h4, ← h3, ← h5]
  · simp only [doobD, indicator_of_notMem hω]

theorem continuous_doobD (L : IsDDSLevels P 𝓕 X v ρ K G Y a M) {S : Set Ω} {m n : ℕ}
    (hmn : m ≤ n)
    (hSflat : ∀ ω ∈ S, ∀ s t, s ≤ t → clockA (v n) (ρ n) s ω = clockA (v n) (ρ n) t ω →
      Y n s ω = Y n t ω) (ω : Ω) : Continuous fun u => doobD v ρ Y S m n u ω := by
  by_cases hω : ω ∈ S
  · simp only [doobD, indicator_of_mem hω]
    have hA := (L.gauss n).isClockAt ω
    have hflat := hSflat ω hω
    have h1 : Continuous fun u : ℝ≥0 => Y n (lvlTime (v n) (ρ n) u ω) ω :=
      continuous_comp_lvl hA ((L.version n).cont ω) hflat
    set c : ℝ≥0 := (clockA (v n) (ρ n) (ρ m ω) ω).toNNReal with hcdef
    have hc : (c : ℝ) = clockA (v n) (ρ n) (ρ m ω) ω := Real.coe_toNNReal _ (hA.nonneg _)
    have hcρ : clockA (v n) (ρ n) (ρ m ω) ω ≤ clockA (v n) (ρ n) (ρ n ω) ω :=
      hA.mono (L.mono_ρ ω hmn)
    have e : ∀ u, Y n (min (lvlTime (v n) (ρ n) u ω) (ρ m ω)) ω =
        Y n (lvlTime (v n) (ρ n) (min u c) ω) ω := by
      intro u
      have hA1 : clockA (v n) (ρ n) (min (lvlTime (v n) (ρ n) u ω) (ρ m ω)) ω =
          min (u : ℝ) (clockA (v n) (ρ n) (ρ m ω) ω) := by
        rw [hA.mono.map_min]
        change min (tcL (v n) (ρ n) u ω) _ = _
        rw [(L.gauss n).tcL_eq, min_assoc, min_eq_right hcρ]
      have hA2 : clockA (v n) (ρ n) (lvlTime (v n) (ρ n) (min u c) ω) ω =
          min (u : ℝ) (clockA (v n) (ρ n) (ρ m ω) ω) := by
        change tcL (v n) (ρ n) (min u c) ω = _
        rw [(L.gauss n).tcL_eq, NNReal.coe_min, hc, min_assoc, min_eq_left hcρ]
      rcases le_total (min (lvlTime (v n) (ρ n) u ω) (ρ m ω))
          (lvlTime (v n) (ρ n) (min u c) ω) with h | h
      · exact hflat _ _ h (hA1.trans hA2.symm)
      · exact (hflat _ _ h (hA2.trans hA1.symm)).symm
    simp only [e]
    exact h1.sub (h1.comp (continuous_id.min continuous_const))
  · simp only [doobD, indicator_of_notMem hω]
    exact continuous_const

/-- **The quartic bound** for the Doob process at time `U`. -/
theorem lintegral_doobD_pow_le [IsProbabilityMeasure P] (L : IsDDSLevels P 𝓕 X v ρ K G Y a M)
    {S : Set Ω} {m n : ℕ} (hmn : m ≤ n) (U : ℝ≥0) :
    ∫⁻ ω, ‖doobD v ρ Y S m n U ω‖ₑ ^ (4 : ℝ) ∂P ≤
      ENNReal.ofReal (6 * U * (∫ ω, tcL (v n) (ρ n) U ω ∂P - ∫ ω, tcL (v m) (ρ m) U ω ∂P)) := by
  have hρm := (L.gauss m).stopping
  have hσ := (L.gauss n).isStoppingTime_lvlTime U
  have hσm := isStoppingTime_min_coe hσ hρm
  have hσρ : ∀ ω, min (lvlTime (v n) (ρ n) U ω) (ρ m ω) ≤ ρ n ω := fun ω =>
    (min_le_right _ _).trans (L.mono_ρ ω hmn)
  have g₁ := (L.gauss n).gauss _ hσm hσρ
  have g₂ := (L.gauss n).gauss _ hσ (IsGaussianExploration.lvlTime_le U)
  have h12 : hσm.measurableSpace ≤ hσ.measurableSpace :=
    IsStoppingTime.measurableSpace_mono hσm hσ fun ω => WithTop.coe_le_coe.2 (min_le_left _ _)
  -- the variance difference is the difference of the time-changed clocks
  have hV : ∀ ω, v n (min (lvlTime (v n) (ρ n) U ω) (ρ m ω)) ω - v n (lvlTime (v n) (ρ n) U ω) ω
      = tcL (v n) (ρ n) U ω - tcL (v m) (ρ m) U ω := by
    intro ω
    rw [← L.clockA_min_lvlTime hmn U ω]
    simp only [tcL, clockA, min_eq_left (hσρ ω),
      min_eq_left (IsGaussianExploration.lvlTime_le (v := v n) U ω)]
    ring
  have hD : ∀ ω, v n (min (lvlTime (v n) (ρ n) U ω) (ρ m ω)) ω -
      v n (lvlTime (v n) (ρ n) U ω) ω ≤ U := by
    intro ω
    rw [hV]
    linarith [(L.gauss n).tcL_le U ω, (L.gauss m).tcL_nonneg U ω]
  have key := integral_pow_four_sub_le g₁ g₂ h12 hD
  have hint4 : Integrable (fun ω => (P[X n | hσ.measurableSpace] ω -
      P[X n | hσm.measurableSpace] ω) ^ 4) P := by
    have := integrable_two_level (W := fun _ => (1 : ℝ)) (a := 4) (b := 0) g₁ g₂
      measurable_const zero_le_one (fun _ => by simp) le_rfl
    exact this.congr (Eventually.of_forall fun ω => by simp)
  have htcLi : ∀ k, Integrable (tcL (v k) (ρ k) U) P := fun k =>
    Integrable.of_bound ((L.gauss k).measurable_tcL U |>.mono ((L.gauss k).tcFilt.le U)
      le_rfl).aestronglyMeasurable U (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg ((L.gauss k).tcL_nonneg U ω)]
        exact (L.gauss k).tcL_le U ω)
  have hVint : ∫ ω, (v n (min (lvlTime (v n) (ρ n) U ω) (ρ m ω)) ω -
      v n (lvlTime (v n) (ρ n) U ω) ω) ∂P =
        ∫ ω, tcL (v n) (ρ n) U ω ∂P - ∫ ω, tcL (v m) (ρ m) U ω ∂P := by
    simp only [hV]
    exact integral_sub (htcLi n) (htcLi m)
  rw [hVint] at key
  calc ∫⁻ ω, ‖doobD v ρ Y S m n U ω‖ₑ ^ (4 : ℝ) ∂P
      ≤ ∫⁻ ω, ENNReal.ofReal ((P[X n | hσ.measurableSpace] ω -
          P[X n | hσm.measurableSpace] ω) ^ 4) ∂P := by
        refine lintegral_mono_ae ?_
        filter_upwards [(L.version n).eq _ hσ (IsGaussianExploration.lvlTime_le U),
          (L.version n).eq _ hσm hσρ] with ω h1 h2
        have hle : ‖doobD v ρ Y S m n U ω‖ₑ ≤ ‖Y n (lvlTime (v n) (ρ n) U ω) ω -
            Y n (min (lvlTime (v n) (ρ n) U ω) (ρ m ω)) ω‖ₑ := by
          by_cases hω : ω ∈ S
          · simp only [doobD, indicator_of_mem hω, le_refl]
          · simp only [doobD, indicator_of_notMem hω, enorm_zero, zero_le]
        refine (ENNReal.rpow_le_rpow hle (by norm_num)).trans (le_of_eq ?_)
        rw [h1, h2, Real.enorm_eq_ofReal_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _)
          (by norm_num)]
        congr 1
        rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, pow_abs,
          abs_of_nonneg (by positivity)]
    _ = ENNReal.ofReal (∫ ω, (P[X n | hσ.measurableSpace] ω -
          P[X n | hσm.measurableSpace] ω) ^ 4 ∂P) :=
        (ofReal_integral_eq_lintegral_ofReal hint4
          (Eventually.of_forall fun ω => by positivity)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal key

/-- **Doob's inequality** for the pair `m ≤ n`. -/
theorem lintegral_iSup_doobD_le [IsProbabilityMeasure P] (L : IsDDSLevels P 𝓕 X v ρ K G Y a M)
    (hnull : ∀ s, MeasurableSet s → P s = 0 → MeasurableSet[𝓕 0] s) {S : Set Ω}
    (hS : MeasurableSet[𝓕 0] S) {m n : ℕ} (hmn : m ≤ n)
    (hSflat : ∀ ω ∈ S, ∀ s t, s ≤ t → clockA (v n) (ρ n) s ω = clockA (v n) (ρ n) t ω →
      Y n s ω = Y n t ω) (U : ℝ≥0) :
    ∫⁻ ω, (⨆ u : Icc (0 : ℝ≥0) U, ‖doobD v ρ Y S m n u ω‖ₑ) ^ (4 : ℝ) ∂P ≤
      ENNReal.ofReal (4 / 3) ^ (4 : ℝ) * ENNReal.ofReal (6 * U *
        (∫ ω, tcL (v n) (ρ n) U ω ∂P - ∫ ω, tcL (v m) (ρ m) U ω ∂P)) :=
  (lintegral_iSup_rpow_le (L.martingale_doobD hnull hS hmn) (L.continuous_doobD hmn hSflat) U).trans
    (mul_le_mul_right (L.lintegral_doobD_pow_le hmn U) _)

end IsDDSLevels

end Levels

end InteractingSLE.Sec6.Prop65
