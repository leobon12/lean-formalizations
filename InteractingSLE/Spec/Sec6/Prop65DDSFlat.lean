/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec6.Prop65Time

/-!
# Proposition 6.5, Brownian representation, part 1: level times and flat stretches

Packet PROVE-SEC6-E (specification §6.1, `source/spec/p145-192.md`, `#prop-6.5` and
`#prop-6.5-proof`, pp. 157–159).

The proof of Proposition 6.5 notes (p. 159) that "this argument also shows that `M` is constant on
every interval on which the clock is constant". We prove this for the abstract conditionally Gaussian
exploration of `Prop65Time` and derive the continuity of the time-changed mean, the first step of the
Dambis–Dubins–Schwarz representation.

* `lvl A ρ L`: the first time the clock `A` reaches the level `L`, capped at `ρ`
  (`isStoppingTime_lvl`; `IsClockAt.clock_lvl`: `A` at that time is `min L A_ρ`).
* `IsGaussianExploration.integral_sq_sub_eq`: `E[(Y_T − Y_S)²] = E[A_T − A_S]` at stopping times
  `S ≤ T ≤ ρ` (conditional Gaussian second moments, `integral_mul_sq_sub`).
* `IsGaussianExploration.ae_flat`: almost surely `Y` is constant on every interval on which the clock
  `A = v₀ − v_{·∧ρ}` is constant. For rational `q ≤ r`, stop at the first time `A ≥ A_q + ε`: the
  second-moment identity bounds `E[(Y_r − Y_q)²; A_q = A_r]` by `ε`.
* `continuous_comp_lvl`: on such a path the time change `u ↦ Y(σ_u)`, `σ_u` the first time `A ≥ u`,
  is continuous (left and right limits of the monotone `σ` lie in the flat stretch of `σ_u`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal NNReal

namespace InteractingSLE.Sec6.Prop65

variable {Ω : Type*}

/-! ### Clocks and level times -/

/-- Along the path `ω`, `A` is a continuous nondecreasing clock started at `0` and stopped at `ρ`. -/
structure IsClockAt (A : ℝ≥0 → Ω → ℝ) (ρ : Ω → ℝ≥0) (ω : Ω) : Prop where
  cont : Continuous fun t => A t ω
  mono : Monotone fun t => A t ω
  zero : A 0 ω = 0
  stop : ∀ t, ρ ω ≤ t → A t ω = A (ρ ω) ω

/-- The first time the clock `A` reaches the level `L`, capped at `ρ`. -/
def lvl (A : ℝ≥0 → Ω → ℝ) (ρ : Ω → ℝ≥0) (L : Ω → ℝ) (ω : Ω) : ℝ≥0 :=
  if L ω ≤ A (ρ ω) ω then sInf {t | L ω ≤ A t ω} else ρ ω

namespace IsClockAt

variable {A : ℝ≥0 → Ω → ℝ} {ρ : Ω → ℝ≥0} {ω : Ω}

lemma le_stop (h : IsClockAt A ρ ω) (t : ℝ≥0) : A t ω ≤ A (ρ ω) ω := by
  rcases le_total t (ρ ω) with htρ | hρt
  · exact h.mono htρ
  · exact (h.stop t hρt).le

lemma nonneg (h : IsClockAt A ρ ω) (t : ℝ≥0) : 0 ≤ A t ω := by
  have := h.mono (zero_le (a := t))
  dsimp only at this
  rwa [h.zero] at this

lemma clock_min (h : IsClockAt A ρ ω) (t : ℝ≥0) : A (min t (ρ ω)) ω = A t ω := by
  rcases le_total t (ρ ω) with htρ | hρt
  · rw [min_eq_left htρ]
  · rw [min_eq_right hρt, h.stop t hρt]

lemma lvl_le (L : Ω → ℝ) : lvl A ρ L ω ≤ ρ ω := by
  unfold lvl
  split_ifs with hL
  · exact csInf_le (OrderBot.bddBelow _) hL
  · exact le_rfl

lemma lvl_of_not_le {L : Ω → ℝ} (hL : ¬ L ω ≤ A (ρ ω) ω) : lvl A ρ L ω = ρ ω := by
  simp only [lvl, hL, ↓reduceIte]

lemma le_clock_lvl (h : IsClockAt A ρ ω) {L : Ω → ℝ} (hL : L ω ≤ A (ρ ω) ω) :
    L ω ≤ A (lvl A ρ L ω) ω := by
  have hmem : sInf {t | L ω ≤ A t ω} ∈ {t | L ω ≤ A t ω} :=
    (isClosed_le continuous_const h.cont).csInf_mem ⟨ρ ω, hL⟩ (OrderBot.bddBelow _)
  simp only [lvl, hL, ↓reduceIte]
  exact hmem

/-- The clock at the level time is `min L A_ρ`. -/
lemma clock_lvl (h : IsClockAt A ρ ω) {L : Ω → ℝ} (hL0 : 0 ≤ L ω) :
    A (lvl A ρ L ω) ω = min (L ω) (A (ρ ω) ω) := by
  by_cases hL : L ω ≤ A (ρ ω) ω
  · rw [min_eq_left hL]
    refine le_antisymm ?_ (h.le_clock_lvl hL)
    simp only [lvl, hL, ↓reduceIte]
    set s := sInf {t | L ω ≤ A t ω} with hs
    by_contra hlt
    push Not at hlt
    rcases (zero_le (a := s)).eq_or_lt with hs0 | hs0
    · rw [← hs0, h.zero] at hlt
      linarith
    · have hev : ∀ᶠ t in 𝓝 s, L ω < A t ω := (h.cont.tendsto s).eventually (lt_mem_nhds hlt)
      have : (𝓝[<] s).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hs0⟩
      obtain ⟨t, htL, hts⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
        (self_mem_nhdsWithin : Iio s ∈ 𝓝[<] s)).exists
      exact (not_le.2 hts) (csInf_le (OrderBot.bddBelow _) htL.le)
  · push Not at hL
    rw [lvl_of_not_le (not_le.2 hL), min_eq_right hL.le]

lemma lvl_mono {L L' : Ω → ℝ} (hLL : L ω ≤ L' ω) :
    lvl A ρ L ω ≤ lvl A ρ L' ω := by
  by_cases hL' : L' ω ≤ A (ρ ω) ω
  · have hL : L ω ≤ A (ρ ω) ω := hLL.trans hL'
    simp only [lvl, hL, hL', ↓reduceIte]
    exact csInf_le_csInf (OrderBot.bddBelow _) ⟨ρ ω, hL'⟩ fun t ht => hLL.trans ht
  · rw [lvl_of_not_le hL']
    exact lvl_le L

/-- Below the level at time `r`, the level time capped at `r` is `ρ` capped at `r`. -/
lemma min_lvl_of_lt (h : IsClockAt A ρ ω) {L : Ω → ℝ} {r : ℝ≥0} (hr : A r ω < L ω) :
    min (lvl A ρ L ω) r = min (ρ ω) r := by
  by_cases hL : L ω ≤ A (ρ ω) ω
  · have hrρ : r ≤ ρ ω := by
      by_contra hρr
      push Not at hρr
      rw [h.stop r hρr.le] at hr
      exact (not_le.2 hr) hL
    have hrs : r ≤ lvl A ρ L ω := by
      simp only [lvl, hL, ↓reduceIte]
      refine le_csInf ⟨ρ ω, hL⟩ fun t ht => ?_
      by_contra htr
      push Not at htr
      exact (not_le.2 (lt_of_le_of_lt (h.mono htr.le) hr)) ht
    rw [min_eq_right hrs, min_eq_right hrρ]
  · rw [lvl_of_not_le hL]

lemma min_le_lvl_of_lt (h : IsClockAt A ρ ω) {L : Ω → ℝ} {t : ℝ≥0} (ht : A t ω < L ω) :
    min t (ρ ω) ≤ lvl A ρ L ω := by
  have := h.min_lvl_of_lt ht
  rw [min_comm t, ← this]
  exact min_le_left _ _

end IsClockAt

variable [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}

/-- The level time is a stopping time when the events `{L ≤ A_t}` are `𝓕_t`-measurable. -/
theorem isStoppingTime_lvl {A : ℝ≥0 → Ω → ℝ} {ρ : Ω → ℝ≥0} (hA : ∀ ω, IsClockAt A ρ ω)
    (hρ : IsStoppingTime 𝓕 fun ω => (ρ ω : WithTop ℝ≥0)) {L : Ω → ℝ}
    (hL : ∀ t, MeasurableSet[𝓕 t] {ω | L ω ≤ A t ω}) :
    IsStoppingTime 𝓕 fun ω => (lvl A ρ L ω : WithTop ℝ≥0) := by
  intro i
  have e : {ω | ((lvl A ρ L ω : ℝ≥0) : WithTop ℝ≥0) ≤ i} =
      {ω | L ω ≤ A i ω} ∪ ({ω | (ρ ω : WithTop ℝ≥0) ≤ i} ∩ {ω | L ω ≤ A i ω}ᶜ) := by
    ext ω
    simp only [mem_ofPred_eq, mem_union, mem_inter_iff, mem_compl_iff, WithTop.coe_le_coe]
    constructor
    · intro hle
      by_cases hL' : L ω ≤ A (ρ ω) ω
      · exact Or.inl ((hA ω).le_clock_lvl hL' |>.trans ((hA ω).mono hle))
      · rw [IsClockAt.lvl_of_not_le hL'] at hle
        refine Or.inr ⟨hle, ?_⟩
        rwa [(hA ω).stop i hle]
    · rintro (h1 | ⟨h1, h2⟩)
      · by_cases hL' : L ω ≤ A (ρ ω) ω
        · simp only [lvl, hL', ↓reduceIte]
          exact csInf_le (OrderBot.bddBelow _) h1
        · exact absurd (h1.trans ((hA ω).le_stop i)) hL'
      · have hL' : ¬ L ω ≤ A (ρ ω) ω := by rwa [← (hA ω).stop i h1]
        rw [IsClockAt.lvl_of_not_le hL']
        exact h1
  rw [e]
  exact (hL i).union ((hρ i).inter (hL i).compl)

/-- The events `{A_q + ε ≤ A_t}` are `𝓕_t`-measurable (empty for `t < q`). -/
theorem measurableSet_add_le_clock {A : ℝ≥0 → Ω → ℝ} {ρ : Ω → ℝ≥0} (hA : ∀ ω, IsClockAt A ρ ω)
    (hAm : ∀ t, Measurable[𝓕 t] (A t)) (q : ℝ≥0) {ε : ℝ} (hε : 0 < ε) (t : ℝ≥0) :
    MeasurableSet[𝓕 t] {ω | A q ω + ε ≤ A t ω} := by
  rcases le_total q t with hqt | htq
  · exact measurableSet_le (((hAm q).mono (𝓕.mono hqt) le_rfl).add_const ε) (hAm t)
  · have e : {ω | A q ω + ε ≤ A t ω} = ∅ := by
      ext ω
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_le]
      linarith [(hA ω).mono htq]
    rw [e]
    exact @MeasurableSet.empty _ (𝓕 t)

/-! ### Versions of the stopped conditional mean -/

/-- `Y` is a continuous version, stopped at `ρ`, of the stopped conditional mean of `X`:
`Y_σ = E[X | 𝓕_σ]` almost surely at every finite stopping time `σ ≤ ρ`. -/
structure IsMeanVersion (P : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ) (X : Ω → ℝ) (ρ : Ω → ℝ≥0)
    (Y : ℝ≥0 → Ω → ℝ) : Prop where
  cont : ∀ ω, Continuous fun t => Y t ω
  meas : ∀ t, Measurable (Y t)
  stop : ∀ ω t, ρ ω ≤ t → Y t ω = Y (ρ ω) ω
  eq : ∀ (σ : Ω → ℝ≥0) (hσ : IsStoppingTime 𝓕 fun ω => (σ ω : WithTop ℝ≥0)), (∀ ω, σ ω ≤ ρ ω) →
    (fun ω => Y (σ ω) ω) =ᵐ[P] P[X | hσ.measurableSpace]

namespace IsMeanVersion

variable {X : Ω → ℝ} {ρ : Ω → ℝ≥0} {Y : ℝ≥0 → Ω → ℝ}

lemma eq_min (hY : IsMeanVersion P 𝓕 X ρ Y) (t : ℝ≥0) (ω : Ω) : Y (min t (ρ ω)) ω = Y t ω := by
  rcases le_total t (ρ ω) with htρ | hρt
  · rw [min_eq_left htρ]
  · rw [min_eq_right hρt, hY.stop ω t hρt]

end IsMeanVersion

namespace IsGaussianExploration

variable {X : Ω → ℝ} {v : ℝ≥0 → Ω → ℝ} {ρ : Ω → ℝ≥0} {K : ℝ}

theorem isClockAt (h : IsGaussianExploration P 𝓕 X v ρ K) (ω : Ω) :
    IsClockAt (clockA v ρ) ρ ω :=
  ⟨h.continuous_clockA ω, h.monotone_clockA ω, clockA_zero v ρ ω, fun t ht => by
    simp only [clockA, min_eq_right ht, min_self]⟩

theorem measurable_clockA (h : IsGaussianExploration P 𝓕 X v ρ K) (t : ℝ≥0) :
    Measurable[𝓕 t] (clockA v ρ t) :=
  (h.stronglyAdapted_clockA t).measurable

theorem exists_isMeanVersion [IsProbabilityMeasure P] (h : IsGaussianExploration P 𝓕 X v ρ K) :
    ∃ Y, IsMeanVersion P 𝓕 X ρ Y := by
  obtain ⟨Y, h1, h2, h3, h4⟩ := h.exists_continuous_version
  exact ⟨Y, h1, h2, h3, h4⟩

/-- The version is square integrable at every finite stopping time `σ ≤ ρ`. -/
theorem memLp_version [IsProbabilityMeasure P] (h : IsGaussianExploration P 𝓕 X v ρ K)
    {Y : ℝ≥0 → Ω → ℝ} (hY : IsMeanVersion P 𝓕 X ρ Y) {σ : Ω → ℝ≥0}
    (hσ : IsStoppingTime 𝓕 fun ω => (σ ω : WithTop ℝ≥0)) (hσρ : ∀ ω, σ ω ≤ ρ ω) :
    MemLp (fun ω => Y (σ ω) ω) 2 P :=
  (h.integrable.condExp (m := hσ.measurableSpace) one_le_two).ae_eq (hY.eq σ hσ hσρ).symm

/-- **Second moments of increments**: `E[(Y_T − Y_S)²] = E[A_T − A_S]` for stopping times
`S ≤ T ≤ ρ`, where `A = v₀ − v_{·∧ρ}`. -/
theorem integral_sq_sub_eq [IsProbabilityMeasure P] (h : IsGaussianExploration P 𝓕 X v ρ K)
    {Y : ℝ≥0 → Ω → ℝ} (hY : IsMeanVersion P 𝓕 X ρ Y) {S T : Ω → ℝ≥0}
    (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0))
    (hT : IsStoppingTime 𝓕 fun ω => (T ω : WithTop ℝ≥0)) (hST : ∀ ω, S ω ≤ T ω)
    (hTρ : ∀ ω, T ω ≤ ρ ω) :
    ∫ ω, (Y (T ω) ω - Y (S ω) ω) ^ 2 ∂P =
      ∫ ω, (clockA v ρ (T ω) ω - clockA v ρ (S ω) ω) ∂P := by
  have hSρ : ∀ ω, S ω ≤ ρ ω := fun ω => (hST ω).trans (hTρ ω)
  have g₁ := h.gauss S hS hSρ
  have g₂ := h.gauss T hT hTρ
  have h12 : hS.measurableSpace ≤ hT.measurableSpace :=
    IsStoppingTime.measurableSpace_mono hS hT fun ω => WithTop.coe_le_coe.2 (hST ω)
  have key := integral_mul_sq_sub (W := fun _ => (1 : ℝ)) g₁ g₂ h12 measurable_const zero_le_one
    (fun _ => by simp)
  simp only [one_mul] at key
  have e1 : (fun ω => (Y (T ω) ω - Y (S ω) ω) ^ 2) =ᵐ[P]
      fun ω => (P[X | hT.measurableSpace] ω - P[X | hS.measurableSpace] ω) ^ 2 := by
    filter_upwards [hY.eq T hT hTρ, hY.eq S hS hSρ] with ω h1 h2
    rw [h1, h2]
  rw [integral_congr_ae e1, key]
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  simp only [clockA, min_eq_left (hTρ ω), min_eq_left (hSρ ω)]
  ring

/-- For deterministic `q ≤ r`: almost surely, if the clock does not move on `[q, r]`, neither does
the version. -/
theorem ae_eq_of_clockA_eq [IsProbabilityMeasure P] (h : IsGaussianExploration P 𝓕 X v ρ K)
    {Y : ℝ≥0 → Ω → ℝ} (hY : IsMeanVersion P 𝓕 X ρ Y) {q r : ℝ≥0} (hqr : q ≤ r) :
    ∀ᵐ ω ∂P, clockA v ρ q ω = clockA v ρ r ω → Y q ω = Y r ω := by
  set A := clockA v ρ with hAdef
  have hA : ∀ ω, IsClockAt A ρ ω := h.isClockAt
  have hAm : ∀ t, Measurable[𝓕 t] (A t) := h.measurable_clockA
  set D : Set Ω := {ω | A q ω = A r ω} with hD
  have hDm : MeasurableSet D :=
    measurableSet_eq_fun ((hAm q).mono (𝓕.le q) le_rfl) ((hAm r).mono (𝓕.le r) le_rfl)
  set f : Ω → ℝ := fun ω => (Y r ω - Y q ω) ^ 2 with hf
  have hfm : Measurable f := ((hY.meas r).sub (hY.meas q)).pow_const 2
  have hS := h.isStoppingTime_min_const q
  -- for each `ε > 0`, `E[f; D] ≤ ε`
  have hbound : ∀ ε : ℝ, 0 < ε → ∫ ω, D.indicator f ω ∂P ≤ ε := by
    intro ε hε
    set L : Ω → ℝ := fun ω => A q ω + ε with hL
    have hτ : IsStoppingTime 𝓕 fun ω => (lvl A ρ L ω : WithTop ℝ≥0) :=
      isStoppingTime_lvl hA h.stopping (measurableSet_add_le_clock hA hAm q hε)
    set T : Ω → ℝ≥0 := fun ω => min (lvl A ρ L ω) r with hTdef
    have hT : IsStoppingTime 𝓕 fun ω => (T ω : WithTop ℝ≥0) :=
      isStoppingTime_min_coe hτ (isStoppingTime_const 𝓕 r)
    have hqL : ∀ ω, A q ω < L ω := fun ω => by simp only [hL]; linarith
    have hST : ∀ ω, min q (ρ ω) ≤ T ω := fun ω =>
      le_min ((hA ω).min_le_lvl_of_lt (hqL ω)) ((min_le_left _ _).trans hqr)
    have hTρ : ∀ ω, T ω ≤ ρ ω := fun ω => (min_le_left _ _).trans (IsClockAt.lvl_le L)
    have hid : ∫ ω, (Y (T ω) ω - Y (min q (ρ ω)) ω) ^ 2 ∂P =
        ∫ ω, (A (T ω) ω - A (min q (ρ ω)) ω) ∂P := h.integral_sq_sub_eq hY hS hT hST hTρ
    -- the clock increment is at most `ε`
    have hAle : ∀ ω, A (T ω) ω - A (min q (ρ ω)) ω ≤ ε := by
      intro ω
      have h1 : A (T ω) ω ≤ A (lvl A ρ L ω) ω := (hA ω).mono (min_le_left _ _)
      have h2 := (hA ω).clock_lvl (L := L) (by simp only [hL]; linarith [(hA ω).nonneg q])
      rw [(hA ω).clock_min q]
      have h3 : min (L ω) (A (ρ ω) ω) ≤ L ω := min_le_left _ _
      simp only [hL] at h3
      linarith
    have hAnn : ∀ ω, 0 ≤ A (T ω) ω - A (min q (ρ ω)) ω := fun ω =>
      sub_nonneg.2 ((hA ω).mono (hST ω))
    have hI : ∫ ω, (A (T ω) ω - A (min q (ρ ω)) ω) ∂P ≤ ε := by
      calc ∫ ω, (A (T ω) ω - A (min q (ρ ω)) ω) ∂P ≤ ∫ _ω, ε ∂P :=
            integral_mono_of_nonneg (Eventually.of_forall hAnn) (integrable_const ε)
              (Eventually.of_forall hAle)
        _ = ε := by simp
    -- `f` on `D` is the square increment between `S` and `T`
    have hg_int : Integrable (fun ω => (Y (T ω) ω - Y (min q (ρ ω)) ω) ^ 2) P :=
      ((h.memLp_version hY hT hTρ).sub
        (h.memLp_version hY hS fun ω => min_le_right _ _)).integrable_sq
    have hle : ∀ ω, D.indicator f ω ≤ (Y (T ω) ω - Y (min q (ρ ω)) ω) ^ 2 := by
      intro ω
      by_cases hω : ω ∈ D
      · rw [indicator_of_mem hω]
        have hrL : A r ω < L ω := by
          have : A q ω = A r ω := hω
          rw [← this]; exact hqL ω
        have hTr : T ω = min (ρ ω) r := (hA ω).min_lvl_of_lt hrL
        simp only [hf]
        rw [hTr, min_comm, hY.eq_min r ω, hY.eq_min q ω]
      · rw [indicator_of_notMem hω]
        exact sq_nonneg _
    calc ∫ ω, D.indicator f ω ∂P ≤ ∫ ω, (Y (T ω) ω - Y (min q (ρ ω)) ω) ^ 2 ∂P :=
          integral_mono_of_nonneg (Eventually.of_forall fun ω => indicator_nonneg
            (fun ω _ => sq_nonneg (Y r ω - Y q ω)) ω) hg_int (Eventually.of_forall hle)
      _ = ∫ ω, (A (T ω) ω - A (min q (ρ ω)) ω) ∂P := hid
      _ ≤ ε := hI
  -- hence `E[f; D] = 0`
  have hnn : 0 ≤ᵐ[P] D.indicator f := Eventually.of_forall fun ω =>
    indicator_nonneg (fun ω _ => sq_nonneg (Y r ω - Y q ω)) ω
  have hint : Integrable (D.indicator f) P := by
    have h1 := h.memLp_version hY (h.isStoppingTime_min_const r) fun ω => min_le_right _ _
    have h2 := h.memLp_version hY hS fun ω => min_le_right _ _
    have hfi : Integrable f P := ((h1.sub h2).integrable_sq).congr (Eventually.of_forall fun ω => by
      simp only [hf, hY.eq_min r ω, hY.eq_min q ω, Pi.sub_apply])
    exact hfi.indicator hDm
  have hzero : ∫ ω, D.indicator f ω ∂P = 0 := by
    refine le_antisymm ?_ (integral_nonneg_of_ae hnn)
    by_contra hpos
    push Not at hpos
    have := hbound _ (half_pos hpos)
    linarith
  have hae := (integral_eq_zero_iff_of_nonneg_ae hnn hint).1 hzero
  filter_upwards [hae] with ω hω hDω
  have h0 : f ω = 0 := by
    have := hω
    simp only [Pi.zero_apply, indicator_of_mem (show ω ∈ D from hDω)] at this
    exact this
  simp only [hf] at h0
  have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h0
  linarith

/-- **Flat stretches** (p. 159: "`M` is constant on every interval on which the clock is
constant"): almost surely the version is constant on every interval on which the clock
`A = v₀ − v_{·∧ρ}` is constant. -/
theorem ae_flat [IsProbabilityMeasure P] (h : IsGaussianExploration P 𝓕 X v ρ K)
    {Y : ℝ≥0 → Ω → ℝ} (hY : IsMeanVersion P 𝓕 X ρ Y) :
    ∀ᵐ ω ∂P, ∀ s t, s ≤ t → clockA v ρ s ω = clockA v ρ t ω → Y s ω = Y t ω := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense ℝ≥0
  have : Countable D := hDc.to_subtype
  have hall : ∀ᵐ ω ∂P, ∀ q r : D, (q : ℝ≥0) ≤ r →
      clockA v ρ q ω = clockA v ρ r ω → Y q ω = Y r ω := by
    rw [ae_all_iff]
    intro q
    rw [ae_all_iff]
    intro r
    by_cases hqr : (q : ℝ≥0) ≤ r
    · filter_upwards [h.ae_eq_of_clockA_eq hY hqr] with ω hω _ hA using hω hA
    · exact Eventually.of_forall fun ω h' => absurd h' hqr
  filter_upwards [hall] with ω hω s t hst hAst
  rcases hst.eq_or_lt with rfl | hlt
  · rfl
  have hA := h.isClockAt ω
  have hconst : ∀ x ∈ Icc s t, clockA v ρ x ω = clockA v ρ s ω := fun x hx =>
    le_antisymm (hAst ▸ hA.mono hx.2) (hA.mono hx.1)
  obtain ⟨q₀, hq₀I, hq₀D⟩ := hDd.inter_open_nonempty (Ioo s t) isOpen_Ioo (nonempty_Ioo.2 hlt)
  have hDeq : Ioo s t ∩ D ⊆ {x | Y x ω = Y q₀ ω} := by
    rintro x ⟨hxI, hxD⟩
    have hAx : clockA v ρ x ω = clockA v ρ q₀ ω := by
      rw [hconst x (Ioo_subset_Icc_self hxI), hconst q₀ (Ioo_subset_Icc_self hq₀I)]
    rcases le_total x q₀ with hxq | hqx
    · exact hω ⟨x, hxD⟩ ⟨q₀, hq₀D⟩ hxq hAx
    · exact (hω ⟨q₀, hq₀D⟩ ⟨x, hxD⟩ hqx hAx.symm).symm
  have hcl : IsClosed {x | Y x ω = Y q₀ ω} := isClosed_eq (hY.cont ω) continuous_const
  have h1 : Ioo s t ⊆ {x | Y x ω = Y q₀ ω} :=
    (hDd.open_subset_closure_inter isOpen_Ioo).trans (closure_minimal hDeq hcl)
  have h2 : Icc s t ⊆ {x | Y x ω = Y q₀ ω} := by
    rw [← closure_Ioo hlt.ne]
    exact closure_minimal h1 hcl
  exact (h2 ⟨le_rfl, hst⟩).trans (h2 ⟨hst, le_rfl⟩).symm

end IsGaussianExploration

/-! ### Continuity of the time change -/

omit mΩ in
/-- On a path along which `Y` is constant on the flat stretches of the clock, the time change
`u ↦ Y(σ_u)` is continuous, `σ_u` the first time the clock reaches `u` (capped at `ρ`): the left and
right limits of the monotone `σ` at `u` have the same clock value as `σ_u`. -/
theorem continuous_comp_lvl {A : ℝ≥0 → Ω → ℝ} {ρ : Ω → ℝ≥0} {ω : Ω} (hA : IsClockAt A ρ ω)
    {Y : ℝ≥0 → Ω → ℝ} (hYc : Continuous fun t => Y t ω)
    (hflat : ∀ s t, s ≤ t → A s ω = A t ω → Y s ω = Y t ω) :
    Continuous fun u : ℝ≥0 => Y (lvl A ρ (fun _ => (u : ℝ)) ω) ω := by
  set σ : ℝ≥0 → ℝ≥0 := fun u => lvl A ρ (fun _ => (u : ℝ)) ω with hσ
  have hmono : Monotone σ := fun u u' huu => IsClockAt.lvl_mono (by exact_mod_cast huu)
  have hAσ : ∀ u : ℝ≥0, A (σ u) ω = min (u : ℝ) (A (ρ ω) ω) := fun u => hA.clock_lvl u.2
  have hAσc : Continuous fun u : ℝ≥0 => A (σ u) ω := by
    simp only [hAσ]
    exact NNReal.continuous_coe.min continuous_const
  have key : ∀ (l : Filter ℝ≥0) [l.NeBot] (u t : ℝ≥0), l ≤ 𝓝 u → Tendsto σ l (𝓝 t) →
      Y t ω = Y (σ u) ω := by
    intro l _ u t hlu hσt
    have h1 : Tendsto (fun x => A (σ x) ω) l (𝓝 (A t ω)) := (hA.cont.tendsto t).comp hσt
    have h2 : Tendsto (fun x => A (σ x) ω) l (𝓝 (A (σ u) ω)) := (hAσc.tendsto u).mono_left hlu
    have hAt : A t ω = A (σ u) ω := tendsto_nhds_unique h1 h2
    rcases le_total t (σ u) with hle | hle
    · exact hflat _ _ hle hAt
    · exact (hflat _ _ hle hAt.symm).symm
  refine continuous_iff_continuousAt.2 fun u => ?_
  rw [continuousAt_iff_continuous_left_right, ← continuousWithinAt_Iio_iff_Iic,
    ← continuousWithinAt_Ioi_iff_Ici]
  constructor
  · by_cases hne : (𝓝[<] u).NeBot
    · have := hne
      have hσl := hmono.tendsto_nhdsLT u
      have := key (𝓝[<] u) u _ nhdsWithin_le_nhds hσl
      show Tendsto _ _ (𝓝 (Y (σ u) ω))
      rw [← this]
      exact (hYc.tendsto _).comp hσl
    · rw [not_neBot] at hne
      show Tendsto _ _ _
      rw [hne]
      exact tendsto_bot
  · have hσr := hmono.tendsto_nhdsGT u
    have := key (𝓝[>] u) u _ nhdsWithin_le_nhds hσr
    show Tendsto _ _ (𝓝 (Y (σ u) ω))
    rw [← this]
    exact (hYc.tendsto _).comp hσr

end InteractingSLE.Sec6.Prop65
