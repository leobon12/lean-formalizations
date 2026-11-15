import InteractingSLE.WangWu.CouplingFrozen

/-!
# Wang–Wu at `κ = 4`: the frozen two-point martingale (Lemma 3.6, pointwise part)

Packet PROVE-WW-A. Source: `source/external/WW17LP/wang_wu_lean_preprocessed.pdf`, §3, proof of Lemma 3.6: "By
Lemmas 3.1 and 3.2, `η_t(z) η_t(w) + G_t(z, w)` is a martingale for almost every distinct pair `z, w`. This remains
true after separation: the mean of a swallowed point is frozen, and the cross-variation ceases at the first
separation; when both points stay in one disconnected component both means are frozen." (ruling R31).

For distinct deterministic `y, z ∈ ℍ` and a bounded stopping time `σ₀ < T`, the process
`η̄_{t∧σ₀}(y) η̄_{t∧σ₀}(z) + G_{U_{t∧σ₀}}(y, z)` (frozen means, retained Green kernel) agrees almost surely with a
martingale (`exists_martingale_frozenMean_mul_add_retainedGreen`).

Route: with `τ = min(σ₀, s(y), s(z))` (the supremum of the two-point localizing times of Lemma 3.2), the stopped
process is the `L¹` limit of the localized martingales of (3.5); after `τ` at least one of the two frozen one-point
martingales `N^y, N^z` is constant and the retained kernel no longer changes, so the process is
`X^τ + N^y_τ (N^z − (N^z)^τ) + N^z_τ (N^y − (N^y)^τ)`, and `Z (N − N^τ)` is a martingale for bounded
`𝓕_τ`-measurable `Z` (`martingale_mul_sub_stopped`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology QuantumZipper
open scoped NNReal ENNReal

namespace InteractingSLE

namespace WangWu

variable {nL nR : ℕ}

/-! ### General martingale lemmas -/

section General

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- `E[h (X − X')] = 0` for `X' = E[X | m]` and bounded `m`-measurable `h`. -/
theorem integral_mul_sub_eq_zero_of_ae_eq_condExp [IsFiniteMeasure P] {m : MeasurableSpace Ω}
    (hm : m ≤ mΩ) {X X' h : Ω → ℝ} (hX : Integrable X P) (hX' : X' =ᵐ[P] P[X | m])
    (hh : StronglyMeasurable[m] h) {K : ℝ} (hhb : ∀ ω, |h ω| ≤ K) :
    ∫ ω, h ω * (X ω - X' ω) ∂P = 0 := by
  have hhm : StronglyMeasurable[mΩ] h := hh.mono hm
  have hb : ∀ᵐ ω ∂P, ‖h ω‖ ≤ K := Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hhb ω
  have hX'i : Integrable X' P := integrable_condExp.congr hX'.symm
  have i1 : Integrable (fun ω => h ω * X ω) P := hX.bdd_mul hhm.aestronglyMeasurable hb
  have i2 : Integrable (fun ω => h ω * X' ω) P := hX'i.bdd_mul hhm.aestronglyMeasurable hb
  have e : ∫ ω, h ω * X ω ∂P = ∫ ω, h ω * X' ω ∂P := by
    rw [← integral_condExp hm (f := fun ω => h ω * X ω)]
    refine integral_congr_ae ?_
    filter_upwards [condExp_mul_of_stronglyMeasurable_left hh i1 hX, hX'] with ω h1 h2
    rw [show (fun ω => h ω * X ω) = h * X from rfl, h1, Pi.mul_apply, h2]
  simp_rw [mul_sub]
  rw [integral_sub i1 i2, e, sub_self]

variable {𝓖 : Filtration ℝ≥0 mΩ}

/-- The supremum of countably many bounded stopping times is a stopping time. -/
theorem isStoppingTime_iSup_coe {ρ : ℕ → Ω → ℝ≥0}
    (hρ : ∀ n, IsStoppingTime 𝓖 fun ω => (ρ n ω : WithTop ℝ≥0)) {N : ℝ≥0} (hρN : ∀ n ω, ρ n ω ≤ N) :
    IsStoppingTime 𝓖 fun ω => ((⨆ n, ρ n ω : ℝ≥0) : WithTop ℝ≥0) := by
  intro t
  have hbdd : ∀ ω, BddAbove (range fun n => ρ n ω) := fun ω => ⟨N, by rintro _ ⟨n, rfl⟩; exact hρN n ω⟩
  have : {ω | ((⨆ n, ρ n ω : ℝ≥0) : WithTop ℝ≥0) ≤ (t : WithTop ℝ≥0)} =
      ⋂ n, {ω | (ρ n ω : WithTop ℝ≥0) ≤ (t : WithTop ℝ≥0)} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iInter, WithTop.coe_le_coe]
    exact ciSup_le_iff (hbdd ω)
  rw [this]
  exact MeasurableSet.iInter fun n => hρ n t

/-- A bounded `𝓕_τ`-measurable `Z`, restricted to `{τ ≤ t}`, is `𝓕_t`-measurable. -/
theorem stronglyMeasurable_indicator_le_of_stopping {τ : Ω → ℝ≥0}
    (hτ : IsStoppingTime 𝓖 fun ω => (τ ω : WithTop ℝ≥0)) {Z : Ω → ℝ}
    (hZ : StronglyMeasurable[hτ.measurableSpace] Z) (t : ℝ≥0) :
    StronglyMeasurable[𝓖 t] ({ω | τ ω ≤ t}.indicator Z) := by
  refine Measurable.stronglyMeasurable ?_
  intro B hB
  have hpre : ({ω | τ ω ≤ t}.indicator Z) ⁻¹' B =
      (Z ⁻¹' B ∩ {ω | τ ω ≤ t}) ∪ ({_ω | (0 : ℝ) ∈ B} ∩ {ω | τ ω ≤ t}ᶜ) := by
    ext ω
    by_cases hω : τ ω ≤ t
    · simp [hω]
    · simp [hω]
  rw [hpre]
  have hle : MeasurableSet[𝓖 t] {ω | τ ω ≤ t} := by
    have := hτ t
    simpa only [WithTop.coe_le_coe] using this
  refine MeasurableSet.union ?_ ((MeasurableSet.const _).inter hle.compl)
  have h1 := ((hτ.measurableSet _).1 (hZ.measurable hB)).2 t
  simpa only [WithTop.coe_le_coe] using h1

/-- For `A ∈ 𝓕_s`, `A ∩ {s < τ} ∈ 𝓕_τ`. -/
theorem measurableSet_inter_gt_stopping {τ : Ω → ℝ≥0}
    (hτ : IsStoppingTime 𝓖 fun ω => (τ ω : WithTop ℝ≥0)) {s : ℝ≥0} {A : Set Ω}
    (hA : MeasurableSet[𝓖 s] A) :
    MeasurableSet[hτ.measurableSpace] (A ∩ {ω | s < τ ω}) := by
  have hgt : MeasurableSet[𝓖 s] {ω | s < τ ω} := by
    have : {ω | s < τ ω} = {ω | (τ ω : WithTop ℝ≥0) ≤ (s : WithTop ℝ≥0)}ᶜ := by
      ext ω; simp only [mem_ofPred_eq, mem_compl_iff, WithTop.coe_le_coe, not_le]
    rw [this]; exact (hτ s).compl
  refine (hτ.measurableSet _).2 ⟨(le_iSup (fun u => (𝓖 u : MeasurableSpace Ω)) s) _
    (MeasurableSet.inter (m := 𝓖 s) hA hgt), fun i => ?_⟩
  by_cases hsi : s < i
  · have hle : MeasurableSet[𝓖 i] {ω | (τ ω : WithTop ℝ≥0) ≤ (i : WithTop ℝ≥0)} := hτ i
    exact MeasurableSet.inter (m := 𝓖 i)
      (MeasurableSet.inter (m := 𝓖 i) (𝓖.mono hsi.le _ hA) (𝓖.mono hsi.le _ hgt)) hle
  · have : A ∩ {ω | s < τ ω} ∩ {ω | (τ ω : WithTop ℝ≥0) ≤ (i : WithTop ℝ≥0)} = ∅ := by
      refine Set.eq_empty_of_forall_notMem fun ω hω => ?_
      have h1 : s < τ ω := hω.1.2
      have h2 : τ ω ≤ i := WithTop.coe_le_coe.1 hω.2
      exact hsi (h1.trans_le h2)
    rw [this]; exact @MeasurableSet.empty _ (𝓖 i)

theorem stronglyMeasurable_of_inf {m₁ m₂ : MeasurableSpace Ω} {g : Ω → ℝ}
    (h₁ : StronglyMeasurable[m₁] g) (h₂ : StronglyMeasurable[m₂] g) : StronglyMeasurable[m₁ ⊓ m₂] g := by
  have hm : Measurable[m₁ ⊓ m₂] g := fun B hB =>
    MeasurableSpace.measurableSet_inf.2 ⟨h₁.measurable hB, h₂.measurable hB⟩
  exact hm.stronglyMeasurable

/-- **Pasting after a stopping time.** For a right-continuous bounded martingale `N`, a stopping time `τ` and a
bounded `𝓕_τ`-measurable `Z`, the process `Z (N_t − N_{t∧τ})` is a martingale. -/
theorem martingale_mul_sub_stopped [IsFiniteMeasure P] {N : ℝ≥0 → Ω → ℝ} (hN : Martingale N 𝓖 P)
    (hNrc : ∀ ω t, ContinuousWithinAt (N · ω) (Ici t) t) {K : ℝ} (hNb : ∀ t ω, |N t ω| ≤ K)
    {τ : Ω → ℝ≥0} (hτ : IsStoppingTime 𝓖 fun ω => (τ ω : WithTop ℝ≥0)) {Z : Ω → ℝ}
    (hZ : StronglyMeasurable[hτ.measurableSpace] Z) {K' : ℝ} (hZb : ∀ ω, |Z ω| ≤ K') :
    Martingale (fun t ω => Z ω * (N t ω - N (min t (τ ω)) ω)) 𝓖 P := by
  have hprog := isStronglyProgressive_of_rightContinuous hN.1 hNrc
  have hstopEq : ∀ t ω, stoppedProcess N (fun ω => (τ ω : WithTop ℝ≥0)) t ω = N (min t (τ ω)) ω :=
    fun t ω => by simp only [stoppedProcess, ← WithTop.coe_min, WithTop.untopA, WithTop.untopD_coe]
  have hstopAd : ∀ t, StronglyMeasurable[𝓖 t] (fun ω => N (min t (τ ω)) ω) := fun t => by
    have := hprog.stronglyAdapted_stoppedProcess hτ t
    rw [show (fun ω => N (min t (τ ω)) ω) = stoppedProcess N (fun ω => (τ ω : WithTop ℝ≥0)) t from
      funext fun ω => (hstopEq t ω).symm]
    exact this
  have hYeq : ∀ t, (fun ω => Z ω * (N t ω - N (min t (τ ω)) ω)) =
      fun ω => {ω | τ ω ≤ t}.indicator Z ω * (N t ω - N (min t (τ ω)) ω) := fun t => by
    funext ω
    by_cases hω : τ ω ≤ t
    · rw [Set.indicator_of_mem (show ω ∈ {ω | τ ω ≤ t} from hω)]
    · rw [Set.indicator_of_notMem (show ω ∉ {ω | τ ω ≤ t} from hω),
        min_eq_left (le_of_lt (not_le.1 hω)), sub_self, mul_zero, zero_mul]
  have hadapt : ∀ t, StronglyMeasurable[𝓖 t] (fun ω => Z ω * (N t ω - N (min t (τ ω)) ω)) :=
    fun t => by
      rw [hYeq t]
      exact (stronglyMeasurable_indicator_le_of_stopping hτ hZ t).mul ((hN.1 t).sub (hstopAd t))
  have hbd : ∀ t ω, |Z ω * (N t ω - N (min t (τ ω)) ω)| ≤ K' * (2 * K) := fun t ω => by
    rw [abs_mul]
    have h1 := abs_sub (N t ω) (N (min t (τ ω)) ω)
    have h2 : |N t ω - N (min t (τ ω)) ω| ≤ 2 * K := by linarith [hNb t ω, hNb (min t (τ ω)) ω]
    exact mul_le_mul (hZb ω) h2 (abs_nonneg _) ((abs_nonneg _).trans (hZb ω))
  have hint : ∀ t, Integrable (fun ω => Z ω * (N t ω - N (min t (τ ω)) ω)) P := fun t =>
    Integrable.of_bound ((hadapt t).mono (𝓖.le t)).aestronglyMeasurable _
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hbd t ω)
  refine ⟨hadapt, fun s t hst => ?_⟩
  refine (ae_eq_condExp_of_forall_setIntegral_eq (𝓖.le s) (hint t)
    (fun A _ _ => (hint s).integrableOn) (fun A hA _ => ?_) ((hadapt s).aestronglyMeasurable)).symm
  -- the two pieces
  set g₁ : Ω → ℝ := A.indicator ({ω | τ ω ≤ s}.indicator Z) with hg₁
  set g₃ : Ω → ℝ := (A ∩ {ω | s < τ ω}).indicator ({ω | τ ω ≤ t}.indicator Z) with hg₃
  have hptw : ∀ ω, A.indicator (fun ω => Z ω * (N t ω - N (min t (τ ω)) ω)) ω -
      A.indicator (fun ω => Z ω * (N s ω - N (min s (τ ω)) ω)) ω =
      g₁ ω * (N t ω - N s ω) + g₃ ω * (N t ω - N (min t (τ ω)) ω) := by
    intro ω
    by_cases hA' : ω ∈ A
    · simp only [hg₁, hg₃, Set.indicator_of_mem hA']
      by_cases h1 : τ ω ≤ s
      · have h1t : τ ω ≤ t := h1.trans hst
        simp only [Set.indicator, mem_inter_iff, mem_ofPred_eq, h1, hA',
          not_lt.2 h1, ↓reduceIte, and_false, min_eq_right h1, min_eq_right h1t]
        ring
      · push Not at h1
        simp only [Set.indicator, mem_inter_iff, mem_ofPred_eq, hA', h1, true_and,
          not_le.2 h1, ↓reduceIte, min_eq_left h1.le, sub_self, mul_zero, zero_mul, zero_add, sub_zero]
        by_cases h2 : τ ω ≤ t
        · simp only [h2, ↓reduceIte]
        · simp only [h2, ↓reduceIte, min_eq_left (le_of_lt (not_le.1 h2)), sub_self, mul_zero]
    · simp only [hg₁, hg₃, Set.indicator_of_notMem hA', mem_inter_iff, hA', false_and,
        not_false_eq_true, Set.indicator_of_notMem, sub_self, zero_mul, add_zero]
  -- measurability of the pieces
  have hg₁m : StronglyMeasurable[𝓖 s] g₁ :=
    (stronglyMeasurable_indicator_le_of_stopping hτ hZ s).indicator hA
  have hτmin := (isStoppingTime_const 𝓖 t).min hτ
  have hms : hτmin.measurableSpace = 𝓖 t ⊓ hτ.measurableSpace := by
    rw [IsStoppingTime.measurableSpace_min (isStoppingTime_const 𝓖 t) hτ,
      IsStoppingTime.measurableSpace_const]
  have hg₃t : StronglyMeasurable[𝓖 t] g₃ := by
    have hgt : MeasurableSet[𝓖 t] {ω | s < τ ω} := by
      have : {ω | s < τ ω} = {ω | (τ ω : WithTop ℝ≥0) ≤ (s : WithTop ℝ≥0)}ᶜ := by
        ext ω; simp only [mem_ofPred_eq, mem_compl_iff, WithTop.coe_le_coe, not_le]
      rw [this]; exact 𝓖.mono hst _ (hτ s).compl
    exact (stronglyMeasurable_indicator_le_of_stopping hτ hZ t).indicator
      (MeasurableSet.inter (m := 𝓖 t) (𝓖.mono hst _ hA) hgt)
  have hg₃τ : StronglyMeasurable[hτ.measurableSpace] g₃ := by
    have hle : MeasurableSet[hτ.measurableSpace] {ω | τ ω ≤ t} := by
      have := hτ.measurableSet_le' t
      simpa only [WithTop.coe_le_coe] using this
    exact (hZ.indicator hle).indicator (measurableSet_inter_gt_stopping hτ hA)
  have hg₃m : StronglyMeasurable[hτmin.measurableSpace] g₃ := by
    rw [hms]
    exact stronglyMeasurable_of_inf (m₁ := 𝓖 t) (m₂ := hτ.measurableSpace) hg₃t hg₃τ
  have hb₁ : ∀ ω, |g₁ ω| ≤ K' := fun ω => by
    simp only [hg₁, Set.indicator]
    split_ifs <;> simp [hZb ω, (abs_nonneg _).trans (hZb ω)]
  have hb₃ : ∀ ω, |g₃ ω| ≤ K' := fun ω => by
    simp only [hg₃, Set.indicator]
    split_ifs <;> simp [hZb ω, (abs_nonneg _).trans (hZb ω)]
  have hI₁ : ∫ ω, g₁ ω * (N t ω - N s ω) ∂P = 0 :=
    integral_mul_sub_eq_zero_of_ae_eq_condExp (𝓖.le s) (hN.integrable t) (hN.2 s t hst).symm hg₁m hb₁
  have hos := Martingale.stoppedValue_ae_eq_condExp_of_rightContinuous hN hNrc hτmin
    (isStoppingTime_const 𝓖 t) (fun ω => min_le_left _ _) (T := t) (fun _ => le_rfl)
  have hos' : (fun ω => N (min t (τ ω)) ω) =ᵐ[P] P[N t | hτmin.measurableSpace] := by
    filter_upwards [hos] with ω h
    simp only [stoppedValue_const] at h
    rw [← h]
    simp only [stoppedValue, ← WithTop.coe_min, WithTop.untopA, WithTop.untopD_coe]
  have hI₃ : ∫ ω, g₃ ω * (N t ω - N (min t (τ ω)) ω) ∂P = 0 :=
    integral_mul_sub_eq_zero_of_ae_eq_condExp hτmin.measurableSpace_le (hN.integrable t) hos' hg₃m hb₃
  have hsum : ∫ ω in A, (Z ω * (N t ω - N (min t (τ ω)) ω)) ∂P -
      ∫ ω in A, (Z ω * (N s ω - N (min s (τ ω)) ω)) ∂P = 0 := by
    rw [← integral_indicator (𝓖.le s _ hA), ← integral_indicator (𝓖.le s _ hA),
      ← integral_sub ((hint t).indicator (𝓖.le s _ hA)) ((hint s).indicator (𝓖.le s _ hA))]
    simp_rw [hptw]
    have i1 : Integrable (fun ω => g₁ ω * (N t ω - N s ω)) P :=
      ((hN.integrable t).sub (hN.integrable s)).bdd_mul
        ((hg₁m.mono (𝓖.le s)).aestronglyMeasurable)
        (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hb₁ ω)
    have i3 : Integrable (fun ω => g₃ ω * (N t ω - N (min t (τ ω)) ω)) P :=
      ((hN.integrable t).sub (integrable_condExp.congr hos'.symm)).bdd_mul
        ((hg₃m.mono hτmin.measurableSpace_le).aestronglyMeasurable)
        (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hb₃ ω)
    rw [integral_add i1 i3, hI₁, hI₃, add_zero]
  linarith

/-- **Bounded `L¹` limits of martingales of the usual augmentation are martingales**: if `M^n` are martingales,
almost surely bounded by `K`, and almost surely `M^n_t → X_t` for all `t`, then `X` agrees almost surely with a
martingale. -/
theorem exists_martingale_of_tendsto [IsFiniteMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    {M : ℕ → ℝ≥0 → Ω → ℝ} (hM : ∀ n, Martingale (M n) (usualAugmentation 𝓕 P) P) {K : ℝ}
    {X : ℝ≥0 → Ω → ℝ}
    (hX : ∀ᵐ ω ∂P, (∀ n t, |M n t ω| ≤ K) ∧ ∀ t, Tendsto (fun n => M n t ω) atTop (𝓝 (X t ω))) :
    ∃ M' : ℝ≥0 → Ω → ℝ, Martingale M' (usualAugmentation 𝓕 P) P ∧ ∀ᵐ ω ∂P, ∀ t, M' t ω = X t ω := by
  set G : Set Ω := {ω | (∀ n t, |M n t ω| ≤ K) ∧ ∀ t, Tendsto (fun n => M n t ω) atTop (𝓝 (X t ω))}
    with hGdef
  set N := toMeasurable P Gᶜ with hNdef
  have hNc : ∀ ω, ω ∉ N → ω ∈ G := fun ω hω => by
    by_contra h
    exact hω (subset_toMeasurable _ _ h)
  have hN0 : P N = 0 := by rw [hNdef, measure_toMeasurable]; exact ae_iff.1 hX
  have hK0 : ∀ ω ∈ G, 0 ≤ K := fun ω hω => (abs_nonneg _).trans (hω.1 0 0)
  set Y : ℕ → ℝ≥0 → Ω → ℝ := fun n t => Nᶜ.indicator (M n t) with hYdef
  have hYm : ∀ n, Martingale (Y n) (usualAugmentation 𝓕 P) P := fun n =>
    WangWu.martingale_indicator_compl_toMeasurable (hM n) hX
  set M' : ℝ≥0 → Ω → ℝ := fun t => Nᶜ.indicator (X t) with hM'def
  have hconv : ∀ t ω, Tendsto (fun n => Y n t ω) atTop (𝓝 (M' t ω)) := by
    intro t ω
    by_cases hω : ω ∈ N
    · simp only [hYdef, hM'def, Set.indicator_of_notMem (show ω ∉ Nᶜ from fun h => h hω)]
      exact tendsto_const_nhds
    · simp only [hYdef, hM'def, Set.indicator_of_mem (show ω ∈ Nᶜ from hω)]
      exact (hNc ω hω).2 t
  have hYb : ∀ n t ω, ‖Y n t ω‖ ≤ max K 0 := fun n t ω => by
    rw [Real.norm_eq_abs]
    by_cases hω : ω ∈ N
    · simp only [hYdef, Set.indicator_of_notMem (show ω ∉ Nᶜ from fun h => h hω), abs_zero]
      exact le_max_right _ _
    · simp only [hYdef, Set.indicator_of_mem (show ω ∈ Nᶜ from hω)]
      exact ((hNc ω hω).1 n t).trans (le_max_left _ _)
  have hM'ad : ∀ t, StronglyMeasurable[usualAugmentation 𝓕 P t] (M' t) := fun t =>
    stronglyMeasurable_of_tendsto atTop (fun n => (hYm n).1 t) (tendsto_pi_nhds.2 (hconv t))
  have hM'b : ∀ t ω, ‖M' t ω‖ ≤ max K 0 := fun t ω =>
    le_of_tendsto ((continuous_norm.tendsto _).comp (hconv t ω))
      (Eventually.of_forall fun n => hYb n t ω)
  have hM'i : ∀ t, Integrable (M' t) P := fun t =>
    Integrable.of_bound ((hM'ad t).mono (Filtration.le _ t)).aestronglyMeasurable _
      (Eventually.of_forall (hM'b t))
  have hsetlim : ∀ t (A : Set Ω), Tendsto (fun n => ∫ ω in A, Y n t ω ∂P) atTop
      (𝓝 (∫ ω in A, M' t ω ∂P)) := fun t A =>
    tendsto_integral_of_dominated_convergence (fun _ => max K 0)
      (fun n => (((hYm n).1 t).mono (Filtration.le _ t)).aestronglyMeasurable)
      (integrable_const _) (fun n => Eventually.of_forall fun ω => hYb n t ω)
      (Eventually.of_forall fun ω => hconv t ω)
  refine ⟨M', ⟨hM'ad, fun s t hst => ?_⟩, ?_⟩
  · refine (ae_eq_condExp_of_forall_setIntegral_eq (Filtration.le _ s) (hM'i t)
      (fun A _ _ => (hM'i s).integrableOn) (fun A hA _ => ?_)
      ((hM'ad s).aestronglyMeasurable)).symm
    refine tendsto_nhds_unique (hsetlim s A) ((hsetlim t A).congr fun n => ?_)
    exact ((hYm n).setIntegral_eq hst hA).symm
  · filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN0] with ω hω t
    simp only [hM'def, Set.indicator_of_mem (show ω ∈ Nᶜ from hω)]

end General

/-! ### Pathwise lemmas -/

section PathwiseTwo

/-- **Continuity of a frozen path**: `t ↦ g(t ∧ σ)` before the swallowing time `S`, the left limit of `g` at `S`
afterwards. -/
theorem continuous_frozen_path {g : ℝ≥0 → ℝ} {S : ℝ≥0∞} {σ : ℝ≥0}
    (hg : ∀ T : ℝ≥0, (T : ℝ≥0∞) < S → T ≤ σ → ContinuousOn g (Icc 0 T))
    (hL : S ≤ σ → Tendsto g (𝓝[<] S.toNNReal) (𝓝 (limUnder (𝓝[<] S.toNNReal) g))) :
    Continuous fun t : ℝ≥0 =>
      if ((min t σ : ℝ≥0) : ℝ≥0∞) < S then g (min t σ) else limUnder (𝓝[<] S.toNNReal) g := by
  rcases lt_or_ge (σ : ℝ≥0∞) S with hσS | hSσ
  · have hcond : ∀ t : ℝ≥0, ((min t σ : ℝ≥0) : ℝ≥0∞) < S := fun t =>
      lt_of_le_of_lt (by exact_mod_cast min_le_right t σ) hσS
    simp only [hcond, ↓reduceIte]
    exact (hg σ hσS le_rfl).comp_continuous (continuous_id.min continuous_const)
      fun t => ⟨bot_le, min_le_right _ _⟩
  · set L := limUnder (𝓝[<] S.toNNReal) g with hLdef
    have hSt : S ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hSσ
    set s := S.toNNReal with hsdef
    have hSc : ((s : ℝ≥0) : ℝ≥0∞) = S := ENNReal.coe_toNNReal hSt
    have hsσ : s ≤ σ := by rw [← hSc] at hSσ; exact_mod_cast hSσ
    have hF : (fun t : ℝ≥0 => if ((min t σ : ℝ≥0) : ℝ≥0∞) < S then g (min t σ) else L) =
        fun t => if t < s then g t else L := by
      funext t
      by_cases hts : t < s
      · have : min t σ = t := min_eq_left (hts.le.trans hsσ)
        have h2 : ((min t σ : ℝ≥0) : ℝ≥0∞) < S := by rw [this, ← hSc]; exact_mod_cast hts
        simp only [h2, hts, ↓reduceIte]
        rw [this]
      · push Not at hts
        have h2 : ¬ ((min t σ : ℝ≥0) : ℝ≥0∞) < S := by
          rw [not_lt, ← hSc]; exact_mod_cast le_min hts hsσ
        simp only [h2, not_lt.2 hts, ↓reduceIte]
    rw [hF]
    refine continuous_iff_continuousAt.2 fun t₀ => ?_
    rcases lt_trichotomy t₀ s with h | h | h
    · -- before `s`: locally `g`
      obtain ⟨T, hT1, hT2⟩ := exists_between h
      have hgT := hg T (by rw [← hSc]; exact_mod_cast hT2) (hT2.le.trans hsσ)
      have hnhds : Icc (0 : ℝ≥0) T ∈ 𝓝 t₀ := by
        rw [show Icc (0 : ℝ≥0) T = Iic T from Icc_bot]
        exact Iic_mem_nhds hT1
      have hga : ContinuousAt g t₀ := (hgT t₀ ⟨bot_le, hT1.le⟩).continuousAt hnhds
      refine hga.congr ?_
      filter_upwards [Iio_mem_nhds h] with t ht
      simp only [show t < s from ht, ↓reduceIte]
    · -- at `s`: the left limit
      subst h
      refine continuousAt_iff_continuous_left_right.2 ⟨?_, ?_⟩
      · rw [ContinuousWithinAt, show (if s < s then g s else L) = L by simp]
        have hlim := hL hSσ
        have hsplit : 𝓝[≤] s = 𝓝[<] s ⊔ pure s := by
          rw [← Iio_union_Icc_eq_Iic le_rfl, nhdsWithin_union]
          simp
        rw [hsplit, tendsto_sup]
        refine ⟨hlim.congr' ?_, ?_⟩
        · filter_upwards [self_mem_nhdsWithin] with t ht
          simp only [show t < s from ht, ↓reduceIte]
        · simp only [tendsto_pure_left, lt_irrefl, ↓reduceIte]
          exact fun _ h => mem_of_mem_nhds h
      · refine (continuousWithinAt_const (b := L)).congr (fun t ht => ?_) (by simp)
        simp only [not_lt.2 (show s ≤ t from ht), ↓reduceIte]
    · -- after `s`: locally constant
      refine (continuousAt_const (y := L)).congr ?_
      filter_upwards [Ioi_mem_nhds h] with t ht
      simp only [not_lt.2 (show s ≤ t from (le_of_lt ht)), ↓reduceIte]

/-- Alive at `s ≤ T < T'` for one driver ⇒ alive for another one agreeing with it on `[0, T']` (continuous there). -/
theorem lt_swallowTime_of_eqOn {V V' : ℝ → ℝ} {T T' : ℝ} (hTT' : T < T')
    (hV' : ContinuousOn V' (Icc 0 T')) (hVV' : EqOn V V' (Icc 0 T')) {x : ℂ} (hx : 0 < x.im) {s : ℝ}
    (hs0 : 0 ≤ s) (hsT : s ≤ T) (hlt : ENNReal.ofReal s < swallowTime V x) :
    ENNReal.ofReal s < swallowTime V' x := by
  obtain ⟨u, hu⟩ := QuantumZipper.exists_isForwardSol_of_not_mem_fwdHull hs0 hx
    (fun h => (not_le.2 hlt) h.2)
  have hu' : IsForwardSol V' x s u :=
    (Ito.isForwardSol_iff_of_eqOn (hVV'.mono (Icc_subset_Icc_right (hsT.trans hTT'.le))) u).1 hu
  exact lt_swallowTime_of_isForwardSol hs0 (hsT.trans_lt hTT') hV' hx ⟨u, hu'⟩

/-- The retained Green kernel `V_T` depends only on the driver on `[0, T']`, `T < T'` (continuous drivers). -/
theorem VTe_eq_of_eqOn {W W' : ℝ → ℝ} {T T' : ℝ} (hTT' : T < T') (hW : ContinuousOn W (Icc 0 T'))
    (hW' : ContinuousOn W' (Icc 0 T')) (heq : EqOn W W' (Icc 0 T')) {a b : ℂ} (ha : 0 < a.im)
    (hb : 0 < b.im) : K3.VTe W T a b = K3.VTe W' T a b := by
  have hidx : K3.vtIdx W T a b = K3.vtIdx W' T a b := by
    ext s
    simp only [K3.vtIdx, mem_ofPred_eq]
    constructor
    · rintro ⟨h0, hT, ha', hb'⟩
      exact ⟨h0, hT, lt_swallowTime_of_eqOn hTT' hW' heq ha h0 hT ha',
        lt_swallowTime_of_eqOn hTT' hW' heq hb h0 hT hb'⟩
    · rintro ⟨h0, hT, ha', hb'⟩
      exact ⟨h0, hT, lt_swallowTime_of_eqOn hTT' hW heq.symm ha h0 hT ha',
        lt_swallowTime_of_eqOn hTT' hW heq.symm hb h0 hT hb'⟩
  rw [K3.VTe, K3.VTe, hidx]
  refine iInf_congr fun s => iInf_congr fun hs => ?_
  have hsT' : s ≤ T' := hs.2.1.trans hTT'.le
  simp only [K3.vtKer, Ito.fwdMap_congr_of_eqOn_of_le heq hsT']

end PathwiseTwo

section PathFacts

variable {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {w : ℝ≥0 → ℝ}
  {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-- A time strictly between `T` and `ζ`. -/
theorem exists_between_lt_lifetime {T : ℝ≥0} (hT : (T : ℝ≥0∞) < ζ) :
    ∃ T' : ℝ≥0, T < T' ∧ (T' : ℝ≥0∞) < ζ := by
  obtain ⟨c, hc1, hc2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hT
  exact ⟨c, by exact_mod_cast hc1, hc2⟩

/-- Along a path of the chain, for `y ≠ z` alive at `r < ζ`: `0 ≤ G_ℍ(f_r y, f_r z) ≤ G_ℍ(y, z)`. -/
theorem greenH_fwdMap_mem_Icc_of_path (hP : IsIntegratedSLEPath 4 xL xR ρL ρR w vL vR b ζ)
    {r : ℝ≥0} (hr : (r : ℝ≥0∞) < ζ) {y z : ℂ} (hy : 0 < y.im) (hz : 0 < z.im) (hyz : y ≠ z)
    (hsy : ∃ v, IsForwardSol (Ito.rpath w) y r v) (hsz : ∃ v, IsForwardSol (Ito.rpath w) z r v) :
    0 ≤ greenH (fwdMap (Ito.rpath w) r y) (fwdMap (Ito.rpath w) r z) ∧
      greenH (fwdMap (Ito.rpath w) r y) (fwdMap (Ito.rpath w) r z) ≤ greenH y z := by
  have hwc : ContinuousOn (Ito.rpath w) (Icc 0 (r : ℝ)) := Ito.continuousOn_rpath hP.2.2.2.1 hr
  set W' := Ito.clampDrv (Ito.rpath w) r
  have hW'c : Continuous W' := Ito.continuous_clampDrv r.coe_nonneg hwc
  have heq : EqOn W' (Ito.rpath w) (Icc 0 (r : ℝ)) := Ito.clampDrv_eqOn
  have hsy' : ∃ v, IsForwardSol W' y r v := by
    obtain ⟨v, hv⟩ := hsy; exact ⟨v, (Ito.isForwardSol_iff_of_eqOn heq v).2 hv⟩
  have hsz' : ∃ v, IsForwardSol W' z r v := by
    obtain ⟨v, hv⟩ := hsz; exact ⟨v, (Ito.isForwardSol_iff_of_eqOn heq v).2 hv⟩
  have h := FwdClock.greenH_fwdMap_mem_Icc hW'c hy hz hyz hsy' hsz' ⟨r.coe_nonneg, le_rfl⟩
  rw [Ito.fwdMap_congr_of_eqOn_of_le heq le_rfl, Ito.fwdMap_congr_of_eqOn_of_le heq le_rfl] at h
  exact h

/-- **Dichotomy at the first stop**: the supremum `τ` of localizing times exhausting the times `≤ σ` at which both
points are alive is `σ`, or one of the two swallowing times is `≤ τ`. -/
theorem iSup_eq_or_swallow {ρ : ℕ → ℝ≥0} {σ : ℝ≥0} {Sy Sz : ℝ≥0∞} (hbdd : BddAbove (range ρ))
    (hρσ : ∀ n, ρ n ≤ σ)
    (hexh : ∀ t : ℝ≥0, t ≤ σ → (t : ℝ≥0∞) < Sy → (t : ℝ≥0∞) < Sz → ∀ᶠ n in atTop, t ≤ ρ n) :
    (⨆ n, ρ n) = σ ∨ Sy ≤ ((⨆ n, ρ n : ℝ≥0) : ℝ≥0∞) ∨ Sz ≤ ((⨆ n, ρ n : ℝ≥0) : ℝ≥0∞) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hne, hy, hz⟩ := hcon
  have hτσ : (⨆ n, ρ n) < σ := lt_of_le_of_ne (ciSup_le hρσ) hne
  have hlt : ((⨆ n, ρ n : ℝ≥0) : ℝ≥0∞) < min (σ : ℝ≥0∞) (min Sy Sz) :=
    lt_min (by exact_mod_cast hτσ) (lt_min hy hz)
  obtain ⟨t, ht1, ht2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hlt
  have htσ : t ≤ σ := by
    have : (t : ℝ≥0∞) ≤ σ := ht2.le.trans (min_le_left _ _)
    exact_mod_cast this
  have hty : (t : ℝ≥0∞) < Sy := ht2.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have htz : (t : ℝ≥0∞) < Sz := ht2.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨n, hn⟩ := (hexh t htσ hty htz).exists
  have : t ≤ ⨆ n, ρ n := hn.trans (le_ciSup hbdd n)
  have h1 : (t : ℝ≥0∞) ≤ ((⨆ n, ρ n : ℝ≥0) : ℝ≥0∞) := by exact_mod_cast this
  exact absurd ht1 (not_lt.2 h1)

/-- After the swallowing time `S ≤ τ ≤ σ`, the frozen mean no longer changes. -/
theorem frozenMean_min_eq_of_swallow {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {w : ℝ≥0 → ℝ}
    {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {y : ℂ} {τ σ t : ℝ≥0}
    (hS : swallowTime (Ito.rpath w) y ≤ τ) (hτσ : τ ≤ σ) (htτ : τ ≤ t) :
    frozenMean ρL ρR w vL vR (min t σ) y = frozenMean ρL ρR w vL vR (min τ σ) y := by
  have h1 : ¬ ((min t σ : ℝ≥0) : ℝ≥0∞) < swallowTime (Ito.rpath w) y :=
    not_lt.2 (hS.trans (by exact_mod_cast le_min htτ hτσ))
  have h2 : ¬ ((min τ σ : ℝ≥0) : ℝ≥0∞) < swallowTime (Ito.rpath w) y :=
    not_lt.2 (hS.trans (by exact_mod_cast le_min le_rfl hτσ))
  simp only [frozenMean, h1, h2, ↓reduceIte]

/-- **The retained kernel stops at the first stop**: if `τ ≤ σ` and `τ = σ` or one swallowing time is `≤ τ`,
then `V_{t∧σ}(y,z) = V_{t∧τ}(y,z)` for every `t`. -/
theorem retainedGreen_min_eq {w : ℝ≥0 → ℝ} {y z : ℂ} {τ σ : ℝ≥0} (hτσ : τ ≤ σ)
    (h : τ = σ ∨ swallowTime (Ito.rpath w) y ≤ τ ∨ swallowTime (Ito.rpath w) z ≤ τ) (t : ℝ≥0) :
    retainedGreen w (min t σ) y z = retainedGreen w (min t τ) y z := by
  rcases h with h | h
  · rw [h]
  rcases le_total t τ with htτ | hτt
  · rw [min_eq_left (htτ.trans hτσ), min_eq_left htτ]
  rw [min_eq_right hτt]
  unfold retainedGreen K3.VT K3.VTe
  congr 1
  have hidx : K3.vtIdx (Ito.rpath w) (min t σ : ℝ≥0) y z = K3.vtIdx (Ito.rpath w) (τ : ℝ≥0) y z := by
    ext s
    simp only [K3.vtIdx, mem_ofPred_eq]
    constructor
    · rintro ⟨h0, hT, ha, hb⟩
      refine ⟨h0, ?_, ha, hb⟩
      have hsS : ENNReal.ofReal s < (τ : ℝ≥0∞) := by
        rcases h with h | h
        · exact ha.trans_le h
        · exact hb.trans_le h
      rw [← ENNReal.ofReal_coe_nnreal] at hsS
      exact ((ENNReal.ofReal_lt_ofReal_iff'.1 hsS).1).le
    · rintro ⟨h0, hT, ha, hb⟩
      exact ⟨h0, hT.trans (by exact_mod_cast le_min hτt hτσ), ha, hb⟩
  rw [hidx]

end PathFacts

section PathFrozen

variable {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {w : ℝ≥0 → ℝ}
  {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-- On a path of the chain, every point of `ℍ` is swallowed at a positive time (if `ζ > 0`). -/
theorem swallowTime_pos_of_path (hP : IsIntegratedSLEPath 4 xL xR ρL ρR w vL vR b ζ) (hζ : 0 < ζ)
    {y : ℂ} (hy : 0 < y.im) : 0 < swallowTime (Ito.rpath w) y := by
  have h0 : ((0 : ℝ≥0) : ℝ≥0∞) < ζ := by rwa [ENNReal.coe_zero]
  have := lt_swallowTime_of_path hP h0 hy (by
    have := Ito.exists_isForwardSol_zero (Ito.rpath w) hy
    simpa using this)
  simpa using this

/-- **Frozen paths are continuous and bounded** on a path of the chain on which the frozen value exists. -/
theorem frozenMean_path_facts (hP : IsIntegratedSLEPath 4 xL xR ρL ρR w vL vR b ζ) {σ : ℝ≥0}
    (hσ : (σ : ℝ≥0∞) < ζ) {y : ℂ} (hy : 0 < y.im)
    (hL : swallowTime (Ito.rpath w) y ≤ σ →
      Tendsto (fun r => meanAt ρL ρR w vL vR r y) (𝓝[<] (swallowTime (Ito.rpath w) y).toNNReal)
        (𝓝 (frozenMean ρL ρR w vL vR σ y))) :
    Continuous (fun t => frozenMean ρL ρR w vL vR (min t σ) y) ∧
      ∀ t, |frozenMean ρL ρR w vL vR (min t σ) y| ≤ meanBound ρL ρR := by
  set S := swallowTime (Ito.rpath w) y with hSdef
  set g : ℝ≥0 → ℝ := fun r => meanAt ρL ρR w vL vR r y with hgdef
  have hSpos : 0 < S := swallowTime_pos_of_path hP (bot_le.trans_lt hσ) hy
  have hfr : ∀ T : ℝ≥0, ¬ ((T : ℝ≥0∞) < S) →
      frozenMean ρL ρR w vL vR T y = limUnder (𝓝[<] S.toNNReal) g := fun T hT => by
    simp only [frozenMean, ← hSdef, hT, ↓reduceIte]; rfl
  have hL' : S ≤ σ → Tendsto g (𝓝[<] S.toNNReal) (𝓝 (limUnder (𝓝[<] S.toNNReal) g)) := fun h => by
    rw [← hfr σ (not_lt.2 h)]; exact hL h
  have hg : ∀ T : ℝ≥0, (T : ℝ≥0∞) < S → T ≤ σ → ContinuousOn g (Icc 0 T) := fun T hTS hTσ =>
    continuousOn_meanAt hP (lt_of_le_of_lt (by exact_mod_cast hTσ) hσ) hy
      (QuantumZipper.exists_isForwardSol_of_not_mem_fwdHull T.coe_nonneg hy fun h => by
        have := h.2; rw [ENNReal.ofReal_coe_nnreal] at this; exact absurd hTS (not_lt.2 this))
  refine ⟨?_, fun t => ?_⟩
  · have := continuous_frozen_path hg hL'
    refine this.congr fun t => ?_
    simp only [frozenMean]
    rfl
  · by_cases ht : ((min t σ : ℝ≥0) : ℝ≥0∞) < S
    · simp only [frozenMean, ← hSdef, ht, ↓reduceIte]
      exact abs_condMean_le _ _ _ _ _
    · rw [hfr _ ht]
      have hSσ : S ≤ σ := (not_lt.1 ht).trans (by exact_mod_cast min_le_right t σ)
      have hSt : S ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hSσ
      have hne : NeBot (𝓝[<] S.toNNReal) := nhdsLT_neBot_of_exists_lt ⟨0, by
        rw [← ENNReal.coe_lt_coe, ENNReal.coe_toNNReal hSt]; exact_mod_cast hSpos⟩
      exact le_of_tendsto ((continuous_abs.tendsto _).comp (hL' hSσ))
        (Eventually.of_forall fun r => abs_condMean_le _ _ _ _ _)

/-- **Convergence of the Green kernel to the retained kernel** along localizing times. -/
theorem tendsto_greenH_retainedGreen (hP : IsIntegratedSLEPath 4 xL xR ρL ρR w vL vR b ζ)
    {σ : ℝ≥0} (hσ : (σ : ℝ≥0∞) < ζ) {y z : ℂ} (hy : 0 < y.im) (hz : 0 < z.im) (hyz : y ≠ z)
    {ρ : ℕ → ℝ≥0} (hmono : Monotone ρ) (hρσ : ∀ n, ρ n ≤ σ)
    (hal : ∀ n, (∃ v, IsForwardSol (Ito.rpath w) y (ρ n) v) ∧ ∃ v, IsForwardSol (Ito.rpath w) z (ρ n) v)
    (hexh : ∀ t : ℝ≥0, t ≤ σ → (∃ v, IsForwardSol (Ito.rpath w) y t v) →
      (∃ v, IsForwardSol (Ito.rpath w) z t v) → ∀ᶠ n in atTop, t ≤ ρ n)
    (hbdd : BddAbove (range ρ)) (t : ℝ≥0) :
    Tendsto (fun n => greenH (fwdMap (Ito.rpath w) (min t (ρ n) : ℝ≥0) y)
      (fwdMap (Ito.rpath w) (min t (ρ n) : ℝ≥0) z)) atTop
      (𝓝 (retainedGreen w (min t (⨆ n, ρ n)) y z)) := by
  obtain ⟨T', hσT', hT'ζ⟩ := exists_between_lt_lifetime hσ
  have hwc : ContinuousOn (Ito.rpath w) (Icc 0 (T' : ℝ)) := Ito.continuousOn_rpath hP.2.2.2.1 hT'ζ
  set W' := Ito.clampDrv (Ito.rpath w) T' with hW'def
  have hW'c : Continuous W' := Ito.continuous_clampDrv T'.coe_nonneg hwc
  have heq : EqOn (Ito.rpath w) W' (Icc 0 (T' : ℝ)) := fun s hs => (Ito.clampDrv_eqOn hs).symm
  set τ := ⨆ n, ρ n with hτdef
  have hτσ : τ ≤ σ := ciSup_le hρσ
  have hτT' : ((min t τ : ℝ≥0) : ℝ) < T' := by
    have : min t τ < T' := (min_le_right _ _).trans_lt (hτσ.trans_lt hσT')
    exact_mod_cast this
  have hVe : K3.VTe (Ito.rpath w) (min t τ : ℝ≥0) y z = K3.VTe W' (min t τ : ℝ≥0) y z :=
    VTe_eq_of_eqOn hτT' hwc hW'c.continuousOn heq hy hz
  -- the localized times are admissible and cofinal for the clamped driver
  have hmem : ∀ n, ((min t (ρ n) : ℝ≥0) : ℝ) ∈ K3.vtIdx W' (min t τ : ℝ≥0) y z := by
    intro n
    have hle : min t (ρ n) ≤ min t τ := min_le_min le_rfl (le_ciSup hbdd n)
    have hlt : ((min t (ρ n) : ℝ≥0) : ℝ) < T' := lt_of_le_of_lt (by exact_mod_cast hle) hτT'
    have halive : ∀ x : ℂ, 0 < x.im → (∃ v, IsForwardSol (Ito.rpath w) x (ρ n) v) →
        ENNReal.ofReal ((min t (ρ n) : ℝ≥0) : ℝ) < swallowTime W' x := by
      intro x hx ⟨v, hv⟩
      have hv' := isForwardSol_of_le hv (show ((min t (ρ n) : ℝ≥0) : ℝ) ≤ ρ n by
        exact_mod_cast min_le_right _ _)
      have hv'' : IsForwardSol W' x ((min t (ρ n) : ℝ≥0) : ℝ) v :=
        (Ito.isForwardSol_iff_of_eqOn (heq.mono (Icc_subset_Icc_right hlt.le)) v).1 hv'
      exact lt_swallowTime_of_isForwardSol (min t (ρ n)).coe_nonneg hlt hW'c.continuousOn hx ⟨v, hv''⟩
    exact ⟨(min t (ρ n)).coe_nonneg, by exact_mod_cast hle, halive y hy (hal n).1,
      halive z hz (hal n).2⟩
  have hcof : ∀ s ∈ K3.vtIdx W' (min t τ : ℝ≥0) y z, ∃ n, s ≤ ((min t (ρ n) : ℝ≥0) : ℝ) := by
    rintro s ⟨h0, hsT, ha, hb⟩
    have hsT' : s < T' := lt_of_le_of_lt hsT hτT'
    have hsol : ∀ x : ℂ, 0 < x.im → ENNReal.ofReal s < swallowTime W' x →
        ∃ v, IsForwardSol (Ito.rpath w) x ((⟨s, h0⟩ : ℝ≥0) : ℝ) v := by
      intro x hx hlt
      obtain ⟨u, hu⟩ := QuantumZipper.exists_isForwardSol_of_not_mem_fwdHull h0 hx
        (fun h => (not_le.2 hlt) h.2)
      exact ⟨u, (Ito.isForwardSol_iff_of_eqOn (heq.mono (Icc_subset_Icc_right hsT'.le)) u).2 hu⟩
    have hsσ : (⟨s, h0⟩ : ℝ≥0) ≤ σ := by
      have : s ≤ σ := hsT.trans (by exact_mod_cast (min_le_right t τ).trans hτσ)
      exact_mod_cast this
    obtain ⟨n, hn⟩ := (hexh ⟨s, h0⟩ hsσ (hsol y hy ha) (hsol z hz hb)).exists
    refine ⟨n, ?_⟩
    have hst : s ≤ t := hsT.trans (by exact_mod_cast min_le_left t τ)
    have : (⟨s, h0⟩ : ℝ≥0) ≤ min t (ρ n) := le_min (by exact_mod_cast hst) hn
    exact_mod_cast this
  have hmonoT : Monotone fun n => ((min t (ρ n) : ℝ≥0) : ℝ) := fun m n hmn => by
    exact_mod_cast min_le_min le_rfl (hmono hmn)
  have hconv := (K3.tendsto_vtKer_VTe hW'c hy hz hmonoT hmem hcof).2
  -- back to real values
  have hfin : K3.VTe W' (min t τ : ℝ≥0) y z ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (iInf₂_le _ (hmem 0))
  have hreal := (ENNReal.tendsto_toReal hfin).comp hconv
  have hval : ∀ n, (K3.vtKer W' ((min t (ρ n) : ℝ≥0) : ℝ) y z).toReal =
      greenH (fwdMap (Ito.rpath w) (min t (ρ n) : ℝ≥0) y) (fwdMap (Ito.rpath w) (min t (ρ n) : ℝ≥0) z) := by
    intro n
    have hle : ((min t (ρ n) : ℝ≥0) : ℝ) ≤ T' := (hmem n).2.1.trans hτT'.le
    simp only [K3.vtKer, ← Ito.fwdMap_congr_of_eqOn_of_le heq hle]
    rw [ENNReal.toReal_ofReal]
    have hr : ((min t (ρ n) : ℝ≥0) : ℝ≥0∞) < ζ := lt_of_le_of_lt
      (by exact_mod_cast (min_le_right t (ρ n)).trans (hρσ n)) hσ
    obtain ⟨v, hv⟩ := (hal n).1
    obtain ⟨v', hv'⟩ := (hal n).2
    exact (greenH_fwdMap_mem_Icc_of_path hP hr hy hz hyz
      ⟨v, isForwardSol_of_le hv (by exact_mod_cast min_le_right _ _)⟩
      ⟨v', isForwardSol_of_le hv' (by exact_mod_cast min_le_right _ _)⟩).1
  rw [show retainedGreen w (min t τ) y z = (K3.VTe W' (min t τ : ℝ≥0) y z).toReal by
    rw [retainedGreen, K3.VT, hVe]]
  exact hreal.congr fun n => hval n

end PathFrozen




/-! ### The frozen two-point martingale -/

section Two

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **Lemma 3.6, pointwise part: the frozen two-point martingale.** For distinct deterministic `y, z ∈ ℍ` and a
bounded stopping time `σ₀ < T` of the usual augmentation, `η̄_{t∧σ₀}(y) η̄_{t∧σ₀}(z) + G_{U_{t∧σ₀}}(y, z)` agrees
almost surely with a martingale (frozen means, retained Green kernel). -/
theorem exists_martingale_frozenMean_mul_add_retainedGreen [IsProbabilityMeasure P]
    (hE : IsMarkedChain xL xR ρL ρR P 𝓕 W VL VR B ζ) {y z : ℂ} (hy : 0 < y.im) (hz : 0 < z.im)
    (hyz : y ≠ z) {σ₀ : Ω → ℝ≥0}
    (hσ₀ : IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (σ₀ ω : WithTop ℝ≥0))
    (hσ₀ζ : ∀ᵐ ω ∂P, (σ₀ ω : ℝ≥0∞) < ζ ω) {N : ℝ≥0} (hσ₀N : ∀ ω, σ₀ ω ≤ N) :
    ∃ M : ℝ≥0 → Ω → ℝ, Martingale M (usualAugmentation 𝓕 P) P ∧ ∀ᵐ ω ∂P, ∀ t,
      M t ω = frozenMean ρL ρR (W · ω) (fun i => (VL i · ω)) (fun i => (VR i · ω)) (min t (σ₀ ω)) y *
          frozenMean ρL ρR (W · ω) (fun i => (VL i · ω)) (fun i => (VR i · ω)) (min t (σ₀ ω)) z +
        retainedGreen (W · ω) (min t (σ₀ ω)) y z := by
  set C := meanBound ρL ρR with hCdef
  have hC0 : 0 ≤ C := meanBound_nonneg ρL ρR
  set fr : ℂ → Ω → ℝ≥0 → ℝ := fun x ω t =>
    frozenMean ρL ρR (W · ω) (fun i => (VL i · ω)) (fun i => (VR i · ω)) (min t (σ₀ ω)) x with hfrdef
  -- the one-point frozen martingales
  obtain ⟨hLy, Ny0, hNy0, hNy0e⟩ := exists_martingale_frozenMean (ρL := ρL) (ρR := ρR) hE hy hσ₀ hσ₀ζ hσ₀N
  obtain ⟨hLz, Nz0, hNz0, hNz0e⟩ := exists_martingale_frozenMean (ρL := ρL) (ρR := ρR) hE hz hσ₀ hσ₀ζ hσ₀N
  -- the two-point localization
  obtain ⟨ρ, hst, hle, hmono, hprot, hex, hM⟩ := exists_localizing_meanAt_mul_add_greenH hE hy hz hyz
    (σ₀ := fun _ => σ₀) (fun _ => hσ₀) (fun ω => monotone_const) (fun _ => hσ₀ζ)
  choose M2 hM2 hM2e using fun n => (hM n).1
  have hρN : ∀ n ω, ρ n ω ≤ N := fun n ω => (hle n ω).trans (hσ₀N ω)
  set τ : Ω → ℝ≥0 := fun ω => ⨆ n, ρ n ω with hτdef
  have hτst : IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (τ ω : WithTop ℝ≥0) :=
    isStoppingTime_iSup_coe hst hρN
  have hbdd : ∀ ω, BddAbove (range fun n => ρ n ω) := fun ω =>
    ⟨N, by rintro _ ⟨n, rfl⟩; exact hρN n ω⟩
  have hτσ : ∀ ω, τ ω ≤ σ₀ ω := fun ω => ciSup_le fun n => hle n ω
  have hρtend : ∀ ω, Tendsto (fun n => ρ n ω) atTop (𝓝 (τ ω)) := fun ω =>
    tendsto_atTop_ciSup (hmono ω) (hbdd ω)
  -- the good set
  set G : Set Ω := {ω | IsIntegratedSLEPath 4 xL xR ρL ρR (W · ω) (fun i => (VL i · ω))
      (fun i => (VR i · ω)) (B · ω) (ζ ω) ∧ (σ₀ ω : ℝ≥0∞) < ζ ω ∧
    (∀ n, (ρ n ω : ℝ≥0∞) < ζ ω ∧ (∃ v, IsForwardSol (Ito.rpath (W · ω)) y (ρ n ω) v) ∧
      ∃ v, IsForwardSol (Ito.rpath (W · ω)) z (ρ n ω) v) ∧
    (∀ (j : ℕ) (t : ℝ≥0), t ≤ σ₀ ω → (∃ v, IsForwardSol (Ito.rpath (W · ω)) y t v) →
      (∃ v, IsForwardSol (Ito.rpath (W · ω)) z t v) → ∀ᶠ n in atTop, t ≤ ρ n ω) ∧
    (∀ n t, M2 n t ω =
      meanAt ρL ρR (W · ω) (fun i => (VL i · ω)) (fun i => (VR i · ω)) (min t (ρ n ω)) y *
        meanAt ρL ρR (W · ω) (fun i => (VL i · ω)) (fun i => (VR i · ω)) (min t (ρ n ω)) z +
      greenH (fwdMap (fun s : ℝ => W s.toNNReal ω) (min t (ρ n ω) : ℝ≥0) y)
        (fwdMap (fun s : ℝ => W s.toNNReal ω) (min t (ρ n ω) : ℝ≥0) z)) ∧
    (∀ t, Ny0 t ω = fr y ω t) ∧ (∀ t, Nz0 t ω = fr z ω t) ∧
    (swallowTime (Ito.rpath (W · ω)) y ≤ σ₀ ω →
      Tendsto (fun r => meanAt ρL ρR (W · ω) (fun i => (VL i · ω)) (fun i => (VR i · ω)) r y)
        (𝓝[<] (swallowTime (Ito.rpath (W · ω)) y).toNNReal)
        (𝓝 (frozenMean ρL ρR (W · ω) (fun i => (VL i · ω)) (fun i => (VR i · ω)) (σ₀ ω) y))) ∧
    (swallowTime (Ito.rpath (W · ω)) z ≤ σ₀ ω →
      Tendsto (fun r => meanAt ρL ρR (W · ω) (fun i => (VL i · ω)) (fun i => (VR i · ω)) r z)
        (𝓝[<] (swallowTime (Ito.rpath (W · ω)) z).toNNReal)
        (𝓝 (frozenMean ρL ρR (W · ω) (fun i => (VL i · ω)) (fun i => (VR i · ω)) (σ₀ ω) z)))}
    with hGdef
  have hG : ∀ᵐ ω ∂P, ω ∈ G := by
    filter_upwards [hE.2.2.2.2, hσ₀ζ, ae_all_iff.2 hprot, hex, ae_all_iff.2 hM2e, hNy0e, hNz0e, hLy,
      hLz] with ω h1 h2 h3 h4 h5 h6 h7 h8 h9
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  set N0 := toMeasurable P Gᶜ with hN0def
  have hN0c : ∀ ω, ω ∉ N0 → ω ∈ G := fun ω hω => by
    by_contra h
    exact hω (subset_toMeasurable _ _ h)
  have hN00 : P N0 = 0 := by rw [hN0def, measure_toMeasurable]; exact ae_iff.1 hG
  -- continuous versions of the one-point martingales
  set Ny : ℝ≥0 → Ω → ℝ := fun t => N0ᶜ.indicator (Ny0 t) with hNydef
  set Nz : ℝ≥0 → Ω → ℝ := fun t => N0ᶜ.indicator (Nz0 t) with hNzdef
  have hNy : Martingale Ny (usualAugmentation 𝓕 P) P := martingale_indicator_compl_toMeasurable hNy0 hG
  have hNz : Martingale Nz (usualAugmentation 𝓕 P) P := martingale_indicator_compl_toMeasurable hNz0 hG
  have hNyv : ∀ t ω, ω ∉ N0 → Ny t ω = fr y ω t := fun t ω hω => by
    simp only [hNydef, Set.indicator_of_mem (show ω ∈ N0ᶜ from hω)]; exact (hN0c ω hω).2.2.2.2.2.1 t
  have hNzv : ∀ t ω, ω ∉ N0 → Nz t ω = fr z ω t := fun t ω hω => by
    simp only [hNzdef, Set.indicator_of_mem (show ω ∈ N0ᶜ from hω)]; exact (hN0c ω hω).2.2.2.2.2.2.1 t
  have hNy0' : ∀ t ω, ω ∈ N0 → Ny t ω = 0 := fun t ω hω =>
    Set.indicator_of_notMem (by simpa using hω) _
  have hNz0' : ∀ t ω, ω ∈ N0 → Nz t ω = 0 := fun t ω hω =>
    Set.indicator_of_notMem (by simpa using hω) _
  have hfy : ∀ ω, ω ∉ N0 → Continuous (fr y ω) ∧ ∀ t, |fr y ω t| ≤ C := fun ω hω =>
    frozenMean_path_facts (hN0c ω hω).1 (hN0c ω hω).2.1 hy (hN0c ω hω).2.2.2.2.2.2.2.1
  have hfz : ∀ ω, ω ∉ N0 → Continuous (fr z ω) ∧ ∀ t, |fr z ω t| ≤ C := fun ω hω =>
    frozenMean_path_facts (hN0c ω hω).1 (hN0c ω hω).2.1 hz (hN0c ω hω).2.2.2.2.2.2.2.2
  have hNyc : ∀ ω, Continuous fun t => Ny t ω := fun ω => by
    by_cases hω : ω ∈ N0
    · simp only [hNy0' _ ω hω]; exact continuous_const
    · simp only [hNyv _ ω hω]; exact (hfy ω hω).1
  have hNzc : ∀ ω, Continuous fun t => Nz t ω := fun ω => by
    by_cases hω : ω ∈ N0
    · simp only [hNz0' _ ω hω]; exact continuous_const
    · simp only [hNzv _ ω hω]; exact (hfz ω hω).1
  have hNyb : ∀ t ω, |Ny t ω| ≤ C := fun t ω => by
    by_cases hω : ω ∈ N0
    · rw [hNy0' t ω hω, abs_zero]; exact hC0
    · rw [hNyv t ω hω]; exact (hfy ω hω).2 t
  have hNzb : ∀ t ω, |Nz t ω| ≤ C := fun t ω => by
    by_cases hω : ω ∈ N0
    · rw [hNz0' t ω hω, abs_zero]; exact hC0
    · rw [hNzv t ω hω]; exact (hfz ω hω).2 t
  have hNyrc : ∀ ω t, ContinuousWithinAt (Ny · ω) (Ici t) t := fun ω t => (hNyc ω).continuousWithinAt
  have hNzrc : ∀ ω t, ContinuousWithinAt (Nz · ω) (Ici t) t := fun ω t => (hNzc ω).continuousWithinAt
  -- pathwise facts at the first stop
  have hdich : ∀ ω, ω ∉ N0 → τ ω = σ₀ ω ∨ swallowTime (Ito.rpath (W · ω)) y ≤ (τ ω : ℝ≥0∞) ∨
      swallowTime (Ito.rpath (W · ω)) z ≤ (τ ω : ℝ≥0∞) := by
    intro ω hω
    have hg := hN0c ω hω
    refine iSup_eq_or_swallow (hbdd ω) (fun n => hle n ω) fun t ht hty htz => hg.2.2.2.1 0 t ht ?_ ?_
    · exact QuantumZipper.exists_isForwardSol_of_not_mem_fwdHull t.coe_nonneg hy fun h => by
        have := h.2; rw [ENNReal.ofReal_coe_nnreal] at this; exact absurd hty (not_lt.2 this)
    · exact QuantumZipper.exists_isForwardSol_of_not_mem_fwdHull t.coe_nonneg hz fun h => by
        have := h.2; rw [ENNReal.ofReal_coe_nnreal] at this; exact absurd htz (not_lt.2 this)
  have hconstY : ∀ ω, ω ∉ N0 → (τ ω = σ₀ ω ∨ swallowTime (Ito.rpath (W · ω)) y ≤ (τ ω : ℝ≥0∞)) →
      ∀ t, τ ω ≤ t → Ny t ω = Ny (τ ω) ω := by
    intro ω hω h t ht
    rw [hNyv t ω hω, hNyv (τ ω) ω hω]
    rcases h with h | h
    · simp only [hfrdef, min_eq_right (h ▸ ht : σ₀ ω ≤ t), h, min_self]
    · exact frozenMean_min_eq_of_swallow h (hτσ ω) ht
  have hconstZ : ∀ ω, ω ∉ N0 → (τ ω = σ₀ ω ∨ swallowTime (Ito.rpath (W · ω)) z ≤ (τ ω : ℝ≥0∞)) →
      ∀ t, τ ω ≤ t → Nz t ω = Nz (τ ω) ω := by
    intro ω hω h t ht
    rw [hNzv t ω hω, hNzv (τ ω) ω hω]
    rcases h with h | h
    · simp only [hfrdef, min_eq_right (h ▸ ht : σ₀ ω ≤ t), h, min_self]
    · exact frozenMean_min_eq_of_swallow h (hτσ ω) ht
  -- the stopped process is a limit of the localized martingales
  set Xτ : ℝ≥0 → Ω → ℝ := fun t ω => Ny (min t (τ ω)) ω * Nz (min t (τ ω)) ω +
    retainedGreen (W · ω) (min t (τ ω)) y z with hXτdef
  have hmeanAt : ∀ ω, ω ∉ N0 → ∀ (x : ℂ) n t, (∃ v, IsForwardSol (Ito.rpath (W · ω)) x (ρ n ω) v) →
      0 < x.im → fr x ω (min t (ρ n ω)) =
        meanAt ρL ρR (W · ω) (fun i => (VL i · ω)) (fun i => (VR i · ω)) (min t (ρ n ω)) x := by
    intro ω hω x n t hal hx
    have hg := hN0c ω hω
    have hlt := lt_swallowTime_of_path hg.1 (hg.2.2.1 n).1 hx hal
    have h1 : min (min t (ρ n ω)) (σ₀ ω) = min t (ρ n ω) :=
      min_eq_left ((min_le_right _ _).trans (hle n ω))
    have h2 : ((min t (ρ n ω) : ℝ≥0) : ℝ≥0∞) < swallowTime (Ito.rpath (W · ω)) x :=
      lt_of_le_of_lt (by exact_mod_cast min_le_right t (ρ n ω)) hlt
    simp only [hfrdef, h1, frozenMean, h2, ↓reduceIte]
  have hlim : ∀ᵐ ω ∂P, (∀ n t, |M2 n t ω| ≤ C * C + greenH y z) ∧
      ∀ t, Tendsto (fun n => M2 n t ω) atTop (𝓝 (Xτ t ω)) := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN00] with ω hω
    have hg := hN0c ω hω
    have hval : ∀ n t, M2 n t ω = Ny (min t (ρ n ω)) ω * Nz (min t (ρ n ω)) ω +
        greenH (fwdMap (fun s : ℝ => W s.toNNReal ω) (min t (ρ n ω) : ℝ≥0) y)
          (fwdMap (fun s : ℝ => W s.toNNReal ω) (min t (ρ n ω) : ℝ≥0) z) := by
      intro n t
      rw [hg.2.2.2.2.1 n t, hNyv _ ω hω, hNzv _ ω hω,
        hmeanAt ω hω y n t (hg.2.2.1 n).2.1 hy, hmeanAt ω hω z n t (hg.2.2.1 n).2.2 hz]
    refine ⟨fun n t => ?_, fun t => ?_⟩
    · rw [hval]
      have hr : ((min t (ρ n ω) : ℝ≥0) : ℝ≥0∞) < ζ ω := lt_of_le_of_lt
        (by exact_mod_cast (min_le_right t (ρ n ω)).trans (hle n ω)) hg.2.1
      obtain ⟨v, hv⟩ := (hg.2.2.1 n).2.1
      obtain ⟨v', hv'⟩ := (hg.2.2.1 n).2.2
      have hG : 0 ≤ greenH (fwdMap (fun s : ℝ => W s.toNNReal ω) (min t (ρ n ω) : ℝ≥0) y)
            (fwdMap (fun s : ℝ => W s.toNNReal ω) (min t (ρ n ω) : ℝ≥0) z) ∧
          greenH (fwdMap (fun s : ℝ => W s.toNNReal ω) (min t (ρ n ω) : ℝ≥0) y)
            (fwdMap (fun s : ℝ => W s.toNNReal ω) (min t (ρ n ω) : ℝ≥0) z) ≤ greenH y z :=
        greenH_fwdMap_mem_Icc_of_path hg.1 hr hy hz hyz
          ⟨v, isForwardSol_of_le hv (by exact_mod_cast min_le_right _ _)⟩
          ⟨v', isForwardSol_of_le hv' (by exact_mod_cast min_le_right _ _)⟩
      have h1 := hNyb (min t (ρ n ω)) ω
      have h2 := hNzb (min t (ρ n ω)) ω
      have h3 : |Ny (min t (ρ n ω)) ω * Nz (min t (ρ n ω)) ω| ≤ C * C := by
        rw [abs_mul]; exact mul_le_mul h1 h2 (abs_nonneg _) hC0
      calc |_ + _| ≤ |Ny (min t (ρ n ω)) ω * Nz (min t (ρ n ω)) ω| +
            |greenH (fwdMap (fun s : ℝ => W s.toNNReal ω) (min t (ρ n ω) : ℝ≥0) y)
              (fwdMap (fun s : ℝ => W s.toNNReal ω) (min t (ρ n ω) : ℝ≥0) z)| := abs_add_le _ _
        _ ≤ C * C + greenH y z := by
          rw [abs_of_nonneg hG.1]; exact add_le_add h3 hG.2
    · simp only [hval]
      have hmin : Tendsto (fun n => min t (ρ n ω)) atTop (𝓝 (min t (τ ω))) :=
        (continuous_const.min continuous_id).continuousAt.tendsto.comp (hρtend ω)
      refine (((hNyc ω).continuousAt.tendsto.comp hmin).mul
        ((hNzc ω).continuousAt.tendsto.comp hmin)).add ?_
      exact tendsto_greenH_retainedGreen hg.1 hg.2.1 hy hz hyz (hmono ω) (fun n => hle n ω)
        (fun n => (hg.2.2.1 n).2) (fun t ht h1 h2 => hg.2.2.2.1 0 t ht h1 h2) (hbdd ω) t
  obtain ⟨Mτ, hMτ, hMτe⟩ := exists_martingale_of_tendsto hM2 hlim
  -- the pasting terms
  have hprogY := isStronglyProgressive_of_rightContinuous hNy.1 hNyrc
  have hprogZ := isStronglyProgressive_of_rightContinuous hNz.1 hNzrc
  have hsv : ∀ (X : ℝ≥0 → Ω → ℝ) ω, stoppedValue X (fun ω => (τ ω : WithTop ℝ≥0)) ω = X (τ ω) ω :=
    fun X ω => by simp only [stoppedValue, WithTop.untopA, WithTop.untopD_coe]
  have hZy : StronglyMeasurable[hτst.measurableSpace] fun ω => Ny (τ ω) ω := by
    have := (measurable_stoppedValue hprogY hτst).stronglyMeasurable
    rwa [show stoppedValue Ny (fun ω => (τ ω : WithTop ℝ≥0)) = fun ω => Ny (τ ω) ω from
      funext (hsv Ny)] at this
  have hZz : StronglyMeasurable[hτst.measurableSpace] fun ω => Nz (τ ω) ω := by
    have := (measurable_stoppedValue hprogZ hτst).stronglyMeasurable
    rwa [show stoppedValue Nz (fun ω => (τ ω : WithTop ℝ≥0)) = fun ω => Nz (τ ω) ω from
      funext (hsv Nz)] at this
  have hP1 := martingale_mul_sub_stopped hNz hNzrc hNzb hτst hZy (fun ω => hNyb (τ ω) ω)
  have hP2 := martingale_mul_sub_stopped hNy hNyrc hNyb hτst hZz (fun ω => hNzb (τ ω) ω)
  refine ⟨Mτ + (fun t ω => Ny (τ ω) ω * (Nz t ω - Nz (min t (τ ω)) ω)) +
      (fun t ω => Nz (τ ω) ω * (Ny t ω - Ny (min t (τ ω)) ω)), (hMτ.add hP1).add hP2, ?_⟩
  filter_upwards [hMτe, measure_eq_zero_iff_ae_notMem.1 hN00] with ω h1 hω t
  simp only [Pi.add_apply, h1 t, hXτdef]
  have e1 : frozenMean ρL ρR (W · ω) (fun i => (VL i · ω)) (fun i => (VR i · ω)) (min t (σ₀ ω)) y =
      Ny t ω := (hNyv t ω hω).symm
  have e2 : frozenMean ρL ρR (W · ω) (fun i => (VL i · ω)) (fun i => (VR i · ω)) (min t (σ₀ ω)) z =
      Nz t ω := (hNzv t ω hω).symm
  rw [e1, e2, retainedGreen_min_eq (hτσ ω) (hdich ω hω) t]
  rcases le_total t (τ ω) with htτ | hτt
  · rw [min_eq_left htτ, sub_self, sub_self, mul_zero, mul_zero, add_zero, add_zero]
  · rw [min_eq_right hτt]
    have hprod : (Ny t ω - Ny (τ ω) ω) * (Nz t ω - Nz (τ ω) ω) = 0 := by
      rcases hdich ω hω with h | h | h
      · rw [hconstY ω hω (Or.inl h) t hτt, sub_self, zero_mul]
      · rw [hconstY ω hω (Or.inr h) t hτt, sub_self, zero_mul]
      · rw [hconstZ ω hω (Or.inr h) t hτt, sub_self, mul_zero]
    linear_combination (-1 : ℝ) * hprod

end Two

end WangWu

end InteractingSLE
