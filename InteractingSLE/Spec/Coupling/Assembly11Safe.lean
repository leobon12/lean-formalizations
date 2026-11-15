import InteractingSLE.Spec.Coupling.SafeCompact

/-!
# Safe stops for any filtration in which the driver is adapted before the lifetime

Packet PROVE-T11-ASM (Theorem 1.1, route R35; obligation 5 of `planning/handoffs/PROVE-T11-L312.md` §4). The frozen
Theorem 1.1 conditions on the stopped σ-algebra of the **driving** filtration (`drivingFiltration`), in which the
Brownian coordinate after the lifetime is not adapted, so the evolution is not an integrated evolution for that
filtration. `exists_safeSeq_of_seq` (PROVE-T11-L312) only uses that the driver is adapted before `ζ` and continuous
on `[0, ζ)` with `W 0 = 0`; this file restates it under exactly these hypotheses, for the usual augmentation of an
arbitrary filtration `𝓗` (for instance `killedDrivingFiltration`). The proof is L312's, with the evolution
hypothesis replaced by the two path facts it uses.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology QuantumZipper
open scoped NNReal ENNReal Classical

namespace InteractingSLE

namespace Coupling

open Ito

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓗 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **Safe stops, adapted form** (`exists_safeSeq_of_seq` for any filtration in which `W` is adapted before `ζ`).
For a compact `K ⊆ ℍ` with `Im ≥ m > 0` on `K`, below a nondecreasing sequence of stopping times `σ₀ n < ζ` of the
usual augmentation of `𝓗`, the level-`n` safe exit times are stopping times of that augmentation, `ρ_n ≤ σ₀ n`,
nondecreasing, safe, and they exhaust every horizon `t ≤ σ₀ j` at which `K` is alive. -/
theorem exists_safeSeq_of_adapted (hWa : AdaptedBefore 𝓗 ζ W)
    (hpath : ∀ᵐ ω ∂P, ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω} ∧ W 0 ω = 0)
    {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ H) {m : ℝ} (hm : 0 < m) (hKm : ∀ z ∈ K, m ≤ z.im)
    {σ₀ : ℕ → Ω → ℝ≥0}
    (hσ₀ : ∀ n, IsStoppingTime (usualAugmentation 𝓗 P) fun ω => (σ₀ n ω : WithTop ℝ≥0))
    (hσ₀m : ∀ ω, Monotone fun n => σ₀ n ω) (hσ₀ζ : ∀ n, ∀ᵐ ω ∂P, (σ₀ n ω : ℝ≥0∞) < ζ ω) :
    ∃ ρ : ℕ → Ω → ℝ≥0,
      (∀ n, IsStoppingTime (usualAugmentation 𝓗 P) fun ω => (ρ n ω : WithTop ℝ≥0)) ∧
      (∀ n ω, ρ n ω ≤ σ₀ n ω) ∧ (∀ ω, Monotone fun n => ρ n ω) ∧
      (∀ n : ℕ, ∀ᵐ ω ∂P, IsSafeAt K (m / ((n : ℝ) + 1)) n (σ₀ n ω) (ζ ω) (W · ω) (ρ n ω)) ∧
      ∀ᵐ ω ∂P, ∀ (j : ℕ) (t : ℝ≥0), t ≤ σ₀ j ω →
        (∀ z ∈ K, ∃ u, IsForwardSol (rpath (W · ω)) z t u) → ∀ᶠ n in atTop, t ≤ ρ n ω := by
  set 𝓖 := usualAugmentation 𝓗 P with h𝓖
  have hWa' : AdaptedBefore 𝓖 ζ W := adaptedBefore_mono (le_usualAugmentation 𝓗 P) hWa
  set good : Ω → Prop := fun ω => (ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω} ∧
      W 0 ω = 0) ∧ ∀ n, (σ₀ n ω : ℝ≥0∞) < ζ ω with hgood
  have hae : ∀ᵐ ω ∂P, good ω := by
    filter_upwards [hpath, ae_all_iff.2 hσ₀ζ] with ω h1 h2 using ⟨h1, h2⟩
  obtain ⟨G, hGm, hGc, hGgood⟩ : ∃ G : Set Ω, MeasurableSet G ∧ P Gᶜ = 0 ∧ ∀ ω ∈ G, good ω := by
    refine ⟨(toMeasurable P {ω | ¬ good ω})ᶜ, (measurableSet_toMeasurable _ _).compl, ?_,
      fun ω hω => ?_⟩
    · rw [compl_compl, measure_toMeasurable]; exact ae_iff.1 hae
    · by_contra h; exact hω (subset_toMeasurable _ _ h)
  have hG : ∀ t, MeasurableSet[𝓖 t] G := fun t => by
    have := (measurableSet_usualAugmentation_of_null (𝓕 := 𝓗) hGm.compl hGc t).compl
    rwa [compl_compl] at this
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := by rw [ae_iff]; exact hGc
  have hwc : ∀ ω ∈ G, ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω} :=
    fun ω hω => (hGgood ω hω).1.1
  obtain ⟨D, hDK, hDc, hKD⟩ :=
    (TopologicalSpace.IsSeparable.of_separableSpace K).exists_countable_dense_subset
  have hδ : ∀ n : ℕ, 0 < m / ((n : ℝ) + 1) := fun n => by positivity
  set ρ : ℕ → Ω → ℝ≥0 := fun n ω => if ω ∈ G then
    safeExitTime K (m / ((n : ℝ) + 1)) n (σ₀ n ω) (ζ ω) (W · ω) else 0 with hρ
  have hDiff : ∀ ω ∈ G, ∀ n : ℕ, ∀ d : ℝ≥0,
      IsSafeAt K (m / ((n : ℝ) + 1)) n (σ₀ n ω) (ζ ω) (W · ω) d ↔
        IsSafeAt D (m / ((n : ℝ) + 1)) n (σ₀ n ω) (ζ ω) (W · ω) d := fun ω hω n d =>
    ⟨fun h => h.subset hDK, fun h => h.of_dense (hwc ω hω) hKH hKD hDK (hδ n)⟩
  refine ⟨ρ, fun n => ?_, fun n ω => ?_, fun ω => ?_, fun n => ?_, ?_⟩
  · -- stopping times
    obtain ⟨T, hTc, hTd⟩ := TopologicalSpace.exists_countable_dense ℝ≥0
    refine isStoppingTime_of_measurableSet_lt_of_isRightContinuous fun t => ?_
    have heq : {ω | ((ρ n ω : ℝ≥0) : WithTop ℝ≥0) < (t : WithTop ℝ≥0)} =
        (⋃ d ∈ T ∩ Iio t, G \ {ω | ω ∈ G ∧
          IsSafeAt D (m / ((n : ℝ) + 1)) n (σ₀ n ω) (ζ ω) (W · ω) d}) ∪
          (Gᶜ ∩ {_ω | (0 : ℝ≥0) < t}) := by
      ext ω
      simp only [mem_ofPred_eq, WithTop.coe_lt_coe, mem_union, mem_iUnion, mem_inter_iff,
        Set.mem_sdiff, mem_Iio, exists_prop, mem_compl_iff]
      by_cases hω : ω ∈ G
      · simp only [hρ, hω, ↓reduceIte, true_and, not_true_eq_false, false_and, or_false]
        rw [safeExitTime_lt_iff (hwc ω hω) hKH hTd]
        constructor
        · rintro ⟨d, hd, hdt, hnp⟩; exact ⟨d, ⟨hd, hdt⟩, fun h => hnp ((hDiff ω hω n d).2 h)⟩
        · rintro ⟨d, ⟨hd, hdt⟩, hnp⟩; exact ⟨d, hd, hdt, fun h => hnp ((hDiff ω hω n d).1 h)⟩
      · simp only [hρ, hω, ↓reduceIte, false_and, and_false, exists_false, false_or,
          not_false_eq_true, true_and]
    rw [heq]
    refine MeasurableSet.union (MeasurableSet.biUnion (hTc.mono inter_subset_left) fun d hd => ?_)
      ((hG t).compl.inter (MeasurableSet.const _))
    exact 𝓖.mono hd.2.le _ ((hG d).diff (measurableSet_isSafeAt hWa' hwc (hG 0) hDc
      (hDK.trans hKH) (hσ₀ n) _ _ d))
  · -- below σ₀
    by_cases hω : ω ∈ G
    · simp only [hρ, hω, ↓reduceIte]; exact safeExitTime_le_sigma
    · simp only [hρ, hω, ↓reduceIte]; exact zero_le
  · -- monotone
    intro n n' hnn'
    by_cases hω : ω ∈ G
    · simp only [hρ, hω, ↓reduceIte]
      have hn : (n : ℝ) ≤ n' := by exact_mod_cast hnn'
      exact safeExitTime_mono (div_le_div_of_nonneg_left hm.le (by positivity) (by linarith)) hn
        (hσ₀m ω hnn')
    · simp only [hρ, hω, ↓reduceIte]; exact le_rfl
  · -- safety at the stop
    filter_upwards [hGae] with ω hω
    simp only [hρ, hω, ↓reduceIte]
    obtain ⟨⟨-, hw0⟩, hσζ⟩ := hGgood ω hω
    have hζ0 : 0 < ζ ω := lt_of_le_of_lt (by exact_mod_cast zero_le) (hσζ n)
    have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [n.cast_nonneg (α := ℝ)]
    exact isSafeAt_safeExitTime (hwc ω hω) hKH (hδ n) (hσζ n)
      (isSafeAt_zero hKH (fun z hz => (div_le_self hm.le hn1).trans (hKm z hz)) hw0 hζ0
        n.cast_nonneg)
  · -- exhaustion
    filter_upwards [hGae] with ω hω j t htσ halive
    have htζ : (t : ℝ≥0∞) < ζ ω := lt_of_le_of_lt (by exact_mod_cast htσ) ((hGgood ω hω).2 j)
    have hev := eventually_le_safeExitTime (hwc ω hω) hK hKH m htσ htζ halive
    filter_upwards [hev, eventually_ge_atTop j] with n hn hjn
    simp only [hρ, hω, ↓reduceIte]
    exact hn.trans (safeExitTime_mono le_rfl le_rfl (hσ₀m ω hjn))

end Coupling

end InteractingSLE
