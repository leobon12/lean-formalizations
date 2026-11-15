/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.AnnouncePath
import InteractingSLE.Spec.Sec2.CriticalLifetime
import InteractingSLE.Spec.Sec2.GirsanovCut

/-!
# The lifetime of an integrated evolution has an announcing sequence

Packet PROVE-T11-ANN: obligation 1 of `planning/handoffs/PROVE-T11-L312.md` §4, the driving prerequisite (1.2) of
Theorem 1.1 by the route of ruling R35 (`source/external/AstraIG1/ig1_formalization_proofs.pdf` §1: "an increasing
sequence of finite announcing stopping times `T_n < T_*`, `T_n ↑ T_*`, `T_n ≤ n`", supplied by "Aux. 3's continuous
terminal-state and predictability result"; Specification p. 24, node `SPEC.thm-1.1#announcing-sequence`).

For an integrated `SLE_κ(ρ)` evolution with an admissible seed, the lifetime `ζ` has an announcing sequence of
stopping times of the usual augmentation of the evolution's filtration (`exists_isAnnouncingSeq`). The candidates are
the hitting times of `AnnouncePath` (open-set hitting times of the killed state, hence stopping times of the
right-continuous augmentation, `isStoppingTime_hitBelow_state`), indexed by `p = Nat.pair c m` with `c` a left
cluster `c < nL` or a right cluster `nL + j` (by the reflection `x ↦ −x`); the abstract selection of
`AnnounceSelect` turns them into an announcing sequence. The direct route of the packet: Aux. 3's terminal state
(`IsIntegratedSLEEvolution.ae_tendsto_threshold`), hitting times per cluster, merged marks stay merged — no general
predictable-time theory.

## Main results

* `isStoppingTime_hitBelow_state`: the first time before `ζ` at which a continuous functional of the state is below
  a level is a stopping time of every right-continuous filtration to which the state is adapted before `ζ`;
* `candTime`: the candidates along one path, with `candTime_lt_of_bdd`, `exists_eventually_le_candTime`,
  `exists_bdd_candTime`;
* **`exists_isAnnouncingSeq`**: `∃ T, IsAnnouncingSeq (usualAugmentation 𝓕 P) P ζ T`; `exists_isAnnouncingSeq_le`
  adds `T_n ≤ n`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Coupling

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-! ### Hitting times of the killed state are stopping times -/

section StoppingTime

variable {nL nR : ℕ} {𝓖 : Filtration ℝ≥0 mΩ} {ζ : Ω → ℝ≥0∞} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}

/-- The state `(W_s, V^L_s, V^R_s)` of the driving evolution. -/
def stateAt (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (s : ℝ≥0)
    (ω : Ω) : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) :=
  (W s ω, fun i => VL i s ω, fun i => VR i s ω)

/-- `{d < ζ, Φ(state_d) < ε}` is an event of `𝓖_d` for a continuous functional `Φ`. -/
theorem measurableSet_lt_zeta_and_lt (hW : AdaptedBefore 𝓖 ζ W) (hVL : ∀ i, AdaptedBefore 𝓖 ζ (VL i))
    (hVR : ∀ i, AdaptedBefore 𝓖 ζ (VR i)) {Φ : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) → ℝ}
    (hΦ : Continuous Φ) (ε : ℝ) (d : ℝ≥0) :
    MeasurableSet[𝓖 d] {ω | (d : ℝ≥0∞) < ζ ω ∧ Φ (stateAt W VL VR d ω) < ε} := by
  set K : Ω → ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) := fun ω =>
    (Girsanov.killed ζ W d ω, fun i => Girsanov.killed ζ (VL i) d ω,
      fun i => Girsanov.killed ζ (VR i) d ω) with hK_def
  have hK : Measurable[𝓖 d] K :=
    (Girsanov.measurable_killed hW d).prodMk
      ((@Measurable.of_eval Ω (Fin nL) (fun _ => ℝ) (𝓖 d) _ _ fun i =>
          Girsanov.measurable_killed (hVL i) d).prodMk
        (@Measurable.of_eval Ω (Fin nR) (fun _ => ℝ) (𝓖 d) _ _ fun i =>
          Girsanov.measurable_killed (hVR i) d))
  have hζ : MeasurableSet[𝓖 d] {ω | (d : ℝ≥0∞) < ζ ω} := by
    simpa using hW d univ MeasurableSet.univ
  have heq : {ω | (d : ℝ≥0∞) < ζ ω ∧ Φ (stateAt W VL VR d ω) < ε} =
      {ω | (d : ℝ≥0∞) < ζ ω} ∩ (Φ ∘ K) ⁻¹' Iio ε := by
    ext ω
    simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage, Function.comp_apply, mem_Iio]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      simpa only [hK_def, stateAt, Girsanov.killed_of_lt h1] using h2
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      simpa only [hK_def, stateAt, Girsanov.killed_of_lt h1] using h2
  rw [heq]
  exact hζ.inter ((hΦ.measurable.comp hK) measurableSet_Iio)

open scoped Classical in
/-- **Hitting times of the killed state are stopping times**: on an event `G ∈ 𝓖_0` on which the state is
continuous before `ζ`, the first time before `ζ` at which `Φ(state) < ε` (`⊤` off `G`) is a stopping time of the
right-continuous filtration `𝓖`. -/
theorem isStoppingTime_hitBelow_state [𝓖.IsRightContinuous] (hW : AdaptedBefore 𝓖 ζ W)
    (hVL : ∀ i, AdaptedBefore 𝓖 ζ (VL i)) (hVR : ∀ i, AdaptedBefore 𝓖 ζ (VR i)) {G : Set Ω}
    (hG : MeasurableSet[𝓖 0] G)
    (hGc : ∀ ω ∈ G, ContinuousOn (fun s => stateAt W VL VR s ω) {s : ℝ≥0 | (s : ℝ≥0∞) < ζ ω})
    {Φ : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) → ℝ} (hΦ : Continuous Φ) (ε : ℝ) :
    IsStoppingTime 𝓖 fun ω =>
      if ω ∈ G then hitBelow (fun s => Φ (stateAt W VL VR s ω)) (ζ ω) ε else ⊤ := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense ℝ≥0
  refine isStoppingTime_of_measurableSet_lt_of_isRightContinuous fun t => ?_
  have heq : {ω | (if ω ∈ G then hitBelow (fun s => Φ (stateAt W VL VR s ω)) (ζ ω) ε else ⊤) <
      (t : WithTop ℝ≥0)} = G ∩ ⋃ d ∈ D ∩ Iio t,
        {ω | (d : ℝ≥0∞) < ζ ω ∧ Φ (stateAt W VL VR d ω) < ε} := by
    ext ω
    by_cases hω : ω ∈ G
    · simp only [hω, ite_true, mem_ofPred_eq, mem_inter_iff, true_and, mem_iUnion, mem_Iio,
        exists_prop]
      rw [hitBelow_lt_iff (f := fun s => Φ (stateAt W VL VR s ω)) (hΦ.comp_continuousOn (hGc ω hω))
        hDd]
      constructor
      · rintro ⟨d, hdD, hdt, hdζ, hfd⟩
        exact ⟨d, ⟨hdD, hdt⟩, hdζ, hfd⟩
      · rintro ⟨d, ⟨hdD, hdt⟩, hdζ, hfd⟩
        exact ⟨d, hdD, hdt, hdζ, hfd⟩
    · simp only [hω, ite_false, mem_ofPred_eq, mem_inter_iff, false_and, iff_false, not_lt]
      exact le_top
  rw [heq]
  exact (𝓖.mono (zero_le (a := t)) _ hG).inter
    (MeasurableSet.biUnion (hDc.mono inter_subset_left) fun d hd =>
      𝓖.mono (le_of_lt hd.2) _ (measurableSet_lt_zeta_and_lt hW hVL hVR hΦ ε d))

theorem isStoppingTime_top' : IsStoppingTime 𝓖 fun _ : Ω => (⊤ : WithTop ℝ≥0) := fun i => by
  simp only [top_le_iff, WithTop.coe_ne_top, ofPred_false]
  exact @MeasurableSet.empty _ (𝓖 i)

end StoppingTime

/-! ### The candidates along one path -/

section Candidates

open Sec2

variable {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-- **The candidates along one path**, indexed by `p = Nat.pair c m`: a code `c < nL` is the left cluster
`{0, …, c}`, a code `nL + j` the right cluster `{0, …, j}` (through the reflection `x ↦ −x`, which exchanges the
sides), at gap level `m`; other codes give `⊤`. -/
def candTime (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (w : ℝ≥0 → ℝ) (vL : Fin nL → ℝ≥0 → ℝ)
    (vR : Fin nR → ℝ≥0 → ℝ) (ζ : ℝ≥0∞) (p k : ℕ) : WithTop ℝ≥0 :=
  if hc : (Nat.unpair p).1 < nL then hitL ρL w vL ζ ⟨(Nat.unpair p).1, hc⟩ (Nat.unpair p).2 k
  else if hc' : (Nat.unpair p).1 - nL < nR then
    hitL ρR (-w) (fun i => -vR i) ζ ⟨(Nat.unpair p).1 - nL, hc'⟩ (Nat.unpair p).2 k
  else ⊤

theorem candTime_mono (p : ℕ) : Monotone fun k => candTime ρL ρR w vL vR ζ p k := by
  by_cases hc : (Nat.unpair p).1 < nL
  · simp only [candTime, hc, ↓reduceDIte]
    exact hitL_mono _ _ _ _ _ _
  by_cases hc' : (Nat.unpair p).1 - nL < nR
  · simp only [candTime, hc, hc', ↓reduceDIte]
    exact hitL_mono _ _ _ _ _ _
  · simp only [candTime, hc, hc', ↓reduceDIte]
    exact monotone_const

/-- A bounded candidate stays strictly below `ζ`. -/
theorem candTime_lt_of_bdd {p : ℕ}
    (hb : ∃ M : ℕ, ∀ k, candTime ρL ρR w vL vR ζ p k ≤ ((M : ℝ≥0) : WithTop ℝ≥0)) (k : ℕ) :
    ∃ t : ℝ≥0, candTime ρL ρR w vL vR ζ p k = t ∧ (t : ℝ≥0∞) < ζ := by
  by_cases hc : (Nat.unpair p).1 < nL
  · simp only [candTime, hc, ↓reduceDIte] at hb ⊢
    exact (hitL_lt_of_bdd hb).2 k
  by_cases hc' : (Nat.unpair p).1 - nL < nR
  · simp only [candTime, hc, hc', ↓reduceDIte] at hb ⊢
    exact (hitL_lt_of_bdd hb).2 k
  · simp only [candTime, hc, hc', ↓reduceDIte, top_le_iff] at hb
    obtain ⟨M, hM⟩ := hb
    exact absurd (hM 0) WithTop.coe_ne_top

/-- For one left cluster, all bounded candidates (every gap level) eventually pass a time `t < ζ`, from one index
on: they all equal the hitting sequence of `|w − v^j|`. -/
theorem eventually_le_hitL_of_bdd (h : IsForcePath xL xR ρL ρR w vL vR ζ) (j : Fin nL) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < ζ) :
    ∀ᶠ K : ℕ in atTop, ∀ m, (∃ M : ℕ, ∀ k, hitL ρL w vL ζ j m k ≤ ((M : ℝ≥0) : WithTop ℝ≥0)) →
      ∀ k, K ≤ k → (t : WithTop ℝ≥0) ≤ hitL ρL w vL ζ j m k := by
  by_cases hex : ∃ m₀, ∃ M : ℕ, ∀ k, hitL ρL w vL ζ j m₀ k ≤ ((M : ℝ≥0) : WithTop ℝ≥0)
  · obtain ⟨m₀, hb₀⟩ := hex
    obtain ⟨K, hK⟩ := eventually_atTop.1 (eventually_le_hitL h (m := m₀) (hitL_lt_of_bdd hb₀).1 ht)
    refine eventually_atTop.2 ⟨K, fun K' hK' m hb k hk => ?_⟩
    rw [hitL_eq_of_bdd h hb k, ← hitL_eq_of_bdd h hb₀ k]
    exact hK k (hK'.trans hk)
  · refine Eventually.of_forall fun K m hb => absurd ⟨m, hb⟩ hex

/-- **Uniformity over the bounded candidates**: one index `K` after which every bounded candidate passes a given
time `t < ζ`. -/
theorem exists_eventually_le_candTime (h : IsForcePath xL xR ρL ρR w vL vR ζ) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < ζ) :
    ∃ K : ℕ, ∀ p, (∃ M : ℕ, ∀ k, candTime ρL ρR w vL vR ζ p k ≤ ((M : ℝ≥0) : WithTop ℝ≥0)) →
      ∀ k, K ≤ k → (t : WithTop ℝ≥0) ≤ candTime ρL ρR w vL vR ζ p k := by
  have hL := eventually_all.2 fun j => eventually_le_hitL_of_bdd h j ht
  have hR := eventually_all.2 fun j => eventually_le_hitL_of_bdd h.reflect j ht
  obtain ⟨K, hKL, hKR⟩ := (hL.and hR).exists
  refine ⟨K, fun p hp k hk => ?_⟩
  by_cases hc : (Nat.unpair p).1 < nL
  · simp only [candTime, hc, ↓reduceDIte] at hp ⊢
    exact hKL _ _ hp k hk
  by_cases hc' : (Nat.unpair p).1 - nL < nR
  · simp only [candTime, hc, hc', ↓reduceDIte] at hp ⊢
    exact hKR _ _ hp k hk
  · simp only [candTime, hc, hc', ↓reduceDIte]
    exact le_top

/-- **At a finite lifetime some candidate is bounded** (Aux. lemma 3's terminal state satisfies the threshold
condition on one side). -/
theorem exists_bdd_candTime (h : IsForcePath xL xR ρL ρR w vL vR ζ) {T : ℝ≥0} (hT : 0 < T)
    (hTζ : (T : ℝ≥0∞) = ζ) {w₀ : ℝ} {vL₀ : Fin nL → ℝ} {vR₀ : Fin nR → ℝ}
    (hlim : Tendsto (fun s => (w s, fun i => vL i s, fun i => vR i s)) (𝓝[<] T) (𝓝 (w₀, vL₀, vR₀)))
    (hth : ForceWord.ThresholdCondition ρL ρR w₀ vL₀ vR₀) :
    ∃ p, ∃ M : ℕ, ∀ k, candTime ρL ρR w vL vR ζ p k ≤ ((M : ℝ≥0) : WithTop ℝ≥0) := by
  have hTM : (T : WithTop ℝ≥0) ≤ ((⌈T⌉₊ : ℕ) : ℝ≥0) := WithTop.coe_le_coe.2 (Nat.le_ceil T)
  rcases hth with hl | hr
  · have hlim' : Tendsto (fun s => (w s, fun i => vL i s)) (𝓝[<] T) (𝓝 (w₀, vL₀)) :=
      ((continuous_fst.prodMk (continuous_fst.comp continuous_snd)).tendsto _).comp hlim
    obtain ⟨j, m, hjm⟩ := exists_bdd_hitL h hT hTζ hlim' hl
    refine ⟨Nat.pair j.1 m, ⌈T⌉₊, fun k => ?_⟩
    have hc : (Nat.unpair (Nat.pair j.1 m)).1 < nL := by rw [Nat.unpair_pair]; exact j.2
    have e : candTime ρL ρR w vL vR ζ (Nat.pair j.1 m) k = hitL ρL w vL ζ j m k := by
      simp only [candTime, hc, ↓reduceDIte]
      congr 1
      · exact Fin.ext (by simp only [Nat.unpair_pair])
      · simp only [Nat.unpair_pair]
    rw [e]
    exact (hjm k).trans hTM
  · have hlim' : Tendsto (fun s => ((-w) s, fun i => (fun i => -vR i) i s)) (𝓝[<] T)
        (𝓝 (-w₀, fun i => -vR₀ i)) :=
      ((continuous_fst.neg.prodMk (continuous_snd.comp continuous_snd).neg).tendsto _).comp hlim
    have hr' : (∑ i ∈ Finset.univ.filter (fun i => (fun i => -vR₀ i) i = -w₀), ρR i) ≤ -2 := by
      simpa only [neg_inj] using hr
    obtain ⟨j, m, hjm⟩ := exists_bdd_hitL h.reflect hT hTζ hlim' hr'
    refine ⟨Nat.pair (nL + j.1) m, ⌈T⌉₊, fun k => ?_⟩
    have hc : ¬ (Nat.unpair (Nat.pair (nL + j.1) m)).1 < nL := by
      rw [Nat.unpair_pair]; omega
    have hc' : (Nat.unpair (Nat.pair (nL + j.1) m)).1 - nL < nR := by
      rw [Nat.unpair_pair]; omega
    have e : candTime ρL ρR w vL vR ζ (Nat.pair (nL + j.1) m) k =
        hitL ρR (-w) (fun i => -vR i) ζ j m k := by
      simp only [candTime, hc, hc', ↓reduceDIte]
      congr 1
      · exact Fin.ext (by simp only [Nat.unpair_pair]; omega)
      · simp only [Nat.unpair_pair]
    rw [e]
    exact (hjm k).trans hTM

end Candidates

/-! ### The announcing sequence -/

section Main

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

open scoped Classical in
/-- **The lifetime has an announcing sequence** (Astra §1 (1.2); obligation 1 of PROVE-T11-L312 §4; the
predictability of the lifetime in Aux. lemma 3, Specification p. 24): for an integrated `SLE_κ(ρ)` evolution with an
admissible seed, there are stopping times `T_n` of the usual augmentation of the evolution's filtration, nondecreasing
in `n`, with `T_n < ζ` almost surely and, almost surely, every `t < ζ` below some `T_n`; moreover `T_n ≤ n`. -/
theorem exists_isAnnouncingSeq_le [IsProbabilityMeasure P]
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hκ : 0 < κ)
    (hseed : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR) :
    ∃ T : ℕ → Ω → ℝ≥0, IsAnnouncingSeq (usualAugmentation 𝓕 P) P ζ T ∧ ∀ n ω, T n ω ≤ n := by
  obtain ⟨-, hWa, hVLa, hVRa, -⟩ := Ito.isIntegratedSLEEvolution_usualAugmentation hE
  set 𝓖 := usualAugmentation 𝓕 P with h𝓖
  -- the good event: the pathwise conditions and Aux. lemma 3's terminal state
  set good : Ω → Prop := fun ω =>
    IsIntegratedSLEPath κ xL xR ρL ρR (fun t => W t ω) (fun i t => VL i t ω) (fun i t => VR i t ω)
      (fun t => B t ω) (ζ ω) ∧
    ∀ T : ℝ≥0, 0 < T → (T : ℝ≥0∞) = ζ ω →
      ∃ (w₀ : ℝ) (vL₀ : Fin nL → ℝ) (vR₀ : Fin nR → ℝ),
        Tendsto (fun t => (W t ω, fun i => VL i t ω, fun i => VR i t ω)) (𝓝[<] T)
          (𝓝 (w₀, vL₀, vR₀)) ∧
        ForceWord.ThresholdCondition ρL ρR w₀ vL₀ vR₀ with hgood
  have hae : ∀ᵐ ω ∂P, good ω := by
    filter_upwards [hE.2.2.2.2, hE.ae_tendsto_threshold hκ] with ω h1 h2 using ⟨h1, h2⟩
  obtain ⟨G, hGm, hGc, hGgood⟩ : ∃ G : Set Ω, MeasurableSet G ∧ P Gᶜ = 0 ∧ ∀ ω ∈ G, good ω := by
    refine ⟨(toMeasurable P {ω | ¬ good ω})ᶜ, (measurableSet_toMeasurable _ _).compl, ?_,
      fun ω hω => ?_⟩
    · rw [compl_compl, measure_toMeasurable]; exact ae_iff.1 hae
    · by_contra h; exact hω (subset_toMeasurable _ _ h)
  have hG0 : MeasurableSet[𝓖 0] G := by
    have := (Ito.measurableSet_usualAugmentation_of_null (𝓕 := 𝓕) hGm.compl hGc 0).compl
    rwa [compl_compl] at this
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := by rw [ae_iff]; exact hGc
  have hF : ∀ ω ∈ G, Sec2.IsForcePath xL xR ρL ρR (fun t => W t ω) (fun i t => VL i t ω)
      (fun i t => VR i t ω) (ζ ω) := fun ω hω => (hGgood ω hω).1.isForcePath
  have hcont : ∀ ω ∈ G, ContinuousOn (fun s => stateAt W VL VR s ω) {s : ℝ≥0 | (s : ℝ≥0∞) < ζ ω} :=
    fun ω hω => (hF ω hω).continuousOn_w.prodMk ((continuousOn_pi.2 (hF ω hω).continuousOn_vL).prodMk
      (continuousOn_pi.2 (hF ω hω).continuousOn_vR))
  -- the random candidates
  set a : ℕ → ℕ → Ω → WithTop ℝ≥0 := fun p k ω => if ω ∈ G then
    candTime ρL ρR (fun t => W t ω) (fun i t => VL i t ω) (fun i t => VR i t ω) (ζ ω) p k else ⊤
    with ha_def
  have hatop : ∀ p k, (∀ ω ∈ G, candTime ρL ρR (fun t => W t ω) (fun i t => VL i t ω)
      (fun i t => VR i t ω) (ζ ω) p k = ⊤) → IsStoppingTime 𝓖 (a p k) := by
    intro p k htop
    have : a p k = fun _ => ⊤ := by
      funext ω
      by_cases hω : ω ∈ G
      · simp only [ha_def, hω, ite_true]; exact htop ω hω
      · simp only [ha_def, hω, ite_false]
    rw [this]
    exact isStoppingTime_top'
  have ha : ∀ p k, IsStoppingTime 𝓖 (a p k) := by
    intro p k
    by_cases hc : (Nat.unpair p).1 < nL
    · set j : Fin nL := ⟨(Nat.unpair p).1, hc⟩ with hj
      set m := (Nat.unpair p).2 with hm
      by_cases hs : (∑ i ∈ Finset.Iic j, ρL i) ≤ -2
      · have e : a p k = fun ω => if ω ∈ G then hitBelow (fun s =>
            (fun x : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) => sideVal m j x.1 x.2.1) (stateAt W VL VR s ω))
            (ζ ω) (1 / ((k : ℝ) + 1)) else ⊤ := by
          funext ω
          simp only [ha_def, candTime, hc, ↓reduceDIte, hitL, ← hj, ← hm, hs, ↓reduceIte, stateAt]
        rw [e]
        exact isStoppingTime_hitBelow_state hWa hVLa hVRa hG0 hcont
          ((continuous_sideVal m j).comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))) _
      · exact hatop p k fun ω _ => by
          simp only [candTime, hc, ↓reduceDIte, hitL, ← hj, hs, ↓reduceIte]
    by_cases hc' : (Nat.unpair p).1 - nL < nR
    · set j : Fin nR := ⟨(Nat.unpair p).1 - nL, hc'⟩ with hj
      set m := (Nat.unpair p).2 with hm
      by_cases hs : (∑ i ∈ Finset.Iic j, ρR i) ≤ -2
      · have e : a p k = fun ω => if ω ∈ G then hitBelow (fun s =>
            (fun x : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) => sideVal m j (-x.1) (-x.2.2))
              (stateAt W VL VR s ω)) (ζ ω) (1 / ((k : ℝ) + 1)) else ⊤ := by
          funext ω
          simp only [ha_def, candTime, hc, hc', ↓reduceDIte, hitL, ← hj, ← hm, hs, ↓reduceIte, stateAt]
          rfl
        rw [e]
        exact isStoppingTime_hitBelow_state hWa hVLa hVRa hG0 hcont
          ((continuous_sideVal m j).comp
            (continuous_fst.neg.prodMk (continuous_snd.comp continuous_snd).neg)) _
      · exact hatop p k fun ω _ => by
          simp only [candTime, hc, hc', ↓reduceDIte, hitL, ← hj, hs, ↓reduceIte]
    · exact hatop p k fun ω _ => by simp only [candTime, hc, hc', ↓reduceDIte]
  have hmono : ∀ p ω, Monotone fun k => a p k ω := by
    intro p ω
    by_cases hω : ω ∈ G
    · simp only [ha_def, hω, ite_true]
      exact candTime_mono p
    · simp only [ha_def, hω, ite_false]
      exact monotone_const
  have hbdd : ∀ ω ∈ G, ∀ p, BddSeq (a p) ω ↔ ∃ M : ℕ, ∀ k, candTime ρL ρR (fun t => W t ω)
      (fun i t => VL i t ω) (fun i t => VR i t ω) (ζ ω) p k ≤ ((M : ℝ≥0) : WithTop ℝ≥0) := by
    intro ω hω p
    simp only [BddSeq, ha_def, hω, ite_true]
  refine exists_isAnnouncingSeq_le_of_candidates ha hmono ?_ ?_ ?_
  · -- bounded candidates stay below the lifetime
    filter_upwards [hGae] with ω hω p hp k
    have := candTime_lt_of_bdd ((hbdd ω hω p).1 hp) k
    simpa only [ha_def, hω, ite_true] using this
  · -- uniformity over the bounded candidates
    filter_upwards [hGae] with ω hω t ht
    obtain ⟨K, hK⟩ := exists_eventually_le_candTime (hF ω hω) ht
    refine ⟨K, fun p hp k hk => ?_⟩
    have := hK p ((hbdd ω hω p).1 hp) k hk
    simpa only [ha_def, hω, ite_true] using this
  · -- some candidate is bounded at a finite lifetime
    filter_upwards [hGae] with ω hω hζ
    have hTζ : (((ζ ω).toNNReal : ℝ≥0) : ℝ≥0∞) = ζ ω := ENNReal.coe_toNNReal hζ
    have hT : 0 < (ζ ω).toNNReal := by
      refine pos_iff_ne_zero.2 fun h0 => hseed ((hF ω hω).threshold_of_eq_zero ?_)
      rw [← hTζ, h0, ENNReal.coe_zero]
    obtain ⟨w₀, vL₀, vR₀, hlim, hth⟩ := (hGgood ω hω).2 _ hT hTζ
    obtain ⟨p, hp⟩ := exists_bdd_candTime (hF ω hω) hT hTζ hlim hth
    exact ⟨p, (hbdd ω hω p).2 hp⟩

/-- **The lifetime has an announcing sequence** (Astra §1 (1.2); obligation 1 of PROVE-T11-L312 §4, in the form
consumed by PROVE-T11-KER and PROVE-T11-ASM): for an integrated `SLE_κ(ρ)` evolution with `κ > 0` and an admissible
seed, `∃ T, IsAnnouncingSeq (usualAugmentation 𝓕 P) P ζ T`. -/
theorem exists_isAnnouncingSeq [IsProbabilityMeasure P]
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hκ : 0 < κ)
    (hseed : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR) :
    ∃ T : ℕ → Ω → ℝ≥0, IsAnnouncingSeq (usualAugmentation 𝓕 P) P ζ T :=
  let ⟨T, hT, _⟩ := exists_isAnnouncingSeq_le hE hκ hseed
  ⟨T, hT⟩

end Main

end Coupling

end InteractingSLE
