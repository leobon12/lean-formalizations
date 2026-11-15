/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.Aux54Kernel
import InteractingSLE.Spec.Coupling.MartMeans2Announce
import InteractingSLE.Spec.Sec2.CriticalLifetime

/-!
# Aux. lemma 54 for general words, part 3: the reference at its rule stop

Packet PROVE-AUX54. A full optional hull coupling of the word (the reference) is stopped at `V₀ = R(its killed history)
∧ ζ₀` for the Galmarino rule `R` of the stopped coupling.

* `measurableSet_usualAugmentation_of_ae_eq`: the usual augmentation is closed under almost sure equality;
* **`isStoppingTime_ruleStop`** (Galmarino's test for the rule): `V₀` is a stopping time of the driving filtration;
  `{V₀ ≤ t}` is almost surely `{ζ₀ ≤ t} ∪ ({t < ζ₀} ∩ {R(history killed at t ∧ ζ₀) ≤ t})`;
* `measurableSet_killedSample_ruleStop`: the samples of the history killed at `V₀` are adapted;
* `stopVal_killedHistory_of_tendsto`: the state recorded at the lifetime is the left limit of the state;
* **`hasSetKernel_reference`**: the kernel at the stop (`HasSetKernel`) for the history killed at `V₀`, from the frozen
  clause at `V₀ ∧ Tₙ` along an announcing sequence `Tₙ` of `ζ₀`; on histories with a future `V₀ < ζ₀` (at `V₀ = ζ₀` the
  recorded state is the threshold state of Aux. lemma 3).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology QuantumZipper
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Restart

namespace Aux54

open LQGMetric LawUnique Sec4 StoppedExtendWF

variable {nL nR : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **The usual augmentation is closed under almost sure equality.** -/
theorem measurableSet_usualAugmentation_of_ae_eq {𝓕 : Filtration ℝ≥0 mΩ} {P : Measure Ω} {t : ℝ≥0}
    {S S' : Set Ω} (hS : MeasurableSet S) (hS'm : MeasurableSet S')
    (hS' : MeasurableSet[usualAugmentation 𝓕 P t] S') (hae : S =ᵐ[P] S') :
    MeasurableSet[usualAugmentation 𝓕 P t] S := by
  set D : Set Ω := symmDiff S S' with hD
  have hDm : MeasurableSet D := hS.symmDiff hS'm
  have hD0 : P D = 0 := by
    rw [hD, symmDiff_def]
    exact measure_union_null (ae_eq_set.1 hae).1 (ae_eq_set.1 hae).2
  have e : S = (S' \ D) ∪ (S ∩ D) := by
    ext ω
    simp only [mem_union, Set.mem_sdiff, mem_inter_iff, hD, Set.mem_symmDiff]
    by_cases h1 : ω ∈ S <;> by_cases h2 : ω ∈ S' <;> simp [h1, h2]
  rw [e]
  refine (hS'.diff (Ito.measurableSet_usualAugmentation_of_null hDm hD0 t)).union ?_
  exact Ito.measurableSet_usualAugmentation_of_null (hS.inter hDm)
    (measure_mono_null inter_subset_right hD0) t

/-! ### The rule stop is a stopping time (Galmarino's test) -/

section Rule

variable {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **The rule stop** `R(history killed at ζ) ∧ ζ`. -/
def ruleStop (R : HistorySpace nL nR → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
    (VR : Fin nR → ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω) : ℝ≥0∞ :=
  min (R (killedHistory W VL VR ζ ω)) (ζ ω)

theorem ruleStop_le (R : HistorySpace nL nR → ℝ≥0∞) (ω : Ω) : ruleStop R W VL VR ζ ω ≤ ζ ω := min_le_right _ _

/-- The lifetime event `{r < ζ}` belongs to the killed driving filtration at every `t ≥ r`. -/
theorem measurableSet_lt_lifetime_killed (hX : IsMeasurableKilledDriving W VL VR ζ) {r t : ℝ≥0} (hrt : r ≤ t) :
    MeasurableSet[killedDrivingFiltration hX t] {ω | (r : ℝ≥0∞) < ζ ω} := by
  have h : MeasurableSet[killedDrivingFiltration hX t]
      {ω | (r : ℝ≥0∞) < ζ ω ∧ (W r ω, fun i => VL i r ω, fun i => VR i r ω) ∈ (univ : Set (DrivingValue nL nR))} :=
    MeasurableSpace.measurableSet_generateFrom ⟨r, hrt, univ, MeasurableSet.univ, rfl⟩
  simpa only [mem_univ, and_true] using h

/-- **The history killed at `t ∧ ζ` is measurable for the killed driving filtration at `t`.** -/
theorem measurable_killedHistory_min (hX : IsMeasurableKilledDriving W VL VR ζ) (t : ℝ≥0) :
    Measurable[killedDrivingFiltration hX t] (killedHistory W VL VR fun ω => min (t : ℝ≥0∞) (ζ ω)) := by
  classical
  have hlife : Measurable[killedDrivingFiltration hX t] fun ω => min (t : ℝ≥0∞) (ζ ω) := by
    refine measurable_of_Ioi fun a => ?_
    induction a using ENNReal.recTopCoe with
    | top => simp only [Ioi_top, preimage_empty]; exact @MeasurableSet.empty _ (killedDrivingFiltration hX t)
    | coe r =>
      by_cases hrt : r < t
      · have e : (fun ω => min (t : ℝ≥0∞) (ζ ω)) ⁻¹' Ioi (r : ℝ≥0∞) = {ω | (r : ℝ≥0∞) < ζ ω} := by
          ext ω
          simp only [mem_preimage, mem_Ioi, lt_min_iff, mem_ofPred_eq, ENNReal.coe_lt_coe, hrt, true_and]
        rw [e]
        exact measurableSet_lt_lifetime_killed hX hrt.le
      · have e : (fun ω => min (t : ℝ≥0∞) (ζ ω)) ⁻¹' Ioi (r : ℝ≥0∞) = ∅ := by
          ext ω
          simp only [mem_preimage, mem_Ioi, lt_min_iff, ENNReal.coe_lt_coe, hrt, false_and, mem_empty_iff_false]
        rw [e]
        exact @MeasurableSet.empty _ (killedDrivingFiltration hX t)
  have hsm : ∀ p : ℕ × ℕ, Measurable[killedDrivingFiltration hX t]
      fun ω => (killedHistory W VL VR (fun ω => min (t : ℝ≥0∞) (ζ ω)) ω).2 p := by
    intro p
    by_cases hpt : dyadicTime p < t
    · have e : (fun ω => (killedHistory W VL VR (fun ω => min (t : ℝ≥0∞) (ζ ω)) ω).2 p) =
          fun ω => (killedHistory W VL VR ζ ω).2 p := by
        funext ω
        have hiff : (dyadicTime p : ℝ≥0∞) < min (t : ℝ≥0∞) (ζ ω) ↔ (dyadicTime p : ℝ≥0∞) < ζ ω := by
          rw [lt_min_iff]
          exact ⟨fun h => h.2, fun h => ⟨ENNReal.coe_lt_coe.2 hpt, h⟩⟩
        simp only [killedHistory, hiff]
      rw [e]
      exact (measurable_killedSample hX p).mono ((killedDrivingFiltration hX).mono hpt.le) le_rfl
    · have e : (fun ω => (killedHistory W VL VR (fun ω => min (t : ℝ≥0∞) (ζ ω)) ω).2 p) = fun _ => 0 := by
        funext ω
        have : ¬ (dyadicTime p : ℝ≥0∞) < min (t : ℝ≥0∞) (ζ ω) := fun h =>
          hpt (ENNReal.coe_lt_coe.1 (lt_of_lt_of_le h (min_le_left _ _)))
        simp only [killedHistory, this, ↓reduceIte]
      rw [e]
      exact measurable_const
  exact Measurable.prodMk (m := killedDrivingFiltration hX t) hlife
    (@measurable_pi_iff Ω (ℕ × ℕ) _ (killedDrivingFiltration hX t) _ _ |>.2 hsm)

/-- **Galmarino's test for the rule stop**: for a measurable Galmarino rule `R` and a state continuous before `ζ`, the
rule stop `R(history killed at ζ) ∧ ζ` is a stopping time of the driving filtration. -/
theorem isStoppingTime_ruleStop {P : Measure Ω} (hX : IsMeasurableKilledDriving W VL VR ζ)
    {R : HistorySpace nL nR → ℝ≥0∞} (hRm : Measurable R) (hRg : IsHistGalmarino R)
    (hc : ∀ᵐ ω ∂P, ContinuousOn (dState W VL VR ω) {t | (t : ℝ≥0∞) < ζ ω}) :
    IsStoppingTime (drivingFiltration P hX) fun ω => (ruleStop R W VL VR ζ ω : WithTop ℝ≥0) := by
  intro t
  set Yt : Ω → HistorySpace nL nR := killedHistory W VL VR fun ω => min (t : ℝ≥0∞) (ζ ω) with hYt
  set S' : Set Ω := {ω | ¬ ((t : ℝ≥0∞) < ζ ω)} ∪ ({ω | (t : ℝ≥0∞) < ζ ω} ∩ Yt ⁻¹' {γ | R γ ≤ t}) with hS'
  have hS'k : MeasurableSet[killedDrivingFiltration hX t] S' :=
    (measurableSet_lt_lifetime_killed hX le_rfl).compl.union ((measurableSet_lt_lifetime_killed hX le_rfl).inter
      ((measurable_killedHistory_min hX t) (measurableSet_le hRm measurable_const)))
  have hS'm : MeasurableSet S' := (killedDrivingFiltration hX).le t _ hS'k
  have hζm := measurable_lifetime hX
  have hSm : MeasurableSet {ω | (ruleStop R W VL VR ζ ω : WithTop ℝ≥0) ≤ (t : WithTop ℝ≥0)} := by
    have h1 : Measurable (ruleStop R W VL VR ζ) := (hRm.comp (measurable_killedHistory hX)).min hζm
    exact measurableSet_le h1 measurable_const
  refine measurableSet_usualAugmentation_of_ae_eq hSm hS'm
    (Ito.le_usualAugmentation (killedDrivingFiltration hX) P t _ hS'k) ?_
  filter_upwards [hc] with ω hω
  have hY : IsKilledContHist (killedHistory W VL VR ζ ω) := isKilledContHist_killedHistory hω
  have hYt' : IsKilledContHist (Yt ω) :=
    isKilledContHist_killedHistory (hω.mono fun s hs =>
      show (s : ℝ≥0∞) < ζ ω from lt_of_lt_of_le hs (min_le_right _ _))
  change ((ruleStop R W VL VR ζ ω : WithTop ℝ≥0) ≤ (t : WithTop ℝ≥0)) = (ω ∈ S')
  apply propext
  simp only [hS', mem_union, mem_ofPred_eq, mem_inter_iff, mem_preimage]
  change ruleStop R W VL VR ζ ω ≤ (t : ℝ≥0∞) ↔ _
  by_cases htζ : (t : ℝ≥0∞) < ζ ω
  · have hmin : min (t : ℝ≥0∞) (ζ ω) = t := min_eq_left htζ.le
    have hYt1 : (Yt ω).1 = t := by simp only [hYt, killedHistory, hmin]
    have hag : ∀ p : ℕ × ℕ, (dyadicTime p : ℝ≥0∞) < t →
        (killedHistory W VL VR ζ ω).2 p = (Yt ω).2 p := by
      intro p hp
      have hp' : (dyadicTime p : ℝ≥0∞) < ζ ω := hp.trans htζ
      have hp'' : (dyadicTime p : ℝ≥0∞) < min (t : ℝ≥0∞) (ζ ω) := by rw [hmin]; exact hp
      simp only [hYt, killedHistory, hp', hp'', ↓reduceIte]
    simp only [htζ, not_true_eq_false, false_or, true_and, ruleStop]
    constructor
    · intro hle
      have hR : R (killedHistory W VL VR ζ ω) ≤ t := by
        rcases min_le_iff.1 hle with h | h
        · exact h
        · exact absurd h (not_le.2 htζ)
      have e := hRg _ _ hY hYt' (hR.trans htζ.le) (by rw [hYt1]; exact hR)
        (fun p hp => hag p (lt_of_lt_of_le hp hR))
      rw [e]
      exact hR
    · intro hle
      have e := hRg _ _ hYt' hY (by rw [hYt1]; exact hle) (hle.trans htζ.le)
        (fun p hp => (hag p (lt_of_lt_of_le hp hle)).symm)
      exact min_le_of_left_le (e ▸ hle)
  · simp only [htζ, not_false_eq_true, true_or, iff_true]
    exact (ruleStop_le R ω).trans (not_lt.1 htζ)

end Rule

/-! ### The kernel of the reference at its rule stop -/

section Ref

variable {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {e : Ω → ℝ≥0∞}
  {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}

/-- **The state recorded at a positive lifetime is the left limit of the state.** -/
theorem stopVal_killedHistory_of_tendsto {ω : Ω} {T : ℝ≥0} (hT : (T : ℝ≥0∞) = e ω) (hTpos : 0 < T)
    {s : DrivingValue nL nR} (hlim : Tendsto (dState W VL VR ω) (𝓝[<] T) (𝓝 s)) :
    stopVal xL xR (killedHistory W VL VR e ω) = s := by
  classical
  have hne : (killedHistory W VL VR e ω).1 ≠ 0 := by
    simp only [killedHistory, ← hT, ne_eq, ENNReal.coe_eq_zero]
    exact hTpos.ne'
  have hS : (killedHistory W VL VR e ω).1.toNNReal = T := by simp only [killedHistory, ← hT, ENNReal.toNNReal_coe]
  simp only [stopVal, hne, ↓reduceIte, hS]
  refine Tendsto.limUnder_eq ?_
  have hl : Tendsto (fun n => dyadicTime (lowerStrict T n)) atTop (𝓝[<] T) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_dyadicTime_lowerStrict T,
      Eventually.of_forall fun n => dyadicTime_lowerStrict_lt hTpos n⟩
  refine (hlim.comp hl).congr fun n => ?_
  have hlt : (dyadicTime (lowerStrict T n) : ℝ≥0∞) < e ω := by
    rw [← hT]; exact ENNReal.coe_lt_coe.2 (dyadicTime_lowerStrict_lt hTpos n)
  simp only [Function.comp_apply, killedHistory, hlt, ↓reduceIte, dState]

/-- **The kernel when almost every history has no future** (only `φ = 0` avoids the recorded hull). -/
theorem hasSetKernel_of_ae_mask (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) {P : Measure Ω}
    {h : Ω → DistOn upperHalfPlaneOpens} {X : Ω → HistorySpace nL nR} (hXm : Measurable X)
    (hmask : ∀ᵐ ω ∂P, recMask ρL ρR xL xR (X ω)) :
    HasSetKernel P X (recHull ρL ρR xL xR) h (recK κ ρL ρR xL xR) := by
  classical
  intro φ B hB hBd
  refine setIntegral_congr_ae (hXm hB) ?_
  filter_upwards [hmask] with ω hm hωB
  have hdis := hBd _ hωB
  simp only [recHull, hm, ↓reduceIte] at hdis
  simp only [recK, recG, hm, ↓reduceIte, apply_eq_zero_of_disjoint_univ hdis, Complex.ofReal_zero, mul_zero,
    Complex.exp_zero, norm_one, le_refl]

/-- **The kernel of a full coupling at its rule stop** `V₀ = R(history) ∧ ζ₀` (set-integral form): from the frozen
clause at `V₀ ∧ Tₙ`, `Tₙ` announcing `ζ₀`. At an inadmissible seed every history has no future. -/
theorem hasSetKernel_reference {κ : ℝ} (hκ : 0 < κ) {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    {h : Ω → DistOn upperHalfPlaneOpens} (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    {R : HistorySpace nL nR → ℝ≥0∞} (hRm : Measurable R) (hRg : IsHistGalmarino R) :
    HasSetKernel P (killedHistory W VL VR (ruleStop R W VL VR ζ)) (recHull ρL ρR xL xR) h
      (recK κ ρL ρR xL xR) := by
  classical
  obtain ⟨hE, hh, -, hX, hcl⟩ := hC
  set V₀ : Ω → ℝ≥0∞ := ruleStop R W VL VR ζ with hV₀def
  have hpath := hE.2.2.2.2
  have hc : ∀ᵐ ω ∂P, ContinuousOn (dState W VL VR ω) {t | (t : ℝ≥0∞) < ζ ω} := by
    filter_upwards [hE.isSLEEvolutionUpTo.ae_path] with ω hp
    exact continuousOn_state_of_isSLEPathUpTo hp
  have hV₀ := isStoppingTime_ruleStop (P := P) hX hRm hRg hc
  have hV₀ζ : ∀ ω, V₀ ω ≤ ζ ω := ruleStop_le R
  have hs : ∀ (p : ℕ × ℕ) (S : Set (DrivingValue nL nR)), MeasurableSet S →
      MeasurableSet[drivingFiltration P hX (dyadicTime p)]
        ((fun ω => (killedHistory W VL VR V₀ ω).2 p) ⁻¹' S) := by
    intro p S hS
    have e : (fun ω => (killedHistory W VL VR V₀ ω).2 p) ⁻¹' S =
        ({ω | (V₀ ω : WithTop ℝ≥0) ≤ ((dyadicTime p : ℝ≥0) : WithTop ℝ≥0)}ᶜ ∩
            (fun ω => (killedHistory W VL VR ζ ω).2 p) ⁻¹' S) ∪
          ({ω | (V₀ ω : WithTop ℝ≥0) ≤ ((dyadicTime p : ℝ≥0) : WithTop ℝ≥0)} ∩
            {_ω | (0 : DrivingValue nL nR) ∈ S}) := by
      ext ω
      simp only [mem_preimage, mem_union, mem_inter_iff, mem_compl_iff, mem_ofPred_eq]
      by_cases hd : (V₀ ω : WithTop ℝ≥0) ≤ ((dyadicTime p : ℝ≥0) : WithTop ℝ≥0)
      · have h1 : ¬ ((dyadicTime p : ℝ≥0∞) < V₀ ω) := not_lt.2 hd
        simp only [killedHistory, h1, ↓reduceIte, hd, not_true_eq_false, false_and, true_and, false_or]
      · have h1 : (dyadicTime p : ℝ≥0∞) < V₀ ω := not_le.1 hd
        have h2 : (dyadicTime p : ℝ≥0∞) < ζ ω := lt_of_lt_of_le h1 (hV₀ζ ω)
        simp only [killedHistory, h1, h2, ↓reduceIte, hd, not_false_eq_true, true_and, false_and, or_false]
    rw [e]
    exact ((hV₀ (dyadicTime p)).compl.inter
      (Ito.le_usualAugmentation _ P _ _ (measurable_killedSample hX p hS))).union
      ((hV₀ (dyadicTime p)).inter (MeasurableSet.const _))
  have hXm := measurable_killedHistory_stopped' hV₀ hs
  have hXm' : Measurable (killedHistory W VL VR V₀) := hXm.mono hV₀.measurableSpace_le le_rfl
  by_cases hseed : ForceWord.ThresholdCondition ρL ρR 0 xL xR
  · -- an inadmissible seed: `ζ = 0`, and every history has no future
    refine hasSetKernel_of_ae_mask κ ρL ρR hXm' ?_
    filter_upwards [hpath] with ω hp
    obtain ⟨h0, h1, h2, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h17, -, -⟩ := hp
    have hζ0 : ζ ω = 0 := by
      by_contra hne
      refine h17 0 (pos_iff_ne_zero.2 hne) ?_
      rw [h0, show (fun i => VL i 0 ω) = xL from funext h1, show (fun i => VR i 0 ω) = xR from funext h2]
      exact hseed
    have hV0 : V₀ ω = 0 := le_antisymm (hζ0 ▸ hV₀ζ ω) zero_le
    have hk : (killedHistory W VL VR V₀ ω).1 = 0 := hV0
    refine Or.inr ?_
    simp only [stopVal, hk, ↓reduceIte, initVal]
    exact hseed
  -- an admissible seed: an announcing sequence of `ζ`
  obtain ⟨T, ⟨hTs, hTm, hTζ, hTex⟩, -⟩ := hE.exists_isAnnouncingSeq_drivingFiltration hκ hseed hX
  have hlt : ∀ᵐ ω ∂P, ¬ recMask ρL ρR xL xR (killedHistory W VL VR V₀ ω) → V₀ ω < ζ ω := by
    filter_upwards [hpath, hE.ae_tendsto_threshold hκ] with ω hp hthr hnm
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h18, -⟩ := hp
    refine lt_of_le_of_ne (hV₀ζ ω) fun heq => hnm ?_
    by_cases htop : ζ ω = ⊤
    · exact Or.inl (show V₀ ω = ⊤ by rw [heq, htop])
    obtain ⟨Z, hZ⟩ := WithTop.ne_top_iff_exists.1 htop
    have hZ' : (Z : ℝ≥0∞) = ζ ω := hZ
    by_cases hZ0 : Z = 0
    · exact absurd (h18 (by rw [← hZ', hZ0, ENNReal.coe_zero])) hseed
    obtain ⟨w₀, vL₀, vR₀, hlim, hth⟩ := hthr Z (pos_iff_ne_zero.2 hZ0) hZ'
    refine Or.inr ?_
    rw [stopVal_killedHistory_of_tendsto (e := V₀) (hZ'.trans heq.symm) (pos_iff_ne_zero.2 hZ0) hlim]
    exact hth
  have h0 : ∀ᵐ ω ∂P, dState W VL VR ω 0 = initVal xL xR := by
    filter_upwards [hE.isSLEEvolutionUpTo.ae_path] with ω hp
    simp only [dState, initVal, hp.w_zero, Prod.mk.injEq, true_and]
    exact ⟨funext hp.vL_zero, funext hp.vR_zero⟩
  refine hasSetKernel_of_stops κ ρL ρR xL xR hh hV₀ hXm ?_ h0 ?_ (σ := fun n ω => (T n ω : WithTop ℝ≥0))
    hTs (fun ω n k hnk => WithTop.coe_le_coe.2 (hTm ω hnk)) ?_ fun n => ?_
  · filter_upwards [hlt, hc] with ω hl hcω hnm Tt hTt
    refine hcω.mono fun t ht => ?_
    show (t : ℝ≥0∞) < ζ ω
    exact lt_of_le_of_lt (ENNReal.coe_le_coe.2 ht) (hTt ▸ hl hnm)
  · filter_upwards [hlt, hc] with ω hl hcω hnm Tt hTt
    obtain ⟨T', h1, h2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 (hTt ▸ hl hnm)
    refine ⟨T', ENNReal.coe_lt_coe.1 h1, continuous_fst.comp_continuousOn (hcω.mono fun t ht => ?_)⟩
    show (t : ℝ≥0∞) < ζ ω
    exact lt_of_le_of_lt (ENNReal.coe_le_coe.2 ht) h2
  · filter_upwards [hlt, hTex] with ω hl hex hnm
    have hlt' := hl hnm
    have hVtop : V₀ ω ≠ ⊤ := ne_top_of_lt hlt'
    obtain ⟨v, hv⟩ := WithTop.ne_top_iff_exists.1 hVtop
    obtain ⟨n, hn⟩ := hex v (by rw [show (v : ℝ≥0∞) = V₀ ω from hv]; exact hlt')
    exact ⟨n, by rw [← hv]; exact WithTop.coe_le_coe.2 hn⟩
  · refine (hcl _ (hV₀.min (hTs n)) ?_).2
    filter_upwards [hTζ n] with ω hω
    exact lt_of_le_of_lt (min_le_right _ _) hω

end Ref

end Aux54

end Restart

end InteractingSLE
