/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.Aux54LocPre

/-!
# Aux. lemma 54 for general words, part 8: the σ-algebra of the pre-stop marks

Packet PROVE-AUX54. The pre-stop marks `preMark t Γ = {t < lifetime, history truncated at t ∈ Γ}` form a π-system, and
the σ-algebra they generate contains the normalized history (`historyNormalize`): the lifetime and every sample before
it are read from the marks. So every measurable function of a killed history is a function of the pre-stop marks
(PROVE-LOCEXT-N's `LocalExtNMarks` for general words, with real truncation times).

* `preMarkSets`, `preMarkSigma`, `isPiSystem_preMarkSets`, `preMarkSigma_le`;
* `measurable_fst_preMarkSigma`, **`measurable_historyNormalize_preMarkSigma`**.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Restart

namespace Aux54

open LawUnique

variable {nL nR : ℕ}

/-- The pre-stop mark sets. -/
def preMarkSets : Set (Set (HistorySpace nL nR)) :=
  {M | ∃ (t : ℝ≥0) (Γ : Set (HistorySpace nL nR)), MeasurableSet Γ ∧ M = preMark t Γ}

/-- **The σ-algebra of the pre-stop marks.** -/
@[instance_reducible]
def preMarkSigma : MeasurableSpace (HistorySpace nL nR) := MeasurableSpace.generateFrom preMarkSets

theorem truncK_truncK {t t' : ℝ≥0} (h : t ≤ t') (γ : HistorySpace nL nR) :
    truncK t (truncK t' γ) = truncK t γ := by
  classical
  have h' : (t : ℝ≥0∞) ≤ (t' : ℝ≥0∞) := ENNReal.coe_le_coe.2 h
  have e : min (min γ.1 (t' : ℝ≥0∞)) (t : ℝ≥0∞) = min γ.1 (t : ℝ≥0∞) := by
    rw [min_assoc, min_eq_right h']
  refine Prod.ext ?_ (funext fun p => ?_)
  · simp only [truncK]
    exact e
  · simp only [truncK]
    by_cases h1 : (dyadicTime p : ℝ≥0∞) < min γ.1 (t : ℝ≥0∞)
    · have h2 : (dyadicTime p : ℝ≥0∞) < min γ.1 (t' : ℝ≥0∞) :=
        lt_of_lt_of_le h1 (min_le_min le_rfl h')
      have h3 : (dyadicTime p : ℝ≥0∞) < min (min γ.1 (t' : ℝ≥0∞)) (t : ℝ≥0∞) := by rw [e]; exact h1
      simp only [h1, h2, h3, ↓reduceIte]
    · have h3 : ¬ (dyadicTime p : ℝ≥0∞) < min (min γ.1 (t' : ℝ≥0∞)) (t : ℝ≥0∞) := by rw [e]; exact h1
      simp only [h1, h3, ↓reduceIte]

theorem preMark_inter_of_le {t t' : ℝ≥0} (h : t ≤ t') (Γ Γ' : Set (HistorySpace nL nR)) :
    preMark t Γ ∩ preMark t' Γ' = preMark t' (truncK t ⁻¹' Γ ∩ Γ') := by
  have h' : (t : ℝ≥0∞) ≤ (t' : ℝ≥0∞) := ENNReal.coe_le_coe.2 h
  ext γ
  simp only [preMark, mem_inter_iff, mem_ofPred_eq, mem_preimage, truncK_truncK h]
  constructor
  · rintro ⟨⟨-, h1⟩, h2, h3⟩
    exact ⟨h2, h1, h3⟩
  · rintro ⟨h2, h1, h3⟩
    exact ⟨⟨lt_of_le_of_lt h' h2, h1⟩, h2, h3⟩

theorem isPiSystem_preMarkSets : IsPiSystem (preMarkSets (nL := nL) (nR := nR)) := by
  rintro _ ⟨t, Γ, hΓ, rfl⟩ _ ⟨t', Γ', hΓ', rfl⟩ -
  rcases le_total t t' with h | h
  · exact ⟨t', _, ((measurable_truncK t) hΓ).inter hΓ', preMark_inter_of_le h Γ Γ'⟩
  · rw [inter_comm]
    exact ⟨t, _, ((measurable_truncK t') hΓ').inter hΓ, preMark_inter_of_le h Γ' Γ⟩

theorem measurableSet_preMark_sigma (t : ℝ≥0) {Γ : Set (HistorySpace nL nR)} (hΓ : MeasurableSet Γ) :
    MeasurableSet[preMarkSigma] (preMark t Γ) :=
  MeasurableSpace.measurableSet_generateFrom ⟨t, Γ, hΓ, rfl⟩

theorem preMarkSigma_le : preMarkSigma ≤ (inferInstance : MeasurableSpace (HistorySpace nL nR)) := by
  refine MeasurableSpace.generateFrom_le ?_
  rintro _ ⟨t, Γ, hΓ, rfl⟩
  exact measurableSet_preMark t hΓ

theorem measurableSet_lt_fst_sigma (t : ℝ≥0) :
    MeasurableSet[preMarkSigma] {γ : HistorySpace nL nR | (t : ℝ≥0∞) < γ.1} := by
  have e : {γ : HistorySpace nL nR | (t : ℝ≥0∞) < γ.1} = preMark t univ := by
    ext γ
    simp only [preMark, mem_ofPred_eq, mem_univ, and_true]
  rw [e]
  exact measurableSet_preMark_sigma t MeasurableSet.univ

/-- **The lifetime of a history is a function of the pre-stop marks.** -/
theorem measurable_fst_preMarkSigma :
    Measurable[preMarkSigma] fun γ : HistorySpace nL nR => γ.1 := by
  refine measurable_of_Ioi (mδ := preMarkSigma) fun x => ?_
  cases x with
  | top =>
    have e : (fun γ : HistorySpace nL nR => γ.1) ⁻¹' Ioi (⊤ : ℝ≥0∞) = ∅ := by
      ext γ
      simp only [mem_preimage, mem_Ioi, not_top_lt, mem_empty_iff_false]
    rw [e]
    exact @MeasurableSet.empty _ preMarkSigma
  | coe x₀ => exact measurableSet_lt_fst_sigma x₀

/-- **A sample before the lifetime is a function of the pre-stop marks.** -/
theorem measurableSet_sample_sigma (p : ℕ × ℕ) {B : Set (DrivingValue nL nR)} (hB : MeasurableSet B) :
    MeasurableSet[preMarkSigma] {γ : HistorySpace nL nR | (dyadicTime p : ℝ≥0∞) < γ.1 ∧ γ.2 p ∈ B} := by
  classical
  set d : ℝ≥0 := dyadicTime p with hd
  set Γp : Set (HistorySpace nL nR) := {γ | (d : ℝ≥0∞) < γ.1 ∧ γ.2 p ∈ B} with hΓp
  have hΓpm : MeasurableSet Γp :=
    (measurableSet_lt measurable_const measurable_fst).inter (((measurable_pi_apply p).comp measurable_snd) hB)
  have e : Γp = ⋃ n : ℕ, preMark (d + 1 / ((n : ℝ≥0) + 1)) Γp := by
    ext γ
    simp only [mem_iUnion, preMark, mem_ofPred_eq, hΓp, truncK]
    constructor
    · rintro ⟨hdγ, hγB⟩
      have hex : ∃ n : ℕ, ((d + 1 / ((n : ℝ≥0) + 1) : ℝ≥0) : ℝ≥0∞) < γ.1 := by
        rcases eq_or_ne γ.1 ⊤ with htop | htop
        · exact ⟨0, by rw [htop]; exact ENNReal.coe_lt_top⟩
        · obtain ⟨g, hg⟩ := WithTop.ne_top_iff_exists.1 htop
          have hg' : (g : ℝ≥0∞) = γ.1 := hg
          have hdg : d < g := by rw [← hg'] at hdγ; exact_mod_cast hdγ
          obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show (0 : ℝ) < (g : ℝ) - d by
            have : (d : ℝ) < g := by exact_mod_cast hdg
            linarith)
          refine ⟨n, ?_⟩
          rw [← hg']
          refine ENNReal.coe_lt_coe.2 ?_
          rw [← NNReal.coe_lt_coe]
          push_cast
          linarith
      obtain ⟨n, hn⟩ := hex
      have hdt : (d : ℝ≥0∞) < ((d + 1 / ((n : ℝ≥0) + 1) : ℝ≥0) : ℝ≥0∞) :=
        ENNReal.coe_lt_coe.2 (lt_add_of_pos_right d (by positivity))
      have hmin : min γ.1 (((d + 1 / ((n : ℝ≥0) + 1) : ℝ≥0) : ℝ≥0∞)) =
          ((d + 1 / ((n : ℝ≥0) + 1) : ℝ≥0) : ℝ≥0∞) := min_eq_right hn.le
      refine ⟨n, hn, ?_, ?_⟩
      · rw [hmin]; exact hdt
      · rw [hmin]
        split_ifs with hh
        · exact hγB
        · exact absurd hdt hh
    · rintro ⟨n, -, h1, h2⟩
      have h1' : (d : ℝ≥0∞) < γ.1 := lt_of_lt_of_le h1 (min_le_left _ _)
      refine ⟨h1', ?_⟩
      split_ifs at h2 with hh
      · exact h2
      · exact absurd h1 hh
  rw [e]
  exact MeasurableSet.iUnion fun n => measurableSet_preMark_sigma _ hΓpm

/-- **The normalized history is a function of the pre-stop marks.** -/
theorem measurable_historyNormalize_preMarkSigma :
    Measurable[preMarkSigma] (historyNormalize (nL := nL) (nR := nR)) := by
  classical
  refine Measurable.prodMk (m := preMarkSigma) measurable_fst_preMarkSigma
    ((@measurable_pi_iff (HistorySpace nL nR) (ℕ × ℕ) (fun _ => DrivingValue nL nR) preMarkSigma _).2
      fun p => ?_)
  intro B hB
  have e : (fun γ : HistorySpace nL nR => if (dyadicTime p : ℝ≥0∞) < γ.1 then γ.2 p else 0) ⁻¹' B =
      {γ : HistorySpace nL nR | (dyadicTime p : ℝ≥0∞) < γ.1 ∧ γ.2 p ∈ B} ∪
        ({γ : HistorySpace nL nR | (dyadicTime p : ℝ≥0∞) < γ.1}ᶜ ∩ {_γ | (0 : DrivingValue nL nR) ∈ B}) := by
    ext γ
    by_cases h : (dyadicTime p : ℝ≥0∞) < γ.1 <;> simp [h]
  change MeasurableSet[preMarkSigma]
    ((fun γ : HistorySpace nL nR => if (dyadicTime p : ℝ≥0∞) < γ.1 then γ.2 p else 0) ⁻¹' B)
  rw [e]
  refine (measurableSet_sample_sigma p hB).union ((measurableSet_lt_fst_sigma _).compl.inter ?_)
  by_cases h0 : (0 : DrivingValue nL nR) ∈ B
  · simp only [h0, ofPred_true, MeasurableSet.univ]
  · simp only [h0, ofPred_false, MeasurableSet.empty]

/-- Every measurable set of normalized histories is a set of the pre-stop marks. -/
theorem measurableSet_preimage_historyNormalize {M : Set (HistorySpace nL nR)} (hM : MeasurableSet M) :
    MeasurableSet[preMarkSigma] (historyNormalize ⁻¹' M) :=
  measurable_historyNormalize_preMarkSigma hM

end Aux54

end Restart

end InteractingSLE
