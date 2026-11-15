/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.WFSBridge

/-!
# Stopped sigma algebras before the cutoff

Restriction to the alive event passes from the full driving filtration to the cutoff
filtration. Consequently the same inclusion holds at any full driving stop before the cutoff.
-/

set_option autoImplicit false

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.WFS

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {nL nR : ℕ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ V : Ω → ℝ≥0∞} {P : Measure Ω}

/-- An event in the full augmented filtration, restricted to survival of the cutoff,
is measurable in the cutoff augmented filtration. -/
theorem measurableSet_drivingFiltration_inter_lt
    (hXζ : IsMeasurableKilledDriving W VL VR ζ) (hXV : IsMeasurableKilledDriving W VL VR V)
    (hVζ : ∀ ω, V ω ≤ ζ ω) {t : ℝ≥0} {A : Set Ω}
    (hA : MeasurableSet[drivingFiltration P hXζ t] A) :
    MeasurableSet[drivingFiltration P hXV t] (A ∩ {ω | (t : ℝ≥0∞) < V ω}) := by
  have hAm : MeasurableSet A := (drivingFiltration P hXζ).le t _ hA
  have hVm := measurable_of_isMeasurableKilledDriving hXV
  change MeasurableSet[usualAugmentation (killedDrivingFiltration hXV) P t] _
  rw [Ito.usualAugmentation_apply]
  simp only [MeasurableSpace.measurableSet_iInf]
  intro s hts
  obtain ⟨q, -, hq, hlim⟩ := exists_seq_strictAnti_tendsto' hts
  have hBex : ∀ n, ∃ B : Set Ω,
      MeasurableSet[killedDrivingSigma W VL VR ζ (q n)] B ∧ A =ᵐ[P] B :=
    fun n => Ito.exists_ae_eq_of_measurableSet_usualAugmentation (hq n).1 hA
  choose B hB hAB using hBex
  have hBm : MeasurableSet[killedDrivingSigma W VL VR V s]
      (⋃ n, B n ∩ {ω | (q n : ℝ≥0∞) < V ω}) := by
    refine MeasurableSet.iUnion fun n => ?_
    exact (killedDrivingFiltration hXV).mono (hq n).2.le _
      (measurableSet_killedDrivingSigma_inter_lt hVζ (hB n))
  have heq : (A ∩ {ω | (t : ℝ≥0∞) < V ω}) =ᵐ[P]
      ⋃ n, B n ∩ {ω | (q n : ℝ≥0∞) < V ω} := by
    filter_upwards [ae_all_iff.2 hAB] with ω hω
    apply propext
    simp only [mem_inter_iff, mem_ofPred_eq, mem_iUnion]
    constructor
    · rintro ⟨hωA, htV⟩
      cases hVω : V ω with
      | top => exact ⟨0, (Iff.of_eq (hω 0)).mp hωA, by simp⟩
      | coe v =>
        have htv : t < v := by exact_mod_cast (hVω ▸ htV)
        obtain ⟨n, hn⟩ := (hlim.eventually (Iio_mem_nhds htv)).exists
        exact ⟨n, (Iff.of_eq (hω n)).mp hωA, by exact_mod_cast hn⟩
    · rintro ⟨n, hnA, hnV⟩
      exact ⟨(Iff.of_eq (hω n)).mpr hnA,
        lt_of_le_of_lt (by exact_mod_cast (hq n).1.le) hnV⟩
  exact Coupling.measurableSet_nullAugmented_of_ae_eq
    (hAm.inter (measurableSet_lt measurable_const hVm)) hBm heq

/-- The full stopped sigma algebra embeds in the cutoff stopped sigma algebra at a
full driving stop strictly before the cutoff. No stopping-time assumption on `V` is used. -/
theorem measurableSpace_drivingFiltration_le_of_lt
    (hXζ : IsMeasurableKilledDriving W VL VR ζ) (hXV : IsMeasurableKilledDriving W VL VR V)
    (hVζ : ∀ ω, V ω ≤ ζ ω) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime (drivingFiltration P hXζ) τ)
    (hτV : ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < V ω)
    (hτ' : IsStoppingTime (drivingFiltration P hXV) τ) :
    hτ.measurableSpace ≤ hτ'.measurableSpace := by
  intro A hA
  have hAm : MeasurableSet A := hτ.measurableSpace_le _ hA
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense ℝ≥0
  have hrestrict : ∀ q : ℝ≥0,
      MeasurableSet[drivingFiltration P hXV q]
        ((A ∩ {ω | τ ω ≤ (q : WithTop ℝ≥0)}) ∩ {ω | (q : ℝ≥0∞) < V ω}) :=
    fun q => measurableSet_drivingFiltration_inter_lt hXζ hXV hVζ (hA.2 q)
  have hint : ∀ t : ℝ≥0,
      MeasurableSet[drivingFiltration P hXV t] (A ∩ {ω | τ ω ≤ (t : WithTop ℝ≥0)}) := by
    intro t
    have : (drivingFiltration P hXV).IsRightContinuous := Ito.isRightContinuous_usualAugmentation _ _
    apply Filtration.IsRightContinuous.measurableSet
    rw [Filtration.rightCont_eq]
    simp only [MeasurableSpace.measurableSet_iInf]
    intro s hts
    let E : Set Ω := {ω | τ ω ≤ (t : WithTop ℝ≥0)} ∩
      ⋃ q ∈ D ∩ Iio s, (A ∩ {ω | τ ω ≤ (q : WithTop ℝ≥0)}) ∩
        {ω | (q : ℝ≥0∞) < V ω}
    have hEm : MeasurableSet[drivingFiltration P hXV s] E :=
      ((drivingFiltration P hXV).mono hts.le _ (hτ' t)).inter
        (MeasurableSet.biUnion (hDc.mono inter_subset_left) fun q hq =>
          (drivingFiltration P hXV).mono hq.2.le _ (hrestrict q))
    have heq : (A ∩ {ω | τ ω ≤ (t : WithTop ℝ≥0)}) =ᵐ[P] E := by
      filter_upwards [hτV] with ω hω
      apply propext
      simp only [E, mem_inter_iff, mem_ofPred_eq, mem_iUnion, mem_Iio, exists_prop]
      constructor
      · rintro ⟨hωA, hτt⟩
        have hτtop : τ ω ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top hτt
        let r := (τ ω).untopD 0
        have hτr : τ ω = (r : WithTop ℝ≥0) := (Coupling.coe_untopD_of_ne_top hτtop).symm
        have hrs : r < s := (WithTop.coe_le_coe.1 (hτr ▸ hτt)).trans_lt hts
        have hrV : (r : ℝ≥0∞) < V ω := by
          change (τ ω : ℝ≥0∞) < V ω at hω
          rw [hτr] at hω
          exact hω
        obtain ⟨v, hrv, hvV⟩ : ∃ v : ℝ≥0, r < v ∧ (v : ℝ≥0∞) < V ω := by
          cases hVω : V ω with
          | top => exact ⟨r + 1, lt_add_one r, by simp⟩
          | coe v =>
            have hrv : r < v := by exact_mod_cast (hVω ▸ hrV)
            obtain ⟨v', hrv', hv'v⟩ := exists_between hrv
            exact ⟨v', hrv', by exact_mod_cast hv'v⟩
        obtain ⟨q, hqD, hrq, hqvs⟩ := hDd.exists_between (lt_min hrv hrs)
        exact ⟨hτt, q, ⟨hqD, hqvs.trans_le (min_le_right _ _)⟩,
          ⟨hωA, by rw [hτr]; exact WithTop.coe_le_coe.2 hrq.le⟩,
          lt_of_lt_of_le (by exact_mod_cast (hqvs.trans_le (min_le_left _ _))) hvV.le⟩
      · rintro ⟨hτt, q, _, ⟨hωA, _⟩, _⟩
        exact ⟨hωA, hτt⟩
    exact WholeField.measurableSet_of_ae_eq ((drivingFiltration P hXV).le s)
      (fun N hN h0 => Ito.measurableSet_usualAugmentation_of_null hN h0 s)
      (hAm.inter ((drivingFiltration P hXV).le t _ (hτ' t))) hEm heq
  refine ⟨?_, hint⟩
  have heq : A =ᵐ[P] ⋃ n : ℕ, A ∩ {ω | τ ω ≤ (n : ℝ≥0)} := by
    filter_upwards [hτV] with ω hω
    apply propext
    simp only [mem_iUnion, mem_inter_iff, mem_ofPred_eq]
    constructor
    · intro hωA
      have hτtop : τ ω ≠ ⊤ := ne_top_of_lt hω
      obtain ⟨n, hn⟩ := exists_nat_ge ((τ ω).untopD 0)
      exact ⟨n, hωA, by rw [← Coupling.coe_untopD_of_ne_top hτtop]; exact_mod_cast hn⟩
    · rintro ⟨n, hωA, _⟩
      exact hωA
  exact WholeField.measurableSet_of_ae_eq (iSup_le (drivingFiltration P hXV).le)
    (fun N hN h0 => le_iSup (drivingFiltration P hXV) 0 _
      (Ito.measurableSet_usualAugmentation_of_null hN h0 0)) hAm
    (MeasurableSet.iUnion fun n : ℕ => le_iSup (drivingFiltration P hXV) (n : ℝ≥0) _ (hint n)) heq

omit mΩ in
/-- Every cutoff-history event has a full-history representative on the event that
the cutoff is still alive. This assertion concerns pointwise agreement on that event. -/
theorem exists_measurableSet_killedDrivingSigma_eqOn
    (hVζ : ∀ ω, V ω ≤ ζ ω) {q : ℝ≥0} {A : Set Ω}
    (hA : MeasurableSet[killedDrivingSigma W VL VR V q] A) :
    ∃ C : Set Ω, MeasurableSet[killedDrivingSigma W VL VR ζ q] C ∧
      ∀ ω, (q : ℝ≥0∞) < V ω → (ω ∈ A ↔ ω ∈ C) := by
  let S : Set (Set Ω) := {E | ∃ r ≤ q,
    ∃ U : Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)), MeasurableSet U ∧
      E = {ω | (r : ℝ≥0∞) < V ω ∧ (W r ω, fun i => VL i r ω, fun i => VR i r ω) ∈ U}}
  change MeasurableSet[MeasurableSpace.generateFrom S] A at hA
  refine MeasurableSpace.generateFrom_induction S
    (fun E _ => ∃ C : Set Ω, MeasurableSet[killedDrivingSigma W VL VR ζ q] C ∧
      ∀ ω, (q : ℝ≥0∞) < V ω → (ω ∈ E ↔ ω ∈ C)) ?_ ?_ ?_ ?_ A hA
  · rintro E ⟨r, hr, U, hU, rfl⟩ _
    refine ⟨{ω | (r : ℝ≥0∞) < ζ ω ∧
      (W r ω, fun i => VL i r ω, fun i => VR i r ω) ∈ U},
      MeasurableSpace.measurableSet_generateFrom ⟨r, hr, U, hU, rfl⟩, ?_⟩
    intro ω hq
    have hrV : (r : ℝ≥0∞) < V ω := lt_of_le_of_lt (by exact_mod_cast hr) hq
    simp only [mem_ofPred_eq, hrV, hrV.trans_le (hVζ ω), true_and]
  · exact ⟨∅, @MeasurableSet.empty Ω (killedDrivingSigma W VL VR ζ q), fun _ _ => Iff.rfl⟩
  · rintro E _ ⟨C, hC, heq⟩
    exact ⟨Cᶜ, hC.compl, fun ω hq => not_congr (heq ω hq)⟩
  · intro E _ hE
    choose C hC heq using hE
    refine ⟨⋃ n, C n, MeasurableSet.iUnion hC, ?_⟩
    intro ω hq
    simp only [mem_iUnion]
    exact exists_congr fun n => heq n ω hq

/-- A cutoff-filtration stop strictly before the cutoff is a full driving stop.
The proof reconstructs its strict sublevel events from countably many raw-history
representatives. On a dead event at the representing time, the stop has already occurred. -/
theorem isStoppingTime_full_drivingFiltration_of_lt
    (hXζ : IsMeasurableKilledDriving W VL VR ζ) (hXV : IsMeasurableKilledDriving W VL VR V)
    (hVζ : ∀ ω, V ω ≤ ζ ω) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime (drivingFiltration P hXV) τ)
    (hτV : ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < V ω) :
    IsStoppingTime (drivingFiltration P hXζ) τ := by
  have : (drivingFiltration P hXζ).IsRightContinuous := Ito.isRightContinuous_usualAugmentation _ _
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense ℝ≥0
  have : Countable D := hDc.to_subtype
  have hex : ∀ i j : D, ∃ C : Set Ω,
      MeasurableSet[killedDrivingSigma W VL VR ζ j] C ∧
      ∀ᵐ ω ∂P, (i : ℝ≥0) < j → (j : ℝ≥0∞) < V ω → (τ ω ≤ (i : ℝ≥0) ↔ ω ∈ C) := by
    intro i j
    by_cases hij : (i : ℝ≥0) < j
    · obtain ⟨A, hA, heq⟩ := Ito.exists_ae_eq_of_measurableSet_usualAugmentation hij (hτ i)
      obtain ⟨C, hC, hAC⟩ := exists_measurableSet_killedDrivingSigma_eqOn hVζ hA
      refine ⟨C, hC, heq.mono fun ω hω _ hjV => ?_⟩
      exact (Iff.of_eq hω).trans (hAC ω hjV)
    · exact ⟨∅, @MeasurableSet.empty Ω (killedDrivingSigma W VL VR ζ j),
        Eventually.of_forall fun _ h => (hij h).elim⟩
  choose C hC heq using hex
  have hae : ∀ᵐ ω ∂P, ∀ i j : D, (i : ℝ≥0) < j → (j : ℝ≥0∞) < V ω →
      (τ ω ≤ (i : ℝ≥0) ↔ ω ∈ C i j) :=
    ae_all_iff.2 fun i => ae_all_iff.2 (heq i)
  apply isStoppingTime_of_measurableSet_lt_of_isRightContinuous
  intro t
  let E : Set Ω := ⋃ i : D, ⋃ j : D, ⋃ (_ : (i : ℝ≥0) < j), ⋃ (_ : (j : ℝ≥0) < t), C i j
  have hEm : MeasurableSet[drivingFiltration P hXζ t] E := by
    refine MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun j =>
      MeasurableSet.iUnion fun _ => MeasurableSet.iUnion fun hj => ?_
    exact Ito.le_usualAugmentation _ _ t _
      ((killedDrivingFiltration hXζ).mono hj.le _ (hC i j))
  have hEq : {ω | τ ω < (t : WithTop ℝ≥0)} =ᵐ[P] E := by
    filter_upwards [hτV, hae] with ω hω hrep
    apply propext
    simp only [E, mem_iUnion, exists_prop]
    constructor
    · intro hτt
      have hτtop : τ ω ≠ ⊤ := ne_top_of_lt hτt
      let r := (τ ω).untopD 0
      have hτr : τ ω = (r : WithTop ℝ≥0) := (Coupling.coe_untopD_of_ne_top hτtop).symm
      have hrt : r < t := WithTop.coe_lt_coe.1 (hτr ▸ hτt)
      have hrV : (r : ℝ≥0∞) < V ω := by
        change (τ ω : ℝ≥0∞) < V ω at hω
        rw [hτr] at hω
        exact hω
      obtain ⟨v, hrv, hvV⟩ : ∃ v : ℝ≥0, r < v ∧ (v : ℝ≥0∞) < V ω := by
        cases hVω : V ω with
        | top => exact ⟨r + 1, lt_add_one r, by simp⟩
        | coe v =>
          have hrv : r < v := by exact_mod_cast (hVω ▸ hrV)
          obtain ⟨v', hrv', hv'v⟩ := exists_between hrv
          exact ⟨v', hrv', by exact_mod_cast hv'v⟩
      obtain ⟨j, hjD, hrj, hjvt⟩ := hDd.exists_between (lt_min hrv hrt)
      obtain ⟨i, hiD, hri, hij⟩ := hDd.exists_between hrj
      have hjV : (j : ℝ≥0∞) < V ω :=
        (show (j : ℝ≥0∞) < v by exact_mod_cast (hjvt.trans_le (min_le_left _ _))).trans hvV
      exact ⟨⟨i, hiD⟩, ⟨j, hjD⟩, hij, hjvt.trans_le (min_le_right _ _),
        (hrep ⟨i, hiD⟩ ⟨j, hjD⟩ hij hjV).mp
          (by rw [hτr]; exact WithTop.coe_le_coe.2 hri.le)⟩
    · rintro ⟨i, j, hij, hjt, hCω⟩
      by_cases hjV : (j : ℝ≥0∞) < V ω
      · exact lt_of_le_of_lt ((hrep i j hij hjV).mpr hCω)
          (WithTop.coe_lt_coe.2 (hij.trans hjt))
      · change (τ ω : ℝ≥0∞) < (t : ℝ≥0∞)
        exact hω.trans_le ((le_of_not_gt hjV).trans (ENNReal.coe_le_coe.2 hjt.le))
  exact WholeField.measurableSet_of_ae_eq ((drivingFiltration P hXζ).le t)
    (fun N hN h0 => Ito.measurableSet_usualAugmentation_of_null hN h0 t)
    ((drivingFiltration P hXV).le t _ (hτ.measurableSet_lt t)) hEm hEq

/-- If the cutoff has a cutoff-filtration announcing sequence, its killed driving
filtration is contained in the full driving filtration. -/
theorem drivingFiltration_le_full_of_announce
    (hXζ : IsMeasurableKilledDriving W VL VR ζ) (hXV : IsMeasurableKilledDriving W VL VR V)
    (hVζ : ∀ ω, V ω ≤ ζ ω) {σ : ℕ → Ω → ℝ≥0}
    (hσ : Coupling.IsAnnouncingSeq (drivingFiltration P hXV) P V σ) :
    drivingFiltration P hXV ≤ drivingFiltration P hXζ := by
  have hσF : ∀ n, IsStoppingTime (drivingFiltration P hXζ) fun ω => (σ n ω : WithTop ℝ≥0) :=
    fun n => isStoppingTime_full_drivingFiltration_of_lt hXζ hXV hVζ (hσ.1 n) (hσ.2.2.1 n)
  have hV : ∀ t : ℝ≥0, MeasurableSet[drivingFiltration P hXζ t] {ω | (t : ℝ≥0∞) < V ω} := by
    intro t
    have hEq : {ω | (t : ℝ≥0∞) < V ω} =ᵐ[P] ⋃ n : ℕ, {ω | t < σ n ω} := by
      filter_upwards [hσ.2.2.2, ae_all_iff.2 hσ.2.2.1] with ω hex hlt
      apply propext
      simp only [mem_ofPred_eq, mem_iUnion]
      constructor
      · intro htV
        obtain ⟨v, htv, hvV⟩ : ∃ v : ℝ≥0, t < v ∧ (v : ℝ≥0∞) < V ω := by
          cases hVω : V ω with
          | top => exact ⟨t + 1, lt_add_one t, by simp⟩
          | coe v =>
            have htv : t < v := by exact_mod_cast (hVω ▸ htV)
            obtain ⟨v', htv', hv'v⟩ := exists_between htv
            exact ⟨v', htv', by exact_mod_cast hv'v⟩
        obtain ⟨n, hn⟩ := hex v hvV
        exact ⟨n, htv.trans_le hn⟩
      · rintro ⟨n, hn⟩
        exact (ENNReal.coe_lt_coe.2 hn).trans (hlt n)
    refine WholeField.measurableSet_of_ae_eq ((drivingFiltration P hXζ).le t)
      (fun N hN h0 => Ito.measurableSet_usualAugmentation_of_null hN h0 t)
      (measurableSet_lt measurable_const (measurable_of_isMeasurableKilledDriving hXV))
      (MeasurableSet.iUnion fun n => ?_) hEq
    have hm := (hσF n t).compl
    have heq : {ω | t < σ n ω} = {ω | ¬ (σ n ω : WithTop ℝ≥0) ≤ t} := by
      ext ω
      simp only [mem_ofPred_eq, not_le, WithTop.coe_lt_coe]
    rwa [heq]
  have hraw : killedDrivingFiltration hXV ≤ drivingFiltration P hXζ := by
    intro t
    refine MeasurableSpace.generateFrom_le ?_
    rintro _ ⟨r, hrt, U, hU, rfl⟩
    have hm : MeasurableSet[drivingFiltration P hXζ r]
        {ω | (r : ℝ≥0∞) < ζ ω ∧ (W r ω, fun i => VL i r ω, fun i => VR i r ω) ∈ U} :=
      Ito.le_usualAugmentation _ _ r _
        (MeasurableSpace.measurableSet_generateFrom ⟨r, le_rfl, U, hU, rfl⟩)
    have heq : {ω | (r : ℝ≥0∞) < V ω ∧
        (W r ω, fun i => VL i r ω, fun i => VR i r ω) ∈ U} =
        {ω | (r : ℝ≥0∞) < V ω} ∩ {ω | (r : ℝ≥0∞) < ζ ω ∧
          (W r ω, fun i => VL i r ω, fun i => VR i r ω) ∈ U} := by
      ext ω
      simp only [mem_ofPred_eq, mem_inter_iff]
      exact ⟨fun h => ⟨h.1, h.1.trans_le (hVζ ω), h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩
    rw [heq]
    exact (drivingFiltration P hXζ).mono hrt _ ((hV r).inter hm)
  have hm := Ito.usualAugmentation_mono hraw P
  have hid : usualAugmentation (drivingFiltration P hXζ) P = drivingFiltration P hXζ := by
    change usualAugmentation (usualAugmentation (killedDrivingFiltration hXζ) P) P = _
    rw [Ito.usualAugmentation_eq_rightCont, Ito.nullAugmented_usualAugmentation,
      Filtration.IsRightContinuous.eq]
    rfl
  exact hid ▸ hm

end InteractingSLE.WFS
