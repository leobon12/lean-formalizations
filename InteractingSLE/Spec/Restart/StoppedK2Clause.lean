/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.DomainMarkovAux79Stop
import InteractingSLE.Spec.Coupling.WholeField4Announce

/-!
# The stopped K2, part 1: the stopped σ-algebra of a killed driving process from below

Packet PROVE-STOPPEDK2 (`planning/handoffs/PROVE-DOMAINMARKOV9.md` §4.3). The coupling through a stop `V`
(`StoppedExtend.IsStoppedHullCoupling`) asks for the conditional-law and locality clauses at every stopping time
`τ ≤ V` of the driving filtration of the process **killed at `V`**. The kernel assembly K2 reaches a stopping time from
above by dyadic stops, which at `τ = V` would need times after `V`. Here the clause at `τ` is reached **from below**,
along `τ ∧ σₙ` for stopping times `σₙ < V` announcing `V`:

* `aeTrace`: the sets whose trace on a fixed set agrees almost everywhere with a set of a given σ-algebra;
* **`exists_ae_eq_of_measurableSet_stopped`**: for the killed driving filtration (usual augmentation), a stopping time
  `τ ≤ V` and announcing stopping times `σₙ` (`σₙ < V`, `σₙ → V`), every event of `𝓕_τ` agrees almost surely with an
  event of `⨆ₙ 𝓕_{τ ∧ σₙ}`. Before `V` this is `{τ ≤ σₙ} ∈ 𝓕_{τ ∧ σₙ}`; on `{τ = V}` the killed driving process is
  read through the generators `{r < σₙ, X_r ∈ A} ∩ {σₙ ≤ τ}`;
* **`ae_tendsto_condExp_stopMin`**: Lévy's upward theorem along `τ ∧ σₙ`, with limit `E[Z | 𝓕_τ]`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Restart.StoppedK2

/-! ### The trace σ-algebra -/

section Trace

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The sets `E` such that `E ∩ B` agrees `ν`-almost everywhere with a `G`-measurable set (`B ∈ G`). -/
@[instance_reducible]
def aeTrace (ν : Measure Ω) (G : MeasurableSpace Ω) (B : Set Ω) (hB : MeasurableSet[G] B) : MeasurableSpace Ω where
  MeasurableSet' E := ∃ E', MeasurableSet[G] E' ∧ (E ∩ B : Set Ω) =ᵐ[ν] E'
  measurableSet_empty := ⟨∅, @MeasurableSet.empty _ G, by rw [empty_inter]⟩
  measurableSet_compl E := by
    rintro ⟨E', hE', h⟩
    refine ⟨B \ E', hB.diff hE', ?_⟩
    filter_upwards [h] with ω hω
    have hω' : (ω ∈ E ∩ B) = (ω ∈ E') := hω
    simp only [eq_iff_iff, mem_inter_iff, mem_compl_iff, Set.mem_sdiff] at hω' ⊢
    tauto
  measurableSet_iUnion f hf := by
    choose E' hE' h using hf
    refine ⟨⋃ i, E' i, MeasurableSet.iUnion hE', ?_⟩
    filter_upwards [ae_all_iff.2 h] with ω hω
    have hω' : ∀ i, (ω ∈ f i ∩ B) = (ω ∈ E' i) := hω
    simp only [eq_iff_iff, mem_inter_iff, mem_iUnion] at hω' ⊢
    constructor
    · rintro ⟨⟨i, hi⟩, hB⟩
      exact ⟨i, (hω' i).1 ⟨hi, hB⟩⟩
    · rintro ⟨i, hi⟩
      exact ⟨⟨i, ((hω' i).2 hi).1⟩, ((hω' i).2 hi).2⟩

theorem measurableSet_aeTrace_iff {ν : Measure Ω} {G : MeasurableSpace Ω} {B : Set Ω}
    (hB : MeasurableSet[G] B) {E : Set Ω} :
    MeasurableSet[aeTrace ν G B hB] E ↔ ∃ E', MeasurableSet[G] E' ∧ (E ∩ B : Set Ω) =ᵐ[ν] E' := Iff.rfl

/-- `aeTrace` is closed under almost-everywhere equality. -/
theorem measurableSet_aeTrace_of_ae_eq {ν : Measure Ω} {G : MeasurableSpace Ω} {B : Set Ω}
    (hB : MeasurableSet[G] B) {E E₁ : Set Ω} (h : MeasurableSet[aeTrace ν G B hB] E₁) (hE : E =ᵐ[ν] E₁) :
    MeasurableSet[aeTrace ν G B hB] E := by
  obtain ⟨E', hE', h'⟩ := h
  refine ⟨E', hE', ?_⟩
  filter_upwards [hE, h'] with ω h1 h2
  have h1' : (ω ∈ E) = (ω ∈ E₁) := h1
  have h2' : (ω ∈ E₁ ∩ B) = (ω ∈ E') := h2
  show (ω ∈ E ∩ B) = (ω ∈ E')
  rw [← h2', mem_inter_iff, mem_inter_iff, h1']

end Trace

/-! ### The stopped σ-algebra of the killed driving filtration from below -/

section Struct

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {nL nR : ℕ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞} {ν : Measure Ω}

open Ito in
/-- A generator `{r < V, X_r ∈ A}` of the killed driving filtration, cut at `r < σ`, is an event of `𝓕_σ` for every
stopping time `σ` of the usual augmentation. -/
theorem measurableSet_stopped_gen (hX : IsMeasurableKilledDriving W VL VR V) {σ : Ω → WithTop ℝ≥0}
    (hσ : IsStoppingTime (drivingFiltration ν hX) σ) (r : ℝ≥0) {A : Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ))}
    (hA : MeasurableSet A) :
    MeasurableSet[hσ.measurableSpace] ({ω | (r : WithTop ℝ≥0) < σ ω} ∩
      {ω | (r : ℝ≥0∞) < V ω ∧ (W r ω, fun i => VL i r ω, fun i => VR i r ω) ∈ A}) := by
  set 𝓖 := drivingFiltration ν hX with h𝓖
  have hE : MeasurableSet[𝓖 r] {ω | (r : ℝ≥0∞) < V ω ∧ (W r ω, fun i => VL i r ω, fun i => VR i r ω) ∈ A} :=
    le_usualAugmentation (killedDrivingFiltration hX) ν r _
      (MeasurableSpace.measurableSet_generateFrom ⟨r, le_rfl, A, hA, rfl⟩)
  have hlt : MeasurableSet[𝓖 r] {ω | (r : WithTop ℝ≥0) < σ ω} := by
    have := (hσ r).compl
    convert this using 1
    ext ω
    simp only [mem_ofPred_eq, mem_compl_iff, not_le]
  have hr : MeasurableSet[𝓖 r] ({ω | (r : WithTop ℝ≥0) < σ ω} ∩
      {ω | (r : ℝ≥0∞) < V ω ∧ (W r ω, fun i => VL i r ω, fun i => VR i r ω) ∈ A}) := hlt.inter hE
  refine ⟨(le_iSup (fun t => 𝓖 t) r) _ hr, fun t => ?_⟩
  by_cases hrt : r ≤ t
  · exact (𝓖.mono hrt _ hr).inter (hσ t)
  · have e : ({ω | (r : WithTop ℝ≥0) < σ ω} ∩
        {ω | (r : ℝ≥0∞) < V ω ∧ (W r ω, fun i => VL i r ω, fun i => VR i r ω) ∈ A}) ∩ {ω | σ ω ≤ t} = ∅ := by
      ext ω
      simp only [mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
      intro h1 h3
      exact hrt (WithTop.coe_le_coe.1 (h1.1.le.trans h3))
    rw [e]
    exact @MeasurableSet.empty _ (𝓖 t)

variable (hX : IsMeasurableKilledDriving W VL VR V) {τ : Ω → WithTop ℝ≥0}
  (hτ : IsStoppingTime (drivingFiltration ν hX) τ) {σ : ℕ → Ω → WithTop ℝ≥0}
  (hσ : ∀ n, IsStoppingTime (drivingFiltration ν hX) (σ n))

/-- The σ-algebra `⨆ₙ 𝓕_{τ ∧ σₙ}`. -/
@[instance_reducible]
def stopSup : MeasurableSpace Ω := ⨆ n, (hτ.min (hσ n)).measurableSpace

theorem measurableSet_stopSup_of {n : ℕ} {s : Set Ω} (hs : MeasurableSet[(hτ.min (hσ n)).measurableSpace] s) :
    MeasurableSet[stopSup hX hτ hσ] s :=
  (le_iSup (fun n => (hτ.min (hσ n)).measurableSpace) n) s hs

open Ito in
/-- **Every event of `𝓕_τ` agrees almost surely with an event of `⨆ₙ 𝓕_{τ ∧ σₙ}`** (the killed driving filtration,
stopping times `σₙ → V` almost surely). -/
theorem exists_ae_eq_of_measurableSet_stopped
    (hσlim : ∀ᵐ ω ∂ν, Tendsto (fun n => (σ n ω : ℝ≥0∞)) atTop (𝓝 (V ω)))
    {D : Set Ω} (hD : MeasurableSet[hτ.measurableSpace] D) :
    ∃ D', MeasurableSet[stopSup hX hτ hσ] D' ∧ D =ᵐ[ν] D' := by
  set 𝓖 := drivingFiltration ν hX with h𝓖
  set B : Set Ω := (⋃ n, {ω | τ ω ≤ σ n ω})ᶜ with hBdef
  have hle : ∀ n, MeasurableSet[stopSup hX hτ hσ] {ω | τ ω ≤ σ n ω} := fun n =>
    measurableSet_stopSup_of hX hτ hσ (IsStoppingTime.measurableSet_stopping_time_le_min hτ (hσ n))
  have hB : MeasurableSet[stopSup hX hτ hσ] B := (MeasurableSet.iUnion (m := stopSup hX hτ hσ) hle).compl
  -- the generators
  have hgen : ∀ (r : ℝ≥0) (A : Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ))), MeasurableSet A →
      MeasurableSet[aeTrace ν (stopSup hX hτ hσ) B hB]
        {ω | (r : ℝ≥0∞) < V ω ∧ (W r ω, fun i => VL i r ω, fun i => VR i r ω) ∈ A} := by
    intro r A hA
    set E := {ω | (r : ℝ≥0∞) < V ω ∧ (W r ω, fun i => VL i r ω, fun i => VR i r ω) ∈ A} with hEdef
    set En : ℕ → Set Ω := fun n => {ω | (r : WithTop ℝ≥0) < σ n ω} ∩ E with hEn
    have hEnm : ∀ n, MeasurableSet[stopSup hX hτ hσ] (En n ∩ {ω | σ n ω ≤ τ ω}) := fun n => by
      have h1 := IsStoppingTime.measurableSet_inter_le (hσ n) hτ (En n)
        (measurableSet_stopped_gen hX (hσ n) r hA)
      have h2 := (IsStoppingTime.measurableSet_min_iff (hσ n) hτ _).1 h1
      exact measurableSet_stopSup_of hX hτ hσ ((IsStoppingTime.measurableSet_min_iff hτ (hσ n) _).2
        ⟨h2.2, h2.1⟩)
    refine ⟨(⋃ n, En n ∩ {ω | σ n ω ≤ τ ω}) ∩ B, (MeasurableSet.iUnion (m := stopSup hX hτ hσ) hEnm).inter hB, ?_⟩
    filter_upwards [hσlim] with ω hω
    show (ω ∈ E ∩ B) = (ω ∈ (⋃ n, En n ∩ {ω | σ n ω ≤ τ ω}) ∩ B)
    simp only [hEn, hBdef, mem_inter_iff, mem_iUnion, mem_compl_iff, mem_ofPred_eq, eq_iff_iff, not_exists,
      not_le]
    constructor
    · rintro ⟨hωE, hωB⟩
      obtain ⟨n, hn⟩ := ((tendsto_order.1 hω).1 _ hωE.1).exists
      exact ⟨⟨n, ⟨hn, hωE⟩, (hωB n).le⟩, hωB⟩
    · rintro ⟨⟨n, ⟨_, hωE⟩, _⟩, hωB⟩
      exact ⟨hωE, hωB⟩
  -- the raw killed filtration, then its usual augmentation
  have hK : ∀ s, killedDrivingFiltration hX s ≤ aeTrace ν (stopSup hX hτ hσ) B hB := fun s =>
    MeasurableSpace.generateFrom_le fun E ⟨r, _, A, hA, hE⟩ => hE ▸ hgen r A hA
  have h𝓖 : ∀ t, 𝓖 t ≤ aeTrace ν (stopSup hX hτ hσ) B hB := fun t E hE => by
    have h1 := DomainMarkov.usualAugmentation_le_nullAugmented (P := ν) (killedDrivingFiltration hX)
      (lt_add_one t) E hE
    obtain ⟨E', hE', hEE'⟩ := exists_ae_eq_of_measurableSet_nullAugmented h1
    exact measurableSet_aeTrace_of_ae_eq hB (hK _ E' hE') hEE'
  obtain ⟨E', hE', hDE'⟩ := (iSup_le h𝓖) D hD.1
  have hDn : ∀ n, MeasurableSet[stopSup hX hτ hσ] (D ∩ {ω | τ ω ≤ σ n ω}) := fun n =>
    measurableSet_stopSup_of hX hτ hσ (IsStoppingTime.measurableSet_inter_le hτ (hσ n) D hD)
  refine ⟨(⋃ n, D ∩ {ω | τ ω ≤ σ n ω}) ∪ E', (MeasurableSet.iUnion (m := stopSup hX hτ hσ) hDn).union hE', ?_⟩
  filter_upwards [hDE'] with ω hω
  have hω' : (ω ∈ D ∩ B) = (ω ∈ E') := hω
  show (ω ∈ D) = (ω ∈ (⋃ n, D ∩ {ω | τ ω ≤ σ n ω}) ∪ E')
  rw [mem_union, ← hω']
  simp only [hBdef, mem_inter_iff, mem_iUnion, mem_compl_iff, mem_ofPred_eq, eq_iff_iff]
  constructor
  · intro hωD
    by_cases h : ∃ i, τ ω ≤ σ i ω
    · obtain ⟨i, hi⟩ := h
      exact Or.inl ⟨i, hωD, hi⟩
    · exact Or.inr ⟨hωD, h⟩
  · rintro (⟨_, hωD, _⟩ | ⟨hωD, _⟩) <;> exact hωD

/-- `τ ∧ σₙ ≤ τ`, so `⨆ₙ 𝓕_{τ ∧ σₙ} ≤ 𝓕_τ`. -/
theorem stopSup_le : stopSup hX hτ hσ ≤ hτ.measurableSpace :=
  iSup_le fun _ => IsStoppingTime.measurableSpace_mono _ hτ fun _ => min_le_left _ _

/-- The filtration `n ↦ 𝓕_{τ ∧ σₙ}` (`σ` nondecreasing). -/
def stopMinFilt (hσm : ∀ ω, Monotone fun n => σ n ω) : Filtration ℕ mΩ where
  seq n := (hτ.min (hσ n)).measurableSpace
  mono' _ _ hmn := IsStoppingTime.measurableSpace_mono _ _ fun ω => min_le_min le_rfl (hσm ω hmn)
  le' n := (hτ.min (hσ n)).measurableSpace_le

/-- **Conditional expectations given `𝓕_τ` and given `⨆ₙ 𝓕_{τ ∧ σₙ}` agree.** -/
theorem condExp_stopped_ae_eq [IsFiniteMeasure ν]
    (hσlim : ∀ᵐ ω ∂ν, Tendsto (fun n => (σ n ω : ℝ≥0∞)) atTop (𝓝 (V ω))) {Z : Ω → ℂ} (hZ : Integrable Z ν) :
    ν[Z | hτ.measurableSpace] =ᵐ[ν] ν[Z | stopSup hX hτ hσ] := by
  have hGle : stopSup hX hτ hσ ≤ mΩ := (stopSup_le hX hτ hσ).trans hτ.measurableSpace_le
  refine (ae_eq_condExp_of_forall_setIntegral_eq hτ.measurableSpace_le hZ
    (fun _ _ _ => integrable_condExp.integrableOn) (fun D hD _ => ?_)
    ((stronglyMeasurable_condExp.mono (stopSup_le hX hτ hσ)).aestronglyMeasurable)).symm
  obtain ⟨D', hD', hDD'⟩ := exists_ae_eq_of_measurableSet_stopped hX hτ hσ hσlim hD
  rw [setIntegral_congr_set hDD', setIntegral_congr_set hDD', setIntegral_condExp hGle hZ hD']

/-- **Lévy's upward theorem along `τ ∧ σₙ`**: `E[Z | 𝓕_{τ ∧ σₙ}] → E[Z | 𝓕_τ]` almost surely. -/
theorem ae_tendsto_condExp_stopMin [IsFiniteMeasure ν] (hσm : ∀ ω, Monotone fun n => σ n ω)
    (hσlim : ∀ᵐ ω ∂ν, Tendsto (fun n => (σ n ω : ℝ≥0∞)) atTop (𝓝 (V ω))) {Z : Ω → ℂ} (hZ : Integrable Z ν) :
    ∀ᵐ ω ∂ν, Tendsto (fun n => (ν[Z | (hτ.min (hσ n)).measurableSpace]) ω) atTop
      (𝓝 ((ν[Z | hτ.measurableSpace]) ω)) := by
  have hl := WholeField.tendsto_ae_condExp_complex (P := ν) (stopMinFilt hX hτ hσ hσm) hZ
  filter_upwards [hl, condExp_stopped_ae_eq hX hτ hσ hσlim hZ] with ω h1 h2
  rw [h2]
  exact h1

end Struct


end InteractingSLE.Restart.StoppedK2
