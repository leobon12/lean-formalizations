/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.Locality11Hull

/-!
# Doob–Dynkin for the usual augmentation along a measure-preserving map

Packet PROVE-FLOWEXIST2, named input (i) (`Exist.HullClauseTransferStatement`). A measurable map `π : Ω → X` with
`P.map π = μ` and a filtration `𝒢` on `X` give the filtration `π⁻¹𝒢` on `Ω` (`filtrationComap`). This file generalizes
`Coupling.CompactTransfer` (the case `π = Prod.fst`) to any such `π`, and adds the stopping-time and
conditional-expectation forms:

* `measurableSet_usualAugmentation_comap`, `exists_ae_eq_preimage_of_measurableSet_usualAugmentation`: the usual
  augmentation of `π⁻¹𝒢` under `P` consists, up to `P`-null sets, of the preimages of the usual augmentation of `𝒢`
  under `μ`;
* **`exists_isStoppingTime_ae_eq_comp`** (Doob–Dynkin for stopping times): an almost surely finite stopping time `τ` of
  the usual augmentation of `π⁻¹𝒢` is almost surely `s ∘ π` for a finite stopping time `s` of the usual augmentation
  of `𝒢` (`s(x) = inf{q ∈ ℚ : x ∈ A_q}` with `{τ ≤ q} = π⁻¹(A_q)` almost surely);
* `measurableSet_stopped_preimage`, `exists_stopped_ae_eq_preimage`: the stopped σ-algebras correspond;
* **`condExp_comp_ae_eq`**: `E_P[g ∘ π | 𝓕_τ] = E_μ[g | 𝒢_s] ∘ π` almost surely;
* `usualAugmentation_eq_of_ae_generators`: two filtrations whose events are almost surely events of the other have the
  same usual augmentation.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Exist

open Ito Coupling

variable {Ω X : Type*} {mΩ : MeasurableSpace Ω} {mX : MeasurableSpace X}

/-- The filtration `π⁻¹𝒢` on `Ω`. -/
def filtrationComap (π : Ω → X) (hπ : Measurable π) (𝒢 : Filtration ℝ≥0 mX) : Filtration ℝ≥0 mΩ where
  seq t := (𝒢 t).comap π
  mono' _ _ hst := MeasurableSpace.comap_mono (𝒢.mono hst)
  le' t := (MeasurableSpace.comap_mono (𝒢.le t)).trans hπ.comap_le

theorem filtrationComap_apply (π : Ω → X) (hπ : Measurable π) (𝒢 : Filtration ℝ≥0 mX) (t : ℝ≥0) :
    filtrationComap π hπ 𝒢 t = (𝒢 t).comap π := rfl

variable {π : Ω → X} {P : Measure Ω} {μ : Measure X}

/-- Almost sure equality of preimages descends to the image law. -/
theorem ae_eq_of_preimage_ae_eq (hπ : Measurable π) (hμ : P.map π = μ) {C D : Set X}
    (hC : MeasurableSet C) (hD : MeasurableSet D) (h : π ⁻¹' C =ᵐ[P] π ⁻¹' D) : C =ᵐ[μ] D := by
  have hm : MeasurableSet {x : X | (x ∈ C) = (x ∈ D)} := by
    have : {x : X | (x ∈ C) = (x ∈ D)} = (C ∩ D) ∪ (Cᶜ ∩ Dᶜ) := by
      ext x; by_cases h1 : x ∈ C <;> by_cases h2 : x ∈ D <;> simp [h1, h2]
    rw [this]; exact (hC.inter hD).union (hC.compl.inter hD.compl)
  rw [← hμ]
  exact (ae_map_iff hπ.aemeasurable hm).2 h

/-- Almost sure equality under the image law pulls back. -/
theorem preimage_ae_eq_of_ae_eq (hπ : Measurable π) (hμ : P.map π = μ) {C D : Set X}
    (h : C =ᵐ[μ] D) : π ⁻¹' C =ᵐ[P] π ⁻¹' D := by
  rw [← hμ] at h
  exact ae_of_ae_map hπ.aemeasurable h

/-- **Pulled-back events of the usual augmentation.** -/
theorem measurableSet_usualAugmentation_comap (hπ : Measurable π) (hμ : P.map π = μ)
    {𝒢 : Filtration ℝ≥0 mX} {t : ℝ≥0} {E : Set X} (hE : MeasurableSet[usualAugmentation 𝒢 μ t] E) :
    MeasurableSet[usualAugmentation (filtrationComap π hπ 𝒢) P t] (π ⁻¹' E) := by
  have hEm : MeasurableSet E := (usualAugmentation 𝒢 μ).le t _ hE
  rw [usualAugmentation_apply] at hE ⊢
  simp only [MeasurableSpace.measurableSet_iInf] at hE ⊢
  intro u hu
  obtain ⟨C, hC, hEC⟩ := exists_ae_eq_of_measurableSet_nullAugmented (hE u hu)
  exact measurableSet_nullAugmented_of_ae_eq (hπ hEm)
    (MeasurableSpace.measurableSet_comap.2 ⟨C, hC, rfl⟩) (preimage_ae_eq_of_ae_eq hπ hμ hEC)

/-- `π⁻¹` maps the usual augmentation of `𝒢` into the usual augmentation of `π⁻¹𝒢`. -/
theorem comap_usualAugmentation_le (hπ : Measurable π) (hμ : P.map π = μ) (𝒢 : Filtration ℝ≥0 mX)
    (t : ℝ≥0) : (usualAugmentation 𝒢 μ t).comap π ≤ usualAugmentation (filtrationComap π hπ 𝒢) P t := by
  rintro _ ⟨E, hE, rfl⟩
  exact measurableSet_usualAugmentation_comap hπ hμ hE

/-- **Events of the usual augmentation of `π⁻¹𝒢` are almost surely preimages.** -/
theorem exists_ae_eq_preimage_of_measurableSet_usualAugmentation (hπ : Measurable π)
    (hμ : P.map π = μ) {𝒢 : Filtration ℝ≥0 mX} {t : ℝ≥0} {A : Set Ω}
    (hA : MeasurableSet[usualAugmentation (filtrationComap π hπ 𝒢) P t] A) :
    ∃ A₀ : Set X, MeasurableSet[usualAugmentation 𝒢 μ t] A₀ ∧ A =ᵐ[P] π ⁻¹' A₀ := by
  set u : ℕ → ℝ≥0 := fun n => t + 1 / ((n : ℝ≥0) + 1) with hu
  have htu : ∀ n, t < u n := fun n => lt_add_of_pos_right _ (by positivity)
  have hC : ∀ n, ∃ C : Set X, MeasurableSet[𝒢 (u n)] C ∧ A =ᵐ[P] π ⁻¹' C := fun n => by
    obtain ⟨A', hA', hAA'⟩ := exists_ae_eq_of_measurableSet_usualAugmentation (htu n) hA
    obtain ⟨C, hCm, rfl⟩ := MeasurableSpace.measurableSet_comap.1 hA'
    exact ⟨C, hCm, hAA'⟩
  choose C hCm hAC using hC
  have hCm' : ∀ n, MeasurableSet (C n) := fun n => 𝒢.le _ _ (hCm n)
  have hCC : ∀ n m, C n =ᵐ[μ] C m := fun n m =>
    ae_eq_of_preimage_ae_eq hπ hμ (hCm' n) (hCm' m) ((hAC n).symm.trans (hAC m))
  set A₀ := ⋂ n, C n with hA₀
  have hA₀m : MeasurableSet A₀ := MeasurableSet.iInter hCm'
  have hA₀C : ∀ m, A₀ =ᵐ[μ] C m := fun m => by
    have := Filter.EventuallyEqSet.countable_iInter (fun n => hCC n m)
    simpa only [iInter_const] using this
  refine ⟨A₀, ?_, (hAC 0).trans (preimage_ae_eq_of_ae_eq hπ hμ (hA₀C 0).symm)⟩
  rw [usualAugmentation_apply]
  simp only [MeasurableSpace.measurableSet_iInf]
  intro v hv
  obtain ⟨m, hm⟩ : ∃ m : ℕ, u m ≤ v := by
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt (sub_pos.2 (show (t : ℝ) < v from hv))
    refine ⟨m, ?_⟩
    rw [hu, ← NNReal.coe_le_coe, NNReal.coe_add]
    push_cast
    linarith
  exact measurableSet_nullAugmented_of_ae_eq hA₀m (𝒢.mono hm _ (hCm m)) (hA₀C m)

/-- The events of `⨆ₜ` of the usual augmentation of `π⁻¹𝒢` are almost surely preimages of events of `⨆ₜ` of the
usual augmentation of `𝒢`. -/
theorem exists_ae_eq_preimage_of_measurableSet_iSup (hπ : Measurable π) (hμ : P.map π = μ)
    {𝒢 : Filtration ℝ≥0 mX} {A : Set Ω}
    (hA : MeasurableSet[⨆ t, usualAugmentation (filtrationComap π hπ 𝒢) P t] A) :
    ∃ A₀ : Set X, MeasurableSet[⨆ t, usualAugmentation 𝒢 μ t] A₀ ∧ A =ᵐ[P] π ⁻¹' A₀ := by
  -- the sets with this property form a σ-algebra containing every `usualAugmentation (π⁻¹𝒢) P t`
  rw [MeasurableSpace.measurableSet_iSup] at hA
  induction hA with
  | basic A hA =>
    obtain ⟨t, ht⟩ := hA
    obtain ⟨A₀, hA₀, h⟩ := exists_ae_eq_preimage_of_measurableSet_usualAugmentation hπ hμ ht
    exact ⟨A₀, le_iSup (fun t => usualAugmentation 𝒢 μ t) t _ hA₀, h⟩
  | empty => exact ⟨∅, @MeasurableSet.empty _ (⨆ t, usualAugmentation 𝒢 μ t), by simp⟩
  | compl A _ ih =>
    obtain ⟨A₀, hA₀, h⟩ := ih
    exact ⟨A₀ᶜ, hA₀.compl, by rw [preimage_compl]; exact h.compl⟩
  | iUnion A _ ih =>
    choose A₀ hA₀ h using ih
    exact ⟨⋃ n, A₀ n, MeasurableSet.iUnion hA₀, by
      rw [preimage_iUnion]; exact Filter.EventuallyEqSet.countable_iUnion h⟩

/-! ### Doob–Dynkin for stopping times -/

/-- The rational time `q⁺`. -/
def ratTime (q : ℚ) : ℝ≥0 := Real.toNNReal q

/-- Every `a : WithTop ℝ≥0` is the infimum of the rational times above it. -/
theorem eq_iInf_ratTime_le (a : WithTop ℝ≥0) :
    a = ⨅ (q : ℚ) (_ : a ≤ (ratTime q : WithTop ℝ≥0)), (ratTime q : WithTop ℝ≥0) := by
  refine le_antisymm (le_iInf₂ fun q hq => hq) ?_
  refine le_of_forall_gt fun c hc => ?_
  induction a using WithTop.recTopCoe with
  | top => exact absurd hc (not_lt_of_ge le_top)
  | coe a =>
    have : ∃ q : ℚ, (a : ℝ) < q ∧ (ratTime q : WithTop ℝ≥0) < c := by
      induction c using WithTop.recTopCoe with
      | top =>
        obtain ⟨q, hq⟩ := exists_rat_gt (a : ℝ)
        exact ⟨q, hq, WithTop.coe_lt_top _⟩
      | coe c =>
        have hc' : (a : ℝ) < c := by exact_mod_cast hc
        obtain ⟨q, h1, h2⟩ := exists_rat_btwn hc'
        refine ⟨q, h1, ?_⟩
        have : ratTime q < c := by
          rw [← NNReal.coe_lt_coe, ratTime, Real.coe_toNNReal _ ((a.coe_nonneg).trans h1.le)]
          exact h2
        exact_mod_cast this
    obtain ⟨q, h1, h2⟩ := this
    have hle : ((a : ℝ≥0) : WithTop ℝ≥0) ≤ (ratTime q : WithTop ℝ≥0) := by
      have : a ≤ ratTime q := by
        rw [← NNReal.coe_le_coe, ratTime, Real.coe_toNNReal _ ((a.coe_nonneg).trans h1.le)]
        exact h1.le
      exact_mod_cast this
    exact lt_of_le_of_lt (iInf₂_le q hle) h2

/-- **Doob–Dynkin for stopping times.** An almost surely finite stopping time `τ` of the usual augmentation of `π⁻¹𝒢`
is almost surely `s ∘ π` for a finite stopping time `s` of the usual augmentation of `𝒢` under `μ = P.map π`. -/
theorem exists_isStoppingTime_ae_eq_comp (hπ : Measurable π) (hμ : P.map π = μ)
    {𝒢 : Filtration ℝ≥0 mX} {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime (usualAugmentation (filtrationComap π hπ 𝒢) P) τ) (hτfin : ∀ᵐ ω ∂P, τ ω ≠ ⊤) :
    ∃ s : X → ℝ≥0, IsStoppingTime (usualAugmentation 𝒢 μ) (fun x => (s x : WithTop ℝ≥0)) ∧
      ∀ᵐ ω ∂P, τ ω = (s (π ω) : WithTop ℝ≥0) := by
  have hq : ∀ q : ℚ, ∃ A : Set X, MeasurableSet[usualAugmentation 𝒢 μ (ratTime q)] A ∧
      {ω | τ ω ≤ (ratTime q : WithTop ℝ≥0)} =ᵐ[P] π ⁻¹' A := fun q =>
    exists_ae_eq_preimage_of_measurableSet_usualAugmentation hπ hμ (hτ _)
  choose A hAm hA using hq
  have hAm' : ∀ q, MeasurableSet (A q) := fun q => (usualAugmentation 𝒢 μ).le _ _ (hAm q)
  set σ : X → WithTop ℝ≥0 := fun x => ⨅ (q : ℚ) (_ : x ∈ A q), (ratTime q : WithTop ℝ≥0) with hσ
  have hσlt : ∀ t : ℝ≥0, MeasurableSet[usualAugmentation 𝒢 μ t] {x | σ x < t} := fun t => by
    have e : {x | σ x < t} = ⋃ (q : ℚ) (_ : ratTime q < t), A q := by
      ext x
      simp only [hσ, mem_ofPred_eq, mem_iUnion, iInf_lt_iff, exists_prop, WithTop.coe_lt_coe]
      constructor
      · rintro ⟨q, hx, hq⟩; exact ⟨q, hq, hx⟩
      · rintro ⟨q, hq, hx⟩; exact ⟨q, hx, hq⟩
    rw [e]
    exact MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun hq =>
      (usualAugmentation 𝒢 μ).mono hq.le _ (hAm q)
  have hσst : IsStoppingTime (usualAugmentation 𝒢 μ) σ :=
    isStoppingTime_of_measurableSet_lt_of_isRightContinuous hσlt
  have hall : ∀ᵐ ω ∂P, ∀ q : ℚ, (τ ω ≤ (ratTime q : WithTop ℝ≥0)) = (π ω ∈ A q) :=
    ae_all_iff.2 fun q => hA q
  have hτσ : ∀ᵐ ω ∂P, τ ω = σ (π ω) := by
    filter_upwards [hall] with ω hω
    rw [eq_iInf_ratTime_le (τ ω)]
    simp only [hσ]
    exact iInf_congr fun q => by rw [hω q]
  have htop : {x | σ x = ⊤} = ⋂ q, (A q)ᶜ := by
    ext x
    simp only [hσ, mem_ofPred_eq, mem_iInter, mem_compl_iff, iInf_eq_top, WithTop.coe_ne_top,
      imp_false]
  have htop_m : MeasurableSet {x | σ x = ⊤} := by
    rw [htop]; exact MeasurableSet.iInter fun q => (hAm' q).compl
  have htop0 : μ {x | σ x = ⊤} = 0 := by
    rw [← hμ, Measure.map_apply hπ htop_m]
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hτσ, hτfin] with ω h1 h2
    simp only [mem_preimage, mem_ofPred_eq]
    rw [← h1]; exact h2
  refine ⟨fun x => (σ x).untopD 0, fun t => ?_, ?_⟩
  · have e : {x | (((σ x).untopD 0 : ℝ≥0) : WithTop ℝ≥0) ≤ t} = {x | σ x ≤ t} ∪ {x | σ x = ⊤} := by
      ext x
      simp only [mem_ofPred_eq, mem_union]
      induction σ x using WithTop.recTopCoe with
      | top => simp only [or_true, iff_true]; exact WithTop.coe_le_coe.2 t.2
      | coe a =>
        change ((a : WithTop ℝ≥0) ≤ t) ↔ _
        exact ⟨Or.inl, fun h => h.elim id fun h => absurd h WithTop.coe_ne_top⟩
    rw [e]
    exact (hσst t).union (measurableSet_usualAugmentation_of_null htop_m htop0 t)
  · filter_upwards [hτσ, hτfin] with ω h1 h2
    rw [h1] at h2 ⊢
    obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.1 h2
    rw [← ha]
    rfl

/-! ### Stopped σ-algebras and conditional expectations -/

section Stopped

variable {𝒢 : Filtration ℝ≥0 mX}

/-- `σ ∘ π` is a stopping time of the usual augmentation of `π⁻¹𝒢`. -/
theorem isStoppingTime_comp (hπ : Measurable π) (hμ : P.map π = μ) {σ : X → WithTop ℝ≥0}
    (hσ : IsStoppingTime (usualAugmentation 𝒢 μ) σ) :
    IsStoppingTime (usualAugmentation (filtrationComap π hπ 𝒢) P) (fun ω => σ (π ω)) := fun t =>
  measurableSet_usualAugmentation_comap hπ hμ (hσ t)

/-- Of two almost surely equal stopping times of a usual augmentation, the stopped σ-algebra of one is contained in
that of the other. -/
theorem measurableSet_stopped_of_ae_eq_time {𝓕 : Filtration ℝ≥0 mΩ} {τ τ' : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime (usualAugmentation 𝓕 P) τ) (hτ' : IsStoppingTime (usualAugmentation 𝓕 P) τ')
    (h : ∀ᵐ ω ∂P, τ ω = τ' ω) {A : Set Ω} (hA : MeasurableSet[hτ'.measurableSpace] A) :
    MeasurableSet[hτ.measurableSpace] A := by
  have hAm : MeasurableSet A := hτ'.measurableSpace_le _ hA
  rw [IsStoppingTime.measurableSet] at hA ⊢
  refine ⟨hA.1, fun i => ?_⟩
  have hτm : MeasurableSet {ω | τ ω ≤ i} := (usualAugmentation 𝓕 P).le i _ (hτ i)
  refine Coupling.measurableSet_usualAugmentation_of_ae_eq (hAm.inter hτm) (hA.2 i) ?_
  have h' : {ω | τ ω ≤ (i : WithTop ℝ≥0)} =ᵐ[P] {ω | τ' ω ≤ (i : WithTop ℝ≥0)} := by
    filter_upwards [h] with ω hω
    rw [hω]
  exact Filter.EventuallyEqSet.inter (EventuallyEq.refl _ _) h'

/-- **Preimages of stopped events are stopped events.** -/
theorem measurableSet_stopped_preimage (hπ : Measurable π) (hμ : P.map π = μ) {σ : X → WithTop ℝ≥0}
    (hσ : IsStoppingTime (usualAugmentation 𝒢 μ) σ) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime (usualAugmentation (filtrationComap π hπ 𝒢) P) τ)
    (hτσ : ∀ᵐ ω ∂P, τ ω = σ (π ω)) {A₀ : Set X} (hA₀ : MeasurableSet[hσ.measurableSpace] A₀) :
    MeasurableSet[hτ.measurableSpace] (π ⁻¹' A₀) := by
  have hστ := isStoppingTime_comp hπ hμ hσ
  refine measurableSet_stopped_of_ae_eq_time hτ hστ hτσ ?_
  rw [IsStoppingTime.measurableSet] at hA₀ ⊢
  refine ⟨?_, fun i => measurableSet_usualAugmentation_comap hπ hμ (hA₀.2 i)⟩
  have h1 : MeasurableSet[(⨆ t, usualAugmentation 𝒢 μ t).comap π] (π ⁻¹' A₀) := ⟨A₀, hA₀.1, rfl⟩
  rw [MeasurableSpace.comap_iSup] at h1
  exact iSup_mono (fun t => comap_usualAugmentation_le hπ hμ 𝒢 t) _ h1

/-- **Stopped events are almost surely preimages of stopped events.** -/
theorem exists_stopped_ae_eq_preimage (hπ : Measurable π) (hμ : P.map π = μ) {s : X → ℝ≥0}
    (hs : IsStoppingTime (usualAugmentation 𝒢 μ) fun x => (s x : WithTop ℝ≥0)) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime (usualAugmentation (filtrationComap π hπ 𝒢) P) τ)
    (hτs : ∀ᵐ ω ∂P, τ ω = (s (π ω) : WithTop ℝ≥0)) {A : Set Ω}
    (hA : MeasurableSet[hτ.measurableSpace] A) :
    ∃ A₀ : Set X, MeasurableSet[hs.measurableSpace] A₀ ∧ A =ᵐ[P] π ⁻¹' A₀ := by
  have hst : IsStoppingTime (usualAugmentation (filtrationComap π hπ 𝒢) P)
      (fun ω => (s (π ω) : WithTop ℝ≥0)) := isStoppingTime_comp hπ hμ hs
  have hA' : MeasurableSet[hst.measurableSpace] A :=
    measurableSet_stopped_of_ae_eq_time hst hτ (hτs.mono fun ω h => h.symm) hA
  set 𝓖₀ := usualAugmentation 𝒢 μ with h𝓖₀
  rw [IsStoppingTime.measurableSet] at hA'
  have hB : ∀ r : ℝ≥0, ∃ B : Set X, MeasurableSet[𝓖₀ r] B ∧
      A ∩ {ω | (s (π ω) : WithTop ℝ≥0) ≤ r} =ᵐ[P] π ⁻¹' (B ∩ {x | s x ≤ r}) := fun r => by
    obtain ⟨B, hBm, hAB⟩ := exists_ae_eq_preimage_of_measurableSet_usualAugmentation hπ hμ (hA'.2 r)
    refine ⟨B, hBm, ?_⟩
    have e1 : A ∩ {ω | (s (π ω) : WithTop ℝ≥0) ≤ r} =
        (A ∩ {ω | (s (π ω) : WithTop ℝ≥0) ≤ r}) ∩ (π ⁻¹' {x | s x ≤ r}) := by
      ext ω; simp only [mem_inter_iff, mem_ofPred_eq, mem_preimage, WithTop.coe_le_coe]; tauto
    rw [e1, preimage_inter]
    exact Filter.EventuallyEqSet.inter hAB (EventuallyEq.refl _ _)
  choose B hBm hAB using hB
  have hsle : ∀ r : ℝ≥0, MeasurableSet[𝓖₀ r] {x | s x ≤ r} := fun r => by
    have := hs r
    simpa only [WithTop.coe_le_coe] using this
  set A₀ := ⋃ n : ℕ, (B n ∩ {x | s x ≤ n}) with hA₀
  have hA₀m : MeasurableSet A₀ :=
    MeasurableSet.iUnion fun n => 𝓖₀.le _ _ ((hBm n).inter (hsle n))
  have hAeq : A =ᵐ[P] π ⁻¹' A₀ := by
    have e : A = ⋃ n : ℕ, (A ∩ {ω | (s (π ω) : WithTop ℝ≥0) ≤ (n : ℝ≥0)}) := by
      ext ω
      simp only [mem_iUnion, mem_inter_iff, mem_ofPred_eq, WithTop.coe_le_coe]
      constructor
      · intro h
        obtain ⟨n, hn⟩ := exists_nat_ge (s (π ω))
        exact ⟨n, h, hn⟩
      · rintro ⟨_, h, -⟩; exact h
    rw [e, hA₀, preimage_iUnion]
    exact Filter.EventuallyEqSet.countable_iUnion fun n => hAB n
  refine ⟨A₀, ?_, hAeq⟩
  rw [IsStoppingTime.measurableSet]
  refine ⟨?_, fun r => ?_⟩
  · exact MeasurableSet.iUnion fun n =>
      (le_iSup (fun t => 𝓖₀ t) (n : ℝ≥0)) _ ((hBm n).inter (hsle n))
  · have hsr : MeasurableSet {x | s x ≤ r} := 𝓖₀.le _ _ (hsle r)
    have hm : MeasurableSet (A₀ ∩ {x | (s x : WithTop ℝ≥0) ≤ (r : WithTop ℝ≥0)}) := by
      simpa only [WithTop.coe_le_coe] using hA₀m.inter hsr
    have hBr : MeasurableSet (B r ∩ {x | s x ≤ r}) := 𝓖₀.le _ _ ((hBm r).inter (hsle r))
    have hae : A₀ ∩ {x | (s x : WithTop ℝ≥0) ≤ (r : WithTop ℝ≥0)} =ᵐ[μ] B r ∩ {x | s x ≤ r} := by
      refine ae_eq_of_preimage_ae_eq hπ hμ hm hBr ?_
      have e : π ⁻¹' (A₀ ∩ {x | (s x : WithTop ℝ≥0) ≤ (r : WithTop ℝ≥0)}) =
          π ⁻¹' A₀ ∩ {ω | (s (π ω) : WithTop ℝ≥0) ≤ r} := rfl
      rw [e]
      exact (Filter.EventuallyEqSet.inter hAeq.symm (EventuallyEq.refl _ _)).trans (hAB r)
    have h := measurableSet_nullAugmented_of_ae_eq (𝓕 := 𝓖₀) (P := μ) hm
      ((hBm r).inter (hsle r)) hae
    rwa [nullAugmented_usualAugmentation] at h

/-- **Conditional expectations transfer**: `E_P[g ∘ π | 𝓕_τ] = E_μ[g | 𝒢_s] ∘ π` almost surely, when `τ = s ∘ π`
almost surely. -/
theorem condExp_comp_ae_eq [IsFiniteMeasure P] (hπ : Measurable π) (hμ : P.map π = μ) {s : X → ℝ≥0}
    (hs : IsStoppingTime (usualAugmentation 𝒢 μ) fun x => (s x : WithTop ℝ≥0)) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime (usualAugmentation (filtrationComap π hπ 𝒢) P) τ)
    (hτs : ∀ᵐ ω ∂P, τ ω = (s (π ω) : WithTop ℝ≥0)) {g : X → ℂ} (hg : Integrable g μ) :
    P[fun ω => g (π ω) | hτ.measurableSpace] =ᵐ[P] fun ω => μ[g | hs.measurableSpace] (π ω) := by
  have hμP : IsFiniteMeasure μ := by rw [← hμ]; infer_instance
  set c := μ[g | hs.measurableSpace] with hc
  have hgP : Integrable (fun ω => g (π ω)) P := by
    rw [← hμ] at hg; exact hg.comp_measurable hπ
  have hcm : StronglyMeasurable[hs.measurableSpace] c := stronglyMeasurable_condExp
  have hcmX : StronglyMeasurable c := hcm.mono hs.measurableSpace_le
  have hcint : Integrable c μ := integrable_condExp
  have hcP : Integrable (fun ω => c (π ω)) P := by
    rw [← hμ] at hcint; exact hcint.comp_measurable hπ
  have hmeas : Measurable[hτ.measurableSpace, hs.measurableSpace] π := fun A hA =>
    measurableSet_stopped_preimage hπ hμ hs hτ hτs hA
  refine (ae_eq_condExp_of_forall_setIntegral_eq hτ.measurableSpace_le hgP
    (fun t _ _ => hcP.integrableOn) (fun t ht _ => ?_) ?_).symm
  · obtain ⟨t₀, ht₀, htt₀⟩ := exists_stopped_ae_eq_preimage hπ hμ hs hτ hτs ht
    have ht₀m : MeasurableSet t₀ := hs.measurableSpace_le _ ht₀
    rw [setIntegral_congr_set htt₀, setIntegral_congr_set htt₀]
    have h1 := MeasureTheory.setIntegral_map (μ := P) (g := π) ht₀m (f := c)
      (by rw [hμ]; exact hcmX.aestronglyMeasurable) hπ.aemeasurable
    have h2 := MeasureTheory.setIntegral_map (μ := P) (g := π) ht₀m (f := g)
      (by rw [hμ]; exact hg.aestronglyMeasurable) hπ.aemeasurable
    rw [hμ] at h1 h2
    rw [← h1, ← h2, hc, setIntegral_condExp hs.measurableSpace_le hg ht₀]
  · exact (hcm.comp_measurable hmeas).aestronglyMeasurable

end Stopped

/-! ### Filtrations with almost surely equal events -/

/-- Two filtrations whose events are, at each time, events of the other's null augmentation have the same usual
augmentation. -/
theorem usualAugmentation_eq_of_le_nullAugmented {𝓕₁ 𝓕₂ : Filtration ℝ≥0 mΩ}
    (h₁ : ∀ t, 𝓕₁ t ≤ nullAugmented 𝓕₂ P t) (h₂ : ∀ t, 𝓕₂ t ≤ nullAugmented 𝓕₁ P t) :
    usualAugmentation 𝓕₁ P = usualAugmentation 𝓕₂ P := by
  have key : ∀ {𝓐 𝓑 : Filtration ℝ≥0 mΩ}, (∀ t, 𝓐 t ≤ nullAugmented 𝓑 P t) →
      usualAugmentation 𝓐 P ≤ usualAugmentation 𝓑 P := fun {𝓐 𝓑} h t => by
    rw [usualAugmentation_apply, usualAugmentation_apply]
    refine iInf₂_mono fun u _ => ?_
    rw [nullAugmented_apply, nullAugmented_apply]
    exact sup_le (h u) le_sup_right
  exact le_antisymm (key h₁) (key h₂)

end Exist

end InteractingSLE
