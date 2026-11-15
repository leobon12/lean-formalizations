/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.RestartMarkov

/-!
# Stopping times of the restarted filtration `s ↦ 𝓕_{T+s}`

Packet PROVE-SEC5-D (Aux. lemma 53, specification p. 245: "At every finite own-filtration stopping time `τ < T_*`,
condition on the recorded driving history … For a later retained stopping time, the old hull is contained in the later
hull"). A stopping time `τ'` of the restarted filtration `𝓖'_s = 𝓕_{T+s}` (`Sec2.Restart.restartFiltration`) is a later
stopping time `T + τ'` of `𝓕`, with the same stopped σ-algebra. This holds for a right-continuous filtration containing
the null sets (the frozen `drivingFiltration` is such a filtration), provided `τ'` is almost surely finite; the finite
version `restartTime T τ' = T + τ'.untopD 0` is used so that its value is defined on every path.

* `measurableSet_inter_lt_of_measurableSet`: `A ∈ 𝓕_ρ ⇒ A ∩ {ρ < t} ∈ 𝓕_t`;
* `isStoppingTime_restartTime`: `T + τ'` is an `𝓕`-stopping time;
* `measurableSpace_restartTime_eq`: its stopped σ-algebra is the stopped σ-algebra of `τ'` for `𝓖'`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec5

namespace Markov

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ}

/-- The finite restart time `T + τ'` (the value `T` where `τ' = ⊤`, a null event in the applications). -/
def restartTime (T : Ω → ℝ≥0) (τ : Ω → WithTop ℝ≥0) (ω : Ω) : WithTop ℝ≥0 :=
  ((T ω + (τ ω).untopD 0 : ℝ≥0) : WithTop ℝ≥0)

theorem restartTime_untopD (T : Ω → ℝ≥0) (τ : Ω → WithTop ℝ≥0) (ω : Ω) :
    (restartTime T τ ω).untopD 0 = T ω + (τ ω).untopD 0 := rfl

/-- `A ∈ 𝓕_ρ ⇒ A ∩ {ρ < t} ∈ 𝓕_t`. -/
theorem measurableSet_inter_lt_of_measurableSet {ρ : Ω → WithTop ℝ≥0} (hρ : IsStoppingTime 𝓕 ρ)
    {A : Set Ω} (hA : MeasurableSet[hρ.measurableSpace] A) (t : ℝ≥0) :
    MeasurableSet[𝓕 t] (A ∩ {ω | ρ ω < t}) := by
  rcases eq_zero_or_pos t with rfl | ht
  · have : A ∩ {ω | ρ ω < ((0 : ℝ≥0) : WithTop ℝ≥0)} = ∅ := by
      ext ω; simp only [mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
      intro _ h
      exact (not_lt.2 (by simp)) h
    rw [this]; exact @MeasurableSet.empty Ω (𝓕 0)
  have key : ∀ q : ℚ, (q : ℝ) < t → (q : ℝ).toNNReal < t := fun q hq => by
    rcases le_or_gt 0 (q : ℝ) with h | h
    · exact (Real.toNNReal_lt_iff_lt_coe h).2 hq
    · rw [Real.toNNReal_of_nonpos h.le]; exact ht
  have heq : A ∩ {ω | ρ ω < t} = ⋃ (q : ℚ) (_ : (q : ℝ) < t),
      A ∩ {ω | ρ ω ≤ (((q : ℝ).toNNReal : ℝ≥0) : WithTop ℝ≥0)} := by
    ext ω
    simp only [mem_inter_iff, mem_ofPred_eq, mem_iUnion, exists_prop]
    constructor
    · rintro ⟨hA, hlt⟩
      obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_lt hlt)
      rw [← hr] at hlt ⊢
      have hrt : (r : ℝ) < t := by exact_mod_cast hlt
      obtain ⟨q, hrq, hqt⟩ := exists_rat_btwn hrt
      refine ⟨q, hqt, hA, ?_⟩
      exact_mod_cast (Real.le_toNNReal_iff_coe_le (r.coe_nonneg.trans hrq.le)).2 hrq.le
    · rintro ⟨q, hqt, hA, hle⟩
      refine ⟨hA, hle.trans_lt ?_⟩
      exact_mod_cast key q hqt
  rw [heq]
  refine MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun hqt => ?_
  have hqle : (q : ℝ).toNNReal ≤ t := (key q hqt).le
  exact 𝓕.mono hqle _ (hA.2 _)

/-! ### Later stopping times -/

section Restart

open Sec2.Restart

variable {P : Measure Ω} {T : Ω → ℝ≥0} (hT : IsStoppingTime 𝓕 fun ω => (T ω : WithTop ℝ≥0))
  {τ : Ω → WithTop ℝ≥0}

/-- `{τ = ⊤}` is measurable for a stopping time of the restarted filtration. -/
theorem measurableSet_eq_top (hτ : IsStoppingTime (restartFiltration 𝓕 T hT) τ) :
    MeasurableSet {ω | τ ω = ⊤} := by
  have e : {ω | τ ω = ⊤} = (⋃ n : ℕ, {ω | τ ω ≤ (n : ℝ≥0)})ᶜ := by
    ext ω
    simp only [mem_ofPred_eq, mem_compl_iff, mem_iUnion, not_exists, not_le]
    constructor
    · intro h n; rw [h]; exact WithTop.coe_lt_top _
    · intro h
      by_contra hne
      obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 hne
      obtain ⟨n, hn⟩ := exists_nat_ge r
      exact (not_le.2 (h n)) (by rw [← hr]; exact_mod_cast hn)
  rw [e]
  exact (MeasurableSet.iUnion fun n : ℕ => (restartFiltration 𝓕 T hT).le _ _ (hτ (n : ℝ≥0))).compl

variable (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → ∀ t, MeasurableSet[𝓕 t] s)
include hnull

/-- **The key decomposition.** For `A` in the stopped σ-algebra of `τ` (restarted filtration) and `τ < ⊤` almost
surely, `A ∩ {T + τ < t} ∈ 𝓕_t`. -/
theorem measurableSet_inter_restartTime_lt (hτ : IsStoppingTime (restartFiltration 𝓕 T hT) τ)
    (hτfin : ∀ᵐ ω ∂P, τ ω ≠ ⊤) {A : Set Ω} (hA : MeasurableSet[hτ.measurableSpace] A) (t : ℝ≥0) :
    MeasurableSet[𝓕 t] (A ∩ {ω | restartTime T τ ω < t}) := by
  set N := {ω | τ ω = ⊤} with hN
  have hNm : MeasurableSet N := measurableSet_eq_top hT hτ
  have hN0 : P N = 0 := by
    rw [← compl_compl N, ← mem_ae_iff]
    filter_upwards [hτfin] with ω h using h
  have hAm : MeasurableSet A := (hτ.measurableSpace_le) _ hA
  have heq : A ∩ {ω | restartTime T τ ω < t} = ((A ∩ N) ∩ {ω | (T ω : WithTop ℝ≥0) < t}) ∪
      ⋃ (q : ℚ) (_ : 0 < q), (A ∩ {ω | τ ω ≤ (((q : ℝ).toNNReal : ℝ≥0) : WithTop ℝ≥0)}) ∩
        {ω | ((T ω + (q : ℝ).toNNReal : ℝ≥0) : WithTop ℝ≥0) < t} := by
    ext ω
    simp only [restartTime, mem_inter_iff, mem_union, mem_ofPred_eq, mem_iUnion, exists_prop, hN,
      WithTop.coe_lt_coe]
    constructor
    · rintro ⟨hA, hlt⟩
      by_cases htop : τ ω = ⊤
      · left
        rw [htop, WithTop.untopD_top, add_zero] at hlt
        exact ⟨⟨hA, htop⟩, hlt⟩
      · right
        obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 htop
        rw [← hr, WithTop.untopD_coe] at hlt
        have hrt : (r : ℝ) < (t : ℝ) - T ω := by
          have : ((T ω + r : ℝ≥0) : ℝ) < t := by exact_mod_cast hlt
          push_cast at this; linarith
        obtain ⟨q, hrq, hqt⟩ := exists_rat_btwn hrt
        have hq0 : (0 : ℝ) < q := r.coe_nonneg.trans_lt hrq
        refine ⟨q, by exact_mod_cast hq0, ⟨hA, ?_⟩, ?_⟩
        · rw [← hr]
          exact_mod_cast (Real.le_toNNReal_iff_coe_le hq0.le).2 hrq.le
        · rw [← NNReal.coe_lt_coe, NNReal.coe_add, Real.coe_toNNReal _ hq0.le]
          linarith
    · rintro (⟨⟨hA, htop⟩, hlt⟩ | ⟨q, -, ⟨hA, hle⟩, hlt⟩)
      · refine ⟨hA, ?_⟩
        rw [htop, WithTop.untopD_top, add_zero]; exact hlt
      · refine ⟨hA, lt_of_le_of_lt ?_ hlt⟩
        obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_le_ne_top WithTop.coe_ne_top hle)
        rw [← hr] at hle ⊢
        rw [WithTop.untopD_coe]
        exact add_le_add le_rfl (by exact_mod_cast hle)
  rw [heq]
  refine MeasurableSet.union ?_ (MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun _ => ?_)
  · refine MeasurableSet.inter ?_ (hT.measurableSet_lt t)
    refine hnull _ (hAm.inter hNm) (measure_mono_null inter_subset_right hN0) t
  · have hA' : MeasurableSet[(isStoppingTime_add_const hT (q : ℝ).toNNReal).measurableSpace]
        (A ∩ {ω | τ ω ≤ (((q : ℝ).toNNReal : ℝ≥0) : WithTop ℝ≥0)}) := hA.2 _
    exact measurableSet_inter_lt_of_measurableSet _ hA' t

variable [𝓕.IsRightContinuous]

/-- **`T + τ'` is a stopping time** of a right-continuous filtration containing the null sets, for a stopping time
`τ'` of the restarted filtration that is almost surely finite. -/
theorem isStoppingTime_restartTime (hτ : IsStoppingTime (restartFiltration 𝓕 T hT) τ)
    (hτfin : ∀ᵐ ω ∂P, τ ω ≠ ⊤) : IsStoppingTime 𝓕 (restartTime T τ) := by
  refine isStoppingTime_of_measurableSet_lt_of_isRightContinuous fun t => ?_
  have h := measurableSet_inter_restartTime_lt hT hnull hτ hτfin (A := univ)
    (@MeasurableSet.univ Ω hτ.measurableSpace) t
  rwa [univ_inter] at h

omit hnull in
/-- A stopping time restricted to an event: `ρ` on `A`, `⊤` off `A`. -/
private theorem measurableSet_inter_le_of_lt {ρ : Ω → WithTop ℝ≥0} {A : Set Ω}
    (h : ∀ t : ℝ≥0, MeasurableSet[𝓕 t] (A ∩ {ω | ρ ω < t})) (t : ℝ≥0) :
    MeasurableSet[𝓕 t] (A ∩ {ω | ρ ω ≤ t}) := by
  classical
  set ρA : Ω → WithTop ℝ≥0 := fun ω => if ω ∈ A then ρ ω else ⊤ with hρA
  have hlt : ∀ u : ℝ≥0, {ω | ρA ω < u} = A ∩ {ω | ρ ω < u} := fun u => by
    ext ω
    by_cases hω : ω ∈ A <;> simp [hρA, hω]
    exact not_top_lt
  have hst : IsStoppingTime 𝓕 ρA :=
    isStoppingTime_of_measurableSet_lt_of_isRightContinuous fun u => by rw [hlt]; exact h u
  have hle : {ω | ρA ω ≤ t} = A ∩ {ω | ρ ω ≤ t} := by
    ext ω
    by_cases hω : ω ∈ A <;> simp [hρA, hω]
    exact fun h => WithTop.coe_ne_top (top_le_iff.1 h)
  rw [← hle]; exact hst t

omit hnull [𝓕.IsRightContinuous] in
/-- `𝓕_t ⊆ 𝓕_{T+t}`. -/
theorem le_restartFiltration (t : ℝ≥0) : 𝓕 t ≤ restartFiltration 𝓕 T hT t := by
  intro B hB
  refine ⟨(le_iSup (fun i => (𝓕 i : MeasurableSpace Ω)) t) _ hB, fun u => ?_⟩
  by_cases htu : t ≤ u
  · exact (𝓕.mono htu _ hB).inter (isStoppingTime_add_const hT t u)
  · have e : B ∩ {ω | ((T ω + t : ℝ≥0) : WithTop ℝ≥0) ≤ u} = ∅ := by
      ext ω
      simp only [mem_inter_iff, mem_ofPred_eq, WithTop.coe_le_coe, mem_empty_iff_false, iff_false,
        not_and, not_le]
      exact fun _ => (lt_of_not_ge htu).trans_le le_add_self
    rw [e]; exact @MeasurableSet.empty Ω (𝓕 u)

/-- **The stopped σ-algebras agree**: `𝓖'_{τ'} = 𝓕_{T+τ'}`. -/
theorem measurableSpace_restartTime_eq (hτ : IsStoppingTime (restartFiltration 𝓕 T hT) τ)
    (hτfin : ∀ᵐ ω ∂P, τ ω ≠ ⊤) :
    hτ.measurableSpace = (isStoppingTime_restartTime hT hnull hτ hτfin).measurableSpace := by
  set hσ := isStoppingTime_restartTime hT hnull hτ hτfin
  set N := {ω | τ ω = ⊤} with hN
  have hNm : MeasurableSet N := measurableSet_eq_top hT hτ
  have hN0 : P N = 0 := by
    rw [← compl_compl N, ← mem_ae_iff]
    filter_upwards [hτfin] with ω h using h
  have hsup : (⨆ s, restartFiltration 𝓕 T hT s) = ⨆ t, 𝓕 t := by
    refine le_antisymm (iSup_le fun s B hB => hB.1) (iSup_mono fun t => le_restartFiltration hT t)
  ext A
  constructor
  · intro hA
    refine ⟨?_, fun t => measurableSet_inter_le_of_lt
      (fun u => measurableSet_inter_restartTime_lt hT hnull hτ hτfin hA u) t⟩
    have := hA.1; rwa [hsup] at this
  · intro hA
    refine ⟨by rw [hsup]; exact hA.1, fun s => ?_⟩
    have hρ := isStoppingTime_add_const hT s
    have e : A ∩ {ω | τ ω ≤ s} =
        (A ∩ {ω | restartTime T τ ω ≤ ((T ω + s : ℝ≥0) : WithTop ℝ≥0)}) ∩ Nᶜ := by
      ext ω
      simp only [restartTime, mem_inter_iff, mem_ofPred_eq, mem_compl_iff, hN, WithTop.coe_le_coe]
      constructor
      · rintro ⟨hA, hle⟩
        obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_le_ne_top WithTop.coe_ne_top hle)
        rw [← hr] at hle ⊢
        exact ⟨⟨hA, add_le_add le_rfl (by exact_mod_cast hle)⟩, WithTop.coe_ne_top⟩
      · rintro ⟨⟨hA, hle⟩, htop⟩
        obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 htop
        rw [← hr] at hle ⊢
        rw [WithTop.untopD_coe] at hle
        exact ⟨hA, by exact_mod_cast le_of_add_le_add_left hle⟩
    rw [e]
    have h1 := IsStoppingTime.measurableSet_inter_le hσ hρ A hA
    have h2 := IsStoppingTime.measurableSpace_mono (hσ.min hρ) hρ (fun ω => min_le_right _ _) _ h1
    refine h2.inter (MeasurableSet.compl ?_)
    refine ⟨(le_iSup (fun i => (𝓕 i : MeasurableSpace Ω)) 0) _ (hnull N hNm hN0 0), fun u => ?_⟩
    exact (hnull N hNm hN0 u).inter (hρ u)

end Restart

end Markov

end Sec5

end InteractingSLE
