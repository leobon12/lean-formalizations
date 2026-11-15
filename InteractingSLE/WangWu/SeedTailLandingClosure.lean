/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.SeedTailFinishChart
import InteractingSLE.Spec.Sec6.DrivingUnconditional
import InteractingSLE.Foundations.Loewner.TraceClose
import InteractingSLE.Spec.Supplement.GB6LifeBase

/-!
# Closing a killed simple arc at a real endpoint

PROVE-WW-B27. The driving criterion applies to the closed arc: its strict
prefixes are slits ending inside the half-plane. This supplies a continuous
driver at the terminal capacity, without assuming one in the killed-arc data.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology Metric Complex
open QuantumZipper (H Hbar fwdHull)
open scoped NNReal ENNReal

namespace InteractingSLE.WangWu.SeedTail

open ImgWord Sec7.Lemma71C

/-- Criterion (a) also holds for a simple arc whose last point is on the real
boundary. Only the strict prefixes need to end inside the half-plane. -/
theorem drivingCriterionA_of_open_simple {η : ℝ → ℂ} {T : ℝ}
    (hc : ContinuousOn η (Icc 0 T)) (hi : InjOn η (Icc 0 T)) (h0 : η 0 = 0)
    (hH : MapsTo η (Ioo 0 T) H) : Sec6.DrivingCriterionA η T := by
  intro t ht
  have hfill : fillH (η '' Icc 0 t) = η '' Ioc 0 t :=
    YuanCharacterisation.fillH_image_eq ht.1.le (hc.mono (Icc_subset_Icc_right ht.2.le))
      (hi.mono (Icc_subset_Icc_right ht.2.le)) (by rw [h0, zero_im])
      (fun u hu => hH ⟨hu.1, hu.2.trans_lt ht.2⟩)
  have hmem : ∀ u ∈ Ioo t T, η u ∈ H \ fillH (η '' Icc 0 t) := by
    intro u hu
    refine ⟨hH ⟨ht.1.trans hu.1, hu.2⟩, ?_⟩
    rw [hfill]
    rintro ⟨v, hv, he⟩
    have h := hi ⟨hv.1.le, hv.2.trans ht.2.le⟩ ⟨ht.1.le.trans hu.1.le, hu.2.le⟩ he
    linarith only [hv.2, hu.1, h]
  rintro _ ⟨u, hu, rfl⟩
  rcases hu.2.lt_or_eq with huT | huT
  · exact subset_closure (hmem u ⟨hu.1, huT⟩)
  · subst u
    have hlim : Tendsto η (𝓝[<] T) (𝓝 (η T)) :=
      (hc T ⟨ht.1.le.trans ht.2.le, le_rfl⟩).mono_of_mem_nhdsWithin (Icc_mem_nhdsLT (ht.1.trans ht.2))
    exact mem_closure_of_tendsto hlim
      ((show ∀ᶠ u in 𝓝[<] T, u ∈ Ioo t T from Ioo_mem_nhdsLT ht.2).mono fun u hu => hmem u hu)

/-- A compact simple arc, interior before its last point, has a continuous
Loewner driver through that point after its capacity change of time. -/
theorem exists_driver_of_open_simple {η : ℝ → ℂ} {T : ℝ} (hT : 0 < T)
    (hc : ContinuousOn η (Icc 0 T)) (hi : InjOn η (Icc 0 T)) (h0 : η 0 = 0)
    (hH : MapsTo η (Ioo 0 T) H) (hHb : MapsTo η (Icc 0 T) Hbar) :
    ∃ U : ℝ → ℝ, Continuous U ∧ U 0 = 0 ∧ ∃ σ : ℝ → ℝ, σ 0 = 0 ∧
      StrictMonoOn σ (Icc 0 T) ∧ ContinuousOn σ (Icc 0 T) ∧
      ∀ t ∈ Icc 0 T, 0 ≤ σ t ∧ fwdHull U (σ t) = fillH (η '' Icc 0 t) ∧
        IsMapOut (fillH (η '' Icc 0 t)) (fun z => QuantumZipper.fwdMap U (σ t) z + U (σ t)) := by
  apply Sec6.exists_driver_of_drivingCriteria hT hc h0
    (Sec6.hasSimpleApproxOn_of_injOn hT hc hi h0 hHb) (drivingCriterionA_of_open_simple hc hi h0 hH)
  apply Sec6.drivingCriterionB_of_injOn hi
  have he : {u ∈ Ioo 0 T | (η u).im = 0} = ∅ := by
    apply eq_empty_iff_forall_notMem.2
    intro u hu
    exact (ne_of_gt (hH hu.1)) hu.2
  rw [he, interior_empty]

/-- The endpoint-updated capacity trace. -/
def closedKTrace (γ : ℝ → ℂ) (P : Set ℝ) (τ : ℝ≥0) (x : ℝ) : ℝ → ℂ :=
  Function.update (fun t : ℝ => kTrace γ P t.toNNReal) τ (x : ℂ)

theorem closedKTrace_of_lt {γ : ℝ → ℂ} {P : Set ℝ} {τ : ℝ≥0} {x t : ℝ} (ht : t < τ) :
    closedKTrace γ P τ x t = kTrace γ P t.toNNReal :=
  Function.update_of_ne ht.ne _ _

theorem closedKTrace_end (γ : ℝ → ℂ) (P : Set ℝ) (τ : ℝ≥0) (x : ℝ) :
    closedKTrace γ P τ x τ = x := Function.update_self ..

/-- Local generating traces give continuity throughout the open lifetime. -/
theorem continuousOn_kTrace_lt {γ : ℝ → ℂ} {P : Set ℝ} (hγ : IsKilledArc γ P)
    {τ : ℝ≥0} (hτ : (τ : WithTop ℝ≥0) = kLife γ P) : ContinuousOn (kTrace γ P) (Iio τ) := by
  intro t ht
  obtain ⟨r, htr, hrτ⟩ := exists_between (show t < τ from ht)
  have hrL : (r : WithTop ℝ≥0) < kLife γ P := by rw [← hτ]; exact_mod_cast hrτ
  have hc : ContinuousOn (kTrace γ P) (Iic r) :=
    (hγ.isGeneratingTraceIcc_kTrace hrL).1.2.1.mono fun s hs => ENNReal.coe_le_coe.2 hs
  exact (hc.continuousAt (Iic_mem_nhds htr)).continuousWithinAt

/-- Closing at a positive real limit preserves simplicity and supplies all
compact-arc hypotheses of the driving criterion. -/
theorem closedKTrace_spec {γ : ℝ → ℂ} {P : Set ℝ} (hγ : IsKilledArc γ P)
    {τ : ℝ≥0} (hτ0 : 0 < τ) (hτ : (τ : WithTop ℝ≥0) = kLife γ P) {x : ℝ}
    (hx : 0 < x) (hlim : Tendsto (kTrace γ P) (𝓝[<] τ) (𝓝 (x : ℂ))) :
    ContinuousOn (closedKTrace γ P τ x) (Icc 0 τ) ∧
      InjOn (closedKTrace γ P τ x) (Icc 0 τ) ∧ closedKTrace γ P τ x 0 = 0 ∧
      MapsTo (closedKTrace γ P τ x) (Ioo 0 τ) H ∧
      MapsTo (closedKTrace γ P τ x) (Icc 0 τ) Hbar := by
  have hτR : (0 : ℝ) < τ := NNReal.coe_pos.2 hτ0
  have hlt : ∀ t ∈ Ico (0 : ℝ) τ, (t.toNNReal : WithTop ℝ≥0) < kLife γ P := by
    intro t ht
    rw [← hτ, WithTop.coe_lt_coe, Real.toNNReal_lt_iff_lt_coe ht.1]
    exact ht.2
  have hzero : kTrace γ P 0 = 0 :=
    (hγ.isGeneratingTraceIcc_kTrace (by rw [← hτ]; exact_mod_cast hτ0)).1.1
  have hηzero : closedKTrace γ P τ x 0 = 0 := by
    rw [closedKTrace_of_lt hτR, Real.toNNReal_zero, hzero]
  have hηH : MapsTo (closedKTrace γ P τ x) (Ioo 0 τ) H := by
    intro t ht
    rw [closedKTrace_of_lt ht.2]
    exact hγ.kTrace_mem_H (Real.toNNReal_pos.2 ht.1) (hlt t ⟨ht.1.le, ht.2⟩)
  have hηne : ∀ t ∈ Ico (0 : ℝ) τ, closedKTrace γ P τ x t ≠ (x : ℂ) := by
    intro t ht
    rcases ht.1.eq_or_lt with he | hp
    · subst t
      rw [hηzero]
      exact_mod_cast hx.ne
    · intro he
      have him := hηH ⟨hp, ht.2⟩
      rw [he] at him
      exact lt_irrefl _ (show (0 : ℝ) < (x : ℂ).im from him)
  have hcont : ContinuousOn (closedKTrace γ P τ x) (Icc 0 τ) := by
    apply continuousOn_update_iff.2
    rw [Icc_sdiff_right]
    refine ⟨(continuousOn_kTrace_lt hγ hτ).comp continuous_real_toNNReal.continuousOn ?_, ?_⟩
    · intro t ht
      change t.toNNReal < τ
      rw [Real.toNNReal_lt_iff_lt_coe ht.1]
      exact ht.2
    · intro _
      have hto : Tendsto (fun t : ℝ => t.toNNReal) (𝓝[<] (τ : ℝ)) (𝓝[<] τ) := by
        refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
        · simpa only [Real.toNNReal_coe] using
            (continuous_real_toNNReal.tendsto (τ : ℝ)).mono_left nhdsWithin_le_nhds
        · filter_upwards [Ioo_mem_nhdsLT hτR] with t ht
          exact (Real.toNNReal_lt_iff_lt_coe ht.1.le).2 ht.2
      exact (hlim.comp hto).mono_left (nhdsWithin_mono _ Ico_subset_Iio_self)
  refine ⟨hcont, ?_, hηzero, hηH, ?_⟩
  · intro a ha b hb he
    rcases ha.2.lt_or_eq with hat | hat
    · rcases hb.2.lt_or_eq with hbt | hbt
      · have hab := hγ.kTrace_injOn (hlt a ⟨ha.1, hat⟩) (hlt b ⟨hb.1, hbt⟩)
          (by simpa only [closedKTrace_of_lt hat, closedKTrace_of_lt hbt] using he)
        have := congrArg (fun r : ℝ≥0 => (r : ℝ)) hab
        simpa only [Real.coe_toNNReal _ ha.1, Real.coe_toNNReal _ hb.1] using this
      · subst b
        exact False.elim (hηne a ⟨ha.1, hat⟩ (by simpa only [closedKTrace_end] using he))
    · subst a
      rcases hb.2.lt_or_eq with hbt | hbt
      · exact False.elim (hηne b ⟨hb.1, hbt⟩ (by simpa only [closedKTrace_end] using he.symm))
      · exact hbt.symm
  · intro t ht
    rcases ht.2.lt_or_eq with hlt | he
    · rcases ht.1.eq_or_lt with hz | hp
      · subst t
        rw [hηzero]
        exact (show (0 : ℝ) ≤ (0 : ℂ).im from le_refl _)
      · exact (show (0 : ℝ) < (closedKTrace γ P τ x t).im from hηH ⟨hp, hlt⟩).le
    · subst t
      rw [closedKTrace_end]
      exact (show (0 : ℝ) ≤ (x : ℂ).im from le_refl _)

/-- Before the horizon, updating the endpoint preserves every filled hull. -/
theorem fwdHull_kPath_closedKTrace {γ : ℝ → ℂ} {P : Set ℝ} (hγ : IsKilledArc γ P)
    {τ : ℝ≥0} (hτ : (τ : WithTop ℝ≥0) = kLife γ P) {x t : ℝ} (ht0 : 0 ≤ t) (htτ : t < τ) :
    fwdHull (kPath γ P) t = fillH (closedKTrace γ P τ x '' Icc 0 t) := by
  have htL : (t.toNNReal : WithTop ℝ≥0) < kLife γ P := by
    rw [← hτ, WithTop.coe_lt_coe, Real.toNNReal_lt_iff_lt_coe ht0]
    exact htτ
  have hg := hγ.isGeneratingTraceIcc_kTrace htL
  have hC : IsCompact (kTrace γ P '' Icc 0 t.toNNReal) :=
    isCompact_Icc.image_of_continuousOn (hg.1.2.1.mono fun r hr => ENNReal.coe_le_coe.2 hr.2)
  have he := (fillH_eq_iff_isFilling_of_isClosed hC.isBounded hC.isClosed
    ((QuantumZipper.fwdHull_mono).2 _)).1 hg.2.1
  rw [Real.coe_toNNReal _ ht0, ← image_toNNReal_Icc (kTrace γ P) ht0] at he
  refine he.trans (congrArg fillH ?_)
  exact image_congr fun r hr => (closedKTrace_of_lt (hr.2.trans_lt htτ)).symm

/-- The original capacity clock fixes the capacity of every closed-trace prefix. -/
theorem hcapSet_closedKTrace {γ : ℝ → ℂ} {P : Set ℝ} (hγ : IsKilledArc γ P)
    {τ : ℝ≥0} (hτ : (τ : WithTop ℝ≥0) = kLife γ P) {x t : ℝ} (ht0 : 0 ≤ t) (htτ : t < τ) :
    ConformalImage.hcapSet (fillH (closedKTrace γ P τ x '' Icc 0 t)) = 2 * t := by
  have htL : (t.toNNReal : WithTop ℝ≥0) < kLife γ P := by
    rw [← hτ, WithTop.coe_lt_coe, Real.toNNReal_lt_iff_lt_coe ht0]
    exact htτ
  obtain ⟨S, -, -, htS, w, hw, hw0, hEq, -⟩ := hγ.exists_kPath_trace htL
  rw [Real.coe_toNNReal _ ht0] at htS
  apply Sec7.Lemma71.hcapSet_eq_of_fwdHull_eq hw hw0 ht0
  exact (LocalExt.fwdHull_congr_of_eqOn_of_lt ht0 htS hEq.symm).trans
    (fwdHull_kPath_closedKTrace hγ hτ ht0 htτ)

/-- The killed capacity driver has a continuous extension through a positive
real landing, proved from the closed arc and the landed driving criterion. -/
theorem exists_closed_driver {γ : ℝ → ℂ} {P : Set ℝ} (hγ : IsKilledArc γ P)
    {τ : ℝ≥0} (hτ0 : 0 < τ) (hτ : (τ : WithTop ℝ≥0) = kLife γ P) {x : ℝ}
    (hx : 0 < x) (hlim : Tendsto (kTrace γ P) (𝓝[<] τ) (𝓝 (x : ℂ))) :
    ∃ U : ℝ → ℝ, Continuous U ∧ U 0 = 0 ∧ EqOn (kPath γ P) U (Ico 0 τ) ∧
      IsLoewnerTraceLT U τ (closedKTrace γ P τ x) := by
  obtain ⟨hc, hi, h0, hH, hHb⟩ := closedKTrace_spec hγ hτ0 hτ hx hlim
  obtain ⟨U, hU, hU0, σ, -, -, -, hσ⟩ :=
    exists_driver_of_open_simple (NNReal.coe_pos.2 hτ0) hc hi h0 hH hHb
  have hσid : ∀ t ∈ Ico (0 : ℝ) τ, σ t = t := by
    intro t ht
    have he := Sec7.Lemma71.hcapSet_eq_of_fwdHull_eq hU hU0 (hσ t ⟨ht.1, ht.2.le⟩).1
      (hσ t ⟨ht.1, ht.2.le⟩).2.1
    have he' := hcapSet_closedKTrace hγ hτ (x := x) ht.1 ht.2
    linarith only [he, he']
  have hLT : IsLoewnerTraceLT U τ (closedKTrace γ P τ x) := by
    refine ⟨h0, hc.mono Ico_subset_Icc_self, fun t ht0 htτ => ?_⟩
    simpa only [hσid t ⟨ht0, htτ⟩] using (hσ t ⟨ht0, htτ.le⟩).2.1
  refine ⟨U, hU, hU0, ?_, hLT⟩
  intro r hr
  obtain ⟨R, hrR, hRτ⟩ := exists_between hr.2
  have hR0 : 0 ≤ R := hr.1.trans hrR.le
  have hRL : (R.toNNReal : WithTop ℝ≥0) < kLife γ P := by
    rw [← hτ, WithTop.coe_lt_coe, Real.toNNReal_lt_iff_lt_coe hR0]
    exact hRτ
  obtain ⟨S, -, -, hRS, w, hw, hw0, hEq, -⟩ := hγ.exists_kPath_trace hRL
  rw [Real.coe_toNNReal _ hR0] at hRS
  have hew : EqOn w U (Icc 0 R) := Sec6.eqOn_of_fwdHull_eq hw hU hw0 hU0 hR0 fun t ht => by
    exact (LocalExt.fwdHull_congr_of_eqOn_of_lt ht.1 (ht.2.trans_lt hRS) hEq.symm).trans
      ((fwdHull_kPath_closedKTrace hγ hτ (x := x) ht.1 (ht.2.trans_lt hRτ)).trans
        (hLT.2.2 t ht.1 (ht.2.trans_lt hRτ)).symm)
  exact (hEq ⟨hr.1, hrR.le.trans hRS.le⟩).trans (hew ⟨hr.1, hrR.le⟩)

end InteractingSLE.WangWu.SeedTail
