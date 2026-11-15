/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.Assembly2Cont
import InteractingSLE.Spec.Sec2.JacobiExists

/-!
# Theorem 2.2, existence for the admissible entrances

Packet PROVE-SEC2-PATCH3. An ordered force word with marks at the driver on both sides (seed groups
of total weights `> −2`) has an integrated `SLE_a(ρ)` evolution
(`exists_isIntegratedSLEEvolution_of_entrance`), so every ordered word has one
(`exists_isIntegratedSLEEvolution_all`, the frozen conclusion of Theorem 2.2's existence):

* the reference: the two-seed evolution (PROVE-SEC2-JAC3, `Sec2.exists_isIntegratedSLEEvolution_twoSeed`)
  with the seed weights, which lives forever (no threshold state exists), modified on a null set to
  have every path continuous, its two marks split into the seed groups;
* the other marks are added by Girsanov up to the first time `τ' ≤ 2` one of them comes within `δ/2`
  of the driver (`IsSLEEvolutionUpTo.exists_addMarks`);
* at the earlier positive stopping time `T ≤ 1` (within `δ`), the word seen from the driver is good
  (the seeds have separated, `IsSLEPathUpTo.vL_lt_vR_of_pos`), and the evolution is continued by the
  maximal solution (`isIntegratedSLEEvolution_cont`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec2

namespace IsSLEPathUpTo

variable {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin nR → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ}
  {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-- **Separation at positive times.** For an ordered force word, at every time `0 < t < ζ` every
left mark is strictly to the left of every right mark. -/
theorem vL_lt_vR_of_pos (h : IsSLEPathUpTo a xL xR ρL ρR w vL vR b ζ)
    (hF : IsOrderedForceWord xL xR) {t : ℝ≥0} (ht0 : 0 < t) (ht : (t : ℝ≥0∞) < ζ) (i : Fin nL)
    (j : Fin nR) : vL i t < vR j t := by
  have hp := h
  have hnL : 0 < nL := Fin.pos i
  have hnR : 0 < nR := Fin.pos j
  set p : Fin nL := ⟨0, hnL⟩
  set q : Fin nR := ⟨0, hnR⟩
  have hip : vL i t ≤ vL p t := hp.antitone_vL ht (show p ≤ i from Nat.zero_le _)
  have hqj : vR q t ≤ vR j t := hp.monotone_vR ht (show q ≤ j from Nat.zero_le _)
  suffices hpq : vL p t < vR q t by linarith
  -- `V^{q,R} − W > 0` almost everywhere on `[0, t]`, so its force integral is positive
  have hf : IntervalIntegrable (fun s : ℝ => 2 / (vR q s.toNNReal - w s.toNNReal)) volume 0 t := by
    simpa only [two_div_sub_eq] using (hp.integrable_gapR ht q).const_mul (-2)
  have hg : IntervalIntegrable (fun s : ℝ => 2 / (vL p s.toNNReal - w s.toNNReal)) volume 0 t := by
    simpa only [two_div_sub_eq] using (hp.integrable_gapL ht p).const_mul (-2)
  have hnn : ∀ s : ℝ, s ∈ Icc (0 : ℝ) t → 0 ≤ 2 / (vR q s.toNNReal - w s.toNNReal) := by
    intro s hs
    have hst : ((s.toNNReal : ℝ≥0) : ℝ≥0∞) < ζ := lt_of_le_of_lt
      (by exact_mod_cast Real.toNNReal_le_iff_le_coe.2 hs.2) ht
    exact div_nonneg zero_le_two (sub_nonneg.2 (hp.w_le_vR hst q))
  have hnn' : ∀ s : ℝ, s ∈ Icc (0 : ℝ) t → 2 / (vL p s.toNNReal - w s.toNNReal) ≤ 0 := by
    intro s hs
    have hst : ((s.toNNReal : ℝ≥0) : ℝ≥0∞) < ζ := lt_of_le_of_lt
      (by exact_mod_cast Real.toNNReal_le_iff_le_coe.2 hs.2) ht
    exact div_nonpos_of_nonneg_of_nonpos zero_le_two (sub_nonpos.2 (hp.vL_le_w hst p))
  have hpos : 0 < ∫ s in (0 : ℝ)..t, 2 / (vR q s.toNNReal - w s.toNNReal) := by
    rw [intervalIntegral.integral_pos_iff_support_of_nonneg_ae' _ hf]
    · refine ⟨by exact_mod_cast ht0, ?_⟩
      -- the support contains `(0, t]` minus the null collision set
      have hnull := hp.volume_collisionR q
      have hsub : Ioc (0 : ℝ) t \ {s : ℝ | 0 ≤ s ∧ (s.toNNReal : ℝ≥0∞) < ζ ∧
          w s.toNNReal = vR q s.toNNReal} ⊆
          Function.support (fun s : ℝ => 2 / (vR q s.toNNReal - w s.toNNReal)) ∩ Ioc 0 t := by
        rintro s ⟨hs, hsn⟩
        refine ⟨?_, hs⟩
        have hst : ((s.toNNReal : ℝ≥0) : ℝ≥0∞) < ζ := lt_of_le_of_lt
          (by exact_mod_cast Real.toNNReal_le_iff_le_coe.2 hs.2) ht
        have hne : w s.toNNReal ≠ vR q s.toNNReal := fun he => hsn ⟨hs.1.le, hst, he⟩
        have hle := hp.w_le_vR hst q
        have : 0 < vR q s.toNNReal - w s.toNNReal := sub_pos.2 (lt_of_le_of_ne hle hne)
        exact (div_pos two_pos this).ne'
      refine lt_of_lt_of_le ?_ (measure_mono hsub)
      rw [measure_sdiff_null hnull, Real.volume_Ioc, sub_zero, ENNReal.ofReal_pos]
      exact_mod_cast ht0
    · rw [uIoc_of_le (NNReal.coe_nonneg t)]
      exact (ae_restrict_iff' measurableSet_Ioc).2
        (Eventually.of_forall fun s hs => hnn s (Ioc_subset_Icc_self hs))
  have hneg : ∫ s in (0 : ℝ)..t, 2 / (vL p s.toNNReal - w s.toNNReal) ≤ 0 :=
    by
      have := intervalIntegral.integral_mono_on (NNReal.coe_nonneg t) hg
        (intervalIntegrable_const (c := (0 : ℝ))) hnn'
      simpa only [intervalIntegral.integral_const, smul_zero] using this
  rw [hp.vL_eq ht p, hp.vR_eq ht q]
  have := hF.2.1 p
  have := hF.2.2.2 q
  linarith

end IsSLEPathUpTo

namespace Assembly2

open Assembly

variable {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin nR → ℝ}

/-- **A modification of an evolution that lives forever** with every path continuous (driver,
marks and Brownian motion), as a local evolution with horizon `∞` in a right-continuous filtration. -/
theorem exists_continuous_modification_top {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hE : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) :
    ∃ (𝓖 : Filtration ℝ≥0 mΩ) (_ : 𝓖.IsRightContinuous) (W' : ℝ≥0 → Ω → ℝ)
      (VL' : Fin nL → ℝ≥0 → Ω → ℝ) (VR' : Fin nR → ℝ≥0 → Ω → ℝ) (B' : ℝ≥0 → Ω → ℝ),
      IsSLEEvolutionUpTo a xL xR ρL ρR P 𝓖 W' VL' VR' B' (fun _ => ⊤) ∧
      (∀ ω, Continuous (W' · ω)) ∧ (∀ i ω, Continuous (VL' i · ω)) ∧
      (∀ j ω, Continuous (VR' j · ω)) ∧ (∀ ω, Continuous (B' · ω)) ∧ ∀ ω, W' 0 ω = 0 := by
  classical
  have hgood : ∀ᵐ ω ∂P, (ζ ω = ⊤ ∧ IsIntegratedSLEPath a xL xR ρL ρR (W · ω)
      (fun i t => VL i t ω) (fun j t => VR j t ω) (B · ω) (ζ ω)) ∧ Continuous (B · ω) :=
    (hζ.and hE.2.2.2.2).and hE.1.1.cont
  obtain ⟨N, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 hgood)
  have hgoodω : ∀ ω, ω ∉ N → (ζ ω = ⊤ ∧ IsIntegratedSLEPath a xL xR ρL ρR (W · ω)
      (fun i t => VL i t ω) (fun j t => VR j t ω) (B · ω) (ζ ω)) ∧ Continuous (B · ω) :=
    fun ω hω => by
      by_contra hc
      exact hω (hNsub hc)
  obtain ⟨hB', hB'c⟩ := Ito.isFilteredBrownianReal_modify hE.1 hNm.compl (by simpa using hN0)
    fun ω hω => (hgoodω ω hω).2
  set 𝓖 := usualAugmentation (Ito.nullAugmented 𝓕 P) P with h𝓖
  have h𝓤 : usualAugmentation 𝓕 P ≤ 𝓖 :=
    Ito.usualAugmentation_mono (Ito.le_nullAugmented 𝓕 P) P
  have hNt : ∀ t, MeasurableSet[usualAugmentation 𝓕 P t] N := fun t =>
    Ito.measurableSet_usualAugmentation_of_null hNm hN0 t
  have hadapt : ∀ {X : ℝ≥0 → Ω → ℝ}, AdaptedBefore 𝓕 ζ X → ∀ c : ℝ,
      AdaptedBefore 𝓖 (fun _ => ⊤) (fun t ω => if ω ∈ N then c else X t ω) :=
    fun {X} hX c t A hA => by
      have e : {ω | (t : ℝ≥0∞) < ⊤ ∧ (if ω ∈ N then c else X t ω) ∈ A} =
          ({ω | (t : ℝ≥0∞) < ζ ω ∧ X t ω ∈ A} ∩ Nᶜ) ∪ (N ∩ {_ω | c ∈ A}) := by
        ext ω
        by_cases hω : ω ∈ N
        · simp [hω]
        · have := (hgoodω ω hω).1.1
          simp [hω, this]
      rw [e]
      exact h𝓤 t _ ((((Ito.le_usualAugmentation 𝓕 P t) _ (hX t A hA)).inter (hNt t).compl).union
        ((hNt t).inter (MeasurableSet.const _)))
  refine ⟨𝓖, inferInstance, fun t ω => if ω ∈ N then 0 else W t ω,
    fun i t ω => if ω ∈ N then xL i else VL i t ω,
    fun j t ω => if ω ∈ N then xR j else VR j t ω,
    fun t ω => @ite ℝ (ω ∈ Nᶜ) (Classical.propDecidable (ω ∈ Nᶜ)) (B t ω) 0,
    ⟨Ito.isFilteredBrownianReal_usualAugmentation hB', hadapt hE.2.1 0,
      fun i => hadapt (hE.2.2.1 i) (xL i), fun j => hadapt (hE.2.2.2.1 j) (xR j), ?_⟩,
    fun ω => ?_, fun i ω => ?_, fun j ω => ?_, hB'c, fun ω => ?_⟩
  · filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN0] with ω hω
    obtain ⟨⟨hζω, hp⟩, -⟩ := hgoodω ω hω
    have hω' : ω ∈ Nᶜ := hω
    simp only [hω, hω', ↓reduceIte]
    rw [hζω] at hp
    exact hp.isSLEPathUpTo le_rfl
  rotate_right
  · by_cases hω : ω ∈ N
    · simp only [hω, ↓reduceIte]
    · obtain ⟨⟨-, hp⟩, -⟩ := hgoodω ω hω
      simp only [hω, ↓reduceIte]
      exact hp.isForcePath.w_zero
  all_goals
    by_cases hω : ω ∈ N
    · simp only [hω, ↓reduceIte]; exact continuous_const
    · obtain ⟨⟨hζω, hp⟩, -⟩ := hgoodω ω hω
      rw [hζω] at hp
      simp only [hω, ↓reduceIte]
      first
        | exact continuousOn_univ.1 (by simpa using (hp.isSLEPathUpTo le_rfl).continuousOn_w)
        | exact continuousOn_univ.1 (by simpa using (hp.isSLEPathUpTo le_rfl).continuousOn_vL i)
        | exact continuousOn_univ.1 (by simpa using (hp.isSLEPathUpTo le_rfl).continuousOn_vR j)

/-! ### The two-seed reference -/

/-- Two seeds with weights `> −2` never satisfy the threshold condition. -/
theorem not_thr_twoSeed {ρL ρR : Fin 1 → ℝ} (hL : -2 < ρL 0) (hR : -2 < ρR 0) (w : ℝ)
    (vL vR : Fin 1 → ℝ) : ¬ ForceWord.ThresholdCondition ρL ρR w vL vR := by
  unfold ForceWord.ThresholdCondition
  rw [Finset.sum_filter, Finset.sum_filter, Fin.sum_univ_one, Fin.sum_univ_one]
  rintro (h | h) <;> split_ifs at h <;> linarith

/-- **The two-seed evolution with weights `> −2` lives forever.** -/
theorem ae_lifetime_eq_top_twoSeed {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ} {xL xR ρL ρR : Fin 1 → ℝ}
    {W : ℝ≥0 → Ω → ℝ} {VL VR : Fin 1 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (ha : 0 < a) (hE : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (hL : -2 < ρL 0) (hR : -2 < ρR 0) : ∀ᵐ ω ∂P, ζ ω = ⊤ := by
  filter_upwards [hE.2.2.2.2, hE.ae_tendsto_threshold ha] with ω hp hlim
  by_contra hne
  rcases eq_or_ne (ζ ω) 0 with h0 | h0
  · exact not_thr_twoSeed hL hR _ _ _ (hp.isForcePath.threshold_of_eq_zero h0)
  · have hT : (((ζ ω).toNNReal : ℝ≥0) : ℝ≥0∞) = ζ ω := ENNReal.coe_toNNReal hne
    have hT0 : 0 < (ζ ω).toNNReal := by
      have : (0 : ℝ≥0∞) < (ζ ω).toNNReal := by rw [hT]; exact pos_iff_ne_zero.2 h0
      exact_mod_cast this
    obtain ⟨w₀, vL₀, vR₀, -, hthr⟩ := hlim _ hT0 hT
    exact not_thr_twoSeed hL hR _ _ _ hthr

/-- **The reference for an entrance**: the two-seed evolution with weights `ρa, ρb > −2`, living
forever, with every path continuous, its seeds split into groups of weights `ρmL`, `ρmR`. -/
theorem exists_reference_twoSeed (ha : 0 < a) {ρa ρb : ℝ} (hρa : -2 < ρa) (hρb : -2 < ρb)
    {kL kR : ℕ} {ρmL : Fin kL → ℝ} {ρmR : Fin kR → ℝ} (hsumL : ρa = ∑ j, ρmL j)
    (hsumR : ρb = ∑ j, ρmR j) :
    ∃ (Ω : Type) (mΩ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (𝓕 : Filtration ℝ≥0 mΩ) (_ : 𝓕.IsRightContinuous) (W : ℝ≥0 → Ω → ℝ)
      (VL : Fin kL → ℝ≥0 → Ω → ℝ) (VR : Fin kR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ),
      IsSLEEvolutionUpTo a (fun _ => 0) (fun _ => 0) ρmL ρmR P 𝓕 W VL VR B (fun _ => ⊤) ∧
      (∀ ω, Continuous (W · ω)) ∧ (∀ i ω, Continuous (VL i · ω)) ∧
      (∀ j ω, Continuous (VR j · ω)) ∧ (∀ ω, Continuous (B · ω)) ∧ ∀ ω, W 0 ω = 0 := by
  obtain ⟨Ω, mΩ, P, hP, 𝓕, W, VL, VR, B, ζ, hE⟩ := exists_isIntegratedSLEEvolution_twoSeed ha
    (xL := fun _ : Fin 1 => 0) (xR := fun _ => 0) (fun _ => rfl) (fun _ => rfl) (fun _ => ρa)
    (fun _ => ρb)
  have hζ := ae_lifetime_eq_top_twoSeed ha hE hρa hρb
  obtain ⟨𝓖, h𝓖, W', VL', VR', B', hE', hWc, hVLc, hVRc, hBc, hW0⟩ :=
    exists_continuous_modification_top hE hζ
  have eL : VL' = fun _ => VL' 0 := funext fun i => by rw [Subsingleton.elim i 0]
  have eR : VR' = fun _ => VR' 0 := funext fun i => by rw [Subsingleton.elim i 0]
  rw [eR] at hE'
  have h1 := IsSLEEvolutionUpTo.splitR (ρ1 := fun _ => ρb) (ρm := ρmR) hsumR hE'
  rw [eL] at h1
  have h2 := IsSLEEvolutionUpTo.splitL (ρ1 := fun _ => ρa) (ρm := ρmL) hsumL h1
  exact ⟨Ω, mΩ, P, hP, 𝓖, h𝓖, W', fun _ => VL' 0, fun _ => VR' 0, B', h2, hWc,
    fun _ => hVLc 0, fun _ => hVRc 0, hBc, hW0⟩

/-! ### Existence for every ordered word -/

/-- Hitting a lower level takes longer. -/
theorem hitTime_mono {Ω : Type*} {K : Type*} {Y : K → ℝ≥0 → Ω → ℝ} {δ₁ δ₂ : ℝ} (h : δ₂ ≤ δ₁)
    (ω : Ω) : hitTime Y δ₁ ω ≤ hitTime Y δ₂ ω :=
  le_iInf₂ fun t ⟨k, hk⟩ =>
    iInf₂_le (f := fun (t : ℝ≥0) (_ : ∃ k, Y k t ω ≤ δ₁) => (t : ℝ≥0∞)) t ⟨k, hk.trans h⟩

/-- Hitting a lower level takes strictly longer. -/
theorem hitTime_lt_hitTime {Ω : Type*} {K : Type*} [Finite K] {Y : K → ℝ≥0 → Ω → ℝ}
    {δ₁ δ₂ : ℝ} (hδ : δ₂ < δ₁) {ω : Ω} (hc : ∀ k, Continuous (Y k · ω))
    (h0 : ∀ k, δ₁ < Y k 0 ω) (hfin : hitTime Y δ₁ ω ≠ ⊤) : hitTime Y δ₁ ω < hitTime Y δ₂ ω := by
  by_contra hcon
  rw [not_lt] at hcon
  have hpos := hitTime_pos hc h0
  have h₂fin : hitTime Y δ₂ ω ≠ ⊤ := ne_top_of_le_ne_top hfin hcon
  have hs : hitTime Y δ₂ ω ≤ ((hitTime Y δ₂ ω).toNNReal : ℝ≥0∞) :=
    (ENNReal.coe_toNNReal h₂fin).ge
  obtain ⟨t, hts, k, hk⟩ := (hitTime_le_iff (δ := δ₂) hc).1 hs
  have ht₂ : (t : ℝ≥0∞) ≤ hitTime Y δ₂ ω := by
    rw [← ENNReal.coe_toNNReal h₂fin]; exact_mod_cast hts
  rcases lt_or_ge (t : ℝ≥0∞) (hitTime Y δ₁ ω) with hlt | hge
  · exact absurd (lt_of_le_of_lt hk hδ) (not_lt.2 (lt_of_lt_hitTime hlt k).le)
  · have heq : (t : ℝ≥0∞) = hitTime Y δ₁ ω := le_antisymm (ht₂.trans hcon) hge
    have ht0 : 0 < t := by
      have : (0 : ℝ≥0∞) < t := by rw [heq]; exact hpos
      exact_mod_cast this
    have : NeBot (𝓝[<] t) := nhdsLT_neBot_of_exists_lt ⟨0, ht0⟩
    have hge' : δ₁ ≤ Y k t ω := by
      refine ge_of_tendsto ((((hc k).continuousAt).tendsto.mono_left nhdsWithin_le_nhds :
        Tendsto (Y k · ω) (𝓝[<] t) (𝓝 (Y k t ω)))) ?_
      filter_upwards [self_mem_nhdsWithin] with u hu
      have hu' : (u : ℝ≥0∞) < hitTime Y δ₁ ω := by rw [← heq]; exact_mod_cast hu
      exact (lt_of_lt_hitTime hu' k).le
    linarith

/-- **Theorem 2.2, existence, for every ordered force word that is not a threshold seed** (in
particular for the admissible entrances): the two-seed reference with the seed groups, the other
marks added by Girsanov, and the continuation by the maximal solution. -/
theorem exists_isIntegratedSLEEvolution_of_not_threshold (ha : 0 < a)
    (hF : IsOrderedForceWord xL xR) (hthr : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR) :
    ∃ (Ω : Type) (mΩ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
      (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
      IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ := by
  classical
  have hnt := hthr
  unfold ForceWord.ThresholdCondition at hnt
  rw [not_or, not_le, not_le] at hnt
  obtain ⟨kL, eL, heL, hcL, hsL⟩ := exists_enum_zero xL
  obtain ⟨kR, eR, heR, hcR, hsR⟩ := exists_enum_zero xR
  obtain ⟨Ω, mΩ, P₀, hP₀, 𝓤, hRC, W, VLr, VRr, B, hE, hWc, hVLrc, hVRrc, hBc, hW0⟩ :=
    exists_reference_twoSeed ha (ρa := ∑ j, ρL (eL j)) (ρb := ∑ j, ρR (eR j))
      (by rw [hsL]; exact hnt.1) (by rw [hsR]; exact hnt.2) (ρmL := fun j => ρL (eL j))
      (ρmR := fun j => ρR (eR j)) rfl rfl
  have e1 : (fun j => xL (eL j)) = fun _ => (0 : ℝ) := funext fun j => (hcL (eL j)).1 ⟨j, rfl⟩
  have e2 : (fun j => xR (eR j)) = fun _ => (0 : ℝ) := funext fun j => (hcR (eR j)).1 ⟨j, rfl⟩
  rw [← e1, ← e2] at hE
  have hWa : ∀ t, Measurable[𝓤 t] (W t) := fun t A hA => by
    have := hE.adapted_W t A hA
    simp only [ENNReal.coe_lt_top, true_and] at this
    exact this
  have hmark : ∀ {X : ℝ≥0 → Ω → ℝ}, AdaptedBefore 𝓤 (fun _ => ⊤) X → ∀ t,
      Measurable[𝓤 t] (X t) := fun {X} hX t A hA => by
    have := hX t A hA
    simp only [ENNReal.coe_lt_top, true_and] at this
    exact this
  -- the gap level
  set f : Fin nL ⊕ Fin nR → ℝ := Sum.elim (fun i => if xL i = 0 then 1 else -xL i)
    (fun j => if xR j = 0 then 1 else xR j) with hf
  have hfpos : ∀ k, 0 < f k := by
    rintro (i | j)
    · simp only [hf, Sum.elim_inl]
      split_ifs with h
      · exact one_pos
      · exact neg_pos.2 (lt_of_le_of_ne (hF.2.1 i) h)
    · simp only [hf, Sum.elim_inr]
      split_ifs with h
      · exact one_pos
      · exact lt_of_le_of_ne (hF.2.2.2 j) (Ne.symm h)
  obtain ⟨δ, hδ, hδf⟩ := exists_pos_forall_lt f hfpos
  have hδ' : 0 < δ / 2 := half_pos hδ
  -- the gaps of the added marks
  set Y : Fin nL ⊕ Fin nR → ℝ≥0 → Ω → ℝ := Sum.elim
    (fun i t ω => if xL i = 0 then δ + 1 else W t ω - leftMark (δ / 2) (xL i) (fun _ => ⊤) W t ω)
    (fun j t ω => if xR j = 0 then δ + 1 else rightMark (δ / 2) (xR j) (fun _ => ⊤) W t ω - W t ω)
    with hY
  have hWc' : ∀ ω, ContinuousOn (fun t => W t ω) {t : ℝ≥0 | (t : ℝ≥0∞) < (fun _ => ⊤) ω} :=
    fun ω => (hWc ω).continuousOn
  have huniv : ∀ ω : Ω, {t : ℝ≥0 | (t : ℝ≥0∞) < (fun (_ : Ω) => (⊤ : ℝ≥0∞)) ω} = univ :=
    fun _ => eq_univ_of_forall fun t => ENNReal.coe_lt_top
  have hLc : ∀ (y : ℝ) ω, Continuous fun t => leftMark (δ / 2) y (fun _ => ⊤) W t ω := fun y ω => by
    have := (markFlow_eq_of_continuousOn (W := W) (ζ := fun _ => ⊤) (y := y)
      (lipschitzWith_leftMarkDrift hδ') (abs_leftMarkDrift_le hδ') (hWc' ω)).1
    rw [huniv ω] at this
    exact continuousOn_univ.1 this
  have hRc : ∀ (y : ℝ) ω, Continuous fun t => rightMark (δ / 2) y (fun _ => ⊤) W t ω :=
    fun y ω => by
      have := (markFlow_eq_of_continuousOn (W := W) (ζ := fun _ => ⊤) (y := y)
        (lipschitzWith_rightMarkDrift hδ') (abs_rightMarkDrift_le hδ') (hWc' ω)).1
      rw [huniv ω] at this
      exact continuousOn_univ.1 this
  have hYc : ∀ k ω, Continuous (Y k · ω) := by
    rintro (i | j) ω
    · simp only [hY, Sum.elim_inl]
      split_ifs
      · exact continuous_const
      · exact (hWc ω).sub (hLc _ ω)
    · simp only [hY, Sum.elim_inr]
      split_ifs
      · exact continuous_const
      · exact (hRc _ ω).sub (hWc ω)
  have hYm : ∀ k t, Measurable[𝓤 t] (Y k t) := by
    rintro (i | j) t
    · simp only [hY, Sum.elim_inl]
      split_ifs
      · exact measurable_const
      · exact (hWa t).sub (hmark (adaptedBefore_leftMark hδ' _ hE.adapted_W) t)
    · simp only [hY, Sum.elim_inr]
      split_ifs
      · exact measurable_const
      · exact (hmark (adaptedBefore_rightMark hδ' _ hE.adapted_W) t).sub (hWa t)
  have hY0 : ∀ k ω, δ < Y k 0 ω := by
    rintro (i | j) ω
    · simp only [hY, Sum.elim_inl]
      split_ifs with h
      · linarith
      · rw [hW0 ω, leftMark, markFlow_zero, zero_sub]
        have := hδf (Sum.inl i)
        simpa only [hf, Sum.elim_inl, h, ↓reduceIte] using this
    · simp only [hY, Sum.elim_inr]
      split_ifs with h
      · linarith
      · rw [hW0 ω, rightMark, markFlow_zero, sub_zero]
        have := hδf (Sum.inr j)
        simpa only [hf, Sum.elim_inr, h, ↓reduceIte] using this
  have hY0' : ∀ k ω, δ / 2 < Y k 0 ω := fun k ω => by linarith [hY0 k ω]
  -- the two stopping times
  set τ' : Ω → ℝ≥0∞ := fun ω => min (hitTime Y (δ / 2) ω) ((2 : ℝ≥0) : ℝ≥0∞) with hτ'def
  set T : Ω → ℝ≥0 := fun ω => (min (hitTime Y δ ω) ((1 : ℝ≥0) : ℝ≥0∞)).toNNReal with hTdef
  have hTfin : ∀ ω, min (hitTime Y δ ω) ((1 : ℝ≥0) : ℝ≥0∞) ≠ ⊤ := fun ω =>
    (lt_of_le_of_lt (min_le_right _ _) ENNReal.coe_lt_top).ne
  have hTcoe : ∀ ω, ((T ω : ℝ≥0) : ℝ≥0∞) = min (hitTime Y δ ω) ((1 : ℝ≥0) : ℝ≥0∞) := fun ω =>
    ENNReal.coe_toNNReal (hTfin ω)
  have hτ' : ∀ u : ℝ≥0, MeasurableSet[𝓤 u] {ω | τ' ω ≤ u} := fun u => by
    have e : {ω | τ' ω ≤ u} = {ω | hitTime Y (δ / 2) ω ≤ u} ∪ {_ω | ((2 : ℝ≥0) : ℝ≥0∞) ≤ u} := by
      ext ω; simp only [hτ'def, mem_ofPred_eq, mem_union, min_le_iff]
    rw [e]
    exact (measurableSet_hitTime_le hYm hYc u).union (MeasurableSet.const _)
  have hT : IsStoppingTime 𝓤 fun ω => (T ω : WithTop ℝ≥0) := fun u => by
    have e : {ω | (T ω : WithTop ℝ≥0) ≤ u} =
        {ω | hitTime Y δ ω ≤ u} ∪ {_ω | ((1 : ℝ≥0) : ℝ≥0∞) ≤ u} := by
      ext ω
      simp only [mem_ofPred_eq, mem_union]
      rw [← min_le_iff, ← hTcoe ω]
      exact WithTop.coe_le_coe.trans ENNReal.coe_le_coe.symm
    rw [e]
    exact (measurableSet_hitTime_le hYm hYc u).union (MeasurableSet.const _)
  have hT0 : ∀ ω, 0 < T ω := fun ω => by
    have : (0 : ℝ≥0∞) < T ω := by
      rw [hTcoe ω]; exact lt_min (hitTime_pos (hYc · ω) (hY0 · ω)) (by exact_mod_cast one_pos)
    exact_mod_cast this
  have hTτ' : ∀ ω, (T ω : ℝ≥0∞) < τ' ω := fun ω => by
    rw [hTcoe ω]
    by_cases hfin : hitTime Y δ ω = ⊤
    · rw [hfin, min_eq_right le_top]
      refine lt_min ?_ (by exact_mod_cast (show (1 : ℝ≥0) < 2 by norm_num))
      have := hitTime_mono (Y := Y) (show δ / 2 ≤ δ by linarith) ω
      rw [hfin] at this
      rw [top_le_iff.1 this]; exact ENNReal.coe_lt_top
    · have hlt := hitTime_lt_hitTime (show δ / 2 < δ by linarith) (hYc · ω) (hY0 · ω) hfin
      exact lt_min (lt_of_le_of_lt (min_le_left _ _) hlt) (lt_of_le_of_lt (min_le_right _ _)
        (by exact_mod_cast (show (1 : ℝ≥0) < 2 by norm_num)))
  have hgap : ∀ ω (t : ℝ≥0), (t : ℝ≥0∞) < τ' ω → ∀ k, δ / 2 < Y k t ω := fun ω t ht k =>
    lt_of_lt_hitTime (lt_of_lt_of_le ht (min_le_left _ _)) k
  have hgapL : ∀ᵐ ω ∂P₀, ∀ t : ℝ≥0, (t : ℝ≥0∞) < τ' ω → ∀ i, (∀ j, eL j ≠ i) →
      δ / 2 ≤ W t ω - leftMark (δ / 2) (xL i) (fun _ => ⊤) W t ω := ae_of_all _ fun ω t ht i hi => by
    have hne : xL i ≠ 0 := fun h0 => by
      obtain ⟨j, hj⟩ := (hcL i).2 h0
      exact hi j hj
    have := hgap ω t ht (Sum.inl i)
    simp only [hY, Sum.elim_inl, hne, ↓reduceIte] at this
    exact this.le
  have hgapR : ∀ᵐ ω ∂P₀, ∀ t : ℝ≥0, (t : ℝ≥0∞) < τ' ω → ∀ i, (∀ j, eR j ≠ i) →
      δ / 2 ≤ rightMark (δ / 2) (xR i) (fun _ => ⊤) W t ω - W t ω := ae_of_all _ fun ω t ht i hi => by
    have hne : xR i ≠ 0 := fun h0 => by
      obtain ⟨j, hj⟩ := (hcR i).2 h0
      exact hi j hj
    have := hgap ω t ht (Sum.inr i)
    simp only [hY, Sum.elim_inr, hne, ↓reduceIte] at this
    exact this.le
  -- Girsanov
  obtain ⟨hQ, hEQ⟩ := hE.exists_addMarks ha hF heL heR hδ' hτ' (fun _ => le_top)
    (fun ω => min_le_right _ _) hgapL hgapR
  have hQp := hQ.isProb
  set VLf := fullMarksL eL VLr (δ / 2) xL (fun _ => ⊤) W with hVLf
  set VRf := fullMarksR eR VRr (δ / 2) xR (fun _ => ⊤) W with hVRf
  have hVLe : (fun j => VLf (eL j)) = VLr := funext fun j => heL.extend_apply _ _ j
  have hVRe : (fun j => VRf (eR j)) = VRr := funext fun j => heR.extend_apply _ _ j
  have hVLp : ∀ i, (∀ j, eL j ≠ i) → VLf i = leftMark (δ / 2) (xL i) (fun _ => ⊤) W :=
    fun i hi => Function.extend_apply' _ _ _ fun ⟨j, hj⟩ => hi j hj
  have hVRp : ∀ i, (∀ j, eR j ≠ i) → VRf i = rightMark (δ / 2) (xR i) (fun _ => ⊤) W :=
    fun i hi => Function.extend_apply' _ _ _ fun ⟨j, hj⟩ => hi j hj
  have hE' : IsSLEEvolutionUpTo a (fun j => xL (eL j)) (fun j => xR (eR j)) (fun j => ρL (eL j))
      (fun j => ρR (eR j)) P₀ 𝓤 W (fun j => VLf (eL j)) (fun j => VRf (eR j)) B (fun _ => ⊤) := by
    rw [hVLe, hVRe]; exact hE
  have hM : IsSLEEvolutionUpTo a xL xR (refWeights eL ρL) (refWeights eR ρR) P₀ 𝓤 W VLf VRf B
      τ' := by
    refine hE'.of_passive hF heL heR hδ' (fun i hi => ?_) (fun i hi => ?_) hτ' (fun _ => le_top)
      ?_ ?_
    · rw [hVLp i hi]; exact adaptedBefore_leftMark hδ' _ hE.adapted_W
    · rw [hVRp i hi]; exact adaptedBefore_rightMark hδ' _ hE.adapted_W
    · filter_upwards [hE.ae_path, hgapL] with ω hp hg i hi
      rw [hVLp i hi]
      exact isPassiveLeft_leftMark hδ' hp.continuousOn_w le_top fun t ht => hg t ht i hi
    · filter_upwards [hE.ae_path, hgapR] with ω hp hg i hi
      rw [hVRp i hi]
      exact isPassiveRight_rightMark hδ' hp.continuousOn_w le_top fun t ht => hg t ht i hi
  obtain ⟨hθp, hθb, -⟩ := hM.weightDrift_props ρL ρR hτ' (fun _ => le_rfl) hδ'
  have hB'c : ∀ ω, Continuous fun t => Girsanov.girsanovProcess B (weightDrift a (δ / 2) (refWeights eL ρL)
      ρL (refWeights eR ρR) ρR τ' τ' W VLf VRf) t ω := fun ω =>
    (hBc ω).add (Girsanov.continuous_drift hθp hθb ω)
  have hVLfc : ∀ i ω, Continuous (VLf i · ω) := fun i ω => by
    by_cases h : ∃ j, eL j = i
    · obtain ⟨j, rfl⟩ := h
      rw [show VLf (eL j) = VLr j from congrFun hVLe j]; exact hVLrc j ω
    · rw [hVLp i fun j hj => h ⟨j, hj⟩]; exact hLc _ ω
  have hVRfc : ∀ i ω, Continuous (VRf i · ω) := fun i ω => by
    by_cases h : ∃ j, eR j = i
    · obtain ⟨j, rfl⟩ := h
      rw [show VRf (eR j) = VRr j from congrFun hVRe j]; exact hVRrc j ω
    · rw [hVRp i fun j hj => h ⟨j, hj⟩]; exact hRc _ ω
  have hVLfa : ∀ i t, Measurable[𝓤 t] (VLf i t) := fun i t => by
    by_cases h : ∃ j, eL j = i
    · obtain ⟨j, rfl⟩ := h
      rw [show VLf (eL j) = VLr j from congrFun hVLe j]; exact hmark (hE.adapted_VL j) t
    · rw [hVLp i fun j hj => h ⟨j, hj⟩]
      exact hmark (adaptedBefore_leftMark hδ' _ hE.adapted_W) t
  have hVRfa : ∀ i t, Measurable[𝓤 t] (VRf i t) := fun i t => by
    by_cases h : ∃ j, eR j = i
    · obtain ⟨j, rfl⟩ := h
      rw [show VRf (eR j) = VRr j from congrFun hVRe j]; exact hmark (hE.adapted_VR j) t
    · rw [hVRp i fun j hj => h ⟨j, hj⟩]
      exact hmark (adaptedBefore_rightMark hδ' _ hE.adapted_W) t
  have hgood : ∀ᵐ ω ∂(Girsanov.girsanovMeasure P₀ 𝓤 B (weightDrift a (δ / 2) (refWeights eL ρL) ρL
      (refWeights eR ρR) ρR τ' τ' W VLf VRf) (2 + 1)),
      GoodWord ρL ρR (contWord W VLf VRf T ω) := by
    filter_upwards [hEQ.ae_path] with ω hp
    have hTlt := hTτ' ω
    refine ⟨fun i j => ?_, ⟨fun i j hij => ?_, fun i => ?_, fun i j hij => ?_, fun j => ?_⟩, ?_⟩
    · show VLf i (T ω) ω - W (T ω) ω < VRf j (T ω) ω - W (T ω) ω
      linarith [hp.vL_lt_vR_of_pos hF (hT0 ω) hTlt i j]
    · show VLf j (T ω) ω - W (T ω) ω ≤ VLf i (T ω) ω - W (T ω) ω
      linarith [hp.antitone_vL hTlt hij]
    · show VLf i (T ω) ω - W (T ω) ω ≤ 0
      linarith [hp.vL_le_w hTlt i]
    · show VRf i (T ω) ω - W (T ω) ω ≤ VRf j (T ω) ω - W (T ω) ω
      linarith [hp.monotone_vR hTlt hij]
    · show 0 ≤ VRf j (T ω) ω - W (T ω) ω
      linarith [hp.w_le_vR hTlt j]
    · exact fun h => hp.not_threshold hTlt ((thresholdCondition_sub_self_iff (W (T ω) ω)
        (fun i => VLf i (T ω) ω) (fun j => VRf j (T ω) ω)).1 h)
  exact ⟨Ω, mΩ, _, hQp, 𝓤, _, _, _, _, _, isIntegratedSLEEvolution_cont ha hEQ.brownian hB'c hWa
    hVLfa hVRfa hWc hVLfc hVRfc hEQ.ae_path hT (ae_of_all _ hTτ') hT0 hgood⟩

/-- **Theorem 2.2, existence, for every ordered force word.** -/
theorem exists_isIntegratedSLEEvolution_of_ordered (ha : 0 < a) (hF : IsOrderedForceWord xL xR) :
    ∃ (Ω : Type) (mΩ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
      (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
      IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ := by
  by_cases hthr : ForceWord.ThresholdCondition ρL ρR 0 xL xR
  · exact exists_isIntegratedSLEEvolution_of_threshold hthr
  · exact exists_isIntegratedSLEEvolution_of_not_threshold ha hF hthr

end Assembly2

end Sec2

/-- **Theorem 2.2, existence** (Specification p. 21), in the provider form of the frozen anchor
`exists_isIntegratedSLEEvolution`: every argument implicit, the hypotheses as auto-parameters. -/
theorem exists_isIntegratedSLEEvolution_assembled {a : ℝ} (ha : 0 < a := by assumption)
    {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (hF : IsOrderedForceWord xL xR := by assumption) :
    ∃ (Ω : Type) (mΩ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
      (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
      IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ :=
  Sec2.Assembly2.exists_isIntegratedSLEEvolution_of_ordered ha hF

end InteractingSLE
