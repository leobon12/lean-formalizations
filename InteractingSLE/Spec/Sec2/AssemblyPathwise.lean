/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.AssemblyLocal

/-!
# Theorem 2.2 assembly: pathwise uniqueness of integrated `SLE_a(ρ)` paths

Packet PROVE-SEC2-PATCH. For a force word whose left and right positions are strictly separated
(`∀ i j, xL i < xR j`: no left mark and no right mark both start at `0`, the "entrance" of the
proof of Theorem 2.2), two solutions of Definition 2.1 (the frozen `IsIntegratedSLEPath`, maximal
lifetime included) driven by the **same path `b`** have the same lifetime and coincide before it
(`IsIntegratedSLEPath.eq_of_separated`). Nothing here is probabilistic and `b` is arbitrary.

Argument (continuous induction, added here):

* let `t*` be the first time before `min ζ ζ'` at which the solutions differ; they agree on
  `[0, t*]` (initial values, or continuity from the left);
* at `t*` at most one side touches the driver (left marks are `≤ xL i`, right marks `≥ xR j`,
  and `xL i < xR j`), the group touching it has weight `> −2` (the threshold condition fails
  before `ζ`), and every other mark is at positive distance; by continuity this persists on a
  right neighbourhood, where the local uniqueness lemmas of `AssemblyLocal` give agreement —
  contradicting the choice of `t*`;
* if `ζ' < ζ`, then either `ζ' = 0` (the seed is a threshold state, contradicting
  `not_threshold` of the first solution at time `0`) or the second solution's state converges at
  `ζ'⁻` to the first solution's state at `ζ'`, which must then be a threshold state
  (maximality of `ζ'`), contradicting `not_threshold` of the first solution at `ζ' < ζ`.

This replaces, for separated words, the iterated Girsanov patching of the source's uniqueness
argument (`source/spec/p001-048.md` L490–L494): pathwise uniqueness plus a measurability argument
(`AssemblyUnique`) gives uniqueness in law directly.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec2

namespace Assembly

/-- Finitely many positive numbers have a common positive lower bound. -/
theorem exists_pos_forall_lt {ι : Type*} [Fintype ι] (f : ι → ℝ) (hf : ∀ i, 0 < f i) :
    ∃ ε > 0, ∀ i, ε < f i := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨1, one_pos, fun i => isEmptyElim i⟩
  · set m := Finset.univ.inf' Finset.univ_nonempty f
    have hm : 0 < m := (Finset.lt_inf'_iff _).2 fun i _ => hf i
    refine ⟨m / 2, by positivity, fun i => ?_⟩
    have : m ≤ f i := Finset.inf'_le _ (Finset.mem_univ i)
    linarith

/-- Two coordinates that agree before `t > 0` and are continuous on `[0, t]` agree at `t`. -/
theorem eq_of_eqOn_Iio {f g : ℝ≥0 → ℝ} {t : ℝ≥0} (ht : 0 < t) (hf : ContinuousOn f (Iic t))
    (hg : ContinuousOn g (Iic t)) (h : ∀ s < t, f s = g s) : f t = g t :=
  EqOn.of_subset_closure (s := Iio t) (fun s hs => h s hs) hf hg Iio_subset_Iic_self
    (by rw [closure_Iio' (show (Iio t).Nonempty from ⟨0, ht⟩)]) (mem_Iic.2 le_rfl)

variable {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin nR → ℝ} {w w' : ℝ≥0 → ℝ} {vL vL' : Fin nL → ℝ≥0 → ℝ} {vR vR' : Fin nR → ℝ≥0 → ℝ}
  {b : ℝ≥0 → ℝ} {ζ ζ' : ℝ≥0∞}

/-- The two states agree at time `t`. -/
def Agree (w : ℝ≥0 → ℝ) (vL : Fin nL → ℝ≥0 → ℝ) (vR : Fin nR → ℝ≥0 → ℝ) (w' : ℝ≥0 → ℝ)
    (vL' : Fin nL → ℝ≥0 → ℝ) (vR' : Fin nR → ℝ≥0 → ℝ) (t : ℝ≥0) : Prop :=
  w t = w' t ∧ (∀ i, vL i t = vL' i t) ∧ ∀ j, vR j t = vR' j t

section Step

variable (hsep : ∀ i j, xL i < xR j) (h : IsForcePath xL xR ρL ρR w vL vR ζ)
  (hw : DriverEq a ρL ρR w vL vR b ζ) (h' : IsForcePath xL xR ρL ρR w' vL' vR' ζ')
  (hw' : DriverEq a ρL ρR w' vL' vR' b ζ')
include hsep h hw h' hw'

omit hw h' hw' in
/-- At a time before the lifetime, no left mark and no right mark both touch the driver. -/
theorem not_two_sided {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) (i : Fin nL) (j : Fin nR)
    (hi : vL i t = w t) (hj : vR j t = w t) : False := by
  have h1 := h.vL_le_xL ht i
  have h2 := h.xR_le_vR ht j
  have := hsep i j
  linarith

/-- **One step of the continuous induction.** If the solutions agree at `t₀ < min ζ ζ'`, they
agree on a right neighbourhood `[t₀, u)`. -/
theorem exists_agree_Ico {t₀ : ℝ≥0} (ht₀ : (t₀ : ℝ≥0∞) < min ζ ζ')
    (hag : Agree w vL vR w' vL' vR' t₀) :
    ∃ u > t₀, ∀ t ∈ Ico t₀ u, Agree w vL vR w' vL' vR' t := by
  obtain ⟨hw₀, hL₀, hR₀⟩ := hag
  have hζ : (t₀ : ℝ≥0∞) < ζ := lt_of_lt_of_le ht₀ (min_le_left _ _)
  have hζ' : (t₀ : ℝ≥0∞) < ζ' := lt_of_lt_of_le ht₀ (min_le_right _ _)
  have hopen : IsOpen {t : ℝ≥0 | (t : ℝ≥0∞) < min ζ ζ'} :=
    isOpen_lt ENNReal.continuous_coe continuous_const
  have hca : ∀ {f : ℝ≥0 → ℝ} {ξ : ℝ≥0∞}, ContinuousOn f {t | (t : ℝ≥0∞) < ξ} →
      (t₀ : ℝ≥0∞) < ξ → ContinuousAt f t₀ := fun hf hξ =>
    hf.continuousAt ((isOpen_lt ENNReal.continuous_coe continuous_const).mem_nhds hξ)
  -- the threshold condition fails at `t₀`
  have hnt := h.not_threshold hζ
  unfold ForceWord.ThresholdCondition at hnt
  simp only [not_or, not_le] at hnt
  obtain ⟨hρL, hρR⟩ := hnt
  -- reduce to a statement on `Ico t₀ u` from an eventual separation
  have finish : ∀ (P : ℝ≥0 → Prop), (∀ᶠ s in 𝓝 t₀, P s) →
      (∀ t₁, t₀ ≤ t₁ → (t₁ : ℝ≥0∞) < min ζ ζ' → (∀ s ∈ Icc t₀ t₁, P s) →
        Agree w vL vR w' vL' vR' t₁) →
      ∃ u > t₀, ∀ t ∈ Ico t₀ u, Agree w vL vR w' vL' vR' t := by
    intro P hP hstep
    have hP' : ∀ᶠ s in 𝓝[≥] t₀, P s ∧ (s : ℝ≥0∞) < min ζ ζ' :=
      ((hP.and (hopen.mem_nhds ht₀))).filter_mono nhdsWithin_le_nhds
    obtain ⟨u, hu, hsub⟩ := (mem_nhdsGE_iff_exists_Ico_subset' (lt_add_one t₀)).1 hP'
    refine ⟨u, hu, fun t ht => hstep t ht.1 (hsub ht).2 fun s hs => (hsub ⟨hs.1, ?_⟩).1⟩
    exact lt_of_le_of_lt hs.2 ht.2
  by_cases hRc : ∃ j, vR j t₀ = w t₀
  · -- right contact group
    set A := Finset.univ.filter fun j => vR j t₀ = w t₀ with hAdef
    have hA : ∀ j ∈ A, vR j t₀ = w t₀ := fun j hj => (Finset.mem_filter.1 hj).2
    have hgL : ∀ i, 0 < w t₀ - vL i t₀ := by
      intro i
      obtain ⟨j, hj⟩ := hRc
      refine sub_pos.2 (lt_of_le_of_ne (h.vL_le_w hζ i) fun he => ?_)
      exact not_two_sided hsep h hζ i j he hj
    have hgR : ∀ j, 0 < if j ∈ A then 1 else vR j t₀ - w t₀ := by
      intro j
      split_ifs with hjA
      · exact one_pos
      · refine sub_pos.2 (lt_of_le_of_ne (h.w_le_vR hζ j) fun he => hjA ?_)
        exact Finset.mem_filter.2 ⟨Finset.mem_univ _, he.symm⟩
    obtain ⟨ε₁, hε₁, hε₁'⟩ := exists_pos_forall_lt _ hgL
    obtain ⟨ε₂, hε₂, hε₂'⟩ := exists_pos_forall_lt _ hgR
    set ε := min ε₁ ε₂
    have hε : 0 < ε := lt_min hε₁ hε₂
    have hev : ∀ᶠ s in 𝓝 t₀, (∀ i, ε < w s - vL i s ∧ ε < w' s - vL' i s) ∧
        ∀ j ∈ Aᶜ, ε < vR j s - w s ∧ ε < vR' j s - w' s := by
      refine Filter.Eventually.and (Filter.eventually_all.2 fun i => ?_)
        (Filter.eventually_all.2 fun j => ?_)
      · have hlt : ε < w t₀ - vL i t₀ := lt_of_le_of_lt (min_le_left _ _) (hε₁' i)
        have hlt' : ε < w' t₀ - vL' i t₀ := by rw [← hw₀, ← hL₀ i]; exact hlt
        exact (continuousAt_const.eventually_lt ((hca h.continuousOn_w hζ).sub
          (hca (h.continuousOn_vL i) hζ)) hlt).and
          (continuousAt_const.eventually_lt ((hca h'.continuousOn_w hζ').sub
          (hca (h'.continuousOn_vL i) hζ')) hlt')
      · by_cases hjA : j ∈ A
        · exact Filter.Eventually.of_forall fun s hs => absurd hjA (Finset.mem_compl.1 hs)
        · have hlt : ε < vR j t₀ - w t₀ := by
            have := hε₂' j
            simp only [hjA, ↓reduceIte] at this
            exact lt_of_le_of_lt (min_le_right _ _) this
          have hlt' : ε < vR' j t₀ - w' t₀ := by rw [← hw₀, ← hR₀ j]; exact hlt
          have e1 := continuousAt_const.eventually_lt ((hca (h.continuousOn_vR j) hζ).sub
            (hca h.continuousOn_w hζ)) hlt
          have e2 := continuousAt_const.eventually_lt ((hca (h'.continuousOn_vR j) hζ').sub
            (hca h'.continuousOn_w hζ')) hlt'
          filter_upwards [e1, e2] with s hs1 hs2 _ using ⟨hs1, hs2⟩
    refine finish _ hev fun t₁ h01 ht₁ hsep₁ => ?_
    have hP : Assembly.LocalPair a xL xR ρL ρR w vL vR w' vL' vR' b ζ ζ' t₀ t₁ :=
      { path := h, drv := hw, path' := h', drv' := hw', le := h01,
        lt := lt_of_lt_of_le ht₁ (min_le_left _ _), lt' := lt_of_lt_of_le ht₁ (min_le_right _ _),
        w₀ := hw₀, vL₀ := hL₀, vR₀ := hR₀ }
    have hρA : -2 < ∑ j ∈ A, ρR j := hρR
    exact hP.eq_of_rightGroup A hA hρA hε
      (fun s hs => ⟨fun i => ((hsep₁ s hs).1 i).1.le, fun j hj => ((hsep₁ s hs).2 j hj).1.le⟩)
      (fun s hs => ⟨fun i => ((hsep₁ s hs).1 i).2.le, fun j hj => ((hsep₁ s hs).2 j hj).2.le⟩)
      ⟨h01, le_rfl⟩
  · -- left contact group (possibly empty)
    simp only [not_exists] at hRc
    set A := Finset.univ.filter fun i => vL i t₀ = w t₀ with hAdef
    have hA : ∀ i ∈ A, vL i t₀ = w t₀ := fun i hi => (Finset.mem_filter.1 hi).2
    have hgR : ∀ j, 0 < vR j t₀ - w t₀ := fun j =>
      sub_pos.2 (lt_of_le_of_ne (h.w_le_vR hζ j) fun he => hRc j he.symm)
    have hgL : ∀ i, 0 < if i ∈ A then 1 else w t₀ - vL i t₀ := by
      intro i
      split_ifs with hiA
      · exact one_pos
      · refine sub_pos.2 (lt_of_le_of_ne (h.vL_le_w hζ i) fun he => hiA ?_)
        exact Finset.mem_filter.2 ⟨Finset.mem_univ _, he⟩
    obtain ⟨ε₁, hε₁, hε₁'⟩ := exists_pos_forall_lt _ hgL
    obtain ⟨ε₂, hε₂, hε₂'⟩ := exists_pos_forall_lt _ hgR
    set ε := min ε₁ ε₂
    have hε : 0 < ε := lt_min hε₁ hε₂
    have hev : ∀ᶠ s in 𝓝 t₀, (∀ i ∈ Aᶜ, ε < w s - vL i s ∧ ε < w' s - vL' i s) ∧
        ∀ j, ε < vR j s - w s ∧ ε < vR' j s - w' s := by
      refine Filter.Eventually.and (Filter.eventually_all.2 fun i => ?_)
        (Filter.eventually_all.2 fun j => ?_)
      · by_cases hiA : i ∈ A
        · exact Filter.Eventually.of_forall fun s hs => absurd hiA (Finset.mem_compl.1 hs)
        · have hlt : ε < w t₀ - vL i t₀ := by
            have := hε₁' i
            simp only [hiA, ↓reduceIte] at this
            exact lt_of_le_of_lt (min_le_left _ _) this
          have hlt' : ε < w' t₀ - vL' i t₀ := by rw [← hw₀, ← hL₀ i]; exact hlt
          have e1 := continuousAt_const.eventually_lt ((hca h.continuousOn_w hζ).sub
            (hca (h.continuousOn_vL i) hζ)) hlt
          have e2 := continuousAt_const.eventually_lt ((hca h'.continuousOn_w hζ').sub
            (hca (h'.continuousOn_vL i) hζ')) hlt'
          filter_upwards [e1, e2] with s hs1 hs2 _ using ⟨hs1, hs2⟩
      · have hlt : ε < vR j t₀ - w t₀ := lt_of_le_of_lt (min_le_right _ _) (hε₂' j)
        have hlt' : ε < vR' j t₀ - w' t₀ := by rw [← hw₀, ← hR₀ j]; exact hlt
        exact (continuousAt_const.eventually_lt ((hca (h.continuousOn_vR j) hζ).sub
          (hca h.continuousOn_w hζ)) hlt).and
          (continuousAt_const.eventually_lt ((hca (h'.continuousOn_vR j) hζ').sub
          (hca h'.continuousOn_w hζ')) hlt')
    refine finish _ hev fun t₁ h01 ht₁ hsep₁ => ?_
    have hP : Assembly.LocalPair a xL xR ρL ρR w vL vR w' vL' vR' b ζ ζ' t₀ t₁ :=
      { path := h, drv := hw, path' := h', drv' := hw', le := h01,
        lt := lt_of_lt_of_le ht₁ (min_le_left _ _), lt' := lt_of_lt_of_le ht₁ (min_le_right _ _),
        w₀ := hw₀, vL₀ := hL₀, vR₀ := hR₀ }
    have hρA : -2 < ∑ i ∈ A, ρL i := hρL
    exact hP.eq_of_leftGroup A hA hρA hε
      (fun s hs => ⟨fun i hi => ((hsep₁ s hs).1 i hi).1.le, fun j => ((hsep₁ s hs).2 j).1.le⟩)
      (fun s hs => ⟨fun i hi => ((hsep₁ s hs).1 i hi).2.le, fun j => ((hsep₁ s hs).2 j).2.le⟩)
      ⟨h01, le_rfl⟩

/-- **Agreement before both lifetimes.** -/
theorem agree_of_lt_min {t : ℝ≥0} (ht : (t : ℝ≥0∞) < min ζ ζ') :
    Agree w vL vR w' vL' vR' t := by
  by_contra hcon
  set S := {s : ℝ≥0 | (s : ℝ≥0∞) < min ζ ζ' ∧ ¬ Agree w vL vR w' vL' vR' s} with hSdef
  have hSne : S.Nonempty := ⟨t, ht, hcon⟩
  set t₀ := sInf S with ht₀def
  have hbdd : BddBelow S := OrderBot.bddBelow S
  have hle : ∀ s ∈ S, t₀ ≤ s := fun s hs => csInf_le hbdd hs
  have ht₀lt : (t₀ : ℝ≥0∞) < min ζ ζ' :=
    lt_of_le_of_lt (by exact_mod_cast hle t ⟨ht, hcon⟩) ht
  have hbefore : ∀ s < t₀, Agree w vL vR w' vL' vR' s := by
    intro s hs
    by_contra hns
    have hsl : (s : ℝ≥0∞) < min ζ ζ' := lt_trans (by exact_mod_cast hs) ht₀lt
    exact (not_le.2 hs) (hle s ⟨hsl, hns⟩)
  have hζ : (t₀ : ℝ≥0∞) < ζ := lt_of_lt_of_le ht₀lt (min_le_left _ _)
  have hζ' : (t₀ : ℝ≥0∞) < ζ' := lt_of_lt_of_le ht₀lt (min_le_right _ _)
  have hIic : ∀ {ξ : ℝ≥0∞}, (t₀ : ℝ≥0∞) < ξ → Iic t₀ ⊆ {s : ℝ≥0 | (s : ℝ≥0∞) < ξ} :=
    fun hξ s hs => lt_of_le_of_lt (by exact_mod_cast hs) hξ
  have hat : Agree w vL vR w' vL' vR' t₀ := by
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t₀) with h0 | h0
    · rw [← h0]
      refine ⟨by rw [h.w_zero, h'.w_zero], fun i => by rw [h.vL_zero, h'.vL_zero],
        fun j => by rw [h.vR_zero, h'.vR_zero]⟩
    · refine ⟨eq_of_eqOn_Iio h0 (h.continuousOn_w.mono (hIic hζ))
          (h'.continuousOn_w.mono (hIic hζ')) fun s hs => (hbefore s hs).1,
        fun i => eq_of_eqOn_Iio h0 ((h.continuousOn_vL i).mono (hIic hζ))
          ((h'.continuousOn_vL i).mono (hIic hζ')) fun s hs => (hbefore s hs).2.1 i,
        fun j => eq_of_eqOn_Iio h0 ((h.continuousOn_vR j).mono (hIic hζ))
          ((h'.continuousOn_vR j).mono (hIic hζ')) fun s hs => (hbefore s hs).2.2 j⟩
  obtain ⟨u, hu, hagree⟩ := exists_agree_Ico hsep h hw h' hw' ht₀lt hat
  obtain ⟨s, hsS, hsu⟩ := exists_lt_of_csInf_lt hSne hu
  exact hsS.2 (hagree s ⟨hle s hsS, hsu⟩)

/-- The lifetime of the first solution is at most that of the second. -/
theorem lifetime_le : ζ ≤ ζ' := by
  by_contra hlt
  rw [not_le] at hlt
  have hfin : ζ' ≠ ⊤ := ne_top_of_lt hlt
  set T := ζ'.toNNReal with hT
  have hTζ' : (T : ℝ≥0∞) = ζ' := ENNReal.coe_toNNReal hfin
  have hTζ : (T : ℝ≥0∞) < ζ := by rw [hTζ']; exact hlt
  have hmin : min ζ ζ' = ζ' := min_eq_right hlt.le
  have hnt := h.not_threshold hTζ
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ T) with h0 | h0
  · have hz : ζ' = 0 := by rw [← hTζ', ← h0]; rfl
    have hthr := h'.threshold_of_eq_zero hz
    apply hnt
    rw [← h0, h.w_zero]
    have e1 : (fun i => vL i 0) = xL := funext h.vL_zero
    have e2 : (fun j => vR j 0) = xR := funext h.vR_zero
    rw [e1, e2]
    exact hthr
  · have hca : ∀ {f : ℝ≥0 → ℝ}, ContinuousOn f {t | (t : ℝ≥0∞) < ζ} → ContinuousAt f T :=
      fun hf => hf.continuousAt ((isOpen_lt ENNReal.continuous_coe continuous_const).mem_nhds hTζ)
    have hcont : ContinuousAt (fun t => (w t, fun i => vL i t, fun j => vR j t)) T :=
      (hca h.continuousOn_w).prodMk ((continuousAt_pi.2 fun i => hca (h.continuousOn_vL i)).prodMk
        (continuousAt_pi.2 fun j => hca (h.continuousOn_vR j)))
    have heq : (fun t => (w' t, fun i => vL' i t, fun j => vR' j t)) =ᶠ[𝓝[<] T]
        (fun t => (w t, fun i => vL i t, fun j => vR j t)) := by
      filter_upwards [self_mem_nhdsWithin] with s hs
      have hs' : (s : ℝ≥0∞) < min ζ ζ' := by
        rw [hmin, ← hTζ']; exact_mod_cast hs
      obtain ⟨e1, e2, e3⟩ := agree_of_lt_min hsep h hw h' hw' hs'
      simp only [e1, e2, e3]
    have htend : Tendsto (fun t => (w' t, fun i => vL' i t, fun j => vR' j t)) (𝓝[<] T)
        (𝓝 (w T, fun i => vL i T, fun j => vR j T)) :=
      (hcont.tendsto.mono_left nhdsWithin_le_nhds).congr' heq.symm
    exact hnt (h'.threshold_of_tendsto h0 hTζ' htend)

end Step

end Assembly

end Sec2

open Sec2 Sec2.Assembly

/-- **Pathwise uniqueness of integrated `SLE_a(ρ)` paths for separated force words.** If no left
mark and no right mark both start at `0` (`∀ i j, xL i < xR j`), two solutions of Definition 2.1
(with its maximal lifetime) driven by the same path `b` have the same lifetime and coincide
before it. -/
theorem IsIntegratedSLEPath.eq_of_separated {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ}
    {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {w w' : ℝ≥0 → ℝ}
    {vL vL' : Fin nL → ℝ≥0 → ℝ} {vR vR' : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {ζ ζ' : ℝ≥0∞}
    (hsep : ∀ i j, xL i < xR j) (h : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ)
    (h' : IsIntegratedSLEPath a xL xR ρL ρR w' vL' vR' b ζ') :
    ζ = ζ' ∧ ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ →
      w t = w' t ∧ (∀ i, vL i t = vL' i t) ∧ ∀ j, vR j t = vR' j t := by
  have hp := h.isForcePath
  have hd := h.driverEq
  have hp' := h'.isForcePath
  have hd' := h'.driverEq
  have hle := lifetime_le hsep hp hd hp' hd'
  have hge := lifetime_le hsep hp' hd' hp hd
  have hζ : ζ = ζ' := le_antisymm hle hge
  refine ⟨hζ, fun t ht => ?_⟩
  have ht' : (t : ℝ≥0∞) < min ζ ζ' := by rw [← hζ, min_self]; exact ht
  exact agree_of_lt_min hsep hp hd hp' hd' ht'

end InteractingSLE
