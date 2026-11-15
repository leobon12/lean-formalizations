/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.LocalExtEPath
import InteractingSLE.Spec.Sec7.LocalExtBGraph
import InteractingSLE.Spec.Sec2.RestartEvolution

/-!
# The restarted local stop `σ = T + S'` is a stopping time; splicing along countably many events of `𝓕_τ`

Packet PROVE-LOCEXT-E (`σ = τ + restarted capStop`). Specification p. 251: "Applying Aux. lemma 55 conditionally …
produces a strictly longer own-filtration stopped driving history".

* **`isStoppingTime_restartTime_capStop`**: for a finite stopping time `T` of the frozen driving filtration `𝓓` and a
  good event `G`, the time `T + S'`, `S'` the capped local stop (radius `r`) of the restarted path
  `W_{T+·} − W_T`, is a `𝓓`-stopping time. The restarted filtration is not known to be right-continuous, so this is
  proved directly in `𝓓` (right-continuous) from the rational description of the hitting time; it does not go
  through `Sec5.Markov.isStoppingTime_restartTime`.
* `spliceTime τ σs E`: `σs i` on the first event `E i` containing the point, `τ` off all of them;
  **`isStoppingTime_spliceTime`**: a stopping time when `E i ∈ 𝓕_τ` and `τ ≤ σs i` on `E i`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace LocalExt

open Sec7 Sec5.Markov Coupling

/-! ### Splicing stopping times along events of `𝓕_τ` -/

section Splice

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓖 : Filtration ℝ≥0 mΩ}

open Classical in
/-- `σs i` on the first event `E i` containing the point, `τ` off all of them. -/
def spliceTime (τ : Ω → WithTop ℝ≥0) (σs : ℕ → Ω → WithTop ℝ≥0) (E : ℕ → Set Ω) (ω : Ω) : WithTop ℝ≥0 :=
  if h : ∃ i, ω ∈ E i then σs (Nat.find h) ω else τ ω

theorem spliceTime_of_mem {τ : Ω → WithTop ℝ≥0} {σs : ℕ → Ω → WithTop ℝ≥0} {E : ℕ → Set Ω}
    (hdisj : Pairwise fun i j => Disjoint (E i) (E j)) {i : ℕ} {ω : Ω} (hω : ω ∈ E i) : spliceTime τ σs E ω = σs i ω := by
  classical
  have h : ∃ i, ω ∈ E i := ⟨i, hω⟩
  have hi : Nat.find h = i := by
    by_contra hne
    exact Set.disjoint_left.1 (hdisj hne) (Nat.find_spec h) hω
  simp only [spliceTime, h, ↓reduceDIte, hi]

theorem spliceTime_of_forall_notMem {τ : Ω → WithTop ℝ≥0} {σs : ℕ → Ω → WithTop ℝ≥0} {E : ℕ → Set Ω}
    {ω : Ω} (hω : ∀ i, ω ∉ E i) : spliceTime τ σs E ω = τ ω := by
  classical
  have h : ¬ ∃ i, ω ∈ E i := fun ⟨i, hi⟩ => hω i hi
  simp only [spliceTime, h, ↓reduceDIte]

/-- **Splicing is a stopping time**: if the events `E i` belong to `𝓖_τ` and `τ ≤ σs i` on `E i`, then
`spliceTime τ σs E` is a stopping time. -/
theorem isStoppingTime_spliceTime {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime 𝓖 τ) {σs : ℕ → Ω → WithTop ℝ≥0}
    (hσs : ∀ i, IsStoppingTime 𝓖 (σs i)) {E : ℕ → Set Ω} (hE : ∀ i, MeasurableSet[hτ.measurableSpace] (E i))
    (hle : ∀ i, ∀ ω ∈ E i, τ ω ≤ σs i ω) : IsStoppingTime 𝓖 (spliceTime τ σs E) := by
  classical
  intro t
  set F : ℕ → Set Ω := fun i => E i ∩ ⋂ j ∈ Finset.range i, (E j)ᶜ with hF
  have hFm : ∀ i, MeasurableSet[hτ.measurableSpace] (F i) := fun i =>
    (hE i).inter (MeasurableSet.biInter (Finset.range i).countable_toSet fun j _ => (hE j).compl)
  have hU : MeasurableSet[hτ.measurableSpace] (⋃ i, E i)ᶜ := (MeasurableSet.iUnion hE).compl
  have heq : {ω | spliceTime τ σs E ω ≤ t} =
      (⋃ i, (F i ∩ {ω | τ ω ≤ t}) ∩ {ω | σs i ω ≤ t}) ∪ ((⋃ i, E i)ᶜ ∩ {ω | τ ω ≤ t}) := by
    ext ω
    simp only [mem_ofPred_eq, mem_union, mem_iUnion, mem_inter_iff, mem_compl_iff, hF, mem_iInter,
      Finset.mem_range, not_exists]
    by_cases h : ∃ i, ω ∈ E i
    · have hs : spliceTime τ σs E ω = σs (Nat.find h) ω := by simp only [spliceTime, h, ↓reduceDIte]
      rw [hs]
      constructor
      · intro hle'
        refine Or.inl ⟨Nat.find h, ⟨⟨Nat.find_spec h, fun j hj => Nat.find_min h hj⟩,
          (hle _ ω (Nat.find_spec h)).trans hle'⟩, hle'⟩
      · rintro (⟨i, ⟨⟨hEi, hmin⟩, -⟩, hσ⟩ | ⟨hno, -⟩)
        · have hi : Nat.find h = i := le_antisymm (Nat.find_min' h hEi)
            (not_lt.1 fun hlt => hmin _ hlt (Nat.find_spec h))
          rw [hi]; exact hσ
        · obtain ⟨i, hi⟩ := h; exact absurd hi (hno i)
    · have hs : spliceTime τ σs E ω = τ ω := by simp only [spliceTime, h, ↓reduceDIte]
      rw [hs]
      push Not at h
      constructor
      · intro hle'; exact Or.inr ⟨h, hle'⟩
      · rintro (⟨i, ⟨⟨hEi, -⟩, hτt⟩, -⟩ | ⟨-, hτt⟩)
        · exact absurd hEi (h i)
        · exact hτt
  rw [heq]
  exact (MeasurableSet.iUnion fun i => ((hFm i).2 t).inter (hσs i t)).union (hU.2 t)

end Splice

/-! ### The restarted local stop -/

section RestartStop

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {T : Ω → ℝ≥0} {G : Set Ω} {r : ℝ}

/-- The restarted capped local stop is finite. -/
theorem capStop_restart_ne_top (ω : Ω) : capStop r G (restartLife ζ T) (restartDrv W T) ω ≠ ⊤ :=
  ne_top_of_le_ne_top localStop_ne_top (min_le_left _ _)

/-- `T + x < t` for `x : ℝ≥0` iff `T < t` and `x < t − T`. -/
theorem coe_add_lt_iff {a x t : ℝ≥0} : (((a + x : ℝ≥0)) : WithTop ℝ≥0) < t ↔ a < t ∧ x < t - a := by
  rw [WithTop.coe_lt_coe]
  constructor
  · intro h
    exact ⟨lt_of_le_of_lt le_self_add h, lt_tsub_iff_left.2 h⟩
  · rintro ⟨-, h⟩
    exact lt_tsub_iff_left.1 h

/-- `(x.untopD 0 : ℝ≥0) < u` iff `x < u` for a finite `x`. -/
theorem untopD_lt_iff {x : WithTop ℝ≥0} (hx : x ≠ ⊤) {u : ℝ≥0} : x.untopD 0 < u ↔ x < (u : WithTop ℝ≥0) := by
  cases x with
  | top => exact absurd rfl hx
  | coe a => simp only [WithTop.untopD_coe, WithTop.coe_lt_coe]

/-- The restarted lifetime is below `t − T` iff the lifetime is below `t` (when `T < t`). -/
theorem restartLife_lt_iff {ω : Ω} {t : ℝ≥0} (hTt : T ω < t) :
    (restartLife ζ T ω : WithTop ℝ≥0) < ((t - T ω : ℝ≥0) : WithTop ℝ≥0) ↔ ζ ω < (t : ℝ≥0∞) := by
  change ζ ω - (T ω : ℝ≥0∞) < ((t - T ω : ℝ≥0) : ℝ≥0∞) ↔ ζ ω < (t : ℝ≥0∞)
  rw [ENNReal.coe_sub]
  constructor
  · intro h
    by_contra hge
    rw [not_lt] at hge
    have h1 : (t : ℝ≥0∞) - T ω ≤ ζ ω - T ω := tsub_le_tsub_right hge _
    exact absurd h (not_lt.2 h1)
  · intro h
    rcases le_or_gt (ζ ω) (T ω) with hζT | hζT
    · rw [tsub_eq_zero_of_le hζT]
      exact tsub_pos_of_lt (by exact_mod_cast hTt)
    · exact AddLECancellable.tsub_lt_tsub_right_of_le (ENNReal.cancel_of_ne ENNReal.coe_ne_top) hζT.le h

/-- The hitting part of the restarted local stop, read in original time on a good path. -/
theorem hitBelow_restart_lt_iff {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {ω : Ω} (hg : IsGoodPath κ xL xR ρL ρR W VL VR B ζ ω) {t : ℝ≥0} {D : Set ℝ≥0}
    (hD : Dense D) :
    hitBelow (stopGap r fun s => restartDrv W T s ω) (restartLife ζ T ω) 0 < ((t - T ω : ℝ≥0) : WithTop ℝ≥0) ↔
      ∃ d ∈ D, (((T ω + d : ℝ≥0)) : WithTop ℝ≥0) < t ∧ ((T ω + d : ℝ≥0) : ℝ≥0∞) < ζ ω ∧
        r / 4 < |Sec2.Restart.progVersion ζ W (T ω + d) ω - Sec2.Restart.progVersion ζ W (T ω) ω| := by
  by_cases hTζ : (T ω : ℝ≥0∞) < ζ ω
  · have hp' := isIntegratedSLEPath_restart (B := B) (T := T) hg hTζ
    have hcont : ContinuousOn (stopGap r fun s => restartDrv W T s ω) {s : ℝ≥0 | (s : ℝ≥0∞) < restartLife ζ T ω} :=
      continuousOn_stopGap hp'.2.2.2.1
    rw [hitBelow_lt_iff hcont hD]
    have hv0 := (Sec2.Restart.restart_values hg.1 hTζ).1
    refine exists_congr fun d => and_congr_right fun _ => ?_
    constructor
    · rintro ⟨hdt, hdζ, hgap⟩
      have hdζ' : ((T ω + d : ℝ≥0) : ℝ≥0∞) < ζ ω := (Sec2.Restart.coe_lt_sub_iff _ _).1 hdζ
      refine ⟨WithTop.coe_lt_coe.2 (lt_tsub_iff_left.1 hdt), hdζ', ?_⟩
      rw [(Sec2.Restart.restart_values hg.1 hdζ').1, hv0]
      simp only [stopGap, restartDrv] at hgap
      linarith
    · rintro ⟨hdt, hdζ', hgap⟩
      refine ⟨lt_tsub_iff_left.2 (WithTop.coe_lt_coe.1 hdt), (Sec2.Restart.coe_lt_sub_iff _ _).2 hdζ', ?_⟩
      rw [(Sec2.Restart.restart_values hg.1 hdζ').1, hv0] at hgap
      simp only [stopGap, restartDrv]
      linarith
  · rw [not_lt] at hTζ
    have hζ0 : restartLife ζ T ω = 0 := tsub_eq_zero_of_le hTζ
    have htop : hitBelow (stopGap r fun s => restartDrv W T s ω) (restartLife ζ T ω) 0 = ⊤ := by
      rw [hζ0, hitBelow]
      have : ¬ {s : ℝ≥0 | (s : ℝ≥0∞) < 0 ∧ stopGap r (fun s => restartDrv W T s ω) s < 0}.Nonempty :=
        fun ⟨s, hs, _⟩ => not_lt_zero hs
      simp only [this, ↓reduceIte]
    rw [htop]
    simp only [not_top_lt, false_iff, not_exists, not_and]
    intro d _ _ hdζ
    exact absurd (lt_of_le_of_lt (by exact_mod_cast le_self_add) hdζ) (not_lt.2 hTζ)

/-- **The restarted local stop is a stopping time**: for a finite stopping time `T` of the frozen driving filtration
`𝓓` and a good event `G`, the time `T + S'`, `S'` the capped local stop of radius `r` of the restarted path
`W_{T+·} − W_T`, is a `𝓓`-stopping time. -/
theorem isStoppingTime_restartTime_capStop {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ} (hX : IsMeasurableKilledDriving W VL VR ζ)
    (hT : IsStoppingTime (drivingFiltration P hX) fun ω => (T ω : WithTop ℝ≥0)) (hGm : MeasurableSet G)
    (hG0 : P Gᶜ = 0) (hG : ∀ ω ∈ G, IsGoodPath κ xL xR ρL ρR W VL VR B ζ ω) (r : ℝ) :
    IsStoppingTime (drivingFiltration P hX) (restartTime T (capStop r G (restartLife ζ T) (restartDrv W T))) := by
  classical
  set 𝓓 := drivingFiltration P hX with h𝓓
  have hle : killedDrivingFiltration hX ≤ 𝓓 := Ito.le_usualAugmentation _ P
  have hWad : AdaptedBefore 𝓓 ζ W := Ito.adaptedBefore_mono hle (Coupling.adaptedBefore_killedDriving_W hX)
  have hζ : IsStoppingTime 𝓓 fun ω => (ζ ω : WithTop ℝ≥0) := Ito.isStoppingTime_lifetime hWad
  have hWp := Sec2.Restart.isStronglyProgressive_progVersion hWad
  have hG𝓓 : MeasurableSet[𝓓 0] G := measurableSet_drivingFiltration_zero_of_null_compl hX hGm hG0
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense ℝ≥0
  set pv := Sec2.Restart.progVersion ζ W with hpv
  set A : ℝ≥0 → Set Ω := fun d =>
    {ω | ((T ω + d : ℝ≥0) : ℝ≥0∞) < ζ ω ∧ r / 4 < |pv (T ω + d) ω - pv (T ω) ω|} with hAdef
  have hA : ∀ d, MeasurableSet[(Sec2.Restart.isStoppingTime_add_const hT d).measurableSpace] (A d) := by
    intro d
    have hB : MeasurableSet {x : ℝ | r / 4 < |x|} := measurableSet_lt measurable_const measurable_abs
    have h := Sec2.Restart.adaptedBefore_restart hT hζ hWp hWp d {x : ℝ | r / 4 < |x|} hB
    have e : {ω | (d : ℝ≥0∞) < ζ ω - T ω ∧ pv (T ω + d) ω - pv (T ω) ω ∈ {x : ℝ | r / 4 < |x|}} = A d := by
      ext ω
      simp only [mem_ofPred_eq, Sec2.Restart.coe_lt_sub_iff, hAdef]
    rw [e] at h
    exact h
  have hrc : 𝓓.IsRightContinuous := by
    rw [h𝓓]; unfold drivingFiltration usualAugmentation; infer_instance
  refine isStoppingTime_of_measurableSet_lt_of_isRightContinuous fun t => ?_
  have heq : {ω | restartTime T (capStop r G (restartLife ζ T) (restartDrv W T)) ω < t} =
      {ω | ((T ω + stopHorizon r : ℝ≥0) : WithTop ℝ≥0) < t} ∪
        ({ω | (T ω : WithTop ℝ≥0) < t} ∩ {ω | (ζ ω : WithTop ℝ≥0) < t}) ∪
        (G ∩ ⋃ d ∈ D, A d ∩ {ω | ((T ω + d : ℝ≥0) : WithTop ℝ≥0) < t}) := by
    ext ω
    have hS : capStop r G (restartLife ζ T) (restartDrv W T) ω =
        min (min (stopHorizon r : WithTop ℝ≥0)
          (if ω ∈ G then hitBelow (stopGap r fun s => restartDrv W T s ω) (restartLife ζ T ω) 0 else ⊤))
          (restartLife ζ T ω : WithTop ℝ≥0) := rfl
    simp only [mem_ofPred_eq, mem_union, mem_inter_iff, mem_iUnion, exists_prop]
    rw [restartTime, coe_add_lt_iff, untopD_lt_iff (capStop_restart_ne_top ω), hS]
    constructor
    · rintro ⟨hTt, h⟩
      rcases min_lt_iff.1 h with h1 | h1
      · rcases min_lt_iff.1 h1 with hH | hite
        · exact Or.inl (Or.inl (coe_add_lt_iff.2 ⟨hTt, WithTop.coe_lt_coe.1 hH⟩))
        · by_cases hω : ω ∈ G
          · simp only [hω, ↓reduceIte] at hite
            obtain ⟨d, hdD, hdt, hdζ, hgap⟩ := (hitBelow_restart_lt_iff (t := t) (hG ω hω) hDd).1 hite
            exact Or.inr ⟨hω, d, hdD, ⟨hdζ, hgap⟩, hdt⟩
          · simp only [hω, ↓reduceIte, not_top_lt] at hite
      · exact Or.inl (Or.inr ⟨WithTop.coe_lt_coe.2 hTt, (restartLife_lt_iff hTt).1 h1⟩)
    · rintro ((hH | ⟨hTt, hζt⟩) | ⟨hω, d, hdD, ⟨hdζ, hgap⟩, hdt⟩)
      · obtain ⟨hTt, hH⟩ := coe_add_lt_iff.1 hH
        exact ⟨hTt, min_lt_iff.2 (Or.inl (min_lt_iff.2 (Or.inl (WithTop.coe_lt_coe.2 hH))))⟩
      · have hTt' : T ω < t := WithTop.coe_lt_coe.1 hTt
        exact ⟨hTt', min_lt_iff.2 (Or.inr ((restartLife_lt_iff hTt').2 hζt))⟩
      · have hTt : T ω < t := (coe_add_lt_iff.1 hdt).1
        refine ⟨hTt, min_lt_iff.2 (Or.inl (min_lt_iff.2 (Or.inr ?_)))⟩
        simp only [hω, ↓reduceIte]
        exact (hitBelow_restart_lt_iff (t := t) (hG ω hω) hDd).2 ⟨d, hdD, hdt, hdζ, hgap⟩
  rw [heq]
  refine (((Sec2.Restart.isStoppingTime_add_const hT _).measurableSet_lt t).union
    ((hT.measurableSet_lt t).inter (hζ.measurableSet_lt t))).union
    ((𝓓.mono (zero_le (a := t)) _ hG𝓓).inter (MeasurableSet.biUnion hDc fun d _ => ?_))
  exact measurableSet_inter_lt_of_measurableSet (Sec2.Restart.isStoppingTime_add_const hT d) (hA d) t

end RestartStop

end LocalExt

end InteractingSLE
