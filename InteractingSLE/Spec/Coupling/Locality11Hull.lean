import InteractingSLE.Spec.Coupling.Assembly11Drv
import InteractingSLE.Spec.Coupling.CompactTransfer
import InteractingSLE.Spec.Dimension.TraceBridge
import InteractingSLE.GFF.LocalSets.HittingSigma

/-!
# Theorem 1.1, locality: the hull `K_τ` at a frozen stopping time as a random set

Packet PROVE-T11-LOC. For a stopping time `τ < ζ` of the frozen driving filtration, read at `τ' = τ.untopD 0`:

* `exists_drivingStopped_disjoint`: for a compact `K ⊆ ℍ` there is an event of the frozen stopped σ-algebra `𝓕_τ`,
  contained in the avoidance event `{K ∩ K_τ = ∅}` and almost surely equal to it (the safe stops of `K` below `τ`, as in
  `exists_drivingStopped_measurable`);
* `exists_hittingVersion_hull`: the hull `K_τ` has a version `A` (almost surely equal to it) that is measurable for the
  hitting σ-algebra, and every avoidance event `{A ∩ V = ∅}`, `V ⊆ ℍ` open, is almost surely equal to an event of
  `𝓕_τ` (rational closed balls: `V` is the union of the rational closed balls inside it);
* `ae_hull_subset_isOpen`: almost surely `K_τ ⊆ ℍ` and `ℍ ∖ K_τ` is open (the driver frozen after a time in
  `(τ', ζ)`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology QuantumZipper Metric
open scoped NNReal ENNReal Classical

namespace InteractingSLE

namespace Coupling

open Ito

/-! ### Rational closed balls -/

/-- The closed rational ball of `(q₁, q₂, r)`. -/
def ratCBall (b : ℚ × ℚ × ℚ) : Set ℂ := closedBall (ratCentre b) (b.2.2 : ℝ)

theorem isCompact_ratCBall (b : ℚ × ℚ × ℚ) : IsCompact (ratCBall b) := isCompact_closedBall _ _

/-- Every point of an open set lies in a rational closed ball inside it. -/
theorem exists_ratCBall_mem_subset {V : Set ℂ} (hV : IsOpen V) {z : ℂ} (hz : z ∈ V) :
    ∃ b : ℚ × ℚ × ℚ, z ∈ ratCBall b ∧ ratCBall b ⊆ V := by
  obtain ⟨F, hzF, hFV⟩ := exists_rationalBalls (isCompact_singleton (x := z)) hV
    (singleton_subset_iff.2 hz)
  obtain ⟨b, hb, hzb⟩ := mem_iUnion₂.1 (hzF (mem_singleton z))
  exact ⟨b, ball_subset_closedBall hzb, (subset_biUnion_of_mem (u := fun b =>
    closedBall (ratCentre b) (b.2.2 : ℝ)) hb).trans hFV⟩

/-- Avoidance of an open set is avoidance of the rational closed balls inside it. -/
theorem disjoint_iff_forall_ratCBall {S V : Set ℂ} (hV : IsOpen V) :
    Disjoint S V ↔ ∀ b : ℚ × ℚ × ℚ, ratCBall b ⊆ V → Disjoint (ratCBall b) S := by
  constructor
  · intro h b hb
    exact (h.mono_right hb).symm
  · intro h
    refine Set.disjoint_left.2 fun z hzS hzV => ?_
    obtain ⟨b, hzb, hbV⟩ := exists_ratCBall_mem_subset hV hzV
    exact Set.disjoint_left.1 (h b hbV) hzb hzS

/-! ### Avoidance of a compact set at a frozen stopping time -/

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {nL nR : ℕ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **Avoidance of a compact set at a frozen stopping time is an event of `𝓕_τ`, up to a null set.** -/
theorem exists_drivingStopped_disjoint (hX : IsMeasurableKilledDriving W VL VR ζ)
    (hpath : ∀ᵐ ω ∂P, ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω} ∧ W 0 ω = 0)
    {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ H)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime (drivingFiltration P hX) τ)
    (hτζ : ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < ζ ω) :
    ∃ E' : Set Ω, MeasurableSet[hτ.measurableSpace] E' ∧
      E' ⊆ {ω | Disjoint K (fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0))} ∧
      ∀ᵐ ω ∂P, Disjoint K (fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)) → ω ∈ E' := by
  set 𝓗 := killedDrivingFiltration hX with h𝓗
  set 𝓓 := drivingFiltration P hX with h𝓓
  set τ' : Ω → ℝ≥0 := fun ω => (τ ω).untopD 0 with hτ'def
  have hτf : ∀ᵐ ω ∂P, τ ω ≠ ⊤ := hτζ.mono fun _ h => ne_top_of_lt_zeta h
  have hτ' : IsStoppingTime 𝓓 fun ω => (τ' ω : WithTop ℝ≥0) := isStoppingTime_untopD (𝓕 := 𝓗) hτ hτf
  have hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[𝓓 0] s := fun s hs h0 =>
    measurableSet_usualAugmentation_of_null (𝓕 := 𝓗) hs h0 0
  have hσeq : hτ.measurableSpace = hτ'.measurableSpace := measurableSpace_untopD_eq hnull hτ hτf hτ'
  obtain ⟨m, hm, hKm⟩ := exists_pos_le_im_of_isCompact hK hKH
  set σ₀ : ℕ → Ω → ℝ≥0 := fun n ω => min (τ' ω) n with hσ₀_def
  have hσ₀ : ∀ n : ℕ, IsStoppingTime 𝓓 fun ω => (σ₀ n ω : WithTop ℝ≥0) := fun n => by
    have h := hτ'.min_const (n : ℝ≥0)
    convert h using 2 with ω
    simp only [hσ₀_def, WithTop.coe_min]
  have hσ₀m : ∀ ω, Monotone fun n => σ₀ n ω := fun ω n n' h =>
    min_le_min le_rfl (by exact_mod_cast h)
  have hσ₀ζ : ∀ n, ∀ᵐ ω ∂P, (σ₀ n ω : ℝ≥0∞) < ζ ω := fun n => by
    filter_upwards [hτζ] with ω h
    exact lt_of_le_of_lt (by exact_mod_cast min_le_left _ _) (coe_untopD_lt_zeta h)
  obtain ⟨ρ, hρst, hρle, hρmono, hρsafe, hρex⟩ := exists_safeSeq_of_adapted (𝓗 := 𝓗) (P := P)
    (adaptedBefore_killedDriving_W hX) hpath hK hKH hm hKm hσ₀ hσ₀m hσ₀ζ
  set good : Ω → Prop := fun ω => ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω} ∧
    (∀ n : ℕ, IsSafeAt K (m / ((n : ℝ) + 1)) n (σ₀ n ω) (ζ ω) (W · ω) (ρ n ω)) ∧
    ∀ (j : ℕ) (t : ℝ≥0), t ≤ σ₀ j ω →
      (∀ z ∈ K, ∃ u, IsForwardSol (rpath (W · ω)) z t u) → ∀ᶠ n in atTop, t ≤ ρ n ω with hgood
  have hae : ∀ᵐ ω ∂P, good ω := by
    filter_upwards [hpath, ae_all_iff.2 hρsafe, hρex] with ω h1 h3 h4
    exact ⟨h1.1, h3, h4⟩
  obtain ⟨G, hGm, hGc, hGgood⟩ : ∃ G : Set Ω, MeasurableSet G ∧ P Gᶜ = 0 ∧ ∀ ω ∈ G, good ω := by
    refine ⟨(toMeasurable P {ω | ¬ good ω})ᶜ, (measurableSet_toMeasurable _ _).compl, ?_,
      fun ω hω => ?_⟩
    · rw [compl_compl, measure_toMeasurable]; exact ae_iff.1 hae
    · by_contra h; exact hω (subset_toMeasurable _ _ h)
  have hG0 : MeasurableSet[𝓓 0] G := by
    have := (hnull _ hGm.compl hGc).compl
    rwa [compl_compl] at this
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := by rw [ae_iff]; exact hGc
  set F : ℕ → Set Ω := fun n => G ∩ {ω | ρ n ω = τ' ω} with hFdef
  have hGτ : MeasurableSet[hτ'.measurableSpace] G := by
    have h0 := IsStoppingTime.measurableSpace_mono (isStoppingTime_const 𝓓 (0 : ℝ≥0)) hτ'
      (fun ω => WithTop.coe_le_coe.2 (zero_le (a := τ' ω)))
    rw [IsStoppingTime.measurableSpace_const] at h0
    exact h0 _ hG0
  have hF : ∀ n, MeasurableSet[hτ'.measurableSpace] (F n) := fun n => by
    have h := IsStoppingTime.measurableSet_eq_stopping_time hτ' (hρst n)
    have e : {ω | ρ n ω = τ' ω} = {ω | (τ' ω : WithTop ℝ≥0) = (ρ n ω : WithTop ℝ≥0)} := by
      ext ω; simp only [mem_ofPred_eq, WithTop.coe_inj, eq_comm]
    rw [hFdef]; simp only
    rw [e]
    exact hGτ.inter h
  refine ⟨⋃ n, F n, ?_, ?_, ?_⟩
  · rw [hσeq]; exact MeasurableSet.iUnion hF
  · rintro ω ⟨_, ⟨n, rfl⟩, hω, heq⟩
    have hs := (hGgood ω hω).2.1 n
    rw [heq] at hs
    have hw := (hGgood ω hω).1
    refine Set.disjoint_left.2 fun z hz hzK => ?_
    exact notMem_fwdHull_of_alive hw hs.1 (hKH hz) (hs.2.2.2 z hz).1 hzK
  · filter_upwards [hGae] with ω hω hdis
    obtain ⟨-, -, hexh⟩ := hGgood ω hω
    have halive : ∀ z ∈ K, ∃ u, IsForwardSol (rpath (W · ω)) z (τ' ω) u := fun z hz =>
      exists_isForwardSol_of_mem (τ' ω).coe_nonneg ⟨hKH hz, Set.disjoint_left.1 hdis hz⟩
    obtain ⟨j, hj⟩ : ∃ j : ℕ, τ' ω ≤ (j : ℝ≥0) := by
      obtain ⟨j, hj⟩ := exists_nat_ge (τ' ω); exact ⟨j, hj⟩
    have hτj : τ' ω ≤ σ₀ j ω := le_min le_rfl hj
    obtain ⟨n, hn⟩ := (hexh j (τ' ω) hτj halive).exists
    exact mem_iUnion.2 ⟨n, hω, le_antisymm ((hρle n ω).trans (min_le_left _ _)) hn⟩

/-! ### Null modifications of stopped events -/

/-- A measurable set almost surely equal to an event of a usual augmentation belongs to it. -/
theorem measurableSet_usualAugmentation_of_ae_eq {𝓕 : Filtration ℝ≥0 mΩ} {t : ℝ≥0} {E E' : Set Ω}
    (hE : MeasurableSet E) (hE' : MeasurableSet[usualAugmentation 𝓕 P t] E') (h : E =ᵐ[P] E') :
    MeasurableSet[usualAugmentation 𝓕 P t] E := by
  have := measurableSet_nullAugmented_of_ae_eq (𝓕 := usualAugmentation 𝓕 P) (P := P) hE hE' h
  rwa [nullAugmented_usualAugmentation] at this

/-- A measurable set almost surely equal to an event of a stopped σ-algebra of a usual augmentation belongs to it. -/
theorem measurableSet_stopped_of_ae_eq {𝓕 : Filtration ℝ≥0 mΩ} {σ : Ω → WithTop ℝ≥0}
    (hσ : IsStoppingTime (usualAugmentation 𝓕 P) σ) {E E' : Set Ω} (hE : MeasurableSet E)
    (hE' : MeasurableSet[hσ.measurableSpace] E') (h : E =ᵐ[P] E') :
    MeasurableSet[hσ.measurableSpace] E := by
  rw [IsStoppingTime.measurableSet] at hE' ⊢
  have hσm : ∀ i : ℝ≥0, MeasurableSet {ω | σ ω ≤ i} := fun i =>
    (usualAugmentation 𝓕 P).le i _ (hσ i)
  refine ⟨?_, fun i => measurableSet_usualAugmentation_of_ae_eq (hE.inter (hσm i)) (hE'.2 i)
    (h.inter EventuallyEq.rfl)⟩
  have hE'm : MeasurableSet E' := (iSup_le fun t => (usualAugmentation 𝓕 P).le t) _ hE'.1
  have h1 : P (E' \ E) = 0 := (ae_eq_set.1 h).2
  have h2 : P (E \ E') = 0 := (ae_eq_set.1 h).1
  have hsup : ∀ s, MeasurableSet s → P s = 0 →
      MeasurableSet[⨆ t, usualAugmentation 𝓕 P t] s := fun s hs h0 =>
    (le_iSup (fun t => usualAugmentation 𝓕 P t) 0) s (measurableSet_usualAugmentation_of_null hs h0 0)
  have e : E = (E' \ (E' \ E)) ∪ (E \ E') := by
    ext ω; by_cases h1 : ω ∈ E <;> by_cases h2 : ω ∈ E' <;> simp [h1, h2]
  rw [e]
  exact (hE'.1.diff (hsup _ (hE'm.diff hE) h1)).union (hsup _ (hE.diff hE'm) h2)

/-! ### A hitting-measurable version of the hull -/

/-- **The hull at a frozen stopping time as a random set.** It has a version measurable for the hitting σ-algebra,
and every avoidance event of an open `V ⊆ ℍ` is almost surely an event of the frozen `𝓕_τ`. -/
theorem exists_hittingVersion_hull (hX : IsMeasurableKilledDriving W VL VR ζ)
    (hpath : ∀ᵐ ω ∂P, ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω} ∧ W 0 ω = 0)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime (drivingFiltration P hX) τ)
    (hτζ : ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < ζ ω) :
    ∃ A : Ω → Set ℂ, Measurable[mΩ, hittingSigma] A ∧
      A =ᵐ[P] (fun ω => fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)) ∧
      ∀ V : Set ℂ, IsOpen V → V ⊆ H → ∃ E' : Set Ω, MeasurableSet[hτ.measurableSpace] E' ∧
        {ω | Disjoint (A ω) V} =ᵐ[P] E' := by
  set Kτ : Ω → Set ℂ := fun ω => fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0) with hKτ
  have hb : ∀ b : ℚ × ℚ × ℚ, ∃ E' : Set Ω, MeasurableSet[hτ.measurableSpace] E' ∧
      (ratCBall b ⊆ H → ∀ᵐ ω ∂P, (Disjoint (ratCBall b) (Kτ ω) ↔ ω ∈ E')) := by
    intro b
    by_cases hbH : ratCBall b ⊆ H
    · obtain ⟨E', hE'm, hE'sub, hE'ae⟩ :=
        exists_drivingStopped_disjoint hX hpath (isCompact_ratCBall b) hbH hτ hτζ
      exact ⟨E', hE'm, fun _ => hE'ae.mono fun ω hω => ⟨hω, fun h => hE'sub h⟩⟩
    · exact ⟨∅, @MeasurableSet.empty _ hτ.measurableSpace, fun h => absurd h hbH⟩
  choose E hEm hEae using hb
  have hEm' : ∀ b, MeasurableSet (E b) := fun b => hτ.measurableSpace_le _ (hEm b)
  set good : Ω → Prop := fun ω => ∀ b, ratCBall b ⊆ H → (Disjoint (ratCBall b) (Kτ ω) ↔ ω ∈ E b)
    with hgood_def
  have hgood : ∀ᵐ ω ∂P, good ω := ae_all_iff.2 fun b => by
    by_cases hbH : ratCBall b ⊆ H
    · filter_upwards [hEae b hbH] with ω hω _ using hω
    · exact Eventually.of_forall fun ω h => absurd h hbH
  set S : Set Ω := toMeasurable P {ω | ¬ good ω} with hS
  have hSm : MeasurableSet S := measurableSet_toMeasurable _ _
  have hS0 : P S = 0 := by rw [hS, measure_toMeasurable]; exact ae_iff.1 hgood
  have hSc : ∀ ω, ω ∉ S → good ω := fun ω hω => by
    by_contra h; exact hω (subset_toMeasurable _ _ h)
  have hSae : ∀ᵐ ω ∂P, ω ∉ S := measure_eq_zero_iff_ae_notMem.1 hS0
  set A : Ω → Set ℂ := fun ω => if ω ∈ S then ∅ else Kτ ω with hA
  have hAae : A =ᵐ[P] Kτ := by
    filter_upwards [hSae] with ω hω
    simp [hA, hω]
  have havoid : ∀ V : Set ℂ, IsOpen V → V ⊆ H → ∀ ω, ω ∉ S →
      (Disjoint (A ω) V ↔ ω ∈ ⋂ b, ⋂ (_ : ratCBall b ⊆ V), E b) := by
    intro V hV hVH ω hω
    simp only [hA, hω, ↓reduceIte, mem_iInter]
    rw [disjoint_iff_forall_ratCBall hV]
    exact forall_congr' fun b => forall_congr' fun hb => hSc ω hω b (hb.trans hVH)
  refine ⟨A, ?_, hAae, fun V hV hVH => ⟨⋂ b, ⋂ (_ : ratCBall b ⊆ V), E b, ?_, ?_⟩⟩
  · refine @measurable_generateFrom _ _ _ _ _ ?_
    rintro _ ⟨U, hU, hUH, rfl⟩
    have e : A ⁻¹' {T : Set ℂ | (T ∩ U).Nonempty} = Sᶜ ∩ (⋂ b, ⋂ (_ : ratCBall b ⊆ U), E b)ᶜ := by
      ext ω
      simp only [mem_preimage, mem_ofPred_eq, mem_inter_iff, mem_compl_iff]
      by_cases hω : ω ∈ S
      · simp [hA, hω]
      · rw [← havoid U hU hUH ω hω, ← not_disjoint_iff_nonempty_inter]
        simp [hω]
    rw [e]
    exact hSm.compl.inter (MeasurableSet.iInter fun b => MeasurableSet.iInter fun _ => hEm' b).compl
  · exact @MeasurableSet.iInter _ _ hτ.measurableSpace _ _ fun b =>
      @MeasurableSet.iInter _ _ hτ.measurableSpace _ _ fun _ => hEm b
  · filter_upwards [hSae] with ω hω
    exact propext (havoid V hV hVH ω hω)

/-- **The hull is almost surely relatively closed in `ℍ`** at a time before the lifetime. -/
theorem ae_hull_subset_isOpen
    (hpath : ∀ᵐ ω ∂P, ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω})
    {τ' : Ω → ℝ≥0} (hτζ : ∀ᵐ ω ∂P, (τ' ω : ℝ≥0∞) < ζ ω) :
    ∀ᵐ ω ∂P, fwdHull (fun s : ℝ => W s.toNNReal ω) (τ' ω) ⊆ H ∧
      IsOpen (H \ fwdHull (fun s : ℝ => W s.toNNReal ω) (τ' ω)) := by
  filter_upwards [hpath, hτζ] with ω hw ht
  refine ⟨fun z hz => hz.1, ?_⟩
  obtain ⟨t₂, htt₂, ht₂ζ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ht
  have hc := continuousOn_rpath hw ht₂ζ
  have htt₂' : ((τ' ω : ℝ≥0) : ℝ) < (t₂ : ℝ) := by exact_mod_cast htt₂
  have heq : fwdHull (rpath (W · ω)) (τ' ω) = fwdHull (clampDrv (rpath (W · ω)) t₂) (τ' ω) :=
    InteractingSLE.fwdHull_eq_of_eqOn (τ' ω).coe_nonneg htt₂' fun r hr =>
      (clampDrv_eqOn (W := rpath (W · ω)) hr).symm
  show IsOpen (H \ fwdHull (rpath (W · ω)) (τ' ω))
  rw [heq]
  exact FwdHolo.isOpen_compl_fwdHull (continuous_clampDrv t₂.coe_nonneg hc) (τ' ω).coe_nonneg

end Coupling

end InteractingSLE
