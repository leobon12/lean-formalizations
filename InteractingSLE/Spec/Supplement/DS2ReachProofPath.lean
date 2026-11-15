/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.DS2ReachProof
import InteractingSLE.Spec.Sec2.Assembly2UpTo
import InteractingSLE.Spec.Sec2.PatchingNonaccum

/-!
# DS2 in reach form, II: deterministic facts about one integrated path

Packet PROVE-T14-DS. Pathwise ingredients of the proof of `DSReach.DS2ReachStatement`:

* `InCBuffer`: the **closed buffer** (coordinates bounded by `R`, designated far gaps at least `g`); the open
  inner buffer `InBuffer` lies inside it;
* `not_threshold_of_inCBuffer`: an ordered state in the closed buffer is not a continuation threshold for a DS1 word
  (the contact groups are inner prefixes, whose weights sum to at least `ε − 2 > −2`);
* `w_eq_linear`: along an integrated path the driver is a linear function of the Brownian path and the force
  coordinates, `w = √a b − ∑ (ρ/2)(v − x)` (the reciprocal drifts are half the coordinate motions);
* `lt_lifetime_of_forall_inCBuffer`: a path of a DS1 word that stays in the closed buffer cannot reach its lifetime
  (the force coordinates are monotone and bounded, so the state has a limit at a finite lifetime, which is not a
  threshold);
* `exitTime`, `stopPath`: the first exit time from a closed set before a horizon, and the path stopped there.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Finset
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Supp12

namespace DSReach

open DS2

/-! ### The closed buffer -/

section Buffer

variable {nL nR : ℕ}

/-- The **closed buffer**: every coordinate of `p = (W, V^L, V^R)` has absolute value at most `R`, and every far gap
(right labels `≥ m_R`, left labels `≥ m_L`) is at least `g`. -/
def InCBuffer (mL mR : ℕ) (R g : ℝ) (p : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)) : Prop :=
  (|p.1| ≤ R ∧ (∀ i, |p.2.1 i| ≤ R) ∧ ∀ j, |p.2.2 j| ≤ R) ∧
    (∀ j : Fin nR, mR ≤ (j : ℕ) → g ≤ p.2.2 j - p.1) ∧ ∀ i : Fin nL, mL ≤ (i : ℕ) → g ≤ p.1 - p.2.1 i

theorem isClosed_setOf_inCBuffer (mL mR : ℕ) (R g : ℝ) :
    IsClosed {p : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) | InCBuffer mL mR R g p} := by
  have cW : Continuous fun p : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) => p.1 := continuous_fst
  have cL : ∀ i, Continuous fun p : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) => p.2.1 i := fun i =>
    (continuous_apply i).comp (continuous_fst.comp continuous_snd)
  have cR : ∀ j, Continuous fun p : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) => p.2.2 j := fun j =>
    (continuous_apply j).comp (continuous_snd.comp continuous_snd)
  have e : {p : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) | InCBuffer mL mR R g p} =
      {p | |p.1| ≤ R} ∩ (⋂ i, {p | |p.2.1 i| ≤ R}) ∩ (⋂ j, {p | |p.2.2 j| ≤ R}) ∩
        (⋂ j : Fin nR, {p | mR ≤ (j : ℕ) → g ≤ p.2.2 j - p.1}) ∩
          ⋂ i : Fin nL, {p | mL ≤ (i : ℕ) → g ≤ p.1 - p.2.1 i} := by
    ext p
    simp only [InCBuffer, mem_ofPred_eq, mem_inter_iff, mem_iInter]
    tauto
  rw [e]
  refine ((((isClosed_le cW.abs continuous_const).inter
    (isClosed_iInter fun i => isClosed_le (cL i).abs continuous_const)).inter
    (isClosed_iInter fun j => isClosed_le (cR j).abs continuous_const)).inter
    (isClosed_iInter fun j => ?_)).inter (isClosed_iInter fun i => ?_)
  · by_cases hj : mR ≤ (j : ℕ)
    · simp only [hj, true_implies]
      exact isClosed_le continuous_const ((cR j).sub cW)
    · simp only [hj, false_implies]
      exact isClosed_univ
  · by_cases hi : mL ≤ (i : ℕ)
    · simp only [hi, true_implies]
      exact isClosed_le continuous_const (cW.sub (cL i))
    · simp only [hi, false_implies]
      exact isClosed_univ

theorem InBuffer.inCBuffer {mL mR : ℕ} {R g : ℝ} {p : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)}
    (hp : InBuffer mL mR R g p) : InCBuffer mL mR R g p :=
  ⟨⟨hp.1.1.le, fun i => (hp.1.2.1 i).le, fun j => (hp.1.2.2 j).le⟩,
    fun j hj => (hp.2.1 j hj).le, fun i hi => (hp.2.2 i hi).le⟩

/-- A state is **ordered**: left coordinates antitone below the driver, right coordinates monotone above it. -/
def IsOrderedState (p : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)) : Prop :=
  Antitone p.2.1 ∧ (∀ i, p.2.1 i ≤ p.1) ∧ (∀ j, p.1 ≤ p.2.2 j) ∧ Monotone p.2.2

theorem isClosed_setOf_isOrderedState :
    IsClosed {p : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) | IsOrderedState p} := by
  have cW : Continuous fun p : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) => p.1 := continuous_fst
  have cL : ∀ i, Continuous fun p : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) => p.2.1 i := fun i =>
    (continuous_apply i).comp (continuous_fst.comp continuous_snd)
  have cR : ∀ j, Continuous fun p : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) => p.2.2 j := fun j =>
    (continuous_apply j).comp (continuous_snd.comp continuous_snd)
  have e : {p : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) | IsOrderedState p} =
      (⋂ i, ⋂ i', {p | i ≤ i' → p.2.1 i' ≤ p.2.1 i}) ∩ (⋂ i, {p | p.2.1 i ≤ p.1}) ∩
        (⋂ j, {p | p.1 ≤ p.2.2 j}) ∩ ⋂ j, ⋂ j', {p | j ≤ j' → p.2.2 j ≤ p.2.2 j'} := by
    ext p
    simp only [IsOrderedState, Antitone, Monotone, mem_ofPred_eq, mem_inter_iff, mem_iInter]
    exact ⟨fun ⟨h1, h2, h3, h4⟩ => ⟨⟨⟨fun i i' h => h1 h, h2⟩, h3⟩, fun j j' h => h4 h⟩,
      fun ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ => ⟨fun i i' h => h1 i i' h, h2, h3, fun j j' h => h4 j j' h⟩⟩
  rw [e]
  refine (((isClosed_iInter fun i => isClosed_iInter fun i' => ?_).inter
    (isClosed_iInter fun i => isClosed_le (cL i) cW)).inter
    (isClosed_iInter fun j => isClosed_le cW (cR j))).inter
    (isClosed_iInter fun j => isClosed_iInter fun j' => ?_)
  · by_cases h : i ≤ i'
    · simp only [h, true_implies]
      exact isClosed_le (cL i') (cL i)
    · simp only [h, false_implies]
      exact isClosed_univ
  · by_cases h : j ≤ j'
    · simp only [h, true_implies]
      exact isClosed_le (cR j) (cR j')
    · simp only [h, false_implies]
      exact isClosed_univ

/-- The right contact group of an ordered state is an inner prefix, so its weight sum is at least `ε − 2`. -/
theorem sum_contactR_gt {mR : ℕ} {ε g : ℝ} (hε : 0 < ε) (hg : 0 < g) {ρR : Fin nR → ℝ}
    (hin : ∀ j : Fin nR, (j : ℕ) < mR → ε ≤ ∑ l ∈ univ.filter (fun l => l ≤ j), ρR l + 2)
    {w : ℝ} {v : Fin nR → ℝ} (hwv : ∀ j, w ≤ v j) (hmono : Monotone v)
    (hfar : ∀ j : Fin nR, mR ≤ (j : ℕ) → g ≤ v j - w) :
    -2 < ∑ j ∈ univ.filter (fun j => v j = w), ρR j := by
  by_cases hC : (univ.filter fun j => v j = w).Nonempty
  · set k := (univ.filter fun j => v j = w).max' hC
    have hk : v k = w := (Finset.mem_filter.1 ((univ.filter fun j => v j = w).max'_mem hC)).2
    have heq : univ.filter (fun j => v j = w) = univ.filter (fun l => l ≤ k) := by
      ext l
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hl
        exact (univ.filter fun j => v j = w).le_max' l (Finset.mem_filter.2 ⟨Finset.mem_univ _, hl⟩)
      · intro hl
        exact le_antisymm (hk ▸ hmono hl) (hwv l)
    have hkm : (k : ℕ) < mR := by
      by_contra hcon
      have := hfar k (not_lt.1 hcon)
      rw [hk, sub_self] at this
      linarith
    rw [heq]
    linarith [hin k hkm]
  · rw [Finset.not_nonempty_iff_eq_empty.1 hC, Finset.sum_empty]
    norm_num

/-- **No threshold in the closed buffer**: an ordered state in the closed buffer is not a continuation threshold for
a DS1 word (`ε > 0`, `g > 0`). -/
theorem not_threshold_of_inCBuffer {mL mR : ℕ} {Rw ε R g : ℝ} (hε : 0 < ε) (hg : 0 < g)
    {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (hw : IsDS1Word mL mR Rw ε xL xR ρL ρR) {p : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)}
    (hord : IsOrderedState p) (hp : InCBuffer mL mR R g p) :
    ¬ ForceWord.ThresholdCondition ρL ρR p.1 p.2.1 p.2.2 := by
  obtain ⟨-, -, -, hinL, hinR⟩ := hw
  obtain ⟨hanti, hLw, hwR, hmono⟩ := hord
  unfold ForceWord.ThresholdCondition
  push Not
  refine ⟨?_, sum_contactR_gt hε hg hinR hwR hmono hp.2.1⟩
  -- the left side, by reflection `x ↦ −x`
  have h := sum_contactR_gt (mR := mL) (w := -p.1) (v := fun i => -p.2.1 i) hε hg hinL
    (fun i => neg_le_neg (hLw i)) (fun i i' hii' => neg_le_neg (hanti hii'))
    (fun i hi => by have := hp.2.2 i hi; linarith)
  have e : (univ.filter fun i => -p.2.1 i = -p.1) = univ.filter fun i => p.2.1 i = p.1 := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, neg_inj]
  rwa [e] at h

end Buffer

/-! ### The driver is linear in the force coordinates -/

section Linear

variable {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin nR → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ}
  {τ : ℝ≥0∞}

/-- `ρ/(w − v) = −(ρ/2)·(2/(v − w))`, also when `v = w`. -/
theorem div_sub_eq_neg_half_mul (ρ w v : ℝ) : ρ / (w - v) = -(ρ / 2) * (2 / (v - w)) := by
  rcases eq_or_ne v w with h | h
  · subst h; simp
  · have h1 : v - w ≠ 0 := sub_ne_zero.2 h
    have h2 : w - v ≠ 0 := sub_ne_zero.2 (Ne.symm h)
    field_simp
    ring

/-- **The driver is linear in the force coordinates**: `w t = √a b t − ∑ (ρ/2)(v t − x)` before the time `τ`. -/
theorem w_eq_linear (h : Sec2.IsSLEPathUpTo a xL xR ρL ρR w vL vR b τ) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < τ) :
    w t = Real.sqrt a * b t - (∑ i, ρL i / 2 * (vL i t - xL i)) - ∑ j, ρR j / 2 * (vR j t - xR j) := by
  rw [h.w_eq ht]
  have hL : ∀ i, ∫ s in (0 : ℝ)..t, ρL i / (w s.toNNReal - vL i s.toNNReal) =
      -(ρL i / 2 * (vL i t - xL i)) := by
    intro i
    simp_rw [div_sub_eq_neg_half_mul (ρL i)]
    rw [intervalIntegral.integral_const_mul, h.vL_eq ht i]
    ring
  have hR : ∀ j, ∫ s in (0 : ℝ)..t, ρR j / (w s.toNNReal - vR j s.toNNReal) =
      -(ρR j / 2 * (vR j t - xR j)) := by
    intro j
    simp_rw [div_sub_eq_neg_half_mul (ρR j)]
    rw [intervalIntegral.integral_const_mul, h.vR_eq ht j]
    ring
  simp only [hL, hR, Finset.sum_neg_distrib]
  ring

end Linear

/-! ### A path in the closed buffer does not reach its lifetime -/

section Lifetime

variable {κ : ℝ} {nL nR : ℕ} {mL mR : ℕ} {Rw ε R g : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
  {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ}
  {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-- The state of a local integrated path before its time is ordered. -/
theorem isOrderedState_of_upTo (h : Sec2.IsSLEPathUpTo κ xL xR ρL ρR w vL vR b ζ) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < ζ) : IsOrderedState ((w t, fun i => vL i t, fun j => vR j t) :
      ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)) :=
  ⟨fun _ _ hii' => h.antitone_vL ht hii', fun i => h.vL_le_w ht i, fun j => h.w_le_vR ht j,
    fun _ _ hjj' => h.monotone_vR ht hjj'⟩

/-- **A path of a DS1 word that stays in the closed buffer does not reach its lifetime before `T`.** If the initial
state is in the closed buffer and every state before `ζ` and up to `T` is, then `T < ζ`: the force coordinates are
monotone and bounded, so at a finite lifetime the state would have a limit in the closed buffer, which is not a
continuation threshold (`not_threshold_of_inCBuffer`), contrary to the maximality of `ζ`. -/
theorem lt_lifetime_of_forall_inCBuffer (hε : 0 < ε) (hg : 0 < g)
    (hw : IsDS1Word mL mR Rw ε xL xR ρL ρR) (hP : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ)
    (hb : Continuous b) (h0 : InCBuffer mL mR R g ((0 : ℝ), xL, xR)) {T : ℝ≥0}
    (hK : ∀ s : ℝ≥0, s ≤ T → (s : ℝ≥0∞) < ζ →
      InCBuffer mL mR R g ((w s, fun i => vL i s, fun j => vR j s) : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ))) :
    (T : ℝ≥0∞) < ζ := by
  by_contra hcon
  push Not at hcon
  have hζfin : ζ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hcon
  set Z := ζ.toNNReal with hZdef
  have hZ : (Z : ℝ≥0∞) = ζ := ENNReal.coe_toNNReal hζfin
  have hup := hP.isSLEPathUpTo le_rfl
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hthr0, hthr⟩ := hP
  have hKs : ∀ s : ℝ≥0, (s : ℝ≥0∞) < ζ →
      InCBuffer mL mR R g ((w s, fun i => vL i s, fun j => vR j s) : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)) :=
    fun s hs => hK s (by exact_mod_cast (hs.le.trans hcon)) hs
  have hord0 : IsOrderedState (((0 : ℝ), xL, xR) : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)) :=
    ⟨hw.1.1, hw.1.2.1, hw.1.2.2.2, hw.1.2.2.1⟩
  rcases eq_or_ne Z 0 with hZ0 | hZ0
  · have : ζ = 0 := by rw [← hZ, hZ0, ENNReal.coe_zero]
    exact not_threshold_of_inCBuffer hε hg hw hord0 h0 (hthr0 this)
  have hpos : 0 < Z := pos_iff_ne_zero.2 hZ0
  have hltZ : ∀ s : ℝ≥0, s ∈ Iio Z → (s : ℝ≥0∞) < ζ := fun s hs => by
    rw [← hZ]; exact_mod_cast hs
  have : (𝓝[<] Z).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hpos⟩
  -- the right coordinates are nondecreasing and bounded
  have hR : ∀ j, Tendsto (vR j) (𝓝[<] Z) (𝓝 (sSup (vR j '' Iio Z))) := fun j =>
    MonotoneOn.tendsto_nhdsLT (fun s _ t ht hst => hup.le_vR_of_le hst (hltZ t ht) j)
      ⟨R, by rintro _ ⟨s, hs, rfl⟩; exact (abs_le.1 ((hKs s (hltZ s hs)).1.2.2 j)).2⟩
  have hL : ∀ i, Tendsto (vL i) (𝓝[<] Z) (𝓝 (sInf (vL i '' Iio Z))) := fun i =>
    AntitoneOn.tendsto_nhdsLT (fun s _ t ht hst => hup.vL_le_of_le hst (hltZ t ht) i)
      ⟨-R, by rintro _ ⟨s, hs, rfl⟩; exact (abs_le.1 ((hKs s (hltZ s hs)).1.2.1 i)).1⟩
  set vR₀ : Fin nR → ℝ := fun j => sSup (vR j '' Iio Z)
  set vL₀ : Fin nL → ℝ := fun i => sInf (vL i '' Iio Z)
  set w₀ : ℝ := Real.sqrt κ * b Z - (∑ i, ρL i / 2 * (vL₀ i - xL i)) - ∑ j, ρR j / 2 * (vR₀ j - xR j)
  have hb' : Tendsto b (𝓝[<] Z) (𝓝 (b Z)) := hb.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hlin : Tendsto (fun t => Real.sqrt κ * b t - (∑ i, ρL i / 2 * (vL i t - xL i)) -
      ∑ j, ρR j / 2 * (vR j t - xR j)) (𝓝[<] Z) (𝓝 w₀) := by
    refine ((hb'.const_mul _).sub ?_).sub ?_
    · exact tendsto_finsetSum _ fun i _ => ((hL i).sub tendsto_const_nhds).const_mul _
    · exact tendsto_finsetSum _ fun j _ => ((hR j).sub tendsto_const_nhds).const_mul _
  have hW : Tendsto w (𝓝[<] Z) (𝓝 w₀) := by
    refine hlin.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (w_eq_linear hup (hltZ t ht)).symm
  have hlim : Tendsto (fun t => (w t, fun i => vL i t, fun i => vR i t)) (𝓝[<] Z)
      (𝓝 (w₀, vL₀, vR₀)) :=
    hW.prodMk_nhds ((tendsto_pi_nhds.2 hL).prodMk_nhds (tendsto_pi_nhds.2 hR))
  have hev : ∀ᶠ t in 𝓝[<] Z, (w t, fun i => vL i t, fun i => vR i t) ∈
      {p : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) | InCBuffer mL mR R g p ∧ IsOrderedState p} := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact ⟨hKs t (hltZ t ht), isOrderedState_of_upTo hup (hltZ t ht)⟩
  obtain ⟨hmem, hord⟩ := (((isClosed_setOf_inCBuffer mL mR R g).inter
    isClosed_setOf_isOrderedState).mem_of_tendsto hlim hev : (w₀, vL₀, vR₀) ∈ _)
  exact not_threshold_of_inCBuffer hε hg hw hord hmem (hthr Z hpos hZ w₀ vL₀ vR₀ hlim)

end Lifetime

/-! ### The exit time and the stopped path -/

section Exit

variable {E : Type*} [TopologicalSpace E] {K : Set E} {T : ℝ≥0} {st : ℝ≥0 → E} {ζ : ℝ≥0∞}

/-- The **exit time** before the horizon `T`: the first time `s ≤ T` at which the path is dead (`s ≥ ζ`) or
outside `K` (`T` if there is none). -/
def exitTime (K : Set E) (T : ℝ≥0) (st : ℝ≥0 → E) (ζ : ℝ≥0∞) : ℝ≥0 :=
  sInf {s : ℝ≥0 | s = T ∨ ¬ ((s : ℝ≥0∞) < ζ ∧ st s ∈ K)}

omit [TopologicalSpace E] in
theorem exitTime_le : exitTime K T st ζ ≤ T :=
  csInf_le (OrderBot.bddBelow _) (Or.inl rfl)

omit [TopologicalSpace E] in
theorem lt_and_mem_of_lt_exitTime {s : ℝ≥0} (hs : s < exitTime K T st ζ) :
    (s : ℝ≥0∞) < ζ ∧ st s ∈ K := by
  by_contra h
  exact (not_le.2 hs) (csInf_le (OrderBot.bddBelow _) (Or.inr h))

omit [TopologicalSpace E] in
/-- The exit time is before the lifetime when staying in `K` up to `T` forces `T < ζ`. -/
theorem exitTime_lt_lifetime
    (H : (∀ s : ℝ≥0, s ≤ T → (s : ℝ≥0∞) < ζ → st s ∈ K) → (T : ℝ≥0∞) < ζ) :
    (exitTime K T st ζ : ℝ≥0∞) < ζ := by
  by_contra hcon
  push Not at hcon
  have hT : (T : ℝ≥0∞) < ζ := H fun s _ hsζ =>
    (lt_and_mem_of_lt_exitTime (by exact_mod_cast hsζ.trans_le hcon)).2
  exact absurd (hT.trans_le hcon) (not_lt.2 (by exact_mod_cast exitTime_le))

theorem continuousAt_of_lt (hc : ContinuousOn st {s | (s : ℝ≥0∞) < ζ}) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) :
    ContinuousAt st t :=
  hc.continuousAt ((isOpen_lt ENNReal.continuous_coe continuous_const).mem_nhds ht)

/-- The state at the exit time is in the closed set `K` (when it starts in `K`). -/
theorem mem_exitTime (hK : IsClosed K) (hc : ContinuousOn st {s | (s : ℝ≥0∞) < ζ})
    (hτ : (exitTime K T st ζ : ℝ≥0∞) < ζ) (h0 : st 0 ∈ K) : st (exitTime K T st ζ) ∈ K := by
  set τ := exitTime K T st ζ
  rcases eq_or_ne τ 0 with h | h
  · rw [h]; exact h0
  · have : (𝓝[<] τ).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, pos_iff_ne_zero.2 h⟩
    exact hK.mem_of_tendsto ((continuousAt_of_lt hc hτ).tendsto.mono_left nhdsWithin_le_nhds)
      (eventually_nhdsWithin_of_forall (s := Iio τ) fun s hs => (lt_and_mem_of_lt_exitTime hs).2)

/-- **At an exit before the horizon the state is not interior to `K`.** -/
theorem not_mem_interior_exitTime (hc : ContinuousOn st {s | (s : ℝ≥0∞) < ζ})
    (hτ : (exitTime K T st ζ : ℝ≥0∞) < ζ) (hT : exitTime K T st ζ < T) :
    st (exitTime K T st ζ) ∉ interior K := by
  set τ := exitTime K T st ζ with hτdef
  intro hmem
  have e1 : ∀ᶠ s : ℝ≥0 in 𝓝 τ, (s : ℝ≥0∞) < ζ :=
    (isOpen_lt ENNReal.continuous_coe continuous_const).mem_nhds hτ
  have e2 : ∀ᶠ s : ℝ≥0 in 𝓝 τ, st s ∈ K :=
    Filter.mem_of_superset ((continuousAt_of_lt hc hτ).preimage_mem_nhds
      (isOpen_interior.mem_nhds hmem)) fun s (hs : st s ∈ interior K) => (interior_subset (s := K) hs)
  have e3 : ∀ᶠ s : ℝ≥0 in 𝓝 τ, s < T := gt_mem_nhds hT
  have hev : ∀ᶠ s : ℝ≥0 in 𝓝 τ, ((s : ℝ≥0∞) < ζ ∧ st s ∈ K) ∧ s < T := (e1.and e2).and e3
  obtain ⟨u, hu, hsub⟩ := (mem_nhdsGE_iff_exists_Ico_subset' (lt_add_one τ)).1
    (hev.filter_mono nhdsWithin_le_nhds)
  have hle : u ≤ τ := le_csInf ⟨T, Or.inl rfl⟩ fun s hs => by
    by_contra hsu
    push Not at hsu
    rcases lt_or_ge s τ with h1 | h1
    · rcases hs with hsT | hbad
      · exact absurd (hsT ▸ h1) (not_lt.2 exitTime_le)
      · exact hbad (lt_and_mem_of_lt_exitTime h1)
    · have hgood := hsub ⟨h1, hsu⟩
      rcases hs with hsT | hbad
      · exact hgood.2.ne hsT
      · exact hbad hgood.1
  exact absurd hu (not_lt.2 hle)

open Classical in
/-- The **stopped path**: the path stopped at its exit time, as a continuous path on `[0, T]` (the constant `x₀`
when the path is not continuous before its lifetime or the exit is not before the lifetime). -/
def stopPath (K : Set E) (T : ℝ≥0) (st : ℝ≥0 → E) (ζ : ℝ≥0∞) (x₀ : E) : C(Set.Icc (0 : ℝ≥0) T, E) :=
  if h : ContinuousOn st {s | (s : ℝ≥0∞) < ζ} ∧ (exitTime K T st ζ : ℝ≥0∞) < ζ then
    ⟨fun t => st (min (t : ℝ≥0) (exitTime K T st ζ)),
      h.1.comp_continuous (continuous_subtype_val.min continuous_const) fun t =>
        lt_of_le_of_lt (by exact_mod_cast min_le_right _ _) h.2⟩
  else ContinuousMap.const _ x₀

theorem stopPath_apply (h : ContinuousOn st {s | (s : ℝ≥0∞) < ζ} ∧ (exitTime K T st ζ : ℝ≥0∞) < ζ)
    (x₀ : E) (t : Set.Icc (0 : ℝ≥0) T) :
    stopPath K T st ζ x₀ t = st (min (t : ℝ≥0) (exitTime K T st ζ)) := by
  rw [stopPath, dite_eq_left_of_eq_true (eq_true h)]
  rfl

theorem stopPath_apply_of_le (h : ContinuousOn st {s | (s : ℝ≥0∞) < ζ} ∧ (exitTime K T st ζ : ℝ≥0∞) < ζ)
    (x₀ : E) {t : Set.Icc (0 : ℝ≥0) T} (ht : (t : ℝ≥0) ≤ exitTime K T st ζ) :
    stopPath K T st ζ x₀ t = st t := by
  rw [stopPath_apply h, min_eq_left ht]

/-- A stopped path staying interior to `K` up to `t` has not exited before `t`. -/
theorem le_exitTime_of_forall_mem
    (h : ContinuousOn st {s | (s : ℝ≥0∞) < ζ} ∧ (exitTime K T st ζ : ℝ≥0∞) < ζ) (x₀ : E) {U : Set E}
    (hU : U ⊆ interior K) {t : Set.Icc (0 : ℝ≥0) T}
    (hf : ∀ u : Set.Icc (0 : ℝ≥0) T, u ≤ t → stopPath K T st ζ x₀ u ∈ U) :
    (t : ℝ≥0) ≤ exitTime K T st ζ := by
  by_contra hcon
  push Not at hcon
  set τ := exitTime K T st ζ
  have hτT : τ < T := hcon.trans_le t.2.2
  have hu := hf ⟨τ, zero_le, exitTime_le⟩ (Subtype.mk_le_mk.2 hcon.le)
  rw [stopPath_apply h, min_self] at hu
  exact not_mem_interior_exitTime h.1 h.2 hτT (hU hu)

end Exit

section ExitMetric

variable {E : Type*} [MetricSpace E] {K : Set E} {T : ℝ≥0} {st : ℝ≥0 → E} {ζ : ℝ≥0∞}

/-- **The reach event in terms of the stopped path**: for a buffer `B` interior to `K`, the path reaches `O` before
`T` while staying in `B` exactly when the stopped path is in the reach set. -/
theorem mem_reachSet_stopPath_iff
    (h : ContinuousOn st {s | (s : ℝ≥0∞) < ζ} ∧ (exitTime K T st ζ : ℝ≥0∞) < ζ) (x₀ : E) {O B : Set E}
    (hB : B ⊆ interior K) :
    stopPath K T st ζ x₀ ∈ reachSet T O B ↔
      ∃ t : ℝ≥0, t < T ∧ (t : ℝ≥0∞) < ζ ∧ st t ∈ O ∧ ∀ u ≤ t, st u ∈ B := by
  set τ := exitTime K T st ζ
  constructor
  · rintro ⟨t, htT, htO, htB⟩
    have hle : (t : ℝ≥0) ≤ τ := le_exitTime_of_forall_mem h x₀ hB htB
    refine ⟨t, htT, lt_of_le_of_lt (by exact_mod_cast hle) h.2, ?_, fun u hu => ?_⟩
    · rwa [stopPath_apply_of_le h x₀ hle] at htO
    · have hu' := htB ⟨u, zero_le, hu.trans t.2.2⟩ (Subtype.mk_le_mk.2 hu)
      rwa [stopPath_apply_of_le h x₀ (hu.trans hle)] at hu'
  · rintro ⟨t, htT, -, htO, htB⟩
    have hle : t < τ := by
      by_contra hcon
      push Not at hcon
      have hτT : τ < T := lt_of_le_of_lt hcon htT
      exact not_mem_interior_exitTime h.1 h.2 hτT (hB (htB τ hcon))
    refine ⟨⟨t, zero_le, htT.le⟩, htT, ?_, fun u hu => ?_⟩
    · rw [stopPath_apply_of_le h x₀ (show ((⟨t, zero_le, htT.le⟩ : Set.Icc (0 : ℝ≥0) T) : ℝ≥0) ≤ τ
        from hle.le)]
      exact htO
    · have hu' : (u : ℝ≥0) ≤ t := hu
      rw [stopPath_apply_of_le h x₀ (hu'.trans hle.le)]
      exact htB u hu'

end ExitMetric

end DSReach

end Supp12

end InteractingSLE
