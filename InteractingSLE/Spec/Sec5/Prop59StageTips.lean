/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop59StageExp
import InteractingSLE.Spec.Sec5.Prop59TipsRoot

/-!
# Proposition 5.9's alternating construction: perpetual success, unbounded capacity, unbounded node images

Packet PROVE-PROP59T2. Specification §5.2, proof of Proposition 5.9, pp. 145–148:

> Fix `ε > 0` and take, for instance, `ε_j = ε 2^{−j}`. Iterating the preceding construction gives
> `P[every stage succeeds | initial reveal] ≥ 1 − Σ ε_j = 1 − ε`. […] on perpetual success infinitely many even stages
> have capacity increment at least one, and total capacity tends to infinity. Since `hcap(K_s) = 2s`, the
> diameter-capacity bound gives `diam(K_s) ≥ c √(2s)`. […] The ranges of the successful finite prefixes are therefore
> unbounded as well.

* `recRule`: the rule chosen stage by stage (each grid index depends only on the earlier ones);
* `tendsto_measure_fail`: the failure probability of a stage tends to `0` as the grid refines (`ae_eventually_succ`);
* **`ae_not_isBounded_of_stageLaw`**: from the stage law (`Prop59StageLawStatement`) and the structure of the
  realized construction (`IsStageSystem`), almost surely on the initial event the node images are unbounded;
* **`tip0UnboundedStatement_of_stageLaw`**, **`tipUnboundedStatement_of_stageLaw`**: PROVE-PROP59T's
  `Tip0UnboundedStatement` and `TipUnboundedStatement`, for node families whose images in `ψ_r` are the node images of a
  stage system obeying the stage law at every positive rational `r`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)

namespace InteractingSLE

namespace Sec5

namespace Prop59Stage

/-! ### The rule chosen stage by stage -/

/-- **The rule chosen stage by stage**: the index at stage `j` is `pick` applied to the rule truncated below `j`. -/
def recRule (pick : (ℕ → ℕ) → ℕ → ℕ) (j : ℕ) : ℕ :=
  pick (fun i => if _h : i < j then recRule pick i else 0) j
termination_by j
decreasing_by assumption

theorem recRule_eq (pick : (ℕ → ℕ) → ℕ → ℕ) (j : ℕ) :
    recRule pick j = pick (fun i => if i < j then recRule pick i else 0) j := by
  rw [recRule]; simp only [dite_eq_ite]

section Main

variable {κ : ℝ} {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {nL₀ nR₀ : ℕ} {hnL : 0 < nL₀}
  {hnR : 0 < nR₀} {Q : Set ℝ≥0} {δ : ℕ → ℝ≥0} {G : ℕ → ℕ → ℝ≥0} {sys : StageSys Ω nL₀ nR₀} {C : Ω → Set ℂ}
  {ρL₀ : Fin nL₀ → ℝ} {ρR₀ : Fin nR₀ → ℝ}

/-- Every success event is measurable. -/
theorem measurableSet_succSet (hS : IsStageSystem P hnL hnR Q δ G sys C) (r : ℕ → ℕ) (j n : ℕ) :
    MeasurableSet (succSet G hnL hnR j (sys r j) n) := by
  set r' : ℕ → ℕ := fun i => if i < j then r i else n with hr'
  have hcoh : sys r' j = sys r j := hS.coh r' r j fun i hi => by simp only [hr', hi, ↓reduceIte]
  have h := hS.past_le r' (j + 1) _ (hS.succ_meas r' j).1
  rw [hcoh] at h
  simpa only [hr', lt_irrefl, ↓reduceIte] using h

/-- **The failure probability of a stage tends to `0` as the grid refines.** -/
theorem tendsto_measure_fail [IsProbabilityMeasure P] (hκ : 0 < κ) (hκ4 : κ < 4)
    (hL : Prop59StageLawStatement κ P ρL₀ ρR₀ sys) (hS : IsStageSystem P hnL hnR Q δ G sys C)
    (hwL : ∀ j, Even j → IsStageWordN κ (stageρL κ ρL₀ j) (stageρR κ ρR₀ j))
    (hwR : ∀ j, ¬ Even j → IsStageWordN κ (stageρR κ ρR₀ j) (stageρL κ ρL₀ j)) (r : ℕ → ℕ) (j : ℕ) :
    Tendsto (fun n => P ((sys r j).R \ succSet G hnL hnR j (sys r j) n)) atTop (𝓝 0) := by
  set F : ℕ → Set Ω := fun n => (sys r j).R \ succSet G hnL hnR j (sys r j) n with hF
  have hRm : MeasurableSet (sys r j).R := hS.past_le r j _ (hS.R_meas r j)
  have hFm : ∀ n, MeasurableSet (F n) := fun n => hRm.diff (measurableSet_succSet hS r j n)
  set U : ℕ → Set Ω := fun n => ⋃ m ≥ n, F m with hU
  have hUanti : Antitone U := fun a b hab => biUnion_subset_biUnion_left fun m hm => le_trans hab hm
  have hUm : ∀ n, MeasurableSet (U n) := fun n => MeasurableSet.biUnion (to_countable _) fun m _ => hFm m
  have hlim := tendsto_measure_iInter_atTop (μ := P) (fun n => (hUm n).nullMeasurableSet) hUanti
    ⟨0, measure_ne_top _ _⟩
  have hnull : P (⋂ n, U n) = 0 := by
    refine measure_mono_null (fun ω hω => ?_) (ae_iff.1 (ae_eventually_succ hκ hκ4 hL hS hwL hwR r j))
    simp only [mem_iInter, hU, mem_iUnion, hF, Set.mem_sdiff, exists_prop] at hω
    simp only [mem_ofPred_eq, not_imp, not_eventually]
    obtain ⟨m, -, hR, -⟩ := hω 0
    exact ⟨hR, frequently_atTop.2 fun n => by
      obtain ⟨m', hm', -, hns⟩ := hω n; exact ⟨m', hm', hns⟩⟩
  rw [hnull] at hlim
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => zero_le)
    fun n => measure_mono fun ω hω => mem_iUnion₂.2 ⟨n, le_rfl, hω⟩

/-- **The alternating construction gives unbounded node images** (proof of Proposition 5.9, pp. 145–148): if the
stage law holds and the realized construction has the structure `IsStageSystem`, then almost surely on the initial
event the images of the light cone's nodes are unbounded. For `ε > 0` the rule is chosen stage by stage with failure
probabilities `ε 2^{−(j+1)}`; the union bound gives perpetual success with probability `≥ 1 − ε`; Lemma 5.10 at the
even stages and the iterated conditional estimate give infinitely many unit switching times; the realized prefixes
then have unbounded capacity, hence (GB9's capacity bound `2t ≤ 3R²`) unbounded traces inside the closure of the node
images. -/
theorem ae_not_isBounded_of_stageLaw [IsProbabilityMeasure P] (hκ : 0 < κ) (hκ4 : κ < 4)
    (hL : Prop59StageLawStatement κ P ρL₀ ρR₀ sys) (hS : IsStageSystem P hnL hnR Q δ G sys C)
    (hwL : ∀ j, Even j → IsStageWordN κ (stageρL κ ρL₀ j) (stageρR κ ρR₀ j))
    (hwR : ∀ j, ¬ Even j → IsStageWordN κ (stageρR κ ρR₀ j) (stageρL κ ρL₀ j)) (r₀ : ℕ → ℕ) :
    ∀ᵐ ω ∂P, ω ∈ (sys r₀ 0).R → ¬ Bornology.IsBounded (C ω) := by
  obtain ⟨p₀, hp₀, hp₀1, hprem⟩ := exists_compPremise_unit hκ hκ4 ρL₀ ρR₀
  have hp₀r : 0 < p₀.toReal := ENNReal.toReal_pos hp₀.ne' (ne_top_of_le_ne_top ENNReal.one_ne_top hp₀1)
  have hp₀r1 : p₀.toReal ≤ 1 := by simpa using ENNReal.toReal_mono ENNReal.one_ne_top hp₀1
  set Bad : Set Ω := {ω | ω ∈ (sys r₀ 0).R ∧ Bornology.IsBounded (C ω)} with hBad
  suffices hallε : ∀ ε : ℝ≥0, 0 < ε → P Bad ≤ ε by
    rw [ae_iff]
    have h0 : P Bad = 0 := le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ => by
      rw [zero_add]; exact hallε ε hε) zero_le
    refine measure_mono_null (fun ω hω => ?_) h0
    simp only [mem_ofPred_eq, not_imp, not_not] at hω
    exact hω
  intro ε hε
  -- the failure budget
  set e : ℕ → ℝ≥0∞ := fun j => (ε : ℝ≥0∞) * 2⁻¹ ^ (j + 1) with he
  have he0 : ∀ j, 0 < e j := fun j => ENNReal.mul_pos (by exact_mod_cast hε.ne') (by simp)
  have hesum : ∑' j, e j = ε := by
    rw [ENNReal.tsum_mul_left]
    have : ∑' j : ℕ, (2⁻¹ : ℝ≥0∞) ^ (j + 1) = 1 := by
      simp_rw [pow_succ]
      rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv,
        ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]
    rw [this, mul_one]
  have hex : ∀ (r : ℕ → ℕ) (j : ℕ), ∃ n, P ((sys r j).R \ succSet G hnL hnR j (sys r j) n) ≤ e j := fun r j =>
    ((tendsto_measure_fail hκ hκ4 hL hS hwL hwR r j).eventually (ge_mem_nhds (he0 j))).exists
  classical
  set rs : ℕ → ℕ := recRule fun r j => Nat.find (hex r j) with hrs
  have htrunc : ∀ j, sys rs j = sys (fun i => if i < j then rs i else 0) j := fun j =>
    hS.coh _ _ j fun i hi => by simp only [hi, ↓reduceIte]
  have hfail : ∀ j, P ((sys rs j).R \ succSet G hnL hnR j (sys rs j) (rs j)) ≤ e j := by
    intro j
    have h1 : rs j = Nat.find (hex (fun i => if i < j then rs i else 0) j) := by rw [hrs, recRule_eq]
    rw [h1, htrunc j]
    exact Nat.find_spec (hex _ j)
  have hR0 : (sys rs 0).R = (sys r₀ 0).R := by rw [hS.coh rs r₀ 0 fun i hi => absurd hi (Nat.not_lt_zero i)]
  -- perpetual success with probability at least `1 − ε`
  have hunion : (sys rs 0).R \ ⋂ j, (sys rs j).R ⊆ ⋃ j, ((sys rs j).R \ succSet G hnL hnR j (sys rs j) (rs j)) := by
    intro ω ⟨h0, hall⟩
    simp only [mem_iInter, not_forall] at hall
    have hk := Nat.find_spec hall
    obtain ⟨k, hk'⟩ : ∃ k, Nat.find hall = k + 1 := by
      rcases Nat.eq_zero_or_pos (Nat.find hall) with h | h
      · exact absurd (h ▸ h0) hk
      · exact ⟨Nat.find hall - 1, by omega⟩
    have hRk : ω ∈ (sys rs k).R := by
      by_contra hc; exact absurd (Nat.find_min' hall hc) (by omega)
    rw [hk', hS.R_succ] at hk
    exact mem_iUnion.2 ⟨k, hRk, fun hs => hk ⟨hRk, hs⟩⟩
  have hP1 : P ((sys rs 0).R \ ⋂ j, (sys rs j).R) ≤ ε :=
    (measure_mono hunion).trans ((measure_iUnion_le _).trans ((ENNReal.tsum_le_tsum hfail).trans hesum.le))
  -- infinitely many unit switching times
  set D : ℕ → ℕ := fun k => 2 * k + 1 + 2 with hD
  have hDodd : ∀ k, ¬ Even (2 * k + 1) := fun k => Nat.not_even_iff_odd.2 (odd_two_mul_add_one k)
  have hpm : Monotone fun j => (sys rs j).past := monotone_nat_of_le_succ fun j => hS.past_mono rs j
  set 𝓖 : ℕ → MeasurableSpace Ω := fun k => (sys rs (D k)).past with h𝓖
  have h𝓖m : Monotone 𝓖 := fun a b hab => hpm (by simp only [hD]; omega)
  set U : ℕ → Set Ω := fun k => {ω | ω ∈ succSet G hnL hnR (D k) (sys rs (D k)) (rs (D k)) ∧
    1 ≤ swT G hnL hnR (D k) (sys rs (D k)) (rs (D k)) ω} with hU
  set F : ℕ → Set Ω := fun k => ((sys rs (D k)).R ∩ succSet G hnL hnR (D k) (sys rs (D k)) (rs (D k))) \ U k
    with hF
  set Gs : ℕ → Set Ω := fun k => ((sys rs (D k)).R)ᶜ ∪ ((sys rs (D k)).R \
    succSet G hnL hnR (D k) (sys rs (D k)) (rs (D k))) ∪ U k with hGs
  have hFm : ∀ k, MeasurableSet[𝓖 (k + 1)] (F k) := fun k => by
    have hle : (sys rs (D k + 1)).past ≤ 𝓖 (k + 1) := hpm (by simp only [hD]; omega)
    exact hle _ (((hS.past_mono rs (D k)) _ (hS.R_meas rs (D k))).inter (hS.succ_meas rs (D k)).1 |>.diff
      (hS.succ_meas rs (D k)).2)
  have hGF : ∀ k, Disjoint (Gs k) (F k) := fun k => Set.disjoint_left.2 fun ω hG hF' => by
    rcases hG with (h | h) | h
    · exact h hF'.1.1
    · exact h.2 hF'.1.2
    · exact hF'.2 h
  have hlow : ∀ k A, MeasurableSet[𝓖 k] A → p₀.toReal * P.real A ≤ P.real (A ∩ Gs k) := fun k A hA =>
    le_measureReal_unit hL hS hp₀1 hprem rs (hDodd k) hA
  have hnullF : P (⋃ m, ⋂ k ≥ m, F k) = 0 :=
    Supp8.GB9Cap.measure_liminf_eq_zero_of_lower h𝓖m (fun k => hS.past_le rs _) hFm hGF hp₀r hp₀r1 hlow
  -- the chain on every successful prefix
  have hchain := ae_all_iff.2 fun j => hS.chain rs j
  have hsub : Bad ⊆ ((sys rs 0).R \ ⋂ j, (sys rs j).R) ∪ (⋃ m, ⋂ k ≥ m, F k) ∪
      {ω | ¬ ∀ j, ω ∈ (sys rs (j + 1)).R → ∃ (W' : ℝ → ℝ) (η : ℝ → ℂ) (T : ℝ), Continuous W' ∧ W' 0 = 0 ∧
        IsLoewnerTraceLT W' T η ∧ capT G hnL hnR sys rs (j + 1) ω < T ∧
        η '' Icc 0 (capT G hnL hnR sys rs (j + 1) ω) ⊆ closure (C ω)} := by
    rintro ω ⟨hω0, hbdd⟩
    by_contra hcon
    have h1 : ω ∉ (sys rs 0).R \ ⋂ j, (sys rs j).R := fun h => hcon (Or.inl (Or.inl h))
    have h2 : ω ∉ ⋃ m, ⋂ k ≥ m, F k := fun h => hcon (Or.inl (Or.inr h))
    have hch : ∀ j, ω ∈ (sys rs (j + 1)).R → ∃ (W' : ℝ → ℝ) (η : ℝ → ℂ) (T : ℝ), Continuous W' ∧ W' 0 = 0 ∧
        IsLoewnerTraceLT W' T η ∧ capT G hnL hnR sys rs (j + 1) ω < T ∧
        η '' Icc 0 (capT G hnL hnR sys rs (j + 1) ω) ⊆ closure (C ω) := by
      by_contra h; exact hcon (Or.inr h)
    have hallR : ∀ j, ω ∈ (sys rs j).R := fun j => by
      by_contra h
      exact h1 ⟨by rw [hR0]; exact hω0, fun hm => h (mem_iInter.1 hm j)⟩
    have hF' : ∀ m, ∃ k ≥ m, ω ∉ F k := by
      intro m
      by_contra h
      push Not at h
      exact h2 (mem_iUnion.2 ⟨m, mem_iInter₂.2 h⟩)
    -- frequently a unit switch
    have hfreq : ∃ᶠ k in atTop, ω ∈ U k := by
      rw [frequently_atTop]
      intro m
      obtain ⟨k, hkm, hk⟩ := hF' m
      refine ⟨k, hkm, by_contra fun hU' => hk ⟨⟨hallR _, ?_⟩, hU'⟩⟩
      have := hallR (D k + 1); rw [hS.R_succ] at this; exact this.2
    have hmono : Monotone fun m => capT G hnL hnR sys rs m ω :=
      monotone_nat_of_le_succ fun m => by
        simp only [capT, Finset.sum_range_succ]; exact le_add_of_nonneg_right (NNReal.coe_nonneg _)
    have hinc : ∃ᶠ m in atTop, capT G hnL hnR sys rs m ω + 1 ≤ capT G hnL hnR sys rs (m + 1) ω := by
      rw [frequently_atTop] at hfreq ⊢
      intro a
      obtain ⟨k, hka, hk⟩ := hfreq a
      refine ⟨D k, by simp only [hD]; omega, ?_⟩
      simp only [capT, Finset.sum_range_succ]
      have : (1 : ℝ) ≤ (swT G hnL hnR (D k) (sys rs (D k)) (rs (D k)) ω : ℝ) := by exact_mod_cast hk.2
      linarith
    have htend := Theorem14.GW2TipSkel.tendsto_atTop_of_frequently_add_one_le hmono hinc
    obtain ⟨R', hR', hball⟩ := hbdd.subset_closedBall_lt 0 0
    have hcl : closure (C ω) ⊆ Metric.closedBall 0 R' := Metric.isClosed_closedBall.closure_subset_iff.2 hball
    obtain ⟨j, hj⟩ := (htend.eventually (eventually_gt_atTop (3 * R' ^ 2))).exists_forall_of_atTop
    obtain ⟨W', η, T, hW', hW0, hη, hT, himg⟩ := hch j (hallR (j + 1))
    have hcap0 : 0 ≤ capT G hnL hnR sys rs (j + 1) ω :=
      Finset.sum_nonneg fun i _ => NNReal.coe_nonneg _
    have := Supp8.GB9Cap.two_mul_le_of_image_subset_closedBall hη hW' hW0 hcap0 hT hR' (himg.trans hcl)
    have := hj (j + 1) (by omega)
    nlinarith
  have hchnull : P {ω | ¬ ∀ j, ω ∈ (sys rs (j + 1)).R → ∃ (W' : ℝ → ℝ) (η : ℝ → ℂ) (T : ℝ), Continuous W' ∧
      W' 0 = 0 ∧ IsLoewnerTraceLT W' T η ∧ capT G hnL hnR sys rs (j + 1) ω < T ∧
        η '' Icc 0 (capT G hnL hnR sys rs (j + 1) ω) ⊆ closure (C ω)} = 0 := ae_iff.1 hchain
  calc P Bad ≤ P ((sys rs 0).R \ ⋂ j, (sys rs j).R) + P (⋃ m, ⋂ k ≥ m, F k) + P {ω | ¬ ∀ j,
        ω ∈ (sys rs (j + 1)).R → ∃ (W' : ℝ → ℝ) (η : ℝ → ℂ) (T : ℝ), Continuous W' ∧ W' 0 = 0 ∧
          IsLoewnerTraceLT W' T η ∧ capT G hnL hnR sys rs (j + 1) ω < T ∧
          η '' Icc 0 (capT G hnL hnR sys rs (j + 1) ω) ⊆ closure (C ω)} :=
        (measure_mono hsub).trans ((measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl))
    _ ≤ ε := by rw [hnullF, hchnull, add_zero, add_zero]; exact hP1

end Main

/-! ### PROVE-PROP59T's unboundedness statements -/

section Tips

open Prop59Tips

variable {κ : ℝ} {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {nL₀ nR₀ : ℚ → ℕ}
  {hnL : ∀ r, 0 < nL₀ r} {hnR : ∀ r, 0 < nR₀ r} {ρL₀ : (r : ℚ) → Fin (nL₀ r) → ℝ}
  {ρR₀ : (r : ℚ) → Fin (nR₀ r) → ℝ} {Q : Set ℝ≥0} {δ : ℚ → ℕ → ℝ≥0} {G : ℚ → ℕ → ℕ → ℝ≥0}
  {sys : (r : ℚ) → StageSys Ω (nL₀ r) (nR₀ r)}

/-- **`Tip0UnboundedStatement` from the stage law** (root `0`; proof of Proposition 5.9, pp. 143–148): if at every
positive rational counterflow time `r` the alternating construction in the chart `ψ_r` is a stage system whose node
images are the `ψ_r`-images of the family `{z n}` in `ℍ ∖ K_r`, which obeys the stage law and is reached almost surely
(no initial prefix), and the stage words are stage words, then `Tip0UnboundedStatement P W z` holds. -/
theorem tip0UnboundedStatement_of_stageLaw [IsProbabilityMeasure P] (hκ : 0 < κ) (hκ4 : κ < 4) {W : ℝ≥0 → Ω → ℝ}
    {z : ℕ → Ω → ℂ} (hL : ∀ r : ℚ, 0 < r → Prop59StageLawStatement κ P (ρL₀ r) (ρR₀ r) (sys r))
    (hS : ∀ r : ℚ, 0 < r → IsStageSystem P (hnL r) (hnR r) Q (δ r) (G r) (sys r) fun ω =>
      (ownComponentChart (fun s : ℝ => W s.toNNReal ω) (r : ℝ).toNNReal).1 ''
        (range (fun n => z n ω) ∩ (H \ fwdHull (fun s : ℝ => W s.toNNReal ω) (r : ℝ).toNNReal)))
    (hwL : ∀ r : ℚ, 0 < r → ∀ j, Even j → IsStageWordN κ (stageρL κ (ρL₀ r) j) (stageρR κ (ρR₀ r) j))
    (hwR : ∀ r : ℚ, 0 < r → ∀ j, ¬ Even j → IsStageWordN κ (stageρR κ (ρR₀ r) j) (stageρL κ (ρL₀ r) j))
    (hR0 : ∀ r : ℚ, 0 < r → ∀ᵐ ω ∂P, ω ∈ (sys r (fun _ => 0) 0).R) :
    Tip0UnboundedStatement P W z := by
  intro r hr
  filter_upwards [ae_not_isBounded_of_stageLaw hκ hκ4 (hL r hr) (hS r hr) (hwL r hr) (hwR r hr) (fun _ => 0),
    hR0 r hr] with ω h1 h2
  exact h1 h2

/-- **`TipUnboundedStatement` from the stage law** (root `z`, the terminal point of an allowed stopped prefix;
pp. 143–148): as `tip0UnboundedStatement_of_stageLaw`, with node images the `ψ_r`-images of the descendant portions
`S` in `ℍ ∖ K_r`, the construction being reached almost surely on `{r < T_z}` ("work on the event that `r` precedes its
first hit of the initial stopped flow-line exploration"). -/
theorem tipUnboundedStatement_of_stageLaw [IsProbabilityMeasure P] (hκ : 0 < κ) (hκ4 : κ < 4) {W : ℝ≥0 → Ω → ℝ}
    {γ : Ω → ℝ≥0 → ℂ} {z : Ω → ℂ} {S : Ω → Set ℂ}
    (hL : ∀ r : ℚ, 0 < r → Prop59StageLawStatement κ P (ρL₀ r) (ρR₀ r) (sys r))
    (hS : ∀ r : ℚ, 0 < r → IsStageSystem P (hnL r) (hnR r) Q (δ r) (G r) (sys r) fun ω =>
      (ownComponentChart (fun s : ℝ => W s.toNNReal ω) (r : ℝ).toNNReal).1 ''
        (S ω ∩ (H \ fwdHull (fun s : ℝ => W s.toNNReal ω) (r : ℝ).toNNReal)))
    (hwL : ∀ r : ℚ, 0 < r → ∀ j, Even j → IsStageWordN κ (stageρL κ (ρL₀ r) j) (stageρR κ (ρR₀ r) j))
    (hwR : ∀ r : ℚ, 0 < r → ∀ j, ¬ Even j → IsStageWordN κ (stageρR κ (ρR₀ r) j) (stageρL κ (ρL₀ r) j))
    (hR0 : ∀ r : ℚ, 0 < r → ∀ᵐ ω ∂P, (r : ℝ) < traceFirstVisit (γ ω) (z ω) → ω ∈ (sys r (fun _ => 0) 0).R) :
    TipUnboundedStatement P W γ z S := by
  intro r hr
  filter_upwards [ae_not_isBounded_of_stageLaw hκ hκ4 (hL r hr) (hS r hr) (hwL r hr) (hwR r hr) (fun _ => 0),
    hR0 r hr] with ω h1 h2 h3
  exact h1 (h2 h3)

end Tips

end Prop59Stage

end Sec5

end InteractingSLE
