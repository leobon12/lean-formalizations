/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop49QExitImg
import InteractingSLE.Spec.Zhan.WordsEnergy

/-!
# The left exit of a killed word whose marks may coincide

Packet PROVE-GLUECOND11 (G6 of Proposition 4.9's direction, specification p. 120, Remark 4.10 and Aux. lemma 22).
PROVE-GLUECOND9's left exit `ae_leftExit_of_killed` asks for strictly ordered marks at positive times. The image word
of Proposition 4.9 has coincident marks in general: repeated positions of the flow word, and flow marks swallowed by
the counterflow (their images coincide with the junction). Coincident marks of an integrated `SLE_κ(ρ)` path stay
coincident and can be merged (their weights added), at any lifetime; the merged word keeps Zhan's strip hypotheses
(its prefix sums are prefix sums of the original word, its total weights are unchanged) and its last left position.
Hence Aux. lemma 22 for a left span holds from every **ordered** start with negative left and positive right marks
(`ae_leftEnd_of_integrated_ord`), and the left exit holds without strict ordering (`ae_leftExit_of_killed_ord`).

## Main results

* `IsIntegratedSLEPath.mergeAdjL_gen`, `mergeAdjL_evol`, `mergeAdjR_evol`: merging two adjacent coincident marks at
  any lifetime (`Zhan.IsIntegratedSLEPath.mergeAdjL` is the infinite-lifetime case);
* `prefix_mergeAdj`, `prefix_init_mergeAdj`: prefix sums of a merged word are prefix sums of the original;
* **`ae_leftEnd_of_integrated_ord`**: Aux. lemma 22 for a left span from an ordered start;
* `SignStart`, `exitCodeS`, **`codeLaw_compl_exitCodeS_eq_zero`**: the restart event at separated ordered starts;
* **`ae_leftExit_of_killed_ord`**: the left exit of a killed word, marks only ordered.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open QuantumZipper (H Hbar fwdHull fwdMapInv)
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Sec5.Prop49Exit

open Sec2 Sec2.Assembly Sec2.Restart Sec7.RandRestart Zhan

/-! ### Index bookkeeping for merging -/

section Index

variable {n : ℕ}

theorem predAbove_succ_succAbove (j : Fin (n + 1)) (k : Fin (n + 1)) :
    j.predAbove (j.succ.succAbove k) = k := by
  rcases lt_or_ge j.val k.val with h | h
  · have e : j.succ.succAbove k = k.succ := Fin.succAbove_of_le_castSucc _ _ (by
      rw [Fin.le_def]; simp; omega)
    rw [e, Fin.predAbove_of_castSucc_lt _ _ (by rw [Fin.lt_def]; simp; omega)]
    simp
  · have e : j.succ.succAbove k = k.castSucc := Fin.succAbove_of_castSucc_lt _ _ (by
      rw [Fin.lt_def]; simp; omega)
    rw [e, Fin.predAbove_of_le_castSucc _ _ (by rw [Fin.le_def]; simp; omega)]
    simp

theorem succ_succAbove_predAbove (j : Fin (n + 1)) (i : Fin (n + 2)) (hi : i ≠ j.succ) :
    j.succ.succAbove (j.predAbove i) = i := by
  have hv : i.val ≠ j.val + 1 := fun h => hi (Fin.ext (by simp [h]))
  rcases lt_or_ge j.val i.val with h | h
  · rw [Fin.predAbove_of_castSucc_lt _ _ (by rw [Fin.lt_def]; simp; omega)]
    rw [Fin.succAbove_of_le_castSucc _ _ (by rw [Fin.le_def]; simp; omega)]
    simp
  · rw [Fin.predAbove_of_le_castSucc _ _ (by rw [Fin.le_def]; simp; omega)]
    rw [Fin.succAbove_of_castSucc_lt _ _ (by rw [Fin.lt_def]; simp; omega)]
    simp

/-- On a merged pair, every original index is read from a merged index. -/
theorem eq_succ_succAbove_predAbove {α : Type*} {f : Fin (n + 2) → α} {j : Fin (n + 1)}
    (hj : f j.castSucc = f j.succ) (i : Fin (n + 2)) : f (j.succ.succAbove (j.predAbove i)) = f i := by
  by_cases hi : i = j.succ
  · subst hi
    rw [Fin.predAbove_succ_self, Fin.succAbove_of_castSucc_lt _ _ Fin.castSucc_lt_succ]
    exact hj
  · rw [succ_succAbove_predAbove j i hi]

/-- Merging keeps the last position. -/
theorem eq_last_of_mergeAdj {α : Type*} {f : Fin (n + 2) → α} {j : Fin (n + 1)} (hj : f j.castSucc = f j.succ) :
    f (j.succ.succAbove (Fin.last n)) = f (Fin.last (n + 1)) := by
  by_cases hjl : j = Fin.last n
  · subst hjl
    rw [Fin.succAbove_of_castSucc_lt _ _ Fin.castSucc_lt_succ, hj, Fin.succ_last]
  · have hlt : j.val < n := by
      have := j.isLt
      have h2 : j.val ≠ n := fun h => hjl (Fin.ext (by simp [h]))
      omega
    rw [Fin.succAbove_of_le_castSucc _ _ (by rw [Fin.le_def]; simp; omega), Fin.succ_last]

end Index

/-! ### Merging two adjacent coincident marks at any lifetime -/

section Merge

variable {n nR : ℕ}

/-- A threshold sum is unchanged by merging two marks. -/
theorem sum_filter_eq_mergeAdj (ρ : Fin (n + 2) → ℝ) (j : Fin (n + 1)) (v : Fin (n + 1) → ℝ) (x : ℝ) :
    (∑ k ∈ Finset.univ.filter (fun k => v k = x), mergeAdj ρ j k) =
      ∑ i ∈ Finset.univ.filter (fun i => v (j.predAbove i) = x), ρ i := by
  rw [← sum_filter_mergeAdj ρ j (fun i => v (j.predAbove i) = x) (by simp)]
  simp only [predAbove_succ_succAbove]

theorem threshold_mergeAdjL_iff (ρL : Fin (n + 2) → ℝ) (ρR : Fin nR → ℝ) (j : Fin (n + 1)) (w : ℝ)
    (vL : Fin (n + 1) → ℝ) (vR : Fin nR → ℝ) :
    ForceWord.ThresholdCondition (mergeAdj ρL j) ρR w vL vR ↔
      ForceWord.ThresholdCondition ρL ρR w (fun i => vL (j.predAbove i)) vR := by
  unfold ForceWord.ThresholdCondition
  rw [sum_filter_eq_mergeAdj]

/-- **Merging adjacent coincident left marks, pathwise, at any lifetime.** -/
theorem IsIntegratedSLEPath.mergeAdjL_gen {a : ℝ} {xL ρL : Fin (n + 2) → ℝ} {xR ρR : Fin nR → ℝ}
    {w : ℝ≥0 → ℝ} {vL : Fin (n + 2) → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}
    (j : Fin (n + 1)) (hj : xL j.castSucc = xL j.succ) (h : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ) :
    IsIntegratedSLEPath a (fun k => xL (j.succ.succAbove k)) xR (mergeAdj ρL j) ρR w
      (fun k => vL (j.succ.succAbove k)) vR b ζ := by
  have hco : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → vL j.castSucc t = vL j.succ t := fun t ht =>
    InteractingSLE.IsIntegratedSLEPath.vL_eq_of_xL_eq h ht hj
  have hpre : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → ∀ i, vL (j.succ.succAbove (j.predAbove i)) t = vL i t :=
    fun t ht i => eq_succ_succAbove_predAbove (f := fun i => vL i t) (hco t ht) i
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩ := h
  have hmono : Monotone (j.succ.succAbove) := (Fin.strictMono_succAbove _).monotone
  refine ⟨h1, fun k => h2 _, h3, h4, fun k => h5 _, h6, fun t ht => (h7 t ht).comp_monotone hmono,
    fun t ht k => h8 t ht _, h9, h10, fun t ht k => h11 t ht _, h12, fun t ht => ?_,
    fun t ht k => h14 t ht _, h15, fun k => h16 _, h17, fun t ht hth => ?_, fun hz => ?_, ?_⟩
  · rw [h13 t ht]
    congr 2
    have hint : ∀ i ∈ Finset.univ, IntervalIntegrable
        (fun s : ℝ => ρL i / (w s.toNNReal - vL i s.toNNReal)) volume 0 t := fun i _ =>
      ((h11 t ht i).const_mul (ρL i)).congr fun s _ => (div_eq_mul_inv _ _).symm
    have hint' : ∀ k ∈ Finset.univ, IntervalIntegrable
        (fun s : ℝ => mergeAdj ρL j k / (w s.toNNReal - vL (j.succ.succAbove k) s.toNNReal)) volume 0 t :=
      fun k _ => ((h11 t ht _).const_mul (mergeAdj ρL j k)).congr fun s _ => (div_eq_mul_inv _ _).symm
    rw [← intervalIntegral.integral_finsetSum hint, ← intervalIntegral.integral_finsetSum hint']
    refine intervalIntegral.integral_congr fun s hs => ?_
    have hsζ : ((s.toNNReal : ℝ≥0) : ℝ≥0∞) < ζ := by
      refine lt_of_le_of_lt ?_ ht
      rw [Set.uIcc_of_le t.coe_nonneg] at hs
      exact ENNReal.coe_le_coe.2 (by
        rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hs.1]; exact hs.2)
    simp only [div_eq_mul_inv]
    exact (sum_mergeAdj_mul ρL j (fun i => (w s.toNNReal - vL i s.toNNReal)⁻¹)
      (by simp only [hco _ hsζ])).symm
  · refine h18 t ht ?_
    rw [threshold_mergeAdjL_iff] at hth
    convert hth using 2 with i
    exact (hpre t ht i).symm
  · rw [threshold_mergeAdjL_iff]
    convert h19 hz using 2 with i
    exact eq_succ_succAbove_predAbove hj i
  · intro T hT hTζ w₀ vL₀ vR₀ hlim
    rw [threshold_mergeAdjL_iff]
    refine h20 T hT hTζ w₀ (fun i => vL₀ (j.predAbove i)) vR₀ ?_
    have hc : Continuous fun p : ℝ × (Fin (n + 1) → ℝ) × (Fin nR → ℝ) =>
        (p.1, (fun i => p.2.1 (j.predAbove i)), p.2.2) := by fun_prop
    have h' := (hc.tendsto _).comp hlim
    refine h'.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t (htT : t < T)
    have htζ : (t : ℝ≥0∞) < ζ := by rw [← hTζ]; exact_mod_cast htT
    simp only [Function.comp_apply, Prod.mk.injEq, true_and, and_true]
    funext i
    exact hpre t htζ i

variable {κ : ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **Merging adjacent coincident left marks of an evolution, at any lifetime.** -/
theorem mergeAdjL_evol {xL ρL : Fin (n + 2) → ℝ} {xR ρR : Fin nR → ℝ}
    {VL : Fin (n + 2) → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} (j : Fin (n + 1))
    (hj : xL j.castSucc = xL j.succ) (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    IsIntegratedSLEEvolution κ (fun k => xL (j.succ.succAbove k)) xR (mergeAdj ρL j) ρR P 𝓕 W
      (fun k => VL (j.succ.succAbove k)) VR B ζ := by
  obtain ⟨hB, hW, hVL, hVR, hpath⟩ := hE
  refine ⟨hB, hW, fun k => hVL _, hVR, ?_⟩
  filter_upwards [hpath] with ω hp
  exact IsIntegratedSLEPath.mergeAdjL_gen j hj hp

/-- **Merging adjacent coincident right marks of an evolution, at any lifetime**, by reflection. -/
theorem mergeAdjR_evol {nL : ℕ} {xL ρL : Fin nL → ℝ} {xR ρR : Fin (n + 2) → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin (n + 2) → ℝ≥0 → Ω → ℝ} (j : Fin (n + 1))
    (hj : xR j.castSucc = xR j.succ) (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    IsIntegratedSLEEvolution κ xL (fun k => xR (j.succ.succAbove k)) ρL (mergeAdj ρR j) P 𝓕 W VL
      (fun k => VR (j.succ.succAbove k)) B ζ := by
  have h1 := InteractingSLE.IsIntegratedSLEEvolution.reflect hE
  have h2 := mergeAdjL_evol (xL := -xR) (VL := fun i => -VR i) j (by simp only [Pi.neg_apply, hj]) h1
  have h3 := InteractingSLE.IsIntegratedSLEEvolution.reflect h2
  convert h3 using 1 <;> (funext k; simp only [Pi.neg_apply, neg_neg])

end Merge

/-! ### Prefix sums of a merged word -/

section Prefix

variable {n : ℕ}

theorem sum_Iic_eq_filter {N : ℕ} (f : Fin N → ℝ) (m : Fin N) :
    ∑ i ∈ Finset.Iic m, f i = ∑ i ∈ Finset.univ.filter (fun i : Fin N => i.val ≤ m.val), f i := by
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext i
  simp only [Finset.mem_Iic, Finset.mem_filter, Finset.mem_univ, true_and, Fin.le_def]

theorem sum_filter_le_eq_init {N : ℕ} (f : Fin (N + 1) → ℝ) (b : ℕ) (hb : b < N) :
    ∑ i ∈ Finset.univ.filter (fun i : Fin (N + 1) => i.val ≤ b), f i =
      ∑ i ∈ Finset.Iic (⟨b, hb⟩ : Fin N), Fin.init f i := by
  have h := sum_Iic_snoc_castSucc (Fin.init f) (f (Fin.last N)) ⟨b, hb⟩
  rw [Fin.snoc_init_self] at h
  rw [← h, sum_Iic_eq_filter]
  rfl

theorem sum_Iic_mergeAdj (ρ : Fin (n + 2) → ℝ) (j : Fin (n + 1)) (m : Fin (n + 1)) :
    ∑ k ∈ Finset.Iic m, mergeAdj ρ j k =
      ∑ i ∈ Finset.univ.filter
        (fun i : Fin (n + 2) => i.val ≤ if m.val < j.val then m.val else m.val + 1), ρ i := by
  have e1 : Finset.Iic m =
      Finset.univ.filter (fun k : Fin (n + 1) => j.predAbove (j.succ.succAbove k) ≤ m) := by
    ext k; simp [predAbove_succ_succAbove]
  rw [e1, sum_filter_mergeAdj ρ j (fun i => j.predAbove i ≤ m) (by simp)]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.le_def]
  rcases lt_or_ge j.val i.val with h | h
  · rw [Fin.predAbove_of_castSucc_lt _ _ (by rw [Fin.lt_def]; simp; omega)]
    simp only [Fin.val_pred]
    split_ifs <;> omega
  · rw [Fin.predAbove_of_le_castSucc _ _ (by rw [Fin.le_def]; simp; omega)]
    simp only [Fin.coe_castPred]
    split_ifs <;> omega

/-- **The prefix sums of a merged word are prefix sums of the original word.** -/
theorem prefix_mergeAdj {c : ℝ} {ρ : Fin (n + 2) → ℝ} (h : ∀ m : Fin (n + 2), c ≤ ∑ i ∈ Finset.Iic m, ρ i)
    (j : Fin (n + 1)) (m : Fin (n + 1)) : c ≤ ∑ i ∈ Finset.Iic m, mergeAdj ρ j i := by
  rw [sum_Iic_mergeAdj]
  have hb : (if m.val < j.val then m.val else m.val + 1) < n + 2 := by
    have := m.isLt; split_ifs <;> omega
  have := h ⟨_, hb⟩
  rwa [sum_Iic_eq_filter] at this

/-- **The prefix sums of the initial part of a merged word** are prefix sums of the initial part of the original. -/
theorem prefix_init_mergeAdj {c : ℝ} {ρ : Fin (n + 2) → ℝ}
    (h : ∀ m : Fin (n + 1), c ≤ ∑ i ∈ Finset.Iic m, Fin.init ρ i) (j : Fin (n + 1)) (m : Fin n) :
    c ≤ ∑ i ∈ Finset.Iic m, Fin.init (mergeAdj ρ j) i := by
  rw [← sum_filter_le_eq_init (mergeAdj ρ j) m.val m.isLt]
  have e : ∑ i ∈ Finset.univ.filter (fun i : Fin (n + 1) => i.val ≤ m.val), mergeAdj ρ j i =
      ∑ i ∈ Finset.Iic m.castSucc, mergeAdj ρ j i := by
    rw [sum_Iic_eq_filter]; rfl
  rw [e, sum_Iic_mergeAdj]
  have hb : (if m.castSucc.val < j.val then m.castSucc.val else m.castSucc.val + 1) < n + 1 := by
    have := m.isLt; simp only [Fin.val_castSucc]; split_ifs <;> omega
  rw [sum_filter_le_eq_init ρ _ hb]
  exact h _

/-- The strip charge difference depends only on the total left weight. -/
theorem charge_sub_eq {nR j : ℕ} (κ : ℝ) (ρL : Fin (j + 1) → ℝ) (ρR : Fin nR → ℝ) :
    Strip.chargePlus κ (Fin.init ρL) ρR (ρL (Fin.last j)) - Strip.chargeMinus (Fin.init ρL) (ρL (Fin.last j)) =
      κ - 6 - 2 * ∑ i, ρL i := by
  rw [Fin.sum_univ_castSucc]
  simp only [Strip.chargePlus, Strip.tauPlus, Strip.chargeMinus, Fin.init]
  ring

end Prefix

/-! ### Aux. lemma 22 for a left span from an ordered start -/

section Ordered

theorem strictAnti_of_fin_one (f : Fin (0 + 1) → ℝ) : StrictAnti f := fun a b hab => by
  exfalso
  have := a.isLt; have := b.isLt; rw [Fin.lt_def] at hab; omega

theorem strictMono_of_fin_le_one {m : ℕ} (hm : m ≤ 1) (f : Fin m → ℝ) : StrictMono f := fun a b hab => by
  exfalso
  have := a.isLt; have := b.isLt; rw [Fin.lt_def] at hab; omega

/-- **Aux. lemma 22 for a left span from an ordered start.** Let `(W, V, B)` be an integrated `SLE_κ(ρ)` evolution,
`0 < κ ≤ 4`, from an ordered start (left marks negative and antitone, right marks positive and monotone; marks may
coincide) whose reflected strip word satisfies Zhan's hypotheses. Then almost surely the driver has a left strip end
beyond its last left mark. Coincident marks are merged (`mergeAdjL_evol`, `mergeAdjR_evol`) until the start is
strictly ordered (`ae_leftEnd_of_integrated`). -/
theorem ae_leftEnd_of_integrated_ord {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ ≤ 4) (N : ℕ) :
    ∀ {n j : ℕ}, j + n ≤ N → ∀ {xL : Fin (j + 1) → ℝ} {xR : Fin n → ℝ} {ρL : Fin (j + 1) → ℝ}
      {ρR : Fin n → ℝ} {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
      {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin (j + 1) → ℝ≥0 → Ω → ℝ}
      {VR : Fin n → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞},
      IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ → Antitone xL → (∀ i, xL i < 0) →
      Monotone xR → (∀ k, 0 < xR k) → Strip.HasStripPrefixSums κ (Fin.init ρL) ρR →
      |κ - 6 - 2 * ∑ i, ρL i| < 2 →
      ∀ᵐ ω ∂P, LeftEnd (xL (Fin.last j)) (fun t => W t ω) (ζ ω) := by
  induction N with
  | zero =>
    intro n j hN xL xR ρL ρR Ω mΩ P _ 𝓕 W VL VR B ζ hE hLa hL0 hRm hR0 hpre hq
    obtain rfl : j = 0 := by omega
    obtain rfl : n = 0 := by omega
    refine ae_leftEnd_of_integrated hκ hκ4 hE ⟨strictAnti_of_fin_one xL, hL0,
      strictMono_of_fin_le_one (by omega) xR, hR0⟩ hpre ?_
    rwa [charge_sub_eq]
  | succ N ih =>
    intro n j hN xL xR ρL ρR Ω mΩ P _ 𝓕 W VL VR B ζ hE hLa hL0 hRm hR0 hpre hq
    by_cases hsL : StrictAnti xL
    · by_cases hsR : StrictMono xR
      · refine ae_leftEnd_of_integrated hκ hκ4 hE ⟨hsL, hL0, hsR, hR0⟩ hpre ?_
        rwa [charge_sub_eq]
      · -- merge two coincident right marks
        obtain ⟨n₁, rfl⟩ : ∃ n₁, n = n₁ + 2 := ⟨n - 2, by
          by_contra hn
          exact hsR (strictMono_of_fin_le_one (by omega) xR)⟩
        obtain ⟨k, hk⟩ := exists_adj_eq_of_not_strictMono hRm hsR
        have hE' := mergeAdjR_evol k hk hE
        refine ih (by omega) hE' hLa hL0 (hRm.comp (Fin.strictMono_succAbove _).monotone)
          (fun _ => hR0 _) ⟨hpre.1, fun m => ?_⟩ hq
        exact prefix_mergeAdj (fun m => hpre.2 m) k m
    · -- merge two coincident left marks
      obtain ⟨j₁, rfl⟩ : ∃ j₁, j = j₁ + 1 := ⟨j - 1, by
        by_contra hj
        obtain rfl : j = 0 := by omega
        exact hsL (strictAnti_of_fin_one xL)⟩
      obtain ⟨k, hk⟩ := exists_adj_eq_of_not_strictAnti hLa hsL
      have hE' := mergeAdjL_evol k hk hE
      have h := ih (by omega) hE' (hLa.comp_monotone (Fin.strictMono_succAbove _).monotone)
        (fun _ => hL0 _) hRm hR0 ⟨fun m => prefix_init_mergeAdj (fun m => hpre.1 m) k m, hpre.2⟩
        (by rwa [sum_mergeAdj])
      simpa only [eq_last_of_mergeAdj hk] using h

end Ordered

/-! ### The restart event at separated ordered starts -/

section CodeEventS

variable {nL nR : ℕ} {a : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {eOf : (Fin nL → ℝ) × (Fin nR → ℝ) → ℝ}

/-- A start whose left marks are negative and whose right marks are positive (marks may coincide). -/
def SignStart (s : (Fin nL → ℝ) × (Fin nR → ℝ)) : Prop := (∀ i, s.1 i < 0) ∧ ∀ j, 0 < s.2 j

theorem measurableSet_signStart : MeasurableSet {s : (Fin nL → ℝ) × (Fin nR → ℝ) | SignStart s} := by
  have h1 : ∀ i : Fin nL, Measurable fun s : (Fin nL → ℝ) × (Fin nR → ℝ) => s.1 i := fun i =>
    (measurable_pi_apply i).comp measurable_fst
  have h2 : ∀ j : Fin nR, Measurable fun s : (Fin nL → ℝ) × (Fin nR → ℝ) => s.2 j := fun j =>
    (measurable_pi_apply j).comp measurable_snd
  refine measurableSet_setOfPred.2 (Measurable.and ?_ ?_)
  · exact Measurable.forall fun i => measurableSet_setOfPred.1 (measurableSet_lt (h1 i) measurable_const)
  · exact Measurable.forall fun j => measurableSet_setOfPred.1 (measurableSet_lt measurable_const (h2 j))

/-- **The restart event without strict order**: a code whose start has negative left and positive right marks has a
left strip end. -/
def exitCodeS (a : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (eOf : (Fin nL → ℝ) × (Fin nR → ℝ) → ℝ) :
    Set (XCode nL nR) :=
  {x | SignStart (startOf x)}ᶜ ∪ endCode a ρL ρR eOf

theorem measurableSet_exitCodeS (he : Measurable eOf) : MeasurableSet (exitCodeS a ρL ρR eOf) :=
  (measurableSet_signStart.preimage measurable_startOf).compl.union (measurableSet_endCode he)

theorem codeLaw_compl_exitCodeS_of_not {s : (Fin nL → ℝ) × (Fin nR → ℝ)} (hs : ¬ SignStart s) :
    codeLaw a ρL ρR (exitCodeS a ρL ρR eOf)ᶜ s = 0 := by
  refine measure_mono_null (fun f hf => ?_) measure_empty
  obtain ⟨x, ⟨⟨hxF, -⟩, hxS⟩, hxe⟩ := hf
  simp only [Prod.mk.injEq] at hxe
  exact hxS (Or.inl (show ¬ SignStart (startOf x) by rw [hxe.1]; exact hs))

theorem mem_exitCodeS_iff {s : (Fin nL → ℝ) × (Fin nR → ℝ)} (hs : SignStart s) {x : XCode nL nR}
    (hx : x ∈ CRel a s.1 s.2 ρL ρR) : x ∈ exitCodeS a ρL ρR eOf ↔ LeftEnd (eOf s) (cw x) (cζ x) := by
  rw [← mem_endCode_iff hx]
  have hst := (mem_cRelF_iff.2 hx).2
  constructor
  · rintro (h | h)
    · exact absurd (show SignStart (startOf x) by rw [hst]; exact hs) h
    · exact h
  · exact Or.inr

/-- **The restart event has full canonical law at every separated ordered start** (marks may coincide; `0 < κ ≤ 4`,
Zhan's hypotheses on the weights; the bound is the last left mark). -/
theorem codeLaw_compl_exitCodeS_eq_zero {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ ≤ 4) {n j : ℕ} {ρL : Fin (j + 1) → ℝ}
    {ρR : Fin n → ℝ} (hpre : Strip.HasStripPrefixSums κ (Fin.init ρL) ρR)
    (hq : |Strip.chargePlus κ (Fin.init ρL) ρR (ρL (Fin.last j)) -
      Strip.chargeMinus (Fin.init ρL) (ρL (Fin.last j))| < 2)
    (s : (Fin (j + 1) → ℝ) × (Fin n → ℝ)) (hsep : SepStart s) (hF : IsOrderedForceWord s.1 s.2) :
    codeLaw κ ρL ρR (exitCodeS κ ρL ρR fun s => s.1 (Fin.last j))ᶜ s = 0 := by
  by_cases hs : SignStart s
  · obtain ⟨Ω₀, m₀, P₀, hP₀, 𝓕₀, W₀, VL₀, VR₀, B₀, ζ₀, hE₀⟩ :=
      exists_isIntegratedSLEEvolution_assembled (a := κ) hκ hF
    rw [charge_sub_eq] at hq
    exact codeLaw_compl_eq_zero_of_ae hκ hsep hE₀ (measurableSet_exitCodeS (by fun_prop))
      (fun x hx _ => mem_exitCodeS_iff hs hx) (fun w w' τ hww' h => leftEnd_congr w w' τ hww' h)
      (ae_leftEnd_of_integrated_ord hκ hκ4 (j + n) le_rfl hE₀ hF.1 hs.1 hF.2.2.1 hs.2 hpre hq)
  · exact codeLaw_compl_exitCodeS_of_not hs

end CodeEventS

/-! ### The left exit of a killed word with ordered marks -/

section KilledOrd

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {𝓘 : Filtration ℝ≥0 mΩ}

/-- **The left exit of a killed `SLE_κ(ρ)` word whose marks may coincide** (PROVE-GLUECOND9's
`ae_leftExit_of_killed` without its strict-order hypothesis). Let `(W, V)` be a killed word before `T` (the integrated
equations of its random initial word before `T`, a Brownian motion of a filtration, adapted, `{q < T} ∈ 𝓘_q`, the marks
strictly separated from the driver at positive times, below the threshold at `0`), whose weights satisfy Zhan's strip
hypotheses for the left span, and assume that `F̄_t` sends the real points left of the last left mark off `ℍ`. Then
almost surely `T` is finite and every trace generating the word in `ℍ` before `T` converges at `T`, either to a point
of `ℍ` or to `F̄_q(y)` for a positive time `q < T` and a real `y` left of the last left mark at `q`. -/
theorem ae_leftExit_of_killed_ord {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ ≤ 4) {n j : ℕ} {ρL : Fin (j + 1) → ℝ}
    {ρR : Fin n → ℝ} (hpre : Strip.HasStripPrefixSums κ (Fin.init ρL) ρR)
    (hq : |Strip.chargePlus κ (Fin.init ρL) ρR (ρL (Fin.last j)) -
      Strip.chargeMinus (Fin.init ρL) (ρL (Fin.last j))| < 2)
    {B : ℝ≥0 → Ω → ℝ} (hB : IsFilteredBrownianReal 𝓘 B P) (hBc : ∀ ω, Continuous (B · ω))
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin (j + 1) → ℝ≥0 → Ω → ℝ} {VR : Fin n → ℝ≥0 → Ω → ℝ}
    (hWa : StronglyAdapted 𝓘 W) (hVLa : ∀ i, StronglyAdapted 𝓘 (VL i))
    (hVRa : ∀ j, StronglyAdapted 𝓘 (VR j)) {T : Ω → ℝ≥0∞}
    (hTq : ∀ q : ℝ≥0, MeasurableSet[𝓘 q] {ω | (q : ℝ≥0∞) < T ω}) (hT0 : ∀ ω, 0 < T ω)
    (hE : ∀ᵐ ω ∂P, Sec7.Aux117.IsWordEntrance κ (fun i => VL i 0 ω) (fun j => VR j 0 ω) ρL ρR
      (fun t => W t ω) (fun i t => VL i t ω) (fun j t => VR j t ω) (fun t => B t ω) (T ω))
    (hsepL : ∀ ω (t : ℝ≥0), 0 < t → (t : ℝ≥0∞) < T ω → ∀ i, VL i t ω < W t ω)
    (hsepR : ∀ ω (t : ℝ≥0), 0 < t → (t : ℝ≥0∞) < T ω → ∀ j, W t ω < VR j t ω)
    (hthr : ∀ᵐ ω ∂P, ¬ ForceWord.ThresholdCondition ρL ρR (W 0 ω) (fun i => VL i 0 ω) (fun j => VR j 0 ω))
    (hgeo : ∀ ω (t : ℝ≥0), 0 < t → (t : ℝ≥0∞) < T ω → ∀ y : ℝ, y < VL (Fin.last j) t ω - W t ω →
      extendFrom H (fwdMapInv (fun s : ℝ => W s.toNNReal ω) t) y ∉ H) :
    ∀ᵐ ω ∂P, ∀ γ : ℝ≥0 → ℂ, (∀ s : ℝ≥0, (s : ℝ≥0∞) < T ω → Sec7.IsGeneratingTraceIcc (W · ω) s γ) →
      (∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) < T ω → γ t ∈ H) →
      T ω ≠ ⊤ ∧ ∃ z : ℂ, Tendsto γ (𝓝[<] (T ω).toNNReal) (𝓝 z) ∧
        (z ∈ H ∨ ∃ (q : ℝ≥0) (y : ℝ), 0 < q ∧ (q : ℝ≥0∞) < T ω ∧ y < VL (Fin.last j) q ω - W q ω ∧
          z = extendFrom H (fwdMapInv (fun s : ℝ => W s.toNNReal ω) q) y) := by
  have hS : ∀ s : (Fin (j + 1) → ℝ) × (Fin n → ℝ), SepStart s → IsOrderedForceWord s.1 s.2 →
      codeLaw κ ρL ρR (exitCodeS κ ρL ρR fun s => s.1 (Fin.last j))ᶜ s = 0 :=
    fun s hsep hF => codeLaw_compl_exitCodeS_eq_zero hκ hκ4 hpre hq s hsep hF
  have hR := ae_restart_code hκ hB hBc hWa hVLa hVRa hTq hT0
    (measurableSet_exitCodeS ((measurable_pi_apply (Fin.last j)).comp measurable_fst)) hS hE hsepL hsepR hthr
  filter_upwards [hR, hE] with ω hω hEω γ hγ hγH
  obtain ⟨q, -, hqpos, hqT⟩ := ENNReal.lt_iff_exists_rat_btwn.1 (hT0 ω)
  have hq0 : 0 < q := by
    have h : (0 : ℝ≥0) < (q : ℝ).toNNReal := by exact_mod_cast hqpos
    exact_mod_cast Real.toNNReal_pos.1 h
  set q' : ℝ≥0 := (q : ℝ).toNNReal with hq'def
  have hqT' : (q' : ℝ≥0∞) < T ω := hqT
  obtain ⟨x, hxC, hxS, -, hagree⟩ := hω q hq0 hqT'
  have hq'0 : 0 < q' := Real.toNNReal_pos.2 (by exact_mod_cast hq0)
  -- the restarted state has negative left and positive right marks
  have hst : SignStart (stAt W VL VR q' ω) := by
    refine ⟨fun i => ?_, fun j' => ?_⟩
    · show VL i q' ω - W q' ω < 0
      linarith [hsepL ω q' hq'0 hqT' i]
    · show 0 < VR j' q' ω - W q' ω
      linarith [hsepR ω q' hq'0 hqT' j']
  obtain ⟨S, y, hend⟩ := (mem_exitCodeS_iff hst hxC).1 hxS
  have hxp := hxC.1.2.2
  obtain ⟨hTne, z, hz, hzalt⟩ := leftExit_of_restart (w := fun t => W t ω) (T := T ω)
    hEω.continuousOn_w hEω.w_zero hγ hγH hq'0 hqT' hxp.isForcePath.continuousOn_w hxp.1
    (fun t ht => (hagree t ht).1) hend (fun y' hy' => hgeo ω q' hq'0 hqT' y' hy')
  refine ⟨hTne, z, hz, ?_⟩
  rcases hzalt with h | ⟨y', hy', rfl⟩
  · exact Or.inl h
  · exact Or.inr ⟨q', y', hq'0, hqT', hy', rfl⟩

end KilledOrd

end InteractingSLE.Sec5.Prop49Exit
