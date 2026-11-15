/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.BR3RefCore

/-!
# BR3's bounded reference for a distinct word (reflected form)

Packet PROVE-T14-BR3. The core estimates of `BR3RefCore` need a right mark before the bad one and a left mark, and the
protection of the off-seed left marks (GB5) needs a left mark before them. Passive zero-weight marks provide these
("Retain all actual and reference marks, with zero weights where needed", BR1's proof, p. 607): the canonical law of
the driving history is the same for every evolution of a separated word (`measure_eventOf_eq_codeLaw_state`), so the
event can be proved for one convenient evolution — an evolution of the word with two passive marks inserted, the
passive marks then deleted (`IsIntegratedSLEEvolution.compEmb`).

* `pre`, `pre_insertNth`, `pre_comp`: prefix sums by value, under insertion of a zero weight and along value-preserving
  maps;
* **`ae_event_dist`**: for `κ > 4` and a distinct separated word whose right list has a bad group end `J` (partial sum
  `≤ −2`, earlier partials `> −2`, weights `0` beyond `J`, `x_J > 0`) and whose left partial sums all exceed `−2` and
  are
  at least `κ/2 − 2` at the marks strictly left of `0`: almost surely the lifetime is finite and, before it, the right
  marks beyond `J` and the left marks strictly left of `0` stay at a positive distance from the driver.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Finset
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Theorem14

namespace BR3Ref

/-! ### Prefix sums by value -/

section Pre

variable {n : ℕ}

/-- The sum of the weights of Lean index `< v`. -/
def pre (ρ : Fin n → ℝ) (v : ℕ) : ℝ := ∑ l ∈ univ.filter (fun l : Fin n => (l : ℕ) < v), ρ l

theorem sum_filter_le_eq_pre (ρ : Fin n → ℝ) (i : Fin n) :
    ∑ l ∈ univ.filter (· ≤ i), ρ l = pre ρ (i + 1) := by
  unfold pre
  refine Finset.sum_congr (Finset.filter_congr fun l _ => ?_) fun _ _ => rfl
  rw [Fin.le_def]; omega

theorem pre_of_le (ρ : Fin n → ℝ) {v : ℕ} (hv : n ≤ v) : pre ρ v = ∑ l, ρ l := by
  unfold pre
  rw [Finset.filter_true_of_mem fun l _ => lt_of_lt_of_le l.isLt hv]

/-- Prefix sums of a tuple with a zero weight inserted at `p`. -/
theorem pre_insertNth (ρ : Fin n → ℝ) (p : Fin (n + 1)) (v : ℕ) :
    pre (Fin.insertNth p 0 ρ) v = pre ρ (if v ≤ (p : ℕ) then v else v - 1) := by
  unfold pre
  rw [Finset.sum_filter, Finset.sum_filter, Fin.sum_univ_succAbove _ p]
  simp only [Fin.insertNth_apply_same, ite_self, zero_add, Fin.insertNth_apply_succAbove]
  refine Finset.sum_congr rfl fun l _ => ?_
  have hv : ((p.succAbove l : Fin (n + 1)) : ℕ) < v ↔ (l : ℕ) < (if v ≤ (p : ℕ) then v else v - 1) := by
    rcases Fin.castSucc_lt_or_lt_succ p l with h | h
    · rw [Fin.succAbove_of_castSucc_lt _ _ h, Fin.val_castSucc]
      rw [Fin.lt_def, Fin.val_castSucc] at h
      split_ifs <;> omega
    · rw [Fin.succAbove_of_lt_succ _ _ h, Fin.val_succ]
      rw [Fin.lt_def, Fin.val_succ] at h
      split_ifs <;> omega
  simp only [hv]

/-- Prefix sums along a value-preserving map. -/
theorem pre_comp {a b : ℕ} (e : Fin a → Fin b) (he : ∀ l, (e l : ℕ) = l) (f : Fin b → ℝ) {v : ℕ} (hv : v ≤ a) :
    pre (fun l => f (e l)) v = pre f v := by
  unfold pre
  refine Finset.sum_bij (fun l _ => e l) (fun l hl => ?_) (fun l₁ _ l₂ _ h => ?_) (fun l hl => ?_)
    (fun _ _ => rfl)
  · simp only [mem_filter, Finset.mem_univ, true_and] at hl ⊢
    rw [he]; exact hl
  · exact Fin.ext (by rw [← he l₁, ← he l₂, h])
  · simp only [mem_filter, Finset.mem_univ, true_and] at hl
    refine ⟨⟨l, by omega⟩, ?_, Fin.ext (by rw [he])⟩
    simp only [mem_filter, Finset.mem_univ, true_and]
    exact hl

theorem pre_mono_zero (ρ : Fin n → ℝ) {v w : ℕ} (hvw : v ≤ w)
    (h0 : ∀ l : Fin n, v ≤ (l : ℕ) → (l : ℕ) < w → ρ l = 0) : pre ρ w = pre ρ v := by
  unfold pre
  rw [Finset.sum_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun l _ => ?_
  by_cases hv : (l : ℕ) < v
  · simp [hv, lt_of_lt_of_le hv hvw]
  · by_cases hw : (l : ℕ) < w
    · simp only [hw, hv, ite_true, ite_false]; exact h0 l (not_lt.1 hv) hw
    · simp [hw, hv]

end Pre

/-! ### Inserting a passive mark -/

section Insert

variable {n : ℕ}

theorem val_succAbove_lt {p : Fin (n + 1)} {l : Fin n} (h : (l : ℕ) < p) : ((p.succAbove l : Fin (n + 1)) : ℕ) = l := by
  rw [Fin.succAbove_of_castSucc_lt _ _ (by rw [Fin.lt_def, Fin.val_castSucc]; exact h), Fin.val_castSucc]

theorem val_succAbove_ge {p : Fin (n + 1)} {l : Fin n} (h : (p : ℕ) ≤ l) :
    ((p.succAbove l : Fin (n + 1)) : ℕ) = l + 1 := by
  rw [Fin.succAbove_of_le_castSucc _ _ (by rw [Fin.le_def, Fin.val_castSucc]; exact h), Fin.val_succ]

/-- The value of `p.succAbove l`. -/
theorem val_succAbove (p : Fin (n + 1)) (l : Fin n) :
    ((p.succAbove l : Fin (n + 1)) : ℕ) = if (l : ℕ) < p then (l : ℕ) else (l : ℕ) + 1 := by
  split_ifs with h
  · exact val_succAbove_lt h
  · exact val_succAbove_ge (not_lt.1 h)

/-- Inserting a value into a strictly increasing tuple at the right place keeps it strictly increasing. -/
theorem strictMono_insertNth' {x : Fin n → ℝ} (hx : StrictMono x) (p : Fin (n + 1)) {y : ℝ}
    (hlo : ∀ i : Fin n, (i : ℕ) < p → x i < y) (hhi : ∀ i : Fin n, (p : ℕ) ≤ i → y < x i) :
    StrictMono (Fin.insertNth p y x) := by
  intro a b hab
  rcases Fin.eq_self_or_eq_succAbove p a with ha | ⟨a', ha⟩ <;>
    rcases Fin.eq_self_or_eq_succAbove p b with hb | ⟨b', hb⟩ <;> subst ha hb
  · exact absurd hab (lt_irrefl _)
  · simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
    refine hhi b' ?_
    rw [Fin.lt_def, val_succAbove] at hab
    split_ifs at hab <;> omega
  · simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
    refine hlo a' ?_
    rw [Fin.lt_def, val_succAbove] at hab
    split_ifs at hab <;> omega
  · simp only [Fin.insertNth_apply_succAbove]
    exact hx (Fin.succAbove_lt_succAbove_iff.1 hab)

/-- The decreasing version. -/
theorem strictAnti_insertNth' {x : Fin n → ℝ} (hx : StrictAnti x) (p : Fin (n + 1)) {y : ℝ}
    (hlo : ∀ i : Fin n, (i : ℕ) < p → y < x i) (hhi : ∀ i : Fin n, (p : ℕ) ≤ i → x i < y) :
    StrictAnti (Fin.insertNth p y x) := by
  intro a b hab
  rcases Fin.eq_self_or_eq_succAbove p a with ha | ⟨a', ha⟩ <;>
    rcases Fin.eq_self_or_eq_succAbove p b with hb | ⟨b', hb⟩ <;> subst ha hb
  · exact absurd hab (lt_irrefl _)
  · simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
    refine hhi b' ?_
    rw [Fin.lt_def, val_succAbove] at hab
    split_ifs at hab <;> omega
  · simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
    refine hlo a' ?_
    rw [Fin.lt_def, val_succAbove] at hab
    split_ifs at hab <;> omega
  · simp only [Fin.insertNth_apply_succAbove]
    exact hx (Fin.succAbove_lt_succAbove_iff.1 hab)

end Insert

/-! ### The word with two passive marks -/

section Aug

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}

theorem insertNth_le_zero {x : Fin nL → ℝ} (hx : ∀ i, x i ≤ 0) (p : Fin (nL + 1)) {y : ℝ} (hy : y < 0)
    (k : Fin (nL + 1)) : Fin.insertNth (α := fun _ => ℝ) p y x k ≤ 0 := by
  rcases Fin.eq_self_or_eq_succAbove p k with rfl | ⟨k', rfl⟩
  · rw [Fin.insertNth_apply_same]; exact hy.le
  · rw [Fin.insertNth_apply_succAbove]; exact hx k'

theorem zero_le_insertNth {x : Fin nR → ℝ} (hx : ∀ i, 0 ≤ x i) (p : Fin (nR + 1)) {y : ℝ} (hy : 0 < y)
    (k : Fin (nR + 1)) : 0 ≤ Fin.insertNth (α := fun _ => ℝ) p y x k := by
  rcases Fin.eq_self_or_eq_succAbove p k with rfl | ⟨k', rfl⟩
  · rw [Fin.insertNth_apply_same]; exact hy.le
  · rw [Fin.insertNth_apply_succAbove]; exact hx k'

/-- The augmented word is distinct and separated. -/
theorem aug_distinct_sep (hD : LP.IsDistinctForceWord xL xR) (hsep : ∀ i i', xL i < xR i') (J : Fin nR)
    (pL : Fin (nL + 1)) {yL yR : ℝ} (hyL : yL < 0) (hyR : 0 < yR)
    (hLlo : ∀ i : Fin nL, (i : ℕ) < pL → yL < xL i) (hLhi : ∀ i : Fin nL, (pL : ℕ) ≤ i → xL i < yL)
    (hRlo : ∀ i : Fin nR, (i : ℕ) < J → xR i < yR) (hRhi : ∀ i : Fin nR, (J : ℕ) ≤ i → yR < xR i) :
    LP.IsDistinctForceWord (Fin.insertNth (α := fun _ => ℝ) pL yL xL)
        (Fin.insertNth (α := fun _ => ℝ) J.castSucc yR xR) ∧
      ∀ i i', Fin.insertNth (α := fun _ => ℝ) pL yL xL i < Fin.insertNth (α := fun _ => ℝ) J.castSucc yR xR i' := by
  obtain ⟨⟨-, hL0, -, hR0⟩, hanti, hmono⟩ := hD
  have hA := strictAnti_insertNth' hanti pL hLlo hLhi
  have hM := strictMono_insertNth' hmono J.castSucc (fun i hi => hRlo i (by simpa using hi))
    (fun i hi => hRhi i (by simpa using hi))
  refine ⟨⟨⟨hA.antitone, insertNth_le_zero hL0 pL hyL, hM.monotone, zero_le_insertNth hR0 _ hyR⟩, hA, hM⟩,
    fun i i' => ?_⟩
  rcases Fin.eq_self_or_eq_succAbove pL i with rfl | ⟨k, rfl⟩ <;>
    rcases Fin.eq_self_or_eq_succAbove J.castSucc i' with h | ⟨k', rfl⟩
  · rw [h, Fin.insertNth_apply_same, Fin.insertNth_apply_same]; linarith
  · rw [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]; linarith [hR0 k']
  · rw [h, Fin.insertNth_apply_succAbove, Fin.insertNth_apply_same]; linarith [hL0 k]
  · rw [Fin.insertNth_apply_succAbove, Fin.insertNth_apply_succAbove]; exact hsep k k'

/-! ### The event on the augmented word -/

/-- **The rational-time event**: finite lifetime, and at every rational time before it the right marks with `pR` and
the left marks with `pL` at distance at least `1/(n+1)` from the driver. -/
def EvRat {nL nR : ℕ} (pL : Fin nL → Prop) (pR : Fin nR → Prop) (w : ℝ≥0 → ℝ) (vL : Fin nL → ℝ≥0 → ℝ)
    (vR : Fin nR → ℝ≥0 → ℝ) (ζ : ℝ≥0∞) : Prop :=
  ζ < ⊤ ∧ ∃ n : ℕ, ∀ q : ℚ≥0, ((q : ℝ≥0) : ℝ≥0∞) < ζ →
    (∀ i, pR i → 1 / ((n : ℝ) + 1) ≤ vR i q - w q) ∧ (∀ i, pL i → 1 / ((n : ℝ) + 1) ≤ w q - vL i q)

theorem one_div_le_of_le {m n : ℕ} (h : m ≤ n) : 1 / ((n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) := by
  have : (m : ℝ) ≤ n := by exact_mod_cast h
  exact one_div_le_one_div_of_le (by positivity) (by linarith)

theorem sum_filter_val_le_eq_pre {n : ℕ} (ρ : Fin n → ℝ) (v : ℕ) :
    ∑ l ∈ univ.filter (fun l : Fin n => (l : ℕ) ≤ v), ρ l = pre ρ (v + 1) := by
  unfold pre
  refine Finset.sum_congr (Finset.filter_congr fun l _ => ?_) fun _ _ => rfl
  omega

/-- **BR3's bounded reference on the word with two passive marks.** A left passive mark at `y_L < 0` (Lean index `p_L`,
just after the marks at `0`) and a right passive mark at `y_R ∈ (x_{J−1}, x_J)` (Lean index `J`) are inserted into a
distinct separated word of the type of `ae_event_dist`. Almost surely on every evolution of the augmented word the
lifetime is finite and the original far right marks and the original left marks strictly left of `0` keep a gap
`≥ 1/(n+1)` from the driver at the rational times before it. -/
theorem ae_evRat_aug (hT13 : Exist.Theorem13Statement.{0}) (hκ : 4 < κ) (hD : LP.IsDistinctForceWord xL xR)
    (hsep : ∀ i i', xL i < xR i') (J : Fin nR) (hLpre : ∀ v ≤ nL, -2 < pre ρL v)
    (hLc : ∀ i : Fin nL, xL i < 0 → κ / 2 - 2 ≤ pre ρL (i + 1)) (hRpre : ∀ v ≤ (J : ℕ), -2 < pre ρR v)
    (hRJ : pre ρR (J + 1) ≤ -2) (hRfar : ∀ i, J < i → ρR i = 0) (pL : Fin (nL + 1)) {yL yR : ℝ} (hyL : yL < 0)
    (hyR : 0 < yR) (hLlo : ∀ i : Fin nL, (i : ℕ) < pL → yL < xL i)
    (hLhi : ∀ i : Fin nL, (pL : ℕ) ≤ i → xL i < yL) (hLneg : ∀ i : Fin nL, xL i < 0 → (pL : ℕ) ≤ i)
    (hRlo : ∀ i : Fin nR, (i : ℕ) < J → xR i < yR) (hRhi : ∀ i : Fin nR, (J : ℕ) ≤ i → yR < xR i)
    {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ} {VR : Fin (nR + 1) → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞}
    (hE : IsIntegratedSLEEvolution κ (Fin.insertNth (α := fun _ => ℝ) pL yL xL)
      (Fin.insertNth (α := fun _ => ℝ) J.castSucc yR xR) (Fin.insertNth (α := fun _ => ℝ) pL 0 ρL)
      (Fin.insertNth (α := fun _ => ℝ) J.castSucc 0 ρR) P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, EvRat (fun i => xL i < 0) (fun i => J < i) (fun t => W t ω) (fun i t => VL (pL.succAbove i) t ω)
      (fun i t => VR (J.castSucc.succAbove i) t ω) (ζ ω) := by
  set xL' := Fin.insertNth (α := fun _ => ℝ) pL yL xL with hxL'
  set xR' := Fin.insertNth (α := fun _ => ℝ) J.castSucc yR xR with hxR'
  set ρL' := Fin.insertNth (α := fun _ => ℝ) pL 0 ρL with hρL'
  set ρR' := Fin.insertNth (α := fun _ => ℝ) J.castSucc 0 ρR with hρR'
  have hκ0 : 0 < κ := by linarith
  obtain ⟨hD', hsep'⟩ := aug_distinct_sep hD hsep J pL hyL hyR hLlo hLhi hRlo hRhi
  have hJ : (J : ℕ) < nR := J.isLt
  have hLp : ∀ i : Fin (nL + 1), -2 < ∑ l ∈ univ.filter (· ≤ i), ρL' l := fun i => by
    rw [sum_filter_le_eq_pre, hρL', pre_insertNth]
    exact hLpre _ (by have := i.isLt; split_ifs <;> omega)
  have hRp : ∀ v ≤ (J : ℕ) + 1, -2 < pre ρR' v := fun v hv => by
    rw [hρR', pre_insertNth]
    exact hRpre _ (by simp only [Fin.val_castSucc]; split_ifs <;> omega)
  have hRtot : pre ρR' ((J : ℕ) + 1 + 1) ≤ -2 := by
    rw [hρR', pre_insertNth]
    simp only [Fin.val_castSucc]
    split_ifs with hc
    · omega
    · simpa using hRJ
  have hRz : ∀ k : Fin (nR + 1), (J : ℕ) + 1 < k → ρR' k = 0 := by
    intro k hk
    rcases Fin.eq_self_or_eq_succAbove J.castSucc k with h | ⟨k', rfl⟩
    · rw [h, Fin.val_castSucc] at hk; omega
    · rw [hρR', Fin.insertNth_apply_succAbove]
      apply hRfar
      rw [val_succAbove, Fin.val_castSucc] at hk
      rw [Fin.lt_def]
      split_ifs at hk <;> omega
  have hrefl : ∀ i, i ∉ Set.range (RelEmbedding.refl (α := Fin (nL + 1)) (· ≤ ·)) → ρL' i = 0 :=
    fun i hi => absurd ⟨i, rfl⟩ hi
  have hcastLE : ∀ {m : ℕ} (h : m ≤ nR + 1), (J : ℕ) + 1 < m →
      ∀ k, k ∉ Set.range (Fin.castLEOrderEmb h) → ρR' k = 0 := by
    intro m h hm k hk
    refine hRz k ?_
    by_contra hk'
    exact hk ⟨⟨k, by omega⟩, Fin.ext (by simp)⟩
  -- (A): the lifetime is finite
  have hA : (J : ℕ) + 1 + 1 + 0 ≤ nR + 1 := by omega
  have hEA := IsIntegratedSLEEvolution.compEmb hE (RelEmbedding.refl (α := Fin (nL + 1)) (· ≤ ·))
    (Fin.castLEOrderEmb hA) hrefl (hcastLE hA (by omega))
  have hfin : ∀ᵐ ω ∂P, ζ ω < ⊤ := by
    refine ae_lifetime_lt_top_core (j := (J : ℕ) + 1) hT13 hκ ⟨hD'.1.compEmb _ _, fun a b hab => hD'.2.1 hab,
      fun a b hab => hD'.2.2 (Fin.strictMono_castLE hA hab)⟩ (fun i i' => hsep' _ _) (by omega) (by omega)
      (fun i => hLp i) (fun i hi => ?_) ?_ hEA
    · rw [sum_filter_le_eq_pre, pre_comp (fun l => Fin.castLEOrderEmb hA l) (fun l => by simp) ρR' (by omega)]
      exact hRp _ (by omega)
    · rw [← pre_of_le _ (le_refl ((J : ℕ) + 1 + 1 + 0)),
        pre_comp (fun l => Fin.castLEOrderEmb hA l) (fun l => by simp) ρR' le_rfl]
      exact hRtot
  -- (B): the nearest far mark
  have hfar : ∀ᵐ ω ∂P, ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → ∀ i : Fin nR, J < i →
      δ ≤ VR (J.castSucc.succAbove i) t ω - W t ω := by
    by_cases hex : (J : ℕ) + 1 < nR
    · have hB : (J : ℕ) + 1 + 1 + 1 + 0 ≤ nR + 1 := by omega
      have hEB := IsIntegratedSLEEvolution.compEmb hE (RelEmbedding.refl (α := Fin (nL + 1)) (· ≤ ·))
        (Fin.castLEOrderEmb hB) hrefl (hcastLE hB (by omega))
      have hfB := ae_far_gap_core (j := (J : ℕ) + 1) hT13 hκ ⟨hD'.1.compEmb _ _, fun a b hab => hD'.2.1 hab,
        fun a b hab => hD'.2.2 (Fin.strictMono_castLE hB hab)⟩ (fun i i' => hsep' _ _) (by omega) (by omega)
        (fun i => hLp i) (fun i hi => by
          rw [sum_filter_le_eq_pre, pre_comp (fun l => Fin.castLEOrderEmb hB l) (fun l => by simp) ρR' (by omega)]
          exact hRp _ (by omega))
        (by
          rw [sum_filter_val_le_eq_pre,
            pre_comp (fun l => Fin.castLEOrderEmb hB l) (fun l => by simp) ρR' (by omega)]
          exact hRtot)
        (hRz _ (by simp [LP.retargetIdx])) hEB
      filter_upwards [hfB, hE.ae_isIntegratedSLEPath] with ω ⟨δ, hδ, hb⟩ hp
      refine ⟨δ, hδ, fun t ht i hi => (hb t ht).trans ?_⟩
      have hle : (Fin.castLEOrderEmb hB (LP.retargetIdx ((J : ℕ) + 1 + 1) 0) : Fin (nR + 1)) ≤
          J.castSucc.succAbove i := by
        rw [Fin.le_def, val_succAbove, Fin.val_castSucc]
        rw [Fin.lt_def] at hi
        simp only [Fin.castLEOrderEmb_apply, Fin.val_castLE, LP.retargetIdx, Fin.val_castAdd, Fin.val_last]
        split_ifs <;> omega
      have := hp.isForcePath.monotone_vR ht hle
      simp only at this ⊢
      linarith
    · exact Eventually.of_forall fun ω => ⟨1, one_pos, fun t _ i hi => absurd (Fin.lt_def.1 hi) (by
        have := i.isLt; omega)⟩
  -- (C): the left marks strictly left of `0`
  have hleft : ∀ᵐ ω ∂P, ζ ω < ⊤ → ∃ n : ℕ, ∀ q : ℚ≥0, ((q : ℝ≥0) : ℝ≥0∞) < ζ ω → ∀ i : Fin nL, xL i < 0 →
      1 / ((n : ℝ) + 1) ≤ W q ω - VL (pL.succAbove i) q ω := by
    by_cases hex : (pL : ℕ) < nL
    · set ℓ : Fin (nL + 1) := pL.succAbove ⟨pL, hex⟩ with hℓdef
      have hℓv : (ℓ : ℕ) = pL + 1 := val_succAbove_ge (le_refl _)
      have hgb := Supp8.GB5.gb5_left hκ0 hD'.1 ℓ (fun i _ _ => hLp i) (fun i hi _ => by
          rw [sum_filter_le_eq_pre, hρL', pre_insertNth]
          rw [Fin.le_def, hℓv] at hi
          split_ifs with hc
          · omega
          have hm : (i : ℕ) - 1 < nL := by have := i.isLt; omega
          have h1 := hLc ⟨(i : ℕ) - 1, hm⟩ ((hLhi _ (by simp; omega)).trans hyL)
          have e : ((i : ℕ) + 1 - 1) = (((⟨(i : ℕ) - 1, hm⟩ : Fin nL) : ℕ) + 1) := by simp; omega
          rw [e]; exact h1)
        (hD'.2.1 (show (⟨0, Fin.pos ℓ⟩ : Fin (nL + 1)) < ℓ by rw [Fin.lt_def, hℓv]; simp)) hE
      filter_upwards [hgb, hE.ae_tendsto_threshold hκ0, hE.ae_isIntegratedSLEPath] with ω hg hl hp hζ
      obtain ⟨-, n, hn⟩ := gapBdd_of_path hp hsep' hLp ⟨(J : ℕ) + 1, by omega⟩
        (fun i hi => by rw [sum_filter_le_eq_pre]; exact hRp _ (by rw [Fin.lt_def] at hi; simp at hi; omega))
        ℓ hg hζ hl
      refine ⟨n, fun q hq i hi => ((hn q hq).1).trans ?_⟩
      have hle : ℓ ≤ pL.succAbove i := by
        rw [Fin.le_def, hℓv, val_succAbove_ge (hLneg i hi)]
        have := hLneg i hi; omega
      have := hp.isForcePath.antitone_vL hq hle
      simp only at this ⊢
      linarith
    · exact Eventually.of_forall fun ω _ => ⟨0, fun q _ i hi => absurd (hLneg i hi) (by have := i.isLt; omega)⟩
  filter_upwards [hfin, hfar, hleft] with ω hf ⟨δ, hδ, hb⟩ hl
  obtain ⟨n₂, hn₂⟩ := hl hf
  obtain ⟨n₁, hn₁⟩ := exists_nat_one_div_lt hδ
  refine ⟨hf, max n₁ n₂, fun q hq => ⟨fun i hi => ?_, fun i hi => ?_⟩⟩
  · exact ((one_div_le_of_le (le_max_left _ _)).trans hn₁.le).trans (hb q hq i hi)
  · exact (one_div_le_of_le (le_max_right _ _)).trans (hn₂ q hq i hi)

end Aug

/-! ### The event on the distinct word -/

section Dist

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}

theorem evRat_congr {pL : Fin nL → Prop} {pR : Fin nR → Prop} (w w' : ℝ≥0 → ℝ) (vL vL' : Fin nL → ℝ≥0 → ℝ)
    (vR vR' : Fin nR → ℝ≥0 → ℝ) (τ : ℝ≥0∞)
    (h : ∀ t : ℝ≥0, (t : ℝ≥0∞) < τ → w t = w' t ∧ (∀ i, vL i t = vL' i t) ∧ ∀ j, vR j t = vR' j t)
    (hw : EvRat pL pR w vL vR τ) : EvRat pL pR w' vL' vR' τ := by
  obtain ⟨hτ, n, hn⟩ := hw
  refine ⟨hτ, n, fun q hq => ⟨fun i hi => ?_, fun i hi => ?_⟩⟩
  · rw [← (h q hq).1, ← (h q hq).2.2 i]; exact (hn q hq).1 i hi
  · rw [← (h q hq).1, ← (h q hq).2.1 i]; exact (hn q hq).2 i hi

theorem measurableSet_evRat (pL : Fin nL → Prop) (pR : Fin nR → Prop) :
    MeasurableSet {x : Sec2.Assembly.XCode nL nR | EvRat pL pR (Sec2.Assembly.cw x) (Sec2.Assembly.cvL x)
      (Sec2.Assembly.cvR x) (Sec2.Assembly.cζ x)} := by
  classical
  open Sec2.Assembly in
  have e : {x : XCode nL nR | EvRat pL pR (cw x) (cvL x) (cvR x) (cζ x)} = {x : XCode nL nR | cζ x < ⊤} ∩
      ⋃ n : ℕ, ⋂ q : ℚ≥0, ({x : XCode nL nR | ¬ (((q : ℝ≥0) : ℝ≥0∞) < cζ x)} ∪
        ((⋂ i ∈ univ.filter pR, {x : XCode nL nR | 1 / ((n : ℝ) + 1) ≤ cvR x i q - cw x q}) ∩
          ⋂ i ∈ univ.filter pL, {x : XCode nL nR | 1 / ((n : ℝ) + 1) ≤ cw x q - cvL x i q})) := by
    ext x
    simp only [EvRat, mem_ofPred_eq, mem_inter_iff, mem_iUnion, mem_iInter, mem_union, mem_filter,
      Finset.mem_univ, true_and]
    refine and_congr Iff.rfl (exists_congr fun n => forall_congr' fun q => ?_)
    tauto
  rw [e]
  refine (measurableSet_lt Sec2.Assembly.measurable_cζ measurable_const).inter
    (MeasurableSet.iUnion fun n => MeasurableSet.iInter fun q => ?_)
  refine (measurableSet_lt measurable_const Sec2.Assembly.measurable_cζ).compl.union
    ((MeasurableSet.biInter (Set.to_countable _) fun i _ => ?_).inter
      (MeasurableSet.biInter (Set.to_countable _) fun i _ => ?_))
  · exact measurableSet_le measurable_const ((Sec2.Assembly.measurable_dec_at
      (Sec2.Assembly.measurable_code_vR i) q).sub (Sec2.Assembly.measurable_dec_at Sec2.Assembly.measurable_code_w q))
  · exact measurableSet_le measurable_const (measurable_gap_at i q)

/-- The left passive position: just after the marks at `0`, strictly between them and the next mark. -/
theorem exists_left_passive (hD : LP.IsDistinctForceWord xL xR) :
    ∃ (pL : Fin (nL + 1)) (yL : ℝ), yL < 0 ∧ (∀ i : Fin nL, (i : ℕ) < pL → yL < xL i) ∧
      (∀ i : Fin nL, (pL : ℕ) ≤ i → xL i < yL) ∧ (∀ i : Fin nL, xL i < 0 → (pL : ℕ) ≤ i) := by
  obtain ⟨⟨-, hL0, -, -⟩, hanti, -⟩ := hD
  by_cases h0 : ∃ i, xL i = 0
  · obtain ⟨i₀, hi₀⟩ := h0
    have hn : 0 < nL := lt_of_le_of_lt (Nat.zero_le _) i₀.isLt
    have hx0 : xL ⟨0, hn⟩ = 0 :=
      le_antisymm (hL0 _) (hi₀ ▸ hanti.antitone (show (⟨0, hn⟩ : Fin nL) ≤ i₀ by rw [Fin.le_def]; exact Nat.zero_le _))
    have hneg : ∀ i : Fin nL, 1 ≤ (i : ℕ) → xL i < 0 := fun i hi => by
      rw [← hx0]; exact hanti (show (⟨0, hn⟩ : Fin nL) < i by rw [Fin.lt_def]; simp; omega)
    by_cases h1 : 1 < nL
    · refine ⟨⟨1, by omega⟩, xL ⟨1, h1⟩ / 2, by linarith [hneg ⟨1, h1⟩ le_rfl], fun i hi => ?_,
        fun i hi => ?_, fun i hi => ?_⟩
      · have : i = ⟨0, hn⟩ := Fin.ext (by simp at hi; omega)
        rw [this, hx0]; linarith [hneg ⟨1, h1⟩ le_rfl]
      · have h2 : xL i ≤ xL ⟨1, h1⟩ := hanti.antitone (show (⟨1, h1⟩ : Fin nL) ≤ i by rw [Fin.le_def]; simpa using hi)
        linarith [hneg ⟨1, h1⟩ le_rfl]
      · by_contra hc
        have : i = ⟨0, hn⟩ := Fin.ext (by simp at hc; omega)
        rw [this, hx0] at hi; exact lt_irrefl _ hi
    · refine ⟨⟨1, by omega⟩, -1, by norm_num, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩
      · have : i = ⟨0, hn⟩ := Fin.ext (by simp at hi; omega)
        rw [this, hx0]; norm_num
      · exfalso; have := i.isLt; simp at hi; omega
      · by_contra hc
        have : i = ⟨0, hn⟩ := Fin.ext (by have := i.isLt; simp at hc; omega)
        rw [this, hx0] at hi; exact lt_irrefl _ hi
  · push Not at h0
    have hneg : ∀ i, xL i < 0 := fun i => lt_of_le_of_ne (hL0 i) (h0 i)
    by_cases hn : 0 < nL
    · refine ⟨0, xL ⟨0, hn⟩ / 2, by linarith [hneg ⟨0, hn⟩], fun i hi => absurd hi (by simp), fun i _ => ?_,
        fun i _ => by simp⟩
      have : xL i ≤ xL ⟨0, hn⟩ := hanti.antitone (show (⟨0, hn⟩ : Fin nL) ≤ i by rw [Fin.le_def]; exact Nat.zero_le _)
      linarith [hneg ⟨0, hn⟩]
    · exact ⟨0, -1, by norm_num, fun i => absurd i.isLt (by omega), fun i => absurd i.isLt (by omega),
        fun i => absurd i.isLt (by omega)⟩

/-- The right passive position: strictly between the mark before `J` (or `0`) and `x_J > 0`. -/
theorem exists_right_passive (hD : LP.IsDistinctForceWord xL xR) (J : Fin nR) (hJ0 : 0 < xR J) :
    ∃ yR : ℝ, 0 < yR ∧ (∀ i : Fin nR, (i : ℕ) < J → xR i < yR) ∧ (∀ i : Fin nR, (J : ℕ) ≤ i → yR < xR i) := by
  obtain ⟨⟨-, -, -, hR0⟩, -, hmono⟩ := hD
  by_cases hJ : 0 < (J : ℕ)
  · set lo := xR ⟨(J : ℕ) - 1, by omega⟩
    have hlo : lo < xR J := hmono (show (⟨(J : ℕ) - 1, _⟩ : Fin nR) < J by rw [Fin.lt_def]; simp; omega)
    refine ⟨(lo + xR J) / 2, by linarith [hR0 ⟨(J : ℕ) - 1, by omega⟩], fun i hi => ?_, fun i hi => ?_⟩
    · have : xR i ≤ lo := hmono.monotone (show i ≤ ⟨(J : ℕ) - 1, _⟩ by rw [Fin.le_def]; simp; omega)
      linarith
    · have : xR J ≤ xR i := hmono.monotone (show J ≤ i by rw [Fin.le_def]; exact hi)
      linarith
  · refine ⟨xR J / 2, by linarith, fun i hi => absurd hi (by omega), fun i hi => ?_⟩
    have : xR J ≤ xR i := hmono.monotone (show J ≤ i by rw [Fin.le_def]; exact hi)
    linarith

/-- **BR3's bounded reference for a distinct word (reflected form).** For `κ > 4` and a distinct separated word with a
right group end `J` (`x_J > 0`; right partial sums `> −2` before `J`, `≤ −2` at `J`; weights `0` beyond `J`) and left
partial sums all `> −2`, at least `κ/2 − 2` at the marks strictly left of `0`: every integrated evolution almost surely
has a finite lifetime before which the right marks beyond `J` and the left marks strictly left of `0` stay at a positive
distance from the driver. -/
theorem ae_event_dist (hT13 : Exist.Theorem13Statement.{0}) (hκ : 4 < κ) (hD : LP.IsDistinctForceWord xL xR)
    (hsep : ∀ i i', xL i < xR i') (J : Fin nR) (hJ0 : 0 < xR J) (hLpre : ∀ v ≤ nL, -2 < pre ρL v)
    (hLc : ∀ i : Fin nL, xL i < 0 → κ / 2 - 2 ≤ pre ρL (i + 1)) (hRpre : ∀ v ≤ (J : ℕ), -2 < pre ρR v)
    (hRJ : pre ρR (J + 1) ≤ -2) (hRfar : ∀ i, J < i → ρR i = 0) {Ω : Type u} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ζ ω < ⊤ ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω →
      (∀ i, J < i → δ ≤ VR i t ω - W t ω) ∧ (∀ i, xL i < 0 → δ ≤ W t ω - VL i t ω) := by
  have hκ0 : 0 < κ := by linarith
  obtain ⟨pL, yL, hyL, hLlo, hLhi, hLneg⟩ := exists_left_passive hD
  obtain ⟨yR, hyR, hRlo, hRhi⟩ := exists_right_passive hD J hJ0
  obtain ⟨hD', -⟩ := aug_distinct_sep hD hsep J pL hyL hyR hLlo hLhi hRlo hRhi
  obtain ⟨Ω₀, mΩ₀, P₀, hP₀, 𝓕₀, W₀, VL₀, VR₀, B₀, ζ₀, hE₀⟩ := exists_isIntegratedSLEEvolution_assembled hκ0 hD'.1
    (ρL := Fin.insertNth (α := fun _ => ℝ) pL 0 ρL) (ρR := Fin.insertNth (α := fun _ => ℝ) J.castSucc 0 ρR)
  have hEv₀ := ae_evRat_aug hT13 hκ hD hsep J hLpre hLc hRpre hRJ hRfar pL hyL hyR hLlo hLhi hLneg hRlo hRhi hE₀
  -- the augmented evolution without its passive marks is an evolution of the word
  have hzL : ∀ i, i ∉ Set.range (Fin.succAboveOrderEmb pL) → Fin.insertNth (α := fun _ => ℝ) pL 0 ρL i = 0 := by
    intro i hi
    rcases Fin.eq_self_or_eq_succAbove pL i with rfl | ⟨k, rfl⟩
    · simp
    · exact absurd ⟨k, rfl⟩ hi
  have hzR : ∀ i, i ∉ Set.range (Fin.succAboveOrderEmb J.castSucc) →
      Fin.insertNth (α := fun _ => ℝ) J.castSucc 0 ρR i = 0 := by
    intro i hi
    rcases Fin.eq_self_or_eq_succAbove J.castSucc i with rfl | ⟨k, rfl⟩
    · simp
    · exact absurd ⟨k, rfl⟩ hi
  have hE₁ := hE₀.compEmb (Fin.succAboveOrderEmb pL) (Fin.succAboveOrderEmb J.castSucc) hzL hzR
  have e1 : (fun j => Fin.insertNth (α := fun _ => ℝ) pL yL xL (Fin.succAboveOrderEmb pL j)) = xL := by
    funext j; simp
  have e2 : (fun j => Fin.insertNth (α := fun _ => ℝ) J.castSucc yR xR (Fin.succAboveOrderEmb J.castSucc j)) =
      xR := by funext j; simp
  have e3 : (fun j => Fin.insertNth (α := fun _ => ℝ) pL 0 ρL (Fin.succAboveOrderEmb pL j)) = ρL := by
    funext j; simp
  have e4 : (fun j => Fin.insertNth (α := fun _ => ℝ) J.castSucc 0 ρR (Fin.succAboveOrderEmb J.castSucc j)) =
      ρR := by funext j; simp
  rw [e1, e2, e3, e4] at hE₁
  -- the canonical law of the complementary event
  set Ψ : (ℝ≥0 → ℝ) → (Fin nL → ℝ≥0 → ℝ) → (Fin nR → ℝ≥0 → ℝ) → ℝ≥0∞ → Prop :=
    fun w vL vR τ => ¬ EvRat (fun i => xL i < 0) (fun i => J < i) w vL vR τ with hΨ
  have hS := (measurableSet_evRat (nL := nL) (nR := nR) (fun i => xL i < 0) (fun i => J < i)).compl
  have hcong : ∀ (w w' : ℝ≥0 → ℝ) (vL vL' : Fin nL → ℝ≥0 → ℝ) (vR vR' : Fin nR → ℝ≥0 → ℝ) (τ : ℝ≥0∞),
      (∀ t : ℝ≥0, (t : ℝ≥0∞) < τ → w t = w' t ∧ (∀ i, vL i t = vL' i t) ∧ ∀ j, vR j t = vR' j t) →
      Ψ w vL vR τ → Ψ w' vL' vR' τ := fun w w' vL vL' vR vR' τ h hw hw' =>
    hw (evRat_congr w' w vL' vL vR' vR τ (fun t ht => ⟨((h t ht).1).symm, fun i => ((h t ht).2.1 i).symm,
      fun j => ((h t ht).2.2 j).symm⟩) hw')
  have e₁ := ZhanGT4.measure_eventOf_eq_codeLaw_state hκ0 hsep hE hS (Ψ := Ψ) (fun _ _ _ => Iff.rfl) hcong
  have e₂ := ZhanGT4.measure_eventOf_eq_codeLaw_state hκ0 hsep hE₁ hS (Ψ := Ψ) (fun _ _ _ => Iff.rfl) hcong
  have h0 : P₀ {ω | Ψ (fun t => W₀ t ω) (fun i t => VL₀ (Fin.succAboveOrderEmb pL i) t ω)
      (fun j t => VR₀ (Fin.succAboveOrderEmb J.castSucc j) t ω) (ζ₀ ω)} = 0 := ae_iff.1 hEv₀
  rw [e₂] at h0
  rw [h0] at e₁
  have hae : ∀ᵐ ω ∂P, EvRat (fun i => xL i < 0) (fun i => J < i) (fun t => W t ω) (fun i t => VL i t ω)
      (fun j t => VR j t ω) (ζ ω) := ae_iff.2 e₁
  -- from rational to real times
  filter_upwards [hae, hE.ae_isIntegratedSLEPath] with ω ⟨hζ, n, hn⟩ hp
  refine ⟨hζ, 1 / ((n : ℝ) + 1), by positivity, fun t ht => ⟨fun i hi => ?_, fun i hi => ?_⟩⟩
  · have hc : ContinuousOn (fun s => VR i s ω - W s ω) (Icc 0 t) :=
      ((hp.isForcePath.continuousOn_vR i).sub hp.isForcePath.continuousOn_w).mono fun s hs =>
        lt_of_le_of_lt (ENNReal.coe_le_coe.2 hs.2) ht
    exact le_of_forall_rat_le (f := fun s => VR i s ω - W s ω) hc
      (fun q hq => (hn q (lt_of_le_of_lt (ENNReal.coe_le_coe.2 hq) ht)).1 i hi) le_rfl
  · have hc : ContinuousOn (fun s => W s ω - VL i s ω) (Icc 0 t) :=
      (hp.isForcePath.continuousOn_w.sub (hp.isForcePath.continuousOn_vL i)).mono fun s hs =>
        lt_of_le_of_lt (ENNReal.coe_le_coe.2 hs.2) ht
    exact le_of_forall_rat_le (f := fun s => W s ω - VL i s ω) hc
      (fun q hq => (hn q (lt_of_le_of_lt (ENNReal.coe_le_coe.2 hq) ht)).2 i hi) le_rfl

end Dist

end BR3Ref

end Theorem14

end InteractingSLE
