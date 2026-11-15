/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop59NodeTreeSched
import InteractingSLE.Spec.Sec5.Prop59SystemInit

/-!
# The initial word of a node experiment

Packet PROVE-PROP59-NODETREE. Specification §5.2, proof of Proposition 5.9 (p. 146: "The weights produced by the
previous angle changes satisfy `ρ^{i,R} = (χ/λ)(θ_{j−i+1} − θ_{j−i})`, `ρ^{i,L} = −ρ^{i,R}`"; p. 144, Figure 5.8, and
the strict-height check: at angle `+π/2` the far totals are `κ − 4` and `κ/2 − 2`). A node experiment starts at the tip
of the node prefix (the schedule `s`, PROVE-PROP59-NODES §5.1 item 5); its initial word is

* the root word of the chart-`Q` flow line at the node's **first** angle `θ₀` (the flow word at `θ₀`, then the
  junction weights `κ − 4 − Σρ_L(π/2)` and `κ/2 − 2 − Σρ_R(π/2)` of the root word, R57: the junction geometry does not
  depend on the angle, so the far total at angle `θ₀` is `κ − 4 + (π/2 − θ₀)χ/λ`), `nodeρL0`, `nodeρR0`;
* preceded by the weights born at the node's switches (one at the end of each piece of `s`; the last one, at the
  terminal time, switches to the experiment's first angle `+π/2`): `bornL`, `bornR`, the most recent next to the
  driver (`consAlt`, as the stage words of PROVE-PROP59T3).

**`isStageInit_nodeρ`**: the node word satisfies `IsStageInit` (the born partial sums telescope to
`∓(χ/λ)(π/2 − θ_i) ∈ [κ/2 − 2, 0]` resp. `[0, 2 − κ/2]`; beyond them the word is the root word shifted at its first
weight by `±(π/2 − θ₀)χ/λ`, which the born total cancels).
-/

set_option autoImplicit false

noncomputable section

open Finset
open QuantumZipper (chiC)
open scoped Real

namespace InteractingSLE.Sec5.Prop59NodeTree

open Prop513TreeExtract Prop59Stage Prop59System CrossCond.Word49 Restart

/-! ### Angles and born weights -/

/-- The angle of a flag (`true` is `+π/2`). -/
def flagAngle (b : Bool) : ℝ := if b then π / 2 else -(π / 2)

/-- **The left weight born at the switch `k`** of the flags `fl`: `−(χ/λ)(θ_{k+1} − θ_k)`. -/
def bornL (κ : ℝ) (fl : ℕ → Bool) (k : ℕ) : ℝ := -((flagAngle (fl (k + 1)) - flagAngle (fl k)) * (chiC κ / sleLambda κ))

/-- **The right weight born at the switch `k`**: `(χ/λ)(θ_{k+1} − θ_k)`. -/
def bornR (κ : ℝ) (fl : ℕ → Bool) (k : ℕ) : ℝ := (flagAngle (fl (k + 1)) - flagAngle (fl k)) * (chiC κ / sleLambda κ)

theorem half_pi_sub_flagAngle (b : Bool) : π / 2 - flagAngle b = if b then 0 else π := by
  cases b <;> simp only [flagAngle, Bool.false_eq_true, ↓reduceIte] <;> ring

/-- **The born weights telescope.** -/
theorem sum_bornL (κ : ℝ) (fl : ℕ → Bool) (m : ℕ) :
    ∀ k, k ≤ m → ∑ i ∈ range k, bornL κ fl (m - 1 - i) =
      -((flagAngle (fl m) - flagAngle (fl (m - k))) * (chiC κ / sleLambda κ))
  | 0, _ => by simp
  | k + 1, hk => by
    rw [sum_range_succ, sum_bornL κ fl m k (by omega), bornL, show m - 1 - k + 1 = m - k by omega,
      show m - (k + 1) = m - 1 - k by omega]
    ring

theorem sum_bornR (κ : ℝ) (fl : ℕ → Bool) (m : ℕ) (k : ℕ) (hk : k ≤ m) :
    ∑ i ∈ range k, bornR κ fl (m - 1 - i) = (flagAngle (fl m) - flagAngle (fl (m - k))) * (chiC κ / sleLambda κ) := by
  have h := sum_bornL κ fl m k hk
  have e : ∀ i, bornR κ fl i = -bornL κ fl i := fun i => by rw [bornL, bornR, neg_neg]
  simp only [e, sum_neg_distrib] at h ⊢
  linarith

/-! ### The words -/

section Words

variable (κ : ℝ) (c : BoundaryWord)

/-- **The left root word at the first angle `θ`**: the chart-`Q` flow word at `θ`, then the root junction weight. -/
def nodeρL0 (θ : ℝ) : Fin (rootNL c) → ℝ :=
  Fin.snoc (flowLineRhoL κ c.fn c.jumps 0 θ) (cL6 κ (∑ i, flowLineRhoL κ c.fn c.jumps 0 (π / 2) i))

/-- **The right root word at the first angle `θ`.** -/
def nodeρR0 (θ : ℝ) : Fin (rootNR c) → ℝ :=
  Fin.snoc (flowLineRhoR κ c.fn c.jumps 0 θ) (cR6 κ (∑ j, flowLineRhoR κ c.fn c.jumps 0 (π / 2) j))

/-- **The left initial word of the node experiment of `s`.** -/
def nodeρL (s : Schedule) : Fin (rootNL c + nodeLen s) → ℝ :=
  consAlt (bornL κ (nodeFlag s)) (nodeρL0 κ c (flagAngle (nodeFlag s 0))) (nodeLen s)

/-- **The right initial word of the node experiment of `s`.** -/
def nodeρR (s : Schedule) : Fin (rootNR c + nodeLen s) → ℝ :=
  consAlt (bornR κ (nodeFlag s)) (nodeρR0 κ c (flagAngle (nodeFlag s 0))) (nodeLen s)

theorem nodeρL0_half_pi : nodeρL0 κ c (π / 2) = rootρL κ c := rfl

theorem nodeρR0_half_pi : nodeρR0 κ c (π / 2) = rootρR κ c := rfl

end Words

/-! ### The first weight depends on the angle -/

theorem flowLineRhoL_sub (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (x θ θ' : ℝ) :
    ∀ i : Fin (flowLineNL b jumps x), flowLineRhoL κ b jumps x θ i - flowLineRhoL κ b jumps x θ' i =
      if (i : ℕ) = 0 then (θ' - θ) * (chiC κ / sleLambda κ) else 0 := by
  unfold flowLineRhoL flowLineNL
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [Fin.cons_zero, Fin.val_zero, ↓reduceIte]
    ring
  · simp only [Fin.cons_succ, sub_self, Fin.val_succ, Nat.add_one_ne_zero, ↓reduceIte]

theorem flowLineRhoR_sub (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (x θ θ' : ℝ) :
    ∀ i : Fin (flowLineNR b jumps x), flowLineRhoR κ b jumps x θ i - flowLineRhoR κ b jumps x θ' i =
      if (i : ℕ) = 0 then (θ - θ') * (chiC κ / sleLambda κ) else 0 := by
  unfold flowLineRhoR flowLineNR
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [Fin.cons_zero, Fin.val_zero, ↓reduceIte]
    ring
  · simp only [Fin.cons_succ, sub_self, Fin.val_succ, Nat.add_one_ne_zero, ↓reduceIte]

/-- Prefix sums of two words differing only at the first weight. -/
theorem psum_eq_of_sub_first {n : ℕ} (ρ ρ' : Fin n → ℝ) (δ : ℝ)
    (h : ∀ i, ρ' i - ρ i = if (i : ℕ) = 0 then δ else 0) (hn : 0 < n) {k : ℕ} (hk : 1 ≤ k) :
    psum ρ' k = psum ρ k + δ := by
  rw [psum_eq_sum_ite, psum_eq_sum_ite]
  have e : ∀ i : Fin n, (if (i : ℕ) < k then ρ' i else 0) =
      (if (i : ℕ) < k then ρ i else 0) + if i = ⟨0, hn⟩ then δ else 0 := by
    intro i
    have hi := h i
    by_cases hik : (i : ℕ) < k
    · by_cases hi0 : i = ⟨0, hn⟩
      · subst hi0
        simp only [hik, ↓reduceIte] at hi ⊢
        linarith
      · have hv : (i : ℕ) ≠ 0 := fun hv => hi0 (Fin.ext hv)
        simp only [hik, hv, hi0, ↓reduceIte, add_zero] at hi ⊢
        linarith
    · have hi0 : i ≠ ⟨0, hn⟩ := fun he => hik (by rw [he]; exact hk)
      simp only [hik, hi0, ↓reduceIte, add_zero]
  rw [sum_congr rfl fun i _ => e i, sum_add_distrib, sum_ite_eq' univ (⟨0, hn⟩ : Fin n)]
  simp only [mem_univ, ↓reduceIte]

theorem flowLineNL_pos (b : ℝ → ℝ) (jumps : Finset ℝ) (x : ℝ) : 0 < flowLineNL b jumps x := by
  unfold flowLineNL; omega

theorem flowLineNR_pos (b : ℝ → ℝ) (jumps : Finset ℝ) (x : ℝ) : 0 < flowLineNR b jumps x := by
  unfold flowLineNR; omega

section Shift

variable (κ : ℝ) (c : BoundaryWord) (θ : ℝ)

theorem psum_nodeρL0 {k : ℕ} (hk : 1 ≤ k) :
    psum (nodeρL0 κ c θ) k = psum (rootρL κ c) k + (π / 2 - θ) * (chiC κ / sleLambda κ) := by
  refine psum_eq_of_sub_first _ _ _ (fun i => ?_) (rootNL_pos c) hk
  refine Fin.lastCases ?_ (fun j => ?_) i
  · have hne : (Fin.last (flowLineNL c.fn c.jumps 0) : ℕ) ≠ 0 := by
      simp only [Fin.val_last]; exact (flowLineNL_pos _ _ _).ne'
    simp only [nodeρL0, rootρL, jwL, Fin.snoc_last, sub_self, hne, ↓reduceIte]
  · simp only [nodeρL0, rootρL, jwL, Fin.snoc_castSucc, Fin.val_castSucc]
    exact flowLineRhoL_sub κ c.fn c.jumps 0 θ (π / 2) j

theorem psum_nodeρR0 {k : ℕ} (hk : 1 ≤ k) :
    psum (nodeρR0 κ c θ) k = psum (rootρR κ c) k + (θ - π / 2) * (chiC κ / sleLambda κ) := by
  refine psum_eq_of_sub_first _ _ _ (fun i => ?_) (rootNR_pos c) hk
  refine Fin.lastCases ?_ (fun j => ?_) i
  · have hne : (Fin.last (flowLineNR c.fn c.jumps 0) : ℕ) ≠ 0 := by
      simp only [Fin.val_last]; exact (flowLineNR_pos _ _ _).ne'
    simp only [nodeρR0, rootρR, jwR, Fin.snoc_last, sub_self, hne, ↓reduceIte]
  · simp only [nodeρR0, rootρR, jwR, Fin.snoc_castSucc, Fin.val_castSucc]
    exact flowLineRhoR_sub κ c.fn c.jumps 0 θ (π / 2) j

end Shift

/-! ### The initial-word conditions -/

theorem chiC_div_sleLambda {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) :
    0 < chiC κ / sleLambda κ ∧ π * (chiC κ / sleLambda κ) = 2 - κ / 2 := by
  have h1 := angleWeightBound_eq hκ
  have h2 := angleWeightBound_pos hκ hκ4
  have e : angleWeightBound κ = π * (chiC κ / sleLambda κ) := by rw [angleWeightBound, mul_div_assoc]
  rw [e] at h1 h2
  exact ⟨pos_of_mul_pos_right h2 Real.pi_pos.le, h1⟩

/-- **The node word satisfies the initial-word conditions** for every node schedule and every chart-`Q` word whose
root word satisfies them. -/
theorem isStageInit_nodeρ {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {c : BoundaryWord}
    (hc : IsStageInit κ (rootρL κ c) (rootρR κ c)) (s : Schedule) :
    IsStageInit κ (nodeρL κ c s) (nodeρR κ c s) := by
  obtain ⟨hL, hR, hLp, hRp⟩ := hc
  obtain ⟨hr, hrπ⟩ := chiC_div_sleLambda hκ hκ4
  set r := chiC κ / sleLambda κ with hrdef
  set m := nodeLen s with hm
  set θ₀ := flagAngle (nodeFlag s 0) with hθ₀
  have hfm : flagAngle (nodeFlag s m) = π / 2 := by
    rw [show m = nodeLen s + 0 from rfl, nodeFlag_add]; rfl
  have hm0 : 0 < m := nodeLen_pos
  have hθ0 : flagAngle (nodeFlag s (m - m)) = θ₀ := by rw [Nat.sub_self]
  -- the born partial sums at angle `+π/2`
  have hbL : ∀ k, k ≤ m → -(π / 2 - flagAngle (nodeFlag s (m - k))) * r ≥ κ / 2 - 2 ∧
      -(π / 2 - flagAngle (nodeFlag s (m - k))) * r ≤ 0 := fun k _ => by
    rw [half_pi_sub_flagAngle]
    split_ifs <;> constructor <;> nlinarith
  refine ⟨?_, ?_, fun k hk1 hk => ?_, fun k hk1 hk => ?_⟩
  · rw [nodeρL, psum_consAlt, min_eq_right (by omega), Nat.add_sub_cancel, sum_bornL κ _ m m le_rfl, hfm, hθ0,
      psum_nodeρL0 κ c θ₀ (rootNL_pos c), hL]
    ring
  · rw [nodeρR, psum_consAlt, min_eq_right (by omega), Nat.add_sub_cancel, sum_bornR κ _ m m le_rfl, hfm, hθ0,
      psum_nodeρR0 κ c θ₀ (rootNR_pos c), hR]
    ring
  · rw [nodeρL, psum_consAlt]
    by_cases hkm : k ≤ m
    · rw [min_eq_left hkm, Nat.sub_eq_zero_of_le hkm, psum_zero, add_zero, sum_bornL κ _ m k hkm, hfm]
      linarith [(hbL k hkm).1]
    · rw [min_eq_right (by omega), sum_bornL κ _ m m le_rfl, hfm, hθ0, psum_nodeρL0 κ c θ₀ (by omega)]
      have := hLp (k - m) (by omega) (by simp only [rootNL] at hk ⊢; omega)
      linarith
  · rw [nodeρR, psum_consAlt]
    by_cases hkm : k ≤ m
    · rw [min_eq_left hkm, Nat.sub_eq_zero_of_le hkm, psum_zero, add_zero, sum_bornR κ _ m k hkm, hfm]
      have := (hbL k hkm).2
      linarith
    · rw [min_eq_right (by omega), sum_bornR κ _ m m le_rfl, hfm, hθ0, psum_nodeρR0 κ c θ₀ (by omega)]
      have := hRp (k - m) (by omega) (by simp only [rootNR] at hk ⊢; omega)
      linarith

end InteractingSLE.Sec5.Prop59NodeTree
