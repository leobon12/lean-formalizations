/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.TrialsHiEnergy
import InteractingSLE.Spec.Sec7.TrialsHiReduce
import InteractingSLE.Spec.Zhan.WordsTail
import InteractingSLE.Spec.Sec4.ZeroMarks

/-!
# Aux. lemmas 109 and 111, driver form: the uniform trial bound from one reference law

Packet PROVE-TRIALS-HI. Specification §7.3, Aux. lemma 109 (`source/spec/p337-384.md` L504–L559, pp. 360–363) and
Aux. lemma 111 (L588–L655, pp. 364–367): "We first construct one reference law with a positive-probability successful
event … Uniform transfer of the successful event … `P_f(E) ≥ P₀(E)² e^{−‖f‖²_∇} ≥ p₀² e^{−C} > 0`."

Here the comparison of Aux. lemma 108 is made on the driving process (`measure_horizonEvent_le`), and the energy of
the change of weights is bounded by the side oscillations (`changeEnergy_le_osc`) instead of the Dirichlet energy of a
cut-off harmonic function. For a midpoint word `y` (nearest marks at `∓1`, all marks in `[−M, M]`) the **combined
word** appends a barrier mark at `−M` and at `M` (`combL`, `combR`). The proposed weights put `ρ` on `y` and `0` on the
barriers (`propW`); the reference weights put `σ_L(0), σ_R(0)` on the nearest marks `∓1`, `σ_L(1), σ_R(1)` on the
barriers and `0` elsewhere (`refW`). The reference law is the law of the **four-mark word** `(−1, −M; 1, M)` with the
weights `σ` (deleting the zero-weight marks, `IsIntegratedSLEEvolution.compEmb`), the same for every `y`. When the side
totals of `σ` and `ρ` agree, the energy of the change is bounded on the reference success event, and

  `codeLaw ρ ntCodeSet (y) ≤ 1 − e^{−m} p₀²`  (`uniformTrialBound_of_reference`),

where `p₀` is the probability of the **reference success event** (`RefGood`): infinite lifetime, the nearest reference
marks never hit, both side oscillations at most `C`, and the trace at rational times beyond `K(R)` outside the disc of
radius `R` (a quantitative transience). This holds for every `κ > 0`.

* For `κ ≥ 4` and side totals `≥ κ/2 − 2` Aux. lemma 111's references are `σ = (s_L, 0; s_R, 0)` (inner marks); for
  `κ < 4` Aux. lemma 109's are `σ = (0, s_L; 0, s_R)` (outer marks). The positivity of the reference success event
  (`RefTrialPositivity`) is a statement about one fixed four-mark law and is the named input that remains.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec7

namespace TrialsHi

open ZhanGT4 Zhan Sec2 Sec2.Assembly Sec2.Restart Sec7.RandRestart Girsanov Coupling

variable {nL nR : ℕ}

/-! ### Combined words -/

section Combined

variable {n : ℕ}

/-- The left positions of the combined word: `yL` followed by the barrier `−M`. -/
def combL (yL : Fin (n + 1) → ℝ) (M : ℝ) : Fin (n + 1 + 1) → ℝ := Fin.snoc (α := fun _ => ℝ) yL (-M)

/-- The right positions of the combined word: `yR` followed by the barrier `M`. -/
def combR (yR : Fin (n + 1) → ℝ) (M : ℝ) : Fin (n + 1 + 1) → ℝ := Fin.snoc (α := fun _ => ℝ) yR M

/-- The proposed weights on the combined word: `ρ`, and `0` at the barrier. -/
def propW (ρ : Fin (n + 1) → ℝ) : Fin (n + 1 + 1) → ℝ := Fin.snoc (α := fun _ => ℝ) ρ 0

/-- The reference weights on the combined word: `σ 0` at the nearest mark, `σ 1` at the barrier, `0` between. -/
def refW (σ : Fin 2 → ℝ) : Fin (n + 1 + 1) → ℝ := fun i =>
  if i = 0 then σ 0 else if i = Fin.last (n + 1) then σ 1 else 0

theorem combL_castSucc (yL : Fin (n + 1) → ℝ) (M : ℝ) (i : Fin (n + 1)) : combL yL M i.castSucc = yL i := by
  simp [combL]

theorem combL_last (yL : Fin (n + 1) → ℝ) (M : ℝ) : combL yL M (Fin.last (n + 1)) = -M := by simp [combL]

theorem combR_castSucc (yR : Fin (n + 1) → ℝ) (M : ℝ) (i : Fin (n + 1)) : combR yR M i.castSucc = yR i := by
  simp [combR]

theorem combR_last (yR : Fin (n + 1) → ℝ) (M : ℝ) : combR yR M (Fin.last (n + 1)) = M := by simp [combR]

theorem propW_castSucc (ρ : Fin (n + 1) → ℝ) (i : Fin (n + 1)) : propW ρ i.castSucc = ρ i := by simp [propW]

theorem propW_last (ρ : Fin (n + 1) → ℝ) : propW ρ (Fin.last (n + 1)) = 0 := by simp [propW]

theorem castSucc_zero' : ((0 : Fin (n + 1)).castSucc : Fin (n + 1 + 1)) = 0 := rfl

theorem zero_ne_last' : (0 : Fin (n + 1 + 1)) ≠ Fin.last (n + 1) := by
  intro h
  have := congrArg Fin.val h
  simp at this

/-- The embedding of the two reference positions (nearest mark, barrier) into the combined word. -/
def refEmb (n : ℕ) : Fin 2 ↪o Fin (n + 1 + 1) :=
  OrderEmbedding.ofStrictMono (fun j => if j = 0 then 0 else Fin.last (n + 1)) (by
    intro a b hab
    have ha : a = 0 := by
      rcases Fin.exists_fin_two.1 ⟨a, rfl⟩ with h | h
      · exact h
      · subst h; exact absurd hab (not_lt.2 (Fin.le_last b))
    have hb : b = 1 := by
      rcases Fin.exists_fin_two.1 ⟨b, rfl⟩ with h | h
      · subst h ha; exact absurd hab (lt_irrefl _)
      · exact h
    subst ha hb
    simp only [Fin.isValue, ↓reduceIte, one_ne_zero]
    exact Fin.last_pos)

theorem refEmb_zero : refEmb n 0 = 0 := by
  show (if (0 : Fin 2) = 0 then (0 : Fin (n + 1 + 1)) else Fin.last (n + 1)) = 0
  simp

theorem refEmb_one : refEmb n 1 = Fin.last (n + 1) := by
  show (if (1 : Fin 2) = 0 then (0 : Fin (n + 1 + 1)) else Fin.last (n + 1)) = Fin.last (n + 1)
  simp

theorem refW_refEmb (σ : Fin 2 → ℝ) (j : Fin 2) : refW (n := n) σ (refEmb n j) = σ j := by
  rcases Fin.exists_fin_two.1 ⟨j, rfl⟩ with h | h <;> subst h
  · simp [refW, refEmb_zero]
  · simp [refW, refEmb_one, zero_ne_last'.symm]

theorem refW_of_notMem (σ : Fin 2 → ℝ) {i : Fin (n + 1 + 1)} (hi : i ∉ Set.range (refEmb n)) :
    refW (n := n) σ i = 0 := by
  have h0 : i ≠ 0 := fun h => hi ⟨0, by rw [refEmb_zero, h]⟩
  have h1 : i ≠ Fin.last (n + 1) := fun h => hi ⟨1, by rw [refEmb_one, h]⟩
  simp [refW, h0, h1]

theorem propW_of_notMem (ρ : Fin (n + 1) → ℝ) {i : Fin (n + 1 + 1)}
    (hi : i ∉ Set.range (Fin.castSuccOrderEmb (n := n + 1))) : propW ρ i = 0 := by
  have : i = Fin.last (n + 1) := by
    by_contra h
    exact hi ⟨i.castPred h, by simp⟩
  rw [this, propW_last]

theorem antitone_combL {yL : Fin (n + 1) → ℝ} {M : ℝ} (hy : Antitone yL) (hM : ∀ i, -M ≤ yL i) :
    Antitone (combL yL M) := by
  intro i j hij
  induction j using Fin.lastCases with
  | last =>
    induction i using Fin.lastCases with
    | last => exact le_rfl
    | cast i => rw [combL_last, combL_castSucc]; exact hM i
  | cast j =>
    induction i using Fin.lastCases with
    | last => exact absurd hij (not_le.2 (Fin.castSucc_lt_last j))
    | cast i => rw [combL_castSucc, combL_castSucc]; exact hy (Fin.castSucc_le_castSucc_iff.1 hij)

theorem monotone_combR {yR : Fin (n + 1) → ℝ} {M : ℝ} (hy : Monotone yR) (hM : ∀ j, yR j ≤ M) :
    Monotone (combR yR M) := by
  intro i j hij
  induction j using Fin.lastCases with
  | last =>
    induction i using Fin.lastCases with
    | last => exact le_rfl
    | cast i => rw [combR_last, combR_castSucc]; exact hM i
  | cast j =>
    induction i using Fin.lastCases with
    | last => exact absurd hij (not_le.2 (Fin.castSucc_lt_last j))
    | cast i => rw [combR_castSucc, combR_castSucc]; exact hy (Fin.castSucc_le_castSucc_iff.1 hij)

/-- The combined word of an ordered word with marks in `[−M, M]` is ordered. -/
theorem isOrderedForceWord_comb {nL nR : ℕ} {yL : Fin (nL + 1) → ℝ} {yR : Fin (nR + 1) → ℝ} {M : ℝ}
    (hy : IsOrderedForceWord yL yR) (hM0 : 0 ≤ M) (hML : ∀ i, -M ≤ yL i) (hMR : ∀ j, yR j ≤ M) :
    IsOrderedForceWord (combL yL M) (combR yR M) := by
  obtain ⟨h1, h2, h3, h4⟩ := hy
  refine ⟨antitone_combL h1 hML, fun i => ?_, monotone_combR h3 hMR, fun j => ?_⟩
  · induction i using Fin.lastCases with
    | last => rw [combL_last]; linarith
    | cast i => rw [combL_castSucc]; exact h2 i
  · induction j using Fin.lastCases with
    | last => rw [combR_last]; exact hM0
    | cast j => rw [combR_castSucc]; exact h4 j

end Combined

/-! ### Sums of the combined weights -/

section Sums

variable {n : ℕ}

theorem sum_propW (ρ : Fin (n + 1) → ℝ) : ∑ i, propW ρ i = ∑ i, ρ i := by
  rw [Fin.sum_univ_castSucc]
  simp [propW_castSucc, propW_last]

theorem sum_refW (σ : Fin 2 → ℝ) : ∑ i, refW (n := n) σ i = σ 0 + σ 1 := by
  have key : ∀ i, refW (n := n) σ i =
      (if i = 0 then σ 0 else 0) + (if i = Fin.last (n + 1) then σ 1 else 0) := by
    intro i
    by_cases h0 : i = 0
    · subst h0; simp [refW]
    · by_cases h1 : i = Fin.last (n + 1)
      · subst h1; simp [refW, zero_ne_last'.symm]
      · simp [refW, h0, h1]
  simp_rw [key, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- The side charges `propW ρ − refW σ` are neutral when the side totals agree. -/
theorem sum_propW_sub_refW {ρ : Fin (n + 1) → ℝ} {σ : Fin 2 → ℝ} (h : σ 0 + σ 1 = ∑ i, ρ i) :
    ∑ i, (propW ρ i - refW (n := n) σ i) = 0 := by
  rw [Finset.sum_sub_distrib, sum_propW, sum_refW, h, sub_self]

end Sums

/-! ### The reference word and its success event -/

/-- The left positions `(−1, −M)` of the four-mark reference word. -/
def refXL (M : ℝ) : Fin 2 → ℝ := ![-1, -M]

/-- The right positions `(1, M)` of the four-mark reference word. -/
def refXR (M : ℝ) : Fin 2 → ℝ := ![1, M]

/-- **The reference success event** of a path of the four-mark word `(−1, −M; 1, M)` (Aux. lemmas 109 and 111: "the
curve stays at distance at least `δ` from `I_L ∪ I_R` until it tends to infinity"): infinite lifetime, the nearest
marks `∓1` never hit, both side oscillations `∫ (1/X_near² − 1/X_barrier²)` at most `C` on every horizon, and the
trace at rational times `p ≥ K(R)` outside the closed disc of radius `R`, for every `R` (quantitative transience). -/
def RefGood (C : ℝ) (K : ℕ → ℕ) (w : ℝ≥0 → ℝ) (vL vR : Fin 2 → ℝ≥0 → ℝ) (ζ : ℝ≥0∞) : Prop :=
  ζ = ⊤ ∧ (∀ t, vL 0 t < w t ∧ w t < vR 0 t) ∧
    (∀ T, sideOsc (fun s => w s - vL 0 s) (fun s => w s - vL 1 s) T ≤ C) ∧
    (∀ T, sideOsc (fun s => vR 0 s - w s) (fun s => vR 1 s - w s) T ≤ C) ∧
    ∀ (R : ℕ) (p : ℚ≥0), (K R : ℚ≥0) ≤ p → (R : ℝ) < ‖LP.traceAt (p : ℝ≥0) w‖

/-- **Named input: positivity of the reference success event** for the four-mark word `(−1, −M; 1, M)` with weights
`σ` (the first step of Aux. lemmas 109 and 111: "We first construct one reference law with a positive-probability
successful event … Choose deterministic `δ > 0` such that this distance exceeds `4δ` with positive probability"):
constants `C`, `K` and `p₀ > 0` such that every evolution of the reference word has an almost surely infinite lifetime
and probability at least `p₀` of the reference success event. -/
def RefTrialPositivity (κ M : ℝ) (σL σR : Fin 2 → ℝ) : Prop :=
  ∃ (C : ℝ) (K : ℕ → ℕ) (p₀ : ℝ), 0 < p₀ ∧
    ∀ {Ω : Type} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P] (𝓕 : Filtration ℝ≥0 mΩ)
      (W : ℝ≥0 → Ω → ℝ) (VL VR : Fin 2 → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
      IsIntegratedSLEEvolution κ (refXL M) (refXR M) σL σR P 𝓕 W VL VR B ζ →
      (∀ᵐ ω ∂P, ζ ω = ⊤) ∧
        ENNReal.ofReal p₀ ≤ P {ω | RefGood C K (fun t => W t ω) (fun i t => VL i t ω) (fun j t => VR j t ω) (ζ ω)}

/-! ### The quantitative transience event and the non-transience event are disjoint -/

/-- The quantitative transience predicate of a driver: infinite horizon and the trace at rational times `p ≥ K(R)`
outside the closed disc of radius `R`. -/
def QTrans (K : ℕ → ℕ) (w : ℝ≥0 → ℝ) (τ : ℝ≥0∞) : Prop :=
  τ = ⊤ ∧ ∀ (R : ℕ) (p : ℚ≥0), (K R : ℚ≥0) ≤ p → (R : ℝ) < ‖LP.traceAt (p : ℝ≥0) w‖

theorem not_nonTransientEvent_of_qTrans {K : ℕ → ℕ} {w : ℝ≥0 → ℝ} (hw : Continuous w) (hw0 : w 0 = 0)
    (h : QTrans K w ⊤) : ¬ NonTransientEvent w ⊤ := by
  rw [not_nonTransientEvent_iff hw hw0]
  intro η hη
  by_contra hn
  have hηc : Continuous η := by
    have := hη.2.1
    exact continuousOn_univ.1 (this.mono fun t _ => show (t : ℝ≥0∞) ≤ ⊤ from le_top)
  obtain ⟨R, hR⟩ := exists_late_of_not_tendsto hηc hn
  obtain ⟨p, hp, hpR⟩ := hR (K R)
  have h1 := h.2 R p hp
  rw [LP.traceAt_eq_of_isGeneratingTrace hη hw.continuousOn hw0 ENNReal.coe_lt_top] at h1
  linarith

/-- The horizon version of the quantitative transience, on codes. -/
def qSet (K : ℕ → ℕ) (T : ℕ) : Set (XCode nL nR) :=
  {x | ((T : ℝ≥0) : ℝ≥0∞) ≤ cζ x ∧ ∀ (R : ℕ) (p : ℚ≥0), (K R : ℚ≥0) ≤ p → (p : ℝ≥0) < (T : ℝ≥0) →
    (R : ℝ) < ‖LP.traceAt (p : ℝ≥0) (cw x)‖}

theorem measurableSet_qSet (K : ℕ → ℕ) (T : ℕ) : MeasurableSet (qSet (nL := nL) (nR := nR) K T) := by
  have h1 : MeasurableSet {x : XCode nL nR | ((T : ℝ≥0) : ℝ≥0∞) ≤ cζ x} :=
    measurableSet_le measurable_const measurable_cζ
  have h2 : ∀ (R : ℕ) (p : ℚ≥0), MeasurableSet {x : XCode nL nR | (K R : ℚ≥0) ≤ p → (p : ℝ≥0) < (T : ℝ≥0) →
      (R : ℝ) < ‖LP.traceAt (p : ℝ≥0) (cw x)‖} := fun R p => by
    by_cases hK : (K R : ℚ≥0) ≤ p
    · by_cases hT : (p : ℝ≥0) < (T : ℝ≥0)
      · simp only [hK, hT, true_implies]
        exact measurableSet_lt measurable_const ((LP.measurable_traceAt _).comp measurable_cw).norm
      · simp [hT]
    · simp [hK]
  have e : qSet (nL := nL) (nR := nR) K T = {x | ((T : ℝ≥0) : ℝ≥0∞) ≤ cζ x} ∩
      ⋂ (R : ℕ) (p : ℚ≥0), {x | (K R : ℚ≥0) ≤ p → (p : ℝ≥0) < (T : ℝ≥0) →
        (R : ℝ) < ‖LP.traceAt (p : ℝ≥0) (cw x)‖} := by
    ext x; simp [qSet]
  rw [e]
  exact h1.inter (MeasurableSet.iInter fun R => MeasurableSet.iInter fun p => h2 R p)

theorem antitone_qSet (K : ℕ → ℕ) : Antitone fun T : ℕ => qSet (nL := nL) (nR := nR) K T := by
  intro T T' hT x ⟨h1, h2⟩
  refine ⟨le_trans (by exact_mod_cast hT) h1, fun R p hK hp => h2 R p hK (lt_of_lt_of_le hp (by exact_mod_cast hT))⟩

theorem iInter_qSet (K : ℕ → ℕ) :
    (⋂ T : ℕ, qSet (nL := nL) (nR := nR) K T) = {x | QTrans K (cw x) (cζ x)} := by
  ext x
  simp only [mem_iInter, mem_ofPred_eq]
  constructor
  · intro h
    refine ⟨?_, fun R p hK => ?_⟩
    · by_contra hne
      obtain ⟨T, hT⟩ := ENNReal.exists_nat_gt hne
      have h1 := (h T).1
      have e : ((T : ℝ≥0) : ℝ≥0∞) = (T : ℝ≥0∞) := by simp
      rw [e] at h1
      exact absurd (lt_of_lt_of_le hT h1) (lt_irrefl _)
    · obtain ⟨T, hT⟩ := exists_nat_gt ((p : ℝ≥0) : ℝ)
      exact (h T).2 R p hK (by rw [← NNReal.coe_lt_coe]; exact_mod_cast hT)
  · rintro ⟨hζ, h⟩ T
    exact ⟨by rw [hζ]; exact le_top, fun R p hK _ => h R p hK⟩

theorem qTrans_congr (K : ℕ → ℕ) (w w' : ℝ≥0 → ℝ) (τ : ℝ≥0∞)
    (h : ∀ t : ℝ≥0, (t : ℝ≥0∞) < τ → w t = w' t) (hq : QTrans K w τ) : QTrans K w' τ := by
  obtain ⟨hτ, h2⟩ := hq
  subst hτ
  have : w = w' := funext fun t => h t ENNReal.coe_lt_top
  subst this
  exact ⟨rfl, h2⟩

/-! ### One word: the reference success event transfers to the proposed weights -/

section OneWord

variable {κ : ℝ} {zL : Fin (nL + 1) → ℝ} {zR : Fin (nR + 1) → ℝ} {τL πL : Fin (nL + 1) → ℝ}
  {τR πR : Fin (nR + 1) → ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ} {VR : Fin (nR + 1) → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞}

/-- The success event of the reference evolution of a word with marks `Fin (nL + 1)`, `Fin (nR + 1)`, read on its
nearest marks (index `0`) and its outermost marks (index `last`). -/
def succEvent (C : ℝ) (K : ℕ → ℕ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ)
    (VR : Fin (nR + 1) → ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) : Set Ω :=
  {ω | ζ ω = ⊤ ∧ (∀ t, VL 0 t ω < W t ω ∧ W t ω < VR 0 t ω) ∧
    (∀ T, sideOsc (fun s => W s ω - VL 0 s ω) (fun s => W s ω - VL (Fin.last nL) s ω) T ≤ C) ∧
    (∀ T, sideOsc (fun s => VR 0 s ω - W s ω) (fun s => VR (Fin.last nR) s ω - W s ω) T ≤ C) ∧
    ∀ (R : ℕ) (p : ℚ≥0), (K R : ℚ≥0) ≤ p → (R : ℝ) < ‖LP.traceAt (p : ℝ≥0) (fun t => W t ω)‖}

/-- **Aux. lemma 108 (HBT1) in driver form, for one word.** Let the reference evolution (weights `τ`) of a separated
ordered word have an almost surely infinite lifetime, and let the proposed weights `π` have the same side totals. Then
`P(success)² ≤ e^m · codeLaw π {quantitative transience}` with `m = 2κ⁻¹ ((Σ|Δ^L|)² + (Σ|Δ^R|)²) C`. -/
theorem sq_measure_succEvent_le (hκ : 0 < κ) [IsProbabilityMeasure P] (hF : IsOrderedForceWord zL zR)
    (hsep : ∀ i j, zL i < zR j) (hE : IsIntegratedSLEEvolution κ zL zR τL τR P 𝓕 W VL VR B ζ)
    (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) (hnL : ∑ i, (πL i - τL i) = 0) (hnR : ∑ j, (πR j - τR j) = 0) (C : ℝ)
    (K : ℕ → ℕ) :
    P (succEvent C K W VL VR ζ) ^ 2 ≤
      ENNReal.ofReal (Real.exp (2 / κ * ((∑ i, |πL i - τL i|) ^ 2 * C + (∑ j, |πR j - τR j|) ^ 2 * C))) *
        codeLaw κ πL πR {x | QTrans K (cw x) (cζ x)} (zL, zR) := by
  set m : ℝ := 2 / κ * ((∑ i, |πL i - τL i|) ^ 2 * C + (∑ j, |πR j - τR j|) ^ 2 * C) with hm
  have hE𝓖 := Ito.isIntegratedSLEEvolution_usualAugmentation hE
  set Good : Ω → Prop := fun ω => ζ ω = ⊤ ∧ Continuous (fun s => stateAt W VL VR s ω) ∧
    IsIntegratedSLEPath κ zL zR τL τR (fun t => W t ω) (fun i t => VL i t ω) (fun j t => VR j t ω)
      (fun t => B t ω) (ζ ω) with hGood
  have hgood : ∀ᵐ ω ∂P, Good ω := by
    filter_upwards [hζ, hE.2.2.2.2] with ω hζω hp
    refine ⟨hζω, ?_, hp⟩
    have hf := hp.isForcePath
    have hlt : ∀ t : ℝ≥0, t ∈ {t : ℝ≥0 | (t : ℝ≥0∞) < ζ ω} := fun t => by
      show (t : ℝ≥0∞) < ζ ω; rw [hζω]; exact ENNReal.coe_lt_top
    have hw : Continuous fun t => W t ω := continuousOn_univ.1 (hf.continuousOn_w.mono fun t _ => hlt t)
    have hl : ∀ i, Continuous fun t => VL i t ω := fun i =>
      continuousOn_univ.1 ((hf.continuousOn_vL i).mono fun t _ => hlt t)
    have hr : ∀ j, Continuous fun t => VR j t ω := fun j =>
      continuousOn_univ.1 ((hf.continuousOn_vR j).mono fun t _ => hlt t)
    exact hw.prodMk ((continuous_pi hl).prodMk (continuous_pi hr))
  set N := {ω | ¬ Good ω} with hNdef
  have hN : P N = 0 := ae_iff.1 hgood
  set G := (toMeasurable P N)ᶜ with hGdef
  have hGm : MeasurableSet[usualAugmentation 𝓕 P 0] G :=
    (Ito.measurableSet_usualAugmentation_of_null (measurableSet_toMeasurable P N)
      (by rw [measure_toMeasurable]; exact hN) 0).compl
  have hGgood : ∀ ω ∈ G, Good ω := fun ω hω => by
    by_contra h
    exact hω (subset_toMeasurable P N h)
  have hGc : P Gᶜ = 0 := by rw [hGdef, compl_compl, measure_toMeasurable]; exact hN
  -- one horizon
  set Φ : ℕ → (ℝ≥0 → ℝ) → Prop := fun T w => ∀ (R : ℕ) (p : ℚ≥0), (K R : ℚ≥0) ≤ p →
    (p : ℝ≥0) < (T : ℝ≥0) → (R : ℝ) < ‖LP.traceAt (p : ℝ≥0) w‖ with hΦdef
  have hΦ : ∀ T : ℕ, ∀ w w' : ℝ≥0 → ℝ, (∀ r : ℝ≥0, r < (T : ℝ≥0) → w r = w' r) → Φ T w → Φ T w' :=
    fun T w w' h hw R p hK hp => by
      rw [← LP.traceAt_congr fun r hr => h r (lt_of_le_of_lt hr hp)]
      exact hw R p hK hp
  have hbound : ∀ (T n : ℕ), P (horizonEvent κ τL πL τR πR G W VL VR (1 / ((n : ℝ) + 1)) (T : ℝ≥0) m (Φ T)) ≤
      ENNReal.ofReal (Real.exp m) ^ (1 / 2 : ℝ) * codeLaw κ πL πR (qSet K T) (zL, zR) ^ (1 / 2 : ℝ) :=
    fun T n => measure_horizonEvent_le hκ hF hsep hE𝓖 hGm (fun ω hω => (hGgood ω hω).1)
      (fun ω hω => (hGgood ω hω).2.1) (by positivity) (T : ℝ≥0) m (hΦ T) (measurableSet_qSet K T)
      (fun x _ hT hx => ⟨hT, hx⟩)
  -- the success event lies in the union of the horizon events
  have hsub : ∀ T : ℕ, succEvent C K W VL VR ζ ∩ G ⊆
      ⋃ n : ℕ, horizonEvent κ τL πL τR πR G W VL VR (1 / ((n : ℝ) + 1)) (T : ℝ≥0) m (Φ T) := by
    intro T ω ⟨hS, hωG⟩
    obtain ⟨hζω, hst, hp⟩ := hGgood ω hωG
    obtain ⟨-, hnear, hoL, hoR, hK⟩ := hS
    have hf := hp.isForcePath
    have hlt : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω := fun t => by rw [hζω]; exact ENNReal.coe_lt_top
    have hpos : ∀ s, 0 < minGap (stateAt W VL VR s ω) := fun s => by
      rw [minGap, Finset.lt_inf'_iff]
      rintro (_ | i | j) -
      · exact one_pos
      · show 0 < |W s ω - VL i s ω|
        have h1 := hf.antitone_vL (hlt s) (Fin.zero_le i)
        have h2 := (hnear s).1
        simp only at h1
        exact abs_pos.2 (by linarith)
      · show 0 < |W s ω - VR j s ω|
        have h1 := hf.monotone_vR (hlt s) (Fin.zero_le j)
        have h2 := (hnear s).2
        simp only at h1
        exact abs_pos.2 (by linarith)
    obtain ⟨n, hn⟩ := exists_one_div_le_on_Iic (continuous_minGap.comp hst) hpos (T : ℝ≥0)
    refine mem_iUnion.2 ⟨n, hωG, hn, ?_, fun R p hKp _ => hK R p hKp⟩
    have hwc : Continuous fun t => W t ω := continuous_fst.comp hst
    have hlc : ∀ i, Continuous fun t => VL i t ω := fun i =>
      (continuous_apply i).comp (continuous_fst.comp (continuous_snd.comp hst))
    have hrc : ∀ j, Continuous fun t => VR j t ω := fun j =>
      (continuous_apply j).comp (continuous_snd.comp (continuous_snd.comp hst))
    have hE := changeEnergy_le_osc hκ hnL hnR (ρL := τL) (ρR := τR) (W := W) (VL := VL) (VR := VR) (ω := ω)
      (T := (T : ℝ≥0)) hwc hlc hrc
      (fun s _ i => ⟨by linarith [(hnear s).1], by
          have := hf.antitone_vL (hlt s) (Fin.zero_le i); simp only at this; linarith, by
          have := hf.antitone_vL (hlt s) (Fin.le_last i); simp only at this; linarith⟩)
      (fun s _ j => ⟨by linarith [(hnear s).2], by
          have := hf.monotone_vR (hlt s) (Fin.zero_le j); simp only at this; linarith, by
          have := hf.monotone_vR (hlt s) (Fin.le_last j); simp only at this; linarith⟩)
    refine hE.trans ?_
    have h2κ : 0 ≤ 2 / κ := by positivity
    refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) h2κ
    · exact mul_le_mul_of_nonneg_left (hoL (T : ℝ≥0)) (sq_nonneg _)
    · exact mul_le_mul_of_nonneg_left (hoR (T : ℝ≥0)) (sq_nonneg _)
  -- each horizon
  have hT : ∀ T : ℕ, P (succEvent C K W VL VR ζ) ≤
      ENNReal.ofReal (Real.exp m) ^ (1 / 2 : ℝ) * codeLaw κ πL πR (qSet K T) (zL, zR) ^ (1 / 2 : ℝ) := by
    intro T
    have hmono : Monotone fun n : ℕ =>
        horizonEvent κ τL πL τR πR G W VL VR (1 / ((n : ℝ) + 1)) (T : ℝ≥0) m (Φ T) := by
      intro n n' hnn' ω ⟨h1, h2, h3, h4⟩
      refine ⟨h1, fun s hs => le_trans ?_ (h2 s hs), h3, h4⟩
      have h1' : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have h2' : (n : ℝ) + 1 ≤ (n' : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hnn'
      exact one_div_le_one_div_of_le h1' h2'
    calc P (succEvent C K W VL VR ζ) = P (succEvent C K W VL VR ζ ∩ G) := (measure_inter_conull hGc).symm
      _ ≤ P (⋃ n : ℕ, horizonEvent κ τL πL τR πR G W VL VR (1 / ((n : ℝ) + 1)) (T : ℝ≥0) m (Φ T)) :=
          measure_mono (hsub T)
      _ = ⨆ n : ℕ, P (horizonEvent κ τL πL τR πR G W VL VR (1 / ((n : ℝ) + 1)) (T : ℝ≥0) m (Φ T)) :=
          hmono.measure_iUnion
      _ ≤ _ := iSup_le fun n => hbound T n
  -- the limit of the horizons
  have hlim := tendsto_codeLaw_of_antitone (a := κ) (ρL := πL) (ρR := πR) (fun T => measurableSet_qSet K T)
    (antitone_qSet K) (zL, zR)
  rw [iInter_qSet] at hlim
  have hlim' : Tendsto (fun T : ℕ => ENNReal.ofReal (Real.exp m) ^ (1 / 2 : ℝ) *
      codeLaw κ πL πR (qSet K T) (zL, zR) ^ (1 / 2 : ℝ)) atTop
      (𝓝 (ENNReal.ofReal (Real.exp m) ^ (1 / 2 : ℝ) *
        codeLaw κ πL πR {x | QTrans K (cw x) (cζ x)} (zL, zR) ^ (1 / 2 : ℝ))) :=
    ENNReal.Tendsto.const_mul ((ENNReal.continuous_rpow_const.tendsto _).comp hlim)
      (Or.inr (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top))
  have hle := ge_of_tendsto' hlim' hT
  have hsq : ∀ a : ℝ≥0∞, (a ^ (1 / 2 : ℝ)) ^ 2 = a := fun a => by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  calc P (succEvent C K W VL VR ζ) ^ 2 ≤ (ENNReal.ofReal (Real.exp m) ^ (1 / 2 : ℝ) *
        codeLaw κ πL πR {x | QTrans K (cw x) (cζ x)} (zL, zR) ^ (1 / 2 : ℝ)) ^ 2 := pow_le_pow_left₀ zero_le hle 2
    _ = _ := by rw [mul_pow, hsq, hsq]

end OneWord

/-! ### Aux. lemmas 109/111: the uniform trial bound -/

/-- **Aux. lemmas 109 and 111 in driver form: the uniform trial bound from one reference law** (every `κ > 0`). If the
reference weights `σ` on the four-mark words `(−1, −M; 1, M)` have the side totals of `ρ` and the reference success
event has positive probability for every `M ≥ 1`, then the weights `ρ` have the uniform trial bound: for every `M`,
`codeLaw ρ ntCodeSet (y) ≤ 1 − e^{−m} p₀²` at every midpoint word `y` with marks in `[−M, M]`. -/
theorem uniformTrialBound_of_reference {κ : ℝ} (hκ : 0 < κ) {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ}
    {σL σR : Fin 2 → ℝ} (hσL : σL 0 + σL 1 = ∑ i, ρL i) (hσR : σR 0 + σR 1 = ∑ j, ρR j)
    (href : ∀ M : ℝ, 1 ≤ M → RefTrialPositivity κ M σL σR) : UniformTrialBound κ ρL ρR := by
  intro M
  by_cases hM : 1 ≤ M
  swap
  · refine ⟨1, one_pos, fun yL yR _ hL0 _ hML _ => ?_⟩
    have := hML 0
    rw [hL0] at this
    exact absurd (by linarith) hM
  obtain ⟨C, K, p₀, hp₀, hpos⟩ := href M hM
  set m : ℝ := 2 / κ * ((∑ i, |propW ρL i - refW (n := nL) σL i|) ^ 2 * C +
    (∑ j, |propW ρR j - refW (n := nR) σR j|) ^ 2 * C) with hm
  refine ⟨Real.exp (-m) * p₀ ^ 2, by positivity, fun yL yR hy hL0 hR0 hML hMR => ?_⟩
  -- the combined word
  have hFz := isOrderedForceWord_comb hy (by linarith) hML hMR
  have hz0L : combL yL M 0 = -1 := by
    rw [← castSucc_zero', combL_castSucc]; exact hL0
  have hz0R : combR yR M 0 = 1 := by
    rw [← castSucc_zero', combR_castSucc]; exact hR0
  have hsepz : ∀ i j, combL yL M i < combR yR M j := fun i j => by
    have h1 := hFz.1 (Fin.zero_le i)
    have h2 := hFz.2.2.1 (Fin.zero_le j)
    rw [hz0L] at h1
    rw [hz0R] at h2
    linarith
  have hsepy : ∀ i j, yL i < yR j := fun i j => by
    have h1 := hy.1 (Fin.zero_le i)
    have h2 := hy.2.2.1 (Fin.zero_le j)
    rw [hL0] at h1
    rw [hR0] at h2
    linarith
  -- the reference evolution of the combined word and its four-mark deletion
  obtain ⟨Ω₁, m₁, P₁, hP₁, 𝓕₁, W₁, VL₁, VR₁, B₁, ζ₁, hE₁⟩ :=
    exists_isIntegratedSLEEvolution_assembled hκ hFz (ρL := refW (n := nL) σL) (ρR := refW (n := nR) σR)
  have hE₄ := hE₁.compEmb (refEmb nL) (refEmb nR) (fun i hi => refW_of_notMem σL hi)
    (fun i hi => refW_of_notMem σR hi)
  have hxL : (fun j => combL yL M (refEmb nL j)) = refXL M := funext fun j => by
    rcases Fin.exists_fin_two.1 ⟨j, rfl⟩ with h | h <;> subst h
    · rw [refEmb_zero, hz0L]; rfl
    · rw [refEmb_one, combL_last]; rfl
  have hxR : (fun j => combR yR M (refEmb nR j)) = refXR M := funext fun j => by
    rcases Fin.exists_fin_two.1 ⟨j, rfl⟩ with h | h <;> subst h
    · rw [refEmb_zero, hz0R]; rfl
    · rw [refEmb_one, combR_last]; rfl
  have hwL : (fun j => refW (n := nL) σL (refEmb nL j)) = σL := funext (refW_refEmb σL)
  have hwR : (fun j => refW (n := nR) σR (refEmb nR j)) = σR := funext (refW_refEmb σR)
  rw [hxL, hxR, hwL, hwR] at hE₄
  obtain ⟨hζ₄, hp₄⟩ := hpos P₁ 𝓕₁ W₁ (fun j => VL₁ (refEmb nL j)) (fun j => VR₁ (refEmb nR j)) B₁ ζ₁ hE₄
  have hsubS : {ω | RefGood C K (fun t => W₁ t ω) (fun i t => VL₁ (refEmb nL i) t ω)
      (fun j t => VR₁ (refEmb nR j) t ω) (ζ₁ ω)} ⊆ succEvent C K W₁ VL₁ VR₁ ζ₁ := by
    intro ω h
    simp only [RefGood, refEmb_zero, refEmb_one, mem_ofPred_eq] at h
    exact h
  have hsq := sq_measure_succEvent_le hκ hFz hsepz hE₁ hζ₄ (πL := propW ρL) (πR := propW ρR)
    (sum_propW_sub_refW hσL) (sum_propW_sub_refW hσR) C K
  rw [← hm] at hsq
  set c := codeLaw κ (propW ρL) (propW ρR) {x | QTrans K (cw x) (cζ x)} (combL yL M, combR yR M) with hc
  have hcge : ENNReal.ofReal (Real.exp (-m) * p₀ ^ 2) ≤ c := by
    have h1 : ENNReal.ofReal p₀ ^ 2 ≤ ENNReal.ofReal (Real.exp m) * c :=
      (pow_le_pow_left₀ zero_le (hp₄.trans (measure_mono hsubS)) 2).trans hsq
    have he : ENNReal.ofReal (Real.exp (-m)) * ENNReal.ofReal (Real.exp m) = 1 := by
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, neg_add_cancel, Real.exp_zero,
        ENNReal.ofReal_one]
    calc ENNReal.ofReal (Real.exp (-m) * p₀ ^ 2) = ENNReal.ofReal (Real.exp (-m)) * ENNReal.ofReal p₀ ^ 2 := by
          rw [ENNReal.ofReal_mul (Real.exp_pos _).le, ENNReal.ofReal_pow hp₀.le]
      _ ≤ ENNReal.ofReal (Real.exp (-m)) * (ENNReal.ofReal (Real.exp m) * c) := by gcongr
      _ = c := by rw [← mul_assoc, he, one_mul]
  -- the proposed evolution of the combined word and its deletion to `y`
  obtain ⟨Ω₂, m₂, P₂, hP₂, 𝓕₂, W₂, VL₂, VR₂, B₂, ζ₂, hE₂⟩ :=
    exists_isIntegratedSLEEvolution_assembled hκ hFz (ρL := propW ρL) (ρR := propW ρR)
  have hEy := hE₂.compEmb (Fin.castSuccOrderEmb (n := nL + 1)) (Fin.castSuccOrderEmb (n := nR + 1))
    (fun i hi => propW_of_notMem ρL hi) (fun i hi => propW_of_notMem ρR hi)
  have hyL : (fun j => combL yL M (Fin.castSuccOrderEmb (n := nL + 1) j)) = yL :=
    funext fun j => combL_castSucc yL M j
  have hyR : (fun j => combR yR M (Fin.castSuccOrderEmb (n := nR + 1) j)) = yR :=
    funext fun j => combR_castSucc yR M j
  have hρL : (fun j => propW ρL (Fin.castSuccOrderEmb (n := nL + 1) j)) = ρL :=
    funext fun j => propW_castSucc ρL j
  have hρR : (fun j => propW ρR (Fin.castSuccOrderEmb (n := nR + 1) j)) = ρR :=
    funext fun j => propW_castSucc ρR j
  rw [hyL, hyR, hρL, hρR] at hEy
  have hA : P₂ {ω | NonTransientEvent (fun t => W₂ t ω) (ζ₂ ω)} = codeLaw κ ρL ρR ntCodeSet (yL, yR) :=
    measure_nonTransient_eq_codeLaw hκ hsepy hEy
  have hQm : MeasurableSet {x : XCode (nL + 1 + 1) (nR + 1 + 1) | QTrans K (cw x) (cζ x)} := by
    rw [← iInter_qSet]; exact MeasurableSet.iInter fun T => measurableSet_qSet K T
  have hB : P₂ {ω | QTrans K (fun t => W₂ t ω) (ζ₂ ω)} = c :=
    measure_eventOf_eq_codeLaw hκ hsepz hE₂ hQm (fun _ _ _ => Iff.rfl) (qTrans_congr K)
  -- the two events are disjoint off a null set
  have hAm : MeasurableSet {ω | NonTransientEvent (fun t => W₂ t ω) (ζ₂ ω)} :=
    (iSup_le fun t => 𝓕₂.le t) _ (measurableSet_nonTransient hE₂.2.1 (Ito.isStoppingTime_lifetime hE₂.2.1))
  have hdisj : P₂ ({ω | QTrans K (fun t => W₂ t ω) (ζ₂ ω)} ∩
      {ω | NonTransientEvent (fun t => W₂ t ω) (ζ₂ ω)}) = 0 := by
    refine measure_mono_null (fun ω ⟨hq, hnt⟩ => ?_) (ae_iff.1 hE₂.2.2.2.2)
    intro hp
    have hζ : ζ₂ ω = ⊤ := hq.1
    have hwc : Continuous fun t => W₂ t ω :=
      continuousOn_univ.1 (hp.isForcePath.continuousOn_w.mono fun t _ => by rw [hζ]; exact ENNReal.coe_lt_top)
    have hq' : QTrans K (fun t => W₂ t ω) ⊤ := by rw [← hζ]; exact hq
    have hnt' : NonTransientEvent (fun t => W₂ t ω) ⊤ := by rw [← hζ]; exact hnt
    exact not_nonTransientEvent_of_qTrans hwc hp.1 hq' hnt'
  have hsum : P₂ {ω | NonTransientEvent (fun t => W₂ t ω) (ζ₂ ω)} + P₂ {ω | QTrans K (fun t => W₂ t ω) (ζ₂ ω)} ≤ 1 := by
    have h := measure_union_add_inter {ω | QTrans K (fun t => W₂ t ω) (ζ₂ ω)} hAm (μ := P₂)
    rw [hdisj, add_zero] at h
    rw [add_comm, ← h]
    exact prob_le_one
  rw [hA, hB] at hsum
  have hc1 : c ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (le_trans le_add_self hsum)
  have hp1 : Real.exp (-m) * p₀ ^ 2 ≤ 1 := by
    have h1 : ENNReal.ofReal (Real.exp (-m) * p₀ ^ 2) ≤ 1 := hcge.trans (le_trans le_add_self hsum)
    rwa [← ENNReal.ofReal_one, ENNReal.ofReal_le_ofReal_iff zero_le_one] at h1
  calc codeLaw κ ρL ρR ntCodeSet (yL, yR) ≤ 1 - c := ENNReal.le_sub_of_add_le_right hc1 hsum
    _ ≤ 1 - ENNReal.ofReal (Real.exp (-m) * p₀ ^ 2) := tsub_le_tsub_left hcge 1
    _ = ENNReal.ofReal (1 - Real.exp (-m) * p₀ ^ 2) := by
        rw [ENNReal.ofReal_sub _ (by positivity), ENNReal.ofReal_one]

/-- **Aux. lemma 111's inner references** (all `κ > 0`): the uniform trial bound of `ρ` from the positivity of the
reference success event of the four-mark words with the side totals of `ρ` at the inner marks `∓1` and zero-weight
barriers at `∓M`. -/
theorem uniformTrialBound_inner {κ : ℝ} (hκ : 0 < κ) {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ}
    (hpos : ∀ M : ℝ, 1 ≤ M → RefTrialPositivity κ M ![∑ i, ρL i, 0] ![∑ j, ρR j, 0]) :
    UniformTrialBound κ ρL ρR :=
  uniformTrialBound_of_reference hκ (by simp) (by simp) hpos

/-- **Aux. lemma 109's outer references** (all `κ > 0`): the same with the side totals at the barriers `∓M` and
zero-weight inner marks `∓1`. -/
theorem uniformTrialBound_outer {κ : ℝ} (hκ : 0 < κ) {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ}
    (hpos : ∀ M : ℝ, 1 ≤ M → RefTrialPositivity κ M ![0, ∑ i, ρL i] ![0, ∑ j, ρR j]) :
    UniformTrialBound κ ρL ρR :=
  uniformTrialBound_of_reference hκ (by simp) (by simp) hpos

end TrialsHi

end Sec7

end InteractingSLE
