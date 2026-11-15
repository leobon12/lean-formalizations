/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1MargHit
import InteractingSLE.Spec.ZhanGT4.DualA15CofinalExit

/-!
# Zhan's A.1 (R80): enclosure exits of a marginal's driver are stopping times

Packet PROVE-A1-EIGHTSEED. Source: Astra, *Follow-up proofs*, §A.1.3 (`ig1_followup_proofs.txt` L300–L305: the
rectangles are the first exits of the two hulls from a separated enclosure pair) and §A.1.5 (L409–L425).

PROVE-ZHAN-GT4-A15F's `hullExit` and `isStoppingTime_hullExit` are for the Brownian drivers `√κ B`, which are
continuous at every time. The driver of a regular marginal (`A1Marg.IsRegMarginal`) is continuous and adapted only
before its lifetime `ζ`. Here the exit is capped by the lifetime:

* `lifeExit w ζ E N`: the first time the hull of `w` leaves `E` or the lifetime is reached, capped at `N`;
* `lifeExit_le`, `lt_and_subset_of_lt_lifeExit`, `le_lifeExit`: before the exit, the driver is alive and its hull is
  in `E`;
* **`fwdHull_lifeExit_subset`**: if the exit precedes the lifetime, the hull at the exit is still in `E` (`E` a compact
  `ℍ`-hull);
* **`lifeExit_pos`**: the exit is positive when `0 < ζ` and `E` contains a relative neighbourhood of the source;
* **`isStoppingTime_lifeExit`**: for a driver family continuous and adapted before `ζ` (`AdaptedBefore`), the exit is a
  stopping time of every right-continuous filtration (`measurableSet_alive_not_subset`: `{q < ζ, K_q ⊄ E}` is
  `𝓕_q`-measurable, through the driver killed at `q` and `A1Marg.measurableSet_hit_stop`);
* `adaptedBefore_add_const`, `continuousOn_add_const`: the shifted driver `w + p` (the other curve's frame).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1EightSeed

open QuantumZipper (H fwdHull)

/-! ### The lifetime-capped exit -/

section Det

variable {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {E : Set ℂ} {N : ℝ≥0}

/-- **The first exit of the hull of `w` from `E`, or the lifetime `ζ`, capped at `N`.** -/
def lifeExit (w : ℝ≥0 → ℝ) (ζ : ℝ≥0∞) (E : Set ℂ) (N : ℝ≥0) : ℝ≥0 :=
  sInf ({t : ℝ≥0 | ζ ≤ t ∨ ¬ fwdHull (Strip.extPath w) t ⊆ E} ∪ Ici N)

theorem lifeExit_le : lifeExit w ζ E N ≤ N := csInf_le (OrderBot.bddBelow _) (Or.inr (Set.mem_Ici.2 le_rfl))

theorem lt_and_subset_of_lt_lifeExit {t : ℝ≥0} (ht : t < lifeExit w ζ E N) :
    (t : ℝ≥0∞) < ζ ∧ fwdHull (Strip.extPath w) t ⊆ E := by
  have h := notMem_of_lt_csInf ht (OrderBot.bddBelow _)
  simp only [mem_union, mem_ofPred_eq, Set.mem_Ici, not_or, not_le, not_not] at h
  exact h.1

theorem le_lifeExit {s : ℝ≥0} (hsN : s ≤ N) (hs : ∀ t : ℝ≥0, t < s → (t : ℝ≥0∞) < ζ ∧ fwdHull (Strip.extPath w) t ⊆ E) :
    s ≤ lifeExit w ζ E N :=
  le_csInf ⟨N, Or.inr (Set.mem_Ici.2 le_rfl)⟩ fun b hb => by
    rcases hb with hb | hb
    · by_contra hlt
      obtain ⟨h1, h2⟩ := hs b (not_le.1 hlt)
      rcases hb with hb | hb
      · exact (not_le.2 h1) hb
      · exact hb h2
    · exact hsN.trans hb

theorem lt_and_subset_of_lt_lifeExit_real {t : ℝ} (ht0 : 0 ≤ t) (ht : t < lifeExit w ζ E N) :
    ENNReal.ofReal t < ζ ∧ fwdHull (Strip.extPath w) t ⊆ E := by
  have h := lt_and_subset_of_lt_lifeExit (w := w) (ζ := ζ) (E := E) (N := N) (t := t.toNNReal)
    (by rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ ht0]; exact ht)
  rw [Real.coe_toNNReal _ ht0] at h
  exact h

/-- A real time `r` before a positive-or-later lifetime with the driver continuous on `[0, r]`. -/
theorem exists_real_btwn_continuousOn (hwc : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) {T : ℝ≥0} (hT : (T : ℝ≥0∞) < ζ) :
    ∃ r : ℝ, (T : ℝ) < r ∧ ENNReal.ofReal r < ζ ∧ ContinuousOn (Strip.extPath w) (Icc 0 r) := by
  rw [← ENNReal.ofReal_coe_nnreal] at hT
  obtain ⟨r, -, hTr, hrζ⟩ := ENNReal.lt_iff_exists_real_btwn.1 hT
  exact ⟨r, ((ENNReal.ofReal_lt_ofReal_iff').1 hTr).1, hrζ, A1Ref.continuousOn_extPath_Icc hwc hrζ⟩

/-- **The hull at the exit is still in the enclosure** when the exit precedes the lifetime. -/
theorem fwdHull_lifeExit_subset (hwc : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) (hw0 : w 0 = 0) (hE : IsHPHull E)
    (hlt : (lifeExit w ζ E N : ℝ≥0∞) < ζ) : fwdHull (Strip.extPath w) (lifeExit w ζ E N) ⊆ E := by
  set T := lifeExit w ζ E N with hTdef
  obtain ⟨r, hTr, -, hcr⟩ := exists_real_btwn_continuousOn hwc hlt
  have hr0 : 0 ≤ r := T.coe_nonneg.trans hTr.le
  set W' := A1Ref.stopDrv (Strip.extPath w) r with hW'
  have hW'c : Continuous W' := A1Ref.continuous_stopDrv hcr hr0
  have hW'0 : W' 0 = 0 := by
    simp only [hW', A1Ref.stopDrv, min_eq_left hr0, max_self, Strip.extPath, Real.toNNReal_zero, hw0]
  have hcongr : ∀ t : ℝ, 0 ≤ t → t < r → fwdHull (Strip.extPath w) t = fwdHull W' t := fun t ht htr =>
    LocalExt.fwdHull_congr_of_eqOn_of_lt ht htr fun s hs => (A1Ref.stopDrv_eqOn _ r hs).symm
  rw [hcongr T T.coe_nonneg hTr]
  refine fwdHull_subset_of_forall_lt hW'c hW'0 T.coe_nonneg (IsHPHull.isOpen_H_diff hE)
    (IsHPHull.isPreconnected_H_diff hE) (IsHPHull.not_isBounded_H_diff hE) fun t ht0 htT => ?_
  rw [← hcongr t ht0 (htT.trans hTr)]
  exact (lt_and_subset_of_lt_lifeExit_real ht0 htT).2

/-- **The exit is positive** when the driver is alive at `0`, starts at `0`, and `E` contains a relative
neighbourhood of `0`. -/
theorem lifeExit_pos (hwc : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) (hw0 : w 0 = 0) (hζ : 0 < ζ) (hN : 0 < N)
    {ε : ℝ} (hε : 0 < ε) (hE : ball (0 : ℂ) ε ∩ H ⊆ E) : 0 < lifeExit w ζ E N := by
  obtain ⟨r, hr, hrζ, hcr⟩ := exists_real_btwn_continuousOn hwc (T := 0) (by simpa using hζ)
  have hr0 : (0 : ℝ) ≤ r := hr.le
  set W' := A1Ref.stopDrv (Strip.extPath w) r with hW'
  have hW'c : Continuous W' := A1Ref.continuous_stopDrv hcr hr0
  have hW'0 : W' 0 = 0 := by
    simp only [hW', A1Ref.stopDrv, min_eq_left hr0, max_self, Strip.extPath, Real.toNNReal_zero, hw0]
  have hpos := hullExit_pos (N := N) hW'c hW'0 hN hε hE
  have hpos' : 0 < min (hullExit W' E N) r.toNNReal := lt_min hpos (Real.toNNReal_pos.2 hr)
  refine hpos'.trans_le (le_lifeExit ((min_le_left _ _).trans hullExit_le) fun t ht => ⟨?_, ?_⟩)
  · have htr : (t : ℝ) < r := by
      have := ht.trans_le (min_le_right _ _)
      rwa [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hr0] at this
    refine lt_of_le_of_lt ?_ hrζ
    rw [← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal htr.le
  · have htr : (t : ℝ) < r := by
      have := ht.trans_le (min_le_right _ _)
      rwa [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hr0] at this
    rw [LocalExt.fwdHull_congr_of_eqOn_of_lt t.coe_nonneg htr fun s hs => (A1Ref.stopDrv_eqOn _ r hs).symm]
    exact fwdHull_subset_of_lt_hullExit (ht.trans_le (min_le_left _ _))

end Det

/-! ### The exit is a stopping time -/

section Stop

variable {X : Type*} {mX : MeasurableSpace X} {𝓕 : Filtration ℝ≥0 mX} {w : ℝ≥0 → X → ℝ} {ζ : X → ℝ≥0∞}

/-- The shifted driver `w + p` is adapted before the lifetime. -/
theorem adaptedBefore_add_const (hwa : AdaptedBefore 𝓕 ζ w) (p : ℝ) :
    AdaptedBefore 𝓕 ζ fun t x => w t x + p := fun t A hA =>
  hwa t ((fun v => v + p) ⁻¹' A) (measurable_add_const p hA)

theorem continuousOn_add_const (hwc : ∀ x, ContinuousOn (w · x) {t | (t : ℝ≥0∞) < ζ x}) (p : ℝ) (x : X) :
    ContinuousOn (fun t => w t x + p) {t | (t : ℝ≥0∞) < ζ x} :=
  (hwc x).add continuousOn_const

open Classical in
/-- The driver killed at `q`: `w (min t q)` on `{q < ζ}`, `0` off it. -/
def killAt (w : ℝ≥0 → X → ℝ) (ζ : X → ℝ≥0∞) (q : ℝ≥0) (t : ℝ≥0) (x : X) : ℝ :=
  if (q : ℝ≥0∞) < ζ x then w (min t q) x else 0

open Classical in
/-- The lifetime of the driver killed at `q`: `∞` on `{q < ζ}`, `0` off it. -/
def killLife (ζ : X → ℝ≥0∞) (q : ℝ≥0) (x : X) : ℝ≥0∞ := if (q : ℝ≥0∞) < ζ x then ⊤ else 0

theorem measurableSet_lt_life (hwa : AdaptedBefore 𝓕 ζ w) (q : ℝ≥0) :
    MeasurableSet[𝓕 q] {x | (q : ℝ≥0∞) < ζ x} := by
  have h := hwa q univ MeasurableSet.univ
  simpa only [mem_univ, and_true] using h

theorem measurable_killAt (hwa : AdaptedBefore 𝓕 ζ w) (q t : ℝ≥0) : Measurable[𝓕 q] (killAt w ζ q t) := by
  intro A hA
  have e : killAt w ζ q t ⁻¹' A = ({x | (q : ℝ≥0∞) < ζ x} ∩ {x | ((min t q : ℝ≥0) : ℝ≥0∞) < ζ x ∧
      w (min t q) x ∈ A}) ∪ ({x | (q : ℝ≥0∞) < ζ x}ᶜ ∩ {_x | (0 : ℝ) ∈ A}) := by
    ext x
    by_cases hx : (q : ℝ≥0∞) < ζ x
    · simp [killAt, hx]
    · simp [killAt, hx]
  rw [e]
  refine ((measurableSet_lt_life hwa q).inter ?_).union ((measurableSet_lt_life hwa q).compl.inter
    (MeasurableSet.const _))
  exact 𝓕.mono (min_le_right t q) _ (hwa (min t q) A hA)

theorem measurable_killLife (hwa : AdaptedBefore 𝓕 ζ w) (q : ℝ≥0) : Measurable[𝓕 q] (killLife ζ q) := by
  classical
  exact Measurable.ite (measurableSet_lt_life hwa q) measurable_const measurable_const

theorem continuousOn_killAt (hwc : ∀ x, ContinuousOn (w · x) {t | (t : ℝ≥0∞) < ζ x}) (q : ℝ≥0) (x : X) :
    ContinuousOn (killAt w ζ q · x) {t | (t : ℝ≥0∞) < killLife ζ q x} := by
  by_cases hx : (q : ℝ≥0∞) < ζ x
  · have e : (killAt w ζ q · x) = fun t => w (min t q) x := by
      funext t; simp [killAt, hx]
    rw [e]
    refine ((hwc x).comp_continuous (continuous_id.min continuous_const) fun t => ?_).continuousOn
    exact lt_of_le_of_lt (ENNReal.coe_le_coe.2 (min_le_right _ _)) hx
  · have e : {t : ℝ≥0 | (t : ℝ≥0∞) < killLife ζ q x} = ∅ := by
      ext t; simp [killLife, hx]
    rw [e]
    exact continuousOn_empty _

/-- On the alive event the hull at `q` of the killed driver is that of the driver. -/
theorem fwdHull_killAt (hwc : ∀ x, ContinuousOn (w · x) {t | (t : ℝ≥0∞) < ζ x}) {q : ℝ≥0} {x : X}
    (hx : (q : ℝ≥0∞) < ζ x) :
    fwdHull (Strip.extPath (killAt w ζ q · x)) q = fwdHull (Strip.extPath (w · x)) q := by
  obtain ⟨r, hqr, -, hcr⟩ := exists_real_btwn_continuousOn (hwc x) hx
  have hr0 : 0 ≤ r := q.coe_nonneg.trans hqr.le
  have hcont : Continuous (Strip.extPath (killAt w ζ q · x)) := by
    have e : Strip.extPath (killAt w ζ q · x) = fun s : ℝ => w (min s.toNNReal q) x := by
      funext s; simp [Strip.extPath, killAt, hx]
    rw [e]
    exact ((hwc x).comp_continuous (continuous_real_toNNReal.min continuous_const) fun s =>
      lt_of_le_of_lt (ENNReal.coe_le_coe.2 (min_le_right _ _)) hx)
  refine LocalExt.fwdHull_congr_of_continuousOn hcont.continuousOn hcr q.coe_nonneg hqr fun s hs => ?_
  have hsq : s.toNNReal ≤ q := by
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hs.1]; exact hs.2
  simp [Strip.extPath, killAt, hx, min_eq_left hsq]

/-- **`{q < ζ, K_q ⊄ E}` is `𝓕_q`-measurable** (`ℍ \ E` open): a countable union of compact hits of the hull of the
driver killed at `q` (`A1Marg.measurableSet_hit_stop` in the σ-algebra `𝓕_q`, sectioned at `q`). -/
theorem measurableSet_alive_not_subset (hwc : ∀ x, ContinuousOn (w · x) {t | (t : ℝ≥0∞) < ζ x})
    (hwa : AdaptedBefore 𝓕 ζ w) {E : Set ℂ} (hEo : IsOpen (H \ E)) (q : ℝ≥0) :
    MeasurableSet[𝓕 q] {x | (q : ℝ≥0∞) < ζ x ∧ ¬ fwdHull (Strip.extPath (w · x)) q ⊆ E} := by
  obtain ⟨F, hFc, hFU, hFeq, hFmono⟩ := hEo.exists_iUnion_isClosed
  set K : ℕ → Set ℂ := fun n => F n ∩ closedBall 0 n with hK
  have hKc : ∀ n, IsCompact (K n) := fun n => (isCompact_closedBall (0 : ℂ) (n : ℝ)).inter_left (hFc n)
  have hKH : ∀ n, K n ⊆ H := fun n z hz => (hFU n hz.1).1
  have hS : ∀ n, MeasurableSet[(borel ℝ≥0).prod (𝓕 q)] {p : ℝ≥0 × X | (p.1 : ℝ≥0∞) < killLife ζ q p.2 ∧
      (K n ∩ fwdHull (Strip.extPath (killAt w ζ q · p.2)) p.1).Nonempty} := fun n => by
    have h := @A1Marg.measurableSet_hit_stop X (𝓕 q) (killAt w ζ q) (killLife ζ q) (continuousOn_killAt hwc q)
      (measurable_killAt hwa q) (measurable_killLife hwa q) (K n) (hKc n) (hKH n)
    have hbor : (inferInstance : MeasurableSpace ℝ≥0) = borel ℝ≥0 := BorelSpace.measurable_eq
    rw [← hbor]
    exact h
  have hsec : Measurable[𝓕 q, (borel ℝ≥0).prod (𝓕 q)] fun x : X => (q, x) := by
    have hbor : (inferInstance : MeasurableSpace ℝ≥0) = borel ℝ≥0 := BorelSpace.measurable_eq
    rw [← hbor]
    exact @measurable_prodMk_left ℝ≥0 X _ (𝓕 q) q
  have e : {x | (q : ℝ≥0∞) < ζ x ∧ ¬ fwdHull (Strip.extPath (w · x)) q ⊆ E} =
      ⋃ n, (fun x : X => (q, x)) ⁻¹' {p : ℝ≥0 × X | (p.1 : ℝ≥0∞) < killLife ζ q p.2 ∧
        (K n ∩ fwdHull (Strip.extPath (killAt w ζ q · p.2)) p.1).Nonempty} := by
    ext x
    simp only [mem_ofPred_eq, mem_iUnion, mem_preimage]
    by_cases hx : (q : ℝ≥0∞) < ζ x
    · have hl : (q : ℝ≥0∞) < killLife ζ q x := by simp [killLife, hx]
      simp only [hx, hl, true_and, fwdHull_killAt hwc hx, not_subset]
      constructor
      · rintro ⟨z, hzK, hzE⟩
        have hz : z ∈ ⋃ n, F n := by rw [hFeq]; exact ⟨(QuantumZipper.fwdHull_mono.2 _) hzK, hzE⟩
        obtain ⟨n, hn⟩ := mem_iUnion.1 hz
        obtain ⟨m, hm⟩ := exists_nat_ge ‖z‖
        exact ⟨max n m, z, ⟨(hFmono (le_max_left n m)) hn,
          mem_closedBall_zero_iff.2 (hm.trans (Nat.cast_le.2 (le_max_right n m)))⟩, hzK⟩
      · rintro ⟨n, z, ⟨hzF, -⟩, hzK⟩
        exact ⟨z, hzK, (hFU n hzF).2⟩
    · have hl : ¬ (q : ℝ≥0∞) < killLife ζ q x := by simp [killLife, hx]
      simp only [hx, hl, false_and, exists_false]
  rw [e]
  exact MeasurableSet.iUnion fun n => hsec (hS n)

/-- **The lifetime-capped exit is a stopping time of every right-continuous filtration** to which the driver is adapted
before its lifetime (`ℍ \ E` open). -/
theorem isStoppingTime_lifeExit [𝓕.IsRightContinuous] (hwc : ∀ x, ContinuousOn (w · x) {t | (t : ℝ≥0∞) < ζ x})
    (hwa : AdaptedBefore 𝓕 ζ w) {E : Set ℂ} (hEo : IsOpen (H \ E)) (N : ℝ≥0) :
    IsStoppingTime 𝓕 fun x => ((lifeExit (w · x) (ζ x) E N : ℝ≥0) : WithTop ℝ≥0) := by
  refine isStoppingTime_of_measurableSet_lt_of_isRightContinuous fun u => ?_
  have hup : ∀ x (b b' : ℝ≥0), b ≤ b' →
      b ∈ {t : ℝ≥0 | ζ x ≤ t ∨ ¬ fwdHull (Strip.extPath (w · x)) t ⊆ E} ∪ Ici N →
      b' ∈ {t : ℝ≥0 | ζ x ≤ t ∨ ¬ fwdHull (Strip.extPath (w · x)) t ⊆ E} ∪ Ici N := by
    rintro x b b' hbb' ((hb | hb) | hb)
    · exact Or.inl (Or.inl (hb.trans (ENNReal.coe_le_coe.2 hbb')))
    · exact Or.inl (Or.inr fun h => hb ((QuantumZipper.fwdHull_mono.1 (NNReal.coe_le_coe.2 hbb')).trans h))
    · exact Or.inr (le_trans hb hbb')
  have e : {x | ((lifeExit (w · x) (ζ x) E N : ℝ≥0) : WithTop ℝ≥0) < u} =
      ⋃ q : ℚ, ⋃ (_ : 0 ≤ (q : ℝ) ∧ (q : ℝ) < u),
        ({x | ¬ (((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) < ζ x} ∪
          {x | (((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) < ζ x ∧
            ¬ fwdHull (Strip.extPath (w · x)) ((q : ℝ).toNNReal : ℝ) ⊆ E} ∪ {_x | N ≤ (q : ℝ).toNNReal}) := by
    ext x
    simp only [mem_ofPred_eq, WithTop.coe_lt_coe, mem_iUnion, mem_union, exists_prop]
    unfold lifeExit
    rw [csInf_lt_iff (OrderBot.bddBelow _) ⟨N, Or.inr (Set.mem_Ici.2 le_rfl)⟩]
    constructor
    · rintro ⟨b, hb, hbu⟩
      obtain ⟨q, hbq, hqu⟩ := exists_rat_btwn (show (b : ℝ) < u from hbu)
      have hq0 : 0 ≤ (q : ℝ) := b.coe_nonneg.trans hbq.le
      refine ⟨q, ⟨hq0, hqu⟩, ?_⟩
      have hb' := hup x b _ (by rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hq0]; exact hbq.le) hb
      rcases hb' with (h | h) | h
      · rw [← not_lt] at h; exact Or.inl (Or.inl h)
      · by_cases hl : (((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) < ζ x
        · exact Or.inl (Or.inr ⟨hl, h⟩)
        · exact Or.inl (Or.inl hl)
      · exact Or.inr h
    · rintro ⟨q, ⟨hq0, hqu⟩, hq⟩
      refine ⟨(q : ℝ).toNNReal, ?_, ?_⟩
      · rcases hq with (h | h) | h
        · exact Or.inl (Or.inl (not_lt.1 h))
        · exact Or.inl (Or.inr h.2)
        · exact Or.inr h
      · rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hq0]
        exact hqu
  rw [e]
  refine MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun hq => ?_
  have hqu : (q : ℝ).toNNReal ≤ u := by
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hq.1]; exact hq.2.le
  refine MeasurableSet.union (MeasurableSet.union ?_ ?_) (MeasurableSet.const _)
  · exact 𝓕.mono hqu _ (measurableSet_lt_life hwa _).compl
  · exact 𝓕.mono hqu _ (measurableSet_alive_not_subset hwc hwa hEo _)

end Stop

end InteractingSLE.ZhanGT4.A1EightSeed
