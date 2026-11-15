/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2NcData
import InteractingSLE.Spec.Supplement.SB2VdCont

/-!
# The relative clock of a driven canonical stage curve

Packet PROVE-AUX61-NOJUMP (round 21, D34, component B), deterministic. In B's own time `s` the relative capacity of
the canonical stage values is SB2(1)'s clock `Vc.clockOf (canonVal X x₀ p L) 0 L s` (entrance `0`, lifetime `L`).
With `uOf L` the inverse of the reparametrization `cTime L`:

* `image_canonCurve_Icc`: `canonCurve '' [0, u] = canonVal '' [0, cTime u]`;
* `capClock_liftR_canonVal`: the capacity in B's time is the curve's capacity at `uOf s`;
* **`clockOf_canonVal`**: the clock is `capClock (canonCurve) (uOf s)` before `L` and the terminal capacity
  `capLife (canonCurve)` from `L` on;
* **`continuous_clockOf_canonVal`** (`Vd.continuous_clockOf`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.SB.Nc

open Sec7.PocketTraversal Sec7.Lemma71C Dv

/-- The parameter of `canonCurve` at B's time `s < L` (the inverse of `rTime L`). -/
def uOf (L : ℝ≥0∞) (s : ℝ) : ℝ := if L = ⊤ then s else s / (L.toReal - s)

variable {L : ℝ≥0∞}

/-- B's times strictly before the lifetime. -/
def BeforeL (L : ℝ≥0∞) (s : ℝ) : Prop := 0 ≤ s ∧ (L = ⊤ ∨ s < L.toReal)

theorem uOf_zero (L : ℝ≥0∞) : uOf L 0 = 0 := by unfold uOf; split_ifs <;> simp

theorem uOf_nonneg {s : ℝ} (hs : BeforeL L s) : 0 ≤ uOf L s := by
  unfold uOf
  split_ifs with h
  · exact hs.1
  · exact div_nonneg hs.1 (by linarith [hs.2.resolve_left h])

theorem rTime_uOf {s : ℝ} (hs : BeforeL L s) : rTime L (uOf L s) = s := by
  unfold rTime uOf
  split_ifs with h
  · rfl
  · have hlt := hs.2.resolve_left h
    have hpos : 0 < L.toReal - s := by linarith
    have hL0 : L.toReal ≠ 0 := by linarith [hs.1]
    unfold clockOf
    have h1 : 1 + s / (L.toReal - s) = L.toReal / (L.toReal - s) := by field_simp; ring
    rw [h1, div_div_div_cancel_right₀ hpos.ne']
    field_simp

theorem cTime_uOf {s : ℝ} (hs : BeforeL L s) : cTime L (uOf L s) = s.toNNReal := by
  unfold cTime; rw [rTime_uOf hs]

theorem continuousOn_uOf : ContinuousOn (uOf L) {s | BeforeL L s} := by
  unfold uOf
  split_ifs with h
  · exact continuousOn_id
  · refine continuousOn_id.div (continuousOn_const.sub continuousOn_id) fun s hs => ?_
    have := hs.2.resolve_left h
    show L.toReal - s ≠ 0
    linarith

theorem monotoneOn_uOf : MonotoneOn (uOf L) {s | BeforeL L s} := by
  intro a ha c hc hac
  unfold uOf
  split_ifs with h
  · exact hac
  · have h1 := ha.2.resolve_left h
    have h2 := hc.2.resolve_left h
    exact div_le_div₀ hc.1 hac (by linarith) (by linarith)

/-- The reparametrization maps `[0, u]` onto `[0, cTime u]`. -/
theorem image_cTime_Icc (hL : L ≠ 0) {u : ℝ} (hu : 0 ≤ u) : cTime L '' Icc 0 u = Icc 0 (cTime L u) := by
  ext s
  constructor
  · rintro ⟨v, hv, rfl⟩
    refine ⟨zero_le, ?_⟩
    rw [← NNReal.coe_le_coe, coe_cTime hL hv.1, coe_cTime hL hu]
    exact (strictMonoOn_rTime hL).monotoneOn hv.1 hu hv.2
  · rintro ⟨-, hs⟩
    have h0 : rTime L 0 = 0 := by unfold rTime; split_ifs <;> simp [clockOf_zero]
    have hsu : (s : ℝ) ≤ rTime L u := by rw [← coe_cTime hL hu]; exact_mod_cast hs
    obtain ⟨v, hv, hvs⟩ := intermediate_value_Icc hu (continuousOn_rTime.mono fun y hy => mem_Ici.2 hy.1)
      (show (s : ℝ) ∈ Icc (rTime L 0) (rTime L u) from ⟨by rw [h0]; exact s.2, hsu⟩)
    refine ⟨v, hv, ?_⟩
    apply NNReal.coe_injective
    rw [coe_cTime hL hv.1, hvs]

theorem image_canonCurve_Icc (hL : L ≠ 0) {u : ℝ} (hu : 0 ≤ u) (X : Set ℂ) (x₀ : ℝ) (p : ℝ≥0 → ℂ) :
    canonCurve X x₀ p L '' Icc 0 u = canonVal X x₀ p L '' Icc 0 (cTime L u) := by
  have e : canonCurve X x₀ p L = canonVal X x₀ p L ∘ cTime L := funext fun v => canonCurve_eq X x₀ p L v
  rw [e, image_comp, image_cTime_Icc hL hu]

/-- **The capacity in B's time** is the curve's capacity at `uOf s`. -/
theorem capClock_liftR_canonVal (hL : L ≠ 0) {s : ℝ} (hs : BeforeL L s) (X : Set ℂ) (x₀ : ℝ) (p : ℝ≥0 → ℂ) :
    capClock (fun r : ℝ => canonVal X x₀ p L r.toNNReal) s = capClock (canonCurve X x₀ p L) (uOf L s) := by
  unfold capClock
  rw [image_canonCurve_Icc hL (uOf_nonneg hs), cTime_uOf hs]
  have := Vd.image_liftR (canonVal X x₀ p L) hs.1
  unfold Vd.liftR at this
  rw [this]

variable {X : Set ℂ} {x₀ : ℝ} {p : ℝ≥0 → ℂ}

theorem beforeL_of_lt {s : ℝ≥0} (hs : (s : ℝ≥0∞) < L) : BeforeL L s := by
  refine ⟨s.2, ?_⟩
  by_cases h : L = ⊤
  · exact Or.inl h
  · right
    have := (ENNReal.toReal_lt_toReal ENNReal.coe_ne_top h).2 hs
    simpa using this

/-- **The relative clock**: `capClock (canonCurve) (uOf s)` before the lifetime, the terminal capacity after. -/
theorem clockOf_canonVal (hd : IsDrivenCurve (canonCurve X x₀ p L)) (hL : L ≠ 0) (t : ℝ≥0) :
    Vc.clockOf (canonVal X x₀ p L) 0 L t = if (t : ℝ≥0∞) < L then
      ENNReal.ofReal (capClock (canonCurve X x₀ p L) (uOf L t)) else capLife (canonCurve X x₀ p L) := by
  split_ifs with ht
  · have hmono : MonotoneOn (capClock fun r : ℝ => canonVal X x₀ p L r.toNNReal) (Icc 0 ((t : ℝ) - (0 : ℝ≥0))) := by
      intro a ha c hc hac
      have hb : ∀ y ∈ Icc 0 ((t : ℝ) - (0 : ℝ≥0)), BeforeL L y := fun y hy => by
        refine ⟨hy.1, ?_⟩
        rcases (beforeL_of_lt ht).2 with h | h
        · exact Or.inl h
        · right; simp only [NNReal.coe_zero, sub_zero] at hy; linarith [hy.2]
      rw [capClock_liftR_canonVal hL (hb a ha), capClock_liftR_canonVal hL (hb c hc)]
      exact hd.strictMonoOn_capClock.monotoneOn (uOf_nonneg (hb a ha)) (uOf_nonneg (hb c hc))
        (monotoneOn_uOf (hb a ha) (hb c hc) hac)
    rw [Vc.clockOf_eq zero_le ht hmono]
    simp only [NNReal.coe_zero, sub_zero]
    rw [capClock_liftR_canonVal hL (beforeL_of_lt ht)]
  · rw [not_lt] at ht
    rw [Vd.clockOf_eq_sup_of_le ht]
    have hfin : L ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top ht
    refine le_antisymm (iSup₂_le fun s hs => ?_) ?_
    · rw [zero_add] at hs
      rw [capClock_liftR_canonVal hL (beforeL_of_lt hs)]
      exact (hd.ofReal_capClock_lt (uOf_nonneg (beforeL_of_lt hs))).le
    · refine iSup_le fun n => ?_
      have hLr : 0 < L.toReal := ENNReal.toReal_pos hL hfin
      set s : ℝ≥0 := (clockOf L.toReal n).toNNReal with hsdef
      have hs0 : (s : ℝ) = clockOf L.toReal n := Real.coe_toNNReal _ (clockOf_nonneg hLr (Nat.cast_nonneg n))
      have hsL : (s : ℝ≥0∞) < L := by
        rw [← ENNReal.ofReal_coe_nnreal, hs0]
        exact (ENNReal.ofReal_lt_iff_lt_toReal (clockOf_nonneg hLr (Nat.cast_nonneg n)) hfin).2
          (clockOf_lt hLr (Nat.cast_nonneg n))
      have hus : uOf L s = n := by
        have := rTime_uOf (L := L) (beforeL_of_lt hsL)
        have hr : rTime L n = s := by unfold rTime; simp only [hfin, ↓reduceIte]; exact hs0.symm
        have hinj := (strictMonoOn_rTime hL).injOn (mem_Ici.2 (uOf_nonneg (beforeL_of_lt hsL)))
          (mem_Ici.2 (Nat.cast_nonneg n))
        exact hinj (this.trans hr.symm)
      refine le_iSup₂_of_le s (by rw [zero_add]; exact hsL) ?_
      rw [capClock_liftR_canonVal hL (beforeL_of_lt hsL), hus]

/-- **The relative clock is continuous.** -/
theorem continuous_clockOf_canonVal (hd : IsDrivenCurve (canonCurve X x₀ p L)) (hL : L ≠ 0) :
    Continuous (Vc.clockOf (canonVal X x₀ p L) 0 L) := by
  refine Vd.continuous_clockOf ?_ fun T₁ _ hT₁ => ?_
  · have h0 : BeforeL L ((0 : ℝ≥0) : ℝ) := beforeL_of_lt (by simpa using pos_iff_ne_zero.2 hL)
    have := capClock_liftR_canonVal hL h0 X x₀ p
    simp only [NNReal.coe_zero] at this
    rw [this, uOf_zero, hd.capClock_zero]
  · have hb : ∀ y ∈ Icc 0 ((T₁ : ℝ) - (0 : ℝ≥0)), BeforeL L y := fun y hy => by
      refine ⟨hy.1, ?_⟩
      rcases (beforeL_of_lt hT₁).2 with h | h
      · exact Or.inl h
      · right; simp only [NNReal.coe_zero, sub_zero] at hy; linarith [hy.2]
    have heq : EqOn (capClock fun r : ℝ => canonVal X x₀ p L r.toNNReal)
        (capClock (canonCurve X x₀ p L) ∘ uOf L) (Icc 0 ((T₁ : ℝ) - (0 : ℝ≥0))) := fun y hy =>
      capClock_liftR_canonVal hL (hb y hy) X x₀ p
    refine ⟨?_, ?_⟩
    · refine ContinuousOn.congr ?_ heq
      exact hd.continuousOn_capClock.comp (continuousOn_uOf.mono fun y hy => hb y hy)
        fun y hy => mem_Ici.2 (uOf_nonneg (hb y hy))
    · intro a ha c hc hac
      rw [heq ha, heq hc]
      exact hd.strictMonoOn_capClock.monotoneOn (uOf_nonneg (hb a ha)) (uOf_nonneg (hb c hc))
        (monotoneOn_uOf (hb a ha) (hb c hc) hac)

end InteractingSLE.Theorem14.SB.Nc
