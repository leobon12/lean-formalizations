/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossRestartExit
import InteractingSLE.WangWu.ReverseContactMartWord

/-!
# The compressed original clock of a killed arc

Packet PROVE-PROP59-PIECES. Specification §5.2, proof of Proposition 5.9 (p. 143): "We use `s` for capacity time in
these new coordinates and `t` for the original capacity time. […] Its two capacity parametrizations are related by a
continuous strictly increasing adapted change of time on each compact initial segment." The pieces of the
alternating construction switch at original times in a prescribed countable set, so each piece carries its original
clock as a function of its joint-chart capacity time (`Prop59Stage.StageData.clk`), and PROVE-PROP59T4's regularity
(`IsRegPiece`) asks this clock to be continuous and strictly increasing at every sample, on all of `[0, ∞)`.

A piece is read through a killed arc `γ` on its pre-contact times `P` (original time `u`, chart capacity
`σ(u) = capClock γ u`, terminal capacity `kLife γ P`). Its original time `σ⁻¹(τ)` blows up when the arc reaches the
target of its own chart at a finite chart capacity (PROVE-PROP59T4 §5.1, obstacle 2), so the clock is
**compressed** by `φ(u) = u/(1 + u)` (`CrossRestart.physTime`; `φ` maps the rationals onto the rationals of `[0, 1)`,
so prescribed rational original switching times are exactly the rational clock values below `1`) and continued
linearly after the terminal capacity:

  `absClock γ P τ = φ(σ⁻¹(τ))` for `τ < kLife γ P`, and `E + (τ − kLife γ P)` after it, `E = sup φ(P)`.

## Main results

* `continuous_of_monotone_of_isOpen_range`: a monotone map `ℝ≥0 → ℝ≥0` with open range is continuous;
* `physTime_image_eq` (`φ(P) = [0, E)`), `absClock_of_lt`, `absClock_capClock`;
* **`strictMono_absClock`**, **`continuous_absClock`**: the clock of a killed arc is continuous and strictly
  increasing on `[0, ∞)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Prop59Pieces

open WangWu WangWu.ImgWord CrossRestart
open Sec7.Lemma71C (capClock)

/-! ### Monotone maps with open range -/

/-- A monotone map `ℝ≥0 → ℝ≥0` whose range is open is continuous. -/
theorem continuous_of_monotone_of_isOpen_range {f : ℝ≥0 → ℝ≥0} (hf : Monotone f) (ho : IsOpen (range f)) :
    Continuous f :=
  continuous_iff_continuousAt.2 fun a =>
    continuousAt_of_monotoneOn_of_image_mem_nhds (hf.monotoneOn univ) univ_mem
      (by rw [image_univ]; exact ho.mem_nhds (mem_range_self a))

/-! ### The compressed end of the pre-contact times -/

/-- The compressed end of the pre-contact times: `sup φ(P)`. -/
def arcEnd (P : Set ℝ) : ℝ := sSup (physTime '' P)

variable {γ : ℝ → ℂ} {P : Set ℝ}

theorem physTime_mono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : physTime a ≤ physTime b :=
  strictMonoOn_physTime.monotoneOn (mem_Ici.2 ha) (mem_Ici.2 (ha.trans hab)) hab

theorem physTime_strictMono {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) : physTime a < physTime b :=
  strictMonoOn_physTime (mem_Ici.2 ha) (mem_Ici.2 (ha.trans hab.le)) hab

theorem continuousOn_physTime : ContinuousOn physTime (Ici 0) := by
  refine ContinuousOn.div continuousOn_id (continuousOn_const.add continuousOn_id) fun x hx => ?_
  have : (0 : ℝ) ≤ x := hx
  linarith

theorem physTime_zero : physTime 0 = 0 := by simp [physTime]

theorem bddAbove_physTime_image (hγ : IsKilledArc γ P) : BddAbove (physTime '' P) :=
  ⟨1, by rintro _ ⟨u, hu, rfl⟩; exact (physTime_lt_one (hγ.nonneg u hu)).le⟩

theorem physTime_lt_arcEnd (hγ : IsKilledArc γ P) {u : ℝ} (hu : u ∈ P) : physTime u < arcEnd P := by
  obtain ⟨u', hu', huu'⟩ := hγ.exists_gt u hu
  exact (physTime_strictMono (hγ.nonneg u hu) huu').trans_le
    (le_csSup (bddAbove_physTime_image hγ) ⟨u', hu', rfl⟩)

theorem arcEnd_pos (hγ : IsKilledArc γ P) : 0 < arcEnd P := by
  have := physTime_lt_arcEnd hγ hγ.zero_mem
  rwa [physTime_zero] at this

theorem arcEnd_le_one (hγ : IsKilledArc γ P) : arcEnd P ≤ 1 :=
  csSup_le (Set.Nonempty.image _ ⟨0, hγ.zero_mem⟩)
    (by rintro _ ⟨u, hu, rfl⟩; exact (physTime_lt_one (hγ.nonneg u hu)).le)

/-- **`φ(P) = [0, E)`.** -/
theorem physTime_image_eq (hγ : IsKilledArc γ P) : physTime '' P = Ico 0 (arcEnd P) := by
  ext y
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨physTime_nonneg (hγ.nonneg u hu), physTime_lt_arcEnd hγ hu⟩
  · rintro ⟨hy0, hyE⟩
    obtain ⟨_, ⟨u', hu', rfl⟩, hyu'⟩ := exists_lt_of_lt_csSup (Set.Nonempty.image _ ⟨0, hγ.zero_mem⟩) hyE
    have hu'0 := hγ.nonneg u' hu'
    have hc : ContinuousOn physTime (Icc 0 u') := continuousOn_physTime.mono fun x hx => mem_Ici.2 hx.1
    obtain ⟨u, hu, rfl⟩ := intermediate_value_Icc hu'0 hc (show y ∈ Icc (physTime 0) (physTime u') from
      ⟨by rw [physTime_zero]; exact hy0, hyu'.le⟩)
    exact ⟨u, hγ.icc u' hu' hu, rfl⟩

/-! ### The absolute compressed clock -/

/-- **The absolute compressed original clock** of a killed arc at chart capacity `τ`: `φ(σ⁻¹(τ))` before the
terminal capacity, continued with slope one after it. -/
def absClock (γ : ℝ → ℂ) (P : Set ℝ) (τ : ℝ≥0) : ℝ≥0 :=
  if (τ : WithTop ℝ≥0) < kLife γ P then (physTime (kInv γ P τ)).toNNReal
  else (arcEnd P).toNNReal + (τ - WithTop.untopD 0 (kLife γ P))

theorem absClock_of_lt {τ : ℝ≥0} (hτ : (τ : WithTop ℝ≥0) < kLife γ P) :
    absClock γ P τ = (physTime (kInv γ P τ)).toNNReal := by
  simp only [absClock, hτ, ↓reduceIte]

theorem absClock_of_le {τ : ℝ≥0} (hτ : ¬ (τ : WithTop ℝ≥0) < kLife γ P) :
    absClock γ P τ = (arcEnd P).toNNReal + (τ - WithTop.untopD 0 (kLife γ P)) := by
  simp only [absClock, hτ, ↓reduceIte]

/-- At the capacity of a pre-contact time `u`, the clock reads `φ(u)`. -/
theorem absClock_capClock (hγ : IsKilledArc γ P) {u : ℝ} (hu : u ∈ P) :
    absClock γ P (capClock γ u).toNNReal = (physTime u).toNNReal := by
  rw [absClock_of_lt (hγ.lt_kLife hu), Real.coe_toNNReal _ (hγ.capClock_nonneg hu), hγ.kInv_capClock hu]

theorem kInv_strictMono (hγ : IsKilledArc γ P) {a b : ℝ≥0} (hb : (b : WithTop ℝ≥0) < kLife γ P) (hab : a < b) :
    kInv γ P a < kInv γ P b := by
  have ha : (a : WithTop ℝ≥0) < kLife γ P := lt_of_le_of_lt (WithTop.coe_le_coe.2 hab.le) hb
  obtain ⟨hma, hea⟩ := hγ.kInv_spec ha
  obtain ⟨hmb, heb⟩ := hγ.kInv_spec hb
  by_contra h
  have := hγ.strictMonoOn_capClock.monotoneOn hmb hma (not_lt.1 h)
  rw [hea, heb] at this
  exact absurd (NNReal.coe_lt_coe.2 hab) (not_lt.2 this)

theorem lt_arcEnd_absClock (hγ : IsKilledArc γ P) {τ : ℝ≥0} (hτ : (τ : WithTop ℝ≥0) < kLife γ P) :
    absClock γ P τ < (arcEnd P).toNNReal := by
  rw [absClock_of_lt hτ]
  exact (Real.toNNReal_lt_toNNReal_iff (arcEnd_pos hγ)).2 (physTime_lt_arcEnd hγ (hγ.kInv_spec hτ).1)

/-- **The clock is strictly increasing.** -/
theorem strictMono_absClock (hγ : IsKilledArc γ P) : StrictMono (absClock γ P) := by
  intro a b hab
  by_cases hb : (b : WithTop ℝ≥0) < kLife γ P
  · have ha : (a : WithTop ℝ≥0) < kLife γ P := lt_of_le_of_lt (WithTop.coe_le_coe.2 hab.le) hb
    rw [absClock_of_lt ha, absClock_of_lt hb]
    have hpos : 0 < physTime (kInv γ P b) := by
      refine lt_of_le_of_lt (physTime_nonneg (hγ.nonneg _ (hγ.kInv_spec ha).1)) ?_
      exact physTime_strictMono (hγ.nonneg _ (hγ.kInv_spec ha).1) (kInv_strictMono hγ hb hab)
    exact (Real.toNNReal_lt_toNNReal_iff hpos).2
      (physTime_strictMono (hγ.nonneg _ (hγ.kInv_spec ha).1) (kInv_strictMono hγ hb hab))
  · rw [absClock_of_le hb]
    by_cases ha : (a : WithTop ℝ≥0) < kLife γ P
    · exact (lt_arcEnd_absClock hγ ha).trans_le le_self_add
    · rw [absClock_of_le ha]
      refine add_lt_add_right ?_ (arcEnd P).toNNReal
      have htop : kLife γ P ≠ ⊤ := fun h => by rw [h] at hb; exact hb (WithTop.coe_lt_top b)
      obtain ⟨K, hK⟩ := WithTop.ne_top_iff_exists.1 htop
      rw [← hK] at ha hb ⊢
      have hKa : K ≤ a := WithTop.coe_le_coe.1 (not_lt.1 ha)
      simp only [WithTop.untopD_coe]
      exact (tsub_lt_tsub_right_of_le hKa hab : a - K < b - K)

/-- The range of the clock before the terminal capacity is `[0, E)`. -/
theorem absClock_image_lt (hγ : IsKilledArc γ P) :
    absClock γ P '' {τ | (τ : WithTop ℝ≥0) < kLife γ P} = Iio (arcEnd P).toNNReal := by
  ext y
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    exact lt_arcEnd_absClock hγ hτ
  · intro hy
    have hy' : (y : ℝ) ∈ Ico 0 (arcEnd P) :=
      ⟨y.coe_nonneg, (Real.lt_toNNReal_iff_coe_lt).1 hy⟩
    rw [← physTime_image_eq hγ] at hy'
    obtain ⟨u, hu, hyu⟩ := hy'
    refine ⟨(capClock γ u).toNNReal, hγ.lt_kLife hu, ?_⟩
    rw [absClock_capClock hγ hu, hyu, Real.toNNReal_coe]

/-- **The clock is continuous.** -/
theorem continuous_absClock (hγ : IsKilledArc γ P) : Continuous (absClock γ P) := by
  refine continuous_of_monotone_of_isOpen_range (strictMono_absClock hγ).monotone ?_
  by_cases htop : kLife γ P = ⊤
  · -- infinite terminal capacity: the range is `[0, E)`
    have e : range (absClock γ P) = Iio (arcEnd P).toNNReal := by
      rw [← absClock_image_lt hγ, htop]
      ext y
      simp only [mem_range, mem_image, mem_ofPred_eq, WithTop.coe_lt_top, true_and]
    rw [e]
    exact isOpen_Iio
  · -- finite terminal capacity: the clock is onto
    obtain ⟨K, hK⟩ := WithTop.ne_top_iff_exists.1 htop
    have h : kLife γ P = K := hK.symm
    have e : range (absClock γ P) = univ := by
      refine eq_univ_of_forall fun y => ?_
      by_cases hy : y < (arcEnd P).toNNReal
      · have hy' : y ∈ Iio (arcEnd P).toNNReal := hy
        rw [← absClock_image_lt hγ] at hy'
        obtain ⟨τ, -, hτ⟩ := hy'
        exact ⟨τ, hτ⟩
      · refine ⟨K + (y - (arcEnd P).toNNReal), ?_⟩
        have hK : ¬ (((K + (y - (arcEnd P).toNNReal) : ℝ≥0)) : WithTop ℝ≥0) < kLife γ P := by
          rw [h, WithTop.coe_lt_coe, not_lt]; exact le_self_add
        rw [absClock_of_le hK, h, WithTop.untopD_coe, add_tsub_cancel_left]
        exact add_tsub_cancel_of_le (not_lt.1 hy)
    rw [e]
    exact isOpen_univ

end InteractingSLE.Sec5.Prop59Pieces
