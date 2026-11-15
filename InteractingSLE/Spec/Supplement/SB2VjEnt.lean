/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2VgClock

/-!
# SB2(1)'s version half: the entrance time read from the clock

Packet PROVE-AUX61-NOJUMP (Theorem 1.4, SB2(1)'s version half, ruling R108). The relative curve is the absolute lift
read after the entrance `T_L`, so a measurable version of `T_L` is needed. The clock gives one: it vanishes up to the
entrance and is positive after it.

* `entMeas a ω = inf {q ∈ ℚ≥0 : 0 < a q ω}`; **`measurable_entMeas`** (for any σ-algebra the clock is measurable for);
* **`entMeas_eq`** (deterministic): for the clock `Vc.clockOf γ t_L ζ` of a lift whose capacity clock vanishes at `0`
  and is positive at positive times before the lifetime, `entMeas = t_L`;
* **`ae_entMeas_eq`**: almost surely at a launch on the entrance event, `entMeas a = T_L` for every clock `a` that is
  a.s. `Vc.clockOf (flowLift)` (positivity from the chains, `Vd.ae_chain_liftOf`).

Theorem 1.3 and the named S3 input as before (R48).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Vj

open Lv Exist.Staged Exist.StagedLaw

open scoped Classical in
/-- **The entrance read from a clock**: the infimum of the rational times at which the clock is positive. -/
def entMeas {Ω : Type*} (a : ℝ≥0 → Ω → ℝ≥0∞) (ω : Ω) : ℝ≥0∞ :=
  ⨅ q : ℚ≥0, if 0 < a q ω then ((q : ℝ≥0) : ℝ≥0∞) else ⊤

open scoped Classical in
theorem measurable_entMeas {Ω : Type*} {m : MeasurableSpace Ω} {a : ℝ≥0 → Ω → ℝ≥0∞}
    (ha : ∀ t, Measurable[m] (a t)) : Measurable[m] (entMeas a) :=
  Measurable.iInf fun q => Measurable.ite (measurableSet_lt measurable_const (ha q)) measurable_const measurable_const

open scoped Classical in
/-- **The entrance read from the clock of a lift** is the entrance. -/
theorem entMeas_eq {Ω : Type*} {a : ℝ≥0 → Ω → ℝ≥0∞} {ω : Ω} {γ : ℝ≥0 → ℂ} {tL : ℝ≥0} {ζ : ℝ≥0∞}
    (ha : ∀ t, a t ω = Vc.clockOf γ tL ζ t)
    (h0 : Sec7.Lemma71C.capClock (fun r : ℝ => γ r.toNNReal) 0 = 0)
    (hpos : ∀ s : ℝ≥0, 0 < s → ((tL + s : ℝ≥0) : ℝ≥0∞) < ζ → 0 < Sec7.Lemma71C.capClock (fun r : ℝ => γ r.toNNReal) s)
    (hζ : (tL : ℝ≥0∞) < ζ) : entMeas a ω = tL := by
  unfold entMeas
  refine le_antisymm ?_ (le_iInf fun q => ?_)
  · by_contra hgt
    rw [not_le] at hgt
    obtain ⟨q, hq1, hq2⟩ := Vg.exists_nnrat_btwn (lt_min hgt hζ)
    have hqζ : ((q : ℝ≥0) : ℝ≥0∞) < ζ := hq2.trans_le (min_le_right _ _)
    have hs : 0 < (q : ℝ≥0) - tL := tsub_pos_of_lt hq1
    have hsq : tL + ((q : ℝ≥0) - tL) = (q : ℝ≥0) := add_tsub_cancel_of_le hq1.le
    have hapos : 0 < a q ω := by
      rw [ha]
      refine lt_of_lt_of_le ?_ (le_iSup₂_of_le ((q : ℝ≥0) - tL) hsq.le (le_iSup_of_le (by rw [hsq]; exact hqζ) le_rfl))
      exact ENNReal.ofReal_pos.2 (hpos _ hs (by rw [hsq]; exact hqζ))
    have h1 : (⨅ q : ℚ≥0, if 0 < a q ω then ((q : ℝ≥0) : ℝ≥0∞) else ⊤) ≤ ((q : ℝ≥0) : ℝ≥0∞) :=
      iInf_le_of_le q (by simp only [hapos, ↓reduceIte, le_refl])
    exact absurd (h1.trans_lt (hq2.trans_le (min_le_left _ _))) (lt_irrefl _)
  · split_ifs with hq
    · by_contra hlt
      rw [not_le, ENNReal.coe_lt_coe] at hlt
      rw [ha, Vc.clockOf_eq_zero_of_le hlt.le h0] at hq
      exact lt_irrefl _ hq
    · exact le_top

/-- A relative chain on `[0, s]` has a positive capacity clock at `s > 0`. -/
theorem capClock_pos_of_chain {A : Set ℂ} {c : Chart} {β' γ : ℝ≥0 → ℂ} {tL : ℝ≥0} {S₀ : ℝ} {Wr : ℝ → ℝ}
    {ηr : ℝ → ℂ} (h : FinRel.IsSB2RelChain A c β' γ tL S₀ Wr ηr) {s : ℝ} (hs : S₀ = s) (hs0 : 0 < s) :
    0 < Sec7.Lemma71C.capClock (fun r : ℝ => γ r.toNNReal) s := by
  subst hs
  have h1 := h.2.2.2.2.1 ⟨le_rfl, hs0.le⟩ ⟨hs0.le, le_rfl⟩ hs0
  rwa [h.2.2.2.1] at h1

section

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
  {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {u ψ : ℝ} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}

/-- **The entrance read from the clock is the entrance**, almost surely at a launch on the entrance event. -/
theorem ae_entMeas_eq (h13 : Exist.Theorem13Statement.{u}) (hS3 : Tc.SB2EntranceNoCommonArcStatement.{u})
    (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ) {a : ℝ≥0 → Ω → ℝ≥0∞}
    (hae : ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) → Ve.entT κ b jumps E k u η ζ ω < ζ ω →
      ∀ t, a t ω = Vc.clockOf (Ve.flowLift κ b jumps E k u η ζ ω) (Ve.entT κ b jumps E k u η ζ ω).toNNReal (ζ ω) t) :
    ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) → Ve.entT κ b jumps E k u η ζ ω < ζ ω →
      entMeas a ω = Ve.entT κ b jumps E k u η ζ ω := by
  filter_upwards [hae, Vd.ae_clockData h13 hS3 HP, Vd.ae_chain_liftOf h13 hS3 HP] with ω ha hcd hch hF hT
  set TL := Ve.entT κ b jumps E k u η ζ ω with hTLdef
  have hTLtop : TL ≠ ⊤ := ne_top_of_lt hT
  have hTLc : ((TL.toNNReal : ℝ≥0) : ℝ≥0∞) = TL := ENNReal.coe_toNNReal hTLtop
  have hTLr : TL.toReal = (TL.toNNReal : ℝ) := rfl
  have h0 : Sec7.Lemma71C.capClock (fun r : ℝ => (Ve.flowLift κ b jumps E k u η ζ ω) r.toNNReal) 0 = 0 := (hcd hF hT).1
  have hpos : ∀ s : ℝ≥0, 0 < s → ((TL.toNNReal + s : ℝ≥0) : ℝ≥0∞) < ζ ω →
      0 < Sec7.Lemma71C.capClock (fun r : ℝ => (Ve.flowLift κ b jumps E k u η ζ ω) r.toNNReal) s := by
    intro s hs hsζ
    obtain ⟨Wr, ηr, β', hc⟩ := hch hF hT (TL.toNNReal + s) le_self_add hsζ
    exact capClock_pos_of_chain hc (by rw [NNReal.coe_add]; exact add_sub_cancel_left _ _) (NNReal.coe_pos.2 hs)
  rw [entMeas_eq (ha hF hT) h0 hpos (by rw [hTLc]; exact hT), hTLc]

end

end InteractingSLE.Theorem14.SB.Vj
