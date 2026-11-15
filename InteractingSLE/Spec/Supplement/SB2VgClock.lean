/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2VgCap
import InteractingSLE.Spec.Supplement.SB2VfCmpl

/-!
# SB2(1)'s version half: the relative clock, measurable for the completed line filtration

Packet PROVE-AUX61-NOJUMP (Theorem 1.4, SB2(1)'s version half, ruling R108).

* `clockMeas D I t`: the line-mark clock reading. Before the lifetime it is `ofReal (capRead D I t)`; from the
  lifetime on, the supremum of these readings at the rational times before `ζ`. **`measurable_clockMeas`**: it is a line
  mark at `t` (`Vg.measurableSet_lifetime_le`, `Vg.measurable_capRead`).
* **`ae_clockOf_eq_clockMeas`**: almost surely at a launch on the entrance event, `Vc.clockOf (flowLift) T_L ζ t =
  clockMeas D I t` for EVERY `t` (`Vg.ae_clockOf_eq_capRead` before `ζ`; monotone supremum after it,
  `Vd.clockOf_eq_sup_of_le`).
* **`exists_versionClock`**: a clock `a` for the version. It is continuous, monotone and `0` at `0` at every sample,
  and measurable for `D.lineFiltC t`. Almost surely at a launch on the entrance event it equals `Vc.clockOf (flowLift)`.
  It is `clockOf` on a measurable conull good event inside the entrance event `D.event`, and `0` elsewhere.

This discharges the clock part (`a`, `ha`, `clock_cont/mono/zero`, `a = clockOf`) of `Ve.SB2MeasVersionStatement`.
Theorem 1.3 and the named S3 input as before (R48).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Vg

open Lv Exist.Staged Exist.StagedLaw

/-- A rational time strictly between a nonnegative real and an extended real. -/
theorem exists_nnrat_btwn {a : ℝ≥0} {c : ℝ≥0∞} (h : (a : ℝ≥0∞) < c) :
    ∃ q : ℚ≥0, a < (q : ℝ≥0) ∧ ((q : ℝ≥0) : ℝ≥0∞) < c := by
  obtain ⟨y, hay, hyc⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 h
  have hay' : (a : ℝ) < y := NNReal.coe_lt_coe.2 (ENNReal.coe_lt_coe.1 hay)
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hay'
  have hq0 : (0 : ℚ) ≤ q := by
    have : (0 : ℝ) ≤ q := (NNReal.coe_nonneg a).trans hq1.le
    exact_mod_cast this
  have hqr : ((q.toNNRat : ℝ≥0) : ℝ) = q := by
    have h1 : ((q.toNNRat : ℚ) : ℝ) = q := by rw [Rat.coe_toNNRat q hq0]
    rw [← h1]
    norm_cast
  refine ⟨q.toNNRat, ?_, ?_⟩
  · rw [← NNReal.coe_lt_coe, hqr]; exact hq1
  · refine lt_trans (ENNReal.coe_lt_coe.2 ?_) hyc
    rw [← NNReal.coe_lt_coe, hqr]; exact hq2

section

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
  {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {u ψ : ℝ} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
  {u₀ : ℂ → ℝ}

open scoped Classical in
/-- **The line-mark clock reading** at the physical time `t`. -/
def clockMeas (D : EntranceUnion κ b jumps P h E k u η ζ u₀) (I : K2LaunchInputs κ b jumps P h E k u ψ)
    (t : ℝ≥0) (ω : Ω) : ℝ≥0∞ :=
  if ζ ω ≤ t then
    ⨆ (q : ℚ≥0) (_ : ((q : ℝ≥0) : ℝ≥0∞) < ζ ω ∧ ((q : ℝ≥0) : ℝ≥0∞) ≤ t), ENNReal.ofReal (capRead D I q ω)
  else ENNReal.ofReal (capRead D I t ω)

open scoped Classical in
/-- **The clock reading is a line mark at `t`.** -/
theorem measurable_clockMeas (D : EntranceUnion κ b jumps P h E k u η ζ u₀)
    (I : K2LaunchInputs κ b jumps P h E k u ψ) (t : ℝ≥0) :
    Measurable[D.absMarks (t : ℝ≥0∞)] (clockMeas D I t) := by
  refine Measurable.ite (EntranceUnion.measurableSet_lifetime_le D t) (Measurable.iSup fun q => ?_)
    (measurable_capRead D I t).ennreal_ofReal
  by_cases hqt : ((q : ℝ≥0) : ℝ≥0∞) ≤ t
  · have e : (fun ω => ⨆ (_ : ((q : ℝ≥0) : ℝ≥0∞) < ζ ω ∧ ((q : ℝ≥0) : ℝ≥0∞) ≤ t),
        ENNReal.ofReal (capRead D I q ω)) =
        fun ω => if ((q : ℝ≥0) : ℝ≥0∞) < ζ ω then ENNReal.ofReal (capRead D I q ω) else 0 := by
      funext ω
      by_cases hqζ : ((q : ℝ≥0) : ℝ≥0∞) < ζ ω
      · rw [iSup_pos ⟨hqζ, hqt⟩]; simp only [hqζ, ↓reduceIte]
      · rw [iSup_neg (fun h => hqζ h.1)]; simp [hqζ]
    rw [e]
    have hle : D.absMarks ((q : ℝ≥0) : ℝ≥0∞) ≤ D.absMarks (t : ℝ≥0∞) := D.absMarks_mono hqt
    exact Measurable.ite (hle _ (EntranceUnion.measurableSet_lt_lifetime D q))
      ((measurable_capRead D I q).ennreal_ofReal.mono hle le_rfl) measurable_const
  · have e : (fun ω => ⨆ (_ : ((q : ℝ≥0) : ℝ≥0∞) < ζ ω ∧ ((q : ℝ≥0) : ℝ≥0∞) ≤ t),
        ENNReal.ofReal (capRead D I q ω)) = fun _ => 0 := by
      funext ω
      rw [iSup_neg (fun h => hqt h.2)]; rfl
    rw [e]; exact measurable_const

/-- **The relative clock is the line-mark reading at every time**, almost surely. -/
theorem ae_clockOf_eq_clockMeas (h13 : Exist.Theorem13Statement.{u})
    (hS3 : Tc.SB2EntranceNoCommonArcStatement.{u}) (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ)
    (I : K2LaunchInputs κ b jumps P h E k u ψ) (D : EntranceUnion κ b jumps P h E k u η ζ u₀) :
    ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) → Ve.entT κ b jumps E k u η ζ ω < ζ ω →
      ∀ t : ℝ≥0, Vc.clockOf (Ve.flowLift κ b jumps E k u η ζ ω) (Ve.entT κ b jumps E k u η ζ ω).toNNReal (ζ ω) t =
        clockMeas D I t ω := by
  classical
  filter_upwards [ae_clockOf_eq_capRead h13 hS3 HP I D] with ω hcap hF hT t
  have hcap := hcap hF hT
  unfold clockMeas
  by_cases hζt : ζ ω ≤ t
  · simp only [hζt, ↓reduceIte]
    refine le_antisymm ?_ (iSup₂_le fun q hq => ?_)
    · rw [Vd.clockOf_eq_sup_of_le hζt]
      refine iSup₂_le fun s hs => ?_
      obtain ⟨q, hq1, hq2⟩ := exists_nnrat_btwn hs
      refine le_trans ?_ (le_iSup₂_of_le q ⟨hq2, hq2.le.trans hζt⟩ le_rfl)
      rw [← hcap q hq2]
      unfold Vc.clockOf
      exact le_iSup₂_of_le s hq1.le (le_iSup_of_le hs le_rfl)
    · rw [← hcap q hq.1]
      exact Vc.monotone_clockOf _ _ _ (ENNReal.coe_le_coe.1 hq.2)
  · simp only [hζt, ↓reduceIte]
    exact hcap t (not_le.1 hζt)

/-- **The version's clock**: continuous, monotone, `0` at `0` at every sample, measurable for the completed line
filtration, and almost surely the relative clock of the flow's lift at a launch on the entrance event. -/
theorem exists_versionClock (h13 : Exist.Theorem13Statement.{u})
    (hS3 : Tc.SB2EntranceNoCommonArcStatement.{u}) (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ)
    (I : K2LaunchInputs κ b jumps P h E k u ψ) (D : EntranceUnion κ b jumps P h E k u η ζ u₀) :
    ∃ (a : ℝ≥0 → Ω → ℝ≥0∞), (∀ t, Measurable[D.lineFiltC HP t] (a t)) ∧
      (∀ ω, Continuous fun t => a t ω) ∧ (∀ ω, Monotone fun t => a t ω) ∧ (∀ ω, a 0 ω = 0) ∧
      ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) → Ve.entT κ b jumps E k u η ζ ω < ζ ω →
        ∀ t, a t ω =
          Vc.clockOf (Ve.flowLift κ b jumps E k u η ζ ω) (Ve.entT κ b jumps E k u η ζ ω).toNNReal (ζ ω) t := by
  classical
  -- the good event
  have hgood : ∀ᵐ ω ∂P, (ω ∈ launchSet κ b jumps E (k + 1) →
      (ω ∈ D.event ↔ firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω)) < ζ ω)) ∧
      (ω ∈ launchSet κ b jumps E (k + 1) → Ve.entT κ b jumps E k u η ζ ω < ζ ω →
        Continuous (Vc.clockOf (Ve.flowLift κ b jumps E k u η ζ ω) (Ve.entT κ b jumps E k u η ζ ω).toNNReal (ζ ω)) ∧
        Sec7.Lemma71C.capClock (fun r : ℝ => (Ve.flowLift κ b jumps E k u η ζ ω) r.toNNReal) 0 = 0 ∧
        ∀ t, Vc.clockOf (Ve.flowLift κ b jumps E k u η ζ ω) (Ve.entT κ b jumps E k u η ζ ω).toNNReal (ζ ω) t =
          clockMeas D I t ω) := by
    filter_upwards [D.ae_mem_event_iff, Vd.ae_continuous_clockOf h13 hS3 HP, Vd.ae_clockData h13 hS3 HP,
      ae_clockOf_eq_clockMeas h13 hS3 HP I D] with ω hev hc hd hm
    exact ⟨hev, fun hF hT => ⟨hc hF hT, (hd hF hT).1, hm hF hT⟩⟩
  obtain ⟨G, hGm, hGnull, hG⟩ := Vf.exists_measurable_conull hgood
  have hEv : MeasurableSet D.event := (D.absMarks_le HP 0) _ (D.marks_le_absMarks 0 _ (D.measurableSet_event HP))
  -- on `G ∩ D.event`: the launch, the entrance, continuity, zero, and the reading
  have hGE : ∀ ω ∈ G ∩ D.event, ω ∈ launchSet κ b jumps E (k + 1) ∧ Ve.entT κ b jumps E k u η ζ ω < ζ ω := by
    intro ω hω
    have hl := D.event_subset hω.2
    exact ⟨hl, ((hG ω hω.1).1 hl).1 hω.2⟩
  set a : ℝ≥0 → Ω → ℝ≥0∞ := fun t ω =>
    if ω ∈ G ∩ D.event then
      Vc.clockOf (Ve.flowLift κ b jumps E k u η ζ ω) (Ve.entT κ b jumps E k u η ζ ω).toNNReal (ζ ω) t
    else 0 with ha
  refine ⟨a, fun t => ?_, fun ω => ?_, fun ω => ?_, fun ω => ?_, ?_⟩
  · -- measurable for the completed line filtration
    have hrd : Measurable[D.absMarks (t : ℝ≥0∞)] fun ω => if ω ∈ D.event then clockMeas D I t ω else 0 :=
      Measurable.ite (D.marks_le_absMarks t _ (D.measurableSet_event HP)) (measurable_clockMeas D I t)
        measurable_const
    have heq : a t = fun ω => if ω ∈ G then (if ω ∈ D.event then clockMeas D I t ω else 0) else 0 := by
      funext ω
      by_cases hω : ω ∈ G ∩ D.event
      · obtain ⟨hl, hT⟩ := hGE ω hω
        simp only [ha, hω, ↓reduceIte, hω.1, hω.2]
        exact ((hG ω hω.1).2 hl hT).2.2 t
      · simp only [ha, hω, ↓reduceIte]
        by_cases hωG : ω ∈ G
        · have hωE : ω ∉ D.event := fun h => hω ⟨hωG, h⟩
          simp only [hωG, hωE, ↓reduceIte]
        · simp only [hωG, ↓reduceIte]
    have hrd' : Measurable fun ω => if ω ∈ D.event then clockMeas D I t ω else 0 :=
      hrd.mono (D.absMarks_le HP t) le_rfl
    have hmeas : Measurable (a t) := by
      rw [heq]; exact Measurable.ite hGm hrd' measurable_const
    refine Vf.measurable_lineFiltC D HP t hmeas hrd ?_
    have hGae : ∀ᵐ ω ∂P, ω ∈ G := by
      rw [ae_iff]; exact hGnull
    filter_upwards [hGae] with ω hω
    rw [heq]
    simp only [hω, ↓reduceIte]
  · -- continuity
    by_cases hω : ω ∈ G ∩ D.event
    · obtain ⟨hl, hT⟩ := hGE ω hω
      simp only [ha, hω, ↓reduceIte]
      exact ((hG ω hω.1).2 hl hT).1
    · simp only [ha, hω, ↓reduceIte]
      exact continuous_const
  · -- monotonicity
    by_cases hω : ω ∈ G ∩ D.event
    · simp only [ha, hω, ↓reduceIte]
      exact Vc.monotone_clockOf _ _ _
    · simp only [ha, hω, ↓reduceIte]
      exact monotone_const
  · -- zero at zero
    by_cases hω : ω ∈ G ∩ D.event
    · obtain ⟨hl, hT⟩ := hGE ω hω
      simp only [ha, hω, ↓reduceIte]
      exact Vc.clockOf_eq_zero_of_le zero_le ((hG ω hω.1).2 hl hT).2.1
    · simp only [ha, hω, ↓reduceIte]
  · -- the identification
    have hGae : ∀ᵐ ω ∂P, ω ∈ G := by
      rw [ae_iff]; exact hGnull
    filter_upwards [hGae, D.ae_mem_event_iff] with ω hωG hev hl hT t
    have hωE : ω ∈ D.event := (hev hl).2 hT
    simp only [ha, show ω ∈ G ∩ D.event from ⟨hωG, hωE⟩, ↓reduceIte]

end

end InteractingSLE.Theorem14.SB.Vg
