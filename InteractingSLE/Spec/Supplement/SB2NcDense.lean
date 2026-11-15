/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2NcObj

/-!
# The good times of a driven canonical stage curve are dense

Packet PROVE-AUX61-NOJUMP (round 21, D34, component B), deterministic. The canonical stage curve
`Dv.canonCurve X x₀ p L` reads the chart at the good times `Dv.canonGood X p L` (the point in `ℍ ∖ fill X`) and a
limit along them elsewhere. Off the closure of the good times the limit is along `⊥`, a constant. A driven curve is
nowhere locally constant (strictly increasing capacity), so:

* `cTime L`: the reparametrization of `[0, ∞)` onto B's time (`canonCurve = canonVal ∘ cTime`);
* **`exists_rat_good`**: if the curve is driven and the piece continuous up to `L ≠ 0`, every parameter is within any
  `ε` of a nonnegative rational parameter whose B-time is good.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.SB.Nc

open Sec7.PocketTraversal Sec7.Lemma71C Dv

/-- The real reparametrization of `canonCurve` (`u` for an infinite lifetime, `clockOf L u` otherwise). -/
def rTime (L : ℝ≥0∞) (u : ℝ) : ℝ := if L = ⊤ then u else clockOf L.toReal u

/-- The reparametrization of `canonCurve` onto B's time. -/
def cTime (L : ℝ≥0∞) (u : ℝ) : ℝ≥0 := (rTime L u).toNNReal

theorem canonCurve_eq (X : Set ℂ) (x₀ : ℝ) (p : ℝ≥0 → ℂ) (L : ℝ≥0∞) (u : ℝ) :
    canonCurve X x₀ p L u = canonVal X x₀ p L (cTime L u) := rfl

variable {L : ℝ≥0∞}

theorem rTime_nonneg (hL : L ≠ 0) {u : ℝ} (hu : 0 ≤ u) : 0 ≤ rTime L u := by
  unfold rTime
  split_ifs with h
  · exact hu
  · exact clockOf_nonneg (ENNReal.toReal_pos hL h) hu

theorem strictMonoOn_rTime (hL : L ≠ 0) : StrictMonoOn (rTime L) (Ici 0) := by
  unfold rTime
  split_ifs with h
  · exact strictMono_id.strictMonoOn _
  · exact strictMonoOn_clockOf (ENNReal.toReal_pos hL h)

theorem continuousOn_rTime : ContinuousOn (rTime L) (Ici 0) := by
  unfold rTime
  split_ifs
  · exact continuousOn_id
  · exact continuousOn_clockOf _

theorem coe_cTime (hL : L ≠ 0) {u : ℝ} (hu : 0 ≤ u) : (cTime L u : ℝ) = rTime L u :=
  Real.coe_toNNReal _ (rTime_nonneg hL hu)

theorem cTime_le (hL : L ≠ 0) {u : ℝ} (hu : 0 ≤ u) : ((cTime L u : ℝ≥0) : ℝ≥0∞) ≤ L := by
  by_cases h : L = ⊤
  · rw [h]; exact le_top
  · have hlt : rTime L u < L.toReal := by
      unfold rTime; rw [if_neg h]; exact clockOf_lt (ENNReal.toReal_pos hL h) hu
    have : (cTime L u : ℝ) ≤ L.toReal := by rw [coe_cTime hL hu]; exact hlt.le
    calc ((cTime L u : ℝ≥0) : ℝ≥0∞) ≤ ((L.toNNReal : ℝ≥0) : ℝ≥0∞) := by
          exact_mod_cast (show (cTime L u : ℝ) ≤ (L.toNNReal : ℝ) by rw [ENNReal.coe_toNNReal_eq_toReal]; exact this)
      _ = L := ENNReal.coe_toNNReal h

theorem continuousOn_cTime : ContinuousOn (cTime L) (Ici 0) :=
  continuous_real_toNNReal.comp_continuousOn continuousOn_rTime

/-- **A driven canonical stage curve has good times near every parameter.** -/
theorem exists_rat_good {X : Set ℂ} (hXo : IsOpen (H \ fillH X)) {x₀ : ℝ} {p : ℝ≥0 → ℂ} (hL : L ≠ 0)
    (hpc : ContinuousOn p {t | (t : ℝ≥0∞) ≤ L}) (hdr : IsDrivenCurve (canonCurve X x₀ p L)) (t : ℝ≥0) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ q : ℚ, 0 ≤ q ∧ dist ((q : ℝ).toNNReal) t < ε ∧ cTime L ((q : ℝ).toNNReal : ℝ) ∈ canonGood X p L := by
  classical
  by_contra hno
  push Not at hno
  set α : ℝ := max 0 ((t : ℝ) - ε) with hα
  set β : ℝ := (t : ℝ) + ε with hβ
  have hαβ : α < β := max_lt (by positivity) (by linarith)
  have hα0 : 0 ≤ α := le_max_left _ _
  -- Claim 1: no point of `(α, β)` has a good B-time
  have h1 : ∀ v ∈ Ioo α β, cTime L v ∉ canonGood X p L := by
    intro v hv hgood
    have hv0 : 0 < v := lt_of_le_of_lt hα0 hv.1
    have hcont : ContinuousAt (fun v' => p (cTime L v')) v := by
      have hct : ContinuousAt (cTime L) v :=
        continuousOn_cTime.continuousAt (Ici_mem_nhds hv0)
      have hpt : ContinuousWithinAt p {t | (t : ℝ≥0∞) ≤ L} (cTime L v) := hpc _ (cTime_le hL hv0.le)
      have hev : ∀ᶠ v' in 𝓝 v, cTime L v' ∈ {t : ℝ≥0 | (t : ℝ≥0∞) ≤ L} := by
        filter_upwards [Ici_mem_nhds hv0] with v' hv' using cTime_le hL hv'
      exact hpt.tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hct, hev⟩)
    have hnb : (fun v' => p (cTime L v')) ⁻¹' (H \ fillH X) ∈ 𝓝 v := hcont.preimage_mem_nhds (hXo.mem_nhds hgood.2)
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hnb
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show max α (v - δ) < min β (v + δ) from
      max_lt (lt_min hαβ (by linarith [hv.1])) (lt_min (by linarith [hv.2]) (by linarith)))
    have hq0 : (0 : ℝ) ≤ q := hα0.trans ((le_max_left _ _).trans hq1.le)
    have hqα : α < q := lt_of_le_of_lt (le_max_left _ _) hq1
    have hqβ : (q : ℝ) < β := lt_of_lt_of_le hq2 (min_le_left _ _)
    have hqball : (q : ℝ) ∈ ball v δ := by
      rw [mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [le_max_right α (v - δ), min_le_right β (v + δ)]
    refine hno q (by exact_mod_cast hq0) ?_ ⟨cTime_le hL ?_, ?_⟩
    · rw [NNReal.dist_eq, Real.coe_toNNReal _ hq0, abs_lt]
      constructor <;> linarith [le_max_right 0 ((t : ℝ) - ε)]
    · rw [Real.coe_toNNReal _ hq0]; exact hq0
    · have := hball hqball
      rwa [Real.coe_toNNReal _ hq0]
  -- Claim 2: no point of `(α, β)` has a B-time in the closure of the good times
  have h2 : ∀ v ∈ Ioo α β, cTime L v ∉ closure (canonGood X p L) := by
    intro v hv hcl
    have hv0 : 0 < v := lt_of_le_of_lt hα0 hv.1
    obtain ⟨δ, hδ, hδv⟩ : ∃ δ > 0, Icc (v - δ) (v + δ) ⊆ Ioo α β := by
      refine ⟨min ((v - α) / 2) ((β - v) / 2), lt_min (by linarith [hv.1]) (by linarith [hv.2]), ?_⟩
      intro y hy
      constructor
      · linarith [hy.1, min_le_left ((v - α) / 2) ((β - v) / 2), hv.1]
      · linarith [hy.2, min_le_right ((v - α) / 2) ((β - v) / 2), hv.2]
    have hvδ0 : 0 ≤ v - δ := le_of_lt (lt_of_le_of_lt hα0 (hδv ⟨le_rfl, by linarith⟩).1)
    have ha : rTime L (v - δ) < rTime L v := strictMonoOn_rTime hL (mem_Ici.2 hvδ0) (mem_Ici.2 hv0.le) (by linarith)
    have hb : rTime L v < rTime L (v + δ) :=
      strictMonoOn_rTime hL (mem_Ici.2 hv0.le) (mem_Ici.2 (by linarith)) (by linarith)
    set N : Set ℝ≥0 := {s | rTime L (v - δ) < (s : ℝ) ∧ (s : ℝ) < rTime L (v + δ)} with hN
    have hNo : IsOpen N := (isOpen_lt continuous_const NNReal.continuous_coe).inter
      (isOpen_lt NNReal.continuous_coe continuous_const)
    have hvN : cTime L v ∈ N := by
      show rTime L (v - δ) < (cTime L v : ℝ) ∧ (cTime L v : ℝ) < rTime L (v + δ)
      rw [coe_cTime hL hv0.le]; exact ⟨ha, hb⟩
    obtain ⟨s, hsN, hsg⟩ := mem_closure_iff.1 hcl N hNo hvN
    have hIcc : Icc (v - δ) (v + δ) ⊆ Ici 0 := fun y hy => mem_Ici.2 (hvδ0.trans hy.1)
    obtain ⟨v', hv', hv's⟩ := intermediate_value_Icc (by linarith : v - δ ≤ v + δ)
      (continuousOn_rTime.mono hIcc) (show (s : ℝ) ∈ Icc (rTime L (v - δ)) (rTime L (v + δ)) from
        ⟨hsN.1.le, hsN.2.le⟩)
    have hcs : cTime L v' = s := by
      apply NNReal.coe_injective
      rw [coe_cTime hL (hIcc hv'), hv's]
    exact h1 v' (hδv hv') (hcs ▸ hsg)
  -- Claim 3: the curve is constant on `(α, β)`
  set c₀ : ℂ := limUnder (⊥ : Filter ℝ≥0) fun t' => (Mo.hullChart (fillH X) x₀).1 (p t') with hc₀
  have h3 : ∀ v ∈ Ioo α β, canonCurve X x₀ p L v = c₀ := by
    intro v hv
    rw [canonCurve_eq]
    unfold canonVal
    rw [if_neg (h1 v hv)]
    have hbot : 𝓝[canonGood X p L] (cTime L v) = ⊥ := by
      rw [← not_neBot, ← mem_closure_iff_nhdsWithin_neBot]
      exact h2 v hv
    rw [hbot]
  -- Claim 4: a driven curve is not constant on an interval
  set u₁ : ℝ := α + (β - α) / 3 with hu₁
  set u₂ : ℝ := α + 2 * (β - α) / 3 with hu₂
  have hu₁m : u₁ ∈ Ioo α β := ⟨by linarith, by linarith⟩
  have hu₂m : u₂ ∈ Ioo α β := ⟨by linarith, by linarith⟩
  have hu12 : u₁ < u₂ := by linarith
  have hu₁0 : 0 ≤ u₁ := hα0.trans hu₁m.1.le
  have hu₂0 : 0 < u₂ := lt_of_le_of_lt hu₁0 hu12
  obtain ⟨-, -, -, -, hsm, -, -⟩ := hdr.localDriver u₂ hu₂0
  have himg : canonCurve X x₀ p L '' Icc 0 u₂ = canonCurve X x₀ p L '' Icc 0 u₁ := by
    refine Subset.antisymm ?_ (image_mono (Icc_subset_Icc_right hu12.le))
    rintro _ ⟨y, hy, rfl⟩
    by_cases hyu : y ≤ u₁
    · exact ⟨y, ⟨hy.1, hyu⟩, rfl⟩
    · refine ⟨u₁, ⟨hu₁0, le_rfl⟩, ?_⟩
      rw [h3 u₁ hu₁m, h3 y ⟨lt_trans hu₁m.1 (not_le.1 hyu), lt_of_le_of_lt hy.2 hu₂m.2⟩]
  have hlt := hsm ⟨hu₁0, hu12.le⟩ ⟨hu₂0.le, le_rfl⟩ hu12
  unfold capClock at hlt
  rw [himg] at hlt
  exact lt_irrefl _ hlt

end InteractingSLE.Theorem14.SB.Nc
