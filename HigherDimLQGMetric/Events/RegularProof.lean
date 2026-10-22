import HigherDimLQGMetric.Events.ScaledEvent
import LQGMetric.Papers.GM.S2.Bilip

/-!
# Lemma R in dimension at least two

This file derives the source regular event from the five uniform consequences
of the sharp weak tightness axiom: crossing, two collar gaps, internal diameter,
and local modulus.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open MeasureTheory Set Metric
open HigherDimLFPP (Rd)
open scoped ENNReal

variable {d : ℕ}

private def coreK (d : ℕ) : Set (Rd d) := annCl 0 1 2
private def collarS (d : ℕ) : Set (Rd d) := sphere 0 (3 / 4) ∪ sphere 0 3

private theorem compact_coreK : IsCompact (coreK d) := by
  refine isCompact_of_isClosed_isBounded (isClosed_annCl _ _ _) ?_
  apply (isBounded_closedBall : Bornology.IsBounded (closedBall (0 : Rd d) 2)).subset
  intro x hx
  simpa only [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hx.2

private theorem compact_collarS : IsCompact (collarS d) :=
  (isCompact_sphere (0 : Rd d) (3 / 4)).union (isCompact_sphere 0 3)

private theorem core_collar_offDiag (p : Rd d × Rd d)
    (hp : p ∈ coreK d ×ˢ collarS d) : p.1 ≠ p.2 := by
  intro heq
  have hcore : 1 ≤ ‖p.1‖ ∧ ‖p.1‖ ≤ 2 := by
    simpa [coreK, annCl] using hp.1
  rcases hp.2 with h | h
  · have hn : ‖p.2‖ = 3 / 4 := by
      simpa only [Metric.mem_sphere, dist_eq_norm, sub_zero] using h
    rw [heq, hn] at hcore
    linarith
  · have hn : ‖p.2‖ = 3 := by
      simpa only [Metric.mem_sphere, dist_eq_norm, sub_zero] using h
    rw [heq, hn] at hcore
    linarith

private theorem crossing_offDiag (p : Rd d × Rd d)
    (hp : p ∈ sphere (0 : Rd d) 1 ×ˢ sphere 0 2) : p.1 ≠ p.2 := by
  intro heq
  have h1 : ‖p.1‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_eq_norm, sub_zero] using hp.1
  have h2 : ‖p.2‖ = 2 := by
    simpa only [Metric.mem_sphere, dist_eq_norm, sub_zero] using hp.2
  rw [heq, h2] at h1
  norm_num at h1

private theorem coreK_subset_buffer :
    coreK d ⊆ annCl (0 : Rd d) (7 / 8) (5 / 2) := by
  intro x hx
  dsimp [coreK, annCl] at hx ⊢
  constructor <;> linarith

/-- The deterministic conjunction behind the high-probability regular event. -/
private theorem unitReg_of_bounds (M N : ContMetric d)
    {U a A₀ ℓ β C κA κB : ℝ}
    (hκA : 0 < κA) (hκB : 0 < κB)
    (hℓA : 4 * max 1 U * ℓ < κA)
    (hℓB : 4 * max 1 U * ℓ < κB) (hCA : C ≤ A₀)
    (hCross : ∀ p ∈ sphere (0 : Rd d) 1 ×ˢ sphere 0 2, a < M.1 p)
    (hCollA : ∀ p ∈ coreK d ×ˢ collarS d, κA < M.1 p)
    (hCollB : ∀ p ∈ coreK d ×ˢ collarS d, κB < N.1 p)
    (hDiam : diamIn M (ann 0 (3 / 4) 3)
      (annCl 0 (7 / 8) (5 / 2)) ≤ ENNReal.ofReal C)
    (hMod : ∀ u ∈ coreK d, ∀ v ∈ coreK d, ‖u - v‖ ≤ β →
      M.internal (ann 0 (3 / 4) 3) u v < ENNReal.ofReal (ℓ / 4)) :
    UnitReg M N U a A₀ ℓ β := by
  unfold UnitReg
  refine ⟨?_, ?_, ?_, hMod⟩
  · unfold acrossDist
    refine le_iInf fun u => le_iInf fun hu => le_iInf fun v => le_iInf fun hv => ?_
    exact ENNReal.ofReal_le_ofReal (hCross (u, v) ⟨hu, hv⟩).le
  · have hmono : diamIn M (ann 0 (3 / 4) 3) (coreK d) ≤
        diamIn M (ann 0 (3 / 4) 3) (annCl 0 (7 / 8) (5 / 2)) := by
      unfold diamIn
      refine iSup_le fun u => iSup_le fun hu => iSup_le fun v => iSup_le fun hv => ?_
      exact le_iSup_of_le u (le_iSup_of_le (coreK_subset_buffer hu)
        (le_iSup_of_le v (le_iSup_of_le (coreK_subset_buffer hv) le_rfl)))
    exact hmono.trans (hDiam.trans (ENNReal.ofReal_le_ofReal hCA))
  · intro ρ hρ
    have hρS : sphere (0 : Rd d) ρ ⊆ collarS d := by
      rcases (by simpa only [mem_insert_iff, mem_singleton_iff] using hρ :
          ρ = 3 / 4 ∨ ρ = 3) with h | h
      · rw [h]
        exact subset_union_left
      · rw [h]
        exact subset_union_right
    have hgap (T : ContMetric d) (κ : ℝ) (hκ : 0 < κ)
        (hκgap : 4 * max 1 U * ℓ < κ)
        (hColl : ∀ p ∈ coreK d ×ˢ collarS d, κ < T.1 p) :
        ENNReal.ofReal (4 * max 1 U * ℓ) <
          setDistIn T (ann 0 (1 / 2) 5) (coreK d) (sphere 0 ρ) := by
      have hle : ENNReal.ofReal κ ≤
          setDistIn T (ann 0 (1 / 2) 5) (coreK d) (sphere 0 ρ) := by
        unfold setDistIn
        refine le_iInf fun u => le_iInf fun hu => le_iInf fun v => le_iInf fun hv => ?_
        exact (ENNReal.ofReal_le_ofReal
          (hColl (u, v) ⟨hu, hρS hv⟩).le).trans (T.ofReal_le_internal _ u v)
      exact ((ENNReal.ofReal_lt_ofReal_iff hκ).2 hκgap).trans_le hle
    exact ⟨hgap M κA hκA hℓA hCollA, hgap N κB hκB hℓB hCollB⟩

/-- Lemma R with the necessary dimension and sharp weak metric hypotheses. -/
theorem regularEvents_of_sharp (hd : 2 ≤ d)
    {ξ Q : ℝ} {A B : DistRd d → ContMetric d}
    (hA : IsSharpWeakExpMetric d ξ Q A)
    (hB : IsSharpWeakExpMetric d ξ Q B) :
    RegularEvents d ξ Q A B := by
  intro U δ hU hδ
  by_cases hδ1 : δ < 1
  · let ε : ℝ≥0∞ := ENNReal.ofReal (δ / 8)
    have hε : 0 < ε := ENNReal.ofReal_pos.mpr (by positivity)
    obtain ⟨a, ha, Hcross⟩ := hA.scaledLowerOffDiag hd
      ((isCompact_sphere (0 : Rd d) 1).prod (isCompact_sphere 0 2))
      crossing_offDiag hε
    obtain ⟨κA, hκA, HcollA⟩ := hA.scaledLowerOffDiag hd
      (compact_coreK.prod compact_collarS) core_collar_offDiag hε
    obtain ⟨κB, hκB, HcollB⟩ := hB.scaledLowerOffDiag hd
      (compact_coreK.prod compact_collarS) core_collar_offDiag hε
    obtain ⟨C, hC, Hdiam⟩ := hA.scaledAnnulusDiameter hd hε
    let A₀ : ℝ := C + 2 * a
    let ℓ : ℝ := min (a / 101) (min κA κB / (8 * max 1 U))
    have hUmax : 0 < max 1 U := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_left _ _)
    have hκmin : 0 < min κA κB := lt_min hκA hκB
    have hℓ : 0 < ℓ := lt_min (by positivity) (by positivity)
    have hℓa : ℓ < a / 100 := by
      have hh : ℓ ≤ a / 101 := min_le_left _ _
      have : a / 101 < a / 100 := by apply div_lt_div_of_pos_left ha <;> norm_num
      exact hh.trans_lt this
    have hℓA : 4 * max 1 U * ℓ < κA := by
      have hh : ℓ ≤ min κA κB / (8 * max 1 U) := min_le_right _ _
      have hk : min κA κB ≤ κA := min_le_left _ _
      apply lt_of_le_of_lt (b := min κA κB / 2)
      · calc
          4 * max 1 U * ℓ ≤ 4 * max 1 U * (min κA κB / (8 * max 1 U)) :=
            mul_le_mul_of_nonneg_left hh (by positivity)
          _ = min κA κB / 2 := by field_simp; ring
      · linarith
    have hℓB : 4 * max 1 U * ℓ < κB := by
      have hh : ℓ ≤ min κA κB / (8 * max 1 U) := min_le_right _ _
      have hk : min κA κB ≤ κB := min_le_right _ _
      apply lt_of_le_of_lt (b := min κA κB / 2)
      · calc
          4 * max 1 U * ℓ ≤ 4 * max 1 U * (min κA κB / (8 * max 1 U)) :=
            mul_le_mul_of_nonneg_left hh (by positivity)
          _ = min κA κB / 2 := by field_simp; ring
      · linarith
    obtain ⟨β₀, hβ₀, hβ₀1, Hmod⟩ :=
      hA.scaledAnnulusModulus hd (show 0 < ℓ / 4 by positivity) hε
    refine ⟨a, A₀, ℓ, β₀, ha, ?_, hℓ, hℓa, hβ₀, hβ₀1, ?_⟩
    · dsimp [A₀]
      linarith
    intro Ω _ P _ h hh r hr z
    let MA : Ω → ContMetric d := fun ω =>
      weakScaledMetric ξ A (fun t => t ^ (ξ * Q)) (h ω) hr z
        (Real.rpow_pos_of_pos hr _)
    let MB : Ω → ContMetric d := fun ω =>
      weakScaledMetric ξ B (fun t => t ^ (ξ * Q)) (h ω) hr z
        (Real.rpow_pos_of_pos hr _)
    let Good : Set Ω := {ω | UnitReg (MA ω) (MB ω) U a A₀ ℓ β₀}
    let E1 : Set Ω := {ω | ¬ ∀ p ∈ sphere (0 : Rd d) 1 ×ˢ sphere 0 2,
      a < scaledField ξ A (fun t => t ^ (ξ * Q)) r z (h ω) p}
    let E2 : Set Ω := {ω | ¬ ∀ p ∈ coreK d ×ˢ collarS d,
      κA < scaledField ξ A (fun t => t ^ (ξ * Q)) r z (h ω) p}
    let E3 : Set Ω := {ω | ¬ ∀ p ∈ coreK d ×ˢ collarS d,
      κB < scaledField ξ B (fun t => t ^ (ξ * Q)) r z (h ω) p}
    let E4 : Set Ω := {ω | ENNReal.ofReal C < diamIn (MA ω)
      (ann 0 (3 / 4) 3) (annCl 0 (7 / 8) (5 / 2))}
    let E5 : Set Ω := {ω | ¬ ∀ u ∈ coreK d, ∀ v ∈ coreK d,
      ‖u - v‖ ≤ β₀ → (MA ω).internal (ann 0 (3 / 4) 3) u v <
        ENNReal.ofReal (ℓ / 4)}
    have hgood (ω : Ω) (h1 : ω ∉ E1) (h2 : ω ∉ E2)
        (h3 : ω ∉ E3) (h4 : ω ∉ E4) (h5 : ω ∉ E5) :
        ω ∈ Good := by
      have hcross : ∀ p ∈ sphere (0 : Rd d) 1 ×ˢ sphere 0 2,
          a < (MA ω).1 p := by
        intro p hp
        rw [weakScaledMetric_apply]
        exact (not_not.mp h1) p hp
      have hcollA : ∀ p ∈ coreK d ×ˢ collarS d,
          κA < (MA ω).1 p := by
        intro p hp
        rw [weakScaledMetric_apply]
        exact (not_not.mp h2) p hp
      have hcollB : ∀ p ∈ coreK d ×ˢ collarS d,
          κB < (MB ω).1 p := by
        intro p hp
        rw [weakScaledMetric_apply]
        exact (not_not.mp h3) p hp
      have hdiam : diamIn (MA ω) (ann 0 (3 / 4) 3)
          (annCl 0 (7 / 8) (5 / 2)) ≤ ENNReal.ofReal C := not_lt.mp h4
      have hmod : ∀ u ∈ coreK d, ∀ v ∈ coreK d,
          ‖u - v‖ ≤ β₀ → (MA ω).internal (ann 0 (3 / 4) 3) u v <
            ENNReal.ofReal (ℓ / 4) := not_not.mp h5
      exact unitReg_of_bounds (MA ω) (MB ω) hκA hκB hℓA hℓB
        (by dsimp [A₀]; linarith) hcross hcollA hcollB hdiam hmod
    have hbad : Goodᶜ ⊆ E1 ∪ E2 ∪ E3 ∪ E4 ∪ E5 := by
      intro ω hω
      by_contra hnot
      simp only [mem_union, not_or] at hnot
      rcases hnot with ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩
      exact hω (hgood ω h1 h2 h3 h4 h5)
    have hE1 : P E1 < ε := Hcross P h hh r hr z
    have hE2 : P E2 < ε := HcollA P h hh r hr z
    have hE3 : P E3 < ε := HcollB P h hh r hr z
    have hE4 : P E4 < ε := Hdiam P h hh r hr z
    have hE5 : P E5 < ε := Hmod P h hh r hr z
    have hbadP : P Goodᶜ ≤ P E1 + P E2 + P E3 + P E4 + P E5 := by
      calc
        P Goodᶜ ≤ P (E1 ∪ E2 ∪ E3 ∪ E4 ∪ E5) := measure_mono hbad
        _ ≤ _ := by
          calc
            P (E1 ∪ E2 ∪ E3 ∪ E4 ∪ E5) ≤ P (E1 ∪ E2 ∪ E3 ∪ E4) + P E5 := measure_union_le _ _
            _ ≤ (P (E1 ∪ E2 ∪ E3) + P E4) + P E5 := by gcongr; exact measure_union_le _ _
            _ ≤ ((P (E1 ∪ E2) + P E3) + P E4) + P E5 := by gcongr; exact measure_union_le _ _
            _ ≤ (((P E1 + P E2) + P E3) + P E4) + P E5 := by gcongr; exact measure_union_le _ _
            _ = P E1 + P E2 + P E3 + P E4 + P E5 := by ac_rfl
    have hεsum : ε + ε + ε + ε + ε ≤ ENNReal.ofReal δ := by
      dsimp [ε]
      have hδ8 : 0 ≤ δ / 8 := by positivity
      rw [← ENNReal.ofReal_add hδ8, ← ENNReal.ofReal_add (by positivity),
        ← ENNReal.ofReal_add (by positivity), ← ENNReal.ofReal_add (by positivity)]
      · exact ENNReal.ofReal_le_ofReal (by linarith)
      all_goals positivity
    have hbadδ : P Goodᶜ ≤ ENNReal.ofReal δ :=
      hbadP.trans ((add_le_add (add_le_add (add_le_add (add_le_add hE1.le hE2.le)
        hE3.le) hE4.le) hE5.le).trans hεsum)
    have hGood : ENNReal.ofReal (1 - δ) ≤ P Good := by
      apply LQGMetric.GM.Bilip.ofReal_le_of_compl_le
      · linarith
      · linarith
      · convert hbadδ using 1; ring_nf
    exact hGood.trans (measure_mono fun ω hω =>
      regEvent_of_unitReg ξ Q U a A₀ ℓ β₀ A B (h ω) hr z hω)
  · refine ⟨1, 2, 1 / 1000, 1 / 2, by norm_num, by norm_num,
      by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
    intro Ω _ P _ h hh r hr z
    have hnonpos : 1 - δ ≤ 0 := by linarith
    simp only [ENNReal.ofReal_eq_zero.mpr hnonpos]
    exact bot_le

end HigherDimLQGMetric
