/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1DetConnector
import InteractingSLE.Spec.Supplement.GW1PathLeftLow
import InteractingSLE.Spec.Supplement.GW1WalkExitD4
import InteractingSLE.Spec.Supplement.GW1LaunchClockRun

/-! # The boundary image of an outward real connector (PROVE-GW1-DET) -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.GW1Det

open Exist Exist.Staged Exist.StagedLaw GW1W GW1Path GW1Laws GW1WalkExit GW1WalkFinish

/-- Boundary inverse correspondence on the connector and the existing fibre
invariant identify all its preimages outside the old union. -/
theorem connectorBoundaryImage_of_inverse {d : Chart} {A B : Set ℂ} {v w : ℝ} {I : Set ℝ}
    (hF : GW1Z.FiberGood d A) (hB : B = A ∪ ((↑) : ℝ → ℂ) '' I) (hw : w ∈ I)
    (hwend : Tendsto d.2.1 (𝓝[H] (v : ℂ)) (𝓝 (w : ℂ)))
    (hI : ∀ x ∈ I, ∃ a : ℝ, ((0 ≤ a ∧ a ≤ v) ∨ (v ≤ a ∧ a ≤ 0)) ∧
      Tendsto d.2.1 (𝓝[H] (a : ℂ)) (𝓝 (x : ℂ))) : ConnectorBoundaryImage d A B v := by
  obtain ⟨g, C, hg, _hC, hfib⟩ := hF
  intro f hf
  have hfg : ∀ p ∈ Hbar, f p = g p := by
    intro p hp
    have := GW1P.neBot_nhdsWithin_H hp
    exact tendsto_nhds_unique (hf p hp) (hg p hp)
  have hreal (a : ℝ) : (a : ℂ) ∈ Hbar := by show 0 ≤ (a : ℂ).im; simp only [Complex.ofReal_im, le_refl]
  have hfw : f (v : ℂ) = (w : ℂ) := by
    have := GW1P.neBot_nhdsWithin_H (hreal v)
    exact tendsto_nhds_unique (hf _ (hreal v)) hwend
  refine ⟨hfw ▸ (hB ▸ Or.inr ⟨w, hw, rfl⟩), ?_⟩
  intro p hp hpB
  by_cases hpA : f p ∈ A
  · exact Or.inl hpA
  · right
    rw [hB] at hpB
    obtain ⟨x, hx, hxf⟩ := hpB.resolve_left hpA
    obtain ⟨a, ha, hax⟩ := hI x hx
    have hfa : f (a : ℂ) = (x : ℂ) := by
      have := GW1P.neBot_nhdsWithin_H (hreal a)
      exact tendsto_nhds_unique (hf _ (hreal a)) hax
    refine ⟨a, ?_, ha⟩
    apply hfib p hp (a : ℂ) (hreal a)
    · rw [← hfg p hp, ← hfg _ (hreal a), hfa, hxf]
    · rwa [← hfg p hp]

/-- The right exterior record supplies the inverse correspondence throughout
the closed connector, including the endpoint at chart coordinate `0`. -/
theorem inverse_interval_right {s : ExplState} (hE : ExteriorRecord true s)
    (hB : HasBdryLimits (stChart s).2.1) {w : ℝ} (hw : stPt s < w) :
    (Tendsto (stChart s).2.1 (𝓝[H] ((rProf (stChart s) w : ℝ) : ℂ)) (𝓝 (w : ℂ))) ∧
    ∀ x ∈ Icc (stPt s) w, ∃ a : ℝ, (0 ≤ a ∧ a ≤ rProf (stChart s) w) ∧
      Tendsto (stChart s).2.1 (𝓝[H] (a : ℂ)) (𝓝 (x : ℂ)) := by
  obtain ⟨hR, hpt, hinv⟩ := hE
  have hw' : stRecR s < w := hpt ▸ hw
  have hlim (x : ℝ) (hx : stRecR s < x) :
      Tendsto (stChart s).2.1 (𝓝[H] ((rProf (stChart s) x : ℝ) : ℂ)) (𝓝 (x : ℂ)) := by
    have hp : (stChart s).1 (x : ℂ) ∈ Hbar := by
      rw [hR.1.eq_ofReal x]
      show 0 ≤ ((rProf (stChart s) x : ℝ) : ℂ).im
      simp only [Complex.ofReal_im, le_refl]
    have ht := hB.tendsto hp
    rw [hinv x hx, hR.1.eq_ofReal x] at ht
    exact ht
  refine ⟨hlim w hw', fun x hx => ?_⟩
  rcases hx.1.eq_or_lt with he | hxq
  · subst x
    exact ⟨0, ⟨le_rfl, (hR.2.2.1 w hw').le⟩,
      by simpa only [Complex.ofReal_zero] using
        boundary_limit_of_exteriorRecord (right := true) hB ⟨hR, hpt, hinv⟩⟩
  · have hx' : stRecR s < x := hpt ▸ hxq
    exact ⟨rProf (stChart s) x, ⟨(hR.2.2.1 x hx').le,
      hR.2.1.1.monotoneOn hx' hw' hx.2⟩, hlim x hx'⟩

/-- The corresponding closed-interval inverse correspondence for the left
exterior record, in the original, unreflected chart coordinates. -/
theorem inverse_interval_left {s : ExplState} (hE : ExteriorRecord false s)
    (hB : HasBdryLimits (stChart s).2.1) {w : ℝ} (hw : w < stPt s) :
    (Tendsto (stChart s).2.1 (𝓝[H] ((rProf (stChart s) w : ℝ) : ℂ)) (𝓝 (w : ℂ))) ∧
    ∀ x ∈ Icc w (stPt s), ∃ a : ℝ, (rProf (stChart s) w ≤ a ∧ a ≤ 0) ∧
      Tendsto (stChart s).2.1 (𝓝[H] (a : ℂ)) (𝓝 (x : ℂ)) := by
  obtain ⟨hL, hpt, hinv⟩ := hE
  have hw' : w < stRecL s := hpt ▸ hw
  have hlim (x : ℝ) (hx : x < stRecL s) :
      Tendsto (stChart s).2.1 (𝓝[H] ((rProf (stChart s) x : ℝ) : ℂ)) (𝓝 (x : ℂ)) := by
    have hp : (stChart s).1 (x : ℂ) ∈ Hbar := by
      rw [hL.1.eq_ofReal x]
      show 0 ≤ ((rProf (stChart s) x : ℝ) : ℂ).im
      simp only [Complex.ofReal_im, le_refl]
    have ht := hB.tendsto hp
    rw [hinv x hx, hL.1.eq_ofReal x] at ht
    exact ht
  have hneg (x : ℝ) (hx : x < stRecL s) : rProf (stChart s) x < 0 := by
    have hp := hL.2.2.1 (-x) (neg_lt_neg hx)
    simpa only [lProf_eq, neg_neg, neg_pos] using hp
  refine ⟨hlim w hw', fun x hx => ?_⟩
  rcases hx.2.lt_or_eq with hxq | he
  · have hx' : x < stRecL s := hpt ▸ hxq
    have hm := hL.2.1.1.monotoneOn (neg_lt_neg hx') (neg_lt_neg hw') (neg_le_neg hx.1)
    simp only [lProf_eq, neg_neg, neg_le_neg_iff] at hm
    exact ⟨rProf (stChart s) x, ⟨hm, (hneg x hx').le⟩, hlim x hx'⟩
  · subst x
    exact ⟨0, ⟨(hneg w hw').le, le_rfl⟩,
      by simpa only [Complex.ofReal_zero] using
        boundary_limit_of_exteriorRecord (right := false) hB ⟨hL, hpt, hinv⟩⟩

end InteractingSLE.Theorem14.GW1Det
