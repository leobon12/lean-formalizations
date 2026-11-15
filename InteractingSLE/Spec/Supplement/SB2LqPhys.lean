/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2LqAlive

/-!
# Physical aliveness: hull closures transported through a chart

Packet PROVE-T14-SB2LIFT (round 7; step (H2) of handoff §R6.2). At a launch with chart `g` (inverse chart on `ℍ`,
continuous boundary map `ĝ` on `ℍ̄`), the run-chart domain identities at the two stages read
`g '' ℍ = ℍ \ fill P` and `g '' (ℍ \ fill A) = ℍ \ fill P'` (`image_runChart_walk`, lemma (T)). Here `A` is the
closed trace in the chart and `P'` the new physical prefix. For a chart point `y ∈ ℍ̄` whose physical point `ĝ y`
lies off the old closed fill:

* **`mem_closure_fillH_iff_of_chart`**: `y ∈ closure (fill A) ↔ ĝ y ∈ closure (fill P')`, provided `ĝ` is injective
  at `y` on `ℍ̄` (no other point of `ℍ̄` has the same boundary value). (⟹) is continuity: images of hull points are
  in the new fill. (⟸) pulls points of the new fill near `ĝ y` back to hull points (they are off the old fill), then
  uses a convergent subsequence and the injectivity at `y`;
* **`lAlive_iff_notMem_closure_prefix`**: with the aliveness criterion of `SB2LqAlive`, a real nonzero chart point
  `y = c.1 z` with these properties is alive at the stop iff `ĝ y ∉ closure (fill P')`, i.e. physically off the
  closure of the new filled prefix.

The injectivity at `y` is the remaining one-chart input. For the untouched ray beyond the record it is GW1's
`RProf`: the chart maps the ray increasingly onto `(0, ∞)`, and its inverse has the boundary limits there
(`ExteriorInverse`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.SB.Lk

open Exist Exist.Staged Exist.StagedLaw

variable {g ĝ : ℂ → ℂ} {P P' A : Set ℂ}

/-- The filling of a bounded closed set is bounded. -/
theorem isBounded_fillH {F : Set ℂ} (hF : IsClosed F) (hFb : Bornology.IsBounded F) :
    Bornology.IsBounded (fillH F) := by
  obtain ⟨R, hR, hFR, -⟩ := HalfPlaneSep.exists_H_diff_fillH_eq hF hFb
  refine (isBounded_ball (x := (0 : ℂ)) (r := R)).subset fun z hz => ?_
  rw [mem_ball_zero_iff]
  by_contra hzR
  exact (HalfPlaneSep.mem_H_diff_fillH_of_le_norm hF hR hFR (fillH_subset_H _ hz) (not_lt.1 hzR)).2 hz

/-- **Hull closures through a chart.** -/
theorem mem_closure_fillH_iff_of_chart (hinj : InjOn g H) (hĝ : ContinuousOn ĝ Hbar) (hgg : EqOn ĝ g H)
    (hD : g '' H = H \ fillH P) (hD' : g '' (H \ fillH A) = H \ fillH P') (hA : IsCompact A) {y : ℂ}
    (hyH : y ∈ Hbar) (hy0 : ĝ y ∉ closure (fillH P)) (hinjy : ∀ k ∈ Hbar, ĝ k = ĝ y → k = y) :
    y ∈ closure (fillH A) ↔ ĝ y ∈ closure (fillH P') := by
  -- images of hull points lie in the new fill
  have himg : ∀ a ∈ fillH A, g a ∈ fillH P' := fun a ha => by
    have haH : a ∈ H := fillH_subset_H _ ha
    have h1 : g a ∈ g '' H := mem_image_of_mem g haH
    rw [hD] at h1
    by_contra hn
    have h2 : g a ∈ H \ fillH P' := ⟨h1.1, hn⟩
    rw [← hD'] at h2
    obtain ⟨w, hw, hwe⟩ := h2
    exact hw.2 (hinj hw.1 haH hwe ▸ ha)
  constructor
  · intro hy
    obtain ⟨a, haA, hlim⟩ := mem_closure_iff_seq_limit.1 hy
    have haH : ∀ n, a n ∈ Hbar := fun n => QuantumZipper.H_subset_Hbar (fillH_subset_H _ (haA n))
    have hlim' : Tendsto a atTop (𝓝[Hbar] y) := tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall haH⟩
    have hc := (hĝ y hyH).tendsto.comp hlim'
    refine mem_closure_of_tendsto hc (Eventually.of_forall fun n => ?_)
    show ĝ (a n) ∈ fillH P'
    rw [hgg (fillH_subset_H _ (haA n))]
    exact himg _ (haA n)
  · intro hx
    obtain ⟨p, hpP, hplim⟩ := mem_closure_iff_seq_limit.1 hx
    -- eventually off the old closed fill
    obtain ⟨ε, hε, hball⟩ : ∃ ε > 0, ball (ĝ y) ε ∩ fillH P = ∅ := by
      have h := isOpen_compl_iff.2 isClosed_closure |>.mem_nhds hy0
      obtain ⟨ε, hε, hεs⟩ := Metric.mem_nhds_iff.1 h
      exact ⟨ε, hε, eq_empty_of_forall_notMem fun z hz => hεs hz.1 (subset_closure hz.2)⟩
    have hev : ∀ᶠ n in atTop, p n ∈ ball (ĝ y) ε := hplim (ball_mem_nhds _ hε)
    -- the pulled-back hull points
    have hpull : ∀ n, p n ∈ ball (ĝ y) ε → ∃ a ∈ fillH A, g a = p n := fun n hn => by
      have hpH : p n ∈ H := fillH_subset_H _ (hpP n)
      have hpD : p n ∈ H \ fillH P := by
        refine ⟨hpH, fun h => ?_⟩
        have : p n ∈ ball (ĝ y) ε ∩ fillH P := ⟨hn, h⟩
        rw [hball] at this
        exact this
      rw [← hD] at hpD
      obtain ⟨a, haH, hae⟩ := hpD
      refine ⟨a, ?_, hae⟩
      by_contra han
      have h3 : g a ∈ g '' (H \ fillH A) := mem_image_of_mem g ⟨haH, han⟩
      rw [hD'] at h3
      exact h3.2 (hae ▸ hpP n)
    obtain ⟨N, hN⟩ := eventually_atTop.1 hev
    choose! a haA hae using fun n => hpull (n + N) (hN (n + N) (Nat.le_add_left N n))
    -- a convergent subsequence of hull points
    have hAb : Bornology.IsBounded (fillH A) := isBounded_fillH hA.isClosed hA.isBounded
    have hcpt : IsCompact (closure (fillH A)) := hAb.isCompact_closure
    obtain ⟨k, hk, φ, hφ, hklim⟩ := hcpt.tendsto_subseq fun n => subset_closure (haA n)
    have hkH : k ∈ Hbar := by
      have : closure (fillH A) ⊆ Hbar := by
        rw [← QuantumZipper.CA.Car.closure_H_eq_Hbar]
        exact closure_mono (fillH_subset_H _)
      exact this hk
    have hlim1 : Tendsto (fun n => ĝ (a (φ n))) atTop (𝓝 (ĝ k)) := by
      have h1 : Tendsto (fun n => a (φ n)) atTop (𝓝[Hbar] k) := tendsto_nhdsWithin_iff.2
        ⟨hklim, Eventually.of_forall fun n => QuantumZipper.H_subset_Hbar (fillH_subset_H _ (haA (φ n)))⟩
      exact (hĝ k hkH).tendsto.comp h1
    have hlim2 : Tendsto (fun n => ĝ (a (φ n))) atTop (𝓝 (ĝ y)) := by
      have h2 : Tendsto (fun n => p (φ n + N)) atTop (𝓝 (ĝ y)) :=
        hplim.comp (tendsto_atTop_mono (fun n => Nat.le_add_right (φ n) N) hφ.tendsto_atTop)
      refine h2.congr fun n => ?_
      rw [hgg (fillH_subset_H _ (haA (φ n))), hae (φ n)]
    have hky : k = y := hinjy k hkH (tendsto_nhds_unique hlim1 hlim2)
    exact hky ▸ hk

/-- **Physical aliveness at a launch**: a real nonzero chart point whose physical point is off the old closed fill,
and at which the boundary map is injective, is alive at the stop iff its physical point is off the closure of the
new filled prefix. -/
theorem lAlive_iff_notMem_closure_prefix {c : Chart} {D : (ℝ≥0 → ℝ) × ℝ≥0∞} (hP : GW1P.PieceRegular D.1 D.2)
    (hfin : D.2 ≠ ⊤) {z : ℂ} (hre : (c.1 z).im = 0) (hne : c.1 z ≠ 0) (hinj : InjOn g H) (hĝ : ContinuousOn ĝ Hbar)
    (hgg : EqOn ĝ g H) (hD : g '' H = H \ fillH P)
    (hD' : g '' (H \ fillH (LuM.trOf D '' Icc 0 D.2.toNNReal)) = H \ fillH P')
    (hA : IsCompact (LuM.trOf D '' Icc 0 D.2.toNNReal)) (hy0 : ĝ (c.1 z) ∉ closure (fillH P))
    (hinjy : ∀ k ∈ Hbar, ĝ k = ĝ (c.1 z) → k = c.1 z) :
    lAlive c ⊤ D z ↔ ĝ (c.1 z) ∉ closure (fillH P') := by
  have hyH : c.1 z ∈ Hbar := show 0 ≤ (c.1 z).im by rw [hre]
  rw [lAlive_iff_notMem_closure_fillH hP hfin hre hne,
    mem_closure_fillH_iff_of_chart hinj hĝ hgg hD hD' hA hyH hy0 hinjy]

end InteractingSLE.Theorem14.SB.Lk
