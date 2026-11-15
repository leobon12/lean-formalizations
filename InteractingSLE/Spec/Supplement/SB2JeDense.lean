/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2JcAS
import InteractingSLE.Spec.Supplement.SB2NvAS

/-!
# SB2(2)'s v6 rule: the mask's dense readings and record goodness from the stage facts

Packet PROVE-SB2-LIFTSET (round 21, D40; GEOM2's v6 rule `Nv.maskEv`). The v6 mask at a stage asks, besides a
non-zero launched actual instruction, for a good relative state:

* **`denseReads_of`**: the readings of a stage curve at rational curve times are dense (`Nv.DenseReads`) when the
  piece is continuous before its lifetime, `c⁻¹ '' ℍ` is open, the good times are dense below the lifetime, and the
  lifted good points lie in the relative chart's domain (the domain clause of `StageRelP`). The good times below the
  lifetime are open; through the clock their curve times are open and dense, so they contain rational curve times;
* **`isDrvGood_of_stageRelFinP`**: a relative piece with `StageRelFinP` has a good record (`recOf ⊤`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.SB.Lk

open Exist Exist.Staged Exist.StagedLaw LuM GW1W GW1Bookkeep Sec7.PocketTraversal

/-- The stage time is continuous at every nonnegative curve time. -/
theorem continuousAt_stTime (L : ℝ≥0∞) {u : ℝ} (hu : 0 ≤ u) : ContinuousAt (Nv.stTime L) u := by
  unfold Nv.stTime
  by_cases hL : L = ⊤
  · simp only [hL, ↓reduceIte]
    exact continuous_real_toNNReal.continuousAt
  · simp only [hL, ↓reduceIte]
    refine continuous_real_toNNReal.continuousAt.comp ?_
    unfold clockOf
    exact continuousAt_const.mul (continuousAt_id.div (continuousAt_const.add continuousAt_id) (by linarith))

/-- **Dense readings** from the continuity of the piece, open `c⁻¹ '' ℍ`, dense good times and the domain clause. -/
theorem denseReads_of {c : Chart} {m : ℝ} {p : ℝ≥0 → ℂ} {L : ℝ≥0∞} {s₂ : ExplState} (hL : L ≠ 0)
    (hpc : ContinuousOn p {t : ℝ≥0 | (t : ℝ≥0∞) < L}) (hO : IsOpen (c.2.1 '' H))
    (hgd : {t : ℝ≥0 | (t : ℝ≥0∞) < L} ⊆ closure (goodTp c p L))
    (hdom : ∀ t ∈ goodTp c p L, liftPt c m (p t) ∈ (stChart s₂).dom) :
    Nv.DenseReads c m p L s₂ := by
  -- the good times below the lifetime form an open set
  set W := {t : ℝ≥0 | (t : ℝ≥0∞) < L} ∩ p ⁻¹' (c.2.1 '' H) with hWdef
  have hLo : IsOpen {t : ℝ≥0 | (t : ℝ≥0∞) < L} := isOpen_lt ENNReal.continuous_coe continuous_const
  have hWo : IsOpen W := hpc.isOpen_inter_preimage hLo hO
  have hWg : W ⊆ goodTp c p L := fun t ht => ⟨ht.1.le, ht.2⟩
  have hWd : {t : ℝ≥0 | (t : ℝ≥0∞) < L} ⊆ closure W := by
    intro t ht
    have h : t ∈ {t : ℝ≥0 | (t : ℝ≥0∞) < L} ∩ closure (goodTp c p L) := ⟨ht, hgd ht⟩
    refine closure_mono ?_ (hLo.inter_closure h)
    rintro t' ⟨h1, h2⟩
    exact ⟨h1, h2.2⟩
  intro k n
  set u₀ : ℝ := ((ratPt k : ℝ≥0) : ℝ) with hu₀
  have hu₀0 : 0 ≤ u₀ := (ratPt k).2
  have hε : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  set ε := 1 / ((n : ℝ) + 1) with hεdef
  -- a curve time near `u₀` whose stage time is in `W`
  have hmem : u₀ ∈ closure ({u' : ℝ | 0 ≤ u' ∧ Nv.stTime L u' ∈ W} ∩ Ici u₀) := by
    by_cases htop : L = ⊤
    · have hgd' : ∀ t : ℝ≥0, t ∈ closure W := fun t => hWd (show (t : ℝ≥0∞) < L by rw [htop]; exact
        ENNReal.coe_lt_top)
      have h := mem_closure_good_top hgd' hu₀0
      convert h using 3
      ext u'
      simp only [Nv.stTime, htop, ↓reduceIte, mem_ofPred_eq]
    · lift L to ℝ≥0 using htop
      have hL₁ : 0 < L := pos_iff_ne_zero.2 (by exact_mod_cast hL)
      have h := mem_closure_clock_good hL₁ hWd hu₀0
      convert h using 3
      ext u'
      simp only [Nv.stTime, ENNReal.coe_ne_top, ↓reduceIte, ENNReal.coe_toReal, mem_ofPred_eq]
  obtain ⟨u', ⟨⟨hu'0, hu'W⟩, -⟩, hu'd⟩ := Metric.mem_closure_iff.1 hmem (ε / 2) (half_pos hε)
  -- a rational curve time near `u'` still in the open preimage
  have hev : ∀ᶠ u in 𝓝 u', Nv.stTime L u ∈ W := (continuousAt_stTime L hu'0).preimage_mem_nhds (hWo.mem_nhds hu'W)
  obtain ⟨δ, hδ, hδW⟩ := Metric.eventually_nhds_iff.1 hev
  set δ' := min δ (ε / 2) with hδ'def
  have hδ' : 0 < δ' := lt_min hδ (half_pos hε)
  obtain ⟨i, hi1, hi2⟩ := Nv.exists_ratPt_mem_Ioo (show u'.toNNReal < u'.toNNReal + δ'.toNNReal by
    simpa using Real.toNNReal_pos.2 hδ')
  have hi1' : u' < (ratPt i : ℝ) := by
    have := NNReal.coe_lt_coe.2 hi1; rwa [Real.coe_toNNReal _ hu'0] at this
  have hi2' : (ratPt i : ℝ) < u' + δ' := by
    have := NNReal.coe_lt_coe.2 hi2
    rwa [NNReal.coe_add, Real.coe_toNNReal _ hu'0, Real.coe_toNNReal _ hδ'.le] at this
  have hdi : dist ((ratPt i : ℝ)) u' < δ := by
    rw [Real.dist_eq, abs_of_pos (by linarith)]
    linarith [min_le_left δ (ε / 2)]
  have hiW := hδW hdi
  refine ⟨i, ⟨hWg hiW, hdom _ (hWg hiW)⟩, ?_⟩
  rw [NNReal.dist_eq]
  have h1 : |(ratPt i : ℝ) - u'| < ε / 2 := by
    rw [abs_of_pos (by linarith)]; linarith [min_le_right δ (ε / 2)]
  have h2 : |u' - u₀| < ε / 2 := by rw [← Real.dist_eq, dist_comm]; exact hu'd
  calc |(ratPt i : ℝ) - (ratPt k : ℝ)| ≤ |(ratPt i : ℝ) - u'| + |u' - u₀| := by
        rw [hu₀]; exact abs_sub_le _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add h1 h2
    _ = ε := add_halves ε

/-- **A relative piece with `StageRelFinP` has a good record.** -/
theorem isDrvGood_of_stageRelFinP {c : Chart} {m : ℝ} {p : ℝ≥0 → ℂ} {L : ℝ≥0∞} {s₂ : ExplState} {e₂ : Drv}
    (hreg : IsRegularDriver e₂) (h : StageRelFinP c m p L s₂ e₂) :
    LocalExt.IsDrvGood (recHist (recOf ⊤ e₂)) := by
  have hmin : min (⊤ : ℝ≥0∞) e₂.2 = e₂.2 := min_eq_right le_top
  refine isDrvGood_of_continuousOn_le hreg (by rw [hmin]; exact h.1) ?_
  rw [hmin]; exact h.2.1

end InteractingSLE.Theorem14.SB.Lk
