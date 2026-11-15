/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2QxHull
import InteractingSLE.Spec.Supplement.SB2QwStep
import InteractingSLE.Spec.ZhanGT4.CrosscutA3Swallow
import InteractingSLE.Spec.Exist.StagedLawRun

/-!
# The terminal hull identity of the step `ℓ → ℓ + 2` from the relative versions, at one sample

Worker REVIEW-FABLE-T14 (items 2–3 of PROVE-SB2-LCMEAN's handoff R13.8). At one sample, the relative versions of B's
stage `ℓ` (F2b′'s successor `Na.SB2LowerStageVersionStatement3`) give, at every rational B-time `q` before a stop
`V m`, the retained hull `K₀ ∪ A₂ q` as the complement of `c⁻¹(ℍ ∖ K_{a q})` (`StageVersionG.hull`, `c` the canonical
hull chart `Mo.hullChart K₀ x₀`); the version drivers are the canonical relative driver `e` before the stops (K2's
match); the stops increase to `e`'s lifetime; the clocks reach every level below a stop (`StageVersionG.reach`) and are
continuous. With the stage-set facts of `SB2QxHull` (the stage set through the connector is covered by `K₀` and the
`A₂ q`, `q` rational before B's lifetime) this gives the hull after the piece:

* **`fill_eq_stepHull_at`**: `fill S = K₀ ∪ c⁻¹(K_T)`, `T` the lifetime of `e`, with the record driver `Qw.recDrv e`
  (so that `Qw.isChartTransport_stepField` applies).

All statements are deterministic (no input).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped Real NNReal ENNReal
open QuantumZipper (H Hbar fwdHull)

namespace InteractingSLE.Theorem14.SB.Qx

open Exist Exist.Staged Exist.StagedLaw WalkIntCanon Qw

/-- Two subsets of `ℍ` with the same complement in `ℍ` are equal. -/
theorem eq_of_H_diff_eq {A B : Set ℂ} (hA : A ⊆ H) (hB : B ⊆ H) (h : H \ A = H \ B) : A = B := by
  ext z
  constructor
  · intro hz
    by_contra hzB
    have : z ∈ H \ B := ⟨hA hz, hzB⟩
    rw [← h] at this
    exact this.2 hz
  · intro hz
    by_contra hzA
    have : z ∈ H \ A := ⟨hB hz, hzA⟩
    rw [h] at this
    exact this.2 hz

/-- The pull-back of the complement of a hull through the canonical hull chart. -/
theorem hullChart_inv_image_diff {K₀ J : Set ℂ} (hK₀ : IsHPHull K₀) (x₀ : ℝ) (hJ : J ⊆ H) :
    (Mo.hullChart K₀ x₀).2.1 '' (H \ J) = H \ (K₀ ∪ (Mo.hullChart K₀ x₀).2.1 '' J) := by
  obtain ⟨c, M, hn, hMh, -, -, -, -, hinv⟩ := exists_model hK₀ x₀
  have h1 : (Mo.hullChart K₀ x₀).2.1 '' (H \ J) = c.2.1 '' (H \ J) :=
    image_congr fun z hz => (hinv hz.1).symm
  have h2 : (Mo.hullChart K₀ x₀).2.1 '' J = c.2.1 '' J := image_congr fun z hz => (hinv (hJ hz)).symm
  rw [h1, h2, M.image_inv_diff hn.conformal hJ, hMh]

/-- **The terminal hull identity from the relative versions, at one sample.** -/
theorem fill_eq_stepHull_at {K₀ S : Set ℂ} (hK₀ : IsHPHull K₀) (x₀ : ℝ) {e : (ℝ≥0 → ℝ) × ℝ≥0∞}
    (he : IsRegularDriver e) (hg : LocalExt.IsDrvGood (recHist (recOf ⊤ e))) (hT : e.2 ≠ ⊤)
    (hZ : IsHPHull (fillH S)) (hKZ : K₀ ⊆ fillH S) {A₂ : ℝ≥0 → Set ℂ}
    (hA₂H : ∀ q : ℚ, A₂ (Real.toNNReal q) ⊆ H) (hA₂Z : ∀ q : ℚ, A₂ (Real.toNNReal q) ⊆ fillH S) {L : ℝ≥0∞}
    (hcov : S ∩ H ⊆ K₀ ∪ ⋃ (q : ℚ) (_ : ((Real.toNNReal q : ℝ≥0) : ℝ≥0∞) < L), A₂ (Real.toNNReal q))
    {W : ℕ → ℝ≥0 → ℝ} {a : ℕ → ℝ≥0 → ℝ≥0∞} (hac : ∀ m, Continuous (a m)) (ha0 : ∀ m, a m 0 = 0)
    {V : ℕ → ℝ≥0∞} (hVlt : ∀ m, V m < e.2) (hVsup : ⨆ m, V m = e.2)
    (hmatch : ∀ m, ∀ s : ℝ≥0, (s : ℝ≥0∞) < V m → W m s = e.1 s)
    (hhull : ∀ (q : ℚ) (m : ℕ), a m (Real.toNNReal q) < V m →
      H \ (K₀ ∪ A₂ (Real.toNNReal q)) = (Mo.hullChart K₀ x₀).2.1 ''
        (H \ fwdHull (fun r : ℝ => W m r.toNNReal) (a m (Real.toNNReal q)).toReal))
    (hcover : ∀ q : ℚ, ((Real.toNNReal q : ℝ≥0) : ℝ≥0∞) < L → ∃ m, a m (Real.toNNReal q) < V m)
    (hreach : ∀ (r : ℚ) (m : ℕ), ((Real.toNNReal r : ℝ≥0) : ℝ≥0∞) < V m →
      ∃ t, ((Real.toNNReal r : ℝ≥0) : ℝ≥0∞) ≤ a m t) :
    fillH S = stepHull K₀ x₀ (recDrv e) (e.2.toNNReal : ℝ) := by
  have hWr := continuous_recDrv he hg
  have hW0 := recDrv_zero he
  have hTr : (0 : ℝ) ≤ (e.2.toNNReal : ℝ) := NNReal.coe_nonneg _
  have hVne : ∀ m, V m ≠ ⊤ := fun m => ne_top_of_lt (hVlt m)
  -- the relative driver agrees with the version drivers before the stops
  have hrec : ∀ m, ∀ r : ℝ, 0 ≤ r → ENNReal.ofReal r < V m → (fun r : ℝ => W m r.toNNReal) r = recDrv e r := by
    intro m r hr hrV
    have hlt : ((r.toNNReal : ℝ≥0) : ℝ≥0∞) < V m := hrV
    have hlt' : ((r.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ e.2 := (hlt.trans (hVlt m)).le
    change W m r.toNNReal = e.1 (min ((r.toNNReal : ℝ≥0) : ℝ≥0∞) (min ⊤ e.2)).toNNReal
    rw [min_eq_right le_top, min_eq_left hlt', ENNReal.toNNReal_coe]
    exact hmatch m _ hlt
  refine fill_eq_stepHull_of_cover (ι := ℚ × ℕ) (D := {p | a p.2 (Real.toNNReal p.1) < V p.2})
    (X := fun p => K₀ ∪ A₂ (Real.toNNReal p.1)) (a := fun p => (a p.2 (Real.toNNReal p.1)).toReal)
    hK₀ x₀ hWr hW0 hTr hZ hKZ ?_ ?_ ?_ ?_ ?_
  · -- the times lie in `[0, T]`
    rintro ⟨q, m⟩ hp
    refine ⟨ENNReal.toReal_nonneg, ?_⟩
    change (a m (Real.toNNReal q)).toReal ≤ (e.2.toNNReal : ℝ)
    rw [← ENNReal.coe_toNNReal_eq_toReal]
    exact ENNReal.toReal_mono hT (hp.le.trans (hVlt m).le)
  · -- the hulls before the lifetime
    rintro ⟨q, m⟩ hp
    have hlt : a m (Real.toNNReal q) < V m := hp
    have hane : a m (Real.toNNReal q) ≠ ⊤ := ne_top_of_lt hlt
    have hJH : fwdHull (fun r : ℝ => W m r.toNNReal) (a m (Real.toNNReal q)).toReal ⊆ H := fun z hz => hz.1
    have hc := Mo.isConformal_hullChart hK₀ x₀
    have hinvH : (Mo.hullChart K₀ x₀).2.1 '' fwdHull (fun r : ℝ => W m r.toNNReal)
        (a m (Real.toNNReal q)).toReal ⊆ H := by
      rintro _ ⟨w, hw, rfl⟩
      have hd := hc.inv_mem_dom (hJH hw)
      change (Mo.hullChart K₀ x₀).2.1 w ∈ ((Mo.hullChart K₀ x₀).dom : Set ℂ) at hd
      rw [Mo.coe_dom_hullChart hK₀ x₀] at hd
      exact hd.1
    have h1 := hhull q m hlt
    rw [hullChart_inv_image_diff hK₀ x₀ hJH] at h1
    have h2 := eq_of_H_diff_eq (union_subset hK₀.1 (hA₂H q)) (union_subset hK₀.1 hinvH) h1
    have hTV : (a m (Real.toNNReal q)).toReal < (V m).toReal := ENNReal.toReal_strict_mono (hVne m) hlt
    have hfw : fwdHull (fun r : ℝ => W m r.toNNReal) (a m (Real.toNNReal q)).toReal =
        fwdHull (recDrv e) (a m (Real.toNNReal q)).toReal :=
      ZhanGT4.A34.fwdHull_congr_of_lt (T₀ := (V m).toReal) ENNReal.toReal_nonneg hTV fun r hr =>
        hrec m r hr.1 ((ENNReal.ofReal_lt_iff_lt_toReal hr.1 (hVne m)).2 hr.2)
    change (K₀ ∪ A₂ (Real.toNNReal q)) ∩ H = stepHull K₀ x₀ (recDrv e) (a m (Real.toNNReal q)).toReal
    rw [inter_eq_left.2 (union_subset hK₀.1 (hA₂H q)), h2, hfw]
    rfl
  · -- the hulls lie in the filled set
    rintro ⟨q, m⟩ -
    exact union_subset hKZ (hA₂Z q)
  · -- the stage set is covered
    intro z hz
    rcases hcov hz with hzK | hzA
    · exact Or.inl hzK
    · simp only [mem_iUnion, exists_prop] at hzA
      obtain ⟨q, hqL, hzq⟩ := hzA
      obtain ⟨m, hm⟩ := hcover q hqL
      exact Or.inr (mem_iUnion₂.2 ⟨(q, m), hm, Or.inr hzq⟩)
  · -- the times are cofinal
    intro s hs hsT
    have hsT' : ENNReal.ofReal s < e.2 := by
      rw [ENNReal.ofReal_lt_iff_lt_toReal hs hT, ← ENNReal.coe_toNNReal_eq_toReal]
      exact hsT
    rw [← hVsup] at hsT'
    obtain ⟨m, hm⟩ := lt_iSup_iff.1 hsT'
    obtain ⟨r, -, hsr, hrV⟩ := ENNReal.lt_iff_exists_rat_btwn.1 hm
    obtain ⟨t₀, ht₀⟩ := hreach r m hrV
    have hivt := intermediate_value_Icc (zero_le : (0 : ℝ≥0) ≤ t₀) (hac m).continuousOn
    obtain ⟨t₁, -, ht₁⟩ := hivt ⟨by rw [ha0 m]; exact zero_le, ht₀⟩
    have hU : IsOpen ((a m) ⁻¹' Ioo (ENNReal.ofReal s) (V m)) := isOpen_Ioo.preimage (hac m)
    have ht₁U : t₁ ∈ (a m) ⁻¹' Ioo (ENNReal.ofReal s) (V m) := by
      change a m t₁ ∈ Ioo _ _
      rw [ht₁]
      exact ⟨hsr, hrV⟩
    obtain ⟨q, hqU⟩ := denseRange_rat_toNNReal.exists_mem_open hU ⟨t₁, ht₁U⟩
    have hqU' : a m (Real.toNNReal q) ∈ Ioo (ENNReal.ofReal s) (V m) := hqU
    have hane : a m (Real.toNNReal q) ≠ ⊤ := ne_top_of_lt hqU'.2
    exact ⟨(q, m), hqU'.2, ((ENNReal.ofReal_lt_iff_lt_toReal hs hane).1 hqU'.1).le⟩

end InteractingSLE.Theorem14.SB.Qx
