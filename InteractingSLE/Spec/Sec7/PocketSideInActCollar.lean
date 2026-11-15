/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInRef
import InteractingSLE.Foundations.Loewner.HullBasic
import InteractingSLE.Foundations.Loewner.YuanFiber

/-!
# The terminal-range and surviving half-disc steps of R.5

PROVE-POCKET-SIDEIN. These constructions use the actual terminal trace range,
not a supposed separation of an entire old filled hull in a physical ball.
Trace avoidance becomes filled-hull avoidance only with a surviving point in
the same connected collar. Identifying that point in the actual current face
and excluding added flow pieces remain separate geometric obligations.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology Metric
open QuantumZipper (H)

namespace InteractingSLE.Sec7.PocketStopSide

/-- R.5's old reference time can be rational and later than any specified
earlier visit. The final trace segment avoids a closed physical ball. -/
theorem exists_rat_terminal_trace_avoids {η : ℝ → ℂ}
    (hη : ContinuousOn η (Ici 0)) {a T : ℝ} (ha : 0 ≤ a) (haT : a < T)
    {p : ℂ} (hp : p ≠ η T) :
    ∃ s : ℚ, a < (s : ℝ) ∧ (s : ℝ) < T ∧
      ∃ r > 0, Disjoint (η '' Icc (s : ℝ) T) (closedBall p r) := by
  have he : 0 < dist (η T) p / 3 := div_pos (dist_pos.2 hp.symm) (by norm_num)
  obtain ⟨d, hd, hclose⟩ := Metric.continuousWithinAt_iff.1
    (hη T (ha.trans haT.le)) _ he
  obtain ⟨s, hs₀, hsT⟩ := exists_rat_btwn
    (max_lt haT (by linarith : T - d / 2 < T))
  refine ⟨s, (le_max_left _ _).trans_lt hs₀, hsT,
    dist (η T) p / 3, he, disjoint_left.2 ?_⟩
  rintro z ⟨t, ht, rfl⟩ hz
  have hat : a < t := ((le_max_left _ _).trans_lt hs₀).trans_le ht.1
  have hdt : dist t T < d := by
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.2 ht.2)]
    have := (le_max_right _ _).trans_lt hs₀
    linarith only [this, ht.1, hd]
  have hnear := hclose (ha.trans hat.le) hdt
  have hball : dist (η t) p ≤ dist (η T) p / 3 := mem_closedBall.1 hz
  have htri := dist_triangle (η T) (η t) p
  rw [dist_comm (η T) (η t)] at htri
  linarith

/-- Pull back a physical ball to an upper half-disc along the selected old
inverse-chart approach. No boundary value on a different incident fibre is used. -/
theorem exists_incident_halfDisc_maps_into {f : ℂ → ℂ} {u : ℝ} {p : ℂ}
    (hf : Tendsto f (𝓝[H] (u : ℂ)) (𝓝 p)) {r : ℝ} (hr : 0 < r) :
    ∃ d > 0, f '' (H ∩ ball (u : ℂ) d) ⊆ ball p r := by
  have he := hf.eventually (ball_mem_nhds p hr)
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at he
  obtain ⟨d, hd, hm⟩ := he
  refine ⟨d, hd, ?_⟩
  rintro z ⟨y, hy, rfl⟩
  exact hm (mem_ball.1 hy.2) hy.1

/-- The rational old stop and old-chart half-disc are constructed together.
The conclusion concerns the actual increment trace, before filling. -/
theorem exists_rat_old_chart_trace_collar {η : ℝ → ℂ}
    (hη : ContinuousOn η (Ici 0)) {a T : ℝ} (ha : 0 ≤ a) (haT : a < T)
    {p : ℂ} (hp : p ≠ η T) {f : ℂ → ℂ} {u : ℝ}
    (hf : Tendsto f (𝓝[H] (u : ℂ)) (𝓝 p)) :
    ∃ s : ℚ, a < (s : ℝ) ∧ (s : ℝ) < T ∧ ∃ r > 0, ∃ d > 0,
      Disjoint (η '' Icc (s : ℝ) T) (closedBall p r) ∧
      f '' (H ∩ ball (u : ℂ) d) ⊆ ball p r ∧
      Disjoint (H ∩ ball (u : ℂ) d) (f ⁻¹' (η '' Icc (s : ℝ) T)) := by
  obtain ⟨s, has, hsT, r, hr, havoid⟩ := exists_rat_terminal_trace_avoids hη ha haT hp
  obtain ⟨d, hd, hmap⟩ := exists_incident_halfDisc_maps_into hf hr
  refine ⟨s, has, hsT, r, hr, d, hd, havoid, hmap, disjoint_left.2 ?_⟩
  intro z hz htrace
  exact disjoint_left.1 havoid htrace
    (ball_subset_closedBall (hmap (mem_image_of_mem f hz)))

/-- A connected trace-free collar containing an active point is unfilled.
This is the component argument required in R.5; trace avoidance alone would
not justify the conclusion. -/
theorem collar_subset_compl_fillH {Γ U : Set ℂ} (hU : IsPreconnected U)
    (haway : U ⊆ H \ closure Γ) {z₀ : ℂ} (hz₀ : z₀ ∈ U)
    (hlive : z₀ ∈ H \ fillH Γ) : U ⊆ H \ fillH Γ := by
  have hcomp := hU.subset_connectedComponentIn hz₀ haway
  intro z hz
  refine ⟨(haway hz).1, fun hfill => ?_⟩
  rcases hfill.2 with hc | hb
  · exact (haway hz).2 hc
  · apply hlive.2
    refine ⟨hlive.1, Or.inr ?_⟩
    rwa [← connectedComponentIn_eq (hcomp hz)] at hb

/-- An open upper half-disc avoiding the increment trace also avoids its
closure. One surviving interior point then certifies the entire half-disc. -/
theorem halfDisc_subset_compl_fillH {Γ : Set ℂ} {u : ℝ} {d : ℝ}
    (htrace : Disjoint (H ∩ ball (u : ℂ) d) Γ) {z₀ : ℂ}
    (hz₀ : z₀ ∈ H ∩ ball (u : ℂ) d) (hlive : z₀ ∈ H \ fillH Γ) :
    H ∩ ball (u : ℂ) d ⊆ H \ fillH Γ := by
  have hclosed := htrace.closure_right (QuantumZipper.isOpen_H.inter isOpen_ball)
  exact collar_subset_compl_fillH
    ((convex_H.inter (convex_ball (u : ℂ) d)).isPreconnected)
    (fun z hz => ⟨hz.1, fun hc => disjoint_left.1 hclosed hz hc⟩) hz₀ hlive

/-- Every selected real boundary approach has a collar from the countable
family of half-discs with rational real centre and rational radius. -/
theorem exists_rat_halfDisc_inside {u d : ℝ} (hd : 0 < d) :
    ∃ c r : ℚ, 0 < (r : ℝ) ∧ (u : ℂ) ∈ ball (c : ℂ) (r : ℝ) ∧
      H ∩ ball (c : ℂ) (r : ℝ) ⊆ H ∩ ball (u : ℂ) d := by
  obtain ⟨c, hc₁, hc₂⟩ := exists_rat_btwn (show u - d / 8 < u + d / 8 by linarith)
  obtain ⟨r, hr₁, hr₂⟩ := exists_rat_btwn (show d / 4 < d / 2 by linarith)
  have hcu : dist (c : ℂ) (u : ℂ) < d / 8 := by
    change dist ((c : ℝ) : ℂ) (u : ℂ) < d / 8
    rw [dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_lt]
    constructor <;> linarith
  refine ⟨c, r, by linarith, ?_, ?_⟩
  · rw [mem_ball, dist_comm]
    linarith
  · intro z hz
    refine ⟨hz.1, mem_ball.2 ?_⟩
    have htri := dist_triangle z (c : ℂ) (u : ℂ)
    have hzdist := mem_ball.1 hz.2
    linarith

end InteractingSLE.Sec7.PocketStopSide
