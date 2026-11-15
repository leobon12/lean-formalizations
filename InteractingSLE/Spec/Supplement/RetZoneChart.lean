/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RetZoneLayer

/-!
# Proposition 3.8 in a chart: the deterministic chart setting

Packet PROVE-T15-RET6 (Aux. lemma 82, supplement pp. 296–297). A *chart setting* `IsChartSetting D O G` is an open
set `D ⊆ O ⊆ ℍ` that is a union of components of the open set `O` (in the application `O = ℍ ∖ A₂`, `D` the active
component) with a conformal chart `G : D → ℍ`. This file proves the pathwise facts used by the chart form of
Proposition 3.8:

* `IsChartSetting.infDist_eq`: `dist(z, ∂D) = dist(z, ∂O)` on `D`;
* `IsChartSetting.ball_subset`: a ball centred in `D` and missing `∂O` lies in `D`;
* `IsChartSetting.norm_sub_lt`: on `B(z, ¾ dist(z, ∂D))` the chart moves by less than `8 Im G(z)` (Schwarz for the
  chart's disc map and the Apollonius bound);
* `IsVerBall`, `IsChartSetting.verBall_spec`, `IsChartSetting.exists_verBall`: *verifiable chart balls* — rational
  balls `B(q_i, 1/(j+1))` whose centre is in `D`, which miss `∂O`, and on whose rational points the chart lands in a
  closed set `K`. They describe the open chart patches `D ∩ G⁻¹(K°)` by countably many conditions, each measurable
  as soon as the membership `q ∈ D` and the chart values `G q` are, at the fixed rational points `q`.

Deterministic; no Theorem 1.2/1.3.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped ComplexConjugate

open QuantumZipper (H)
open SupercriticalConformalCovariance (IsConformalBijection)
open QuantumZipper.CA.Koebe (koebeCovConst koebeDistExp koebeCovConst_pos koebeDistExp_pos)

namespace InteractingSLE

namespace RLC

namespace RetZone

/-- The `i`-th point of the dense sequence of `ℂ`. -/
abbrev qpt (i : ℕ) : ℂ := TopologicalSpace.denseSeq ℂ i

/-- The rational radius `1/(j+1)`. -/
abbrev qrad (j : ℕ) : ℝ := 1 / ((j : ℝ) + 1)

lemma qrad_pos (j : ℕ) : 0 < qrad j := by positivity

/-- **A chart setting**: `D ⊆ O ⊆ ℍ` open, `D` a union of components of `O`, and a conformal chart `G : D → ℍ`. -/
structure IsChartSetting (D O : Set ℂ) (G : ℂ → ℂ) : Prop where
  isOpen_D : IsOpen D
  isOpen_O : IsOpen O
  subset_O : D ⊆ O
  O_subset : O ⊆ H
  comp : ∀ z ∈ D, connectedComponentIn O z ⊆ D
  conf : IsConformalBijection G D H

namespace IsChartSetting

variable {D O : Set ℂ} {G : ℂ → ℂ} (hc : IsChartSetting D O G)
include hc

theorem subset_H : D ⊆ H := hc.subset_O.trans hc.O_subset

theorem O_ne_univ : O ≠ univ := ne_univ_of_subset_H hc.O_subset

theorem continuousOn : ContinuousOn G D := hc.conf.1.continuousOn

theorem mapsTo : MapsTo G D H := hc.conf.2.mapsTo

/-- On `D`, the distance to `∂D` is the distance to `∂O`. -/
theorem infDist_eq {z : ℂ} (hz : z ∈ D) : infDist z Dᶜ = infDist z Oᶜ := by
  refine le_antisymm (infDist_le_infDist_of_subset (compl_subset_compl.2 hc.subset_O)
    (nonempty_compl.2 hc.O_ne_univ)) ?_
  have hzO := hc.subset_O hz
  rw [← LocalSets.infDist_compl_connectedComponentIn hc.isOpen_O hc.O_ne_univ hzO]
  exact infDist_le_infDist_of_subset (compl_subset_compl.2 (hc.comp z hz))
    (nonempty_compl.2 (ne_univ_of_subset_H hc.subset_H))

/-- A ball centred in `D` and missing `∂O` lies in `D`. -/
theorem ball_subset {q : ℂ} (hq : q ∈ D) {r : ℝ} (hr : r ≤ infDist q Oᶜ) : ball q r ⊆ D := by
  have hO : ball q r ⊆ O := (ball_subset_ball hr).trans ball_infDist_compl_subset
  by_cases hr0 : 0 < r
  · exact ((convex_ball q r).isPreconnected.subset_connectedComponentIn (mem_ball_self hr0) hO).trans
      (by rw [connectedComponentIn_eq (mem_connectedComponentIn (hc.subset_O hq))]; exact hc.comp q hq)
  · rw [ball_eq_empty.2 (not_lt.1 hr0)]; exact empty_subset _

/-- **The chart oscillation on a Whitney ball**: on `B(z, ¾ dist(z, ∂D))` the chart moves by less than
`8 Im G(z)`. -/
theorem norm_sub_lt {z : ℂ} (hz : z ∈ D) {ζ : ℂ} (hζ : dist ζ z < 3 / 4 * infDist z Dᶜ) :
    ‖G ζ - G z‖ < 8 * (G z).im := by
  have hDne : D ≠ univ := ne_univ_of_subset_H hc.subset_H
  have hd0 : 0 < infDist z Dᶜ := infDist_compl_pos hc.isOpen_D hDne hz
  have hζd : dist ζ z < infDist z Dᶜ := by linarith
  have hζD : ζ ∈ D := ball_infDist_compl_subset (mem_ball.2 hζd)
  have hφ := isConformalBijection_chartDisc hc.conf hz
  have h1 := norm_le_of_isConformalBijection_ball hφ (chartDisc_self G z) hζd
  have h2 : dist ζ z / infDist z Dᶜ < 3 / 4 := by rw [div_lt_iff₀ hd0]; linarith
  have h3 : ‖mobH (G z) (G ζ)‖ < 1 - 1 / 4 := by
    have : ‖chartDisc G z ζ‖ = ‖mobH (G z) (G ζ)‖ := rfl
    linarith
  have := norm_sub_lt_of_norm_mobH_lt (hc.mapsTo hz) (hc.mapsTo hζD) (by norm_num) (by norm_num) h3
  have e : 2 * (G z).im / (1 / 4) = 8 * (G z).im := by ring
  rwa [e] at this

/-- The ball `B(z, ¾ dist(z, ∂D))` lies in `D`. -/
theorem ball_three_quarters_subset {z : ℂ} (hz : z ∈ D) : ball z (3 / 4 * infDist z Dᶜ) ⊆ D := by
  have hDne : D ≠ univ := ne_univ_of_subset_H hc.subset_H
  have hd0 : 0 < infDist z Dᶜ := infDist_compl_pos hc.isOpen_D hDne hz
  exact (ball_subset_ball (by linarith)).trans ball_infDist_compl_subset

end IsChartSetting

/-! ### Verifiable chart balls -/

/-- **A verifiable chart ball**: the rational ball `B(q_i, 1/(j+1))` has its centre in `D`, misses `∂O`, and the
chart values `Gi` at its rational points lie in `K`. -/
def IsVerBall (D O : Set ℂ) (Gi : ℂ → ℂ) (K : Set ℂ) (i j : ℕ) : Prop :=
  qpt i ∈ D ∧ qrad j ≤ infDist (qpt i) Oᶜ ∧ ∀ i' : ℕ, qpt i' ∈ ball (qpt i) (qrad j) → Gi (qpt i') ∈ K

namespace IsChartSetting

variable {D O : Set ℂ} {G : ℂ → ℂ} (hc : IsChartSetting D O G)
include hc

/-- **A verifiable chart ball lies in `D` and the chart sends it into `K`.** -/
theorem verBall_spec {Gi : ℂ → ℂ} (hGi : ∀ z ∈ D, Gi z = G z) {K : Set ℂ} (hK : IsClosed K) {i j : ℕ}
    (hv : IsVerBall D O Gi K i j) : ball (qpt i) (qrad j) ⊆ D ∧ ∀ y ∈ ball (qpt i) (qrad j), G y ∈ K := by
  obtain ⟨hq, hr, hK'⟩ := hv
  have hB := hc.ball_subset hq hr
  refine ⟨hB, fun y hy => ?_⟩
  by_contra hyK
  have hGc : ContinuousAt G y := hc.continuousOn.continuousAt (hc.isOpen_D.mem_nhds (hB hy))
  have hU : ∀ᶠ y' in 𝓝 y, G y' ∈ Kᶜ := hGc.eventually (hK.isOpen_compl.mem_nhds hyK)
  have hV : ∀ᶠ y' in 𝓝 y, y' ∈ ball (qpt i) (qrad j) := isOpen_ball.mem_nhds hy
  obtain ⟨ε, hε, hεs⟩ := Metric.eventually_nhds_iff_ball.1 (hU.and hV)
  obtain ⟨i', hi'⟩ := Metric.denseRange_iff.1 (TopologicalSpace.denseRange_denseSeq ℂ) y ε hε
  have hmem : qpt i' ∈ ball y ε := by rw [mem_ball, dist_comm]; exact hi'
  obtain ⟨h1, h2⟩ := hεs (qpt i') hmem
  exact h1 (by rw [← hGi _ (hB h2)]; exact hK' i' h2)

/-- **Verifiable chart balls cover the chart patches**: if `B(z, ε) ⊆ D` is sent into `K`, every point of
`B(z, ε)` lies in a verifiable chart ball. -/
theorem exists_verBall {Gi : ℂ → ℂ} (hGi : ∀ z ∈ D, Gi z = G z) {K : Set ℂ} {z : ℂ} {ε : ℝ}
    (hzε : ball z ε ⊆ D) (hKε : ∀ y ∈ ball z ε, G y ∈ K) {y : ℂ} (hy : y ∈ ball z ε) :
    ∃ i j : ℕ, y ∈ ball (qpt i) (qrad j) ∧ IsVerBall D O Gi K i j := by
  have hyz : dist y z < ε := hy
  obtain ⟨j, hj⟩ := exists_nat_one_div_lt (show 0 < (ε - dist y z) / 2 by linarith)
  obtain ⟨i, hi⟩ := Metric.denseRange_iff.1 (TopologicalSpace.denseRange_denseSeq ℂ) y (qrad j) (qrad_pos j)
  have hsub : ball (qpt i) (qrad j) ⊆ ball z ε := fun w hw => by
    rw [mem_ball] at hw ⊢
    have h1 : dist (qpt i) y < qrad j := by rw [dist_comm]; exact hi
    have h2 : qrad j < (ε - dist y z) / 2 := hj
    linarith [dist_triangle w (qpt i) y, dist_triangle w y z]
  have hyq : y ∈ ball (qpt i) (qrad j) := by rw [mem_ball]; exact hi
  have hqD : qpt i ∈ D := hzε (hsub (mem_ball_self (qrad_pos j)))
  refine ⟨i, j, hyq, hqD, ?_, fun i' hi' => ?_⟩
  · have hBO : ball (qpt i) (qrad j) ⊆ O := (hsub.trans hzε).trans hc.subset_O
    exact GFF.le_infDist_of_ball_subset hc.O_ne_univ hBO
  · rw [hGi _ (hzε (hsub hi'))]; exact hKε _ (hsub hi')

end IsChartSetting

end RetZone

end RLC

end InteractingSLE
