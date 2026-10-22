import HigherDimLQGContinuity.ForcingCount.Good
import HigherDimLQGContinuity.Forcing.Visits

/-!
# Paths: canonical geodesics, exit intervals, disjoint time intervals

Packet Q9 (deterministic). The canonical geodesic `q9Path D x y H` is a geodesic segment on `[0, 1]` from `x` to `y`
whenever `ρ^D_H` has a constant-speed geodesic (`q9Path_spec`). A continuous path that starts and ends outside an
open set and visits it has an exit interval around each visit (`q9_exit_interval`). Time intervals mapped into
disjoint sets are disjoint (`q9_interval_disjoint`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd e₁)

variable {d : ℕ}

theorem continuous_q9Path (D : DistRd d → ContMetric d) (x y : Rd d) (H : DistRd d) :
    Continuous (q9Path D x y H) :=
  (sec8Sel x y (rho D H).1).continuous.comp continuous_projIcc

/-- The canonical geodesic has the right endpoints and is a geodesic segment on `[0, 1]`. -/
theorem q9Path_spec {D : DistRd d → ContMetric d} {x y : Rd d} {H : DistRd d}
    (h : ∃ γ, IsConstSpeedGeod (rho D H) x y γ) :
    q9Path D x y H 0 = x ∧ q9Path D x y H 1 = y ∧ IsGeodSeg (rho D H) (q9Path D x y H) 0 1 := by
  have hsel := ((exists_measurable_geodSelector x y).choose_spec.2 (rho D H) h).1
  have hsel' : IsConstSpeedGeod (rho D H) x y (sec8Sel x y (rho D H).1) := hsel
  have hgeo := s7b_constSpeed_isGeod (rho D H) x y _ hsel'
  refine ⟨?_, ?_, zero_le_one, hgeo.1, hgeo.2⟩
  · simp only [q9Path, s7b_realPath_zero, hsel'.1]
  · simp only [q9Path, s7b_realPath_one, hsel'.2.1]

/-- **Exit interval** around a visit of an open set. -/
theorem q9_exit_interval {P : ℝ → Rd d} {a b : ℝ} (hP : ContinuousOn P (Icc a b)) {V : Set (Rd d)}
    (hV : IsOpen V) (ha : P a ∉ V) (hb : P b ∉ V) {t₀ : ℝ} (ht₀ : t₀ ∈ Icc a b) (hPt₀ : P t₀ ∈ V) :
    ∃ u w : ℝ, a ≤ u ∧ u < t₀ ∧ t₀ < w ∧ w ≤ b ∧ P u ∉ V ∧ P w ∉ V ∧
      ∀ τ ∈ Ioo u w, P τ ∈ V := by
  let S₁ : Set ℝ := Icc a t₀ ∩ P ⁻¹' Vᶜ
  let S₂ : Set ℝ := Icc t₀ b ∩ P ⁻¹' Vᶜ
  have hS₁c : IsClosed S₁ :=
    (hP.mono (Icc_subset_Icc le_rfl ht₀.2)).preimage_isClosed_of_isClosed isClosed_Icc
      hV.isClosed_compl
  have hS₂c : IsClosed S₂ :=
    (hP.mono (Icc_subset_Icc ht₀.1 le_rfl)).preimage_isClosed_of_isClosed isClosed_Icc
      hV.isClosed_compl
  have hS₁n : S₁.Nonempty := ⟨a, ⟨le_rfl, ht₀.1⟩, ha⟩
  have hS₂n : S₂.Nonempty := ⟨b, ⟨ht₀.2, le_rfl⟩, hb⟩
  have hS₁b : BddAbove S₁ := ⟨t₀, fun t ht => ht.1.2⟩
  have hS₂b : BddBelow S₂ := ⟨t₀, fun t ht => ht.1.1⟩
  have hu := hS₁c.csSup_mem hS₁n hS₁b
  have hw := hS₂c.csInf_mem hS₂n hS₂b
  have hut : sSup S₁ < t₀ := lt_of_le_of_ne hu.1.2 (fun h => hu.2 (h ▸ hPt₀))
  have htw : t₀ < sInf S₂ := lt_of_le_of_ne hw.1.1 (fun h => hw.2 (h.symm ▸ hPt₀))
  refine ⟨sSup S₁, sInf S₂, hu.1.1, hut, htw, hw.1.2, hu.2, hw.2, fun τ hτ => ?_⟩
  by_contra hnot
  rcases le_total τ t₀ with hτt | hτt
  · have hmem : τ ∈ S₁ := ⟨⟨hu.1.1.trans hτ.1.le, hτt⟩, hnot⟩
    exact (not_le.2 hτ.1) (le_csSup hS₁b hmem)
  · have hmem : τ ∈ S₂ := ⟨⟨hτt, hτ.2.le.trans hw.1.2⟩, hnot⟩
    exact (not_le.2 hτ.2) (csInf_le hS₂b hmem)

/-- On the closed exit interval the path stays in the closure of the open set (here a closed ball). -/
theorem q9_exit_interval_closedBall {P : ℝ → Rd d} {u w : ℝ} (huw : u < w)
    (hP : ContinuousOn P (Icc u w)) {z : Rd d} {r : ℝ} (hin : ∀ τ ∈ Ioo u w, P τ ∈ ball z r) :
    ∀ τ ∈ Icc u w, P τ ∈ closedBall z r := by
  have hcl : IsClosed (Icc u w ∩ P ⁻¹' closedBall z r) :=
    hP.preimage_isClosed_of_isClosed isClosed_Icc isClosed_closedBall
  have hsub : Ioo u w ⊆ Icc u w ∩ P ⁻¹' closedBall z r :=
    fun τ hτ => ⟨Ioo_subset_Icc_self hτ, ball_subset_closedBall (hin τ hτ)⟩
  have h := closure_minimal hsub hcl
  rw [closure_Ioo huw.ne] at h
  exact fun τ hτ => (h hτ).2

/-- Time intervals mapped into disjoint sets are disjoint, in the ordered form used by the chain bound. -/
theorem q9_interval_disjoint {P : ℝ → Rd d} {s₁ t₁ s₂ t₂ : ℝ} (h₁ : s₁ ≤ t₁) (h₂ : s₂ ≤ t₂)
    {A₁ A₂ : Set (Rd d)} (hA : Disjoint A₁ A₂) (hP₁ : ∀ τ ∈ Icc s₁ t₁, P τ ∈ A₁)
    (hP₂ : ∀ τ ∈ Icc s₂ t₂, P τ ∈ A₂) : t₁ < s₂ ∨ t₂ < s₁ := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h12, h21⟩ := hcon
  let τ := max s₁ s₂
  have hτ₁ : τ ∈ Icc s₁ t₁ := ⟨le_max_left _ _, max_le h₁ h12⟩
  have hτ₂ : τ ∈ Icc s₂ t₂ := ⟨le_max_right _ _, max_le h21 h₂⟩
  exact Set.disjoint_left.1 hA (hP₁ τ hτ₁) (hP₂ τ hτ₂)

/-- The unit of a selection site is positive. -/
theorem countUnit_pos (K : CountData d) {s : ℝ} (hs : 0 < s) (z : Rd d) (H : DistRd d) :
    0 < countUnit K s z H :=
  scaleS_pos d K.ξ 1 hs z H

end HigherDimLQGContinuity
