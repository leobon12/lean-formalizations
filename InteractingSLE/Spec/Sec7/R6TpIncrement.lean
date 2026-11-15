/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R6FcLocal
import InteractingSLE.Spec.Sec7.R6TnBoundary

/-!
# Local incidence at a visit persists away from the moving tip

PROVE-R6-TWO. The input concerns the incident domain at one original
visit. The right neighbourhood of inner times is proved using FACE2's
small-hull-increment theorem; it is no longer an assumed face input.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open QuantumZipper (H Hbar fwdMapInv fwdHull)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R6Tp

open R6Fc

/-- The precise local incident-domain property at one original visit.
Both domains are the actual selected relative domains; an ambient
complement may contain unvisited outer bulges (R88). -/
def HasLocalVisitIncidence (O I : Chart) (p : ℂ) : Prop :=
  ∃ r > 0, (O.dom : Set ℂ) ∩ ball p r ⊆ I.dom

/-- Local agreement at an old capacity persists for short increments
away from the old physical tip. -/
theorem local_inclusion_persists {D V : Set ℂ} {ψ E₀ : ℂ → ℂ}
    (hψ : SupercriticalConformalCovariance.IsConformalBijection ψ V H)
    (hE₀ : EqOn E₀ (Function.invFunOn ψ V) H)
    {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {qT : ℝ} (hqT : 0 ≤ qT)
    (hEc : ContinuousOn (fun z => E₀ (extendFrom H (fwdMapInv W qT) z)) Hbar)
    {p pT : ℂ} (hEtip : E₀ (extendFrom H (fwdMapInv W qT) (0 : ℂ)) = pT) (hne : p ≠ pT)
    {r : ℝ} (hr : 0 < r) (hloc : D ∩ ball p r ⊆ V ∩ ψ ⁻¹' (H \ fwdHull W qT)) :
    ∃ θ > 0, ∃ ε > 0, ∀ q : ℝ, qT ≤ q → q < qT + θ →
      D ∩ ball p ε ⊆ V ∩ ψ ⁻¹' (H \ fwdHull W q) := by
  let d := dist p pT
  have hd : 0 < d := dist_pos.2 hne
  obtain ⟨ρ, hρ, hρE⟩ := Metric.continuousWithinAt_iff.1
    (hEc _ (real_mem_Hbar 0)) (d / 2) (half_pos hd)
  have hB : ∀ z ∈ H, ‖z‖ ≤ ρ / 2 → E₀ (fwdMapInv W qT z) ∈ ball pT (d / 2) := by
    intro z hz hzn
    have hc := hρE (QuantumZipper.H_subset_Hbar hz) (show dist z (0 : ℂ) < ρ by
      rw [dist_zero_right]; linarith)
    simp only [Complex.ofReal_zero] at hc
    rw [hEtip, extendFrom_H_eq (continuousOn_fwdMapInv hW hW0 hqT) hz] at hc
    exact hc
  obtain ⟨θ, hθ, hsmall⟩ := exists_shift_hull_small hW qT hρ
  refine ⟨θ, hθ, min r (d / 2), lt_min hr (half_pos hd), fun q hq hqθ w hw => ?_⟩
  have hwold := hloc ⟨hw.1, ball_subset_ball (min_le_left _ _) hw.2⟩
  have hwB : w ∉ ball pT (d / 2) := by
    intro hb
    have h1 := mem_ball.1 hb
    have h2 := (mem_ball.1 hw.2).trans_le (min_le_right r (d / 2))
    have h3 := dist_triangle p w pT
    rw [dist_comm p w] at h3
    change d ≤ dist w p + dist w pT at h3
    linarith
  refine ⟨hwold.1, hwold.2.1, ?_⟩
  exact mem_of_increment hE₀ hψ hW hW0 hqT hB hq
    (hsmall _ (sub_nonneg.2 hq) (by linarith)) hwold.1 hwold.2.2 hwB

/-- Turn a visit-time local inclusion into all sufficiently close
later landing patches, using the exact current-chart pullback formulas. -/
theorem landingPatch_near_of_chain {C V P : Set ℂ} {O : Chart} {I : ℝ≥0 → Chart}
    {ψ E₀ : ℂ → ℂ} (hψ : SupercriticalConformalCovariance.IsConformalBijection ψ V H)
    (hE₀ : EqOn E₀ (Function.invFunOn ψ V) H)
    {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0)
    {qT t₁ : ℝ≥0} (hqt : qT < t₁)
    (hdom : ∀ q : ℝ≥0, q < t₁ → ((I q).dom : Set ℂ) = V ∩ ψ ⁻¹' (H \ fwdHull W q))
    (hEc : ContinuousOn (fun z => E₀ (extendFrom H (fwdMapInv W qT) z)) Hbar)
    {v : ℝ} {pT : ℂ} (hEtip : E₀ (extendFrom H (fwdMapInv W qT) (0 : ℂ)) = pT)
    (hne : extendFrom H O.2.1 (v : ℂ) ≠ pT)
    (hp : extendFrom H O.2.1 (v : ℂ) ∈ P)
    (hinit : ∃ r > 0, C ∩ ball (extendFrom H O.2.1 (v : ℂ)) r ⊆ V)
    (hvisit : ∃ r > 0, (O.dom : Set ℂ) ∩ ball (extendFrom H O.2.1 (v : ℂ)) r ⊆ (I qT).dom) :
    ∃ θ > 0, ∀ q : ℝ≥0, qT < q → (q : ℝ) < qT + θ →
      R6Tn.IsLandingPatch C V P O (I q) v := by
  obtain ⟨r, hr, hloc⟩ := hvisit
  rw [hdom qT hqt] at hloc
  obtain ⟨θ, hθ, ε, hε, hfuture⟩ := local_inclusion_persists hψ hE₀ hW hW0 qT.coe_nonneg
    hEc hEtip hne hr hloc
  obtain ⟨r₀, hr₀, hinit⟩ := hinit
  refine ⟨min θ ((t₁ : ℝ) - qT), lt_min hθ (sub_pos.2 (by exact_mod_cast hqt)), fun q hlo hhi =>
    ⟨hp, min r₀ ε, lt_min hr₀ hε, ?_, ?_⟩⟩
  · exact fun w hw => hinit ⟨hw.1, ball_subset_ball (min_le_left _ _) hw.2⟩
  · have hqt' : q < t₁ := by
      rw [← NNReal.coe_lt_coe]
      have := min_le_right θ ((t₁ : ℝ) - qT)
      linarith
    rw [hdom q hqt']
    exact fun w hw => hfuture q (by exact_mod_cast hlo.le)
      (hhi.trans_le (add_le_add le_rfl (min_le_left _ _)))
      ⟨hw.1, ball_subset_ball (min_le_right _ _) hw.2⟩

end InteractingSLE.Sec7.R6Tp
