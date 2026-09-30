import QuantumZipper.Proofs.Zipper.SWCoreB7bFlowMain

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-B7c (1): the flow class with separation from the tip `0`

`flow_local_class_sep`: the statement of `SWCore.flow_local_class` (SWCoreB7bFlowMain.lean, whose
proof is repeated verbatim) with one more conclusion: the flow maps stay at distance `≥ c > 0`
from `0` on the `ρ`-thickening (the good reverse-flow solutions keep clearance `c₀/2`). This is
the separation hypothesis of the `𝔥₀` add-on (`ae_transport_family_h0rev`). Own bookkeeping.
-/

noncomputable section

open Complex Filter MeasureTheory Set Metric
open scoped Topology NNReal ENNReal ComplexConjugate

namespace QuantumZipper
namespace SWCore

open RevMapExtension B2

variable {W : ℝ → ℝ}

theorem flow_local_class_sep (hW : Continuous W) {T q : ℝ} (hq0 : 0 < q) (hqT : q ≤ T)
    {u v u' v' : ℝ} (huu' : u < u') (hu'v' : u' < v') (hv'v : v' < v)
    (hLive : ∀ x ∈ Icc u v, ENNReal.ofReal (T - q) < realHitTime (vrev W T) x) {s₀ : ℝ}
    (hs₀ : s₀ ∈ Icc q T) :
    ∃ a b ρ M : ℚ, ∃ ε L c : ℝ, (a : ℝ) < b ∧ 0 < (ρ : ℝ) ∧ 0 < ε ∧ 0 ≤ L ∧ 0 < c ∧
      (∀ s ∈ Icc q T, |s - s₀| ≤ ε → ∀ w : ℝ, |w - W s₀| ≤ ε →
        flowFam W q ![s, w] ∈ BdryClass a b ρ M 1) ∧
      (∀ s ∈ Icc q T, |s - s₀| ≤ ε → ∀ x ∈ Icc u' v',
        realRevMap (vrev W T) (T - s) x ∈ Ioo (a : ℝ) b) ∧
      (∀ s ∈ Icc q T, |s - s₀| ≤ ε → ∀ w : ℝ, |w - W s₀| ≤ ε →
        ∀ s' ∈ Icc q T, |s' - s₀| ≤ ε → ∀ w' : ℝ, |w' - W s₀| ≤ ε →
        ∀ z ∈ thickening (ρ : ℝ) (segC a b),
          ‖flowFam W q ![s, w] z - flowFam W q ![s', w'] z‖ ≤ L * (|s - s'| + |w - w'|)) ∧
      (∀ s ∈ Icc q T, |s - s₀| ≤ ε → ∀ w : ℝ, |w - W s₀| ≤ ε →
        ∀ z ∈ thickening (ρ : ℝ) (segC a b), c ≤ ‖flowFam W q ![s, w] z‖) := by
  set V := vrev W T with hVdef
  have hV : Continuous V := continuous_vrev hW T
  have hτ : 0 ≤ T - q := by linarith
  have huv : u ≤ v := by linarith
  obtain ⟨c₀, hc₀, hcl'⟩ := RegUnif.exists_unif_clearance hV hτ hLive
  have hcl : ∀ x ∈ Icc u v, ∀ σ ∈ Icc (0 : ℝ) (T - q), c₀ ≤ |realRevMap V σ x| :=
    fun x hx σ hσ => by simpa [Real.norm_eq_abs] using hcl' x hx σ hσ
  obtain ⟨Mf, -, hMf⟩ := RegUnif.exists_unif_family_deriv_bounds hW hq0 hqT hLive
  obtain ⟨a, b, η, ε, hη, hε, hεη, hwin⟩ := b7bf_setup hW hqT huu' hu'v' hv'v hLive hs₀
  obtain ⟨Bd, hBd⟩ := isCompact_Icc.exists_bound_of_continuousOn (hW.continuousOn (s := Icc 0 T))
  set R₀ := (c₀ / 4) / Real.exp ((2 / (c₀ / 2) ^ 2) * T) with hR₀def
  have hR₀ : 0 < R₀ := by positivity
  obtain ⟨ρ, hρ0, hρ1⟩ := exists_rat_btwn (lt_min (by positivity : (0 : ℝ) < η / 8)
    (by positivity : (0 : ℝ) < R₀ / 2))
  have hρη : (ρ : ℝ) ≤ η / 8 := hρ1.le.trans (min_le_left _ _)
  have hρR : (ρ : ℝ) ≤ R₀ / 2 := hρ1.le.trans (min_le_right _ _)
  set c₁ := c₀ / 2 with hc₁def
  have hc₁ : 0 < c₁ := by positivity
  set E := Real.exp (2 / c₁ ^ 2 * T) with hEdef
  have hE : 0 < E := Real.exp_pos _
  set Rb := max |(a : ℝ)| |(b : ℝ)| + ρ + η with hRbdef
  obtain ⟨M, hM⟩ := exists_rat_gt (Rb + 2 * Bd + 2 / c₁ * T)
  have hσ : ∀ s ∈ Icc q T, T - s ∈ Icc (0 : ℝ) (T - q) := fun s hs =>
    ⟨by linarith [hs.2], by linarith [hs.1]⟩
  -- points of the translated segment are carrier images of window points
  have hpt : ∀ s ∈ Icc q T, |s - s₀| ≤ ε → ∀ d : ℝ, |d| ≤ η / 2 → ∀ t ∈ Icc (a : ℝ) b,
      ∃ x ∈ Icc u v, realRevMap V (T - s) x = t + d := by
    intro s hs hss d hd t ht
    obtain ⟨w1, -, -, w4, -⟩ := hwin s hs hss
    have hd' := abs_le.1 hd
    exact b7bf_ivt hV hτ huv hLive (hσ s hs) ⟨by linarith [ht.1], by linarith [ht.2]⟩
  -- good solutions on the translated thickening
  have hG : ∀ s ∈ Icc q T, |s - s₀| ≤ ε → ∀ d : ℝ, |d| ≤ η / 2 →
      ∀ z ∈ thickening (ρ : ℝ) (segC a b), ∀ y ∈ ball (z + d) ρ,
        ∃ w, IsCRevSol (vrev W s) y (s - q) w ∧ ∀ r ∈ Icc (0 : ℝ) (s - q), c₁ ≤ ‖w r‖ := by
    intro s hs hss d hd z hz y hy
    obtain ⟨p, ⟨t, ht, rfl⟩, hzt⟩ := mem_thickening_iff.1 hz
    obtain ⟨x, hx, hFx⟩ := hpt s hs hss d hd t ht
    refine b7bf_good hW hq0 hLive hc₀ hcl hs hx y ?_
    rw [mem_ball, hFx]
    have e : dist (z + (d : ℂ)) (((t + d : ℝ)) : ℂ) = dist z (t : ℂ) := by
      rw [Complex.ofReal_add, dist_add_right]
    have := dist_triangle y (z + (d : ℂ)) ((t + d : ℝ) : ℂ)
    rw [mem_ball] at hy
    linarith
  -- shift bounds
  have hdb : ∀ s ∈ Icc q T, |s - s₀| ≤ ε → ∀ w : ℝ, |w - W s₀| ≤ ε → |w - W s| ≤ η / 2 := by
    intro s hs hss w hw
    have h5 := (hwin s hs hss).2.2.2.2
    rw [show w - W s = (w - W s₀) - (W s - W s₀) by ring]
    exact (abs_sub _ _).trans (by linarith)
  have hfam : ∀ s w : ℝ, flowFam W q ![s, w] =
      fun z => revMapExt (vrev W s) (s - q) (z + ((w - W s : ℝ) : ℂ)) := by
    intro s w; funext z; rw [flowFam_apply]; congr 1; push_cast; ring
  refine ⟨a, b, ρ, M, ε, E + 2 / c₁ * E, c₁, ?_, hρ0, hε, by positivity, hc₁, ?_, ?_, ?_, ?_⟩
  rotate_left 4
  · intro s hs hss w hw z hz
    have hmem : z + (w : ℂ) - (W s : ℂ) ∈ ball (z + ((w - W s : ℝ) : ℂ)) ρ := by
      rw [show z + (w : ℂ) - (W s : ℂ) = z + ((w - W s : ℝ) : ℂ) by push_cast; ring]
      exact mem_ball_self hρ0
    obtain ⟨u1, hu1, hb1⟩ := hG s hs hss _ (hdb s hs hss w hw) z hz _ hmem
    rw [flowFam_apply, revMapExt_eq hu1 (by linarith [hs.1])]
    exact hb1 _ ⟨by linarith [hs.1], le_rfl⟩
  · obtain ⟨-, w2, w3, -, -⟩ := hwin s₀ hs₀ (by simp [hε.le])
    have := (b7bf_strictMonoOn hV hLive (hσ s₀ hs₀)).monotoneOn
      (⟨huu'.le, by linarith⟩ : u' ∈ Icc u v) (⟨by linarith, hv'v.le⟩ : v' ∈ Icc u v)
      hu'v'.le
    linarith
  · intro s hs hss w hw
    have hd := hdb s hs hss w hw
    rw [hfam]
    refine b7bf_mem_bdryClass (by linarith [hs.1]) hρ0 hc₁ (w - W s)
      (hG s hs hss _ hd) (R := Rb) (fun z hz => ?_) (B := 2 * Bd) ?_ ?_ fun t ht => ?_
    · obtain ⟨p, ⟨t, ht, rfl⟩, hzt⟩ := mem_thickening_iff.1 hz
      have h1 : ‖z‖ ≤ ‖(t : ℂ)‖ + ρ := by
        have := norm_le_norm_add_norm_sub' z (t : ℂ)
        rw [← dist_eq_norm] at this; linarith
      have h2 : ‖(t : ℂ)‖ ≤ max |(a : ℝ)| |(b : ℝ)| := by
        rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_le_max_abs_abs ht.1 ht.2
      have h3 : ‖((w - W s : ℝ) : ℂ)‖ ≤ η := by
        rw [Complex.norm_real, Real.norm_eq_abs]; linarith
      have := norm_add_le z ((w - W s : ℝ) : ℂ)
      simp only [hRbdef]; linarith
    · have e : vrev W s (s - q) = W q - W s := by
        rw [vrev_of_mem ⟨by linarith [hs.1], by linarith⟩, show s - (s - q) = q by ring]
      rw [e]
      have h1 := hBd q ⟨hq0.le, hqT⟩
      have h2 := hBd s ⟨by linarith [hs.1], hs.2⟩
      rw [Real.norm_eq_abs] at h1 h2
      exact (abs_sub _ _).trans (by linarith)
    · have : 2 / c₁ * (s - q) ≤ 2 / c₁ * T :=
        mul_le_mul_of_nonneg_left (by linarith [hs.2]) (by positivity)
      linarith
    · obtain ⟨x, hx, hFx⟩ := hpt s hs hss _ hd t ht
      have e : (t : ℂ) + ((w - W s : ℝ) : ℂ) = ((realRevMap V (T - s) x : ℝ) : ℂ) := by
        rw [hFx]; push_cast; ring
      rw [e]
      obtain ⟨k1, -, -, -, k5⟩ := hMf s hs x hx
      exact ⟨k1, k5⟩
  · intro s hs hss x hx
    obtain ⟨-, w2, w3, -, -⟩ := hwin s hs hss
    have hm := (b7bf_strictMonoOn hV hLive (hσ s hs)).monotoneOn
    have k1 := hm (⟨huu'.le, by linarith⟩ : u' ∈ Icc u v) ⟨by linarith [hx.1], by linarith [hx.2]⟩
      hx.1
    have k2 := hm ⟨by linarith [hx.1], by linarith [hx.2]⟩ (⟨by linarith, hv'v.le⟩ : v' ∈ Icc u v)
      hx.2
    exact ⟨by linarith, by linarith⟩
  · intro s hs hss w hw s' hs' hss' w' hw' z hz
    rw [flowFam_apply, flowFam_apply]
    have hmem : ∀ r x : ℝ, z + (x : ℂ) - (W r : ℂ) ∈ ball (z + ((x - W r : ℝ) : ℂ)) ρ := by
      intro r x
      rw [show z + (x : ℂ) - (W r : ℂ) = z + ((x - W r : ℝ) : ℂ) by push_cast; ring]
      exact mem_ball_self hρ0
    obtain ⟨u1, hu1, hb1⟩ := hG s hs hss _ (hdb s hs hss w hw) z hz _ (hmem s w)
    obtain ⟨u2, hu2, hb2⟩ := hG s hs hss _ (hdb s hs hss w' hw') z hz _ (hmem s w')
    obtain ⟨u3, hu3, hb3⟩ := hG s' hs' hss' _ (hdb s' hs' hss' w' hw') z hz _ (hmem s' w')
    have hexp : ∀ r ∈ Icc q T, Real.exp (2 / c₁ ^ 2 * (r - q)) ≤ E := fun r hr =>
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (by linarith [hr.2]) (by positivity))
    have t1 := norm_revMapExt_sub_le (by linarith [hs.1] : 0 ≤ s - q) hc₁ hu2 hu1 hb2 hb1
    have e1 : z + (w : ℂ) - (W s : ℂ) - (z + (w' : ℂ) - (W s : ℂ)) = ((w - w' : ℝ) : ℂ) := by
      push_cast; ring
    rw [e1, Complex.norm_real, Real.norm_eq_abs] at t1
    have t1' : ‖revMapExt (vrev W s) (s - q) (z + (w : ℂ) - (W s : ℂ)) -
        revMapExt (vrev W s) (s - q) (z + (w' : ℂ) - (W s : ℂ))‖ ≤ |w - w'| * E :=
      t1.trans (mul_le_mul_of_nonneg_left (hexp s hs) (abs_nonneg _))
    have t2 : ‖revMapExt (vrev W s) (s - q) (z + (w' : ℂ) - (W s : ℂ)) -
        revMapExt (vrev W s') (s' - q) (z + (w' : ℂ) - (W s' : ℂ))‖ ≤ 2 / c₁ * E * |s - s'| := by
      rcases le_total s' s with h | h
      · have k := norm_revMapExt_vrev_time_sub_le hc₁ hq0.le hs'.1 h hu2 hb2 hu3 hb3
        have k2 : 2 * (s - s') / c₁ * Real.exp (2 / c₁ ^ 2 * (s' - q)) ≤ 2 * (s - s') / c₁ * E :=
          mul_le_mul_of_nonneg_left (hexp s' hs') (div_nonneg (by linarith) hc₁.le)
        rw [abs_of_nonneg (by linarith : 0 ≤ s - s')]
        calc _ ≤ _ := k.trans k2
          _ = 2 / c₁ * E * (s - s') := by ring
      · have k := norm_revMapExt_vrev_time_sub_le hc₁ hq0.le hs.1 h hu3 hb3 hu2 hb2
        have k2 : 2 * (s' - s) / c₁ * Real.exp (2 / c₁ ^ 2 * (s - q)) ≤ 2 * (s' - s) / c₁ * E :=
          mul_le_mul_of_nonneg_left (hexp s hs) (div_nonneg (by linarith) hc₁.le)
        rw [norm_sub_rev, abs_sub_comm, abs_of_nonneg (by linarith : 0 ≤ s' - s)]
        calc _ ≤ _ := k.trans k2
          _ = 2 / c₁ * E * (s' - s) := by ring
    have k1 : 0 ≤ E * |s - s'| := mul_nonneg hE.le (abs_nonneg _)
    have k2 : 0 ≤ 2 / c₁ * E * |w - w'| := mul_nonneg (by positivity) (abs_nonneg _)
    have eq : (E + 2 / c₁ * E) * (|s - s'| + |w - w'|) =
        |w - w'| * E + 2 / c₁ * E * |s - s'| + (E * |s - s'| + 2 / c₁ * E * |w - w'|) := by ring
    calc _ ≤ _ := norm_sub_le_norm_sub_add_norm_sub _
          (revMapExt (vrev W s) (s - q) (z + (w' : ℂ) - (W s : ℂ))) _
      _ ≤ |w - w'| * E + 2 / c₁ * E * |s - s'| := add_le_add t1' t2
      _ ≤ _ := by rw [eq]; linarith

end SWCore
end QuantumZipper
