/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R6TrCollar

/-!
# Fixed shared intervals and reflected transitions at all close real times

PROVE-R6-TWO, Astra §5. The hypotheses describe the one common-time
interval and the ordinary one-pocket chart formulas. The later collars,
bounds and real limits are conclusions. Seed corners are permitted.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open QuantumZipper (H Hbar fwdMapInv fwdHull)

namespace InteractingSLE.Sec7.R6Tr

open PocketStopSide R6Fc

/-- R.6(b) and its reflected real limits on one fixed interval for
every sufficiently close real inner time, from a common-time incident
interval. No physical local inclusion at the force landing is needed. -/
theorem reflected_faces_near {V P : Set ℂ} {ψ E₀ EO : ℂ → ℂ} {O : Chart} {I : ℝ → Chart}
    (hO : O.IsConformal) (hEO : EqOn EO O.2.1 H) (hEOc : ContinuousOn EO Hbar)
    (hψ : SupercriticalConformalCovariance.IsConformalBijection ψ V H)
    (hVP : V ⊆ P) (hψc : ContinuousOn ψ P)
    (hE₀ : EqOn E₀ (Function.invFunOn ψ V) H)
    {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {q₀ : ℝ} (hq₀ : 0 ≤ q₀)
    (hEc : ContinuousOn (fun z => E₀ (extendFrom H (fwdMapInv W q₀) z)) Hbar)
    {p : ℂ} (htip : E₀ (extendFrom H (fwdMapInv W q₀) 0) = p)
    (hIncl : V ∩ ψ ⁻¹' (H \ fwdHull W q₀) ⊆ O.dom)
    {K J : Set ℝ} (hK : IsCompact K) (hJK : J ⊆ K) (hJo : IsOpen J)
    (havoid : ∀ x ∈ K, EO (x : ℂ) ≠ p) (hEP : ∀ x ∈ J, EO (x : ℂ) ∈ P)
    (hcollars : ∀ x ∈ K, ∃ r > 0,
      H ∩ ball (x : ℂ) r ⊆ O.1 '' (V ∩ ψ ⁻¹' (H \ fwdHull W q₀)))
    {τ : ℝ} (hτ : 0 < τ)
    (hdom : ∀ q ∈ Ico q₀ (q₀ + τ), ((I q).dom : Set ℂ) = V ∩ ψ ⁻¹' (H \ fwdHull W q))
    (hI : ∀ q ∈ Ico q₀ (q₀ + τ), (I q).IsConformal)
    (hEI : ∀ q ∈ Ico q₀ (q₀ + τ), ∃ E : ℂ → ℂ, EqOn E (I q).2.1 H ∧ ContinuousOn E Hbar)
    (hnorm : ∀ q ∈ Ico q₀ (q₀ + τ), ∃ B : ℝ,
      ∀ w ∈ ((I q).dom : Set ℂ), ‖(I q).1 w‖ ≤ ‖ψ w‖ + B) :
    ∃ θ > 0, ∀ q : ℝ, q₀ ≤ q → q < q₀ + θ →
      ((I q).dom : Set ℂ) ⊆ O.dom ∧
      (∀ x ∈ J, ∃ r > 0, H ∩ ball (x : ℂ) r ⊆
        ((pocketTransitionChart O (I q)).dom : Set ℂ)) ∧
      (∀ x ∈ J, ∃ M : ℝ, ∀ᶠ z in 𝓝[((pocketTransitionChart O (I q)).dom : Set ℂ)] (x : ℂ),
        ‖(pocketTransitionChart O (I q)).1 z‖ ≤ M) ∧
      ∃ G : ℂ → ℂ,
        EqOn G (pocketTransitionChart O (I q)).1 (pocketTransitionChart O (I q)).dom ∧
        ContinuousOn G (((pocketTransitionChart O (I q)).dom : Set ℂ) ∪ Complex.ofReal '' J) ∧
        (∀ x ∈ J, ∃ r > 0, R16.IsRealBoundaryConformal G x r) ∧
        (∀ x ∈ J, (G (x : ℂ)).im = 0) ∧
        (∀ x ∈ J, Tendsto (pocketTransitionChart O (I q)).1
          (𝓝[((pocketTransitionChart O (I q)).dom : Set ℂ)] (x : ℂ)) (𝓝 (G (x : ℂ)))) := by
  obtain ⟨θ₀, hθ₀, hfuture⟩ := compact_collars_persist hO hEO hEOc hψ hE₀ hW hW0 hq₀ hEc htip hIncl hK havoid hcollars
  refine ⟨min θ₀ τ, lt_min hθ₀ hτ, fun q hq hqθ => ?_⟩
  have hqτ : q ∈ Ico q₀ (q₀ + τ) := ⟨hq, hqθ.trans_le (add_le_add le_rfl (min_le_right _ _))⟩
  have hqθ₀ : q < q₀ + θ₀ := hqθ.trans_le (add_le_add le_rfl (min_le_left _ _))
  have hi : ((I q).dom : Set ℂ) ⊆ O.dom := by
    rw [hdom q hqτ]
    intro w hw
    exact hIncl ⟨hw.1, hw.2.1, fun hk => hw.2.2 ((QuantumZipper.fwdHull_mono.1 hq) hk)⟩
  have hTdom := dom_pocketTransitionChart hO (hI q hqτ) hi
  have hc : ∀ x ∈ J, ∃ r > 0, H ∩ ball (x : ℂ) r ⊆
      ((pocketTransitionChart O (I q)).dom : Set ℂ) := by
    intro x hx
    obtain ⟨r, hr, hrf⟩ := hfuture x (hJK hx)
    refine ⟨r, hr, ?_⟩
    rw [hTdom, hdom q hqτ]
    exact hrf q hq hqθ₀
  obtain ⟨B, hB⟩ := hnorm q hqτ
  have hb : ∀ x ∈ J, ∃ M : ℝ, ∀ᶠ z in 𝓝[((pocketTransitionChart O (I q)).dom : Set ℂ)] (x : ℂ),
      ‖(pocketTransitionChart O (I q)).1 z‖ ≤ M := by
    intro x hx
    obtain ⟨a, ha, haψ⟩ := Metric.continuousWithinAt_iff.1 (hψc _ (hEP x hx)) 1 zero_lt_one
    obtain ⟨b, hb, hbE⟩ := Metric.continuousWithinAt_iff.1 (hEOc _ (real_mem_Hbar x)) a ha
    refine ⟨‖ψ (EO (x : ℂ))‖ + 1 + B, ?_⟩
    filter_upwards [nhdsWithin_le_nhds (ball_mem_nhds (x : ℂ) hb), self_mem_nhdsWithin] with z hzb hz
    have hw : O.2.1 z ∈ (I q).dom := ((mem_dom_pocketTransitionChart hO (hI q hqτ) hi).1 hz).2
    have hzH : z ∈ H := (isConformal_pocketTransitionChart hO (hI q hqτ) hi).dom_subset hz
    have hwV : O.2.1 z ∈ V := by
      have hw' : O.2.1 z ∈ ((I q).dom : Set ℂ) := hw
      rw [hdom q hqτ] at hw'
      exact hw'.1
    have he : dist (O.2.1 z) (EO (x : ℂ)) < a := by
      rw [← hEO hzH]
      exact hbE (QuantumZipper.H_subset_Hbar hzH) (mem_ball.1 hzb)
    have hψdist := haψ (hVP hwV) he
    have hn := norm_le_norm_add_norm_sub' (ψ (O.2.1 z)) (ψ (EO (x : ℂ)))
    rw [dist_eq_norm] at hψdist
    have hbound := hB _ hw
    change ‖(I q).1 (O.2.1 z)‖ ≤ _
    linarith
  obtain ⟨E, hE, hEc'⟩ := hEI q hqτ
  obtain ⟨G, hG, hGc, hGr, -⟩ := exists_transition_extension_of_inverse_and_bounds hO (hI q hqτ) hi hE hEc' hJo hc
    (fun x _ => tendsto_of_extension hEO hEOc x) hb
  refine ⟨hi, hc, hb, G, hG, hGc, hGr, ?_, ?_⟩
  · intro x hx
    obtain ⟨r, hr, hrG⟩ := hGr x hx
    exact hrG.2.2.1 x (mem_ball_self hr) (by simp)
  · intro x hx
    have hlim := ((hGc _ (Or.inr ⟨x, hx, rfl⟩)).mono subset_union_left).tendsto
    exact hlim.congr' (eventually_nhdsWithin_of_forall fun z hz => hG hz)

end InteractingSLE.Sec7.R6Tr
