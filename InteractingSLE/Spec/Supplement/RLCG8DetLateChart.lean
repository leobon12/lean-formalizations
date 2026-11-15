/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RLCG8DetLateTip

/-!
# G8: the initial joint chart and its continuous inverse

Packet PROVE-G8-DET. The retained-chart Carathéodory theorem supplies an
inverse continuous on the closed half-plane, including the retained tip and
the untouched real mark. The two fixed maps factor the actual joint map.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.RLC.G8Det.Late

open Restart

/-- The hydrodynamic boundary coordinate of a physical point. -/
def hydroMark (α β : ℝ≥0 → ℂ) (a r : ℝ≥0) (p : ℂ) : ℝ :=
  (limUnder (𝓝[activeDomain α a β r] p) (ConformalImage.mapOut (jointHull α β a r))).re

/-- The boundary coordinate of the original driver after the fixed obstacle. -/
def seedMark (α β : ℝ≥0 → ℂ) (w : ℝ≥0 → ℝ) (a r : ℝ≥0) : ℝ :=
  (limUnder (𝓝[H] (cutDrive w a 0 : ℂ)) (obstacleMap α β a r)).re

theorem initial_factorization {α β : ℝ≥0 → ℂ} (hcα : Continuous α) (hcβ : Continuous β)
    (hα0 : α 0 = 0) (hβ0 : β 0 = 0) (a r : ℝ≥0) :
    EqOn (ConformalImage.mapOut (jointHull α β a r))
      (obstacleMap α β a r ∘ cutMap α a) (activeDomain α a β r) := by
  rw [domain_eq hcα hcβ]
  exact (ConformalImage.isMapOut_mapOut (isHPHull_jointHull hcα hcβ hα0 hβ0 a r)).eqOn
    (isHPHull_jointHull hcα hcβ hα0 hβ0 a r)
    ((ConformalImage.isMapOut_mapOut (isHPHull_ownHull hcα hα0 a)).comp
      (isHPHull_ownHull hcα hα0 a) (isHPHull_jointHull hcα hcβ hα0 hβ0 a r)
      (ownHull_subset le_rfl)
      (ConformalImage.isMapOut_mapOut (isHPHull_cutObstacle hcα hcβ hα0 hβ0 a r)))

/-- The original joint inverse chart, with the original hydrodynamic real
coordinates rather than the retained-tip translation. -/
structure InitialChart (α β : ℝ≥0 → ℂ) (a r : ℝ≥0) where
  inv : ℂ → ℂ
  continuous_inv : ContinuousOn inv Hbar
  maps_inv : MapsTo inv H (activeDomain α a β r)
  maps_fwd : MapsTo (obstacleMap α β a r ∘ cutMap α a) (activeDomain α a β r) H
  fwd_inv : ∀ w ∈ H, obstacleMap α β a r (cutMap α a (inv w)) = w
  inv_fwd : ∀ z ∈ activeDomain α a β r, inv (obstacleMap α β a r (cutMap α a z)) = z
  left_limit : Tendsto (obstacleMap α β a r ∘ cutMap α a)
    (𝓝[activeDomain α a β r] (β r)) (𝓝[H] (hydroMark α β a r (β r) : ℂ))
  right_limit : Tendsto (obstacleMap α β a r ∘ cutMap α a)
    (𝓝[activeDomain α a β r] 1) (𝓝[H] (hydroMark α β a r 1 : ℂ))
  inv_left : inv (hydroMark α β a r (β r)) = β r
  inv_right : inv (hydroMark α β a r 1) = 1

/-- Construct the initial inverse and both boundary marks from the landed
retained-chart theorem, at an active retained tip and an untouched `1`. -/
theorem exists_initialChart {α β : ℝ≥0 → ℂ}
    (hcop : Sec7.Prop74Order.IsCompleteOrderedPair α β) (hα0 : α 0 = 0) (hβ0 : β 0 = 0)
    {a r : ℝ≥0} (hβH : β r ∈ H) (hβoff : β r ∉ α '' Icc 0 a)
    (hβcl : β r ∈ closure (activeDomain α a β r))
    (h1off : (1 : ℂ) ∉ Restart.prefixSet α a β r)
    (h1cl : (1 : ℂ) ∈ closure (activeDomain α a β r)) : Nonempty (InitialChart α β a r) := by
  have hcα := hcop.1
  have hcβ := hcop.2.2.2.2.1
  have h0α : (α 0).im = 0 := by rw [hα0]; rfl
  have h0β : (β 0).im = 0 := by rw [hβ0]; rfl
  obtain ⟨L, hL, hcharts⟩ := Supp7.exists_retChart hcα.continuousOn hcβ.continuousOn
    (fun t _ => hcop.2.2.1 t) (fun t _ => hcop.2.2.2.2.2.2.1 t) h0α h0β hβH hβoff
    (fun t ht he => ht.ne (hcop.2.2.2.2.2.1 he)) hβcl
  have hB := isHPHull_jointHull hcα hcβ hα0 hβ0 a r
  have hlog := isCanonicalDerivLog_canonDerivLog hB
  let lift : ℂ → ℝ := fun z => (canonDerivLog (jointHull α β a r) z).im
  have hlogc : ContinuousOn lift (activeDomain α a β r) := by
    rw [domain_eq hcα hcβ]
    exact Complex.continuous_im.comp_continuousOn hlog.1.1.continuousOn
  have hlift : ∀ z ∈ activeDomain α a β r,
      deriv (fun z => ConformalImage.mapOut (jointHull α β a r) z - L) z =
        (‖deriv (fun z => ConformalImage.mapOut (jointHull α β a r) z - L) z‖ : ℂ) *
          exp (I * (lift z : ℂ)) := by
    intro z hz
    rw [domain_eq hcα hcβ] at hz
    rw [deriv_sub_const, ← hlog.1.2 z hz]
    exact exp_eq_norm_mul_exp_im _
  obtain ⟨ψ, hC⟩ := hcharts lift hlogc hlift
  have hfac := initial_factorization hcα hcβ hα0 hβ0 a r
  have hmap : MapsTo (obstacleMap α β a r ∘ cutMap α a) (activeDomain α a β r) H := by
    intro z hz
    rw [← hfac hz]
    exact (ConformalImage.isMapOut_mapOut hB).1.2.mapsTo (domain_eq hcα hcβ a r ▸ hz)
  have hreg := Supp7.isChartRegularPoint_of_notMem hcα.continuousOn hcβ.continuousOn h0α h0β h1off
  obtain ⟨v, hv, hvlim, hψv, _⟩ := hC.exists_tendsto_of_regular h0β h1cl hreg
  have hvr : v.im = 0 := by
    by_contra h
    have hvH : v ∈ H := lt_of_le_of_ne hv (Ne.symm h)
    have h1H := (domain_subset_own hcα hcβ a r (hψv ▸ (hC.bijOn h0β).mapsTo hvH)).1
    change 0 < (1 : ℂ).im at h1H
    simp only [one_im, lt_self_iff_false] at h1H
  have hvreal : v = (v.re : ℂ) := (Restart.ofReal_re_eq hvr).symm
  have hRlim : Tendsto (ConformalImage.mapOut (jointHull α β a r))
      (𝓝[activeDomain α a β r] 1) (𝓝 ((v.re + L : ℝ) : ℂ)) := by
    have h := hvlim.add_const (L : ℂ)
    simp only [sub_add_cancel] at h
    have he : v + (L : ℂ) = ((v.re + L : ℝ) : ℂ) := by
      rw [ofReal_add]
      exact congrArg (fun z : ℂ => z + L) hvreal
    exact he ▸ h
  have : (𝓝[activeDomain α a β r] (β r)).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hβcl
  have : (𝓝[activeDomain α a β r] (1 : ℂ)).NeBot := mem_closure_iff_nhdsWithin_neBot.1 h1cl
  have hLm : hydroMark α β a r (β r) = L := by
    change (limUnder _ (ConformalImage.mapOut (fillH (prefixSet α a β r)))).re = L
    rw [hL.limUnder_eq, ofReal_re]
  have hRm : hydroMark α β a r 1 = v.re + L := by rw [hydroMark, hRlim.limUnder_eq, ofReal_re]
  let F : ℂ → ℂ := fun w => ψ (w - L)
  have hFH : ∀ w ∈ H, w - (L : ℂ) ∈ H := fun w hw => Restart.sub_ofReal_mem_H hw L
  have hFD : MapsTo F H (activeDomain α a β r) := fun w hw => (hC.bijOn h0β).mapsTo (hFH w hw)
  refine ⟨{
    inv := F
    continuous_inv := ?_
    maps_inv := hFD
    maps_fwd := hmap
    fwd_inv := ?_
    inv_fwd := ?_
    left_limit := ?_
    right_limit := ?_
    inv_left := ?_
    inv_right := ?_ }⟩
  · exact hC.continuousOn_inv.comp (continuous_id.sub continuous_const).continuousOn
      (fun w hw => by
        change 0 ≤ (w - (L : ℂ)).im
        change 0 ≤ w.im at hw
        simpa only [sub_im, ofReal_im, sub_zero] using hw)
  · intro w hw
    have he := hC.fwd_inv _ (hFH w hw)
    have heq := hfac (hFD hw)
    dsimp only [Function.comp_apply] at heq
    rw [← heq]
    exact sub_left_injective he
  · intro z hz
    dsimp only [F]
    have heq := hfac hz
    dsimp only [Function.comp_apply] at heq
    rw [← heq]
    apply hC.inv_fwd
    rwa [Supp7.activeDomain_retPath h0β]
  · rw [hLm]
    exact tendsto_nhdsWithin_iff.2 ⟨hL.congr' (eventually_mem_nhdsWithin.mono fun z hz => hfac hz),
      eventually_mem_nhdsWithin.mono fun z hz => hmap hz⟩
  · rw [hRm]
    exact tendsto_nhdsWithin_iff.2 ⟨hRlim.congr' (eventually_mem_nhdsWithin.mono fun z hz => hfac hz),
      eventually_mem_nhdsWithin.mono fun z hz => hmap hz⟩
  · rw [hLm]
    exact (show F L = ψ 0 by simp only [F, sub_self]).trans (hC.inv_zero h0β)
  · rw [hRm]
    dsimp only [F]
    rw [ofReal_add, add_sub_cancel_right, ← hvreal]
    exact hψv

end InteractingSLE.RLC.G8Det.Late
