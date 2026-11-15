/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkIntCanonRun

/-!
# Canonical hull models identify the inherited walk lift

A `HullModel` supplies geometric domain and mapping-out data, with a real
recentering constant. Its derivative argument is determined by the proved
normalization at infinity. Aux. lemma 57 then supplies the real-collar and
nested-hull zero limits without assuming a lift comparison.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped Real NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.WalkIntCanon

/-- A physical hull model for a chart. This data contains no derivative
logarithm, branch choice, or boundary lift limit. -/
structure HullModel (c : Chart) where
  hull : Set ℂ
  shift : ℝ
  isHull : IsHPHull hull
  dom_eq : (c.dom : Set ℂ) = H \ hull
  mapOut : IsMapOut hull (fun z => c.1 z + (shift : ℂ))

/-- Normalization at infinity fixes the integer between the actual chart
lift and the canonical logarithm of its physical hull map. -/
theorem HullModel.lift_eq_canonical {c : Chart} (M : HullModel c)
    (h : IsNormalized c) {L : ℂ → ℂ}
    (hL : Restart.IsCanonicalDerivLog M.hull (fun z => c.1 z + (M.shift : ℂ)) L) :
    EqOn c.2.2 (fun z => (L z).im) (H \ M.hull) := by
  obtain ⟨Lc, hLc, hlift⟩ := h.derivLift
  have hLc' : IsDerivLog (fun z => c.1 z + (M.shift : ℂ)) Lc (H \ M.hull) := by
    rw [M.dom_eq] at hLc
    exact ⟨hLc.1, fun z hz => by rw [deriv_add_const]; exact hLc.2 z hz⟩
  obtain ⟨n, hn⟩ := IsDerivLog.exists_int_eqOn M.isHull.isOpen
    M.isHull.isConnected.isPreconnected hLc' hL.1
  have he : ∀ z ∈ H \ M.hull,
      c.2.2 z - (L z).im = 2 * π * (n : ℝ) := by
    intro z hz
    rw [hlift z (by rwa [M.dom_eq]), hn hz]
    simp only [add_im, mul_im, mul_re, re_ofNat, im_ofNat, ofReal_re,
      ofReal_im, I_re, I_im, intCast_re, intCast_im]
    ring
  obtain ⟨B, hB⟩ := h.inverse_bound
  have hhigh : Tendsto c.2.1 highHalfPlane highHalfPlane :=
    tendsto_highHalfPlane_of_bound h.conformal.2.1 hB
  have hcan : Tendsto (fun z => (L (c.2.1 z)).im) highHalfPlane (𝓝 0) := by
    have hc := (tendsto_canonicalLog_of_im_atTop M.isHull M.mapOut hL
      tendsto_im_highHalfPlane).comp hhigh
    simpa only [Function.comp_def, zero_im] using continuous_im.tendsto 0 |>.comp hc
  have hdiff := h.lift_limit.sub hcan
  rw [sub_self] at hdiff
  have hconst : Tendsto (fun _ : ℂ => 2 * π * (n : ℝ)) highHalfPlane (𝓝 0) := by
    refine hdiff.congr' ?_
    filter_upwards [eventually_mem_highHalfPlane] with z hz
    exact he _ (by rw [← M.dom_eq]; exact h.conformal.inv_mem_dom hz)
  let _ : NeBot highHalfPlane := highHalfPlane_neBot
  have hn0 : 2 * π * (n : ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds hconst
  intro z hz
  exact sub_eq_zero.1 ((he z hz).trans hn0)

/-- The actual inherited lift tends to zero at an untouched physical real
collar. The approach need only be eventually in H near that real point. -/
theorem HullModel.tendsto_lift_zero {c : Chart} (M : HullModel c)
    (h : IsNormalized c) {a ρ : ℝ} (hρ : 0 < ρ)
    (hd : Disjoint (ball (a : ℂ) ρ) M.hull) {F : Filter ℂ}
    (hF : F ≤ 𝓝[H] (a : ℂ)) : Tendsto c.2.2 F (𝓝 0) := by
  obtain ⟨L, hL⟩ := Restart.exists_isCanonicalDerivLog M.isHull M.mapOut
  have he := M.lift_eq_canonical h hL
  have hlim := (hL.tendsto_im_nhdsWithin_zero M.isHull M.mapOut hρ hd).mono_left hF
  refine hlim.congr' ?_
  filter_upwards [hF self_mem_nhdsWithin,
    hF (nhdsWithin_le_nhds (ball_mem_nhds (a : ℂ) hρ))] with z hz hzb
  exact (he ⟨hz, fun hzh => Set.disjoint_left.1 hd hzb hzh⟩).symm

/-- The inherited lifts of nested physical hull charts have zero difference
where the smaller mapping-out map sees an untouched transition collar. -/
theorem tendsto_lift_sub_of_nested {cA cB : Chart}
    (A : HullModel cA) (B : HullModel cB)
    (hA : IsNormalized cA) (hB : IsNormalized cB) (hAB : A.hull ⊆ B.hull)
    {F : Filter ℂ} (hF : F ≤ 𝓟 (H \ B.hull)) {u ρ : ℝ} (hρ : 0 < ρ)
    (hd : Disjoint (ball (u : ℂ) ρ)
      ((fun z => cA.1 z + (A.shift : ℂ)) '' (B.hull \ A.hull)))
    (hq : Tendsto (fun z => cA.1 z + (A.shift : ℂ)) F (𝓝[H] (u : ℂ))) :
    Tendsto (fun z => cB.2.2 z - cA.2.2 z) F (𝓝 0) := by
  obtain ⟨LA, hLA⟩ := Restart.exists_isCanonicalDerivLog A.isHull A.mapOut
  obtain ⟨LB, hLB⟩ := Restart.exists_isCanonicalDerivLog B.isHull B.mapOut
  have heA := A.lift_eq_canonical hA hLA
  have heB := B.lift_eq_canonical hB hLB
  have hlim := Sec7.ReverseArc.tendsto_im_sub_of_le A.isHull B.isHull hAB
    A.mapOut B.mapOut hLA hLB hF hρ hd hq
  refine hlim.congr' ?_
  filter_upwards [hF (mem_principal_self _)] with z hz
  rw [heB hz, heA ⟨hz.1, fun hza => hz.2 (hAB hza)⟩]

end InteractingSLE.Theorem14.WalkIntCanon
