/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2FmGeo
import InteractingSLE.Spec.Supplement.SB2QwChart
import QuantumZipper.Proofs.Zipper.F1Side
import QuantumZipper.Proofs.RS.HullBasics

/-!
# D34's clause, step (L): the stepped hull's chart on the free ray

Worker PROVE-SB2-F3LAW (round 2, target 3, handoff §R2.7 item 4). For the step of F3's induction, the retained hull
after B's piece is `Qw.stepHull K x₀ W T = K ∪ Φ⁻¹(K_T)` (`Φ = Mo.hullChart K x₀`, `K_T = fwdHull W T`). Its
mapping-out function is the Loewner map composed with the old one (the hull model `HullModel.loewner` has shift
`x₀ + W_T`, and mapping-out functions are unique), and so are the real boundary values on the free ray:

* **`mapOut_stepHull_eqOn`**: `g_{K'} = (fwdMap W T + W T) ∘ (g_K − x₀) + x₀` on `ℍ ∖ K'`;
* **`bdryVal_stepHull`**: at a real point untouched by `K'`, `a = bdryVal K x − x₀` is untouched by `K_T` (open
  mapping for Aux. 57's reflection) and `bdryVal K' x = bdryVal K_T a + x₀`;
* **`bdryVal_fwdHull_of_alive`**: at an alive real point `bdryVal K_T a = Re f_T(a) + W_T` (the real flow).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open QuantumZipper (H fwdMap fwdHull IsForwardSol)

namespace InteractingSLE.Theorem14.SB.Fm

open Restart Sec7 WalkIntCanon

/-- **The mapping-out function of the stepped hull is the Loewner map composed with the old one**:
`g_{K ∪ Φ⁻¹(K_T)} = g_T ∘ (g_K − x₀) + x₀` on `ℍ ∖ (K ∪ Φ⁻¹(K_T))`, `g_T = fwdMap W T + W T`. -/
theorem mapOut_stepHull_eqOn {K : Set ℂ} (hK : IsHPHull K) (x₀ : ℝ) {W : ℝ → ℝ} (hW : Continuous W)
    (hW0 : W 0 = 0) {T : ℝ} (hT : 0 ≤ T) :
    EqOn (ConformalImage.mapOut (Qw.stepHull K x₀ W T))
      (fun z => fwdMap W T (ConformalImage.mapOut K z - (x₀ : ℂ)) + ((x₀ + W T : ℝ) : ℂ))
      (H \ Qw.stepHull K x₀ W T) := by
  obtain ⟨c, M, hn, hMh, hMs, -, hfwd, -, hinv⟩ := Qw.exists_model hK x₀
  have hstep := Qw.stepHull_eq_model M hn hMh hinv hW hW0 hT
  have hA' := Qw.isHPHull_stepHull hK x₀ hW hW0 hT
  set M' := M.loewner hn hW hW0 hT with hM'
  have h1 : IsMapOut (Qw.stepHull K x₀ W T) (fun z => (c.loewner W T).1 z + (M'.shift : ℂ)) := by
    rw [hstep]; exact M'.mapOut
  have hs' : M'.shift = M.shift + W T := rfl
  intro z hz
  have hzK : z ∈ H \ K := ⟨hz.1, fun h => hz.2 (Or.inl h)⟩
  rw [(ConformalImage.isMapOut_mapOut hA').eqOn hA' h1 hz, hs', hMs]
  simp only [Chart.loewner]
  rw [hfwd hzK, Mo.hullChart_fwd]

/-- **Boundary values compose through the step**: at a real point `x` untouched by the stepped hull, the old boundary
value `a = bdryVal K x − x₀` is untouched by the relative hull `K_T`, and
`bdryVal (K ∪ Φ⁻¹(K_T)) x = bdryVal K_T a + x₀`. -/
theorem bdryVal_stepHull {K : Set ℂ} (hK : IsHPHull K) (x₀ : ℝ) {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0)
    {T : ℝ} (hT : 0 ≤ T) {x r : ℝ} (hr : 0 < r) (hd : Disjoint (ball (x : ℂ) r) (Qw.stepHull K x₀ W T)) :
    (∃ ρ > 0, Disjoint (ball ((bdryVal K x - x₀ : ℝ) : ℂ) ρ) (fwdHull W T)) ∧
      bdryVal (Qw.stepHull K x₀ W T) x = bdryVal (fwdHull W T) (bdryVal K x - x₀) + x₀ := by
  have hA' := Qw.isHPHull_stepHull hK x₀ hW hW0 hT
  have hJ : IsHPHull (fwdHull W T) := isHPHull_fwdHull hW hT
  have hKsub : K ⊆ Qw.stepHull K x₀ W T := subset_union_left
  have hdK : Disjoint (ball (x : ℂ) r) K := hd.mono_right hKsub
  have hg := ConformalImage.isMapOut_mapOut hK
  have hc := Mo.isConformal_hullChart hK x₀
  have hdom := Mo.coe_dom_hullChart hK x₀
  -- points off the stepped hull are sent off `K_T`
  have hoff : ∀ z ∈ H \ Qw.stepHull K x₀ W T, ConformalImage.mapOut K z - (x₀ : ℂ) ∈ H \ fwdHull W T := by
    intro z hz
    have hzK : z ∈ H \ K := ⟨hz.1, fun h => hz.2 (hKsub h)⟩
    have hzd : z ∈ (Mo.hullChart K x₀).dom := by rw [← SetLike.mem_coe, hdom]; exact hzK
    have hm := hc.fwd_mem hzd
    rw [Mo.hullChart_fwd] at hm
    refine ⟨hm, fun hJz => hz.2 (Or.inr ⟨_, hJz, ?_⟩)⟩
    have := hc.inv_fwd hzd
    rwa [Mo.hullChart_fwd] at this
  -- part 1: a ball around `a` misses `K_T` (open mapping for the reflection at `x`)
  have hball : ∃ ρ > 0, Disjoint (ball ((bdryVal K x - x₀ : ℝ) : ℂ) ρ) (fwdHull W T) := by
    obtain ⟨G, hG⟩ := exists_isBdryReflection hK hg hr hdK
    have hx : (x : ℂ) ∈ ball (x : ℂ) (r / 2) := mem_ball_self hG.pos
    have hGx := ofReal_bdryVal_of_reflection hG hx
    have han : AnalyticOnNhd ℂ G (ball (x : ℂ) (r / 2)) := hG.diff.analyticOnNhd isOpen_ball
    have hopen : IsOpen (G '' ball (x : ℂ) (r / 2)) := by
      rcases han.is_constant_or_isOpen (convex_ball _ _).isPreconnected with ⟨w, hw⟩ | h
      · exfalso
        have hy : ((x : ℂ) + ((r / 4 : ℝ) : ℂ) * Complex.I) ∈ ball (x : ℂ) (r / 2) := by
          rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
            Real.norm_eq_abs, abs_of_pos (by linarith [hG.pos])]
          linarith [hG.pos]
        have hne : (x : ℂ) ≠ (x : ℂ) + ((r / 4 : ℝ) : ℂ) * Complex.I := by
          intro h
          have := congrArg Complex.im h
          simp at this
          linarith [hG.pos]
        exact hne (hG.injOn (ConformalImage.isMapOut_mapOut hK) hx hy ((hw _ hx).trans (hw _ hy).symm))
      · exact h _ subset_rfl isOpen_ball
    obtain ⟨ρ, hρ, hρsub⟩ := Metric.isOpen_iff.1 hopen (G x) ⟨x, hx, rfl⟩
    refine ⟨ρ, hρ, Set.disjoint_left.2 fun w hw hwJ => ?_⟩
    have hwH : w ∈ H := hJ.1 hwJ
    have hw' : w + (x₀ : ℂ) ∈ ball (G x) ρ := by
      rw [← hGx, mem_ball, dist_eq_norm]
      rw [mem_ball, dist_eq_norm] at hw
      convert hw using 2; push_cast; ring
    obtain ⟨z, hz, hGz⟩ := hρsub hw'
    have hzH : z ∈ H := by
      by_contra hzH
      have hle : z.im ≤ 0 := not_lt.1 hzH
      rcases lt_or_eq_of_le hle with hlt | heq
      · have := hG.im_neg (ConformalImage.isMapOut_mapOut hK) hz hlt
        rw [hGz] at this
        have : (0 : ℝ) < (w + (x₀ : ℂ)).im := by simpa using (show (0 : ℝ) < w.im from hwH)
        linarith
      · have := hG.real_of_im z hz heq
        rw [hGz] at this
        have : (0 : ℝ) < (w + (x₀ : ℂ)).im := by simpa using (show (0 : ℝ) < w.im from hwH)
        linarith
    have hzA' : z ∉ Qw.stepHull K x₀ W T := fun h =>
      Set.disjoint_left.1 hd (ball_subset_ball (by linarith [hG.pos]) hz) h
    have hz2 := hoff z ⟨hzH, hzA'⟩
    rw [← hG.eqOn ⟨hz, hzH⟩, hGz, add_sub_cancel_right] at hz2
    exact hz2.2 hwJ
  refine ⟨hball, ?_⟩
  obtain ⟨ρ, hρ, hρd⟩ := hball
  have hNe := neBot_nhdsWithin_H_real x
  have h1 := tendsto_mapOut_bdryVal hA' hr hd
  have hsub : ∀ᶠ z in 𝓝[H] (x : ℂ), z ∈ H \ Qw.stepHull K x₀ W T := by
    have hev : H ∩ ball (x : ℂ) r ∈ 𝓝[H] (x : ℂ) :=
      inter_mem_nhdsWithin H (isOpen_ball.mem_nhds (mem_ball_self hr))
    filter_upwards [hev] with z hz
    exact ⟨hz.1, fun h => Set.disjoint_left.1 hd hz.2 h⟩
  have hK1 : Tendsto (fun z => ConformalImage.mapOut K z - (x₀ : ℂ)) (𝓝[H] (x : ℂ))
      (𝓝[H] ((bdryVal K x - x₀ : ℝ) : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have h := (tendsto_mapOut_bdryVal hK hr hdK).sub_const (x₀ : ℂ)
      convert h using 2; push_cast; ring
    · filter_upwards [hsub] with z hz using (hoff z hz).1
  have hJ1 := (tendsto_mapOut_bdryVal hJ hρ hρd).comp hK1
  have h2 : Tendsto (ConformalImage.mapOut (Qw.stepHull K x₀ W T)) (𝓝[H] (x : ℂ))
      (𝓝 (((bdryVal (fwdHull W T) (bdryVal K x - x₀) : ℝ) : ℂ) + (x₀ : ℂ))) := by
    refine (hJ1.add_const (x₀ : ℂ)).congr' ?_
    filter_upwards [hsub] with z hz
    have hz2 := hoff z hz
    rw [mapOut_stepHull_eqOn hK x₀ hW hW0 hT hz, Function.comp_apply,
      (ConformalImage.isMapOut_mapOut hJ).eqOn hJ (isMapOut_fwdMap hW hW0 hT) hz2]
    push_cast; ring
  have := tendsto_nhds_unique h1 h2
  exact_mod_cast this

/-- **Boundary values of a Loewner hull at alive real points are the real flow**: an alive real point `a` is
untouched by `K_T`, and `bdryVal K_T a = Re f_T(a) + W_T`. -/
theorem bdryVal_fwdHull_of_alive {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ} (hT : 0 ≤ T) {a : ℝ}
    (hal : ∃ u, IsForwardSol W (a : ℂ) T u) :
    (∃ ρ > 0, Disjoint (ball (a : ℂ) ρ) (fwdHull W T)) ∧ bdryVal (fwdHull W T) a = (fwdMap W T a).re + W T := by
  obtain ⟨v, hv⟩ := hal
  have hJ : IsHPHull (fwdHull W T) := isHPHull_fwdHull hW hT
  obtain ⟨⟨r, hr, hsub⟩, hlim, -⟩ := QuantumZipper.RS.fwdFlow_near_alive_real hW hT hv
  have hd : Disjoint (ball (a : ℂ) r) (fwdHull W T) := Set.disjoint_left.2 fun z hz hzJ =>
    (hsub ⟨hz, hJ.1 hzJ⟩).2 hzJ
  refine ⟨⟨r, hr, hd⟩, ?_⟩
  have hNe := neBot_nhdsWithin_H_real a
  have heq : fwdMap W T (a : ℂ) = v T := QuantumZipper.F1.fwdMap_eq_of_isForwardSol hv ⟨hT, le_rfl⟩
  have h1 := tendsto_mapOut_bdryVal hJ hr hd
  have h2 : Tendsto (ConformalImage.mapOut (fwdHull W T)) (𝓝[H] (a : ℂ)) (𝓝 (v T + (W T : ℂ))) := by
    refine (hlim.add_const _).congr' ?_
    have hev : H ∩ ball (a : ℂ) r ∈ 𝓝[H] (a : ℂ) :=
      inter_mem_nhdsWithin H (isOpen_ball.mem_nhds (mem_ball_self hr))
    filter_upwards [hev] with z hz
    exact ((ConformalImage.isMapOut_mapOut hJ).eqOn hJ (isMapOut_fwdMap hW hW0 hT) (hsub ⟨hz.2, hz.1⟩)).symm
  have h3 := congrArg Complex.re (tendsto_nhds_unique h1 h2)
  rw [heq]
  simpa using h3

end InteractingSLE.Theorem14.SB.Fm
