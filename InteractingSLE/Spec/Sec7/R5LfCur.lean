/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5LfReflect
import InteractingSLE.Spec.Sec7.R5LiftSeed
import InteractingSLE.Spec.Supplement.Aux61Mean

/-!
# Lemma R.5's common phase: every reference compared with the current ambient time

Packet PROVE-R5-LIFT2. PROVE-R5-LIFT's route (`R5Lift.R7LiftGeom'`) linked the references to one another
(directedness) and asked each reference to reflect along its whole seed interval. Here every reference `s` is
compared with the CURRENT ambient time `T = T⁰(q)` instead, at the single coordinate of its collar:

* **`tendsto_fwdMap_of_alive`**: if `f_s ∘ F → x ≠ 0` (real) and `x` is off the closed increment hull `K̃_{s′ − s}`,
  then `f_{s′} ∘ F` tends to a real point on the same side of `0` (Markov property; alive real points keep their
  side);
* **`ref_lift_side_of_cur`**: at a coordinate `ξ` of the current chart (`dom = C ∩ (ℍ ∖ K_T)`) landing in `C`, with an
  unfilled collar of a reference chart (`dom = C ∩ (ℍ ∖ K_s)`) at `x`: if the current lift minus `arg f_T′` tends to
  `2πn` at `ξ`, then the current lift minus `arg f_s′` tends to `2πn` too, and the side of the ambient image at time
  `s` is the side at time `T` (local surjectivity of the reflected transition at `x` for `s ≤ T`, at `ξ` for `T ≤ s`);
* **`exists_int_forall_tendsto_cur`**: one integer `n` on an open interval of current coordinates whose landings all
  lie in `K_T` (reflection along the interval, `R5Lift.exists_int_forall_tendsto_lift_sub`).

Ruling R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any result taking
them as hypotheses.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv logDerivFwd isOpen_H IsForwardSol)

namespace InteractingSLE.Sec7.R5Lift

/-- **An alive real point keeps its side**: for a continuous driver with `W 0 = 0` and a forward solution from a
real `y ≠ 0`, the image `f_T(y)` is real, nonzero, and on the side of `y`. -/
theorem fwdMap_real_side {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ} (hT : 0 ≤ T) {y : ℝ}
    (hy : y ≠ 0) {v : ℝ → ℂ} (hv : IsForwardSol W (y : ℂ) T v) :
    (fwdMap W T y).im = 0 ∧ ((fwdMap W T y).re < 0 ↔ y < 0) := by
  have hTI : T ∈ Icc (0 : ℝ) T := ⟨hT, le_rfl⟩
  refine ⟨GB7a.im_fwdMap_real_eq_zero hW hv hTI, ?_⟩
  rcases lt_or_gt_of_ne hy with hneg | hpos
  · refine ⟨fun _ => hneg, fun _ => ?_⟩
    obtain ⟨v', hv'⟩ := (exists_isForwardSol_neg_iff (W := W) (x := y) (T := T)).2 ⟨v, hv⟩
    have h1 := re_fwdMap_pos (W := fun s => -W s) hW.neg (by simp [hW0]) (neg_pos.2 hneg) hv' hTI
    rw [fwdMap_neg_real hW hv hTI, neg_re] at h1
    linarith
  · refine ⟨fun h => absurd h (not_lt.2 (re_fwdMap_pos hW hW0 hpos hv hTI).le), fun h => absurd h (not_lt.2 hpos.le)⟩

/-- **The image at a later time of a boundary limit off the increment hull.** If `F` eventually avoids `K_{s′}`,
`f_s ∘ F → x` with `x ≠ 0` real and `x ∉ closure K̃_{s′ − s}` (hull of `r ↦ W(s + r) − W(s)`), then `f_{s′} ∘ F`
tends to a real point on the same side of `0` as `x`. -/
theorem tendsto_fwdMap_of_alive {W : ℝ → ℝ} (hW : Continuous W) {s s' : ℝ} (hs : 0 ≤ s) (hss' : s ≤ s')
    {α : Type*} {l : Filter α} {F : α → ℂ} (hF : ∀ᶠ a in l, F a ∈ H \ fwdHull W s') {x : ℝ} (hx0 : x ≠ 0)
    (hFx : Tendsto (fun a => fwdMap W s (F a)) l (𝓝 (x : ℂ)))
    (hx : (x : ℂ) ∉ closure (fwdHull (fun r => W (s + r) - W s) (s' - s))) :
    ∃ y : ℝ, Tendsto (fun a => fwdMap W s' (F a)) l (𝓝 (y : ℂ)) ∧ (y < 0 ↔ x < 0) := by
  set W' : ℝ → ℝ := fun r => W (s + r) - W s with hW'
  have hd : 0 ≤ s' - s := sub_nonneg.2 hss'
  have hWc : Continuous W' := (hW.comp (continuous_const.add continuous_id)).sub continuous_const
  have hW'0 : W' 0 = 0 := by simp [hW']
  -- `x` is alive for the restarted driver
  obtain ⟨δ, hδ, hball⟩ : ∃ δ > 0, Disjoint (ball (x : ℂ) δ) (fwdHull W' (s' - s)) := by
    rw [Metric.mem_closure_iff] at hx
    push Not at hx
    obtain ⟨δ, hδ, hfar⟩ := hx
    exact ⟨δ, hδ, Set.disjoint_left.2 fun z hz hzK => absurd (hfar z hzK) (not_le.2 (by
      rw [mem_ball, dist_comm] at hz; exact hz))⟩
  obtain ⟨v, hv⟩ := ZhanGT4.exists_isForwardSol_of_disjoint_ball hWc hW'0 hx0 hd hδ hball
  obtain ⟨δ', hδ', hlow⟩ := exists_two_mul_le_norm_of_isForwardSol hd hv
  have hcont : ContinuousAt (fwdMap W' (s' - s)) (x : ℂ) := by
    have h1 := ZhanGT4.continuousOn_fwdMap_aliveDisc hWc hv hδ' hlow
    have h2 : ContinuousWithinAt (fun q : ℝ × ℂ => fwdMap W' q.1 q.2) (Icc 0 (s' - s) ×ˢ ball (x : ℂ)
        (ZhanGT4.aliveRad (s' - s) δ')) ((s' - s), (x : ℂ)) :=
      h1 _ ⟨⟨hd, le_rfl⟩, mem_ball_self (ZhanGT4.aliveRad_pos hδ')⟩
    have h3 : ContinuousWithinAt (fwdMap W' (s' - s)) (ball (x : ℂ) (ZhanGT4.aliveRad (s' - s) δ')) (x : ℂ) := by
      have hpair : ContinuousWithinAt (fun z : ℂ => ((s' - s), z)) (ball (x : ℂ) (ZhanGT4.aliveRad (s' - s) δ'))
          (x : ℂ) := (continuous_const.prodMk continuous_id).continuousWithinAt
      exact h2.comp hpair fun z hz => ⟨⟨hd, le_rfl⟩, hz⟩
    exact h3.continuousAt (isOpen_ball.mem_nhds (mem_ball_self (ZhanGT4.aliveRad_pos hδ')))
  obtain ⟨him, hside⟩ := fwdMap_real_side hWc hW'0 hd hx0 hv
  refine ⟨(fwdMap W' (s' - s) x).re, ?_, hside⟩
  have hreal : ((fwdMap W' (s' - s) x).re : ℂ) = fwdMap W' (s' - s) x :=
    Complex.ext (by rw [ofReal_re]) (by rw [ofReal_im, him])
  rw [hreal]
  refine (hcont.tendsto.comp hFx).congr' ?_
  filter_upwards [hF] with a ha
  have h := QuantumZipper.fwdMap_add hW ha.1 hs hd
    (Ito.exists_isForwardSol_of_mem (add_nonneg hs hd) (by rw [add_sub_cancel]; exact ha))
  rw [add_sub_cancel] at h
  exact h.symm

/-- A real point of a complex disc about a real centre is a point of the real disc. -/
theorem mem_ball_of_ofReal_mem_ball {u v ρ : ℝ} (h : (v : ℂ) ∈ ball (u : ℂ) ρ) : v ∈ ball u ρ := by
  rw [mem_ball, Complex.dist_eq, ← ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at h
  rw [mem_ball, Real.dist_eq]
  exact h

/-- **Landings near a landing in `C` lie in the hull**: for a conformal chart with continuous inverse extension `F`
and `dom = C ∩ (ℍ ∖ K)`, `C ⊆ ℍ` open, if `F u ∈ C` then every real point of a small disc about `u` lands in `K`. -/
theorem exists_ball_landing_mem_hull {ch : Chart} (hch : ch.IsConformal) {F : ℂ → ℂ} (hF : EqOn F ch.2.1 H)
    (hFc : ContinuousOn F Hbar) {C K : Set ℂ} (hCo : IsOpen C) (hCH : C ⊆ H)
    (hdom : (ch.dom : Set ℂ) = C ∩ (H \ K)) {u : ℝ} (hu : F u ∈ C) :
    ∃ ρ > 0, ∀ v : ℝ, (v : ℂ) ∈ ball (u : ℂ) ρ → F v ∈ K := by
  have hubar : (u : ℂ) ∈ Hbar := show (0 : ℝ) ≤ (u : ℂ).im by rw [ofReal_im]
  have hmem : F ⁻¹' C ∈ 𝓝[Hbar] (u : ℂ) := (hFc _ hubar).preimage_mem_nhdsWithin (hCo.mem_nhds hu)
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhdsWithin_iff.1 hmem
  refine ⟨ρ, hρ, fun v hv => ?_⟩
  have hvbar : (v : ℂ) ∈ Hbar := show (0 : ℝ) ≤ (v : ℂ).im by rw [ofReal_im]
  have hvC : F v ∈ C := hball ⟨hv, hvbar⟩
  have hland : Tendsto ch.2.1 (𝓝[H] (v : ℂ)) (𝓝 (F v)) :=
    ((hFc _ hvbar).mono QuantumZipper.H_subset_Hbar).tendsto.congr'
      (eventually_nhdsWithin_of_forall fun y hy => hF hy)
  have hnot := landing_notMem_dom hch hland
  by_contra hK
  exact hnot (by rw [hdom]; exact ⟨hvC, hCH hvC, hK⟩)

/-- **One integer along an interval of hull landings**: if every real point of `(a, b)` lands (under the current
chart `cur`, `cur.dom ⊆ ℍ ∖ K_T`) in the ambient hull `K_T`, then the current lift minus `arg f_T′` tends to one
`2πn` at every point of `(a, b)`. -/
theorem exists_int_forall_tendsto_cur {cur : Chart} (hcur : cur.IsConformal) {Lc : ℂ → ℂ}
    (hLc : IsDerivLog cur.1 Lc cur.dom) (hlift : ∀ z ∈ cur.dom, cur.2.2 z = (Lc z).im)
    {Fc : ℂ → ℂ} (hFc : EqOn Fc cur.2.1 H) (hFcc : ContinuousOn Fc Hbar)
    {W : ℝ → ℝ} {η : ℝ → ℂ} (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ} (hT : 0 ≤ T)
    (hK : (cur.dom : Set ℂ) ⊆ H \ fwdHull W T) {a b : ℝ} (hland : ∀ u ∈ Ioo a b, Fc u ∈ fwdHull W T) :
    ∃ n : ℤ, ∀ u ∈ Ioo a b, Tendsto (fun y => cur.2.2 (cur.2.1 y) - (logDerivFwd W T (cur.2.1 y)).im)
      (𝓝[H] (u : ℂ)) (𝓝 (2 * Real.pi * n)) := by
  refine exists_int_forall_tendsto_lift_sub hcur hLc hlift (isDerivLog_fwdMap hW hT) isPreconnected_Ioo
    fun u hu => ?_
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 isOpen_Ioo u hu
  exact ⟨ρ, hρ, fun y hy => hK (hcur.inv_mem_dom hy.1), exists_pos_tendsto_deriv_of_hull_landing hcur hFc hFcc
    hη hW hW0 hT hK hρ fun v hv => hland v (hball (mem_ball_of_ofReal_mem_ball hv))⟩

/-- **A reference compared with the current ambient time at one collar, from landings in the hulls.** The current chart
`cur` (`dom ⊆ ℍ ∖ K_T`) and a reference chart `old` (`dom ⊆ ℍ ∖ K_s`, containing `cur.dom`) with continuous inverse
extensions; every real point near the current coordinate `ξ` lands in `K_T` and every real point near the old coordinate
`x` lands in `K_s`, the old half-disc of radius `ε` about `x` lies in `cur.dom`; `f_s ∘ cur⁻¹ → x′ ≠ 0` at `ξ` and `f_s
∘ old⁻¹ → x′` at `x`. If a lift `A` minus `arg f_T′` tends to `d` along `cur⁻¹` at `ξ`, then `A − arg f_s′` tends to `d`
too; and if the side of `ξ` is the side of its ambient image at time `T`, it is also the side of `x′`. -/
theorem ref_lift_side_of_cur_land {cur old : Chart} (hcur : cur.IsConformal) (hold : old.IsConformal)
    {Fc Fo : ℂ → ℂ} (hFc : EqOn Fc cur.2.1 H) (hFcc : ContinuousOn Fc Hbar) (hFo : EqOn Fo old.2.1 H)
    (hFoc : ContinuousOn Fo Hbar)
    {W : ℝ → ℝ} {η : ℝ → ℂ} (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) {s T : ℝ}
    (hs : 0 ≤ s) (hT : 0 ≤ T)
    (hKT : (cur.dom : Set ℂ) ⊆ H \ fwdHull W T) (hKs : (old.dom : Set ℂ) ⊆ H \ fwdHull W s)
    (hincl : (cur.dom : Set ℂ) ⊆ old.dom) {ξ x ε x' : ℝ} (hε : 0 < ε)
    (hcol : old.2.1 '' (H ∩ ball (x : ℂ) ε) ⊆ cur.dom)
    (hlandT : ∃ ρ > 0, ∀ v : ℝ, (v : ℂ) ∈ ball (ξ : ℂ) ρ → Fc v ∈ fwdHull W T)
    (hlandS : ∃ ρ > 0, ∀ u : ℝ, (u : ℂ) ∈ ball (x : ℂ) ρ → Fo u ∈ fwdHull W s) (hx'0 : x' ≠ 0)
    (hfx : Tendsto (fun y => fwdMap W s (cur.2.1 y)) (𝓝[H] (ξ : ℂ)) (𝓝 (x' : ℂ)))
    (hfo : Tendsto (fun y => fwdMap W s (old.2.1 y)) (𝓝[H] (x : ℂ)) (𝓝 (x' : ℂ))) {A : ℂ → ℝ} {d : ℝ}
    (hn : Tendsto (fun y => A (cur.2.1 y) - (logDerivFwd W T (cur.2.1 y)).im) (𝓝[H] (ξ : ℂ)) (𝓝 d))
    (hside : ∀ y : ℝ, Tendsto (fun z => fwdMap W T (cur.2.1 z)) (𝓝[H] (ξ : ℂ)) (𝓝 (y : ℂ)) →
      (ξ < 0 ↔ y < 0)) :
    Tendsto (fun y => A (cur.2.1 y) - (logDerivFwd W s (cur.2.1 y)).im) (𝓝[H] (ξ : ℂ)) (𝓝 d) ∧
      (ξ < 0 ↔ x' < 0) := by
  have := nhdsWithin_H_neBot ξ
  have hcurK : ∀ᶠ y in 𝓝[H] (ξ : ℂ), cur.2.1 y ∈ H \ fwdHull W T :=
    eventually_nhdsWithin_of_forall fun y hy => hKT (hcur.inv_mem_dom hy)
  have hcurKs : ∀ᶠ y in 𝓝[H] (ξ : ℂ), cur.2.1 y ∈ H \ fwdHull W s :=
    eventually_nhdsWithin_of_forall fun y hy => hKs (hincl (hcur.inv_mem_dom hy))
  rcases le_total s T with hsT | hTs
  · -- the old transition covers a half-disc about `x′`, inside `f_s(ℍ ∖ K_T)`
    obtain ⟨ρ, hρ, hlandK⟩ := hlandS
    set r := min ρ ε with hr
    have hr0 : 0 < r := lt_min hρ hε
    obtain ⟨hgΦ, hgc, hgreal, hmaps, hinj, hgd, hglim⟩ := reflect_data_of_hull_landing (x := x) (ρ := r) hold
      hFo hFoc hη hW hW0 hs hKs fun u hu => hlandK u (ball_subset_ball (min_le_left _ _) hu)
    have hxbar : (x : ℂ) ∈ Hbar := show (0 : ℝ) ≤ (x : ℂ).im by rw [ofReal_im]
    have := nhdsWithin_H_neBot x
    have hgx := tendsto_nhds_unique (hglim x ⟨hxbar, mem_ball_self hr0⟩) hfo
    obtain ⟨ρ', hρ', hsub⟩ := exists_halfBall_subset_image_of_reflect hr0 hgd hgc hgreal hmaps hinj
    rw [hgx] at hsub
    have hsub' : H ∩ ball (x' : ℂ) ρ' ⊆ fwdMap W s '' (H \ fwdHull W T) := by
      intro w hw
      obtain ⟨z, hz, rfl⟩ := hsub hw
      refine ⟨old.2.1 z, hKT (hcol ⟨z, ⟨hz.1, ball_subset_ball (min_le_right _ _) hz.2⟩, rfl⟩), ?_⟩
      exact hgΦ hz
    have hxK := notMem_closure_incrHull_of_subset_image hW hs hsT hρ' hsub'
    have hcomp := tendsto_im_logDerivFwd_sub_of_notMem_closure hW hs hsT hcurK hfx hxK
    refine ⟨?_, ?_⟩
    · have h := hn.add hcomp
      rw [add_zero] at h
      exact h.congr fun y => by ring
    · obtain ⟨y, hy, hyside⟩ := tendsto_fwdMap_of_alive hW hs hsT hcurK hx'0 hfx hxK
      exact (hside y hy).trans hyside
  · -- the current transition at time `T` covers a half-disc inside `f_T(ℍ ∖ K_s)`
    obtain ⟨ρ, hρ, hlandK⟩ := hlandT
    obtain ⟨hgΦ, hgc, hgreal, hmaps, hinj, hgd, hglim⟩ := reflect_data_of_hull_landing (x := ξ) (ρ := ρ) hcur
      hFc hFcc hη hW hW0 hT hKT hlandK
    have hξbar : (ξ : ℂ) ∈ Hbar := show (0 : ℝ) ≤ (ξ : ℂ).im by rw [ofReal_im]
    set g := extendFrom H fun y => fwdMap W T (cur.2.1 y) with hg
    set y₀ : ℝ := (g ξ).re with hy₀
    have hgreal' : g ξ = (y₀ : ℂ) :=
      Complex.ext (by rw [ofReal_re]) (by rw [ofReal_im]; exact hgreal _ (mem_ball_self hρ) (ofReal_im ξ))
    have hy₀T : Tendsto (fun y => fwdMap W T (cur.2.1 y)) (𝓝[H] (ξ : ℂ)) (𝓝 (y₀ : ℂ)) := by
      rw [← hgreal']; exact hglim ξ ⟨hξbar, mem_ball_self hρ⟩
    obtain ⟨ρ', hρ', hsub⟩ := exists_halfBall_subset_image_of_reflect hρ hgd hgc hgreal hmaps hinj
    rw [hgreal'] at hsub
    have hsub' : H ∩ ball (y₀ : ℂ) ρ' ⊆ fwdMap W T '' (H \ fwdHull W s) := by
      intro w hw
      obtain ⟨z, hz, rfl⟩ := hsub hw
      exact ⟨cur.2.1 z, hKs (hincl (hcur.inv_mem_dom hz.1)), (hgΦ hz)⟩
    have hyK := notMem_closure_incrHull_of_subset_image hW hT hTs hρ' hsub'
    have hcomp := tendsto_im_logDerivFwd_sub_of_notMem_closure hW hT hTs hcurKs hy₀T hyK
    refine ⟨?_, ?_⟩
    · have h := hn.sub hcomp
      rw [sub_zero] at h
      exact h.congr fun y => by ring
    · have hy₀0 : y₀ ≠ 0 := by
        rcases hTs.lt_or_eq with hlt | heq
        · intro h0
          apply hyK
          rw [h0, ofReal_zero]
          exact ConformalImageFull.zero_mem_closure_fwdHull
            ((hW.comp (continuous_const.add continuous_id)).sub continuous_const) (by simp) (sub_pos.2 hlt)
        · subst heq
          have h1 : (y₀ : ℂ) = (x' : ℂ) := tendsto_nhds_unique hy₀T hfx
          have h2 : y₀ = x' := by exact_mod_cast h1
          exact fun h0 => hx'0 (h2 ▸ h0)
      obtain ⟨z, hz, hzside⟩ := tendsto_fwdMap_of_alive hW hT hTs hcurKs hy₀0 hy₀T hyK
      have hzx : z = x' := by exact_mod_cast tendsto_nhds_unique hz hfx
      rw [hzx] at hzside
      exact (hside y₀ hy₀T).trans hzside.symm

/-- **A reference compared with the current ambient time at one collar.** The current chart `cur`
(`dom = C ∩ (ℍ ∖ K_T)`) and a reference chart `old` (`dom = C ∩ (ℍ ∖ K_s)`, containing `cur.dom`) with continuous
inverse extensions; `ξ` a current coordinate landing in `C`, `x` an old coordinate landing in `C` whose old
half-disc of radius `ε` lies in `cur.dom`; `f_s ∘ cur⁻¹ → x′ ≠ 0` at `ξ` and `f_s ∘ old⁻¹ → x′` at `x`. If a lift `A`
minus `arg f_T′` tends to `d` along `cur⁻¹` at `ξ`, then `A − arg f_s′` tends to `d` too; and if the side of `ξ` is
the side of its ambient image at time `T`, it is also the side of `x′`. -/
theorem ref_lift_side_of_cur {cur old : Chart} (hcur : cur.IsConformal) (hold : old.IsConformal)
    {Fc Fo : ℂ → ℂ} (hFc : EqOn Fc cur.2.1 H) (hFcc : ContinuousOn Fc Hbar) (hFo : EqOn Fo old.2.1 H)
    (hFoc : ContinuousOn Fo Hbar) {C : Set ℂ} (hCo : IsOpen C) (hCH : C ⊆ H)
    {W : ℝ → ℝ} {η : ℝ → ℂ} (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) {s T : ℝ}
    (hs : 0 ≤ s) (hT : 0 ≤ T)
    (hcurdom : (cur.dom : Set ℂ) = C ∩ (H \ fwdHull W T)) (holddom : (old.dom : Set ℂ) = C ∩ (H \ fwdHull W s))
    (hincl : (cur.dom : Set ℂ) ⊆ old.dom) {ξ x ε x' : ℝ} (hε : 0 < ε)
    (hcol : old.2.1 '' (H ∩ ball (x : ℂ) ε) ⊆ cur.dom) (hξC : Fc ξ ∈ C) (hxC : Fo x ∈ C) (hx'0 : x' ≠ 0)
    (hfx : Tendsto (fun y => fwdMap W s (cur.2.1 y)) (𝓝[H] (ξ : ℂ)) (𝓝 (x' : ℂ)))
    (hfo : Tendsto (fun y => fwdMap W s (old.2.1 y)) (𝓝[H] (x : ℂ)) (𝓝 (x' : ℂ))) {A : ℂ → ℝ} {d : ℝ}
    (hn : Tendsto (fun y => A (cur.2.1 y) - (logDerivFwd W T (cur.2.1 y)).im) (𝓝[H] (ξ : ℂ)) (𝓝 d))
    (hside : ∀ y : ℝ, Tendsto (fun z => fwdMap W T (cur.2.1 z)) (𝓝[H] (ξ : ℂ)) (𝓝 (y : ℂ)) →
      (ξ < 0 ↔ y < 0)) :
    Tendsto (fun y => A (cur.2.1 y) - (logDerivFwd W s (cur.2.1 y)).im) (𝓝[H] (ξ : ℂ)) (𝓝 d) ∧
      (ξ < 0 ↔ x' < 0) :=
  ref_lift_side_of_cur_land hcur hold hFc hFcc hFo hFoc hη hW hW0 hs hT
    (by rw [hcurdom]; exact inter_subset_right) (by rw [holddom]; exact inter_subset_right) hincl hε hcol
    (exists_ball_landing_mem_hull hcur hFc hFcc hCo hCH hcurdom hξC)
    (exists_ball_landing_mem_hull hold hFo hFoc hCo hCH holddom hxC) hx'0 hfx hfo hn hside

end InteractingSLE.Sec7.R5Lift
