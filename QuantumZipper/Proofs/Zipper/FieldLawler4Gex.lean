import QuantumZipper.Proofs.Zipper.FieldLawlerCoverHarm

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# FL4-GEX: harmonic measure of a bounded real interval in `H_η`

`fl4_gex`: for a crosscut `η` of `ℍ`, the harmonic measure of a bounded real interval
`(c, d)` in `hullComp η` exists. More generally `fl4Gex_of_bdd` does this for any bounded
set `A` in the closed upper half-plane disjoint from `hullComp η`.

**Source.** Same as `flHullHarmExists_holds` (`FieldLawlerCoverHarm.lean`): Garnett–Marshall,
*Harmonic Measure*, Ch. I §1, p. 5, eq. (1.6) (conformal invariance of harmonic measure)
with Pommerenke, *Boundary Behaviour of Conformal Maps*, Thm 2.1 (Carathéodory extension),
through `lwHarm_exists_car` applied in `M(H_η)`, `M z = 1/(z + i)`. The proof is the proof of
`flHullHarmExists_holds` with the arc replaced by the set `A`; the Möbius transport is our own
routine step.
-/

noncomputable section

open Filter Set Metric Complex
open scoped Topology

namespace QuantumZipper
namespace FieldLawler

open Thm18Asm.LWFar QuantumZipper.CA

/-- Harmonic measure in `H_η` of a bounded set `A ⊆ {Im ≥ 0}` disjoint from `H_η`. -/
theorem fl4Gex_of_bdd {η : ℝ → ℂ} (hη : IsCrosscutH η) {a b : ℝ}
    (ha : Tendsto η (𝓝[>] 0) (𝓝 (a : ℂ))) (hb : Tendsto η (𝓝[<] 1) (𝓝 (b : ℂ)))
    {A : Set ℂ} (hAbdd : Bornology.IsBounded A) (hAim : ∀ z ∈ A, 0 ≤ z.im)
    (hAU : Disjoint A (hullComp η)) :
    ∃ G : ℂ → ℝ, IsHarmMeas (hullComp η) A G := by
  set U := hullComp η with hUdef
  have hUo : IsOpen U := lwExc_hullComp_isOpen hη
  have hUH : U ⊆ H := lwExc_hullComp_subset_H η
  have hUim : ∀ z ∈ U, 0 ≤ z.im := fun z hz => (hUH hz : (0 : ℝ) < z.im).le
  obtain ⟨p₀, hp₀U, hUeq⟩ := flH_hullComp_eq hη
  have hUc : IsPreconnected U := by rw [hUdef, hUeq]; exact isPreconnected_connectedComponentIn
  have hUunb : ¬ Bornology.IsBounded U := by
    have := hp₀U.2; rwa [← hUeq] at this
  have hUuniv : U ≠ univ := fun h => by
    have := hUH (h ▸ mem_univ (0 : ℂ)); simp [H] at this
  obtain ⟨φ₀, -, -, ψ₀, hψb, hψd, -⟩ := RMT.riemann_mapping_of_hasHoloSqrt hUo hUc ⟨p₀, hp₀U⟩
    hUuniv (RMT.hasHoloSqrt_of_unbounded_compl hUo hUc (flH_compl_unbounded hη ha hb))
  set D' := flMob '' U with hD'def
  set A' := flMob '' A with hA'def
  have hD'mem : ∀ w, w ∈ D' ↔ w ≠ 0 ∧ flMobInv w ∈ U := by
    intro w
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨flMob_ne_zero (hUim z hz), by rw [flMobInv_flMob]; exact hz⟩
    · rintro ⟨-, h⟩
      exact ⟨_, h, flMob_flMobInv⟩
  have hD'o : IsOpen D' := by
    have : D' = {w : ℂ | w ≠ 0} ∩ flMobInv ⁻¹' U := by
      ext w; rw [hD'mem]; rfl
    rw [this]
    refine ContinuousOn.isOpen_inter_preimage (fun w hw => ?_) isOpen_ne hUo
    exact (flMobInv_continuousAt hw).continuousWithinAt
  -- boundary set
  set γ : ℝ → ℂ := flMob ∘ lwArcExt η a b with hγ
  have hγc : ContinuousOn γ (Icc 0 1) := by
    refine ContinuousOn.comp (t := {z : ℂ | 0 ≤ z.im}) (fun z hz => ?_)
      (lwArcExt_contOn hη ha hb) (fun t _ => flH_lwArcExt_im hη t)
    exact (flMob_continuousAt hz).continuousWithinAt
  set E := γ '' Icc 0 1 ∪ sphere (-I / 2) (1 / 2) with hEdef
  have hγK : IsCompact (γ '' Icc 0 1) := isCompact_Icc.image_of_continuousOn hγc
  have hEc : IsClosed E := hγK.isClosed.union isClosed_sphere
  have hEulc : Topo.ULC E :=
    Topo.ULC.union_of_isCompact_of_isClosed hγK isClosed_sphere (Topo.ULC.image_Icc hγc)
      (Topo.ULC.sphere _ _)
  -- frontier transport
  have hfrD' : ∀ w ∈ frontier D', w ≠ 0 → flMobInv w ∈ frontier U := by
    intro w hw hw0
    rw [hD'o.frontier_eq] at hw
    rw [hUo.frontier_eq]
    refine ⟨closure_mono ?_ (mem_closure_image (flMobInv_continuousAt hw0) hw.1), fun hU => ?_⟩
    · rintro _ ⟨v, hv, rfl⟩; exact ((hD'mem v).1 hv).2
    · exact hw.2 ((hD'mem w).2 ⟨hw0, hU⟩)
  have hfrU : ∀ z ∈ frontier U, flMob z ∈ frontier D' := by
    intro z hz
    rw [hUo.frontier_eq] at hz
    have hzim : 0 ≤ z.im := flH_closure_H_im (closure_mono hUH hz.1)
    rw [hD'o.frontier_eq]
    refine ⟨mem_closure_image (flMob_continuousAt hzim) hz.1, fun hD => ?_⟩
    have := ((hD'mem _).1 hD).2
    rw [flMobInv_flMob] at this
    exact hz.2 this
  have hEsub : frontier D' ⊆ E := by
    intro w hw
    by_cases hw0 : w = 0
    · right; rw [hw0, mem_sphere, dist_eq_norm]; simp
    · have hz := hfrD' w hw hw0
      set z := flMobInv w
      have hwz : w = flMob z := flMob_flMobInv.symm
      rw [hUo.frontier_eq] at hz
      have hzim : 0 ≤ z.im := flH_closure_H_im (closure_mono hUH hz.1)
      rcases hzim.lt_or_eq with hpos | hzero
      · -- `z ∈ ℍ \ U` in the closure of `U`: on the arc
        have harc : z ∈ arcH η := by
          by_contra hna
          exact hz.2 (lw3_mem_hull_of_closure hη ⟨hpos, hna⟩ hz.1)
        obtain ⟨s, hs, hzs⟩ := harc
        left
        refine ⟨s, Ioo_subset_Icc_self hs, ?_⟩
        simp only [hγ, Function.comp_apply, (lwArcExt_mem (a := a) (b := b) hη hs).1, hzs, hwz]
      · right
        have hzr : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [← hzero])
        rw [hwz, hzr]
        exact flMob_real_mem_sphere _
  have hEcompl : E ⊆ D'ᶜ := by
    rintro w (⟨t, ht, rfl⟩ | hw) hD
    · have h2 := ((hD'mem _).1 hD).2
      simp only [hγ, Function.comp_apply, flMobInv_flMob] at h2
      have hS := h2.1
      unfold lwArcExt at hS
      split_ifs at hS with h0 h1
      · exact (show ¬ (0 : ℝ) < ((a : ℂ)).im by simp) hS.1
      · exact (show ¬ (0 : ℝ) < ((b : ℂ)).im by simp) hS.1
      · exact hS.2 ⟨t, ⟨not_le.1 h0, not_le.1 h1⟩, rfl⟩
    · obtain ⟨hw0, hwU⟩ := (hD'mem w).1 hD
      have := hUH hwU
      simp only [H, mem_setOf_eq, flMobInv_im_of_sphere hw hw0] at this
      exact lt_irrefl _ this
  have hEbdd : E ⊆ closedBall 0 1 := by
    rintro w (⟨t, -, rfl⟩ | hw)
    · rw [mem_closedBall, dist_zero_right]; exact flMob_norm_le (flH_lwArcExt_im hη t)
    · rw [mem_sphere, dist_eq_norm] at hw
      rw [mem_closedBall, dist_zero_right]
      have := norm_add_le (w - -I / 2) (-I / 2)
      rw [sub_add_cancel] at this
      have hI : ‖-I / 2‖ = 1 / 2 := by simp
      linarith
  have hCar : Car.CarHyp (flMob ∘ ψ₀ ∘ cayley) D' E 1 := by
    have hd1 : DifferentiableOn ℂ (ψ₀ ∘ cayley) H :=
      hψd.comp (differentiableOn_cayley_Hbar.mono H_subset_Hbar) bijOn_cayley_H.mapsTo
    have hb1 : BijOn (ψ₀ ∘ cayley) H U := hψb.comp bijOn_cayley_H
    have hinj : InjOn flMob U := fun z _ w _ he => by
      have := congrArg flMobInv he; rwa [flMobInv_flMob, flMobInv_flMob] at this
    refine ⟨?_, (hinj.bijOn_image).comp hb1, hD'o, ?_, hEc, hEsub, hEcompl, hEbdd⟩
    · refine DifferentiableOn.comp (t := U) (fun z hz => ?_) hd1 hb1.mapsTo
      exact (flMob_analyticAt (hUim z hz)).differentiableAt.differentiableWithinAt
    · rintro _ ⟨z, hz, rfl⟩
      rw [mem_ball, dist_zero_right]; exact flMob_norm_lt (hUH hz)
  -- the point `0 = M(∞)`
  have hA'far : ∃ r : ℝ, 0 < r ∧ ∀ w ∈ A', r ≤ ‖w‖ := by
    obtain ⟨M₀, hM₀⟩ := hAbdd.exists_norm_le
    refine ⟨(|M₀| + 1)⁻¹, by positivity, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    have h1 : ‖z + I‖ ≤ |M₀| + 1 := by
      have := norm_add_le z I
      rw [Complex.norm_I] at this
      linarith [hM₀ z hz, le_abs_self M₀]
    have hne : z + I ≠ 0 := add_I_ne_zero_of_im_nonneg (hAim z hz)
    rw [flMob, norm_inv]
    exact inv_anti₀ (norm_pos_iff.2 hne) h1
  obtain ⟨r₀, hr₀, hr₀A⟩ := hA'far
  have h0cl : (0 : ℂ) ∉ closure A' := by
    intro h
    have hsub : closure A' ⊆ {w : ℂ | r₀ ≤ ‖w‖} :=
      closure_minimal hr₀A (isClosed_le continuous_const continuous_norm)
    have := hsub h
    simp only [mem_setOf_eq, norm_zero] at this
    linarith
  have hneb : (Bornology.cobounded ℂ ⊓ 𝓟 U).NeBot := by
    rw [inf_principal_neBot_iff]
    intro V hV
    by_contra hVU
    rw [not_nonempty_iff_eq_empty] at hVU
    have hVb : Bornology.IsBounded Vᶜ := Bornology.isBounded_compl_iff.2 hV
    exact hUunb (hVb.subset fun z hz hzV => (hVU ▸ ⟨hzV, hz⟩ : z ∈ (∅ : Set ℂ)))
  have hTinf : Tendsto flMob (Bornology.cobounded ℂ ⊓ 𝓟 U) (𝓝[D'] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨flMob_tendsto_cobounded.mono_left inf_le_left,
      eventually_inf_principal.2 (Eventually.of_forall fun z hz => ⟨z, hz, rfl⟩)⟩
  have h0fr : (0 : ℂ) ∈ frontier D' := by
    rw [hD'o.frontier_eq]
    refine ⟨mem_closure_of_tendsto (flMob_tendsto_cobounded.mono_left inf_le_left)
      (eventually_inf_principal.2 (Eventually.of_forall fun z hz => ⟨z, hz, rfl⟩)), fun h => ?_⟩
    exact ((hD'mem 0).1 h).1 rfl
  have hAb : Bornology.IsBounded A' := by
    refine (isBounded_closedBall (x := (0 : ℂ)) (r := 1)).subset ?_
    rintro _ ⟨z, hz, rfl⟩
    rw [mem_closedBall, dist_zero_right]; exact flMob_norm_le (hAim z hz)
  have hAD : Disjoint A' D' := by
    rw [Set.disjoint_left]
    rintro _ ⟨z, hz, rfl⟩ hD
    have := ((hD'mem _).1 hD).2
    rw [flMobInv_flMob] at this
    exact Set.disjoint_left.1 hAU hz this
  obtain ⟨hm', hHM⟩ := lwHarm_exists_car hCar hEulc hAb hAD ⟨0, h0fr, h0cl⟩
  -- pull back
  have hTw : ∀ z₀ : ℂ, 0 ≤ z₀.im → Tendsto flMob (𝓝[U] z₀) (𝓝[D'] (flMob z₀)) := fun z₀ hz₀ =>
    tendsto_nhdsWithin_iff.2 ⟨(flMob_continuousAt hz₀).tendsto.mono_left nhdsWithin_le_nhds,
      eventually_nhdsWithin_of_forall fun z hz => ⟨z, hz, rfl⟩⟩
  refine ⟨hm' ∘ flMob, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    exact pocket_harmonicAt_comp (flMob_analyticAt (hUim z hz)) (hHM.harm _ ⟨z, hz, rfl⟩)
  · intro z hz
    exact hHM.mem01 _ ⟨z, hz, rfl⟩
  · intro x₀ hx₀ hx₀cl
    have hx₀H : 0 ≤ x₀.im := hAim x₀ hx₀
    have hne : flMob x₀ ≠ 0 := flMob_ne_zero hx₀H
    have key : flMob x₀ ∉ closure (frontier D' \ A') := by
      intro hc
      have h1 := mem_closure_image (flMobInv_continuousAt hne) hc
      rw [flMobInv_flMob] at h1
      have hsub : flMobInv '' (frontier D' \ A') ⊆ (frontier U \ A) ∪ {flMobInv 0} := by
        rintro _ ⟨w, ⟨hwfr, hwA⟩, rfl⟩
        by_cases hw0 : w = 0
        · right; rw [hw0]; rfl
        · left
          refine ⟨hfrD' w hwfr hw0, fun harc => hwA ⟨_, harc, flMob_flMobInv⟩⟩
      have h2 := closure_mono hsub h1
      rw [closure_union, closure_singleton] at h2
      rcases h2 with h2 | h2
      · exact hx₀cl h2
      · have : x₀.im = (flMobInv 0).im := by rw [h2]
        simp [flMobInv] at this
        linarith
    exact (hHM.one _ ⟨x₀, hx₀, rfl⟩ key).comp (hTw x₀ hx₀H)
  · intro x₀ hx₀ hx₀cl
    have hx₀im : 0 ≤ x₀.im := by
      rw [hUo.frontier_eq] at hx₀; exact flH_closure_H_im (closure_mono hUH hx₀.1)
    have hncl : flMob x₀ ∉ closure A' := by
      intro hc
      have h1 := mem_closure_image (flMobInv_continuousAt (flMob_ne_zero hx₀im)) hc
      rw [flMobInv_flMob] at h1
      refine hx₀cl (closure_mono ?_ h1)
      rintro _ ⟨w, ⟨z, hz, rfl⟩, rfl⟩
      rw [flMobInv_flMob]; exact hz
    exact (hHM.zero _ (hfrU x₀ hx₀) hncl).comp (hTw x₀ hx₀im)
  · intro _
    exact (hHM.zero 0 h0fr h0cl).comp hTinf

/-- **FL4-GEX.** The harmonic measure of a bounded real interval `(c, d)` in `H_η` exists
(the hypotheses `hcd`, `hdisj` of the intended applications are not needed). -/
theorem fl4_gex {η : ℝ → ℂ} (hη : IsCrosscutH η) {a b : ℝ}
    (ha : Tendsto η (𝓝[>] 0) (𝓝 (a : ℂ))) (hb : Tendsto η (𝓝[<] 1) (𝓝 (b : ℂ)))
    {c d : ℝ} (_hcd : c < d) (_hdisj : d ≤ min a b ∨ max a b ≤ c) :
    ∃ G : ℂ → ℝ, IsHarmMeas (hullComp η) (((↑) : ℝ → ℂ) '' Ioo c d) G := by
  refine fl4Gex_of_bdd hη ha hb ?_ ?_ ?_
  · refine (isBounded_closedBall (x := (0 : ℂ)) (r := |c| + |d|)).subset ?_
    rintro _ ⟨x, hx, rfl⟩
    rw [mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs]
    rcases le_total 0 x with h | h
    · rw [abs_of_nonneg h]; linarith [hx.2, le_abs_self d, abs_nonneg c]
    · rw [abs_of_nonpos h]; linarith [hx.1, neg_abs_le c, abs_nonneg d]
  · rintro _ ⟨x, -, rfl⟩; simp
  · rw [Set.disjoint_left]
    rintro _ ⟨x, -, rfl⟩ hx
    have := lwExc_hullComp_subset_H η hx
    simp [H] at this

end FieldLawler
end QuantumZipper
