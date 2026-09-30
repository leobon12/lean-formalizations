import QuantumZipper.Proofs.Zipper.FieldLawlerCoverHarmA
import QuantumZipper.Proofs.Zipper.FieldLawlerSubSum
import QuantumZipper.Proofs.Thm18.LWFarPocketFar
import QuantumZipper.Proofs.Thm18.LWExc3Circle

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# FL-THM-COVER: harmonic measure of a crosscut in the unbounded component `H_η`

`flHullHarmExists_holds : FLHullHarmExistsStmt`.

**Source.** J. B. Garnett, D. E. Marshall, *Harmonic Measure*, Ch. I §1, p. 5, eq. (1.6)
(harmonic measure is conformally invariant, and in a Jordan-type domain with locally connected
boundary it is obtained by pulling back the half-plane harmonic measure through a Riemann map with
Carathéodory boundary extension, Pommerenke, *Boundary Behaviour of Conformal Maps*,
Thm 2.1). The repository has this as `lwHarm_exists_car` for bounded domains with ULC frontier
(`Thm18/LWHarmCar.lean`). We apply it to `D' = M(H_η)`, `M z = 1/(z + i)`, a bounded
domain with frontier inside the ULC compact `M(η̄) ∪ {|w + i/2| = 1/2}`; the Riemann map exists
since `H_η` is connected and all components of its complement are unbounded
(`FieldLawlerCoverHarmA.lean`, RMT: `RMT.riemann_mapping_of_hasHoloSqrt`,
`RMT.hasHoloSqrt_of_unbounded_compl`). The harmonic measure in `D'` is pulled back by `M`
(harmonic by `pocket_harmonicAt_comp`, boundary values by continuity of `M`, `M⁻¹`; the
condition at `∞` becomes the boundary value at `M(∞) = 0`). The Möbius transport is our own
routine step.
-/

noncomputable section

open Filter Set Metric Complex
open scoped Topology

namespace QuantumZipper
namespace FieldLawler

open Thm18Asm.LWFar QuantumZipper.CA

lemma flMob_continuousAt {z : ℂ} (hz : 0 ≤ z.im) : ContinuousAt flMob z :=
  (continuousAt_id.add continuousAt_const).inv₀ (add_I_ne_zero_of_im_nonneg hz)

lemma flMobInv_continuousAt {w : ℂ} (hw : w ≠ 0) : ContinuousAt flMobInv w :=
  (continuousAt_inv₀ hw).sub continuousAt_const

lemma flMob_analyticAt {z : ℂ} (hz : 0 ≤ z.im) : AnalyticAt ℂ flMob z :=
  (analyticAt_id.add analyticAt_const).inv (add_I_ne_zero_of_im_nonneg hz)

lemma flMob_tendsto_cobounded : Tendsto flMob (Bornology.cobounded ℂ) (𝓝 0) :=
  tendsto_inv₀_cobounded.comp (tendsto_add_const_cobounded I)

lemma flH_lwArcExt_im {η : ℝ → ℂ} {a b : ℝ} (hη : IsCrosscutH η) (t : ℝ) :
    0 ≤ (lwArcExt η a b t).im := by
  unfold lwArcExt
  split_ifs with h0 h1
  · simp
  · simp
  · exact (hη.2.2.1 ⟨not_le.1 h0, not_le.1 h1⟩ : (0 : ℝ) < _).le

lemma flH_closure_H_im {z : ℂ} (hz : z ∈ closure H) : 0 ≤ z.im := by
  have hs : H ⊆ {w : ℂ | 0 ≤ w.im} := fun w (hw : 0 < w.im) => hw.le
  exact closure_minimal hs (isClosed_le continuous_const continuous_im) hz

/-- **Harmonic measure of a crosscut in `H_η` exists.** -/
theorem flHullHarmExists_holds : FLHullHarmExistsStmt := by
  intro η hη
  obtain ⟨a, ha⟩ := hη.2.2.2.1
  obtain ⟨b, hb⟩ := hη.2.2.2.2
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
  set A' := flMob '' arcH η with hA'def
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
    obtain ⟨M₀, hM₀⟩ := (lwExc_arc_isBounded hη).exists_norm_le
    refine ⟨(|M₀| + 1)⁻¹, by positivity, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    have h1 : ‖z + I‖ ≤ |M₀| + 1 := by
      have := norm_add_le z I
      rw [Complex.norm_I] at this
      linarith [hM₀ z hz, le_abs_self M₀]
    have hne : z + I ≠ 0 := add_I_ne_zero_of_im_nonneg (hη.2.2.1.mono_left le_rfl |> fun _ => by
      obtain ⟨s, hs, rfl⟩ := hz; exact (hη.2.2.1 hs : (0 : ℝ) < _).le)
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
    obtain ⟨s, hs, rfl⟩ := hz
    rw [mem_closedBall, dist_zero_right]; exact flMob_norm_le (hη.2.2.1 hs : (0 : ℝ) < _).le
  have hAD : Disjoint A' D' := by
    rw [Set.disjoint_left]
    rintro _ ⟨z, hz, rfl⟩ hD
    have := ((hD'mem _).1 hD).2
    rw [flMobInv_flMob] at this
    exact this.1.2 hz
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
    have hx₀H : 0 < x₀.im := by obtain ⟨s, hs, rfl⟩ := hx₀; exact hη.2.2.1 hs
    have hne : flMob x₀ ≠ 0 := flMob_ne_zero hx₀H.le
    have key : flMob x₀ ∉ closure (frontier D' \ A') := by
      intro hc
      have h1 := mem_closure_image (flMobInv_continuousAt hne) hc
      rw [flMobInv_flMob] at h1
      have hsub : flMobInv '' (frontier D' \ A') ⊆ (frontier U \ arcH η) ∪ {flMobInv 0} := by
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
    exact (hHM.one _ ⟨x₀, hx₀, rfl⟩ key).comp (hTw x₀ hx₀H.le)
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

end FieldLawler
end QuantumZipper
