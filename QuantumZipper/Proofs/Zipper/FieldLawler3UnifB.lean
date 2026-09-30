import QuantumZipper.Proofs.Zipper.FieldLawler3UnifA

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# FL3-UNIF (B): the uniformizing map `ℍ̄ → closure H_η` with `∞ ↦ ∞`

For a crosscut `η` of `ℍ` with feet `a ≠ b`, `fl3u_unif_exists` gives `Φ : ℂ → ℂ` which is
holomorphic on `ℍ`, maps `ℍ` bijectively onto `H_η = hullComp η`, is continuous on `ℍ̄`, maps
`ℝ` bijectively onto `frontier H_η`, and tends to `∞` at `∞` in `ℍ̄`.

**Source.** Carathéodory's theorem in the Jordan case (Pommerenke, *Boundary Behaviour of
Conformal Maps*, 1992, Thm 2.1 and Thm 2.6, pp. 20–24; repo `CA.Car.continuousOn_extension`,
`CA.Car.isClosedEmbedding_bdryMap`), applied to the bounded model `M(H_η)`, `M z = 1/(z + i)`
(`FieldLawler3UnifA.lean`), after the normalization `M(∞) = 0 ↦ ∞`
(`lwHarm_car_normalize`). The frontier of `M(H_η)` lies in a theta graph `E` whose punctures are
connected, which is all that `isClosedEmbedding_bdryMap` needs. The transport back by `M⁻¹` is
routine.
-/

noncomputable section

open Filter Set Metric Complex
open scoped Topology

namespace QuantumZipper
namespace FieldLawler

open Thm18Asm.LWFar QuantumZipper.CA

/-- The Carathéodory extension tends to the limit `wInf` at `∞` along all of `ℍ̄` (as
`Car.tendsto_extension_cocompact` along `ℝ`). -/
theorem fl3u_tendsto_ext_Hbar {ψ F : ℂ → ℂ} (hEq : EqOn F ψ H) (hF : ContinuousOn F Hbar)
    {wInf : ℂ} (hInf : Tendsto ψ (Bornology.cobounded ℂ ⊓ 𝓟 H) (𝓝 wInf)) :
    Tendsto F (Bornology.cobounded ℂ ⊓ 𝓟 Hbar) (𝓝 wInf) := by
  refine (nhds_basis_closedBall.tendsto_right_iff).2 fun ε hε => ?_
  have hmem := hInf (closedBall_mem_nhds wInf hε)
  rw [mem_map, mem_inf_principal] at hmem
  set S : Set ℂ := {z | z ∈ H → z ∈ ψ ⁻¹' closedBall wInf ε} with hS
  have hSb : Bornology.IsBounded Sᶜ := Bornology.isBounded_def.2 (by rwa [compl_compl])
  obtain ⟨R, hR⟩ := hSb.subset_closedBall 0
  rw [eventually_inf_principal]
  filter_upwards [Bornology.isBounded_def.1 (isBounded_closedBall (x := (0 : ℂ)) (r := R))]
    with z hz hzH
  have hzR : R < ‖z‖ := by simpa [mem_closedBall, dist_zero_right] using hz
  have hcl := Car.mem_closure_image_of_mem_nhdsWithin hEq hF hzH
    (inter_mem_nhdsWithin H ((isOpen_lt continuous_const continuous_norm).mem_nhds
      (show z ∈ {z : ℂ | R < ‖z‖} from hzR)))
  refine closure_minimal ?_ isClosed_closedBall hcl
  rintro _ ⟨w, ⟨hwH, hwR⟩, rfl⟩
  have hwS : w ∈ S := by
    by_contra hwS
    have := hR hwS
    rw [mem_closedBall, dist_zero_right] at this
    exact not_le.2 hwR this
  exact hwS hwH

/-- **Uniformization of `H_η` with continuous boundary values.** For a crosscut `η` of `ℍ` with
feet `a ≠ b` there is `Φ`, holomorphic on `ℍ`, mapping `ℍ` bijectively onto `hullComp η`,
continuous on `ℍ̄`, mapping `ℝ` bijectively onto `frontier (hullComp η)`, with `Φ → ∞` at `∞`. -/
theorem fl3u_unif_exists {η : ℝ → ℂ} (hη : IsCrosscutH η) {a b : ℝ}
    (ha : Tendsto η (𝓝[>] 0) (𝓝 (a : ℂ))) (hb : Tendsto η (𝓝[<] 1) (𝓝 (b : ℂ)))
    (hab : a ≠ b) :
    ∃ Φ : ℂ → ℂ, DifferentiableOn ℂ Φ H ∧ BijOn Φ H (hullComp η) ∧ ContinuousOn Φ Hbar ∧
      Function.Injective (fun x : ℝ => Φ x) ∧
      range (fun x : ℝ => Φ x) = frontier (hullComp η) ∧
      Tendsto Φ (Bornology.cobounded ℂ ⊓ 𝓟 Hbar) (Bornology.cobounded ℂ) := by
  set U := hullComp η with hUdef
  have hUo : IsOpen U := lwExc_hullComp_isOpen hη
  have hUH : U ⊆ H := lwExc_hullComp_subset_H η
  have hUunb : ¬ Bornology.IsBounded U := by
    obtain ⟨p₀, hp₀U, hUeq⟩ := flH_hullComp_eq hη
    have := hp₀U.2; rwa [← hUeq] at this
  set D' := flMob '' U with hD'
  obtain ⟨G, hG⟩ := fl3u_carHyp hη ha hb
  obtain ⟨ψ₁, F₁, h1, hEq, hF, hInf⟩ :=
    lwHarm_car_normalize hG (fl3u_E_ulc hη ha hb) (fl3u_zero_frD hUo hUH hUunb)
  obtain ⟨hemb, hrange⟩ := Car.isClosedEmbedding_bdryMap h1 hEq hF hInf
    (fl3u_E_diff_preconnected hη ha hb hab)
  have hFD : ∀ z ∈ H, F₁ z ∈ D' := fun z hz => by rw [hEq hz]; exact h1.bij.mapsTo hz
  have hFfr : ∀ x : ℝ, F₁ x ∈ frontier D' := fun x => by
    rw [← hrange]; exact ⟨(x : OnePoint ℝ), rfl⟩
  have hF0 : ∀ x : ℝ, F₁ x ≠ 0 := fun x h =>
    OnePoint.coe_ne_infty x (hemb.injective
      (show Car.bdryMap F₁ 0 (x : OnePoint ℝ) = Car.bdryMap F₁ 0 OnePoint.infty from h))
  have hFinj : Function.Injective (fun x : ℝ => F₁ x) := fun x y h =>
    OnePoint.coe_injective (hemb.injective
      (show Car.bdryMap F₁ 0 (x : OnePoint ℝ) = Car.bdryMap F₁ 0 (y : OnePoint ℝ) from h))
  have hFne : ∀ z ∈ Hbar, F₁ z ≠ 0 := by
    intro z hz
    rcases (show (0 : ℝ) ≤ z.im from hz).lt_or_eq with hpos | hzero
    · exact ((fl3u_memD hUH _).1 (hFD z hpos)).1
    · have hzr : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [← hzero])
      rw [hzr]; exact hF0 _
  refine ⟨fun z => flMobInv (F₁ z), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have : DifferentiableOn ℂ (fun z => flMobInv (ψ₁ z)) H := by
      intro z hz
      have hne : ψ₁ z ≠ 0 := by rw [← hEq hz]; exact hFne z (H_subset_Hbar hz)
      exact ((differentiableAt_inv hne).sub_const I).comp_differentiableWithinAt z (h1.holo z hz)
    exact this.congr fun z hz => by simp only [hEq hz]
  · have hinv : BijOn flMobInv D' U := by
      refine InvOn.bijOn (f' := flMob) ⟨fun w _ => flMob_flMobInv, fun z _ => flMobInv_flMob⟩
        (fun w hw => ((fl3u_memD hUH w).1 hw).2) (fun z hz => ⟨z, hz, rfl⟩)
    exact (hinv.comp h1.bij).congr fun z hz => by simp only [Function.comp_apply, hEq hz]
  · intro z hz
    exact (flMobInv_continuousAt (hFne z hz)).comp_continuousWithinAt (hF z hz)
  · intro x y h
    apply hFinj
    have := congrArg flMob h
    simpa only [flMob_flMobInv] using this
  · ext z
    constructor
    · rintro ⟨x, rfl⟩
      exact fl3u_frD_inv hUo hUH (hFfr x) (hF0 x)
    · intro hz
      have hw := fl3u_fr_mob hUo hUH hz
      rw [← hrange] at hw
      obtain ⟨o, ho⟩ := hw
      induction o using OnePoint.rec with
      | infty => exact absurd (ho : (0 : ℂ) = flMob z).symm (flMob_ne_zero (fl3u_frontier_im hUH hz))
      | coe x =>
        refine ⟨x, ?_⟩
        have ho' : F₁ x = flMob z := ho
        simp only [ho', flMobInv_flMob]
  · have h0 := fl3u_tendsto_ext_Hbar hEq hF hInf
    have h0' : Tendsto F₁ (Bornology.cobounded ℂ ⊓ 𝓟 Hbar) (𝓝[≠] 0) :=
      tendsto_nhdsWithin_iff.2 ⟨h0, eventually_inf_principal.2
        (Eventually.of_forall fun z hz => hFne z hz)⟩
    exact (tendsto_sub_const_cobounded I).comp (tendsto_inv₀_nhdsNE_zero.comp h0')

end FieldLawler
end QuantumZipper
