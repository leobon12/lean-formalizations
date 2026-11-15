/- Provenance (PROVE-GEO-JORDAN, ruling R21): ported, through an intermediate copy, from an earlier mating-of-trees
formalization; only the module and namespace prefixes were changed (now `InteractingSLE.Foundations.Topology` and
`InteractingSLE.Foundations`), and declaration names are unchanged. -/
import InteractingSLE.Foundations.Topology.Schoenflies.Radial
import InteractingSLE.Foundations.Topology.Schoenflies.Exterior
import LQGMetric.Papers.GM.S4.P412cLC

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! # The Schoenflies theorem in the plane

**Schoenflies theorem.** For every Jordan curve `Γ ⊆ ℂ` there is a homeomorphism `h : ℂ ≃ₜ ℂ`
with `h '' ∂𝔻 = Γ`; it maps `𝔻` onto the bounded and `{|z| > 1}` onto the unbounded component
of `Γᶜ` (`schoenflies_plane`, `schoenflies_plane'`).

Proof: the standard derivation from Carathéodory's theorem (Pommerenke, *Boundary Behaviour of
Conformal Maps*, 1992, Thm 2.6 and §2.1; e.g. also C. Thomassen, *The Jordan–Schönflies theorem
and the classification of surfaces*, Amer. Math. Monthly 99 (1992)): glue the interior map
`f : cl 𝔻 → cl U` (`schoenflies_disc`) and the exterior map `E : {|z| ≥ 1} → cl V`
(`schoenflies_exterior`) after correcting `f` on the circle by the circle homeomorphism
`ψ = f⁻¹ ∘ E`, extended radially to the disc (Alexander trick, `alexander_trick`). The glued map
is a continuous bijection of `ℂ` tending to `∞` at `∞`, hence proper, hence closed, hence a
homeomorphism.
-/

noncomputable section

namespace InteractingSLE.Foundations.Schoenflies

open Metric Set Function Bornology Topology Filter
open LQGMetric.JordanMap

/-- **Schoenflies theorem (plane, deliverable 3).** For a Jordan curve `Γ ⊆ ℂ` and `p` in the
bounded component `U` of `Γᶜ`, a homeomorphism `h` of `ℂ` with `h 0 = p`, `h '' ∂𝔻 = Γ`,
`h '' 𝔻 = U` and `h '' {|z| > 1} = Γᶜ ∖ U` (the unbounded component). -/
theorem schoenflies_plane {Γ : Set ℂ} (hΓ : IsJordanCurve Γ) {p : ℂ} (hp : p ∈ Γᶜ)
    (hb : IsBounded (connectedComponentIn Γᶜ p)) :
    ∃ h : ℂ ≃ₜ ℂ, h '' sphere 0 1 = Γ ∧ h '' ball 0 1 = connectedComponentIn Γᶜ p ∧
      h '' {z | 1 < ‖z‖} = Γᶜ \ connectedComponentIn Γᶜ p ∧ h 0 = p := by
  set U := connectedComponentIn Γᶜ p with hU
  obtain ⟨f, hfc, hfi, -, hf0, hfb, hfs⟩ := schoenflies_disc hΓ hp hb
  obtain ⟨E, hEc, hEi, hEout, hEs, hEt⟩ := schoenflies_exterior hΓ hp hb
  -- the boundary correspondence `ψ = f⁻¹ ∘ E` on the circle
  set ψ : ℂ → ℂ := fun z => invFunOn f (sphere 0 1) (E z) with hψdef
  have hEmaps : MapsTo E (sphere 0 1) (f '' sphere 0 1) := by
    rw [hfs, ← hEs]; exact mapsTo_image _ _
  have hfsI : InjOn f (sphere 0 1) := hfi.mono sphere_subset_closedBall
  have hsph1 : sphere (0 : ℂ) 1 ⊆ {z | 1 ≤ ‖z‖} := fun z hz => by
    rw [mem_sphere_zero_iff_norm] at hz
    exact le_of_eq hz.symm
  have hψc : ContinuousOn ψ (sphere 0 1) :=
    (LQGMetric.GM.p412c_invFun_contOn (isCompact_sphere 0 1)
      (hfc.mono sphere_subset_closedBall) hfsI).comp (hEc.mono hsph1) hEmaps
  have hfψ : ∀ z ∈ sphere (0 : ℂ) 1, f (ψ z) = E z := fun z hz => invFunOn_eq (hEmaps hz)
  have hψm : MapsTo ψ (sphere 0 1) (sphere 0 1) := fun z hz => invFunOn_mem (hEmaps hz)
  have hψi : InjOn ψ (sphere 0 1) := fun z hz w hw h =>
    hEi (hsph1 hz) (hsph1 hw) (by rw [← hfψ z hz, ← hfψ w hw, h])
  have hψs : SurjOn ψ (sphere 0 1) (sphere 0 1) := by
    intro w hw
    have : f w ∈ E '' sphere 0 1 := by rw [hEs, ← hfs]; exact mem_image_of_mem f hw
    obtain ⟨z, hz, hzw⟩ := this
    exact ⟨z, hz, hfsI (hψm hz) hw (by rw [hfψ z hz, hzw])⟩
  obtain ⟨Ψ, hΨc, hΨi, hΨn, hΨψ, hΨb, -, hΨs⟩ := alexander_trick hψc hψm hψi hψs
  -- the glued map
  set H : ℂ → ℂ := fun z => if ‖z‖ ≤ 1 then f (Ψ z) else E z with hHdef
  have hΨcb : ∀ z : ℂ, ‖z‖ ≤ 1 → Ψ z ∈ closedBall 0 1 := fun z hz => by
    rw [mem_closedBall_zero_iff, hΨn]; exact hz
  have hfΨc : ContinuousOn (fun z => f (Ψ z)) {z | ‖z‖ ≤ 1} :=
    hfc.comp hΨc.continuousOn fun z hz => hΨcb z hz
  have hHc : Continuous H := by
    refine continuous_if_le continuous_norm continuous_const hfΨc hEc ?_
    intro z hz
    have hz' : z ∈ sphere (0 : ℂ) 1 := by rw [mem_sphere_zero_iff_norm]; exact hz
    rw [hΨψ z hz', hfψ z hz']
  have hHin : EqOn H (fun z => f (Ψ z)) (closedBall 0 1) := fun z hz => by
    rw [mem_closedBall_zero_iff] at hz
    simp [hHdef, hz]
  have hHout : EqOn H E {z | 1 < ‖z‖} := fun z hz => by
    simp [hHdef, not_le.mpr (show 1 < ‖z‖ from hz)]
  have himB : H '' ball 0 1 = U := by
    rw [(hHin.mono ball_subset_closedBall).image_eq, ← image_image (g := f), hΨb, hfb]
  have himS : H '' sphere 0 1 = Γ := by
    rw [(hHin.mono sphere_subset_closedBall).image_eq, ← image_image (g := f), hΨs, hfs]
  have himO : H '' {z | 1 < ‖z‖} = Γᶜ \ U := by rw [hHout.image_eq, hEout]
  have hin : ∀ z : ℂ, ‖z‖ ≤ 1 → H z ∈ U ∪ Γ := fun z hz => by
    rcases hz.lt_or_eq with hz | hz
    · exact Or.inl (himB ▸ mem_image_of_mem H (mem_ball_zero_iff.mpr hz))
    · exact Or.inr (himS ▸ mem_image_of_mem H (mem_sphere_zero_iff_norm.mpr hz))
  have hout : ∀ z : ℂ, 1 < ‖z‖ → H z ∈ Γᶜ \ U := fun z hz =>
    himO ▸ mem_image_of_mem H (show z ∈ {z : ℂ | 1 < ‖z‖} from hz)
  have hdis : ∀ z w : ℂ, ‖z‖ ≤ 1 → 1 < ‖w‖ → H z ≠ H w := fun z w hz hw h => by
    have h1 := hin z hz
    have h2 := hout w hw
    rw [h] at h1
    rcases h1 with h1 | h1
    · exact h2.2 h1
    · exact h2.1 h1
  have hHi : Injective H := by
    intro z w h
    rcases le_or_gt ‖z‖ 1 with hz | hz <;> rcases le_or_gt ‖w‖ 1 with hw | hw
    · rw [hHin (mem_closedBall_zero_iff.mpr hz), hHin (mem_closedBall_zero_iff.mpr hw)] at h
      exact hΨi (hfi (hΨcb z hz) (hΨcb w hw) h)
    · exact absurd h (hdis z w hz hw)
    · exact absurd h.symm (hdis w z hw hz)
    · rw [hHout hz, hHout hw] at h
      exact hEi (le_of_lt hz) (le_of_lt hw) h
  have hHs : Surjective H := by
    intro w
    by_cases hwU : w ∈ U
    · rw [← himB] at hwU
      obtain ⟨z, -, hz⟩ := hwU
      exact ⟨z, hz⟩
    by_cases hwΓ : w ∈ Γ
    · rw [← himS] at hwΓ
      obtain ⟨z, -, hz⟩ := hwΓ
      exact ⟨z, hz⟩
    have hwO : w ∈ Γᶜ \ U := ⟨hwΓ, hwU⟩
    rw [← himO] at hwO
    obtain ⟨z, -, hz⟩ := hwO
    exact ⟨z, hz⟩
  have hHt : Tendsto H (cobounded ℂ) (cobounded ℂ) := by
    refine hEt.congr' ?_
    filter_upwards [tendsto_norm_cobounded_atTop.eventually_gt_atTop 1] with z hz
    exact (hHout hz).symm
  have hHp : IsProperMap H := isProperMap_iff_tendsto_cocompact.mpr
    ⟨hHc, by simpa only [← Metric.cobounded_eq_cocompact] using hHt⟩
  refine ⟨(Equiv.ofBijective H ⟨hHi, hHs⟩).toHomeomorphOfContinuousClosed hHc hHp.isClosedMap,
    himS, himB, himO, ?_⟩
  show H 0 = p
  have hΨ0 : Ψ 0 = 0 := norm_eq_zero.mp (by rw [hΨn, norm_zero])
  rw [hHin (mem_closedBall_self zero_le_one)]
  simp only [hΨ0, hf0]

/-- **Schoenflies theorem (plane).** Every Jordan curve in `ℂ` is the image of the unit circle
under a homeomorphism of `ℂ`. -/
theorem schoenflies_plane' {Γ : Set ℂ} (hΓ : IsJordanCurve Γ) :
    ∃ h : ℂ ≃ₜ ℂ, h '' sphere 0 1 = Γ := by
  obtain ⟨x₁, hx₁, -, -, hb, -⟩ := InteractingSLE.Foundations.Jordan.jordan_curve_components_complex hΓ
  obtain ⟨h, hs, -⟩ := schoenflies_plane hΓ hx₁ hb
  exact ⟨h, hs⟩

end InteractingSLE.Foundations.Schoenflies

namespace InteractingSLE

open Metric in
/-- **Schoenflies theorem** in `ℂ`, in the form of the INFRA-GEO design core (PROVE-GEO-JORDAN):
for a Jordan curve `Γ` and a point `p` of its bounded complementary component, a homeomorphism of
`ℂ` carries the unit circle onto `Γ`, the open unit disc onto the component of `p`, the exterior
of the closed disc onto the rest of `Γᶜ`, and `0` to `p`. Restates
`InteractingSLE.Foundations.Schoenflies.schoenflies_plane`. -/
theorem schoenflies_plane {Γ : Set ℂ} (hΓ : LQGMetric.JordanMap.IsJordanCurve Γ) {p : ℂ}
    (hp : p ∈ Γᶜ) (hb : Bornology.IsBounded (connectedComponentIn Γᶜ p)) :
    ∃ h : ℂ ≃ₜ ℂ, h '' sphere 0 1 = Γ ∧ h '' ball 0 1 = connectedComponentIn Γᶜ p ∧
      h '' {z | 1 < ‖z‖} = Γᶜ \ connectedComponentIn Γᶜ p ∧ h 0 = p :=
  Foundations.Schoenflies.schoenflies_plane hΓ hp hb

end InteractingSLE
