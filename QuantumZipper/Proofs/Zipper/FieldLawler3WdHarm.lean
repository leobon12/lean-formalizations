import QuantumZipper.Proofs.Zipper.FieldLawler3WdMob
import QuantumZipper.Proofs.Thm18.LWFarPocketFar

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# FL3-WD (Harm): harmonic measure under the Möbius map `T_p z = 1/(z - p)`

`fl3Wd_isHarmMeas`: if `ω` is the harmonic measure of `A ⊆ ∂D` in a bounded domain `D`, and
`p ∈ ∂D \ closure A`, then `ω ∘ T_p⁻¹` is the harmonic measure of `T_p(A)` in `T_p(D)`
(conformal invariance of harmonic measure; Lawler, *Conformally Invariant Processes in the
Plane*, 2005, §2.3, Prop. 2.10 context; own elementary transport of the boundary clauses, as
`flSim_isHarmMeas` in FieldLawlerSubExcGeo.lean for similarities).
-/

noncomputable section

open Filter Set Metric Complex
open scoped Topology

namespace QuantumZipper
namespace FieldLawler

open Thm18Asm.LWFar QuantumZipper.CA

variable {p : ℂ} {D : Set ℂ}

lemma fl3Wd_tendsto_Ti (hpD : p ∉ D) {z : ℂ} (hz : z ≠ p) {g : ℂ → ℝ} {l : Filter ℝ}
    (ht : Tendsto g (𝓝[D] z) l) :
    Tendsto (fun w => g (fl3WdTi p w)) (𝓝[fl3WdT p '' D] (fl3WdT p z)) l := by
  refine ht.comp (tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩)
  · have := (fl3WdTi_contAt (p := p) (fl3WdT_ne_zero hz)).tendsto
    rw [fl3WdTi_T hz] at this
    exact this.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with w hw
    exact ((fl3Wd_memT hpD w).1 hw).2

lemma fl3Wd_mem_closureT {S : Set ℂ} {z : ℂ} (hz : z ≠ p) (hS : z ∈ closure S) :
    fl3WdT p z ∈ closure (fl3WdT p '' (S \ {p})) := by
  refine mem_closure_image (fl3WdT_contAt hz) ?_
  have h1 : closure S ⊆ closure (S \ {p}) ∪ {p} := by
    have hsub : S ⊆ (S \ {p}) ∪ {p} := fun y hy => by
      by_cases h : y = p
      exacts [Or.inr h, Or.inl ⟨hy, h⟩]
    refine (closure_mono hsub).trans ?_
    rw [closure_union, closure_singleton]
  rcases h1 hS with h | h
  · exact h
  · exact absurd h hz

/-- **Transport of harmonic measure by `T_p`.** -/
theorem fl3Wd_isHarmMeas {R₀ : ℝ} (hDo : IsOpen D) (hDb : D ⊆ ball 0 R₀) (hne : D.Nonempty)
    (hp : p ∈ frontier D) {A : Set ℂ} (hpA : p ∉ closure A) {ω : ℂ → ℝ}
    (hω : IsHarmMeas D A ω) :
    IsHarmMeas (fl3WdT p '' D) (fl3WdT p '' A) (fun w => ω (fl3WdTi p w)) := by
  have hpD : p ∉ D := fun h => by rw [hDo.frontier_eq] at hp; exact hp.2 h
  have hfr := fl3Wd_frontierT hDo hDb hne hpD
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    have hzp : z ≠ p := fun e => hpD (e ▸ hz)
    have hw := fl3WdT_ne_zero hzp
    have han : AnalyticAt ℂ (fl3WdTi p) (fl3WdT p z) :=
      analyticAt_const.add (analyticAt_id.inv hw)
    have h1 : InnerProductSpace.HarmonicAt ω (fl3WdTi p (fl3WdT p z)) := by
      rw [fl3WdTi_T hzp]; exact hω.harm z hz
    exact pocket_harmonicAt_comp han h1
  · rintro _ ⟨z, hz, rfl⟩
    rw [fl3WdTi_T (show z ≠ p from fun e => hpD (e ▸ hz))]; exact hω.mem01 z hz
  · rintro _ ⟨z, hz, rfl⟩ hcl
    have hzp : z ≠ p := fun e => hpA (e ▸ subset_closure hz)
    refine fl3Wd_tendsto_Ti hpD hzp (hω.one z hz fun hc => hcl ?_)
    refine closure_mono ?_ (fl3Wd_mem_closureT hzp hc)
    rintro _ ⟨y, ⟨⟨hyf, hyA⟩, hyp⟩, rfl⟩
    refine ⟨hfr ▸ ⟨y, ⟨hyf, hyp⟩, rfl⟩, ?_⟩
    rintro ⟨y', hy', he⟩
    have hy'p : y' ≠ p := fun e => hpA (e ▸ subset_closure hy')
    exact hyA (fl3WdT_inj hy'p hyp he ▸ hy')
  · intro x₀ hx₀ hcl
    rw [hfr] at hx₀
    obtain ⟨z, ⟨hzf, hzp⟩, rfl⟩ := hx₀
    refine fl3Wd_tendsto_Ti hpD hzp (hω.zero z hzf fun hc => hcl ?_)
    refine closure_mono (image_mono sdiff_subset) (fl3Wd_mem_closureT hzp hc)
  · intro _
    refine (hω.zero p hp hpA).comp (tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩)
    · have h1 : Tendsto (fl3WdTi p) (Bornology.cobounded ℂ) (𝓝 (p + 0)) :=
        tendsto_const_nhds.add tendsto_inv₀_cobounded
      rw [add_zero] at h1
      exact h1.mono_left inf_le_left
    · exact eventually_inf_principal.2 (Eventually.of_forall fun w hw =>
        ((fl3Wd_memT hpD w).1 hw).2)

end FieldLawler
end QuantumZipper
