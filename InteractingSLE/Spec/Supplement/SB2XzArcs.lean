/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2MaSet
import InteractingSLE.Spec.Supplement.SB2KEntry
import InteractingSLE.Spec.Supplement.BR3Ref
import InteractingSLE.Spec.Supplement.GW1ConnectorFirst

/-!
# The lower walk's connectors lie in `[0, ∞)`, almost surely under the retained kernel

Packet PROVE-T14-SB2LIFT (round 30). **`sb2LowerArcsIci`**: in SB2(2)'s setting, at almost every retained sample,
almost surely under its kernel, every connector recorded by the lower walk lies in `[0, ∞)`. This is
`Lv.ae_arcs_subset_Ici` for the regularized family, with GW1's ambient bound from the counterflow
(`GW1Conn.ambient_bounds`, GW0's forward statement from Theorem 1.3, `BR3Ref.gw0ForwardStatement_of_theorem13`),
transferred to the actual family (`StagedReg.regFam_spec`) and to the kernel (`KernelTower.ae_ae_condExpKernel_of_ae`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lk

open Exist Exist.Staged Exist.StagedLaw GW1W

/-- **The lower walk's connectors lie in `[0, ∞)`**, almost surely under the retained kernel (Theorem 1.3). -/
theorem sb2LowerArcsIci (h13₀ : Exist.Theorem13Statement.{0}) :
    Lf.SB2LowerSetting.{u} fun κ b jumps _ _ _ P _ E u l k ω₀ _ _ _ _ =>
      ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (Lu.upperSpec u l) (E (Lu.upperSpec u l)) k) ω₀),
        ∀ n, ∀ a ∈ (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) n).2.1, a ⊆ Ici 0 := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft
  have hsp : IsBoundaryContinuedProgram (Lu.upperSpec u l).2.2 := Lu.isBoundaryContinuedProgram_upperSpec hlθ
  have hm𝒢 := (hE _ hsp).2.1 k
  have hamb := (GW1Conn.ambient_bounds (BR3Ref.gw0ForwardStatement_of_theorem13 h13₀) hκ hκ4 hb hh hcf hζ').1
  have hlwp : IsBoundaryContinuedProgram (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2 :=
    isBoundaryContinuedProgram_boundaryWalkSpec b jumps ⟨le_rfl, by linarith [Real.pi_pos]⟩ true
  obtain ⟨hE', hreg', hrun⟩ := StagedReg.regFam_spec hb hE hER
  have hP : ∀ᵐ ω ∂P, ∀ n, ∀ a ∈ (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) n).2.1, a ⊆ Ici 0 := by
    filter_upwards [Lv.ae_arcs_subset_Ici hκ hb hh (hE' _ hlwp) (hreg' _) hamb, hrun _ hlwp] with ω harcs hr
    intro n a ha
    rw [← hr n] at ha
    exact harcs n a ha
  filter_upwards [KernelTower.ae_ae_condExpKernel_of_ae hm𝒢 hP] with ω₀ hω₀
  intro c θ hlaunch b' J' h' hb' hT' hG'
  exact hω₀

end InteractingSLE.Theorem14.SB.Lk
