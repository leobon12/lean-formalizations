import SupercriticalLQGUniqueness.B2.Final.OpenInputs
import SupercriticalLQGUniqueness.B2.Final.CouplingGlue
import SupercriticalLQGUniqueness.B2.Final.LusinBridge
import SupercriticalLQGUniqueness.B2.PfeLocal.L5Main
import SupercriticalLQGUniqueness.B2.PfeAxioms.S2SubseqLimit
import SupercriticalLQGUniqueness.B2.PfeAxioms.S2WeakMetric
import SupercriticalLQGUniqueness.B2.DG20Lim.SkUpgradeOfInputs
import SupercriticalLQGUniqueness.Frozen.ExistsUnique_isLFPPExponent

 
























set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal
open LQGMetric (DistC normGFFLaw heatMollify)
open SupercriticalLQGUniqueness.B2.Iface

namespace SupercriticalLQGUniqueness.B2.Final

 
theorem iface_pfeThm17_of_open_inputs (hI : DG20Interfaces)
    (hSA : DG20SmallAnnuliCoupling) (hAT : DG20CoupledAcrossTailsInput)
    (hLoc : PfeL5ObsLocality) : PfeThm17 := by
  obtain ⟨hS4, hPerc, hRatio, hRel, hPos, hTop⟩ := id hI
  have hSkC := DG20Lim.dg20LimitSkC_of_inputs_via_SkSB hS4 hPerc hRatio hRel hPos hTop
  have hLus : PfeLusinApprox := pfeLusinApprox_proved
  intro ξ m hm ε hε
  obtain ⟨Q, hQ, -⟩ := existsUnique_isLFPPExponent ξ
  
  obtain ⟨φ₁, hφ₁, c, V, Ω', M', SB', P', hP', h', hN, L, hB, hsa, hS1⟩ :=
    hSA hI ξ Q hQ m hm ε hε
  let _ : MeasurableSpace Ω' := M'
  have : StandardBorelSpace Ω' := SB'
  have : IsProbabilityMeasure P' := hP'
  have : Nonempty Ω' := nonempty_of_isProbabilityMeasure' P'
  
  have hat : CoupledAcrossTails P' L :=
    hAT hI ξ Q m (fun n => ε (φ₁ n)) c V P' h' hN L hB
  
  have hloc : PfeLocal.Inputs.L5ObsLocality P' h' L :=
    hLoc hI ξ Q m (fun n => ε (φ₁ n)) c V P' h' hN L hB hsa hat
  obtain ⟨Φ, hΦ, hII, hconvΦ⟩ := PfeLocal.l5_hconv_of_obsLocality hS4 hPerc ξ Q hB.exponent
    m hB.normalizer V hB.heat_measurable hB.heat_ae (fun n => ε (φ₁ n))
    hB.scale_tendsto c hB.ratio P' h' hB.limit_field hN
    hB.field_measurable hB.field_law
    (DG20Lim.ae_pairing_tendsto_of_ae_tendsto hB.field_tendsto) L hB.limit_measurable
    hB.metric_tendsto (hB.geometry.mono fun _ hω => hω.2) hloc
  
  have hgeoΦ : PfeWeyl.NormalizedLimitGeometry Φ := normalizedLimitGeometry_of_coupling hB Φ hII
  have htailΦ : PfeWeyl.NormalizedAcrossTails Φ :=
    normalizedAcrossTails_of_coupling hB hΦ hII hat
  
  obtain ⟨ψ₁, hψ₁, hsmall, hpts⟩ := hS1 Φ hΦ hII
  have hB₁ : DG20CouplingData ξ Q m (fun n => ε (φ₁ (ψ₁ n))) c V P' h'
      (fun n => hN (ψ₁ n)) L := hB.comp hψ₁
  have hconvΦ₁ : ∀ᵐ ω ∂P', Tendsto (fun n =>
      PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (m (ε (φ₁ (ψ₁ n))))
        (V (ε (φ₁ (ψ₁ n))) (hN (ψ₁ n) ω))) atTop (𝓝 (Φ (h' ω))) :=
    hconvΦ.mono fun _ hω => hω.comp hψ₁.tendsto_atTop
  
  obtain ⟨ψ₂, hψ₂, happrox⟩ := hLus hI ξ Q m (fun n => ε (φ₁ (ψ₁ n))) c V P' h'
    (fun n => hN (ψ₁ n)) L hB₁ Φ hΦ hII
  have hB₂ : DG20CouplingData ξ Q m (fun n => ε (φ₁ (ψ₁ (ψ₂ n)))) c V P' h'
      (fun n => hN (ψ₁ (ψ₂ n))) L := hB₁.comp hψ₂
  have hconvΦ₂ : ∀ᵐ ω ∂P', Tendsto (fun n =>
      PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (m (ε (φ₁ (ψ₁ (ψ₂ n)))))
        (V (ε (φ₁ (ψ₁ (ψ₂ n)))) (hN (ψ₁ (ψ₂ n)) ω))) atTop (𝓝 (Φ (h' ω))) :=
    hconvΦ₁.mono fun _ hω => hω.comp hψ₂.tendsto_atTop
  
  obtain ⟨ns, hns, hlsc⟩ := PfeWeyl.normalizedLscLimit_of_coupling ξ m
    (fun n => ε (φ₁ (ψ₁ (ψ₂ n)))) V hB₂.heat_measurable hB₂.heat_ae Φ hΦ P'
    (fun n => hN (ψ₁ (ψ₂ n))) h' hB₂.field_measurable hB₂.limit_field.1.measurable
    hB₂.field_law (PfeAxioms.normGFFLaw_eq_of_normalized P' h' hB₂.limit_field).symm
    hconvΦ₂ happrox
  
  have hB₃ : DG20CouplingData ξ Q m (fun n => ε (φ₁ (ψ₁ (ψ₂ (ns n))))) c V P' h'
      (fun n => hN (ψ₁ (ψ₂ (ns n)))) L := hB₂.comp hns
  have hlsc₃ : PfeWeyl.NormalizedLscLimit ξ m (fun n => ε (φ₁ (ψ₁ (ψ₂ (ns n))))) Φ := hlsc
  have hsmall₃ : PfeWeyl.NormalizedSmallAnnuli ξ m (fun n => ε (φ₁ (ψ₁ (ψ₂ (ns n))))) Φ :=
    PfeWeyl.normalizedSmallAnnuli_comp hsmall (hψ₂.comp hns)
  have hpts₃ : PfeWeyl.NormalizedPointCircles ξ m (fun n => ε (φ₁ (ψ₁ (ψ₂ (ns n))))) Φ :=
    PfeWeyl.normalizedPointCircles_comp hpts (hψ₂.comp hns)
  obtain ⟨Λ, hΛ, hV17⟩ := hB₃.ratio_bound
  let _ : MeasurableSpace LSCFun := borel LSCFun
  have : BorelSpace LSCFun := ⟨rfl⟩
  have hmono : StrictMono (fun n => φ₁ (ψ₁ (ψ₂ (ns n)))) :=
    hφ₁.comp (hψ₁.comp (hψ₂.comp hns))
  refine ⟨fun n => φ₁ (ψ₁ (ψ₂ (ns n))), hmono,
    PfeAxioms.patchWitness ξ m (fun n => ε (φ₁ (ψ₁ (ψ₂ (ns n))))), c, ?_, ?_, hB₃.ratio⟩
  · exact PfeAxioms.isPfeWeakMetric_patchWitness hSkC hS4 hPerc ξ Q hQ m hm
      (fun n => ε (φ₁ (ψ₁ (ψ₂ (ns n))))) hB₃.scale_tendsto Φ hlsc₃ hgeoΦ htailΦ
      hsmall₃ hpts₃ c hB₃.ratio Λ hΛ hV17
  · exact PfeAxioms.subseqLimit_patchWitness ξ m
      (fun n => ε (φ₁ (ψ₁ (ψ₂ (ns n))))) hB₃.scale_tendsto Φ hlsc₃ hgeoΦ htailΦ
      hsmall₃ hpts₃

end SupercriticalLQGUniqueness.B2.Final
