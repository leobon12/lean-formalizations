import SupercriticalLQGUniqueness.B2.Final.OpenInputs5
import SupercriticalLQGUniqueness.B2.Final.PfeThm17Assembly
import SupercriticalLQGUniqueness.B2.Final.DG20CoupledInput3a
import SupercriticalLQGUniqueness.B2.PfeLocal.L6Iface
import SupercriticalLQGUniqueness.B2.PfeAxioms.S2ProdAcrossCoupled
import SupercriticalLQGUniqueness.B2.PfeAxioms.R68VReal
import SupercriticalLQGUniqueness.B2.PfeWeyl.W3XFinal
import SupercriticalLQGUniqueness.B2.PfeWeyl.R68S1TFinal

 






















set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal
open LQGMetric (DistC normGFFLaw heatMollify)
open SupercriticalLQGUniqueness.B2.Iface

namespace SupercriticalLQGUniqueness.B2.Final

 
theorem iface_pfeThm17_of_3bnew (hI : DG20Interfaces) (h3b : ThreeBNew) : PfeThm17 := by
  obtain ⟨hIdent, hLocal⟩ := h3b
  obtain ⟨hS4, hPerc, hRatio, hRel, hPos, hTop⟩ := id hI
  have hSkC := DG20Lim.dg20LimitSkC_of_inputs_via_SkSB hS4 hPerc hRatio hRel hPos hTop
  have hLoc : PfeL5ObsLocality := PfeLocal.pfeL5ObsLocality_proved
  have hLus : PfeLusinApprox := pfeLusinApprox_proved
  intro ξ m hm ε hε
  obtain ⟨Q, hQ, -⟩ := existsUnique_isLFPPExponent ξ
  
  obtain ⟨φ₁, hφ₁, c, V, Ω', M', SB', P', hP', h', hN, L, hB, hsa, hrc⟩ :=
    dg20CouplingSmallAnnuliCoords_proved hI ξ Q hQ m hm ε hε
  let _ : MeasurableSpace Ω' := M'
  have : StandardBorelSpace Ω' := SB'
  have : IsProbabilityMeasure P' := hP'
  have : Nonempty Ω' := nonempty_of_isProbabilityMeasure' P'
  have hat : CoupledAcrossTails P' L :=
    PfeAxioms.dg20CoupledAcrossTailsInput_proved hI ξ Q m (fun n => ε (φ₁ n)) c V P' h' hN L hB
  
  have hloc : PfeLocal.Inputs.L5ObsLocality P' h' L :=
    hLoc hI ξ Q m (fun n => ε (φ₁ n)) c V P' h' hN L hB hsa hat
  obtain ⟨Φ, hΦ, hII, hconvΦ⟩ := PfeLocal.l5_hconv_of_obsLocality hS4 hPerc ξ Q hB.exponent
    m hB.normalizer V hB.heat_measurable hB.heat_ae (fun n => ε (φ₁ n))
    hB.scale_tendsto c hB.ratio P' h' hB.limit_field hN hB.field_measurable hB.field_law
    (DG20Lim.ae_pairing_tendsto_of_ae_tendsto hB.field_tendsto) L hB.limit_measurable
    hB.metric_tendsto (hB.geometry.mono fun _ hω => hω.2) hloc
  
  obtain ⟨ψ₁, hψ₁, happrox⟩ := hLus hI ξ Q m (fun n => ε (φ₁ n)) c V P' h' hN L hB Φ hΦ hII
  have hBa : DG20CouplingData ξ Q m (fun n => ε (φ₁ (ψ₁ n))) c V P' h'
      (fun n => hN (ψ₁ n)) L := hB.comp hψ₁
  have hconva : ∀ᵐ ω ∂P', Tendsto (fun n =>
      PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (m (ε (φ₁ (ψ₁ n))))
        (V (ε (φ₁ (ψ₁ n))) (hN (ψ₁ n) ω))) atTop (𝓝 (Φ (h' ω))) :=
    hconvΦ.mono fun _ hω => hω.comp hψ₁.tendsto_atTop
  obtain ⟨ns, hns, hlsc⟩ := PfeWeyl.normalizedLscLimit_of_coupling ξ m
    (fun n => ε (φ₁ (ψ₁ n))) V hBa.heat_measurable hBa.heat_ae Φ hΦ P'
    (fun n => hN (ψ₁ n)) h' hBa.field_measurable hBa.limit_field.1.measurable
    hBa.field_law (PfeAxioms.normGFFLaw_eq_of_normalized P' h' hBa.limit_field).symm
    hconva happrox
  have hψ01 : StrictMono (fun n => ψ₁ (ns n)) := hψ₁.comp hns
  have hB₁ : DG20CouplingData ξ Q m (fun n => ε (φ₁ (ψ₁ (ns n)))) c V P' h'
      (fun n => hN (ψ₁ (ns n))) L := hB.comp hψ01
  have hsa₁ : CoupledSmallAnnuli ξ m (fun n => ε (φ₁ (ψ₁ (ns n)))) V P'
      (fun n => hN (ψ₁ (ns n))) L := hsa.comp hψ01
  have hrc₁ : CoupledRatCoords ξ m (fun n => ε (φ₁ (ψ₁ (ns n)))) V P'
      (fun n => hN (ψ₁ (ns n))) L := hrc.comp hψ01
  have hlsc₁ : PfeWeyl.NormalizedLscLimit ξ m (fun n => ε (φ₁ (ψ₁ (ns n)))) Φ := hlsc
  
  obtain ⟨ψc, hψc, hW⟩ :=
    PfeWeyl.exists_fixedFieldWeylAllBounded_of_coupling P' hB₁ hsa₁ hat Φ hΦ hII
  have hB₂ : DG20CouplingData ξ Q m (fun n => ε (φ₁ (ψ₁ (ns (ψc n))))) c V P' h'
      (fun n => hN (ψ₁ (ns (ψc n)))) L := hB₁.comp hψc
  have hsa₂ : CoupledSmallAnnuli ξ m (fun n => ε (φ₁ (ψ₁ (ns (ψc n))))) V P'
      (fun n => hN (ψ₁ (ns (ψc n)))) L := hsa₁.comp hψc
  have hrc₂ : CoupledRatCoords ξ m (fun n => ε (φ₁ (ψ₁ (ns (ψc n))))) V P'
      (fun n => hN (ψ₁ (ns (ψc n)))) L := hrc₁.comp hψc
  have hlsc₂ : PfeWeyl.NormalizedLscLimit ξ m (fun n => ε (φ₁ (ψ₁ (ns (ψc n))))) Φ :=
    PfeWeyl.normalizedLscLimit_comp hlsc₁ hψc
  have hW₂ : FixedFieldWeylAllBounded ξ m (fun n => ε (φ₁ (ψ₁ (ns (ψc n))))) Φ := hW
  
  obtain ⟨ψi, hψi, hId⟩ := hIdent hI ξ Q m (fun n => ε (φ₁ (ψ₁ (ns (ψc n))))) c V P' h'
    (fun n => hN (ψ₁ (ns (ψc n)))) L hB₂ hsa₂ hat hrc₂ Φ hΦ hII hlsc₂ hW₂
  have hB₅ : DG20CouplingData ξ Q m (fun n => ε (φ₁ (ψ₁ (ns (ψc (ψi n)))))) c V P' h'
      (fun n => hN (ψ₁ (ns (ψc (ψi n))))) L := hB₂.comp hψi
  have hsa₅ : CoupledSmallAnnuli ξ m (fun n => ε (φ₁ (ψ₁ (ns (ψc (ψi n)))))) V P'
      (fun n => hN (ψ₁ (ns (ψc (ψi n))))) L := hsa₂.comp hψi
  have hrc₅ : CoupledRatCoords ξ m (fun n => ε (φ₁ (ψ₁ (ns (ψc (ψi n)))))) V P'
      (fun n => hN (ψ₁ (ns (ψc (ψi n))))) L := hrc₂.comp hψi
  have hlsc₅ : PfeWeyl.NormalizedLscLimit ξ m (fun n => ε (φ₁ (ψ₁ (ns (ψc (ψi n)))))) Φ :=
    PfeWeyl.normalizedLscLimit_comp hlsc₂ hψi
  have hW₅ : FixedFieldWeylAllBounded ξ m (fun n => ε (φ₁ (ψ₁ (ns (ψc (ψi n)))))) Φ :=
    PfeWeyl.fixedFieldWeylAllBounded_comp hW₂ hψi
  have hId₅ : FixedFieldPatchIdentification ξ m
      (fun n => ε (φ₁ (ψ₁ (ns (ψc (ψi n)))))) Φ := hId
  
  have hKI : PatchWeylIdentity ξ m (fun n => ε (φ₁ (ψ₁ (ns (ψc (ψi n)))))) Φ :=
    patchWeylIdentity_of_identification hId₅
  have hgeoΦ : PfeWeyl.NormalizedLimitGeometry Φ := normalizedLimitGeometry_of_coupling hB₅ Φ hII
  have hII_D : ∀ᵐ ω ∂P', L ω =
      PfeAxioms.patchWitness ξ m (fun n => ε (φ₁ (ψ₁ (ns (ψc (ψi n)))))) (h' ω) := by
    filter_upwards [hII, ae_patchWitness_eq_of_identity hKI hgeoΦ P' h' hB₅.limit_field]
      with ω h1 h2
    rw [h1, h2]
  
  obtain ⟨ψt, hψt, hSub⟩ := PfeWeyl.r68_subseqLimit_of_normalized_of_inputs ξ Q m
    (fun n => ε (φ₁ (ψ₁ (ns (ψc (ψi n)))))) c V P' h' (fun n => hN (ψ₁ (ns (ψc (ψi n))))) L
    hS4 hPerc hPos hB₅ hsa₅ hat hrc₅
    (PfeAxioms.patchWitness ξ m (fun n => ε (φ₁ (ψ₁ (ns (ψc (ψi n)))))))
    (PfeAxioms.measurable_patchWitness ξ m _) hII_D
    (fixedFieldWeyl_patchWitness_of_identity hKI hgeoΦ hW₅)
    (normalizedLimitGeometry_patchWitness_of_identity hKI hgeoΦ)
    (boundedShiftWeyl_patchWitness_of_identity hKI hgeoΦ)
  have hSub' : SubseqLimit ξ m (fun n => ε (φ₁ (ψ₁ (ns (ψc (ψi (ψt n)))))))
      (PfeAxioms.patchWitness ξ m (fun n => ε (φ₁ (ψ₁ (ns (ψc (ψi n))))))) := hSub
  
  have hB₆ : DG20CouplingData ξ Q m (fun n => ε (φ₁ (ψ₁ (ns (ψc (ψi (ψt n))))))) c V P' h'
      (fun n => hN (ψ₁ (ns (ψc (ψi (ψt n)))))) L := hB₅.comp hψt
  have hsa₆ : CoupledSmallAnnuli ξ m (fun n => ε (φ₁ (ψ₁ (ns (ψc (ψi (ψt n))))))) V P'
      (fun n => hN (ψ₁ (ns (ψc (ψi (ψt n)))))) L := hsa₅.comp hψt
  obtain ⟨Λ, hΛ, hV17⟩ := hB₆.ratio_bound
  let _ : MeasurableSpace LSCFun := borel LSCFun
  have : BorelSpace LSCFun := ⟨rfl⟩
  refine ⟨fun n => φ₁ (ψ₁ (ns (ψc (ψi (ψt n))))),
    hφ₁.comp (hψ₁.comp (hns.comp (hψc.comp (hψi.comp hψt)))),
    PfeAxioms.patchWitness ξ m (fun n => ε (φ₁ (ψ₁ (ns (ψc (ψi n)))))), c,
    ⟨PfeAxioms.measurable_patchWitness ξ m _,
      fun P _ h hh => ae_isLengthSpace_patchWitness_of_identity hKI hgeoΦ P h hh,
      fun P _ h hh U => hLocal hI ξ Q m (fun n => ε (φ₁ (ψ₁ (ns (ψc (ψi n)))))) c V P' h'
        (fun n => hN (ψ₁ (ns (ψc (ψi n))))) L hB₅ hsa₅ hat hrc₅ Φ hΦ hII hlsc₅ hW₅ hId₅ P h hh U,
      fun P _ h hh => ae_weyl_patchWitness_of_identity hKI hgeoΦ P h hh,
      fun P _ h hh z => ae_translate_patchWitness_of_identity hKI hgeoΦ hSub' P h hh z,
      ⟨Λ, hΛ, hV17⟩,
      fun P _ h hh a ha A => PfeAxioms.r68v_pfeAxiomV_of_coupling hSkC hS4 hPerc ξ Q hQ m hm
        (fun n => ε (φ₁ (ψ₁ (ns (ψc (ψi (ψt n))))))) hB₆.scale_tendsto
        (PfeAxioms.patchWitness ξ m (fun n => ε (φ₁ (ψ₁ (ns (ψc (ψi n)))))))
        hSub' c hB₆.ratio Λ hΛ hV17 P' h' (fun n => hN (ψ₁ (ns (ψc (ψi (ψt n)))))) L hB₆
        hsa₆ (PfeAxioms.measurable_patchWitness ξ m _) hII_D P h hh a ha A⟩,
    hSub', hB₆.ratio⟩

end SupercriticalLQGUniqueness.B2.Final
