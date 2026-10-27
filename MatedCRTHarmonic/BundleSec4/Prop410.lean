import MatedCRTHarmonic.BundleSec4.Density
import MatedCRTHarmonic.BundleSec4.Prop210Source
import MatedCRTHarmonic.Lemma38Source.MTC
import MatedCRTHarmonic.MesoModel.FinalAssembly
import MatedCRTHarmonic.GMS4.Prop210
import MatedCRTHarmonic.GMS4.CellGraphInterface
import MatedCRTHarmonic.MesoModel.RecAdmissible
import MatedCRTHarmonic.MesoModel.RecBridge

/-!
# [18] Proposition 2.10 from Proposition 4.10 and (4.20), on MTC's family

[18] : "Proposition 2.10 is an immediate consequence of Proposition 4.10 and
(4.20)." Here, for the bundle model:

* `prop210Source_of_prop410Source`: `Prop410Source P η` (Proposition 4.10 for the bundle's γ-cone curve `η`, geometric
  `u_*^ε`) implies `Prop210Source` for MTC's dyadic family, through the concrete (4.20)
  (`BundleSec4.ae_uDens_le_two_uStar`), G4's deterministic transfer `GMS4.prop210Bound_of_localized_integral_ae`
  (threshold `2A`, tolerance `2ε^α`), and the dyadic absorption `2ε^α ≤ ε^{α/2}` for small meshes (probability `≤ 1`
  otherwise; rate constant `Cfail + 2`);
* `prop410Source_congr_ae`: the statement only depends on the a.e. class of the curve;
* `exists_cellModel_of_matingOfTrees_of_prop410Source`, the companion map conclusion: both
  frozen v3 conclusions with `Prop410Source` (at the cone realization's curve of every coupling) as the only remaining
  input.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.BundleSec4

open MatedCRTHarmonic

/-- G3's Proposition 2.10 bound is monotone in the tolerance. -/
theorem bundle_prop210Bound_mono_tol {V E : Type*} {G : LFMultigraph V E} {o : V}
    (H : CellularEmbedding G o) {D : Set ℂ} {f : ℂ → ℝ} {A η η' : ℝ} (hη : η ≤ η')
    (h : GMS3.Prop210Bound H D f A η) : GMS3.Prop210Bound H D f A η' :=
  h.trans (add_le_add le_rfl (ENNReal.ofReal_le_ofReal hη))

section Coupling

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}

/-- **One test of [18] Proposition 2.10 from the same test of Proposition 4.10 and (4.20)** at MTC's family: if the
Proposition 4.10 failure (threshold `A`, tolerance `ε^α`) has outer probability `≤ Cfail ε^α`, then G3's Proposition 2.10
failure (threshold `2A`, tolerance `ε^{α/2}`) has outer probability `≤ (Cfail + 2) ε^{α/2}` (`ε = 2^{-k}`; small meshes
by (4.20) and `2ε^α ≤ ε^{α/2}`, the others since the bound exceeds one). -/
theorem prop210Bad_le_of_prop410Bad
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hstd : StandardBorelSpace Ω) (hγ : γ ∈ Ioo 0 2) {k : ℕ} {V : Set ℂ} {f : ℂ → ℝ}
    {A α Cfail : ℝ} (hV : MeasurableSet V) (hα : 0 < α) (hCfail : 0 ≤ Cfail)
    (hbound : P (Prop410Bad η (CellFamily.mesh k) V f A (CellFamily.mesh k ^ α)) ≤
      ENNReal.ofReal (Cfail * CellFamily.mesh k ^ α)) :
    (MoTInput.unitMesoModelOfCoupling D hstd hγ).coupled.family.P
        (GMS4.Prop210Bad (MoTInput.unitMesoModelOfCoupling D hstd hγ).coupled.family k V f (2 * A)
          (CellFamily.mesh k ^ (α / 2))) ≤
      ENNReal.ofReal ((Cfail + 2) * CellFamily.mesh k ^ (α / 2)) := by
  -- the family's probability is `P`
  change P (GMS4.Prop210Bad (MoTInput.unitMesoModelOfCoupling D hstd hγ).coupled.family k V f (2 * A)
    (CellFamily.mesh k ^ (α / 2))) ≤ ENNReal.ofReal ((Cfail + 2) * CellFamily.mesh k ^ (α / 2))
  have : IsProbabilityMeasure P := D.isProbabilityMeasure
  have hε := bundle_mesh_pos k
  have ht0 : 0 < CellFamily.mesh k ^ (α / 2) := Real.rpow_pos_of_pos hε _
  have htt : CellFamily.mesh k ^ α = CellFamily.mesh k ^ (α / 2) * CellFamily.mesh k ^ (α / 2) := by
    rw [← Real.rpow_add hε, add_halves]
  have hpow : CellFamily.mesh k ^ α ≤ CellFamily.mesh k ^ (α / 2) :=
    bundle_mesh_rpow_le_of_le k (by linarith)
  by_cases hsmall : 2 * CellFamily.mesh k ^ α ≤ CellFamily.mesh k ^ (α / 2)
  · -- small mesh: (4.20) and absorption of the doubled tolerance
    have hcmp : ∀ᵐ ω ∂P, ∀ᵐ z ∂volume.restrict V,
        GMS3.uDens ((MoTInput.unitMesoModelOfCoupling D hstd hγ).coupled.family.H k ω) z ≤
          2 * GMS4b.uStar (CellFamily.mesh k) (η ω) z := by
      filter_upwards [ae_uDens_le_two_uStar D hstd hγ] with ω hω
      exact ae_restrict_of_ae (hω k)
    have hnull : P {ω | ¬ ∀ᵐ z ∂volume.restrict V,
        GMS3.uDens ((MoTInput.unitMesoModelOfCoupling D hstd hγ).coupled.family.H k ω) z ≤
          2 * GMS4b.uStar (CellFamily.mesh k) (η ω) z} = 0 := ae_iff.mp hcmp
    have hsub : GMS4.Prop210Bad (MoTInput.unitMesoModelOfCoupling D hstd hγ).coupled.family k V f (2 * A)
        (CellFamily.mesh k ^ (α / 2)) ⊆
        Prop410Bad η (CellFamily.mesh k) V f A (CellFamily.mesh k ^ α) ∪
          {ω | ¬ ∀ᵐ z ∂volume.restrict V,
            GMS3.uDens ((MoTInput.unitMesoModelOfCoupling D hstd hγ).coupled.family.H k ω) z ≤
              2 * GMS4b.uStar (CellFamily.mesh k) (η ω) z} := by
      intro ω hbad
      by_cases hc : ∀ᵐ z ∂volume.restrict V,
          GMS3.uDens ((MoTInput.unitMesoModelOfCoupling D hstd hγ).coupled.family.H k ω) z ≤
            2 * GMS4b.uStar (CellFamily.mesh k) (η ω) z
      · left
        intro hgood410
        apply hbad
        have hb := GMS4.prop210Bound_of_localized_integral_ae
          ((MoTInput.unitMesoModelOfCoupling D hstd hγ).coupled.family.H k ω) hV f
          (fun z => GMS4b.uStar (CellFamily.mesh k) (η ω) z) hc hgood410
        exact bundle_prop210Bound_mono_tol _ hsmall hb
      · exact Or.inr hc
    calc
      P (GMS4.Prop210Bad (MoTInput.unitMesoModelOfCoupling D hstd hγ).coupled.family k V f (2 * A)
          (CellFamily.mesh k ^ (α / 2))) ≤
          P (Prop410Bad η (CellFamily.mesh k) V f A (CellFamily.mesh k ^ α)) + P {ω | ¬ ∀ᵐ z ∂volume.restrict V,
            GMS3.uDens ((MoTInput.unitMesoModelOfCoupling D hstd hγ).coupled.family.H k ω) z ≤
              2 * GMS4b.uStar (CellFamily.mesh k) (η ω) z} :=
        (measure_mono hsub).trans (measure_union_le _ _)
      _ = P (Prop410Bad η (CellFamily.mesh k) V f A (CellFamily.mesh k ^ α)) := by rw [hnull, add_zero]
      _ ≤ ENNReal.ofReal (Cfail * CellFamily.mesh k ^ α) := hbound
      _ ≤ ENNReal.ofReal ((Cfail + 2) * CellFamily.mesh k ^ (α / 2)) := by
        apply ENNReal.ofReal_le_ofReal
        calc
          Cfail * CellFamily.mesh k ^ α ≤ Cfail * CellFamily.mesh k ^ (α / 2) :=
            mul_le_mul_of_nonneg_left hpow hCfail
          _ ≤ (Cfail + 2) * CellFamily.mesh k ^ (α / 2) :=
            mul_le_mul_of_nonneg_right (by linarith) ht0.le
  · -- large mesh: the bound exceeds one
    have hhalf : 1 / 2 < CellFamily.mesh k ^ (α / 2) := by
      rw [htt] at hsmall
      rw [not_le] at hsmall
      nlinarith
    calc
      P (GMS4.Prop210Bad (MoTInput.unitMesoModelOfCoupling D hstd hγ).coupled.family k V f (2 * A)
          (CellFamily.mesh k ^ (α / 2))) ≤ 1 := prob_le_one
      _ = ENNReal.ofReal 1 := ENNReal.ofReal_one.symm
      _ ≤ ENNReal.ofReal ((Cfail + 2) * CellFamily.mesh k ^ (α / 2)) := by
        apply ENNReal.ofReal_le_ofReal
        nlinarith

end Coupling

end MatedCRTHarmonic.BundleSec4
