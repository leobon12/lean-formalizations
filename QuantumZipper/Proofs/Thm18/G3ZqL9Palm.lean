import QuantumZipper.Proofs.Thm18.G2PalmIdCore
import QuantumZipper.Proofs.Thm18.G3PalmRBasic
import QuantumZipper.Proofs.Thm18.G3Pl2Meas
import QuantumZipper.Proofs.Thm18.G4CMeas4Good
import QuantumZipper.Proofs.Section5.Prop17PalmABRep
import QuantumZipper.Proofs.Section5.Prop17PalmZoomReg

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G3PATH-LOC (9): transfer of null events from the Palm fields to `ν_h`-typical points

Duplantier–Sheffield, arXiv:0808.1560, §3.3 (the rooted measure), in the form
`E ∫ φ(h, x) ν_h(dx) = ∫ ρ(x) E φ(h + ψ_x, x) dx` (`pid_palm`, Palm formula of `PalmNorm`).
If an event of the dyadic coordinates of the field and the point `x` is null for the Palm field
`normField γ (xPalm γ x)` at Lebesgue-a.e. `x ∈ (a, b) ⊆ [−1, 1]`, then a.s. it fails for the
free field at `ν_h`-a.e. `x ∈ (a, b)` (`ae_hν_of_palm_null`). This is how a statement proved at a
fixed Palm point (Sheffield, arXiv:1012.4797, proof of Prop. 5.5, p. 65: "once we condition on
`x` …") becomes a statement at quantum-typical points. Own bookkeeping, following
`ae_pidFine_palm` (G2PalmIdCore).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace Thm18Asm

local notation "Ω₀" => gffBase.Ω
local notation "X₀" => gffBase.X

namespace G3ZqL

open Factorization

/-- **Palm null transfer.** -/
theorem ae_hν_of_palm_null {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {E : Set ((ℕ → ℝ) × ℝ)}
    (hE : MeasurableSet E) {a b : ℝ} (hab : Icc a b ⊆ Icc (-((1 : ℕ) : ℝ)) ((1 : ℕ) : ℝ))
    (hP : ∀ᵐ x ∂(volume.restrict (Ioo a b)), ∀ᵐ ω ∂gffBase.P,
      (coords (normField γ (xPalm γ x) ω), x) ∉ E) :
    ∀ᵐ ω ∂gffBase.P, ∀ᵐ x ∂((g3Hν γ ω).restrict (Ioo a b)),
      (coords (normField γ X₀ ω), x) ∉ E := by
  set A : ℕ → Measure ℂ := fun _ => refS with hA
  have hAa : ∀ n, IsAdmissibleH (A n) := fun _ => isAdmissibleH_refS
  set Eb : Set ((ℕ → ℝ) × ℝ) := {p | (pidDN γ p.1, p.2) ∈ E} with hEb
  have hEbm : MeasurableSet Eb :=
    (((measurable_pidDN γ).comp measurable_fst).prodMk measurable_snd) hE
  set φ : (ℕ → ℝ) → ℝ → ℝ≥0∞ := fun c x => Eb.indicator 1 (c, x) with hφdef
  have hφ : Measurable (Function.uncurry φ) := measurable_one.indicator hEbm
  have hc : ∀ V : FieldSample, pidDN γ (pidC A A V) = coords (pidNf γ V) := fun V =>
    (coords_pidNf γ A A V).symm
  have H := pid_palm hγ hγ2 hAa hAa hab hφ
  have hR : ∫⁻ x in Ioo a b, ENNReal.ofReal (PalmNorm.rhoNorm γ 0 refS x) *
      ∫⁻ ω, φ (pidC A A (xPalm γ x ω)) x ∂gffBase.P = 0 := by
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    filter_upwards [hP] with x hx
    have h0 : ∫⁻ ω, φ (pidC A A (xPalm γ x ω)) x ∂gffBase.P = 0 := by
      refine (lintegral_congr_ae ?_).trans lintegral_zero
      filter_upwards [hx] with ω hω
      have hn : (pidC A A (xPalm γ x ω), x) ∉ Eb := by
        simp only [hEb, mem_setOf_eq, hc]
        exact hω
      simp only [hφdef, indicator_of_notMem hn, Pi.zero_apply]
    rw [h0, mul_zero]
  rw [hR] at H
  set F' : Ω₀ → ℝ≥0∞ := fun ω => ∫⁻ x, (Ioo a b).indicator (φ (pidC A A (X₀ ω))) x
      ∂(bdryM γ (S5.FieldLaw.Raw.freeFieldN refS X₀ ω)) with hF'
  have hmF' : Measurable F' := by
    have hν : Measurable fun ω => bdryM γ (S5.FieldLaw.Raw.freeFieldN refS X₀ ω) :=
      (measurable_bdryM γ).comp (S5.FieldLaw.Raw.measurable_freeFieldN gffBase.gff refS)
    have hmc : Measurable fun ω => pidC A A (X₀ ω) := measurable_pidC_free A A
    exact R18.measurable_lintegral_family (H := fun q : Ω₀ × ℝ =>
      (Ioo a b).indicator (φ (pidC A A (X₀ q.1))) q.2) hν
      (fun ω N => R18.bdryM_Icc_ne_top γ _ _ _) <| (hφ.comp ((hmc.comp measurable_fst).prodMk measurable_snd)).indicator
      (measurableSet_Ioo.preimage measurable_snd)
  have hFF : (fun ω => ∫⁻ x in Ioo a b, φ (pidC A A (X₀ ω)) x ∂(g3Zν γ ω)) =ᵐ[gffBase.P] F' := by
    filter_upwards [S5.FieldLaw.Raw.ae_freeFieldN_bdry gffBase.gff hγ hγ2 refS] with ω hω
    simp only [hF', bdryM, if_pos (G4Core.bCert_of_isLQGGood hω.1)]
    rw [lintegral_indicator measurableSet_Ioo]
  have hmL : AEMeasurable (fun ω => ∫⁻ x in Ioo a b, φ (pidC A A (X₀ ω)) x ∂(g3Zν γ ω))
      gffBase.P := hmF'.aemeasurable.congr hFF.symm
  filter_upwards [(lintegral_eq_zero_iff' hmL).1 H, ae_g3Hν_eq hγ hγ2] with ω hω hH
  have hZ : ∀ᵐ x ∂((g3Zν γ ω).restrict (Ioo a b)), φ (pidC A A (X₀ ω)) x = 0 :=
    (lintegral_eq_zero_iff (hφ.comp (measurable_const.prodMk measurable_id))).1 hω
  have hac : (g3Hν γ ω).restrict (Ioo a b) ≪ (g3Zν γ ω).restrict (Ioo a b) := by
    rw [hH]
    refine Measure.AbsolutelyContinuous.restrict ?_ _
    exact (withDensity_absolutelyContinuous _ _).trans
      (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
  filter_upwards [hac.ae_le hZ] with x hx
  intro hmem
  have hin : (pidC A A (X₀ ω), x) ∈ Eb := by
    simp only [hEb, mem_setOf_eq, hc]
    exact hmem
  simp [hφdef, indicator_of_mem hin] at hx

end G3ZqL
end Thm18Asm
end QuantumZipper
