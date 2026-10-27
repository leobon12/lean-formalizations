/- Provenance: ported from an earlier mating-of-trees formalization; only imports and namespace names were changed. -/
import MatedCRTHarmonic.MoTPort.IG.GFF.AbsContCore

/-!
# Markov decomposition of a zero-boundary GFF on a subdomain (task IGR-2a, part 3)

IG1 (arXiv:1201.1496) Prop. 3.1 (`gff::prop::markov`), in the form used in the proof of
Prop. 3.4 (l. 1261): for `Ũ ⊆ D`, the zero-boundary GFF `h` on `D` restricted to `Ũ` is
`h^Ũ + K` with `h^Ũ` a zero-boundary GFF on `Ũ` and `K` harmonic on `Ũ`, independent of `h^Ũ`.

`exists_zb_markov` builds such a triple on one probability space, for every open `D` disjoint
from some circle `∂B_ρ(z₀)`: from a whole-plane GFF `h` normalized by `h_ρ(z₀) = 0`, the
whole-plane Markov property (LQGMetric `DFGPS.markov_normAt`, i.e. LM Lemma 2.1 =
GMSh arXiv:1807.07511 Lemma 2.2 at a general circle; `MarkovFinal.lmLem2_1`) gives
`h = 𝔥_D + h̊_D` and `h = 𝔥_Ũ + h̊_Ũ`; then `h̊_D|_Ũ = h̊_Ũ|_Ũ + (𝔥_Ũ − 𝔥_D)|_Ũ`, where `𝔥_Ũ` and
`𝔥_D` are measurable for `σ(h|_{ℂ∖Ũ})` (`σ(h|_{ℂ∖D}) ⊆ σ(h|_{ℂ∖Ũ})`, `fieldSigmaClosed_mono`)
and hence independent of `h̊_Ũ` (Berestycki–Powell arXiv:2404.16642 Thm 1.52 proof: the
nested decomposition `H₀¹(D) = H₀¹(Ũ) ⊕ Harm`). The law of `h̊_D` is that of every zero-boundary
GFF on `D` (LQGMetric `IsZeroBoundaryGFF.map_eq`). Own assembly of these sourced facts.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set TopologicalSpace Metric Filter Topology
open scoped ENNReal

namespace MatedCRTHarmonic.MoTPort.IG.GFFAbsCont

open LQGMetric QuantumZipper Blueprint

lemma resOn_resOn {U W D : Opens ℂ} (hUW : U ≤ W) (hWD : W ≤ D) (k : DistOn D) :
    resOn U W (resOn W D k) = resOn U D k := by
  refine DFunLike.ext _ _ fun φ => ?_
  simp only [resOn_apply]
  congr 1
  ext x
  simp [GM.coe_testIncl hUW, GM.coe_testIncl hWD, GM.coe_testIncl (hUW.trans hWD)]

lemma resOn_add (U D : Opens ℂ) (a b : DistOn D) :
    resOn U D (a + b) = resOn U D a + resOn U D b := rfl

lemma fieldSigma_mono {Ω : Type} [MeasurableSpace Ω] (h : Ω → DistC) {V W : Opens ℂ}
    (hVW : V ≤ W) : fieldSigma h V ≤ fieldSigma h W := by
  have e : (fun ω => restrictTo V (h ω)) = resOn V W ∘ fun ω => restrictTo W (h ω) := by
    funext ω; exact (resOn_restrictTo hVW (h ω)).symm
  change MeasurableSpace.comap _ _ ≤ MeasurableSpace.comap _ _
  rw [e, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono (measurable_resOn V W).comap_le

lemma fieldSigmaClosed_mono {Ω : Type} [MeasurableSpace Ω] (h : Ω → DistC) {K K' : Set ℂ}
    (hK : K ⊆ K') : fieldSigmaClosed h K ≤ fieldSigmaClosed h K' :=
  iInf₂_mono fun ε _ => fieldSigma_mono h (fun x hx => thickening_subset_of_subset ε hK hx)

/-- **Markov decomposition of the zero-boundary GFF on `D` on a subdomain `Ũ`** (IG1 Prop. 3.1 as
used in the proof of Prop. 3.4), for `D` disjoint from a circle. -/
theorem exists_zb_markov {D W : Opens ℂ} (hWD : W ≤ D) {z₀ : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hD : Disjoint (D : Set ℂ) (sphere z₀ ρ)) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (Y : Ω → DistOn D) (Z K : Ω → DistOn W),
      IsProbabilityMeasure P ∧ IsZeroBoundaryGFF D Y P ∧ IsZeroBoundaryGFF W Z P ∧
      Measurable K ∧ IndepFun Z K P ∧ (∀ᵐ ω ∂P, IsHarmRep W (K ω)) ∧
      ∀ᵐ ω ∂P, resOn W D (Y ω) = Z ω + K ω := by
  obtain ⟨Ω, _, P, g, hP, hg⟩ := GFFExist.exists_wholePlaneGFF
  have := hP
  set h : Ω → Field := fun ω => addConst (g ω) (-circleAvg (g ω) ρ z₀)
  have hh : IsWholePlaneGFF h P :=
    IsWholePlaneGFF.addConst hg ((measurable_circleAvg_left ρ z₀).comp hg.measurable).neg
  have hn : ∀ᵐ ω ∂P, circleAvg (h ω) ρ z₀ = 0 := by
    filter_upwards [CircleAvg.ae_tendsto_mollAvg hg z₀ hρ] with ω ⟨a, ha⟩
    rw [CircleAvg.circleAvg_addConst_of_tendsto ha, add_neg_cancel]
  have hW : Disjoint (W : Set ℂ) (sphere z₀ ρ) := hD.mono_left hWD
  obtain ⟨hhD, hzD, hdecD, hharmD, ⟨GD, hGDm, hGD⟩, -, hzbD, -, -⟩ :=
    DFGPS.markov_normAt MarkovFinal.lmLem2_1 P h hh hρ z₀ hn D hD
  obtain ⟨hhW, hzW, hdecW, hharmW, ⟨GW, hGWm, hGW⟩, -, hzbW, -, hindW⟩ :=
    DFGPS.markov_normAt MarkovFinal.lmLem2_1 P h hh hρ z₀ hn W hW
  have hle : fieldSigmaClosed h (W : Set ℂ)ᶜ ≤ ‹MeasurableSpace Ω› :=
    MarkovZBIndep.fieldSigmaClosed_le hh _
  have hDW : fieldSigmaClosed h (D : Set ℂ)ᶜ ≤ fieldSigmaClosed h (W : Set ℂ)ᶜ :=
    fieldSigmaClosed_mono h (compl_subset_compl.2 hWD)
  have hKm' : Measurable[fieldSigmaClosed h (W : Set ℂ)ᶜ] fun ω => restrictTo W (GW ω - GD ω) :=
    (measurable_restrictTo W).comp (GFFBdry.measurable_sub hGWm (hGDm.mono hDW le_rfl))
  refine ⟨Ω, inferInstance, P, fun ω => restrictTo D (hzD ω), fun ω => restrictTo W (hzW ω),
    fun ω => restrictTo W (GW ω - GD ω), hP, hzbD, hzbW, hKm'.mono hle le_rfl, ?_, ?_, ?_⟩
  · -- independence
    rw [IndepFun_iff_Indep]
    refine indep_of_indep_of_le_right (indep_of_indep_of_le_left hindW ?_) hKm'.comap_le
    exact ((measurable_restrictTo W).comp (comap_measurable hzW)).comap_le
  · -- harmonic
    filter_upwards [hharmD, hharmW, hGD, hGW] with ω ⟨gD, hgD, hrD⟩ ⟨gW, hgW, hrW⟩ e1 e2
    refine ⟨fun x => gW x - gD x, hgW.sub (hgD.mono hWD), fun φ => ?_⟩
    rw [GFFBdry.restrictTo_sub, ← e1, ← e2, sub_apply, hrW,
      GM.restrictTo_apply_testIncl hWD, hrD, ← integral_sub]
    · congr 1; funext x; rw [GM.coe_testIncl hWD]; ring
    · exact integrable_mul_test (contDiffOn_of_harmonicOnNhd hgW) φ
    · rw [GM.coe_testIncl hWD]
      exact integrable_mul_test ((contDiffOn_of_harmonicOnNhd hgD).mono hWD) φ
  · filter_upwards [hGD, hGW] with ω e1 e2
    rw [resOn_restrictTo hWD, ← e1, ← e2]
    have h1 := hdecD ω
    have h2 := hdecW ω
    have : hzD ω = hhW ω + hzW ω - hhD ω := by rw [← h2, h1]; abel
    rw [this, GFFBdry.restrictTo_sub, GFFBdry.restrictTo_add, GFFBdry.restrictTo_sub]
    abel

end MatedCRTHarmonic.MoTPort.IG.GFFAbsCont
