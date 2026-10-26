import SupercriticalConformalCovariance.Markov.HGenerated
import LQGMetric.Field.GFFLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric TopologicalSpace

namespace SupercriticalConformalCovariance.Markov

open LQGMetric LQGMetric.MarkovZB LQGMetric.MarkovExt
  QuantumZipper QuantumZipper.K3

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistC} {V : Opens ℂ}

private theorem measurable_ev0 : Measurable (GFFLaw.ev0 : DistC → TestC0 → ℝ) :=
  measurable_pi_iff.2 fun ψ => measurable_distOn_apply ψ.1

/-- The whole-plane GFF definition depends only on the full law of mean-zero pairings. -/
theorem isWholePlaneGFF_of_pairProc_map_eq (hh : IsWholePlaneGFF h P)
    {g : Ω → DistC} (hgm : Measurable g)
    (hlaw : P.map (GFFLaw.pairProc g) = P.map (GFFLaw.pairProc h)) :
    IsWholePlaneGFF g P := by
  let X := GFFLaw.pairProc g
  let Y := GFFLaw.pairProc h
  have hXm : Measurable X := GFFLaw.measurable_pairProc hgm
  have hYm : Measurable Y := GFFLaw.measurable_pairProc hh.measurable
  have hlaw' : P.map X = P.map Y := hlaw
  have hg : IsGaussianProcess (fun (ψ : TestC0) (ω : Ω) => g ω ψ.1) P := by
    refine ⟨fun I => ?_⟩
    have hvec : P.map (fun ω (i : I) => g ω i.1.1) =
        P.map (fun ω (i : I) => h ω i.1.1) := by
      change P.map (I.restrict ∘ X) = P.map (I.restrict ∘ Y)
      rw [← Measure.map_map (Finset.measurable_restrict I) hXm,
        ← Measure.map_map (Finset.measurable_restrict I) hYm, hlaw']
    haveI : IsGaussian (P.map (fun ω (i : I) => h ω i.1.1)) :=
      (hh.gaussian.hasGaussianLaw I).isGaussian_map
    exact (show HasLaw (fun ω (i : I) => g ω i.1.1)
      (P.map (fun ω (i : I) => h ω i.1.1)) P from
        ⟨(measurable_pi_iff.2 fun (i : I) =>
          (measurable_distOn_apply i.1.1).comp hgm).aemeasurable, hvec⟩).hasGaussianLaw
  have hcoord (ψ : TestC0) :
      P.map (fun ω => g ω ψ.1) = P.map (fun ω => h ω ψ.1) := by
    change P.map ((fun x : TestC0 → ℝ => x ψ) ∘ X) =
      P.map ((fun x : TestC0 → ℝ => x ψ) ∘ Y)
    rw [← Measure.map_map (measurable_pi_apply ψ) hXm,
      ← Measure.map_map (measurable_pi_apply ψ) hYm, hlaw']
  refine ⟨hgm, hg, ?_, ?_⟩
  · intro ψ
    calc
      ∫ ω, g ω ψ.1 ∂P = ∫ x : ℝ, x ∂(P.map (fun ω => g ω ψ.1)) := by
        simpa only [Function.comp_def, id_eq] using
          (integral_map ((measurable_distOn_apply ψ.1).comp hgm).aemeasurable
            aestronglyMeasurable_id).symm
      _ = ∫ x : ℝ, x ∂(P.map (fun ω => h ω ψ.1)) := by rw [hcoord ψ]
      _ = ∫ ω, h ω ψ.1 ∂P := by
        simpa only [Function.comp_def, id_eq] using
          (integral_map ((measurable_distOn_apply ψ.1).comp hh.measurable).aemeasurable
            aestronglyMeasurable_id)
      _ = 0 := hh.centered ψ
  · intro ψ χ
    calc
      cov[fun ω => g ω ψ.1, fun ω => g ω χ.1; P] =
          cov[(fun x : TestC0 → ℝ => x ψ), (fun x : TestC0 → ℝ => x χ); P.map X] := by
            rw [covariance_map (measurable_pi_apply ψ).aestronglyMeasurable
              (measurable_pi_apply χ).aestronglyMeasurable hXm.aemeasurable]
            rfl
      _ = cov[(fun x : TestC0 → ℝ => x ψ), (fun x : TestC0 → ℝ => x χ); P.map Y] :=
        by rw [hlaw']
      _ = cov[fun ω => h ω ψ.1, fun ω => h ω χ.1; P] := by
        rw [covariance_map (measurable_pi_apply ψ).aestronglyMeasurable
          (measurable_pi_apply χ).aestronglyMeasurable hYm.aemeasurable]
        rfl
      _ = logCov ψ.1 χ.1 := hh.covariance_eq ψ χ

/-- Replacing the canonical zero-boundary extension by an independent copy with the
same full distribution law preserves the whole-plane GFF law modulo constants. -/
theorem replace_zbExt_general (hh : IsWholePlaneGFF h P)
    (hV : ZBAdmissible V) {hz Z : Ω → DistC}
    (hzm : Measurable hz)
    (hzae : ∀ φ : TestC, (fun ω => hz ω φ) =ᵐ[P] zbExt hh V φ)
    (hZm : Measurable Z) (hZlaw : P.map Z = P.map hz)
    (hZind : IndepFun Z h P) :
    IsWholePlaneGFF (fun ω => h ω - hz ω + Z ω) P := by
  let C : Ω → TestC0 → ℝ := fun ω ψ => h ω ψ.1 - hz ω ψ.1
  let E : Ω → TestC0 → ℝ := GFFLaw.ev0 ∘ hz
  let E' : Ω → TestC0 → ℝ := GFFLaw.ev0 ∘ Z
  have hCm : Measurable C := measurable_pi_iff.2 fun ψ =>
    ((measurable_distOn_apply ψ.1).comp hh.measurable).sub
      ((measurable_distOn_apply ψ.1).comp hzm)
  have hEm : Measurable E := measurable_ev0.comp hzm
  have hE'm : Measurable E' := measurable_ev0.comp hZm
  have hIndCE : IndepFun C E P := by
    have hi := indepFun_zbExt_complement_meanZero hh hV
    have hi' : IndepFun E C P := by
      apply hi.process_congr
      · intro ψ
        exact (hzae ψ.1).symm
      · intro ψ
        filter_upwards [hzae ψ.1] with ω he
        change h ω ψ.1 - zbExt hh V ψ.1 ω = h ω ψ.1 - hz ω ψ.1
        rw [← he]
    exact hi'.symm
  have hIndCE' : IndepFun C E' P := by
    have hi := indepFun_external_complement hh hV hzae hZm hZind
    have hi' : IndepFun E' C P := by
      simpa only [Function.comp_def, id_eq, E', C, GFFLaw.ev0] using
        hi.comp measurable_ev0 measurable_id
    exact hi'.symm
  have hElaw : P.map E' = P.map E := by
    change P.map (GFFLaw.ev0 ∘ Z) = P.map (GFFLaw.ev0 ∘ hz)
    rw [← Measure.map_map measurable_ev0 hZm,
      ← Measure.map_map measurable_ev0 hzm, hZlaw]
  have hPairLaw : P.map (fun ω => (C ω, E' ω)) =
      P.map (fun ω => (C ω, E ω)) := by
    rw [hIndCE'.map_prod_eq_prod_map_map hCm.aemeasurable hE'm.aemeasurable,
      hIndCE.map_prod_eq_prod_map_map hCm.aemeasurable hEm.aemeasurable,
      hElaw]
  let plus : (TestC0 → ℝ) × (TestC0 → ℝ) → TestC0 → ℝ :=
    fun p ψ => p.1 ψ + p.2 ψ
  have hplus : Measurable plus := measurable_pi_iff.2 fun ψ =>
    ((measurable_pi_apply ψ).comp measurable_fst).add
      ((measurable_pi_apply ψ).comp measurable_snd)
  have hsumlaw : P.map (fun ω => plus (C ω, E' ω)) =
      P.map (fun ω => plus (C ω, E ω)) := by
    change P.map (plus ∘ fun ω => (C ω, E' ω)) =
      P.map (plus ∘ fun ω => (C ω, E ω))
    rw [← Measure.map_map hplus (hCm.prodMk hE'm),
      ← Measure.map_map hplus (hCm.prodMk hEm), hPairLaw]
  have hrep : GFFLaw.pairProc (fun ω => h ω - hz ω + Z ω) =
      (fun ω => plus (C ω, E' ω)) := by
    funext ω ψ
    simp only [GFFLaw.pairProc, plus, C, E', GFFLaw.ev0,
      Function.comp_def, sub_apply, add_apply]
  have hold : GFFLaw.pairProc h = (fun ω => plus (C ω, E ω)) := by
    funext ω ψ
    simp only [GFFLaw.pairProc, plus, C, E, GFFLaw.ev0,
      Function.comp_def]
    ring
  have hrepM : Measurable (fun ω => h ω - hz ω + Z ω) :=
    measurable_distOn_iff.2 fun φ =>
      (((measurable_distOn_apply φ).comp hh.measurable).sub
        ((measurable_distOn_apply φ).comp hzm)).add
        ((measurable_distOn_apply φ).comp hZm)
  apply isWholePlaneGFF_of_pairProc_map_eq hh hrepM
  rw [hrep, hold]
  exact hsumlaw

end SupercriticalConformalCovariance.Markov
