import QuantumZipper.Proofs.LQG.WedgeCReg
import QuantumZipper.Proofs.LQG.WedgeCRegCont
import QuantumZipper.Proofs.Section5.Prop17RawLaw

/-!
# B4(d) without the all-test-function continuum statement

`F1.wedgeRefReflectStmt_of` (`F1B4dPath`) derives B4(d) (`F1.WedgeRefReflectStmt γ α`, a
statement about **laws**) from the pathwise identity `WedgeReflPathStmt`, which needs the
continuum limits `WedgeContPairStmt` almost surely for **all** test functions at once. A law on
`(ℕ → ℝ) × (TestFun H → ℝ)` is determined by its finite-dimensional marginals, so it suffices to
have the identity of the data coordinate by coordinate, almost surely for each test function
(`S5.FieldLaw.Raw.map_prod_eq_of_ae`). This file does that:

* `coordsFull_reflectH_canonical`, `pairRaw_reflectH_canonical`: the deterministic identity of
  `F1.B4d.dataH_reflectH_canonical`, split by coordinate (the pairing at `ρ` only needs the
  continuum limits at `ρ`);
* `dataH_reflectH_eq_psi`: `dataH (reflectH y)` is a measurable function of `coordsFull y`, which
  gives the a.e.-measurability of the reflected data;
* `wedgeRefReflectStmt_holds`: **B4(d)** from `WedgeInfiniteTotal` alone, with the lateral input
  `WedgeCReg.wedgeLatReflRegStmt_holds` and the per-test-function continuum limits
  `WedgeCReg.ae_contPair_wedgeRef`.

Own elementary argument (bookkeeping; the analytic inputs are cited in `WedgeCReg`,
`WedgeCRegCont`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ComplexConjugate

namespace QuantumZipper
namespace WedgeCReg

open Factorization CoordsFull

/-! ## 1. The deterministic identity, coordinate by coordinate -/

theorem reflectH_rescale_dens' {x : FieldSample} {F : ℂ × ℝ → ℝ} (h : IsRegularWith x F)
    (Q : ℝ) {b : ℝ} (hb : 0 < b) {f : ℂ → ℝ} (hfc : Continuous f) (hfs : HasCompactSupport f)
    (hfH : tsupport f ⊆ H) {L : ℝ}
    (hL : Tendsto (fun r => ∫ u, evalReg x (foldedCircle ((b : ℂ) * -conj u) r)
      ∂(volume.withDensity fun z => ENNReal.ofReal (f z))) (𝓝[>] 0) (𝓝 L)) :
    RegClosure.reflectH (rescale x Q b) (volume.withDensity fun z => ENNReal.ofReal (f z)) =
      rescale (RegClosure.reflectH x) Q b (volume.withDensity fun z => ENNReal.ofReal (f z)) := by
  obtain ⟨hfin, hae⟩ := F1.B4d.withDensity_facts hfc hfs
  exact F1.B4d.reflectH_rescale_eq_of_lim h.congr_evalReg Q hb _ hfs
    (hfH.trans F1.B4d.H_subset_Hbar) hae hL

/-- The continuum limits of `ContPair` at one test function. -/
def ContPairAt (x : FieldSample) (b : ℝ) (ρ : TestFun H) : Prop :=
  ∀ f ∈ ({ρ.1, -ρ.1} : Set (ℂ → ℝ)), ∃ L : ℝ,
    Tendsto (fun r => ∫ u, evalReg x (foldedCircle ((b : ℂ) * -conj u) r)
      ∂(volume.withDensity fun z => ENNReal.ofReal (f z))) (𝓝[>] 0) (𝓝 L)

theorem coordsFull_reflectH_canonical {γ : ℝ} {x : FieldSample} (hx : IsLQGGood γ x)
    (hs : 0 < scaleParam γ x) :
    coordsFull (RegClosure.reflectH (canonical γ x)) =
      coordsFull (canonical γ (RegClosure.reflectH x)) := by
  obtain ⟨F, hF⟩ := hx.1
  have hc' : canonical γ (RegClosure.reflectH x) =
      rescale (RegClosure.reflectH x) (Qc γ) (scaleParam γ x) := by
    rw [canonical, F1.B4d.scaleParam_reflectH hx]
  rw [show canonical γ x = rescale x (Qc γ) (scaleParam γ x) from rfl, hc']
  funext i
  exact F1.B4d.reflectH_rescale_fc hF _ hs _ (WedgeTK.fullIndex_pos i)

theorem pairRaw_reflectH_canonical {γ : ℝ} {x : FieldSample} (hx : IsLQGGood γ x)
    (hs : 0 < scaleParam γ x) (ρ : TestFun H) (hc : ContPairAt x (scaleParam γ x) ρ) :
    pairRaw (RegClosure.reflectH (canonical γ x)) ρ.1 =
      pairRaw (canonical γ (RegClosure.reflectH x)) ρ.1 := by
  obtain ⟨F, hF⟩ := hx.1
  have hc' : canonical γ (RegClosure.reflectH x) =
      rescale (RegClosure.reflectH x) (Qc γ) (scaleParam γ x) := by
    rw [canonical, F1.B4d.scaleParam_reflectH hx]
  rw [show canonical γ x = rescale x (Qc γ) (scaleParam γ x) from rfl, hc']
  obtain ⟨hρs, hρc, hρH⟩ := ρ.2
  obtain ⟨L1, h1⟩ := hc ρ.1 (Set.mem_insert _ _)
  obtain ⟨L2, h2⟩ := hc (fun z => -ρ.1 z) (Set.mem_insert_of_mem _ rfl)
  unfold pairRaw
  rw [reflectH_rescale_dens' hF _ hs hρs.continuous hρc hρH h1,
    reflectH_rescale_dens' hF _ hs (f := fun z => -ρ.1 z) hρs.continuous.neg hρc.neg
      (by rw [show (fun z => -ρ.1 z) = -ρ.1 from rfl, tsupport_neg]; exact hρH) h2]

/-! ## 2. Measurability of the reflected data -/

/-- The data of the reflection, read off the full circle coordinates. -/
def psiR (c : ℕ → ℝ) : (ℕ → ℝ) × (TestFun H → ℝ) :=
  WedgeMeas.dataFull H (RegClosure.reflectH (reconstruct (S5.FieldLaw.proj c)))

theorem measurable_psiR : Measurable psiR := by
  have hr : Measurable fun c : ℕ → ℝ => reconstruct (S5.FieldLaw.proj c) :=
    measurable_reconstruct.comp S5.FieldLaw.measurable_proj
  have hE : ∀ (ν : Measure ℂ) [SFinite ν],
      Measurable fun c : ℕ → ℝ => RegClosure.reflectH (reconstruct (S5.FieldLaw.proj c)) ν :=
    fun ν _ => (measurable_evalReg _).comp hr
  unfold psiR WedgeMeas.dataFull
  exact (measurable_pi_iff.2 fun i => hE _).prodMk
    (measurable_pi_iff.2 fun ρ => (hE _).sub (hE _))

theorem reflectH_reconstruct (y : FieldSample) :
    RegClosure.reflectH y = RegClosure.reflectH (reconstruct (S5.FieldLaw.proj (coordsFull y))) := by
  rw [← S5.FieldLaw.coords_eq_proj]
  funext μ
  unfold RegClosure.reflectH evalReg
  rw [avgReg_reconstruct_coords]

theorem dataH_reflectH_eq_psi (y : FieldSample) :
    F1.dataH (RegClosure.reflectH y) = psiR (coordsFull y) := by
  unfold psiR
  rw [← reflectH_reconstruct]

/-! ## 3. B4(d) -/

/-- **B4(d) for the reference wedge** (`F1.WedgeRefReflectStmt`), from `WedgeInfiniteTotal`
only: neither `F1.WedgeLatReflRegStmt` (proved in `WedgeCReg`) nor the all-test-function
`F1.WedgeContPairStmt` is needed as a hypothesis. -/
theorem wedgeRefReflectStmt_holds {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < Qc γ)
    (hinf : WedgeCan4.WedgeInfiniteTotal γ α) : F1.WedgeRefReflectStmt γ α := by
  intro Ω' _ P' X A hP hX hA hI
  have hg := LogSingGood.wedgeRefGoodAS_holds hγ hγ2 hα Ω' _ P' X A hP hX hA hI
  have hD := WedgeMeas.aemeasurable_wedgeRefData hX hA hg H
  refine ⟨hD, ?_⟩
  have h1c := F1.B4d.aemeasurable_coords_wedgeField_reflect hX hA
  have h2c := WedgeMeas.aemeasurable_coords_wedgeField hX.measurable_coord hA
  have hlaw := F1.B4d.map_coords_wedgeField_reflect hX hA hI
  have hg' := F1.B4d.ae_good_of_map_coords_eq h1c h2c hlaw hg
  have hgD := WedgeMeas.aemeasurable_dataFull_canonical h1c hg' H
  have hfD : AEMeasurable (fun ω => F1.dataH (RegClosure.reflectH
      (canonical γ (wedgeField (lateralPart (X ω)) (fun t => A t ω) (Qc γ))))) P' := by
    have := measurable_psiR.comp_aemeasurable (measurable_fst.comp_aemeasurable hD)
    refine this.congr (ae_of_all _ fun ω => ?_)
    simp only [Function.comp_apply]
    rw [dataH_reflectH_eq_psi]
    rfl
  have hreg := wedgeLatReflRegStmt_holds hγ hγ2 hα Ω' P' X A hP hX hA hI
  have hspec := WedgeCan4.ae_wedge_canonical_spec_of_inputs
    (WedgeFinZero.wedgeFiniteNearZero_holds hγ hγ2 hα) hinf hγ hγ2 hα hX hA hI
  have key : P'.map (fun ω => F1.dataH (RegClosure.reflectH
      (canonical γ (wedgeField (lateralPart (X ω)) (fun t => A t ω) (Qc γ))))) =
      P'.map (fun ω => WedgeMeas.dataFull H (canonical γ
        (wedgeField (lateralPart (RegClosure.reflectH (X ω))) (fun t => A t ω) (Qc γ)))) := by
    refine S5.FieldLaw.Raw.map_prod_eq_of_ae hfD hgD ?_ fun ρ => ?_
    · filter_upwards [hreg, hspec, hg] with ω h1 h3 h4
      simp only [F1.dataH, WedgeMeas.dataFull]
      rw [coordsFull_reflectH_canonical h4 h3.1, Factorization.canonical_congr h1.symm]
    · filter_upwards [hreg, hspec, hg, ae_contPair_wedgeRef hX hA ρ] with ω h1 h3 h4 h5
      simp only [F1.dataH, WedgeMeas.dataFull]
      rw [pairRaw_reflectH_canonical h4 h3.1 ρ (h5 _ h3.1), Factorization.canonical_congr h1.symm]
  rw [key]
  exact F1.B4d.map_dataFull_canonical_eq h1c h2c hlaw hg

end WedgeCReg
end QuantumZipper
