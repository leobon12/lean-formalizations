/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61FibKGen
import InteractingSLE.Spec.Restart.DomainMarkovTransfer
import InteractingSLE.Spec.Coupling.MartMeans2Rand
import InteractingSLE.Spec.Coupling.WholeField2Kernel
import InteractingSLE.Spec.Sec7.LocalExtA3Joint

/-!
# Countably many identities give the fibre kernel at the dyadic times

Packet PROVE-AUX61-FIB2. `FibKernelRaw d P` quantifies over every cutoff, every reference extension and every test
function. Only countably many identities pass from the glued space to almost every fibre. This file reduces
`FibKernelRaw` to the identities for **one** cutoff `(F₀, N₀)`, the **canonical** reference extension `canonExt d` and
the countably many tests `ratTest p`:

* `integrableOn_greenPot_closedBall`, **`locallyIntegrableOn_meanF`**: the explicit mean is locally integrable off the
  hull (its Green-potential term through the cross-kernel integrability with a ball indicator);
* `canonExt`, `refExt_canonExt`, **`integral_meanF_congr_ext`** (two reference extensions give the same mean off the
  hull: uniqueness of the bounded harmonic extension);
* **`fibKernelRaw_of_rat`**: the identities for `ratTest p` at the dyadic times give `FibKernelRaw` (local Gaussian
  laws and the landed `DomainMarkov.condExp_cexp_ae_eq_of_local_countable`, then the extension and the cutoff).

Conditional helpers with distinct names; they replace no source theorem. R48: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param` result; R77: no post-contact kernel.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61FibK

open QuantumZipper (H fwdHull greenH fwdMap)
open LQGMetric (TestOn DistOn)
open LocalExt (cfVal IsGreenTest)
open Restart.FlowStopIdentCMI (CMCut)
open Aux61Win (meanF IsCutoffOn)
open Aux61R2 (RefExt)
open Aux61Fib (FibCode FibData PathGood fibW fibΓ fibU fibField)
open Sec7.PocketTraversal

universe u

/-! ### Local integrability of the explicit mean -/

/-- **The Green-potential term is integrable on a closed ball off the hull.** -/
theorem integrableOn_greenPot_closedBall {w : ℝ → ℝ} (hw : Continuous w) {t : ℝ} (ht : 0 ≤ t) {F : CMCut}
    (hF : IsGreenTest w t F.src) {x : ℂ} {δ : ℝ} (hB : closedBall x δ ⊆ H \ fwdHull w t) :
    IntegrableOn (GB7a.greenPot w (H.indicator (QuantumZipper.K3.greenDensity F.f)) t) (closedBall x δ) := by
  set φ : ℂ → ℝ := (closedBall x δ).indicator fun _ => (1 : ℝ) with hφ
  have hφne : ∀ z, φ z ≠ 0 → z ∈ closedBall x δ := fun z hz => by
    by_contra h
    exact hz (indicator_of_notMem h _)
  have hφG : IsGreenTest w t φ :=
    ⟨measurable_const.indicator measurableSet_closedBall, ⟨1, fun z => by
      by_cases hz : z ∈ closedBall x δ
      · simp [hφ, indicator_of_mem hz]
      · simp [hφ, indicator_of_notMem hz]⟩,
      ⟨closedBall x δ, isCompact_closedBall x δ, fun z hz => show (0 : ℝ) ≤ z.im from le_of_lt (hB hz).1, hφne⟩,
      fun z hz => hB (hφne z hz)⟩
  have hI := (LocalExt.integrable_crossKer hw ht hφG hF).integral_prod_left
  have e : (fun y => ∫ z, LocalExt.crossKer w t φ F.src (y, z)) =
      fun y => -((closedBall x δ).indicator
        (GB7a.greenPot w (H.indicator (QuantumZipper.K3.greenDensity F.f)) t) y) := by
    funext y
    have e1 : ∀ z, LocalExt.crossKer w t φ F.src (y, z) = φ y * greenH (fwdMap w t y) (fwdMap w t z) * F.src z :=
      fun z => (LocalExt.crossKer_eq hφG.alive hF.alive y z).symm
    simp only [e1]
    have e2 : (fun z => φ y * greenH (fwdMap w t y) (fwdMap w t z) * F.src z) =
        fun z => -(φ y * (greenH (fwdMap w t y) (fwdMap w t z) *
          H.indicator (QuantumZipper.K3.greenDensity F.f) z)) := by
      funext z
      simp only [CMCut.src]
      ring
    rw [e2, integral_neg, integral_const_mul, ← GB7a.greenPot]
    by_cases hy : y ∈ closedBall x δ
    · simp [hφ, indicator_of_mem hy]
    · simp [hφ, indicator_of_notMem hy]
  rw [e] at hI
  have hI' : Integrable ((closedBall x δ).indicator
      (GB7a.greenPot w (H.indicator (QuantumZipper.K3.greenDensity F.f)) t)) := by
    exact integrable_neg_iff.1 hI
  exact (integrable_indicator_iff measurableSet_closedBall).1 hI'

/-- **The explicit mean is locally integrable off the hull.** -/
theorem locallyIntegrableOn_meanF {κ : ℝ} {u₀ q : ℂ → ℝ} (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hq : ContinuousOn q H) {F : CMCut} {w : ℝ → ℝ} (hw : Continuous w) {t : ℝ} (ht : 0 ≤ t)
    (hF : IsGreenTest w t F.src) {R : Set ℂ} (hRo : IsOpen R) (hR : R ⊆ H \ fwdHull w t) :
    LocallyIntegrableOn (meanF κ u₀ q F w t) R := by
  intro x hx
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hRo x hx
  have hB : closedBall x (δ / 2) ⊆ R := (closedBall_subset_ball (by linarith)).trans hball
  refine ⟨closedBall x (δ / 2), mem_nhdsWithin_of_mem_nhds (closedBall_mem_nhds x (by linarith)), ?_⟩
  have hBH := hB.trans hR
  have hK := isCompact_closedBall x (δ / 2)
  have hu₀c : ContinuousOn u₀ H := fun z hz => (hu₀ z hz).1.continuousAt.continuousWithinAt
  have i₁ : IntegrableOn (couplingMean κ w t u₀) (closedBall x (δ / 2)) :=
    ((LocalExt.continuousOn_couplingMean_alive (κ := κ) hw ht hu₀c).mono hBH).integrableOn_compact hK
  have i₂ := integrableOn_greenPot_closedBall hw ht hF hBH
  have i₃ : IntegrableOn (fun z => q z - F.f z) (closedBall x (δ / 2)) :=
    ((hq.sub F.smooth.continuous.continuousOn).mono (hBH.trans sdiff_subset)).integrableOn_compact hK
  exact (i₁.add i₂).add i₃

/-! ### The canonical reference extension and the uniqueness of extensions -/

/-- **The canonical reference extension of a code fibre**: the bounded harmonic extension process of the reference
word along the decoded driver. -/
def canonExt (d : FibData) : ULift.{u} FibCode → ℝ≥0 → ℂ → ℝ :=
  Restart.DomainMarkov.bheProc d.κ (flowLineRhoL d.κ d.bR d.JR 0 0) (flowLineRhoR d.κ d.bR d.JR 0 0) fibW
    (geomLW fibW fun _ => flowLineXL d.bR d.JR 0) (geomRW fibW fun _ => flowLineXR d.bR d.JR 0)

theorem refExt_canonExt (d : FibData) (ω : ULift.{u} FibCode) (t : ℝ≥0) :
    RefExt d.κ d.bR d.JR fibW t ω (canonExt d ω t) :=
  Restart.DomainMarkov.isBoundedHarmonicExtension_bheProc ω t

/-- **Two reference extensions give the same explicit mean off the hull** (uniqueness of the bounded harmonic
extension off the finite jump set). -/
theorem integral_meanF_congr_ext {κ : ℝ} {bR : ℝ → ℝ} {JR : Finset ℝ} {S : Type*} {W : ℝ≥0 → S → ℝ} {t : ℝ≥0}
    {ω : S} (hWc : Continuous (W · ω)) {u v : ℂ → ℝ} (hu : RefExt κ bR JR W t ω u) (hv : RefExt κ bR JR W t ω v)
    (q : ℂ → ℝ) (F : CMCut) (ψ : TestOn upperHalfPlaneOpens)
    (hψ : Disjoint (tsupport ψ) (fwdHull (Ito.rpath (W · ω)) t)) :
    (∫ z, meanF κ u q F (Ito.rpath (W · ω)) t z * ψ z) = ∫ z, meanF κ v q F (Ito.rpath (W · ω)) t z * ψ z := by
  have hS : (forceJumpSet (fun i => geomLW W (fun _ => flowLineXL bR JR 0) i t ω - W t ω)
      (fun j => geomRW W (fun _ => flowLineXR bR JR 0) j t ω - W t ω)).Finite := by
    unfold forceJumpSet
    exact ((Set.finite_range _).union (Set.finite_range _)).insert 0
  have huv : EqOn v u H := Impl.eqOn_of_isBoundedHarmonicExtension hS hu hv
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  by_cases hz : z ∈ tsupport ψ
  · have hzH : z ∈ H := ψ.tsupport_subset hz
    have hzK : z ∉ fwdHull (Ito.rpath (W · ω)) t := fun h => Set.disjoint_left.1 hψ hz h
    have hg : fwdMap (Ito.rpath (W · ω)) t z ∈ H :=
      QuantumZipper.FwdHolo.mapsTo_fwdMap (hWc.comp continuous_real_toNNReal) t.coe_nonneg ⟨hzH, hzK⟩
    simp only [meanF, couplingMean]
    rw [huv hg]
  · simp [image_eq_zero_of_notMem_tsupport hz]

/-! ### Countably many identities give `FibKernelRaw` -/

/-- **The fibre kernel at the dyadic times from countably many identities**: for a law with the path facts, the
identities for one cutoff `(F₀, N₀)`, the canonical extension and the tests `ratTest p` give `FibKernelRaw` (every
cutoff, every reference extension, every test). -/
theorem fibKernelRaw_of_rat (d : FibData) (P : Measure (ULift.{u} FibCode)) [IsProbabilityMeasure P]
    (hgood : ∀ᵐ s ∂P, PathGood d s.down) {F₀ : CMCut} {N₀ : Set ℂ} (hF₀ : IsCutoffOn F₀ d.q N₀ d.O₀)
    (hbN₀ : d.buffer ⊆ N₀)
    (hrat : ∀ (n k : ℕ) (p : Restart.DomainMarkov.RatIdx), ∀ᵐ ω ∂P,
      ((Restart.DomainMarkov.dyT n k : ℝ≥0) : ℝ≥0∞) < fibU ω →
      Disjoint (tsupport (Restart.DomainMarkov.ratTest upperHalfPlaneOpens p))
        (fwdHull (Ito.rpath (fibW · ω)) (Restart.DomainMarkov.dyT n k : ℝ≥0)) →
      P[fun ω' => Complex.exp (Complex.I * (fibField ω' (Restart.DomainMarkov.ratTest upperHalfPlaneOpens p) : ℂ)) |
          Ito.nullAugmented codeFiltration.{u} P (Restart.DomainMarkov.dyT n k)] ω =
        cfVal (∫ z, meanF d.κ (canonExt d ω (Restart.DomainMarkov.dyT n k)) d.q F₀ (Ito.rpath (fibW · ω))
            (Restart.DomainMarkov.dyT n k : ℝ≥0) z * Restart.DomainMarkov.ratTest upperHalfPlaneOpens p z)
          (loewnerGreenEnergy (Ito.rpath (fibW · ω)) (Restart.DomainMarkov.dyT n k : ℝ≥0)
            (Restart.DomainMarkov.ratTest upperHalfPlaneOpens p))) :
    FibKernelRaw d P := by
  intro F N hF hbN n k u hu ψ
  set q : ℝ≥0 := Restart.DomainMarkov.dyT n k with hqdef
  have h𝒢 := (Ito.nullAugmented codeFiltration.{u} P).le q
  have hWc : ∀ ω : ULift.{u} FibCode, Continuous (fibW · ω) := fun ω => Aux61Fib.FibCode.continuous_driver ω.down
  have hW0 : ∀ ω : ULift.{u} FibCode, fibW 0 ω = 0 := fun ω => Aux61Fib.FibCode.driver_zero ω.down
  -- the hulls before the clock lie in the buffer
  have hKb : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) < fibU ω → closure (fwdHull (Ito.rpath (fibW · ω)) t) ⊆ d.buffer :=
    Aux61Cov.ae_hull_buffer_of_exit rfl (Aux61Fib.dataClock d P hgood) d.V_sub
      (hgood.mono fun _ h => h.2.2.2.2.2) (hgood.mono fun _ h => h.2.2.2.2.1)
  -- the random open sets
  set U : ULift.{u} FibCode → Set ℂ := fun ω =>
    if (q : ℝ≥0∞) < fibU ω then H \ fwdHull (Ito.rpath (fibW · ω)) q else ∅ with hUdef
  have hUo : ∀ ω, IsOpen (U ω) := fun ω => by
    by_cases hq : (q : ℝ≥0∞) < fibU ω
    · simp only [hUdef, hq, ↓reduceIte]
      exact Coupling.MartMeans2.isOpen_H_diff_fwdHull_rpath (w := fun t => fibW t ω) (hWc ω).continuousOn hq
    · simp only [hUdef, hq, ↓reduceIte]
      exact isOpen_empty
  have hUH : ∀ ω, U ω ⊆ upperHalfPlaneOpens := fun ω => by
    by_cases hq : (q : ℝ≥0∞) < fibU ω
    · simp only [hUdef, hq, ↓reduceIte]
      exact sdiff_subset
    · simp only [hUdef, hq, ↓reduceIte]
      exact empty_subset _
  -- the mean and the functional
  set m : ULift.{u} FibCode → ℂ → ℝ := fun ω z =>
    meanF d.κ (canonExt d ω q) d.q F₀ (Ito.rpath (fibW · ω)) q z with hmdef
  set Ψ : ULift.{u} FibCode → TestOn upperHalfPlaneOpens → ℂ := fun ω φ =>
    Complex.exp (Complex.I * ((∫ z, m ω z * φ z : ℝ) : ℂ) -
      (((1 / 2 : ℝ) * QuantumZipper.zeroGFFTestCov (U ω) φ φ : ℝ) : ℂ)) with hΨdef
  have hΨ : ∀ᵐ ω ∂P, ∀ R : TopologicalSpace.Opens ℂ, (R : Set ℂ) ⊆ U ω →
      ∃ μ : Measure (DistOn R), IsProbabilityMeasure μ ∧
        ∀ ψ' : TestOn R, ∫ v, Complex.exp (Complex.I * (v ψ' : ℂ)) ∂μ =
          Ψ ω (GFF.testIncl R upperHalfPlaneOpens ψ') := by
    filter_upwards [hKb] with ω hKω R hR
    have hRH : R ≤ upperHalfPlaneOpens := fun x hx => hUH ω (hR hx)
    have hloc : LocallyIntegrableOn (m ω) R := by
      by_cases hq : (q : ℝ≥0∞) < fibU ω
      · have hRK : (R : Set ℂ) ⊆ H \ fwdHull (Ito.rpath (fibW · ω)) q := by
          simpa only [hUdef, hq, ↓reduceIte] using hR
        have hG : IsGreenTest (Ito.rpath (fibW · ω)) q F₀.src :=
          hF₀.isGreenTest_src ((hKω q hq).trans hbN₀)
        exact locallyIntegrableOn_meanF (refExt_canonExt d ω q).1 d.q_harm.contDiffOn.continuousOn
          ((hWc ω).comp continuous_real_toNNReal) q.coe_nonneg hG R.isOpen hRK
      · have hR0 : (R : Set ℂ) = ∅ := by
          simpa only [hUdef, hq, ↓reduceIte, subset_empty_iff] using hR
        rw [hR0]
        exact fun x hx => absurd hx (Set.notMem_empty x)
    obtain ⟨μ, hμP, hμ⟩ := Coupling.MartMeans2.exists_gaussLocalLaw (U := ⟨U ω, hUo ω⟩) (hUH ω) (R := R) hR hloc
    refine ⟨μ, hμP, fun ψ' => ?_⟩
    rw [hμ ψ', hΨdef]
    simp only [GFF.coe_testIncl hRH ψ', TopologicalSpace.Opens.coe_mk]
  -- the functional at a test off the hull before the clock
  have hcfΨ : ∀ (φ : TestOn upperHalfPlaneOpens) (ω : ULift.{u} FibCode), (q : ℝ≥0∞) < fibU ω →
      Disjoint (tsupport φ) (fwdHull (Ito.rpath (fibW · ω)) q) →
      cfVal (∫ z, m ω z * φ z) (loewnerGreenEnergy (Ito.rpath (fibW · ω)) q φ) = Ψ ω φ := by
    intro φ ω hq hdis
    have he : loewnerGreenEnergy (Ito.rpath (fibW · ω)) q φ =
        QuantumZipper.zeroGFFTestCov (H \ fwdHull (Ito.rpath (fibW · ω)) q) φ φ :=
      WholeField.loewnerGreenEnergy_rpath_eq_zeroGFFTestCov (w := fun t => fibW t ω) (hWc ω).continuousOn
        (hW0 ω) hq φ hdis
    simp only [hΨdef, hUdef, hq, ↓reduceIte, cfVal]
    rw [he]
  have hXm : Measurable fibField.{u} := Aux61Fib.FibCode.measurable_field.comp measurable_down
  have hcond : ∀ p : Restart.DomainMarkov.RatIdx, ∀ᵐ ω ∂P,
      tsupport (Restart.DomainMarkov.ratTest upperHalfPlaneOpens p) ⊆ U ω →
      P[fun ω => Complex.exp (Complex.I * (fibField ω (Restart.DomainMarkov.ratTest upperHalfPlaneOpens p) : ℂ)) |
          Ito.nullAugmented codeFiltration.{u} P q] ω = Ψ ω (Restart.DomainMarkov.ratTest upperHalfPlaneOpens p) := by
    intro p
    by_cases hφ0 : Restart.DomainMarkov.ratTest upperHalfPlaneOpens p = 0
    · rw [hφ0]
      have e : (fun ω => Complex.exp (Complex.I * (fibField.{u} ω 0 : ℂ))) = fun _ => (1 : ℂ) := by
        funext ω; simp only [map_zero, Complex.ofReal_zero, mul_zero, Complex.exp_zero]
      have h1 : P[fun ω => Complex.exp (Complex.I * (fibField.{u} ω 0 : ℂ)) |
          Ito.nullAugmented codeFiltration.{u} P q] = fun _ => (1 : ℂ) := by
        rw [e, condExp_const h𝒢]
      refine Eventually.of_forall fun ω _ => ?_
      rw [h1]
      have e2 : ((0 : TestOn upperHalfPlaneOpens) : ℂ → ℝ) = (0 : ℂ → ℝ) := rfl
      simp only [hΨdef, e2, Pi.zero_apply, mul_zero, integral_zero, Complex.ofReal_zero,
        GFF.zeroGFFTestCov_zero_zero, sub_zero, Complex.exp_zero]
    · filter_upwards [hrat n k p] with ω hω hsupp
      have hq : (q : ℝ≥0∞) < fibU ω := by
        by_contra hq
        simp only [hUdef, hq, ↓reduceIte, subset_empty_iff] at hsupp
        exact hφ0 (TestFunction.ext fun z => image_eq_zero_of_notMem_tsupport (by rw [hsupp]; exact id))
      have hdis : Disjoint (tsupport (Restart.DomainMarkov.ratTest upperHalfPlaneOpens p))
          (fwdHull (Ito.rpath (fibW · ω)) q) := by
        refine Set.disjoint_left.2 fun z hz hzK => ?_
        have := hsupp hz
        simp only [hUdef, hq, ↓reduceIte] at this
        exact this.2 hzK
      rw [hω hq hdis, hcfΨ _ ω hq hdis]
  have hall := Restart.DomainMarkov.condExp_cexp_ae_eq_of_local_countable h𝒢 hXm hUo hUH hΨ hcond ψ
  filter_upwards [hall, hKb, hgood] with ω hω hKω hg hlt hdis
  have hsupp : tsupport ψ ⊆ U ω := by
    simp only [hUdef, hlt, ↓reduceIte]
    exact fun z hz => ⟨ψ.tsupport_subset hz, fun hK => Set.disjoint_left.1 hdis hz hK⟩
  rw [hω hsupp, ← hcfΨ ψ ω hlt hdis, hmdef]
  congr 1
  -- the extension and the cutoff
  rw [integral_meanF_congr_ext (hWc ω) (refExt_canonExt d ω q) (hu ω) d.q F₀ ψ hdis]
  have htr' : IsGeneratingTrace (fibW · ω) (fibU ω) (fibΓ ω) := hg.1
  have hK' : closure (fwdHull (Ito.rpath (fibW · ω)) q) ⊆ N₀ ∩ N :=
    subset_inter ((hKω q hlt).trans hbN₀) ((hKω q hlt).trans hbN)
  have hbhe : IsBoundedHarmonicExtension
      (forceBoundaryData d.κ (flowLineRhoL d.κ d.bR d.JR 0 0) (flowLineRhoR d.κ d.bR d.JR 0 0)
        (fun i => Restart.FlowStopIdentCMI.geomL (Ito.rpath (fibW · ω)) q (flowLineXL d.bR d.JR 0 i))
        (fun j => Restart.FlowStopIdentCMI.geomR (Ito.rpath (fibW · ω)) q (flowLineXR d.bR d.JR 0 j)))
      (forceJumpSet (fun i => Restart.FlowStopIdentCMI.geomL (Ito.rpath (fibW · ω)) q (flowLineXL d.bR d.JR 0 i))
        (fun j => Restart.FlowStopIdentCMI.geomR (Ito.rpath (fibW · ω)) q (flowLineXR d.bR d.JR 0 j))) (u ω) := by
    have e1 : (fun i => Restart.FlowStopIdentCMI.geomL (Ito.rpath (fibW · ω)) q (flowLineXL d.bR d.JR 0 i)) =
        fun i => geomLW fibW (fun _ => flowLineXL d.bR d.JR 0) i q ω - fibW q ω :=
      funext fun i => Restart.FlowStopIdentCMI.geomL_rpath_eq_geomLW_sub fibW _ i q ω
    have e2 : (fun j => Restart.FlowStopIdentCMI.geomR (Ito.rpath (fibW · ω)) q (flowLineXR d.bR d.JR 0 j)) =
        fun j => geomRW fibW (fun _ => flowLineXR d.bR d.JR 0) j q ω - fibW q ω :=
      funext fun j => Restart.FlowStopIdentCMI.geomR_rpath_eq_geomRW_sub fibW _ j q ω
    rw [e1, e2]
    exact hu ω
  exact Aux61Act.integral_meanF_congr_cut d.κ_pos d.bR_pc (hWc ω) (hW0 ω)
    (fun _ => Aux61Act.exists_trace_real htr' hlt) hbhe d.q_harm.contDiffOn.continuousOn hF₀ hF
    ⟨hbN₀ d.zero_mem, hbN d.zero_mem⟩ hK' ψ hdis

end InteractingSLE.Sec5.Aux61FibK
