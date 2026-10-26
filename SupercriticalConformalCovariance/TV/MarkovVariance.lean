import SupercriticalConformalCovariance.TV.VarianceComparison
import LQGMetric.Papers.DFGPS.L2_8Couple
import LQGMetric.Field.MarkovFinal
import LQGMetric.Field.ZeroBoundaryVar

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Metric
open LQGMetric LQGMetric.Blueprint
open QuantumZipper


namespace SupercriticalConformalCovariance.TV

def localTestOn (U : TopologicalSpace.Opens ℂ) (ψ : TestC0)
    (hψ : tsupport (ψ.1 : ℂ → ℝ) ⊆ U) : TestOn U :=
  ⟨ψ.1, ψ.1.contDiff, ψ.1.hasCompactSupport, hψ⟩

theorem pair_restrict_localTestOn (U : TopologicalSpace.Opens ℂ)
    (ψ : TestC0) (hψ : tsupport (ψ.1 : ℂ → ℝ) ⊆ U) (T : DistC) :
    restrictTo U T (localTestOn U ψ hψ) = T ψ.1 := by
  change T (TestFunction.monoCLM ℝ (localTestOn U ψ hψ)) = T ψ.1
  congr 1
  ext z
  simp [TestFunction.monoCLM_apply, localTestOn]

theorem pair_recenter (h : DistC) (ψ : TestC0) (c : ℝ) :
    addConst h c ψ.1 = h ψ.1 := by
  simpa [ψ.2] using GFFInv.addConst_apply h c ψ.1

theorem memLp_markov_zb_pair
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {U : TopologicalSpace.Opens ℂ} {hz : Ω → DistC}
    {X : BddOn (U : Set ℂ) → Ω → ℝ}
    (hX : IsZBGFFProcessExt U X P)
    (hEq : ∀ φ : TestOn U, X φ.toBddOn =ᵐ[P] fun ω => restrictTo U (hz ω) φ)
    (φ : TestOn U) :
    MemLp (fun ω => restrictTo U (hz ω) φ) 2 P :=
  (memLp_congr_ae (hEq φ)).mp
    ((hX.gaussian.hasGaussianLaw_eval φ.toBddOn).memLp_two)

theorem variance_markov_zb_pair
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {U : TopologicalSpace.Opens ℂ} {hz : Ω → DistC}
    {X : BddOn (U : Set ℂ) → Ω → ℝ}
    (hX : IsZBGFFProcessExt U X P)
    (hEq : ∀ φ : TestOn U, X φ.toBddOn =ᵐ[P] fun ω => restrictTo U (hz ω) φ)
    (φ : TestOn U) :
    Var[fun ω => restrictTo U (hz ω) φ; P] = zeroGFFTestCov U φ φ := by
  rw [variance_congr (hEq φ).symm]
  rw [← covariance_self (hX.measurable φ.toBddOn).aemeasurable]
  exact hX.covariance_eq φ.toBddOn φ.toBddOn

/-- The harmonic-part variance decreases when the zero-boundary domain grows.
Both parts are obtained by independent Markov decompositions of the same
whole-plane GFF, with one common normalization circle. -/
theorem exists_markov_harmonic_variance_le
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (h : Ω → DistC) (hh : IsWholePlaneGFF h P)
    (B D : TopologicalSpace.Opens ℂ) (hBD : (B : Set ℂ) ⊆ D)
    (hBb : Bornology.IsBounded (B : Set ℂ))
    (hDb : Bornology.IsBounded (D : Set ℂ))
    {r : ℝ} (hr : 0 < r) (z : ℂ)
    (hBr : Disjoint (B : Set ℂ) (sphere z r))
    (hDr : Disjoint (D : Set ℂ) (sphere z r))
    (ψ : TestC0) (hψB : tsupport (ψ.1 : ℂ → ℝ) ⊆ B) :
    ∃ hD zD hB zB : Ω → DistC,
      (∀ ω, addConst (h ω) (-circleAvg (h ω) r z) = hD ω + zD ω) ∧
      (∀ ω, addConst (h ω) (-circleAvg (h ω) r z) = hB ω + zB ω) ∧
      (∀ᵐ ω ∂P, ∃ g : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd g (D : Set ℂ) ∧
        ∀ φ : TestOn D, restrictTo D (hD ω) φ = ∫ x, g x * φ x) ∧
      (∀ᵐ ω ∂P, ∃ g : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd g (B : Set ℂ) ∧
        ∀ φ : TestOn B, restrictTo B (hB ω) φ = ∫ x, g x * φ x) ∧
      IndepFun hD zD P ∧ IndepFun hB zB P ∧
      Var[fun ω => hD ω ψ.1; P] ≤ Var[fun ω => hB ω ψ.1; P] := by
  let ψB : TestOn B := localTestOn B ψ hψB
  let ψD : TestOn D := localTestOn D ψ (hψB.trans hBD)
  obtain ⟨hD, zD, XD, hsumD, hharmD, hindD, hXD, hEqD⟩ :=
    DFGPS.markov_zb_coupling MarkovFinal.lmLem2_1 P h hh hr z D hDb hDr
  obtain ⟨hB, zB, XB, hsumB, hharmB, hindB, hXB, hEqB⟩ :=
    DFGPS.markov_zb_coupling MarkovFinal.lmLem2_1 P h hh hr z B hBb hBr
  have hZDL2 : MemLp (fun ω => zD ω ψ.1) 2 P := by
    simpa only [ψD, pair_restrict_localTestOn] using
      memLp_markov_zb_pair hXD hEqD ψD
  have hZBL2 : MemLp (fun ω => zB ω ψ.1) 2 P := by
    simpa only [ψB, pair_restrict_localTestOn] using
      memLp_markov_zb_pair hXB hEqB ψB
  have hZDvar : Var[fun ω => zD ω ψ.1; P] = zeroGFFTestCov D ψD ψD := by
    simpa only [ψD, pair_restrict_localTestOn] using
      variance_markov_zb_pair hXD hEqD ψD
  have hZBvar : Var[fun ω => zB ω ψ.1; P] = zeroGFFTestCov B ψB ψB := by
    simpa only [ψB, pair_restrict_localTestOn] using
      variance_markov_zb_pair hXB hEqB ψB
  have hWmem : MemLp (fun ω => h ω ψ.1) 2 P := MarkovZB.memLp_pair hh ψ
  have hsumDψ (ω : Ω) : h ω ψ.1 = hD ω ψ.1 + zD ω ψ.1 := by
    have he := congrArg (fun T : DistC => T ψ.1) (hsumD ω)
    rw [pair_recenter, add_apply] at he
    exact he
  have hsumBψ (ω : Ω) : h ω ψ.1 = hB ω ψ.1 + zB ω ψ.1 := by
    have he := congrArg (fun T : DistC => T ψ.1) (hsumB ω)
    rw [pair_recenter, add_apply] at he
    exact he
  have hHDL2 : MemLp (fun ω => hD ω ψ.1) 2 P := by
    have he : (fun ω => hD ω ψ.1) = (fun ω => h ω ψ.1 - zD ω ψ.1) := by
      funext ω; linarith [hsumDψ ω]
    rw [he]
    exact hWmem.sub hZDL2
  have hHBL2 : MemLp (fun ω => hB ω ψ.1) 2 P := by
    have he : (fun ω => hB ω ψ.1) = (fun ω => h ω ψ.1 - zB ω ψ.1) := by
      funext ω; linarith [hsumBψ ω]
    rw [he]
    exact hWmem.sub hZBL2
  have hindDψ : IndepFun (fun ω => zD ω ψ.1) (fun ω => hD ω ψ.1) P :=
    hindD.symm.comp (GFFInv.measurable_pair ψ.1) (GFFInv.measurable_pair ψ.1)
  have hindBψ : IndepFun (fun ω => zB ω ψ.1) (fun ω => hB ω ψ.1) P :=
    hindB.symm.comp (GFFInv.measurable_pair ψ.1) (GFFInv.measurable_pair ψ.1)
  have hsame : Var[fun ω => zD ω ψ.1 + hD ω ψ.1; P] =
      Var[fun ω => zB ω ψ.1 + hB ω ψ.1; P] := by
    have eD : (fun ω => zD ω ψ.1 + hD ω ψ.1) = fun ω => h ω ψ.1 := by
      funext ω; linarith [hsumDψ ω]
    have eB : (fun ω => zB ω ψ.1 + hB ω ψ.1) = fun ω => h ω ψ.1 := by
      funext ω; linarith [hsumBψ ω]
    rw [eD, eB]
  have hmono : Var[fun ω => zB ω ψ.1; P] ≤ Var[fun ω => zD ω ψ.1; P] := by
    rw [hZBvar, hZDvar]
    apply zeroGFFTestCov_self_mono hBD (zbAdmissible_of_isBounded hBb)
      (zbAdmissible_of_isBounded hDb) ψB ψD rfl
  exact ⟨hD, zD, hB, zB, hsumD, hsumB, hharmD, hharmB, hindD, hindB,
    harmonic_variance_le_of_zb_variance_mono hZDL2 hHDL2 hZBL2 hHBL2
      hindDψ hindBψ hsame hmono⟩

end SupercriticalConformalCovariance.TV
