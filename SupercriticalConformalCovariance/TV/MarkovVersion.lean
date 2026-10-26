import SupercriticalConformalCovariance.TV.VarianceAsymptotic
import LQGMetric.Papers.DFGPS.ZBBridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Metric LQGMetric QuantumZipper

namespace SupercriticalConformalCovariance.TV

/-- The bounded-domain Markov decomposition retaining its measurable harmonic
version, needed to define a random smooth cutoff. -/
theorem exists_markov_zb_measurable_version
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (h : Ω → DistC) (hh : IsWholePlaneGFF h P)
    (D : TopologicalSpace.Opens ℂ) (hDb : Bornology.IsBounded (D : Set ℂ))
    {s : ℝ} (hs : 0 < s) (z : ℂ)
    (hDs : Disjoint (D : Set ℂ) (sphere z s)) :
    ∃ hH hZ G : Ω → DistC,
      ∃ X : BddOn (D : Set ℂ) → Ω → ℝ,
      (∀ ω, addConst (h ω) (-circleAvg (h ω) s z) = hH ω + hZ ω) ∧
      (∀ᵐ ω ∂P, ∃ g : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd g (D : Set ℂ) ∧
        ∀ φ : TestOn D, restrictTo D (hH ω) φ = ∫ x, g x * φ x) ∧
      Measurable G ∧ hH =ᵐ[P] G ∧ IndepFun hH hZ P ∧
      IsZeroBoundaryGFF D (fun ω => restrictTo D (hZ ω)) P ∧
      IsZBGFFProcessExt D X P ∧
      (∀ φ : TestOn D, X φ.toBddOn =ᵐ[P]
        fun ω => restrictTo D (hZ ω) φ) := by
  obtain ⟨hW, hn⟩ := DFGPS.isNormalizedAt_recenter hh hs z
  obtain ⟨hH, hZ, hsum, hharm, ⟨G, hGσ, hGeq⟩, hind, hzb, _, _⟩ :=
    DFGPS.markov_normAt MarkovFinal.lmLem2_1 P _ hW hs z hn D hDs
  have hGm : Measurable G :=
    hGσ.mono (MarkovZBIndep.fieldSigmaClosed_le hW _) le_rfl
  exact ⟨hH, hZ, G, DFGPS.zbBdd hzb (zbAdmissible_of_isBounded hDb),
    hsum, hharm, hGm, hGeq, hind, hzb,
    DFGPS.isZBGFFProcessExt_zbBdd hzb hDb,
    fun φ => DFGPS.zbBdd_toBddOn_ae hzb _ φ⟩

end SupercriticalConformalCovariance.TV
