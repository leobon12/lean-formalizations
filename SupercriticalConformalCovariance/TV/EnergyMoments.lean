import SupercriticalConformalCovariance.TV.EnergyCutoff
import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Metric Set LQGMetric LQGMetric.GM QuantumZipper Filter ProbabilityTheory

namespace SupercriticalConformalCovariance.TV

theorem sq_setIntegral_abs_le_measure_mul_setIntegral_sq
    (K : Set ℂ) (hK : IsCompact K) (hKm : MeasurableSet K)
    (u : ℂ → ℝ) (hu : ContinuousOn u K) :
    (∫ y in K, |u y|) ^ 2 ≤ (volume K).toReal * ∫ y in K, u y ^ 2 := by
  have hci : IntegrableOn (fun y => |u y|) K :=
    hu.abs.integrableOn_compact hK
  have hcs : IntegrableOn (fun y => |u y| ^ 2) K :=
    hu.abs.pow 2 |>.integrableOn_compact hK
  let μ : Measure ℂ := volume.restrict K
  haveI : IsFiniteMeasure μ := by
    exact ⟨by simpa [μ] using (hK.measure_lt_top (μ := (volume : Measure ℂ)))⟩
  have hmem : MemLp (fun y => |u y|) (ENNReal.ofReal (2 : ℝ)) μ := by
    simpa using (memLp_two_iff_integrable_sq hci.aestronglyMeasurable).2 hcs
  have hOne : MemLp (fun _ : ℂ => (1 : ℝ)) (ENNReal.ofReal (2 : ℝ)) μ := memLp_const 1
  have hcs' := integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := μ) Real.HolderConjugate.two_two
    (Eventually.of_forall fun y => abs_nonneg (u y))
    (Eventually.of_forall fun _ => zero_le_one) hmem hOne
  simp only [mul_one, integral_const, smul_eq_mul] at hcs'
  have hcs'' : (∫ y in K, |u y|) ≤
      ((∫ y in K, |u y| ^ 2) ^ ((1 : ℝ) / 2)) *
        ((volume K).toReal ^ ((1 : ℝ) / 2)) := by
    simpa [μ, measureReal_def, Real.rpow_two] using hcs'
  have hJ : 0 ≤ ∫ y in K, u y ^ 2 := integral_nonneg fun y => sq_nonneg _
  have hm : 0 ≤ (volume K).toReal := ENNReal.toReal_nonneg
  have hI : 0 ≤ ∫ y in K, |u y| := integral_nonneg fun y => abs_nonneg _
  have hS : (∫ y in K, |u y|) ≤
      Real.sqrt (∫ y in K, |u y| ^ 2) * Real.sqrt (volume K).toReal := by
    simpa only [Real.sqrt_eq_rpow, one_div] using hcs''
  have hJeq : (∫ y in K, |u y| ^ 2) = ∫ y in K, u y ^ 2 := by
    congr 1
    funext y
    exact sq_abs _
  rw [hJeq] at hS
  have hsq := pow_le_pow_left₀ hI hS 2
  nlinarith [Real.sq_sqrt hJ, Real.sq_sqrt hm]

theorem memLp_markov_harmonic_pair
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h hH hZ G : Ω → DistC} (hh : IsWholePlaneGFF h P)
    (hGeq : hH =ᵐ[P] G) (D : TopologicalSpace.Opens ℂ)
    (X : BddOn (D : Set ℂ) → Ω → ℝ)
    (hX : IsZBGFFProcessExt D X P)
    (hEq : ∀ φ : TestOn D, X φ.toBddOn =ᵐ[P]
      fun ω => restrictTo D (hZ ω) φ)
    (s : ℝ) (z : ℂ)
    (hsum : ∀ ω, addConst (h ω) (-circleAvg (h ω) s z) = hH ω + hZ ω)
    (ψ : TestC0) (hψD : tsupport (ψ.1 : ℂ → ℝ) ⊆ D) :
    MemLp (fun ω => G ω ψ.1) 2 P := by
  let φ : TestOn D := localTestOn D ψ hψD
  have hZmem : MemLp (fun ω => hZ ω ψ.1) 2 P := by
    simpa only [φ, pair_restrict_localTestOn] using
      memLp_markov_zb_pair hX hEq φ
  have hWmem : MemLp (fun ω => h ω ψ.1) 2 P := MarkovZB.memLp_pair hh ψ
  have hHmem : MemLp (fun ω => hH ω ψ.1) 2 P := by
    have heq : (fun ω => hH ω ψ.1) = fun ω => h ω ψ.1 - hZ ω ψ.1 := by
      funext ω
      have he := congrArg (fun T : DistC => T ψ.1) (hsum ω)
      rw [pair_recenter, add_apply] at he
      linarith
    rw [heq]
    exact hWmem.sub hZmem
  exact (memLp_congr_ae (hGeq.mono fun ω he => by rw [← he])).mp hHmem

theorem memLp_rawCenteredRepresentative
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h hH hZ G : Ω → DistC} (hh : IsWholePlaneGFF h P)
    (hGeq : hH =ᵐ[P] G) (D : TopologicalSpace.Opens ℂ)
    {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ)
    (hBD : ball (0 : ℂ) L ⊆ D)
    (X : BddOn (D : Set ℂ) → Ω → ℝ)
    (hX : IsZBGFFProcessExt D X P)
    (hEq : ∀ φ : TestOn D, X φ.toBddOn =ᵐ[P]
      fun ω => restrictTo D (hZ ω) φ)
    (s : ℝ) (z : ℂ)
    (hsum : ∀ ω, addConst (h ω) (-circleAvg (h ω) s z) = hH ω + hZ ω)
    {y : ℂ} (hy : ‖y‖ + δ < L) (h0 : δ < L) :
    MemLp (fun ω => rawCenteredRepresentative δ hδ (G ω) y) 2 P := by
  let ψ : TestC0 := radDiff hδ.le y 0
  let B : TopologicalSpace.Opens ℂ := ⟨ball (0 : ℂ) L, isOpen_ball⟩
  let φB : TestOn B :=
    radBumpOnDisk hδ hL y hy - radBumpOnDisk hδ hL 0 (by
      simpa using h0)
  have hφψ : (φB : ℂ → ℝ) = ψ.1 := by funext x; rfl
  have hψD : tsupport (ψ.1 : ℂ → ℝ) ⊆ D := by
    rw [← hφψ]
    exact φB.tsupport_subset.trans hBD
  have hm := memLp_markov_harmonic_pair hh hGeq D X hX hEq s z hsum ψ hψD
  have heq : (fun ω => rawCenteredRepresentative δ hδ (G ω) y) =
      fun ω => G ω ψ.1 / ∫ x, radProf δ x := by
    funext ω
    exact radialRepresentative_sub_zero δ hδ (G ω) y
  rw [heq]
  simpa only [div_eq_mul_inv] using hm.mul_const (∫ x, radProf δ x)⁻¹

end SupercriticalConformalCovariance.TV
