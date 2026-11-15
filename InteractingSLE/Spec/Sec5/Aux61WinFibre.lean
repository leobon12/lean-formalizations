/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61WinTilt
import InteractingSLE.Spec.Restart.FlowStopIdentCMIProofKernel
import InteractingSLE.Spec.Sec7.Prop74ProofWord

/-!
# The restart fibre (R2's per-fibre output) and its tilted reference kernel (R3 at every stop)

Packet PROVE-AUX61-WIN. Astra's follow-up 4 §§1.1–1.3 (`source/external/AstraIG1/ig1_followup4_audited.txt`
L68–L262, ruling R71); specification Aux. lemmas 61–62 (`source/spec/p241-288.md` L427–L500).

**The fibre.** Conditionally on the retained history `𝓗_t` (counterflow record, forward record through the rational
restart time `t`, germs), on the event that the current access lies in the original right-target component, the field
read in the restart chart and the restarted forward path form a *general-mean pre-contact coupling*: at every stop `τ`
of the restarted filtration before the clock `e` (first new contact, exit from the comparison buffer) the field's
conditional characteristic functional is Gaussian, with the Green energy of `ℍ ∖ K_τ` and the (PC1) mean
`meanF = M⁰_τ + G_{ℍ∖K_τ}(1_ℍ gD Fq.f) + (q − Fq.f)` of Aux. lemma 61, read through one cutoff `Fq` of the old-mean
difference `q = M − u₀` (`u₀` the basic word `−λ | λ`). `RestartFibre` records exactly these data; in every fibre `q`
is a fixed harmonic function (the old mean is unidentified at old kissing points and stays so).

**The tilt (R3).** For a finite-word reference `b̂` agreeing with the basic word on the real window and a cutoff `F`
of `v = q̂ − q` on the buffer, the Cameron–Martin weight `k e^{−Λ}` and the shift `T = v − F.f` turn the fibre's kernel
into the reference word's (`RestartFibre.ae_condExp_tilt_ref`, one stop), via `Aux61Win.ae_condExp_tilt_eq_ref` and
the (PC1) identity of the reference (`Aux61Win.isPC1_couplingMean_ref`).

Deterministic layer here:

* `integrable_meanF_mul`, **`tendsto_integral_meanF_mul`**: the explicit mean is integrable against tests off the
  hull, and its pairings with tests dominated by a cutoff source converge (the `μ₂` input of the tilt);
* `tendsto_energy_of_abs_le_src`: Green-energy convergence of such tests (the `s₂₂` input).

Conditional helpers with distinct names; they replace no source theorem. R48: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param` result.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal ComplexConjugate

namespace InteractingSLE.Sec5.Aux61Win

open QuantumZipper (H Hbar fwdMap fwdHull greenH)
open LQGMetric (TestOn DistOn)
open LocalExt (IsGreenTest greenCross cfVal)
open Restart.FlowStopIdentCMI (CMCut)
open SupercriticalConformalCovariance.GM24 (smoothDist)

/-! ### The explicit mean: integrability and limits -/

section Det

variable {κ : ℝ} {u₀ q : ℂ → ℝ}

/-- The explicit (PC1) mean is integrable against a test off the hull. -/
theorem integrable_meanF_mul (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H) (hq : ContinuousOn q H) {Fq : CMCut}
    {w' : ℝ≥0 → ℝ} (hw' : Continuous w') {t : ℝ≥0} (hF : IsGreenTest (Ito.rpath w') t Fq.src)
    (φ : TestOn upperHalfPlaneOpens) (hφ : Disjoint (tsupport φ) (fwdHull (Ito.rpath w') t)) :
    Integrable fun z => meanF κ u₀ q Fq (Ito.rpath w') t z * φ z := by
  have hw : Continuous (Ito.rpath w') := hw'.comp continuous_real_toNNReal
  have i₁ := LocalExt.integrable_couplingMean_mul (κ := κ) hw.continuousOn hu₀ hφ
  have i₂ := integrable_greenPot_mul hw t.coe_nonneg hF φ hφ
  have i₃ : Integrable fun z => (q z - Fq.f z) * φ z :=
    LocalExt.integrable_mul_testOn (u₀ := fun z => q z - Fq.f z) (hq.sub Fq.smooth.continuous.continuousOn) φ
  refine ((i₁.add i₂).add i₃).congr (ae_of_all _ fun z => ?_)
  simp only [meanF, Pi.add_apply]
  ring

/-- **Green-energy convergence** of tests dominated by a cutoff source, at a time whose hull closure lies where the
cutoff is harmonic. -/
theorem tendsto_energy_of_abs_le_src {F : CMCut} {q' : ℂ → ℝ} {N : Set ℂ} {O₀ : Set ℝ}
    (hF : IsCutoffOn F q' N O₀) {w : ℝ → ℝ} (hw : Continuous w) {t : ℝ} (ht : 0 ≤ t)
    (hK : closure (fwdHull w t) ⊆ N) {s : ℕ → TestOn upperHalfPlaneOpens} (hsle : ∀ n z, |s n z| ≤ |F.src z|)
    (hslim : ∀ z, Tendsto (fun n => s n z) atTop (𝓝 (F.src z))) :
    Tendsto (fun n => loewnerGreenEnergy w t (s n)) atTop (𝓝 (loewnerGreenEnergy w t F.src)) := by
  have hG := hF.isGreenTest_src hK
  have hsd : ∀ n, Disjoint (tsupport (s n)) (fwdHull w t) := fun n =>
    disjoint_tsupport_of_abs_le_src hF (hsle n) fun z hz => hK (subset_closure hz)
  have hgs : ∀ n, IsGreenTest w t (s n) := fun n => LocalExt.isGreenTest_of_testOn _ (hsd n)
  exact (Restart.FlowStopIdentCM.tendsto_greenCross_of_dominated ht (lt_add_one t) hw.continuousOn hG hG hgs hG
    hsle hslim).2

/-- **The pairings of the explicit mean with tests dominated by a cutoff source converge** (the `μ₂` input of the
tilt). The cutoff `F` and the mean's cutoff `Fq` are harmonic on an open `Nb ∋ 0` containing `closure K_t`, `u₀` is
bounded, and `q` is bounded on the support of `F.src`. The limit is
`∫ M⁰_t F.src − E_t(F.src, Fq.src) + ∫ (q − Fq.f) F.src`. -/
theorem tendsto_integral_meanF_mul (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H) {Cu : ℝ}
    (hCu : ∀ z ∈ H, |u₀ z| ≤ Cu) (hq : ContinuousOn q H) {Fq F : CMCut} {Nb : Set ℂ} (hNbo : IsOpen Nb)
    (h0 : (0 : ℂ) ∈ Nb) (hΔq : ∀ z ∈ Nb, QuantumZipper.K3.greenDensity Fq.f z = 0)
    (hΔ : ∀ z ∈ Nb, QuantumZipper.K3.greenDensity F.f z = 0) {Cq : ℝ} (hqb : ∀ z, F.src z ≠ 0 → |q z| ≤ Cq)
    {w' : ℝ≥0 → ℝ} (hw' : Continuous w') (hw0 : w' 0 = 0) {t : ℝ≥0}
    (hK : closure (fwdHull (Ito.rpath w') t) ⊆ Nb) {s : ℕ → TestOn upperHalfPlaneOpens}
    (hsle : ∀ n z, |s n z| ≤ |F.src z|) (hslim : ∀ z, Tendsto (fun n => s n z) atTop (𝓝 (F.src z))) :
    Tendsto (fun n => ∫ z, meanF κ u₀ q Fq (Ito.rpath w') t z * s n z) atTop
      (𝓝 ((∫ z, couplingMean κ (Ito.rpath w') t u₀ z * F.src z) - greenCross (Ito.rpath w') t F.src Fq.src +
        ∫ z, (q z - Fq.f z) * F.src z)) := by
  set w : ℝ → ℝ := Ito.rpath w' with hwdef
  have hw : Continuous w := hw'.comp continuous_real_toNNReal
  have hw00 : w 0 = 0 := by simp [hwdef, Ito.rpath, hw0]
  have ht0 : (0 : ℝ) ≤ t := t.coe_nonneg
  have hF' : IsCutoffOn F (fun z => F.f z) Nb univ := ⟨hNbo, fun _ _ _ => trivial, fun _ _ _ => rfl, hΔ⟩
  have hFq' : IsCutoffOn Fq (fun z => Fq.f z) Nb univ := ⟨hNbo, fun _ _ _ => trivial, fun _ _ _ => rfl, hΔq⟩
  have hG : IsGreenTest w t F.src := hF'.isGreenTest_src hK
  have hGq : IsGreenTest w t Fq.src := hFq'.isGreenTest_src hK
  have hsd : ∀ n, Disjoint (tsupport (s n)) (fwdHull w t) := fun n =>
    disjoint_tsupport_of_abs_le_src hF' (hsle n) fun z hz => hK (subset_closure hz)
  have hgs : ∀ n, IsGreenTest w t (s n) := fun n => LocalExt.isGreenTest_of_testOn _ (hsd n)
  -- rewrite each pairing in the (PC1) form
  have hrw : ∀ n, (∫ z, meanF κ u₀ q Fq w t z * s n z) =
      (∫ z, couplingMean κ w t u₀ z * s n z) - greenCross w t (s n) Fq.src + ∫ z, (q z - Fq.f z) * s n z :=
    fun n => integral_meanF_eq hu₀ hq hw' hGq (s n) (hsd n)
  simp_rw [hrw]
  -- (1) the canonical mean, by dominated convergence
  obtain ⟨C, hC⟩ := Restart.FlowStopIdentCMI.exists_bound_couplingMean_src κ F hNbo h0 hΔ hw hw00 ht0 hK hCu
  have l₁ : Tendsto (fun n => ∫ z, couplingMean κ w t u₀ z * s n z) atTop
      (𝓝 (∫ z, couplingMean κ w t u₀ z * F.src z)) := by
    refine tendsto_integral_of_dominated_convergence (fun z => C * |F.src z|)
      (fun n => (LocalExt.integrable_couplingMean_mul (κ := κ) hw.continuousOn hu₀ (hsd n)).aestronglyMeasurable)
      (F.integrable_src.abs.const_mul C) (fun n => ae_of_all _ fun z => ?_)
      (ae_of_all _ fun z => (hslim z).const_mul _)
    rw [Real.norm_eq_abs, abs_mul]
    by_cases hz : F.src z = 0
    · have h0' := hsle n z
      rw [hz, abs_zero] at h0'
      rw [abs_nonpos_iff.1 h0', hz, abs_zero, mul_zero, mul_zero]
    · exact mul_le_mul (hC z hz) (hsle n z) (abs_nonneg _) ((abs_nonneg _).trans (hC z hz))
  -- (2) the cross energy, by symmetry and dominated convergence in the second slot
  have l₂ : Tendsto (fun n => greenCross w t (s n) Fq.src) atTop (𝓝 (greenCross w t F.src Fq.src)) := by
    have e : (fun n => greenCross w t (s n) Fq.src) = fun n => greenCross w t Fq.src (s n) :=
      funext fun n => LocalExt.greenCross_comm hw ht0 (hgs n) hGq
    rw [e, LocalExt.greenCross_comm hw ht0 hG hGq]
    exact LocalExt.tendsto_greenCross hw ht0 hGq hG hgs hG hsle hslim
  -- (3) the old-mean difference, bounded on the source's support
  obtain ⟨Cf, hCf⟩ := Fq.smooth.continuous.bounded_above_of_compact_support Fq.compact
  have l₃ : Tendsto (fun n => ∫ z, (q z - Fq.f z) * s n z) atTop (𝓝 (∫ z, (q z - Fq.f z) * F.src z)) := by
    have hm : ∀ n, AEStronglyMeasurable (fun z => (q z - Fq.f z) * s n z) volume := fun n =>
      (LocalExt.integrable_mul_testOn (u₀ := fun z => q z - Fq.f z)
        (hq.sub Fq.smooth.continuous.continuousOn) (s n)).aestronglyMeasurable
    refine tendsto_integral_of_dominated_convergence (fun z => (Cq + Cf) * |F.src z|) hm
      (F.integrable_src.abs.const_mul _) (fun n => ae_of_all _ fun z => ?_)
      (ae_of_all _ fun z => (hslim z).const_mul _)
    rw [Real.norm_eq_abs, abs_mul]
    by_cases hz : F.src z = 0
    · have h0' := hsle n z
      rw [hz, abs_zero] at h0'
      rw [abs_nonpos_iff.1 h0', hz, abs_zero, mul_zero, mul_zero]
    · have hb : |q z - Fq.f z| ≤ Cq + Cf := by
        have h1 := hqb z hz
        have h2 : |Fq.f z| ≤ Cf := by simpa only [Real.norm_eq_abs] using hCf z
        calc |q z - Fq.f z| ≤ |q z| + |Fq.f z| := abs_sub _ _
          _ ≤ Cq + Cf := add_le_add h1 h2
      exact mul_le_mul hb (hsle n z) (abs_nonneg _) ((abs_nonneg _).trans hb)
  exact (l₁.sub l₂).add l₃

end Det

/-! ### The basic word `−λ | λ` -/

section Basic

open Restart.FlowStopIdentCMI (geomL geomR)

/-- The basic data `−λ | λ`. -/
abbrev basicData (κ : ℝ) : ℝ → ℝ := Sec7.prop74Data (sleLambda κ) (sleLambda κ)

/-- **The basic word has zero weights**, so its force data are the basic data at any marks. -/
theorem forceBoundaryData_basic {κ : ℝ} (hκ : 0 < κ) (vL : Fin (flowLineNL (basicData κ) {0} 0) → ℝ)
    (vR : Fin (flowLineNR (basicData κ) {0} 0) → ℝ) :
    forceBoundaryData κ (flowLineRhoL κ (basicData κ) {0} 0 0) (flowLineRhoR κ (basicData κ) {0} 0 0) vL vR =
      basicData κ := by
  have hlam : sleLambda κ ≠ 0 := (Sec4.sleLambda_pos hκ).ne'
  have hL : ∀ i, flowLineRhoL κ (basicData κ) {0} 0 0 i = 0 := fun i => by
    rw [Sec7.flowLineRhoL_prop74Data, zero_mul, sub_zero, div_self hlam, sub_self]
  have hR : ∀ j, flowLineRhoR κ (basicData κ) {0} 0 0 j = 0 := fun j => by
    rw [Sec7.flowLineRhoR_prop74Data, zero_mul, add_zero, div_self hlam, sub_self]
  have sL : ∀ s : Finset (Fin (flowLineNL (basicData κ) {0} 0)),
      ∑ i ∈ s, flowLineRhoL κ (basicData κ) {0} 0 0 i = 0 := fun s => Finset.sum_eq_zero fun i _ => hL i
  have sR : ∀ s : Finset (Fin (flowLineNR (basicData κ) {0} 0)),
      ∑ j ∈ s, flowLineRhoR κ (basicData κ) {0} 0 0 j = 0 := fun s => Finset.sum_eq_zero fun j _ => hR j
  funext x
  simp only [forceBoundaryData, sL, sR, add_zero, mul_one]
  simp only [basicData, Sec7.prop74Data, sleLambda]

/-- A bounded harmonic extension stays one for a larger exceptional set. -/
theorem IsBoundedHarmonicExtension.mono_set {g : ℝ → ℝ} {S S' : Set ℝ} {u : ℂ → ℝ}
    (h : IsBoundedHarmonicExtension g S u) (hS : S ⊆ S') : IsBoundedHarmonicExtension g S' u :=
  ⟨h.1, h.2.1, fun x hx => h.2.2 x fun h' => hx (hS h')⟩

/-- **Every extension of the basic word, at any marks, is the basic mean `u₀`.** -/
theorem eqOn_basic {κ : ℝ} (hκ : 0 < κ) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (basicData κ) {0} u₀) (vL : Fin (flowLineNL (basicData κ) {0} 0) → ℝ)
    (vR : Fin (flowLineNR (basicData κ) {0} 0) → ℝ) {u : ℂ → ℝ}
    (hu : IsBoundedHarmonicExtension
      (forceBoundaryData κ (flowLineRhoL κ (basicData κ) {0} 0 0) (flowLineRhoR κ (basicData κ) {0} 0 0) vL vR)
      (forceJumpSet vL vR) u) : EqOn u u₀ H := by
  rw [forceBoundaryData_basic hκ] at hu
  have hfin : (forceJumpSet vL vR ∪ {0}).Finite :=
    ((Set.finite_range vL).union (Set.finite_range vR)).insert 0 |>.union (Set.finite_singleton 0)
  exact PiecewiseConstant.eqOn_of_isBoundedHarmonicExtension hfin
    (IsBoundedHarmonicExtension.mono_set hu₀ subset_union_right)
    (IsBoundedHarmonicExtension.mono_set hu subset_union_left)

/-- **(PC1) of a finite-word reference against the basic mean**, at any time `t` of a continuous driver from `0`
generated by a trace (for `t > 0`): the reference word `b̂` agrees with the basic word on the real window `O ∋ 0`. -/
theorem isPC1_ref_basic {κ : ℝ} (hκ : 0 < κ) {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension (basicData κ) {0} u₀)
    {bR : ℝ → ℝ} {JR : Finset ℝ} (hbR : IsPiecewiseConstantBoundaryData bR JR) {O : Set ℝ} (hO : IsOpen O)
    (hbO : ∀ x ∈ O, basicData κ x = bR x) (h0O : (0 : ℝ) ∈ O) {qR : ℂ → ℝ}
    (hq : IsBoundedHarmonicExtension (fun x => bR x - basicData κ x) ((({0} : Finset ℝ) ∪ JR : Finset ℝ) : Set ℝ) qR)
    {w' : ℝ≥0 → ℝ} (hw' : Continuous w') (hw0 : w' 0 = 0) {t : ℝ≥0}
    (htr : 0 < t → ∃ η : ℝ → ℂ, ContinuousOn η (Icc 0 (t : ℝ)) ∧
      ∀ r ∈ Ioc (0 : ℝ) t, fwdHull (Ito.rpath w') r = fillH (η '' Icc 0 r)) {uR : ℂ → ℝ}
    (huR : IsBoundedHarmonicExtension
      (forceBoundaryData κ (flowLineRhoL κ bR JR 0 0) (flowLineRhoR κ bR JR 0 0)
        (fun i => geomL (Ito.rpath w') t (flowLineXL bR JR 0 i))
        (fun j => geomR (Ito.rpath w') t (flowLineXR bR JR 0 j)))
      (forceJumpSet (fun i => geomL (Ito.rpath w') t (flowLineXL bR JR 0 i))
        (fun j => geomR (Ito.rpath w') t (flowLineXR bR JR 0 j))) uR) :
    IsPC1 κ u₀ (Ito.rpath w') t qR O (couplingMean κ (Ito.rpath w') t uR) := by
  classical
  have hb0 := Sec7.isPiecewiseConstant_prop74Data (sleLambda κ) (sleLambda κ)
  have hw : Continuous (Ito.rpath w') := hw'.comp continuous_real_toNNReal
  set vL := fun i => geomL (Ito.rpath w') t (flowLineXL (basicData κ) {0} 0 i) with hvL
  set vR := fun j => geomR (Ito.rpath w') t (flowLineXR (basicData κ) {0} 0 j) with hvR
  have huB := LocalExt.isBoundedHarmonicExtension_bheAt κ (flowLineRhoL κ (basicData κ) {0} 0 0)
    (flowLineRhoR κ (basicData κ) {0} 0 0) vL vR
  refine IsPC1.congr_u₀ t.coe_nonneg hw.continuousOn ?_ (eqOn_basic hκ hu₀ vL vR huB)
  rcases eq_zero_or_pos t with rfl | hpos
  · simp only [hvL, hvR, NNReal.coe_zero] at huR huB ⊢
    exact isPC1_couplingMean_ref_zero hκ hb0 hbR hO hbO h0O 0 hq hw' hw0 huR huB
  · obtain ⟨η, hηc, hfill⟩ := htr hpos
    exact isPC1_couplingMean_ref hκ hb0 hbR hO hbO h0O 0 hq hw' hw0 hpos hηc hfill huR huB

end Basic

end InteractingSLE.Sec5.Aux61Win
