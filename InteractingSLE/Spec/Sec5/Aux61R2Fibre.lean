/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61WinFibreRef

/-!
# The restart fibre over the reference word (R2, corrected form) and its tilted reference kernel

Packet PROVE-AUX61-R2. Astra's follow-up 4 §1.3 "One density through the endpoint" (`source/external/AstraIG1/
ig1_followup4_audited.txt` L214–L262, ruling R71): "The difference `v = M^c − M` has zero continuous boundary values
on those portions [the seed and the comparison interval], including the canonical seed cancellation. The reflected
cutoff construction […] gives one `f ∈ H¹₀(ℍ)` equal to `v` on a neighborhood of the closed buffer. Weight the
conditional field law by the single strictly positive full Cameron–Martin density for adding `f`. At each pre-contact
announcing stop its mean becomes `M_u + P_{ℍ∖A_u} f`, `P_{ℍ∖A_u} f = f − H_u(f|A_u)`. Identity (1.1), applied to
actual and reference means, now identifies this expression with the canonical reference mean on the buffer."

## Why a corrected fibre

PROVE-AUX61-WIN's `Aux61Win.RestartFibre` writes the fibre's mean at a stop as `meanF κ u₀ q Fq` with `u₀` the
**basic** mean `−λ | λ` and a fixed odd cutoff `Fq` of `q = M − u₀` on a neighbourhood `Nq` of every pre-contact hull.
On the comparison interval `I` the actual mean has the constant boundary value `b` (Astra (1.2): `b > λ + πχ`), so
`q → b − λ ≠ 0` at the points of `I`, while an odd continuous cutoff vanishes on `ℝ`; hence `Nq ∩ ℍ` cannot
accumulate at a point of `I` (`Aux61R2Obstruction`), and the fibre's hulls never approach `I`. A fibre cover of the
window event by such fibres therefore exists only if the event is already null: `RestartFibreCoverOn` cannot be proved
through its fibres.

The correction is Astra's own normalization: the fibre's base mean is the **reference word's** canonical mean
`M^c_τ` (marks at the geometric images of the fibre's driver), and `q = M − M^c` is the difference of the actual and
reference means at the restart. It has zero boundary values both at the seed and on the comparison interval, so it
has a cutoff on a neighbourhood of a buffer that contains the completed slit. Aux. lemma 61 relative to the reference
reads `M_τ = M^c_τ + q − 𝓗_τ(q|A_τ) = M^c_τ + G_τ(1_ℍ gD Fq) + (q − Fq)` on the buffer (`meanF κ u_τ q Fq` with
`u_τ` the reference extension at time `τ`), and the comparison density adds `−Fq`: no separate `v`, no shift identity.

## Contents

* `RefExt κ b̂ Ĵ W t ω u`: `u` is a bounded harmonic extension of the reference word's force data at the geometric
  images (at time `t`, centred at `W_t`) of its initial marks — the frame of `IsCouplingCharFun`;
* **`RefFibre`** — the per-fibre output of R2 in corrected form: a probability space carrying the field read in the
  restart chart and the restarted driver, a clock `e` and a buffer, such that at every stop `τ < e` the field's
  conditional characteristic functional is Gaussian with the Green energy of `ℍ ∖ K_τ` and mean
  `meanF κ u_τ q Fq` (Aux. lemma 61 relative to the reference word);
* `RefFibre.chartField = h + (Fq − q)`; `RefFibre.TiltData` — the Cameron–Martin data for adding `−Fq` (the pairing
  limit `Λ` of the field with the approximations `Fq.neg.testSeq` of the source of `−Fq`, `e^{−Λ}` integrable, a
  constant `k > 0`); `tilt`, `tilt_equivalent`;
* **`RefFibre.TiltData.isCouplingCharFun_tilt`**: under the tilt, the shifted field has the reference word's kernel
  at every stop `τ < e` (exactly the `kernel` field of `Aux61R45.ReferenceSetting`).

Conditional helpers with distinct names; they replace no source theorem. R48: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param` result.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61R2

open QuantumZipper (H fwdHull)
open LQGMetric (TestOn DistOn)
open LocalExt (IsGreenTest greenCross cfVal)
open Restart.FlowStopIdentCMI (CMCut)
open SupercriticalConformalCovariance.GM24 (smoothDist)
open Aux61Win (meanF IsCutoffOn)
open Sec7.PocketTraversal

universe u

/-- **The reference word's frame at time `t`**: `u` is a bounded harmonic extension of the force data of the reference
word `b̂` (from `0`, angle `0`) with its marks at the geometric images at time `t` of the initial marks, centred at
`W_t` (the frame of `Coupling.MartMeans.IsCouplingCharFun`). -/
def RefExt {S : Type u} (κ : ℝ) (bR : ℝ → ℝ) (JR : Finset ℝ) (W : ℝ≥0 → S → ℝ) (t : ℝ≥0) (ω : S)
    (u : ℂ → ℝ) : Prop :=
  IsBoundedHarmonicExtension
    (forceBoundaryData κ (flowLineRhoL κ bR JR 0 0) (flowLineRhoR κ bR JR 0 0)
      (fun i => geomLW W (fun _ => flowLineXL bR JR 0) i t ω - W t ω)
      (fun j => geomRW W (fun _ => flowLineXR bR JR 0) j t ω - W t ω))
    (forceJumpSet (fun i => geomLW W (fun _ => flowLineXL bR JR 0) i t ω - W t ω)
      (fun j => geomRW W (fun _ => flowLineXR bR JR 0) j t ω - W t ω)) u

/-- **A restart fibre over the reference word** (the per-fibre output of piece R2, corrected form): see the module
docstring. The kernel is Aux. lemma 61 relative to the reference word `b̂`: at every stop `τ < e`, for every choice
`u` of the reference extension at time `τ`, the conditional mean is `meanF κ u q Fq` at `τ`. -/
structure RefFibre (S : Type u) [m : MeasurableSpace S] where
  κ : ℝ
  κ_pos : 0 < κ
  bR : ℝ → ℝ
  JR : Finset ℝ
  P : Measure S
  prob : IsProbabilityMeasure P
  field : S → DistOn upperHalfPlaneOpens
  measurable_field : Measurable field
  q : ℂ → ℝ
  q_cont : ContinuousOn q H
  O₀ : Set ℝ
  Fq : CMCut
  Nq : Set ℂ
  cut : IsCutoffOn Fq q Nq O₀
  Cq : ℝ
  q_bdd : ∀ z, Fq.src z ≠ 0 → |q z| ≤ Cq
  buffer : Set ℂ
  buffer_open : IsOpen buffer
  zero_mem : (0 : ℂ) ∈ buffer
  buffer_sub : buffer ⊆ Nq
  W : ℝ≥0 → S → ℝ
  zero : ∀ ω, W 0 ω = 0
  continuous : ∀ ω, Continuous (W · ω)
  filt : Filtration ℝ≥0 m
  e : S → ℝ≥0∞
  hull_buffer : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) < e ω → closure (fwdHull (Ito.rpath (W · ω)) t) ⊆ buffer
  kernel : ∀ (τ : S → WithTop ℝ≥0) (hτ : IsStoppingTime filt τ), (∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < e ω) →
    ∀ u : S → ℂ → ℝ, (∀ ω, RefExt κ bR JR W ((τ ω).untopD 0) ω (u ω)) →
    ∀ ψ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P,
      Disjoint (tsupport ψ) (fwdHull (Ito.rpath (W · ω)) ((τ ω).untopD 0 : ℝ≥0)) →
      P[fun ω' => Complex.exp (Complex.I * (field ω' ψ : ℂ)) | hτ.measurableSpace] ω =
        cfVal (∫ z, meanF κ (u ω) q Fq (Ito.rpath (W · ω)) ((τ ω).untopD 0 : ℝ≥0) z * ψ z)
          (loewnerGreenEnergy (Ito.rpath (W · ω)) ((τ ω).untopD 0 : ℝ≥0) ψ)

namespace RefFibre

variable {S : Type u} [mS : MeasurableSpace S] (D : RefFibre S)

/-- **The Cameron–Martin data for adding `−Fq`** (Aux. lemma 62's density with the comparison function `−q` near the
buffer): the a.s. limit `Λ` of the field's pairings with the approximations of the source of `−Fq`, `e^{−Λ}`
integrable, and a normalizing constant `k > 0`. -/
structure TiltData where
  Λ : S → ℝ
  Λ_measurable : Measurable Λ
  pairing_limit : ∀ᵐ ω ∂D.P, Tendsto (fun n => D.field ω (D.Fq.neg.testSeq n)) atTop (𝓝 (Λ ω))
  integrable_exp : Integrable (fun ω => Real.exp (-Λ ω)) D.P
  k : ℝ
  k_pos : 0 < k

/-- The shifted field `h + (Fq − q)` (the field minus the comparison function `q` near the buffer). -/
def chartField : S → DistOn upperHalfPlaneOpens :=
  fun ω => D.field ω + smoothDist upperHalfPlaneOpens (fun z => D.Fq.f z - D.q z)

theorem measurable_chartField : Measurable D.chartField :=
  (Coupling.measurable_add_distOnConst _).comp D.measurable_field

variable {D}

namespace TiltData

variable (T : D.TiltData)

/-- The Cameron–Martin weighted law `k e^{−Λ} · P`. -/
def tilt : Measure S := D.P.withDensity fun ω => ENNReal.ofReal (T.k * Real.exp (-T.Λ ω))

/-- The weighted law is equivalent to the fibre's law. -/
theorem tilt_equivalent : T.tilt ≪ D.P ∧ D.P ≪ T.tilt :=
  ⟨withDensity_absolutelyContinuous _ _,
    Restart.FlowStopIdentCMI.absolutelyContinuous_withDensity_exp T.Λ_measurable T.k_pos⟩

end TiltData

/-! ### The tilted kernel -/

/-- `greenCross` is odd in its second argument. -/
theorem greenCross_neg_right (W : ℝ → ℝ) (t : ℝ) (φ ψ : ℂ → ℝ) :
    greenCross W t φ (fun z => -ψ z) = -greenCross W t φ ψ := by
  simp only [greenCross, mul_neg, integral_neg]

/-- The negated cutoff of `q` is a cutoff of its own values on the buffer, harmonic there. -/
theorem isCutoffOn_neg_buffer : IsCutoffOn D.Fq.neg (fun z => D.Fq.neg.f z) D.buffer univ := by
  refine ⟨D.buffer_open, fun _ _ _ => trivial, fun _ _ _ => rfl, fun z hz => ?_⟩
  rw [CMCut.greenDensity_neg, D.cut.harmonic z (D.buffer_sub hz), neg_zero]

namespace TiltData

variable (T : D.TiltData)

/-- **R3 for the corrected fibre: the tilted fibre has the reference word's kernel** (the `kernel` field of
`Aux61R45.ReferenceSetting`): under `k e^{−Λ} · P`, the shifted field `h + (Fq − q)` has, at every stop `τ < e` of
the fibre's filtration, the Gaussian conditional law of the reference word `b̂` from `0` (angle `0`) with its marks
at the geometric images of the fibre's driver. Proof: the general tilt `ae_condExp_withDensity_add_of_kernel`; the
cross energy with the source of `−Fq` cancels the Green potential of `meanF`, and the shift `Fq − q` cancels its
remainder `q − Fq`. -/
theorem isCouplingCharFun_tilt : Coupling.MartMeans.IsCouplingCharFun D.κ (flowLineRhoL D.κ D.bR D.JR 0 0)
    (flowLineRhoR D.κ D.bR D.JR 0 0) T.tilt D.filt D.W (geomLW D.W fun _ => flowLineXL D.bR D.JR 0)
    (geomRW D.W fun _ => flowLineXR D.bR D.JR 0) D.e D.chartField := by
  intro τ hτ hτe u hu φ
  let _ := D.prob
  have hτe₀ : ∀ᵐ ω ∂D.P, (τ ω : ℝ≥0∞) < D.e ω := T.tilt_equivalent.2.ae_le hτe
  set κ := D.κ with hκdef
  set Wd : S → ℝ → ℝ := fun ω => Ito.rpath (D.W · ω) with hWd
  set t : S → ℝ≥0 := fun ω => (τ ω).untopD 0 with ht
  set F : CMCut := D.Fq.neg with hFdef
  have hWc : ∀ ω, Continuous (Wd ω) := fun ω => (D.continuous ω).comp continuous_real_toNNReal
  have hKb : ∀ᵐ ω ∂D.P, closure (fwdHull (Wd ω) (t ω)) ⊆ D.buffer := by
    filter_upwards [D.hull_buffer, hτe₀] with ω hb hτω
    exact hb _ (Restart.FlowStopIdentCM.coe_untopD_lt hτω)
  have hΔq : ∀ z ∈ D.buffer, QuantumZipper.K3.greenDensity D.Fq.f z = 0 := fun z hz =>
    D.cut.harmonic z (D.buffer_sub hz)
  have hΔ : ∀ z ∈ D.buffer, QuantumZipper.K3.greenDensity F.f z = 0 := fun z hz => by
    rw [hFdef, CMCut.greenDensity_neg, hΔq z hz, neg_zero]
  have hFq' : IsCutoffOn D.Fq (fun z => D.Fq.f z) D.buffer univ :=
    ⟨D.buffer_open, fun _ _ _ => trivial, fun _ _ _ => rfl, hΔq⟩
  have hF' : IsCutoffOn F (fun z => F.f z) D.buffer univ := isCutoffOn_neg_buffer
  have hqb : ∀ z, F.src z ≠ 0 → |D.q z| ≤ D.Cq := fun z hz => D.q_bdd z fun h0 => hz (by
    rw [hFdef, CMCut.src_neg, h0, neg_zero])
  set s : ℕ → TestOn upperHalfPlaneOpens := F.testSeq with hs
  have hsle : ∀ n z, |s n z| ≤ |F.src z| := F.abs_testSeq_le
  have hslim : ∀ z, Tendsto (fun n => s n z) atTop (𝓝 (F.src z)) := F.tendsto_testSeq
  -- the inputs of the tilt
  have hMint : ∀ᵐ ω ∂D.P, ∀ ψ : TestOn upperHalfPlaneOpens, Disjoint (tsupport ψ) (fwdHull (Wd ω) (t ω)) →
      Integrable fun z => meanF κ (u ω) D.q D.Fq (Wd ω) (t ω) z * ψ z := by
    filter_upwards [hKb] with ω hK ψ hψ
    exact Aux61Win.integrable_meanF_mul (hu ω).1 D.q_cont (D.continuous ω) (hFq'.isGreenTest_src hK) ψ hψ
  have hsd : ∀ᵐ ω ∂D.P, ∀ n, Disjoint (tsupport (s n)) (fwdHull (Wd ω) (t ω)) := by
    filter_upwards [hKb] with ω hK n
    exact Aux61Win.disjoint_tsupport_of_abs_le_src hF' (hsle n) fun z hz => hK (subset_closure hz)
  have hμ₂ : ∀ᵐ ω ∂D.P, Tendsto (fun n => ∫ z, meanF κ (u ω) D.q D.Fq (Wd ω) (t ω) z * s n z) atTop
      (𝓝 ((∫ z, couplingMean κ (Wd ω) (t ω) (u ω) z * F.src z) - greenCross (Wd ω) (t ω) F.src D.Fq.src +
        ∫ z, (D.q z - D.Fq.f z) * F.src z)) := by
    filter_upwards [hKb] with ω hK
    obtain ⟨Cu, hCu⟩ := (hu ω).2.1
    exact Aux61Win.tendsto_integral_meanF_mul (hu ω).1 hCu D.q_cont D.buffer_open D.zero_mem hΔq hΔ hqb
      (D.continuous ω) (D.zero ω) hK hsle hslim
  have hs₂₂ : ∀ᵐ ω ∂D.P, Tendsto (fun n => loewnerGreenEnergy (Wd ω) (t ω) (s n)) atTop
      (𝓝 (loewnerGreenEnergy (Wd ω) (t ω) F.src)) := by
    filter_upwards [hKb] with ω hK
    exact Aux61Win.tendsto_energy_of_abs_le_src hF' (hWc ω) (NNReal.coe_nonneg _) hK hsle hslim
  have hs₁₂ : ∀ᵐ ω ∂D.P, Disjoint (tsupport φ) (fwdHull (Wd ω) (t ω)) →
      Tendsto (fun n => greenCross (Wd ω) (t ω) φ (s n)) atTop (𝓝 (greenCross (Wd ω) (t ω) φ F.src)) := by
    filter_upwards [hKb, hsd] with ω hK hd hφ
    have hG := hF'.isGreenTest_src hK
    exact LocalExt.tendsto_greenCross (hWc ω) (NNReal.coe_nonneg _) (LocalExt.isGreenTest_of_testOn φ hφ) hG
      (fun n => LocalExt.isGreenTest_of_testOn (s n) (hd n)) hG hsle hslim
  have hpath : ∀ᵐ ω ∂D.P, 0 ≤ (t ω : ℝ) ∧ ∃ t₂, (t ω : ℝ) < t₂ ∧ ContinuousOn (Wd ω) (Icc 0 t₂) :=
    ae_of_all _ fun ω => ⟨NNReal.coe_nonneg _, t ω + 1, by linarith, (hWc ω).continuousOn⟩
  set Sh : DistOn upperHalfPlaneOpens := smoothDist upperHalfPlaneOpens (fun z => D.Fq.f z - D.q z) with hSh
  have htilt := Restart.FlowStopIdentCM.ae_condExp_withDensity_add_of_kernel hτ.measurableSpace_le
    D.measurable_field (D.kernel τ hτ hτe₀ u hu) hpath hMint T.Λ_measurable T.pairing_limit T.integrable_exp hsd
    hμ₂ hs₂₂ T.k_pos Sh φ hs₁₂
  -- the mean identity, pathwise
  have hc : ContinuousOn (fun z => D.Fq.f z - D.q z) H := D.Fq.smooth.continuous.continuousOn.sub D.q_cont
  have hShφ : Sh φ = -∫ z, (D.q z - D.Fq.f z) * φ z := by
    rw [hSh, SupercriticalConformalCovariance.GM24.smoothDist_apply hc φ, ← integral_neg]
    exact integral_congr_ae (ae_of_all _ fun z => by simp only; ring)
  have hQP : T.tilt ≪ D.P := withDensity_absolutelyContinuous _ _
  filter_upwards [htilt, hQP.ae_le hKb] with ω h1 hK hφ
  have hφ' : Disjoint (tsupport φ) (fwdHull (Wd ω) (t ω)) := hφ
  change (D.P.withDensity fun ω => ENNReal.ofReal (T.k * Real.exp (-T.Λ ω)))[fun ω' =>
    Complex.exp (Complex.I * ((D.field ω' + Sh) φ : ℂ)) | hτ.measurableSpace] ω = _
  rw [h1 hφ', hShφ, Aux61Win.integral_meanF_eq (hu ω).1 D.q_cont (D.continuous ω) (hFq'.isGreenTest_src hK) φ hφ',
    hFdef, show (D.Fq.neg.src : ℂ → ℝ) = fun z => -D.Fq.src z from funext D.Fq.src_neg, greenCross_neg_right]
  simp only [cfVal]
  congr 4
  change ((∫ z, couplingMean D.κ (Ito.rpath fun x => D.W x ω) (t ω : ℝ) (u ω) z * φ z) -
      greenCross (Ito.rpath fun x => D.W x ω) (t ω : ℝ) φ D.Fq.src + ∫ z, (D.q z - D.Fq.f z) * φ z) -
      -greenCross (Ito.rpath fun x => D.W x ω) (t ω : ℝ) φ D.Fq.src + -(∫ z, (D.q z - D.Fq.f z) * φ z) =
    ∫ z, couplingMean D.κ (Ito.rpath fun x => D.W x ω) (t ω : ℝ) (u ω) z * φ z
  ring

end TiltData

end RefFibre

end InteractingSLE.Sec5.Aux61R2
