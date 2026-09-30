import QuantumZipper.Proofs.GFF.CoordRegHarm

/-!
# Energy of the smoothing error of a pulled-back field (helper for RC3)

For `f = revMap W T` and a finite measure `ν` carried by `ℍ ∩ closedBall 0 R`, Frostman, with a
boundary-layer bound `∫_{Im z ≤ t} (1 + |log Im z|) dν ≤ c t^γ` (`StripBound`), the Neumann
energy of `f_* ν_r − f_* ν`, `ν_r = ν.bind fc(·, r)`, is `O(r^α + r^γ)` (`abs_energy_push_le`).

Proof. Pull the kernel back (`kernelCov_map_eq`): `N(f u, f v) = N(u, v) + hK(u, v)` off the
diagonal (`CoordRegHarm`). The `N`-part is the energy of `ν_r − ν`, bounded by
`FrostmanReg.abs_energy_frostman_le`. For the `hK`-part, `hK` is harmonic in each variable, so
smoothing by a circle contained in `ℍ` does not change `u ↦ ∫ hK(u, v) dB(v)`; only centres with
`Im z ≤ r` contribute, and there the integrand is `O(1 + |log Im z|)`.
Own argument (see `CoordRegHarm`).
-/

set_option maxErrors 400

noncomputable section

open MeasureTheory Filter Metric Set
open scoped ENNReal Real ComplexConjugate Topology

namespace QuantumZipper
namespace CoordReg

open CircleFubini FrostmanReg SmoothConv

/-- Boundary-layer bound for a measure on `ℍ` (used together with integrability of
`|log Im|`, so that the Bochner integral is the true one). -/
def StripBound (ν : Measure ℂ) (c γ : ℝ) : Prop :=
  ∀ t : ℝ, 0 < t → t ≤ 1 → ∫ z, {z : ℂ | z.im ≤ t}.indicator
    (fun z => 1 + |Real.log z.im|) z ∂ν ≤ c * t ^ γ

variable {W : ℝ → ℝ} {T : ℝ}

/-! ## Pulling the kernel back -/

theorem kernelCov_map_eq {f : ℂ → ℂ} (hf : Measurable f) (A B : Measure ℂ) [SFinite B] :
    kernelCov neumannH (A.map f) (B.map f) = ∫ u, ∫ v, neumannH (f u) (f v) ∂B ∂A := by
  unfold kernelCov
  have hin : ∀ x, ∫ y, neumannH x y ∂(B.map f) = ∫ v, neumannH x (f v) ∂B := fun x =>
    integral_map hf.aemeasurable
      (measurable_neumannH.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  simp_rw [hin]
  have hm : StronglyMeasurable fun x => ∫ v, neumannH x (f v) ∂B :=
    ((measurable_neumannH.comp (measurable_fst.prodMk (hf.comp measurable_snd))).stronglyMeasurable
      ).integral_prod_right'
  exact integral_map hf.aemeasurable hm.aestronglyMeasurable

theorem measurable_hK (hW : Continuous W) (hT : 0 ≤ T) :
    Measurable fun p : ℂ × ℂ => hK W T p.1 p.2 := by
  have hfm := TwoPoint.measurable_revMap hW hT
  have hd : Measurable fun p : ℂ × ℂ => dslope (revMap W T) p.2 p.1 := by
    have e : (fun p : ℂ × ℂ => dslope (revMap W T) p.2 p.1) = fun p =>
        if p.1 = p.2 then deriv (revMap W T) p.2
        else (revMap W T p.1 - revMap W T p.2) / (p.1 - p.2) := by
      funext p; rw [dslope_eq_ite]
    rw [e]
    exact Measurable.ite (measurableSet_eq_fun measurable_fst measurable_snd)
      ((measurable_deriv _).comp measurable_snd)
      (((hfm.comp measurable_fst).sub (hfm.comp measurable_snd)).div
        (measurable_fst.sub measurable_snd))
  unfold hK
  exact ((Real.measurable_log.comp hd.norm).neg.sub (Real.measurable_log.comp
    ((hfm.comp measurable_fst).sub (Complex.continuous_conj.measurable.comp
      (hfm.comp measurable_snd))).norm)).add
    (Real.measurable_log.comp (measurable_fst.sub
      (Complex.continuous_conj.measurable.comp measurable_snd)).norm)

theorem prod_diagonal_null {A B : Measure ℂ} [SFinite B] (hB : ∀ a, B {a} = 0) :
    (A.prod B) {p : ℂ × ℂ | p.1 = p.2} = 0 := by
  rw [Measure.prod_apply (measurableSet_eq_fun measurable_fst measurable_snd)]
  have : ∀ x : ℂ, Prod.mk x ⁻¹' {p : ℂ × ℂ | p.1 = p.2} = {x} := fun x => by
    ext y; simp [eq_comm]
  simp [this, hB]

theorem ae_fst_mem_of {A B : Measure ℂ} [SFinite B] {S : Set ℂ} (hA : ∀ᵐ u ∂A, u ∈ S) :
    ∀ᵐ p ∂(A.prod B), p.1 ∈ S := by
  rw [ae_iff]
  have e : {p : ℂ × ℂ | ¬ p.1 ∈ S} = Sᶜ ×ˢ univ := by ext p; simp
  rw [e, Measure.prod_prod, show A Sᶜ = 0 from ae_iff.1 hA, zero_mul]

theorem ae_snd_mem_of {A B : Measure ℂ} [SFinite B] {S : Set ℂ} (hB : ∀ᵐ v ∂B, v ∈ S) :
    ∀ᵐ p ∂(A.prod B), p.2 ∈ S := by
  rw [ae_iff]
  have e : {p : ℂ × ℂ | ¬ p.2 ∈ S} = univ ×ˢ Sᶜ := by ext p; simp
  rw [e, Measure.prod_prod, show B Sᶜ = 0 from ae_iff.1 hB, mul_zero]

/-- Splitting the pulled-back iterated kernel integral. -/
theorem iterated_neumannH_revMap_split (hW : Continuous W) (hT : 0 ≤ T) {A B : Measure ℂ}
    [IsFiniteMeasure A] [IsFiniteMeasure B] (hAH : ∀ᵐ u ∂A, u ∈ H) (hBH : ∀ᵐ v ∂B, v ∈ H)
    (hB0 : ∀ a, B {a} = 0)
    (iN : Integrable (fun p : ℂ × ℂ => neumannH p.1 p.2) (A.prod B))
    (iK : Integrable (fun p : ℂ × ℂ => hK W T p.1 p.2) (A.prod B)) :
    ∫ u, ∫ v, neumannH (revMap W T u) (revMap W T v) ∂B ∂A =
      ∫ u, ∫ v, neumannH u v ∂B ∂A + ∫ u, ∫ v, hK W T u v ∂B ∂A := by
  have h3 : ∀ᵐ p ∂(A.prod B), p.1 ≠ p.2 := by
    rw [ae_iff]
    have e : {p : ℂ × ℂ | ¬ p.1 ≠ p.2} = {p : ℂ × ℂ | p.1 = p.2} := by ext p; simp
    rw [e]; exact prod_diagonal_null hB0
  have hae : ∀ᵐ p ∂(A.prod B), neumannH (revMap W T p.1) (revMap W T p.2) =
      neumannH p.1 p.2 + hK W T p.1 p.2 := by
    filter_upwards [ae_fst_mem_of (B := B) hAH, ae_snd_mem_of (A := A) hBH, h3] with p a b c
    exact neumannH_revMap_eq hW hT a b c
  have iG : Integrable (fun p : ℂ × ℂ => neumannH (revMap W T p.1) (revMap W T p.2))
      (A.prod B) := (iN.add iK).congr (hae.mono fun p hp => hp.symm)
  have e1 : ∫ p, neumannH (revMap W T p.1) (revMap W T p.2) ∂(A.prod B) =
      ∫ u, ∫ v, neumannH (revMap W T u) (revMap W T v) ∂B ∂A := integral_prod _ iG
  have e2 : ∫ p, neumannH p.1 p.2 ∂(A.prod B) = ∫ u, ∫ v, neumannH u v ∂B ∂A :=
    integral_prod _ iN
  have e3 : ∫ p, hK W T p.1 p.2 ∂(A.prod B) = ∫ u, ∫ v, hK W T u v ∂B ∂A :=
    integral_prod _ iK
  rw [← e1, ← e2, ← e3, ← integral_add iN iK]
  exact integral_congr_ae hae

/-! ## The harmonic part -/

section Harmonic

/-- `u ↦ ∫ hK(u, v) dB(v)`. -/
def PhiK (W : ℝ → ℝ) (T : ℝ) (B : Measure ℂ) (u : ℂ) : ℝ := ∫ v, hK W T u v ∂B

theorem measurable_PhiK (hW : Continuous W) (hT : 0 ≤ T) (B : Measure ℂ) [SFinite B] :
    Measurable (PhiK W T B) :=
  ((measurable_hK hW hT).stronglyMeasurable.integral_prod_right' (ν := B)).measurable

variable (hW : Continuous W) (hT : 0 ≤ T)
include hW hT

theorem integrable_hK_prod {R : ℝ} {A B : Measure ℂ} [IsFiniteMeasure A] [IsFiniteMeasure B]
    (hA : ∀ᵐ u ∂A, u ∈ H ∧ ‖u‖ ≤ R) (hB : ∀ᵐ v ∂B, v ∈ H ∧ ‖v‖ ≤ R)
    (hlA : Integrable (fun u : ℂ => |Real.log u.im|) A)
    (hlB : Integrable (fun v : ℂ => |Real.log v.im|) B) :
    Integrable (fun p : ℂ × ℂ => hK W T p.1 p.2) (A.prod B) := by
  obtain ⟨K, hK0, hKb⟩ := abs_hK_le hW hT R
  refine ((integrable_const K).add (((hlA.comp_fst B).add (hlB.comp_snd A)).const_mul 3)).mono'
    (measurable_hK hW hT).aestronglyMeasurable ?_
  filter_upwards [ae_fst_mem_of (B := B) hA, ae_snd_mem_of (A := A) hB] with p a b
  rw [Real.norm_eq_abs]
  exact hKb p.1 a.1 p.2 b.1 a.2 b.2

/-- Pointwise bound for `PhiK`, with the constant of `abs_hK_le`. -/
theorem abs_PhiK_le {R K : ℝ}
    (hKb : ∀ u ∈ H, ∀ v ∈ H, ‖u‖ ≤ R → ‖v‖ ≤ R →
      |hK W T u v| ≤ K + 3 * (|Real.log u.im| + |Real.log v.im|))
    {B : Measure ℂ} [IsFiniteMeasure B] (hB : ∀ᵐ v ∂B, v ∈ H ∧ ‖v‖ ≤ R)
    (hlB : Integrable (fun v : ℂ => |Real.log v.im|) B) {u : ℂ} (hu : u ∈ H) (huR : ‖u‖ ≤ R) :
    |PhiK W T B u| ≤ (K * B.real univ + 3 * ∫ v, |Real.log v.im| ∂B) +
      3 * B.real univ * |Real.log u.im| := by
  have hi : Integrable (fun v : ℂ => K + 3 * (|Real.log u.im| + |Real.log v.im|)) B :=
    (integrable_const _).add (((integrable_const _).add hlB).const_mul 3)
  have h := norm_integral_le_of_norm_le hi (hB.mono fun v hv => by
    rw [Real.norm_eq_abs]; exact hKb u hu v hv.1 huR hv.2)
  rw [Real.norm_eq_abs] at h
  refine h.trans (le_of_eq ?_)
  rw [integral_add (f := fun _ : ℂ => K)
      (g := fun v => 3 * (|Real.log u.im| + |Real.log v.im|)) (integrable_const _)
      (((integrable_const _).add hlB).const_mul 3),
    integral_const_mul,
    integral_add (f := fun _ : ℂ => |Real.log u.im|) (g := fun v => |Real.log v.im|)
      (integrable_const _) hlB, integral_const, integral_const]
  simp only [smul_eq_mul]
  ring

/-- **Mean value property** of `PhiK` on circles inside `ℍ`. -/
theorem integral_PhiK_fc {R : ℝ} {B : Measure ℂ} [IsFiniteMeasure B]
    (hB : ∀ᵐ v ∂B, v ∈ H ∧ ‖v‖ ≤ R) (hlB : Integrable (fun v : ℂ => |Real.log v.im|) B)
    {z : ℂ} {r : ℝ} (hr : 0 < r) (hrz : r < z.im) (hzR : ‖z‖ + r ≤ R) :
    ∫ u, PhiK W T B u ∂foldedCircle z r = PhiK W T B z := by
  have hfc : foldedCircle z r = circleUnif z r := foldedCircle_eq_circleUnif_sc hr.le hrz.le
  have hball : closedBall z r ⊆ H := fun u hu => by
    rw [mem_closedBall, dist_eq_norm] at hu
    have := Complex.abs_im_le_norm (u - z)
    rw [Complex.sub_im] at this
    show 0 < u.im
    linarith [(abs_le.1 this).1]
  have hcirc : ∀ᵐ u ∂circleUnif z r, u ∈ H ∧ ‖u‖ ≤ R := by
    filter_upwards [ae_mem_closedBall_circleUnif z hr.le] with u hu
    refine ⟨hball hu, ?_⟩
    rw [mem_closedBall, dist_eq_norm] at hu
    calc ‖u‖ = ‖z + (u - z)‖ := by ring_nf
      _ ≤ ‖z‖ + ‖u - z‖ := norm_add_le _ _
      _ ≤ R := by linarith
  have hlc : Integrable (fun u : ℂ => |Real.log u.im|) (circleUnif z r) := by
    rw [← hfc]; exact (TwoPoint.integrable_log_im_foldedCircle z hr).abs
  have hint := integrable_hK_prod hW hT hcirc hB hlc hlB
  rw [hfc]
  unfold PhiK
  rw [integral_integral_swap (f := fun u v => hK W T u v) hint]
  refine integral_congr_ae ?_
  filter_upwards [hB] with v hv
  exact integral_hK_circleUnif hW hT hv.1 hr.le hball

end Harmonic

/-! ## Measures smoothed by folded circles -/

theorem bind_fc_ae (ν : Measure ℂ) [IsFiniteMeasure ν] {r : ℝ} (hr : 0 < r) {S : Set ℂ}
    (hS : MeasurableSet S) (h : ∀ᵐ z ∂ν, ∀ᵐ u ∂foldedCircle z r, u ∈ S) :
    ∀ᵐ u ∂(ν.bind fun z => foldedCircle z r), u ∈ S := by
  rw [ae_iff, show {u | ¬ u ∈ S} = Sᶜ from rfl,
    Measure.bind_apply hS.compl (SmoothConv.measurable_foldedCircle r).aemeasurable]
  refine le_antisymm ?_ bot_le
  calc ∫⁻ z, foldedCircle z r Sᶜ ∂ν ≤ ∫⁻ _, 0 ∂ν :=
        lintegral_mono_ae (h.mono fun z hz => (ae_iff.1 hz).le)
    _ = 0 := lintegral_zero

theorem bind_fc_mem_H_norm (ν : Measure ℂ) [IsFiniteMeasure ν] {r R : ℝ} (hr : 0 < r)
    (hν : ∀ᵐ z ∂ν, ‖z‖ ≤ R) :
    ∀ᵐ u ∂(ν.bind fun z => foldedCircle z r), u ∈ H ∧ ‖u‖ ≤ R + r := by
  refine bind_fc_ae ν hr (isOpen_H.measurableSet.inter
    (isClosed_le continuous_norm continuous_const).measurableSet) ?_
  filter_upwards [hν] with z hz
  filter_upwards [TwoPoint.foldedCircle_ae_mem_H z hr, TwoPoint.foldedCircle_ae_norm_le z hr.le]
    with u h1 h2
  exact ⟨h1, by show ‖u‖ ≤ R + r; linarith⟩

theorem integrable_abs_log_im_bind {ν : Measure ℂ} [IsFiniteMeasure ν] {R C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hLA : ∀ z ∈ H, ‖z‖ ≤ R → ∀ r : ℝ, 0 < r → r ≤ 1 →
      ∫ u, |Real.log u.im| ∂foldedCircle z r ≤ C₀ + |Real.log z.im|)
    (hν : ∀ᵐ z ∂ν, z ∈ H ∧ ‖z‖ ≤ R) (hlν : Integrable (fun z : ℂ => |Real.log z.im|) ν)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    Integrable (fun u : ℂ => |Real.log u.im|) (ν.bind fun z => foldedCircle z r) ∧
      ∫ u, |Real.log u.im| ∂(ν.bind fun z => foldedCircle z r) ≤
        C₀ * ν.real univ + ∫ z, |Real.log z.im| ∂ν := by
  have := isFiniteMeasure_bind_circle (r := r) ν
  have hm : Measurable fun u : ℂ => |Real.log u.im| :=
    continuous_abs.measurable.comp (Real.measurable_log.comp Complex.measurable_im)
  have hpt : ∀ᵐ z ∂ν, ∫⁻ u, ENNReal.ofReal |Real.log u.im| ∂foldedCircle z r ≤
      ENNReal.ofReal (C₀ + |Real.log z.im|) := by
    filter_upwards [hν] with z hz
    rw [← ofReal_integral_eq_lintegral_ofReal
      (TwoPoint.integrable_log_im_foldedCircle z hr).abs (ae_of_all _ fun u => abs_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (hLA z hz.1 hz.2 r hr hr1)
  have hbd : ∫⁻ u, ENNReal.ofReal |Real.log u.im| ∂(ν.bind fun z => foldedCircle z r) ≤
      ∫⁻ z, ENNReal.ofReal (C₀ + |Real.log z.im|) ∂ν := by
    rw [Measure.lintegral_bind (SmoothConv.measurable_foldedCircle r).aemeasurable
      hm.ennreal_ofReal.aemeasurable]
    exact lintegral_mono_ae hpt
  have hfin : ∫⁻ z, ENNReal.ofReal (C₀ + |Real.log z.im|) ∂ν =
      ENNReal.ofReal (∫ z, (C₀ + |Real.log z.im|) ∂ν) :=
    (ofReal_integral_eq_lintegral_ofReal ((integrable_const _).add hlν)
      (ae_of_all _ fun z => add_nonneg hC₀ (abs_nonneg _))).symm
  refine ⟨⟨hm.aestronglyMeasurable, ?_⟩, ?_⟩
  · rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun u => abs_nonneg _)]
    exact lt_of_le_of_lt (hbd.trans hfin.le) ENNReal.ofReal_lt_top
  · rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun u => abs_nonneg _)
      hm.aestronglyMeasurable]
    refine (ENNReal.toReal_mono ENNReal.ofReal_ne_top (hbd.trans hfin.le)).trans ?_
    rw [ENNReal.toReal_ofReal (integral_nonneg fun z => add_nonneg hC₀ (abs_nonneg _)),
      integral_add (integrable_const _) hlν, integral_const, smul_eq_mul]
    exact le_of_eq (by ring)

/-! ## The energy estimate -/

section EnergyEst

variable (hW : Continuous W) (hT : 0 ≤ T)
include hW hT

/-- `∫∫ hK dB dA` is symmetric in `(A, B)`. -/
theorem integral_PhiK_symm {R : ℝ} {A B : Measure ℂ} [IsFiniteMeasure A] [IsFiniteMeasure B]
    (hA : ∀ᵐ u ∂A, u ∈ H ∧ ‖u‖ ≤ R) (hB : ∀ᵐ v ∂B, v ∈ H ∧ ‖v‖ ≤ R)
    (hlA : Integrable (fun u : ℂ => |Real.log u.im|) A)
    (hlB : Integrable (fun v : ℂ => |Real.log v.im|) B) :
    ∫ u, PhiK W T B u ∂A = ∫ v, PhiK W T A v ∂B := by
  unfold PhiK
  rw [integral_integral_swap (f := fun u v => hK W T u v)
    (integrable_hK_prod hW hT hA hB hlA hlB)]
  congr 1; funext v; congr 1; funext u
  exact hK_symm hW hT

/-- Pulling back the Neumann covariance along `revMap`: Neumann part plus harmonic part. -/
theorem kernelCov_map_revMap_eq {R : ℝ} {A B : Measure ℂ} [IsFiniteMeasure A]
    [IsFiniteMeasure B] (hAa : IsAdmissibleH A) (hBa : IsAdmissibleH B)
    (hA : ∀ᵐ u ∂A, u ∈ H ∧ ‖u‖ ≤ R) (hB : ∀ᵐ v ∂B, v ∈ H ∧ ‖v‖ ≤ R)
    (hlA : Integrable (fun u : ℂ => |Real.log u.im|) A)
    (hlB : Integrable (fun v : ℂ => |Real.log v.im|) B) :
    kernelCov neumannH (A.map (revMap W T)) (B.map (revMap W T)) =
      kernelCov neumannH A B + ∫ u, PhiK W T B u ∂A := by
  rw [kernelCov_map_eq (TwoPoint.measurable_revMap hW hT)]
  exact iterated_neumannH_revMap_split hW hT (hA.mono fun u hu => hu.1)
    (hB.mono fun v hv => hv.1) (noAtoms_of_isAdmissibleH hBa) (integrable_neumannH_prod hAa hBa)
    (integrable_hK_prod hW hT hA hB hlA hlB)

/-- Smoothing `ν` by circles of radius `r` changes `∫ PhiK_B dν` only through the centres with
`Im z ≤ r` (mean value property), which the strip bound controls. -/
theorem abs_integral_PhiK_bind_sub_le {R K C₀ c γ : ℝ} (hK0 : 0 ≤ K)
    (hKb : ∀ u ∈ H, ∀ v ∈ H, ‖u‖ ≤ R + 1 → ‖v‖ ≤ R + 1 →
      |hK W T u v| ≤ K + 3 * (|Real.log u.im| + |Real.log v.im|))
    (hC₀ : 0 ≤ C₀) (hLA : ∀ z ∈ H, ‖z‖ ≤ R + 1 → ∀ r : ℝ, 0 < r → r ≤ 1 →
      ∫ u, |Real.log u.im| ∂foldedCircle z r ≤ C₀ + |Real.log z.im|)
    {ν B : Measure ℂ} [IsFiniteMeasure ν] [IsFiniteMeasure B]
    (hν : ∀ᵐ z ∂ν, z ∈ H ∧ ‖z‖ ≤ R) (hlν : Integrable (fun z : ℂ => |Real.log z.im|) ν)
    (hS : StripBound ν c γ)
    (hB : ∀ᵐ v ∂B, v ∈ H ∧ ‖v‖ ≤ R + 1) (hlB : Integrable (fun v : ℂ => |Real.log v.im|) B)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    |∫ u, PhiK W T B u ∂(ν.bind fun z => foldedCircle z r) - ∫ u, PhiK W T B u ∂ν| ≤
      (2 * (K * B.real univ + 3 * ∫ v, |Real.log v.im| ∂B) + 3 * B.real univ * (C₀ + 2)) *
        (c * r ^ γ) := by
  have := isFiniteMeasure_bind_circle (r := r) ν
  set a₀ := K * B.real univ + 3 * ∫ v, |Real.log v.im| ∂B with ha₀def
  set b₀ := 3 * B.real univ with hb₀def
  have ha₀ : 0 ≤ a₀ := add_nonneg (mul_nonneg hK0 measureReal_nonneg)
    (mul_nonneg (by norm_num) (integral_nonneg fun _ => abs_nonneg _))
  have hb₀ : 0 ≤ b₀ := mul_nonneg (by norm_num) measureReal_nonneg
  have hPb : ∀ u ∈ H, ‖u‖ ≤ R + 1 → |PhiK W T B u| ≤ a₀ + b₀ * |Real.log u.im| :=
    fun u hu huR => abs_PhiK_le hW hT hKb hB hlB hu huR
  have hPm := measurable_PhiK hW hT B
  have hlm : Measurable fun u : ℂ => |Real.log u.im| :=
    continuous_abs.measurable.comp (Real.measurable_log.comp Complex.measurable_im)
  -- integrability on the three measures
  have hint_of : ∀ (μ : Measure ℂ) [IsFiniteMeasure μ], (∀ᵐ u ∂μ, u ∈ H ∧ ‖u‖ ≤ R + 1) →
      Integrable (fun u : ℂ => |Real.log u.im|) μ → Integrable (PhiK W T B) μ := by
    intro μ _ hμ hlμ
    refine ((integrable_const a₀).add (hlμ.const_mul b₀)).mono' hPm.aestronglyMeasurable ?_
    filter_upwards [hμ] with u hu
    rw [Real.norm_eq_abs]; exact hPb u hu.1 hu.2
  have hLA' : ∀ z ∈ H, ‖z‖ ≤ R → ∀ r : ℝ, 0 < r → r ≤ 1 →
      ∫ u, |Real.log u.im| ∂foldedCircle z r ≤ C₀ + |Real.log z.im| :=
    fun z hz hzR => hLA z hz (by linarith)
  obtain ⟨hlr, -⟩ := integrable_abs_log_im_bind hC₀ hLA' hν hlν hr hr1
  have hνr : ∀ᵐ u ∂(ν.bind fun z => foldedCircle z r), u ∈ H ∧ ‖u‖ ≤ R + 1 := by
    filter_upwards [bind_fc_mem_H_norm ν hr (hν.mono fun z hz => hz.2)] with u hu
    exact ⟨hu.1, by linarith [hu.2]⟩
  have i1 := hint_of _ hνr hlr
  have i0 := hint_of ν (hν.mono fun z hz => ⟨hz.1, by linarith [hz.2]⟩) hlν
  obtain ⟨i2, e2⟩ := integral_bind_circle ν i1
  rw [e2, ← integral_sub i2 i0]
  -- pointwise bound
  set g : ℂ → ℝ := {z : ℂ | z.im ≤ r}.indicator (fun z => 1 + |Real.log z.im|) with hg
  set M := 2 * a₀ + b₀ * (C₀ + 2) with hM
  have hM0 : 0 ≤ M := by positivity
  have hgi : Integrable g ν :=
    ((integrable_const (1 : ℝ)).add hlν).indicator
      (measurableSet_le Complex.measurable_im measurable_const)
  have hpt : ∀ᵐ z ∂ν, ‖∫ u, PhiK W T B u ∂foldedCircle z r - PhiK W T B z‖ ≤ M * g z := by
    filter_upwards [hν] with z hz
    rw [Real.norm_eq_abs]
    rcases lt_or_ge r z.im with hrz | hrz
    · have hzR : ‖z‖ + r ≤ R + 1 := by linarith [hz.2]
      rw [integral_PhiK_fc hW hT hB hlB hr hrz hzR, sub_self, abs_zero]
      have : g z = 0 := Set.indicator_of_notMem (by simpa using hrz) _
      rw [this, mul_zero]
    · have hgz : g z = 1 + |Real.log z.im| := Set.indicator_of_mem (by simpa using hrz) _
      rw [hgz]
      have hfcb : ∀ᵐ u ∂foldedCircle z r, u ∈ H ∧ ‖u‖ ≤ R + 1 := by
        filter_upwards [TwoPoint.foldedCircle_ae_mem_H z hr,
          TwoPoint.foldedCircle_ae_norm_le z hr.le] with u h1 h2
        exact ⟨h1, by linarith [hz.2]⟩
      have hlfc : Integrable (fun u : ℂ => |Real.log u.im|) (foldedCircle z r) :=
        (TwoPoint.integrable_log_im_foldedCircle z hr).abs
      have hb1 : |∫ u, PhiK W T B u ∂foldedCircle z r| ≤ a₀ + b₀ * (C₀ + |Real.log z.im|) := by
        have hib : Integrable (fun u : ℂ => a₀ + b₀ * |Real.log u.im|) (foldedCircle z r) :=
          (integrable_const a₀).add (hlfc.const_mul b₀)
        have h := norm_integral_le_of_norm_le hib
          (hfcb.mono fun u hu => by rw [Real.norm_eq_abs]; exact hPb u hu.1 hu.2)
        rw [Real.norm_eq_abs, integral_add (integrable_const _) (hlfc.const_mul b₀),
          integral_const_mul] at h
        simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at h
        refine h.trans ?_
        have := hLA z hz.1 (by linarith [hz.2]) r hr hr1
        nlinarith
      have hb2 := hPb z hz.1 (by linarith [hz.2])
      have hL0 : 0 ≤ |Real.log z.im| := abs_nonneg _
      calc |∫ u, PhiK W T B u ∂foldedCircle z r - PhiK W T B z|
          ≤ |∫ u, PhiK W T B u ∂foldedCircle z r| + |PhiK W T B z| := abs_sub _ _
        _ ≤ M * (1 + |Real.log z.im|) := by
          rw [hM]; nlinarith [mul_nonneg hb₀ hL0, mul_nonneg ha₀ hL0,
            mul_nonneg (mul_nonneg hb₀ hC₀) hL0]
  have h := norm_integral_le_of_norm_le (hgi.const_mul M) hpt
  rw [Real.norm_eq_abs, integral_const_mul] at h
  exact h.trans (mul_le_mul_of_nonneg_left (hS r hr hr1) hM0)

omit hW hT in
theorem strip_nonneg {ν : Measure ℂ} {c γ : ℝ} (hS : StripBound ν c γ) {r : ℝ} (hr : 0 < r)
    (hr1 : r ≤ 1) : 0 ≤ c * r ^ γ :=
  (integral_nonneg fun z => Set.indicator_nonneg (fun z _ => by positivity) z).trans
    (hS r hr hr1)

/-- **Energy estimate.** For `ν` Frostman on `ℍ ∩ closedBall 0 R` with `|log Im|` integrable and
a strip bound, the Neumann energy of `f_* ν_r − f_* ν` (`f = revMap W T`,
`ν_r = ν.bind fc(·, r)`) is `O(r^α + r^γ)`, uniformly in `r ∈ (0, 1]`. -/
theorem abs_energy_push_le {R α C c γ : ℝ} {ν : Measure ℂ} [IsFiniteMeasure ν]
    (hsupp : ν (closedBall 0 R ∩ Hbar)ᶜ = 0) (hνH : ∀ᵐ z ∂ν, z ∈ H) (hF : IsFrostman ν α C)
    (hα : 0 < α) (hlν : Integrable (fun z : ℂ => |Real.log z.im|) ν) (hS : StripBound ν c γ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ r : ℝ, 0 < r → r ≤ 1 →
      |kernelCov2 neumannH
          ((ν.bind fun z => foldedCircle z r).map (revMap W T), ν.map (revMap W T))
          ((ν.bind fun z => foldedCircle z r).map (revMap W T), ν.map (revMap W T))| ≤
        2 * (C * r ^ α / α) * (ν Set.univ).toReal + M * (c * r ^ γ) := by
  obtain ⟨K, hK0, hKb⟩ := abs_hK_le hW hT (R + 1)
  obtain ⟨C₀, hC₀, hLA⟩ := integral_abs_log_im_fc_le (R + 1)
  set m := ν.real univ with hm
  set L := ∫ z, |Real.log z.im| ∂ν with hL
  have hm0 : 0 ≤ m := measureReal_nonneg
  have hL0 : 0 ≤ L := integral_nonneg fun _ => abs_nonneg _
  set M₁ := 2 * (K * m + 3 * (C₀ * m + L)) + 3 * m * (C₀ + 2) with hM₁
  refine ⟨2 * M₁, by positivity, fun r hr hr1 => ?_⟩
  have := isFiniteMeasure_bind_circle (r := r) ν
  set νr := ν.bind fun z => foldedCircle z r with hνr
  have hν : ∀ᵐ z ∂ν, z ∈ H ∧ ‖z‖ ≤ R := by
    filter_upwards [ae_mem_of_compl_null_frostman hsupp, hνH] with z h1 h2
    exact ⟨h2, by simpa using h1.1⟩
  have hν1 : ∀ᵐ z ∂ν, z ∈ H ∧ ‖z‖ ≤ R + 1 := hν.mono fun z hz => ⟨hz.1, by linarith [hz.2]⟩
  have hνr1 : ∀ᵐ u ∂νr, u ∈ H ∧ ‖u‖ ≤ R + 1 := by
    filter_upwards [bind_fc_mem_H_norm ν hr (hν.mono fun z hz => hz.2)] with u hu
    exact ⟨hu.1, by linarith [hu.2]⟩
  have hLA' : ∀ z ∈ H, ‖z‖ ≤ R → ∀ r : ℝ, 0 < r → r ≤ 1 →
      ∫ u, |Real.log u.im| ∂foldedCircle z r ≤ C₀ + |Real.log z.im| :=
    fun z hz hzR => hLA z hz (by linarith)
  obtain ⟨hlr, hlr'⟩ := integrable_abs_log_im_bind hC₀ hLA' hν hlν hr hr1
  have hA0 := isAdmissibleH_of_frostman hsupp hF hα
  have hA1 := isAdmissibleH_bind_fc_of_supp hsupp hr
  have hmr : νr.real univ = m := by
    rw [hm]; simp only [Measure.real, hνr, bind_fc_univ]
  have e11 := kernelCov_map_revMap_eq hW hT hA1 hA1 hνr1 hνr1 hlr hlr
  have e10 := kernelCov_map_revMap_eq hW hT hA1 hA0 hνr1 hν1 hlr hlν
  have e01 := kernelCov_map_revMap_eq hW hT hA0 hA1 hν1 hνr1 hlν hlr
  have e00 := kernelCov_map_revMap_eq hW hT hA0 hA0 hν1 hν1 hlν hlν
  have hsym := integral_PhiK_symm hW hT hν1 hνr1 hlν hlr
  have hN := abs_energy_frostman_le hsupp hF hα hr
  have b1 := abs_integral_PhiK_bind_sub_le hW hT hK0 hKb hC₀ hLA hν hlν hS hνr1 hlr hr hr1
  have b0 := abs_integral_PhiK_bind_sub_le hW hT hK0 hKb hC₀ hLA hν hlν hS hν1 hlν hr hr1
  have hcr := strip_nonneg hS hr hr1
  have hM1 : (2 * (K * νr.real univ + 3 * ∫ v, |Real.log v.im| ∂νr) +
      3 * νr.real univ * (C₀ + 2)) ≤ M₁ := by
    rw [hmr, hM₁]; nlinarith
  have hM0 : (2 * (K * ν.real univ + 3 * ∫ v, |Real.log v.im| ∂ν) +
      3 * ν.real univ * (C₀ + 2)) ≤ M₁ := by
    rw [hM₁]; nlinarith [mul_nonneg hC₀ hm0]
  have b1' := b1.trans (mul_le_mul_of_nonneg_right hM1 hcr)
  have b0' := b0.trans (mul_le_mul_of_nonneg_right hM0 hcr)
  unfold kernelCov2 at hN ⊢
  simp only at hN ⊢
  rw [e11, e10, e01, e00]
  rw [abs_le] at hN b1' b0' ⊢
  constructor <;> linarith [hN.1, hN.2, b1'.1, b1'.2, b0'.1, b0'.2]

end EnergyEst

end CoordReg
end QuantumZipper
