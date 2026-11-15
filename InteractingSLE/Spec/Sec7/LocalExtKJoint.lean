/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.LocalExtKPath
import InteractingSLE.Spec.Sec7.LocalExtIRand
import InteractingSLE.Spec.Coupling.WholeField2Kernel

/-!
# Aux. lemma 55 with a random seed word: the joint conditional law of a test pairing and the source pairing

Packet PROVE-LOCEXT-K (step 2 of `planning/handoffs/PROVE-LOCEXT-I.md`, "the conditional law of the random pairing at
stops before the local stop"). After a restart the force positions are random (known at time `0` of the restarted
filtration). This file works in an abstract **random-word setting**: a probability space with a filtration `𝓖`, a
driving process `(W, V, B, ζ)` and a field `h` satisfying the coupling clause (`MartMeans.IsCouplingCharFun`) for the
weights `(ρL, ρR)`, and a `𝓖₀`-measurable admissible word `c` such that almost surely the path is an integrated path of
the word `c ω` with an admissible seed (`IsWordPath`). Results:

* `measurable_bheAt_word`, `abs_bheAt_le`: the explicit harmonic extension is jointly measurable in the word and the
  point, and bounded uniformly in the word;
* `condExp_cexp_centred_zero`: given `𝓖₀`, the centred field `h − 𝔥₀(c)` has the zero-boundary GFF characteristic
  functional at every `𝓖₀`-measurable random test function (the clause at `τ = 0`);
* `ae_tendsto_srcPairW_word`: `h(v_{n_k(c)}) → (h, v_c) = srcPairW c h` almost surely;
* **`condExp_cexp_joint_word`**: at every `𝓖`-stopping time `τ` before the local stop, almost surely on
  `{supp φ ∩ K_τ = ∅}`, `(h(φ), (h, v_c))` is conditionally Gaussian given `𝓖_τ` with means `∫ 𝔥_τ φ`, `(𝔥_τ, v_c)` and
  covariances `E_τ(φ)`, `E_τ(φ, v_c)`, `E_τ(v_c)` (the random-word form of A3Joint's `hjoint`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace LocalExt

open QuantumZipper (H fwdMap fwdHull greenH)
open LQGMetric (TestOn DistOn)

/-! ### The explicit harmonic extension as a function of the word -/

section BheWord

variable {nL nR : ℕ} (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)

theorem measurable_jumpExt : Measurable fun p : ℝ × ℂ => Impl.jumpExt p.1 p.2 := by
  simp_rw [Impl.jumpExt_eq]
  exact measurable_const.sub ((Complex.measurable_arg.comp
    (measurable_snd.sub (Complex.measurable_ofReal.comp measurable_fst))).div_const _)

/-- **The explicit harmonic extension is jointly measurable in the word and the point.** -/
theorem measurable_bheAt_word :
    Measurable fun p : ((Fin nL → ℝ) × (Fin nR → ℝ)) × ℂ => bheAt κ ρL ρR p.1.1 p.1.2 p.2 := by
  set X := ((Fin nL → ℝ) × (Fin nR → ℝ)) × ℂ
  have hJ : ∀ {f : X → ℝ}, Measurable f → Measurable fun p : X => Impl.jumpExt (f p) p.2 := by
    intro f hf
    have h := measurable_jumpExt.comp (hf.prodMk (measurable_snd (α := (Fin nL → ℝ) × (Fin nR → ℝ)) (β := ℂ)))
    exact h
  have h0 : Measurable fun p : X => Impl.jumpExt 0 p.2 := hJ measurable_const
  have hL : Measurable fun p : X => ∑ i, ρL i * (1 - Impl.jumpExt (min 0 (p.1.1 i)) p.2) :=
    Finset.measurable_sum _ fun i _ => measurable_const.mul (measurable_const.sub
      (hJ (measurable_const.min ((measurable_pi_apply i).comp measurable_fst.fst))))
  have hR : Measurable fun p : X => ∑ i, ρR i * Impl.jumpExt (max 0 (p.1.2 i)) p.2 :=
    Finset.measurable_sum _ fun i _ => measurable_const.mul
      (hJ (measurable_const.max ((measurable_pi_apply i).comp measurable_fst.snd)))
  have h := measurable_const (a := Real.pi / Real.sqrt κ) |>.mul
    (((measurable_const (a := (-1 : ℝ))).add ((measurable_const (a := (2 : ℝ))).mul h0)).sub hL |>.add hR)
  exact h

/-- The uniform bound of the explicit harmonic extension. -/
def bheBound : ℝ := |Real.pi / Real.sqrt κ| * (3 + 2 * ∑ i, |ρL i| + ∑ i, |ρR i|)

theorem abs_bheAt_le (vL : Fin nL → ℝ) (vR : Fin nR → ℝ) {z : ℂ} (hz : z ∈ H) :
    |bheAt κ ρL ρR vL vR z| ≤ bheBound κ ρL ρR :=
  Impl.abs_forceExt_le κ (Ito.weightWord ρL ρR) vL vR hz

end BheWord

/-! ### The random-word setting -/

section Setting

variable {κ : ℝ} {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {r : ℝ}
  {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **A good path of a random word**: the integrated path of Definition 2.1 for the word `c ω`, with the terminal-state
property of Aux. lemma 3 and an admissible seed. -/
def IsWordPath (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
    (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (c : Ω → (Fin nL → ℝ) × (Fin nR → ℝ))
    (ω : Ω) : Prop :=
  IsIntegratedSLEPath κ (c ω).1 (c ω).2 ρL ρR (fun t => W t ω) (fun i t => VL i t ω) (fun j t => VR j t ω)
      (fun t => B t ω) (ζ ω) ∧
    HasThresholdLimit ρL ρR (fun t => W t ω) (fun i t => VL i t ω) (fun j t => VR j t ω) (ζ ω) ∧
    ¬ ForceWord.ThresholdCondition ρL ρR 0 (c ω).1 (c ω).2

variable {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {c : Ω → (Fin nL → ℝ) × (Fin nR → ℝ)} {ω : Ω}

theorem IsWordPath.localStopPath_lt (hg : IsWordPath κ ρL ρR W VL VR B ζ c ω) (hx : IsAdmWord r (c ω)) :
    ((localStopPath r (ζ ω) fun t => W t ω : WithTop ℝ≥0) : ℝ≥0∞) < ζ ω :=
  LocalExt.localStopPath_lt hg.1 hx.1 hx.2 hg.2.2 hg.2.1

theorem IsWordPath.zeta_pos (hg : IsWordPath κ ρL ρR W VL VR B ζ c ω) (hx : IsAdmWord r (c ω)) : 0 < ζ ω :=
  lt_of_le_of_lt zero_le (hg.localStopPath_lt hx)

/-- At time `0` the centred positions are the word. -/
theorem IsWordPath.pos_zero (hg : IsWordPath κ ρL ρR W VL VR B ζ c ω) :
    (fun i => VL i 0 ω - W 0 ω) = (c ω).1 ∧ (fun j => VR j 0 ω - W 0 ω) = (c ω).2 := by
  have hpu := hg.1.isSLEPathUpTo le_rfl
  have hw0 : W 0 ω = 0 := hpu.w_zero
  exact ⟨funext fun i => by rw [hpu.vL_zero i, hw0, sub_zero], funext fun j => by rw [hpu.vR_zero j, hw0, sub_zero]⟩

theorem IsWordPath.fwdHull_zero (hg : IsWordPath κ ρL ρR W VL VR B ζ c ω) (hx : IsAdmWord r (c ω)) :
    fwdHull (fun s : ℝ => W s.toNNReal ω) ((0 : ℝ≥0) : ℝ) = ∅ :=
  Coupling.MartMeans2.fwdHull_rpath_zero hg.1.2.2.2.1 (hg.zeta_pos hx)

end Setting

/-! ### Measurability of tested means with random test functions -/

section RandomMean

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- A random test function with measurable values is jointly measurable. -/
theorem measurable_uncurry_randomTest {φ : Ω → TestOn upperHalfPlaneOpens} (hφ : ∀ z, Measurable fun ω => φ ω z) :
    Measurable fun q : Ω × ℂ => φ q.1 q.2 := by
  have h := measurable_uncurry_of_continuous_of_measurable (u := fun (z : ℂ) (ω : Ω) => φ ω z)
    (fun ω => (φ ω).continuous) hφ
  have h2 := h.comp measurable_swap
  exact h2

/-- `ω ↦ ∫ u ω z φ ω z` is measurable for a jointly measurable `u` and a random test function `φ`. -/
theorem measurable_integral_mul_randomTest {u : Ω → ℂ → ℝ} (hu : Measurable (Function.uncurry u))
    {φ : Ω → TestOn upperHalfPlaneOpens} (hφ : ∀ z, Measurable fun ω => φ ω z) :
    Measurable fun ω => ∫ z, u ω z * φ ω z := by
  have hj : Measurable fun q : Ω × ℂ => u q.1 q.2 * φ q.1 q.2 := hu.mul (measurable_uncurry_randomTest hφ)
  exact (hj.stronglyMeasurable.integral_prod_right (ν := (volume : Measure ℂ))).measurable

end RandomMean

/-! ### The clause at time `0` and the source pairing -/

section Clause

variable {κ : ℝ} {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {r : ℝ}
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {𝓖 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens} {c : Ω → (Fin nL → ℝ) × (Fin nR → ℝ)}

/-- The mean at time `0` of a random word. -/
def wordMean (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (c : Ω → (Fin nL → ℝ) × (Fin nR → ℝ)) (ω : Ω) :
    ℂ → ℝ :=
  bheAt κ ρL ρR (c ω).1 (c ω).2

omit [IsProbabilityMeasure P] in
theorem measurable_uncurry_wordMean (hc : Measurable c) :
    Measurable (Function.uncurry (wordMean κ ρL ρR c)) := by
  have h := (measurable_bheAt_word κ ρL ρR).comp ((hc.comp measurable_fst).prodMk (measurable_snd (β := ℂ)))
  exact h

/-- **The clause at time `0`**: given `𝓖₀`, the centred field `h − 𝔥₀(c)` has the zero-boundary GFF characteristic
functional at every `𝓖₀`-measurable random test function. -/
theorem condExp_cexp_centred_zero (hcf : Coupling.MartMeans.IsCouplingCharFun κ ρL ρR P 𝓖 W VL VR ζ h)
    (hhm : Measurable h) (hc : Measurable[𝓖 0] c) (hadm : ∀ ω, IsAdmWord r (c ω))
    (hgood : ∀ᵐ ω ∂P, IsWordPath κ ρL ρR W VL VR B ζ c ω) (φ : Ω → TestOn upperHalfPlaneOpens)
    (hφ : ∀ z, Measurable[𝓖 0] fun ω => φ ω z) (t : ℝ) :
    P[fun ω => Complex.exp (Complex.I * ((t * (h ω (φ ω) - ∫ z, wordMean κ ρL ρR c ω z * φ ω z) : ℝ) : ℂ)) |
        𝓖 0] =ᵐ[P] fun ω => ((Real.exp (-(1 / 2) * (t ^ 2 * greenEnergy (φ ω) (φ ω))) : ℝ) : ℂ) := by
  have hτ : IsStoppingTime 𝓖 fun _ : Ω => ((0 : ℝ≥0) : WithTop ℝ≥0) := isStoppingTime_const _ _
  have hms : hτ.measurableSpace = 𝓖 0 := IsStoppingTime.measurableSpace_const _ _
  have hpath : ∀ᵐ ω ∂P, W 0 ω = 0 ∧ ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω} := by
    filter_upwards [hgood] with ω hg
    exact ⟨(hg.1.isSLEPathUpTo le_rfl).w_zero, hg.1.2.2.2.1⟩
  have hlt : ∀ᵐ ω ∂P, ((((0 : ℝ≥0) : WithTop ℝ≥0)) : ℝ≥0∞) < ζ ω := by
    filter_upwards [hgood] with ω hg
    exact (hg.zeta_pos (hadm ω))
  set u : Ω → ℂ → ℝ := fun ω => bheAt κ ρL ρR (fun i => VL i 0 ω - W 0 ω) (fun j => VR j 0 ω - W 0 ω) with hudef
  have hu : ∀ ω, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR
        (fun i => VL i ((((0 : ℝ≥0) : WithTop ℝ≥0)).untopD 0) ω - W ((((0 : ℝ≥0) : WithTop ℝ≥0)).untopD 0) ω)
        (fun i => VR i ((((0 : ℝ≥0) : WithTop ℝ≥0)).untopD 0) ω - W ((((0 : ℝ≥0) : WithTop ℝ≥0)).untopD 0) ω))
      (forceJumpSet
        (fun i => VL i ((((0 : ℝ≥0) : WithTop ℝ≥0)).untopD 0) ω - W ((((0 : ℝ≥0) : WithTop ℝ≥0)).untopD 0) ω)
        (fun i => VR i ((((0 : ℝ≥0) : WithTop ℝ≥0)).untopD 0) ω - W ((((0 : ℝ≥0) : WithTop ℝ≥0)).untopD 0) ω))
      (u ω) := fun ω => by
    simp only [WithTop.untopD_coe]
    exact isBoundedHarmonicExtension_bheAt κ ρL ρR _ _
  have hφt : ∀ z, Measurable[hτ.measurableSpace] fun ω => (t • φ ω) z := fun z => by
    rw [hms]
    exact (hφ z).const_mul t
  have hcl := isCouplingCharFun_condExp_cexp_random hcf hhm hpath hτ hlt u hu hφt
  rw [hms] at hcl
  -- the mean, a `𝓖₀`-measurable factor
  set M : Ω → ℝ := fun ω => ∫ z, wordMean κ ρL ρR c ω z * φ ω z with hMdef
  have hMm : Measurable[𝓖 0] M :=
    measurable_integral_mul_randomTest (mΩ := 𝓖 0) (measurable_uncurry_wordMean (mΩ := 𝓖 0) hc) hφ
  have he : StronglyMeasurable[𝓖 0] fun ω => Complex.exp (Complex.I * ((-(t * M ω) : ℝ) : ℂ)) :=
    (@GFF.measurable_exp_I_mul Ω (𝓖 0) _ (hMm.const_mul t).neg).stronglyMeasurable
  have hnorm : ∀ x : ℝ, ‖Complex.exp (Complex.I * (x : ℂ))‖ = 1 := fun x => by
    rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I x
  have hhφ : Measurable fun ω => h ω (t • φ ω) :=
    RandomTest.measurable_apply_of_forall_measurable hhm fun z => ((hφt z).mono hτ.measurableSpace_le le_rfl)
  have hEi : Integrable (fun ω => Complex.exp (Complex.I * (h ω (t • φ ω) : ℂ))) P :=
    Integrable.of_bound (GFF.measurable_exp_I_mul hhφ).aestronglyMeasurable 1
      (Eventually.of_forall fun ω => (hnorm _).le)
  have hF : (fun ω => Complex.exp (Complex.I * ((t * (h ω (φ ω) - M ω) : ℝ) : ℂ))) = fun ω =>
      Complex.exp (Complex.I * ((-(t * M ω) : ℝ) : ℂ)) * Complex.exp (Complex.I * (h ω (t • φ ω) : ℂ)) := by
    funext ω
    rw [← Complex.exp_add, map_smul, smul_eq_mul]
    congr 1
    push_cast
    ring
  have hpull := condExp_bilin_of_stronglyMeasurable_left (m := 𝓖 0) (μ := P)
    (ContinuousLinearMap.mul ℝ ℂ) he (by
      refine Integrable.of_bound ((he.mono (𝓖.le 0)).aestronglyMeasurable.mul hEi.1) 1
        (Eventually.of_forall fun ω => ?_)
      simp only [ContinuousLinearMap.mul_apply', norm_mul, hnorm, mul_one, le_refl]) hEi
  rw [hF]
  filter_upwards [hpull, hcl, hgood] with ω h1 h2 hg
  simp only [ContinuousLinearMap.mul_apply'] at h1
  rw [h1]
  have hK := hg.fwdHull_zero (hadm ω)
  have hdis : Disjoint (tsupport (t • φ ω)) (fwdHull (fun s : ℝ => W s.toNNReal ω)
      ((((((0 : ℝ≥0) : WithTop ℝ≥0)).untopD 0 : ℝ≥0)) : ℝ)) := by
    rw [WithTop.untopD_coe, hK]
    exact disjoint_empty _
  rw [h2 hdis, clauseKernel]
  -- the kernel at time `0`
  obtain ⟨hpL, hpR⟩ := hg.pos_zero
  have hw0 : (fun s : ℝ => W s.toNNReal ω) 0 = 0 := by simpa using (hg.1.isSLEPathUpTo le_rfl).w_zero
  have hmean : ∫ z, couplingMean κ (fun s : ℝ => W s.toNNReal ω) ((((((0 : ℝ≥0) : WithTop ℝ≥0)).untopD 0 : ℝ≥0)) : ℝ)
      (u ω) z * (t • φ ω) z = t * M ω := by
    rw [hMdef, ← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    simp only [WithTop.untopD_coe, NNReal.coe_zero]
    by_cases hz : z ∈ tsupport (φ ω : ℂ → ℝ)
    · have hzH : z ∈ H := Coupling.tsupport_subset_H (φ ω) hz
      have hz0 : z ≠ 0 := fun h0 => by
        have : (0 : ℝ) < z.im := hzH
        rw [h0, Complex.zero_im] at this; exact lt_irrefl _ this
      rw [Coupling.MartMeans2.couplingMean_zero κ hw0 (u ω) hz0, hudef]
      simp only [hpL, hpR, wordMean]
      show bheAt κ ρL ρR (c ω).1 (c ω).2 z * (t * φ ω z) = _
      ring
    · show couplingMean κ _ 0 (u ω) z * (t * φ ω z) = t * (wordMean κ ρL ρR c ω z * φ ω z)
      rw [image_eq_zero_of_notMem_tsupport hz]
      ring
  have hen : loewnerGreenEnergy (fun s : ℝ => W s.toNNReal ω)
      ((((((0 : ℝ≥0) : WithTop ℝ≥0)).untopD 0 : ℝ≥0)) : ℝ) (⇑(t • φ ω) : ℂ → ℝ) =
        t ^ 2 * greenEnergy (φ ω) (φ ω) := by
    have hsm : (⇑(t • φ ω) : ℂ → ℝ) = t • ⇑(φ ω) := rfl
    have hζ := hg.zeta_pos (hadm ω)
    have hd0 : Disjoint (tsupport (φ ω)) (fwdHull (fun s : ℝ => W s.toNNReal ω) ((0 : ℝ≥0) : ℝ)) := by
      rw [hK]; exact disjoint_empty _
    rw [hsm, WithTop.untopD_coe, Coupling.MartMeans.loewnerGreenEnergy_smul,
      WholeField.loewnerGreenEnergy_rpath_eq_zeroGFFTestCov hg.1.2.2.2.1
        (hg.1.isSLEPathUpTo le_rfl).w_zero (t := 0) (by simpa using hζ) (φ ω) hd0, hK, sdiff_empty,
      zeroGFFTestCov_H_eq_greenEnergy]
  rw [hmean, hen, ← Complex.exp_add, Complex.ofReal_exp]
  congr 1
  push_cast
  ring

/-- **The source pairing of the random word is the limit of the approximate pairings** almost surely. -/
theorem ae_tendsto_srcPairW_word (hcf : Coupling.MartMeans.IsCouplingCharFun κ ρL ρR P 𝓖 W VL VR ζ h)
    (hhm : Measurable h) (hc : Measurable[𝓖 0] c) (hadm : ∀ ω, IsAdmWord r (c ω))
    (hgood : ∀ᵐ ω ∂P, IsWordPath κ ρL ρR W VL VR B ζ c ω) :
    ∀ᵐ ω ∂P, Tendsto (fun k => h ω (srcTestW κ ρL ρR r (c ω) k)) atTop
      (𝓝 (srcPairW κ ρL ρR r (c ω) (h ω))) := by
  have hum : Measurable (Function.uncurry (wordMean κ ρL ρR c)) :=
    measurable_uncurry_wordMean (hc.mono (𝓖.le 0) le_rfl)
  have hu : ∀ ω, ContinuousOn (wordMean κ ρL ρR c ω) H := fun ω =>
    continuousOn_of_isBoundedHarmonicExtension (isBoundedHarmonicExtension_bheAt κ ρL ρR _ _)
  have hC : ∀ ω, ∀ z ∈ H, |wordMean κ ρL ρR c ω z| ≤ bheBound κ ρL ρR := fun ω z hz =>
    abs_bheAt_le κ ρL ρR _ _ hz
  have hcf0 : ∀ φ : Ω → TestOn upperHalfPlaneOpens, (∀ z, Measurable[𝓖 0] fun ω => φ ω z) → ∀ t : ℝ,
      P[fun ω => Complex.exp (Complex.I * ((t * (h ω (φ ω) - ∫ z, wordMean κ ρL ρR c ω z * φ ω z) : ℝ) : ℂ)) |
        𝓖 0] =ᵐ[P] fun ω => ((Real.exp (-(1 / 2) * (t ^ 2 * greenEnergy (φ ω) (φ ω))) : ℝ) : ℂ) :=
    fun φ hφ t => condExp_cexp_centred_zero hcf hhm hc hadm hgood φ hφ t
  exact ae_tendsto_srcPairW (𝒢 := 𝓖 0) (𝓖.le 0) hhm hc hadm hum hu hC hcf0

theorem measurable_srcPairW_word (hhm : Measurable h) (hc : Measurable c) :
    Measurable fun ω => srcPairW κ ρL ρR r (c ω) (h ω) := by
  have h1 := (measurable_srcPairW (nL := nL) (nR := nR) κ ρL ρR r).comp (hc.prodMk hhm)
  exact h1

/-- **The joint conditional law of a test pairing and the source pairing of the random word** (random-word form of
PROVE-LOCEXT-A3's `hjoint`): at every `𝓖`-stopping time `τ` before the local stop, for every test function `φ` and all
real `a, b`, almost surely on `{supp φ ∩ K_τ = ∅}`,
`E[e^{i (a h(φ) + b (h, v_c))} | 𝓖_τ] = exp(i (a ∫ 𝔥_τ φ + b (𝔥_τ, v_c)) − ½ (a² E_τ(φ) + 2ab E_τ(φ, v_c) + b² E_τ(v_c)))`. -/
theorem condExp_cexp_joint_word (hcf : Coupling.MartMeans.IsCouplingCharFun κ ρL ρR P 𝓖 W VL VR ζ h)
    (hhm : Measurable h) (hc : Measurable[𝓖 0] c) (hadm : ∀ ω, IsAdmWord r (c ω))
    (hgood : ∀ᵐ ω ∂P, IsWordPath κ ρL ρR W VL VR B ζ c ω) {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime 𝓖 τ)
    (hτS : ∀ᵐ ω ∂P, τ ω ≤ localStopPath r (ζ ω) fun t => W t ω) (φ : TestOn upperHalfPlaneOpens) (a b : ℝ) :
    ∀ᵐ ω ∂P, ω ∈ {ω | Disjoint (tsupport φ)
        (fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0))} →
      (P[fun ω' => Complex.exp (Complex.I * ((a * h ω' φ + b * srcPairW κ ρL ρR r (c ω') (h ω') : ℝ) : ℂ)) |
        hτ.measurableSpace]) ω =
        cfVal (a * (∫ z, couplingMean κ (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)
            (bheProc κ ρL ρR W VL VR ω ((τ ω).untopD 0)) z * φ z) +
            b * ∫ z, couplingMean κ (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)
              (bheProc κ ρL ρR W VL VR ω ((τ ω).untopD 0)) z * vSrc κ (c ω).1 (c ω).2 ρL ρR r z)
          (a ^ 2 * loewnerGreenEnergy (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0) φ +
            2 * a * b * greenCross (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0) φ
              (vSrc κ (c ω).1 (c ω).2 ρL ρR r) +
            b ^ 2 * loewnerGreenEnergy (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)
              (vSrc κ (c ω).1 (c ω).2 ρL ρR r)) := by
  have hpath : ∀ᵐ ω ∂P, W 0 ω = 0 ∧ ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω} := by
    filter_upwards [hgood] with ω hg
    exact ⟨(hg.1.isSLEPathUpTo le_rfl).w_zero, hg.1.2.2.2.1⟩
  have hτζ : ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < ζ ω := by
    filter_upwards [hgood, hτS] with ω hg hτω
    exact lt_of_le_of_lt (by exact_mod_cast hτω) (hg.localStopPath_lt (hadm ω))
  have h0τ : 𝓖 0 ≤ hτ.measurableSpace := hτ.le_measurableSpace_of_const_le fun _ => bot_le
  have hconv := ae_tendsto_srcPairW_word hcf hhm hc hadm hgood
  set ψ : ℕ → Ω → TestOn upperHalfPlaneOpens := fun k ω => a • φ + b • srcTestW κ ρL ρR r (c ω) k with hψ
  have hψm : ∀ k z, Measurable[hτ.measurableSpace] fun ω => ψ k ω z := fun k z => by
    have h1 : Measurable[𝓖 0] fun ω => srcTestW κ ρL ρR r (c ω) k z := by
      have h2 := (measurable_srcTestW_apply κ ρL ρR r k).comp
        ((measurable_id (α := (Fin nL → ℝ) × (Fin nR → ℝ))).prodMk (measurable_const (a := z)))
      exact h2.comp hc
    have h3 : Measurable[𝓖 0] fun ω => ψ k ω z := by
      show Measurable[𝓖 0] fun ω => a * φ z + b * srcTestW κ ρL ρR r (c ω) k z
      exact measurable_const.add (h1.const_mul b)
    exact h3.mono h0τ le_rfl
  refine ae_condExp_cexp_of_tendsto_on (m := hτ.measurableSpace)
    (Y := fun k ω => h ω (ψ k ω))
    (a := fun k ω => ∫ z, couplingMean κ (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)
      (bheProc κ ρL ρR W VL VR ω ((τ ω).untopD 0)) z * (ψ k ω) z)
    (q := fun k ω => loewnerGreenEnergy (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0) (ψ k ω))
    (fun k => (RandomTest.measurable_apply_of_forall_measurable hhm fun z =>
      (hψm k z).mono hτ.measurableSpace_le le_rfl).aemeasurable) (fun k => ?_) ?_ ?_
  · have hcl := isCouplingCharFun_condExp_cexp_random hcf hhm hpath hτ hτζ
      (fun ω => bheProc κ ρL ρR W VL VR ω ((τ ω).untopD 0))
      (fun ω => isBoundedHarmonicExtension_bheProc κ ρL ρR ω _) (hψm k)
    filter_upwards [hcl, hgood, hτS] with ω h1 hg hτω hD
    refine h1 (Disjoint.mono_left (tsupport_add _ _) (Disjoint.union_left ?_ ?_))
    · exact Disjoint.mono_left (tsupport_smul_subset_right (fun _ => a) φ) hD
    · exact Disjoint.mono_left (tsupport_smul_subset_right (fun _ => b) (srcTestW κ ρL ρR r (c ω) k))
        (disjoint_tsupport_srcTestW_fwdHull hg.1 hg.2.1 (hadm ω) hg.2.2 (coe_untopD_le_localStopPath hτω) k)
  · filter_upwards [hconv] with ω hω
    have e : ∀ k, h ω (ψ k ω) = a * h ω φ + b * h ω (srcTestW κ ρL ρR r (c ω) k) := fun k => by
      simp only [hψ, map_add, map_smul, smul_eq_mul]
    simp_rw [e]
    exact tendsto_const_nhds.add (hω.const_mul b)
  · filter_upwards [hgood, hτS] with ω hg hτω hD
    exact tendsto_params_srcTestW hg.1 hg.2.1 (hadm ω) hg.2.2 (coe_untopD_le_localStopPath hτω) φ hD
      (isBoundedHarmonicExtension_bheProc κ ρL ρR ω _) a b

end Clause

end LocalExt

end InteractingSLE
