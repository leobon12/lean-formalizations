/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.StagedS6Ann
import InteractingSLE.Spec.Sec5.StagedRepLaterStd
import InteractingSLE.Spec.Sec5.Aux61FibKTilt
import InteractingSLE.Spec.Theorem15Inputs

/-!
# Proposition 5.9 at depth `ℓ`, step S6 (c): the martingale and the word entrance after the last switch

Packet PROVE-STAGED-S6 (`planning/handoffs/PROVE-STAGED-S5.md` §5.2, steps 3–5). For PIECES' candidate `(ℓ, t)` on the
glued space, conditioned on the alive event `A = s3Alive` of its last switch (`μ_A = μ[|A]`, `A ∈ candFilt 0`):

* **`isChartCouplingCharFunConst_cand`**: the chart clause at fixed restarted times for `μ_A` and the Galmarino
  filtration `candFilt` (from PROVE-STAGED-S5's `ae_condExp_candFilt_full`, conditioning on `A` does not change the
  conditional expectation on `A`, and the chart mean is the integral of the coupling mean,
  `Lemma71D.integral_couplingMean_eq_chartMean`);
* **`isLocalMartingaleBefore_coupProc_cand`**: the coupling means of the restarted word in tree order are local
  martingales before `s(z) ∧ ζ` in the usual augmentation of `candFilt` (the template chain of
  `CrossCondThetaMart.imageWordFiltThetaStatement_of_chartConst`: chart clause at stopping times, transport through
  the restarted chart, `exists_isLocalMartingaleBefore_meanProcOn`);
* **`exists_isWordEntrance_cand`**: the word entrance (Wang–Wu Lemma 2.11, Aux. lemma 117's form) of the restarted
  word in tree order, driven by a Brownian motion of the usual augmentation of `candFilt` extended by the standard
  noise space `ℕ → ℝ` (`StagedRepLater.exists_isWordEntrance_std`).

Conditional helpers with distinct names; they replace no source theorem. R48: the only named input is `h44`
(`Theorem12ParamCond44Statement`, R74); nothing here uses Theorem 1.2/1.3 or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal Real
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.Sec5.CrossCond.StagedS6

open WangWu hiding ratPt exists_ratPt_dist_lt
open WangWu.ImgWord LawUnique GlueCond Cond44Ref Word49 StagedS3 StagedS4 StagedS5
open Restart Exist.StagedLaw Exist.Staged
open Sec7.AdmCode Prop513TreeExtract Prop513Schedule Prop513Target Prop59Pieces StagedRepLater
open Sec4 (IsStripGFF IsStripCounterflowDriver)
open Sec7.Lemma71C (capClock)
open StagedFinal (imgStageRhoL imgStageRhoR)

section Times

variable {ℓ : ℕ} {t : Fin ℓ → ℝ≥0}

theorem monotone_candTs (hv : IsValid ℓ t) : Monotone fun j : Fin ℓ => candTs ℓ t (j + 1) := by
  intro j j' hjj
  simp only [candTs_succ hv]
  rcases hjj.lt_or_eq with hlt | heq
  · rw [oTime_eq (hv.2 j).2.2, oTime_eq (hv.2 j').2.2]
    exact (decode_strictMono (hv.2 j').2.1 (hv.1 hlt)).le
  · rw [heq]

end Times

section Cand

variable (x₀ : ℝ) (h44 : Theorem12ParamCond44Statement.{0}) {κ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
  (hb : IsFig51Bounds κ a b a' b') {Ω : Type} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ)
  (ζ : Ω → ℝ≥0∞)

include hκ4 in
/-- **The candidate's chart clause at fixed restarted times, conditioned on the alive event.** -/
theorem isChartCouplingCharFunConst_cand (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) {us : ℂ → ℝ}
    (hus : IsBoundedHarmonicExtension (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps us)
    {ℓ : ℕ} {t : Fin ℓ → ℝ≥0} (hv : IsValid ℓ t) {s : ℝ≥0} (hs : 0 < s) :
    Sec7.Lemma71D.IsChartCouplingCharFunConst κ
      (imgStageRhoL κ (π / 2) (flowLineRhoL κ (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps
        0 (π / 2)) (fun j => candAng ℓ t j - candAng ℓ t 0) ℓ)
      (imgStageRhoR κ (π / 2) (flowLineRhoR κ (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps
        0 (π / 2)) (fun j => candAng ℓ t j - candAng ℓ t 0) ℓ)
      ((candMu x₀ (κ := κ) P h W ζ hG.1)[|s3Alive s (candW x₀ h44 hκ hκ4 hb h ℓ t)
        (candEg x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s) (lastO ℓ t : ℝ)])
      (candFilt x₀ h44 hκ hκ4 hb P h W ζ hG hcf us hv hs)
      (s3W s (candW x₀ h44 hκ hκ4 hb h ℓ t) (candEg x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s) (lastO ℓ t : ℝ))
      (s3VL (flowLineXL (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps 0) (candTs ℓ t) ℓ s
        (candW x₀ h44 hκ hκ4 hb h ℓ t) (candEg x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s) (lastO ℓ t : ℝ))
      (s3VR (flowLineXR (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps 0) (candTs ℓ t) ℓ s
        (candW x₀ h44 hκ hκ4 hb h ℓ t) (candEg x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s) (lastO ℓ t : ℝ))
      (s3ζ s (candW x₀ h44 hκ hκ4 hb h ℓ t) (candEg x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s) (lastO ℓ t : ℝ))
      (s3Chart s (candW x₀ h44 hκ hκ4 hb h ℓ t) (candEg x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s) (lastO ℓ t : ℝ))
      (2 * Real.pi * chiC κ + (candAng ℓ t ℓ - candAng ℓ t 0) * chiC κ) (chiC κ)
      (fun p => rootField (κ := κ) (x₀ := x₀) h p.1) := by
  intro r u hu φ
  set c := sourceWord (x₀ := x₀) hκ hb with hc
  set μ := candMu x₀ (κ := κ) P h W ζ hG.1 with hμ
  set Wc := candW x₀ h44 hκ hκ4 hb h ℓ t with hWc
  set Eg := candEg x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s with hEgdef
  set A := s3Alive s Wc Eg (lastO ℓ t : ℝ) with hAdef
  set 𝓐 := candFilt x₀ h44 hκ hκ4 hb P h W ζ hG hcf us hv hs with h𝓐
  have hEg := candEg_good x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s
  have hAm : MeasurableSet[𝓐 r] A := measurableSet_s3Alive_candFilt x₀ h44 hκ hκ4 hb P h W ζ hG hcf us hv hs r
  set X : Ω × HistorySpace 0 0 → ℂ := fun p' =>
    Complex.exp (Complex.I * (rootField (κ := κ) (x₀ := x₀) h p'.1 φ : ℂ)) with hXdef
  have hXm : Measurable X := Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp
    (((LQGMetric.measurable_distOn_apply φ).comp (measurable_rootField hG.1)).comp measurable_fst)))
  have hXb : ∀ p, ‖X p‖ ≤ 1 := fun p => by
    simp only [hXdef]
    rw [mul_comm, Complex.norm_exp_ofReal_mul_I]
  have hXi : Integrable X μ := Integrable.of_bound hXm.aestronglyMeasurable 1 (Eventually.of_forall hXb)
  have h1 := ae_condExp_candFilt_full x₀ h44 hκ hκ4 hb P h W ζ hG hcf hus hv hs φ r
  have h2 := Sec5.Aux61FibK.condExp_cond_ae_eq (𝓐.le r) hAm hXi
  have hAmeas : MeasurableSet A := 𝓐.le r _ hAm
  have hF := Theorem15.isOrderedForceWord_flowLine c.fn c.jumps 0
  have hK := isKilledWord_s6 (xL := flowLineXL c.fn c.jumps 0) (xR := flowLineXR c.fn c.jumps 0) hEg hF.2.1 hF.1
    hF.2.2.2 hF.2.2.1 (candTs_bounds hv) (monotone_candTs hv)
  filter_upwards [cond_absolutelyContinuous.ae_le h1, h2, ae_cond_mem hAmeas] with p hp1 hp2 hpA hlt hsupp
  have hmem : p ∈ candEr x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s φ r := ⟨hpA, hlt, hsupp⟩
  have e1 := hp2.trans (hp1 hmem)
  refine e1.trans ?_
  have hcc := isConformal_s3Chart hEg hpA
  have hvL : ∀ i, s3VL (flowLineXL c.fn c.jumps 0) (candTs ℓ t) ℓ s Wc Eg (lastO ℓ t : ℝ) i r p ≤
      s3W s Wc Eg (lastO ℓ t : ℝ) r p := fun i => by
    have := hK.ordL p r ((treeIdx ℓ _).symm i) hlt
    simpa only [s6VL, Equiv.apply_symm_apply] using this
  have hvR : ∀ j, s3W s Wc Eg (lastO ℓ t : ℝ) r p ≤
      s3VR (flowLineXR c.fn c.jumps 0) (candTs ℓ t) ℓ s Wc Eg (lastO ℓ t : ℝ) j r p := fun j => by
    have := hK.ordR p r ((treeIdx ℓ _).symm j) hlt
    simpa only [s6VR, Equiv.apply_symm_apply] using this
  have hav : Sec7.Lemma71D.IsChartAvoid (fun r' => s3W s Wc Eg (lastO ℓ t : ℝ) r' p)
      (s3ζ s Wc Eg (lastO ℓ t : ℝ) p) (s3Chart s Wc Eg (lastO ℓ t : ℝ) p) φ r := ⟨hlt, hsupp⟩
  have hI := Sec7.Lemma71D.integral_couplingMean_eq_chartMean (κ := κ)
    (ρL := imgStageRhoL κ (π / 2) (flowLineRhoL κ c.fn c.jumps 0 (π / 2)) (fun j => candAng ℓ t j - candAng ℓ t 0) ℓ)
    (ρR := imgStageRhoR κ (π / 2) (flowLineRhoR κ c.fn c.jumps 0 (π / 2)) (fun j => candAng ℓ t j - candAng ℓ t 0) ℓ)
    (w := fun r' => s3W s Wc Eg (lastO ℓ t : ℝ) r' p)
    (vL := fun i r' => s3VL (flowLineXL c.fn c.jumps 0) (candTs ℓ t) ℓ s Wc Eg (lastO ℓ t : ℝ) i r' p)
    (vR := fun j r' => s3VR (flowLineXR c.fn c.jumps 0) (candTs ℓ t) ℓ s Wc Eg (lastO ℓ t : ℝ) j r' p)
    (ζ := s3ζ s Wc Eg (lastO ℓ t : ℝ) p) (c := s3Chart s Wc Eg (lastO ℓ t : ℝ) p)
    (a := 2 * Real.pi * chiC κ + (candAng ℓ t ℓ - candAng ℓ t 0) * chiC κ) (k := chiC κ) (φ := φ) (t := r) hcc.1
    (StagedS4.continuousOn_s3W hEg p) hav hvL hvR (hu p)
  unfold candF s4F
  rw [← hI]
  rfl

include hκ4 in
/-- **The word entrance of the candidate's restarted word after the last switch** (Wang–Wu Lemma 2.11 for the killed
word in tree order), conditioned on the alive event: on `(glued space) × (ℕ → ℝ)` there is a Brownian motion of the
usual augmentation of `candFilt` (extended by an independent filtration) driving the integrated equations of the
restarted word before its lifetime. -/
theorem exists_isWordEntrance_cand (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) {us : ℂ → ℝ}
    (hus : IsBoundedHarmonicExtension (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps us)
    {ℓ : ℕ} {t : Fin ℓ → ℝ≥0} (hv : IsValid ℓ t) {s : ℝ≥0} (hs : 0 < s)
    (hA0 : candMu x₀ (κ := κ) P h W ζ hG.1 (s3Alive s (candW x₀ h44 hκ hκ4 hb h ℓ t)
      (candEg x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s) (lastO ℓ t : ℝ)) ≠ 0) :
    ∃ (P₀ : Measure (ℕ → ℝ)) (_ : IsProbabilityMeasure P₀)
      (𝓦 : Filtration ℝ≥0 (inferInstance : MeasurableSpace (ℕ → ℝ)))
      (B : ℝ≥0 → (Ω × HistorySpace 0 0) × (ℕ → ℝ) → ℝ),
      IsFilteredBrownianReal (WholeField.prodFiltration (usualAugmentation
        (candFilt x₀ h44 hκ hκ4 hb P h W ζ hG hcf us hv hs)
        ((candMu x₀ (κ := κ) P h W ζ hG.1)[|s3Alive s (candW x₀ h44 hκ hκ4 hb h ℓ t)
          (candEg x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s) (lastO ℓ t : ℝ)])) 𝓦) B
        (((candMu x₀ (κ := κ) P h W ζ hG.1)[|s3Alive s (candW x₀ h44 hκ hκ4 hb h ℓ t)
          (candEg x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s) (lastO ℓ t : ℝ)]).prod P₀) ∧
      (∀ p, Continuous fun r => B r p) ∧
      ∀ᵐ p ∂(((candMu x₀ (κ := κ) P h W ζ hG.1)[|s3Alive s (candW x₀ h44 hκ hκ4 hb h ℓ t)
          (candEg x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s) (lastO ℓ t : ℝ)]).prod P₀),
        Sec7.Aux117.IsWordEntrance κ
          (fun i => s6VL (flowLineXL (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps 0)
            (candTs ℓ t) ℓ s (candW x₀ h44 hκ hκ4 hb h ℓ t) (candEg x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s)
            (lastO ℓ t : ℝ) i 0 p.1)
          (fun j => s6VR (flowLineXR (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps 0)
            (candTs ℓ t) ℓ s (candW x₀ h44 hκ hκ4 hb h ℓ t) (candEg x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s)
            (lastO ℓ t : ℝ) j 0 p.1)
          (fun i => imgStageRhoL κ (π / 2) (flowLineRhoL κ (sourceWord (x₀ := x₀) hκ hb).fn
            (sourceWord (x₀ := x₀) hκ hb).jumps 0 (π / 2)) (fun j => candAng ℓ t j - candAng ℓ t 0) ℓ
            (treeIdx ℓ _ i))
          (fun j => imgStageRhoR κ (π / 2) (flowLineRhoR κ (sourceWord (x₀ := x₀) hκ hb).fn
            (sourceWord (x₀ := x₀) hκ hb).jumps 0 (π / 2)) (fun j => candAng ℓ t j - candAng ℓ t 0) ℓ
            (treeIdx ℓ _ j))
          (fun r => s3W s (candW x₀ h44 hκ hκ4 hb h ℓ t) (candEg x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s)
            (lastO ℓ t : ℝ) r p.1)
          (fun i r => s6VL (flowLineXL (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps 0)
            (candTs ℓ t) ℓ s (candW x₀ h44 hκ hκ4 hb h ℓ t) (candEg x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s)
            (lastO ℓ t : ℝ) i r p.1)
          (fun j r => s6VR (flowLineXR (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps 0)
            (candTs ℓ t) ℓ s (candW x₀ h44 hκ hκ4 hb h ℓ t) (candEg x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s)
            (lastO ℓ t : ℝ) j r p.1)
          (fun r => B r p)
          (s3ζ s (candW x₀ h44 hκ hκ4 hb h ℓ t) (candEg x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s) (lastO ℓ t : ℝ)
            p.1) := by
  set c := sourceWord (x₀ := x₀) hκ hb with hc
  set μ := candMu x₀ (κ := κ) P h W ζ hG.1 with hμ
  set Wc := candW x₀ h44 hκ hκ4 hb h ℓ t with hWc
  set Eg := candEg x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s with hEgdef
  set A := s3Alive s Wc Eg (lastO ℓ t : ℝ) with hAdef
  set μA := μ[|A] with hμA
  have : IsProbabilityMeasure μA := cond_isProbabilityMeasure hA0
  set 𝓐 := candFilt x₀ h44 hκ hκ4 hb P h W ζ hG hcf us hv hs with h𝓐
  set 𝓖 := usualAugmentation 𝓐 μA with h𝓖
  have h𝓐𝓖 : 𝓐 ≤ 𝓖 := Ito.le_usualAugmentation 𝓐 μA
  have : 𝓖.IsRightContinuous := Ito.isRightContinuous_usualAugmentation _ _
  have hnull : ∀ s', MeasurableSet s' → μA s' = 0 → MeasurableSet[𝓖 0] s' := fun s' hs' h0 =>
    Ito.measurableSet_usualAugmentation_of_null hs' h0 0
  have hEg := candEg_good x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s
  have hF := Theorem15.isOrderedForceWord_flowLine c.fn c.jumps 0
  have hK := isKilledWord_s6 (xL := flowLineXL c.fn c.jumps 0) (xR := flowLineXR c.fn c.jumps 0) hEg hF.2.1 hF.1
    hF.2.2.2 hF.2.2.1 (candTs_bounds hv) (monotone_candTs hv)
  -- adaptedness
  have hWa : StronglyAdapted 𝓖 (s3W s Wc Eg (lastO ℓ t : ℝ)) := fun r =>
    (stronglyAdapted_s3W_candFilt x₀ h44 hκ hκ4 hb P h W ζ hG hcf us hv hs r).mono (h𝓐𝓖 r)
  have hVLa : ∀ i, StronglyAdapted 𝓖
      (s6VL (flowLineXL c.fn c.jumps 0) (candTs ℓ t) ℓ s Wc Eg (lastO ℓ t : ℝ) i) := fun i r =>
    (stronglyAdapted_s6VL_candFilt x₀ h44 hκ hκ4 hb P h W ζ hG hcf us hv hs _ i r).mono (h𝓐𝓖 r)
  have hVRa : ∀ j, StronglyAdapted 𝓖
      (s6VR (flowLineXR c.fn c.jumps 0) (candTs ℓ t) ℓ s Wc Eg (lastO ℓ t : ℝ) j) := fun j r =>
    (stronglyAdapted_s6VR_candFilt x₀ h44 hκ hκ4 hb P h W ζ hG hcf us hv hs _ j r).mono (h𝓐𝓖 r)
  have hζm : ∀ r : ℝ≥0, MeasurableSet[𝓖 r] {p | s3ζ s Wc Eg (lastO ℓ t : ℝ) p ≤ r} := fun r => by
    have h1 := (measurableSet_lt_s3ζ_candFilt x₀ h44 hκ hκ4 hb P h W ζ hG hcf us hv hs r).compl
    convert h𝓐𝓖 r _ h1 using 1
    ext p
    simp only [mem_ofPred_eq, mem_compl_iff, not_lt]
    exact Iff.rfl
  -- the announcing sequence
  have hgoodA : ∀ᵐ p ∂μA, p ∈ Eg := cond_absolutelyContinuous.ae_le
    ((ae_good_cand x₀ h44 hκ hκ4 hb P h W ζ hG hcf ℓ t hv hs).mono fun p hp => hp.1)
  obtain ⟨hσ0, hσm, hσT, hσlim⟩ := isAnnouncingSeq_s6Ann x₀ h44 hκ hκ4 hb P h W ζ hG hcf us hv hs hgoodA
  have hσ : ∀ n, IsStoppingTime 𝓖 fun p => (s6Ann s Wc Eg (lastO ℓ t : ℝ) n p : WithTop ℝ≥0) := fun n r =>
    h𝓐𝓖 r _ (hσ0 n r)
  have hT : Coupling.IsAnnouncingSeq 𝓖 μA (s3ζ s Wc Eg (lastO ℓ t : ℝ)) (s6Ann s Wc Eg (lastO ℓ t : ℝ)) :=
    ⟨hσ, hσm, hσT, hσlim⟩
  -- the chart clause at stopping times and its transport
  have hch := isMeasChart_s3Chart_candFilt x₀ h44 hκ hκ4 hb P h W ζ hG hcf us hv hs
  have hFm : Measurable fun p : Ω × HistorySpace 0 0 => rootField (κ := κ) (x₀ := x₀) h p.1 :=
    (measurable_rootField hG.1).comp measurable_fst
  have hcf1 := isChartCouplingCharFunConst_comp_equiv
    (isChartCouplingCharFunConst_cand x₀ h44 hκ hκ4 hb P h W ζ hG hcf hus hv hs) (treeIdx ℓ _) (treeIdx ℓ _)
  have hcfU := Sec7.Lemma71D.isChartCouplingCharFun_usualAugmentation (P := μA) hFm hch.conf hch.lift
    (fun p => hK.contW p) (fun i p => (hK.pathL p i).1) (fun j p => (hK.pathR p j).1)
    (fun p r hr => ⟨fun i => hK.ordL p r i hr, fun j => hK.ordR p r j hr⟩) hcf1
  set a₀ : ℝ := 2 * Real.pi * chiC κ + (candAng ℓ t ℓ - candAng ℓ t 0) * chiC κ with ha₀
  set h' : Ω × HistorySpace 0 0 → DistOn upperHalfPlaneOpens := fun p =>
    Sec7.Lemma71K.chartField (s3Chart s Wc Eg (lastO ℓ t : ℝ) p) a₀ (chiC κ) (rootField (κ := κ) (x₀ := x₀) h p.1)
    with hh'
  have ht : ∀ p, IsChartTransport (s3Chart s Wc Eg (lastO ℓ t : ℝ) p) 1 a₀ (chiC κ)
      (rootField (κ := κ) (x₀ := x₀) h p.1) (h' p) := fun p =>
    Sec7.Lemma71K.isChartTransport_chartField (hch.conf p) (hch.lift p) _ _ _
  have hdom0 : ∀ z, MeasurableSet[𝓐 0] {p | z ∈ (s3Chart s Wc Eg (lastO ℓ t : ℝ) p).dom} := fun z =>
    hch.measurableSet_mem (mX := 𝓐 0) z
  have hdom : ∀ z, MeasurableSet[𝓖 0] {p | z ∈ (s3Chart s Wc Eg (lastO ℓ t : ℝ) p).dom} := fun z =>
    h𝓐𝓖 0 _ (hdom0 z)
  have hfwd : ∀ z, Measurable[𝓖 0] ({p | z ∈ (s3Chart s Wc Eg (lastO ℓ t : ℝ) p).dom}.indicator
      fun p => (s3Chart s Wc Eg (lastO ℓ t : ℝ) p).1 z) := fun z => (hch.fwd z).mono (h𝓐𝓖 0) le_rfl
  have hliftm : ∀ z, Measurable[𝓖 0] ({p | z ∈ (s3Chart s Wc Eg (lastO ℓ t : ℝ) p).dom}.indicator
      fun p => (s3Chart s Wc Eg (lastO ℓ t : ℝ) p).2.2 z) := fun z => (hch.lft z).mono (h𝓐𝓖 0) le_rfl
  have hcf' := Coupling.MartMeans2.isCouplingCharFun_of_isChartTransport (P := μA) hch.conf hdom hfwd hliftm
    hch.lift hFm (Eventually.of_forall fun p => ⟨hK.w_zero p, hK.contW p⟩) hcfU ht
  have hh'm : Measurable h' := by
    have hm := Chart.measurable_chartTransport_random' hch.conf (fun z => 𝓐.le 0 _ (hdom0 z))
      (fun z => (hch.fwd z).mono (𝓐.le 0) le_rfl) (fun z => (hch.lft z).mono (𝓐.le 0) le_rfl) hch.lift hFm 1
      a₀ (chiC κ)
    have e : h' = fun p => Chart.chartTransport (hch.conf p) 1 a₀ (chiC κ) (rootField (κ := κ) (x₀ := x₀) h p.1) := by
      funext p
      simp only [hh', Sec7.Lemma71K.chartField]
      exact dite_eq_left_of_eq_true (eq_true (hch.conf p))
    rw [e]
    exact hm
  have hpos : ∀ p, (0 : ℝ≥0∞) < s3ζ s Wc Eg (lastO ℓ t : ℝ) p := fun p => by
    refine lt_arcζ_iff.2 ⟨mem_univ _, ?_⟩
    rw [add_zero]
    exact s3Start_lt_kLife' hEg (lastO ℓ t : ℝ) p
  have hint : ∀ φ : TestOn upperHalfPlaneOpens, Integrable (fun p => h' p φ) μA := fun φ =>
    integrable_apply_of_isCouplingCharFun_of_bounded hcf'
      (Eventually.of_forall fun p => ⟨hpos p, hK.contW p, hK.w_zero p⟩)
      φ ((LQGMetric.measurable_distOn_apply φ).comp hh'm)
  -- the martingale clause
  have hWb : AdaptedBefore 𝓖 (s3ζ s Wc Eg (lastO ℓ t : ℝ)) (s3W s Wc Eg (lastO ℓ t : ℝ)) :=
    MartChar.adaptedBefore_of_stronglyAdapted hζm hWa
  have hmart : ∀ z ∈ H, MartChar.IsLocalMartingaleBefore 𝓖 μA
      (fun p => min (QuantumZipper.swallowTime (MartChar.wpath (s3W s Wc Eg (lastO ℓ t : ℝ)) p) z : WithTop ℝ≥0)
        (s6T s Wc Eg (lastO ℓ t : ℝ) p))
      (MartChar.coupProc κ
        (fun i => imgStageRhoL κ (π / 2) (flowLineRhoL κ c.fn c.jumps 0 (π / 2))
          (fun j => candAng ℓ t j - candAng ℓ t 0) ℓ (treeIdx ℓ _ i))
        (fun j => imgStageRhoR κ (π / 2) (flowLineRhoR κ c.fn c.jumps 0 (π / 2))
          (fun j => candAng ℓ t j - candAng ℓ t 0) ℓ (treeIdx ℓ _ j))
        (s3W s Wc Eg (lastO ℓ t : ℝ)) (s6VL (flowLineXL c.fn c.jumps 0) (candTs ℓ t) ℓ s Wc Eg (lastO ℓ t : ℝ))
        (s6VR (flowLineXR c.fn c.jumps 0) (candTs ℓ t) ℓ s Wc Eg (lastO ℓ t : ℝ)) z) := by
    intro z hz
    obtain ⟨G, hG0, hGae, hloc⟩ := Coupling.MartMeans2.exists_isLocalMartingaleBefore_meanProcOn hnull hWb
      (fun i => MartChar.adaptedBefore_of_stronglyAdapted hζm (hVLa i))
      (fun j => MartChar.adaptedBefore_of_stronglyAdapted hζm (hVRa j))
      (Eventually.of_forall fun p => ⟨hK.w_zero p, hK.contW p,
        ⟨fun i => (hK.pathL p i).1, fun j => (hK.pathR p j).1⟩,
        fun r hr => ⟨fun i => hK.ordL p r i hr, fun j => hK.ordR p r j hr⟩⟩)
      hT hint hcf' (fun p r => MartChar.meanExt κ _ _ (s3W s Wc Eg (lastO ℓ t : ℝ) r p)
        (fun i => s6VL (flowLineXL c.fn c.jumps 0) (candTs ℓ t) ℓ s Wc Eg (lastO ℓ t : ℝ) i r p)
        (fun j => s6VR (flowLineXR c.fn c.jumps 0) (candTs ℓ t) ℓ s Wc Eg (lastO ℓ t : ℝ) j r p))
      (fun p r => MartChar.isBoundedHarmonicExtension_meanExt κ _ _ _ _ _) hz
    exact Restart.ConverseBefore.isLocalMartingaleBefore_coupProc_of_meanProcOn hnull hG0 hGae
      (Restart.ConverseBefore.measurable_coupProc_zero hK.w_zero
        (fun i => ((hVLa i 0).measurable.mono (𝓖.le 0) le_rfl))
        (fun j => ((hVRa j 0).measurable.mono (𝓖.le 0) le_rfl)) hz) hloc
  exact StagedRepLater.exists_isWordEntrance_std hκ hnull hK hWa hVLa hVRa hσ hσm
    (fun n p => s6Ann_lt_s3ζ hEg n p) hσlim hmart

end Cand

end InteractingSLE.Sec5.CrossCond.StagedS6
