/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.ImgChartConstAsm

/-!
# The fixed-image-time chart clause of the contact step (`ImgChartConstStatement`), steps R1–R6

Packet PROVE-WW-B19, Astra's follow-up note, Part E (E.3: identification at deterministic forward times; E.4: the
passage of the full Gaussian characteristic functions to optional times by upper dyadic approximation; E.6: random
chart and the capacity clock). PROVE-WW-B18's named input `ImgChartConstStatement` (the chart coupling clause of the
explicit image word at **fixed image times** of the raw filtration `imgRaw`) is reduced here to one precise
measurability statement about the stopped histories (`ImgMarksStatement`).

Route (it replaces B18's R3–R6; the σ-algebras need not be monotone in the forward time, so no forward filtration and
no usual augmentation is built):

* at each rational forward time `t > 0`, the history-marked two-slit law (`ae_condExp_twoSlit_glue_eq_imgF`, R1) gives
  `E[e^{i(h,φ)} | 𝒜_{A_t ∪ G} ∨ marks_t] = imgF(σ(t))` on the forward validity event `imgAv φ t`;
* for a fixed image time `r`, its forward time `θ_r = σ⁻¹(r)` is measurable (`measurable_imgTheta`), and along the
  strict upper dyadic times `dyF n θ_r ↓ θ_r` the validity event holds eventually and `imgF(σ(dyF n θ_r)) → imgF(r)`
  (`tendsto_imgF_dyF`);
* the pieces `A ∩ {⌊2ⁿθ_r⌋ = k} ∩ imgAv φ ((k+1)/2ⁿ)`, `A ∈ imgRaw r`, are (up to null sets) in the marks at
  `(k+1)/2ⁿ` — this is **`ImgMarksStatement`** (the image word before the forward time `t` is a function of the
  forward history stopped at `t` and the reverse history stopped at `s`);
* the abstract optional passage `ChartConst.setIntegral_eq_of_dyadic` then gives `∫_{A ∩ E_r} e^{i(h,φ)} =
  ∫_{A ∩ E_r} imgF(r)` for all `A ∈ imgRaw r`, and `imgF(r)` is `imgRaw r`-measurable on the validity event `E_r`
  (`measurable_imgChartAvoid_raw`, R5), so `E[e^{i(h,φ)} | imgRaw r] = imgF(r)` on `E_r`;
* `Lemma71D.integral_couplingMean_eq_chartMean` turns the chart mean into the clause's `couplingMean` form for every
  bounded harmonic extension (R6, the image time `0`, is covered by the same passage: `θ_0 = 0`).

## Main results

* `ImgMarksStatement` (named input: stopped-history measurability of the image word before a forward time);
* **`imgChartConstStatement_of_marks`**: `ImgMarksStatement → ImgChartConstStatement`;
* `reverseTipContactStatement_of_marks`.

Conditional helpers; they replace no source theorem.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric Complex
open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.WangWu

open Sec7.Lemma71C (capClock)
open ImgWord LawUnique WholeField LocalSets Coupling ChartConst

/-- **Named input: the image word before a forward time is known from the two stopped histories.** In the setting of
`ImgChartConstStatement` (glued measure `μ`, good set `E`), for rational `s > 0`: (1) for every image time `r`,
rational forward times `0 ≤ t' ≤ t`, `0 < t`, and every `A ∈ imgRaw r`, the event `A ∩ {t' before contact, r < σ(t')}`
is, up to a `μ`-null set, in the marks `twoSlitMarks t s` (forward history stopped at `t`, reverse history stopped at
`s`); (2) for every rational `t > 0` and test function `φ`, the forward validity event `{t before contact, supp φ
outside the image hull at σ(t) in the chart}` is, up to a null set, in the same marks (Astra's follow-up note, E.2 and
E.6: "R and a mapped stopped prefix recover its original geometric prefix ... The capacity clock is adapted to
σ(R, γ[0,t])"). -/
def ImgMarksStatement : Prop :=
  ∀ (rL rR : ℝ), 0 ≤ rL → 0 ≤ rR →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P] (𝓕 : Filtration ℝ≥0 mΩ)
      (W : ℝ≥0 → Ω → ℝ) (VL VR : Fin 1 → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞)
      (h : Ω → DistOn upperHalfPlaneOpens)
      (hC : IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ h)
      {Ω₂ : Type u} {mΩ₂ : MeasurableSpace Ω₂} (P₂ : Measure Ω₂) [IsProbabilityMeasure P₂]
      (𝓕₂ : Filtration ℝ≥0 mΩ₂) (W₂ : ℝ≥0 → Ω₂ → ℝ) (VL₂ VR₂ : Fin 1 → ℝ≥0 → Ω₂ → ℝ) (B₂ : ℝ≥0 → Ω₂ → ℝ)
      (ζ₂ : Ω₂ → ℝ≥0∞) (h₂ : Ω₂ → DistOn upperHalfPlaneOpens),
      IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rR) (fun _ => rL) P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ h₂ →
      P.map h = P₂.map (fun ω => reflectField (h₂ ω)) →
      ∀ (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 1 1)) [IsMarkovKernel k],
        P₂.map (fun ω => (reflectField (h₂ ω), killedHistory W₂ VL₂ VR₂ ζ₂ ω)) =
          P₂.map (fun ω => reflectField (h₂ ω)) ⊗ₘ k →
        ∀ s : ℚ, 0 < s →
          (∀ (r : ℝ≥0) (t' t : ℚ), 0 ≤ t' → t' ≤ t → 0 < t → ∀ A : Set (Ω × HistorySpace 1 1),
            MeasurableSet[imgRaw s ζ W (glueGood (glueMeasure P k h hC.2.1) s ζ W) r] A →
            ∃ B', MeasurableSet[twoSlitMarks W VL VR ζ t s] B' ∧ B' =ᵐ[glueMeasure P k h hC.2.1]
              A ∩ {p | (t' : ℝ) ∈ gPre s ζ W (glueGood (glueMeasure P k h hC.2.1) s ζ W) p ∧
                (r : ℝ) < capClock (gCurve s ζ W (glueGood (glueMeasure P k h hC.2.1) s ζ W) p) t'}) ∧
          ∀ (t : ℚ), 0 < t → ∀ φ : TestOn upperHalfPlaneOpens,
            ∃ B', MeasurableSet[twoSlitMarks W VL VR ζ t s] B' ∧ B' =ᵐ[glueMeasure P k h hC.2.1]
              {p | (t : ℝ) ∈ gPre s ζ W (glueGood (glueMeasure P k h hC.2.1) s ζ W) p ∧
                Sec7.Lemma71D.IsChartAvoid (fun r => imgW s ζ W (glueGood (glueMeasure P k h hC.2.1) s ζ W) r p)
                  (imgT s ζ W (glueGood (glueMeasure P k h hC.2.1) s ζ W) p : ℝ≥0∞) (imgChart s p.2) φ
                  (capClock (gCurve s ζ W (glueGood (glueMeasure P k h hC.2.1) s ζ W) p) t).toNNReal}

namespace ChartConst

/-- The rational dyadic grid point `(k + 1)/2ⁿ`. -/
def dyqQ (n k : ℕ) : ℚ := ((k : ℚ) + 1) / 2 ^ n

theorem dyqQ_coe (n k : ℕ) : ((dyqQ n k : ℚ) : ℝ) = ((dyq n k : ℝ≥0) : ℝ) := by
  rw [dyq_coe, dyqQ]
  push_cast
  ring

theorem dyqQ_pos (n k : ℕ) : 0 < dyqQ n k := by
  rw [dyqQ]
  positivity

end ChartConst

section Main

variable {rL rR : ℝ} {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL VR : Fin 1 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
  {h : Ω → DistOn upperHalfPlaneOpens}
  {Ω₂ : Type u} {mΩ₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
  {𝓕₂ : Filtration ℝ≥0 mΩ₂} {W₂ : ℝ≥0 → Ω₂ → ℝ} {VL₂ VR₂ : Fin 1 → ℝ≥0 → Ω₂ → ℝ} {B₂ : ℝ≥0 → Ω₂ → ℝ}
  {ζ₂ : Ω₂ → ℝ≥0∞} {h₂ : Ω₂ → DistOn upperHalfPlaneOpens}

omit [IsProbabilityMeasure P] in
/-- The pieces of the dyadic level sets, read through the capacity clock (deterministic, on a good sample alive at
the image time `r`). -/
theorem dyIdx_imgTheta_and_mem_imgAv_iff {s : ℚ} {E : Set (Ω × HistorySpace 1 1)} (hs : 0 < s)
    (hEg : ∀ p ∈ E, IsGlueGood s ζ W p) {p : Ω × HistorySpace 1 1} (hpE : p ∈ E) {r : ℝ≥0}
    (hr : (r : WithTop ℝ≥0) < imgT s ζ W E p) (n k : ℕ) (φ : TestOn upperHalfPlaneOpens) :
    (dyIdx n (imgTheta s ζ W E r p) = k ∧ p ∈ imgAv s ζ W E φ (dyq n k)) ↔
      (((dyqQ n k : ℚ) : ℝ) ∈ gPre s ζ W E p ∧ (r : ℝ) < capClock (gCurve s ζ W E p) (dyqQ n k)) ∧
        ¬ ((((k : ℚ) / 2 ^ n : ℚ) : ℝ) ∈ gPre s ζ W E p ∧
          (r : ℝ) < capClock (gCurve s ζ W E p) ((k : ℚ) / 2 ^ n : ℚ)) ∧
        (((dyqQ n k : ℚ) : ℝ) ∈ gPre s ζ W E p ∧ Sec7.Lemma71D.IsChartAvoid (fun t => imgW s ζ W E t p)
          (imgT s ζ W E p : ℝ≥0∞) (imgChart s p.2) φ
          (capClock (gCurve s ζ W E p) (dyqQ n k)).toNNReal) := by
  have hγ := isKilledArc_gCurve hs hEg p
  obtain ⟨hθP, hθc⟩ := imgTheta_spec hs hEg hr
  set θ := imgTheta s ζ W E r p with hθdef
  have hc : ((dyq n k : ℝ≥0) : ℝ) = ((dyqQ n k : ℚ) : ℝ) := (dyqQ_coe n k).symm
  have hc' : ((((k : ℚ) / 2 ^ n : ℚ) : ℝ)) = (((k : ℝ≥0) / 2 ^ n : ℝ≥0) : ℝ) := by push_cast; ring
  -- `θ < u ↔ r < σ(u)` for `u` before contact
  have key : ∀ u : ℝ, u ∈ gPre s ζ W E p → ((θ : ℝ) < u ↔ (r : ℝ) < capClock (gCurve s ζ W E p) u) := by
    intro u hu
    constructor
    · intro hlt
      rw [← hθc]
      exact hγ.strictMonoOn_capClock hθP hu hlt
    · intro hlt
      by_contra hle
      have := hγ.strictMonoOn_capClock.monotoneOn hu hθP (not_lt.1 hle)
      rw [hθc] at this
      linarith
  have hk0 : (0 : ℝ) ≤ (((k : ℚ) / 2 ^ n : ℚ) : ℝ) := by push_cast; positivity
  have hkt : (((k : ℚ) / 2 ^ n : ℚ) : ℝ) ≤ ((dyqQ n k : ℚ) : ℝ) := by
    rw [dyqQ]; push_cast
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  rw [dyIdx_eq_iff, imgAv, mem_ofPred_eq, hc]
  constructor
  · rintro ⟨⟨h1, h2⟩, -, hP, hav⟩
    have hP' := hγ.icc _ hP ⟨hk0, hkt⟩
    have h2' : (θ : ℝ) < ((dyqQ n k : ℚ) : ℝ) := by rw [← hc]; exact_mod_cast h2
    refine ⟨⟨hP, (key _ hP).1 h2'⟩, fun hh => ?_, hP, hav⟩
    have h4 := (key _ hP').2 hh.2
    rw [hc'] at h4
    exact absurd (show θ < (k : ℝ≥0) / 2 ^ n by exact_mod_cast h4) (not_lt.2 h1)
  · rintro ⟨⟨hP, h2⟩, h3, -, hav⟩
    have hP' := hγ.icc _ hP ⟨hk0, hkt⟩
    refine ⟨⟨?_, ?_⟩, hpE, hP, hav⟩
    · by_contra hlt
      have h5 : (θ : ℝ) < (((k : ℚ) / 2 ^ n : ℚ) : ℝ) := by rw [hc']; exact_mod_cast not_le.1 hlt
      exact h3 ⟨hP', (key _ hP').1 h5⟩
    · have := (key _ hP).2 h2
      rw [← hc] at this
      exact_mod_cast this

/-- **The clause at a fixed image time from the stopped-history measurability** (Astra's E.4 with the passage of the
characteristic functions along strict upper dyadic forward times): almost surely on the validity event at the image
time `r`, `E[e^{i(h,φ)} | imgRaw r] = imgF(r)`. -/
theorem ae_condExp_imgRaw_eq_imgF (hL : 0 ≤ rL) (hR : 0 ≤ rR)
    (hC : IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ h)
    (hC₂ : IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rR) (fun _ => rL) P₂ 𝓕₂ W₂ VL₂ VR₂ B₂
      ζ₂ h₂)
    (hlaw : P.map h = P₂.map (fun ω => reflectField (h₂ ω)))
    (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 1 1)) [IsMarkovKernel k]
    (hk : P₂.map (fun ω => (reflectField (h₂ ω), killedHistory W₂ VL₂ VR₂ ζ₂ ω)) =
      P₂.map (fun ω => reflectField (h₂ ω)) ⊗ₘ k) {s : ℚ} (hs : 0 < s)
    (hM1 : ∀ (r : ℝ≥0) (t' t : ℚ), 0 ≤ t' → t' ≤ t → 0 < t → ∀ A : Set (Ω × HistorySpace 1 1),
      MeasurableSet[imgRaw s ζ W (glueGood (glueMeasure P k h hC.2.1) s ζ W) r] A →
      ∃ B', MeasurableSet[twoSlitMarks W VL VR ζ t s] B' ∧ B' =ᵐ[glueMeasure P k h hC.2.1]
        A ∩ {p | (t' : ℝ) ∈ gPre s ζ W (glueGood (glueMeasure P k h hC.2.1) s ζ W) p ∧
          (r : ℝ) < capClock (gCurve s ζ W (glueGood (glueMeasure P k h hC.2.1) s ζ W) p) t'})
    (hM3 : ∀ (t : ℚ), 0 < t → ∀ φ : TestOn upperHalfPlaneOpens,
      ∃ B', MeasurableSet[twoSlitMarks W VL VR ζ t s] B' ∧ B' =ᵐ[glueMeasure P k h hC.2.1]
        {p | (t : ℝ) ∈ gPre s ζ W (glueGood (glueMeasure P k h hC.2.1) s ζ W) p ∧
          Sec7.Lemma71D.IsChartAvoid (fun r => imgW s ζ W (glueGood (glueMeasure P k h hC.2.1) s ζ W) r p)
            (imgT s ζ W (glueGood (glueMeasure P k h hC.2.1) s ζ W) p : ℝ≥0∞) (imgChart s p.2) φ
            (capClock (gCurve s ζ W (glueGood (glueMeasure P k h hC.2.1) s ζ W) p) t).toNNReal})
    (r : ℝ≥0) (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ p ∂(glueMeasure P k h hC.2.1),
      p ∈ {p | Sec7.Lemma71D.IsChartAvoid (fun t => imgW s ζ W (glueGood (glueMeasure P k h hC.2.1) s ζ W) t p)
        (imgT s ζ W (glueGood (glueMeasure P k h hC.2.1) s ζ W) p : ℝ≥0∞) (imgChart s p.2) φ r} →
      (glueMeasure P k h hC.2.1)[fun p' => Complex.exp (Complex.I * (h p'.1 φ : ℂ)) |
          imgRaw s ζ W (glueGood (glueMeasure P k h hC.2.1) s ζ W) r] p =
        imgF rL rR s ζ W (glueGood (glueMeasure P k h hC.2.1) s ζ W) φ r p := by
  set μ := glueMeasure P k h hC.2.1 with hμ
  set E := glueGood μ s ζ W with hEdef
  have hE : MeasurableSet E := measurableSet_glueGood
  have hEg : ∀ p ∈ E, IsGlueGood s ζ W p := fun p hp => isGlueGood_of_mem_glueGood p hp
  have hW : AdaptedBefore 𝓕 ζ W := hC.1.2.1
  obtain ⟨hX, -⟩ := hC.2.2.2
  have hEae : ∀ᵐ p ∂μ, p ∈ E := ae_mem_glueGood (ae_isGlueGood hL hR hC hC₂ hlaw k hk hs)
  obtain ⟨u₀, hu₀⟩ := Sec4.exists_isBoundedHarmonicExtension_forceBoundaryData 4 (fun _ : Fin 1 => rL)
    (fun _ : Fin 1 => rR) LP.twoSeedXL LP.twoSeedXR
  have hXm : Measurable fun p : Ω × HistorySpace 1 1 => Complex.exp (Complex.I * (h p.1 φ : ℂ)) :=
    Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp
      (((LQGMetric.measurable_distOn_apply φ).comp hC.2.1).comp measurable_fst)))
  have hXb : ∀ p : Ω × HistorySpace 1 1, ‖Complex.exp (Complex.I * (h p.1 φ : ℂ))‖ ≤ 1 := fun p => by
    rw [mul_comm, Complex.norm_exp_ofReal_mul_I]
  have hXi : Integrable (fun p : Ω × HistorySpace 1 1 => Complex.exp (Complex.I * (h p.1 φ : ℂ))) μ :=
    Integrable.of_bound hXm.aestronglyMeasurable 1 (Eventually.of_forall hXb)
  obtain ⟨hErm, hmeanm, hvarm⟩ := measurable_imgChartAvoid_raw rL rR hs hW hE hEg r φ
  set Er := {p : Ω × HistorySpace 1 1 | Sec7.Lemma71D.IsChartAvoid (fun t => imgW s ζ W E t p)
    (imgT s ζ W E p : ℝ≥0∞) (imgChart s p.2) φ r} with hErdef
  -- the candidate is `imgRaw r`-measurable on `Er`
  have hGm : Measurable[imgRaw s ζ W E r] (Er.indicator (imgF rL rR s ζ W E φ r)) := by
    have e : Er.indicator (imgF rL rR s ζ W E φ r) = Er.indicator (fun p => Complex.exp (Complex.I *
        ((Er.indicator (fun p => Sec7.Lemma71D.chartMean 4 (imgρ rL) (imgρ rR) (fun t => imgW s ζ W E t p)
          (fun i t => imgVL s ζ W E i t p) (fun j t => imgVR s ζ W E j t p) (imgChart s p.2) 0 0 φ r) p : ℝ) : ℂ) -
        (((1 / 2 : ℝ) * Er.indicator (fun p => Sec7.Lemma71D.chartVar (fun t => imgW s ζ W E t p)
          (imgChart s p.2) φ r) p : ℝ) : ℂ))) := by
      refine Set.indicator_congr fun p hp => ?_
      simp only [imgF, indicator_of_mem hp]
    rw [e]
    refine Measurable.indicator ?_ hErm
    exact Complex.measurable_exp.comp ((Complex.measurable_ofReal.comp hmeanm).const_mul _ |>.sub
      (Complex.measurable_ofReal.comp (hvarm.const_mul _)))
  have hGi : Integrable (Er.indicator (imgF rL rR s ζ W E φ r)) μ := by
    refine Integrable.of_bound ((hGm.mono ((imgRaw s ζ W E).le r) le_rfl).aestronglyMeasurable) 1
      (Eventually.of_forall fun p => ?_)
    by_cases hp : p ∈ Er
    · rw [indicator_of_mem hp]
      exact norm_imgF_le_one rL rR hs hEg φ hp.1
    · rw [indicator_of_notMem hp, norm_zero]
      exact zero_le_one
  refine ae_condExp_eq_of_forall_setIntegral ((imgRaw s ζ W E).le r) hErm hXi hGm.stronglyMeasurable hGi ?_
  intro A hA
  have hUm : ∀ t : ℚ, Measurable[_, hittingSigma] fun p : Ω × HistorySpace 1 1 =>
      histHull t (killedHistory W VL VR ζ p.1) ∪ negInv '' histHull s p.2 := fun t =>
    measurable_union_hitting (((measurable_histHull t).comp (measurable_killedHistory hX)).comp measurable_fst)
      ((measurable_image_negInv.comp (measurable_histHull s)).comp measurable_snd)
  refine setIntegral_eq_of_dyadic hXi (Eventually.of_forall hXb)
    (fun n k => germSigma (fun p : Ω × HistorySpace 1 1 =>
      histHull (dyqQ n k) (killedHistory W VL VR ζ p.1) ∪ negInv '' histHull s p.2)
        (fun p => centredField h u₀ p.1) ⊔ twoSlitMarks W VL VR ζ (dyqQ n k) s)
    (fun n k => sup_le (germSigma_le (hUm _) ((measurable_centredField hC.2.1 u₀).comp measurable_fst))
      (twoSlitMarks_le _ _ hX))
    (Av := imgAv s ζ W E φ) (F := fun q p => imgF rL rR s ζ W E φ (capClock (gCurve s ζ W E p) q).toNNReal p)
    (fun q p hp => norm_imgF_le_one rL rR hs hEg φ hp.2.2.1) ?_ (measurable_imgTheta hs hW hE hEg r)
    (((imgRaw s ζ W E).le r _ hA).inter ((imgRaw s ζ W E).le r _ hErm)) ?_ ?_
  · -- the clause at the rational forward times
    intro n j
    have h1 := ae_condExp_twoSlit_glue_eq_imgF hL hR hC hC₂ hlaw k hk hu₀ (dyqQ_pos n j) hs φ
    filter_upwards [h1] with p hp hAv
    obtain ⟨hpE, hpP, hpA⟩ := hAv
    have hc := dyqQ_coe n j
    rw [← hc] at hpP hpA
    show _ = imgF rL rR s ζ W E φ (capClock (gCurve s ζ W E p) ((dyq n j : ℝ≥0) : ℝ)).toNNReal p
    rw [← hc]
    exact hp hpE hpP hpA
  · -- the pieces are in the marks
    intro n j
    have ht0 := dyqQ_pos n j
    have hk0 : (0 : ℚ) ≤ (j : ℚ) / 2 ^ n := by positivity
    have hkt : (j : ℚ) / 2 ^ n ≤ dyqQ n j := by
      rw [dyqQ]
      exact div_le_div_of_nonneg_right (by linarith) (by positivity)
    obtain ⟨B1, hB1m, hB1e⟩ := hM1 r (dyqQ n j) (dyqQ n j) ht0.le le_rfl ht0 (A ∩ Er) (hA.inter hErm)
    obtain ⟨B2, hB2m, hB2e⟩ := hM1 r ((j : ℚ) / 2 ^ n) (dyqQ n j) hk0 hkt ht0 univ MeasurableSet.univ
    obtain ⟨B3, hB3m, hB3e⟩ := hM3 (dyqQ n j) ht0 φ
    refine ⟨B1 ∩ B2ᶜ ∩ B3, le_sup_right (a := germSigma (fun p : Ω × HistorySpace 1 1 =>
      histHull (dyqQ n j) (killedHistory W VL VR ζ p.1) ∪ negInv '' histHull s p.2)
        (fun p => centredField h u₀ p.1)) _ ((hB1m.inter hB2m.compl).inter hB3m), ?_⟩
    refine ((hB1e.inter hB2e.compl).inter hB3e).trans ?_
    refine eventuallyEqSet_iff.2 ?_
    filter_upwards [hEae] with p hpE
    simp only [mem_inter_iff, mem_compl_iff, mem_univ, true_and]
    constructor
    · rintro ⟨⟨⟨⟨hAp, hEr⟩, h1⟩, h2⟩, h3⟩
      have hh := (dyIdx_imgTheta_and_mem_imgAv_iff hs hEg hpE hEr.1 n j φ).2 ⟨h1, h2, h3⟩
      exact ⟨⟨⟨hAp, hEr⟩, hh.1⟩, hh.2⟩
    · rintro ⟨⟨⟨hAp, hEr⟩, hd⟩, hav⟩
      obtain ⟨h1, h2, h3⟩ := (dyIdx_imgTheta_and_mem_imgAv_iff hs hEg hpE hEr.1 n j φ).1 ⟨hd, hav⟩
      exact ⟨⟨⟨⟨hAp, hEr⟩, h1⟩, h2⟩, h3⟩
  · -- the right limit
    filter_upwards [hEae] with p hpE hpD
    exact tendsto_imgF_dyF rL rR hs hEg hpE hpD.2

end Main

/-- **`ImgChartConstStatement` from the stopped-history measurability of the image word** (steps R1–R6). -/
theorem imgChartConstStatement_of_marks (hM : ImgMarksStatement.{u}) : ImgChartConstStatement.{u} := by
  intro rL rR hL hR Ω mΩ P _ 𝓕 W VL VR B ζ h hC Ω₂ mΩ₂ P₂ _ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ h₂ hC₂ hlaw k _ hk s hs
  obtain ⟨hM1, hM3⟩ := hM rL rR hL hR P 𝓕 W VL VR B ζ h hC P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ h₂ hC₂ hlaw k hk s hs
  have hEg : ∀ p ∈ glueGood (glueMeasure P k h hC.2.1) s ζ W, IsGlueGood s ζ W p := fun p hp =>
    isGlueGood_of_mem_glueGood p hp
  have hkw := isKilledWord_img (ζ := ζ) (W := W) hs hEg
  intro r u hu φ
  filter_upwards [ae_condExp_imgRaw_eq_imgF hL hR hC hC₂ hlaw k hk hs hM1 hM3 r φ] with p hp hr hsupp
  have hav : Sec7.Lemma71D.IsChartAvoid (fun t => imgW s ζ W (glueGood (glueMeasure P k h hC.2.1) s ζ W) t p)
      (imgT s ζ W (glueGood (glueMeasure P k h hC.2.1) s ζ W) p : ℝ≥0∞) (imgChart s p.2) φ r := ⟨hr, hsupp⟩
  rw [hp hav, imgF]
  have hint := Sec7.Lemma71D.integral_couplingMean_eq_chartMean (κ := 4) (ρL := imgρ rL) (ρR := imgρ rR)
    (a := 0) (k := 0) (isConformal_imgChart hs p.2) (hkw.contW p) hav (fun i => hkw.ordL p r i hr)
    (fun j => hkw.ordR p r j hr) (hu p)
  congr 3
  exact congrArg Complex.ofReal hint.symm

/-- **The contact step from the stopped-history measurability of the image word.** -/
theorem reverseTipContactStatement_of_marks (hM : ImgMarksStatement.{u}) : ReverseTipContactStatement.{u} :=
  reverseTipContactStatement_of_chartConst (imgChartConstStatement_of_marks hM)

end InteractingSLE.WangWu
