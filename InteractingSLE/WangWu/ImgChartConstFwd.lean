/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.ImgChartConstIdent
import InteractingSLE.WangWu.ImgChartConstDyadic

/-!
# The fixed-image-time chart clause, step R1 on the glued space: the two-slit law in the image word's coordinates

Packet PROVE-WW-B19 (Astra's follow-up note, Part E.3: "Fix an original deterministic rational forward time `t` ...
the conditional mean is exactly the bounded canonical Poisson mean of the finite boundary word in the two-slit
complement ... The residual covariance is the Green kernel of that complement").

At a rational forward time `t > 0`, on the good glued samples before contact, PROVE-WW-B18's explicit conditional law
of the history-marked two-slit union (`ae_condExp_cexp_twoSlit_glue`) is rewritten with the explicit killed image word
of PROVE-WW-B17 at the image time `σ(t)` (the capacity of `Ψ(α((0, t]))`), in the chart `Ψ = imgChart`:

* `revChartInv_image_H_diff`: `Ψ⁻¹(ℍ \ Ψ(A)) = ℍ \ (A ∪ G)` for `A ⊆ ℍ \ G`;
* `ChartConst.imgF`: the explicit Gaussian characteristic function of the image word at an image time (chart mean
  `Lemma71D.chartMean` and chart variance `Lemma71D.chartVar` of `imgChart`);
* **`ae_condExp_twoSlit_glue_eq_imgF`**: almost surely on the good set, if `t` is before contact and `supp φ` avoids
  the image hull at `σ(t)` in the chart, then `E[e^{i(h,φ)} | 𝒜_{A_t ∪ G} ∨ marks] = imgF(σ(t))`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Complex
open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.WangWu

open Sec7.Lemma71C (capClock)
open ImgWord LawUnique WholeField LocalSets Coupling

/-! ### The two-slit complement through the chart -/

/-- `Ψ⁻¹(ℍ \ Ψ(A)) = ℍ \ (A ∪ G)` for `A ⊆ ℍ \ G`, `G = R(K_s)`. -/
theorem revChartInv_image_H_diff {Wβ : ℝ → ℝ} (hW : Continuous Wβ) (hW0 : Wβ 0 = 0) {s : ℝ} (hs : 0 ≤ s)
    {A : Set ℂ} (hA : A ⊆ H \ negInv '' fwdHull Wβ s) :
    revChartInv Wβ s '' (H \ revChart Wβ s '' A) = H \ (A ∪ negInv '' fwdHull Wβ s) := by
  ext z
  constructor
  · rintro ⟨w, ⟨hwH, hwA⟩, rfl⟩
    have hm := revChartInv_mem hW hW0 hs hwH
    refine ⟨hm.1, fun hz => ?_⟩
    rcases hz with hz | hz
    · exact hwA ⟨_, hz, revChart_revChartInv hW hW0 hs hwH⟩
    · exact hm.2 hz
  · rintro ⟨hzH, hz⟩
    have hzG : z ∈ H \ negInv '' fwdHull Wβ s := ⟨hzH, fun h => hz (Or.inr h)⟩
    refine ⟨revChart Wβ s z, ⟨revChart_mem_H hW hs hzG, ?_⟩, revChartInv_revChart hW hW0 hs hzG⟩
    rintro ⟨a, ha, e⟩
    exact hz (Or.inl (injOn_revChart hW hW0 hs (hA ha) hzG e ▸ ha))

namespace ChartConst

/-- **The explicit Gaussian characteristic function of the image word at the image time `q`**: the chart mean and
the chart variance of `imgChart` along the killed image word (`κ = 4`, no lift term). -/
def imgF (rL rR : ℝ) {Ω : Type*} (s : ℚ) (ζ : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ) (E : Set (Ω × HistorySpace 1 1))
    (φ : TestOn upperHalfPlaneOpens) (q : ℝ≥0) (p : Ω × HistorySpace 1 1) : ℂ :=
  Complex.exp (Complex.I * (Sec7.Lemma71D.chartMean 4 (imgρ rL) (imgρ rR) (fun r => imgW s ζ W E r p)
      (fun i r => imgVL s ζ W E i r p) (fun j r => imgVR s ζ W E j r p) (imgChart s p.2) 0 0 φ q : ℂ) -
    (((1 / 2 : ℝ) * Sec7.Lemma71D.chartVar (fun r => imgW s ζ W E r p) (imgChart s p.2) φ q : ℝ) : ℂ))

end ChartConst

open ChartConst

section Glue

variable {rL rR : ℝ} {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL VR : Fin 1 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
  {h : Ω → DistOn upperHalfPlaneOpens}
  {Ω₂ : Type u} {mΩ₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
  {𝓕₂ : Filtration ℝ≥0 mΩ₂} {W₂ : ℝ≥0 → Ω₂ → ℝ} {VL₂ VR₂ : Fin 1 → ℝ≥0 → Ω₂ → ℝ} {B₂ : ℝ≥0 → Ω₂ → ℝ}
  {ζ₂ : Ω₂ → ℝ≥0∞} {h₂ : Ω₂ → DistOn upperHalfPlaneOpens}

omit [IsProbabilityMeasure P] in
/-- The forward stopped hull is the prefix of the seed line, almost surely. -/
theorem ae_histHull_eq_image_seedLine (hL : 0 ≤ rL) (hR : 0 ≤ rR)
    (hC : IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ h)
    {t : ℚ} (ht : 0 < t) :
    ∀ᵐ ω ∂P, histHull t (killedHistory W VL VR ζ ω) = seedLine ζ W ω '' Ioc 0 t := by
  have ht' : (0 : ℝ) ≤ t := by exact_mod_cast ht.le
  filter_upwards [ae_histHull_eq_fwdHull hL hR hC.1 ht,
    IsMarkedChain.ae_seedLine isOrderedForceWord_twoSeed (hasNonnegCumWeights_twoSeed hL hR) hC.1]
    with ω h1 h2
  rw [h1, h2.2.2.2.2 (Real.toNNReal t), Real.coe_toNNReal _ ht']

/-- **R1 on the glued space.** At a rational forward time `t > 0`, almost surely on the good set, before contact and
when `supp φ` avoids the image hull at `σ(t)` in the chart `Ψ`, the conditional characteristic function of `(h, φ)`
given the germ of the two stopped slits and both stopped histories is `imgF(σ(t))`. -/
theorem ae_condExp_twoSlit_glue_eq_imgF (hL : 0 ≤ rL) (hR : 0 ≤ rR)
    (hC : IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ h)
    (hC₂ : IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rR) (fun _ => rL) P₂ 𝓕₂ W₂ VL₂ VR₂ B₂
      ζ₂ h₂)
    (hlaw : P.map h = P₂.map (fun ω => reflectField (h₂ ω)))
    (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 1 1)) [IsMarkovKernel k]
    (hk : P₂.map (fun ω => (reflectField (h₂ ω), killedHistory W₂ VL₂ VR₂ ζ₂ ω)) =
      P₂.map (fun ω => reflectField (h₂ ω)) ⊗ₘ k)
    {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData 4 (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR)
      LP.twoSeedXL LP.twoSeedXR) (forceJumpSet LP.twoSeedXL LP.twoSeedXR) u₀)
    {t s : ℚ} (ht : 0 < t) (hs : 0 < s) (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ p ∂(glueMeasure P k h hC.2.1), p ∈ glueGood (glueMeasure P k h hC.2.1) s ζ W →
      (t : ℝ) ∈ gPre s ζ W (glueGood (glueMeasure P k h hC.2.1) s ζ W) p →
      Sec7.Lemma71D.IsChartAvoid (fun r => imgW s ζ W (glueGood (glueMeasure P k h hC.2.1) s ζ W) r p)
        (imgT s ζ W (glueGood (glueMeasure P k h hC.2.1) s ζ W) p : ℝ≥0∞) (imgChart s p.2) φ
        (capClock (gCurve s ζ W (glueGood (glueMeasure P k h hC.2.1) s ζ W) p) t).toNNReal →
      (glueMeasure P k h hC.2.1)[fun p' => Complex.exp (Complex.I * (h p'.1 φ : ℂ)) |
          germSigma (fun p : Ω × HistorySpace 1 1 =>
            histHull t (killedHistory W VL VR ζ p.1) ∪ negInv '' histHull s p.2) (fun p => centredField h u₀ p.1) ⊔
            twoSlitMarks W VL VR ζ t s] p =
        imgF rL rR s ζ W (glueGood (glueMeasure P k h hC.2.1) s ζ W) φ
          (capClock (gCurve s ζ W (glueGood (glueMeasure P k h hC.2.1) s ζ W) p) t).toNNReal p := by
  set μ := glueMeasure P k h hC.2.1 with hμ
  set E := glueGood μ s ζ W with hEdef
  have hEg : ∀ p ∈ E, IsGlueGood s ζ W p := fun p hp => isGlueGood_of_mem_glueGood p hp
  have ht0 : (0 : ℝ) < t := by exact_mod_cast ht
  have hs' : (0 : ℝ) ≤ s := by exact_mod_cast hs.le
  filter_upwards [ae_condExp_cexp_twoSlit_glue hL hR hC hC₂ hlaw k hk hu₀ ht hs φ,
    ae_glue_fst (μ := P) k hC.2.1 (ae_histHull_eq_image_seedLine hL hR hC ht)] with p hB hA hpE htP havoid
  obtain ⟨hα, hβ, -⟩ := hEg p hpE
  obtain ⟨hWβc, hWβ0, -, -, hGeq, -, -⟩ := trace_of_mem_betaSet hs hβ
  set A := histHull t (killedHistory W VL VR ζ p.1) with hAdef
  set Wβ := Ito.rpath (frzDrive s p.2) with hWβdef
  have hP : gPre s ζ W E p = preContact (seedLine ζ W p.1) (negInv '' histHull s p.2) := gPre_of_mem hpE
  have hγ : gCurve s ζ W E p = imgCurve Wβ s (seedLine ζ W p.1) := gCurve_of_mem hpE
  have htP' := hP ▸ htP
  have hAsub : A ⊆ H \ negInv '' fwdHull Wβ s := by
    rw [hA, ← hGeq]
    rintro _ ⟨u, hu, rfl⟩
    exact ⟨hα.mem_H u hu.1, htP'.2 u ⟨hu.1.le, hu.2⟩⟩
  have hdisj : Disjoint A (negInv '' histHull s p.2) := by
    rw [hGeq]
    exact Set.disjoint_left.2 fun z hz hzG => (hAsub hz).2 hzG
  have hγimg : gCurve s ζ W E p '' Ioc 0 t = revChart Wβ s '' A := by
    rw [hγ, hA, image_image]
    refine image_congr fun u hu => ?_
    simp only [imgCurve, not_le.2 hu.1, ↓reduceIte]
  have hkill : IsKilledArc (gCurve s ζ W E p) (gPre s ζ W E p) := isKilledArc_gCurve hs hEg p
  have hcap0 : 0 ≤ capClock (gCurve s ζ W E p) t := hkill.capClock_nonneg htP
  have hhull : fwdHull (Ito.rpath fun r => imgW s ζ W E r p)
      (((capClock (gCurve s ζ W E p) t).toNNReal : ℝ≥0) : ℝ) = revChart Wβ s '' A := by
    rw [Real.coe_toNNReal _ hcap0, ← hγimg]
    exact hkill.fwdHull_eq_of_eqOn_chainDrv (fun S hS r hr => (hkill.kW_eq_chainDrv hS).2 r hr) htP
  have hset : (imgChart s p.2).2.1 '' (H \ fwdHull (Ito.rpath fun r => imgW s ζ W E r p)
      (((capClock (gCurve s ζ W E p) t).toNNReal : ℝ≥0) : ℝ)) = H \ (A ∪ negInv '' histHull s p.2) := by
    simp only [imgChart]
    rw [revDrv0_of_mem hs hβ, hhull, revChartInv_image_H_diff hWβc hWβ0 hs' hAsub, hGeq]
  have hsupp : tsupport φ ⊆ H \ (A ∪ negInv '' histHull s p.2) := hset ▸ havoid.2
  obtain ⟨W', hW'c, hW'0, T, hT, η', hη', hη'p, hK', hval⟩ := hB hdisj hsupp
  have hK : fwdHull W' T = gCurve s ζ W E p '' Ioc 0 t := hK'.trans hγimg.symm
  obtain ⟨hTc, hmean⟩ := meanCan_img_eq_chartMean hs hEg hpE htP ht0 hW'c hW'0 hη' hη'p hT hK rL rR
  rw [hval, imgF, ← hTc]
  have hm : Sec7.Lemma71D.chartMean 4 (imgρ rL) (imgρ rR) (fun r => imgW s ζ W E r p)
      (fun i r => imgVL s ζ W E i r p) (fun j r => imgVR s ζ W E j r p) (imgChart s p.2) 0 0 φ T.toNNReal =
      ∫ z, chartMean rL rR W' T (frzVL s p.2) (frzVR s p.2) (fwdMap W' T (revChart Wβ s z)) * φ z := by
    rw [Sec7.Lemma71D.chartMean]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [imgChart, sub_zero, zero_mul]
    rw [revDrv0_of_mem hs hβ, hmean]
  have hv : Sec7.Lemma71D.chartVar (fun r => imgW s ζ W E r p) (imgChart s p.2) φ T.toNNReal =
      QuantumZipper.zeroGFFTestCov (H \ (A ∪ negInv '' histHull s p.2)) φ φ := by
    rw [Sec7.Lemma71D.chartVar, hTc, hset]
  rw [hm, hv, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

end Glue

end InteractingSLE.WangWu
