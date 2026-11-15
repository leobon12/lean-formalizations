/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Exist.Param12Kernel
import InteractingSLE.Spec.Coupling.ResampleProjBridge
import InteractingSLE.Spec.Sec2.Assembly2Entr
import InteractingSLE.Spec.Exist.StagedAssembly

/-!
# The named input of PROVE-PARAM12 is exactly as strong as the parametric Theorem 1.2

Packet PROVE-PARAM12. `Param12Kernel.lean` derives `Staged.Theorem12ParamStatement` from the per-word Theorems 1.2–1.3
and the named input `CouplingLawKernelStatement` (Theorem 1.1's coupling law, a Borel kernel in the word). This file
proves the converse, from Theorem 1.3 and Theorem 1.1's construction (`Coupling.exists_isOptionalHullCoupling_of_thm22`
with Theorem 2.2's `exists_isIntegratedSLEEvolution_assembled`). So the named input is equivalent to the target
(`theorem12ParamStatement_iff_couplingLawKernel`), and no proof obligation is moved into it.

* `wordExt κ w`: the explicit bounded harmonic extension `Impl.forceExt` of the word's boundary data; **jointly
  measurable** in the word and the point (`measurable_wordExt`: `jumpExt b z = 1 − arg(z − b)/π`);
* `map_field_eq_zbLaw_map`: in every coupling the field has the law of `g + 𝔥₀` with `g` the zero-boundary GFF law
  `Coupling.zbLaw` and `𝔥₀ = meanH u₀` (uniqueness of the zero-boundary GFF law, `IsZBGFFProcess.map_eq`, on the cylinder
  σ-algebra);
* `mapKernel`: the push-forward of a fixed law along a jointly measurable family of maps is a kernel;
* **`couplingLawKernelStatement_of_param`**: the kernel `w ↦ law of (g + 𝔥_w, detCode Φ (w, g + 𝔥_w))`;
* `stagedHistoryConstructionStatement_of_couplingLawKernel`: PROVE-STAGED's assembly with its input (b) replaced by the
  named input of this packet.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Exist

namespace Param12

open Sec2.Assembly LQGMetric Staged Coupling

/-! ### The harmonic extension of a word, measurable in the word -/

/-- The explicit bounded harmonic extension of the force data of the word `w = ((xL, xR), (ρL, ρR))`. -/
def wordExt (κ : ℝ) {nL nR : ℕ} (w : WordData nL nR) : ℂ → ℝ :=
  Impl.forceExt κ (Ito.weightWord w.2.1 w.2.2) w.1.1 w.1.2

theorem isBoundedHarmonicExtension_wordExt (κ : ℝ) {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ)
    (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) :
    IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR)
      (wordExt κ (((xL, xR), (ρL, ρR)))) :=
  Impl.isBoundedHarmonicExtension_forceExt κ (Ito.weightWord ρL ρR) xL xR

theorem continuousOn_wordExt (κ : ℝ) {nL nR : ℕ} (w : WordData nL nR) :
    ContinuousOn (wordExt κ w) QuantumZipper.H := fun z hz =>
  ((isBoundedHarmonicExtension_wordExt κ w.1.1 w.1.2 w.2.1 w.2.2).1 z hz).1.continuousAt.continuousWithinAt

theorem measurable_jumpExt : Measurable fun q : ℝ × ℂ => Impl.jumpExt q.1 q.2 := by
  have : (fun q : ℝ × ℂ => Impl.jumpExt q.1 q.2) = fun q => 1 - Complex.arg (q.2 - q.1) / Real.pi :=
    funext fun q => Impl.jumpExt_eq q.1 q.2
  rw [this]
  exact measurable_const.sub ((Complex.measurable_arg.comp
    (measurable_snd.sub (Complex.measurable_ofReal.comp measurable_fst))).div_const _)

/-- **The harmonic extension is jointly measurable in the word and the point.** -/
theorem measurable_wordExt (κ : ℝ) {nL nR : ℕ} :
    Measurable fun p : WordData nL nR × ℂ => wordExt κ p.1 p.2 := by
  have hJ' : ∀ {f : WordData nL nR × ℂ → ℝ}, Measurable f →
      Measurable fun p : WordData nL nR × ℂ => Impl.jumpExt (f p) p.2 := fun {f} hf => by
    have e : (fun p : WordData nL nR × ℂ => Impl.jumpExt (f p) p.2) =
        fun p => 1 - Complex.arg (p.2 - f p) / Real.pi := funext fun p => Impl.jumpExt_eq _ _
    rw [e]
    exact measurable_const.sub ((Complex.measurable_arg.comp
      (measurable_snd.sub (Complex.measurable_ofReal.comp hf))).div_const _)
  have hxL : ∀ i : Fin nL, Measurable fun p : WordData nL nR × ℂ => p.1.1.1 i := fun i =>
    (measurable_pi_apply i).comp (measurable_fst.comp (measurable_fst.comp measurable_fst))
  have hxR : ∀ i : Fin nR, Measurable fun p : WordData nL nR × ℂ => p.1.1.2 i := fun i =>
    (measurable_pi_apply i).comp (measurable_snd.comp (measurable_fst.comp measurable_fst))
  have hρL : ∀ i : Fin nL, Measurable fun p : WordData nL nR × ℂ => p.1.2.1 i := fun i =>
    (measurable_pi_apply i).comp (measurable_fst.comp (measurable_snd.comp measurable_fst))
  have hρR : ∀ i : Fin nR, Measurable fun p : WordData nL nR × ℂ => p.1.2.2 i := fun i =>
    (measurable_pi_apply i).comp (measurable_snd.comp (measurable_snd.comp measurable_fst))
  have he : (fun p : WordData nL nR × ℂ => wordExt κ p.1 p.2) = fun p =>
      Real.pi / Real.sqrt κ * (-1 + 2 * Impl.jumpExt 0 p.2
        - ∑ i, p.1.2.1 i * (1 - Impl.jumpExt (min 0 (p.1.1.1 i)) p.2)
        + ∑ i, p.1.2.2 i * Impl.jumpExt (max 0 (p.1.1.2 i)) p.2) := by
    funext p
    rfl
  rw [he]
  refine Measurable.const_mul ?_ _
  refine ((measurable_const.add ((hJ' (f := fun _ => 0) measurable_const).const_mul _)).sub ?_).add ?_
  · exact Finset.measurable_sum _ fun i _ =>
      (hρL i).mul (measurable_const.sub (hJ' (measurable_const.min (hxL i))))
  · exact Finset.measurable_sum _ fun i _ => (hρR i).mul (hJ' (measurable_const.max (hxR i)))

theorem meanH_apply_eq {u : ℂ → ℝ} (hu : ContinuousOn u QuantumZipper.H) (φ : TestOn upperHalfPlaneOpens) :
    meanH u φ = ∫ z, u z * φ z := by
  rw [meanH, Distribution.ofFun_apply (hu.locallyIntegrableOn upperHalfPlaneOpens.isOpen.measurableSet)]
  simp only [smul_eq_mul]
  simp_rw [mul_comm (φ _)]

/-- The shift `(w, g) ↦ g + 𝔥_w` is jointly measurable. -/
theorem measurable_shift (κ : ℝ) {nL nR : ℕ} :
    Measurable fun p : WordData nL nR × DistOn upperHalfPlaneOpens => p.2 + meanH (wordExt κ p.1) := by
  refine measurable_distOn_iff.2 fun φ => ?_
  have hI : Measurable fun w : WordData nL nR => ∫ z, wordExt κ w z * φ z :=
    ((measurable_wordExt κ).mul (φ.continuous.measurable.comp measurable_snd)).stronglyMeasurable.integral_prod_right'.measurable
  have he : (fun p : WordData nL nR × DistOn upperHalfPlaneOpens => (p.2 + meanH (wordExt κ p.1)) φ) =
      fun p => p.2 φ + ∫ z, wordExt κ p.1 z * φ z := by
    funext p
    rw [← meanH_apply_eq (continuousOn_wordExt κ p.1) φ]
    rfl
  rw [he]
  exact ((measurable_distOn_apply φ).comp measurable_snd).add (hI.comp measurable_fst)

/-! ### The field law of a coupling -/

/-- **The field law of every coupling** is the zero-boundary GFF law shifted by the time-zero harmonic mean. -/
theorem map_field_eq_zbLaw_map {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀) :
    P.map h = (zbLaw upperHalfPlaneOpens).map fun g => g + meanH u₀ := by
  have g₁ := hC.2.2.1 u₀ hu₀
  have g₂ : IsZBGFFProcess upperHalfPlaneOpens (fun φ (g : DistOn upperHalfPlaneOpens) => g φ)
      (zbLaw upperHalfPlaneOpens) := (isZeroBoundaryGFF_zbLaw (fun _ hz => hz)).process
  have e := g₁.map_eq g₂
  have hcont : ContinuousOn u₀ QuantumZipper.H := fun z hz => (hu₀.1 z hz).1.continuousAt.continuousWithinAt
  obtain ⟨c, hc⟩ : ∃ c : TestOn upperHalfPlaneOpens → ℝ, c = fun φ => ∫ z, u₀ z * φ z := ⟨_, rfl⟩
  have hadd : Measurable fun f : TestOn upperHalfPlaneOpens → ℝ => f + c := measurable_id.add_const c
  have hT : Measurable fun g : DistOn upperHalfPlaneOpens => g + meanH u₀ :=
    measurable_distOn_iff.2 fun φ => (measurable_distOn_apply φ).add_const _
  have hd₁ : distEval upperHalfPlaneOpens ∘ h =
      (fun f => f + c) ∘ zbPath (fun φ ω => h ω φ - ∫ z, u₀ z * φ z) := by
    funext ω φ; simp [zbPath, distEval, hc]
  have hd₂ : distEval upperHalfPlaneOpens ∘ (fun g => g + meanH u₀) =
      (fun f => f + c) ∘ zbPath (fun φ (g : DistOn upperHalfPlaneOpens) => g φ) := by
    funext g φ
    have := meanH_apply_eq hcont φ
    simp only [Function.comp_apply, distEval, zbPath, Pi.add_apply, hc]
    rw [← this]
    rfl
  have hz₁ : Measurable (zbPath (fun φ ω => h ω φ - ∫ z, u₀ z * φ z)) := measurable_pi_iff.2 g₁.measurable
  have hz₂ : Measurable (zbPath fun φ (g : DistOn upperHalfPlaneOpens) => g φ) :=
    measurable_pi_iff.2 g₂.measurable
  have hD : P.map (distEval upperHalfPlaneOpens ∘ h) =
      (zbLaw upperHalfPlaneOpens).map (distEval upperHalfPlaneOpens ∘ fun g => g + meanH u₀) := by
    rw [hd₁, hd₂, ← Measure.map_map hadd hz₁, ← Measure.map_map hadd hz₂, e]
  ext s hs
  obtain ⟨t, ht, rfl⟩ := hs
  have hS : MeasurableSet (distEval upperHalfPlaneOpens ⁻¹' t) := measurable_distEval _ ht
  have := congrArg (fun μ : Measure (TestOn upperHalfPlaneOpens → ℝ) => μ t) hD
  rw [Measure.map_apply ((measurable_distEval _).comp hC.2.1) ht,
    Measure.map_apply ((measurable_distEval _).comp hT) ht] at this
  change (P.map h) (distEval upperHalfPlaneOpens ⁻¹' t) =
    ((zbLaw upperHalfPlaneOpens).map fun g => g + meanH u₀) (distEval upperHalfPlaneOpens ⁻¹' t)
  rw [Measure.map_apply hC.2.1 hS, Measure.map_apply hT hS]
  exact this

/-! ### Push-forward kernels -/

/-- The push-forward of a fixed s-finite measure along a jointly measurable family of maps, as a kernel. -/
def mapKernel {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] (ν : Measure β)
    [SFinite ν] (T : α × β → γ) (hT : Measurable T) : Kernel α γ where
  toFun a := ν.map fun b => T (a, b)
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
    have : (fun a => (ν.map fun b => T (a, b)) s) = fun a => ν (Prod.mk a ⁻¹' (T ⁻¹' s)) := by
      funext a
      have hTa : Measurable fun b => T (a, b) := hT.comp measurable_prodMk_left
      rw [Measure.map_apply hTa hs]
      rfl
    rw [this]
    exact measurable_measure_prodMk_left (hT hs)

theorem mapKernel_apply {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (ν : Measure β) [SFinite ν] (T : α × β → γ) (hT : Measurable T) (a : α) :
    mapKernel ν T hT a = ν.map fun b => T (a, b) := rfl

instance isMarkovKernel_mapKernel {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (ν : Measure β) [IsProbabilityMeasure ν] (T : α × β → γ) (hT : Measurable T) :
    IsMarkovKernel (mapKernel ν T hT) :=
  ⟨fun a => by
    rw [mapKernel_apply]
    infer_instance⟩

/-! ### The converse -/

/-- **The parametric Theorem 1.2 gives the named input** (with Theorem 1.3 and Theorem 1.1's construction): the
kernel `w ↦ law of (g + 𝔥_w, detCode Φ (w, g + 𝔥_w))`, `g` the zero-boundary GFF law. -/
theorem couplingLawKernelStatement_of_param (h13 : Theorem13Statement.{u})
    (hP : Theorem12ParamStatement.{u}) : CouplingLawKernelStatement.{u} := by
  intro κ hκ nL nR
  obtain ⟨Φ, hΦm, hΦ⟩ := hP κ hκ nL nR
  have hT := measurable_shift κ (nL := nL) (nR := nR)
  have hD := measurable_detCode hΦm
  have hM : Measurable fun p : WordData nL nR × DistOn upperHalfPlaneOpens =>
      (p.2 + meanH (wordExt κ p.1), detCode Φ (p.1, p.2 + meanH (wordExt κ p.1))) :=
    hT.prodMk (hD.comp (measurable_fst.prodMk hT))
  refine ⟨mapKernel (zbLaw upperHalfPlaneOpens) _ hM, inferInstance, fun xL xR ρL ρR hF => ?_⟩
  obtain ⟨Ω, mΩ, P, hPp, 𝓕, W, VL, VR, B, ζ, h, hC⟩ := Coupling.exists_isOptionalHullCoupling_of_thm22.{u} hκ hF
    (exists_isIntegratedSLEEvolution_assembled (ρL := ρL) (ρR := ρR) hκ hF)
  refine ⟨Ω, mΩ, P, hPp, 𝓕, W, VL, VR, B, ζ, h, hC, ?_⟩
  have hf := map_field_eq_zbLaw_map hC (isBoundedHarmonicExtension_wordExt κ xL xR ρL ρR)
  have hG : Measurable fun f : DistOn upperHalfPlaneOpens => (f, detCode Φ (((xL, xR), (ρL, ρR)), f)) :=
    measurable_id.prodMk (hD.comp (measurable_const.prodMk measurable_id))
  have hae : fieldCode h W ζ =ᵐ[P] (fun f => (f, detCode Φ (((xL, xR), (ρL, ρR)), f))) ∘ h := by
    filter_upwards [ae_detCode_eq hκ hF h13 hC (hΦ xL xR ρL ρR hF hC)] with ω hω
    obtain ⟨x₀, hx₀, hζx, hcw, hdet⟩ := hω
    simp only [fieldCode, Function.comp_apply, hdet, dOf_eq_killedCode hx₀ hζx fun t ht => (hcw t ht).1]
  have hsh : Measurable fun g : DistOn upperHalfPlaneOpens => g + meanH (wordExt κ (((xL, xR), (ρL, ρR)))) :=
    hT.comp measurable_prodMk_left
  rw [Measure.map_congr hae, ← Measure.map_map hG hC.2.1, hf, Measure.map_map hG hsh, mapKernel_apply]
  rfl

/-- **The named input is equivalent to the parametric Theorem 1.2**, given the per-word Theorems 1.2 and 1.3 (and
Theorem 1.1's construction, used in the converse). -/
theorem theorem12ParamStatement_iff_couplingLawKernel (h12 : Theorem12Statement.{u})
    (h13 : Theorem13Statement.{u}) : Theorem12ParamStatement.{u} ↔ CouplingLawKernelStatement.{u} :=
  ⟨couplingLawKernelStatement_of_param h13, theorem12ParamStatement_of_couplingLawKernel h12 h13⟩

/-- **PROVE-STAGED's construction with input (b) replaced by the named input of this packet**: the staged-history
construction statement of Theorem 1.4's companion from the per-word Theorems 1.2–1.3, `CouplingLawKernelStatement` and
PROVE-STAGED's input (a). -/
theorem stagedHistoryConstructionStatement_of_couplingLawKernel (h12 : Theorem12Statement.{u})
    (h13 : Theorem13Statement.{u}) (hK : CouplingLawKernelStatement.{u}) (hGW : StagedCondLawStatement.{u}) :
    Theorem14.StagedHistoryConstructionStatement.{u} :=
  stagedHistoryConstructionStatement_of_inputs (theorem12ParamStatement_of_couplingLawKernel h12 h13 hK) h13 hGW

end Param12

end Exist

end InteractingSLE
