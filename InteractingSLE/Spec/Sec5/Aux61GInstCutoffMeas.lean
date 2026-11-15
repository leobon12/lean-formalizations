/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GInstCutoff
import InteractingSLE.GFF.PushforwardMeas

/-! # Measurable families of reflected cutoffs and their source densities -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Topology Metric
open scoped ComplexConjugate Laplacian InteractingSLE.RandomTest
open QuantumZipper (H)

namespace InteractingSLE.Sec5.Aux61GInst
open Aux61Cov
open Restart.FlowStopIdentCMI (CMCut)
open Aux61Win (IsCutoffOn)

/-- The odd reflection preserves joint measurability. -/
theorem measurable_oddRefl {β : Type*} [MeasurableSpace β] {q : β → ℂ → ℝ}
    (hq : Measurable (fun p : β × ℂ => q p.1 p.2)) :
    Measurable (fun p : β × ℂ => oddRefl (q p.1) p.2) := by
  classical
  exact Measurable.ite (measurableSet_lt measurable_const (Complex.measurable_im.comp measurable_snd)) hq
    (Measurable.ite (measurableSet_lt (Complex.measurable_im.comp measurable_snd) measurable_const)
      (hq.comp (measurable_fst.prodMk (Complex.continuous_conj.measurable.comp measurable_snd))).neg
      measurable_const)

/-- Point evaluations of the density are measurable by the existing derivative API. -/
theorem measurable_greenDensity_apply {β : Type*} [MeasurableSpace β] {F : β → CMCut}
    (hm : ∀ z, Measurable (fun b => (F b).f z)) (z : ℂ) :
    Measurable (fun b => QuantumZipper.K3.greenDensity (F b).f z) := by
  have hi := RandomTest.measurable_iteratedFDeriv_apply (fun b => (F b).smooth) hm 2 z
  have hv : ∀ v : Fin 2 → ℂ,
      Measurable (fun b => iteratedFDeriv ℝ 2 (F b).f z v) := fun v =>
    (continuous_eval_const v).measurable.comp hi
  have he : (fun b => QuantumZipper.K3.greenDensity (F b).f z) =
      fun b => -(2 * Real.pi)⁻¹ * (iteratedFDeriv ℝ 2 (F b).f z ![1, 1] +
        iteratedFDeriv ℝ 2 (F b).f z ![Complex.I, Complex.I]) := by
    funext b
    rw [QuantumZipper.K3.greenDensity,
      InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]
  rw [he]
  exact measurable_const.mul ((hv _).add (hv _))

/-- A smooth family measurable at each point has a jointly measurable Laplacian. -/
theorem measurable_greenDensity_family {β : Type*} [MeasurableSpace β] {F : β → CMCut}
    (hF : Measurable (fun p : β × ℂ => (F p.1).f p.2)) :
    Measurable (fun p : β × ℂ => QuantumZipper.K3.greenDensity (F p.1).f p.2) := by
  have hm : ∀ z, Measurable (fun b => (F b).f z) := fun z =>
    hF.comp (measurable_id.prodMk measurable_const)
  have h := measurable_uncurry_of_continuous_of_measurable
    (u := fun (z : ℂ) (b : β) => QuantumZipper.K3.greenDensity (F b).f z)
    (fun b => (F b).continuous_greenDensity) (measurable_greenDensity_apply (F := F) hm)
  have hc : Measurable ((Function.uncurry
      (fun (z : ℂ) (b : β) => QuantumZipper.K3.greenDensity (F b).f z)) ∘
        (Prod.swap : β × ℂ → ℂ × β)) := h.comp measurable_swap
  simpa only [Function.comp_def, Function.uncurry, Prod.swap] using hc

/-- One deterministic neighbourhood works for every history; the selected
cutoff and its source density are jointly measurable. -/
theorem exists_measurable_cmCuts {β : Type*} [MeasurableSpace β]
    {O : Set ℝ} (hO : IsOpen O) {K : Set ℂ} (hK : IsCompact K)
    (hKO : ∀ z ∈ K, z.im = 0 → z.re ∈ O) {q : β → ℂ → ℝ}
    (hqm : Measurable (fun p : β × ℂ => q p.1 p.2))
    (hqh : ∀ b, InnerProductSpace.HarmonicOnNhd (q b) H)
    (hq0 : ∀ b x, x ∈ O → Tendsto (q b) (𝓝[H] (x : ℂ)) (𝓝 0)) :
    ∃ (N : Set ℂ) (F : β → CMCut), K ⊆ N ∧
      (∀ b, IsCutoffOn (F b) (q b) N O) ∧
      Measurable (fun p : β × ℂ => (F p.1).f p.2) ∧
      Measurable (fun p : β × ℂ => QuantumZipper.K3.greenDensity (F p.1).f p.2) := by
  obtain ⟨C⟩ := exists_reflectionCutoff hO hK hKO
  let hR := fun b => schwarzReflStatement (q b) O hO (hqh b) (hq0 b)
  let F := fun b => C.cut (q b) (hR b)
  have hfm : Measurable (fun p : β × ℂ => (F p.1).f p.2) :=
    (C.smooth.continuous.measurable.comp measurable_snd).mul (measurable_oddRefl hqm)
  exact ⟨C.neighbourhood, F, C.buffer_sub, fun b => C.isCutoffOn (hR b),
    hfm, measurable_greenDensity_family (F := F) hfm⟩

end InteractingSLE.Sec5.Aux61GInst
