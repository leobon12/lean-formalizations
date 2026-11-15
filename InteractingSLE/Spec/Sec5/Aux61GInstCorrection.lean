/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GInstData
import InteractingSLE.Spec.Sec5.Aux61GInstCutoffMeas
import InteractingSLE.Spec.Sec5.Aux61FibDataData

/-! # Admissible measurable corrections and cutoff selection -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open QuantumZipper (H)
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.Sec5.Aux61GInst
open Aux61Fib (FibData)
open Aux61FibData
open Aux61Win (IsCutoffOn)
open Restart.FlowStopIdentCMI (CMCut)

/-- Set a measurable harmonic family to zero on one measurable null set so
its almost-sure boundary cancellation holds at every history. -/
theorem exists_validCorrection_ae_eq {β : Type*} [MeasurableSpace β] {μ : Measure β}
    (d : FibData) {Q : β → ℂ → ℝ}
    (hQ : Measurable (fun p : β × ℂ => Q p.1 p.2))
    (hqh : ∀ b, InnerProductSpace.HarmonicOnNhd (Q b) H)
    (hq0 : ∀ᵐ b ∂μ, ∀ x ∈ d.O₀, Tendsto (Q b) (𝓝[H] (x : ℂ)) (𝓝 0)) :
    ∃ R : β → ℂ → ℝ, Measurable (fun p : β × ℂ => R p.1 p.2) ∧
      (∀ b, ValidQ d (R b)) ∧ R =ᵐ[μ] Q := by
  classical
  obtain ⟨N, hsub, hNm, hNμ⟩ := exists_measurable_superset_of_null (ae_iff.1 hq0)
  let R : β → ℂ → ℝ := fun b w => if b ∈ N then 0 else Q b w
  refine ⟨R, Measurable.ite (measurable_fst hNm) measurable_const hQ, fun b => ?_, ?_⟩
  · by_cases hb : b ∈ N
    · have he : R b = fun _ => 0 := funext fun w => by simp [R, hb]
      rw [he]
      exact ⟨InnerProductSpace.harmonicOnNhd_const 0, fun _ _ => tendsto_const_nhds⟩
    · have he : R b = Q b := funext fun w => by simp [R, hb]
      rw [he]
      exact ⟨hqh b, not_not.1 (fun hbad => hb (hsub hbad))⟩
  · have hgood : ∀ᵐ b ∂μ, b ∉ N := by
      apply mem_ae_iff.2
      have he : {b | b ∉ N}ᶜ = N := by ext b; simp
      rw [he]
      exact hNμ
    filter_upwards [hgood] with b hb
    exact funext fun w => by simp [R, hb]

/-- Once the actual harmonic representative has the reference boundary
values, its measurable correction can satisfy `ValidQ` at every history.
This is an adapter; the physical boundary identification is an explicit input. -/
theorem exists_measurable_validInitialCorrection {β : Type*} [MeasurableSpace β] {μ : Measure β}
    (d : FibData) {T : β → DistOn upperHalfPlaneOpens} (hT : Measurable T)
    (hh : ∀ᵐ b ∂μ, IsHarmonicDistOn (T b) H)
    (hboundary : ∀ᵐ b ∂μ, ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v H →
      (∀ ψ : TestOn upperHalfPlaneOpens, T b ψ = ∫ w, v w * ψ w) →
      ∀ x ∈ d.O₀, Tendsto (fun w => v w - Aux61GlueK.refMean0 d w) (𝓝[H] (x : ℂ)) (𝓝 0)) :
    ∃ Q : β → ℂ → ℝ, Measurable (fun p : β × ℂ => Q p.1 p.2) ∧
      (∀ b, ValidQ d (Q b)) ∧
      ∀ᵐ b ∂μ, ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v H →
        (∀ ψ : TestOn upperHalfPlaneOpens, T b ψ = ∫ w, v w * ψ w) →
        EqOn (fun w => Aux61GlueK.refMean0 d w + Q b w) v H := by
  obtain ⟨Q, hQm, hQh, hQrep⟩ := exists_measurable_initialCorrection d hT hh
  have hQ0 : ∀ᵐ b ∂μ, ∀ x ∈ d.O₀, Tendsto (Q b) (𝓝[H] (x : ℂ)) (𝓝 0) := by
    filter_upwards [hh, hboundary, hQrep] with b hb hbd hrep
    obtain ⟨v, hv, hvr⟩ := hb
    have hvr' : ∀ ψ : TestOn upperHalfPlaneOpens, T b ψ = ∫ w, v w * ψ w :=
      fun ψ => hvr ψ ψ.tsupport_subset
    intro x hx
    refine (hbd v hv hvr' x hx).congr' ?_
    have hH : ∀ᶠ w : ℂ in 𝓝[H] (x : ℂ), w ∈ H := self_mem_nhdsWithin
    filter_upwards [hH] with w hw
    have he := hrep v hv hvr' hw
    linarith
  obtain ⟨R, hRm, hRv, hRQ⟩ := exists_validCorrection_ae_eq d hQm hQh hQ0
  refine ⟨R, hRm, hRv, ?_⟩
  filter_upwards [hQrep, hRQ] with b hb he
  rw [he]
  exact hb

/-- Fixed-window admissible corrections give the measurable cutoff inputs of
the fibre cover, with one deterministic neighbourhood for all histories. -/
theorem exists_measurable_fibreCutoffs {β : Type*} [MeasurableSpace β]
    (d : FibData) {Q : β → ℂ → ℝ}
    (hQm : Measurable (fun p : β × ℂ => Q p.1 p.2)) (hQv : ∀ b, ValidQ d (Q b)) :
    ∃ (N : Set ℂ) (F : β → CMCut), d.buffer ⊆ N ∧
      (∀ b, IsCutoffOn (F b) (withQ d (Q b)).q N (withQ d (Q b)).O₀) ∧
      Measurable (fun p : β × ℂ => (withQ d (Q p.1)).q p.2) ∧
      Measurable (fun p : β × ℂ => (F p.1).f p.2) ∧
      Measurable (fun p : β × ℂ => QuantumZipper.K3.greenDensity (F p.1).f p.2) := by
  obtain ⟨N, F, hKN, hcut, hfm, hsrc⟩ := exists_measurable_cmCuts d.O₀_open d.buffer_compact
    d.buffer_real hQm (fun b => (hQv b).1) (fun b => (hQv b).2)
  refine ⟨N, F, subset_closure.trans hKN, fun b => ?_, ?_, hfm, hsrc⟩
  · rw [withQ_q_of_valid d (Q b) (hQv b), withQ_O₀]
    exact hcut b
  · convert hQm using 1
    funext p
    exact congrFun (withQ_q_of_valid d (Q p.1) (hQv p.1)) p.2

end InteractingSLE.Sec5.Aux61GInst
