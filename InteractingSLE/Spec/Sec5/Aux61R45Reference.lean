/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61R45Converse
import InteractingSLE.Spec.Sec5.Aux61R45Barrier

/-!
# Reference interval barriers for a tilted general-mean coupling

The stochastic converse and the stopped GB7a comparison are combined on the
same independent Brownian enlargement, and the null event is projected back.
Only injectivity of the actual path is added. In particular no full reference
flow, determination theorem, or extension of a stopped coupling is used.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology Finset
open scoped NNReal ENNReal
universe u
namespace InteractingSLE.Sec5.Aux61R45.ReferenceSetting
open Restart Sec7.PocketTraversal
variable {S : Type u} [MeasurableSpace S] (D : ReferenceSetting S)

/-- GB7a for the stopped reference produced by the general-mean converse,
including visits exactly at the window exit, on either side of the seed. -/
theorem ae_avoid_intervals (hκ4 : D.κ ≤ 4) (hb : IsPiecewiseConstantBoundaryData D.b D.J)
    (hinj : ∀ᵐ ω ∂D.P, InjOn (D.Γ ω) {t | (t : ℝ≥0∞) ≤ D.e ω})
    {a a' v : ℝ} (hv : ∀ z ∈ Ioo a a', z ∉ D.J → D.b z = v) :
    (D.y ≤ a → D.κ / 2 - 2 ≤ Sec4.cumWeightRight D.κ (v + D.θ * QuantumZipper.chiC D.κ) →
      ∀ᵐ ω ∂D.P, ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ D.e ω → ∀ z ∈ Ioo a a', D.Γ ω t ≠ z) ∧
    (a' ≤ D.y → D.κ / 2 - 2 ≤ Sec4.cumWeightLeft D.κ (v + D.θ * QuantumZipper.chiC D.κ) →
      ∀ᵐ ω ∂D.P, ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ D.e ω → ∀ z ∈ Ioo a a', D.Γ ω t ≠ z) := by
  let _ := D.prob
  let _ := D.rightContinuous
  have hF := Theorem15.isOrderedForceWord_flowLine D.b D.J D.y
  have hinit : ∀ᵐ ω ∂D.P, 0 < D.e ω ∧
      ContinuousOn (D.W · ω) {t | (t : ℝ≥0∞) < D.e ω} ∧ D.W 0 ω = 0 ∧
      (∀ i, geomLW D.W (fun _ => flowLineXL D.b D.J D.y) i 0 ω = flowLineXL D.b D.J D.y i) ∧
      ∀ j, geomRW D.W (fun _ => flowLineXR D.b D.J D.y) j 0 ω = flowLineXR D.b D.J D.y j := by
    filter_upwards [D.ae_pos] with ω hω
    exact ⟨hω, (D.continuous ω).continuousOn, D.zero ω,
      fun i => geomLW_zero D.continuous D.zero (hF.2.1 i),
      fun j => geomRW_zero D.continuous D.zero (hF.2.2.2 j)⟩
  have hint := fun φ => Coupling.MartMeans2.integrable_apply_of_isCouplingCharFun D.kernel hinit φ
    ((LQGMetric.measurable_distOn_apply φ).comp D.measurable_field)
  obtain ⟨ν, hν, 𝓦, B, hE, -, -⟩ := StoppedK2.isRandomWordEvolutionUpTo_prod_of_isCouplingCharFun
    (𝒢 := ⊥) (F := Set.univ) D.κ_pos D.nullSets bot_le MeasurableSet.univ
    measurable_const measurable_const (fun _ => hF.2.1) (fun _ => hF.2.2.2)
    (fun _ => hF.1) (fun _ => hF.2.2.1) D.zero D.continuous D.adapted D.stopping D.announcing hint
    D.kernel (D.threshold.mono fun _ h _ => h)
  let _ := hν
  let 𝓕 := WholeField.prodFiltration D.filt 𝓦
  let W : ℝ≥0 → S × (ℕ → ℝ) → ℝ := fun t p => D.W t p.1
  let VL := fun i t (p : S × (ℕ → ℝ)) => geomLW D.W (fun _ => flowLineXL D.b D.J D.y) i t p.1
  let VR := fun j t (p : S × (ℕ → ℝ)) => geomRW D.W (fun _ => flowLineXR D.b D.J D.y) j t p.1
  let e := fun p : S × (ℕ → ℝ) => D.e p.1
  let η := fun (p : S × (ℕ → ℝ)) t => D.Γ p.1 t - D.y
  obtain ⟨-, -, -, -, hB, hW, hVL, hVR, hp⟩ := hE
  have hlocal : Sec2.IsSLEEvolutionUpTo D.κ (flowLineXL D.b D.J D.y) (flowLineXR D.b D.J D.y)
      (flowLineRhoL D.κ D.b D.J D.y D.θ) (flowLineRhoR D.κ D.b D.J D.y D.θ)
      (D.P.prod ν) 𝓕 W VL VR B e :=
    ⟨hB, hW, hVL, hVR, hp.mono fun _ h => h trivial⟩
  have hT : Coupling.IsAnnouncingSeq 𝓕 (D.P.prod ν) e (fun n p => D.T n p.1) := by
    refine ⟨fun n => Sec7.PhaseSelFull.isStoppingTime_fst (D.announcing.1 n),
      fun p => D.announcing.2.1 p.1, fun n => ?_, ?_⟩
    · exact ConverseBefore.ae_fst_of_ae (P₀ := ν) (D.announcing.2.2.1 n)
    · exact ConverseBefore.ae_fst_of_ae (P₀ := ν) D.announcing.2.2.2
  have hg : ∀ᵐ p ∂(D.P.prod ν), IsGeneratingTrace (W · p) (e p) (η p) :=
    ConverseBefore.ae_fst_of_ae (P₀ := ν) D.trace
  have hi : ∀ᵐ p ∂(D.P.prod ν), InjOn (η p) {t | (t : ℝ≥0∞) ≤ e p} := by
    filter_upwards [ConverseBefore.ae_fst_of_ae (P₀ := ν) hinj] with p h s hs t ht he
    exact h hs ht (sub_left_inj.1 he)
  have hcW : ∀ p, Continuous (W · p) := fun p => D.continuous p.1
  have hcL : ∀ i p, Continuous (VL i · p) := fun i p =>
    (isForcePath_geomLW D.continuous (fun _ => flowLineXL D.b D.J D.y) p.1 i).1
  have hcR : ∀ j p, Continuous (VR j · p) := fun j p =>
    (isForcePath_geomRW D.continuous (fun _ => flowLineXR D.b D.J D.y) p.1 j).1
  have hc : ∀ᵐ p ∂(D.P.prod ν), ∀ T : ℝ≥0, (T : ℝ≥0∞) = e p →
      ContinuousOn (fun t => (W t p, fun i => VL i t p, fun j => VR j t p)) (Iic T) :=
    ae_of_all _ fun p _ _ =>
      ((hcW p).prodMk ((continuous_pi fun i => hcL i p).prodMk (continuous_pi fun j => hcR j p))).continuousOn
  have key : ∀ p t (z : ℝ), D.Γ p.1 t = z → η p t = ((z - D.y : ℝ) : ℂ) := by
    intro p t z he
    simp only [η, he, Complex.ofReal_sub]
  refine ⟨fun hya hS => ?_, fun hay hS => ?_⟩
  · rcases le_or_gt a' a with haa | haa
    · exact ae_of_all _ fun _ _ _ _ hz => absurd (hz.1.trans hz.2) (not_lt.2 haa)
    obtain ⟨k, hka, hnext, hsum⟩ := Supp8.exists_mark_right D.κ_pos hb D.θ hya haa hv
    have hgb := gb7aEvol_right_upTo D.κ_pos hκ4 hF hlocal
      (fun p => (hcW p).continuousOn) (fun i p => (hcL i p).continuousOn)
      (fun j p => (hcR j p).continuousOn) hT hg hi hc hnext (by rw [hsum]; exact hS)
    apply ConverseBefore.ae_of_ae_fst (P₀ := ν)
    filter_upwards [hgb] with p h t ht z hz he
    exact h t ht (z - D.y) ⟨by linarith [hz.1], by linarith [hz.2]⟩ (key p t z he)
  · rcases le_or_gt a' a with haa | haa
    · exact ae_of_all _ fun _ _ _ _ hz => absurd (hz.1.trans hz.2) (not_lt.2 haa)
    obtain ⟨k, hka, hnext, hsum⟩ := Supp8.exists_mark_left D.κ_pos hb D.θ hay haa hv
    have hgb := gb7aEvol_left_upTo D.κ_pos hκ4 hF hlocal
      (fun p => (hcW p).continuousOn) (fun i p => (hcL i p).continuousOn)
      (fun j p => (hcR j p).continuousOn) hT hg hi hc hnext (by rw [hsum]; exact hS)
    apply ConverseBefore.ae_of_ae_fst (P₀ := ν)
    filter_upwards [hgb] with p h t ht z hz he
    exact h t ht (z - D.y) ⟨by linarith [hz.1], by linarith [hz.2]⟩ (key p t z he)

end InteractingSLE.Sec5.Aux61R45.ReferenceSetting
