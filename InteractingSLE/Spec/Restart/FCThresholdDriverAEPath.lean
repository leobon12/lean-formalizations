/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FCThresholdDriverAEMeas
import InteractingSLE.Spec.Restart.RetAux79Path

/-!
# Continuous drivers of the source first-contact chart paths

Window drivers are glued using the landed deterministic clock theorem. The
source proof uses confinement from Lemma 7.7 and simplicity from Aux. 25.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)
open LQGMetric (DistOn)

namespace InteractingSLE.Restart.FCPlumb

universe u

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- Good continuation geometry supplies the existing measurable chart-path
specification on any measurable event where it holds pointwise. -/
theorem contSpec_of_continuationGood {d : PairData Ω} {E : Set Ω}
    (hE : MeasurableSet E) (hsub : E ⊆ d.E)
    {ρ ρ' : Ω → ℝ≥0 → ℂ} {ζ ζ' : Ω → ℝ≥0∞} {σ τ : Ω → ℝ≥0}
    (hσ : Measurable σ) (hζ : Measurable ζ) (hρ : ∀ t, Measurable fun ω => ρ ω t)
    (hlt : ∀ ω ∈ E, (σ ω : ℝ≥0∞) < ζ ω)
    (hg : ∀ ω ∈ E, IsContinuationGood (ρ ω) (ζ ω) (σ ω) (ρ' ω) (ζ' ω) (τ ω))
    (hC : ∀ ω ∈ E, IsFirstContactChart (ρ ω) (σ ω) (ρ' ω) (τ ω)
      (d.fwd ω) (d.inv ω) (d.lift ω))
    (hD : ∀ ω ∈ E, d.D ω = activeDomain (ρ ω) (σ ω) (ρ' ω) (τ ω))
    (h0 : ∀ ω ∈ E, (ρ' ω 0).im = 0) : IsContSpec d E σ ρ ζ := by
  refine ⟨hE, hsub, hσ, hζ, hρ, fun ω hω => (hg ω hω).continuousOn₁, hlt,
    fun ω hω s hs hsζ => ?_, fun ω hω s hs hsζ => ?_, fun ω hω => ?_⟩
  · rw [hD ω hω]
    exact (hg ω hω).conf s hs hsζ
  · rw [hD ω hω]
    exact (hg ω hω).exists_limit (hC ω hω) (h0 ω hω) hs hsζ
  · exact (hC ω hω).2.2.2.2.2.2.2.2.1

/-- A chart path satisfying the continuation specification has one globally
continuous driver, including at its finite terminal capacity. -/
theorem exists_driver_cGamma {d : PairData Ω} (hd : d.IsMeasGood) {E : Set Ω}
    {ρ ρ' : Ω → ℝ≥0 → ℂ} {ζ ζ' : Ω → ℝ≥0∞} {σ τ : Ω → ℝ≥0}
    (hs : IsContSpec d E σ ρ ζ) {ω : Ω} (hω : ω ∈ E)
    (hg : IsContinuationGood (ρ ω) (ζ ω) (σ ω) (ρ' ω) (ζ' ω) (τ ω))
    (hC : IsFirstContactChart (ρ ω) (σ ω) (ρ' ω) (τ ω)
      (d.fwd ω) (d.inv ω) (d.lift ω))
    (hclk : IsClockOn (chartClock (cPath d E σ ρ ζ ω)) (ζ ω - σ ω)) :
    ∃ W : ℝ≥0 → ℝ, Continuous W ∧ W 0 = 0 ∧
      IsGeneratingTrace W (cLife d E σ ρ ζ ω) (cGamma d E σ ρ ζ ω) := by
  have heq : cClock d E σ ρ ζ ω = chartClock (cPath d E σ ρ ζ ω) := hs.cClock_eq hd hω
  have hwin : ∀ S : ℝ≥0, 0 < S → (S : ℝ≥0∞) ≤ ζ ω - σ ω →
      ∃ W : ℝ → ℝ, Continuous W ∧ W 0 = 0 ∧
        ∀ t ∈ Icc 0 S, QuantumZipper.fwdHull W (chartClock (cPath d E σ ρ ζ ω) t) =
          fillH (cPath d E σ ρ ζ ω '' Icc 0 t) := by
    intro S hS hSV
    obtain ⟨-, -, -, W, hW, hW0, hWK⟩ := hg.exists_driver_chartClock hC hS
      ((coe_le_sub_iff (hs.lt ω hω).le).1 hSV) (hs.continuous_cPath hd ω).continuousOn
      (fun r _ => (hs.cPath_spec hω r).1)
      (fun r hr => by rw [(hs.cPath_spec hω r).2.2.1,
        contTime_of_le ((ENNReal.coe_le_coe.2 hr.2).trans hSV)]) (hs.cPath_zero hω)
    exact ⟨W, hW, hW0, fun t ht => (hWK t ht).2⟩
  obtain ⟨W, hW, hW0, hWK⟩ := RetAux79.exists_driver_of_windows hclk
    (tsub_pos_of_lt (hs.lt ω hω)) hwin
  refine ⟨W, hW, hW0, ?_⟩
  have htr := RetAux79.isGeneratingTrace_invClock hclk (hs.continuous_cPath hd ω)
    (hs.cPath_zero hω) hWK
  have heγ : cGamma d E σ ρ ζ ω = fun u => cPath d E σ ρ ζ ω
      (invClock (chartClock (cPath d E σ ρ ζ ω)) (ζ ω - σ ω) u) :=
    funext fun u => by simp only [cGamma, hω, ite_true, heq]
  rw [heγ]
  simpa only [cLife, hω, ite_true, heq] using htr

/-- Under the source coupling, both original measured paths have the continuation
geometry needed for window-driver gluing, almost surely at their first contact. -/
theorem ae_continuationGood_flowLines
    {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (h77 : Supp10.Lemma77Statement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps)
    {x₁ x₂ θ₁ θ₂ : ℝ} (hx : x₂ < x₁) (hθ : θ₁ < θ₂ + Real.pi)
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps)
    {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁)
    (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    {d : PairData Ω} (hd : d.IsMeasGood) (hζ₁ : d.ζ₁ = ζ₁) (hζ₂ : d.ζ₂ = ζ₂)
    (hae : ∀ᵐ ω ∂P, ω ∈ d.G ∧
      (∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → d.η₁ ω s = η₁ ω s) ∧
      ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₂ ω → d.η₂ ω s = η₂ ω s) :
    ∀ᵐ ω ∂P, ω ∈ meetSet d →
      IsContinuationGood (d.η₁ ω) (d.ζ₁ ω) (d.s₀ ω) (d.η₂ ω) (d.ζ₂ ω) (d.t₀ ω) ∧
      IsContinuationGood (d.η₂ ω) (d.ζ₂ ω) (d.t₀ ω) (d.η₁ ω) (d.ζ₁ ω) (d.s₀ ω) ∧
      (∀ s : ℝ≥0, (s : ℝ≥0∞) < d.ζ₁ ω →
        ConformalImage.hcapSet (fillH (d.η₁ ω '' Icc 0 s)) = 2 * s) ∧
      (∀ s : ℝ≥0, (s : ℝ≥0∞) < d.ζ₂ ω →
        ConformalImage.hcapSet (fillH (d.η₂ ω '' Icc 0 s)) = 2 * s) := by
  subst hζ₁ hζ₂
  filter_upwards [hae, ae_isPathGood_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₁,
    ae_isPathGood_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₂,
    h77 κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ d.ζ₁ d.ζ₂ hη₁ hη₂]
    with ω ha hp₁ hp₂ h7 hm
  have hf := hd.isFirstContact (mem_meetSet_iff.1 hm).1
  have hfo := (isFirstContact_congr ha.2.1 ha.2.2).1 hf
  obtain ⟨s, t, hfc, hc₁, hc₂⟩ := h7 ⟨_, _, hfo.1, hfo.2.1, hfo.2.2.1⟩
  obtain ⟨rfl, rfl⟩ := Sec7.IsFirstContact.unique hfc hfo
  refine ⟨(isContinuationGood_of_isPathGood hp₁ hp₂ hfc hc₁).congr ha.2.1 ha.2.2,
    (isContinuationGood_of_isPathGood hp₂ hp₁ (IsFirstContact.swap hfc)
      (fun r hr hrζ => by rw [activeDomain_comm]; exact hc₂ r hr hrζ)).congr ha.2.2 ha.2.1,
    fun s hs => ?_, fun s hs => ?_⟩
  · rw [image_Icc_congr ha.2.1 hs.le]
    exact hp₁.hcapSet hs
  · rw [image_Icc_congr ha.2.2 hs.le]
    exact hp₂.hcapSet hs

/-- The actual canonical chart continuations have globally continuous drivers
almost surely. This discharges pathwise driver existence without using a K2 law,
force weights, a boundary word, or a threshold identity. -/
theorem ae_exists_drivers_canonClock
    {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (h77 : Supp10.Lemma77Statement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps)
    {x₁ x₂ θ₁ θ₂ : ℝ} (hx : x₂ < x₁) (hθ : θ₁ < θ₂ + Real.pi)
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps)
    {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁)
    (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    {d : PairData Ω} (hd : d.IsMeasGood) (hζ₁ : d.ζ₁ = ζ₁) (hζ₂ : d.ζ₂ = ζ₂)
    (hae : ∀ᵐ ω ∂P, ω ∈ d.G ∧
      (∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → d.η₁ ω s = η₁ ω s) ∧
      ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₂ ω → d.η₂ ω s = η₂ ω s)
    {γ₁ γ₂ : Ω → ℝ≥0 → ℂ} {U₁ U₂ : Ω → ℝ≥0∞}
    (hcanon : d.IsCanonClock P γ₁ γ₂ U₁ U₂) :
    ∀ᵐ ω ∂P, ω ∈ meetSet d →
      (∃ W : ℝ≥0 → ℝ, Continuous W ∧ W 0 = 0 ∧ IsGeneratingTrace W (U₁ ω) (γ₁ ω)) ∧
      (∃ W : ℝ≥0 → ℝ, Continuous W ∧ W 0 = 0 ∧ IsGeneratingTrace W (U₂ ω) (γ₂ ω)) := by
  classical
  have hgeo := ae_continuationGood_flowLines h77 hκ hκ4 hb hx hθ hh hη₁ hη₂ hd hζ₁ hζ₂ hae
  let Good : Set Ω := {ω | ω ∈ meetSet d →
    IsContinuationGood (d.η₁ ω) (d.ζ₁ ω) (d.s₀ ω) (d.η₂ ω) (d.ζ₂ ω) (d.t₀ ω) ∧
    IsContinuationGood (d.η₂ ω) (d.ζ₂ ω) (d.t₀ ω) (d.η₁ ω) (d.ζ₁ ω) (d.s₀ ω) ∧
    (∀ s : ℝ≥0, (s : ℝ≥0∞) < d.ζ₁ ω →
      ConformalImage.hcapSet (fillH (d.η₁ ω '' Icc 0 s)) = 2 * s) ∧
    (∀ s : ℝ≥0, (s : ℝ≥0∞) < d.ζ₂ ω →
      ConformalImage.hcapSet (fillH (d.η₂ ω '' Icc 0 s)) = 2 * s)}
  let G : Set Ω := (toMeasurable P Goodᶜ)ᶜ
  have hG : MeasurableSet G := (measurableSet_toMeasurable P _).compl
  have hGsub : G ⊆ Good := by
    intro ω hω
    by_contra hn
    exact hω (subset_toMeasurable P Goodᶜ hn)
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := by
    rw [ae_iff]
    have he : {ω | ¬ ω ∈ G} = toMeasurable P Goodᶜ := by
      ext ω
      simp only [G, mem_compl_iff, not_not, mem_ofPred_eq]
    rw [he]
    rw [measure_toMeasurable]
    exact ae_iff.1 hgeo
  let E : Set Ω := G ∩ meetSet d
  have hE : MeasurableSet E := hG.inter (retSigma_le P _ (hd.measurableSet_meetSet P))
  have hsub : E ⊆ d.E := fun _ hω => (mem_meetSet_iff.1 hω.2).1
  have hcg ω (hω : ω ∈ E) := hGsub hω.1 hω.2
  have hC ω (hω : ω ∈ E) := (hd.isFirstContactChart (hsub hω)).2
  have hseed ω (hω : ω ∈ E) : (d.η₁ ω 0).im = 0 ∧ (d.η₂ ω 0).im = 0 :=
    ⟨(hd.good ω (hsub hω).1).2.2.2.2.1, (hd.good ω (hsub hω).1).2.2.2.2.2.1⟩
  have hC₂ ω (hω : ω ∈ E) := (hC ω hω).swap (hd.isFirstContact (hsub hω)).2.2.1
  have hs₁ : IsContSpec d E d.s₀ d.η₁ d.ζ₁ :=
    contSpec_of_continuationGood hE hsub hd.measurable_s₀ hd.measζ₁ hd.meas₁
      (fun ω hω => (mem_meetSet_iff.1 hω.2).2.1) (fun ω hω => (hcg ω hω).1) hC
      (fun _ hω => hd.D_of_mem (hsub hω)) (fun ω hω => (hseed ω hω).2)
  have hs₂ : IsContSpec d E d.t₀ d.η₂ d.ζ₂ :=
    contSpec_of_continuationGood hE hsub hd.measurable_t₀ hd.measζ₂ hd.meas₂
      (fun ω hω => (mem_meetSet_iff.1 hω.2).2.2) (fun ω hω => (hcg ω hω).2.1) hC₂
      (fun ω hω => (hd.D_of_mem (hsub hω)).trans activeDomain_comm)
      (fun ω hω => (hseed ω hω).1)
  have hgm ω (hω : ω ∈ E) :
      IsMapOut (fillH (prefixSet (d.η₁ ω) (d.s₀ ω) (d.η₂ ω) (d.t₀ ω))) (d.g ω) := by
    have hg : IsMapOut (fillH (d.K ω)) (d.g ω) :=
      ConformalImage.isMapOut_mapOut (hd.isHPHull ω)
    rwa [PairData.K_of_mem (hsub hω)] at hg
  have hshift ω (hω : ω ∈ E) : (d.shift ω).im = 0 := by
    obtain ⟨x, hx⟩ := (hd.isFirstContactChart (hsub hω)).1
    rw [hx]
    simp
  have hclk₁ : ∀ ω ∈ E, IsClockOn (chartClock (cPath d E d.s₀ d.η₁ d.ζ₁ ω))
      (d.ζ₁ ω - d.s₀ ω) := by
    intro ω hω
    exact (hcg ω hω).1.isClockOn_chartClock (hC ω hω) (hgm ω hω) (fun _ => rfl)
      (hshift ω hω) (hseed ω hω).2 (hcg ω hω).2.2.1 (hs₁.lt ω hω)
      (hs₁.continuous_cPath hd ω).continuousOn (fun r _ => (hs₁.cPath_spec hω r).1)
      (fun r hr => by rw [(hs₁.cPath_spec hω r).2.2.1, contTime_of_le hr]) (hs₁.cPath_zero hω)
  have hclk₂ : ∀ ω ∈ E, IsClockOn (chartClock (cPath d E d.t₀ d.η₂ d.ζ₂ ω))
      (d.ζ₂ ω - d.t₀ ω) := by
    intro ω hω
    exact (hcg ω hω).2.1.isClockOn_chartClock (hC₂ ω hω)
      (by rw [prefixSet_comm]; exact hgm ω hω) (fun _ => rfl)
      (hshift ω hω) (hseed ω hω).1 (hcg ω hω).2.2.2 (hs₂.lt ω hω)
      (hs₂.continuous_cPath hd ω).continuousOn (fun r _ => (hs₂.cPath_spec hω r).1)
      (fun r hr => by rw [(hs₂.cPath_spec hω r).2.2.1, contTime_of_le hr]) (hs₂.cPath_zero hω)
  filter_upwards [hGae, hcanon] with ω hωG hc hm
  have hω : ω ∈ E := ⟨hωG, hm⟩
  have hc₁ := (hc (hsub hω)).1 (hs₁.lt ω hω)
  have hc₂ := (hc (hsub hω)).2 (hs₂.lt ω hω)
  have he₁ := (hs₁.clockData hd hclk₁).2.2.2 ω hω
  have he₂ := (hs₂.clockData hd hclk₂).2.2.2 ω hω
  have hp₁ : cPath d E d.s₀ d.η₁ d.ζ₁ ω = cPath d univ d.s₀ d.η₁ d.ζ₁ ω :=
    funext fun r => by rw [cPath_of_mem hω, cPath_of_mem (mem_univ ω)]
  have hp₂ : cPath d E d.t₀ d.η₂ d.ζ₂ ω = cPath d univ d.t₀ d.η₂ d.ζ₂ ω :=
    funext fun r => by rw [cPath_of_mem hω, cPath_of_mem (mem_univ ω)]
  rw [hp₁] at he₁
  rw [hp₂] at he₂
  obtain ⟨W₁, hw₁, hz₁, ht₁⟩ := exists_driver_cGamma hd hs₁ hω (hcg ω hω).1 (hC ω hω) (hclk₁ ω hω)
  obtain ⟨W₂, hw₂, hz₂, ht₂⟩ := exists_driver_cGamma hd hs₂ hω (hcg ω hω).2.1 (hC₂ ω hω) (hclk₂ ω hω)
  rw [he₁.2, ← hc₁.2] at ht₁
  rw [he₂.2, ← hc₂.2] at ht₂
  exact ⟨⟨W₁, hw₁, hz₁, isGeneratingTrace_congr_le ht₁ fun t ht => by rw [he₁.1]; exact hc₁.1 t ht⟩,
    ⟨W₂, hw₂, hz₂, isGeneratingTrace_congr_le ht₂ fun t ht => by rw [he₂.1]; exact hc₂.1 t ht⟩⟩

end InteractingSLE.Restart.FCPlumb
