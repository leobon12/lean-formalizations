/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FCK2FinalWord

/-!
# Inverse-clock readings at every live canonical tip

This exports the continuation specifications constructed in the existing
source driver-gluing proof, and reads the inverse chart at strictly live tips.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Topology Complex
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)
open LQGMetric (DistOn)

namespace InteractingSLE.Restart.FCPlumb
universe u

/-- A strictly live positive capacity has a strictly later, strictly live
physical preimage. No threshold identity enters this deterministic fact. -/
theorem live_tip_reading_of_clock {Ω : Type*} [MeasurableSpace Ω]
    {d : PairData Ω} {E : Set Ω} {σ : Ω → ℝ≥0}
    {ρ : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞} (hs : IsContSpec d E σ ρ ζ)
    {ω : Ω} (hω : ω ∈ E)
    (hclk : IsClockOn (chartClock (cPath d E σ ρ ζ ω)) (ζ ω - σ ω))
    {γ : ℝ≥0 → ℂ} {U : ℝ≥0∞}
    (hγ : ∀ q : ℝ≥0, (q : ℝ≥0∞) ≤ U → γ q = cPath d E σ ρ ζ ω
      (invClock (chartClock (cPath d E σ ρ ζ ω)) (ζ ω - σ ω) q))
    (hU : U = capLife (chartClock (cPath d E σ ρ ζ ω)) (ζ ω - σ ω)) :
    ∀ q : ℝ≥0, 0 < q → (q : ℝ≥0∞) < U →
      ∃ s : ℝ≥0, σ ω < s ∧ (s : ℝ≥0∞) < ζ ω ∧ d.inv ω (γ q) = ρ ω s := by
  intro q hq hqU
  rw [hU] at hqU
  set C := chartClock (cPath d E σ ρ ζ ω)
  set L := ζ ω - σ ω
  set r := invClock C L q
  obtain ⟨hr, hCr⟩ := hclk.invClock_spec hqU.le
  change (r : ℝ≥0∞) ≤ L at hr
  change C r = (q : ℝ) at hCr
  have hr0 : 0 < r := by
    have h := hclk.strictMonoOn_invClock (show ((0 : ℝ≥0) : ℝ≥0∞) ≤ capLife C L from zero_le)
      hqU.le hq
    simpa only [RetAux79.invClock_zero hclk] using h
  have hrL : (r : ℝ≥0∞) < L := by
    by_contra hn
    have he : (r : ℝ≥0∞) = L := le_antisymm hr (not_lt.1 hn)
    have hLt : L ≠ ⊤ := he ▸ ENNReal.coe_ne_top
    have heNN : L.toNNReal = r := by rw [← he, ENNReal.toNNReal_coe]
    have hcap : capLife C L = (q : ℝ≥0∞) := by
      rw [capLife, ite_eq_right hLt, heNN, hCr, ENNReal.ofReal_coe_nnreal]
    rw [hcap] at hqU
    exact (lt_irrefl _ hqU)
  refine ⟨σ ω + r, lt_add_of_pos_right _ hr0, (Supp7.coe_add_lt_iff).1 hrL, ?_⟩
  rw [hγ q (by rw [hU]; exact hqU.le)]
  have he := (hs.cPath_spec hω r).2.2.1
  rw [contTime_of_le hr] at he
  exact he

/-- Both source canonical chart paths admit live physical tip readings a.s. -/
theorem ae_live_canon_tip_readings
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
      (∀ q : ℝ≥0, 0 < q → (q : ℝ≥0∞) < U₁ ω →
        ∃ s : ℝ≥0, d.s₀ ω < s ∧ (s : ℝ≥0∞) < d.ζ₁ ω ∧ d.inv ω (γ₁ ω q) = d.η₁ ω s) ∧
      (∀ q : ℝ≥0, 0 < q → (q : ℝ≥0∞) < U₂ ω →
        ∃ s : ℝ≥0, d.t₀ ω < s ∧ (s : ℝ≥0∞) < d.ζ₂ ω ∧ d.inv ω (γ₂ ω q) = d.η₂ ω s) := by
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
  have hp₁ : cPath d E d.s₀ d.η₁ d.ζ₁ ω = cPath d univ d.s₀ d.η₁ d.ζ₁ ω :=
    funext fun r => by rw [cPath_of_mem hω, cPath_of_mem (mem_univ ω)]
  have hp₂ : cPath d E d.t₀ d.η₂ d.ζ₂ ω = cPath d univ d.t₀ d.η₂ d.ζ₂ ω :=
    funext fun r => by rw [cPath_of_mem hω, cPath_of_mem (mem_univ ω)]
  rw [← hp₁] at hc₁
  rw [← hp₂] at hc₂
  exact ⟨live_tip_reading_of_clock hs₁ hω (hclk₁ ω hω) hc₁.1 hc₁.2,
    live_tip_reading_of_clock hs₂ hω (hclk₂ ω hω) hc₂.1 hc₂.2⟩

end InteractingSLE.Restart.FCPlumb
