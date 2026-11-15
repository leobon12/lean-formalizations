/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma72
import InteractingSLE.WangWu.TwoSeedHit4

/-!
# Wang–Wu Proposition 4.24: the chamber pair as an optional hull coupling, and the two references

Packet PROVE-WW-B20. Source: `source/external/WW17LP/wang_wu_lean_preprocessed.pdf` (ruling R31), Proposition 4.24
(text dump L1816–L1867). Its proof realises the word `SLE₄(ρL; ρR)` as the image `X = ψ(γ₀ ∩ C)` of the middle seed line
in a chamber `C` between the seed lines of heights `u₁ = −λ(ρR + 2) < 0 < u₂ = λ(ρL + 2)`, with the
wall-measurable chart
`ψ : C → ℍ` and the conditional field `H = (h|_C) ∘ ψ⁻¹`:

> "Proposition 4.20 applies at every stopping time in the filtration enlarged by the walls. Therefore the transformed
> middle line `X` satisfies the local Markov coupling with these values. Lemma 4.22 supplies its continuous driving
> function. The harmonic-mean martingale characterization identifies that driver as `SLE₄(ρL; ρR)`. Its continuity and
> transience follow from the Jordan-closure homeomorphism and the seed curve. […] Write `B` for the pair of walls,
> `Y = h|_C`, `E` for the fields in the two exterior components […] Lemmas 4.3 and 4.2 show that the segment is
> determined by `(B, Y)`. Finally, the joint conditional law of `(X, H)` given `B` is independent of `B` […] This proves
> determination by `H` alone."

This is the `κ = 4` twin of the specification's Lemmas 7.1–7.2 (`κ < 4`: the middle flow line in a pocket between two
outer flow lines; `Sec7.Lemma71J`, `Sec7.Lemma72`, `Sec7.Prop73Ref`), with heights in place of angles. The landed
`κ < 4` pipeline uses `κ < 4` only to know that the (CPF2) seed weights exceed `−2`. This file

* restates that pipeline for **arbitrary seed weights `ρL, ρR > −2` and any `κ > 0`**
  (`exists_isOptionalHullCoupling_chart`, `exists_global_chart`, **`exists_isOptionalHullCoupling_of_chart`**):
  the chart
  form of the coupling clause of the mapped middle segment, with the locality of its hulls for the transported field, is
  an optional hull coupling of the two-seed word with a transient generating trace (Lemma 2.11 = Theorem 2.4 of the
  specification, the terminal capacity is infinite, the GFF conjunct at `τ = 0`);
* states Proposition 4.24's chamber pair on one space as the named input **`Chamber4JointStatement`** (the exact
  `κ = 4` counterpart of `Sec7.Lemma72.Lemma71JointStatement`, with the seed weights `ρL, ρR` directly);
* proves the two references of `WangWu/TwoSeedHit4.lean` from it (**`hit4TraceReferenceStatement_of_joint`**,
  **`hit4DetReferenceStatement_of_joint`**; the determination is Lemma 7.2's (CPF3) argument
  `Prop73Ref.isFieldDeterminedHistory_of_cpf3`, which is Proposition 4.24's last paragraph), hence `hhit`, `hneg` and
  **`LP.TwoSeedGraphInput 4` from the chamber pair alone** (`twoSeedGraphInput_four_of_joint`).

Conditional helpers; they replace no source theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper (H Hbar fwdHull zeroGFFTestCov)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal

universe u v

namespace InteractingSLE.WangWu.Chamber4

open Sec7

/-! ### The chart pipeline for arbitrary seed weights `> −2` -/

section Pocket

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓖 : Filtration ℝ≥0 mΩ} [𝓖.IsRightContinuous] {κ rL rR : ℝ} {γ : Ω → ℝ → ℂ} {W : ℝ≥0 → Ω → ℝ}
  {h : Ω → DistOn upperHalfPlaneOpens} {c : Ω → Chart} {a k : ℝ}

/-- **The chart pair is an optional hull coupling, given the locality of its hulls**
(`Lemma71J.exists_isOptionalHullCoupling_pocket`
for arbitrary seed weights `ρL, ρR > −2`). With a global continuous adapted driver `W` generating every filled prefix of
the mapped segment `γ`, a `𝓖₀`-measurable chart `c` and the chart coupling clause of the two-seed word `(ρL; ρR)` with
infinite lifetime, the driver with its geometric force points, the Brownian motion of the martingale
characterization and
the lifetime `∞` is an optional hull coupling with the transported field, and `W` has a transient generating trace. -/
theorem exists_isOptionalHullCoupling_chart (hκ : 0 < κ) (hL : -2 < rL) (hR : -2 < rR)
    (hnull : ∀ s, MeasurableSet s → P s = 0 → MeasurableSet[𝓖 0] s)
    (hγ : ∀ᵐ ω ∂P, ContinuousOn (γ ω) (Ici 0) ∧ InjOn (γ ω) (Ici 0) ∧ MapsTo (γ ω) (Ici 0) QuantumZipper.Hbar ∧
      γ ω 0 = 0 ∧ Tendsto (fun t => ‖γ ω t‖) atTop atTop ∧
      interior {u ∈ Ici (0 : ℝ) | 0 < u ∧ (γ ω u).im = 0} = ∅)
    (hW0 : ∀ ω, W 0 ω = 0) (hWc : ∀ ω, Continuous fun t => W t ω) (hWa : StronglyAdapted 𝓖 W)
    (hK : ∀ᵐ ω ∂P, ∀ t, 0 ≤ t → ∃ s, 0 ≤ s ∧
      fwdHull (fun s : ℝ => W s.toNNReal ω) s = fillH (γ ω '' Icc 0 t))
    (hh : Measurable h) (hc : ∀ ω, (c ω).IsConformal)
    (hdom : ∀ z, MeasurableSet[𝓖 0] {ω | z ∈ (c ω).dom})
    (hfwd : ∀ z, Measurable[𝓖 0] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z))
    (hliftm : ∀ z, Measurable[𝓖 0] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z))
    (hliftc : ∀ ω, ContinuousOn (c ω).2.2 (c ω).dom)
    (hcf : Coupling.MartMeans2.IsChartCouplingCharFun κ (fun _ : Fin 1 => rL)
      (fun _ : Fin 1 => rR) P 𝓖 W (MartChar.geomL W LP.twoSeedXL) (MartChar.geomR W LP.twoSeedXR)
      (fun _ => ⊤) c a k h)
    (hloc : ∀ τ : Ω → WithTop ℝ≥0, IsStoppingTime 𝓖 τ → (∀ᵐ ω ∂P, τ ω ≠ ⊤) →
      IsLocalSet (fun ω => fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0))
        (fun ω => Chart.chartTransport (hc ω) 1 a k (h ω)) P) :
    ∃ (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
      IsOptionalHullCoupling κ LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓖 W
        (MartChar.geomL W LP.twoSeedXL) (MartChar.geomR W LP.twoSeedXR) B ζ
        (fun ω => Chart.chartTransport (hc ω) 1 a k (h ω)) ∧
      (∀ ω, ζ ω = ⊤) ∧ LP.HasTransientGeneratingTrace P W ζ := by
  have ht : ∀ ω, IsChartTransport (c ω) 1 a k (h ω) (Chart.chartTransport (hc ω) 1 a k (h ω)) := fun ω =>
    Chart.isChartTransport_chartTransport (hc ω)
      (Chart.locallyIntegrableOn_of_continuousOn ((hc ω).continuousOn_lift_inv (hliftc ω))) 1 a k (h ω)
  have hmart := Coupling.MartMeans2.hasTwoSeedMartingaleMeans_of_isChartTransport hc hdom hfwd hliftm hliftc hh
    hW0 hWc hWa hcf ht
  have hE := MartChar.isIntegratedSLEEvolution_geom_of_couplingMean (ρL := fun _ : Fin 1 => rL)
    (ρR := fun _ : Fin 1 => rR) hκ Lemma71.isOrderedForceWord_twoSeed hW0 hWc hWa hmart
  set ζ : Ω → ℝ≥0∞ := fun ω => MartChar.thresholdTime (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR)
    (fun t => W t ω) (fun i t => MartChar.geomL W LP.twoSeedXL i t ω)
    (fun j t => MartChar.geomR W LP.twoSeedXR j t ω) with hζdef
  have hζ : ∀ ω, ζ ω = ⊤ := fun ω =>
    Lemma71.thresholdTime_eq_top_of_fin_one (ρL := fun _ : Fin 1 => rL)
      (ρR := fun _ : Fin 1 => rR) hL hR _ _ _
  have hζe : ζ = fun _ => ⊤ := funext hζ
  have hψm : Measurable fun ω => Chart.chartTransport (hc ω) 1 a k (h ω) :=
    Chart.measurable_chartTransport_random' hc (fun z => 𝓖.le 0 _ (hdom z))
      (fun z => (hfwd z).mono (𝓖.le 0) le_rfl) (fun z => (hliftm z).mono (𝓖.le 0) le_rfl) hliftc hh 1 a k
  have hcf' := Coupling.MartMeans2.isCouplingCharFun_of_isChartTransport hc hdom hfwd hliftm hliftc hh
    (Eventually.of_forall fun ω => ⟨hW0 ω, (hWc ω).continuousOn⟩) hcf ht
  have hU := Lemma71J.usualAugmentation_eq_self 𝓖 hnull
  refine ⟨_, ζ, Lemma71J.isOptionalHullCoupling_of_isCouplingCharFun hE hψm ?_ ?_ ?_, hζ, ?_⟩
  · rw [hU, hζe]; exact hcf'
  · exact Eventually.of_forall fun ω => by rw [hζ ω]; exact ENNReal.zero_lt_top
  · intro τ hτ hτζ
    rw [hU] at hτ
    refine hloc τ hτ (hτζ.mono fun ω hω => ?_)
    rw [hζ ω] at hω
    exact fun htop => by rw [htop] at hω; exact lt_irrefl _ hω
  · filter_upwards [Lemma71.ae_transientTrace_of_fwdHull_eq hW0 hWc hγ hK] with ω ⟨η, hη, hinf⟩
    exact ⟨η, by rw [hζ ω]; exact hη, fun _ => hinf⟩
end Pocket

section Clean

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓖 : Filtration ℝ≥0 mΩ} [𝓖.IsRightContinuous] {κ rL rR : ℝ} {γ : Ω → ℝ → ℂ} {W : ℝ≥0 → Ω → ℝ}
  {T : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens} {c : Ω → Chart} {a k : ℝ}

/-- **The chart pair with a global driver** (`Lemma71J.exists_global_pocketChart` for arbitrary seed weights `> −2`):
the terminal capacity time is almost surely infinite, and on a `𝓖₀`-measurable full event the driver is global; the
modified driver `W'` keeps the filled prefixes and the chart coupling clause with infinite lifetime. -/
theorem exists_global_chart (hκ : 0 < κ) (hL : -2 < rL) (hR : -2 < rR)
    (hnull : ∀ s, MeasurableSet s → P s = 0 → MeasurableSet[𝓖 0] s)
    (hγ : ∀ᵐ ω ∂P, ContinuousOn (γ ω) (Ici 0) ∧ InjOn (γ ω) (Ici 0) ∧ MapsTo (γ ω) (Ici 0) QuantumZipper.Hbar ∧
      γ ω 0 = 0 ∧ Tendsto (fun t => ‖γ ω t‖) atTop atTop ∧
      interior {u ∈ Ici (0 : ℝ) | 0 < u ∧ (γ ω u).im = 0} = ∅)
    (hW0 : ∀ ω, W 0 ω = 0) (hc : ∀ ω, ContinuousOn (fun t => W t ω) {t : ℝ≥0 | (t : ℝ≥0∞) < T ω})
    (hWa : AdaptedBefore 𝓖 T W)
    (hK : ∀ᵐ ω ∂P, ∀ t, 0 ≤ t → ∃ s : ℝ≥0, (s : ℝ≥0∞) < T ω ∧
      fwdHull (fun s : ℝ => W s.toNNReal ω) s = fillH (γ ω '' Icc 0 t))
    (hh : Measurable h) (hcc : ∀ ω, (c ω).IsConformal)
    (hdom : ∀ z, MeasurableSet[𝓖 0] {ω | z ∈ (c ω).dom})
    (hfwd : ∀ z, Measurable[𝓖 0] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z))
    (hliftm : ∀ z, Measurable[𝓖 0] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z))
    (hliftc : ∀ ω, ContinuousOn (c ω).2.2 (c ω).dom)
    (hcf : Coupling.MartMeans2.IsChartCouplingCharFun κ (fun _ : Fin 1 => rL)
      (fun _ : Fin 1 => rR) P 𝓖 W (MartChar.geomL W LP.twoSeedXL) (MartChar.geomR W LP.twoSeedXR)
      T c a k h) :
    ∃ (W' : ℝ≥0 → Ω → ℝ) (G : Set Ω), MeasurableSet[𝓖 0] G ∧ (∀ᵐ ω ∂P, ω ∈ G) ∧
      (∀ ω ∈ G, T ω = ⊤ ∧ ∀ t, W' t ω = W t ω) ∧
      (∀ ω, W' 0 ω = 0) ∧ (∀ ω, Continuous fun t => W' t ω) ∧ StronglyAdapted 𝓖 W' ∧
      (∀ᵐ ω ∂P, ∀ t, 0 ≤ t → ∃ s, 0 ≤ s ∧
        fwdHull (fun s : ℝ => W' s.toNNReal ω) s = fillH (γ ω '' Icc 0 t)) ∧
      Coupling.MartMeans2.IsChartCouplingCharFun κ (fun _ : Fin 1 => rL)
        (fun _ : Fin 1 => rR) P 𝓖 W' (MartChar.geomL W' LP.twoSeedXL)
        (MartChar.geomR W' LP.twoSeedXR) (fun _ => ⊤) c a k h := by
  classical
  have hunb : ∀ᵐ ω ∂P, T ω ≠ ⊤ → ∀ C : ℝ, ∃ s : ℝ≥0, (s : ℝ≥0∞) < T ω ∧ C < |W s ω| := by
    filter_upwards [hγ, hK] with ω hγω hKω
    obtain ⟨hγc, -, hγH, hγ0, hγinf, hγR⟩ := hγω
    exact Lemma71B.unbounded_of_fwdHull_eq (hc ω) hγc hγH hγ0 hγinf hγR hKω
  have hm := Lemma71C.hasMartingaleMeansBefore_of_isChartTransport
    (h' := fun ω => Chart.chartTransport (hcc ω) 1 a k (h ω)) hcc hdom hfwd hliftm hliftc hh hnull hW0 hc hWa
    hunb hcf fun ω => Chart.isChartTransport_chartTransport (hcc ω)
      (Chart.locallyIntegrableOn_of_continuousOn ((hcc ω).continuousOn_lift_inv (hliftc ω))) 1 a k (h ω)
  have hT := Lemma71B.ae_eq_top_of_hasMartingaleMeansBefore hκ hL hR hm hW0 hc hWa hnull hunb
  -- the good event `G`, in `𝓖₀`, on which `T = ⊤`
  set Bad := {ω | ¬ T ω = ⊤} with hBad
  have hBad0 : P Bad = 0 := ae_iff.1 hT
  set G := (toMeasurable P Bad)ᶜ with hGdef
  have hG : MeasurableSet[𝓖 0] G :=
    (hnull _ (measurableSet_toMeasurable P Bad) (by rw [measure_toMeasurable]; exact hBad0)).compl
  have hGt : ∀ t, MeasurableSet[𝓖 t] G := fun t => 𝓖.mono zero_le _ hG
  have hTG : ∀ ω ∈ G, T ω = ⊤ := fun ω hω => by
    by_contra h
    exact hω (subset_toMeasurable P Bad h)
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := by
    have hGc : P Gᶜ = 0 := by rw [hGdef, compl_compl, measure_toMeasurable]; exact hBad0
    rw [ae_iff]
    simpa only [compl_def] using hGc
  set W' : ℝ≥0 → Ω → ℝ := fun t ω => if ω ∈ G then W t ω else 0 with hW'def
  have hW'G : ∀ ω ∈ G, ∀ t, W' t ω = W t ω := fun ω hω t => by simp only [hW'def, hω, ↓reduceIte]
  have hW'n : ∀ ω ∉ G, ∀ t, W' t ω = 0 := fun ω hω t => by simp only [hW'def, hω, ↓reduceIte]
  have hW'0 : ∀ ω, W' 0 ω = 0 := fun ω => by
    by_cases hω : ω ∈ G
    · rw [hW'G ω hω, hW0]
    · exact hW'n ω hω 0
  have hW'c : ∀ ω, Continuous fun t => W' t ω := fun ω => by
    by_cases hω : ω ∈ G
    · have heq : (fun t => W' t ω) = fun t => W t ω := funext (hW'G ω hω)
      rw [heq]
      have hcu := hc ω
      have huniv : {t : ℝ≥0 | (t : ℝ≥0∞) < T ω} = univ := by
        ext t
        simp [hTG ω hω]
      rw [huniv] at hcu
      exact continuousOn_univ.1 hcu
    · have heq : (fun t => W' t ω) = fun _ => (0 : ℝ) := funext (hW'n ω hω)
      rw [heq]
      exact continuous_const
  have hW'a : StronglyAdapted 𝓖 W' := fun t => by
    have heq : (fun ω => W' t ω) = G.indicator (Girsanov.killed T W t) := funext fun ω => by
      by_cases hω : ω ∈ G
      · rw [hW'G ω hω, indicator_of_mem hω,
          Girsanov.killed_of_lt (by rw [hTG ω hω]; exact ENNReal.coe_lt_top)]
      · rw [hW'n ω hω, indicator_of_notMem hω]
    show StronglyMeasurable[𝓖 t] fun ω => W' t ω
    rw [heq]
    exact ((Girsanov.measurable_killed hWa t).indicator (hGt t)).stronglyMeasurable
  have hpath : ∀ ω ∈ G, (fun s : ℝ => W' s.toNNReal ω) = fun s : ℝ => W s.toNNReal ω :=
    fun ω hω => funext fun s => hW'G ω hω _
  have hgeomL : ∀ ω ∈ G, ∀ i t, MartChar.geomL W' LP.twoSeedXL i t ω = MartChar.geomL W LP.twoSeedXL i t ω :=
    fun ω hω i t => by
      have : Bessel.realPath (fun t ω => -W' t ω) ω = Bessel.realPath (fun t ω => -W t ω) ω :=
        funext fun s => by simp only [Bessel.realPath, hW'G ω hω]
      simp only [MartChar.geomL, this]
  have hgeomR : ∀ ω ∈ G, ∀ i t, MartChar.geomR W' LP.twoSeedXR i t ω = MartChar.geomR W LP.twoSeedXR i t ω :=
    fun ω hω i t => by
      have : Bessel.realPath W' ω = Bessel.realPath W ω :=
        funext fun s => by simp only [Bessel.realPath, hW'G ω hω]
      simp only [MartChar.geomR, this]
  refine ⟨W', G, hG, hGae, fun ω hω => ⟨hTG ω hω, hW'G ω hω⟩, hW'0, hW'c, hW'a, ?_, ?_⟩
  · filter_upwards [hK, hGae] with ω hKω hω t ht
    obtain ⟨s, -, hs⟩ := hKω t ht
    refine ⟨s, s.coe_nonneg, ?_⟩
    rw [hpath ω hω]
    exact hs
  -- the chart clause for the global driver
  intro τ hτ hlt u' hu' φ
  set ρL : Fin 1 → ℝ := fun _ => rL with hρL
  set ρR : Fin 1 → ℝ := fun _ => rR with hρR
  set u : Ω → ℂ → ℝ := fun ω => if ω ∈ G then u' ω else
    MartChar.meanExt κ ρL ρR (W ((τ ω).untopD 0) ω) (fun i => MartChar.geomL W LP.twoSeedXL i ((τ ω).untopD 0) ω)
      (fun i => MartChar.geomR W LP.twoSeedXR i ((τ ω).untopD 0) ω) with hudef
  have hu : ∀ ω, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR
        (fun i => MartChar.geomL W LP.twoSeedXL i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)
        (fun i => MartChar.geomR W LP.twoSeedXR i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω))
      (forceJumpSet (fun i => MartChar.geomL W LP.twoSeedXL i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)
        (fun i => MartChar.geomR W LP.twoSeedXR i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)) (u ω) := by
    intro ω
    by_cases hω : ω ∈ G
    · have h1 := hu' ω
      simp only [hgeomL ω hω, hgeomR ω hω, hW'G ω hω] at h1
      simp only [hudef, hω, ↓reduceIte]
      exact h1
    · simp only [hudef, hω, ↓reduceIte]
      exact MartChar.isBoundedHarmonicExtension_meanExt κ ρL ρR _ _ _
  have hltT : ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < T ω := by
    filter_upwards [hlt, hGae] with ω h1 hω
    rw [hTG ω hω]
    exact h1
  have hold := hcf τ hτ hltT u hu φ
  filter_upwards [hold, hGae] with ω hω hωG hsub
  rw [hpath ω hωG] at hsub ⊢
  have huω : u ω = u' ω := by simp only [hudef, hωG, ↓reduceIte]
  rw [hω hsub, huω]
end Clean

section Compose

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓖 : Filtration ℝ≥0 mΩ} [𝓖.IsRightContinuous] {κ rL rR : ℝ} {γ : Ω → ℝ → ℂ} {W : ℝ≥0 → Ω → ℝ}
  {T : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens} {c : Ω → Chart} {a k : ℝ}

/-- **The chart pair as an optional hull coupling with a transient trace**
(`Lemma71J.exists_isOptionalHullCoupling_of_pocketChart`
for arbitrary seed weights `ρL, ρR > −2` and any `κ > 0`): from the chart form of the coupling clause killed at the
terminal capacity time `T`, with the locality of the hulls before `T`; the killed driving histories of the global driver
`W'` and of `(W, T)` agree almost surely. -/
theorem exists_isOptionalHullCoupling_of_chart (hκ : 0 < κ) (hL : -2 < rL) (hR : -2 < rR)
    (hnull : ∀ s, MeasurableSet s → P s = 0 → MeasurableSet[𝓖 0] s)
    (hγ : ∀ᵐ ω ∂P, ContinuousOn (γ ω) (Ici 0) ∧ InjOn (γ ω) (Ici 0) ∧ MapsTo (γ ω) (Ici 0) QuantumZipper.Hbar ∧
      γ ω 0 = 0 ∧ Tendsto (fun t => ‖γ ω t‖) atTop atTop ∧
      interior {u ∈ Ici (0 : ℝ) | 0 < u ∧ (γ ω u).im = 0} = ∅)
    (hW0 : ∀ ω, W 0 ω = 0) (hc : ∀ ω, ContinuousOn (fun t => W t ω) {t : ℝ≥0 | (t : ℝ≥0∞) < T ω})
    (hWa : AdaptedBefore 𝓖 T W)
    (hK : ∀ᵐ ω ∂P, ∀ t, 0 ≤ t → ∃ s : ℝ≥0, (s : ℝ≥0∞) < T ω ∧
      fwdHull (fun s : ℝ => W s.toNNReal ω) s = fillH (γ ω '' Icc 0 t))
    (hh : Measurable h) (hcc : ∀ ω, (c ω).IsConformal)
    (hdom : ∀ z, MeasurableSet[𝓖 0] {ω | z ∈ (c ω).dom})
    (hfwd : ∀ z, Measurable[𝓖 0] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z))
    (hliftm : ∀ z, Measurable[𝓖 0] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z))
    (hliftc : ∀ ω, ContinuousOn (c ω).2.2 (c ω).dom)
    (hcf : Coupling.MartMeans2.IsChartCouplingCharFun κ (fun _ : Fin 1 => rL)
      (fun _ : Fin 1 => rR) P 𝓖 W (MartChar.geomL W LP.twoSeedXL) (MartChar.geomR W LP.twoSeedXR)
      T c a k h)
    (hloc : ∀ τ : Ω → WithTop ℝ≥0, IsStoppingTime 𝓖 τ → (∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < T ω) →
      IsLocalSet (fun ω => fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0))
        (fun ω => Chart.chartTransport (hcc ω) 1 a k (h ω)) P) :
    ∃ (W' : ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
      IsOptionalHullCoupling κ LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓖 W'
        (MartChar.geomL W' LP.twoSeedXL) (MartChar.geomR W' LP.twoSeedXR) B ζ
        (fun ω => Chart.chartTransport (hcc ω) 1 a k (h ω)) ∧
      LP.HasTransientGeneratingTrace P W' ζ ∧
      (fun ω => LawUnique.killedHistory W' (MartChar.geomL W' LP.twoSeedXL) (MartChar.geomR W' LP.twoSeedXR) ζ ω)
        =ᵐ[P] LawUnique.killedHistory W (MartChar.geomL W LP.twoSeedXL) (MartChar.geomR W LP.twoSeedXR) T := by
  obtain ⟨W', G, -, hGae, hGW, hW'0, hW'c, hW'a, hK', hcf'⟩ :=
    exists_global_chart hκ hL hR hnull hγ hW0 hc hWa hK hh hcc hdom hfwd hliftm hliftc hcf
  have hloc' : ∀ τ : Ω → WithTop ℝ≥0, IsStoppingTime 𝓖 τ → (∀ᵐ ω ∂P, τ ω ≠ ⊤) →
      IsLocalSet (fun ω => fwdHull (fun s : ℝ => W' s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0))
        (fun ω => Chart.chartTransport (hcc ω) 1 a k (h ω)) P := by
    intro τ hτ hfin
    have hlt : ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < T ω := by
      filter_upwards [hfin, hGae] with ω h1 hω
      rw [(hGW ω hω).1]
      exact lt_top_iff_ne_top.2 h1
    refine Sec7.IsLocalSet.congr_ae (hloc τ hτ hlt) ?_
    filter_upwards [hGae] with ω hω
    have hp : (fun s : ℝ => W' s.toNNReal ω) = fun s : ℝ => W s.toNNReal ω :=
      funext fun s => (hGW ω hω).2 _
    rw [hp]
  obtain ⟨B, ζ, hC, hζ, htr⟩ := exists_isOptionalHullCoupling_chart hκ hL hR hnull hγ hW'0 hW'c hW'a hK'
    hh hcc hdom hfwd hliftm hliftc hcf' hloc'
  refine ⟨W', B, ζ, hC, htr, ?_⟩
  filter_upwards [hGae] with ω hω
  obtain ⟨hT, hW⟩ := hGW ω hω
  simp only [LawUnique.killedHistory, hζ ω, hT, hW, Lemma71J.geomL_eq_of_forall_eq hW,
    Lemma71J.geomR_eq_of_forall_eq hW]

end Compose

/-! ### Proposition 4.24's chamber pair on one space (named input) -/

/-- **Named input: Proposition 4.24's chamber pair on one space, with the ingredients of its last paragraph** (Wang–Wu
Proposition 4.24, L1816–L1867; the `κ = 4` counterpart of `Sec7.Lemma72.Lemma71JointStatement`). For seed weights
`ρL, ρR > −2` with a weight in `(−2, 0)` there is one probability space carrying
* a right-continuous filtration `𝓖` with the null sets at time `0` ("the filtration enlarged by the walls", augmented),
  the mapped middle segment `γ = ψ(γ₀ ∩ C)` (almost surely a continuous simple path in `ℍ̄` from `0` to `∞` whose real
  boundary times have empty interior: Lemma 4.22, Lemma 4.21 and the Jordan-closure homeomorphism), its driver `W` up to
  the terminal capacity time `T` (`W₀ = 0`, continuous and adapted before `T`, generating every filled prefix of `γ`:
  Lemma 4.22), the measurable original field `h`, the `𝓖₀`-measurable conformal chamber chart `c` ("a wall-measurable
  Riemann map `ψ`") with lifts continuous on the chamber, and the coupling clause of the two-seed word `(ρL; ρR)` in the
  chamber chart, killed at `T` (Proposition 4.20 at the stopping times of the enlarged filtration, with Corollary 4.23:
  "the transformed middle line `X` satisfies the local Markov coupling with these values");
* the pulled-back field `h_ψ = H`, the chart transport of `h` (rule (1.4), `σ = 1`, constants `a`, `k`);
* the locality of the hulls `K_τ` of `W` for `h_ψ` at every stopping time `τ < T` of `𝓖`;
* an exterior record `Q` (the walls `B` and the fields `E, P, Q` off the chamber) with (i) `h` determined by `(Q, h_ψ)`
  (Lemma 4.14), (ii) the killed driving history of `(W, T)` determined by `(h, Q)` (Proposition 4.18 for the middle seed
  line, the chart from the walls), (iii) `(history, h_ψ)` independent of `Q` ("the joint conditional law of `(X, H)`
  given `B` is independent of `B`", with the untouched-component independence). -/
def Chamber4JointStatement : Prop :=
  ∀ rL rR : ℝ, -2 < rL → -2 < rR → (rL < 0 ∨ rR < 0) →
    ∃ (Ω : Type u) (mΩ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (𝓖 : Filtration ℝ≥0 mΩ) (_ : 𝓖.IsRightContinuous) (γ : Ω → ℝ → ℂ) (W : ℝ≥0 → Ω → ℝ)
      (T : Ω → ℝ≥0∞) (h hψ : Ω → DistOn upperHalfPlaneOpens) (c : Ω → Chart) (a k : ℝ)
      (δ : Type u) (_ : MeasurableSpace δ) (Q : Ω → δ),
      (∀ s, MeasurableSet s → P s = 0 → MeasurableSet[𝓖 0] s) ∧
      (∀ᵐ ω ∂P, ContinuousOn (γ ω) (Ici 0) ∧ InjOn (γ ω) (Ici 0) ∧ MapsTo (γ ω) (Ici 0) Hbar ∧
        γ ω 0 = 0 ∧ Tendsto (fun t => ‖γ ω t‖) atTop atTop ∧
        interior {u ∈ Ici (0 : ℝ) | 0 < u ∧ (γ ω u).im = 0} = ∅) ∧
      (∀ ω, W 0 ω = 0) ∧ (∀ ω, ContinuousOn (fun t => W t ω) {t : ℝ≥0 | (t : ℝ≥0∞) < T ω}) ∧
      AdaptedBefore 𝓖 T W ∧
      (∀ᵐ ω ∂P, ∀ t, 0 ≤ t → ∃ s : ℝ≥0, (s : ℝ≥0∞) < T ω ∧
        fwdHull (fun s : ℝ => W s.toNNReal ω) s = fillH (γ ω '' Icc 0 t)) ∧
      Measurable h ∧ (∀ ω, (c ω).IsConformal) ∧
      (∀ z, MeasurableSet[𝓖 0] {ω | z ∈ (c ω).dom}) ∧
      (∀ z, Measurable[𝓖 0] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z)) ∧
      (∀ z, Measurable[𝓖 0] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z)) ∧
      (∀ ω, ContinuousOn (c ω).2.2 (c ω).dom) ∧
      Coupling.MartMeans2.IsChartCouplingCharFun 4 (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) P 𝓖 W
        (MartChar.geomL W LP.twoSeedXL) (MartChar.geomR W LP.twoSeedXR) T c a k h ∧
      (∀ ω, IsChartTransport (c ω) 1 a k (h ω) (hψ ω)) ∧
      (∀ τ : Ω → WithTop ℝ≥0, IsStoppingTime 𝓖 τ → (∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < T ω) →
        IsLocalSet (fun ω => fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)) hψ P) ∧
      Measurable Q ∧ Sec7.IsAEDeterminedBy P (fun ω => (Q ω, hψ ω)) h ∧
      Sec7.IsAEDeterminedBy P (fun ω => (h ω, Q ω))
        (LawUnique.killedHistory W (MartChar.geomL W LP.twoSeedXL) (MartChar.geomR W LP.twoSeedXR) T) ∧
      IndepFun (fun ω => (LawUnique.killedHistory W (MartChar.geomL W LP.twoSeedXL)
        (MartChar.geomR W LP.twoSeedXR) T ω, hψ ω)) Q P

/-- **The chamber pair is an optional hull coupling with a transient trace and a field-determined history**
(Proposition 4.24 for one realisation): the chart pipeline (`exists_isOptionalHullCoupling_of_chart`) and Lemma 7.2's
(CPF3) argument (`Prop73Ref.isFieldDeterminedHistory_of_cpf3`: `F(X) = E[F(X) | Q, H] = E[F(X) | H]`). -/
theorem exists_reference_of_joint (hj : Chamber4JointStatement.{u}) {rL rR : ℝ} (hL : -2 < rL) (hR : -2 < rR)
    (hneg : rL < 0 ∨ rR < 0) :
    ∃ (Ω : Type u) (mΩ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL VR : Fin 1 → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ)
      (ζ : Ω → ℝ≥0∞) (h : Ω → DistOn upperHalfPlaneOpens),
      IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ h ∧
        LP.HasTransientGeneratingTrace P W ζ ∧ LP.IsFieldDeterminedHistory P h W VL VR ζ := by
  obtain ⟨Ω, mΩ, P, hP, 𝓖, h𝓖, γ, W, T, h, hψ, c, a, k, δ, mδ, Q, hnull, hγ, hW0, hc, hWa, hK, hh, hcc,
    hdom, hfwd, hliftm, hliftc, hcf, ht, hloc, hQ, hrec, hdet, hind⟩ := hj rL rR hL hR hneg
  have hψe : hψ = fun ω => Chart.chartTransport (hcc ω) 1 a k (h ω) := funext fun ω =>
    IsChartTransport.eq_chartTransport (hcc ω)
      (Chart.locallyIntegrableOn_of_continuousOn ((hcc ω).continuousOn_lift_inv (hliftc ω))) (ht ω)
  subst hψe
  obtain ⟨W', B, ζ, hC, htr, hhist⟩ := exists_isOptionalHullCoupling_of_chart (by norm_num) hL hR hnull
    hγ hW0 hc hWa hK hh hcc hdom hfwd hliftm hliftc hcf hloc
  refine ⟨Ω, mΩ, P, hP, 𝓖, W', MartChar.geomL W' LP.twoSeedXL, MartChar.geomR W' LP.twoSeedXR, B, ζ, _, hC, htr,
    Prop73Ref.isFieldDeterminedHistory_of_cpf3 hC hQ hrec (hdet.congr_ae hhist.symm)
      (hind.congr ?_ (ae_eq_refl Q))⟩
  filter_upwards [hhist] with ω hω
  rw [hω]

/-- **The trace reference of `TwoSeedHit4` from the chamber pair.** -/
theorem hit4TraceReferenceStatement_of_joint (hj : Chamber4JointStatement.{u}) :
    Hit4TraceReferenceStatement.{u} := by
  intro rL rR hL hR hneg
  obtain ⟨Ω, mΩ, P, hP, 𝓕, W, VL, VR, B, ζ, h, hC, htr, -⟩ := exists_reference_of_joint hj hL hR hneg
  exact ⟨Ω, mΩ, P, hP, 𝓕, W, VL, VR, B, ζ, hC.1, htr⟩

/-- **The determination reference of `TwoSeedHit4` from the chamber pair.** -/
theorem hit4DetReferenceStatement_of_joint (hj : Chamber4JointStatement.{u}) :
    Hit4DetReferenceStatement.{u} := by
  intro rL rR hL hR hneg
  obtain ⟨Ω, mΩ, P, hP, 𝓕, W, VL, VR, B, ζ, h, hC, -, hdet⟩ := exists_reference_of_joint hj hL hR hneg
  exact ⟨Ω, mΩ, P, hP, 𝓕, W, VL, VR, B, ζ, h, hC, hdet⟩

/-- **`hhit` from Proposition 4.24's chamber pair.** -/
theorem twoSeedHittingStatement_four_of_joint (hj : Chamber4JointStatement.{v}) :
    Theorem18.TwoSeedHittingStatement.{u} 4 :=
  twoSeedHittingStatement_four_of_reference (hit4TraceReferenceStatement_of_joint hj)

/-- **`hneg` from Proposition 4.24's chamber pair.** -/
theorem hasFieldDeterminedHistories_four_of_joint (hj : Chamber4JointStatement.{v}) {rL rR : ℝ} (hL : -2 < rL)
    (hR : -2 < rR) (hneg : rL < 0 ∨ rR < 0) :
    LP.HasFieldDeterminedHistories.{u} 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) :=
  hasFieldDeterminedHistories_four_of_reference (hit4TraceReferenceStatement_of_joint hj)
    (hit4DetReferenceStatement_of_joint hj) hL hR hneg

/-- **The two-seed input of Theorem 1.2 at `κ = 4` from Proposition 4.24's chamber pair alone** (the
nonnegative words by
the contact step of Proposition 4.18). -/
theorem twoSeedGraphInput_four_of_joint (hj : Chamber4JointStatement.{v}) : LP.TwoSeedGraphInput.{u} 4 :=
  twoSeedGraphInput_four_of_reference (hit4TraceReferenceStatement_of_joint hj) (hit4DetReferenceStatement_of_joint hj)

end InteractingSLE.WangWu.Chamber4
