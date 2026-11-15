/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2FbConfig
import InteractingSLE.Spec.Supplement.GW2FbFlowMean

/-!
# The union mean of a retained inverted hull and an explored coupling hull at a stopping time

Packet PROVE-GW2-FABLE. GB9, p. 525 ("Finite-exception uniqueness therefore gives the canonical complete word at
every pre-contact stop"): the finite-word mean identification of GW2's joint (Det), in the generality that serves
both role assignments (GB6: the flow prefix is retained and the counterflow explored; GW2: the counterflow prefix is
retained and the flow line explored) and every later stage:

* the **retained** curve is given by its paths alone — a driver `W` with a generating trace `γ` on `[0, ∞)`, an
  interior tip at `s` and no return to `0` on `(0, s]` — and by its retained mean `hind₁`, for an arbitrary random
  retained force word `(ρL′, ρR′, yL, yR)` (the word of the field read in the chart `Ψ = relMap W s`); the retained
  time `s` may be random (at a later stage the counterflow is read in a stage chart at its relative clock);
* the **explored** curve is an optional hull coupling of an arbitrary force word of ANY lifetime, read at a stopping
  time `τ < ζα` of its driving filtration (a flow line of GW2 may reach a continuation threshold, so deterministic
  times are not available).

* `IsRelChainStop`: the relative chain of the explored driver, frozen before its lifetime, in the retained chart,
  with the hull identities up to `τ` and `Supp8.Q3Rel.IsRelConfigOff` for the words flowed from the two force words;
* `exists_isRelChainStop` (deterministic, from `exists_isRelConfigOff_gw2_hull` and the generic word lemmas
  `Supp8.Q3Chain.isSideWord_flowedData`, `isFlowedWord_flowedData`);
* **`ae_eqOn_unionMean_invHull_stop`**: on `E ∩ {γ(s) ∈ ℍ, 0 < τ < T_c}` (`T_c` the first contact of the explored
  curve with the inverted retained prefix), the harmonic representative `w_U` of the local-set mean of `A ∪ K`
  satisfies `w_U + 𝔥⁰ = G ∘ g̃_u ∘ Ψ − χ (arg g̃_u′ ∘ Ψ + Im relLog)`, where `(Wr, u)` is the relative chain and `G` a
  bounded harmonic extension of the retained word at the marks flowed by `Wr` to `u`.

Inputs about the field that are not proved here (as in `Supp8.GB6LMean.ae_eqOn_unionMean_gb6_hull`): hitting-
measurability of `A` and `K`, field-determination of `A`, locality of `A` and of `A ∪ K`, and the retained mean
`hind₁` (for GW2: `ae_eqOn_retMean_gw2`). Proved here: the configuration, the locality of `K`, the unbounded
components of `K`, the explored mean (`ae_eqOn_explMean_stop`).

Conditional helpers with distinct names; they replace no source theorem. No `κ < 4` hypothesis.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdMap fwdMapInv fwdHull logDerivFwd chiC)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.GW2Fb

open Supp8.GB6 (relMap relInv relClock firstContactTime sphereInv)
open Supp8.Q3Rel (invHull relLog relBad IsRelConfigOff)
open Supp8.GB6LMean (HullsUpTo)
open Supp8.Q3Chain LocalSets

/-! ### The relative chain at a stop -/

/-- **The relative chain of an explored driver, frozen before its lifetime, in the chart of a retained driver.** The
tuple `p = (w′, α′, Wr, ηr)` consists of the frozen explored driver with its generating trace on `[0, ∞)` and the
relative chain; `(ρL, ρR, xL, xR)` is the explored force word and `(ρL′, ρR′, yL, yR)` the retained force word. -/
def IsRelChainStop (κ : ℝ) {nL nR nL' nR' : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (xL : Fin nL → ℝ)
    (xR : Fin nR → ℝ) (ρL' : Fin nL' → ℝ) (ρR' : Fin nR' → ℝ) (yL : Fin nL' → ℝ) (yR : Fin nR' → ℝ)
    (U : ℝ → ℝ) (s : ℝ≥0) (wα : ℝ≥0 → ℝ) (T : ℝ≥0)
    (p : (ℝ≥0 → ℝ) × (ℝ≥0 → ℂ) × (ℝ → ℝ) × (ℝ → ℂ)) : Prop :=
  Continuous p.1 ∧ p.1 0 = 0 ∧ IsGeneratingTrace p.1 ⊤ p.2.1 ∧
    (∃ t₂ : ℝ≥0, T < t₂ ∧ ∀ u ≤ t₂, p.1 u = wα u) ∧
    Continuous p.2.2.1 ∧ p.2.2.1 0 = 0 ∧ IsLoewnerTrace p.2.2.1 p.2.2.2 ∧
    0 < relClock U s (fun r : ℝ => p.1 r.toNNReal) T ∧
    relMap U s '' fwdHull (fun r : ℝ => p.1 r.toNNReal) T =
      fwdHull p.2.2.1 (relClock U s (fun r : ℝ => p.1 r.toNNReal) T) ∧
    HullsUpTo U s (fun r : ℝ => p.1 r.toNNReal) p.2.2.1 T ∧
    ∀ G₀ GE G v : ℂ → ℝ,
      IsBoundedHarmonicExtension (forceBoundaryData κ ρL' ρR' yL yR) (initJumps yL yR) G₀ →
      IsBoundedHarmonicExtension (flowedData κ ρL ρR xL xR (fun r : ℝ => p.1 r.toNNReal) T)
        (flowedJumps xL xR (fun r : ℝ => p.1 r.toNNReal) T) GE →
      IsBoundedHarmonicExtension
        (flowedData κ ρL' ρR' yL yR p.2.2.1 (relClock U s (fun r : ℝ => p.1 r.toNNReal) T))
        (flowedJumps yL yR p.2.2.1 (relClock U s (fun r : ℝ => p.1 r.toNNReal) T)) G →
      (∀ z, v z = G (fwdMap p.2.2.1 (relClock U s (fun r : ℝ => p.1 r.toNNReal) T) (relMap U s z)) -
        chiC κ * ((logDerivFwd p.2.2.1 (relClock U s (fun r : ℝ => p.1 r.toNNReal) T) (relMap U s z)).im +
          (relLog U s z).im)) →
      IsRelConfigOff (invHull U s) (relMap U s) (relInv U s) (relLog U s) (relBad U s)
        (fun r : ℝ => p.1 r.toNNReal) p.2.2.1 (fun r : ℝ => p.2.1 r.toNNReal) p.2.2.2 T
        (relClock U s (fun r : ℝ => p.1 r.toNNReal) T) (chiC κ) (Real.pi / Real.sqrt κ)
        (forceBoundaryData κ ρL' ρR' yL yR) (flowedData κ ρL ρR xL xR (fun r : ℝ => p.1 r.toNNReal) T)
        (flowedData κ ρL' ρR' yL yR p.2.2.1 (relClock U s (fun r : ℝ => p.1 r.toNNReal) T))
        (initJumps yL yR) (flowedJumps xL xR (fun r : ℝ => p.1 r.toNNReal) T)
        (flowedJumps yL yR p.2.2.1 (relClock U s (fun r : ℝ => p.1 r.toNNReal) T)) G₀ GE G v

/-- **The relative chain at a pre-contact time before the explored lifetime** (deterministic). -/
theorem exists_isRelChainStop (κ : ℝ) {nL nR nL' nR' : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} (hxL : ∀ i, xL i ≤ 0) (hxR : ∀ j, 0 ≤ xR j)
    (ρL' : Fin nL' → ℝ) (ρR' : Fin nR' → ℝ) {yL : Fin nL' → ℝ} {yR : Fin nR' → ℝ} (hyL : ∀ i, yL i ≤ 0)
    (hyR : ∀ j, 0 ≤ yR j) {w wα : ℝ≥0 → ℝ} {Tα : ℝ≥0∞} {γ α : ℝ≥0 → ℂ} {s : ℝ≥0}
    (hγ : IsGeneratingTrace w ⊤ γ) (hw : Continuous w) (hw0 : w 0 = 0) (hsH : γ s ∈ H)
    (hNR : ∀ v : ℝ≥0, 0 < v → v ≤ s → γ v ≠ 0)
    (hα : IsGeneratingTrace wα Tα α) (hwα : ContinuousOn wα {t | (t : ℝ≥0∞) < Tα}) (hwα0 : wα 0 = 0)
    {T : ℝ≥0} (hT0 : 0 < T) (hTα : (T : ℝ≥0∞) < Tα)
    (hTc : (T : ℝ≥0∞) < firstContactTime (fun u => (α u : OnePoint ℂ))
      ((fun u => sphereInv (γ u : OnePoint ℂ)) '' Icc 0 s)) :
    ∃ p, IsRelChainStop κ ρL ρR xL xR ρL' ρR' yL yR (fun r : ℝ => w r.toNNReal) s wα T p := by
  obtain ⟨t₁, hTt₁, ht₁⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 (lt_min hTα hTc)
  have hTt₁' : T < t₁ := ENNReal.coe_lt_coe.1 hTt₁
  obtain ⟨w', α', t₂, h12, -, hw'c, hw'0, hα', hweq, -, Wr, ηr, hWr, hWr0, hηr, hu, hK, hKall, hall⟩ :=
    exists_isRelConfigOff_gw2_hull hγ hw hw0 hsH hNR hα hwα hwα0 hT0 hTt₁'
      (lt_of_lt_of_le ht₁ (min_le_left _ _)) (lt_of_lt_of_le ht₁ (min_le_right _ _))
  refine ⟨(w', α', Wr, ηr), hw'c, hw'0, hα', ⟨t₂, hTt₁'.trans h12, hweq⟩, hWr, hWr0, hηr, hu, hK, hKall,
    fun G₀ GE G v hG₀ hGE hG hv => ?_⟩
  have hD : Continuous fun r : ℝ => w' r.toNNReal := hw'c.comp continuous_real_toNNReal
  have hD0 : (fun r : ℝ => w' r.toNNReal) 0 = 0 := by simp only [Real.toNNReal_zero, hw'0]
  have hη := isLoewnerTrace_of_isGeneratingTrace hα'
  exact hall _ _ _ _ _ _ _ _ G₀ GE G v hG₀ hGE hG
    (isSideWord_flowedData hη hD hD0 T.2 κ ρL ρR hxL hxR)
    (isSideWord_flowedData hηr hWr hWr0 hu.le κ ρL' ρR' hyL hyR)
    (isFlowedWord_flowedData hηr hWr hWr0 hu κ ρL' ρR' hyL hyR) hv

/-! ### The union mean -/

/-- **The union mean of a retained inverted hull and an explored coupling hull at a stopping time** (GB9, p. 525;
`Supp8.GB6LMean.ae_eqOn_unionMean_gb6_hull` with the retained curve given by its paths and no-return property at a
possibly random retained time `s`, an arbitrary retained word, and an explored coupling of any lifetime read at a
stopping time). -/
theorem ae_eqOn_unionMean_invHull_stop {κ : ℝ} (hκ : 0 < κ) {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (hxL : ∀ i, xL i ≤ 0) (hxR : ∀ j, 0 ≤ xR j)
    {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} {Wα : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζα : Ω → ℝ≥0∞} {X : Ω → DistOn upperHalfPlaneOpens}
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 Wα VL VR B ζα X) {α γ : Ω → ℝ≥0 → ℂ}
    (hWα : ∀ᵐ ω ∂P, Wα 0 ω = 0 ∧ ContinuousOn (fun t => Wα t ω) {t | (t : ℝ≥0∞) < ζα ω})
    (hα : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => Wα t ω) (ζα ω) (α ω)) {W : ℝ≥0 → Ω → ℝ}
    (hW : ∀ᵐ ω ∂P, Continuous (fun t => W t ω) ∧ W 0 ω = 0 ∧ IsGeneratingTrace (fun t => W t ω) ⊤ (γ ω))
    (s : Ω → ℝ≥0) (hNR : ∀ᵐ ω ∂P, ∀ v : ℝ≥0, 0 < v → v ≤ s ω → γ ω v ≠ 0) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀)
    (hh0 : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (WholeField.centredField X u₀) P)
    (hX : IsMeasurableKilledDriving Wα VL VR ζα) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime (drivingFiltration P hX) τ) (hτζ : ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < ζα ω)
    (E : Set Ω) {A : Ω → Set ℂ}
    (hAeq : ∀ᵐ ω ∂P, ω ∈ E → A ω = invHull (fun r : ℝ => W r.toNNReal ω) (s ω))
    (hunbA : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (A ω),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (A ω)) z))
    {K : Ω → Set ℂ}
    (hKeq : ∀ᵐ ω ∂P, K ω = fwdHull (fun r : ℝ => Wα r.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0))
    (hAm : Measurable[mΩ, hittingSigma] A) (hKm : Measurable[mΩ, hittingSigma] K)
    (hdA : MeasurableSpace.comap A hittingSigma ≤
      aeSigma (MeasurableSpace.comap (WholeField.centredField X u₀) inferInstance) P)
    (hlA : IsLocalSet A (WholeField.centredField X u₀) P)
    (hlU : IsLocalSet (fun ω => A ω ∪ K ω) (WholeField.centredField X u₀) P)
    {g g₁ g₂ : Ω → DistOn upperHalfPlaneOpens}
    (hg : IsLocalSetMean (fun ω => A ω ∪ K ω) (WholeField.centredField X u₀) P g)
    (hg₁ : IsLocalSetMean A (WholeField.centredField X u₀) P g₁)
    (hg₂ : IsLocalSetMean K (WholeField.centredField X u₀) P g₂)
    {nL' nR' : Ω → ℕ} {ρL' : ∀ ω, Fin (nL' ω) → ℝ} {ρR' : ∀ ω, Fin (nR' ω) → ℝ}
    {yL : ∀ ω, Fin (nL' ω) → ℝ} {yR : ∀ ω, Fin (nR' ω) → ℝ} (hyL : ∀ ω i, yL ω i ≤ 0)
    (hyR : ∀ ω j, 0 ≤ yR ω j)
    (hind₁ : ∀ᵐ ω ∂P, ω ∈ E → γ ω (s ω) ∈ H →
      ∀ G₀ : ℂ → ℝ, IsBoundedHarmonicExtension (forceBoundaryData κ (ρL' ω) (ρR' ω) (yL ω) (yR ω))
          (initJumps (yL ω) (yR ω)) G₀ →
        ∀ w₁ : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w₁ (H \ A ω) →
          (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A ω → g₁ ω φ = ∫ z, w₁ z * φ z) →
          EqOn (fun z => w₁ z + u₀ z)
            (fun z => G₀ (relMap (fun r : ℝ => W r.toNNReal ω) (s ω) z) -
              chiC κ * (relLog (fun r : ℝ => W r.toNNReal ω) (s ω) z).im) (H \ A ω)) :
    ∀ᵐ ω ∂P, ω ∈ E → γ ω (s ω) ∈ H → 0 < (τ ω).untopD 0 →
      (((τ ω).untopD 0 : ℝ≥0) : ℝ≥0∞) < firstContactTime (fun u => (α ω u : OnePoint ℂ))
        ((fun u => sphereInv (γ ω u : OnePoint ℂ)) '' Icc 0 (s ω)) →
      ∃ (p : (ℝ≥0 → ℝ) × (ℝ≥0 → ℂ) × (ℝ → ℝ) × (ℝ → ℂ)) (G : ℂ → ℝ),
        IsRelChainStop κ ρL ρR xL xR (ρL' ω) (ρR' ω) (yL ω) (yR ω) (fun r : ℝ => W r.toNNReal ω) (s ω)
          (fun t => Wα t ω) ((τ ω).untopD 0) p ∧
        IsBoundedHarmonicExtension
          (flowedData κ (ρL' ω) (ρR' ω) (yL ω) (yR ω) p.2.2.1
            (relClock (fun r : ℝ => W r.toNNReal ω) (s ω) (fun r : ℝ => p.1 r.toNNReal)
              ((τ ω).untopD 0 : ℝ≥0)))
          (flowedJumps (yL ω) (yR ω) p.2.2.1
            (relClock (fun r : ℝ => W r.toNNReal ω) (s ω) (fun r : ℝ => p.1 r.toNNReal)
              ((τ ω).untopD 0 : ℝ≥0))) G ∧
        ∀ wU : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd wU (H \ (A ω ∪ K ω)) →
          (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (A ω ∪ K ω) → g ω φ = ∫ z, wU z * φ z) →
          EqOn (fun z => wU z + u₀ z)
            (fun z => G (fwdMap p.2.2.1
                (relClock (fun r : ℝ => W r.toNNReal ω) (s ω) (fun r : ℝ => p.1 r.toNNReal)
                  ((τ ω).untopD 0 : ℝ≥0)) (relMap (fun r : ℝ => W r.toNNReal ω) (s ω) z)) -
              chiC κ * ((logDerivFwd p.2.2.1
                (relClock (fun r : ℝ => W r.toNNReal ω) (s ω) (fun r : ℝ => p.1 r.toNNReal)
                  ((τ ω).untopD 0 : ℝ≥0)) (relMap (fun r : ℝ => W r.toNNReal ω) (s ω) z)).im +
                (relLog (fun r : ℝ => W r.toNNReal ω) (s ω) z).im))
            (H \ (A ω ∪ K ω)) := by
  classical
  set T : Ω → ℝ≥0 := fun ω => (τ ω).untopD 0 with hTdef
  set Tc : Ω → ℝ≥0∞ := fun ω => firstContactTime (fun u => (α ω u : OnePoint ℂ))
    ((fun u => sphereInv (γ ω u : OnePoint ℂ)) '' Icc 0 (s ω)) with hTc
  set D : Set Ω := {ω | ω ∈ E ∧ γ ω (s ω) ∈ H ∧ 0 < T ω ∧ (T ω : ℝ≥0∞) < Tc ω} with hD
  -- the stopping time is before the lifetime, in the `untopD` form
  have hTζ : ∀ᵐ ω ∂P, (T ω : ℝ≥0∞) < ζα ω := by
    filter_upwards [hτζ] with ω hlt
    have hne : τ ω ≠ ⊤ := fun h => by
      rw [h] at hlt
      exact not_top_lt hlt
    obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1 hne
    show (((τ ω).untopD 0 : ℝ≥0) : ℝ≥0∞) < ζα ω
    rw [← ht, WithTop.untopD_coe]
    rw [← ht] at hlt
    exact hlt
  -- the per-sample relative chain, chosen
  have hex : ∀ᵐ ω ∂P, ω ∈ D → ∃ p, IsRelChainStop κ ρL ρR xL xR (ρL' ω) (ρR' ω) (yL ω) (yR ω)
      (fun r : ℝ => W r.toNNReal ω) (s ω) (fun t => Wα t ω) (T ω) p := by
    filter_upwards [hW, hNR, hWα, hα, hTζ] with ω hWω hNRω hWαω hαω hTζω hωD
    obtain ⟨-, hsH, hT0, hTcω⟩ := hωD
    exact exists_isRelChainStop κ ρL ρR hxL hxR (ρL' ω) (ρR' ω) (hyL ω) (hyR ω) hWω.2.2 hWω.1 hWω.2.1 hsH
      hNRω hαω hWαω.2 hWαω.1 hT0 hTζω hTcω
  set pr : Ω → (ℝ≥0 → ℝ) × (ℝ≥0 → ℂ) × (ℝ → ℝ) × (ℝ → ℂ) := fun ω =>
    Classical.epsilon fun p => IsRelChainStop κ ρL ρR xL xR (ρL' ω) (ρR' ω) (yL ω) (yR ω)
      (fun r : ℝ => W r.toNNReal ω) (s ω) (fun t => Wα t ω) (T ω) p with hpr
  have hprs : ∀ᵐ ω ∂P, ω ∈ D → IsRelChainStop κ ρL ρR xL xR (ρL' ω) (ρR' ω) (yL ω) (yR ω)
      (fun r : ℝ => W r.toNNReal ω) (s ω) (fun t => Wα t ω) (T ω) (pr ω) := by
    filter_upwards [hex] with ω hω hωD
    exact Classical.epsilon_spec (p := fun p => IsRelChainStop κ ρL ρR xL xR (ρL' ω) (ρR' ω) (yL ω) (yR ω)
      (fun r : ℝ => W r.toNNReal ω) (s ω) (fun t => Wα t ω) (T ω) p) (hω hωD)
  -- the explored driver (frozen) and the relative clock
  set Dw : Ω → ℝ → ℝ := fun ω r => (pr ω).1 r.toNNReal with hDw
  set uc : Ω → ℝ := fun ω => relClock (fun r : ℝ => W r.toNNReal ω) (s ω) (Dw ω) (T ω) with huc
  -- the three bounded harmonic extensions
  set G₀ : Ω → ℂ → ℝ := fun ω => (Sec7.StripSysField.exists_isBoundedHarmonicExtension_forceBoundaryData κ
    (ρL' ω) (ρR' ω) (yL ω) (yR ω)).choose with hG₀
  set GE : Ω → ℂ → ℝ := fun ω => (Sec7.StripSysField.exists_isBoundedHarmonicExtension_forceBoundaryData κ
    ρL ρR (fun i => Exist.StagedLaw.markPosL (Dw ω) (T ω) (xL i))
    (fun j => Exist.StagedLaw.markPos (Dw ω) (T ω) (xR j))).choose with hGE
  set G : Ω → ℂ → ℝ := fun ω => (Sec7.StripSysField.exists_isBoundedHarmonicExtension_forceBoundaryData κ
    (ρL' ω) (ρR' ω) (fun i => Exist.StagedLaw.markPosL (pr ω).2.2.1 (uc ω) (yL ω i))
    (fun j => Exist.StagedLaw.markPos (pr ω).2.2.1 (uc ω) (yR ω j))).choose with hG
  have hG₀s : ∀ ω, IsBoundedHarmonicExtension (forceBoundaryData κ (ρL' ω) (ρR' ω) (yL ω) (yR ω))
      (initJumps (yL ω) (yR ω)) (G₀ ω) := fun ω => by
    rw [coe_initJumps]
    exact (Sec7.StripSysField.exists_isBoundedHarmonicExtension_forceBoundaryData _ _ _ _ _).choose_spec
  have hGEs : ∀ ω, IsBoundedHarmonicExtension (flowedData κ ρL ρR xL xR (Dw ω) (T ω))
      (flowedJumps xL xR (Dw ω) (T ω)) (GE ω) := fun ω => by
    rw [flowedJumps, coe_initJumps]
    exact (Sec7.StripSysField.exists_isBoundedHarmonicExtension_forceBoundaryData _ _ _ _ _).choose_spec
  have hGs : ∀ ω, IsBoundedHarmonicExtension
      (flowedData κ (ρL' ω) (ρR' ω) (yL ω) (yR ω) (pr ω).2.2.1 (uc ω))
      (flowedJumps (yL ω) (yR ω) (pr ω).2.2.1 (uc ω)) (G ω) := fun ω => by
    rw [flowedJumps, coe_initJumps]
    exact (Sec7.StripSysField.exists_isBoundedHarmonicExtension_forceBoundaryData _ _ _ _ _).choose_spec
  -- the candidate mean
  set v : Ω → ℂ → ℝ := fun ω z => G ω (fwdMap (pr ω).2.2.1 (uc ω) (relMap (fun r : ℝ => W r.toNNReal ω) (s ω) z)) -
    chiC κ * ((logDerivFwd (pr ω).2.2.1 (uc ω) (relMap (fun r : ℝ => W r.toNNReal ω) (s ω) z)).im +
      (relLog (fun r : ℝ => W r.toNNReal ω) (s ω) z).im) with hv
  -- the configuration on `D`
  have hcfg : ∀ᵐ ω ∂P, ω ∈ D → IsRelConfigOff (A ω)
      (relMap (fun r : ℝ => W r.toNNReal ω) (s ω)) (relInv (fun r : ℝ => W r.toNNReal ω) (s ω))
      (relLog (fun r : ℝ => W r.toNNReal ω) (s ω)) (relBad (fun r : ℝ => W r.toNNReal ω) (s ω))
      (Dw ω) (pr ω).2.2.1 (fun r : ℝ => (pr ω).2.1 r.toNNReal) (pr ω).2.2.2 ((fun ω => (T ω : ℝ)) ω)
      (uc ω) (chiC κ) (Real.pi / Real.sqrt κ)
      (forceBoundaryData κ (ρL' ω) (ρR' ω) (yL ω) (yR ω)) (flowedData κ ρL ρR xL xR (Dw ω) (T ω))
      (flowedData κ (ρL' ω) (ρR' ω) (yL ω) (yR ω) (pr ω).2.2.1 (uc ω))
      (initJumps (yL ω) (yR ω)) (flowedJumps xL xR (Dw ω) (T ω))
      (flowedJumps (yL ω) (yR ω) (pr ω).2.2.1 (uc ω)) (G₀ ω) (GE ω) (G ω) (v ω) := by
    filter_upwards [hprs, hAeq] with ω hω hAω hωD
    have hc := (hω hωD).2.2.2.2.2.2.2.2.2.2
    rw [hAω hωD.1]
    exact hc (G₀ ω) (GE ω) (G ω) (v ω) (hG₀s ω) (hGEs ω) (hGs ω) fun z => rfl
  -- locality and topology of the explored hull
  obtain ⟨hX', hker⟩ := hC.2.2.2
  have hK' : IsLocalSet (fun ω => fwdHull (fun r : ℝ => Wα r.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)) X P :=
    (hker τ hτ hτζ).1
  have hlK : IsLocalSet K (WholeField.centredField X u₀) P := by
    refine Coupling.IsLocalSet.congr_set
      (WholeField.IsLocalSet.sub_dist hK' (WholeField.isHarmonicDistOn_smoothDist hu₀.1)) ?_
    filter_upwards [hKeq] with ω hω
    simp only [hω]
  have hunbK : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (K ω),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (K ω)) z) := by
    filter_upwards [hKeq, hWα, hTζ] with ω hω hWαω hTζω
    obtain ⟨t₃, hTt₃, ht₃⟩ := exists_real_btwn_of_lt hTζω
    have hfr : fwdHull (fun r : ℝ => Wα r.toNNReal ω) (T ω) =
        fwdHull (frozenDrive (fun t => Wα t ω) t₃) (T ω) :=
      fwdHull_eq_of_eqOn (T ω).coe_nonneg hTt₃ fun r hr =>
        (frozenDrive_eq (w := fun t => Wα t ω) hr).symm
    rw [hω]
    show ∀ z ∈ lowerUnion (fwdHull (fun r : ℝ => Wα r.toNNReal ω) (T ω)), _
    rw [hfr]
    exact Sec5.GlueCond.not_isBounded_lowerUnion_of_isHPHull
      (isHPHull_fwdHull (continuous_frozenDrive_of_lt hWαω.2 ht₃) (T ω).coe_nonneg)
  -- the explored hull on `D`, read with the frozen driver
  have hKD : ∀ᵐ ω ∂P, ω ∈ D → K ω = fwdHull (Dw ω) ((fun ω => (T ω : ℝ)) ω) := by
    filter_upwards [hKeq, hprs] with ω hω hpω hωD
    obtain ⟨t₂, hTt₂, hweq⟩ := (hpω hωD).2.2.2.1
    rw [hω]
    refine fwdHull_eq_of_eqOn (T ω).coe_nonneg (NNReal.coe_lt_coe.2 hTt₂) fun r hr => ?_
    show Wα r.toNNReal ω = (pr ω).1 r.toNNReal
    exact (hweq r.toNNReal (Real.toNNReal_le_iff_le_coe.2 hr.2)).symm
  -- the two partial means
  have hind₂ := ae_eqOn_explMean_stop hκ hC hu₀ hh0 hX hτ hτζ hKeq hKm hg₂
  have hmain := ae_eqOn_unionMean_of_relConfigOff_ver hh0 hu₀.1 hu₀.2.1 hAm hKm hdA hlA hlK hlU hunbA hunbK hg hg₁
    hg₂ (D := D) hKD hcfg
    (by
      filter_upwards [hind₁] with ω hω hωD w₁ hw₁ hr₁
      exact hω hωD.1 hωD.2.1 (G₀ ω) (hG₀s ω) w₁ hw₁ hr₁)
    (by
      filter_upwards [hind₂, hprs] with ω hω hpω hωD w₂ hw₂ hr₂
      obtain ⟨hw'c, hw'0, -, ⟨t₂, hTt₂, hweq⟩, -⟩ := hpω hωD
      refine hω (Dw ω) t₂ (hw'c.comp continuous_real_toNNReal) ?_ (NNReal.coe_lt_coe.2 hTt₂) (fun r hr => ?_)
        (GE ω) (hGEs ω) w₂ hw₂ hr₂
      · show (pr ω).1 (0 : ℝ).toNNReal = 0
        rw [Real.toNNReal_zero, hw'0]
      · show (pr ω).1 r.toNNReal = Wα r.toNNReal ω
        exact hweq r.toNNReal (Real.toNNReal_le_iff_le_coe.2 hr.2))
  filter_upwards [hmain, hprs] with ω hω hpω hE hsH hT0 hTcω
  have hωD : ω ∈ D := ⟨hE, hsH, hT0, hTcω⟩
  exact ⟨pr ω, G ω, hpω hωD, hGs ω, fun wU hwU hrU => hω hωD wU hwU hrU⟩

end InteractingSLE.Theorem14.GW2Fb
