/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.HsdSide
import InteractingSLE.Spec.Sec7.PhaseSideAux122

/-!
# Theorem 1.2's R.7 side half: constancy and phase selection from Aux. lemma 122

Packet PROVE-PHASE. PROVE-HSD reduced the side field of `hsd` to `Hsd.R7PhaseSideRemaining`: on every R.7 pocket
test, (1) R.5's boundary word up to one common lattice phase `δ` (`PocketStopSide.PocketStopPhaseSideLimit`),
(2) continuity of `δ` on the positive relative lifetime, (3) `δ = 0` at one positive time. Astra's follow-up 5 §3.2
(R73, `source/external/AstraIG1/ig1_followup5.txt` L456–L483) and the specification's Aux. lemma 122 (pp. 389–391)
derive (2) and (3) from the **retained Gaussian field kernel** of the pocket: its harmonic means `M_t(z)` are
continuous local martingales until `z` is swallowed ("Retain a stopped Gaussian field kernel whose harmonic mean
`M_t(z)` is a continuous local martingale until `z` is swallowed", p. 389; "the adopted mean continuity […] the adopted
martingale characterization", L469–L483). For the extremal pockets of `hsd` both seed weights lie in `(−2, k − 6)`
(`k/2 − 4 < k − 6` for `k > 4`), the range (3.3) of Aux. lemma 122, so the phase is zero on the whole positive
lifetime — which gives (2) and (3) at once.

* `TwoSeedPhaseMeans`: Aux. lemma 122's retained hypothesis on one test — the phase is lattice-valued at positive
  times before the lifetime, and in some right-continuous filtration on the test event (as a subtype, under
  `condSub P A`) in which the traversal's filled prefixes are adapted, the coupling means of every extension of the
  phase-`δ` word are local martingales before swallowing and the lifetime, and continuous before swallowing
  (`PocketMartLife.HasPhaseMeansBefore`);
* `TwoSeedPhaseMeansAt`: (1) together with `TwoSeedPhaseMeans` for the same phase;
* **`twoSeedPhaseSideAt_of_means`**: `Hsd.TwoSeedPhaseSideAt` from it (`ae_phase_eq_zero_of_hasPhaseMeans`);
* `TwoSeedPhaseMeansInput(Inf)`, **`twoSeedPhaseSideInput(Inf)_of_means`**: on every test of a walls' event;
* `R7PhaseMeansRemaining`: on every R.7 configuration (the premises of `Hsd.R7PhaseSideRemaining` verbatim);
  **`r7PhaseSideRemaining_of_means`**;
* **`r7ReferenceStatement_late_means`**: Theorem 1.2's R.7 reference (`Hsd.r7ReferenceStatement_late_hsd`) with the
  side field replaced by `R7PhaseMeansRemaining` at the heights `c = πχ(16/k)`, `c′ = 0`.

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Function
open LQGMetric (DistOn)
open QuantumZipper (H Hbar chiC)
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Sec7.PhaseSide

open WholeField R7Outer R7Leaves RefWire Wire Hsd
open WangWu Lemma71C Lemma71I PocketCoord PocketJordan PocketMarks PocketWordAssembly PocketSeedOpen PocketStopField
  PocketStopWallsFin PocketStopWalls PocketCoupling StripPocketConfig PocketWordPerQ PocketStop R7Aux131 R7Pocket
open MartChar PocketTraversal PhaseSel PocketMartLife

/-! ### One pocket test -/

section Test

/-- **Aux. lemma 122's retained hypothesis on one two-seed pocket test** (specification p. 389; follow-up 5 §3.2): the
phase `δ` lies in `2πχℤ` at every positive time before the relative lifetime, and in some right-continuous filtration
on the test event `A` (a subtype, under `condSub P A`) in which the traversal's filled prefixes are adapted, for every
choice of the bounded harmonic extensions of the phase-`δ` word `(r_L; r_R)` at the seeds' geometric images, the
coupling means are local martingales before swallowing and the relative lifetime, and continuous before swallowing
(`HasPhaseMeansBefore`). -/
def TwoSeedPhaseMeans {Ω : Type*} [MeasurableSpace Ω] (κ rL rR : ℝ) (P : Measure Ω) (A : Set Ω)
    (γ : Ω → ℝ → ℂ) (δ : ℝ≥0 → Ω → ℝ) : Prop :=
  (∀ ω ∈ A, ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) < capLife (γ ω) → ∃ n : ℤ, δ t ω = n * phaseStep κ) ∧
    ∃ 𝓕 : Filtration ℝ≥0 (inferInstance : MeasurableSpace A), 𝓕.IsRightContinuous ∧
      IsPrefixAdapted 𝓕 (fun ω : A => γ ω) ∧
      HasPhaseMeansBefore κ (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) (condSub P A) 𝓕
        (fun t (ω : A) => segDriver (γ ω) t) (fun _ => LP.twoSeedXL) (fun _ => LP.twoSeedXR)
        (fun t (ω : A) => δ t ω) (fun ω : A => capLife (γ ω))

/-- **R.5 up to a lattice phase together with Aux. lemma 122's retained hypothesis, for the same phase**, on one
two-seed pocket test in the chart `c`. -/
def TwoSeedPhaseMeansAt {Ω : Type*} [MeasurableSpace Ω] (κ rL rR : ℝ) (P : Measure Ω) (A : Set Ω)
    (γ : Ω → ℝ → ℂ) (c : Ω → Chart) (h₀ : Ω → DistOn upperHalfPlaneOpens) (u : ℂ → ℝ) : Prop :=
  ∃ (a : ℝ) (δ : ℝ≥0 → Ω → ℝ),
    (∀ q : ℝ≥0, PocketStopSide.PocketStopPhaseSideLimit κ (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) P A γ
      (fun _ => LP.twoSeedXL) (fun _ => LP.twoSeedXR) c a h₀ u (activeCompl A γ c q) (δ q) q) ∧
    TwoSeedPhaseMeans κ rL rR P A γ δ

/-- **Constancy and the phase selection from Aux. lemma 122** (follow-up 5 §3.2, specification pp. 389–391): with seed
weights in `(−2, κ − 6)`, a measurable test event of positive probability on which the traversal is a driven curve
with points of `ℍ` of arbitrarily large modulus, R.5 up to a lattice phase and Aux. lemma 122's retained hypothesis
for that phase give the three parts of `Hsd.TwoSeedPhaseSideAt` for the same offset and phase: the phase vanishes
almost surely on the whole positive lifetime (`ae_phase_eq_zero_of_hasPhaseMeans` on the subtype), so it is continuous
there and zero at a positive time whenever the lifetime is positive. -/
theorem twoSeedPhaseSideAt_of_means {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {κ rL rR : ℝ} (hκ : 4 < κ) (hrL : -2 < rL) (hrL' : rL < κ - 6) (hrR : -2 < rR) (hrR' : rR < κ - 6)
    {A : Set Ω} (hA : MeasurableSet A) (hPA : P A ≠ 0) {γ : Ω → ℝ → ℂ}
    (hγ : ∀ ω ∈ A, IsDrivenCurve (γ ω) ∧ ∀ M : ℝ, ∃ u, 0 ≤ u ∧ γ ω u ∈ H ∧ M < ‖γ ω u‖)
    {c : Ω → Chart} {h₀ : Ω → DistOn upperHalfPlaneOpens} {u : ℂ → ℝ}
    (h : TwoSeedPhaseMeansAt κ rL rR P A γ c h₀ u) : TwoSeedPhaseSideAt κ rL rR P A γ c h₀ u := by
  obtain ⟨a, δ, hph, hlat, 𝓕, h𝓕, hpre, hM⟩ := h
  have := h𝓕
  have : IsProbabilityMeasure (condSub P A) := isProbabilityMeasure_condSub hA hPA
  have hk : 2 * (κ / 2 - 2) - 2 = κ - 6 := by ring
  have hzero := ae_phase_eq_zero_of_hasPhaseMeans (P := condSub P A) (𝓕 := 𝓕) (γ := fun ω : A => γ ω)
    (ρL := fun _ : Fin 1 => rL) (ρR := fun _ : Fin 1 => rR) (xL := fun _ => LP.twoSeedXL)
    (xR := fun _ => LP.twoSeedXR) (d := fun t (ω : A) => δ t ω) hκ hrL (by rw [hk]; exact hrL') hrR
    (by rw [hk]; exact hrR') (fun ω => (hγ ω ω.2).1) (fun ω => (hγ ω ω.2).2) hpre measurable_const
    measurable_const (fun _ => rfl) (fun _ => rfl) (fun _ i => i.elim0) (fun _ j => j.elim0)
    (fun _ => fun _ _ _ => le_rfl) (fun _ => fun _ _ _ => le_rfl) (fun t ω ht htT => hlat ω ω.2 t ht htT) hM
  have hae : ∀ᵐ ω ∂P, ω ∈ A →
      ∀ t : ℝ≥0, 0 < t → (t : WithTop ℝ≥0) < capLife (γ ω) → δ t ω = 0 :=
    ae_of_ae_condSub (p := fun ω => ∀ t : ℝ≥0, 0 < t → (t : WithTop ℝ≥0) < capLife (γ ω) → δ t ω = 0) hA hzero
  refine ⟨a, δ, hph, ?_, ?_⟩
  · filter_upwards [hae] with ω hω hωA
    exact (continuousOn_const (c := (0 : ℝ))).congr fun t ht => hω hωA t ht.1 ht.2
  · filter_upwards [hae] with ω hω hωA hpos
    obtain ⟨r, hr0, hrT⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hpos
    have hr0' : 0 < r := ENNReal.coe_pos.1 hr0
    exact ⟨r, hr0', hrT, hω hωA r hr0' hrT⟩

end Test

/-! ### Every test of a walls' event -/

section Input

/-- R.5 up to a lattice phase and Aux. lemma 122's retained hypothesis on every test of a walls' event `G` (bounded
change pocket), in a walls-measurable chart branch. -/
def TwoSeedPhaseMeansInput {Ω : Type*} (κ rL rR : ℝ) (𝓦 : MeasurableSpace Ω) [MeasurableSpace Ω]
    (P : Measure Ω) (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (η : Ω → ℝ → ℂ) (G : Set Ω)
    (h₀ : Ω → DistOn upperHalfPlaneOpens) (u : ℂ → ℝ) : Prop :=
  ∀ A : Set Ω, MeasurableSet[𝓦] A → A ⊆ G → 0 < P A → ∀ ψ : Ω → ℂ → ℂ,
    (∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω)) → @IsPointMeasurable Ω 𝓦 R L r G ψ →
      ∃ n : Ω → ℤ, Measurable[𝓦] n ∧ TwoSeedPhaseMeansAt κ rL rR P A (travAll R L r η ψ)
        (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) h₀ u

/-- R.5 up to a lattice phase and Aux. lemma 122's retained hypothesis on every test of a walls' event `G` (pocket
opening at the flow seed), in a walls-measurable chart branch. -/
def TwoSeedPhaseMeansInputInf {Ω : Type*} (κ rL rR : ℝ) (𝓦 : MeasurableSpace Ω) [MeasurableSpace Ω]
    (P : Measure Ω) (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (η : Ω → ℝ → ℂ) (G : Set Ω)
    (h₀ : Ω → DistOn upperHalfPlaneOpens) (u : ℂ → ℝ) : Prop :=
  ∀ A : Set Ω, MeasurableSet[𝓦] A → A ⊆ G → 0 < P A → ∀ ψ : Ω → ℂ → ℂ,
    (∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω)) → @IsPointMeasurableInf Ω 𝓦 R L r G ψ →
      ∃ n : Ω → ℤ, Measurable[𝓦] n ∧ TwoSeedPhaseMeansAt κ rL rR P A (travAllInf R L r η ψ)
        (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) h₀ u

/-- **The three parts of the two-seed side limits in the bounded change pocket from R.5 up to phase and Aux. lemma
122's retained hypothesis** (the same branch on every test; the traversal is driven, with points of large modulus, by
the counterflow configuration). -/
theorem twoSeedPhaseSideInput_of_means {Ω : Type*} {κ rL rR : ℝ} (hκ : 4 < κ) (hrL : -2 < rL)
    (hrL' : rL < κ - 6) (hrR : -2 < rR) (hrR' : rR < κ - 6) {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    (h𝓦 : 𝓦 ≤ mΩ) {P : Measure Ω} [IsProbabilityMeasure P] {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0}
    {η : Ω → ℝ → ℂ} {G : Set Ω} {h₀ : Ω → DistOn upperHalfPlaneOpens} {u : ℂ → ℝ} {W : Ω → ℝ → ℝ}
    (hcfg : ∀ ω ∈ G, IsCfPocketConfig (R ω) (L ω) r (W ω) (η ω))
    (h : TwoSeedPhaseMeansInput κ rL rR 𝓦 P R L r η G h₀ u) :
    TwoSeedPhaseSideInput κ rL rR 𝓦 P R L r η G h₀ u := by
  intro A hA hAG hPA ψ hJ hPt
  obtain ⟨n, hn, hat⟩ := h A hA hAG hPA ψ hJ hPt
  exact ⟨n, hn, twoSeedPhaseSideAt_of_means hκ hrL hrL' hrR hrR' (h𝓦 _ hA) hPA.ne'
    (fun ω hω => (hcfg ω (hAG hω)).isDrivenCurve (hJ ω hω)) hat⟩

/-- **The three parts of the two-seed side limits in the pocket opening at the flow seed from R.5 up to phase and
Aux. lemma 122's retained hypothesis.** -/
theorem twoSeedPhaseSideInputInf_of_means {Ω : Type*} {κ rL rR : ℝ} (hκ : 4 < κ) (hrL : -2 < rL)
    (hrL' : rL < κ - 6) (hrR : -2 < rR) (hrR' : rR < κ - 6) {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    (h𝓦 : 𝓦 ≤ mΩ) {P : Measure Ω} [IsProbabilityMeasure P] {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0}
    {η : Ω → ℝ → ℂ} {G : Set Ω} {h₀ : Ω → DistOn upperHalfPlaneOpens} {u : ℂ → ℝ} {W : Ω → ℝ → ℝ}
    (hcfg : ∀ ω ∈ G, IsCfPocketConfigInf (R ω) (L ω) r (W ω) (η ω))
    (h : TwoSeedPhaseMeansInputInf κ rL rR 𝓦 P R L r η G h₀ u) :
    TwoSeedPhaseSideInputInf κ rL rR 𝓦 P R L r η G h₀ u := by
  intro A hA hAG hPA ψ hJ hPt
  obtain ⟨n, hn, hat⟩ := h A hA hAG hPA ψ hJ hPt
  exact ⟨n, hn, twoSeedPhaseSideAt_of_means hκ hrL hrL' hrR hrR' (h𝓦 _ hA) hPA.ne'
    (fun ω hω => (hcfg ω (hAG hω)).isDrivenCurve (hJ ω hω)) hat⟩

end Input

/-! ### Every R.7 configuration -/

section Remaining

/-- **R.5 up to a lattice phase with Aux. lemma 122's retained hypothesis on every R.7 configuration** (heights `c`,
`c′`; named input replacing `Hsd.R7PhaseSideRemaining`): the premises are exactly those of
`Hsd.R7PhaseSideRemaining` (hence of `R7ExtremalSideDet.side`); the conclusion asks, on every pocket test, for R.5's
phase word (1) and, for the same phase, the retained local-martingale means of Aux. lemma 122 (`TwoSeedPhaseMeans`),
instead of the constancy (2) and the phase selection (3). -/
def R7PhaseMeansRemaining (k rL rR c c' : ℝ) : Prop :=
  ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistOn upperHalfPlaneOpens) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞)
    (αR βR βL αL : Ω → ℝ≥0 → ℂ) (ζαR ζβR ζβL ζαL : Ω → ℝ≥0∞),
    IsR7OuterConfig k rL rR c c' P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL →
    ∀ (b' : ℝ → ℝ) (J' : Finset ℝ) (h' h'' : Ω → DistOn upperHalfPlaneOpens) (𝓕 : Filtration ℝ≥0 mΩ)
      (VL : Fin (flowLineNL b' J' 0) → ℝ≥0 → Ω → ℝ) (VR : Fin (flowLineNR b' J' 0) → ℝ≥0 → Ω → ℝ)
      (B : ℝ≥0 → Ω → ℝ), IsCfDecomp k P h W' ζ' b' J' h' h'' 𝓕 VL VR B →
    ∀ u₀' : ℂ → ℝ, IsBoundedHarmonicExtension (forceBoundaryData k (flowLineRhoL k b' J' 0 0)
      (flowLineRhoR k b' J' 0 0) (flowLineXL b' J' 0) (flowLineXR b' J' 0))
      (forceJumpSet (flowLineXL b' J' 0) (flowLineXR b' J' 0)) u₀' →
    ∀ (R L : Ω → ℝ≥0 → ℂ) (η : Ω → ℝ → ℂ), IsR7Versions P W' αR αL R L η →
    ∀ q : ℚ, 0 < q → ∀ G : Set Ω, MeasurableSet[wallsSigma P R L] G → 0 < P G →
      (∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) (StripSys.rt q)) →
      (∀ ω ∈ G, ζ' ω = ⊤) →
      (∀ ω ∈ G, 0 < rightLo (R ω) (L ω) (StripSys.rt q) →
        IsCfPocketConfig (R ω) (L ω) (StripSys.rt q) (fun s : ℝ => W' s.toNNReal ω) (η ω)) →
      (∀ ω ∈ G, rightLo (R ω) (L ω) (StripSys.rt q) = 0 →
        IsCfPocketConfigInf (R ω) (L ω) (StripSys.rt q) (fun s : ℝ => W' s.toNNReal ω) (η ω)) →
      TwoSeedPhaseMeansInput k rL rR (wallsSigma P R L) P R L (StripSys.rt q) η
          {ω | ω ∈ G ∧ 0 < rightLo (R ω) (L ω) (StripSys.rt q)} (centredField h'' u₀') u₀' ∧
        TwoSeedPhaseMeansInputInf k rL rR (wallsSigma P R L) P R L (StripSys.rt q) η
          {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (L ω) (StripSys.rt q)} (centredField h'' u₀') u₀'

/-- **The three parts of the side limits on every R.7 configuration from R.5 up to phase and Aux. lemma 122's
retained hypothesis**, for seed weights in Aux. lemma 122's range `(−2, k − 6)`: the walls' σ-algebra lies in the
ambient one (the walls are measurable versions), and on each test `twoSeedPhaseSideAt_of_means`. -/
theorem r7PhaseSideRemaining_of_means {k rL rR c c' : ℝ} (hk4 : 4 < k) (hrL : -2 < rL) (hrL' : rL < k - 6)
    (hrR : -2 < rR) (hrR' : rR < k - 6) (hmeans : R7PhaseMeansRemaining.{u} k rL rR c c') :
    R7PhaseSideRemaining.{u} k rL rR c c' := by
  intro Ω mΩ hSB P hP h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg b' J' h' h'' 𝓕 VL VR B hD u₀' hu₀' R L η hV
    q hq G hGm hPG hconf hζG hcfgP hcfgI
  obtain ⟨hs, hsI⟩ := hmeans P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg b' J' h' h'' 𝓕 VL VR B hD u₀' hu₀' R L η
    hV q hq G hGm hPG hconf hζG hcfgP hcfgI
  have h𝓦 : wallsSigma P R L ≤ mΩ := wallsSigma_le hV.R_meas hV.L_meas
  refine ⟨twoSeedPhaseSideInput_of_means (W := fun ω (s : ℝ) => W' s.toNNReal ω) hk4 hrL hrL' hrR hrR' h𝓦
    ?_ hs, twoSeedPhaseSideInputInf_of_means (W := fun ω (s : ℝ) => W' s.toNNReal ω) hk4 hrL hrL' hrR hrR' h𝓦
    ?_ hsI⟩
  · exact fun ω hω => hcfgP ω hω.1 hω.2
  · exact fun ω hω => hcfgI ω hω.1 (le_antisymm (not_lt.1 hω.2) ((hconf ω hω.1).changeCorner_props.1.1))

/-- The extremal seed weights of `hsd` lie in Aux. lemma 122's range: `max r_L r_R = k/2 − 4 < k − 6` for `k > 4`. -/
theorem lt_sub_six_of_max_eq {k rL rR : ℝ} (hk4 : 4 < k) (hmax : max rL rR = k / 2 - 4) :
    rL < k - 6 ∧ rR < k - 6 := by
  have h1 := le_max_left rL rR
  have h2 := le_max_right rL rR
  rw [hmax] at h1 h2
  constructor <;> linarith

/-- **Theorem 1.2's R.7 reference with the side field from R.5 up to phase and Aux. lemma 122's retained
hypothesis**: `Hsd.r7ReferenceStatement_late_hsd` with `R7PhaseSideRemaining` replaced by `R7PhaseMeansRemaining` at
the heights `c = πχ(16/k)`, `c′ = 0`, for the extremal pairs (`max r_L r_R = k/2 − 4`, both weights `> −2`). The other
inputs are exactly those of `Hsd.r7ReferenceStatement_late_hsd`. -/
theorem r7ReferenceStatement_late_means
    (hRect : ∀ κ, ZhanGT4.A1Core.A1DualCouplingG3RectStatement κ)
    (hRectEight : ∀ κ, ZhanGT4.A1Core.A1DualCouplingEightRectStatement κ)
    (Ref0 : ℝ → (ℝ → ℝ) → Finset ℝ → Set ℝ → Prop)
    (hCover0 : Sec5.Aux61R2.RefClockFibreCoverOn.{0}
      (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂) Ref0)
    (hAvoid0 : ∀ κ b J I, Ref0 κ b J I → Sec5.Aux61Win.IsAvoidingRef.{0} κ b J I)
    (hQ0 : Sec5.FrameQ.QScheduleFirstHitStatement.{0})
    (hlaws : Fig51CandLawsStatement
      (late_theorem12ParamCond44Statement (late_coreG3 hRect) (late_coreEight hRectEight)))
    (hmeans : ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → max rL rR = k / 2 - 4 →
      R7PhaseMeansRemaining.{0} k rL rR (π * chiC (16 / k)) 0)
    (hOuter : ∀ κ : ℝ, 4 < κ → ∀ rL rR : ℝ, -2 < rL → -2 < rR →
      κ / 2 - 4 < max rL rR → OuterPocketCompletion.{0} κ rL rR) :
    R7.R7ReferenceStatement.{0} :=
  r7ReferenceStatement_late_hsd hRect hRectEight Ref0 hCover0 hAvoid0 hQ0 hlaws
    (fun k hk4 rL rR hL hR hmax => r7PhaseSideRemaining_of_means hk4 hL (lt_sub_six_of_max_eq hk4 hmax).1 hR
      (lt_sub_six_of_max_eq hk4 hmax).2 (hmeans k hk4 rL rR hL hR hmax)) hOuter

end Remaining

end InteractingSLE.Sec7.PhaseSide
