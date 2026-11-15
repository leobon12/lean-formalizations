/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.HsdDet
import InteractingSLE.Spec.Sec7.PocketStopSideLim

/-!
# Theorem R.7's `hsd`: the two-seed side limits in the source's three parts, and the assembly

Packet PROVE-HSD. The side field of `R7Leaves.R7ExtremalSideDet` asks, on every walls' event of an R.7 configuration
and for every Jordan coordinate of the two-seed pocket, for the canonical side limits (Corollary 3.2 of Astra's
follow-up 5, R73) in some branch `n` of the pocket chart. Following follow-up 5 §3.1–§3.2 (and the specification's
Lemma R.5, Aux. lemma 122) they split into

1. **R.5 up to a lattice phase**: the conditional mean in the pocket chart (a walls-measurable branch `n`) has the
   boundary word (3.1) — the canonical heights `−Λ`, `+Λ` on the exposed sides raised by one common `δ_t ∈ 2πχℤ`
   (`PocketStopSide.PocketStopPhaseSideLimit`, which also records the lattice condition);
2. **constancy** (§3.2): `δ` is continuous on the positive relative lifetime (the bounded-sector quotient (3.2));
3. **phase selection**: `δ` vanishes at one positive time (Aux. lemma 122; for the extremal pairs of `hsd` both seed
   weights lie in `(−2, k − 6)`, since `k/2 − 4 < k − 6` for `k > 4`, which is the range of (3.3)).

Given 1–3, the landed `PocketStopSide.pocketStopSideLimit_of_phase_common_anchor` (lattice-valued continuous phase is
constant; at time `0` the exposed interval is empty) gives the side limits for every `q`, in the same branch `n`.

* `TwoSeedPhaseSideAt`, `TwoSeedPhaseSideInput`, `TwoSeedPhaseSideInputInf`: the three parts for one pocket test, and
  on every test of a walls' event (bounded pocket / pocket opening at the flow seed);
* **`twoSeedSideInput_of_phase`**, **`twoSeedSideInputInf_of_phase`**: `RefWire.TwoSeedSideInput(Inf)` from them;
* `R7PhaseSideRemaining`: the three parts on every R.7 configuration (the named input replacing `hsd.side`);
  `R7SideRemaining`: `hsd.side` itself on every configuration; `r7SideRemaining_of_phase`;
* **`r7ExtremalSideDetRemaining_of_side`**, **`r7ExtremalSideDetRemaining_of_phase`**: `hsd` from the side input and
  `Fig51CandLawsStatement`;
* **`r7ReferenceStatement_late_hsd`** (phase form), **`r7ReferenceStatement_late_side`** (original side form):
  `StripSafe.r7ReferenceStatement_late_sideDet_safe` with `hsd` replaced by these two named inputs (and Theorem 1.2's
  existing binder `hQ0`).

Part 1 is what the R73 collector produces from raw reference laws, the lattice and the collar
(`PocketStopSide.pocketStopPhaseSideLimit_of_raw_reference_germs`); part 2 from the mean probes
(`PocketStopSide.ae_continuous_phase_of_mean_probes`). R48: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Function
open LQGMetric (DistOn)
open QuantumZipper (H Hbar chiC)
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Sec7.Hsd

open WholeField R7Outer R7Leaves RefWire Wire
open WangWu Lemma71C Lemma71I PocketCoord PocketJordan PocketMarks PocketWordAssembly PocketSeedOpen PocketStopField
  PocketStopWallsFin PocketStopWalls PocketCoupling StripPocketConfig PocketWordPerQ PocketStop R7Aux131 R7Pocket

/-! ### The side limits from the three parts -/

section Side

/-- **R.5 up to a lattice phase, constancy and the phase selection for one two-seed pocket test**: for the traversal
`γ` in the chart `c` there are an offset `a` and a phase `δ` with (1) the phase boundary word (3.1) at every relative
time (with `δ_q ∈ 2πχℤ` on the live event), (2) `δ` continuous on the positive lifetime, (3) `δ` zero at some positive
time. -/
def TwoSeedPhaseSideAt {Ω : Type*} [MeasurableSpace Ω] (κ rL rR : ℝ) (P : Measure Ω) (A : Set Ω) (γ : Ω → ℝ → ℂ)
    (c : Ω → Chart) (h₀ : Ω → DistOn upperHalfPlaneOpens) (u : ℂ → ℝ) : Prop :=
  ∃ (a : ℝ) (δ : ℝ≥0 → Ω → ℝ),
    (∀ q : ℝ≥0, PocketStopSide.PocketStopPhaseSideLimit κ (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) P A γ
      (fun _ => LP.twoSeedXL) (fun _ => LP.twoSeedXR) c a h₀ u (activeCompl A γ c q) (δ q) q) ∧
    (∀ᵐ ω ∂P, ω ∈ A →
      ContinuousOn (fun t => δ t ω) {t : ℝ≥0 | 0 < t ∧ (t : ℝ≥0∞) < capLife (γ ω)}) ∧
    (∀ᵐ ω ∂P, ω ∈ A → 0 < capLife (γ ω) →
      ∃ s : ℝ≥0, 0 < s ∧ (s : ℝ≥0∞) < capLife (γ ω) ∧ δ s ω = 0)

/-- The three parts on every test of a walls' event `G` (bounded change pocket, in a walls-measurable chart branch). -/
def TwoSeedPhaseSideInput {Ω : Type*} (κ rL rR : ℝ) (𝓦 : MeasurableSpace Ω) [MeasurableSpace Ω] (P : Measure Ω)
    (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (η : Ω → ℝ → ℂ) (G : Set Ω) (h₀ : Ω → DistOn upperHalfPlaneOpens)
    (u : ℂ → ℝ) : Prop :=
  ∀ A : Set Ω, MeasurableSet[𝓦] A → A ⊆ G → 0 < P A → ∀ ψ : Ω → ℂ → ℂ,
    (∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω)) → @IsPointMeasurable Ω 𝓦 R L r G ψ →
      ∃ n : Ω → ℤ, Measurable[𝓦] n ∧ TwoSeedPhaseSideAt κ rL rR P A (travAll R L r η ψ)
        (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) h₀ u

/-- The three parts on every test of a walls' event `G` (pocket opening at the flow seed, walls-measurable branch). -/
def TwoSeedPhaseSideInputInf {Ω : Type*} (κ rL rR : ℝ) (𝓦 : MeasurableSpace Ω) [MeasurableSpace Ω]
    (P : Measure Ω) (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (η : Ω → ℝ → ℂ) (G : Set Ω)
    (h₀ : Ω → DistOn upperHalfPlaneOpens) (u : ℂ → ℝ) : Prop :=
  ∀ A : Set Ω, MeasurableSet[𝓦] A → A ⊆ G → 0 < P A → ∀ ψ : Ω → ℂ → ℂ,
    (∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω)) → @IsPointMeasurableInf Ω 𝓦 R L r G ψ →
      ∃ n : Ω → ℤ, Measurable[𝓦] n ∧ TwoSeedPhaseSideAt κ rL rR P A (travAllInf R L r η ψ)
        (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) h₀ u

/-- **The two-seed side limits in the bounded change pocket from the three parts** (the same branch `n`):
`pocketStopSideLimit_of_phase_common_anchor` on each test; the traversal is driven by the counterflow configuration. -/
theorem twoSeedSideInput_of_phase {Ω : Type*} {κ rL rR : ℝ} (hκ : 4 < κ) {𝓦 : MeasurableSpace Ω}
    [MeasurableSpace Ω] {P : Measure Ω}
    {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {η : Ω → ℝ → ℂ} {G : Set Ω} {h₀ : Ω → DistOn upperHalfPlaneOpens}
    {u : ℂ → ℝ} {W : Ω → ℝ → ℝ} (hcfg : ∀ ω ∈ G, IsCfPocketConfig (R ω) (L ω) r (W ω) (η ω))
    (h : TwoSeedPhaseSideInput κ rL rR 𝓦 P R L r η G h₀ u) :
    TwoSeedSideInput κ rL rR 𝓦 P R L r η G h₀ u := by
  intro A hA hAG hPA ψ hJ hPt
  obtain ⟨n, hn, a, δ, hph, hcont, hanc⟩ := h A hA hAG hPA ψ hJ hPt
  refine ⟨n, a, hn, ?_⟩
  exact PocketStopSide.pocketStopSideLimit_of_phase_common_anchor hκ
    (fun ω hω => ((hcfg ω (hAG hω)).isDrivenCurve (hJ ω hω)).1) (fun _ _ => rfl) (fun _ _ => rfl) hph hcont hanc

/-- **The two-seed side limits in the pocket opening at the flow seed from the three parts** (the same branch). -/
theorem twoSeedSideInputInf_of_phase {Ω : Type*} {κ rL rR : ℝ} (hκ : 4 < κ) {𝓦 : MeasurableSpace Ω}
    [MeasurableSpace Ω] {P : Measure Ω}
    {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {η : Ω → ℝ → ℂ} {G : Set Ω} {h₀ : Ω → DistOn upperHalfPlaneOpens}
    {u : ℂ → ℝ} {W : Ω → ℝ → ℝ} (hcfg : ∀ ω ∈ G, IsCfPocketConfigInf (R ω) (L ω) r (W ω) (η ω))
    (h : TwoSeedPhaseSideInputInf κ rL rR 𝓦 P R L r η G h₀ u) :
    TwoSeedSideInputInf κ rL rR 𝓦 P R L r η G h₀ u := by
  intro A hA hAG hPA ψ hJ hPt
  obtain ⟨n, hn, a, δ, hph, hcont, hanc⟩ := h A hA hAG hPA ψ hJ hPt
  refine ⟨n, a, hn, ?_⟩
  exact PocketStopSide.pocketStopSideLimit_of_phase_common_anchor hκ
    (fun ω hω => ((hcfg ω (hAG hω)).isDrivenCurve (hJ ω hω)).1) (fun _ _ => rfl) (fun _ _ => rfl) hph hcont hanc

end Side

/-! ### `hsd` on every R.7 configuration -/

section Remaining

/-- **The three parts of the two-seed side limits on every R.7 configuration** (heights `c`, `c′`; named input
replacing `R7ExtremalSideDet.side`): for every configuration, decomposition, force-word mean `u₀′` and versions
`R`, `L`, `η`, on every walls' event `G` of the change configuration at a rational time with infinite counterflow
lifetime, the R.5 phase word, its constancy and the Aux. 122 phase selection hold on every pocket test, for the field
`centredField h″ u₀′` and harmonic part `u₀′` — the premises are exactly those of `R7ExtremalSideDet.side`. -/
def R7PhaseSideRemaining (k rL rR c c' : ℝ) : Prop :=
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
      TwoSeedPhaseSideInput k rL rR (wallsSigma P R L) P R L (StripSys.rt q) η
          {ω | ω ∈ G ∧ 0 < rightLo (R ω) (L ω) (StripSys.rt q)} (centredField h'' u₀') u₀' ∧
        TwoSeedPhaseSideInputInf k rL rR (wallsSigma P R L) P R L (StripSys.rt q) η
          {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (L ω) (StripSys.rt q)} (centredField h'' u₀') u₀'

/-- **The side field of `hsd` on every R.7 configuration** (heights `c`, `c′`), in its original form: the `side` field
of `R7Leaves.R7ExtremalSideDet` quantified as in `R7ExtremalSideDetRemaining`. -/
def R7SideRemaining (k rL rR c c' : ℝ) : Prop :=
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
      TwoSeedSideInput k rL rR (wallsSigma P R L) P R L (StripSys.rt q) η
          {ω | ω ∈ G ∧ 0 < rightLo (R ω) (L ω) (StripSys.rt q)} (centredField h'' u₀') u₀' ∧
        TwoSeedSideInputInf k rL rR (wallsSigma P R L) P R L (StripSys.rt q) η
          {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (L ω) (StripSys.rt q)} (centredField h'' u₀') u₀'

/-- **The side field from the three parts** on every R.7 configuration (`twoSeedSideInput(Inf)_of_phase`; the
traversals are driven by the counterflow configurations of the premises). -/
theorem r7SideRemaining_of_phase {k rL rR c c' : ℝ} (hk4 : 4 < k)
    (hside : R7PhaseSideRemaining.{u} k rL rR c c') :
    R7SideRemaining.{u} k rL rR c c' := by
  intro Ω mΩ hSB P hP h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg b' J' h' h'' 𝓕 VL VR B hD u₀' hu₀' R L η hV
    q hq G hGm hPG hconf hζG hcfgP hcfgI
  obtain ⟨hs, hsI⟩ := hside P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg b' J' h' h'' 𝓕 VL VR B hD u₀' hu₀' R L η hV
    q hq G hGm hPG hconf hζG hcfgP hcfgI
  refine ⟨twoSeedSideInput_of_phase (W := fun ω (s : ℝ) => W' s.toNNReal ω) hk4 ?_ hs,
    twoSeedSideInputInf_of_phase (W := fun ω (s : ℝ) => W' s.toNNReal ω) hk4 ?_ hsI⟩
  · exact fun ω hω => hcfgP ω hω.1 hω.2
  · exact fun ω hω => hcfgI ω hω.1 (le_antisymm (not_lt.1 hω.2) ((hconf ω hω.1).changeCorner_props.1.1))

/-- **`hsd` on every R.7 configuration from the side field and Proposition 5.9's per-candidate laws**: the
determination field is `r7_det`. -/
theorem r7ExtremalSideDetRemaining_of_side (h44 : AdmCode.Theorem12ParamCond44Statement.{0})
    (hA : Sec5.PartAInputsSixteenDivOfClearance) (hFH : Sec5.StripRevVisit.StagedPrefixFirstHitStatement.{0})
    (hlaws : Fig51CandLawsStatement h44) {k rL rR c c' : ℝ} (hk4 : 4 < k) (hc : 0 ≤ c) (hc' : 0 ≤ c')
    (hside : R7SideRemaining.{0} k rL rR c c') : R7ExtremalSideDetRemaining.{0} k rL rR c c' := by
  intro Ω mΩ hSB P hP h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg b' J' h' h'' 𝓕 VL VR B hD u₀' hu₀' R L η hV
  exact ⟨hside P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg b' J' h' h'' 𝓕 VL VR B hD u₀' hu₀' R L η hV,
    r7_det h44 hA hFH hlaws hk4 hc hc' hcfg.gff hcfg.counterflow hD hV.η_trace⟩

/-- **`hsd` on every R.7 configuration from the two named inputs**: the side field from `R7PhaseSideRemaining`
(`r7SideRemaining_of_phase`), the determination field from Proposition 5.9's per-candidate laws (`r7_det`). -/
theorem r7ExtremalSideDetRemaining_of_phase (h44 : AdmCode.Theorem12ParamCond44Statement.{0})
    (hA : Sec5.PartAInputsSixteenDivOfClearance) (hFH : Sec5.StripRevVisit.StagedPrefixFirstHitStatement.{0})
    (hlaws : Fig51CandLawsStatement h44) {k rL rR c c' : ℝ} (hk4 : 4 < k) (hc : 0 ≤ c) (hc' : 0 ≤ c')
    (hside : R7PhaseSideRemaining.{0} k rL rR c c') : R7ExtremalSideDetRemaining.{0} k rL rR c c' :=
  r7ExtremalSideDetRemaining_of_side h44 hA hFH hlaws hk4 hc hc' (r7SideRemaining_of_phase hk4 hside)

/-- **Theorem 1.2's R.7 reference with `hsd`'s determination discharged**:
`StripSafe.r7ReferenceStatement_late_sideDet_safe` with `hsd` replaced by Proposition 5.9's per-candidate laws
(`Fig51CandLawsStatement`, at the late wiring's `h44`) and
the side field in its original form (`R7SideRemaining` at `c = πχ(16/k)`, `c′ = 0`); `hQ0` is Theorem 1.2's existing
binder. -/
theorem r7ReferenceStatement_late_side
    (hRect : ∀ κ, ZhanGT4.A1Core.A1DualCouplingG3RectStatement κ)
    (hRectEight : ∀ κ, ZhanGT4.A1Core.A1DualCouplingEightRectStatement κ)
    (Ref0 : ℝ → (ℝ → ℝ) → Finset ℝ → Set ℝ → Prop)
    (hCover0 : Sec5.Aux61R2.RefClockFibreCoverOn.{0}
      (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂) Ref0)
    (hAvoid0 : ∀ κ b J I, Ref0 κ b J I → Sec5.Aux61Win.IsAvoidingRef.{0} κ b J I)
    (hQ0 : Sec5.FrameQ.QScheduleFirstHitStatement.{0})
    (hlaws : Fig51CandLawsStatement
      (late_theorem12ParamCond44Statement (late_coreG3 hRect) (late_coreEight hRectEight)))
    (hside : ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → max rL rR = k / 2 - 4 →
      R7SideRemaining.{0} k rL rR (π * chiC (16 / k)) 0)
    (hOuter : ∀ κ : ℝ, 4 < κ → ∀ rL rR : ℝ, -2 < rL → -2 < rR →
      κ / 2 - 4 < max rL rR → OuterPocketCompletion.{0} κ rL rR) :
    R7.R7ReferenceStatement.{0} := by
  have hA := late_partAInputs (late_coreG3 hRect) (late_coreEight hRectEight)
  have hFH := Sec5.FrameQ.stagedPrefixFirstHitStatement_of_qScheduleFirstHit hA hQ0
  refine StripSafe.r7ReferenceStatement_late_sideDet_safe hRect hRectEight Ref0 hCover0 hAvoid0
    (fun k hk4 rL rR hL hR hmax => ?_) hOuter
  have hκ : 0 < 16 / k := R7.sixteen_div_pos (by linarith)
  have hκ4 : 16 / k < 4 := R7.sixteen_div_lt_four hk4
  exact @r7ExtremalSideDetRemaining_of_side _ hA hFH hlaws k rL rR (π * chiC (16 / k)) 0 hk4
    (mul_nonneg Real.pi_pos.le (Sec4.chiC_pos hκ hκ4).le) le_rfl (hside k hk4 rL rR hL hR hmax)

/-- **Theorem 1.2's R.7 reference without `hsd`**: `StripSafe.r7ReferenceStatement_late_sideDet_safe` with `hsd`
replaced by Proposition 5.9's per-candidate laws (`Fig51CandLawsStatement`, at the late wiring's `h44`) and the three
parts of the extremal side limits (`R7PhaseSideRemaining` at the heights `c = πχ(16/k)`, `c′ = 0`); `hQ0` is Theorem
1.2's existing binder (the staged prefix first exits, `FrameQ.stagedPrefixFirstHitStatement_of_qScheduleFirstHit`). -/
theorem r7ReferenceStatement_late_hsd
    (hRect : ∀ κ, ZhanGT4.A1Core.A1DualCouplingG3RectStatement κ)
    (hRectEight : ∀ κ, ZhanGT4.A1Core.A1DualCouplingEightRectStatement κ)
    (Ref0 : ℝ → (ℝ → ℝ) → Finset ℝ → Set ℝ → Prop)
    (hCover0 : Sec5.Aux61R2.RefClockFibreCoverOn.{0}
      (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂) Ref0)
    (hAvoid0 : ∀ κ b J I, Ref0 κ b J I → Sec5.Aux61Win.IsAvoidingRef.{0} κ b J I)
    (hQ0 : Sec5.FrameQ.QScheduleFirstHitStatement.{0})
    (hlaws : Fig51CandLawsStatement
      (late_theorem12ParamCond44Statement (late_coreG3 hRect) (late_coreEight hRectEight)))
    (hside : ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → max rL rR = k / 2 - 4 →
      R7PhaseSideRemaining.{0} k rL rR (π * chiC (16 / k)) 0)
    (hOuter : ∀ κ : ℝ, 4 < κ → ∀ rL rR : ℝ, -2 < rL → -2 < rR →
      κ / 2 - 4 < max rL rR → OuterPocketCompletion.{0} κ rL rR) :
    R7.R7ReferenceStatement.{0} := by
  have hA := late_partAInputs (late_coreG3 hRect) (late_coreEight hRectEight)
  have hFH := Sec5.FrameQ.stagedPrefixFirstHitStatement_of_qScheduleFirstHit hA hQ0
  refine StripSafe.r7ReferenceStatement_late_sideDet_safe hRect hRectEight Ref0 hCover0 hAvoid0
    (fun k hk4 rL rR hL hR hmax => ?_) hOuter
  have hκ : 0 < 16 / k := R7.sixteen_div_pos (by linarith)
  have hκ4 : 16 / k < 4 := R7.sixteen_div_lt_four hk4
  exact @r7ExtremalSideDetRemaining_of_phase _ hA hFH hlaws k rL rR (π * chiC (16 / k)) 0 hk4
    (mul_nonneg Real.pi_pos.le (Sec4.chiC_pos hκ hκ4).le) le_rfl (hside k hk4 rL rR hL hR hmax)

end Remaining

end InteractingSLE.Sec7.Hsd
