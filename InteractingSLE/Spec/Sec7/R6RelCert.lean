/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R6NestRel
import InteractingSLE.Spec.Sec7.R6NestTransfer

/-!
# R.6 at deterministic relative times from a phase-free pathwise certificate

PROVE-R6-NESTREL. `R6Nest.TwoSeedNestRelInput` (the zero outer phase at a rational relative time `q` on the event
that the physical tip lies in a nested candidate pocket) asks for a conclusion about an arbitrary phase word `δ` of
the outer pocket. This file removes the phase word from what remains to be proved: the outer word at `q` is the
antecedent itself, and Lemma R.6 with independent offsets (`R6Nest.phase_eq_of_shared_current_pocket_words`) turns
it into `δ_q = 0` as soon as the actual outer local-set mean comes with an **R.6 certificate** (`R6Cert`) at that
time — data that do not mention `δ`:

* an inner current chart (the current chart of a nested pocket at the physical time of relative capacity `q`, e.g.
  the inner pocket `U` of the mixed case, or the intermediate mixed pocket `V` for two outer arms), the transition
  geometry (inclusion of current domains, a connected real interval `J` across which the transition reflects with
  positive derivative, its inherited logarithm), collars at a shared-side point `y₀` and an exposed point `ξ`;
* an inner harmonic function `vI` whose corrected inner-chart reading has the **zero-phase** inner word at the two
  image points (R.5 for the nested pocket with Aux. 122's zero phase, at the common physical time), with its own
  offset `aI`;
* the two physical germ comparisons `vI − v → 0` (R.5's ambient germ identification for nested pockets);
* the canonical heights of the two words agree at the two points.

`phase_eq_zero_of_r6Cert` (deterministic), the test-level inputs `TwoSeedNestCertInput(Inf)` (named, unproved) and
**`twoSeedNestRelInput_of_cert`**, **`twoSeedNestRelInputInf_of_cert`**.

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open QuantumZipper (H Hbar chiC)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Sec7.R6Rel

open PocketTraversal Lemma71C PocketStop PocketWordAssembly PocketSeedOpen PocketCoupling PocketJordan Hsd
  PhaseClause PocketStopField PocketMarks SideVis HOuter WangWu PocketCoord PocketStopSide R6Nest LocalSets

/-! ### The pathwise certificate -/

section Cert

/-- **The transition geometry of R.6** between an outer and an inner current chart: both conformal, the inner
current domain inside the outer one, a connected real interval `J` across which the transition `G` reflects with
positive derivative, `G` extends the transition chart, and `Lg` is the inherited transition logarithm. -/
def R6Transition (outer inner : Chart) (J : Set ℝ) (G Lg : ℂ → ℂ) : Prop :=
  outer.IsConformal ∧ inner.IsConformal ∧ (inner.dom : Set ℂ) ⊆ outer.dom ∧ IsPreconnected J ∧
    (∀ y ∈ J, ∃ r > 0, R16.IsRealBoundaryConformal G y r) ∧ ContinuousOn (fun y : ℝ => Lg y) J ∧
    (∀ y ∈ J, Complex.exp (Lg y) = deriv (QuantumZipper.CA.schwarzReflect G) y) ∧
    EqOn G (pocketTransitionChart outer inner).1 (pocketTransitionChart outer inner).dom ∧
    ∀ z ∈ (pocketTransitionChart outer inner).dom, (Lg z).im = (pocketTransitionChart outer inner).2.2 z

/-- **A collar of R.6 at a real point `y ∈ J`**: a half-disc of the outer chart at `y` lies in the transition's
domain, `Lg` is continuous within `Hbar` at `y`, and the transition lands at the inner real point `η`. -/
def R6Collar (outer inner : Chart) (J : Set ℝ) (G Lg : ℂ → ℂ) (y η : ℝ) : Prop :=
  y ∈ J ∧ (∃ r > 0, H ∩ ball (y : ℂ) r ⊆ ((pocketTransitionChart outer inner).dom : Set ℂ)) ∧
    ContinuousWithinAt Lg Hbar (y : ℂ) ∧ Tendsto G (𝓝[H] (y : ℂ)) (𝓝[H] (η : ℂ))

/-- **R.5's physical germ comparison at `y`** between the outer harmonic function `v` and the inner one `vI`, read
through the outer chart. -/
def R6Germ (outer : Chart) (v vI : ℂ → ℝ) (y : ℝ) : Prop :=
  Tendsto (fun z => vI (outer.2.1 z) - v (outer.2.1 z)) (𝓝[H] (y : ℂ)) (𝓝 0)

/-- **A pathwise R.6 certificate** for the outer current chart `outer`, the outer harmonic function `v` (a
representative of the outer local-set mean), the outer two-seed word `(ρL, ρR)` at the relative marks `(vL, vR)`, and
the harmonic part `u`: an inner current chart with R.6's transition geometry, a shared unvisited-side point `y₀` and
an exposed point `ξ` of the outer word (non-jump points, outside resp. inside the exposed interval) with collars,
an inner harmonic function `vI` whose corrected inner reading has the **zero-phase** inner word (own weights, marks
and offset `aI`) at their images `η₀`, `η`, equal canonical heights, and the two germ comparisons. No outer phase
appears. -/
def R6Cert (κ : ℝ) {nL nR : ℕ} (ρL : Fin (nL + 1) → ℝ) (ρR : Fin (nR + 1) → ℝ) (vL : Fin (nL + 1) → ℝ)
    (vR : Fin (nR + 1) → ℝ) (outer : Chart) (u v : ℂ → ℝ) : Prop :=
  ∃ (inner : Chart) (J : Set ℝ) (G Lg : ℂ → ℂ) (mL mR : ℕ) (σL : Fin (mL + 1) → ℝ) (σR : Fin (mR + 1) → ℝ)
    (wL : Fin (mL + 1) → ℝ) (wR : Fin (mR + 1) → ℝ) (vI : ℂ → ℝ) (aI y₀ η₀ ξ η : ℝ),
    R6Transition outer inner J G Lg ∧
    (R6Collar outer inner J G Lg y₀ η₀ ∧ y₀ ∉ forceJumpSet vL vR ∧ y₀ ∉ Ioo (vL 0) (vR 0) ∧
      η₀ ∉ Ioo (wL 0) (wR 0) ∧ forceBoundaryData κ ρL ρR vL vR y₀ = forceBoundaryData κ σL σR wL wR η₀ ∧
      Tendsto (sideMean κ inner u vI) (𝓝[H] (η₀ : ℂ)) (𝓝 (PhaseSel.phaseData κ σL σR wL wR 0 η₀ - aI)) ∧
      R6Germ outer v vI y₀) ∧
    (R6Collar outer inner J G Lg ξ η ∧ ξ ∉ forceJumpSet vL vR ∧ ξ ∈ Ioo (vL 0) (vR 0) ∧
      η ∈ Ioo (wL 0) (wR 0) ∧ forceBoundaryData κ ρL ρR vL vR ξ = forceBoundaryData κ σL σR wL wR η ∧
      Tendsto (sideMean κ inner u vI) (𝓝[H] (η : ℂ)) (𝓝 (PhaseSel.phaseData κ σL σR wL wR 0 η - aI)) ∧
      R6Germ outer v vI ξ)

/-- **The certificate forces zero phase** (Lemma R.6 with independent offsets): if the outer corrected reading of
`v` has the outer phase word with phase `d` and offset `a` at every non-jump point, an R.6 certificate gives `d = 0`. -/
theorem phase_eq_zero_of_r6Cert {κ : ℝ} {nL nR : ℕ} {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ}
    {vL : Fin (nL + 1) → ℝ} {vR : Fin (nR + 1) → ℝ} {outer : Chart} {u v : ℂ → ℝ}
    (hcert : R6Cert κ ρL ρR vL vR outer u v) {a d : ℝ}
    (hlim : ∀ ξ : ℝ, ξ ∉ forceJumpSet vL vR →
      Tendsto (sideMean κ outer u v) (𝓝[H] (ξ : ℂ)) (𝓝 (PhaseSel.phaseData κ ρL ρR vL vR d ξ - a))) :
    d = 0 := by
  obtain ⟨inner, J, G, Lg, mL, mR, σL, σR, wL, wR, vI, aI, y₀, η₀, ξ, η,
    ⟨hO, hI, hinc, hJ, hloc, hLc, hexp, hext, hlog⟩,
    ⟨⟨hy₀J, ⟨r₀, hr₀, hcol₀⟩, hL₀, hG₀⟩, hy₀j, hy₀Out, hη₀Out, hSH, hIn₀, hgerm₀⟩,
    ⟨⟨hξJ, ⟨r, hr, hcol⟩, hLξ, hGξ⟩, hξj, hξIn, hηIn, hEH, hInξ, hgermξ⟩⟩ := hcert
  exact phase_eq_of_shared_current_pocket_words hO hI hinc hJ hloc hLc hexp hext hlog hy₀J hr₀ hcol₀ hL₀ hG₀
    hy₀Out hη₀Out hSH (hlim y₀ hy₀j) hIn₀ hgerm₀ hξJ hr hcol hLξ hGξ hξIn hηIn hEH (hlim ξ hξj) hInξ hgermξ

end Cert

/-! ### Two-seed heights (for building certificates) -/

section Heights

variable {κ : ℝ} {ρL ρR vL vR : Fin 1 → ℝ} {x : ℝ}

/-- A two-seed word on its unvisited right side `[v_R, ∞)` (`0 ≤ v_R`) has the height `λ(1 + ρ_R)`. -/
theorem forceBoundaryData_one_of_vR_le (h0 : 0 ≤ vR 0) (hx : vR 0 ≤ x) :
    forceBoundaryData κ ρL ρR vL vR x = Real.pi / Real.sqrt κ * (1 + ρR 0) := by
  have hf : Finset.univ.filter (fun i : Fin 1 => vR i ≤ x) = Finset.univ :=
    Finset.filter_true_of_mem fun i _ => by rwa [Subsingleton.elim i 0]
  simp only [forceBoundaryData, not_lt.2 (h0.trans hx), ↓reduceIte, hf, Fin.sum_univ_one]

/-- A two-seed word on its unvisited left side `(−∞, v_L)` (`v_L ≤ 0`) has the height `−λ(1 + ρ_L)`. -/
theorem forceBoundaryData_one_of_lt_vL (h0 : vL 0 ≤ 0) (hx : x < vL 0) :
    forceBoundaryData κ ρL ρR vL vR x = -(Real.pi / Real.sqrt κ) * (1 + ρL 0) := by
  have hf : Finset.univ.filter (fun i : Fin 1 => x < vL i) = Finset.univ :=
    Finset.filter_true_of_mem fun i _ => by rwa [Subsingleton.elim i 0]
  simp only [forceBoundaryData, lt_of_lt_of_le hx h0, ↓reduceIte, hf, Fin.sum_univ_one]

/-- A two-seed word on the left exposed side `[v_L, 0)` has the canonical height `−λ`. -/
theorem forceBoundaryData_one_exposedLeft (hvL : vL 0 ≤ x) (hx : x < 0) :
    forceBoundaryData κ ρL ρR vL vR x = -(Real.pi / Real.sqrt κ) := by
  have hf : Finset.univ.filter (fun i : Fin 1 => x < vL i) = ∅ :=
    Finset.filter_false_of_mem fun i _ => by rw [Subsingleton.elim i 0]; exact not_lt.2 hvL
  simp only [forceBoundaryData, hx, ↓reduceIte, hf, Finset.sum_empty, add_zero, mul_one]

/-- A two-seed word on the right exposed side `[0, v_R)` has the canonical height `λ`. -/
theorem forceBoundaryData_one_exposedRight (hx : 0 ≤ x) (hvR : x < vR 0) :
    forceBoundaryData κ ρL ρR vL vR x = Real.pi / Real.sqrt κ := by
  have hf : Finset.univ.filter (fun i : Fin 1 => vR i ≤ x) = ∅ :=
    Finset.filter_false_of_mem fun i _ => by rw [Subsingleton.elim i 0]; exact not_le.2 hvR
  simp only [forceBoundaryData, not_lt.2 hx, ↓reduceIte, hf, Finset.sum_empty, add_zero, mul_one]

end Heights

/-! ### The certificate on a pocket test -/

section Test

variable {Ω : Type*}

/-- **R.6 certificates at deterministic relative times on every test** (bounded outer pocket; named, unproved):
for every test `A`, Jordan chart `ψ`, walls-measurable branch `n`, rational relative time `q` and inner parameter
`s`, some local-set mean `g` of the outer pocket's active complement at `q` has, almost surely on the test and on the
nested-pocket event `nestRelEvent … s q`, a harmonic representative `v` with an R.6 certificate in the current chart
at `q` for the outer two-seed word. No phase word of the outer pocket appears. -/
def TwoSeedNestCertInput (k rL rR : ℝ) (𝓦 : MeasurableSpace Ω) [MeasurableSpace Ω] (P : Measure Ω)
    (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (η : Ω → ℝ → ℂ) (G : Set Ω) (h₀ : Ω → DistOn upperHalfPlaneOpens)
    (u : ℂ → ℝ) (βR βL R' L' : Ω → ℝ≥0 → ℂ) : Prop :=
  ∀ A : Set Ω, MeasurableSet[𝓦] A → A ⊆ G → 0 < P A →
    ∀ ψ : Ω → ℂ → ℂ, (∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω)) →
      @IsPointMeasurable Ω 𝓦 R L r G ψ →
    ∀ n : Ω → ℤ, Measurable[𝓦] n → ∀ q s : ℚ,
      ∃ g : Ω → DistOn upperHalfPlaneOpens,
        IsLocalSetMean (activeCompl A (travAll R L r η ψ)
          (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) (StripSys.rt q)) h₀ P g ∧
        ∀ᵐ ω ∂P, ω ∈ A → ω ∈ nestRelEvent R L r η ψ βR βL R' L' s q →
          ∃ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ activeCompl A (travAll R L r η ψ)
              (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) (StripSys.rt q) ω) ∧
            (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ activeCompl A (travAll R L r η ψ)
                (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) (StripSys.rt q) ω →
              g ω φ = ∫ z, v z * φ z) ∧
            R6Cert k (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR)
              (fun i => geomLW (fun t ω => segDriver (travAll R L r η ψ ω) t) (fun _ => LP.twoSeedXL) i
                (StripSys.rt q) ω - segDriver (travAll R L r η ψ ω) (StripSys.rt q))
              (fun j => geomRW (fun t ω => segDriver (travAll R L r η ψ ω) t) (fun _ => LP.twoSeedXR) j
                (StripSys.rt q) ω - segDriver (travAll R L r η ψ ω) (StripSys.rt q))
              (relChart (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω))
                (travAll R L r η ψ) (StripSys.rt q) ω) u v

/-- **R.6 certificates at deterministic relative times on every test** (pocket opening at the flow seed; named,
unproved). -/
def TwoSeedNestCertInputInf (k rL rR : ℝ) (𝓦 : MeasurableSpace Ω) [MeasurableSpace Ω] (P : Measure Ω)
    (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (η : Ω → ℝ → ℂ) (G : Set Ω) (h₀ : Ω → DistOn upperHalfPlaneOpens)
    (u : ℂ → ℝ) (βR βL R' L' : Ω → ℝ≥0 → ℂ) : Prop :=
  ∀ A : Set Ω, MeasurableSet[𝓦] A → A ⊆ G → 0 < P A →
    ∀ ψ : Ω → ℂ → ℂ, (∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω)) →
      @IsPointMeasurableInf Ω 𝓦 R L r G ψ →
    ∀ n : Ω → ℤ, Measurable[𝓦] n → ∀ q s : ℚ,
      ∃ g : Ω → DistOn upperHalfPlaneOpens,
        IsLocalSetMean (activeCompl A (travAllInf R L r η ψ)
          (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) (StripSys.rt q)) h₀ P g ∧
        ∀ᵐ ω ∂P, ω ∈ A → ω ∈ nestRelEventInf R L r η ψ βR βL R' L' s q →
          ∃ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ activeCompl A (travAllInf R L r η ψ)
              (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) (StripSys.rt q) ω) ∧
            (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ activeCompl A (travAllInf R L r η ψ)
                (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) (StripSys.rt q) ω →
              g ω φ = ∫ z, v z * φ z) ∧
            R6Cert k (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR)
              (fun i => geomLW (fun t ω => segDriver (travAllInf R L r η ψ ω) t) (fun _ => LP.twoSeedXL) i
                (StripSys.rt q) ω - segDriver (travAllInf R L r η ψ ω) (StripSys.rt q))
              (fun j => geomRW (fun t ω => segDriver (travAllInf R L r η ψ ω) t) (fun _ => LP.twoSeedXR) j
                (StripSys.rt q) ω - segDriver (travAllInf R L r η ψ ω) (StripSys.rt q))
              (relChart (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω))
                (travAllInf R L r η ψ) (StripSys.rt q) ω) u v

/-- **The R.6 transfer at deterministic relative times from certificates** (bounded outer pocket): the outer word at
`q` (the antecedent of `TwoSeedNestRelInput`) and a certificate for the same mean representative give `δ_q = 0`. -/
theorem twoSeedNestRelInput_of_cert {k rL rR : ℝ} {𝓦 : MeasurableSpace Ω} [MeasurableSpace Ω] {P : Measure Ω}
    {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {η : Ω → ℝ → ℂ} {G : Set Ω} {h₀ : Ω → DistOn upperHalfPlaneOpens}
    {u : ℂ → ℝ} {βR βL R' L' : Ω → ℝ≥0 → ℂ}
    (hcert : TwoSeedNestCertInput k rL rR 𝓦 P R L r η G h₀ u βR βL R' L') :
    TwoSeedNestRelInput k rL rR 𝓦 P R L r η G h₀ u βR βL R' L' := by
  intro A hA hAG hPA ψ hJ hPt n hn a δ γ c hside _hcont q s
  obtain ⟨g, hg, hae⟩ := hcert A hA hAG hPA ψ hJ hPt n hn q s
  filter_upwards [(hside (StripSys.rt q)).2 g hg, hae] with ω hs hω hωA hωN
  obtain ⟨v, hv, hvr, hc⟩ := hω hωA hωN
  exact phase_eq_zero_of_r6Cert hc fun ξ hξ => hs hωA hωN.2.1 v hv hvr ξ hξ

/-- **The R.6 transfer at deterministic relative times from certificates** (pocket opening at the flow seed). -/
theorem twoSeedNestRelInputInf_of_cert {k rL rR : ℝ} {𝓦 : MeasurableSpace Ω} [MeasurableSpace Ω] {P : Measure Ω}
    {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {η : Ω → ℝ → ℂ} {G : Set Ω} {h₀ : Ω → DistOn upperHalfPlaneOpens}
    {u : ℂ → ℝ} {βR βL R' L' : Ω → ℝ≥0 → ℂ}
    (hcert : TwoSeedNestCertInputInf k rL rR 𝓦 P R L r η G h₀ u βR βL R' L') :
    TwoSeedNestRelInputInf k rL rR 𝓦 P R L r η G h₀ u βR βL R' L' := by
  intro A hA hAG hPA ψ hJ hPt n hn a δ γ c hside _hcont q s
  obtain ⟨g, hg, hae⟩ := hcert A hA hAG hPA ψ hJ hPt n hn q s
  filter_upwards [(hside (StripSys.rt q)).2 g hg, hae] with ω hs hω hωA hωN
  obtain ⟨v, hv, hvr, hc⟩ := hω hωA hωN
  exact phase_eq_zero_of_r6Cert hc fun ξ hξ => hs hωA hωN.2.1 v hv hvr ξ hξ

end Test

end InteractingSLE.Sec7.R6Rel
