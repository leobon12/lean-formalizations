/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.StripPocketPathFinal
import InteractingSLE.Spec.Sec7.StripWallMeanFull
import InteractingSLE.Spec.Sec7.StripWallVersion
import InteractingSLE.WangWu.Prop418RangeGlue
import InteractingSLE.Spec.Dimension.TraceBridge

/-!
# Theorem 1.3's pocket word from the strip system: the realization data

Packet PROVE-STRIPSYS34 (second part). PROVE-STRIPSYS31's `StripPocketPath.pocketWordEvolution_of_stripSystem` takes,
besides its field-level inputs, **realization data**: driver regularity at every sample for the three programs
(`hregα`, `hregβ`, `hregE`) and versions of the paths (the walls `α`, `β^{(q)}`, the unchanged extremal path
`β = η_{π/2}` and the counterflow's trace `η`). Here they are supplied.

* **`stagedPiecesRegular_leftExtremal`**: the one-piece history `β = η_{π/2}` is `StagedPiecesRegular` (R51) for the
  strip system: its only piece is the stage-`0` flow line of `h` itself, whose driver is continuous from `0` and has a
  simple transient trace almost surely (`ae_simple_trace_leftExtremal_strip`). So `hregE` needs no input: the
  regularized family `StripWall.regStrip` is regular at every sample on `leftExtremalSpec`.
* **`exists_traceVersion`** (generic): a measurable family of drivers which almost surely is continuous from `0` with a
  generating trace on `[0, ∞)` has a version of that trace — continuous at every sample, `0` at `0`, in `ℍ̄`, measurable
  at fixed times. Applied to `β` (`exists_betaVersion`) and, through the dyadic killed history, to the counterflow
  driver `W′` (`exists_cfVersion`, the `η : Ω → ℝ → ℂ` of STRIPSYS31).
* **`pocketWordEvolution_of_stripSystem_reg`**: STRIPSYS31's theorem with `hregα`, `hregβ`, `hregE` replaced by
  `StagedPiecesRegular` of the two two-angle programs (the R51 hypothesis carried by the frozen Theorem 1.4 surface and
  produced by the strengthened companion), through `StripWall.regStrip`; the given versions are versions for the
  original family.
* **`exists_stripVersions`**: versions of all four paths for the original family (under the same two
  `StagedPiecesRegular` hypotheses).

No result here uses Theorem 1.2, Theorem 1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`
(R43, R48).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Function
open QuantumZipper (H Hbar chiC)
open LQGMetric (DistOn IsZeroBoundaryGFF)
open InteractingSLE.WangWu (negInv)
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Sec7.StripPocketVersions

open Exist.Staged (IsRegularDriver)
open StripSideHeightProb (catPath)
open Theorem14.StagedReg (regHist regHist_snd isRegularDriver_regHist regularize_eq_of_lt)

/-! ### A version of a generating trace -/

section Generic

/-- The points of a continuous generating trace on `[0, ∞)` of a continuous driver from `0` lie in `ℍ̄`. -/
theorem trace_mem_Hbar {w : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} (hγ : IsGeneratingTrace w ⊤ γ) (hw : Continuous w)
    (hw0 : w 0 = 0) (t : ℝ≥0) : γ t ∈ Hbar :=
  QuantumZipper.isClosed_Hbar.mem_of_tendsto
    (hγ.tendsto_fwdMapInv_mul_I hw.continuousOn hw0 ENNReal.coe_lt_top)
    (Eventually.of_forall fun _ => QuantumZipper.F1.fwdMapInv_mem_Hbar _ _ _)

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

open scoped Classical in
/-- **A version of a generating trace.** A measurable family of drivers `w` which is almost surely continuous from
`0` with a generating trace on `[0, ∞)` has a version `γ` of that trace: continuous at every sample, `0` at `0`, in
`ℍ̄`, measurable at fixed times, and almost surely the generating trace of `w`. It is the trace read by `LP.traceAt`
on a measurable full-measure set, and `0` elsewhere. -/
theorem exists_traceVersion {w : Ω → ℝ≥0 → ℝ} (hwm : Measurable w)
    (htr : ∀ᵐ ω ∂P, Continuous (w ω) ∧ w ω 0 = 0 ∧ ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (w ω) ⊤ η) :
    ∃ γ : Ω → ℝ≥0 → ℂ, (∀ ω, Continuous (γ ω)) ∧ (∀ ω, γ ω 0 = 0) ∧ (∀ ω t, γ ω t ∈ Hbar) ∧
      (∀ t, Measurable fun ω => γ ω t) ∧ ∀ᵐ ω ∂P, IsGeneratingTrace (w ω) ⊤ (γ ω) := by
  set S : Set Ω := {ω | Continuous (w ω) ∧ w ω 0 = 0 ∧ ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (w ω) ⊤ η} with hS
  obtain ⟨N, hSN, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 htr)
  have hG : ∀ ω, ω ∉ N → ω ∈ S := fun ω hω => by
    by_contra h
    exact hω (hSN h)
  have hread : ∀ ω, ω ∉ N → Continuous (w ω) ∧ w ω 0 = 0 ∧ ∃ η : ℝ≥0 → ℂ,
      (∀ t, LP.traceAt t (w ω) = η t) ∧ IsGeneratingTrace (w ω) ⊤ η := by
    intro ω hω
    obtain ⟨hc, h0, η, hη⟩ := hG ω hω
    exact ⟨hc, h0, η, fun t => LP.traceAt_eq_of_isGeneratingTrace hη hc.continuousOn h0 ENNReal.coe_lt_top, hη⟩
  refine ⟨fun ω t => if ω ∈ N then 0 else LP.traceAt t (w ω), fun ω => ?_, fun ω => ?_, fun ω t => ?_,
    fun t => ?_, ?_⟩
  · by_cases hω : ω ∈ N
    · simp only [hω, ↓reduceIte]
      exact continuous_const
    · obtain ⟨-, -, η, he, hη⟩ := hread ω hω
      simp only [hω, ↓reduceIte, he]
      exact continuousOn_univ.1 (hη.2.1.mono fun t _ => show (t : ℝ≥0∞) ≤ ⊤ from le_top)
  · by_cases hω : ω ∈ N
    · simp only [hω, ↓reduceIte]
    · obtain ⟨-, -, η, he, hη⟩ := hread ω hω
      simp only [hω, ↓reduceIte, he]
      exact hη.1
  · by_cases hω : ω ∈ N
    · simp only [hω, ↓reduceIte]
      exact show (0 : ℝ) ≤ (0 : ℂ).im from le_of_eq Complex.zero_im.symm
    · obtain ⟨hc, h0, η, he, hη⟩ := hread ω hω
      simp only [hω, ↓reduceIte, he]
      exact trace_mem_Hbar hη hc h0 t
  · exact Measurable.ite hNm measurable_const ((LP.measurable_traceAt t).comp hwm)
  · have hNc : ∀ᵐ ω ∂P, ω ∉ N := measure_eq_zero_iff_ae_notMem.1 hN0
    filter_upwards [hNc] with ω hω
    obtain ⟨-, -, η, he, hη⟩ := hread ω hω
    simp only [hω, ↓reduceIte, he]
    exact hη

end Generic

/-! ### The unchanged extremal path `β = η_{π/2}` is regular -/

section Extremal

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ}
  {ζ' : Ω → ℝ≥0∞} {Es : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- **The driver of `β = η_{π/2}` is regular almost surely**: infinite lifetime, `0` at `0`, continuous, with a
transient generating trace on `[0, ∞)` (the stage-`0` flow line of `h`; Proposition 4.12 for its (4.4) word). -/
theorem ae_regular_leftExtremal (hS : StripSys.IsStripSystem κ b jumps P h W' ζ' Es)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ) :
    ∀ᵐ ω ∂P, (Es StripSys.leftExtremalSpec 0 ω).2 = ⊤ ∧ (Es StripSys.leftExtremalSpec 0 ω).1 0 = 0 ∧
      Continuous (Es StripSys.leftExtremalSpec 0 ω).1 ∧ ∃ η : ℝ≥0 → ℂ,
        IsGeneratingTrace (Es StripSys.leftExtremalSpec 0 ω).1 ⊤ η ∧ Tendsto (fun t => ‖η t‖) atTop atTop := by
  obtain ⟨h', 𝓕, VL, VR, B, -, hC⟩ := StripPocketPath.isFlowLineDriver_leftExtremal hS.kappa_pos hS.boundaryData
    hS.gff hS.isStagedHistory_leftExtremal
  filter_upwards [StripPocketPath.ae_simple_trace_leftExtremal_strip hS hcumL hcumR, hC.1.2.2.2.2] with ω h1 hp
  obtain ⟨hζ, η, hη, -, -, htr⟩ := h1
  have hc : ContinuousOn (Es StripSys.leftExtremalSpec 0 ω).1
      {t : ℝ≥0 | (t : ℝ≥0∞) < (Es StripSys.leftExtremalSpec 0 ω).2} := hp.2.2.2.1
  rw [hζ] at hc
  exact ⟨hζ, hp.1, continuousOn_univ.1 (hc.mono fun t _ => ENNReal.coe_lt_top), η, hη, htr⟩

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
/-- The only instruction of `leftExtremalSpec` is the angle-`π/2` piece run through its lifetime. -/
theorem eq_of_leftExtremalSpec_getElem? {k : ℕ} {θ : ℝ} {t : ℝ≥0∞}
    (hk : StripSys.leftExtremalSpec.2.2[k]? = some (Sum.inl (θ, t))) : k = 0 ∧ t = ⊤ := by
  rcases k with _ | n
  · simp only [StripSys.leftExtremalSpec, List.getElem?_cons_zero, Option.some.injEq, Sum.inl.injEq,
      Prod.mk.injEq] at hk
    exact ⟨rfl, hk.2.symm⟩
  · simp [StripSys.leftExtremalSpec] at hk

/-- **`β = η_{π/2}` is `StagedPiecesRegular`** (R51) for the strip system: its only piece is the stage-`0` flow line of
`h` itself, which is almost surely regular (`ae_regular_leftExtremal`). -/
theorem stagedPiecesRegular_leftExtremal (hS : StripSys.IsStripSystem κ b jumps P h W' ζ' Es)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ) :
    StagedPiecesRegular κ b jumps P StripSys.leftExtremalSpec (Es StripSys.leftExtremalSpec) := by
  filter_upwards [ae_regular_leftExtremal hS hcumL hcumR] with ω hω k θ t c hk _
  obtain ⟨hζ, h0, hc, η, hη, htr⟩ := hω
  obtain ⟨rfl, rfl⟩ := eq_of_leftExtremalSpec_getElem? hk
  rw [hζ, min_self]
  exact ⟨h0, hc.continuousOn, η, hη, fun _ => htr⟩

/-- **The regularized strip family is regular at every sample on `β = η_{π/2}`**, and its driver is almost surely the
original one. -/
theorem regStrip_leftExtremal (hS : StripSys.IsStripSystem κ b jumps P h W' ζ' Es)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ) :
    (∀ ω, IsRegularDriver (StripWall.regStrip κ b jumps P Es StripSys.leftExtremalSpec 0 ω)) ∧
      ∀ᵐ ω ∂P, (StripWall.regStrip κ b jumps P Es StripSys.leftExtremalSpec 0 ω).1 =
        (Es StripSys.leftExtremalSpec 0 ω).1 := by
  have e := StripWall.regStrip_of (stagedPiecesRegular_leftExtremal hS hcumL hcumR)
  refine ⟨fun ω => by rw [e]; exact isRegularDriver_regHist 0 ω, ?_⟩
  rw [e]
  filter_upwards [ae_regular_leftExtremal hS hcumL hcumR] with ω hω
  obtain ⟨hζ, h0, hc, -⟩ := hω
  funext s
  exact regularize_eq_of_lt _ h0 hc.continuousOn (by rw [hζ]; exact ENNReal.coe_lt_top)

end Extremal

/-! ### The two-angle walls of the regularized family -/

section Walls

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ}
  {ζ' : Ω → ℝ≥0∞} {Es : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- **The wall `α` of the regularized family**: regular at every sample, and almost surely with the original
concatenated driver (under `StagedPiecesRegular` of `alphaSpec θ₁`, R51). -/
theorem regStrip_alpha (hS : StripSys.IsStripSystem κ b jumps P h W' ζ' Es)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {θ₁ : ℝ} (hθ₁ : θ₁ ∈ Icc (-(π / 2)) (π / 2))
    (hRα : StagedPiecesRegular κ b jumps P (StripSys.alphaSpec θ₁) (Es (StripSys.alphaSpec θ₁))) :
    (∀ j ω, IsRegularDriver (StripWall.regStrip κ b jumps P Es (StripSys.alphaSpec θ₁) j ω)) ∧
      ∀ᵐ ω ∂P, catPath (StripWall.regStrip κ b jumps P Es (StripSys.alphaSpec θ₁) 0 ω).1 1
        (StripWall.regStrip κ b jumps P Es (StripSys.alphaSpec θ₁) 1 ω).1 =
          catPath (Es (StripSys.alphaSpec θ₁) 0 ω).1 1 (Es (StripSys.alphaSpec θ₁) 1 ω).1 := by
  have hS' := StripWall.isStripSystem_regStrip hS
  have eα := StripWall.regStrip_of hRα
  have hregα : ∀ j ω, IsRegularDriver (StripWall.regStrip κ b jumps P Es (StripSys.alphaSpec θ₁) j ω) :=
    fun j ω => by rw [eα]; exact isRegularDriver_regHist j ω
  have hζα : ∀ᵐ ω ∂P, (Es (StripSys.alphaSpec θ₁) 0 ω).2 = ⊤ ∧ (Es (StripSys.alphaSpec θ₁) 1 ω).2 = ⊤ := by
    filter_upwards [StripWall.ae_simple_trace_alpha hS' hcumL hcumR hθ₁ hregα] with ω hω
    rw [eα, regHist_snd, regHist_snd] at hω
    exact hω.1
  refine ⟨hregα, ?_⟩
  rw [eα]
  filter_upwards [StripWall.ae_catPath_regHist_eq (θ₀ := -(π / 2)) (t₀ := 1) (θ := θ₁) hRα hζα] with ω h2
  rw [StripSys.alphaSpec] at h2 ⊢
  exact h2

/-- **The wall `β^{(r)}` of the regularized family**: regular at every sample, and almost surely with the original
concatenated driver (under `StagedPiecesRegular` of `betaSpec r θ₂`, R51). -/
theorem regStrip_beta (hS : StripSys.IsStripSystem κ b jumps P h W' ζ' Es)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {θ₂ : ℝ} (hθ₂ : θ₂ ∈ Icc (-(π / 2)) (π / 2)) (r : ℝ≥0)
    (hRβ : StagedPiecesRegular κ b jumps P (StripSys.betaSpec r θ₂) (Es (StripSys.betaSpec r θ₂))) :
    (∀ j ω, IsRegularDriver (StripWall.regStrip κ b jumps P Es (StripSys.betaSpec r θ₂) j ω)) ∧
      ∀ᵐ ω ∂P, catPath (StripWall.regStrip κ b jumps P Es (StripSys.betaSpec r θ₂) 0 ω).1 r
        (StripWall.regStrip κ b jumps P Es (StripSys.betaSpec r θ₂) 1 ω).1 =
          catPath (Es (StripSys.betaSpec r θ₂) 0 ω).1 r (Es (StripSys.betaSpec r θ₂) 1 ω).1 := by
  have hS' := StripWall.isStripSystem_regStrip hS
  have eβ := StripWall.regStrip_of hRβ
  have hregβ : ∀ j ω, IsRegularDriver (StripWall.regStrip κ b jumps P Es (StripSys.betaSpec r θ₂) j ω) :=
    fun j ω => by rw [eβ]; exact isRegularDriver_regHist j ω
  have hζβ : ∀ᵐ ω ∂P, (Es (StripSys.betaSpec r θ₂) 0 ω).2 = ⊤ ∧ (Es (StripSys.betaSpec r θ₂) 1 ω).2 = ⊤ := by
    filter_upwards [StripWall.ae_simple_trace_beta hS' hcumL hcumR hθ₂ r hregβ] with ω hω
    rw [eβ, regHist_snd, regHist_snd] at hω
    exact hω.1
  refine ⟨hregβ, ?_⟩
  rw [eβ]
  filter_upwards [StripWall.ae_catPath_regHist_eq (θ₀ := π / 2) (t₀ := r) (θ := θ₂) hRβ hζβ] with ω h2
  rw [StripSys.betaSpec] at h2 ⊢
  exact h2

end Walls

/-! ### hPW from the strip system with `StagedPiecesRegular` in place of everywhere-regular drivers -/

section Final

open WangWu Lemma71I PocketCoord PocketJordan PocketMarks PocketWordAssembly PocketSeedOpen PocketLeftFrontier
  PocketCoupling StripSideHeightProb StripPocketPath

/-- **hPW from the strip system, with R51's regularity** (STRIPSYS31's `pocketWordEvolution_of_stripSystem` with the
driver regularity at every sample replaced by `StagedPiecesRegular` of the two two-angle programs; the extremal path
needs nothing, `stagedPiecesRegular_leftExtremal`): the given versions `α`, `β`, `Lr`, `η` are versions of the paths of
the original family `Es`, and the remaining inputs are those of STRIPSYS31 (see there). The proof applies
STRIPSYS31's result to the regularized family `StripWall.regStrip κ b jumps P Es`, a strip system with the same field
and counterflow, whose drivers agree with the original ones almost surely. -/
theorem pocketWordEvolution_of_stripSystem_reg {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u}
    {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    {Es : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (h44 : AdmCode.Theorem12ParamCond44Statement.{u}) (haux7 : Sec4.Aux7Statement.{u} (16 / κ))
    (hS : StripSys.IsStripSystem κ b jumps P h W' ζ' Es)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {θ₁ θ₂ : ℝ} (hθ₁ : θ₁ ∈ Ioo (-(π / 2)) (π / 2)) (hθ₂ : θ₂ ∈ Icc (-(π / 2)) (π / 2))
    {rL rR : ℝ} (hL : -2 < rL) (hLd : rL < 16 / κ / 2 - 4) (hRr : -2 < rR) (hRd : rR < 16 / κ / 2 - 4)
    (hRα : StagedPiecesRegular κ b jumps P (StripSys.alphaSpec θ₁) (Es (StripSys.alphaSpec θ₁)))
    (hRβ : ∀ q : ℚ, 0 < q → StagedPiecesRegular κ b jumps P (StripSys.betaSpec (StripSys.rt q) θ₂)
      (Es (StripSys.betaSpec (StripSys.rt q) θ₂))) (h𝓦 : 𝓦 ≤ mΩ)
    {α β : Ω → ℝ≥0 → ℂ} {Lr : ℚ → Ω → ℝ≥0 → ℂ} {η : Ω → ℝ → ℂ}
    (hαc : ∀ ω, Continuous (α ω)) (hα0 : ∀ ω, α ω 0 = 0) (hαm : ∀ t, Measurable[𝓦] fun ω => α ω t)
    (hαtr : ∀ᵐ ω ∂P, IsGeneratingTrace (catPath (Es (StripSys.alphaSpec θ₁) 0 ω).1 1
      (Es (StripSys.alphaSpec θ₁) 1 ω).1) ⊤ (α ω))
    (hβc : ∀ ω, Continuous (β ω)) (hβ0 : ∀ ω, β ω 0 = 0) (hβm : ∀ t, Measurable fun ω => β ω t)
    (hβtr : ∀ᵐ ω ∂P, IsGeneratingTrace (Es StripSys.leftExtremalSpec 0 ω).1 ⊤ (β ω))
    (hLc : ∀ q ω, Continuous (Lr q ω)) (hL0 : ∀ q ω, Lr q ω 0 = 0)
    (hLm : ∀ q t, Measurable[𝓦] fun ω => Lr q ω t)
    (hLtr : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, IsGeneratingTrace (catPath (Es (StripSys.betaSpec (StripSys.rt q) θ₂) 0 ω).1
      (StripSys.rt q) (Es (StripSys.betaSpec (StripSys.rt q) θ₂) 1 ω).1) ⊤ (Lr q ω))
    (hηc : ∀ ω, ContinuousOn (η ω) (Ici 0)) (hηH : ∀ ω, ∀ t : ℝ, 0 ≤ t → η ω t ∈ Hbar) (hη0 : ∀ ω, η ω 0 = 0)
    (hηm : ∀ t : ℝ, 0 ≤ t → Measurable fun ω => η ω t)
    (hηtr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (fun t : ℝ≥0 => η ω t))
    (hwalls : ∀ᵐ ω ∂P, IsWallReverseVisit (α ω) (η ω) ∧ IsWallVisited (α ω) (η ω) ∧
      IsWallReverseVisit (β ω) (η ω) ∧ IsWallVisited (β ω) (η ω))
    (hwallsL : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, IsWallReverseVisit (Lr q ω) (η ω) ∧ IsWallVisited (Lr q ω) (η ω))
    (hnohit : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → η ω t ≠ 0)
    (hav : ∀ᵐ ω ∂P, ∀ q : ℚ, 0 ≤ (q : ℝ) → negInv (η ω q) ∉ leftSideOf (range (β ω)))
    (hwit : ∀ q : ℚ, 0 < q → ∀ s₁ s₂ v v₁ v₂ : ℚ, ∀ᵐ ω ∂P, IsChangeConfigInc (α ω) (Lr q ω) (StripSys.rt q) →
      0 < rightLo (α ω) (Lr q ω) (StripSys.rt q) →
        ¬ IsPocketWitness (α ω) (Lr q ω) (StripSys.rt q) (η ω) s₁ s₂ v v₁ v₂)
    (hwitI : ∀ q : ℚ, 0 < q → ∀ s₁ s₂ v v₁ v₂ : ℚ, ∀ᵐ ω ∂P, IsChangeConfigInc (α ω) (Lr q ω) (StripSys.rt q) →
      rightLo (α ω) (Lr q ω) (StripSys.rt q) = 0 →
        ¬ IsPocketWitnessInf (α ω) (Lr q ω) (StripSys.rt q) (η ω) s₁ s₂ v v₁ v₂)
    {h₀ : Ω → DistOn upperHalfPlaneOpens} (hh₀ : IsZeroBoundaryGFF upperHalfPlaneOpens h₀ P)
    (𝔥 : DistOn upperHalfPlaneOpens)
    (hin : ∀ q : ℚ, 0 < q → ∀ G : Set Ω, MeasurableSet[𝓦 ⊔ Ito.nullSets P] G → 0 < P G →
      (∀ ω ∈ G, IsChangeConfigInc (α ω) (Lr q ω) (StripSys.rt q) ∧
        discTime 1 < rightHi (α ω) (Lr q ω) (StripSys.rt q)) →
      PocketUnionPtInput κ rL rR (𝓦 ⊔ Ito.nullSets P) P α (Lr q) (StripSys.rt q) η
          {ω | ω ∈ G ∧ 0 < rightLo (α ω) (Lr q ω) (StripSys.rt q)} h₀ 𝔥 ∧
        PocketUnionPtInputInf κ rL rR (𝓦 ⊔ Ito.nullSets P) P α (Lr q) (StripSys.rt q) η
          {ω | ω ∈ G ∧ ¬ 0 < rightLo (α ω) (Lr q ω) (StripSys.rt q)} h₀ 𝔥) :
    Lemma725Ref.PocketWordEvolution.{u} (16 / κ) rL rR := by
  have hθ₁c : θ₁ ∈ Icc (-(π / 2)) (π / 2) := Ioo_subset_Icc_self hθ₁
  have hS' := StripWall.isStripSystem_regStrip hS
  obtain ⟨hregα, hαe⟩ := regStrip_alpha hS hcumL hcumR hθ₁c hRα
  obtain ⟨hregE, hEe⟩ := regStrip_leftExtremal hS hcumL hcumR
  have hregβ : ∀ q : ℚ, 0 < q → ∀ j ω,
      IsRegularDriver (StripWall.regStrip κ b jumps P Es (StripSys.betaSpec (StripSys.rt q) θ₂) j ω) :=
    fun q hq => (regStrip_beta hS hcumL hcumR hθ₂ (StripSys.rt q) (hRβ q hq)).1
  have hαtr' : ∀ᵐ ω ∂P, IsGeneratingTrace
      (catPath (StripWall.regStrip κ b jumps P Es (StripSys.alphaSpec θ₁) 0 ω).1 1
        (StripWall.regStrip κ b jumps P Es (StripSys.alphaSpec θ₁) 1 ω).1) ⊤ (α ω) := by
    filter_upwards [hαtr, hαe] with ω h1 h2
    rw [h2]
    exact h1
  have hβtr' : ∀ᵐ ω ∂P, IsGeneratingTrace (StripWall.regStrip κ b jumps P Es StripSys.leftExtremalSpec 0 ω).1 ⊤
      (β ω) := by
    filter_upwards [hβtr, hEe] with ω h1 h2
    rw [h2]
    exact h1
  have hLtr' : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, IsGeneratingTrace
      (catPath (StripWall.regStrip κ b jumps P Es (StripSys.betaSpec (StripSys.rt q) θ₂) 0 ω).1 (StripSys.rt q)
        (StripWall.regStrip κ b jumps P Es (StripSys.betaSpec (StripSys.rt q) θ₂) 1 ω).1) ⊤ (Lr q ω) :=
    fun q hq => by
      filter_upwards [hLtr q hq, (regStrip_beta hS hcumL hcumR hθ₂ (StripSys.rt q) (hRβ q hq)).2] with ω h1 h2
      rw [h2]
      exact h1
  exact pocketWordEvolution_of_stripSystem h44 haux7 hS' hcumL hcumR hθ₁ hθ₂ hL hLd hRr hRd hregα hregβ hregE h𝓦
    hαc hα0 hαm hαtr' hβc hβ0 hβm hβtr' hLc hL0 hLm hLtr' hηc hηH hη0 hηm hηtr hwalls hwallsL hnohit hav hwit
    hwitI hh₀ 𝔥 hin

end Final

/-! ### Versions of the four paths -/

section Versions

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ}
  {ζ' : Ω → ℝ≥0∞} {Es : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- **A version of `β = η_{π/2}`**: continuous at every sample from `0`, measurable at fixed times, almost surely the
generating trace of its driver on `[0, ∞)`. -/
theorem exists_betaVersion (hS : StripSys.IsStripSystem κ b jumps P h W' ζ' Es)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ) :
    ∃ β : Ω → ℝ≥0 → ℂ, (∀ ω, Continuous (β ω)) ∧ (∀ ω, β ω 0 = 0) ∧ (∀ t, Measurable fun ω => β ω t) ∧
      ∀ᵐ ω ∂P, IsGeneratingTrace (Es StripSys.leftExtremalSpec 0 ω).1 ⊤ (β ω) := by
  obtain ⟨γ, hc, h0, -, hm, htr⟩ := exists_traceVersion (P := P)
    (w := fun ω => (Es StripSys.leftExtremalSpec 0 ω).1)
    (measurable_fst.comp (hS.isStagedHistory_leftExtremal.1 0)) (by
      filter_upwards [ae_regular_leftExtremal hS hcumL hcumR] with ω hω
      obtain ⟨-, h0, hc, η, hη, -⟩ := hω
      exact ⟨hc, h0, η, hη⟩)
  exact ⟨γ, hc, h0, hm, htr⟩

/-- **A version of the counterflow's trace** (the curve `η` of STRIPSYS31, indexed by `ℝ`): continuous on `[0, ∞)` at
every sample, in `ℍ̄`, `0` at `0`, measurable at fixed times, and almost surely the generating trace of the counterflow
driver `W′` on `[0, ∞)`. It is read from the dyadic killed history of `W′` (measurable by the coupling), on a
measurable full-measure set. -/
theorem exists_cfVersion (hS : StripSys.IsStripSystem κ b jumps P h W' ζ' Es)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ) :
    ∃ η : Ω → ℝ → ℂ, (∀ ω, ContinuousOn (η ω) (Ici 0)) ∧ (∀ ω, ∀ t : ℝ, 0 ≤ t → η ω t ∈ Hbar) ∧
      (∀ ω, η ω 0 = 0) ∧ (∀ t : ℝ, 0 ≤ t → Measurable fun ω => η ω t) ∧
      ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (fun t : ℝ≥0 => η ω t) := by
  set w : Ω → ℝ≥0 → ℝ := fun ω => Sec5.CfRegQ.hDrv (Sec5.Cond44Ref.cfHistory W' ζ' ω) with hw
  have hwm : Measurable w := Sec5.CfRegQ.measurable_hDrv.comp (Sec5.Cond44Ref.measurable_cfHistory
    (Sec5.Cond44Ref.isMeasurableKilledDriving_of_isCenteredCounterflowDriver hS.counterflow))
  have hwe : ∀ᵐ ω ∂P, Continuous (fun t => W' t ω) ∧ W' 0 ω = 0 ∧
      (∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W' t ω) ⊤ η) ∧ w ω = fun t => W' t ω := by
    filter_upwards [StripPocketPath.ae_counterflow_trace hS hcumL hcumR] with ω hω
    obtain ⟨hζ, hc, h0, η, hη⟩ := hω
    refine ⟨hc, h0, ⟨η, hη⟩, funext fun t => ?_⟩
    exact WangWu.pathsOfHistory_killedHistory_driver hc.continuousOn (by rw [hζ]; exact ENNReal.coe_lt_top)
  obtain ⟨γ, hc, h0, hH, hm, htr⟩ := exists_traceVersion hwm (by
    filter_upwards [hwe] with ω hω
    obtain ⟨hc, h0, ⟨η, hη⟩, he⟩ := hω
    rw [he]
    exact ⟨hc, h0, η, hη⟩)
  refine ⟨fun ω s => γ ω s.toNNReal, fun ω => ((hc ω).comp continuous_real_toNNReal).continuousOn,
    fun ω t _ => hH ω _, fun ω => by simpa using h0 ω, fun t _ => hm _, ?_⟩
  filter_upwards [htr, hwe] with ω h1 h2
  rw [h2.2.2.2] at h1
  simpa only [Real.toNNReal_coe] using h1

/-- **A version of the wall `α`** of the original family (under `StagedPiecesRegular` of `alphaSpec θ₁`, R51). -/
theorem exists_alphaVersion (hS : StripSys.IsStripSystem κ b jumps P h W' ζ' Es)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {θ₁ : ℝ} (hθ₁ : θ₁ ∈ Icc (-(π / 2)) (π / 2))
    (hRα : StagedPiecesRegular κ b jumps P (StripSys.alphaSpec θ₁) (Es (StripSys.alphaSpec θ₁))) :
    ∃ α : Ω → ℝ≥0 → ℂ, (∀ ω, Continuous (α ω)) ∧ (∀ ω, α ω 0 = 0) ∧ (∀ t, Measurable fun ω => α ω t) ∧
      ∀ᵐ ω ∂P, IsGeneratingTrace (catPath (Es (StripSys.alphaSpec θ₁) 0 ω).1 1
        (Es (StripSys.alphaSpec θ₁) 1 ω).1) ⊤ (α ω) := by
  obtain ⟨hregα, hαe⟩ := regStrip_alpha hS hcumL hcumR hθ₁ hRα
  obtain ⟨γ, hγ, -⟩ := StripWall.exists_isWallVersion_alpha (StripWall.isStripSystem_regStrip hS) hcumL hcumR hθ₁
    hregα
  refine ⟨γ, hγ.continuous, hγ.zero, hγ.measurable, ?_⟩
  filter_upwards [hγ.ae_isGeneratingTrace, hαe] with ω h1 h2
  rw [← h2]
  exact h1

/-- **A version of the wall `β^{(r)}`** of the original family (under `StagedPiecesRegular` of `betaSpec r θ₂`). -/
theorem exists_betaWallVersion (hS : StripSys.IsStripSystem κ b jumps P h W' ζ' Es)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {θ₂ : ℝ} (hθ₂ : θ₂ ∈ Icc (-(π / 2)) (π / 2)) (r : ℝ≥0)
    (hRβ : StagedPiecesRegular κ b jumps P (StripSys.betaSpec r θ₂) (Es (StripSys.betaSpec r θ₂))) :
    ∃ L : Ω → ℝ≥0 → ℂ, (∀ ω, Continuous (L ω)) ∧ (∀ ω, L ω 0 = 0) ∧ (∀ t, Measurable fun ω => L ω t) ∧
      ∀ᵐ ω ∂P, IsGeneratingTrace (catPath (Es (StripSys.betaSpec r θ₂) 0 ω).1 r
        (Es (StripSys.betaSpec r θ₂) 1 ω).1) ⊤ (L ω) := by
  obtain ⟨hregβ, hβe⟩ := regStrip_beta hS hcumL hcumR hθ₂ r hRβ
  obtain ⟨γ, hγ, -⟩ := StripWall.exists_isWallVersion_beta (StripWall.isStripSystem_regStrip hS) hcumL hcumR hθ₂ r
    hregβ
  refine ⟨γ, hγ.continuous, hγ.zero, hγ.measurable, ?_⟩
  filter_upwards [hγ.ae_isGeneratingTrace, hβe] with ω h1 h2
  rw [← h2]
  exact h1

open scoped Classical in
/-- **Versions of the walls `β^{(q)}`, `q ∈ ℚ`, `q > 0`, as one family** (the `Lr` of STRIPSYS31; `0` for `q ≤ 0`). -/
theorem exists_LrVersion (hS : StripSys.IsStripSystem κ b jumps P h W' ζ' Es)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {θ₂ : ℝ} (hθ₂ : θ₂ ∈ Icc (-(π / 2)) (π / 2))
    (hRβ : ∀ q : ℚ, 0 < q → StagedPiecesRegular κ b jumps P (StripSys.betaSpec (StripSys.rt q) θ₂)
      (Es (StripSys.betaSpec (StripSys.rt q) θ₂))) :
    ∃ Lr : ℚ → Ω → ℝ≥0 → ℂ, (∀ q ω, Continuous (Lr q ω)) ∧ (∀ q ω, Lr q ω 0 = 0) ∧
      (∀ q t, Measurable fun ω => Lr q ω t) ∧
      ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, IsGeneratingTrace (catPath (Es (StripSys.betaSpec (StripSys.rt q) θ₂) 0 ω).1
        (StripSys.rt q) (Es (StripSys.betaSpec (StripSys.rt q) θ₂) 1 ω).1) ⊤ (Lr q ω) := by
  choose V hV using fun (q : ℚ) (hq : 0 < q) =>
    exists_betaWallVersion hS hcumL hcumR hθ₂ (StripSys.rt q) (hRβ q hq)
  refine ⟨fun q => if hq : 0 < q then V q hq else fun _ _ => 0, fun q ω => ?_, fun q ω => ?_, fun q t => ?_,
    fun q hq => ?_⟩
  · by_cases hq : 0 < q
    · simp only [hq, ↓reduceDIte]; exact (hV q hq).1 ω
    · simp only [hq, ↓reduceDIte]; exact continuous_const
  · by_cases hq : 0 < q
    · simp only [hq, ↓reduceDIte]; exact (hV q hq).2.1 ω
    · simp only [hq, ↓reduceDIte]
  · by_cases hq : 0 < q
    · simp only [hq, ↓reduceDIte]; exact (hV q hq).2.2.1 t
    · simp only [hq, ↓reduceDIte]; exact measurable_const
  · simp only [hq, ↓reduceDIte]
    exact (hV q hq).2.2.2

end Versions

end InteractingSLE.Sec7.StripPocketVersions
