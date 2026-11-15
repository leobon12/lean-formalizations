/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.StripWallStage0

/-!
# The side heights of a two-angle strip wall at rational stops (both pieces)

Packet PROVE-STRIPSYS27, second item. Specification §7.4, proof of Aux. lemma 119 (`source/spec/p385-432.md` L33,
p. 386: "the own height `λ − θ_Lχ` on a right side of the left path, and `−λ − θ_Rχ` on a left side of the right
path"), for the walls `α = η^{1,∞}_{−π/2,θ₁}`, `β^{(r)} = η^{r,∞}_{π/2,θ₂}` of (RS13.1), each a staged history `E` of
the two-angle program `StripSys.twoAngleSpec θ₀ t₀ θ`, read through a version `γ` of its trace (a generating trace of
the concatenated driver `catPath (E 0).1 t₀ (E 1).1` on `[0, ∞)`).

* `IsDetTwoPiece P h E`: both pieces almost surely have infinite lifetime and are Borel functions of the field — the
  conclusion of PROVE-STRIPSYS21's `StripDet.exists_borel_drivers`, which proves it for an **increasing** change
  `θ₀ ≤ θ ≤ θ₀ + π` (the wall `α`; `isDetTwoPiece_of_heights`). The decreasing change of `β^{(r)}`
  (`θ₀ − π ≤ θ ≤ θ₀`, "the reflected condition", p. 410) is `isDetTwoPiece_of_heights_refl`
  (`Spec/Sec7/StripWallInputsReflDet`);
* `IsDetTwoPiece.hdet`: Lemma 6.2's determination input for every version of the wall (PROVE-STRIPSYS21's
  `hdet_of_trace`, from the predicate);
* **`ae_sideHeights_second`**: the side heights of angle `θ` after the change, at every rational stop `q > t₀`
  (`RS133.ae_sideHeights_stage` at `r = q − t₀`; the good event from the infinite lifetimes, the driver identity from
  the records);
* **`ae_sideHeights_wall`**: both pieces at once, in the form `hsideL`/`hsideR` of
  `Aux119Heights.ae_eqOn_changePocket_of_sideHeights` (`Aux119Heights.ae_sideHeights_rat_of_stages` with
  `ae_sideHeights_first`).

No Theorem 1.2/1.3 (R43, R48). Conditional helpers; they replace no source theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Function
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Sec7

namespace StripWall

open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)
open StripSideHeightProb
open Exist.Staged (IsRegularDriver)
open Exist.StagedLaw (recOf)
open SupercriticalConformalCovariance.GM24 (smoothDist)

section Det

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {θ₀ θ : ℝ} {t₀ : ℝ≥0}
  {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
/-- **Both pieces of a two-piece staged path are Borel functions of the field with infinite lifetimes** (the
conclusion of `StripDet.exists_borel_drivers`): Borel maps `D₀`, `D₁` to regular drivers with, almost surely,
`E 0 = D₀(h)`, `E 1 = D₁(h)`, both lifetimes `⊤`. -/
def IsDetTwoPiece (P : Measure Ω) (h : Ω → DistOn upperHalfPlaneOpens) (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) :
    Prop :=
  ∃ D₀ D₁ : DistOn upperHalfPlaneOpens → (ℝ≥0 → ℝ) × ℝ≥0∞, Measurable D₀ ∧ Measurable D₁ ∧
    (∀ f, IsRegularDriver (D₀ f)) ∧ (∀ f, IsRegularDriver (D₁ f)) ∧
    ∀ᵐ ω ∂P, (E 0 ω).2 = ⊤ ∧ (E 1 ω).2 = ⊤ ∧ E 0 ω = D₀ (h ω) ∧ E 1 ω = D₁ (h ω)

/-- **An increasing angle change is field determined** (PROVE-STRIPSYS21, R48-safe): for (4.4) heights of `b` at
both angles and `θ₀ ≤ θ ≤ θ₀ + π` (the wall `α`, `θ₀ = −π/2`). -/
theorem isDetTwoPiece_of_heights (h44 : AdmCode.Theorem12ParamCond44Statement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    (hE : IsStagedHistory κ b jumps P h (StripSys.twoAngleSpec θ₀ t₀ θ) E) (hreg : ∀ j ω, IsRegularDriver (E j ω))
    (hL0 : ∀ y : ℝ, y < 0 → y ∉ jumps → b y + θ₀ * chiC κ ≤ -sleLambda κ + Real.pi * chiC κ)
    (hR0 : ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + θ₀ * chiC κ)
    (hL : ∀ y : ℝ, y < 0 → y ∉ jumps → b y + θ * chiC κ ≤ -sleLambda κ + Real.pi * chiC κ)
    (hR : ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + θ * chiC κ) (hθ : θ₀ ≤ θ)
    (hθπ : θ ≤ θ₀ + Real.pi) : IsDetTwoPiece P h E :=
  StripDet.exists_borel_drivers h44 hκ hκ4 hb hh hE hreg hL0 hR0 hL hR hθ hθπ

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
theorem IsDetTwoPiece.ae_lifetimes (hD : IsDetTwoPiece P h E) :
    ∀ᵐ ω ∂P, (E 0 ω).2 = ⊤ ∧ (E 1 ω).2 = ⊤ := by
  obtain ⟨_, _, -, -, -, -, hD'⟩ := hD
  filter_upwards [hD'] with ω hω
  exact ⟨hω.1, hω.2.1⟩

/-- A regular driver with infinite lifetime is continuous. -/
theorem continuous_of_isRegularDriver {e : (ℝ≥0 → ℝ) × ℝ≥0∞} (he : IsRegularDriver e) (h2 : e.2 = ⊤) :
    Continuous e.1 := by
  have := he.1
  rw [h2] at this
  exact continuousOn_univ.1 (by simpa using this)

/-- The concatenated driver of two regular drivers with infinite lifetimes is continuous and starts at `0`. -/
theorem continuous_catPath_of_isRegularDriver {e₀ e₁ : (ℝ≥0 → ℝ) × ℝ≥0∞} (h₀ : IsRegularDriver e₀)
    (h₁ : IsRegularDriver e₁) (h₀2 : e₀.2 = ⊤) (h₁2 : e₁.2 = ⊤) (T : ℝ≥0) :
    Continuous (catPath e₀.1 T e₁.1) ∧ catPath e₀.1 T e₁.1 0 = 0 :=
  ⟨continuous_catPath (continuous_of_isRegularDriver h₀ h₀2) (continuous_of_isRegularDriver h₁ h₁2) h₁.2.1,
    catPath_zero h₀.2.1⟩

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
/-- **Lemma 6.2's determination input for a version of the wall** (PROVE-STRIPSYS21's `hdet_of_trace`, from
`IsDetTwoPiece`): every path that is almost surely a generating trace of the concatenated driver on `[0, ∞)` is, at
every time, almost surely a Borel function of the centred field. -/
theorem IsDetTwoPiece.hdet (hD : IsDetTwoPiece P h E) (hreg : ∀ j ω, IsRegularDriver (E j ω)) (u₀ : ℂ → ℝ)
    {γ : Ω → ℝ≥0 → ℂ} (htr : ∀ᵐ ω ∂P, IsGeneratingTrace (catPath (E 0 ω).1 t₀ (E 1 ω).1) ⊤ (γ ω)) :
    ∀ t : ℝ≥0, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => γ ω t) =ᵐ[P] fun ω => f (WholeField.centredField h u₀ ω) := by
  obtain ⟨D₀, D₁, hD₀, hD₁, -, -, hD⟩ := hD
  intro t
  set c : DistOn upperHalfPlaneOpens := smoothDist upperHalfPlaneOpens u₀ with hc
  have hadd : Measurable fun g : DistOn upperHalfPlaneOpens => g + c := Coupling.measurable_add_distOnConst c
  refine ⟨fun g => LP.traceAt t (catPath (D₀ (g + c)).1 t₀ (D₁ (g + c)).1), ?_, ?_⟩
  · exact (LP.measurable_traceAt t).comp ((StripDet.measurable_catPath t₀).comp
      ((measurable_fst.comp (hD₀.comp hadd)).prodMk (measurable_fst.comp (hD₁.comp hadd))))
  · filter_upwards [hD, htr] with ω hω hη
    obtain ⟨h0, h1, e0, e1⟩ := hω
    have hcent : WholeField.centredField h u₀ ω + c = h ω := by
      simp only [WholeField.centredField, hc, sub_add_cancel]
    simp only [hcent, ← e0, ← e1]
    obtain ⟨hcc, hc0⟩ := continuous_catPath_of_isRegularDriver (hreg 0 ω) (hreg 1 ω) h0 h1 t₀
    exact (LP.traceAt_eq_of_isGeneratingTrace hη hcc.continuousOn hc0 ENNReal.coe_lt_top).symm

end Det

/-! ### The second piece -/

section Second

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {θ₀ θ : ℝ} {t₀ : ℝ≥0}
  {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

omit mΩ [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
/-- On the good event, the concatenated driver agrees up to `t₀ + r` with the concatenated record driver of the
stopped program. -/
theorem catPath_eq_catPath_recW (hreg : ∀ j ω, IsRegularDriver (E j ω)) {r : ℝ≥0} {ω : Ω}
    (hω : ω ∈ goodEv κ b jumps θ₀ t₀ θ r E) {s : ℝ≥0} (hs : s ≤ t₀ + r) :
    catPath (E 0 ω).1 t₀ (E 1 ω).1 s =
      catPath (recW (recsTwo κ b jumps θ₀ t₀ θ r E ω 0)) t₀ (recW (recsTwo κ b jumps θ₀ t₀ θ r E ω 1)) s := by
  have e0 : recsTwo κ b jumps θ₀ t₀ θ r E ω 0 = recOf (t₀ : ℝ≥0∞) (E 0 ω) := pastMap_two_zero ω
  have e1 : recsTwo κ b jumps θ₀ t₀ θ r E ω 1 = recOf (r : ℝ≥0∞) (E 1 ω) := pastMap_two_one hω.1
  have hz0 := lt_zeta_zero_of_mem_goodEv hω
  have hz1 := lt_zeta_one_of_mem_goodEv hω
  have hW0 := StripMark.recW_recOf_of_lt (hreg 0 ω) hz0 (StripMark.isDrvGood_recOf_of_lt (hreg 0 ω) hz0)
  have hW1 := StripMark.recW_recOf_of_lt (hreg 1 ω) hz1 (StripMark.isDrvGood_recOf_of_lt (hreg 1 ω) hz1)
  rw [e0, e1]
  unfold catPath
  split_ifs with hst
  · rw [hW0, min_eq_left hst]
  · rw [hW0, hW1, min_self, min_eq_left (tsub_le_iff_left.2 hs)]

/-- **The second-piece side heights of a two-angle wall** (the input `hst1` of
`Aux119Heights.ae_sideHeights_rat_of_stages`): for a version `γ` of the wall with Lemma 6.2's inputs, almost surely
simple (injective, in `ℍ` at positive times), when both pieces almost surely live forever, at every rational stop
`q > t₀` almost surely every harmonic representative of the mean of `γ([0, q]) ∩ ℍ` has the side heights `±λ − θχ`
at every wall point `γ(s) ∈ ℍ`, `t₀ < s < q`, read with the wall driver (`RS133.ae_sideHeights_stage` at
`r = q − t₀`). -/
theorem ae_sideHeights_second (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps)
    (hE : IsStagedHistory κ b jumps P h (StripSys.twoAngleSpec θ₀ t₀ θ) E) (hreg : ∀ j ω, IsRegularDriver (E j ω))
    (hlife : ∀ᵐ ω ∂P, (E 0 ω).2 = ⊤ ∧ (E 1 ω).2 = ⊤) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension b jumps u₀) {γ : Ω → ℝ≥0 → ℂ} (hγc : ∀ ω, Continuous (γ ω))
    (hγ0 : ∀ ω, γ ω 0 = 0) (hγm : ∀ t, Measurable fun ω => γ ω t)
    (hdet : ∀ t : ℝ≥0, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => γ ω t) =ᵐ[P] fun ω => f (WholeField.centredField h u₀ ω))
    (hloc : Sec6.IsEntranceHistoryLocal γ (WholeField.centredField h u₀) P)
    (hver : ∀ᵐ ω ∂P, IsGeneratingTrace (catPath (E 0 ω).1 t₀ (E 1 ω).1) ⊤ (γ ω) ∧ Injective (γ ω) ∧
      ∀ t, 0 < t → γ ω t ∈ H)
    {g : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens}
    (hg : ∀ q : ℝ≥0, LocalSets.IsLocalSetMean (fun ω => γ ω '' Icc 0 q ∩ H) (WholeField.centredField h u₀) P (g q)) :
    ∀ q : ℚ≥0, t₀ < (q : ℝ≥0) → ∀ᵐ ω ∂P, ∀ v : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd v (H \ (γ ω '' Icc 0 (q : ℝ≥0) ∩ H)) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (γ ω '' Icc 0 (q : ℝ≥0) ∩ H) →
        g q ω φ = ∫ z, v z * φ z) →
      ∀ s : ℝ≥0, t₀ < s → s < q → γ ω s ∈ H →
        StripGeom.HasSideHeights κ θ (γ ω) 0 (catPath (E 0 ω).1 t₀ (E 1 ω).1) q (γ ω s) v u₀ := by
  intro q hq
  set r : ℝ≥0 := (q : ℝ≥0) - t₀ with hr
  have e : t₀ + r = q := add_tsub_cancel_of_le hq.le
  have hT : 0 < t₀ + r := by rw [e]; exact lt_of_le_of_lt zero_le hq
  have hgood : ∀ᵐ ω ∂P, ω ∈ goodEv κ b jumps θ₀ t₀ θ r E := by
    filter_upwards [hlife] with ω hω
    refine StripMark.mem_goodEv_of_lt hreg ?_ ?_
    · rw [hω.1]; exact ENNReal.coe_lt_top
    · rw [hω.2]; exact ENNReal.coe_lt_top
  have hW : ∀ᵐ ω ∂P, IsGeneratingTrace (catPath (E 0 ω).1 t₀ (E 1 ω).1) ⊤ (γ ω) ∧
      Continuous (catPath (E 0 ω).1 t₀ (E 1 ω).1) ∧ catPath (E 0 ω).1 t₀ (E 1 ω).1 0 = 0 ∧ Injective (γ ω) ∧
      (∀ t, 0 < t → γ ω t ∈ H) ∧ ∀ s : ℝ≥0, s ≤ t₀ + r →
        catPath (E 0 ω).1 t₀ (E 1 ω).1 s =
          catPath (recW (recsTwo κ b jumps θ₀ t₀ θ r E ω 0)) t₀ (recW (recsTwo κ b jumps θ₀ t₀ θ r E ω 1)) s := by
    filter_upwards [hver, hlife, hgood] with ω hv hl hgd
    obtain ⟨hcc, hc0⟩ := continuous_catPath_of_isRegularDriver (hreg 0 ω) (hreg 1 ω) hl.1 hl.2 t₀
    exact ⟨hv.1, hcc, hc0, hv.2.1, hv.2.2, fun s hs => catPath_eq_catPath_recW hreg hgd hs⟩
  have hg' : LocalSets.IsLocalSetMean (fun ω => γ ω '' Icc 0 (t₀ + r) ∩ H) (WholeField.centredField h u₀) P
      (g q) := by
    rw [e]; exact hg q
  have key := RS133.ae_sideHeights_stage hκ hb hh hE hreg r hT hu₀ hgood hγc hγ0 hγm hdet hloc hW hg'
  rw [e] at key
  filter_upwards [key] with ω hk v hv hrep s hs1 hs2 _
  exact hk v hv hrep s hs1 hs2

/-! ### Both pieces at rational stops -/

/-- **The side heights of a two-angle wall at rational stops, both pieces** (the input `hsideL`/`hsideR` of
`Aux119Heights.ae_eqOn_changePocket_of_sideHeights`, against any other wall `ρ` from `0`): almost surely every wall
point `γ(s)` off `ρ`, `s ≠ t₀`, has a rational stop `q > s` at which every harmonic representative of the mean of
`γ([0, q]) ∩ ℍ` has the side heights of angle `θ₀` (before the change) or `θ` (after). Inputs: the first piece's
(4.4) heights at `θ₀`, infinite lifetimes of both pieces, and a simple version `γ` of the wall with Lemma 6.2's
inputs. -/
theorem ae_sideHeights_wall (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps)
    (hE : IsStagedHistory κ b jumps P h (StripSys.twoAngleSpec θ₀ t₀ θ) E) (hreg : ∀ j ω, IsRegularDriver (E j ω))
    (hL0 : ∀ y : ℝ, y < 0 → y ∉ jumps → b y + θ₀ * chiC κ ≤ -sleLambda κ + Real.pi * chiC κ)
    (hR0 : ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + θ₀ * chiC κ)
    (hlife : ∀ᵐ ω ∂P, (E 0 ω).2 = ⊤ ∧ (E 1 ω).2 = ⊤) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension b jumps u₀) {γ : Ω → ℝ≥0 → ℂ} (hγc : ∀ ω, Continuous (γ ω))
    (hγ0 : ∀ ω, γ ω 0 = 0) (hγm : ∀ t, Measurable fun ω => γ ω t)
    (hdet : ∀ t : ℝ≥0, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => γ ω t) =ᵐ[P] fun ω => f (WholeField.centredField h u₀ ω))
    (hloc : Sec6.IsEntranceHistoryLocal γ (WholeField.centredField h u₀) P)
    (hver : ∀ᵐ ω ∂P, IsGeneratingTrace (catPath (E 0 ω).1 t₀ (E 1 ω).1) ⊤ (γ ω) ∧ Injective (γ ω) ∧
      ∀ t, 0 < t → γ ω t ∈ H)
    {g : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens}
    (hg : ∀ q : ℝ≥0, LocalSets.IsLocalSetMean (fun ω => γ ω '' Icc 0 q ∩ H) (WholeField.centredField h u₀) P (g q))
    {ρ : Ω → ℝ≥0 → ℂ} (hρ0 : ∀ ω, ρ ω 0 = 0) :
    ∀ᵐ ω ∂P, ∀ s : ℝ≥0, γ ω s ∉ range (ρ ω) → s ∉ ({t₀} : Set ℝ≥0) → ∃ q : ℚ≥0, s < q ∧
      ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ (γ ω '' Icc 0 (q : ℝ≥0) ∩ H)) →
        (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (γ ω '' Icc 0 (q : ℝ≥0) ∩ H) →
          g q ω φ = ∫ z, v z * φ z) →
        StripGeom.HasSideHeights κ (if s < t₀ then θ₀ else θ) (γ ω) 0 (catPath (E 0 ω).1 t₀ (E 1 ω).1) q
          (γ ω s) v u₀ := by
  have htrγ : ∀ᵐ ω ∂P, IsGeneratingTrace (catPath (E 0 ω).1 t₀ (E 1 ω).1) ⊤ (γ ω) := hver.mono fun _ h => h.1
  have hγH : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, 0 < s → γ ω s ∈ H := hver.mono fun _ h => h.2.2
  exact Aux119Heights.ae_sideHeights_rat_of_stages (W := fun ω => catPath (E 0 ω).1 t₀ (E 1 ω).1) hγ0 hρ0 hγH
    (ae_sideHeights_first hκ hκ4 hb hh hE hreg hL0 hR0 hu₀ hγc hγ0 hγm hdet hloc htrγ hg)
    (ae_sideHeights_second hκ hb hh hE hreg hlife hu₀ hγc hγ0 hγm hdet hloc hver hg)

end Second

end StripWall

end Sec7

end InteractingSLE
