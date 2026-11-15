/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.CounterflowProbDilation
import InteractingSLE.Spec.Supplement.LPAssembly
import InteractingSLE.Spec.Sec2.TwoSeedLawPath
import InteractingSLE.Spec.Sec2.TwoSeedExistsPath

/-!
# §7.4, Lemma 7.25: finite-time continuity of the both-low two-seed law (the LP11 input)

Packet PROVE-SEC7-D2. Specification §7.4.1, Lemma 7.25 and its proof (`source/spec/p385-432.md` L489–L514,
pp. 413–414), with Aux. lemmas 126–127 (L251–L333, pp. 399–403).

The form used downstream is `LP.Lemma725TraceStatement` (LP4, LP5 and LP11: "Lemma 7.25 already supplies finite-time
trace continuity"): for `κ' > 4` and `ρ^L, ρ^R ∈ (−2, κ'/2 − 4)` every integrated two-seed evolution almost surely
has a continuous generating trace. The source's proof is:

1. Aux. lemmas 130, 119–122, 125 construct, on a positive-probability event, the complete canonical traversal of a
   Jordan pocket with seed weights `(ρ^L, ρ^R)` (RS13.6); Aux. lemma 127 extracts from that kernel family one
   deterministic reference coupling satisfying the hypotheses of Aux. lemma 126 (`Aux126Reference`).
2. Aux. lemma 126, first part (FS11.1)–(FS11.4): a whole-field change of measure removes the distant marks through
   the buffered stop `S_r`; integrated weak uniqueness and the measurable coding of the trace event transfer the
   stopped continuity to every two-seed evolution (`Aux126StoppedTraceStatement`).
3. Aux. lemma 126, "finite-time continuity by dilation of the driving law": dilation gives continuity through every
   `S_R`, and `S_{R_n} ↑ ∞` (**proved**: `Dilation.ae_isGeneratingTrace_of_bufferedStop`).

The two-seed lifetime is infinite almost surely when both weights exceed `−2` ("Both seed weights exceed −2, so the
integrated two-seed evolution has infinite lifetime", p. 401): **proved** here (`ae_lifetime_eq_top_twoSeed`) from
the landed two-seed uniqueness of the angle law (Theorem 2.2, PROVE-SEC2-JAC2) and the divergence of the Jacobi clock
(PROVE-SEC2-JAC3), given the existence of one Jacobi diffusion (`JacobiDiffusionExistsStatement`, the input already
recorded by PROVE-SEC2-JAC3).

## Named inputs (each a `…Statement : Prop`; none is assumed anywhere else)

| Input | Source |
|---|---|
| `JacobiDiffusionExistsStatement` | Theorem 2.2's proof, p. 23 (spec p. 4, "Bessel/Jacobi diffusion theory"); PROVE-SEC2-JAC3 |
| `Lemma725ReferenceStatement` | Lemma 7.25's proof, pp. 413–414, through Aux. lemmas 130, 119–122, 125 and 127 (pp. 395–410) |
| `Aux126StoppedTraceStatement` | Aux. lemma 126's proof, (FS11.1)–(FS11.4) and the measurable trace coding, pp. 399–401 |
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u v

namespace InteractingSLE

namespace Sec7

/-! ### The two-seed lifetime is infinite -/

/-- **Named input (§2): existence of a Jacobi diffusion** (Theorem 2.2's proof, p. 23; the external input
"Bessel/Jacobi diffusion theory", p. 4). The exact proposition left open by PROVE-SEC2-JAC3. -/
def JacobiDiffusionExistsStatement : Prop :=
  ∀ κ a b : ℝ, 0 < κ → 0 < a → 0 < b →
    ∃ (Ω : Type) (mΩ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (𝓗 : Filtration ℝ mΩ) (U : ℝ → Ω → ℝ), Sec2.Jacobi.IsJacobiDiffusion κ a b P 𝓗 U

/-- **The two-seed lifetime is infinite** (Aux. lemma 126, p. 401: "Both seed weights exceed `−2`, so the integrated
two-seed evolution has infinite lifetime"; Theorem 2.2's proof, p. 23). For weights `> −2` the lifetime of an
evolution is the total clock of its logarithmic-clock angle (`Sec2.TwoSeed.lifetime_eq_iSup_clock`), whose path law
is the Jacobi law (`Sec2.TwoSeed.map_toCPathR_eq`), under which the clock diverges almost surely
(`Sec2.Jacobi.IsJacobiDiffusion.ae_tendsto_clock`). -/
theorem ae_lifetime_eq_top_twoSeed {κ : ℝ} (hκ : 0 < κ) {ρL ρR : Fin 1 → ℝ} (hρL : -2 < ρL 0)
    (hρR : -2 < ρR 0) (hJ : JacobiDiffusionExistsStatement) {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
    {VL VR : Fin 1 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hE : IsIntegratedSLEEvolution κ (fun _ => 0) (fun _ => 0) ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ := by
  have ha : 0 < ρL 0 + 2 := by linarith
  have hb : 0 < ρR 0 + 2 := by linarith
  obtain ⟨Ω', mΩ', P', hP', 𝓗, U', hU'⟩ := hJ κ _ _ hκ ha hb
  obtain ⟨U, hU, hUeq⟩ := Sec2.TwoSeed.exists_isJacobiMP_logAngle hE hκ hρL hρR
  have hJ' := hU'.isJacobiMP
  have hmap := Sec2.TwoSeed.map_toCPathR_eq hU hJ' hκ.le (by linarith)
  set S : Set Sec2.TwoSeed.CPathR := {f | Sec2.TwoSeed.totalClock f = ⊤} with hSdef
  have hS : MeasurableSet S := Sec2.TwoSeed.measurable_totalClock (measurableSet_singleton ⊤)
  -- a divergent clock has infinite total clock
  have htop : ∀ f : Sec2.TwoSeed.CPathR, (∀ v, f.1 v ∈ Icc (0 : ℝ) 1) →
      Tendsto (Sec2.TwoSeed.clock f.1) atTop atTop → f ∈ S := by
    intro f h01 hf
    show Sec2.TwoSeed.totalClock f = ⊤
    refine ENNReal.eq_top_of_forall_nnreal_le fun x => ?_
    obtain ⟨N, hN⟩ := eventually_atTop.1 ((tendsto_atTop.1 hf) (x : ℝ))
    obtain ⟨q, hq⟩ := exists_rat_gt N
    refine le_trans ?_ (le_iSup _ q)
    rw [Sec2.TwoSeed.clampU_eq h01, ← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal (hN q hq.le)
  have h' : ∀ᵐ ω' ∂P', Sec2.TwoSeed.toCPathR U' hJ'.continuous ω' ∈ S := by
    filter_upwards [hU'.ae_tendsto_clock hκ.le ha hb] with ω' hω'
    exact htop _ (fun v => hJ'.1 v ω') hω'
  have hP : ∀ᵐ ω ∂P, Sec2.TwoSeed.toCPathR U hU.continuous ω ∈ S := by
    have hm := Sec2.TwoSeed.measurable_toCPathR hU.measurable hU.continuous
    have hm' := Sec2.TwoSeed.measurable_toCPathR hJ'.measurable hJ'.continuous
    have h1 : ∀ᵐ y ∂(P'.map (Sec2.TwoSeed.toCPathR U' hJ'.continuous)), y ∈ S :=
      (ae_map_iff hm'.aemeasurable hS).2 h'
    rw [← hmap] at h1
    exact (ae_map_iff hm.aemeasurable hS).1 h1
  filter_upwards [hP, hUeq, hE.2.2.2.2, hE.1.1.cont] with ω hω hUω hpath hBc
  rw [Sec2.TwoSeed.lifetime_eq_iSup_clock hpath hBc hρL hρR]
  have hfun : Sec2.TwoSeed.logAngle (fun t => W t ω) (fun i t => VL i t ω) (fun i t => VR i t ω) (ζ ω) =
      Sec2.TwoSeed.clampU (Sec2.TwoSeed.toCPathR U hU.continuous ω) := by
    rw [Sec2.TwoSeed.clampU_eq (fun v => hU.1 v ω)]
    funext x
    exact (hUω x).symm
  rw [hfun]
  exact hω

/-! ### The named inputs of Lemma 7.25 -/

/-- **The hypothesis of Aux. lemma 126** (p. 399) for the seed weights `rL, rR`: "one coupling of a canonical
finite-force evolution with a GFF on `ℍ`, with these two total weights at `0⁻, 0⁺` and finitely many other force
marks strictly separated from zero, which satisfies the original optional local-set and outside-filled-hull
specification. Assume its trace is continuous on every finite interval before its continuation threshold and its
stopped driving histories are determined by its whole field. The nonseed marks and their weights are deterministic."
On the frozen carriers: an ordered force word whose first mark on each side sits at the origin with weight `rL`,
`rR` and whose other marks are strictly separated from `0`; a coupling satisfying `IsOptionalHullCoupling`; a
generating trace on `[0, T]` for every `T` before the lifetime; and a Borel field-to-history map
(`LP.IsFieldDeterminedHistory`). -/
def Aux126Reference (κ rL rR : ℝ) : Prop :=
  ∃ (nL nR : ℕ) (xL : Fin (nL + 1) → ℝ) (xR : Fin (nR + 1) → ℝ) (ρL : Fin (nL + 1) → ℝ)
    (ρR : Fin (nR + 1) → ℝ),
    IsOrderedForceWord xL xR ∧ xL 0 = 0 ∧ xR 0 = 0 ∧ (∀ i, i ≠ 0 → xL i < 0) ∧
      (∀ i, i ≠ 0 → 0 < xR i) ∧ ρL 0 = rL ∧ ρR 0 = rR ∧
      ∃ (Ω : Type v) (mΩ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
        (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ)
        (VR : Fin (nR + 1) → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞)
        (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens),
        IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h ∧
          (∀ᵐ ω ∂P, ∀ T : ℝ≥0, (T : ℝ≥0∞) < ζ ω →
            ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) T η) ∧
          LP.IsFieldDeterminedHistory P h W VL VR ζ

/-- **Named input (§7.4): the reference of Lemma 7.25** (Lemma 7.25's proof, pp. 413–414: "Construct the
non-boundary centered counterflow and the two schedules in Aux. lemma 130 … Aux. lemma 125 gives the complete
canonical pair kernel `Q_Θ` … Finally Aux. lemma 127 selects a good deterministic member of this family and applies
Aux. lemma 126"; Aux. lemma 127's conclusion, p. 403: "`Q_{θ_*}` satisfies the hypotheses of Aux. lemma 126"). For
`κ' > 4` and `ρ^L, ρ^R ∈ (−2, κ'/2 − 4)` the hypothesis of Aux. lemma 126 holds with these seed weights. -/
def Lemma725ReferenceStatement : Prop :=
  ∀ κ : ℝ, 4 < κ → ∀ rL rR : ℝ, -2 < rL → rL < κ / 2 - 4 → -2 < rR → rR < κ / 2 - 4 →
    Aux126Reference.{v} κ rL rR

/-- **Named input (§7.4): the stopped two-seed transfer of Aux. lemma 126** (pp. 399–401, "An exact stopped
two-seed coupling", (FS11.1)–(FS11.4), with the measurable coding of the trace event, p. 399: "Existence of a
continuous extension is a countable uniform continuity condition …"; then "Fix any full original two-seed coupling
provided by Theorem 1.1. Its stopped driving marginal at `S_r` agrees with the one just obtained"): from a reference
as in `Aux126Reference`, there is a buffer radius `r > 0` such that every integrated two-seed evolution with the same
seed weights almost surely has a generating trace through its buffered stop `S_r` (FS11.1). -/
def Aux126StoppedTraceStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → ∀ rL rR : ℝ, -2 < rL → -2 < rR → Aux126Reference.{v} κ rL rR →
    ∃ r : ℝ, 0 < r ∧ ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin 1 → ℝ≥0 → Ω → ℝ) (VR : Fin 1 → ℝ≥0 → Ω → ℝ)
      (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
      IsIntegratedSLEEvolution κ LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ →
        ∀ᵐ ω ∂P, ∃ η : ℝ≥0 → ℂ,
          IsGeneratingTrace (fun t => W t ω) (Dilation.bufferedStop r fun t => W t ω) η

/-! ### Lemma 7.25, trace part -/

/-- **Lemma 7.25, finite-time continuity** (p. 413), in the form `LP.Lemma725TraceStatement` used by LP4, LP5 and
LP11: for `κ' > 4` and `ρ^L, ρ^R ∈ (−2, κ'/2 − 4)`, every integrated two-seed evolution almost surely has a continuous
generating trace on `[0, ζ]` (here `ζ = ∞` almost surely). Assembled from the reference (Aux. lemmas 130, 125, 127),
the stopped transfer of Aux. lemma 126 and the existence of a Jacobi diffusion; the dilation step of Aux. lemma 126
and the infinite lifetime are proved (`Dilation.ae_isGeneratingTrace_of_bufferedStop`,
`ae_lifetime_eq_top_twoSeed`). -/
theorem lemma725TraceStatement_of_inputs (hJ : JacobiDiffusionExistsStatement)
    (hRef : Lemma725ReferenceStatement.{v}) (h126 : Aux126StoppedTraceStatement.{u, v}) :
    LP.Lemma725TraceStatement.{u} := by
  intro κ hκ rL rR hL hLd hR hRd Ω mΩ P _ 𝓕 W VL VR B ζ hE
  obtain ⟨r, hr, hstop⟩ := h126 κ (by linarith) rL rR hL hR (hRef κ hκ rL rR hL hLd hR hRd)
  have hζ : ∀ᵐ ω ∂P, ζ ω = ⊤ :=
    ae_lifetime_eq_top_twoSeed (ρL := fun _ => rL) (ρR := fun _ => rR) (by linarith) hL hR hJ hE
  exact Dilation.ae_isGeneratingTrace_of_bufferedStop hr hstop hE hζ

/-- **The two-seed inputs of LP10 from Lemma 7.25's inputs** (LP11's proof, p. 488): `LP.isCompleteForceWord_twoSeed`
with `LP.Lemma725TraceStatement` discharged by `lemma725TraceStatement_of_inputs`. -/
theorem isCompleteForceWord_twoSeed_of_inputs (hR7 : LP.TheoremR7TraceStatement.{u})
    (hLP4 : LP.LP4Statement.{u}) (hJ : JacobiDiffusionExistsStatement)
    (hRef : Lemma725ReferenceStatement.{v}) (h126 : Aux126StoppedTraceStatement.{u, v}) {κ : ℝ}
    (hκ : 4 < κ) {rL rR : ℝ} (hL : -2 < rL) (hR : -2 < rR) :
    LP.IsCompleteForceWord.{u} κ LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) :=
  LP.isCompleteForceWord_twoSeed hR7 (lemma725TraceStatement_of_inputs hJ hRef h126) hLP4 hκ hL hR

end Sec7

end InteractingSLE
