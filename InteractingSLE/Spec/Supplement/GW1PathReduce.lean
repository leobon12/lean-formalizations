/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1PathKernel

/-!
# GW1's retargeting: from the conditional pair to the pathwise half

Packet PROVE-GW1-PATH. `GW1PathKernel.ae_kernel_retarget_right` identifies the next-launch driver `U` with the
terminal relative driver `Q` retargeted at `v` **under each regular conditional law**. `GW1Laws.RetargetPathStatement`
asks for the same relation **`P`-almost surely**, in physical coordinates, with the first visit of the next union.
Two steps remain, both deterministic:

1. **Lifting** (ruling R51: the tip relation is not a measurable event). It is enough that the retargeted driver is a
   measurable function of `(Q, v)`, determined by the tip relation: `DetRetargetStatement` (deterministic Loewner
   theory: Schramm–Wilson's coordinate change for one continuous driver, uniqueness of a Loewner driver given its
   hull family, and a Borel construction). Given it, `ae_isRetargetOf_of_kernel` lifts the kernel statement to `P`
   (the event `U = R(Q, v)` at rational times is measurable).
2. **Physical form at the connector**: `ConnectorPhysStatement` (deterministic walk geometry: BW2's first visit of
   the arc `[q, w]` at `w`, by swallowing and the injectivity of the chart on the untouched outward ray, and reading
   the relation through the post-piece chart's boundary extension).

* **`forcedRetargetPath_of_kernel`**: the pathwise half `IsForcedRetargetPath` from the kernel identification and the
  two deterministic statements, for either walk;
* **`retargetPath_right_of_det`**: `RetargetPathStatement`'s conclusion for the right walk from Corollary BR4a,
  Theorems 1.2–1.3 and the two deterministic statements.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.GW1Path

open Exist Exist.StagedLaw Exist.Staged Restart PiecewiseConstantBoundaryData GW1W GW1WalkExit GW1Laws
  GW1RestartPair

/-! ### The two deterministic statements -/

/-- **Named deterministic input: retargeting a regular counterflow driver is a Borel operation, unique when it
exists.** There are a map `R` (jointly measurable in the path, for the product σ-algebra, and the target point) and a
measurable set `G` such that, for every regular counterflow driver path `Q` (`IsRegCf`): `(Q, v) ∈ G` iff `v ≠ 0` is a
point of `Q`'s trace and some continuous driver retargets `Q` at `v`; and then `R Q v` is continuous and it is the only
continuous driver retargeting `Q` at `v` (`IsRetargetOf U Q v ↔ U = R Q v`). (`G` records existence: for a single
deterministic path the retargeted capacity need not tend to `∞` at the first visit of `v`.) Deterministic content: the
target-change coordinate algebra for one continuous driver up to the first visit of the new target
(`Zhan.Retarget.PullData`), uniqueness of a Loewner driver given its hull family (`GW4Ident.eq_of_fwdHull_eq_comp`), the
Möbius invariance of fillings before disconnection, and a Borel version of these constructions. -/
def DetRetargetStatement : Prop :=
  ∃ (R : (ℝ≥0 → ℝ) → ℝ → ℝ≥0 → ℝ) (G : Set ((ℝ≥0 → ℝ) × ℝ)),
    (∀ t, Measurable fun p : (ℝ≥0 → ℝ) × ℝ => R p.1 p.2 t) ∧ MeasurableSet G ∧
    ∀ (Q : ℝ≥0 → ℝ) (v : ℝ), IsRegCf Q →
      ((Q, v) ∈ G ↔ v ≠ 0 ∧ (v : ℂ) ∈ infinitySourceChart.tipSet Q ⊤ ∧
        ∃ U : ℝ≥0 → ℝ, Continuous U ∧ IsRetargetOf U Q v) ∧
      ((Q, v) ∈ G → Continuous (R Q v) ∧
        ∀ U : ℝ≥0 → ℝ, Continuous U → (IsRetargetOf U Q v ↔ U = R Q v))

/-- **Named deterministic input: the retargeting at a walk connector in physical coordinates** (BW2, supplement
p. 615–616; Astra follow-up 5 §4.4: the connector arc `[q, w]` is first visited at `w`). Along a run of a boundary walk
with regular pieces and stage data, at a next launch `2(n+1)` with chart `c`: if a regular counterflow driver `Q`, read
through the post-piece chart `d` and the inversion, never has a tip in the old union, visits `v = postShift`, and `U`
is `Q` retargeted at `v`, then `Q`'s first physical visit of the next union is attained at the first visit time of `v`,
and `U`'s physical tips through `c` are `Q`'s physical tips through `d` at the clock times. -/
def ConnectorPhysStatement : Prop :=
  ∀ (κ : ℝ), 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ (right : Bool) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞), (∀ k, IsRegularDriver (D k)) →
    WalkStageData κ b jumps (if right then -(Real.pi / 2) else Real.pi / 2) right D →
    (∀ k c θ', (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right) D (k + 1)).2.2.2.1 k = some (c, θ') →
      GW1P.PieceRegular (D k).1 (min (instrTime (GW1Z.walkSpec b jumps right) k) (D k).2)) →
    ∀ (n : ℕ) (c : Chart) (θ : ℝ),
      (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right) D (2 * (n + 1) + 1)).2.2.2.1 (2 * (n + 1)) =
        some (c, θ) →
    ∀ U Q : ℝ≥0 → ℝ, IsRegCf Q → Continuous U → U 0 = 0 →
      (∀ r z, ((stChart (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right) D (2 * n + 1))).trans
          infinitySourceChart).tipAt Q r z →
        z ∉ SB.prefixPhysSet κ b jumps (GW1Z.walkSpec b jumps right) D (2 * n + 1)) →
      ((postShift κ b jumps (GW1Z.walkSpec b jumps right) D n : ℝ) : ℂ) ∈ infinitySourceChart.tipSet Q ⊤ →
      IsRetargetOf U Q (postShift κ b jumps (GW1Z.walkSpec b jumps right) D n) →
      ∃ (a : ℝ≥0 → ℝ≥0) (T : ℝ≥0),
        firstTipTime ((stChart (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right) D (2 * n + 1))).trans
          infinitySourceChart) Q (SB.prefixPhysSet κ b jumps (GW1Z.walkSpec b jumps right) D (2 * (n + 1))) = T ∧
        (∃ z ∈ SB.prefixPhysSet κ b jumps (GW1Z.walkSpec b jumps right) D (2 * (n + 1)),
          ((stChart (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right) D (2 * n + 1))).trans
            infinitySourceChart).tipAt Q T z) ∧
        Continuous a ∧ StrictMono a ∧ range a = Iio T ∧
        ∀ r z, (c.trans infinitySourceChart).tipAt U r z ↔
          ((stChart (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right) D (2 * n + 1))).trans
            infinitySourceChart).tipAt Q (a r) z

/-! ### Lifting from the conditional laws -/

/-- The rational times are dense in `ℝ≥0`. -/
theorem denseRange_toNNReal_rat : DenseRange (fun q : ℚ => Real.toNNReal q) :=
  (Function.Surjective.denseRange (fun x : ℝ≥0 => ⟨(x : ℝ), Real.toNNReal_coe⟩)).comp Rat.denseRange_cast
    continuous_real_toNNReal

/-- **The retargeting relation passes from almost every conditional law to `P`**, given the deterministic statement:
the event "`U = R(Q, v)` at rational times, and `(Q, v) ∈ G`" is measurable, holds under almost every conditional law,
hence `P`-almost surely, and implies the relation for continuous `U`. -/
theorem ae_isRetargetOf_of_kernel (hDet : DetRetargetStatement) {Ω : Type*} {𝒢 : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] (h𝒢 : 𝒢 ≤ mΩ)
    {U Q : ℝ≥0 → Ω → ℝ} (hUm : ∀ t, Measurable (U t)) (hQm : ∀ t, Measurable (Q t)) {v : Ω → ℝ}
    (hvm : Measurable v) {L : Set Ω} (hL : MeasurableSet[𝒢] L)
    (hreg : ∀ᵐ ω ∂P, ω ∈ L → IsRegCf (fun t => Q t ω) ∧ Continuous (fun t => U t ω))
    (hker : ∀ᵐ ω₀ ∂P, ω₀ ∈ L → ∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀),
      v ω ≠ 0 ∧ (v ω : ℂ) ∈ infinitySourceChart.tipSet (fun t => Q t ω) ⊤ ∧
        IsRetargetOf (fun t => U t ω) (fun t => Q t ω) (v ω)) :
    ∀ᵐ ω ∂P, ω ∈ L → v ω ≠ 0 ∧ (v ω : ℂ) ∈ infinitySourceChart.tipSet (fun t => Q t ω) ⊤ ∧
      IsRetargetOf (fun t => U t ω) (fun t => Q t ω) (v ω) := by
  obtain ⟨R, G, hRm, hGm, hRG⟩ := hDet
  have hpm : Measurable fun ω => ((fun t => Q t ω), v ω) := (measurable_pi_iff.mpr hQm).prodMk hvm
  set M : Set Ω := ((fun ω => ((fun t => Q t ω), v ω)) ⁻¹' G) ∩
    ⋂ q : ℚ, {ω | U (Real.toNNReal q) ω = R (fun t => Q t ω) (v ω) (Real.toNNReal q)} with hMdef
  have hM : MeasurableSet M :=
    (hpm hGm).inter (MeasurableSet.iInter fun q => measurableSet_eq_fun (hUm _) ((hRm _).comp hpm))
  have hker' : ∀ᵐ ω₀ ∂P, ω₀ ∈ L → ∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀), ω ∈ M := by
    filter_upwards [hker, Sec7.Aux122Disint.ae_ae_condExpKernel h𝒢 hreg,
      Sec7.Aux122Disint.ae_ae_condExpKernel_mem (P := P) h𝒢 hL] with ω₀ hk hr hmem hω₀
    filter_upwards [hk hω₀, hr, hmem hω₀] with ω hω hrω hωL
    obtain ⟨hv0, hvis, hret⟩ := hω
    obtain ⟨hQr, hUc⟩ := hrω hωL
    have hG := ((hRG _ _ hQr).1).2 ⟨hv0, hvis, _, hUc, hret⟩
    have hUR := (((hRG _ _ hQr).2 hG).2 _ hUc).1 hret
    exact ⟨hG, mem_iInter.2 fun q => congrFun hUR _⟩
  have hP := GW2Later.ae_of_ae_condExpKernel_on' h𝒢 hL hM hker'
  filter_upwards [hP, hreg] with ω hω hr hωL
  obtain ⟨hG, hq⟩ := hω hωL
  rw [mem_iInter] at hq
  obtain ⟨hQr, hUc⟩ := hr hωL
  obtain ⟨hv0, hvis, -⟩ := ((hRG _ _ hQr).1).1 hG
  obtain ⟨hRc, hiff⟩ := (hRG _ _ hQr).2 hG
  have hUR : (fun t => U t ω) = R (fun t => Q t ω) (v ω) := by
    refine Continuous.ext_on denseRange_toNNReal_rat hUc hRc ?_
    rintro _ ⟨q, rfl⟩
    exact hq q
  exact ⟨hv0, hvis, (hiff _ hUc).2 hUR⟩

/-! ### The retained clock keeps the relative tips off the retained set -/

/-- A relative tip under a retained clock is a source tip before the first visit of the retained set, hence not in
it. -/
theorem notMem_of_isRetainedClock {source target : Chart} {W V : ℝ≥0 → ℝ} {A : Set ℂ} {β : ℝ≥0 → ℝ≥0}
    (hβ : IsRetainedClock source target W V A β) {r : ℝ≥0} {z : ℂ} (hz : target.tipAt V r z) : z ∉ A := by
  intro hzA
  have hlt : ((β r : ℝ≥0) : ℝ≥0∞) < firstTipTime source W A := by
    have hm := mem_range_self (f := β) r
    rw [hβ.2.2.1] at hm
    exact hm
  have hle : firstTipTime source W A ≤ (β r : ℝ≥0∞) :=
    iInf₂_le (β r) ⟨z, hzA, (hβ.2.2.2 r z).1 hz⟩
  exact absurd (lt_of_le_of_lt hle hlt) (lt_irrefl _)

/-! ### Assembly -/

section Assembly

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}

/-- **The pathwise half of the forced retargeting from its kernel identification** (either walk), given the two
deterministic statements. The kernel identification is `ae_kernel_retarget_right`'s conclusion (with
`postShift ≠ 0`). -/
theorem forcedRetargetPath_of_kernel (hDet : DetRetargetStatement) (hPhys : ConnectorPhysStatement)
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {right : Bool} {n : ℕ}
    {V : ℝ≥0 → Ω → ℝ} {ζV : Ω → ℝ≥0∞} {ℓ : Ω → ℝ≥0 → ℝ≥0}
    (hdata : RestartData κ b jumps P h W' ζ' E right n V ζV ℓ)
    {Q : ℝ≥0 → Ω → ℝ} {ζQ : Ω → ℝ≥0∞} {β : Ω → ℝ≥0 → ℝ≥0}
    (hQ : IsTerminalRestart κ b jumps P h right (E (GW1Z.walkSpec b jumps right)) n V Q ζQ β)
    {U : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} (hUm : ∀ t, Measurable (U t))
    (hUreg : ∀ᵐ ω ∂P, (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right)
        (fun j => E (GW1Z.walkSpec b jumps right) j ω) (2 * (n + 1) + 1)).2.2.2.1 (2 * (n + 1)) ≠ none →
      ζ ω = ⊤ ∧ Continuous (fun t => U t ω) ∧ U 0 ω = 0)
    (hK : ∀ᵐ ω₀ ∂P,
      (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right) (fun j => E (GW1Z.walkSpec b jumps right) j ω₀)
        (2 * (n + 1) + 1)).2.2.2.1 (2 * (n + 1)) ≠ none →
      postShift κ b jumps (GW1Z.walkSpec b jumps right) (fun j => E (GW1Z.walkSpec b jumps right) j ω₀) n ≠ 0 ∧
      ∀ᵐ ω ∂(condExpKernel P
          (pastSigma κ b jumps (GW1Z.walkSpec b jumps right) (E (GW1Z.walkSpec b jumps right)) (2 * n + 1)) ω₀),
        ((postShift κ b jumps (GW1Z.walkSpec b jumps right) (fun j => E (GW1Z.walkSpec b jumps right) j ω₀) n : ℝ) :
            ℂ) ∈ infinitySourceChart.tipSet (fun t => Q t ω) ⊤ ∧
        IsRetargetOf (fun s => U s ω) (fun s => Q s ω)
          (postShift κ b jumps (GW1Z.walkSpec b jumps right) (fun j => E (GW1Z.walkSpec b jumps right) j ω₀) n)) :
    ∃ a : Ω → ℝ≥0 → ℝ≥0,
      IsForcedRetargetPath κ b jumps P right (E (GW1Z.walkSpec b jumps right)) n Q U ζ a := by
  have hκ := hdata.pos
  have hκ4 := hdata.lt_four
  have hb := hdata.boundary
  have hprog := isBoundaryContinuedProgram_boundaryWalkSpec b jumps (GW1Z.walkAngle_mem_Icc right) right
  have hE := hdata.staged _ hprog
  have hreg := hdata.regular (GW1Z.walkSpec b jumps right)
  have hker : ∀ ω, condExpKernel P (pastSigma κ b jumps (GW1Z.walkSpec b jumps right)
        (E (GW1Z.walkSpec b jumps right)) (2 * (n + 1))) ω =
      condExpKernel P (pastSigma κ b jumps (GW1Z.walkSpec b jumps right)
        (E (GW1Z.walkSpec b jumps right)) (2 * n + 1)) ω :=
    condExpKernel_walk_connector (κ := κ) (b := b) (jumps := jumps)
      (θ := if right then -(Real.pi / 2) else Real.pi / 2) (right := right) P _ n
  have hL := GW1W.measurableSet_pastSigma_launch (κ := κ) hb (GW1Z.walkSpec b jumps right) hE.1 hreg (2 * (n + 1))
  have hvm := measurable_postShift (κ := κ) hb (GW1Z.walkSpec b jumps right) hE.1 hreg n
  -- the recentring amount is constant under the kernel
  have hrunk := ae_ae_run_eq (κ := κ) runMeasStatement hb (GW1Z.walkSpec b jumps right) (k := 2 * (n + 1))
    (fun j _ => hE.1 j) (fun j _ => hreg j) (P := P)
  have hrun1 := ae_ae_run_eq (κ := κ) runMeasStatement hb (GW1Z.walkSpec b jumps right) (k := 2 * n + 1)
    (fun j _ => hE.1 j) (fun j _ => hreg j) (P := P)
  have hkerv : ∀ᵐ ω₀ ∂P,
      (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right) (fun j => E (GW1Z.walkSpec b jumps right) j ω₀)
        (2 * (n + 1) + 1)).2.2.2.1 (2 * (n + 1)) ≠ none →
      ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (GW1Z.walkSpec b jumps right)
          (E (GW1Z.walkSpec b jumps right)) (2 * (n + 1))) ω₀),
        postShift κ b jumps (GW1Z.walkSpec b jumps right) (fun j => E (GW1Z.walkSpec b jumps right) j ω) n ≠ 0 ∧
        ((postShift κ b jumps (GW1Z.walkSpec b jumps right) (fun j => E (GW1Z.walkSpec b jumps right) j ω) n : ℝ) :
          ℂ) ∈ infinitySourceChart.tipSet (fun t => Q t ω) ⊤ ∧
        IsRetargetOf (fun s => U s ω) (fun s => Q s ω)
          (postShift κ b jumps (GW1Z.walkSpec b jumps right) (fun j => E (GW1Z.walkSpec b jumps right) j ω) n) := by
    filter_upwards [hK, hrunk, hrun1] with ω₀ hk h1 h2 hlk
    obtain ⟨hv0, hk'⟩ := hk hlk
    rw [← hker ω₀] at hk' h2
    filter_upwards [hk', h1, h2] with ω hω e1 e2
    have hv : postShift κ b jumps (GW1Z.walkSpec b jumps right) (fun j => E (GW1Z.walkSpec b jumps right) j ω) n =
        postShift κ b jumps (GW1Z.walkSpec b jumps right) (fun j => E (GW1Z.walkSpec b jumps right) j ω₀) n := by
      unfold postShift
      rw [e1, e2]
    rw [hv]
    exact ⟨hv0, hω⟩
  have hregP : ∀ᵐ ω ∂P, ω ∈ {ω | (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right)
        (fun j => E (GW1Z.walkSpec b jumps right) j ω) (2 * (n + 1) + 1)).2.2.2.1 (2 * (n + 1)) ≠ none} →
      IsRegCf (fun t => Q t ω) ∧ Continuous (fun t => U t ω) := by
    filter_upwards [hQ.pathwise, hUreg] with ω hq hu hl
    obtain ⟨-, hQc, hQ0, hγ, -⟩ := hq hl
    exact ⟨⟨hQc, hQ0, hγ⟩, (hu hl).2.1⟩
  have hlift := ae_isRetargetOf_of_kernel hDet (hE.2.1 _) hUm hQ.measurable_driver hvm hL hregP hkerv
  classical
  -- the pathwise clause, with the clock chosen pointwise
  let clause : Ω → (ℝ≥0 → ℝ≥0) → Prop := fun ω a => ∀ c θ,
    (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right) (fun j => E (GW1Z.walkSpec b jumps right) j ω)
      (2 * (n + 1) + 1)).2.2.2.1 (2 * (n + 1)) = some (c, θ) →
    ζ ω = ⊤ ∧ Continuous (fun t => U t ω) ∧ U 0 ω = 0 ∧
    (∃ γ, IsGeneratingTrace (fun t => U t ω) ⊤ γ ∧ Tendsto (fun t => ‖γ t‖) atTop atTop) ∧
    let d := stChart (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right)
      (fun j => E (GW1Z.walkSpec b jumps right) j ω) (2 * n + 1))
    let B := SB.prefixPhysSet κ b jumps (GW1Z.walkSpec b jumps right)
      (fun j => E (GW1Z.walkSpec b jumps right) j ω) (2 * (n + 1))
    ∃ T : ℝ≥0, firstTipTime (d.trans infinitySourceChart) (fun t => Q t ω) B = T ∧
      (∃ z ∈ B, (d.trans infinitySourceChart).tipAt (fun t => Q t ω) T z) ∧
      Continuous a ∧ StrictMono a ∧ range a = Iio T ∧
      ∀ r z, (c.trans infinitySourceChart).tipAt (fun t => U t ω) r z ↔
        (d.trans infinitySourceChart).tipAt (fun t => Q t ω) (a r) z
  refine ⟨fun ω => if hω : ∃ a, clause ω a then Classical.choose hω else fun _ => 0, ?_⟩
  filter_upwards [hlift, hQ.pathwise, hUreg, hdata.stages, hdata.pieces _ hprog] with ω hlω hqω huω hsω hpω
  have hex : ∃ a, clause ω a := by
    by_cases hl : (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right)
        (fun j => E (GW1Z.walkSpec b jumps right) j ω) (2 * (n + 1) + 1)).2.2.2.1 (2 * (n + 1)) = none
    · exact ⟨fun _ => 0, fun c θ hcθ => absurd (hcθ.symm.trans hl) (by simp)⟩
    obtain ⟨⟨c, θ⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hl
    obtain ⟨hv0, hvis, hret⟩ := hlω hl
    obtain ⟨-, hQc, hQ0, hγ, hβ⟩ := hqω hl
    obtain ⟨hζ, hUc, hU0⟩ := huω hl
    have hpieces : ∀ k c' θ', (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right)
        (fun j => E (GW1Z.walkSpec b jumps right) j ω) (k + 1)).2.2.2.1 k = some (c', θ') →
        GW1P.PieceRegular (E (GW1Z.walkSpec b jumps right) k ω).1
          (min (instrTime (GW1Z.walkSpec b jumps right) k) (E (GW1Z.walkSpec b jumps right) k ω).2) :=
      fun k c' θ' hk => hpω k θ' _ c' (eq_launch_of_launches _ _ hk).1 hk
    obtain ⟨a, T, hT, hz, ha1, ha2, ha3, ha4⟩ := hPhys κ hκ hκ4 b jumps hb right
      (fun j => E (GW1Z.walkSpec b jumps right) j ω) (fun k => hreg k ω) hsω hpieces n c θ hcθ
      (fun t => U t ω) (fun t => Q t ω) ⟨hQc, hQ0, hγ⟩ hUc hU0 (fun r z hrz => notMem_of_isRetainedClock hβ hrz)
      hvis hret
    refine ⟨a, fun c' θ' hc' => ?_⟩
    have hcc : (c', θ') = (c, θ) := Option.some_injective _ (hc'.symm.trans hcθ)
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hcc
    exact ⟨hζ, hUc, hU0, hret.1, T, hT, hz, ha1, ha2, ha3, ha4⟩
  intro c θ hcθ
  split_ifs
  exact Classical.choose_spec hex c θ hcθ

/-- **GW1's forced retargeting, pathwise half, for the right walk** from Corollary BR4a (`BR4a.BR4aStatement`, an
existing Theorem 1.4 leaf), Theorems 1.2 (R44 form) and 1.3, and the two deterministic statements: the body of
`GW1Laws.RetargetPathStatement` at `right = true`. -/
theorem retargetPath_right_of_det (hBR4a : BR4a.BR4aStatement.{u})
    (h12p : Exist.Staged.Theorem12ParamStatement.{u}) (hT13 : Exist.Theorem13Statement.{u})
    (hT13₀ : Exist.Theorem13Statement.{0}) (hDet : DetRetargetStatement) (hPhys : ConnectorPhysStatement)
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {n : ℕ}
    {V : ℝ≥0 → Ω → ℝ} {ζV : Ω → ℝ≥0∞} {ℓ : Ω → ℝ≥0 → ℝ≥0}
    (hdata : RestartData κ b jumps P h W' ζ' E true n V ζV ℓ)
    {Q : ℝ≥0 → Ω → ℝ} {ζQ : Ω → ℝ≥0∞} {β : Ω → ℝ≥0 → ℝ≥0}
    (hQ : IsTerminalRestart κ b jumps P h true (E (GW1Z.walkSpec b jumps true)) n V Q ζQ β)
    {U : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hU : IsForcedRetargetCond κ b jumps P h true (E (GW1Z.walkSpec b jumps true)) n U ζ)
    (hUreg : ∀ᵐ ω ∂P, (ExplState.run κ b jumps (GW1Z.walkSpec b jumps true)
        (fun j => E (GW1Z.walkSpec b jumps true) j ω) (2 * (n + 1) + 1)).2.2.2.1 (2 * (n + 1)) ≠ none →
      ζ ω = ⊤ ∧ Continuous (fun t => U t ω) ∧ U 0 ω = 0) :
    ∃ a : Ω → ℝ≥0 → ℝ≥0,
      IsForcedRetargetPath κ b jumps P true (E (GW1Z.walkSpec b jumps true)) n Q U ζ a :=
  forcedRetargetPath_of_kernel hDet hPhys hdata hQ hU.1 hUreg
    ((ae_kernel_retarget_right hBR4a h12p hT13 hT13₀ hdata hQ hU).mono fun _ hk hl =>
      ⟨(hk hl).1.ne', (hk hl).2⟩)

end Assembly

end InteractingSLE.Theorem14.GW1Path
