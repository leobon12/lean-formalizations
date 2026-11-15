/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.StripPocketPathLate
import InteractingSLE.Spec.Sec7.PocketWordFinal
import InteractingSLE.Spec.Sec7.Aux37Attach

/-!
# Theorem 1.3's pocket word from the strip system

Packet PROVE-STRIPSYS31. Specification §7.4.1, Aux. lemma 130 and Lemma 7.25's proof (`source/spec/p385-432.md`
L401–L515, pp. 408–414); Aux. lemma 37 (`source/spec/p193-240.md` L80–L136, pp. 197–200, repaired by R41).

PROVE-STRIPSYS30's `StripPocketConfig.pocketWordEvolution_of_stripPocket` derives hPW
(`Lemma725Ref.PocketWordEvolution (16/κ) r_L r_R`) from random walls `R = α`, `β = η_{π/2}`, `Lr q = β^{(q)}` and a
random counterflow `η`, through almost sure pathwise inputs. Here those inputs are supplied for the strip system's
paths (versions of the staged histories `alphaSpec θ₁`, `leftExtremalSpec`, `betaSpec (rt q) θ₂` and of the trace of
the centred counterflow driver `W′`):

* `IsSimpleProper` of the three walls (`StripWall.ae_isSimpleProper_alpha/beta`,
  `StripPocketPath.ae_isSimpleProper_leftExtremal`);
* the common prefix `β^{(q)}(q) = β(q)` (`ae_eq_leftExtremal_of_le`);
* (RS13.3)'s late points of `β` off `α` (`ae_late_strip`);
* the counterflow's Loewner trace in the chart `m` (`ae_isLoewnerTrace_counterflow`) and, when the pocket opens at the
  flow seed, its transience (`ae_transient_counterflow`, from Aux. lemma 7 at `κ′ = 16/κ`);
* Aux. lemma 37's attachment constancy, reduced to the exclusion of its countably many rational witnesses
  (`attachmentConstancy_of_noWitness`, `attachmentConstancyInf_of_noWitness`; the reduction of the source's proof,
  `Aux37Attach.exists_rat_attachWitness`).

**`pocketWordEvolution_of_stripSystem`** is hPW with the remaining inputs: Lemma 5.7's reverse visit order of the walls
(with their points visited), the counterflow's non-return to its seed (R59), the non-boundary duality avoidance of
the open left side of `β`, the field-level inputs `PocketUnionPtInput`/`…Inf` (`hin`), Aux. lemma 37's witness
exclusion (the field comparison at one rational witness: marked flat clock, flow-side and counterflow-side germs, which
need the marked couplings of Aux. lemmas 32–36), Aux. lemma 7 at `16/κ` (Zhan's `κ > 4` line), and the R48-safe
determination `AdmCode.Theorem12ParamCond44Statement`.

No Theorem 1.2/1.3, no `Theorem12ParamStatement`/`Theorem13Statement`, no `*_of_param` (R43, R48).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric Function
open QuantumZipper (H Hbar chiC)
open LQGMetric (DistOn IsZeroBoundaryGFF)
open InteractingSLE.WangWu (negInv)
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Sec7.StripPocketPath

open WangWu Lemma71I PocketCoord PocketJordan PocketMarks PocketWordAssembly PocketSeedOpen PocketLeftFrontier
  PocketCoupling StripSideHeightProb
open Exist.Staged (IsRegularDriver)

/-! ### Aux. lemma 37 from its rational witnesses -/

section Attach

variable {R L : ℝ≥0 → ℂ} {r : ℝ≥0} {η : ℝ → ℂ}

/-- **The angle-change points of the pocket arcs** in their arc parameters (bounded case): the right arc
`s ↦ m(R̃(rightLo + s (rightHi − rightLo)))` meets the change point `α(1)` (disc parameter `discTime 1`), the left arc
meets `L(r)` (disc parameter `discTime r`). -/
def chgPts (R L : ℝ≥0 → ℂ) (r : ℝ≥0) : Finset ℝ :=
  {(discTime 1 - rightLo R L r) / (rightHi R L r - rightLo R L r),
    (discTime r - leftLo R L r) / (leftHi R L r - leftLo R L r)}

/-- **The angle-change points of the pocket arms at infinity** in their arm parameters (`v ↦ R̃(rightHi/(1 + v))`). -/
def chgPtsInf (R L : ℝ≥0 → ℂ) (r : ℝ≥0) : Finset ℝ :=
  {rightHi R L r / discTime 1 - 1, leftHi R L r / discTime r - 1}

/-- **A rational witness of attachment progress in the change pocket** ((PFI1), p. 198), on either arc, with its
parameter interval `[v, v₂]` inside one constant-angle piece (off the angle-change points). -/
def IsPocketWitness (R L : ℝ≥0 → ℂ) (r : ℝ≥0) (η : ℝ → ℂ) (s₁ s₂ v v₁ v₂ : ℝ) : Prop :=
  (Aux37Attach.IsAttachWitness η (cfPocket R L r) (cfArcR R L r) (firstHit η (cfArcR R L r 1))
      (firstHit η (cfArcR R L r 0)) s₁ s₂ v v₁ v₂ ∨
    Aux37Attach.IsAttachWitness η (cfPocket R L r) (cfArcL R L r) (firstHit η (cfArcR R L r 1))
      (firstHit η (cfArcR R L r 0)) s₁ s₂ v v₁ v₂) ∧
  ∀ c ∈ chgPts R L r, c ∉ Icc v v₂

/-- **A rational witness of attachment progress in the pocket opening at the flow seed** (the arms to `∞`). -/
def IsPocketWitnessInf (R L : ℝ≥0 → ℂ) (r : ℝ≥0) (η : ℝ → ℂ) (s₁ s₂ v v₁ v₂ : ℝ) : Prop :=
  (Aux37Attach.IsAttachWitnessInf η (cfPocket R L r) (cfArcRInf R L r) (firstHit η (cfArcRInf R L r 0))
      s₁ s₂ v v₁ v₂ ∨
    Aux37Attach.IsAttachWitnessInf η (cfPocket R L r) (cfArcLInf R L r) (firstHit η (cfArcRInf R L r 0))
      s₁ s₂ v v₁ v₂) ∧
  ∀ c ∈ chgPtsInf R L r, c ∉ Icc v v₂

/-- **Aux. lemma 37 in the change pocket from the exclusion of every rational witness** (pathwise): "Any nontrivial
attachment progress yields one of these witnesses." -/
theorem attachmentConstancy_of_noWitness (h : IsChangeConfigInc R L r) (hpos : 0 < rightLo R L r) {W : ℝ → ℝ}
    (trace : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) (hrevR : IsWallReverseVisit R η)
    (hrevL : IsWallReverseVisit L η) (hvisR : IsWallVisited R η)
    (hno : ∀ s₁ s₂ v v₁ v₂ : ℚ, ¬ IsPocketWitness R L r η s₁ s₂ v v₁ v₂) :
    Sec6.AttachmentConstancy η (cfPocket R L r) (cfArcR R L r) (cfArcL R L r) (firstHit η (cfArcR R L r 1))
      (firstHit η (cfArcR R L r 0)) := by
  by_contra hAC
  have hP := h.isReversePocket_of_counterflow (zero_notMem_closure_of_rightLo_pos h hpos) trace hW hW0 hrevR hrevL
    hvisR
  obtain ⟨A, hA, s₁, s₂, v, v₁, v₂, hw, hB⟩ := Aux37Attach.exists_rat_attachWitness hP (chgPts R L r) hAC
  refine hno s₁ s₂ v v₁ v₂ ⟨?_, hB⟩
  rcases hA with rfl | rfl
  · exact Or.inl hw
  · exact Or.inr hw

/-- **Aux. lemma 37 in the pocket opening at the flow seed from the exclusion of every rational witness**
(pathwise). -/
theorem attachmentConstancyInf_of_noWitness (h : IsChangeConfigInc R L r) (h0 : rightLo R L r = 0) {W : ℝ → ℝ}
    (trace : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) (hrevR : IsWallReverseVisit R η)
    (hrevL : IsWallReverseVisit L η) (hvisR : IsWallVisited R η) (hvisL : IsWallVisited L η)
    (hno : ∀ s₁ s₂ v v₁ v₂ : ℚ, ¬ IsPocketWitnessInf R L r η s₁ s₂ v v₁ v₂) :
    Sec6.AttachmentConstancyInf η (cfPocket R L r) (cfArcRInf R L r) (cfArcLInf R L r)
      (firstHit η (cfArcRInf R L r 0)) := by
  by_contra hAC
  have hP := h.isReversePocketInf_of_counterflow h0 trace hW hW0 hrevR hrevL hvisR hvisL
  obtain ⟨A, hA, s₁, s₂, v, v₁, v₂, hw, hB⟩ := Aux37Attach.exists_rat_attachWitnessInf hP (chgPtsInf R L r) hAC
  refine hno s₁ s₂ v v₁ v₂ ⟨?_, hB⟩
  rcases hA with rfl | rfl
  · exact Or.inl hw
  · exact Or.inr hw

end Attach

/-! ### The counterflow's transience -/

section Transient

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ}
  {ζ' : Ω → ℝ≥0∞} {Es : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- **The strip system's counterflow is transient in the chart `m`** (Aux. lemma 7 at `κ′ = 16/κ` for its admissible
word, Remark 4.8 (b)): every version `η` of its trace tends to `∞` almost surely. -/
theorem ae_transient_counterflow (haux7 : Sec4.Aux7Statement.{u} (16 / κ))
    (hS : StripSys.IsStripSystem κ b jumps P h W' ζ' Es)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {η : Ω → ℝ → ℂ} (hηtr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (fun t : ℝ≥0 => η ω t)) :
    ∀ᵐ ω ∂P, Tendsto (fun t => ‖η ω t‖) atTop atTop := by
  have hκ := hS.kappa_pos
  have hb := hS.boundaryData
  obtain ⟨h', -, hfl⟩ := Theorem14.GW2Cone.isFlowLineDriver_counterflowData hκ hb hS.gff hS.counterflow
  obtain ⟨h'', 𝓕₂, VL₂, VR₂, B₂, -, hC'⟩ := hfl
  have hk' : 0 < 16 / κ := by positivity
  have hbd := counterflowData_bounds_off hκ (g := b) (J := jumps)
    (fun x hx hxJ => by have := hcumL _ StripSys.neg_pi_div_two_mem_Icc x hx hxJ; linarith)
    (fun x hx hxJ => by have := hcumR _ StripSys.pi_div_two_mem_Icc x hx hxJ; linarith)
  have hadm := Sec4.hasAdmissiblePartialSums_flowLine hk'
    (StripSysField.isPiecewiseConstant_counterflowData κ hb) hbd.1 hbd.2
  have hF' := Theorem15.isOrderedForceWord_flowLine (StripSysField.counterflowData κ b)
    (StripSysField.counterflowJumps jumps) 0
  filter_upwards [haux7 _ _ _ _ P 𝓕₂ W' VL₂ VR₂ B₂ ζ' hF' hadm hC'.1, hηtr] with ω hω hη
  have h1 := hω.2.2 _ hη
  have h2 : Tendsto (fun t : ℝ => ‖η ω (t.toNNReal : ℝ)‖) atTop atTop := h1.comp tendsto_real_toNNReal_atTop
  refine h2.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  rw [Real.coe_toNNReal _ ht]

end Transient

/-! ### hPW from the strip system -/

/-- **hPW from the strip system** (Aux. lemma 130 and Lemma 7.25's proof, pp. 408–414): for the strip system of a GFF
`h` (`0 < κ < 4`, Aux. lemma 130's heights `hcumL`, `hcumR`), angles `θ₁ ∈ (−π/2, π/2)`, `θ₂ ∈ [−π/2, π/2]`, and seed
weights `r_L, r_R ∈ (−2, κ′/2 − 4)` (`κ′ = 16/κ`), `Lemma725Ref.PocketWordEvolution κ′ r_L r_R` holds, given versions
of the paths — `α` of `alphaSpec θ₁`, `β = η_{π/2}` of `leftExtremalSpec`, `Lr q = β^{(q)}` of `betaSpec (rt q) θ₂`
(continuous, `0` at `0`, almost surely generating traces of their drivers; the walls `α`, `Lr q` measurable at fixed
times for `𝓦`) and `η` of the trace of the counterflow driver `W′` (continuous on `[0, ∞)` in `ℍ̄` from `0`, measurable
at fixed times) — and the remaining inputs:

* `hwalls`, `hwallsL` — Lemma 5.7: the walls `α`, `β`, `β^{(q)}` are visited by the counterflow in reverse order, every
  point after the seed visited;
* `hnohit` — the counterflow does not return to its seed (R59, `GW4Ident.CounterflowNoReturnStatement`);
* `hav` — non-boundary duality: the counterflow avoids the open left side of `β` (`β` is the left frontier);
* `hwit`, `hwitI` — Aux. lemma 37's exclusion of each rational witness (the field comparison at one witness);
* `hin` — the field-level pocket inputs `PocketUnionPtInput`/`…Inf` for every walls-measurable configuration event;
* `h44` — the R48-safe word-measurable determination for (4.4) words (from the §4.2 reference);
* `haux7` — Aux. lemma 7 at `κ′ = 16/κ` (used only for the transience of the counterflow when the pocket opens at the
  flow seed). -/
theorem pocketWordEvolution_of_stripSystem {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u}
    {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    {Es : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (h44 : AdmCode.Theorem12ParamCond44Statement.{u}) (haux7 : Sec4.Aux7Statement.{u} (16 / κ))
    (hS : StripSys.IsStripSystem κ b jumps P h W' ζ' Es)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {θ₁ θ₂ : ℝ} (hθ₁ : θ₁ ∈ Ioo (-(π / 2)) (π / 2)) (hθ₂ : θ₂ ∈ Icc (-(π / 2)) (π / 2))
    {rL rR : ℝ} (hL : -2 < rL) (hLd : rL < 16 / κ / 2 - 4) (hRr : -2 < rR) (hRd : rR < 16 / κ / 2 - 4)
    (hregα : ∀ j ω, IsRegularDriver (Es (StripSys.alphaSpec θ₁) j ω))
    (hregβ : ∀ q : ℚ, 0 < q → ∀ j ω, IsRegularDriver (Es (StripSys.betaSpec (StripSys.rt q) θ₂) j ω))
    (hregE : ∀ ω, IsRegularDriver (Es StripSys.leftExtremalSpec 0 ω)) (h𝓦 : 𝓦 ≤ mΩ)
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
  have hκ := hS.kappa_pos
  have hκ4 := hS.kappa_lt_four
  have hκ' : 4 < 16 / κ := by rw [lt_div_iff₀ hκ]; linarith
  have e16 : 16 / (16 / κ) = κ := by field_simp
  have hθ₁c : θ₁ ∈ Icc (-(π / 2)) (π / 2) := Ioo_subset_Icc_self hθ₁
  have hαm' : ∀ t, Measurable fun ω => α ω t := fun t => (hαm t).mono h𝓦 le_rfl
  have htrace := ae_isLoewnerTrace_counterflow hS hcumL hcumR hηtr
  have htrans := ae_transient_counterflow haux7 hS hcumL hcumR hηtr
  have hαsp := StripWall.ae_isSimpleProper_alpha hS hcumL hcumR hθ₁c hregα hαc hα0 hαtr
  have hβsp := ae_isSimpleProper_leftExtremal hS hcumL hcumR hregE hβc hβ0 hβtr
  have hR : ∀ᵐ ω ∂P, IsSimpleProper (α ω) ∧ IsWallReverseVisit (α ω) (η ω) ∧ IsWallVisited (α ω) (η ω) := by
    filter_upwards [hαsp, hwalls] with ω h1 h2 using ⟨h1, h2.1, h2.2.1⟩
  have hβ : ∀ᵐ ω ∂P, IsSimpleProper (β ω) ∧ IsWallReverseVisit (β ω) (η ω) ∧ IsWallVisited (β ω) (η ω) := by
    filter_upwards [hβsp, hwalls] with ω h1 h2 using ⟨h1, h2.2.2.1, h2.2.2.2⟩
  have hLw : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, IsSimpleProper (Lr q ω) ∧ IsWallReverseVisit (Lr q ω) (η ω) ∧
      Lr q ω (StripSys.rt q) = β ω (StripSys.rt q) := fun q hq => by
    filter_upwards [StripWall.ae_isSimpleProper_beta hS hcumL hcumR hθ₂ (StripSys.rt q) (hregβ q hq) (hLc q) (hL0 q)
      (hLtr q hq), hwallsL q hq,
      ae_eq_leftExtremal_of_le h44 hS hcumL hcumR hθ₂ (StripSys.rt q) (hregβ q hq 0) (hLtr q hq) hβtr]
      with ω h1 h2 h3
    exact ⟨h1, h2.1, h3 _ le_rfl⟩
  have hlate := ae_late_strip h44 hS hcumL hcumR hθ₁ hregα hregE hαc hα0 hαm' hαtr hβc hβ0 hβm hβtr hηc hwalls
  have hattach : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, IsChangeConfigInc (α ω) (Lr q ω) (StripSys.rt q) →
      0 < rightLo (α ω) (Lr q ω) (StripSys.rt q) →
      Sec6.AttachmentConstancy (η ω) (cfPocket (α ω) (Lr q ω) (StripSys.rt q))
        (cfArcR (α ω) (Lr q ω) (StripSys.rt q)) (cfArcL (α ω) (Lr q ω) (StripSys.rt q))
        (firstHit (η ω) (cfArcR (α ω) (Lr q ω) (StripSys.rt q) 1))
        (firstHit (η ω) (cfArcR (α ω) (Lr q ω) (StripSys.rt q) 0)) := fun q hq => by
    have hw : ∀ᵐ ω ∂P, ∀ s₁ s₂ v v₁ v₂ : ℚ, IsChangeConfigInc (α ω) (Lr q ω) (StripSys.rt q) →
        0 < rightLo (α ω) (Lr q ω) (StripSys.rt q) →
          ¬ IsPocketWitness (α ω) (Lr q ω) (StripSys.rt q) (η ω) s₁ s₂ v v₁ v₂ := by
      simp only [ae_all_iff]
      exact hwit q hq
    filter_upwards [htrace, hwalls, hwallsL q hq, hw] with ω htr hwl hwL hwω hconf hpos
    exact attachmentConstancy_of_noWitness hconf hpos htr.1 htr.2.1 htr.2.2 hwl.1 hwL.1 hwl.2.1
      fun s₁ s₂ v v₁ v₂ => hwω s₁ s₂ v v₁ v₂ hconf hpos
  have hattachI : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, IsChangeConfigInc (α ω) (Lr q ω) (StripSys.rt q) →
      rightLo (α ω) (Lr q ω) (StripSys.rt q) = 0 →
      Tendsto (fun t => ‖η ω t‖) atTop atTop ∧ IsWallVisited (Lr q ω) (η ω) ∧
        Sec6.AttachmentConstancyInf (η ω) (cfPocket (α ω) (Lr q ω) (StripSys.rt q))
          (cfArcRInf (α ω) (Lr q ω) (StripSys.rt q)) (cfArcLInf (α ω) (Lr q ω) (StripSys.rt q))
          (firstHit (η ω) (cfArcRInf (α ω) (Lr q ω) (StripSys.rt q) 0)) := fun q hq => by
    have hw : ∀ᵐ ω ∂P, ∀ s₁ s₂ v v₁ v₂ : ℚ, IsChangeConfigInc (α ω) (Lr q ω) (StripSys.rt q) →
        rightLo (α ω) (Lr q ω) (StripSys.rt q) = 0 →
          ¬ IsPocketWitnessInf (α ω) (Lr q ω) (StripSys.rt q) (η ω) s₁ s₂ v v₁ v₂ := by
      simp only [ae_all_iff]
      exact hwitI q hq
    filter_upwards [htrace, htrans, hwalls, hwallsL q hq, hw] with ω htr htω hwl hwL hwω hconf h0
    exact ⟨htω, hwL.2, attachmentConstancyInf_of_noWitness hconf h0 htr.1 htr.2.1 htr.2.2 hwl.1 hwL.1 hwl.2.1
      hwL.2 fun s₁ s₂ v v₁ v₂ => hwω s₁ s₂ v v₁ v₂ hconf h0⟩
  refine StripPocketConfig.pocketWordEvolution_of_stripPocket (W := fun ω (s : ℝ) => W' s.toNNReal ω) hκ' hL hLd
    hRr hRd h𝓦 hαm hLm hβm hηm hηc hηH hη0 hR hβ hLw hnohit hlate htrace hav hattach hattachI hh₀ 𝔥 ?_
  intro q hq G hGm hPG hG
  rw [e16]
  exact hin q hq G hGm hPG hG

end InteractingSLE.Sec7.StripPocketPath
