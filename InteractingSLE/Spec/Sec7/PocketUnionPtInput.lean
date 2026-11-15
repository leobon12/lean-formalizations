/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketUnionPtLaw

/-!
# The pocket inputs `PocketUnionPtInput` / `…Inf` from the ambient-time statements

Packet PROVE-STRIPSYS32. Specification §7.4: Aux. lemmas 124–125 (`source/spec/p385-432.md` L171–L250,
pp. 393–398), Aux. lemma 130's proof and Lemma 7.25's proof (L427–L515, pp. 410–414: "The contained two-arc
mean theorem applies at all enlarged stopping times with the exact inherited lifts. […] the erased counterflow is
therefore a complete continuous traversal of this actual Jordan pocket with a continuous relative driver").

For the change pocket `C = cfPocket R L r` of the walls `R`, `L` in the counterflow chart `m(z) = −1/z`, traversed by
the counterflow `η` with driver `W` (`IsCfPocketConfig`, resp. `IsCfPocketConfigInf` when the pocket opens at the flow
seed), and a Jordan coordinate `ψ` of the pocket, the **ambient counterflow hull at the relative capacity time `q`** is
`stopHull R L r W η ψ q = fwdHull W (T(q))`, `T(q)` the right inverse of the relative clock
(`PocketUnionPtGeom.ambTime`).

* `PocketStopInput`, `PocketStopInputInf`: `PocketUnionPtInput`, `PocketUnionPtInputInf` with the pocket chart law
  `PocketUnionPtChartLaw` replaced by the ambient-time statements `PocketStopChartLaw` (`PocketUnionPtLaw`): the marked
  union law of a set `K_q` at `T(q)` (history-local for the relative history) and the central pocket mean on the
  ambient pocket domain `C ∩ (ℍ ∖ stopHull q)`;
* **`pocketUnionPtInput_of_stopInput`**, **`pocketUnionPtInputInf_of_stopInputInf`**: the field-free part is proved —
  the relative prefix events are measurable (the traversal is measurable at fixed own times: STRIPSYS23's
  `traversalMeasStatement_of_measurable`, `PocketSeedOpen.measurable_travSubInf`), the pocket is open with
  `𝓦`-measurable point events (`PocketTraversalMeasRand.measurableSet_mem_cfPocket`), `ψ` is injective on it, and the
  relative active domain is `ψ(C ∩ (ℍ ∖ stopHull q))` (`PocketUnionPtGeom.image_inter_domain_ambTime(Inf)`);
* **`pocketWordEvolution_of_stopInput'`**: hPW (`Lemma725Ref.PocketWordEvolution`) from a random change pocket and
  the ambient-time inputs of both kinds (STRIPSYS26's `pocketWordEvolution_of_unionPtInput'`).

Conditional helpers; no source theorem is replaced. Ruling R48: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement` or any result taking them as hypotheses.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H fwdHull)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PocketUnionPt

open WangWu Lemma71I PocketCoord PocketJordan PocketMarks PocketTraversal PocketAdapt Lemma71C PocketCoupling
  PocketWordAssembly PocketSeedOpen

section Defs

variable {Ω : Type*}

/-- **The ambient counterflow hull at the relative capacity time `q`** (bounded change pocket): the hull of the
counterflow driver `W` at `T(q)`. -/
def stopHull (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (W : Ω → ℝ → ℝ) (η : Ω → ℝ → ℂ) (ψ : Ω → ℂ → ℂ) (q : ℝ≥0)
    (ω : Ω) : Set ℂ :=
  fwdHull (W ω) (ambTime (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcR (R ω) (L ω) r 1))
    (firstHit (η ω) (cfArcR (R ω) (L ω) r 0)) (ψ ω) q)

/-- **The ambient counterflow hull at the relative capacity time `q`** (change pocket opening at the flow seed). -/
def stopHullInf (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (W : Ω → ℝ → ℝ) (η : Ω → ℝ → ℂ) (ψ : Ω → ℂ → ℂ) (q : ℝ≥0)
    (ω : Ω) : Set ℂ :=
  fwdHull (W ω) (ambTimeInf (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0)) (ψ ω) q)

/-- **The ambient-time pocket inputs on every word-shape event** (bounded change pocket): `PocketUnionPtInput` with
the pocket chart law in its ambient-time form `PocketStopChartLaw` (the marked union law and the central pocket mean
at `T(q)`). -/
def PocketStopInput (κ rL rR : ℝ) (𝓦 : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (W : Ω → ℝ → ℝ) (η : Ω → ℝ → ℂ) (G : Set Ω)
    (h₀ : Ω → DistOn upperHalfPlaneOpens) (𝔥 : DistOn upperHalfPlaneOpens) : Prop :=
  ∀ A : Set Ω, MeasurableSet[𝓦] A → A ⊆ G → 0 < P A → ∀ ψ : Ω → ℂ → ℂ,
    (∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω)) → @IsPointMeasurable Ω 𝓦 R L r G ψ →
    ((∀ ω ∈ A, discTime 1 ∈ Ioo (rightLo (R ω) (L ω) r) (rightHi (R ω) (L ω) r)) →
      PocketStopChartLaw (16 / κ) (wordL2 κ (rs136Theta1 κ rL)) (wordR2 κ (rs136Theta2 κ rR)) 𝓦 P A
        (travAll R L r η ψ) (marksL2All R ψ) (marksRAll L r ψ) (fun ω => cfPocket (R ω) (L ω) r) ψ
        (stopHull R L r W η ψ) h₀ 𝔥) ∧
    ((∀ ω ∈ A, discTime 1 ∉ Ioo (rightLo (R ω) (L ω) r) (rightHi (R ω) (L ω) r)) →
      PocketStopChartLaw (16 / κ) (wordL1 κ (rs136Theta1 κ rL)) (wordR2 κ (rs136Theta2 κ rR)) 𝓦 P A
        (travAll R L r η ψ) marksL1All (marksRAll L r ψ) (fun ω => cfPocket (R ω) (L ω) r) ψ
        (stopHull R L r W η ψ) h₀ 𝔥)

/-- **The ambient-time pocket inputs on every word-shape event** (change pocket opening at the flow seed). -/
def PocketStopInputInf (κ rL rR : ℝ) (𝓦 : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (W : Ω → ℝ → ℝ) (η : Ω → ℝ → ℂ) (G : Set Ω)
    (h₀ : Ω → DistOn upperHalfPlaneOpens) (𝔥 : DistOn upperHalfPlaneOpens) : Prop :=
  ∀ A : Set Ω, MeasurableSet[𝓦] A → A ⊆ G → 0 < P A → ∀ ψ : Ω → ℂ → ℂ,
    (∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω)) → @IsPointMeasurableInf Ω 𝓦 R L r G ψ →
    ((∀ ω ∈ A, discTime 1 ∈ Ioo (rightLo (R ω) (L ω) r) (rightHi (R ω) (L ω) r)) →
      PocketStopChartLaw (16 / κ) (wordL2 κ (rs136Theta1 κ rL)) (wordR2 κ (rs136Theta2 κ rR)) 𝓦 P A
        (travAllInf R L r η ψ) (marksL2All R ψ) (marksRAll L r ψ) (fun ω => cfPocket (R ω) (L ω) r) ψ
        (stopHullInf R L r W η ψ) h₀ 𝔥) ∧
    ((∀ ω ∈ A, discTime 1 ∉ Ioo (rightLo (R ω) (L ω) r) (rightHi (R ω) (L ω) r)) →
      PocketStopChartLaw (16 / κ) (wordL1 κ (rs136Theta1 κ rL)) (wordR2 κ (rs136Theta2 κ rR)) 𝓦 P A
        (travAllInf R L r η ψ) marksL1All (marksRAll L r ψ) (fun ω => cfPocket (R ω) (L ω) r) ψ
        (stopHullInf R L r W η ψ) h₀ 𝔥)

end Defs

section Meas

variable {Ω : Type*} {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]

/-- **The localized relative history is measurable** when the curve is driven on `A` and measurable at fixed own times
on `A` (the prefix events on the subtype, `PocketMeas.measurableSet_prefixEvent`, pushed to `Ω`). -/
theorem locPrefixSigma_le (h𝓦 : 𝓦 ≤ mΩ) {A : Set Ω} (hA : MeasurableSet[𝓦] A) {γ : Ω → ℝ → ℂ}
    (hγ : ∀ ω ∈ A, IsDrivenCurve (γ ω)) (hγm : ∀ u, 0 ≤ u → Measurable fun ω : A => γ ω u) (q : ℝ≥0) :
    locPrefixSigma 𝓦 A γ q ≤ mΩ := by
  refine sup_le h𝓦 (MeasurableSpace.generateFrom_le ?_)
  rintro _ ⟨s, -, n, k, rfl⟩
  have hE := PocketMeas.measurableSet_prefixEvent (γ := fun ω : A => γ ω) (fun ω => hγ ω ω.2) hγm s n k
  have e : A ∩ prefixEvent γ s n k = Subtype.val '' prefixEvent (fun ω : A => γ ω) s n k := by
    ext ω
    constructor
    · rintro ⟨hωA, hω⟩
      exact ⟨⟨ω, hωA⟩, hω, rfl⟩
    · rintro ⟨⟨ω', hω'A⟩, hω', rfl⟩
      exact ⟨hω'A, hω'⟩
  rw [e]
  exact MeasurableSet.subtype_image (h𝓦 _ hA) hE

omit mΩ in
/-- The point events of the pocket on a subevent `A ⊆ G`. -/
theorem measurableSet_mem_cfPocket_of_subset {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0}
    (hRm : ∀ t, Measurable[𝓦] fun ω => R ω t) (hLm : ∀ t, Measurable[𝓦] fun ω => L ω t) {G : Set Ω}
    (hGm : MeasurableSet[𝓦] G) (hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r) {A : Set Ω}
    (hA : MeasurableSet[𝓦] A) (hAG : A ⊆ G) (z : ℂ) :
    MeasurableSet[𝓦] {ω | ω ∈ A ∧ z ∈ cfPocket (R ω) (L ω) r} := by
  have e : {ω | ω ∈ A ∧ z ∈ cfPocket (R ω) (L ω) r} = A ∩ {ω | ω ∈ G ∧ z ∈ cfPocket (R ω) (L ω) r} := by
    ext ω
    exact ⟨fun h => ⟨h.1, hAG h.1, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩
  rw [e]
  exact hA.inter (PocketTraversalMeasRand.measurableSet_mem_cfPocket hRm hLm hGm hG z)

end Meas

section Thms

variable {Ω : Type*} {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {h₀ : Ω → DistOn upperHalfPlaneOpens} {𝔥 : DistOn upperHalfPlaneOpens}

/-- **`PocketUnionPtInput` from the ambient-time inputs** (bounded change pocket). -/
theorem pocketUnionPtInput_of_stopInput [IsProbabilityMeasure P] {κ rL rR : ℝ} (h𝓦 : 𝓦 ≤ mΩ)
    {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} (hRm : ∀ t, Measurable[𝓦] fun ω => R ω t)
    (hLm : ∀ t, Measurable[𝓦] fun ω => L ω t) {G : Set Ω} (hGm : MeasurableSet[𝓦] G) {W : Ω → ℝ → ℝ}
    {η : Ω → ℝ → ℂ} (hcfg : ∀ ω ∈ G, IsCfPocketConfig (R ω) (L ω) r (W ω) (η ω))
    (hηm : ∀ u, 0 ≤ u → Measurable fun ω => η ω u) (hh₀ : IsZeroBoundaryGFF upperHalfPlaneOpens h₀ P)
    (hin : PocketStopInput κ rL rR 𝓦 P R L r W η G h₀ 𝔥) : PocketUnionPtInput κ rL rR 𝓦 P R L r η G h₀ 𝔥 := by
  intro A hA hAG hPA ψ hψ hψm
  have hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r := fun ω hω => (hcfg ω hω).conf
  have hP : ∀ ω ∈ A, Sec6.IsReversePocket (W ω) (η ω) (cfPocket (R ω) (L ω) r) (cfArcR (R ω) (L ω) r)
      (cfArcL (R ω) (L ω) r) (cfBeta (R ω) (L ω) r) (firstHit (η ω) (cfArcR (R ω) (L ω) r 1))
      (firstHit (η ω) (cfArcR (R ω) (L ω) r 0)) := fun ω hω =>
    (hcfg ω (hAG hω)).conf.isReversePocket_of_counterflow
      (zero_notMem_closure_of_rightLo_pos (hcfg ω (hAG hω)).conf (hcfg ω (hAG hω)).bounded)
      (hcfg ω (hAG hω)).trace (hcfg ω (hAG hω)).continuous_W (hcfg ω (hAG hω)).W_zero (hcfg ω (hAG hω)).revR
      (hcfg ω (hAG hω)).revL (hcfg ω (hAG hω)).visR
  have hψ' : ∀ ω ∈ A, Sec6.IsJordanCoord (cfPocket (R ω) (L ω) r) (cfArcR (R ω) (L ω) r 0)
      (cfArcR (R ω) (L ω) r 1) (ψ ω) := fun ω hω => by
    rw [PocketCoord.IsChangeConfigInc.cfArcR_zero, PocketCoord.IsChangeConfigInc.cfArcR_one]
    exact hψ ω hω
  have hpre : ∀ q : ℝ≥0, locPrefixSigma 𝓦 A (travAll R L r η ψ) q ≤ mΩ :=
    locPrefixSigma_le h𝓦 hA (fun ω hω => ((hcfg ω (hAG hω)).isDrivenCurve (hψ ω hω)).1)
      (PocketTraversalMeasRand.traversalMeasStatement_of_measurable h𝓦 hRm hLm hGm hcfg hηm A (h𝓦 _ hA) hAG ψ hψ
        hψm)
  have hCo : ∀ ω ∈ A, IsOpen (cfPocket (R ω) (L ω) r) := fun ω hω => (hP ω hω).isOpen
  have hinj : ∀ ω ∈ A, InjOn (ψ ω) (cfPocket (R ω) (L ω) r) := fun ω hω => (hψ ω hω).2.2.2.1.2.injOn
  have hgeo : ∀ q : ℝ≥0, ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (travAll R L r η ψ ω) →
      ψ ω '' (cfPocket (R ω) (L ω) r ∩ (H \ stopHull R L r W η ψ q ω)) =
        H \ fwdHull (fun s : ℝ => segDriver (travAll R L r η ψ ω) s.toNNReal) q := fun q ω hω hq =>
    image_inter_domain_ambTime (hP ω hω) (hcfg ω (hAG hω)).attach (hψ' ω hω) q.coe_nonneg
      (by rw [ENNReal.ofReal_coe_nnreal]; exact hq)
  obtain ⟨h1, h2⟩ := hin A hA hAG hPA ψ hψ hψm
  exact ⟨fun hs => pocketUnionPtChartLaw_of_stop hA hpre hCo
      (measurableSet_mem_cfPocket_of_subset hRm hLm hGm hG hA hAG) hinj hgeo hh₀ (h1 hs),
    fun hs => pocketUnionPtChartLaw_of_stop hA hpre hCo
      (measurableSet_mem_cfPocket_of_subset hRm hLm hGm hG hA hAG) hinj hgeo hh₀ (h2 hs)⟩

/-- **`PocketUnionPtInputInf` from the ambient-time inputs** (change pocket opening at the flow seed). -/
theorem pocketUnionPtInputInf_of_stopInputInf [IsProbabilityMeasure P] {κ rL rR : ℝ} (h𝓦 : 𝓦 ≤ mΩ)
    {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} (hRm : ∀ t, Measurable[𝓦] fun ω => R ω t)
    (hLm : ∀ t, Measurable[𝓦] fun ω => L ω t) {G : Set Ω} (hGm : MeasurableSet[𝓦] G) {W : Ω → ℝ → ℝ}
    {η : Ω → ℝ → ℂ} (hcfg : ∀ ω ∈ G, IsCfPocketConfigInf (R ω) (L ω) r (W ω) (η ω))
    (hηm : ∀ u, 0 ≤ u → Measurable fun ω => η ω u) (hh₀ : IsZeroBoundaryGFF upperHalfPlaneOpens h₀ P)
    (hin : PocketStopInputInf κ rL rR 𝓦 P R L r W η G h₀ 𝔥) :
    PocketUnionPtInputInf κ rL rR 𝓦 P R L r η G h₀ 𝔥 := by
  intro A hA hAG hPA ψ hψ hψm
  have hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r := fun ω hω => (hcfg ω hω).conf
  have hP : ∀ ω ∈ A, Sec6.IsReversePocketInf (W ω) (η ω) (cfPocket (R ω) (L ω) r) (cfArcRInf (R ω) (L ω) r)
      (cfArcLInf (R ω) (L ω) r) (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0)) := fun ω hω =>
    (hcfg ω (hAG hω)).isReversePocketInf
  have hψ' : ∀ ω ∈ A, Sec6.IsJordanCoordInf (cfPocket (R ω) (L ω) r) (cfArcRInf (R ω) (L ω) r 0) (ψ ω) :=
    fun ω hω => by
      rw [PocketCoord.IsChangeConfigInc.cfArcRInf_zero]
      exact hψ ω hω
  have hpre : ∀ q : ℝ≥0, locPrefixSigma 𝓦 A (travAllInf R L r η ψ) q ≤ mΩ :=
    locPrefixSigma_le h𝓦 hA (fun ω hω => ((hcfg ω (hAG hω)).isDrivenCurve (hψ ω hω)).1)
      fun u hu => measurable_travSubInf h𝓦 hRm hLm hGm hcfg hηm hAG hψ hψm hu
  have hCo : ∀ ω ∈ A, IsOpen (cfPocket (R ω) (L ω) r) := fun ω hω => (hP ω hω).isOpen
  have hinj : ∀ ω ∈ A, InjOn (ψ ω) (cfPocket (R ω) (L ω) r) := fun ω hω => (hψ ω hω).2.2.2.1.2.injOn
  have hgeo : ∀ q : ℝ≥0, ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω) →
      ψ ω '' (cfPocket (R ω) (L ω) r ∩ (H \ stopHullInf R L r W η ψ q ω)) =
        H \ fwdHull (fun s : ℝ => segDriver (travAllInf R L r η ψ ω) s.toNNReal) q := fun q ω hω hq =>
    image_inter_domain_ambTimeInf (hP ω hω) (hcfg ω (hAG hω)).attach (hψ' ω hω) q.coe_nonneg
      (by rw [ENNReal.ofReal_coe_nnreal]; exact hq)
  obtain ⟨h1, h2⟩ := hin A hA hAG hPA ψ hψ hψm
  exact ⟨fun hs => pocketUnionPtChartLaw_of_stop hA hpre hCo
      (measurableSet_mem_cfPocket_of_subset hRm hLm hGm hG hA hAG) hinj hgeo hh₀ (h1 hs),
    fun hs => pocketUnionPtChartLaw_of_stop hA hpre hCo
      (measurableSet_mem_cfPocket_of_subset hRm hLm hGm hG hA hAG) hinj hgeo hh₀ (h2 hs)⟩

end Thms

/-! ### The two canonical choices of the union set -/

section Instances

open QuantumZipper.CA (cayley cayleyInv)

/-- **Aux. lemma 124's `B ∪ R_T`** in `ℍ`: the complement of the pocket together with the counterflow hull. -/
def extHullSet (C F : Set ℂ) : Set ℂ := H ∩ (Cᶜ ∪ F)

/-- **Aux. lemmas 35–36's marked union `A_T = Γ ∪ R_T`** in `ℍ`: the walls in the counterflow chart together with the
counterflow hull. -/
def wallsHullSet (R L : ℝ≥0 → ℂ) (F : Set ℂ) : Set ℂ := H ∩ (negInv '' (range R ∪ range L) ∪ F)

/-- The pathwise clauses of `PocketStopLaw` for Aux. lemma 124's `B ∪ R_T` (for every open pocket and every hull). -/
theorem extHullSet_props {C : Set ℂ} (hC : IsOpen C) (F : Set ℂ) :
    frontier C ∩ H ⊆ extHullSet C F ∧ F ∩ H ⊆ extHullSet C F ∧ extHullSet C F ∩ C ⊆ F := by
  refine ⟨fun z hz => ⟨hz.2, Or.inl ?_⟩, fun z hz => ⟨hz.2, Or.inr hz.1⟩, fun z hz => ?_⟩
  · have := hz.1
    rw [hC.frontier_eq] at this
    exact this.2
  · rcases hz.1.2 with h | h
    · exact absurd hz.2 h
    · exact h

/-- The regularity clause of `PocketStopLaw` for Aux. lemma 124's `B ∪ R_T`: it lies in `ℍ`, with open complement
`C ∩ (ℍ ∖ F)` there, for an open pocket and a hull with open complement in `ℍ`. -/
theorem extHullSet_regular {C F : Set ℂ} (hC : IsOpen C) (hF : IsOpen (H \ F)) :
    extHullSet C F ⊆ H ∧ IsOpen (H \ extHullSet C F) := by
  refine ⟨inter_subset_left, ?_⟩
  have e : H \ extHullSet C F = C ∩ (H \ F) := by
    ext z
    simp only [extHullSet, Set.mem_sdiff, mem_inter_iff, mem_union, mem_compl_iff, not_and, not_or, not_not]
    tauto
  rw [e]
  exact hC.inter hF

/-- **Aux. lemma 124's `B ∪ R_{T(q)}` is regular** for a bounded change pocket traversed by the counterflow: it lies in
`ℍ` and its complement there, the ambient pocket domain, is open. -/
theorem extHullSet_stopHull_regular {Ω : Type*} {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {W : Ω → ℝ → ℝ} {η : Ω → ℝ → ℂ}
    {ω : Ω} (hc : IsCfPocketConfig (R ω) (L ω) r (W ω) (η ω)) (ψ : Ω → ℂ → ℂ) (q : ℝ≥0) :
    extHullSet (cfPocket (R ω) (L ω) r) (stopHull R L r W η ψ q ω) ⊆ H ∧
      IsOpen (H \ extHullSet (cfPocket (R ω) (L ω) r) (stopHull R L r W η ψ q ω)) := by
  have hP := hc.conf.isReversePocket_of_counterflow (zero_notMem_closure_of_rightLo_pos hc.conf hc.bounded) hc.trace
    hc.continuous_W hc.W_zero hc.revR hc.revL hc.visR
  exact extHullSet_regular hP.isOpen (isOpen_H_diff_fwdHull_ambTime hP (ψ ω) q)

/-- **Aux. lemma 124's `B ∪ R_{T(q)}` is regular** for a change pocket opening at the flow seed. -/
theorem extHullSet_stopHullInf_regular {Ω : Type*} {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {W : Ω → ℝ → ℝ}
    {η : Ω → ℝ → ℂ} {ω : Ω} (hc : IsCfPocketConfigInf (R ω) (L ω) r (W ω) (η ω)) (ψ : Ω → ℂ → ℂ) (q : ℝ≥0) :
    extHullSet (cfPocket (R ω) (L ω) r) (stopHullInf R L r W η ψ q ω) ⊆ H ∧
      IsOpen (H \ extHullSet (cfPocket (R ω) (L ω) r) (stopHullInf R L r W η ψ q ω)) := by
  have hP := hc.isReversePocketInf
  exact extHullSet_regular hP.isOpen (isOpen_H_diff_fwdHull_ambTimeInf hP hc.attach (ψ ω) q)

/-- A point of a wall's disc parametrization in the counterflow chart lies on the inverted wall when it is in `ℍ`
(the two ends of the parametrization, the seed `−1 ↦ 0` and the target `1 ↦ 0`, are not in `ℍ`). -/
theorem cfPt_toDisc_mem_negInv {R : ℝ≥0 → ℂ} (hR : IsSimpleProper R) {s : ℝ}
    (hs : cfPt (toDisc (realPath R) s) ∈ H) : cfPt (toDisc (realPath R) s) ∈ negInv '' range R := by
  by_cases hs1 : s < 1
  · rw [toDisc_of_lt hs1] at hs ⊢
    set t := (arcTime s).toNNReal with ht
    have hRt : realPath R (arcTime s) = R t := rfl
    rw [hRt] at hs ⊢
    by_cases ht0 : t = 0
    · exfalso
      rw [ht0, hR.2.2.1] at hs
      simp [cfPt, cayley, cayleyInv, QuantumZipper.H] at hs
    · have hH : R t ∈ H := hR.2.2.2.1 t (pos_iff_ne_zero.2 ht0)
      have hne : R t ≠ 0 := fun h0 => by
        rw [h0] at hH
        simp [QuantumZipper.H] at hH
      rw [cfPt_cayley (show R t ∈ QuantumZipper.Hbar from le_of_lt (show (0:ℝ) < (R t).im from hH)) hne]
      exact mem_image_of_mem _ (mem_range_self t)
  · exfalso
    simp only [toDisc, hs1, ↓reduceIte, cfPt_one] at hs
    simp [QuantumZipper.H] at hs

/-- The pathwise clauses of `PocketStopLaw` for the marked union `m(walls) ∪ R_T`, for a pocket whose frontier is
covered by the disc parametrizations of the two walls in the counterflow chart. -/
theorem wallsHullSet_props {R L : ℝ≥0 → ℂ} {r : ℝ≥0} (h : IsChangeConfigInc R L r)
    (hfr : frontier (cfPocket R L r) ⊆
      (range fun s => cfPt (toDisc (realPath R) s)) ∪ range fun s => cfPt (toDisc (realPath L) s)) (F : Set ℂ) :
    frontier (cfPocket R L r) ∩ H ⊆ wallsHullSet R L F ∧ F ∩ H ⊆ wallsHullSet R L F ∧
      wallsHullSet R L F ∩ cfPocket R L r ⊆ F := by
  refine ⟨fun z hz => ⟨hz.2, Or.inl ?_⟩, fun z hz => ⟨hz.2, Or.inr hz.1⟩, fun z hz => ?_⟩
  · rcases hfr hz.1 with ⟨s, rfl⟩ | ⟨s, rfl⟩
    · obtain ⟨w, hw, he⟩ := cfPt_toDisc_mem_negInv h.right hz.2
      exact ⟨w, Or.inl hw, he⟩
    · obtain ⟨w, hw, he⟩ := cfPt_toDisc_mem_negInv h.left hz.2
      exact ⟨w, Or.inr hw, he⟩
  · rcases hz.1.2 with ⟨w, hw, rfl⟩ | hF
    · exfalso
      obtain ⟨w', hw', he⟩ := hz.2
      have : w' = w := by
        simpa only [negInv, neg_inj, inv_inj] using he
      exact (h.changePocket_subset (this ▸ hw')).2 hw
    · exact hF

/-- The frontier of a bounded change pocket is covered by the walls' disc parametrizations. -/
theorem frontier_cfPocket_subset {R L : ℝ≥0 → ℂ} {r : ℝ≥0} (h : IsChangeConfigInc R L r)
    (h0 : (0 : ℂ) ∉ closure (changePocket R L r)) :
    frontier (cfPocket R L r) ⊆
      (range fun s => cfPt (toDisc (realPath R) s)) ∪ range fun s => cfPt (toDisc (realPath L) s) := by
  rw [(h.isCfPocket h0).frontier_eq]
  rintro _ (⟨s, -, rfl⟩ | ⟨s, -, rfl⟩)
  · exact Or.inl ⟨_, rfl⟩
  · exact Or.inr ⟨_, rfl⟩

/-- The frontier of a change pocket opening at the flow seed is covered by the walls' disc parametrizations. -/
theorem frontier_cfPocket_subset_inf {R L : ℝ≥0 → ℂ} {r : ℝ≥0} (h : IsChangeConfigInc R L r)
    (h0 : rightLo R L r = 0) :
    frontier (cfPocket R L r) ⊆
      (range fun s => cfPt (toDisc (realPath R) s)) ∪ range fun s => cfPt (toDisc (realPath L) s) := by
  rw [(h.isCfPocketInf h0).frontier_eq]
  rintro _ (⟨s, -, rfl⟩ | ⟨s, -, rfl⟩)
  · exact Or.inl ⟨_, rfl⟩
  · exact Or.inr ⟨_, rfl⟩

end Instances

open WangWu Lemma71I PocketCoord PocketJordan PocketMarks in
/-- **hPW from the ambient-time pocket inputs** (`κ′ > 4`, both-low seed weights; Lemma 7.25's proof with Aux. lemmas
119–125 and 130): STRIPSYS26's `pocketWordEvolution_of_unionPtInput'` with the pocket inputs in their ambient-time form
(`PocketStopInput`, `PocketStopInputInf`). -/
theorem pocketWordEvolution_of_stopInput'.{v} {κ' rL rR : ℝ} (hκ' : 4 < κ') (hL : -2 < rL)
    (hLd : rL < κ' / 2 - 4) (hR : -2 < rR) (hRd : rR < κ' / 2 - 4)
    {Ω : Type v} {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (h𝓦 : 𝓦 ≤ mΩ) {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0}
    (hRm : ∀ t, Measurable[𝓦] fun ω => R ω t) (hLm : ∀ t, Measurable[𝓦] fun ω => L ω t)
    {G : Set Ω} (hGm : MeasurableSet[𝓦] G) (hPG : 0 < P G) {W : Ω → ℝ → ℝ} {η : Ω → ℝ → ℂ}
    (hconf : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r)
    (hcfg : ∀ ω ∈ G, 0 < rightLo (R ω) (L ω) r → PocketWordAssembly.IsCfPocketConfig (R ω) (L ω) r (W ω) (η ω))
    (hcfgI : ∀ ω ∈ G, rightLo (R ω) (L ω) r = 0 → PocketSeedOpen.IsCfPocketConfigInf (R ω) (L ω) r (W ω) (η ω))
    (hηm : ∀ u, 0 ≤ u → Measurable fun ω => η ω u) {h₀ : Ω → DistOn upperHalfPlaneOpens}
    (hh₀ : IsZeroBoundaryGFF upperHalfPlaneOpens h₀ P) (𝔥 : DistOn upperHalfPlaneOpens)
    (hin : PocketStopInput (16 / κ') rL rR 𝓦 P R L r W η {ω | ω ∈ G ∧ 0 < rightLo (R ω) (L ω) r} h₀ 𝔥)
    (hinI : PocketStopInputInf (16 / κ') rL rR 𝓦 P R L r W η {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (L ω) r} h₀ 𝔥) :
    Lemma725Ref.PocketWordEvolution.{v} κ' rL rR := by
  have hGp : MeasurableSet[𝓦] {ω | ω ∈ G ∧ 0 < rightLo (R ω) (L ω) r} :=
    (measurableSet_rightLo_pos_and (mΩ := 𝓦) hRm hLm hGm hconf).1
  have hG0 : MeasurableSet[𝓦] {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (L ω) r} := by
    have e : {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (L ω) r} = G \ {ω | ω ∈ G ∧ 0 < rightLo (R ω) (L ω) r} := by
      ext ω
      exact ⟨fun h => ⟨h.1, fun h' => h.2 h'.2⟩, fun h => ⟨h.1, fun h' => h.2 ⟨h.1, h'⟩⟩⟩
    rw [e]
    exact hGm.diff hGp
  have hcfgI' : ∀ ω ∈ {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (L ω) r},
      PocketSeedOpen.IsCfPocketConfigInf (R ω) (L ω) r (W ω) (η ω) := fun ω hω =>
    hcfgI ω hω.1 (le_antisymm (not_lt.1 hω.2) (hconf ω hω.1).changeCorner_props.1.1)
  exact pocketWordEvolution_of_unionPtInput' hκ' hL hLd hR hRd h𝓦 hRm hLm hGm hPG hconf hcfg hcfgI hηm hh₀ 𝔥
    (pocketUnionPtInput_of_stopInput h𝓦 hRm hLm hGp (fun ω hω => hcfg ω hω.1 hω.2) hηm hh₀ hin)
    (pocketUnionPtInputInf_of_stopInputInf h𝓦 hRm hLm hG0 hcfgI' hηm hh₀ hinI)

end InteractingSLE.Sec7.PocketUnionPt
