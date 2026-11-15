/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketMeas
import InteractingSLE.Spec.Sec7.PocketReverseFieldsDrive
import InteractingSLE.Spec.Sec7.PocketOrientFact
import InteractingSLE.Spec.Sec7.PhaseSel3

/-!
# The random assembly of the pocket word evolution (hPW) from a random bounded change pocket

Packet PROVE-STRIPSYS20, item 6. Specification §7.4.1, proof of Lemma 7.25 (`source/spec/p385-432.md` L489–L515, p.
413–414: "Construct the non-boundary centered counterflow and the two schedules in Aux. lemma 130. That lemma supplies
a deterministic second change time and a positive-probability event, measurable from the final incoming paths, on
which the selected two-arc Jordan pocket is nondegenerate, has the correct local side order, and ends strictly after
both angle changes. … The exact initial flow-side mean and its common lift are proved by Aux. lemma 119. … The
inversion in Aux. lemma 120 gives the two near-entry seed weights `(ρ^L, ρ^R)` in (RS13.6). Every actual angle-change
mark on a selected open arc remains present. Its cumulative value beyond the mark is `d`, by Aux. lemma 121"), and
proof of Aux. lemma 130 (p. 412: "Conditional on the full marked incoming union, its selected component retains the
usual zero-boundary GFF residual; restricting to its measurable event `F_r` does not change that conditional law").

This file assembles `Lemma725Ref.PocketWordEvolution (16/κ) r_L r_R` (hPW, at the counterflow parameter `κ′ = 16/κ`)
from a random change configuration on a selection event `G` of positive probability:

* the pathwise hypotheses of one realization are bundled in `IsCfPocketConfig` (the change configuration in the
  bounded case `0 < rightLo`, its flow-chart orientation, the counterflow's Loewner trace in the chart `m(z) = −1/z`,
  the two walls' reverse visit order, the visit of the right wall, Aux. 37's attachment constancy); from them the
  erased counterflow traversal in any Jordan coordinate is a driven curve with points of large modulus
  (`IsCfPocketConfig.isDrivenCurve`, PROVE-STRIPSYS18);
* one Jordan coordinate `ψ`, measurable for the walls' σ-algebra `𝓦` at its measurable points, serves both the marks
  (Aux. 119–121) and the traversal (`exists_measurable_pocketMarks_pts`: STRIPSYS17's `exists_measurable_pocketMarks`
  with the measurability of `ψ` at measurable points kept); the marks are then `𝓦`-measurable;
* the word shape is selected on a time-zero event of positive probability: the right wall's change point `R(1)` on the
  selected right arc (four-mark word `wordL2`/`wordR2`) or not (`wordL1`/`wordR2`);
* on that event (a standard Borel subtype with the conditional law `condSub P A`) the time-zero σ-algebra is the walls'
  σ-algebra, which fixes the word and its marked positions ("Conditional on initial information fixing the word and its
  marked positions", Aux. lemma 122, p. 390), and PROVE-STRIPSYS18's reduction applies with the prefix events made
  measurable by `PocketMeas.measurableSet_prefixEvent`.

The two remaining inputs are stated as named propositions, never as weakened conclusions:

* `TraversalMeasStatement` (packet item 2, second half): the actual traversal is measurable at each fixed own time for
  every Jordan coordinate family measurable at measurable points;
* `PocketCouplingClause` (packet item 1): on the event, the field in the pocket coordinate satisfies the conditional
  characteristic-function clause of the optional hull specification along the traversal, in the relative history
  filtration (R.5, Aux. 27–29, Aux. 119; the field itself is existentially quantified, as only its conditional law
  enters the martingale argument).

## Main results

* `IsCfPocketConfig`, `IsCfPocketConfig.isDrivenCurve`;
* `exists_measurable_pocketMarks_pts`;
* `pocketWordEvolution_of_sub`: hPW from the coupling clause on a positive-probability measurable subset;
* **`pocketWordEvolution_of_cfPocketConfig`**: hPW from a random bounded change pocket with the two named inputs.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open QuantumZipper (H)
open LQGMetric (DistOn TestOn)
open InteractingSLE.WangWu (negInv)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PocketWordAssembly

open WangWu Lemma71I Lemma71C PocketCoord PocketJordan PocketMarks PocketTraversal PocketAdapt PocketMeas PhaseSel

/-! ### The pathwise hypotheses of one realization -/

/-- **The pathwise hypotheses of a bounded change pocket traversed by the counterflow** (one realization): the
change configuration with `0 < rightLo` (the pocket does not open at the flow seed), its flow-chart orientation
(Aux. 119), the counterflow driver `W` and trace `η` in the chart `m(z) = −1/z`, the reverse first-visit order of both
walls and the visit of every point of the right wall (Lemma 5.7), and Aux. lemma 37's attachment constancy at the
first-visit times of `m(y₀)` and `m(x₀)`. -/
structure IsCfPocketConfig (R L : ℝ≥0 → ℂ) (r : ℝ≥0) (W : ℝ → ℝ) (η : ℝ → ℂ) : Prop where
  conf : IsChangeConfigInc R L r
  bounded : 0 < rightLo R L r
  oriented : IsFlowChartOriented R L r
  trace : IsLoewnerTrace W η
  continuous_W : Continuous W
  W_zero : W 0 = 0
  revR : IsWallReverseVisit R η
  revL : IsWallReverseVisit L η
  visR : IsWallVisited R η
  attach : Sec6.AttachmentConstancy η (cfPocket R L r) (cfArcR R L r) (cfArcL R L r) (firstHit η (cfArcR R L r 1))
    (firstHit η (cfArcR R L r 0))

/-- The Jordan coordinates of the bounded change pocket in the counterflow chart (`m(x₀) ↦ 0`, `m(y₀) ↦ ∞`). -/
abbrev IsCfJordan (R L : ℝ≥0 → ℂ) (r : ℝ≥0) (ψ : ℂ → ℂ) : Prop :=
  Sec6.IsJordanCoord (cfPocket R L r) (cfPt (openPt R L r)) (cfPt (closePt R L r)) ψ

/-- **The erased traversal of a bounded change pocket is a driven curve with points of large modulus**
(PROVE-STRIPSYS18's `isDrivenCurve_cfTraversal`). -/
theorem IsCfPocketConfig.isDrivenCurve {R L : ℝ≥0 → ℂ} {r : ℝ≥0} {W : ℝ → ℝ} {η : ℝ → ℂ}
    (hc : IsCfPocketConfig R L r W η) {ψ : ℂ → ℂ} (hψ : IsCfJordan R L r ψ) :
    IsDrivenCurve (cfTraversal R L r η ψ) ∧
      ∀ M : ℝ, ∃ u, 0 ≤ u ∧ cfTraversal R L r η ψ u ∈ H ∧ M < ‖cfTraversal R L r η ψ u‖ :=
  hc.conf.isDrivenCurve_cfTraversal (zero_notMem_closure_of_rightLo_pos hc.conf hc.bounded) hc.trace
    hc.continuous_W hc.W_zero hc.revR hc.revL hc.visR hc.attach hψ

/-! ### One measurable Jordan coordinate for the marks and the traversal -/

section Random

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {G : Set Ω}

/-- The measurability of a random Jordan coordinate at measurable random points of the closed pocket away from
`m(x₀)`, on measurable subsets of `G`. -/
def IsPointMeasurable (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (G : Set Ω) (ψ : Ω → ℂ → ℂ) : Prop :=
  ∀ A : Set Ω, MeasurableSet A → A ⊆ G → ∀ p : Ω → ℂ, Measurable p →
    (∀ ω ∈ A, p ω ∈ closure (cfPocket (R ω) (L ω) r) \ {cfPt (openPt (R ω) (L ω) r)}) →
    Measurable (A.indicator fun ω => ψ ω (p ω))

/-- **The marks (Aux. 119–121) and the traversal from one measurable Jordan coordinate**: STRIPSYS17's
`exists_measurable_pocketMarks` with the measurability at measurable points (`exists_measurable_cfJordanCoord`) kept
for the same `ψ`. -/
theorem exists_measurable_pocketMarks_pts (hRm : ∀ t, Measurable fun ω => R ω t)
    (hLm : ∀ t, Measurable fun ω => L ω t) (hGm : MeasurableSet G) (hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r)
    (hG0 : ∀ ω ∈ G, (0 : ℂ) ∉ closure (changePocket (R ω) (L ω) r))
    (hor : ∀ ω ∈ G, IsFlowChartOriented (R ω) (L ω) r) (c₁ : ℝ) :
    ∃ ψ : Ω → ℂ → ℂ, (∀ ω ∈ G, IsCfJordan (R ω) (L ω) r (ψ ω)) ∧ IsPointMeasurable R L r G ψ ∧
      Measurable (G.indicator fun ω => (ψ ω (cfPt (toDisc (realPath (L ω)) (discTime r)))).re) ∧
      (∀ ω ∈ G, 0 < (ψ ω (cfPt (toDisc (realPath (L ω)) (discTime r)))).re) ∧
      Measurable ({ω | ω ∈ G ∧ c₁ ∈ Ioo (rightLo (R ω) (L ω) r) (rightHi (R ω) (L ω) r)}.indicator
        fun ω => (ψ ω (cfPt (toDisc (realPath (R ω)) c₁))).re) ∧
      ∀ ω ∈ G, c₁ ∈ Ioo (rightLo (R ω) (L ω) r) (rightHi (R ω) (L ω) r) →
        (ψ ω (cfPt (toDisc (realPath (R ω)) c₁))).re < 0 := by
  classical
  obtain ⟨a, Ψ, haΨ, hmeas0⟩ := exists_measurable_cfCoord hRm hLm hGm hG
  have hJ : ∀ ω ∈ G, IsCfJordan (R ω) (L ω) r (cfCoord (a ω) (Ψ ω) (closePt (R ω) (L ω) r)) := fun ω hω =>
    (hG ω hω).isJordanCoord_cfCoord (hG0 ω hω) (haΨ ω hω).2 (haΨ ω hω).1
  set ψ : Ω → ℂ → ℂ := fun ω => if ω ∈ G then cfCoord (a ω) (Ψ ω) (closePt (R ω) (L ω) r) else 0 with hψdef
  have hψG : ∀ ω ∈ G, ψ ω = cfCoord (a ω) (Ψ ω) (closePt (R ω) (L ω) r) := fun ω hω => by
    simp only [hψdef, hω, ↓reduceIte]
  have hpts : IsPointMeasurable R L r G ψ := by
    intro A hA hAG p hp hpA
    have h := hmeas0 A hA hAG p hp fun ω hω => ⟨(hpA ω hω).1, ((hJ ω (hAG hω)).1 _ (hpA ω hω)).mono
      fun z hz => ⟨subset_closure hz, fun h' => (hG ω (hAG hω)).cfPt_openPt_notMem (h' ▸ hz)⟩⟩
    convert h using 1
    funext ω
    by_cases hω : ω ∈ A
    · simp only [indicator_of_mem hω, hψG ω (hAG hω)]
    · simp only [indicator_of_notMem hω]
  have hre : ∀ A : Set Ω, MeasurableSet A → A ⊆ G → ∀ p : Ω → ℂ, Measurable p →
      (∀ ω ∈ A, p ω ∈ closure (cfPocket (R ω) (L ω) r) \ {cfPt (openPt (R ω) (L ω) r)}) →
      Measurable (A.indicator fun ω => (ψ ω (p ω)).re) := fun A hA hAG p hp hpA => by
    have h := Complex.measurable_re.comp (hpts A hA hAG p hp hpA)
    convert h using 1
    funext ω
    by_cases hω : ω ∈ A
    · simp only [indicator_of_mem hω, Function.comp_apply]
    · simp only [indicator_of_notMem hω, Function.comp_apply, Complex.zero_re]
  have hE := (measurableSet_rightLo_pos_and hRm hLm hGm hG).2 c₁
  have hLpt : ∀ ω ∈ G, ∃ s ∈ Ioo (0 : ℝ) 1, cfArcL (R ω) (L ω) r s = cfPt (toDisc (realPath (L ω)) (discTime r)) :=
    fun ω hω => by
      obtain ⟨s, hs, he⟩ := exists_affine_eq (hG ω hω).changeCorners.2.2.2.2.1
      exact ⟨s, hs, by rw [cfArcL, he]⟩
  have hRpt : ∀ ω ∈ G, c₁ ∈ Ioo (rightLo (R ω) (L ω) r) (rightHi (R ω) (L ω) r) →
      ∃ s ∈ Ioo (0 : ℝ) 1, cfArcR (R ω) (L ω) r s = cfPt (toDisc (realPath (R ω)) c₁) := fun ω _ hc => by
    obtain ⟨s, hs, he⟩ := exists_affine_eq hc
    exact ⟨s, hs, by rw [cfArcR, he]⟩
  have hmemR : ∀ ω ∈ G, ∀ s ∈ Ioo (0 : ℝ) 1, cfArcR (R ω) (L ω) r s ∈
      closure (cfPocket (R ω) (L ω) r) \ {cfPt (openPt (R ω) (L ω) r)} := fun ω hω s hs => by
    have hP := (hG ω hω).isCfPocket (hG0 ω hω)
    refine ⟨frontier_subset_closure (hP.frontier_eq ▸ Or.inl ⟨s, Ioo_subset_Icc_self hs, rfl⟩), fun he => ?_⟩
    have h0 : cfArcR (R ω) (L ω) r 0 = cfPt (openPt (R ω) (L ω) r) := by
      simp only [cfArcR, zero_mul, add_zero, openPt]
    rw [← h0] at he
    exact hs.1.ne' (hP.inj₁ (Ioo_subset_Icc_self hs) ⟨le_rfl, zero_le_one⟩ he)
  have hmemL : ∀ ω ∈ G, ∀ s ∈ Ioo (0 : ℝ) 1, cfArcL (R ω) (L ω) r s ∈
      closure (cfPocket (R ω) (L ω) r) \ {cfPt (openPt (R ω) (L ω) r)} := fun ω hω s hs => by
    have hP := (hG ω hω).isCfPocket (hG0 ω hω)
    refine ⟨frontier_subset_closure (hP.frontier_eq ▸ Or.inr ⟨s, Ioo_subset_Icc_self hs, rfl⟩), fun he => ?_⟩
    have h0 : cfArcR (R ω) (L ω) r 0 = cfPt (openPt (R ω) (L ω) r) := by
      simp only [cfArcR, zero_mul, add_zero, openPt]
    rw [← h0, ← hP.junction] at he
    exact hs.1.ne' (hP.inj₂ (Ioo_subset_Icc_self hs) ⟨le_rfl, zero_le_one⟩ he)
  have hpL : Measurable fun ω => cfPt (toDisc (realPath (L ω)) (discTime r)) :=
    measurable_cfPt.comp (measurable_toDisc_apply hLm _)
  have hpR : Measurable fun ω => cfPt (toDisc (realPath (R ω)) c₁) :=
    measurable_cfPt.comp (measurable_toDisc_apply hRm _)
  refine ⟨ψ, fun ω hω => hψG ω hω ▸ hJ ω hω, hpts, ?_, fun ω hω => ?_, ?_, fun ω hω hc => ?_⟩
  · refine hre G hGm subset_rfl _ hpL fun ω hω => ?_
    obtain ⟨s, hs, he⟩ := hLpt ω hω
    exact he ▸ hmemL ω hω s hs
  · rw [hψG ω hω]
    exact (cfCoord_sides (hG ω hω) (hor ω hω) (haΨ ω hω).2 (haΨ ω hω).1).2 _
      (hG ω hω).changeCorners.2.2.2.2.1
  · refine hre _ hE (fun ω hω => hω.1) _ hpR fun ω hω => ?_
    obtain ⟨s, hs, he⟩ := hRpt ω hω.1 hω.2
    exact he ▸ hmemR ω hω.1 s hs
  · rw [hψG ω hω]
    exact (cfCoord_sides (hG ω hω) (hor ω hω) (haΨ ω hω).2 (haΨ ω hω).1).1 _ hc

end Random

/-! ### The marks and the traversal on an event -/

section Defs

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The right marks on `A`: the seed and the image of the left wall's change point `L r` (Aux. 119–121). -/
def marksR (L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (ψ : Ω → ℂ → ℂ) (A : Set Ω) : A → Fin 2 → ℝ :=
  fun ω => ![0, (ψ ω (cfPt (toDisc (realPath (L ω)) (discTime r)))).re]

/-- The left marks on `A` when the right wall's change point `R(1)` is on the selected right arc. -/
def marksL2 (R : Ω → ℝ≥0 → ℂ) (ψ : Ω → ℂ → ℂ) (A : Set Ω) : A → Fin 2 → ℝ :=
  fun ω => ![0, (ψ ω (cfPt (toDisc (realPath (R ω)) (discTime 1)))).re]

/-- The left marks on `A` when the right wall's change point is not on the selected arc: the seed only. -/
def marksL1 (A : Set Ω) : A → Fin 1 → ℝ := fun _ => ![0]

/-- The erased counterflow traversal of the change pocket on `A`, in the Jordan coordinate `ψ`. -/
def travSub (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (η : Ω → ℝ → ℂ) (ψ : Ω → ℂ → ℂ) (A : Set Ω) : A → ℝ → ℂ :=
  fun ω => cfTraversal (R ω) (L ω) r (η ω) (ψ ω)

end Defs

/-! ### The two named inputs -/

/-- **The coupling clause along a random driven curve with random marks** (packet item 1, as an input): some random
field, integrable against every test function, satisfies the conditional-law clause of the optional hull
specification (`MartMeans.IsCouplingCharFun`) for the word `(ρL; ρR)` at the geometric force coordinates of the marks,
along the canonical driver of `γ` with lifetime `capLife γ`, in the relative history filtration over the time-zero
σ-algebra `𝓔`. For the pocket traversal this is the field in the pocket coordinate (chart transport by `ψ ∘ m`, the
offset `−πχ`, Aux. 120's inversion), from R.5 (marked union local-set Markov property), Aux. 27–29 (no singular
terms) and Aux. 119 (the exact initial word). The hypotheses `h𝓔`, `hm` only make the filtration well defined. -/
def PocketCouplingClause (κ : ℝ) {nL nR : ℕ} (ρL : Fin (nL + 1) → ℝ) (ρR : Fin (nR + 1) → ℝ) {Ω : Type*}
    (𝓔 : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] (P : Measure Ω) (γ : Ω → ℝ → ℂ)
    (xL : Ω → Fin (nL + 1) → ℝ) (xR : Ω → Fin (nR + 1) → ℝ) : Prop :=
  ∀ (h𝓔 : 𝓔 ≤ mΩ) (hm : ∀ r n k, MeasurableSet[mΩ] (prefixEvent γ r n k)),
    ∃ h : Ω → DistOn upperHalfPlaneOpens, (∀ φ : TestOn upperHalfPlaneOpens, Integrable (fun ω => h ω φ) P) ∧
      Coupling.MartMeans.IsCouplingCharFun κ ρL ρR P (usualAugmentation (prefixFilt 𝓔 h𝓔 γ hm) P)
        (fun t ω => segDriver (γ ω) t) (geomLW (fun t ω => segDriver (γ ω) t) xL)
        (geomRW (fun t ω => segDriver (γ ω) t) xR) (fun ω => capLife (γ ω)) h

/-- **Fixed-time measurability of the actual traversal** (packet item 2, second half, as an input): on every measurable
`A ⊆ G`, for every family of Jordan coordinates measurable for the walls' σ-algebra `𝓦` at its measurable points, the
erased counterflow traversal is measurable at every fixed own time (any such family is a walls-measurable positive
multiple of the jointly measurable coordinate of `PocketJordanMeas`). Route: the first-hit times of the measurable
points `m(x₀)`, `m(y₀)` are measurable (compact initial ranges); the erasure clock is a parametric integral of the
jointly measurable visit indicator; its right fibre endpoint is a countable supremum; the erased path is then a
measurable point of the closed pocket. -/
def TraversalMeasStatement {Ω : Type*} (𝓦 : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] (R L : Ω → ℝ≥0 → ℂ)
    (r : ℝ≥0) (η : Ω → ℝ → ℂ) (G : Set Ω) : Prop :=
  ∀ A : Set Ω, MeasurableSet[mΩ] A → A ⊆ G → ∀ ψ : Ω → ℂ → ℂ, (∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω)) →
    @IsPointMeasurable Ω 𝓦 R L r G ψ → ∀ u : ℝ, 0 ≤ u → Measurable fun ω : A => travSub R L r η ψ A ω u

/-! ### Elementary facts about the marks -/

theorem monotone_vec_two {a : ℝ} (ha : 0 ≤ a) : Monotone ![(0 : ℝ), a] := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

theorem antitone_vec_two {a : ℝ} (ha : a ≤ 0) : Antitone ![(0 : ℝ), a] := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

theorem antitone_vec_one : Antitone ![(0 : ℝ)] := fun i j _ => by rw [Subsingleton.elim i j]

theorem measurable_vec_two {α : Type*} [MeasurableSpace α] {f : α → ℝ} (hf : Measurable f) :
    Measurable fun x => ![(0 : ℝ), f x] := by
  refine measurable_pi_iff.2 fun i => ?_
  fin_cases i
  · exact measurable_const
  · exact hf

/-- A measurable indicator restricted to a subset of its support set is measurable on the subtype. -/
theorem measurable_sub_of_indicator {Ω : Type*} {m : MeasurableSpace Ω} {G A : Set Ω} (hAG : A ⊆ G) {f : Ω → ℝ}
    (hf : Measurable[m] (G.indicator f)) : Measurable[MeasurableSpace.comap Subtype.val m] fun ω : A => f ω := by
  have h := hf.comp (comap_measurable (Subtype.val : A → Ω))
  convert h using 1
  funext ω
  simp only [Function.comp_apply, indicator_of_mem (hAG ω.2)]

/-! ### hPW on one word shape -/

/-- **hPW from the coupling clause on one word-shape event** (the assembly on a positive-probability, walls-measurable
event `A ⊆ G` with left marks `xL`): the conditional law `condSub P A` on the standard Borel subtype `A`, the
traversal in the measurable Jordan coordinate `ψ`, the right marks `marksR`, the time-zero σ-algebra of the walls. -/
theorem pocketWordEvolution_of_word.{v} {κ rL rR : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    (hL : rL ∈ Ioo (-2) (counterflowA κ - 2)) (hR : rR ∈ Ioo (-2) (counterflowA κ - 2))
    {Ω : Type v} {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (h𝓦 : 𝓦 ≤ mΩ) {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {G : Set Ω}
    {W : Ω → ℝ → ℝ} {η : Ω → ℝ → ℂ} (hcfg : ∀ ω ∈ G, IsCfPocketConfig (R ω) (L ω) r (W ω) (η ω))
    (hmeas : TraversalMeasStatement 𝓦 R L r η G) {ψ : Ω → ℂ → ℂ}
    (hψ : ∀ ω ∈ G, IsCfJordan (R ω) (L ω) r (ψ ω)) (hψm : @IsPointMeasurable Ω 𝓦 R L r G ψ)
    (hxRm : Measurable[𝓦] (G.indicator fun ω => (ψ ω (cfPt (toDisc (realPath (L ω)) (discTime r)))).re))
    (hxRp : ∀ ω ∈ G, 0 < (ψ ω (cfPt (toDisc (realPath (L ω)) (discTime r)))).re)
    {A : Set Ω} (hA : MeasurableSet[𝓦] A) (hAG : A ⊆ G) (hPA : 0 < P A)
    {nL : ℕ} {ρL : Fin (nL + 1) → ℝ} (hρL : ρL 0 = rL)
    (hsL : ∀ m : Fin (nL + 1), -2 < ∑ i ∈ Finset.univ.filter (fun i => i ≤ m), ρL i)
    {xL : A → Fin (nL + 1) → ℝ} (hxLm : Measurable[MeasurableSpace.comap Subtype.val 𝓦] xL) (hseedL : ∀ ω, xL ω 0 = 0)
    (hxLd : ∀ ω (i : Fin nL), xL ω i.succ < 0) (hxLi : ∀ ω, Antitone (xL ω))
    (hcpl : PocketCouplingClause (16 / κ) ρL (wordR2 κ (rs136Theta2 κ rR)) (MeasurableSpace.comap Subtype.val 𝓦)
      (condSub P A) (travSub R L r η ψ A) xL (marksR L r ψ A)) :
    Lemma725Ref.PocketWordEvolution.{v} (16 / κ) rL rR := by
  have hAm : MeasurableSet A := h𝓦 _ hA
  have : StandardBorelSpace A := hAm.standardBorel
  have : IsProbabilityMeasure (condSub P A) := isProbabilityMeasure_condSub hAm hPA.ne'
  obtain ⟨-, -, hρR, -, -, hsR, -, -⟩ := lemma725_word hκ hκ4 hL hR
  have hAe : counterflowA κ = 16 / κ / 2 - 2 := rfl
  have hκ' : 4 < 16 / κ := by rw [lt_div_iff₀ hκ]; linarith
  have hLd : rL < 16 / κ / 2 - 4 := by have := hL.2; rw [hAe] at this; linarith
  have hRd : rR < 16 / κ / 2 - 4 := by have := hR.2; rw [hAe] at this; linarith
  have hxRm' : Measurable[MeasurableSpace.comap Subtype.val 𝓦] (marksR L r ψ A) :=
    @measurable_vec_two A (MeasurableSpace.comap Subtype.val 𝓦) _ (measurable_sub_of_indicator hAG hxRm)
  have hdrive : ∀ ω : A, IsDrivenCurve (travSub R L r η ψ A ω) ∧ ∀ M : ℝ, ∃ u, 0 ≤ u ∧
      travSub R L r η ψ A ω u ∈ H ∧ M < ‖travSub R L r η ψ A ω u‖ := fun ω =>
    (hcfg ω (hAG ω.2)).isDrivenCurve (hψ ω (hAG ω.2))
  have hγm : ∀ u, 0 ≤ u → Measurable fun ω : A => travSub R L r η ψ A ω u := fun u hu =>
    hmeas A hAm hAG ψ (fun ω hω => hψ ω (hAG hω)) hψm u hu
  have h𝓔 : MeasurableSpace.comap Subtype.val 𝓦 ≤ (inferInstance : MeasurableSpace A) :=
    MeasurableSpace.comap_mono h𝓦
  obtain ⟨h, hint, hcf⟩ := hcpl h𝓔 fun r n k => measurableSet_prefixEvent (fun ω => (hdrive ω).1) hγm r n k
  refine pocketWordEvolution_of_charFun_measurable hκ' hLd hRd hρL hρR hsL hsR h𝓔 (fun ω => (hdrive ω).1) hγm
    (fun ω => (hdrive ω).2) hxLm hxRm' hseedL
    (fun ω => by simp [marksR]) hxLd (fun ω j => ?_) hxLi (fun ω => monotone_vec_two (hxRp ω (hAG ω.2)).le) hint hcf
  have hj : j.succ = (1 : Fin 2) := by fin_cases j; rfl
  rw [hj]
  simpa [marksR] using hxRp ω (hAG ω.2)

/-! ### hPW from a random bounded change pocket -/

/-- **The coupling inputs on every word-shape event** (packet item 1): for every walls-measurable event `A ⊆ G` of
positive probability and every Jordan coordinate family `ψ` on it measurable for `𝓦` at its measurable points (so
that any two differ by a walls-measurable positive scaling), the coupling clause holds for the traversal in `ψ`,
with the four-mark word `(wordL2; wordR2)` when the right wall's change point `R(1)` is on the selected right arc
throughout `A`, and with `(wordL1; wordR2)` when it is off that arc throughout `A` (the weights of (RS13.6) and
Aux. 121). -/
def PocketCouplingInput (κ rL rR : ℝ) {Ω : Type*} (𝓦 : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (η : Ω → ℝ → ℂ) (G : Set Ω) : Prop :=
  ∀ A : Set Ω, MeasurableSet[𝓦] A → A ⊆ G → 0 < P A → ∀ ψ : Ω → ℂ → ℂ,
    (∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω)) → @IsPointMeasurable Ω 𝓦 R L r G ψ →
    ((∀ ω ∈ A, discTime 1 ∈ Ioo (rightLo (R ω) (L ω) r) (rightHi (R ω) (L ω) r)) →
      PocketCouplingClause (16 / κ) (wordL2 κ (rs136Theta1 κ rL)) (wordR2 κ (rs136Theta2 κ rR))
        (MeasurableSpace.comap Subtype.val 𝓦) (condSub P A) (travSub R L r η ψ A)
        (marksL2 R ψ A) (marksR L r ψ A)) ∧
    ((∀ ω ∈ A, discTime 1 ∉ Ioo (rightLo (R ω) (L ω) r) (rightHi (R ω) (L ω) r)) →
      PocketCouplingClause (16 / κ) (wordL1 κ (rs136Theta1 κ rL)) (wordR2 κ (rs136Theta2 κ rR))
        (MeasurableSpace.comap Subtype.val 𝓦) (condSub P A) (travSub R L r η ψ A)
        (marksL1 A) (marksR L r ψ A))

/-- **hPW from a random bounded change pocket** (Lemma 7.25's proof with Aux. 119–122 and 130): on a standard Borel
probability space, let the walls `R`, `L` be measurable for a sub-σ-algebra `𝓦` at every time, and let `G ∈ 𝓦` have
positive probability with every realization in `G` a bounded change pocket traversed by the counterflow
(`IsCfPocketConfig`). Given fixed-time measurability of the traversal (`TraversalMeasStatement`) and the coupling
clause on every word-shape event (`PocketCouplingInput`), the pocket word evolution exists at `κ′ = 16/κ`. -/
theorem pocketWordEvolution_of_cfPocketConfig.{v} {κ rL rR : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    (hL : rL ∈ Ioo (-2) (counterflowA κ - 2)) (hR : rR ∈ Ioo (-2) (counterflowA κ - 2))
    {Ω : Type v} {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (h𝓦 : 𝓦 ≤ mΩ) {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0}
    (hRm : ∀ t, Measurable[𝓦] fun ω => R ω t) (hLm : ∀ t, Measurable[𝓦] fun ω => L ω t)
    {G : Set Ω} (hGm : MeasurableSet[𝓦] G) (hPG : 0 < P G) {W : Ω → ℝ → ℝ} {η : Ω → ℝ → ℂ}
    (hcfg : ∀ ω ∈ G, IsCfPocketConfig (R ω) (L ω) r (W ω) (η ω)) (hmeas : TraversalMeasStatement 𝓦 R L r η G)
    (hcpl : PocketCouplingInput κ rL rR 𝓦 P R L r η G) :
    Lemma725Ref.PocketWordEvolution.{v} (16 / κ) rL rR := by
  have hconf : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r := fun ω hω => (hcfg ω hω).conf
  obtain ⟨ψ, hψ, hψm, hxRm, hxRp, hxL2m, hxL2n⟩ := exists_measurable_pocketMarks_pts (mΩ := 𝓦) hRm hLm hGm hconf
    (fun ω hω => zero_notMem_closure_of_rightLo_pos (hcfg ω hω).conf (hcfg ω hω).bounded)
    (fun ω hω => (hcfg ω hω).oriented) (discTime 1)
  obtain ⟨hρL2, hρL1, -, hsL2, hsL1, -, -, -⟩ := lemma725_word hκ hκ4 hL hR
  set E := {ω | ω ∈ G ∧ discTime 1 ∈ Ioo (rightLo (R ω) (L ω) r) (rightHi (R ω) (L ω) r)} with hEdef
  have hEm : MeasurableSet[𝓦] E := (measurableSet_rightLo_pos_and (mΩ := 𝓦) hRm hLm hGm hconf).2 _
  by_cases hE : 0 < P E
  · -- the four-mark word: `R(1)` on the selected right arc
    have hxLm : Measurable[MeasurableSpace.comap Subtype.val 𝓦] (marksL2 R ψ E) :=
      @measurable_vec_two E (MeasurableSpace.comap Subtype.val 𝓦) _ (measurable_sub_of_indicator subset_rfl hxL2m)
    refine pocketWordEvolution_of_word hκ hκ4 hL hR h𝓦 hcfg hmeas hψ hψm hxRm hxRp hEm (fun ω hω => hω.1) hE
      hρL2 hsL2 hxLm (fun ω => by simp [marksL2]) (fun ω i => ?_) (fun ω => antitone_vec_two ?_)
      ((hcpl E hEm (fun ω hω => hω.1) hE ψ (fun ω hω => hψ ω hω.1) hψm).1 fun ω hω => hω.2)
    · have hi : i.succ = (1 : Fin 2) := by fin_cases i; rfl
      rw [hi]
      simpa [marksL2] using hxL2n ω ω.2.1 ω.2.2
    · exact (hxL2n ω ω.2.1 ω.2.2).le
  · -- the three-mark word: `R(1)` off the selected right arc
    have hPE : P E = 0 := le_antisymm (not_lt.1 hE) zero_le
    have hPA : 0 < P (G \ E) := by
      have h1 : P G ≤ P (G ∩ E) + P (G \ E) := measure_le_inter_add_sdiff P G E
      have h2 : P (G ∩ E) = 0 := measure_mono_null inter_subset_right hPE
      rw [h2, zero_add] at h1
      exact lt_of_lt_of_le hPG h1
    refine pocketWordEvolution_of_word hκ hκ4 hL hR h𝓦 hcfg hmeas hψ hψm hxRm hxRp (hGm.diff hEm) sdiff_subset hPA
      hρL1 hsL1 measurable_const (fun ω => rfl) (fun ω i => i.elim0) (fun ω => antitone_vec_one)
      ((hcpl (G \ E) (hGm.diff hEm) sdiff_subset hPA ψ (fun ω hω => hψ ω hω.1) hψm).2
        fun ω hω hc => hω.2 ⟨hω.1, hc⟩)

/-- **hPW in the form the Theorem 1.3 wiring consumes** (`κ′ > 4`, both-low seed weights): if for the flow
parameter `κ = 16/κ′` some random bounded change pocket satisfies the hypotheses of
`pocketWordEvolution_of_cfPocketConfig`, then `PocketWordEvolution κ′ r_L r_R`. -/
theorem pocketWordEvolution_of_cfPocketConfig'.{v} {κ' rL rR : ℝ} (hκ' : 4 < κ') (hL : -2 < rL)
    (hLd : rL < κ' / 2 - 4) (hR : -2 < rR) (hRd : rR < κ' / 2 - 4)
    {Ω : Type v} {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (h𝓦 : 𝓦 ≤ mΩ) {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0}
    (hRm : ∀ t, Measurable[𝓦] fun ω => R ω t) (hLm : ∀ t, Measurable[𝓦] fun ω => L ω t)
    {G : Set Ω} (hGm : MeasurableSet[𝓦] G) (hPG : 0 < P G) {W : Ω → ℝ → ℝ} {η : Ω → ℝ → ℂ}
    (hcfg : ∀ ω ∈ G, IsCfPocketConfig (R ω) (L ω) r (W ω) (η ω)) (hmeas : TraversalMeasStatement 𝓦 R L r η G)
    (hcpl : PocketCouplingInput (16 / κ') rL rR 𝓦 P R L r η G) :
    Lemma725Ref.PocketWordEvolution.{v} κ' rL rR := by
  have hκ0 : 0 < κ' := by linarith
  have hκ : 0 < 16 / κ' := by positivity
  have hκ4 : 16 / κ' < 4 := by rw [div_lt_iff₀ hκ0]; linarith
  have hinv : 16 / (16 / κ') = κ' := by field_simp
  have hA : counterflowA (16 / κ') - 2 = κ' / 2 - 4 := by
    show 16 / (16 / κ') / 2 - 2 - 2 = κ' / 2 - 4
    rw [hinv]; ring
  have h := pocketWordEvolution_of_cfPocketConfig hκ hκ4 ⟨hL, by rw [hA]; exact hLd⟩ ⟨hR, by rw [hA]; exact hRd⟩
    h𝓦 hRm hLm hGm hPG hcfg hmeas hcpl
  rwa [hinv] at h

end InteractingSLE.Sec7.PocketWordAssembly
