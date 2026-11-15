/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Foundations.Loewner.FiniteEndpointLaunch
import InteractingSLE.Foundations.Loewner.FiniteEndpoint
import InteractingSLE.Spec.Exist.FlowField
import InteractingSLE.Spec.Exist.StagedRun
import InteractingSLE.Spec.Sec6.Prop61Mean
import InteractingSLE.Spec.Sec4.Special3Thin

/-!
# Lemmas GW0–GW1 for the first piece of an extreme walk: `GW1FirstThresholdStatement`

Packet PROVE-T14-GW. The named input `Theorem14.GW1FirstThresholdStatement` (`Spec/Supplement/GW6Reduction.lean`,
PROVE-T14-IN) says that almost surely the first ordinary piece of either extreme boundary walk, if its lifetime is
finite, ends at a continuation threshold with a bad side (`IsThresholdEnd`). Source: Lemma GW0, p. 617 ("An
inadmissible seed gives zero available lifetime"; with the maximal-lifetime reading of the threshold, R15 Q1, a zero
lifetime is an inadmissible seed), and Lemma GW1, pp. 618–619 ("Every finite threshold of a nonempty ordinary stage
consequently has physical value `q_j > w_j`, and is a new original right record").

Two halves.

* **Finite positive lifetime** (PROVE-ENDPOINT): `IsIntegratedSLEEvolution.ae_isThresholdEnd_launch_init`.
* **Zero lifetime** (this file): the maximal lifetime gives the threshold condition at the seed for the force word of
  the first piece, i.e. its seed is inadmissible for the boundary data `b'` of the conditional field
  (`thresholdCondition_flowLine_zero_iff`). The first piece is launched from the root, so the retained history is
  trivial (`pastSigma_zero_eq_bot`), its conditional law is `P` itself (`condExpKernel_bot_apply`), and its chart is
  the identity. The field `h` is then a GFF with data `b` and, translated by `θχ`, a GFF with the force-word data of
  `b'`; the means of a GFF are unique (`integral_mul_eq_of_isZBGFFProcess`, `eqOn_of_integral_mul_eq`), so `b = b'`
  off a finite set and the one-sided limits at the seed agree (`leftLim_eq_of_eqOn`, `rightLim_eq_of_eqOn`).

Main result: `gw1FirstThresholdStatement`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Theorem14

namespace GW1

open PiecewiseConstantBoundaryData (leftLim rightLim jumpSet)
open QuantumZipper (H)
open LQGMetric (TestOn DistOn)

/-! ### Deterministic part: the zero-lifetime launch and the seed condition -/

/-- **A zero lifetime at an inadmissible seed ends the first piece at a threshold**: the launch from the root with
zero lifetime has status *thr* `none` at the root `0` with the piece's angle. -/
theorem isThresholdEnd_launch_init_of_zero (κ : ℝ) (b : ℝ → ℝ) {D : (ℝ≥0 → ℝ) × ℝ≥0∞} (θ : ℝ)
    (hD : D.2 = 0) (hadm : ¬ ExplState.IsAdmissibleSeed κ (leftLim b 0) (rightLim b 0) θ) :
    IsThresholdEnd κ b (ExplState.launch (ExplState.init 0) 0 D θ ⊤) := by
  obtain ⟨W, ζ⟩ := D
  simp only at hD
  subst hD
  right; right
  simp [ExplState.launch, ExplState.init, hadm]

/-- A sum over the marks at the seed `0` of a word whose first position is `0` and whose other positions are
nonzero is the first weight. -/
theorem sum_filter_cons_eq_zero {n : ℕ} (f g : Fin n → ℝ) (a : ℝ) (hf : ∀ j, f j ≠ 0) :
    ∑ i ∈ Finset.univ.filter (fun i : Fin (n + 1) => (Fin.cons (0 : ℝ) f : Fin (n + 1) → ℝ) i = 0),
      (Fin.cons a g : Fin (n + 1) → ℝ) i = a := by
  have e : Finset.univ.filter (fun i : Fin (n + 1) => (Fin.cons (0 : ℝ) f : Fin (n + 1) → ℝ) i = 0) = {0} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp only [Fin.cons_succ, Fin.succ_ne_zero, iff_false]
      exact hf j
  rw [e, Finset.sum_singleton, Fin.cons_zero]

/-- The left seed group of the flow-line word from `0`. -/
theorem sum_seed_flowLineL (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (θ : ℝ) :
    ∑ i ∈ Finset.univ.filter (fun i => flowLineXL b jumps 0 i = 0), flowLineRhoL κ b jumps 0 θ i =
      -(leftLim b 0 + θ * QuantumZipper.chiC κ) / sleLambda κ - 1 :=
  sum_filter_cons_eq_zero _ _ _ fun j => by
    have hm := Finset.orderEmbOfFin_mem ((jumpSet b jumps).filter (· < 0)) rfl (Fin.rev j)
    rw [sub_zero]
    exact (Finset.mem_filter.1 hm).2.ne

/-- The right seed group of the flow-line word from `0`. -/
theorem sum_seed_flowLineR (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (θ : ℝ) :
    ∑ i ∈ Finset.univ.filter (fun i => flowLineXR b jumps 0 i = 0), flowLineRhoR κ b jumps 0 θ i =
      (rightLim b 0 + θ * QuantumZipper.chiC κ) / sleLambda κ - 1 :=
  sum_filter_cons_eq_zero _ _ _ fun j => by
    have hm := Finset.orderEmbOfFin_mem ((jumpSet b jumps).filter (0 < ·)) rfl j
    rw [sub_zero]
    exact (Finset.mem_filter.1 hm).2.ne'

/-- **The threshold condition at the seed of the flow-line word is the inadmissibility of the seed** (GW0: "An
inadmissible seed gives zero available lifetime"; BW2.4: the seed groups are `−(b(0⁻) + θχ)/λ − 1` and
`(b(0⁺) + θχ)/λ − 1`). -/
theorem thresholdCondition_flowLine_zero_iff {κ : ℝ} (hκ : 0 < κ) (b : ℝ → ℝ) (jumps : Finset ℝ) (θ : ℝ) :
    ForceWord.ThresholdCondition (flowLineRhoL κ b jumps 0 θ) (flowLineRhoR κ b jumps 0 θ) 0
        (flowLineXL b jumps 0) (flowLineXR b jumps 0) ↔
      ¬ ExplState.IsAdmissibleSeed κ (leftLim b 0) (rightLim b 0) θ := by
  have hΛ := Sec4.sleLambda_pos hκ
  unfold ForceWord.ThresholdCondition ExplState.IsAdmissibleSeed
  rw [sum_seed_flowLineL, sum_seed_flowLineR]
  simp only [not_and_or, not_lt]
  constructor
  · rintro (h | h)
    · left
      have : 1 ≤ (leftLim b 0 + θ * QuantumZipper.chiC κ) / sleLambda κ := by
        rw [neg_div] at h; linarith
      rwa [le_div_iff₀ hΛ, one_mul] at this
    · right
      have : (rightLim b 0 + θ * QuantumZipper.chiC κ) / sleLambda κ ≤ -1 := by linarith
      rwa [div_le_iff₀ hΛ, neg_one_mul] at this
  · rintro (h | h)
    · left
      have : 1 ≤ (leftLim b 0 + θ * QuantumZipper.chiC κ) / sleLambda κ := by
        rwa [le_div_iff₀ hΛ, one_mul]
      rw [neg_div]; linarith
    · right
      have : (rightLim b 0 + θ * QuantumZipper.chiC κ) / sleLambda κ ≤ -1 := by
        rwa [div_le_iff₀ hΛ, neg_one_mul]
      linarith

/-! ### The first piece is launched with the trivial past -/

/-- A σ-algebra pulled back from functions on `Fin 0` is trivial. -/
theorem comap_fin_zero_eq_bot {Ω X : Type*} (m : MeasurableSpace (Fin 0 → X)) (f : Ω → Fin 0 → X) :
    MeasurableSpace.comap f m = ⊥ := by
  have e : f = fun _ => (fun i => i.elim0 : Fin 0 → X) := funext fun _ => Subsingleton.elim _ _
  rw [e, MeasurableSpace.comap_const]

/-- **The retained history before the first instruction is trivial.** -/
theorem pastSigma_zero_eq_bot (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} (spec : ExplSpec)
    (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) : pastSigma κ b jumps spec E 0 = ⊥ :=
  comap_fin_zero_eq_bot _ _

/-- **The conditional kernel given the trivial σ-algebra is the measure itself.** -/
theorem condExpKernel_bot_apply {Ω : Type*} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ω₀ : Ω) : condExpKernel P ⊥ ω₀ = P := by
  ext s hs
  have hmeas : Measurable[⊥] (fun ω => condExpKernel P ⊥ ω s) := measurable_condExpKernel hs
  have hconst : ∀ ω, condExpKernel P ⊥ ω s = condExpKernel P ⊥ ω₀ s := by
    intro ω
    have hset := hmeas (measurableSet_singleton (condExpKernel P ⊥ ω₀ s))
    rcases MeasurableSpace.measurableSet_bot_iff.1 hset with he | he
    · have : ω₀ ∈ (fun ω => condExpKernel P ⊥ ω s) ⁻¹' {condExpKernel P ⊥ ω₀ s} := rfl
      rw [he] at this
      exact absurd this (Set.notMem_empty ω₀)
    · have : ω ∈ (fun ω => condExpKernel P ⊥ ω s) ⁻¹' {condExpKernel P ⊥ ω₀ s} := by
        rw [he]; exact Set.mem_univ ω
      exact this
  have hcomp := condExpKernel_comp_trim (μ := P) (bot_le : (⊥ : MeasurableSpace Ω) ≤ mΩ)
  have h1 : P s = ∫⁻ ω, condExpKernel P ⊥ ω s ∂(P.trim (bot_le : (⊥ : MeasurableSpace Ω) ≤ mΩ)) := by
    conv_lhs => rw [← hcomp]
    exact Measure.bind_apply hs (condExpKernel P ⊥).aemeasurable
  rw [h1, lintegral_congr fun ω => hconst ω, lintegral_const,
    trim_measurableSet_eq _ MeasurableSet.univ, measure_univ, mul_one]

/-- The first instruction of a walk launches its piece from the root, in the identity chart. -/
theorem launches_run_one_boundaryWalkSpec (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (θ : ℝ) (right : Bool)
    (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) :
    (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (0 + 1)).2.2.2.1 0 =
      some (Chart.id.recenter 0, θ) := by
  obtain ⟨rest, hrest⟩ := zipIdx_take_boundaryWalkSpec b jumps θ right
  have h1 : (boundaryWalkSpec b jumps θ right).2.2.zipIdx.take (0 + 1) = [(Sum.inl (θ, ⊤), 0)] := by
    have hlen : 0 + 1 ≤ (boundaryWalkSpec b jumps θ right).2.2.length := by
      simp [boundaryWalkSpec, List.replicate_succ]
    have := congrArg (List.take (0 + 1)) hrest
    rw [List.take_take, min_eq_left hlen] at this
    rw [this]
    rfl
  unfold ExplState.run
  rw [h1, List.foldl_cons, List.foldl_nil]
  show (ExplState.launch (ExplState.init 0) 0 (D 0) θ ⊤).2.2.2.1 0 = _
  rw [Exist.Staged.launches_launch, Function.update_self]
  rfl

/-! ### The mean of a GFF is unique -/

/-- **A zero-boundary GFF process shifted by constants is a zero-boundary GFF only for the zero shift** (both are
centred, and Gaussian coordinates are integrable). -/
theorem eq_zero_of_isZBGFFProcess_add {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {U : TopologicalSpace.Opens ℂ} {X : TestOn U → Ω → ℝ} {c : TestOn U → ℝ}
    (hX : LQGMetric.IsZBGFFProcess U X P) (hY : LQGMetric.IsZBGFFProcess U (fun φ ω => X φ ω + c φ) P)
    (φ : TestOn U) : c φ = 0 := by
  have hi : Integrable (X φ) P := (hX.gaussian.hasGaussianLaw_eval φ).integrable
  have h1 := hY.centered φ
  rw [integral_add hi (integrable_const _), hX.centered φ, integral_const, probReal_univ, one_smul,
    zero_add] at h1
  exact h1

/-- A real point is eventually not in a finite set, punctured at `0`. -/
theorem eventually_notMem_nhdsNE (S : Finset ℝ) : ∀ᶠ y in 𝓝[≠] (0 : ℝ), y ≠ 0 ∧ y ∉ S := by
  have ho : IsOpen ((((S.erase 0 : Finset ℝ) : Set ℝ))ᶜ) := (S.erase 0).finite_toSet.isClosed.isOpen_compl
  have h0 : (0 : ℝ) ∈ (((S.erase 0 : Finset ℝ) : Set ℝ))ᶜ := by simp
  filter_upwards [mem_nhdsWithin_of_mem_nhds (ho.mem_nhds h0), self_mem_nhdsWithin] with y hy hy0
  refine ⟨hy0, fun hyS => hy ?_⟩
  exact Finset.mem_coe.2 (Finset.mem_erase.2 ⟨hy0, hyS⟩)

/-- Functions that agree off a finite set and off `0` have the same one-sided limits at `0`. -/
theorem lims_eq_of_eq_off {f g : ℝ → ℝ} (S : Finset ℝ) (hfg : ∀ y, y ≠ 0 → y ∉ S → f y = g y) :
    leftLim f 0 = leftLim g 0 ∧ rightLim f 0 = rightLim g 0 := by
  have he : f =ᶠ[𝓝[≠] (0 : ℝ)] g := (eventually_notMem_nhdsNE S).mono fun y hy => hfg y hy.1 hy.2
  have hL : Filter.map f (𝓝[<] (0 : ℝ)) = Filter.map g (𝓝[<] 0) :=
    Filter.map_congr (he.filter_mono (nhdsWithin_mono _ fun y hy => ne_of_lt hy))
  have hR : Filter.map f (𝓝[>] (0 : ℝ)) = Filter.map g (𝓝[>] 0) :=
    Filter.map_congr (he.filter_mono (nhdsWithin_mono _ fun y hy => ne_of_gt hy))
  exact ⟨congrArg lim hL, congrArg lim hR⟩

/-- **The conditional data of the first piece are the original data.** If `h` is a GFF with data `b`, and the field
`h + θχ` is a GFF with the force-word data of the angle-`θ` flow-line word from `0` of some piecewise-constant `b'`,
then `b' = b` off a finite set: the two means agree on `ℍ` (uniqueness of the mean of a GFF and of harmonic
representatives), so their boundary values `b' + θχ` and `b + θχ` agree off a finite set. -/
theorem eq_off_of_isGFF {κ : ℝ} (hκ : 0 < κ) {b b' : ℝ → ℝ} {jumps jumps' : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hb' : IsPiecewiseConstantBoundaryData b' jumps') (θ : ℝ)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h h'' : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps)
    (hshift : ∀ ω φ, h'' ω φ = h ω φ + θ * QuantumZipper.chiC κ * ∫ z, φ z)
    (hgff : ∀ u₀ : ℂ → ℝ, IsBoundedHarmonicExtension (forceBoundaryData κ (flowLineRhoL κ b' jumps' 0 θ)
        (flowLineRhoR κ b' jumps' 0 θ) (flowLineXL b' jumps' 0) (flowLineXR b' jumps' 0))
        (forceJumpSet (flowLineXL b' jumps' 0) (flowLineXR b' jumps' 0)) u₀ →
      LQGMetric.IsZBGFFProcess upperHalfPlaneOpens (fun φ ω => h'' ω φ - ∫ z, u₀ z * φ z) P) :
    ∀ y, y ≠ 0 → y ∉ Exist.flowExcept b' jumps' 0 ∪ jumps → b' y = b y := by
  set a : ℝ := θ * QuantumZipper.chiC κ with ha
  obtain ⟨u, hu, -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension hb
  obtain ⟨v, hv⟩ := Sec4.exists_isBoundedHarmonicExtension_forceBoundaryData κ (flowLineRhoL κ b' jumps' 0 θ)
    (flowLineRhoR κ b' jumps' 0 θ) (flowLineXL b' jumps' 0) (flowLineXR b' jumps' 0)
  have hX := hh.2 u hu
  set c : TestOn upperHalfPlaneOpens → ℝ := fun φ => a * (∫ z, φ z) + (∫ z, u z * φ z) - ∫ z, v z * φ z
    with hc
  have hY : LQGMetric.IsZBGFFProcess upperHalfPlaneOpens
      (fun φ ω => (h ω φ - ∫ z, u z * φ z) + c φ) P := by
    have e : (fun φ ω => (h ω φ - ∫ z, u z * φ z) + c φ) = (fun φ ω => h'' ω φ - ∫ z, v z * φ z) := by
      funext φ ω
      rw [hshift, hc]
      ring
    rw [e]
    exact hgff v hv
  have hc0 := eq_zero_of_isZBGFFProcess_add hX hY
  -- the two means have the same pairings
  have hint : ∀ φ : TestOn upperHalfPlaneOpens, ∫ z, v z * φ z = ∫ z, (u z + a) * φ z := by
    intro φ
    have hui : Integrable (fun z => u z * φ z) :=
      Coupling.MartMeans2.integrable_mul_test_of_continuousOn (S := H) hu.1.continuousOn φ φ.tsupport_subset
    have hφi : Integrable (fun z => a * φ z) :=
      (φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport).const_mul a
    have e : ∫ z, (u z + a) * φ z = (∫ z, u z * φ z) + a * ∫ z, φ z := by
      rw [← integral_const_mul, ← integral_add hui hφi]
      congr 1
      funext z
      ring
    have := hc0 φ
    simp only [hc] at this
    rw [e]
    linarith
  have hharm : InnerProductSpace.HarmonicOnNhd (fun z => u z + a) H :=
    fun z hz => (hu.1 z hz).add (InnerProductSpace.harmonicAt_const _)
  have heq : EqOn v (fun z => u z + a) H :=
    Sec6.eqOn_of_integral_mul_eq QuantumZipper.isOpen_H subset_rfl hv.1 hharm fun φ _ => hint φ
  -- hence the boundary values agree off a finite set
  intro y hy0 hyS
  have hy1 : y ∉ Exist.flowExcept b' jumps' 0 := fun hm => hyS (Finset.mem_union_left _ hm)
  have hy2 : y ∉ jumps := fun hm => hyS (Finset.mem_union_right _ hm)
  have t1 := hv.2.2 y (Exist.notMem_forceJumpSet_of_notMem_flowExcept hy1)
  have t2 := (hu.2.2 y hy2).add_const a
  have t1' : Tendsto (fun z => u z + a) (𝓝[H] (y : ℂ))
      (𝓝 (forceBoundaryData κ (flowLineRhoL κ b' jumps' 0 θ) (flowLineRhoR κ b' jumps' 0 θ)
        (flowLineXL b' jumps' 0) (flowLineXR b' jumps' 0) y)) :=
    t1.congr' (eventually_nhdsWithin_of_forall fun z hz => heq hz)
  have := FiniteEndpoint.neBot_nhdsWithin_H (z := (y : ℂ)) (by simp)
  have e := tendsto_nhds_unique t1' t2
  rw [Exist.forceBoundaryData_flowLine_seed hκ hb' 0 θ hy0 (Exist.add_notMem_of_notMem_flowExcept hy1),
    add_zero] at e
  linarith

/-- **The seed of the first piece sees the original one-sided limits** (`eq_off_of_isGFF` at `0`). -/
theorem seed_lims_eq {κ : ℝ} (hκ : 0 < κ) {b b' : ℝ → ℝ} {jumps jumps' : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hb' : IsPiecewiseConstantBoundaryData b' jumps') (θ : ℝ)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h h'' : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps)
    (hshift : ∀ ω φ, h'' ω φ = h ω φ + θ * QuantumZipper.chiC κ * ∫ z, φ z)
    (hgff : ∀ u₀ : ℂ → ℝ, IsBoundedHarmonicExtension (forceBoundaryData κ (flowLineRhoL κ b' jumps' 0 θ)
        (flowLineRhoR κ b' jumps' 0 θ) (flowLineXL b' jumps' 0) (flowLineXR b' jumps' 0))
        (forceJumpSet (flowLineXL b' jumps' 0) (flowLineXR b' jumps' 0)) u₀ →
      LQGMetric.IsZBGFFProcess upperHalfPlaneOpens (fun φ ω => h'' ω φ - ∫ z, u₀ z * φ z) P) :
    leftLim b' 0 = leftLim b 0 ∧ rightLim b' 0 = rightLim b 0 :=
  lims_eq_of_eq_off _ (eq_off_of_isGFF hκ hb hb' θ hh hshift hgff)

/-! ### The named input -/

/-- **`GW1FirstThresholdStatement`** (Lemmas GW0–GW1 for the first piece of either extreme walk): almost surely, if
the first ordinary piece of the right walk (angle `−π/2`) or of the left walk (angle `π/2`) has finite lifetime, it
ends at a continuation threshold with a bad side. -/
theorem gw1FirstThresholdStatement : GW1FirstThresholdStatement.{u} := by
  intro κ hκ _ b jumps hb Ω _ _ P _ h hh _ _ _ _ E hE θ right hθr
  have hpi := Real.pi_pos
  have hθ : θ ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    rcases hθr with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> constructor <;> linarith
  have hS := hE _ (isBoundaryContinuedProgram_boundaryWalkSpec b jumps hθ right)
  obtain ⟨ω₀, hω₀⟩ := (hS.2.2.2 0).exists
  obtain ⟨b', jumps', h', hb', hT, hF⟩ :=
    hω₀ _ _ (launches_run_one_boundaryWalkSpec κ b jumps θ right (fun j => E _ j ω₀))
  rw [pastSigma_zero_eq_bot, condExpKernel_bot_apply] at hF
  obtain ⟨h'', 𝓕, VL, VR, B, htr, hC⟩ := hF
  -- the conditional field is `h` itself, translated by `θχ`
  have hshift : ∀ ω φ, h'' ω φ = h ω φ + θ * QuantumZipper.chiC κ * ∫ z, φ z := by
    intro ω φ
    have e1 : h' ω φ = h ω φ := by
      have := hT ω φ φ (by
        intro z hz
        refine ⟨z, ?_, by simp [Chart.recenter, Chart.id]⟩
        exact φ.tsupport_subset hz) (by
        intro z _
        simp [Chart.recenter, Chart.id])
      simpa [Chart.recenter, Chart.id] using this
    rw [htr ω φ φ (fun z => by rw [Complex.ofReal_zero, add_zero]), e1]
  have hseed := seed_lims_eq hκ hb hb' θ hh hshift hC.2.2.1
  filter_upwards [hC.1.ae_isThresholdEnd_launch_init hκ κ b θ, hC.1.2.2.2.2] with ω hpos hpath hne
  by_cases h0 : (E (boundaryWalkSpec b jumps θ right) 0 ω).2 = 0
  · refine isThresholdEnd_launch_init_of_zero κ b θ h0 ?_
    have hthr := hpath.isForcePath.threshold_of_eq_zero h0
    rw [thresholdCondition_flowLine_zero_iff hκ, hseed.1, hseed.2] at hthr
    exact hthr
  · exact hpos hne h0

end GW1

end Theorem14

end InteractingSLE
