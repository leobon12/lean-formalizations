/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.G7Restart
import InteractingSLE.Spec.Restart.CondDetG7
import InteractingSLE.Spec.Supplement.S7Interior
import InteractingSLE.Spec.Supplement.RLCGlue

/-!
# The two-tip joint chart at a retained pair (ruling R47), with the inverse-chart properties of the gluing

Packet PROVE-RLC-A, part (a). Ruling R47: "The stopped pair in the joint chart is represented by the chart paths `Γᵢ`
of `Supp7.IsRetainedContinuation`, extended to two tips with ONE shared `(φ, ψ, lift)` of the joint unbounded
component `Supp9.activeDomain η₁ u η₂ r`."

That representation is the landed `Supp9D.IsJointRetainedContinuation` (PROVE-W5-REST), and its carrier
`Supp9D.JointRetainedPairStatement` is proved from the retained-pair restart
(`Supp7.jointRetainedPairStatement_of_restart`, PROVE-G7; `…_of_kernelClock`, PROVE-G7B), i.e. from PROVE-CONDDET's
two-tip P-side input `Restart.RetainedCanonCondDetStatement` with Theorems 1.2 (param) and 1.3
(`Restart.retainedKernelClockStatement_of_param`).
The planar gluing (`RLCGlue.lean`) needs three more facts about the shared inverse chart `ψ`, all part of the landed
retained chart (`Supp7.IsRetChart`, an `IsFirstContactChart`): `ψ` is continuous on `ℍ̄`, has bounded displacement
(hydrodynamic normalization, so `ψ` is proper), and sends the chart seed `0` to the second tip; and the chart paths lie
in `ℍ̄` up to their stops (`Supp7.IsRetainedClock`). This file adds them:

* `IsJointRetainedChart`: `IsJointRetainedContinuation` with these facts;
* `JointRetainedChartStatement`: the joint carrier with `IsJointRetainedChart`;
* `jointRetainedChartStatement_of_restart`, `…_of_kernelClock`, **`jointRetainedChartStatement_of_param`** (from
  Theorems 1.2 (param), 1.3 and `Restart.RetainedCanonCondDetStatement`), and the forgetful maps to the landed
  predicates.

It also states the chart-side completability predicates used by the gluing (`IsChartCompletable`,
`ChartInteriorCompletion`) and proves G10's interior form for them (`exists_interior_completions`).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

open QuantumZipper (H Hbar)

universe u

namespace InteractingSLE

namespace RLC

open Supp7 Supp9D Restart

/-! ### The joint chart -/

/-- **The two-tip joint chart at a retained pair** (ruling R47; Lemma G7 for both tips, pp. 497–498; the planar
gluing, pp. 502–503). `Supp9D.IsJointRetainedContinuation` (one shared `(φ, ψ, lift)` of `D = activeDomain η₁ u η₂ r`
active at the second tip, the chart field, the two clocks up to and including the first new contact with
`A = η₁([0, u]) ∪ η₂([0, r])`, the separation of fresh common points) together with: `ψ` continuous on `ℍ̄`, with
bounded displacement and `ψ(0) = η₂(r)`, and the chart paths in `ℍ̄` up to their stops. -/
def IsJointRetainedChart (κ : ℝ) (h H₀ : LQGMetric.DistOn upperHalfPlaneOpens) (η₁ : ℝ≥0 → ℂ)
    (ζ₁ : ℝ≥0∞) (u : ℝ≥0) (η₂ : ℝ≥0 → ℂ) (ζ₂ : ℝ≥0∞) (r : ℝ≥0) (Γ₁ Γ₂ : ℝ≥0 → ℂ) (U₁ U₂ : ℝ≥0∞) :
    Prop :=
  ∃ (φ ψ : ℂ → ℂ) (lift : ℂ → ℝ) (c₁ c₂ : ℝ≥0 → ℝ≥0) (σ₁ σ₂ : ℝ≥0∞),
    IsActiveChart (activeDomain η₁ u η₂ r) (η₂ r) φ ∧
    BijOn ψ H (activeDomain η₁ u η₂ r) ∧ (∀ w ∈ H, φ (ψ w) = w) ∧
    (∀ w ∉ H, ψ w ∉ activeDomain η₁ u η₂ r) ∧
    ContinuousOn lift (activeDomain η₁ u η₂ r) ∧
    (∀ z ∈ activeDomain η₁ u η₂ r,
      deriv φ z = (‖deriv φ z‖ : ℂ) * Complex.exp (Complex.I * (lift z : ℂ))) ∧
    IsChartTransport (φ, ψ, lift) 1 0 (QuantumZipper.chiC κ) h H₀ ∧
    ContinuousOn ψ Hbar ∧ (∃ M : ℝ, ∀ w ∈ Hbar, ‖ψ w - w‖ ≤ M) ∧ ψ 0 = η₂ r ∧
    σ₁ ≤ U₁ ∧ StrictMonoOn c₁ {s | (s : ℝ≥0∞) ≤ σ₁} ∧
    c₁ '' {s | (s : ℝ≥0∞) ≤ σ₁} =
      {x | u ≤ x ∧ (x : ℝ≥0∞) ≤ ζ₁ ∧ ∀ x' : ℝ≥0, u < x' → x' < x → η₁ x' ∉ η₁ '' Icc 0 u ∪ η₂ '' Icc 0 r} ∧
    σ₂ ≤ U₂ ∧ StrictMonoOn c₂ {s | (s : ℝ≥0∞) ≤ σ₂} ∧
    c₂ '' {s | (s : ℝ≥0∞) ≤ σ₂} =
      {y | r ≤ y ∧ (y : ℝ≥0∞) ≤ ζ₂ ∧ ∀ y' : ℝ≥0, r < y' → y' < y → η₂ y' ∉ η₁ '' Icc 0 u ∪ η₂ '' Icc 0 r} ∧
    (∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ σ₁ → η₁ (c₁ s) = ψ (Γ₁ s) ∧ Γ₁ s ∈ Hbar) ∧
    (∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ σ₂ → η₂ (c₂ s) = ψ (Γ₂ s) ∧ Γ₂ s ∈ Hbar) ∧
    ∀ s₁ s₂ : ℝ≥0, (s₁ : ℝ≥0∞) ≤ σ₁ → (s₂ : ℝ≥0∞) ≤ σ₂ → η₁ (c₁ s₁) = η₂ (c₂ s₂) →
      η₁ (c₁ s₁) ∉ η₁ '' Icc 0 u ∪ η₂ '' Icc 0 r → Γ₁ s₁ = Γ₂ s₂

/-- The joint chart is a joint retained continuation (forgetting the inverse-chart facts). -/
theorem IsJointRetainedChart.isJointRetainedContinuation {κ : ℝ} {h H₀ : LQGMetric.DistOn upperHalfPlaneOpens}
    {η₁ η₂ Γ₁ Γ₂ : ℝ≥0 → ℂ} {ζ₁ ζ₂ U₁ U₂ : ℝ≥0∞} {u r : ℝ≥0}
    (hJ : IsJointRetainedChart κ h H₀ η₁ ζ₁ u η₂ ζ₂ r Γ₁ Γ₂ U₁ U₂) :
    IsJointRetainedContinuation κ h H₀ η₁ ζ₁ u η₂ ζ₂ r Γ₁ Γ₂ U₁ U₂ := by
  obtain ⟨φ, ψ, lift, c₁, c₂, σ₁, σ₂, h1, h2, h3, h4, h5, h6, h7, -, -, -, h8, h9, h10, h11, h12, h13, h14, h15,
    h16⟩ := hJ
  exact ⟨φ, ψ, lift, c₁, c₂, σ₁, σ₂, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13,
    fun s hs => (h14 s hs).1, fun s hs => (h15 s hs).1, h16⟩

/-- **The joint carrier with the joint chart** (R47): `Supp9D.JointRetainedPairStatement` with
`IsJointRetainedChart` in place of `IsJointRetainedContinuation`. -/
def JointRetainedChartStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x₁ x₂ θ₁ θ₂ : ℝ, x₂ ≤ x₁ → θ₁ < θ₂ →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁ → IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂ →
    ∀ u r : ℝ≥0,
    ∃ (S : Type) (_ : MeasurableSpace S) (H₀ : S → LQGMetric.DistOn upperHalfPlaneOpens) (Γ₁ Γ₂ : S → ℝ≥0 → ℂ)
      (U₁ U₂ : S → ℝ≥0∞) (M : Set Ω) (β : Ω → BoundaryWord × ℝ) (X : Ω → S)
      (K : Kernel (BoundaryWord × ℝ) S),
      IsRestartCoordinates H₀ Γ₁ Γ₂ U₁ U₂ ∧ MeasurableSet M ∧ Measurable β ∧ Measurable X ∧
      IsMarkovKernel K ∧
      (P.restrict M).map (fun ω => (β ω, X ω)) = (P.restrict M).map β ⊗ₘ K ∧
      (∀ᵐ c ∂(P.restrict M).map β, 0 < c.2 ∧ IsGFFWithBoundaryData (K c) H₀ c.1.fn c.1.jumps ∧
        IsFlowLine κ c.1.fn c.1.jumps c.2 θ₁ (K c) H₀ Γ₁ U₁ ∧ IsFlowLine κ c.1.fn c.1.jumps 0 θ₂ (K c) H₀ Γ₂ U₂) ∧
      ∀ᵐ ω ∂P, Supp7.IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) u (η₂ ω) (ζ₂ ω) r →
        ω ∈ M ∧ IsJointRetainedChart κ (h ω) (H₀ (X ω)) (η₁ ω) (ζ₁ ω) u (η₂ ω) (ζ₂ ω) r
          (Γ₁ (X ω)) (Γ₂ (X ω)) (U₁ (X ω)) (U₂ (X ω))

/-- The joint chart carrier gives the landed joint carrier. -/
theorem jointRetainedPairStatement_of_chart (hJ : JointRetainedChartStatement.{u}) :
    Supp9D.JointRetainedPairStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ Ω _ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ u r
  obtain ⟨S, mS, H₀, Γ₁, Γ₂, U₁, U₂, M, β, X, K, hco, hM, hβ, hX, hK, hlaw, hdis, hpath⟩ :=
    hJ κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ u r
  refine ⟨S, mS, H₀, Γ₁, Γ₂, U₁, U₂, M, β, X, K, hco, hM, hβ, hX, hK, hlaw, hdis, ?_⟩
  filter_upwards [hpath] with ω hω hord
  exact ⟨(hω hord).1, (hω hord).2.isJointRetainedContinuation⟩

/-- **The joint chart carrier from the retained-pair restart input** (`Supp7.RetainedPairRestartStatement`): the proof
of `Supp7.jointRetainedPairStatement_of_restart`, keeping the inverse-chart facts of the retained chart. -/
theorem jointRetainedChartStatement_of_restart (hR : RetainedPairRestartStatement.{u}) :
    JointRetainedChartStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ Ω _ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ u r
  obtain ⟨d, hd, hu, hr, hag⟩ := exists_retData_of_isFlowLine hκ hκ4 hη₁ hη₂ u r
  subst hu hr
  obtain ⟨S, mS, H₀, Γ₁, Γ₂, U₁, U₂, M, β, X, K, hco, hM, hβ, hX, hK, hdis, hlaw, hpath⟩ :=
    hR κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ d hd hag
  refine ⟨S, mS, H₀, Γ₁, Γ₂, U₁, U₂, M, β, X, K, hco, hM, hβ, hX, hK, hdis, hlaw, ?_⟩
  filter_upwards [hpath, hag] with ω hω hagω hord
  obtain ⟨hG, ha₁, ha₂⟩ := hagω hord.1 hord.2.1
  have hE := hd.mem_E_of_ordinary hG ha₁ ha₂ hord
  obtain ⟨hMω, hHX, ⟨c₁, σ₁, hσ₁, hmono₁, himg₁, hpth₁, hH₁⟩, ⟨c₂, σ₂, hσ₂, hmono₂, himg₂, hpth₂, hH₂⟩, -⟩ :=
    hω hord
  have hg := hd.good ω (RetData.E_subset_G hE)
  obtain ⟨-, hC⟩ := hd.isRetChart hE
  have e₁ : EqOn (d.η₁ ω) (η₁ ω) (Icc 0 d.u) := fun s hs => ha₁ s hs.2
  have e₂ : EqOn (d.η₂ ω) (η₂ ω) (Icc 0 d.r) := fun t ht => ha₂ t ht.2
  have hdom := activeDomain_congr_Icc e₁ e₂
  have htip : d.η₂ ω d.r = η₂ ω d.r := ha₂ d.r le_rfl
  have htr := hd.isChartTransport_chartField κ h ω
  rw [RetData.chart_of_mem hE, ← hHX] at htr
  refine ⟨hMω, d.fwd ω, d.inv ω, d.lift ω, c₁, c₂, σ₁, σ₂, ?_, ?_, hC.fwd_inv, ?_, ?_, ?_, htr,
    hC.continuousOn_inv, hC.2.2.2.2.2.2.2.2.2.1, ?_, hσ₁, hmono₁, himg₁, hσ₂, hmono₂, himg₂,
    fun s hs => ⟨hpth₁ s hs, hH₁ s hs⟩, fun s hs => ⟨hpth₂ s hs, hH₂ s hs⟩, ?_⟩
  · rw [← hdom, ← htip]; exact hC.isActiveChart hg.2.2.2.2.2.1
  · rw [← hdom]; exact hC.bijOn hg.2.2.2.2.2.1
  · rw [← hdom]; exact hC.inv_notMem hg.2.2.2.2.2.1
  · rw [← hdom]; exact hC.continuousOn_lift hg.2.2.2.2.2.1
  · rw [← hdom]; exact hC.deriv_eq hg.2.2.2.2.2.1
  · rw [← htip]; exact hC.inv_zero hg.2.2.2.2.2.1
  · intro s₁ s₂ hs₁ hs₂ he hA
    have hψ : d.inv ω (Γ₁ (X ω) s₁) = d.inv ω (Γ₂ (X ω) s₂) := by rw [← hpth₁ s₁ hs₁, ← hpth₂ s₂ hs₂, he]
    have hK : d.inv ω (Γ₁ (X ω) s₁) ∉ prefixSet (d.η₁ ω) d.u (d.η₂ ω) d.r := by
      rw [prefixSet_congr_Icc e₁ e₂, ← hpth₁ s₁ hs₁]; exact hA
    exact eq_of_inv_eq_of_notMem hC hg.1 hg.2.1 hg.2.2.2.2.1 hg.2.2.2.2.2.1 (hH₁ s₁ hs₁) (hH₂ s₂ hs₂) hψ hK

/-- The joint chart carrier from the clock-supplied retained kernel (PROVE-G7B). -/
theorem jointRetainedChartStatement_of_kernelClock (hR : RetainedKernelClockStatement.{u}) :
    JointRetainedChartStatement.{u} :=
  jointRetainedChartStatement_of_restart (retainedPairRestartStatement_of_clock hR)

/-- **The joint chart carrier from Theorems 1.2 (param), 1.3 and PROVE-CONDDET's two-tip P-side input**
`Restart.RetainedCanonCondDetStatement` (the retained pair's conditional field, outer word and (Det) for both
continuations; its (Det) clause is PROVE-DOMAINMARKOV's domain-Markov step). R43: downstream of Theorem 1.2. -/
theorem jointRetainedChartStatement_of_param (h12p : Exist.Staged.Theorem12ParamStatement.{0})
    (h13 : Exist.Theorem13Statement.{0}) (hD : RetainedCanonCondDetStatement.{u}) :
    JointRetainedChartStatement.{u} :=
  jointRetainedChartStatement_of_kernelClock (retainedKernelClockStatement_of_param h12p h13 hD)

/-! ### Chart-side completability -/

/-- **The stopped chart tangle has ordered proper completions which avoid the other seed** (the property that G2,
G2b and G9 give the reference and G3 / G7a transfer to the actual stopped pair; W0's `HasOrderedProperCompletions` for
the chart prefixes `g₁([0, s₁])`, `g₂([0, s₂])`, with G10's seed condition). -/
def IsChartCompletable (g₁ : ℝ≥0 → ℂ) (s₁ : ℝ≥0) (g₂ : ℝ≥0 → ℂ) (s₂ : ℝ≥0) : Prop :=
  ∃ γ₁ γ₂ : ℝ≥0 → ℂ, IsProperCompletion g₁ s₁ γ₁ ∧ IsProperCompletion g₂ s₂ γ₂ ∧
    range γ₂ ⊆ closedLeftSide γ₁ ∧ g₁ 0 ∉ range γ₂ ∧ g₂ 0 ∉ range γ₁

/-- **The interior local completion property of a chart pair**: every pair of available chart prefixes which stay
in `ℍ` after their seeds is completable. For the chart pair at a retained pair this is the conclusion of Lemma G3
(interior two-tip comparison) with the G2 reference (G2b for the seed condition) and Lemma G1, for every buffer
around the two prefixes. -/
def ChartInteriorCompletion (g₁ : ℝ≥0 → ℂ) (U₁ : ℝ≥0∞) (g₂ : ℝ≥0 → ℂ) (U₂ : ℝ≥0∞) : Prop :=
  ∀ s₁ s₂ : ℝ≥0, (s₁ : ℝ≥0∞) < U₁ → (s₂ : ℝ≥0∞) < U₂ → (∀ t, 0 < t → t ≤ s₁ → g₁ t ∈ H) →
    (∀ t, 0 < t → t ≤ s₂ → g₂ t ∈ H) → IsChartCompletable g₁ s₁ g₂ s₂

/-- Completability passes to shorter prefixes. -/
theorem IsChartCompletable.mono {g₁ g₂ : ℝ≥0 → ℂ} {s₁ s₂ s₁' s₂' : ℝ≥0} (h : IsChartCompletable g₁ s₁ g₂ s₂)
    (h₁ : s₁' ≤ s₁) (h₂ : s₂' ≤ s₂) : IsChartCompletable g₁ s₁' g₂ s₂' := by
  obtain ⟨γ₁, γ₂, hγ₁, hγ₂, hord, hs₁, hs₂⟩ := h
  exact ⟨γ₁, γ₂, ⟨hγ₁.1, hγ₁.2.1, hγ₁.2.2.1, hγ₁.2.2.2.1, fun t ht => hγ₁.2.2.2.2 t (ht.trans h₁)⟩,
    ⟨hγ₂.1, hγ₂.2.1, hγ₂.2.2.1, hγ₂.2.2.2.1, fun t ht => hγ₂.2.2.2.2 t (ht.trans h₂)⟩, hord, hs₁, hs₂⟩

/-- **G10 in the interior case**: if the chart prefixes stay in `ℍ` after their (real) seeds, completable prefixes
have ordered proper completions which stay in `ℍ` after time `0`. -/
theorem exists_interior_completions {g₁ g₂ : ℝ≥0 → ℂ} {s₁ s₂ : ℝ≥0} (hC : IsChartCompletable g₁ s₁ g₂ s₂)
    (h10 : (g₁ 0).im = 0) (hg₁ : ∀ t, 0 < t → t ≤ s₁ → g₁ t ∈ H) (hg₂ : ∀ t, 0 < t → t ≤ s₂ → g₂ t ∈ H) :
    ∃ γ₁ γ₂ : ℝ≥0 → ℂ, IsProperCompletion g₁ s₁ γ₁ ∧ IsProperCompletion g₂ s₂ γ₂ ∧
      range γ₂ ⊆ closedLeftSide γ₁ ∧ (∀ t, 0 < t → γ₁ t ∈ H) ∧ (∀ t, 0 < t → γ₂ t ∈ H) := by
  obtain ⟨αh, βh, hα, hβ, hord, hαβ, hβα⟩ := hC
  obtain ⟨α', β', h1, h2, h3, h4, h5, h6, h7⟩ :=
    Supp7.exists_interiorized_completions_of_seeds hα hβ h10 hord hαβ hβα
  -- the real points of the stopped prefixes are the two seeds
  have hreal : ∀ z ∈ g₁ '' Iic s₁ ∪ g₂ '' Iic s₂, z.im = 0 → z = g₁ 0 ∨ z = g₂ 0 := by
    rintro z (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩) hz
    · rcases eq_zero_or_pos t with rfl | htp
      · exact Or.inl rfl
      · exact absurd hz (ne_of_gt (show (0 : ℝ) < (g₁ t).im from hg₁ t htp ht))
    · rcases eq_zero_or_pos t with rfl | htp
      · exact Or.inr rfl
      · exact absurd hz (ne_of_gt (show (0 : ℝ) < (g₂ t).im from hg₂ t htp ht))
  refine ⟨α', β', h1, h2, h3, fun t ht => ?_, fun t ht => ?_⟩
  · rcases (h1.2.2.1 t).lt_or_eq with hpos | hzero
    · exact hpos
    · exfalso
      rcases hreal _ (h6 t hzero.symm) hzero.symm with he | he
      · have : t = 0 := h1.2.1 (by rw [he, h1.2.2.2.2 0 zero_le])
        exact (ne_of_gt ht) this
      · exact h5 ⟨t, he⟩
  · rcases (h2.2.2.1 t).lt_or_eq with hpos | hzero
    · exact hpos
    · exfalso
      rcases hreal _ (h7 t hzero.symm) hzero.symm with he | he
      · exact h4 ⟨t, he⟩
      · have : t = 0 := h2.2.1 (by rw [he, h2.2.2.2.2 0 zero_le])
        exact (ne_of_gt ht) this

end RLC

end InteractingSLE
