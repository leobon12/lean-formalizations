/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB6
import InteractingSLE.Spec.Restart.Carrier
import InteractingSLE.Spec.Dimension.TraceBridge

/-!
# Proposition GB6: the conditional-law half as a restart carrier, and the first-contact assertion from it

Packet PROVE-GB6B. Supplement §8.6, Proposition GB6 (`source/spec/p481-528.md` L929–L975, pp. 518–520):

> "Let `U` be the flow's own target component, containing the original counterflow seed `y` and incident to `p`.
> Conditional on the marked prefix, the portion of `η` before its first contact with `α[0, σ]`, in the chart of `U`
> taking `(y, p)` to `(0, ∞)`, is the complete canonical counterflow of the conditional component field. Its relative
> lifetime is infinite. The original first-contact time is finite and its contact point is exactly `p`."

The first two sentences (the **conditional-law half**) are stated here in the form of the project's restart carriers
(`Restart.FirstContactRestartStatement`, `Supp7.G7RetainedPairStatement`): one regular conditional law of an explicit
restart variable, and a pathwise identification. The third sentence (the **first-contact assertion**,
`GB6FirstContactStatement`) is then **proved** from it: this is the source's endpoint argument ("Reference transience
and the continuous inverse at infinity now give the physical endpoint `p`. It differs from the original terminal point
`x`, so original transience excludes `T = ∞`. Thus `T` is finite and `η(T) = p`").

Everything is read in the original flow chart `(ℍ, 0, ∞)`, as in `GB6.lean`. The chart of `U` is
`ownComponentChart Wα σ = I ∘ f_σ` (`Spec/Jordan/Coupling.lean`): it takes `y = ∞` to `0` and the tip `p = α(σ)` to `∞`
(`tendsto_ownComponentChart_inv_tip`).

## Main definitions

* `firstContactTime η A`: the first time the path `η` meets `A` (`⊤` if never);
* `IsGB6RestartCoordinates`, `IsGB6ConditionalCounterflow` (the kernel at one conditional word: the chart field is a
  GFF with that word and the chart path is its complete canonical counterflow, with infinite relative lifetime and a
  complete continuous transient trace), `IsGB6ChartContinuation` (the pathwise identification: chart field, capacity
  clock onto `[0, T)`, `T` the first contact, and `η ∘ ℓ = U-chart⁻¹ ∘ Γ` at interior chart times);
* **`GB6RestartStatement`**: GB6's conditional-law half at every deterministic own time (a named statement, not proved
  here; see the handoff `planning/handoffs/PROVE-GB6B.md` for what its proof needs).

## Main results

* `isFirstContactAtTip_of_chart`: the deterministic endpoint argument;
* **`gb6FirstContactStatement_of_restart`**: `GB6RestartStatement → GB6FirstContactStatement`;
* `ae_reverseVisit_of_gb6Restart`: GB6's final assertion (containment and reverse first visits) from the carrier.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

universe u

namespace InteractingSLE

namespace Supp8

namespace GB6

open Sec7.Aux130 (firstVisit)

/-! ### The first-contact time -/

/-- The first time at which the path `η` meets the set `A` (`⊤` if it never does). -/
def firstContactTime {X : Type*} (η : ℝ≥0 → X) (A : Set X) : ℝ≥0∞ :=
  ⨅ (t : ℝ≥0) (_ : η t ∈ A), (t : ℝ≥0∞)

theorem notMem_of_lt_firstContactTime {X : Type*} {η : ℝ≥0 → X} {A : Set X} {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < firstContactTime η A) : η t ∉ A := fun hA =>
  (iInf₂_le t hA : firstContactTime η A ≤ t).not_gt ht

/-! ### The chart of the flow's own component at infinity -/

/-- **The inverse own-component chart tends to the tip at `∞`** (frozen generating trace form of
`isRealizedAt_tip_ownComponentChart`): `f_σ⁻¹(−1/w) → α(σ)` as `w → ∞` in `ℍ`, for every own time `σ` before the
lifetime. -/
theorem tendsto_ownComponentChart_inv_tip {w : ℝ≥0 → ℝ} {T : ℝ≥0∞} {α : ℝ≥0 → ℂ}
    (hα : IsGeneratingTrace w T α) (hw : ContinuousOn w {s | (s : ℝ≥0∞) < T}) (hw0 : w 0 = 0)
    {s : ℝ≥0} (hs : (s : ℝ≥0∞) < T) :
    Tendsto (ownComponentChart (fun r : ℝ => w r.toNNReal) s).2.1 (Bornology.cobounded ℂ ⊓ 𝓟 H)
      (𝓝 (α s)) := by
  have hR : Tendsto (fun w : ℂ => -w⁻¹) (Bornology.cobounded ℂ ⊓ 𝓟 H) (𝓝[H] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, mem_inf_of_right fun w hw =>
      Chart.isConformal_infinitySourceChart.2.1 hw⟩
    have := ((tendsto_inv₀_cobounded (α := ℂ)).neg).mono_left (inf_le_left (b := 𝓟 H))
    simpa using this
  exact (hα.tendsto_fwdMapInv_tip hw hw0 hs).comp hR

/-- The physical counterflow `R̂ ∘ γ` of a transient trace `γ` tends to the original target `x = 0`. -/
theorem tendsto_sphereInv_of_tendsto_norm {γ : ℝ≥0 → ℂ} (hγ : Tendsto (fun t => ‖γ t‖) atTop atTop) :
    Tendsto (fun t => sphereInv (γ t : OnePoint ℂ)) atTop (𝓝 ((0 : ℂ) : OnePoint ℂ)) := by
  have hcob : Tendsto γ atTop (Bornology.cobounded ℂ) := tendsto_norm_atTop_iff_cobounded.1 hγ
  exact (continuous_sphereInv.tendsto OnePoint.infty).comp (tendsto_coe_cobounded_onePointC.comp hcob)

/-! ### The deterministic endpoint argument -/

/-- The closed ball of `ℂ` seen in the sphere is closed. -/
theorem isClosed_coe_closedBall (p : ℂ) (ε : ℝ) :
    IsClosed (((↑) : ℂ → OnePoint ℂ) '' Metric.closedBall p ε) :=
  ((isCompact_closedBall p ε).image OnePoint.continuous_coe).isClosed

/-- **The chart path at infinity gives the tip.** Let `F : ℍ → U` be an inverse chart with `F(w) → p` as `w → ∞`
in `ℍ`, let `Γ` be a continuous chart path with `|Γ| → ∞` whose interior times are dense, and let the physical path
satisfy `η(ℓ(u)) = F(Γ(u))` at every interior chart time `u`, for a continuous clock `ℓ`. Then `η(ℓ(u)) → p`. -/
theorem tendsto_comp_clock_of_chart {η : ℝ≥0 → OnePoint ℂ} {F : ℂ → ℂ} {p : ℂ} {Γ : ℝ≥0 → ℂ}
    {ℓ : ℝ≥0 → ℝ≥0} (hη : Continuous η) (hF : Tendsto F (Bornology.cobounded ℂ ⊓ 𝓟 H) (𝓝 p))
    (hΓ : Tendsto (fun u => ‖Γ u‖) atTop atTop) (hΓH : ∀ a b : ℝ≥0, a < b → ∃ v ∈ Ioo a b, Γ v ∈ H)
    (hℓc : Continuous ℓ) (hrel : ∀ u, Γ u ∈ H → η (ℓ u) = (F (Γ u) : OnePoint ℂ)) :
    Tendsto (fun u => η (ℓ u)) atTop (𝓝 (p : OnePoint ℂ)) := by
  rw [← OnePoint.isOpenEmbedding_coe.map_nhds_eq]
  refine (Metric.nhds_basis_closedBall.map _).tendsto_right_iff.2 fun ε hε => ?_
  have hmem : {w | F w ∈ Metric.ball p ε} ∈ Bornology.cobounded ℂ ⊓ 𝓟 H :=
    hF (Metric.ball_mem_nhds p hε)
  rw [mem_inf_principal] at hmem
  have hcob : Tendsto Γ atTop (Bornology.cobounded ℂ) := tendsto_norm_atTop_iff_cobounded.1 hΓ
  obtain ⟨u₀, hu₀⟩ := eventually_atTop.1 (hcob.eventually hmem)
  refine eventually_atTop.2 ⟨u₀, fun u hu => ?_⟩
  -- `u` is a limit of interior chart times above `u₀`
  have hcl : u ∈ closure {v | u₀ ≤ v ∧ Γ v ∈ H} := by
    rw [Metric.mem_closure_iff]
    intro δ hδ
    have hlt : u < u + (δ / 2).toNNReal := lt_add_of_pos_right u (Real.toNNReal_pos.2 (by linarith))
    obtain ⟨v, hv, hvH⟩ := hΓH u _ hlt
    refine ⟨v, ⟨hu.trans hv.1.le, hvH⟩, ?_⟩
    rw [NNReal.dist_eq, abs_sub_comm, abs_of_pos (sub_pos.2 (NNReal.coe_lt_coe.2 hv.1))]
    have h2 : (v : ℝ) < u + δ / 2 := by
      have := NNReal.coe_lt_coe.2 hv.2
      rwa [NNReal.coe_add, Real.coe_toNNReal _ (by linarith)] at this
    linarith
  have himg : (fun u => η (ℓ u)) '' {v | u₀ ≤ v ∧ Γ v ∈ H} ⊆
      ((↑) : ℂ → OnePoint ℂ) '' Metric.closedBall p ε := by
    rintro _ ⟨v, ⟨hv, hvH⟩, rfl⟩
    exact ⟨F (Γ v), Metric.ball_subset_closedBall (hu₀ v hv hvH), (hrel v hvH).symm⟩
  exact closure_minimal himg (isClosed_coe_closedBall p ε)
    (image_closure_subset_closure_image (hη.comp hℓc) ⟨u, hcl, rfl⟩)

/-- **GB6's endpoint argument** (deterministic form). Let `η` be a continuous physical counterflow in the sphere with
`η(t) → x = 0` (original transience), `α` a flow path with interior tip `α(s) ∈ ℍ`, and `F` the inverse chart of its own
component, with `F(w) → α(s)` as `w → ∞` in `ℍ`. Suppose a capacity clock `ℓ` (continuous, strictly increasing) maps
`[0, ∞)` onto `[0, T)`, `T` the first contact of `η` with `α([0, s])`, and `η ∘ ℓ = F ∘ Γ` at the interior times of a
continuous transient chart path `Γ` with dense interior times. Then `T` is finite and `η(T) = α(s)`: `η` first meets
`α([0, s])` at its tip. -/
theorem isFirstContactAtTip_of_chart {η : ℝ≥0 → OnePoint ℂ} {α : ℝ≥0 → ℂ} {s : ℝ≥0} {F : ℂ → ℂ}
    {Γ : ℝ≥0 → ℂ} {ℓ : ℝ≥0 → ℝ≥0} (hη : Continuous η)
    (hη0 : Tendsto η atTop (𝓝 ((0 : ℂ) : OnePoint ℂ))) (hsH : α s ∈ H)
    (hF : Tendsto F (Bornology.cobounded ℂ ⊓ 𝓟 H) (𝓝 (α s)))
    (hΓ : Tendsto (fun u => ‖Γ u‖) atTop atTop) (hΓH : ∀ a b : ℝ≥0, a < b → ∃ v ∈ Ioo a b, Γ v ∈ H)
    (hℓc : Continuous ℓ) (hℓm : StrictMono ℓ)
    (hℓr : range ℓ = {t : ℝ≥0 | (t : ℝ≥0∞) < firstContactTime η ((fun t => (α t : OnePoint ℂ)) '' Icc 0 s)})
    (hrel : ∀ u, Γ u ∈ H → η (ℓ u) = (F (Γ u) : OnePoint ℂ)) :
    IsFirstContactAtTip η (fun t => (α t : OnePoint ℂ)) s := by
  have hlim := tendsto_comp_clock_of_chart hη hF hΓ hΓH hℓc hrel
  set A := (fun t => (α t : OnePoint ℂ)) '' Icc 0 s with hA
  rcases eq_top_or_lt_top (firstContactTime η A) with hT | hT
  · -- `T = ∞`: the clock is onto `[0, ∞)`, and original transience gives the endpoint `x = 0 ≠ α(s)`
    exfalso
    have hsurj : ∀ t : ℝ≥0, ∃ u, ℓ u = t := fun t => by
      have : t ∈ range ℓ := by rw [hℓr, hT]; exact ENNReal.coe_lt_top
      exact this
    have hℓ : Tendsto ℓ atTop atTop := tendsto_atTop_atTop.2 fun t => by
      obtain ⟨u₀, hu₀⟩ := hsurj t
      exact ⟨u₀, fun u hu => hu₀ ▸ hℓm.monotone hu⟩
    have h0 := tendsto_nhds_unique hlim (hη0.comp hℓ)
    have hα0 : α s = 0 := OnePoint.coe_injective h0
    have h0H : (0 : ℂ).im > 0 := hα0 ▸ hsH
    simp at h0H
  · -- `T < ∞`: the clock tends to `T`, and continuity of `η` gives `η(T) = α(s)`
    obtain ⟨T, hTe⟩ : ∃ T : ℝ≥0, firstContactTime η A = T := ⟨_, (ENNReal.coe_toNNReal hT.ne).symm⟩
    have hrange : ∀ t : ℝ≥0, t ∈ range ℓ ↔ t < T := fun t => by
      rw [hℓr, hTe]
      exact ENNReal.coe_lt_coe
    have hℓT : Tendsto ℓ atTop (𝓝 T) := by
      refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩
      · obtain ⟨u₀, hu₀⟩ := (hrange a).2 ha
        exact eventually_atTop.2 ⟨u₀ + 1, fun u hu => hu₀ ▸ hℓm (lt_of_lt_of_le (lt_add_one u₀) hu)⟩
      · exact Eventually.of_forall fun u => ((hrange (ℓ u)).1 ⟨u, rfl⟩).trans hb
    have hT' := tendsto_nhds_unique ((hη.tendsto T).comp hℓT) hlim
    refine ⟨T, hT', fun t ht => notMem_of_lt_firstContactTime ?_⟩
    rw [hTe]
    exact ENNReal.coe_lt_coe.2 ht

/-! ### Transient chart paths with dense interior times, read at rational times -/

/-- A chart path is **transient with dense interior times**, read at rational times (a measurable condition on a
canonical space): `|Γ(q)| → ∞` along rational times, and every open rational interval of `[0, ∞)` contains a rational
time with `Γ(q) ∈ ℍ`. -/
def TransientDenseQ (Γ : ℝ≥0 → ℂ) : Prop :=
  (∀ R : ℕ, ∃ N : ℕ, ∀ q : ℚ, (N : ℝ) ≤ q → (R : ℝ) ≤ ‖Γ (q : ℝ).toNNReal‖) ∧
    ∀ a b : ℚ, 0 ≤ a → a < b → ∃ q : ℚ, a < q ∧ q < b ∧ Γ (q : ℝ).toNNReal ∈ H

theorem measurableSet_transientDenseQ {S : Type*} [MeasurableSpace S] {Γ : S → ℝ≥0 → ℂ}
    (hΓ : ∀ t, Measurable fun x => Γ x t) : MeasurableSet {x | TransientDenseQ (Γ x)} := by
  have hH : MeasurableSet H := QuantumZipper.isOpen_H.measurableSet
  have h1 : ∀ (R : ℕ) (q : ℚ), Measurable fun x => (R : ℝ) ≤ ‖Γ x (q : ℝ).toNNReal‖ := fun R q =>
    measurableSet_setOfPred.1 (measurableSet_le measurable_const (hΓ _).norm)
  have h2 : ∀ q : ℚ, Measurable fun x => Γ x (q : ℝ).toNNReal ∈ H := fun q =>
    measurableSet_setOfPred.1 ((hΓ _) hH)
  refine measurableSet_setOfPred.2 (Measurable.and ?_ ?_)
  · exact Measurable.forall fun R => Measurable.exists fun N => Measurable.forall fun q =>
      Measurable.imp measurable_const (h1 R q)
  · exact Measurable.forall fun a => Measurable.forall fun b => Measurable.imp measurable_const
      (Measurable.imp measurable_const (Measurable.exists fun q => Measurable.and measurable_const
        (Measurable.and measurable_const (h2 q))))

/-- The rational condition gives real transience, for a continuous path. -/
theorem TransientDenseQ.tendsto_norm {Γ : ℝ≥0 → ℂ} (hΓc : Continuous Γ) (h : TransientDenseQ Γ) :
    Tendsto (fun u => ‖Γ u‖) atTop atTop := by
  refine tendsto_atTop.2 fun R => ?_
  obtain ⟨N, hN⟩ := h.1 ⌈R⌉₊
  refine eventually_atTop.2 ⟨(N : ℝ≥0), fun u hu => ?_⟩
  have hclosed : IsClosed {t : ℝ≥0 | (⌈R⌉₊ : ℝ) ≤ ‖Γ t‖} :=
    isClosed_le continuous_const (continuous_norm.comp hΓc)
  have hcl : u ∈ closure {t : ℝ≥0 | (⌈R⌉₊ : ℝ) ≤ ‖Γ t‖} := by
    rw [Metric.mem_closure_iff]
    intro δ hδ
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show (u : ℝ) < u + δ by linarith)
    have hq0 : (0 : ℝ) ≤ q := u.coe_nonneg.trans hq1.le
    have hNu : (N : ℝ) ≤ u := by exact_mod_cast hu
    refine ⟨(q : ℝ).toNNReal, hN q (hNu.trans hq1.le), ?_⟩
    rw [NNReal.dist_eq, Real.coe_toNNReal _ hq0, abs_sub_comm, abs_of_pos (by linarith)]
    linarith
  rw [hclosed.closure_eq] at hcl
  exact (Nat.le_ceil R).trans hcl

/-- The rational condition gives interior times in every real interval. -/
theorem TransientDenseQ.exists_mem_H {Γ : ℝ≥0 → ℂ} (h : TransientDenseQ Γ) {a b : ℝ≥0} (hab : a < b) :
    ∃ v ∈ Ioo a b, Γ v ∈ H := by
  obtain ⟨q₁, hq₁a, hq₁b⟩ := exists_rat_btwn (NNReal.coe_lt_coe.2 hab)
  obtain ⟨q₂, hq₂a, hq₂b⟩ := exists_rat_btwn hq₁b
  have hq₁0 : (0 : ℝ) ≤ q₁ := a.coe_nonneg.trans hq₁a.le
  obtain ⟨q, hq1, hq2, hqH⟩ := h.2 q₁ q₂ (by exact_mod_cast hq₁0) (by exact_mod_cast hq₂a)
  have hq1' : (q₁ : ℝ) < q := by exact_mod_cast hq1
  have hq2' : (q : ℝ) < q₂ := by exact_mod_cast hq2
  refine ⟨(q : ℝ).toNNReal, ⟨Real.lt_toNNReal_iff_coe_lt.2 (by linarith),
    (Real.toNNReal_lt_iff_lt_coe (by linarith)).2 (by linarith)⟩, hqH⟩

/-- **A complete continuous transient generating trace satisfies the rational condition** (interior times are dense:
a generating trace has no real subarc, `Supp9D.exists_mem_H_of_isGeneratingTrace`). -/
theorem transientDenseQ_of_isGeneratingTrace {w : ℝ≥0 → ℝ} {Γ : ℝ≥0 → ℂ} (hΓ : IsGeneratingTrace w ⊤ Γ)
    (hw : Continuous w) (hw0 : w 0 = 0) (htr : Tendsto (fun t => ‖Γ t‖) atTop atTop) : TransientDenseQ Γ := by
  have hΓc : Continuous Γ := by
    have := hΓ.2.1
    simp only [le_top, ofPred_true] at this
    exact continuousOn_univ.1 this
  refine ⟨fun R => ?_, fun a b ha hab => ?_⟩
  · obtain ⟨u₀, hu₀⟩ := eventually_atTop.1 (tendsto_atTop.1 htr R)
    refine ⟨⌈(u₀ : ℝ)⌉₊, fun q hq => hu₀ _ ?_⟩
    have hq0 : (0 : ℝ) ≤ q := (Nat.cast_nonneg _).trans hq
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hq0]
    exact (Nat.le_ceil _).trans hq
  · have ha' : (0 : ℝ) ≤ a := by exact_mod_cast ha
    have hab' : (a : ℝ) < b := by exact_mod_cast hab
    have hab'' : (a : ℝ).toNNReal < (b : ℝ).toNNReal :=
      (Real.toNNReal_lt_toNNReal_iff (by linarith)).2 hab'
    obtain ⟨z, hz, hzH⟩ := Supp9D.exists_mem_H_of_isGeneratingTrace hΓ hw.continuousOn hw0 hab''
      ENNReal.coe_lt_top
    have hopen : IsOpen ({t : ℝ≥0 | Γ t ∈ H} ∩ Ioo (a : ℝ).toNNReal (b : ℝ).toNNReal) :=
      (QuantumZipper.isOpen_H.preimage hΓc).inter isOpen_Ioo
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hopen z ⟨hzH, hz⟩
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show (z : ℝ) < z + ε by linarith)
    have hq0 : (0 : ℝ) ≤ q := le_trans z.coe_nonneg hq1.le
    have hs : (((q : ℝ).toNNReal : ℝ≥0) : ℝ) = q := Real.coe_toNNReal _ hq0
    have hsU : (q : ℝ).toNNReal ∈ {t : ℝ≥0 | Γ t ∈ H} ∩ Ioo (a : ℝ).toNNReal (b : ℝ).toNNReal := by
      refine hball ?_
      rw [Metric.mem_ball, NNReal.dist_eq, hs, abs_of_pos (by linarith)]
      linarith
    have h1 := (Real.toNNReal_lt_toNNReal_iff' (r := (a : ℝ)) (p := (q : ℝ))).1 hsU.2.1
    have h2 := (Real.toNNReal_lt_toNNReal_iff' (r := (q : ℝ)) (p := (b : ℝ))).1 hsU.2.2
    exact ⟨q, by exact_mod_cast h1.1, by exact_mod_cast h2.1, hsU.1⟩

/-- The driver of a flow line has `W 0 = 0` and is continuous before the lifetime, almost surely. -/
theorem ae_driver_zero_continuousOn {κ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {θ : ℝ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {W : ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞} (hfl : IsFlowLineDriver κ b J θ P h W ζ) :
    ∀ᵐ ω ∂P, W 0 ω = 0 ∧ ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω} := by
  obtain ⟨_, _, _, _, _, _, hC⟩ := hfl
  filter_upwards [hC.1.2.2.2.2] with ω hp
  exact ⟨hp.1, hp.2.2.2.1⟩

/-! ### GB6's conditional-law half: the restart carrier -/

/-- The coordinates of GB6's canonical space: the chart field `H'`, the chart driver `WC` and the chart path `Γ` are
measurable (each time coordinate), and every chart path is continuous. -/
def IsGB6RestartCoordinates {S : Type*} [MeasurableSpace S] (H' : S → LQGMetric.DistOn upperHalfPlaneOpens)
    (WC : ℝ≥0 → S → ℝ) (Γ : S → ℝ≥0 → ℂ) : Prop :=
  Measurable H' ∧ (∀ t, Measurable (WC t)) ∧ (∀ t, Measurable fun x => Γ x t) ∧ ∀ x, Continuous (Γ x)

/-- **The conditional counterflow at one conditional word** (GB6: "is the complete canonical counterflow of the
conditional component field. Its relative lifetime is infinite"): under `Q`, the chart field `H'` (in the
counterflow frame `F = −h − πχ` read in the chart of `U`) is a GFF on `ℍ` with the boundary word `c`, `WC` drives its
centred counterflow — the angle-`0` flow line at parameter `16/κ` — with infinite relative lifetime, and almost
surely `Γ` is a complete continuous transient generating trace of `WC` ("By the complete finite-force theorem this
conditional word has a continuous transient trace of infinite integrated lifetime"). -/
def IsGB6ConditionalCounterflow (κ : ℝ) (c : Restart.BoundaryWord) {S : Type*} [MeasurableSpace S]
    (Q : Measure S) (H' : S → LQGMetric.DistOn upperHalfPlaneOpens) (WC : ℝ≥0 → S → ℝ) (Γ : S → ℝ≥0 → ℂ) :
    Prop :=
  IsGFFWithBoundaryData Q H' c.fn c.jumps ∧ IsFlowLineDriver (16 / κ) c.fn c.jumps 0 Q H' WC (fun _ => ⊤) ∧
    ∀ᵐ x ∂Q, IsGeneratingTrace (fun t => WC t x) ⊤ (Γ x) ∧ Tendsto (fun t => ‖Γ x t‖) atTop atTop

/-- Under the conditional counterflow law, the chart path is almost surely transient with dense interior times. -/
theorem IsGB6ConditionalCounterflow.ae_transientDenseQ {κ : ℝ} {c : Restart.BoundaryWord} {S : Type*}
    [MeasurableSpace S] {Q : Measure S} {H' : S → LQGMetric.DistOn upperHalfPlaneOpens} {WC : ℝ≥0 → S → ℝ}
    {Γ : S → ℝ≥0 → ℂ} (hc : IsGB6ConditionalCounterflow κ c Q H' WC Γ) :
    ∀ᵐ x ∂Q, TransientDenseQ (Γ x) := by
  filter_upwards [hc.2.2, ae_driver_zero_continuousOn hc.2.1] with x ⟨hgen, htr⟩ ⟨hw0, hwc⟩
  have hwc' : Continuous fun t => WC t x := by
    simp only [ENNReal.coe_lt_top, ofPred_true] at hwc
    exact continuousOn_univ.1 hwc
  exact transientDenseQ_of_isGeneratingTrace hgen hwc' hw0 htr

/-- **The pathwise part of GB6's conditional-law half** at own time `s`, for one realization. With `c_U` the chart of
the flow's own component `U = ℍ \ K_s` (`ownComponentChart`, taking `(y, p) = (∞, α(s))` to `(0, ∞)`):
* `H'` is the field `h` read in `c_U` in the counterflow frame (frozen `IsChartTransport` with `σ = −1`, `a = −πχ`,
  `k = χ(16/κ)`, GB6's "common centered frame `F = −h − πχ`" and the inherited lift);
* a capacity clock `ℓ` (continuous, strictly increasing) maps `[0, ∞)` onto `[0, T)`, where `T` is the first contact
  of the physical counterflow `η` with `α([0, s])` ("the portion of `η` before its first contact"; relative lifetime
  infinite);
* at every chart time `u` with `Γ(u) ∈ ℍ`, `η(ℓ(u)) = c_U⁻¹(Γ(u))`. -/
def IsGB6ChartContinuation (κ : ℝ) (h H' : LQGMetric.DistOn upperHalfPlaneOpens) (η : ℝ≥0 → OnePoint ℂ)
    (w : ℝ≥0 → ℝ) (α : ℝ≥0 → ℂ) (s : ℝ≥0) (Γ : ℝ≥0 → ℂ) : Prop :=
  IsChartTransport (ownComponentChart (fun r : ℝ => w r.toNNReal) s) (-1) (-(Real.pi * QuantumZipper.chiC κ))
      (QuantumZipper.chiC (16 / κ)) h H' ∧
    ∃ ℓ : ℝ≥0 → ℝ≥0, Continuous ℓ ∧ StrictMono ℓ ∧
      range ℓ = {t : ℝ≥0 | (t : ℝ≥0∞) < firstContactTime η ((fun t => (α t : OnePoint ℂ)) '' Icc 0 s)} ∧
      ∀ u, Γ u ∈ H → η (ℓ u) = ((ownComponentChart (fun r : ℝ => w r.toNNReal) s).2.1 (Γ u) : OnePoint ℂ)

/-- **Proposition GB6, conditional-law half** (named statement; restart-carrier form), at every deterministic own
time `s`, in the setting of `GB6FirstContactStatement` (verbatim). There are a canonical space `S` with coordinates
`(H', WC, Γ)`, a measurable event `M`, a measurable conditional word `β` (the boundary word of the conditional field
in the chart of `U`), a restart variable `X` and a Markov kernel `K`, such that
* `K` is the conditional law of `X` given `β` on `M`: `(P|M).map (β, X) = (P|M).map β ⊗ₘ K`;
* for almost every word `c`, under `K c` the chart field is a GFF with word `c` and `Γ` is its complete canonical
  counterflow with infinite relative lifetime (`IsGB6ConditionalCounterflow`);
* almost surely on `{s < ζα, α(s) ∈ ℍ}` (an interior tip before the continuation threshold), `ω ∈ M` and the chart
  field, the capacity clock and the identification of `IsGB6ChartContinuation` hold for `X ω`.

Source: "Conditional on the marked prefix, the portion of `η` before its first contact with `α[0, σ]`, in the chart
of `U` taking `(y, p)` to `(0, ∞)`, is the complete canonical counterflow of the conditional component field. Its
relative lifetime is infinite." Conditioning on the word `β` instead of the whole marked prefix is equivalent here
(tower property: the conditional law given the prefix depends on it only through `β`). -/
def GB6RestartStatement : Prop :=
  ∀ (κ θ : ℝ), 0 < κ → κ < 4 → -(Real.pi / 2) ≤ θ → θ ≤ Real.pi / 2 →
  ∀ (Ω : Type u) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P →
  ∀ (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens) (b : ℝ → ℝ) (J : Finset ℝ)
    (W Wα : ℝ≥0 → Ω → ℝ) (ζ ζα : Ω → ℝ≥0∞) (γ α : Ω → ℝ≥0 → ℂ)
    (b' : ℝ → ℝ) (J' : Finset ℝ) (h' : Ω → LQGMetric.DistOn upperHalfPlaneOpens),
    IsPiecewiseConstantBoundaryData b J → IsGFFWithBoundaryData P h b J →
    IsPiecewiseConstantBoundaryData b' J' →
    (∀ ω, IsChartTransport infinitySourceChart (-1) (-(Real.pi * QuantumZipper.chiC κ))
      (QuantumZipper.chiC (16 / κ)) (h ω) (h' ω)) →
    IsFlowLineDriver (16 / κ) b' J' 0 P h' W ζ →
    (∀ i : Fin (flowLineNL b' J' 0),
      -2 < ∑ l ∈ Finset.univ.filter (fun l => l ≤ i), flowLineRhoL (16 / κ) b' J' 0 0 l) →
    (∀ i : Fin (flowLineNR b' J' 0),
      -2 < ∑ l ∈ Finset.univ.filter (fun l => l ≤ i), flowLineRhoR (16 / κ) b' J' 0 0 l) →
    (∀ᵐ ω ∂P, ζ ω = ⊤ ∧ IsGeneratingTrace (fun t => W t ω) ⊤ (γ ω) ∧
      Tendsto (fun t => ‖γ ω t‖) atTop atTop) →
    IsFlowLineDriver κ b J θ P h Wα ζα →
    (∀ᵐ ω ∂P, IsGeneratingTrace (fun t => Wα t ω) (ζα ω) (α ω)) →
    ∀ s : ℝ≥0, ∃ (S : Type) (_ : MeasurableSpace S) (H' : S → LQGMetric.DistOn upperHalfPlaneOpens)
      (WC : ℝ≥0 → S → ℝ) (Γ : S → ℝ≥0 → ℂ) (M : Set Ω) (β : Ω → Restart.BoundaryWord) (X : Ω → S)
      (K : Kernel Restart.BoundaryWord S),
      IsGB6RestartCoordinates H' WC Γ ∧ MeasurableSet M ∧ Measurable β ∧ Measurable X ∧ IsMarkovKernel K ∧
      (P.restrict M).map (fun ω => (β ω, X ω)) = (P.restrict M).map β ⊗ₘ K ∧
      (∀ᵐ c ∂(P.restrict M).map β, IsGB6ConditionalCounterflow κ c (K c) H' WC Γ) ∧
      ∀ᵐ ω ∂P, (s : ℝ≥0∞) < ζα ω → α ω s ∈ H →
        ω ∈ M ∧ IsGB6ChartContinuation κ (h ω) (H' (X ω)) (fun t => sphereInv (γ ω t : OnePoint ℂ))
          (fun t => Wα t ω) (α ω) s (Γ (X ω))

/-! ### The first-contact assertion from the conditional-law half -/

/-- **Proposition GB6, first-contact assertion, from its conditional-law half** (conditional helper with a distinct
name): the restart carrier `GB6RestartStatement` implies `GB6FirstContactStatement`. The kernel event "the chart path
is transient with dense interior times" (measurable, `measurableSet_transientDenseQ`) has conditional probability one
(complete transient trace of the conditional counterflow) and is integrated back (`Restart.ae_mem_of_compProd_eq`);
then the deterministic endpoint argument `isFirstContactAtTip_of_chart` applies on the event of an interior tip. -/
theorem gb6FirstContactStatement_of_restart (hR : GB6RestartStatement.{u}) : GB6FirstContactStatement.{u} := by
  intro κ θ hκ hκ4 hθ₁ hθ₂ Ω mΩ P hP h b J W Wα ζ ζα γ α b' J' h' hb hG hb' htr hcf hadmL hadmR hcomp hfl hα s
  obtain ⟨S, mS, H', WC, Γ, M, β, X, K, hcoord, hM, hβ, hX, hK, hlaw, hcond, hpath⟩ :=
    hR κ θ hκ hκ4 hθ₁ hθ₂ Ω mΩ P hP h b J W Wα ζ ζα γ α b' J' h' hb hG hb' htr hcf hadmL hadmR hcomp hfl hα s
  have hKE : ∀ᵐ c ∂(P.restrict M).map β, ∀ᵐ x ∂(K c), x ∈ {x | TransientDenseQ (Γ x)} := by
    filter_upwards [hcond] with c hc
    exact hc.ae_transientDenseQ
  have hXE := Restart.ae_mem_of_compProd_eq hM hβ hX hlaw (measurableSet_transientDenseQ hcoord.2.2.1) hKE
  filter_upwards [hcomp, hα, ae_driver_zero_continuousOn hfl, hpath, hXE] with ω hcω hαω hpω hpathω hXω hsζ hsH
  obtain ⟨hMω, -, ℓ, hℓc, hℓm, hℓr, hrel⟩ := hpathω hsζ hsH
  have hΓq : TransientDenseQ (Γ (X ω)) := hXω hMω
  have hγc : Continuous (γ ω) := by
    have := hcω.2.1.2.1
    simp only [le_top, ofPred_true] at this
    exact continuousOn_univ.1 this
  exact isFirstContactAtTip_of_chart (continuous_sphereInv.comp (OnePoint.continuous_coe.comp hγc))
    (tendsto_sphereInv_of_tendsto_norm hcω.2.2) hsH (tendsto_ownComponentChart_inv_tip hαω hpω.2 hpω.1 hsζ)
    (hΓq.tendsto_norm (hcoord.2.2.2 (X ω))) (fun _ _ hab => hΓq.exists_mem_H hab) hℓc hℓm hℓr hrel

/-- **GB6's final assertion from its conditional-law half** (conditional helper): for a complete constant-angle flow
line, almost surely every flow point lies in the closure of the physical counterflow range, and the points are first
visited in reverse flow order. -/
theorem ae_reverseVisit_of_gb6Restart (hR : GB6RestartStatement.{u}) {κ θ : ℝ} (hκ : 0 < κ)
    (hκ4 : κ < 4) (hθ₁ : -(Real.pi / 2) ≤ θ) (hθ₂ : θ ≤ Real.pi / 2) {Ω : Type u} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {b : ℝ → ℝ}
    {J : Finset ℝ} {W Wα : ℝ≥0 → Ω → ℝ} {ζ ζα : Ω → ℝ≥0∞} {γ α : Ω → ℝ≥0 → ℂ} {b' : ℝ → ℝ} {J' : Finset ℝ}
    {h' : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hb : IsPiecewiseConstantBoundaryData b J)
    (hG : IsGFFWithBoundaryData P h b J) (hb' : IsPiecewiseConstantBoundaryData b' J')
    (htr : ∀ ω, IsChartTransport infinitySourceChart (-1) (-(Real.pi * QuantumZipper.chiC κ))
      (QuantumZipper.chiC (16 / κ)) (h ω) (h' ω))
    (hcf : IsFlowLineDriver (16 / κ) b' J' 0 P h' W ζ)
    (hadmL : ∀ i : Fin (flowLineNL b' J' 0),
      -2 < ∑ l ∈ Finset.univ.filter (fun l => l ≤ i), flowLineRhoL (16 / κ) b' J' 0 0 l)
    (hadmR : ∀ i : Fin (flowLineNR b' J' 0),
      -2 < ∑ l ∈ Finset.univ.filter (fun l => l ≤ i), flowLineRhoR (16 / κ) b' J' 0 0 l)
    (hcomp : ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ IsGeneratingTrace (fun t => W t ω) ⊤ (γ ω) ∧
      Tendsto (fun t => ‖γ ω t‖) atTop atTop)
    (hfl : IsFlowLineDriver κ b J θ P h Wα ζα)
    (hα : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => Wα t ω) (ζα ω) (α ω)) (hζα : ∀ᵐ ω ∂P, ζα ω = ⊤) :
    ∀ᵐ ω ∂P, (∀ t, (α ω t : OnePoint ℂ) ∈ closure (range fun t => sphereInv (γ ω t : OnePoint ℂ))) ∧
      Antitone fun t => firstVisit (fun t => sphereInv (γ ω t : OnePoint ℂ)) ((α ω t : ℂ) : OnePoint ℂ) :=
  ae_reverseVisit_of_gb6FirstContactStatement (gb6FirstContactStatement_of_restart hR) hκ hκ4 hθ₁ hθ₂ hb hG hb'
    htr hcf hadmL hadmR hcomp hfl hα hζα

end GB6

end Supp8

end InteractingSLE
