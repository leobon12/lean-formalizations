/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.W0bSelect
import InteractingSLE.Spec.Supplement.S9Propagation
import InteractingSLE.Spec.Sec7.ReverseArcAux70
import InteractingSLE.Spec.Sec4.Heights
import InteractingSLE.Spec.Coupling.WholeField9Entr

/-!
# Lemma W0b: no common open arc on an ordered earlier prefix

Packet PROVE-G12D (specification supplement §9, Lemma W0b, p. 529, `source/spec/p529-576.md#id-W0b`): "For
`θ₁ ≠ θ₂`, almost surely no pair of original finite prefixes which admits the ordered proper completions of W0
contains a common nontrivial open subarc."

## The proof (p. 529), and where each step is

* "All marked-kernel and boundary-decay identities are intersected over the countable family of rational own
  stopping pairs before the compact common arc is selected": the probability-one event below, over every integer cap
  `m` and every pair of rational stops — the single-path side heights (`Sec7.SinglePathSideHeightStatement`, Theorem
  1.1 read on the local-set mean with Aux. lemma 56) and Proposition 3.8 for the two stopped prefixes and their union
  (`Sec7.ae_tendsto_sub_explored_const`, from Lemma 7.5 and Aux. lemma 56 at first entrances, `Sec7.TwoHist`).
* "The contact-order theorem for the proper completions makes any common arc cooriented. Choose a compact subarc in
  its interior which lies in `ℍ`, and choose rational original own stopping times […] Injectivity and compactness
  give positive physical clearance": `W0b.exists_coorientedStops` (`W0bSelect.lean`).
* "Its common right-hand side is exposed to the joint unbounded component […] use the ordered proper completion of
  the right-hand path: its right collar avoids the other path […] Aux. lemma 57 gives the analytic-logarithm lift
  exactly zero": `W0b.coorientedArcChart` (`W0bSelect.lean`, with the chart lemmas of `W0bChart.lean`): an approach
  from the joint unbounded domain along which both charts tend to positive reals and the lifts agree.
* "The nested marked Gaussian boundary comparison identifies the union germ on this collar with the germ of each
  individual path. […] Thus the two heights in the same inherited joint chart are `λ − θ₁χ` and `λ − θ₂χ`. They are
  the boundary value of the same harmonic mean, so they are equal. Since `χ > 0`, this contradicts `θ₁ ≠ θ₂`": the
  assembly `w0bStatement_of_sideHeight` (Proposition 3.8 twice, `Sec7.tendsto_sub_of_union_means`;
  `Sec7.eq_of_side_limits`).

## Main results

* `w0bStatement_of_sideHeight`: `Supp9.W0bStatement` from Lemma 7.5 (`Theorem15.Lemma75Statement`), Aux. lemma 56 at
  first entrances and the single-path side heights (a conditional helper);
* **`w0bStatement_of_lemma75`**: `Supp9.W0bStatement` from Lemma 7.5 alone (Aux. lemma 56 at first entrances is
  `WholeField.retainedRangeEntranceStatement`, the side heights are
  `SideHeight.singlePathSideHeightStatement_of_inputs`). This is the same input as the landed Aux. lemma 70
  (`Sec7.aux70Statement_of_lemma75`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace Topology Metric Complex
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Supp9

open QuantumZipper (H)
open LQGMetric (DistOn TestOn)
open LocalSets Sec6 Restart Sec7

universe u

/-- **Lemma W0b from Lemma 7.5, Aux. lemma 56 at first entrances and the single-path side heights** (a conditional
helper; specification supplement p. 529). -/
theorem w0bStatement_of_sideHeight (hL75 : Theorem15.Lemma75Statement.{u})
    (hA56 : Restart.RetainedRangeEntranceStatement.{u}) (hside : SinglePathSideHeightStatement.{u}) :
    W0bStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ Ω _ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂
  classical
  set χ := QuantumZipper.chiC κ with hχ
  obtain ⟨u₀, hu₀, -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension hb
  have hh0 := Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀
  set hc' := WholeField.centredField h u₀ with hc'def
  -- capped versions for every integer cap
  have hver := fun m : ℕ => exists_twoHist_versions hL75 hA56 hκ hκ4 hb hh hη₁ hη₂ hu₀ (m : ℝ≥0)
  choose ηs hcont h0 hηm hdet hloc hfr him hs₁ hs₂ using hver
  have hx0 : ∀ i, ((![(x₁ : ℂ), (x₂ : ℂ)] : Fin 2 → ℂ) i).im = 0 := by
    intro i; fin_cases i <;> simp
  have hηs0 : ∀ m i ω, (ηs m i ω 0).im = 0 := fun m i ω => by rw [h0 m i ω]; exact hx0 i
  -- the drivers
  obtain ⟨_, _, W₁, _, _, _, -, hcoup₁, htr₁⟩ := id hη₁
  obtain ⟨_, _, W₂, _, _, _, -, hcoup₂, htr₂⟩ := id hη₂
  have hinj₁ := Theorem15.ae_injOn_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₁
  have hinj₂ := Theorem15.ae_injOn_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₂
  -- the local sets and their means at every pair of stops
  have hmean : ∀ (m : ℕ) (s : Fin 2 → ℝ≥0∞), ∃ g, IsLocalSetMean (explored (ηs m) fun i _ => s i) hc' P g :=
    fun m s => IsLocalSet.exists_isLocalSetMean hh0 (measurable_explored_const (hcont m) (hηm m) s)
      (isLocalSet_explored_const hh0 (hcont m) (h0 m) (hηm m) (hdet m) (hloc m) (hfr m) s)
  choose G hG using hmean
  -- the pathwise sets
  have hA₁ : ∀ (m : ℕ) (r : ℚ) ω, explored (ηs m) (fun i _ => stop₁ r i) ω =
      ηs m 0 ω '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ (r : ℝ).toNNReal} ∩ H := fun m r ω =>
    explored_pair_left (ηs m) _ (hηs0 m 1 ω)
  have hA₂ : ∀ (m : ℕ) (r : ℚ) ω, explored (ηs m) (fun i _ => stop₂ r i) ω =
      ηs m 1 ω '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ (r : ℝ).toNNReal} ∩ H := fun m r ω =>
    explored_pair_right (ηs m) _ (hηs0 m 0 ω)
  -- the single-path side heights at every cap and rational stop
  have hN₁ : ∀ (m : ℕ) (r : ℚ), ∀ᵐ ω ∂P, (r : ℝ).toNNReal ≤ (m : ℝ≥0) →
      ((((r : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) < ζ₁ ω → ∀ v : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd v (H \ (ηs m 0 ω '' {t | (t : ℝ≥0∞) ≤ (r : ℝ).toNNReal} ∩ H)) →
      (∀ φ : TestOn upperHalfPlaneOpens,
        tsupport φ ⊆ H \ (ηs m 0 ω '' {t | (t : ℝ≥0∞) ≤ (r : ℝ).toNNReal} ∩ H) →
        G m (stop₁ r) ω φ = ∫ z, v z * φ z) →
      ∀ t₀ : ℝ≥0, t₀ < (r : ℝ).toNNReal → η₁ ω t₀ ∈ H → ∀ F : Filter ℂ, F.NeBot →
        F ≤ 𝓝[H \ fillH (η₁ ω '' Icc 0 (r : ℝ).toNNReal)] (η₁ ω t₀) → ∀ y : ℝ,
        Tendsto (fun z => QuantumZipper.fwdMap (fun s : ℝ => W₁ s.toNNReal ω) (r : ℝ).toNNReal (z - x₁)) F
          (𝓝 (y : ℂ)) →
          (0 < y → Tendsto (fun z => v z + u₀ z + χ *
              (QuantumZipper.logDerivFwd (fun s : ℝ => W₁ s.toNNReal ω) (r : ℝ).toNNReal (z - x₁)).im) F
            (𝓝 (sleLambda κ - θ₁ * χ))) ∧
          (y < 0 → Tendsto (fun z => v z + u₀ z + χ *
              (QuantumZipper.logDerivFwd (fun s : ℝ => W₁ s.toNNReal ω) (r : ℝ).toNNReal (z - x₁)).im) F
            (𝓝 (-sleLambda κ - θ₁ * χ)))) := by
    intro m r
    by_cases hrm : (r : ℝ).toNNReal ≤ (m : ℝ≥0)
    · have hg : IsLocalSetMean (fun ω => ηs m 0 ω '' {t | (t : ℝ≥0∞) ≤ (r : ℝ).toNNReal} ∩ H) hc' P
          (G m (stop₁ r)) := by
        have e : (fun ω => ηs m 0 ω '' {t | (t : ℝ≥0∞) ≤ (r : ℝ).toNNReal} ∩ H) =
            explored (ηs m) (fun i _ => stop₁ r i) := funext fun ω => (hA₁ m r ω).symm
        rw [e]
        exact hG m _
      filter_upwards [hside κ hκ hκ4 b jumps hb x₁ θ₁ P h hh η₁ ζ₁ hη₁ W₁ htr₁ u₀ hu₀ (m : ℝ≥0)
        (r : ℝ).toNNReal hrm (ηs m 0) (hcont m 0) (hηm m 0) (hs₁ m) (G m (stop₁ r)) hg] with ω hω _
      exact hω
    · exact Eventually.of_forall fun ω h => absurd h hrm
  have hN₂ : ∀ (m : ℕ) (r : ℚ), ∀ᵐ ω ∂P, (r : ℝ).toNNReal ≤ (m : ℝ≥0) →
      ((((r : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) < ζ₂ ω → ∀ v : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd v (H \ (ηs m 1 ω '' {t | (t : ℝ≥0∞) ≤ (r : ℝ).toNNReal} ∩ H)) →
      (∀ φ : TestOn upperHalfPlaneOpens,
        tsupport φ ⊆ H \ (ηs m 1 ω '' {t | (t : ℝ≥0∞) ≤ (r : ℝ).toNNReal} ∩ H) →
        G m (stop₂ r) ω φ = ∫ z, v z * φ z) →
      ∀ t₀ : ℝ≥0, t₀ < (r : ℝ).toNNReal → η₂ ω t₀ ∈ H → ∀ F : Filter ℂ, F.NeBot →
        F ≤ 𝓝[H \ fillH (η₂ ω '' Icc 0 (r : ℝ).toNNReal)] (η₂ ω t₀) → ∀ y : ℝ,
        Tendsto (fun z => QuantumZipper.fwdMap (fun s : ℝ => W₂ s.toNNReal ω) (r : ℝ).toNNReal (z - x₂)) F
          (𝓝 (y : ℂ)) →
          (0 < y → Tendsto (fun z => v z + u₀ z + χ *
              (QuantumZipper.logDerivFwd (fun s : ℝ => W₂ s.toNNReal ω) (r : ℝ).toNNReal (z - x₂)).im) F
            (𝓝 (sleLambda κ - θ₂ * χ))) ∧
          (y < 0 → Tendsto (fun z => v z + u₀ z + χ *
              (QuantumZipper.logDerivFwd (fun s : ℝ => W₂ s.toNNReal ω) (r : ℝ).toNNReal (z - x₂)).im) F
            (𝓝 (-sleLambda κ - θ₂ * χ)))) := by
    intro m r
    by_cases hrm : (r : ℝ).toNNReal ≤ (m : ℝ≥0)
    · have hg : IsLocalSetMean (fun ω => ηs m 1 ω '' {t | (t : ℝ≥0∞) ≤ (r : ℝ).toNNReal} ∩ H) hc' P
          (G m (stop₂ r)) := by
        have e : (fun ω => ηs m 1 ω '' {t | (t : ℝ≥0∞) ≤ (r : ℝ).toNNReal} ∩ H) =
            explored (ηs m) (fun i _ => stop₂ r i) := funext fun ω => (hA₂ m r ω).symm
        rw [e]
        exact hG m _
      filter_upwards [hside κ hκ hκ4 b jumps hb x₂ θ₂ P h hh η₂ ζ₂ hη₂ W₂ htr₂ u₀ hu₀ (m : ℝ≥0)
        (r : ℝ).toNNReal hrm (ηs m 1) (hcont m 1) (hηm m 1) (hs₂ m) (G m (stop₂ r)) hg] with ω hω _
      exact hω
    · exact Eventually.of_forall fun ω h => absurd h hrm
  -- Proposition 3.8 at every cap and rational pair
  have hmc : ∀ r₁ r₂ : ℚ, (fun (i : Fin 2) (_ : Ω) => max (stop₂ r₂ i) (stop₁ r₁ i)) =
      fun i _ => max (stop₁ r₁ i) (stop₂ r₂ i) := fun _ _ => by
    funext i _
    exact max_comm _ _
  have hPa : ∀ (m : ℕ) (r₁ r₂ : ℚ), ∀ᵐ ω ∂P, ∃ u : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd u (H \ explored (ηs m) (fun i _ => max (stop₁ r₁ i) (stop₂ r₂ i)) ω) ∧
      (∀ φ : TestOn upperHalfPlaneOpens,
        tsupport φ ⊆ H \ explored (ηs m) (fun i _ => max (stop₁ r₁ i) (stop₂ r₂ i)) ω →
        G m (fun i => max (stop₁ r₁ i) (stop₂ r₂ i)) ω φ - G m (stop₁ r₁) ω φ = ∫ z, u z * φ z) ∧
      ∀ z₀ ∈ explored (ηs m) (fun i _ => stop₁ r₁ i) ω ∪ {z : ℂ | z.im = 0},
        (∃ r > 0, explored (ηs m) (fun i _ => stop₂ r₂ i) ω ∩ ball z₀ r ⊆
          explored (ηs m) (fun i _ => stop₁ r₁ i) ω) →
        Tendsto u (𝓝[H \ explored (ηs m) (fun i _ => max (stop₁ r₁ i) (stop₂ r₂ i)) ω] z₀) (𝓝 0) := by
    intro m r₁ r₂
    have hg : IsLocalSetMean (explored (ηs m) fun i _ => max (stop₂ r₂ i) (stop₁ r₁ i)) hc' P
        (G m (fun i => max (stop₁ r₁ i) (stop₂ r₂ i))) := by
      rw [hmc]
      exact hG m _
    have := ae_tendsto_sub_explored_const hh0 (hcont m) (h0 m) hx0 (hηm m) (hdet m) (hloc m) (hfr m) (him m)
      (stop₂ r₂) (stop₁ r₁) hg (hG m _)
    rw [hmc] at this
    exact this
  have hPb : ∀ (m : ℕ) (r₁ r₂ : ℚ), ∀ᵐ ω ∂P, ∃ u : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd u (H \ explored (ηs m) (fun i _ => max (stop₁ r₁ i) (stop₂ r₂ i)) ω) ∧
      (∀ φ : TestOn upperHalfPlaneOpens,
        tsupport φ ⊆ H \ explored (ηs m) (fun i _ => max (stop₁ r₁ i) (stop₂ r₂ i)) ω →
        G m (fun i => max (stop₁ r₁ i) (stop₂ r₂ i)) ω φ - G m (stop₂ r₂) ω φ = ∫ z, u z * φ z) ∧
      ∀ z₀ ∈ explored (ηs m) (fun i _ => stop₂ r₂ i) ω ∪ {z : ℂ | z.im = 0},
        (∃ r > 0, explored (ηs m) (fun i _ => stop₁ r₁ i) ω ∩ ball z₀ r ⊆
          explored (ηs m) (fun i _ => stop₂ r₂ i) ω) →
        Tendsto u (𝓝[H \ explored (ηs m) (fun i _ => max (stop₁ r₁ i) (stop₂ r₂ i)) ω] z₀) (𝓝 0) :=
    fun m r₁ r₂ => ae_tendsto_sub_explored_const hh0 (hcont m) (h0 m) hx0 (hηm m) (hdet m) (hloc m) (hfr m) (him m)
      (stop₁ r₁) (stop₂ r₂) (hG m _) (hG m _)
  -- the probability-one event
  filter_upwards [ae_all_iff.2 hs₁, ae_all_iff.2 hs₂, htr₁, htr₂, hcoup₁.1.2.2.2.2, hcoup₂.1.2.2.2.2, hinj₁, hinj₂,
    ae_all_iff.2 fun m => ae_all_iff.2 (hN₁ m), ae_all_iff.2 fun m => ae_all_iff.2 (hN₂ m),
    ae_all_iff.2 fun m => ae_all_iff.2 fun r₁ => ae_all_iff.2 (hPa m r₁),
    ae_all_iff.2 fun m => ae_all_iff.2 fun r₁ => ae_all_iff.2 (hPb m r₁),
    ae_all_iff.2 fun m => ae_all_iff.2 fun r => (hG m (stop₁ r)).2.1,
    ae_all_iff.2 fun m => ae_all_iff.2 fun r => (hG m (stop₂ r)).2.1]
    with ω ha₁ ha₂ ht₁ ht₂ hp₁ hp₂ hi₁ hi₂ hn₁ hn₂ hpa hpb hr₁ hr₂
  intro a c ha hc hord hcom
  -- the chart geometry of the common arc
  obtain ⟨r₁, r₂, s, t, hq₁a, hq₂c, hsq₁, htq₂, hβt, hsH, ⟨ρ, hρ, hagree⟩, F, hFne, hF, y₁, y₂, hy₁, hy₂, hf₁,
    hf₂, hL⟩ := W0b.coorientedArcChart hx ht₁ hp₁.2.2.2.1 hp₁.1 ht₂ hp₂.2.2.2.1 hp₂.1 hi₁ hi₂ ha hc hord hcom
  set q₁ := (r₁ : ℝ).toNNReal with hq₁
  set q₂ := (r₂ : ℝ).toNNReal with hq₂
  -- an integer cap above both prefixes
  set m : ℕ := ⌈((max a c : ℝ≥0) : ℝ)⌉₊ with hm
  have hmax : (max a c : ℝ≥0) ≤ (m : ℝ≥0) := by
    rw [← NNReal.coe_le_coe, NNReal.coe_natCast]; exact Nat.le_ceil _
  have hq₁m : q₁ ≤ (m : ℝ≥0) := hq₁a.trans ((le_max_left a c).trans hmax)
  have hq₂m : q₂ ≤ (m : ℝ≥0) := hq₂c.trans ((le_max_right a c).trans hmax)
  have hq₁ζ : (q₁ : ℝ≥0∞) < ζ₁ ω := (ENNReal.coe_le_coe.2 hq₁a).trans_lt ha
  have hq₂ζ : (q₂ : ℝ≥0∞) < ζ₂ ω := (ENNReal.coe_le_coe.2 hq₂c).trans_lt hc
  have hq₁min : (q₁ : ℝ≥0∞) ≤ min (ζ₁ ω) ((m : ℝ≥0) : ℝ≥0∞) := le_min hq₁ζ.le (ENNReal.coe_le_coe.2 hq₁m)
  have hq₂min : (q₂ : ℝ≥0∞) ≤ min (ζ₂ ω) ((m : ℝ≥0) : ℝ≥0∞) := le_min hq₂ζ.le (ENNReal.coe_le_coe.2 hq₂m)
  -- the pathwise sets
  have hA₁ω : explored (ηs m) (fun i _ => stop₁ r₁ i) ω = η₁ ω '' Icc 0 q₁ ∩ H := by
    rw [hA₁, image_capped_eq (ha₁ m) hq₁min]
  have hA₂ω : explored (ηs m) (fun i _ => stop₂ r₂ i) ω = η₂ ω '' Icc 0 q₂ ∩ H := by
    rw [hA₂, image_capped_eq (ha₂ m) hq₂min]
  have hUω : explored (ηs m) (fun i _ => max (stop₁ r₁ i) (stop₂ r₂ i)) ω =
      (η₁ ω '' Icc 0 q₁ ∩ H) ∪ (η₂ ω '' Icc 0 q₂ ∩ H) := by
    rw [← explored_const_union (stop₁ r₁) (stop₂ r₂) ω, hA₁ω, hA₂ω]
  have hz₀₁ : η₁ ω s ∈ η₁ ω '' Icc 0 q₁ ∩ H := ⟨⟨s, ⟨zero_le, hsq₁.le⟩, rfl⟩, hsH⟩
  have hz₀₂ : η₁ ω s ∈ η₂ ω '' Icc 0 q₂ ∩ H := ⟨⟨t, ⟨zero_le, htq₂.le⟩, hβt⟩, hsH⟩
  have hsub₂₁ : (η₂ ω '' Icc 0 q₂ ∩ H) ∩ ball (η₁ ω s) ρ ⊆ η₁ ω '' Icc 0 q₁ ∩ H := by
    rintro z ⟨⟨hz, hzH⟩, hzb⟩
    have : z ∈ η₂ ω '' Icc 0 q₂ ∩ ball (η₁ ω s) ρ := ⟨hz, hzb⟩
    rw [← hagree] at this
    exact ⟨this.1, hzH⟩
  have hsub₁₂ : (η₁ ω '' Icc 0 q₁ ∩ H) ∩ ball (η₁ ω s) ρ ⊆ η₂ ω '' Icc 0 q₂ ∩ H := by
    rintro z ⟨⟨hz, hzH⟩, hzb⟩
    have : z ∈ η₁ ω '' Icc 0 q₁ ∩ ball (η₁ ω s) ρ := ⟨hz, hzb⟩
    rw [hagree] at this
    exact ⟨this.1, hzH⟩
  -- Proposition 3.8 at the point
  obtain ⟨ua, hua, huar, hual⟩ := hpa m r₁ r₂
  obtain ⟨ub, hub, hubr, hubl⟩ := hpb m r₁ r₂
  rw [hUω] at hua huar hual hub hubr hubl
  rw [hA₁ω, hA₂ω] at hual hubl
  have hla := hual (η₁ ω s) (Or.inl hz₀₁) ⟨ρ, hρ, hsub₂₁⟩
  have hlb := hubl (η₁ ω s) (Or.inl hz₀₂) ⟨ρ, hρ, hsub₁₂⟩
  -- harmonic representatives of the two single-prefix means
  obtain ⟨v₁, hv₁, hv₁r⟩ := hr₁ m r₁
  obtain ⟨v₂, hv₂, hv₂r⟩ := hr₂ m r₂
  have hO : IsOpen (H \ ((η₁ ω '' Icc 0 q₁ ∩ H) ∪ (η₂ ω '' Icc 0 q₂ ∩ H))) := by
    rw [← hUω]
    exact isOpen_H_diff_explored_of_frozen (fun i => hcont m i ω) (fun i => hfr m i ω)
  have hO₁ : H \ ((η₁ ω '' Icc 0 q₁ ∩ H) ∪ (η₂ ω '' Icc 0 q₂ ∩ H)) ⊆
      H \ explored (ηs m) (fun i _ => stop₁ r₁ i) ω := by
    rw [hA₁ω]; exact sdiff_subset_sdiff_right subset_union_left
  have hO₂ : H \ ((η₁ ω '' Icc 0 q₁ ∩ H) ∪ (η₂ ω '' Icc 0 q₂ ∩ H)) ⊆
      H \ explored (ηs m) (fun i _ => stop₂ r₂ i) ω := by
    rw [hA₂ω]; exact sdiff_subset_sdiff_right subset_union_right
  have h12 := tendsto_sub_of_union_means hO hO₁ hO₂ hv₁ hv₁r hv₂ hv₂r hua huar hub hubr hla hlb
  -- the approach lies off the union
  have hfillsub : ∀ {K : Set ℂ}, H \ fillH K ⊆ H \ (K ∩ H) := fun {K} z hz =>
    ⟨hz.1, fun hzK => hz.2 ⟨hzK.2, Or.inl (subset_closure hzK.1)⟩⟩
  have hFO : F ≤ 𝓝[H \ ((η₁ ω '' Icc 0 q₁ ∩ H) ∪ (η₂ ω '' Icc 0 q₂ ∩ H))] (η₁ ω s) := by
    refine hF.trans (nhdsWithin_mono _ ?_)
    rw [← union_inter_distrib_right]
    exact hfillsub
  have hF₁ : F ≤ 𝓝[H \ fillH (η₁ ω '' Icc 0 q₁)] (η₁ ω s) :=
    hF.trans (nhdsWithin_mono _ (sdiff_subset_sdiff_right (fillH_mono subset_union_left)))
  have hF₂ : F ≤ 𝓝[H \ fillH (η₂ ω '' Icc 0 q₂)] (η₂ ω t) := by
    rw [hβt]
    exact hF.trans (nhdsWithin_mono _ (sdiff_subset_sdiff_right (fillH_mono subset_union_right)))
  -- the single-path side heights: both on the right side
  rw [hA₁ m r₁ ω] at hv₁ hv₁r
  rw [hA₂ m r₂ ω] at hv₂ hv₂r
  have h₁ := (hn₁ m r₁ hq₁m hq₁ζ v₁ hv₁ hv₁r s hsq₁ hsH F hFne hF₁ y₁ hf₁).1 hy₁
  have h₂ := (hn₂ m r₂ hq₂m hq₂ζ v₂ hv₂ hv₂r t htq₂ (hβt ▸ hsH) F hFne hF₂ y₂ hf₂).1 hy₂
  have heq := eq_of_side_limits (h12.mono_left hFO) hL h₁ h₂
  have hχ0 : 0 < χ := Sec4.chiC_pos hκ hκ4
  have : θ₁ * χ = θ₂ * χ := by linarith
  exact absurd (mul_right_cancel₀ hχ0.ne' this) hθ.ne

/-- **Lemma W0b from Lemma 7.5** (a conditional helper with the single named input `Theorem15.Lemma75Statement`, field
determination, the same input as the landed Aux. lemma 70): Aux. lemma 56 at first entrances is
`WholeField.retainedRangeEntranceStatement` and the single-path side heights are
`SideHeight.singlePathSideHeightStatement_of_inputs`. -/
theorem w0bStatement_of_lemma75 (hL75 : Theorem15.Lemma75Statement.{u}) : W0bStatement.{u} :=
  w0bStatement_of_sideHeight hL75 WholeField.retainedRangeEntranceStatement
    (SideHeight.singlePathSideHeightStatement_of_inputs hL75 WholeField.retainedRangeEntranceStatement)

end Supp9

end InteractingSLE
