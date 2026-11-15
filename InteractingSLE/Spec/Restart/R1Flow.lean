/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.R1StopLineLocal
import InteractingSLE.Spec.Restart.ChartMeasFlow
import InteractingSLE.Spec.Coupling.WholeField2Hull

/-!
# Lemma 7.7's marked locality for two flow lines (capped at a deterministic time)

Packet PROVE-RESTART-CPL6, (R1) (b) for the flow lines of `FirstContactKernelClockStatement`. The abstract stopping-line
theorem `ae_condExp_exp_eq_fcUnion` (`R1StopLineLocal.lean`) is applied to two flow lines, each **capped** at a
deterministic time `m` (Lemma 7.7's proof: "First suppose `T₁, T₂` are bounded […] Finite common-contact realizations
are covered by countably many bounded grid boxes"): the capped path `η(t ∧ ζ ∧ m)` with the killing record
`cutLife ζ m` (`ζ` if `ζ ≤ m`, else `⊤`).

Inputs:
* field determination, the landed named input `Theorem15.Lemma75Statement` (Lemma 7.5);
* Lemma 7.7's common first point, the landed named input `Supp10.Lemma77Statement`;
* **the new named input `RetainedRangeEntranceStatement`**: Aux. lemma 56 ("Retained range laws for every continuous
  prefix", p. 249: "its stopped trace range and history are marked local, including the zero-boundary fields in all
  swallowed components. The same conclusion holds at an announced continuous terminal endpoint") at the first
  entrance times of the capped flow line, in the form of Lemma 6.2's hypothesis (`IsEntranceKilledHistoryLocal`).

## Main results

* `capPath`, `measurable_capPath`, `capPath_eq`, `capPath_congr`: a measurable reading of the capped path from a
  recorded `(lifetime, path)` pair;
* **`exists_fcUnion_marked_of_isFlowLine`**: for two flow lines and every cap `m` there are capped versions `ηc₁, ηc₂`
  (continuous for every `ω`, measurable, almost surely equal to the capped flow lines) whose first-contact union,
  with the two retained killed histories, has the marked Gaussian law off the union: given the germs and the
  histories, on every complementary component the centred field is its local-set mean plus a zero-boundary GFF.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Restart

open QuantumZipper (H)
open LQGMetric (DistOn TestOn)
open LocalSets Sec6

/-! ### Capped paths -/

/-- The capped time `t ∧ ζ ∧ m`. -/
def capTime (m : ℝ≥0) (ζ : ℝ≥0∞) (t : ℝ≥0) : ℝ≥0 := min t (min ζ (m : ℝ≥0∞)).toNNReal

/-- The killing record of the capped path: `ζ` if `ζ ≤ m`, `⊤` otherwise. -/
def cutLife (ζ : ℝ≥0∞) (m : ℝ≥0) : ℝ≥0∞ := if ζ ≤ m then ζ else ⊤

/-- The endpoint value of a recorded `(lifetime, path)` pair: the limit along the dyadic times below the lifetime. -/
def endVal (p : ℝ≥0∞ × (ℝ≥0 → ℂ)) : ℂ :=
  if p.1 = 0 then p.2 0 else limUnder atTop fun n => p.2 (LP.dyadicBelow n p.1.toNNReal)

/-- **The capped path read from a recorded `(lifetime, path)` pair**: `γ(t)` before `ζ ∧ m`, then `γ(m)` if `m < ζ`,
else the endpoint value. -/
def capPath (m : ℝ≥0) (p : ℝ≥0∞ × (ℝ≥0 → ℂ)) (t : ℝ≥0) : ℂ :=
  if (t : ℝ≥0∞) < min p.1 m then p.2 t else if (m : ℝ≥0∞) < p.1 then p.2 m else endVal p

theorem dyadicBelow_le (n : ℕ) (x : ℝ≥0) : LP.dyadicBelow n x ≤ x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [LP.dyadicBelow, LP.dyadicIdx]
  · exact (LP.dyadicBelow_lt (pos_iff_ne_zero.2 hx) n).le

theorem measurable_eval_dyadicBelow (n : ℕ) :
    Measurable fun p : ℝ≥0∞ × (ℝ≥0 → ℂ) => p.2 (LP.dyadicBelow n p.1.toNNReal) := by
  set G : (ℝ≥0 → ℂ) × ℕ → ℂ := fun q => q.1 ((q.2 : ℝ≥0) / 2 ^ n) with hGdef
  have hG : Measurable G := measurable_from_prod_countable_left fun k => by
    show Measurable fun γ : ℝ≥0 → ℂ => γ ((k : ℝ≥0) / 2 ^ n)
    exact measurable_pi_apply _
  have hg : Measurable fun p : ℝ≥0∞ × (ℝ≥0 → ℂ) => (p.2, LP.dyadicIdx n p.1.toNNReal) :=
    measurable_snd.prodMk ((LP.measurable_dyadicIdx n).comp (ENNReal.measurable_toNNReal.comp measurable_fst))
  exact hG.comp hg

theorem measurable_endVal : Measurable endVal := by
  unfold endVal
  refine Measurable.ite (measurable_fst (measurableSet_singleton 0))
    ((measurable_pi_apply 0).comp measurable_snd) ?_
  exact (StronglyMeasurable.limUnder fun n => (measurable_eval_dyadicBelow n).stronglyMeasurable).measurable

theorem measurable_capPath (m : ℝ≥0) (t : ℝ≥0) : Measurable fun p : ℝ≥0∞ × (ℝ≥0 → ℂ) => capPath m p t := by
  unfold capPath
  refine Measurable.ite (measurableSet_lt measurable_const (measurable_fst.min measurable_const))
    ((measurable_pi_apply t).comp measurable_snd) ?_
  exact Measurable.ite (measurableSet_lt measurable_const measurable_fst)
    ((measurable_pi_apply m).comp measurable_snd) measurable_endVal

/-- The capped path only reads the recorded path on the closed available interval. -/
theorem capPath_congr (m : ℝ≥0) {T : ℝ≥0∞} {γ γ' : ℝ≥0 → ℂ} (hγ : ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ T → γ s = γ' s)
    (t : ℝ≥0) : capPath m (T, γ) t = capPath m (T, γ') t := by
  unfold capPath endVal
  simp only
  split_ifs with h1 h2 h3
  · exact hγ t (h1.le.trans (min_le_left _ _))
  · exact hγ m h2.le
  · exact hγ 0 (by simp)
  · congr 1
    funext n
    refine hγ _ ?_
    rcases eq_or_ne T ⊤ with rfl | hT
    · exact le_top
    · rw [← ENNReal.coe_toNNReal hT, ENNReal.coe_le_coe]
      exact dyadicBelow_le n _

theorem capTime_le (m : ℝ≥0) (ζ : ℝ≥0∞) (t : ℝ≥0) : (capTime m ζ t : ℝ≥0∞) ≤ ζ := by
  have h1 : ((min ζ (m : ℝ≥0∞)).toNNReal : ℝ≥0∞) ≤ ζ := by
    rw [ENNReal.coe_toNNReal (ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_right _ _))]
    exact min_le_left _ _
  exact (ENNReal.coe_le_coe.2 (min_le_right _ _)).trans h1

theorem capTime_le_cap (m : ℝ≥0) (ζ : ℝ≥0∞) (t : ℝ≥0) : capTime m ζ t ≤ m := by
  have h1 : ((min ζ (m : ℝ≥0∞)).toNNReal : ℝ≥0∞) ≤ m := by
    rw [ENNReal.coe_toNNReal (ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_right _ _))]
    exact min_le_right _ _
  exact (min_le_right _ _).trans (ENNReal.coe_le_coe.1 h1)

theorem capTime_of_le (m : ℝ≥0) (ζ : ℝ≥0∞) {t : ℝ≥0} (ht : (t : ℝ≥0∞) ≤ min ζ m) : capTime m ζ t = t := by
  refine min_eq_left ?_
  rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal (ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_right _ _))]
  exact ht

/-- **The capped path of a continuous path** is the path at the capped time. -/
theorem capPath_eq (m : ℝ≥0) {T : ℝ≥0∞} {γ : ℝ≥0 → ℂ} (hγ : ContinuousOn γ {s | (s : ℝ≥0∞) ≤ T})
    (t : ℝ≥0) : capPath m (T, γ) t = γ (capTime m T t) := by
  have hc : min T (m : ℝ≥0∞) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_right _ _)
  unfold capPath
  simp only
  split_ifs with h1 h2
  · rw [capTime_of_le m T h1.le]
  · have e : capTime m T t = m := by
      have hmin : min T (m : ℝ≥0∞) = m := min_eq_right h2.le
      unfold capTime
      rw [hmin, ENNReal.toNNReal_coe]
      refine min_eq_right ?_
      rw [← ENNReal.coe_le_coe, ← hmin]
      exact not_lt.1 h1
    rw [e]
  · have hTm : T ≤ m := not_lt.1 h2
    have hmin : min T (m : ℝ≥0∞) = T := min_eq_left hTm
    have hT : T ≠ ⊤ := by rw [← hmin]; exact hc
    have e : capTime m T t = T.toNNReal := by
      unfold capTime
      rw [hmin]
      refine min_eq_right ?_
      rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal hT, ← hmin]
      exact not_lt.1 h1
    rw [e]
    unfold endVal
    simp only
    split_ifs with h0
    · rw [h0, ENNReal.toNNReal_zero]
    · have hpos : 0 < T.toNNReal := by
        rw [pos_iff_ne_zero, Ne, ENNReal.toNNReal_eq_zero_iff]
        push Not
        exact ⟨h0, hT⟩
      have hmem : ∀ s : ℝ≥0, s ≤ T.toNNReal → (s : ℝ≥0∞) ≤ T := fun s hs => by
        rw [← ENNReal.coe_toNNReal hT]; exact ENNReal.coe_le_coe.2 hs
      have htend : Tendsto (fun n => LP.dyadicBelow n T.toNNReal) atTop
          (𝓝[{s : ℝ≥0 | (s : ℝ≥0∞) ≤ T}] T.toNNReal) :=
        tendsto_nhdsWithin_iff.2 ⟨LP.tendsto_dyadicBelow _,
          Eventually.of_forall fun n => hmem _ (dyadicBelow_le n _)⟩
      exact ((hγ _ (hmem _ le_rfl)).tendsto.comp htend).limUnder_eq

/-- The capped path of a continuous path is continuous. -/
theorem continuous_capTime_comp (m : ℝ≥0) {T : ℝ≥0∞} {γ : ℝ≥0 → ℂ} (hγ : ContinuousOn γ {s | (s : ℝ≥0∞) ≤ T}) :
    Continuous fun t => γ (capTime m T t) :=
  hγ.comp_continuous (continuous_id.min continuous_const) fun t => capTime_le m T t

/-- The range of a path frozen after a finite time up to any `σ ≤ ⊤` is compact. -/
theorem isCompact_image_of_const {γ : ℝ≥0 → ℂ} (hγ : Continuous γ) {m : ℝ≥0} (hm : ∀ t, m ≤ t → γ t = γ m)
    (σ : ℝ≥0∞) : IsCompact (γ '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ σ}) := by
  have e : γ '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ σ} =
      γ '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ σ ∧ (t : ℝ≥0∞) ≤ σ ∧ t ≤ m} := by
    refine Subset.antisymm ?_ (image_mono fun t ht => ht.1)
    rintro _ ⟨t, ht, rfl⟩
    by_cases htm : t ≤ m
    · exact ⟨t, ⟨ht, ht, htm⟩, rfl⟩
    · have hmσ : (m : ℝ≥0∞) ≤ σ := (ENNReal.coe_le_coe.2 (not_le.1 htm).le).trans ht
      exact ⟨m, ⟨hmσ, hmσ, le_rfl⟩, (hm t (not_le.1 htm).le).symm⟩
  rw [e]
  exact (isCompact_capSet σ σ m).image hγ

/-! ### The named input: Aux. lemma 56 at first entrance times -/

/-- **Named input: Aux. lemma 56 at the first entrance times of a capped flow line** (specification §7.1, Aux. lemma 56,
p. 249, "Retained range laws for every continuous prefix": "Let `S < T_*` be a bounded own-filtration stopping time
through which the trace is continuous almost surely. Then the coupling has, through `S`, the canonical retained-range
conditional laws of Aux. lemma 16. In particular its stopped trace range and history are marked local, including the
zero-boundary fields in all swallowed components. The same conclusion holds at an announced continuous terminal
endpoint by Aux. lemma 9. Field determination is not an input to this assertion"). Applied at the stop
`S = T^U ∧ ζ ∧ m`, `T^U` the first entrance time into a deterministic open `U ⊆ ℍ` (a stopping time of the
right-continuous filtration, ruling R34), this is Lemma 6.2's history-sensitive hypothesis for the capped flow line
`η(· ∧ ζ ∧ m)` with its killing record `cutLife ζ m`: given `h_{U^c}`, the capped history through `T^U` is
conditionally independent of `h_U` (`IsEntranceKilledHistoryLocal`, for the centred field `h − 𝔥₀`). It is stated for
every version `ηc` of the capped path that is continuous for every `ω` and measurable at each time. **Not proved in
Lean.** -/
def RetainedRangeEntranceStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x θ : ℝ, ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞), IsFlowLine κ b jumps x θ P h η ζ →
    ∀ u₀ : ℂ → ℝ, IsBoundedHarmonicExtension b jumps u₀ → ∀ m : ℝ≥0,
    ∀ ηc : Ω → ℝ≥0 → ℂ, (∀ ω, Continuous (ηc ω)) → (∀ t, Measurable fun ω => ηc ω t) →
      (∀ᵐ ω ∂P, ∀ t, ηc ω t = η ω (capTime m (ζ ω) t)) →
      IsEntranceKilledHistoryLocal ηc (fun ω => cutLife (ζ ω) m) (WholeField.centredField h u₀) P

/-! ### Capped versions of a flow line -/

section Flow

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x θ : ℝ} {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}

omit [IsProbabilityMeasure P] in
/-- The centred field of a GFF with boundary data is a zero-boundary GFF. -/
theorem isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData {S : Set ℝ} (hh : IsGFFWithBoundaryData P h b S)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b S u₀) :
    LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (WholeField.centredField h u₀) P := by
  refine ⟨WholeField.measurable_centredField hh.1 u₀, ?_⟩
  have e : (fun φ ω => WholeField.centredField h u₀ ω φ) = fun φ ω => h ω φ - ∫ z, u₀ z * φ z := by
    funext φ ω
    exact WholeField.centredField_apply h hu₀.1 ω φ
  rw [e]
  exact hh.2 u₀ hu₀

theorem measurable_cutLife (m : ℝ≥0) : Measurable fun ζ : ℝ≥0∞ => cutLife ζ m :=
  Measurable.ite (measurableSet_le measurable_id measurable_const) measurable_id measurable_const

/-- **A capped version of a flow line**: continuous for every `ω`, measurable at each time, started at `x`, frozen
after `m`, almost surely the capped flow line; its coordinates and its killing record are almost surely Borel
functions of the centred field (Lemma 7.5). -/
theorem exists_capped_version (hL75 : Theorem15.Lemma75Statement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    (hη : IsFlowLine κ b jumps x θ P h η ζ) (u₀ : ℂ → ℝ) (m : ℝ≥0) :
    ∃ ηc : Ω → ℝ≥0 → ℂ, (∀ ω, Continuous (ηc ω)) ∧ (∀ t, Measurable fun ω => ηc ω t) ∧
      (∀ ω, ηc ω 0 = x) ∧ (∀ ω t, m ≤ t → ηc ω t = ηc ω m) ∧
      (∀ᵐ ω ∂P, ∀ t, ηc ω t = η ω (capTime m (ζ ω) t)) ∧
      (∀ t : ℝ≥0, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
        (fun ω => ηc ω t) =ᵐ[P] fun ω => f (WholeField.centredField h u₀ ω)) ∧
      (∃ f : DistOn upperHalfPlaneOpens → ℝ≥0∞, Measurable f ∧
        (fun ω => cutLife (ζ ω) m) =ᵐ[P] fun ω => f (WholeField.centredField h u₀ ω)) := by
  classical
  obtain ⟨Φ, hΦm, hΦ⟩ := hL75 κ hκ hκ4 b jumps hb x θ
  have hΦh := hΦ P h hh η ζ hη
  have hζm := measurable_lifetime_of_isFlowLine hη
  obtain ⟨η', hη'm, hη'⟩ := exists_measurable_version_of_isFlowLine hη
  obtain ⟨_, _, _, _, _, _, -, -, htr⟩ := hη
  -- the good event
  set good : Ω → Prop := fun ω => ContinuousOn (η ω) {s | (s : ℝ≥0∞) ≤ ζ ω} ∧ η ω 0 = x ∧
    (∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ ω → η' ω s = η ω s) ∧ (Φ (h ω)).1 = ζ ω ∧
    ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ ω → (Φ (h ω)).2 s = η ω s with hgooddef
  have hgood : ∀ᵐ ω ∂P, good ω := by
    filter_upwards [htr, hη', hΦh] with ω h1 h2 h3
    refine ⟨?_, ?_, h2, h3.1, h3.2⟩
    · have hc := h1.2.1.add (continuousOn_const (c := (x : ℂ)))
      refine hc.congr fun s _ => ?_
      simp
    · have := h1.1
      simp only at this
      exact sub_eq_zero.1 this
  set G : Set Ω := (toMeasurable P {ω | ¬ good ω})ᶜ with hGdef
  have hGm : MeasurableSet G := (measurableSet_toMeasurable _ _).compl
  have hGg : ∀ ω ∈ G, good ω := fun ω hω => by
    by_contra hng
    exact hω (subset_toMeasurable _ _ hng)
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := by
    rw [ae_iff]
    have e : {ω | ¬ ω ∈ G} = toMeasurable P {ω | ¬ good ω} := by ext ω; simp [hGdef]
    rw [e, measure_toMeasurable]
    exact ae_iff.1 hgood
  have hcont' : ∀ ω ∈ G, ContinuousOn (η' ω) {s | (s : ℝ≥0∞) ≤ ζ ω} := fun ω hω =>
    (hGg ω hω).1.congr fun s hs => (hGg ω hω).2.2.1 s hs
  have hcap : ∀ ω ∈ G, ∀ t, capPath m (ζ ω, η' ω) t = η ω (capTime m (ζ ω) t) := fun ω hω t => by
    rw [capPath_eq m (hcont' ω hω) t, (hGg ω hω).2.2.1 _ (capTime_le m (ζ ω) t)]
  refine ⟨fun ω t => if ω ∈ G then capPath m (ζ ω, η' ω) t else (x : ℂ), fun ω => ?_, fun t => ?_,
    fun ω => ?_, fun ω t ht => ?_, ?_, fun t => ?_, ?_⟩
  · by_cases hω : ω ∈ G
    · simp only [hω, ↓reduceIte]
      have e : (fun t => capPath m (ζ ω, η' ω) t) = fun t => η' ω (capTime m (ζ ω) t) :=
        funext (capPath_eq m (hcont' ω hω))
      rw [e]
      exact continuous_capTime_comp m (hcont' ω hω)
    · simp only [hω, ↓reduceIte]
      exact continuous_const
  · exact Measurable.ite hGm ((measurable_capPath m t).comp (hζm.prodMk (measurable_pi_iff.2 hη'm)))
      measurable_const
  · by_cases hω : ω ∈ G
    · simp only [hω, ↓reduceIte]
      rw [hcap ω hω, show capTime m (ζ ω) 0 = 0 from min_eq_left zero_le]
      exact (hGg ω hω).2.1
    · simp only [hω, ↓reduceIte]
  · by_cases hω : ω ∈ G
    · simp only [hω, ↓reduceIte]
      rw [hcap ω hω, hcap ω hω]
      congr 1
      unfold capTime
      rw [min_eq_right ((ENNReal.coe_le_coe.1 ?_).trans ht), min_eq_right (ENNReal.coe_le_coe.1 ?_)]
      · rw [ENNReal.coe_toNNReal (ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_right _ _))]
        exact min_le_right _ _
      · rw [ENNReal.coe_toNNReal (ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_right _ _))]
        exact min_le_right _ _
    · simp only [hω, ↓reduceIte]
  · filter_upwards [hGae] with ω hω t
    simp only [hω, ↓reduceIte]
    exact hcap ω hω t
  · refine ⟨fun g => capPath m (Φ (g + SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀)) t,
      (measurable_capPath m t).comp (hΦm.comp (WholeField.measurable_add_dist _)), ?_⟩
    filter_upwards [hGae] with ω hω
    simp only [hω, ↓reduceIte, WholeField.centredField, sub_add_cancel]
    have hg := hGg ω hω
    rw [← Prod.mk.eta (p := Φ (h ω)), hg.2.2.2.1]
    exact capPath_congr m (fun s hs => (hg.2.2.1 s hs).trans (hg.2.2.2.2 s hs).symm) t
  · refine ⟨fun g => cutLife (Φ (g + SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀)).1 m,
      (measurable_cutLife m).comp (measurable_fst.comp (hΦm.comp (WholeField.measurable_add_dist _))), ?_⟩
    filter_upwards [hGae] with ω hω
    simp only [WholeField.centredField, sub_add_cancel, (hGg ω hω).2.2.2.1]

end Flow

/-! ### Lemma 7.7's marked locality for two flow lines -/

/-- **Lemma 7.7's marked locality for two capped flow lines** (the input (b) of (R1), "marked locality off the union",
on the `m`-capped grid box). Setting of `FirstContactKernelClockStatement`. From Lemma 7.5 (`Lemma75Statement`),
Lemma 7.7's common first point (`Lemma77Statement`) and Aux. lemma 56 at first entrance times
(`RetainedRangeEntranceStatement`): for every cap `m` there are capped versions `ηc₁, ηc₂` of the two flow lines
(continuous for every `ω`, measurable, almost surely `ηᵢ(· ∧ ζᵢ ∧ m)`) and a version `g` of the local-set mean of their
first-contact union `fcUnion ηc₁ ηc₂` (for the centred field `h⁰ = h − 𝔥₀`) such that, given the germs of the union
and the two retained killed histories `fcHist`, the centred field paired with a test function supported in a
complementary component `C` of the union is Gaussian with mean `g(φ)` and the zero-boundary variance of `C`.

On a realization whose first contact `(s₀, t₀)` has `s₀, t₀ ≤ m`, the first-contact union of the capped paths is
`η₁([0, s₀]) ∪ η₂([0, t₀])` (`fcLine_eq`), and its unbounded complementary component is the active domain `D` of
Lemma 7.8. -/
theorem exists_fcUnion_marked_of_isFlowLine (hL75 : Theorem15.Lemma75Statement.{u})
    (hL77 : Supp10.Lemma77Statement.{u}) (hA56 : RetainedRangeEntranceStatement.{u}) {κ : ℝ} (hκ : 0 < κ)
    (hκ4 : κ < 4) {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps)
    {x₁ x₂ θ₁ θ₂ : ℝ} (hx : x₂ < x₁) (hθ : θ₁ < θ₂ + Real.pi) {Ω : Type u} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps) {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) (m : ℝ≥0) :
    ∃ ηc₁ ηc₂ : Ω → ℝ≥0 → ℂ, (∀ ω, Continuous (ηc₁ ω)) ∧ (∀ ω, Continuous (ηc₂ ω)) ∧
      (∀ t, Measurable fun ω => ηc₁ ω t) ∧ (∀ t, Measurable fun ω => ηc₂ ω t) ∧
      (∀ᵐ ω ∂P, ∀ t, ηc₁ ω t = η₁ ω (capTime m (ζ₁ ω) t)) ∧
      (∀ᵐ ω ∂P, ∀ t, ηc₂ ω t = η₂ ω (capTime m (ζ₂ ω) t)) ∧
      ∃ g : Ω → DistOn upperHalfPlaneOpens,
        IsLocalSetMean (fcUnion ηc₁ ηc₂) (WholeField.centredField h u₀) P g ∧
        ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ∀ z₀ ∈ H \ fcUnion ηc₁ ηc₂ ω,
          tsupport φ ⊆ connectedComponentIn (H \ fcUnion ηc₁ ηc₂ ω) z₀ →
          P[fun ω' => Complex.exp (Complex.I * (WholeField.centredField h u₀ ω' φ : ℂ)) |
              germSigma (fcUnion ηc₁ ηc₂) (WholeField.centredField h u₀) ⊔
                MeasurableSpace.comap
                  (fcHist ηc₁ ηc₂ (fun ω => cutLife (ζ₁ ω) m) (fun ω => cutLife (ζ₂ ω) m)) inferInstance] ω =
            Complex.exp (Complex.I * (g ω φ : ℂ)) *
              ((Real.exp (-(1 / 2) *
                QuantumZipper.zeroGFFTestCov (connectedComponentIn (H \ fcUnion ηc₁ ηc₂ ω) z₀) φ φ) : ℝ) : ℂ) := by
  obtain ⟨ηc₁, hc₁, hm₁, h0₁, hfr₁, hag₁, hdet₁, hdetζ₁⟩ := exists_capped_version hL75 hκ hκ4 hb hh hη₁ u₀ m
  obtain ⟨ηc₂, hc₂, hm₂, h0₂, hfr₂, hag₂, hdet₂, hdetζ₂⟩ := exists_capped_version hL75 hκ hκ4 hb hh hη₂ u₀ m
  have hloc₁ := hA56 κ hκ hκ4 b jumps hb x₁ θ₁ P h hh η₁ ζ₁ hη₁ u₀ hu₀ m ηc₁ hc₁ hm₁ hag₁
  have hloc₂ := hA56 κ hκ hκ4 b jumps hb x₂ θ₂ P h hh η₂ ζ₂ hη₂ u₀ hu₀ m ηc₂ hc₂ hm₂ hag₂
  have hζm₁ := (measurable_cutLife m).comp (measurable_lifetime_of_isFlowLine hη₁)
  have hζm₂ := (measurable_cutLife m).comp (measurable_lifetime_of_isFlowLine hη₂)
  have hh0 := isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀
  -- Lemma 7.7's common first point for the capped paths
  have hfc : ∀ᵐ ω ∂P, (∃ s t : ℝ≥0, ηc₁ ω s = ηc₂ ω t) →
      ∃ s₀ t₀ : ℝ≥0, IsFirstContact (ηc₁ ω) ⊤ (ηc₂ ω) ⊤ s₀ t₀ := by
    filter_upwards [hL77 κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂, hag₁, hag₂]
      with ω h77 ha₁ ha₂
    rintro ⟨s, t, hst⟩
    rw [ha₁, ha₂] at hst
    obtain ⟨s₀, t₀, hfc, -, -⟩ := h77 ⟨_, _, capTime_le m (ζ₁ ω) s, capTime_le m (ζ₂ ω) t, hst⟩
    obtain ⟨hs₀, ht₀⟩ := hfc.2.2.2 _ _ (capTime_le m (ζ₁ ω) s) (capTime_le m (ζ₂ ω) t) hst
    have hcs₀ : capTime m (ζ₁ ω) s₀ = s₀ := capTime_of_le m (ζ₁ ω)
      (le_min hfc.1 (ENNReal.coe_le_coe.2 (hs₀.trans (capTime_le_cap m (ζ₁ ω) s))))
    have hct₀ : capTime m (ζ₂ ω) t₀ = t₀ := capTime_of_le m (ζ₂ ω)
      (le_min hfc.2.1 (ENNReal.coe_le_coe.2 (ht₀.trans (capTime_le_cap m (ζ₂ ω) t))))
    refine ⟨s₀, t₀, le_top, le_top, ?_, fun s' t' _ _ he => ?_⟩
    · rw [ha₁, ha₂, hcs₀, hct₀]
      exact hfc.2.2.1
    · rw [ha₁, ha₂] at he
      obtain ⟨a, c⟩ := hfc.2.2.2 _ _ (capTime_le m (ζ₁ ω) s') (capTime_le m (ζ₂ ω) t') he
      exact ⟨a.trans (min_le_left _ _), c.trans (min_le_left _ _)⟩
  -- the capped union is relatively closed
  have hcl : ∀ᵐ ω ∂P, IsOpen (H \ fcUnion ηc₁ ηc₂ ω) := by
    refine Eventually.of_forall fun ω => ?_
    have hK : IsCompact (ηc₁ ω '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ recFst (fullHist ηc₁ ηc₂ ω)} ∪
        ηc₂ ω '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ recSnd (fullHist ηc₁ ηc₂ ω)}) :=
      (isCompact_image_of_const (hc₁ ω) (hfr₁ ω) _).union (isCompact_image_of_const (hc₂ ω) (hfr₂ ω) _)
    have e : H \ fcUnion ηc₁ ηc₂ ω = H \ (ηc₁ ω '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ recFst (fullHist ηc₁ ηc₂ ω)} ∪
        ηc₂ ω '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ recSnd (fullHist ηc₁ ηc₂ ω)}) := by
      rw [fcUnion_eq]
      ext z
      simp only [Set.mem_sdiff, mem_inter_iff, not_and]
      exact ⟨fun ⟨hz, hn⟩ => ⟨hz, fun hu => hn hu hz⟩, fun ⟨hz, hn⟩ => ⟨hz, fun hu _ => hn hu⟩⟩
    rw [e]
    exact QuantumZipper.isOpen_H.sdiff hK.isClosed
  refine ⟨ηc₁, ηc₂, hc₁, hc₂, hm₁, hm₂, hag₁, hag₂, ?_⟩
  exact ae_condExp_exp_eq_fcUnion (x₁ := (x₁ : ℂ)) (x₂ := (x₂ : ℂ)) hh0.measurable hc₁ hc₂ h0₁ h0₂ hm₁ hm₂ hζm₁ hζm₂
    hdet₁ hdet₂ hdetζ₁ hdetζ₂ hloc₁ hloc₂ hfc hh0 hcl

end Restart

end InteractingSLE
