/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Carrier
import InteractingSLE.Spec.Sec5.Recovery
import InteractingSLE.Spec.Sec4.Special2Order
import InteractingSLE.Frozen.Spec.hittingSigma
import InteractingSLE.Frozen.Spec.boundaryLightConeFamily

/-!
# §5.2: the light cone in the strip carriers, and the field recovery of Proposition 5.13

Packet PROVE-SEC5-C (specification §5.2, `source/spec/p097-144.md` L840–L1004, `p145-192.md` L1–L157,
pp. 136–152).

* **Angle-varying flow lines and the light cone** in the strip, read in the chart `E`, are the frozen staged
  histories (`IsStagedHistory`, ruling R29) of the `E`-image field with the transported data `stripHData κ bL bU`,
  rooted at the seed `0`, run by the schedule programs `scheduleProgram 0 l` (`l = [(θ₁, τ₁), …, (θ_ℓ, τ_ℓ)]`, own
  switch and terminal times; §5.2, p. 136: "the flow line of `h` conditional on `η|[0, τ_{j−1}]` starting at
  `η(τ_{j−1})` with angle `θ_j`"). `stripLightConeFamily` is the union of their physical sets over the
  `Θ`-schedules with times in `Q` (Proposition 5.9 at the root `0`, Corollary 5.12); it is the schedule part of the
  frozen GW2 family `boundaryLightConeFamily` (`stripLightConeFamily_subset_boundaryLightConeFamily`).
* **Lemma 5.7** (containment and reverse chronological order) has the same pathwise and almost-sure structure as
  Lemma 4.7: it is `Sec4.lemma47_of_remark48` (generic in the explored path `η`, landed by PROVE-SEC4-B2), applied to
  the completed counterflow `Sec4.stripCounterflowPath q γ` and to the angle-varying path, with input (a) the
  continuity and simplicity of the angle-varying path (Lemma 5.6) and input (b) the first-exit statement at each
  deterministic time (Lemma 4.5 for the conditional field after mapping out the stopped path, p. 138). It is not
  restated here.
* **"`L_z` is a measurable function of `h`, since it is the closure of a countable family of field-determined
  paths"** (proof of Proposition 5.13, p. 151): `measurable_closure_iUnion_image` — the closure of a countable union of
  the ranges of random paths, continuous on `[0, 1]` and measurable at each time, is measurable for the frozen hitting
  σ-algebra (`hittingSigma`).
* **Proposition 5.13's recovery** (`prop513_of_lightConeIdentity`, conditional helper): from the light-cone identity
  `L_z = η'([0, T_z])`, `z = η'(T_z)` (Proposition 5.9, extreme-angle version, and the first visit of Lemma 5.7), the
  time density (5.7), and a hitting-measurable capacity functional reading `2T` off every trace prefix
  `η'([0, T])` (the specification's "Filling a compact set and taking its half-plane capacity are measurable
  operations"; packet PROVE-WHOLEFIELD2's `hcapHit`, with `hcap(K_t) = 2t`), every `η'(t)` is almost surely equal to
  a `σ(h)`-measurable function: "`T_z = ½ hcap(Hull(Φ(L_z)))` … Thus each pair `(T_z, z)` is determined by `h`" and
  SEC5-A's `exists_stronglyMeasurable_eq_of_dense`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology MeasureTheory
open scoped Real NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE

namespace Sec5

open Sec4 (stripHData stripHJumps)

/-! ### The light cone of the strip field at the seed -/

/-- The light-cone family of Proposition 5.9 at the root `0` (Corollary 5.12) in the strip, read in the chart `E`:
the union of the physical sets of the staged histories of the `E`-image field (data `stripHData κ bL bU`, jumps
`stripHJumps JL JU`) rooted at `0` and run by the schedule programs of all finite `Θ`-schedules with switch and
terminal times in `Q` (each retained through its actual available portion, GW2 convention). `D spec` is the driver
family of the history `spec`. The light cone is its closure. -/
def stripLightConeFamily (κ : ℝ) (bL bU : ℝ → ℝ) (JL JU : Finset ℝ) (Θ : Set ℝ) (Q : Set ℝ≥0)
    (D : ExplSpec → ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) : Set ℂ :=
  ⋃ l ∈ {l | IsSchedule Θ Q l},
    ExplState.physSet κ (stripHData κ bL bU) (stripHJumps JL JU) ⟨0, true, scheduleProgram 0 l⟩
      (D ⟨0, true, scheduleProgram 0 l⟩)

/-- The strip light-cone family is the schedule part of the frozen GW2 family (`boundaryLightConeFamily`) of the
transported data: Proposition 5.9 at the root `0` is the non-boundary case of GW2. -/
theorem stripLightConeFamily_subset_boundaryLightConeFamily (κ : ℝ) (bL bU : ℝ → ℝ) (JL JU : Finset ℝ)
    (Θ : Set ℝ) (Q : Set ℝ≥0) (D : ExplSpec → ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) :
    stripLightConeFamily κ bL bU JL JU Θ Q D ⊆
      boundaryLightConeFamily κ (stripHData κ bL bU) (stripHJumps JL JU) Θ Q D :=
  subset_union_left

/-- The root `0` belongs to the physical set of every history rooted at `0` (Proposition 5.9: "The root itself is
always included in its light cone"). -/
theorem zero_mem_physSet (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (gw2 : Bool) (p : List Instr)
    (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) : (0 : ℂ) ∈ ExplState.physSet κ b jumps ⟨0, gw2, p⟩ D := by
  unfold ExplState.physSet
  exact Or.inl (Or.inl (by simp))

/-- The root `0` is in the strip light-cone family as soon as there is one admissible schedule (e.g. the empty
schedule, which is always a schedule). -/
theorem zero_mem_stripLightConeFamily (κ : ℝ) (bL bU : ℝ → ℝ) (JL JU : Finset ℝ) (Θ : Set ℝ)
    (Q : Set ℝ≥0) (D : ExplSpec → ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) :
    (0 : ℂ) ∈ stripLightConeFamily κ bL bU JL JU Θ Q D := by
  refine mem_iUnion₂.2 ⟨[], ⟨fun p hp => absurd hp (List.not_mem_nil), List.Pairwise.nil⟩, ?_⟩
  exact zero_mem_physSet _ _ _ _ _ _

/-! ### Hitting-measurability of the closure of a countable family of random paths -/

/-- A point of an open set reached by a path continuous on `[0, 1]` is reached at a rational time of `(0, 1)`. -/
theorem exists_rat_mem_of_continuousOn {γ : ℝ → ℂ} (hγ : ContinuousOn γ (Icc 0 1)) {U : Set ℂ}
    (hU : IsOpen U) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hγt : γ t ∈ U) :
    ∃ q : ℚ, (q : ℝ) ∈ Ioo (0 : ℝ) 1 ∧ γ q ∈ U := by
  have hev : ∀ᶠ s in 𝓝[Icc 0 1] t, γ s ∈ U := (hγ t ht).preimage_mem_nhdsWithin (hU.mem_nhds hγt)
  have hcl : t ∈ closure (Ioo (0 : ℝ) 1 ∩ range ((↑) : ℚ → ℝ)) :=
    Sec4.Icc_subset_closure_rat_Ioo one_pos ht
  have hne : (𝓝[Ioo (0 : ℝ) 1 ∩ range ((↑) : ℚ → ℝ)] t).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hcl
  have hmono : 𝓝[Ioo (0 : ℝ) 1 ∩ range ((↑) : ℚ → ℝ)] t ≤ 𝓝[Icc 0 1] t :=
    nhdsWithin_mono _ (inter_subset_left.trans Ioo_subset_Icc_self)
  obtain ⟨s, hsU, hsD⟩ := ((hev.filter_mono hmono).and self_mem_nhdsWithin).exists
  obtain ⟨hs, q, rfl⟩ := hsD
  exact ⟨q, hs, hsU⟩

/-- The event that the closure of a countable union of path ranges meets an open set is the countable union, over
paths and rational times, of the events that a path is in the set at that time. -/
theorem closure_iUnion_image_inter_nonempty_iff {γ : ℕ → ℝ → ℂ} (hγ : ∀ k, ContinuousOn (γ k) (Icc 0 1))
    {U : Set ℂ} (hU : IsOpen U) :
    (closure (⋃ k, γ k '' Icc 0 1) ∩ U).Nonempty ↔
      ∃ k, ∃ q : ℚ, (q : ℝ) ∈ Ioo (0 : ℝ) 1 ∧ γ k q ∈ U := by
  rw [closure_inter_open_nonempty_iff hU]
  constructor
  · rintro ⟨_, hz, hzU⟩
    obtain ⟨k, t, ht, rfl⟩ := mem_iUnion.1 hz |>.imp fun k h => h
    exact ⟨k, exists_rat_mem_of_continuousOn (hγ k) hU ht hzU⟩
  · rintro ⟨k, q, hq, hqU⟩
    exact ⟨_, mem_iUnion.2 ⟨k, q, Ioo_subset_Icc_self hq, rfl⟩, hqU⟩

/-- **"`L_z` is a measurable function of `h`, since it is the closure of a countable family of field-determined
paths"** (proof of Proposition 5.13, p. 151). If every path `γ k ω` is continuous on `[0, 1]` and every evaluation
`ω ↦ γ k ω t` is `𝒢`-measurable, then `ω ↦ closure (⋃ k, γ k ω([0, 1]))` is measurable from `𝒢` to the frozen hitting
σ-algebra on `Set ℂ`. -/
theorem measurable_closure_iUnion_image {Ω : Type*} {𝒢 : MeasurableSpace Ω} {γ : ℕ → Ω → ℝ → ℂ}
    (hγm : ∀ k (t : ℝ), Measurable[𝒢] fun ω => γ k ω t) (hγc : ∀ k ω, ContinuousOn (γ k ω) (Icc 0 1)) :
    @Measurable Ω (Set ℂ) 𝒢 hittingSigma fun ω => closure (⋃ k, γ k ω '' Icc 0 1) := by
  refine @measurable_generateFrom Ω (Set ℂ) 𝒢 _ _ ?_
  rintro _ ⟨U, hU, -, rfl⟩
  have hset : (fun ω => closure (⋃ k, γ k ω '' Icc 0 1)) ⁻¹' {A | (A ∩ U).Nonempty} =
      ⋃ k, ⋃ q : ℚ, if (q : ℝ) ∈ Ioo (0 : ℝ) 1 then (fun ω => γ k ω q) ⁻¹' U else ∅ := by
    ext ω
    simp only [mem_preimage, mem_ofPred_eq, mem_iUnion]
    rw [closure_iUnion_image_inter_nonempty_iff (hγc · ω) hU]
    constructor
    · rintro ⟨k, q, hq, hqU⟩
      exact ⟨k, q, by rw [ite_eq_left hq]; exact hqU⟩
    · rintro ⟨k, q, hq⟩
      by_cases hq' : (q : ℝ) ∈ Ioo (0 : ℝ) 1
      · rw [ite_eq_left hq'] at hq; exact ⟨k, q, hq', hq⟩
      · rw [ite_eq_right hq'] at hq; exact hq.elim
  rw [hset]
  refine MeasurableSet.iUnion fun k => MeasurableSet.iUnion fun q => ?_
  split_ifs
  · exact hγm k q hU.measurableSet
  · exact MeasurableSet.empty

/-! ### Proposition 5.13: the counterflow is determined by the field -/

/-- The time recovered from a capacity functional: `T = ½ cap(L)` (proof of Proposition 5.13,
"`T_z = ½ hcap(Hull_ℍ(Φ(L_z)))`"). -/
def recoveredTime (cap : Set ℂ → ℝ≥0∞) (L : Set ℂ) : ℝ := (cap L).toReal / 2

/-- If the capacity functional reads `2t` off every prefix `γ([0, t])` of a capacity-parametrized trace, the
recovered time of `γ([0, T])` is `T`. -/
theorem recoveredTime_image_Icc {cap : Set ℂ → ℝ≥0∞} {γ : ℝ≥0 → ℂ}
    (hcap : ∀ t : ℝ≥0, cap (γ '' Icc 0 t) = 2 * (t : ℝ≥0∞)) (T : ℝ≥0) :
    recoveredTime cap (γ '' Icc 0 T) = T := by
  rw [recoveredTime, hcap, ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.toReal_ofNat]
  ring

/-- **Proposition 5.13 from the light-cone identity** (conditional helper; proof of Proposition 5.13, pp. 149–151).
Let `γ ω` be the counterflow trace in the capacity chart `Φ` (`hcap(K_t) = 2t`), continuous, and let `(z n, L n)`
enumerate the countable family `Γ` of terminal points of the allowed extreme-angle prefixes with their descendant
light cones `L_z` (in the chart `Φ`). Assume:
* `z n` is `𝒢`-measurable and `L n` is measurable for the hitting σ-algebra (`𝒢 = σ(h)`; "Every member of `𝒯_*` is
  determined by `h`, by Lemma 5.6", and `measurable_closure_iUnion_image`);
* `cap` is a hitting-measurable functional reading `2t` off every trace prefix `γ([0, t])` ("Filling a compact set
  and taking its half-plane capacity are measurable operations"; `WholeField.hcapHit`);
* the light-cone identity: almost surely, for every `n`, `L n = γ([0, T])` and `z n = γ(T)` for some `T` ("The
  extreme-angle version of Proposition 5.9 gives `L_z = η'([0, T_z])`", `T_z` the first visit of `z`, Lemma 5.7);
* the time density (5.7): almost surely these times are dense in `(0, ∞)`.

Then for every `t > 0` the point `γ(t)` is almost surely equal to a `𝒢`-measurable function ("This determines `η'(t)`
measurably from `h`"). -/
theorem prop513_of_lightConeIdentity {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {𝒢 : MeasurableSpace Ω} {γ : Ω → ℝ≥0 → ℂ} {z : ℕ → Ω → ℂ} {L : ℕ → Ω → Set ℂ}
    {cap : Set ℂ → ℝ≥0∞} (hcapm : Measurable[hittingSigma] cap) (hz : ∀ n, Measurable[𝒢] (z n))
    (hL : ∀ n, @Measurable Ω (Set ℂ) 𝒢 hittingSigma (L n))
    (hcap : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, cap (γ ω '' Icc 0 t) = 2 * (t : ℝ≥0∞))
    (hcont : ∀ᵐ ω ∂P, Continuous (γ ω))
    (hlc : ∀ᵐ ω ∂P, ∀ n, ∃ T : ℝ≥0, L n ω = γ ω '' Icc 0 T ∧ z n ω = γ ω T)
    (hdense : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → ∀ ε > 0,
      ∃ n, ∃ T : ℝ≥0, L n ω = γ ω '' Icc 0 T ∧ |(T : ℝ) - t| < ε)
    (t : ℝ≥0) (ht : 0 < t) :
    ∃ R : Ω → ℂ, StronglyMeasurable[𝒢] R ∧ ∀ᵐ ω ∂P, R ω = γ ω t := by
  have hT : ∀ n, Measurable[𝒢] fun ω => recoveredTime cap (L n ω) := by
    intro n
    have h1 : Measurable[𝒢] fun ω => cap (L n ω) :=
      @Measurable.comp Ω (Set ℂ) ℝ≥0∞ 𝒢 hittingSigma _ cap (L n) hcapm (hL n)
    exact h1.ennreal_toReal.div_const 2
  obtain ⟨R, hRm, hR⟩ := exists_stronglyMeasurable_eq_of_dense hT hz (t : ℝ)
  refine ⟨R, hRm, ?_⟩
  filter_upwards [hcap, hcont, hlc, hdense] with ω hcapω hcontω hlcω hdω
  have hγc : Continuous fun s : ℝ => γ ω s.toNNReal := hcontω.comp continuous_real_toNNReal
  have key := hR ω (fun s : ℝ => γ ω s.toNNReal) hγc.continuousAt ?_ ?_
  · simpa only [Real.toNNReal_coe] using key
  · intro n
    obtain ⟨T, hLT, hzT⟩ := hlcω n
    simp only [hLT, recoveredTime_image_Icc hcapω, Real.toNNReal_coe, hzT]
  · intro ε hε
    obtain ⟨n, T, hLT, hTt⟩ := hdω t ht ε hε
    exact ⟨n, by rw [hLT, recoveredTime_image_Icc hcapω]; exact hTt⟩

/-- A positive rational approximation of `t ≥ 0` from above at scale `1/(m + 1)`:
`r = (⌊t(m + 1)⌋₊ + 1)/(m + 1)`. -/
def ratAbove (m : ℕ) (t : ℝ≥0) : ℚ := ((⌊(t : ℝ) * (m + 1)⌋₊ : ℚ) + 1) / (m + 1)

theorem ratAbove_cast (m : ℕ) (t : ℝ≥0) :
    ((ratAbove m t : ℚ) : ℝ) = ((⌊(t : ℝ) * (m + 1)⌋₊ : ℝ) + 1) / (m + 1) := by
  rw [ratAbove]; push_cast; ring

theorem ratAbove_pos (m : ℕ) (t : ℝ≥0) : 0 < ratAbove m t := by
  rw [ratAbove]; positivity

theorem lt_ratAbove (m : ℕ) (t : ℝ≥0) : (t : ℝ) < ratAbove m t := by
  rw [ratAbove_cast, lt_div_iff₀ (by positivity)]
  exact Nat.lt_floor_add_one _

theorem ratAbove_le (m : ℕ) (t : ℝ≥0) : ((ratAbove m t : ℚ) : ℝ) ≤ t + 1 / (m + 1) := by
  rw [ratAbove_cast, div_le_iff₀ (by positivity), add_mul, one_div_mul_cancel (by positivity)]
  gcongr
  exact Nat.floor_le (by positivity)

theorem tendsto_ratAbove (t : ℝ≥0) :
    Tendsto (fun m : ℕ => ((ratAbove m t : ℚ) : ℝ).toNNReal) atTop (𝓝 t) := by
  have hR : Tendsto (fun m : ℕ => ((ratAbove m t : ℚ) : ℝ)) atTop (𝓝 (t : ℝ)) := by
    have hup : Tendsto (fun m : ℕ => (t : ℝ) + 1 / ((m : ℝ) + 1)) atTop (𝓝 (t : ℝ)) := by
      have h0 : Tendsto (fun m : ℕ => 1 / ((m : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have := (tendsto_const_nhds (x := (t : ℝ))).add h0
      rwa [add_zero] at this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
      (fun m => (lt_ratAbove m t).le) (fun m => ratAbove_le m t)
  have := (continuous_real_toNNReal.tendsto _).comp hR
  rw [Real.toNNReal_coe] at this
  exact this

/-- **Proposition 5.13, the whole path** (conditional helper, same inputs as `prop513_of_lightConeIdentity`;
"doing so at all positive rational `t` determines the entire continuous path and its terminal limit"): there is a
path-valued map `Γ`, each of whose evaluations is `𝒢`-measurable, that almost surely equals the counterflow trace at
every time. -/
theorem prop513_path_of_lightConeIdentity {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝒢 : MeasurableSpace Ω} {γ : Ω → ℝ≥0 → ℂ} {z : ℕ → Ω → ℂ} {L : ℕ → Ω → Set ℂ}
    {cap : Set ℂ → ℝ≥0∞} (hcapm : Measurable[hittingSigma] cap) (hz : ∀ n, Measurable[𝒢] (z n))
    (hL : ∀ n, @Measurable Ω (Set ℂ) 𝒢 hittingSigma (L n))
    (hcap : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, cap (γ ω '' Icc 0 t) = 2 * (t : ℝ≥0∞))
    (hcont : ∀ᵐ ω ∂P, Continuous (γ ω))
    (hlc : ∀ᵐ ω ∂P, ∀ n, ∃ T : ℝ≥0, L n ω = γ ω '' Icc 0 T ∧ z n ω = γ ω T)
    (hdense : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → ∀ ε > 0,
      ∃ n, ∃ T : ℝ≥0, L n ω = γ ω '' Icc 0 T ∧ |(T : ℝ) - t| < ε) :
    ∃ Γ : Ω → ℝ≥0 → ℂ, (∀ t, StronglyMeasurable[𝒢] fun ω => Γ ω t) ∧ ∀ᵐ ω ∂P, Γ ω = γ ω := by
  have hR : ∀ q : ℚ, ∃ R : Ω → ℂ, StronglyMeasurable[𝒢] R ∧
      (0 < q → ∀ᵐ ω ∂P, R ω = γ ω (q : ℝ).toNNReal) := by
    intro q
    by_cases hq : 0 < q
    · obtain ⟨R, hRm, hRe⟩ := @prop513_of_lightConeIdentity Ω mΩ P 𝒢 γ z L cap hcapm hz hL hcap hcont
        hlc hdense ((q : ℝ).toNNReal) (by simpa using hq)
      exact ⟨R, hRm, fun _ => hRe⟩
    · exact ⟨fun _ => 0, stronglyMeasurable_const, fun h => absurd h hq⟩
  choose R hRm hRe using hR
  have hall : ∀ᵐ ω ∂P, ∀ q : ℚ, 0 < q → R q ω = γ ω (q : ℝ).toNNReal := by
    rw [ae_all_iff]
    intro q
    by_cases hq : 0 < q
    · exact (hRe q hq).mono fun ω hω _ => hω
    · exact Eventually.of_forall fun ω h => absurd h hq
  refine ⟨fun ω t => limUnder atTop (fun m : ℕ => R (ratAbove m t) ω),
    fun t => StronglyMeasurable.limUnder fun m => hRm (ratAbove m t), ?_⟩
  filter_upwards [hall, hcont] with ω hω hcω
  funext t
  have hlim : Tendsto (fun m : ℕ => R (ratAbove m t) ω) atTop (𝓝 (γ ω t)) := by
    have := (hcω.tendsto t).comp (tendsto_ratAbove t)
    refine this.congr fun m => ?_
    exact (hω _ (ratAbove_pos m t)).symm
  exact hlim.limUnder_eq

end Sec5

end InteractingSLE
