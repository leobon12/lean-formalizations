/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Theorem15D5Inputs
import InteractingSLE.Spec.Theorem15D5Code
import InteractingSLE.Spec.Supplement.S9Completion

/-!
# Theorem 1.5 by D.5: crossing — W5 applied to the outgoing paths in the first-contact chart

Packet PROVE-T15-D5. Follow-up note D.5, "Crossing and no recrossing": "At their first available interior meeting,
use the same common active chart and actual conditional continuation kernels. The incoming seed order has the first
path on the right. W5 applied to the outgoing common-seed paths puts the higher-angle first path on the left. This
reversal is the asserted crossing." (Supplement p. 542: "apply W5 to that same field, with the angles listed in
increasing order. It puts the higher-angle first path to the left of the lower-angle second path for every pair of
strict finite outgoing prefixes.")

The step is `chartOrderAfterCrossingStatement_of_restartLim`: PROVE-SUPP10's chart proposition
`Supp10.ChartOrderAfterCrossingStatement` from interface 2 with the active prime end
(`FirstContactRestartLimStatement`) and W5 (`Theorem15.W5Statement` on the canonical space). Its pieces:

* **W5 at each datum** under the restart kernel: the conditional continuations are the angle-`θ₂` (lower) and
  angle-`θ₁` (higher) flow lines from the common seed `0` of a GFF with the chart datum, so W5 orders all their strict
  prefixes, `K c`-almost surely.
* **Integrating it back** (`ae_mem_of_compProd_eq_of_uMeasurable`): W0's event is not known to be Borel, but on the
  dyadic prefixes it is universally measurable (`uMeasurableSet_w5Event`, from `Theorem15D5Code`); a universally
  measurable event of full `K c`-measure for almost every datum has full measure under the mixture.
* **All strict prefixes** from the dyadic ones (heredity of W0, `hasOrderedProperCompletions_of_mem_w5Event`).
* **Original time**: the chart paths are parametrized by relative capacity; the frozen `CrossesFromRightAt` reads
  them at the original times `s₀ + u`. The inverse clocks (`invClock`) extend to increasing homeomorphisms of `ℝ≥0`
  (`extClock`), and W0's predicate is invariant under such reparametrizations of the prefixes
  (`hasOrderedProperCompletions_comp`: the completions are reparametrized, ranges and seeds are unchanged).
* **Chart limits** at the original points: interface 2's active prime end at the chart times `invClock u`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Theorem15D5

open Sec7 Theorem15 Supp10 Restart Sec2.Assembly

/-! ### Integrating a universally measurable event of the conditional law -/

/-- **Integrating a universally measurable event back.** If `K` is the conditional law of `X` given `β` on `M` and a
universally measurable event `E` has `K c`-probability one for almost every value `c` of `β`, then almost surely on
`M`, `X ∈ E`. (Choose a measurable `E₁ ⊆ E` with `E \ E₁` null for the law of `X`; integrate `E₁ ∪ N` for a measurable
null hull `N` of `E \ E₁`.) -/
theorem ae_mem_of_compProd_eq_of_uMeasurable {Ω C S : Type*} [MeasurableSpace Ω] [MeasurableSpace C]
    [MeasurableSpace S] {P : Measure Ω} [IsFiniteMeasure P] {M : Set Ω} (hM : MeasurableSet M) {β : Ω → C}
    {X : Ω → S} (hβ : Measurable β) (hX : Measurable X) {K : Kernel C S} [IsMarkovKernel K]
    (hlaw : (P.restrict M).map (fun ω => (β ω, X ω)) = (P.restrict M).map β ⊗ₘ K)
    {E : Set S} (hE : LQGMetric.UMeasurableSet E) (hK : ∀ᵐ c ∂(P.restrict M).map β, ∀ᵐ s ∂(K c), s ∈ E) :
    ∀ᵐ ω ∂P, ω ∈ M → X ω ∈ E := by
  set μ : Measure S := (P.restrict M).map X with hμ
  obtain ⟨E₁, hE₁E, hE₁m, hE₁ae⟩ := (hE.nullMeasurableSet μ).exists_measurable_subset_ae_eq
  set N : Set S := toMeasurable μ (E \ E₁) with hN
  have hμN : μ N = 0 := by
    rw [hN, measure_toMeasurable]
    exact (ae_eq_set.mp hE₁ae).2
  have hNm : MeasurableSet N := measurableSet_toMeasurable _ _
  have h1 : ∀ᵐ ω ∂P, ω ∈ M → X ω ∈ E₁ ∪ N := by
    refine ae_mem_of_compProd_eq hM hβ hX hlaw (hE₁m.union hNm) ?_
    filter_upwards [hK] with c hc
    filter_upwards [hc] with s hs
    by_cases hs₁ : s ∈ E₁
    · exact Or.inl hs₁
    · exact Or.inr (subset_toMeasurable μ (E \ E₁) ⟨hs, hs₁⟩)
  have h2 : ∀ᵐ ω ∂P, ω ∈ M → X ω ∉ N := by
    rw [← ae_restrict_iff' hM]
    have : (P.restrict M) (X ⁻¹' N) = 0 := by
      rw [← Measure.map_apply hX hNm]
      exact hμN
    exact measure_eq_zero_iff_ae_notMem.mp this
  filter_upwards [h1, h2] with ω h1 h2 hω
  rcases h1 hω with h | h
  · exact hE₁E h
  · exact absurd h (h2 hω)

/-! ### W5's event on the canonical space -/

/-- W5's event on the dyadic prefixes of the restart coordinates (lower-angle path `γ₂` first). -/
def W5Event {S : Type*} (γ₁ γ₂ : S → ℝ≥0 → ℂ) (U₁ U₂ : S → ℝ≥0∞) : Set S :=
  {s | ∀ n k n' k' : ℕ, (dyad n k : ℝ≥0∞) < U₂ s → (dyad n' k' : ℝ≥0∞) < U₁ s →
    HasOrderedProperCompletions (γ₂ s) (dyad n k) (γ₁ s) (dyad n' k')}

/-- **W5's event is universally measurable** for restart coordinates. -/
theorem uMeasurableSet_w5Event {S : Type*} [MeasurableSpace S] {H : S → LQGMetric.DistOn upperHalfPlaneOpens}
    {γ₁ γ₂ : S → ℝ≥0 → ℂ} {U₁ U₂ : S → ℝ≥0∞} (hco : IsRestartCoordinates H γ₁ γ₂ U₁ U₂) :
    LQGMetric.UMeasurableSet (W5Event γ₁ γ₂ U₁ U₂) := by
  obtain ⟨-, hU₁, hU₂, hγ₁, hγ₂, hc₁, hc₂⟩ := hco
  set code : S → CCode × CCode := fun s => (encC (γ₂ s), encC (γ₁ s)) with hcode
  have hcm : Measurable code :=
    (measurable_pi_iff.mpr fun n => measurable_pi_iff.mpr fun k => hγ₂ (dyad n k)).prodMk
      (measurable_pi_iff.mpr fun n => measurable_pi_iff.mpr fun k => hγ₁ (dyad n k))
  have hset : W5Event γ₁ γ₂ U₁ U₂ = ⋂ n : ℕ, ⋂ k : ℕ, ⋂ n' : ℕ, ⋂ k' : ℕ,
      ({s | (dyad n k : ℝ≥0∞) < U₂ s ∧ (dyad n' k' : ℝ≥0∞) < U₁ s}ᶜ ∪
        ({s | (dyad n k : ℝ≥0∞) < U₂ s ∧ (dyad n' k' : ℝ≥0∞) < U₁ s} ∩
          code ⁻¹' {p | ∃ y, (p, y) ∈ CompRel (dyad n k) (dyad n' k')})) := by
    ext s
    simp only [W5Event, mem_iInter, mem_union, mem_compl_iff, mem_inter_iff, mem_preimage, mem_ofPred_eq]
    refine forall_congr' fun n => forall_congr' fun k => forall_congr' fun n' => forall_congr' fun k' => ?_
    by_cases hP : (dyad n k : ℝ≥0∞) < U₂ s ∧ (dyad n' k' : ℝ≥0∞) < U₁ s
    · have hα : ContinuousOn (γ₂ s) (Iic (dyad n k)) := (hc₂ s).mono fun t (ht : t ≤ dyad n k) =>
        (ENNReal.coe_le_coe.mpr ht).trans hP.1.le
      have hβ : ContinuousOn (γ₁ s) (Iic (dyad n' k')) := (hc₁ s).mono fun t (ht : t ≤ dyad n' k') =>
        (ENNReal.coe_le_coe.mpr ht).trans hP.2.le
      rw [hasOrderedProperCompletions_iff_exists hα hβ]
      exact ⟨fun h => Or.inr ⟨hP, h hP.1 hP.2⟩, fun h _ _ => h.resolve_left (not_not.mpr hP) |>.2⟩
    · exact ⟨fun _ => Or.inl hP, fun _ h1 h2 => absurd ⟨h1, h2⟩ hP⟩
  rw [hset]
  have hPm : ∀ n k n' k' : ℕ,
      MeasurableSet {s | (dyad n k : ℝ≥0∞) < U₂ s ∧ (dyad n' k' : ℝ≥0∞) < U₁ s} := fun n k n' k' =>
    (measurableSet_lt measurable_const hU₂).inter (measurableSet_lt measurable_const hU₁)
  refine LQGMetric.UMeasurableSet.iInter fun n => LQGMetric.UMeasurableSet.iInter fun k =>
    LQGMetric.UMeasurableSet.iInter fun n' => LQGMetric.UMeasurableSet.iInter fun k' => ?_
  exact (LQGMetric.UMeasurableSet.of_measurableSet (hPm n k n' k').compl).union
    ((LQGMetric.UMeasurableSet.of_measurableSet (hPm n k n' k')).inter
      ((uMeasurableSet_hopcCode _ _).preimage hcm))

/-- On W5's event, every pair of strict prefixes (not only dyadic ones) has ordered proper completions. -/
theorem hasOrderedProperCompletions_of_mem_w5Event {S : Type*} {γ₁ γ₂ : S → ℝ≥0 → ℂ} {U₁ U₂ : S → ℝ≥0∞}
    {s : S} (hs : s ∈ W5Event γ₁ γ₂ U₁ U₂) {a c : ℝ≥0} (ha : (a : ℝ≥0∞) < U₂ s) (hc : (c : ℝ≥0∞) < U₁ s) :
    HasOrderedProperCompletions (γ₂ s) a (γ₁ s) c := by
  obtain ⟨n, k, han, hn⟩ := exists_dyad_btwn ha
  obtain ⟨n', k', hcn, hn'⟩ := exists_dyad_btwn hc
  exact Supp9.HasOrderedProperCompletions.mono (hs n k n' k' hn hn') han.le hcn.le

/-! ### Inverting the capacity clocks -/

section Clock

variable {c : ℝ≥0 → ℝ≥0} {U : ℝ≥0∞} {s₀ : ℝ≥0} {ζ : ℝ≥0∞}

/-- The chart time at the original time `s₀ + t`: the inverse of the clock `c`. -/
def invClock (c : ℝ≥0 → ℝ≥0) (U : ℝ≥0∞) (s₀ t : ℝ≥0) : ℝ≥0 :=
  Function.invFunOn c {u : ℝ≥0 | (u : ℝ≥0∞) ≤ U} (s₀ + t)

theorem invClock_spec (himg : c '' {u | (u : ℝ≥0∞) ≤ U} = {s | s₀ ≤ s ∧ (s : ℝ≥0∞) ≤ ζ}) {t : ℝ≥0}
    (ht : ((s₀ + t : ℝ≥0) : ℝ≥0∞) ≤ ζ) :
    (invClock c U s₀ t : ℝ≥0∞) ≤ U ∧ c (invClock c U s₀ t) = s₀ + t := by
  have hmem : s₀ + t ∈ c '' {u : ℝ≥0 | (u : ℝ≥0∞) ≤ U} := by
    rw [himg]; exact ⟨le_self_add, ht⟩
  exact ⟨Function.invFunOn_mem hmem, Function.invFunOn_eq hmem⟩

theorem invClock_lt_invClock (hmono : StrictMonoOn c {u | (u : ℝ≥0∞) ≤ U})
    (himg : c '' {u | (u : ℝ≥0∞) ≤ U} = {s | s₀ ≤ s ∧ (s : ℝ≥0∞) ≤ ζ}) {t t' : ℝ≥0}
    (ht' : ((s₀ + t' : ℝ≥0) : ℝ≥0∞) ≤ ζ) (htt' : t < t') : invClock c U s₀ t < invClock c U s₀ t' := by
  have ht : ((s₀ + t : ℝ≥0) : ℝ≥0∞) ≤ ζ :=
    (ENNReal.coe_le_coe.mpr ((add_le_add_iff_left s₀).mpr htt'.le)).trans ht'
  obtain ⟨h1, e1⟩ := invClock_spec himg ht
  obtain ⟨h2, e2⟩ := invClock_spec himg ht'
  by_contra hle
  have := hmono.monotoneOn h2 h1 (not_lt.mp hle)
  rw [e1, e2] at this
  exact absurd (le_of_add_le_add_left this) (not_le.mpr htt')

theorem invClock_surj (hmono : StrictMonoOn c {u | (u : ℝ≥0∞) ≤ U})
    (himg : c '' {u | (u : ℝ≥0∞) ≤ U} = {s | s₀ ≤ s ∧ (s : ℝ≥0∞) ≤ ζ}) {a : ℝ≥0}
    (ha : ((s₀ + a : ℝ≥0) : ℝ≥0∞) ≤ ζ) {w : ℝ≥0} (hw : w ≤ invClock c U s₀ a) :
    ∃ t ≤ a, invClock c U s₀ t = w := by
  obtain ⟨ha₁, ea⟩ := invClock_spec himg ha
  have hwU : (w : ℝ≥0∞) ≤ U := (ENNReal.coe_le_coe.mpr hw).trans ha₁
  have hcw : c w ∈ {s | s₀ ≤ s ∧ (s : ℝ≥0∞) ≤ ζ} := by rw [← himg]; exact mem_image_of_mem c hwU
  have hcwa : c w ≤ s₀ + a := ea ▸ hmono.monotoneOn hwU ha₁ hw
  refine ⟨c w - s₀, tsub_le_iff_left.mpr hcwa, ?_⟩
  have hsum : s₀ + (c w - s₀) = c w := add_tsub_cancel_of_le hcw.1
  have ht : ((s₀ + (c w - s₀) : ℝ≥0) : ℝ≥0∞) ≤ ζ := by rw [hsum]; exact hcw.2
  obtain ⟨ht₁, et⟩ := invClock_spec himg ht
  exact hmono.injOn ht₁ hwU (et.trans hsum)

theorem invClock_lt (himg : c '' {u | (u : ℝ≥0∞) ≤ U} = {s | s₀ ≤ s ∧ (s : ℝ≥0∞) ≤ ζ})
    (hmono : StrictMonoOn c {u | (u : ℝ≥0∞) ≤ U}) {t : ℝ≥0}
    (ht : ((s₀ + t : ℝ≥0) : ℝ≥0∞) < ζ) : (invClock c U s₀ t : ℝ≥0∞) < U := by
  obtain ⟨h1, e1⟩ := invClock_spec himg ht.le
  obtain ⟨r, hr₁, hr₂⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp ht
  have hr : r ∈ c '' {u | (u : ℝ≥0∞) ≤ U} := by
    rw [himg]
    exact ⟨(le_self_add.trans (ENNReal.coe_lt_coe.mp hr₁).le), hr₂.le⟩
  obtain ⟨w, hw, rfl⟩ := hr
  have hw' : (w : ℝ≥0∞) ≤ U := hw
  refine lt_of_le_of_ne h1 fun heq => ?_
  have hle : w ≤ invClock c U s₀ t := ENNReal.coe_le_coe.mp (hw'.trans heq.symm.le)
  have := hmono.monotoneOn hw h1 hle
  rw [e1] at this
  exact absurd (ENNReal.coe_lt_coe.mp hr₁) (not_lt.mpr this)

/-- The inverse clock on `[0, a]`, continued with slope one after `a`. -/
def extClock (g : ℝ≥0 → ℝ≥0) (a t : ℝ≥0) : ℝ≥0 := if t ≤ a then g t else g a + (t - a)

theorem extClock_of_le {g : ℝ≥0 → ℝ≥0} {a t : ℝ≥0} (ht : t ≤ a) : extClock g a t = g t := by
  simp only [extClock, ht, ↓reduceIte]

theorem extClock_strictMono {g : ℝ≥0 → ℝ≥0} {a : ℝ≥0} (hg : ∀ t t', t' ≤ a → t < t' → g t < g t') :
    StrictMono (extClock g a) := by
  intro t t' htt'
  simp only [extClock]
  by_cases ht' : t' ≤ a
  · rw [ite_eq_left (htt'.le.trans ht'), ite_eq_left ht']
    exact hg t t' ht' htt'
  · rw [ite_eq_right ht']
    push Not at ht'
    by_cases ht : t ≤ a
    · rw [ite_eq_left ht]
      calc g t ≤ g a := by
            rcases ht.lt_or_eq with h | h
            · exact (hg t a le_rfl h).le
            · rw [h]
        _ < g a + (t' - a) := lt_add_of_pos_right _ (tsub_pos_of_lt ht')
    · rw [ite_eq_right ht]
      push Not at ht
      exact (add_lt_add_iff_left _).mpr (tsub_lt_tsub_right_of_le ht.le htt')

theorem extClock_surjective {g : ℝ≥0 → ℝ≥0} {a : ℝ≥0} (hg : ∀ w ≤ g a, ∃ t ≤ a, g t = w) :
    Function.Surjective (extClock g a) := by
  intro w
  by_cases hw : w ≤ g a
  · obtain ⟨t, ht, rfl⟩ := hg w hw
    exact ⟨t, extClock_of_le ht⟩
  · push Not at hw
    refine ⟨a + (w - g a), ?_⟩
    have hgt : ¬ a + (w - g a) ≤ a := by
      push Not
      exact lt_add_of_pos_right _ (tsub_pos_of_lt hw)
    simp only [extClock, hgt, ↓reduceIte, add_tsub_cancel_left]
    exact add_tsub_cancel_of_le hw.le

end Clock

/-! ### W0's predicate under reparametrization of the prefixes -/

theorem closedLeftSide_comp {γ : ℝ≥0 → ℂ} {H : ℝ≥0 → ℝ≥0} (hs : Function.Surjective H) (h0 : H 0 = 0) :
    closedLeftSide (γ ∘ H) = closedLeftSide γ := by
  unfold closedLeftSide seedRayClosure
  rw [hs.range_comp]
  simp only [Function.comp_apply, h0]

theorem StrictMono.apply_zero_of_surjective {H : ℝ≥0 → ℝ≥0} (hH : StrictMono H)
    (hs : Function.Surjective H) : H 0 = 0 := by
  obtain ⟨x, hx⟩ := hs 0
  have h := hH.monotone (zero_le : (0 : ℝ≥0) ≤ x)
  rw [hx] at h
  exact le_antisymm h zero_le

theorem IsProperCompletion.comp {γ γ' γt : ℝ≥0 → ℂ} {A a : ℝ≥0} (hp : IsProperCompletion γ A γ')
    {H : ℝ≥0 → ℝ≥0} (hH : StrictMono H) (hs : Function.Surjective H) (ha : H a ≤ A)
    (hγ : ∀ t ≤ a, γt t = γ (H t)) : IsProperCompletion γt a (γ' ∘ H) := by
  obtain ⟨hc, hi, him, hpr, hag⟩ := hp
  refine ⟨hc.comp (hH.monotone.continuous_of_surjective hs), hi.comp hH.injective, fun t => him (H t),
    hpr.comp (hH.monotone.tendsto_atTop_atTop fun b => ⟨(hs b).choose, (hs b).choose_spec.ge⟩), ?_⟩
  intro t ht
  rw [hγ t ht, Function.comp_apply]
  exact hag _ ((hH.monotone ht).trans ha)

/-- **W0's predicate is invariant under increasing reparametrizations of the prefixes**: completions are
reparametrized by increasing homeomorphisms of `ℝ≥0`, which keep their ranges and seeds. -/
theorem hasOrderedProperCompletions_comp {α β αt βt : ℝ≥0 → ℂ} {A C a c : ℝ≥0}
    (h : HasOrderedProperCompletions α A β C) {H₁ H₂ : ℝ≥0 → ℝ≥0} (hH₁ : StrictMono H₁)
    (hs₁ : Function.Surjective H₁) (hH₂ : StrictMono H₂) (hs₂ : Function.Surjective H₂) (ha : H₁ a ≤ A)
    (hc : H₂ c ≤ C) (hα : ∀ t ≤ a, αt t = α (H₁ t)) (hβ : ∀ t ≤ c, βt t = β (H₂ t)) :
    HasOrderedProperCompletions αt a βt c := by
  obtain ⟨α', β', hα', hβ', hsub⟩ := h
  refine ⟨α' ∘ H₁, β' ∘ H₂, IsProperCompletion.comp hα' hH₁ hs₁ ha hα,
    IsProperCompletion.comp hβ' hH₂ hs₂ hc hβ, ?_⟩
  rw [closedLeftSide_comp hs₁ (StrictMono.apply_zero_of_surjective hH₁ hs₁), hs₂.range_comp]
  exact hsub

/-- W0's predicate at original times from the chart times: for a strictly increasing clock `c` mapping `[0, U]`
onto `[s₀, ζ]`, the path `u ↦ γ (invClock c U s₀ u)` read at original times. -/
theorem hasOrderedProperCompletions_invClock {γ₁ γ₂ : ℝ≥0 → ℂ} {c₁ c₂ : ℝ≥0 → ℝ≥0} {U₁ U₂ ζ₁ ζ₂ : ℝ≥0∞}
    {s₀ t₀ u v : ℝ≥0} (hm₁ : StrictMonoOn c₁ {u | (u : ℝ≥0∞) ≤ U₁})
    (him₁ : c₁ '' {u | (u : ℝ≥0∞) ≤ U₁} = {s | s₀ ≤ s ∧ (s : ℝ≥0∞) ≤ ζ₁})
    (hm₂ : StrictMonoOn c₂ {u | (u : ℝ≥0∞) ≤ U₂})
    (him₂ : c₂ '' {u | (u : ℝ≥0∞) ≤ U₂} = {t | t₀ ≤ t ∧ (t : ℝ≥0∞) ≤ ζ₂})
    (hu : ((s₀ + u : ℝ≥0) : ℝ≥0∞) ≤ ζ₁) (hv : ((t₀ + v : ℝ≥0) : ℝ≥0∞) ≤ ζ₂)
    (h : HasOrderedProperCompletions γ₂ (invClock c₂ U₂ t₀ v) γ₁ (invClock c₁ U₁ s₀ u)) :
    HasOrderedProperCompletions (fun v => γ₂ (invClock c₂ U₂ t₀ v)) v (fun u => γ₁ (invClock c₁ U₁ s₀ u)) u := by
  have hmono₁ : ∀ t t', t' ≤ u → t < t' → invClock c₁ U₁ s₀ t < invClock c₁ U₁ s₀ t' := fun t t' ht' htt' =>
    invClock_lt_invClock hm₁ him₁ ((ENNReal.coe_le_coe.mpr ((add_le_add_iff_left s₀).mpr ht')).trans hu) htt'
  have hmono₂ : ∀ t t', t' ≤ v → t < t' → invClock c₂ U₂ t₀ t < invClock c₂ U₂ t₀ t' := fun t t' ht' htt' =>
    invClock_lt_invClock hm₂ him₂ ((ENNReal.coe_le_coe.mpr ((add_le_add_iff_left t₀).mpr ht')).trans hv) htt'
  exact hasOrderedProperCompletions_comp h (extClock_strictMono hmono₂)
    (extClock_surjective fun w hw => invClock_surj hm₂ him₂ hv hw) (extClock_strictMono hmono₁)
    (extClock_surjective fun w hw => invClock_surj hm₁ him₁ hu hw) (extClock_of_le le_rfl).le
    (extClock_of_le le_rfl).le (fun t ht => by rw [extClock_of_le ht]) (fun t ht => by rw [extClock_of_le ht])

/-! ### The crossing step -/

/-- **D.5's crossing step: W5 applied to the outgoing paths in the first-contact chart** (supplement p. 542), the
chart proposition `Supp10.ChartOrderAfterCrossingStatement`, from interface 2 with the active prime end and W5 on
the canonical space. -/
theorem chartOrderAfterCrossingStatement_of_restartLim (hR : FirstContactRestartLimStatement.{u})
    (hW5 : W5Statement.{0}) : ChartOrderAfterCrossingStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ hθπ Ω _ P _ h hh η₁ η₂ ζ₁ ζ₂ h₁ h₂
  obtain ⟨S, mS, H, γ₁, γ₂, U₁, U₂, M, β, X, K, hco, hM, hβ, hX, hK, hlaw, hpair, hpath⟩ :=
    hR κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθπ P h hh η₁ η₂ ζ₁ ζ₂ h₁ h₂
  have hKE : ∀ᵐ c ∂(P.restrict M).map β, ∀ᵐ s ∂(K c), s ∈ W5Event γ₁ γ₂ U₁ U₂ := by
    filter_upwards [hpair] with c hc
    obtain ⟨hgff, hf₁, hf₂⟩ := hc
    filter_upwards [hW5 κ hκ hκ4 c.fn c.jumps (BoundaryWord.isPiecewiseConstantBoundaryData c) 0 0 θ₂ θ₁ le_rfl
      hθ (K c) H hgff γ₂ γ₁ U₂ U₁ hf₂ hf₁] with s hs n k n' k' h1 h2
    exact hs _ _ h1 h2
  filter_upwards [ae_mem_of_compProd_eq_of_uMeasurable hM hβ hX hlaw (uMeasurableSet_w5Event hco) hKE, hpath]
    with ω hEω hpω
  intro s₀ t₀ h₀ hs₀ ht₀
  obtain ⟨hMω, hC⟩ := hpω s₀ t₀ h₀ hs₀ ht₀
  have hW := hEω hMω
  obtain ⟨φ, -, -, c₁, c₂, hφ, -, -, -, -, -, -, hm₁, him₁, hm₂, him₂, -, -, hl₁, hl₂⟩ := hC
  refine ⟨φ, hφ, fun u => γ₁ (X ω) (invClock c₁ (U₁ (X ω)) s₀ u),
    fun v => γ₂ (X ω) (invClock c₂ (U₂ (X ω)) t₀ v), fun u hu => ?_, fun v hv => ?_, fun u v hu hv => ?_⟩
  · have e := (invClock_spec him₁ hu.le).2
    rw [← e]
    exact hl₁ _ (invClock_lt him₁ hm₁ hu)
  · have e := (invClock_spec him₂ hv.le).2
    rw [← e]
    exact hl₂ _ (invClock_lt him₂ hm₂ hv)
  · exact hasOrderedProperCompletions_invClock hm₁ him₁ hm₂ him₂ hu.le hv.le
      (hasOrderedProperCompletions_of_mem_w5Event hW (invClock_lt him₂ hm₂ hv) (invClock_lt him₁ hm₁ hu))

end Theorem15D5

end InteractingSLE
