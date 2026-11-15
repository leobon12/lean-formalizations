/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Ito.Measurability
import InteractingSLE.Spec.Supplement.LPTrace

/-!
# Relative continuations read in the physical history: the generic core

Packet PROVE-GB6-RELSAFE (shared core for GB6, BW1 and GW4). A relative continuation (GB6's counterflow read in the
chart of the retained flow prefix, BW1's relative chain, GW4's relative counterflow) has a relative driver `R` that
is a version: it is defined through a measurable choice and identified with the true relative driver only almost
surely. K2's inputs (S)/(L) at physical lines (`Aux79.hasSafeLaw_of_lineKernel`,
`BW1Lines.hasSafeLaw_life_of_lineKernel`) need the relative filtration, traced on `{q ≤ a(t)}`, inside the physical
filtration at `t`: the relative driver up to `q` and the relative stop must be functions of the record and of the
physical driver up to `t`, up to null sets. This file isolates the measure-theoretic part, valid for any relative
continuation:

* `physSigma rec W t = σ(rec) ∨ σ(W_r, r ≤ t)` and the filtration `physFilt` with the null sets added; the physical
  driver frozen at `t` and the trace reader `LP.traceAt v` (`v ≤ t`) are `physSigma t`-measurable;
* `measurableSet_of_ae_eq`: a σ-algebra containing the null sets contains every measurable set a.e. equal to one of
  its sets;
* **`measurableSet_le_inter_of_lt`**: if `R` (continuous) agrees almost surely, below a measurable relative clock
  `c`, with a process `Y` measurable for `m`, then `{u ≤ c} ∩ {R_u ∈ B}` is in `m` (left limits at the endpoint);
* **`measurableSet_inter_stop_le`**: a stop `V = ρ(rec, R)` given by a measurable path rule `ρ` is, on an event of
  `m` where `R = Y` up to `min(V, y)`, a `m`-event `{V ≤ y}`;
* **`measurable_min_stop`**: the relative clock stopped at the version stop, `min(c, V)`, is `m`-measurable.

The instance-specific input is the process `Y`: a relative driver computed from the record and from the physical
driver up to `t` (for GB6: `RelSafeGB6Drv`, the canonical drivers of the mapped local curves).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Supp8.RelSafe

section Phys

variable {Ω : Type*} {ε : Type*} [MeasurableSpace ε]

/-- **The physical σ-algebra at time `t`**: the record and the physical driver on `[0, t]`. -/
@[instance_reducible]
def physSigma (rec : Ω → ε) (W : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) : MeasurableSpace Ω :=
  MeasurableSpace.comap rec inferInstance ⊔
    ⨆ (r : ℝ≥0) (_ : r ≤ t), MeasurableSpace.comap (W r) inferInstance

theorem measurable_rec_physSigma (rec : Ω → ε) (W : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) :
    Measurable[physSigma rec W t] rec :=
  Measurable.of_comap_le le_sup_left

theorem measurable_physSigma_apply {rec : Ω → ε} {W : ℝ≥0 → Ω → ℝ} {r t : ℝ≥0} (hr : r ≤ t) :
    Measurable[physSigma rec W t] (W r) :=
  Measurable.of_comap_le ((le_iSup₂_of_le (f := fun (r : ℝ≥0) (_ : r ≤ t) =>
    MeasurableSpace.comap (W r) inferInstance) r hr le_rfl).trans le_sup_right)

theorem physSigma_mono {rec : Ω → ε} {W : ℝ≥0 → Ω → ℝ} {s t : ℝ≥0} (hst : s ≤ t) :
    physSigma rec W s ≤ physSigma rec W t :=
  sup_le_sup_left (iSup₂_le fun r hr => le_iSup₂_of_le (f := fun (r : ℝ≥0) (_ : r ≤ t) =>
    MeasurableSpace.comap (W r) inferInstance) r (hr.trans hst) le_rfl) _

theorem physSigma_le [mΩ : MeasurableSpace Ω] {rec : Ω → ε} (hrec : Measurable rec) {W : ℝ≥0 → Ω → ℝ}
    (hW : ∀ r, Measurable (W r)) (t : ℝ≥0) : physSigma rec W t ≤ mΩ :=
  sup_le hrec.comap_le (iSup₂_le fun r _ => (hW r).comap_le)

/-- The physical driver frozen at `t` is a `physSigma t`-measurable path. -/
theorem measurable_freezeAt_physSigma (rec : Ω → ε) (W : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) :
    Measurable[physSigma rec W t] fun ω => LP.freezeAt t (fun r => W r ω) :=
  (@measurable_pi_iff Ω ℝ≥0 (fun _ => ℝ) (physSigma rec W t) _ _).2 fun r =>
    measurable_physSigma_apply (min_le_right r t)

/-- The measurable trace reader at a time `v ≤ t` is `physSigma t`-measurable. -/
theorem measurable_traceAt_physSigma (rec : Ω → ε) (W : ℝ≥0 → Ω → ℝ) {v t : ℝ≥0} (hv : v ≤ t) :
    Measurable[physSigma rec W t] fun ω => LP.traceAt v (fun r => W r ω) := by
  have he : (fun ω => LP.traceAt v (fun r => W r ω)) =
      fun ω => LP.traceAt v (LP.freezeAt t (fun r => W r ω)) := by
    funext ω
    refine LP.traceAt_congr fun r hr => ?_
    show W r ω = W (min r t) ω
    rw [min_eq_left (hr.trans hv)]
  rw [he]
  exact (LP.measurable_traceAt v).comp (measurable_freezeAt_physSigma rec W t)

/-- **The physical filtration** with the null sets: `σ(rec) ∨ σ(W_r, r ≤ t) ∨ 𝒩_P`. -/
def physFilt [mΩ : MeasurableSpace Ω] {rec : Ω → ε} (hrec : Measurable rec) {W : ℝ≥0 → Ω → ℝ}
    (hW : ∀ r, Measurable (W r)) (P : Measure Ω) : Filtration ℝ≥0 mΩ where
  seq t := physSigma rec W t ⊔ Ito.nullSets P
  mono' _ _ hst := sup_le_sup_right (physSigma_mono hst) _
  le' t := sup_le (physSigma_le hrec hW t) (Ito.nullSets_le P)

theorem physFilt_apply [mΩ : MeasurableSpace Ω] {rec : Ω → ε} (hrec : Measurable rec) {W : ℝ≥0 → Ω → ℝ}
    (hW : ∀ r, Measurable (W r)) (P : Measure Ω) (t : ℝ≥0) :
    physFilt hrec hW P t = physSigma rec W t ⊔ Ito.nullSets P := rfl

theorem physSigma_le_physFilt [mΩ : MeasurableSpace Ω] {rec : Ω → ε} (hrec : Measurable rec)
    {W : ℝ≥0 → Ω → ℝ} (hW : ∀ r, Measurable (W r)) (P : Measure Ω) (t : ℝ≥0) :
    physSigma rec W t ≤ physFilt hrec hW P t := le_sup_left

theorem nullSets_le_physFilt [mΩ : MeasurableSpace Ω] {rec : Ω → ε} (hrec : Measurable rec)
    {W : ℝ≥0 → Ω → ℝ} (hW : ∀ r, Measurable (W r)) (P : Measure Ω) (t : ℝ≥0) :
    Ito.nullSets P ≤ physFilt hrec hW P t := le_sup_right

end Phys

section Null

variable {Ω : Type*} {m : MeasurableSpace Ω} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- A measurable null set is in every σ-algebra containing the null sets. -/
theorem measurableSet_of_null (hnull : Ito.nullSets P ≤ m) {N : Set Ω} (hN : MeasurableSet N) (h0 : P N = 0) :
    MeasurableSet[m] N :=
  hnull _ (MeasurableSpace.measurableSet_generateFrom ⟨hN, h0⟩)

/-- **Null modifications.** A measurable set a.e. equal to a set of `m ⊇ 𝒩_P` is in `m`. -/
theorem measurableSet_of_ae_eq (hm : m ≤ mΩ) (hnull : Ito.nullSets P ≤ m) {A C : Set Ω}
    (hA : MeasurableSet A) (hC : MeasurableSet[m] C) (h : A =ᵐ[P] C) : MeasurableSet[m] A := by
  have hCm : MeasurableSet C := hm _ hC
  have h1 : P (C \ A) = 0 := (ae_eq_set.1 h).2
  have h2 : P (A \ C) = 0 := (ae_eq_set.1 h).1
  have e : A = (C \ (C \ A)) ∪ (A \ C) := by
    ext ω; by_cases h1 : ω ∈ A <;> by_cases h2 : ω ∈ C <;> simp [h1, h2]
  rw [e]
  exact (hC.diff (measurableSet_of_null hnull (hCm.diff hA) h1)).union
    (measurableSet_of_null hnull (hA.diff hCm) h2)

/-- A measurable almost sure event is in every σ-algebra containing the null sets. -/
theorem measurableSet_of_ae (hm : m ≤ mΩ) (hnull : Ito.nullSets P ≤ m) {G : Set Ω} (hG : MeasurableSet G)
    (h : ∀ᵐ ω ∂P, ω ∈ G) : MeasurableSet[m] G :=
  measurableSet_of_ae_eq hm hnull hG (@MeasurableSet.univ Ω m)
    (h.mono fun ω hω => by simp only [hω, mem_univ])

end Null

section Core

variable {Ω : Type*} {m : MeasurableSpace Ω} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- **The relative driver at the clock is readable** (the generic core). Let `m ⊇ 𝒩_P` be a σ-algebra, `c` an
`m`-measurable relative clock and `Y` a process with `m`-measurable values. If the continuous process `R` (from `0`)
agrees almost surely with `Y` at every relative time strictly below `c`, then `{u ≤ c} ∩ {R_u ∈ B}` is in `m`
(at `u = c` the value is the left limit of the `Y`-values). -/
theorem measurableSet_le_inter_of_lt (hm : m ≤ mΩ) (hnull : Ito.nullSets P ≤ m) {R : ℝ≥0 → Ω → ℝ}
    (hRm : ∀ u, Measurable (R u)) (hRc : ∀ ω, Continuous fun u => R u ω) (hR0 : ∀ ω, R 0 ω = 0)
    {c : Ω → ℝ≥0∞} (hc : Measurable[m] c) {Y : ℝ≥0 → Ω → ℝ} (hY : ∀ u, Measurable[m] (Y u))
    (hRY : ∀ᵐ ω ∂P, ∀ u : ℝ≥0, (u : ℝ≥0∞) < c ω → R u ω = Y u ω) (u : ℝ≥0) {B : Set ℝ}
    (hB : MeasurableSet B) : MeasurableSet[m] ({ω | (u : ℝ≥0∞) ≤ c ω} ∩ R u ⁻¹' B) := by
  have hL : MeasurableSet[m] {ω | (u : ℝ≥0∞) ≤ c ω} := measurableSet_le measurable_const hc
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ u) with hu | hu
  · subst hu
    have e : R 0 ⁻¹' B = {_ω | (0 : ℝ) ∈ B} := by
      ext ω; simp only [mem_preimage, hR0 ω, mem_ofPred_eq]
    rw [e]
    exact hL.inter (MeasurableSet.const _)
  obtain ⟨v, -, hv, hvlim⟩ := exists_seq_strictMono_tendsto' hu
  let g : Ω → ℝ := fun ω => limsup (fun n => Y (v n) ω) atTop
  have hg : Measurable[m] g := Measurable.limsup fun n => hY (v n)
  have hae : ∀ᵐ ω ∂P, ω ∈ {ω | (u : ℝ≥0∞) ≤ c ω} → R u ω = g ω := by
    filter_upwards [hRY] with ω hω hωL
    have hlim : Tendsto (fun n => R (v n) ω) atTop (𝓝 (R u ω)) := ((hRc ω).tendsto u).comp hvlim
    have heq : ∀ n, R (v n) ω = Y (v n) ω := fun n =>
      hω (v n) ((ENNReal.coe_lt_coe.2 (hv n).2).trans_le hωL)
    simp only [heq] at hlim
    exact hlim.limsup_eq.symm
  refine measurableSet_of_ae_eq hm hnull ((hm _ hL).inter (hRm u hB)) (hL.inter (hg hB)) ?_
  filter_upwards [hae] with ω hω
  by_cases hωL : ω ∈ {ω | (u : ℝ≥0∞) ≤ c ω}
  · simp only [mem_inter_iff, mem_preimage, hωL, true_and, hω hωL]
  · simp only [mem_inter_iff, hωL, false_and]

/-- The traced driver at every earlier relative time (`u ≤ q`), for the event `{q ≤ c}`. -/
theorem measurableSet_le_inter_of_le (hm : m ≤ mΩ) (hnull : Ito.nullSets P ≤ m) {R : ℝ≥0 → Ω → ℝ}
    (hRm : ∀ u, Measurable (R u)) (hRc : ∀ ω, Continuous fun u => R u ω) (hR0 : ∀ ω, R 0 ω = 0)
    {c : Ω → ℝ≥0∞} (hc : Measurable[m] c) {Y : ℝ≥0 → Ω → ℝ} (hY : ∀ u, Measurable[m] (Y u))
    (hRY : ∀ᵐ ω ∂P, ∀ u : ℝ≥0, (u : ℝ≥0∞) < c ω → R u ω = Y u ω) {u q : ℝ≥0} (huq : u ≤ q) {B : Set ℝ}
    (hB : MeasurableSet B) : MeasurableSet[m] ({ω | (q : ℝ≥0∞) ≤ c ω} ∩ R u ⁻¹' B) := by
  have e : {ω | (q : ℝ≥0∞) ≤ c ω} ∩ R u ⁻¹' B =
      {ω | (q : ℝ≥0∞) ≤ c ω} ∩ ({ω | (u : ℝ≥0∞) ≤ c ω} ∩ R u ⁻¹' B) := by
    ext ω
    simp only [mem_inter_iff, mem_ofPred_eq, mem_preimage]
    exact ⟨fun h => ⟨h.1, (ENNReal.coe_le_coe.2 huq).trans h.1, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩
  rw [e]
  exact (measurableSet_le measurable_const hc).inter
    (measurableSet_le_inter_of_lt hm hnull hRm hRc hR0 hc hY hRY u hB)

end Core

section Stop

variable {Ω : Type*} {m : MeasurableSpace Ω} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {ε : Type*} [MeasurableSpace ε]

/-- A path frozen at `y` from a process with `m`-measurable values is an `m`-measurable path. -/
theorem measurable_freezeAt_of_apply {Y : ℝ≥0 → Ω → ℝ} (hY : ∀ u, Measurable[m] (Y u)) (y : ℝ≥0) :
    Measurable[m] fun ω => LP.freezeAt y (fun v => Y v ω) :=
  @measurable_pi_iff Ω ℝ≥0 (fun _ => ℝ) m _ _ |>.2 fun r => hY (min r y)

/-- **Stops given by path rules are readable.** Let `V = ρ(rec, R)` almost surely, with `ρ` a measurable path rule
(its value does not change when the path changes after it) and `rec` `m`-measurable, and let `L ∈ m` be an event on
which, almost surely, `R = Y` on `[0, min(V, y)]` for a process `Y` with `m`-measurable values. Then
`L ∩ {V ≤ y} ∈ m`: on `L`, `V ≤ y` iff `ρ(rec, Y frozen at y) ≤ y`. -/
theorem measurableSet_inter_stop_le (hm : m ≤ mΩ) (hnull : Ito.nullSets P ≤ m) {rec : Ω → ε}
    (hrec : Measurable[m] rec) {ρ : ε × (ℝ≥0 → ℝ) → ℝ≥0∞} (hρm : Measurable ρ)
    (hρ : ∀ (r : ε) (w w' : ℝ≥0 → ℝ), (∀ v : ℝ≥0, (v : ℝ≥0∞) ≤ ρ (r, w) → w v = w' v) → ρ (r, w') = ρ (r, w))
    {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞} (hVm : Measurable V)
    (hVρ : ∀ᵐ ω ∂P, V ω = ρ (rec ω, fun v => R v ω)) {Y : ℝ≥0 → Ω → ℝ} (hY : ∀ u, Measurable[m] (Y u))
    {L : Set Ω} (hL : MeasurableSet[m] L) (y : ℝ≥0)
    (hRY : ∀ᵐ ω ∂P, ω ∈ L → ∀ v : ℝ≥0, v ≤ y → (v : ℝ≥0∞) ≤ V ω → R v ω = Y v ω) :
    MeasurableSet[m] (L ∩ {ω | V ω ≤ y}) := by
  have hpath := measurable_freezeAt_of_apply hY y
  have hS : MeasurableSet[m] (L ∩ {ω | ρ (rec ω, LP.freezeAt y (fun v => Y v ω)) ≤ y}) :=
    hL.inter (measurableSet_le (hρm.comp (hrec.prodMk hpath)) measurable_const)
  refine measurableSet_of_ae_eq hm hnull ((hm _ hL).inter (measurableSet_le hVm measurable_const)) hS ?_
  filter_upwards [hVρ, hRY] with ω hV hω
  by_cases hωL : ω ∈ L
  · have hiff : V ω ≤ y ↔ ρ (rec ω, LP.freezeAt y (fun v => Y v ω)) ≤ y := by
      constructor
      · intro hVy
        have hagree : ∀ v : ℝ≥0, (v : ℝ≥0∞) ≤ ρ (rec ω, fun v => R v ω) →
            R v ω = LP.freezeAt y (fun v => Y v ω) v := by
          intro v hv
          rw [← hV] at hv
          have hvy : v ≤ y := ENNReal.coe_le_coe.1 (hv.trans hVy)
          show R v ω = Y (min v y) ω
          rw [min_eq_left hvy]
          exact hω hωL v hvy hv
        rw [hρ _ _ _ hagree, ← hV]
        exact hVy
      · intro hρy
        by_contra hVy
        have hyV : (y : ℝ≥0∞) < V ω := lt_of_not_ge hVy
        have hagree : ∀ v : ℝ≥0, (v : ℝ≥0∞) ≤ ρ (rec ω, LP.freezeAt y (fun v => Y v ω)) →
            LP.freezeAt y (fun v => Y v ω) v = R v ω := by
          intro v hv
          have hvy : v ≤ y := ENNReal.coe_le_coe.1 (hv.trans hρy)
          show Y (min v y) ω = R v ω
          rw [min_eq_left hvy]
          exact (hω hωL v hvy ((ENNReal.coe_le_coe.2 hvy).trans hyV.le)).symm
        have := hρ _ _ _ hagree
        rw [← hV] at this
        exact hVy (this ▸ hρy)
    simp only [mem_inter_iff, mem_ofPred_eq, hωL, true_and, hiff]
  · simp only [mem_inter_iff, hωL, false_and]

/-- **The relative clock stopped at a path-rule stop is readable.** If `R = Y` almost surely on
`{v < c, v ≤ V}` (uniformly in `v`), with `c` and `Y` `m`-measurable, then `min(c, V)` is `m`-measurable. -/
theorem measurable_min_stop (hm : m ≤ mΩ) (hnull : Ito.nullSets P ≤ m) {rec : Ω → ε}
    (hrec : Measurable[m] rec) {ρ : ε × (ℝ≥0 → ℝ) → ℝ≥0∞} (hρm : Measurable ρ)
    (hρ : ∀ (r : ε) (w w' : ℝ≥0 → ℝ), (∀ v : ℝ≥0, (v : ℝ≥0∞) ≤ ρ (r, w) → w v = w' v) → ρ (r, w') = ρ (r, w))
    {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞} (hVm : Measurable V)
    (hVρ : ∀ᵐ ω ∂P, V ω = ρ (rec ω, fun v => R v ω)) {c : Ω → ℝ≥0∞} (hc : Measurable[m] c)
    {Y : ℝ≥0 → Ω → ℝ} (hY : ∀ u, Measurable[m] (Y u))
    (hRY : ∀ᵐ ω ∂P, ∀ v : ℝ≥0, (v : ℝ≥0∞) < c ω → (v : ℝ≥0∞) ≤ V ω → R v ω = Y v ω) :
    Measurable[m] fun ω => min (c ω) (V ω) := by
  refine measurable_of_Ici (mδ := m) fun x => ?_
  let L : Set Ω := {ω | x ≤ c ω}
  have hL : MeasurableSet[m] L := measurableSet_le measurable_const hc
  have e : (fun ω => min (c ω) (V ω)) ⁻¹' Ici x =
      L \ ⋃ q : ℚ, ⋃ (_ : 0 ≤ q ∧ ((Real.toNNReal q : ℝ≥0) : ℝ≥0∞) < x),
        (L ∩ {ω | V ω ≤ (Real.toNNReal q : ℝ≥0)}) := by
    ext ω
    simp only [mem_preimage, mem_Ici, le_min_iff, Set.mem_sdiff, mem_iUnion, mem_inter_iff, mem_ofPred_eq,
      exists_prop, not_exists, not_and, L]
    constructor
    · rintro ⟨hxc, hxV⟩
      exact ⟨hxc, fun q hq _ hVq => absurd (hxV.trans hVq) (not_le.2 hq.2)⟩
    · rintro ⟨hxc, hno⟩
      refine ⟨hxc, ?_⟩
      by_contra hxV
      obtain ⟨q, hq0, hVq, hqx⟩ := ENNReal.lt_iff_exists_rat_btwn.1 (lt_of_not_ge hxV)
      exact hno q ⟨hq0, hqx⟩ hxc hVq.le
  rw [e]
  refine hL.diff (MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun hq => ?_)
  refine measurableSet_inter_stop_le hm hnull hrec hρm hρ hVm hVρ hY hL _ ?_
  filter_upwards [hRY] with ω hω hωL v hvy hvV
  exact hω v (((ENNReal.coe_le_coe.2 hvy).trans_lt hq.2).trans_le hωL) hvV

end Stop

/-! ### Left regularization: identification up to and including the clock -/

section Left

variable {Ω : Type*} {m : MeasurableSpace Ω} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- A sequence increasing strictly to `u > 0` (`0` for `u = 0`). -/
def leftSeq (u : ℝ≥0) : ℕ → ℝ≥0 :=
  if h : 0 < u then (exists_seq_strictMono_tendsto' h).choose else fun _ => 0

theorem leftSeq_lt {u : ℝ≥0} (h : 0 < u) (n : ℕ) : leftSeq u n < u := by
  simp only [leftSeq, h, ↓reduceDIte]
  exact ((exists_seq_strictMono_tendsto' h).choose_spec.2.1 n).2

theorem tendsto_leftSeq {u : ℝ≥0} (h : 0 < u) : Tendsto (leftSeq u) atTop (𝓝 u) := by
  simp only [leftSeq, h, ↓reduceDIte]
  exact (exists_seq_strictMono_tendsto' h).choose_spec.2.2

/-- **The left-regularized process**: `limsup_n Y(u_n)` along `u_n ↑ u` (`0` at `u = 0`). -/
def leftReg (Y : ℝ≥0 → Ω → ℝ) (u : ℝ≥0) (ω : Ω) : ℝ :=
  if u = 0 then 0 else limsup (fun n => Y (leftSeq u n) ω) atTop

theorem measurable_leftReg {Y : ℝ≥0 → Ω → ℝ} (hY : ∀ u, Measurable[m] (Y u)) (u : ℝ≥0) :
    Measurable[m] (leftReg Y u) := by
  by_cases hu : u = 0
  · have he : leftReg Y u = fun _ => 0 := by funext ω; simp only [leftReg, hu, ↓reduceIte]
    rw [he]; exact measurable_const
  · have he : leftReg Y u = fun ω => limsup (fun n => Y (leftSeq u n) ω) atTop := by
      funext ω; simp only [leftReg, hu, ↓reduceIte]
    rw [he]
    exact Measurable.limsup fun n => hY _

/-- **Identification up to and including the clock.** If the continuous `R` (from `0`) agrees with `Y` strictly below
`c` and up to `V`, it agrees with the left-regularized `Y` up to `c` and `V`. -/
theorem ae_eq_leftReg {R : ℝ≥0 → Ω → ℝ} (hRc : ∀ ω, Continuous fun u => R u ω) (hR0 : ∀ ω, R 0 ω = 0)
    {c V : Ω → ℝ≥0∞} {Y : ℝ≥0 → Ω → ℝ}
    (hRY : ∀ᵐ ω ∂P, ∀ u : ℝ≥0, (u : ℝ≥0∞) < c ω → (u : ℝ≥0∞) ≤ V ω → R u ω = Y u ω) :
    ∀ᵐ ω ∂P, ∀ u : ℝ≥0, (u : ℝ≥0∞) ≤ c ω → (u : ℝ≥0∞) ≤ V ω → R u ω = leftReg Y u ω := by
  filter_upwards [hRY] with ω hω u huc huV
  by_cases hu : u = 0
  · simp only [leftReg, hu, ↓reduceIte, hR0]
  have hpos : 0 < u := pos_iff_ne_zero.2 hu
  have hlim : Tendsto (fun n => R (leftSeq u n) ω) atTop (𝓝 (R u ω)) :=
    ((hRc ω).tendsto u).comp (tendsto_leftSeq hpos)
  have heq : ∀ n, R (leftSeq u n) ω = Y (leftSeq u n) ω := fun n =>
    hω _ ((ENNReal.coe_lt_coe.2 (leftSeq_lt hpos n)).trans_le huc)
      ((ENNReal.coe_lt_coe.2 (leftSeq_lt hpos n)).le.trans huV)
  simp only [heq] at hlim
  simp only [leftReg, hu, ↓reduceIte]
  exact hlim.limsup_eq.symm

end Left

end InteractingSLE.Supp8.RelSafe
