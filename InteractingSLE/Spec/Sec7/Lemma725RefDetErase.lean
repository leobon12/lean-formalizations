/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma725RefDetCompose
import InteractingSLE.Spec.Sec7.Lemma72

/-!
# The measurable pocket erasure

Packet PROVE-LEMMA725REF4, item 3. Specification §7.4, Aux. lemma 125's proof (`source/spec/p385-432.md` L197–L250,
p. 398: "the measurable selected-pocket erasure"); Astra's shortcut note, Proposition 2.1 step 3.

`PocketErasure` (`Lemma725RefDetCompose`) asks that, almost surely on the word-shape event `A`, the killed relative
history of the erased counterflow traversal be a Borel function of a walls' record and the ambient counterflow at the
nonnegative rational times. It is proved here when the walls' σ-algebra `𝓦` is generated, up to null sets, by a
standard Borel record `E₀` (for the strip system: the walls at the rational times) and the counterflow is continuous on
`[0, ∞)` at every sample:

* the counterflow at every time is measurable from its values at the nonnegative rational times
  (`measurable_apply_of_rat`, by continuity);
* the traversal at every own time is then measurable for `𝓦 ∨ σ(η|_ℚ)` on `A` (the landed fixed-time measurability of
  the erasure, `PocketTraversalMeasRand.traversalMeasStatement_of_measurable`, `PocketSeedOpen.measurable_travSubInf`,
  applied with that σ-algebra);
* the relative driver, its force coordinates and the capacity lifetime are then adapted to the constant filtration of
  that σ-algebra (`adaptedBefore_segDriver_of_isDrivenCurve`, `PocketPhaseMeans.adaptedBefore_geomLW/RW`), so the
  killed history is measurable (`measurable_killedHistory_of_driven`);
* Doob–Dynkin up to null sets (`Lemma72.isAEDeterminedBy_of_measurable_sup_nullSets`) for the record `(E₀, η|_ℚ)`.

## Main results

* `measurable_apply_of_rat`, `measurable_killedHistory_of_driven`;
* **`pocketErasure_of_driven`** (generic), **`pocketErasure_cfPocket`**, **`pocketErasure_cfPocketInf`**.

Ruling R48: nothing here uses Theorem 1.2/1.3 or any result taking them as hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.Lemma725RefChart

open PocketTraversal Lemma71C LawUnique PocketWordAssembly PocketSeedOpen PocketCoupling PocketCoord

universe u

/-! ### Measurability from the rational times -/

section Rat

/-- A sequence of nonnegative rationals decreasing to a nonnegative real `u`: `⌈u (n + 1)⌉ / (n + 1)`. -/
theorem exists_seq_rat_tendsto {u : ℝ} (hu : 0 ≤ u) :
    ∃ q : ℕ → ℚ≥0, Tendsto (fun n => ((q n : ℚ≥0) : ℝ)) atTop (𝓝 u) := by
  refine ⟨fun n => (⌈u * ((n : ℝ) + 1)⌉₊ : ℚ≥0) / ((n : ℚ≥0) + 1), ?_⟩
  have hc : ∀ n : ℕ, (((⌈u * ((n : ℝ) + 1)⌉₊ : ℚ≥0) / ((n : ℚ≥0) + 1) : ℚ≥0) : ℝ) =
      (⌈u * ((n : ℝ) + 1)⌉₊ : ℝ) / ((n : ℝ) + 1) := fun n => by push_cast; ring
  simp only [hc]
  have hup : Tendsto (fun n : ℕ => u + 1 / ((n : ℝ) + 1)) atTop (𝓝 u) := by
    have h := (tendsto_const_nhds (x := u)).add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    rwa [add_zero] at h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun n => ?_) (fun n => ?_)
  · have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [le_div_iff₀ hn]
    exact Nat.le_ceil _
  · have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have h := Nat.ceil_lt_add_one (mul_nonneg hu hn.le)
    show (⌈u * ((n : ℝ) + 1)⌉₊ : ℝ) / ((n : ℝ) + 1) ≤ u + 1 / ((n : ℝ) + 1)
    rw [div_le_iff₀ hn, add_mul, one_div, inv_mul_cancel₀ hn.ne']
    exact h.le

/-- **A path continuous on `[0, ∞)` is measurable at every time from its values at the nonnegative rationals.** -/
theorem measurable_apply_of_rat {Ω : Type*} {m : MeasurableSpace Ω} {η : Ω → ℝ → ℂ}
    (hηc : ∀ ω, ContinuousOn (η ω) (Ici 0)) (hq : ∀ q : ℚ≥0, Measurable[m] fun ω => η ω (q : ℝ)) {u : ℝ}
    (hu : 0 ≤ u) : Measurable[m] fun ω => η ω u := by
  obtain ⟨q, hqt⟩ := exists_seq_rat_tendsto hu
  refine measurable_of_tendsto_metrizable (fun n => hq (q n)) (tendsto_pi_nhds.2 fun ω => ?_)
  have hw : Tendsto (fun n => ((q n : ℚ≥0) : ℝ)) atTop (𝓝[Ici 0] u) :=
    tendsto_nhdsWithin_iff.2 ⟨hqt, Eventually.of_forall fun n => Set.mem_Ici.2 (q n).cast_nonneg⟩
  exact ((hηc ω u hu).tendsto).comp hw

end Rat

/-! ### The killed history of a driven random curve -/

section Killed

variable {α : Type*} [mα : MeasurableSpace α] {nL nR : ℕ}

/-- **The killed history of a driven random curve with measurable fixed-time values and measurable marks is
measurable**: the relative driver, its force coordinates and the capacity lifetime are adapted to the constant
filtration. -/
theorem measurable_killedHistory_of_driven {γ : α → ℝ → ℂ} (hγ : ∀ ω, IsDrivenCurve (γ ω))
    (hm : ∀ u, 0 ≤ u → Measurable fun ω => γ ω u) {xL : α → Fin nL → ℝ} {xR : α → Fin nR → ℝ}
    (hxL : Measurable xL) (hxR : Measurable xR) :
    Measurable (killedHistory (fun t ω => segDriver (γ ω) t) (geomLW (fun t ω => segDriver (γ ω) t) xL)
      (geomRW (fun t ω => segDriver (γ ω) t) xR) (fun ω => capLife (γ ω))) := by
  set 𝓖 : Filtration ℝ≥0 mα := Filtration.const ℝ≥0 mα le_rfl with h𝓖
  have hpre : IsPrefixAdapted 𝓖 γ := fun r n k => PocketMeas.measurableSet_prefixEvent hγ hm r n k
  have hWa := PocketTraversal.adaptedBefore_segDriver_of_isDrivenCurve hγ hpre
  have hWc : ∀ ω, ContinuousOn (fun s => segDriver (γ ω) s) {s : ℝ≥0 | (s : ℝ≥0∞) < capLife (γ ω)} :=
    fun ω => (hγ ω).segDriver_spec.2.1
  exact measurable_killedHistory (Coupling.isMeasurableKilledDriving_of_adaptedBefore hWa
    (fun i => PocketPhaseMeans.adaptedBefore_geomLW hWc hWa hxL i)
    (fun j => PocketPhaseMeans.adaptedBefore_geomRW hWc hWa hxR j))

end Killed

/-! ### The erasure -/

section Erase

/-- **The walls' σ-algebra enlarged by the counterflow at the nonnegative rational times.** -/
@[instance_reducible] def wallsRatSigma {Ω : Type*} (𝓦 : MeasurableSpace Ω) (η : Ω → ℝ → ℂ) : MeasurableSpace Ω :=
  𝓦 ⊔ MeasurableSpace.comap (fun ω (q : ℚ≥0) => η ω q) inferInstance

variable {Ω : Type u} {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- **The measurable pocket erasure for a driven traversal** (generic): if `𝓦 ≤ σ(E₀) ∨ 𝒩` for a walls-measurable
standard Borel record `E₀`, the counterflow `η` is measurable at fixed times, and on the
walls-event `A` the traversal `γ` is a driven curve whose fixed-time values are measurable for `𝓦 ∨ σ(η|_ℚ)` with
walls-measurable marks, then `PocketErasure` holds with the record `E₀`. -/
theorem pocketErasure_of_driven [IsProbabilityMeasure P] {nL nR : ℕ} (h𝓦 : 𝓦 ≤ mΩ) {A : Set Ω}
    (hA : MeasurableSet[𝓦] A) {η : Ω → ℝ → ℂ}
    (hηm : ∀ u, 0 ≤ u → Measurable fun ω => η ω u) {γ : Ω → ℝ → ℂ} (hγ : ∀ ω ∈ A, IsDrivenCurve (γ ω))
    (hγm : ∀ u, 0 ≤ u → Measurable[MeasurableSpace.comap Subtype.val (wallsRatSigma 𝓦 η)] fun ω : A => γ ω u)
    {xL : Ω → Fin (nL + 1) → ℝ} {xR : Ω → Fin (nR + 1) → ℝ}
    (hxLm : Measurable[MeasurableSpace.comap Subtype.val 𝓦] (fun ω : A => xL ω))
    (hxRm : Measurable[MeasurableSpace.comap Subtype.val 𝓦] (fun ω : A => xR ω))
    {ε₀ : Type u} [MeasurableSpace ε₀] [StandardBorelSpace ε₀] {E₀ : Ω → ε₀} (hE₀ : Measurable[𝓦] E₀)
    (hgen : 𝓦 ≤ MeasurableSpace.comap E₀ inferInstance ⊔ Ito.nullSets P) :
    PocketErasure 𝓦 P A γ xL xR η := by
  classical
  set ηQ : Ω → ℚ≥0 → ℂ := fun ω q => η ω q with hηQ
  set K : Ω → HistorySpace (nL + 1) (nR + 1) := killedHistory (fun t ω => segDriver (γ ω) t)
    (geomLW (fun t ω => segDriver (γ ω) t) xL) (geomRW (fun t ω => segDriver (γ ω) t) xR)
    (fun ω => capLife (γ ω)) with hK
  set f : Ω → HistorySpace (nL + 1) (nR + 1) := A.piecewise K fun _ => 0 with hf
  -- the killed history on `A` is measurable for `𝓦 ∨ σ(η|_ℚ)`
  have hKA : Measurable[MeasurableSpace.comap Subtype.val (wallsRatSigma 𝓦 η)] fun ω : A => K ω :=
    @measurable_killedHistory_of_driven A (MeasurableSpace.comap Subtype.val (wallsRatSigma 𝓦 η)) (nL + 1) (nR + 1)
      (fun ω : A => γ ω) (fun ω => hγ ω ω.2) hγm (fun ω : A => xL ω) (fun ω : A => xR ω)
      (hxLm.mono (MeasurableSpace.comap_mono le_sup_left) le_rfl)
      (hxRm.mono (MeasurableSpace.comap_mono le_sup_left) le_rfl)
  have hfm : Measurable[wallsRatSigma 𝓦 η] f := by
    refine @measurable_of_restrict_of_restrict_compl Ω _ (wallsRatSigma 𝓦 η) _ f A
      (le_sup_left (b := MeasurableSpace.comap ηQ inferInstance) _ hA) ?_ ?_
    · have e : A.domRestrict f = fun ω : A => K ω := funext fun ω =>
        (piecewise_eq_of_mem A K (fun _ => 0) ω.2 : f ω = K ω)
      rw [e]
      exact hKA
    · have e : Aᶜ.domRestrict f = fun _ => 0 := funext fun ω =>
        (piecewise_eq_of_notMem A K (fun _ => 0) ω.2 : f ω = 0)
      rw [e]
      exact measurable_const
  -- the record `Y = (E₀, η|_ℚ)` and Doob–Dynkin up to null sets
  set Y : Ω → ε₀ × (ℚ≥0 → ℂ) := fun ω => (E₀ ω, ηQ ω) with hY
  have hYm : Measurable Y :=
    (hE₀.mono h𝓦 le_rfl).prodMk (measurable_pi_iff.2 fun q : ℚ≥0 => hηm (q : ℝ) (NNRat.cast_nonneg q))
  have hle : wallsRatSigma 𝓦 η ≤ MeasurableSpace.comap Y inferInstance ⊔ Ito.nullSets P := by
    have h1 : MeasurableSpace.comap E₀ inferInstance ≤ MeasurableSpace.comap Y inferInstance := by
      have e : E₀ = Prod.fst ∘ Y := rfl
      rw [e, ← MeasurableSpace.comap_comp]
      exact MeasurableSpace.comap_mono measurable_fst.comap_le
    have h2 : MeasurableSpace.comap ηQ inferInstance ≤ MeasurableSpace.comap Y inferInstance := by
      have e : ηQ = Prod.snd ∘ Y := rfl
      rw [e, ← MeasurableSpace.comap_comp]
      exact MeasurableSpace.comap_mono measurable_snd.comap_le
    exact sup_le (hgen.trans (sup_le_sup_right h1 _)) (h2.trans le_sup_left)
  obtain ⟨g, hg, hfg⟩ := Lemma72.isAEDeterminedBy_of_measurable_sup_nullSets (P := P) hYm (hfm.mono hle le_rfl)
  refine ⟨ε₀, inferInstance, inferInstance, E₀, fun p => g (p.1, p.2), hE₀, hg, ?_⟩
  filter_upwards [hfg] with ω hω hωA
  have e : f ω = K ω := piecewise_eq_of_mem A K _ hωA
  change K ω = g (E₀ ω, ηQ ω)
  rw [← e]
  exact hω

open WangWu Lemma71I PocketJordan PocketMarks in
/-- **The measurable pocket erasure for a bounded change pocket** (`pocketErasure_of_driven` with the traversal's
fixed-time measurability, `traversalMeasStatement_of_measurable`, for the σ-algebra `𝓦 ∨ σ(η|_ℚ)`). -/
theorem pocketErasure_cfPocket [IsProbabilityMeasure P] {nL nR : ℕ} (h𝓦 : 𝓦 ≤ mΩ) {R L : Ω → ℝ≥0 → ℂ}
    {r : ℝ≥0} (hRm : ∀ t, Measurable[𝓦] fun ω => R ω t) (hLm : ∀ t, Measurable[𝓦] fun ω => L ω t)
    {G : Set Ω} (hGm : MeasurableSet[𝓦] G) {W : Ω → ℝ → ℝ} {η : Ω → ℝ → ℂ}
    (hcfg : ∀ ω ∈ G, IsCfPocketConfig (R ω) (L ω) r (W ω) (η ω)) (hηc : ∀ ω, ContinuousOn (η ω) (Ici 0))
    (hηm : ∀ u, 0 ≤ u → Measurable fun ω => η ω u) {A : Set Ω} (hA : MeasurableSet[𝓦] A) (hAG : A ⊆ G)
    {ψ : Ω → ℂ → ℂ} (hψ : ∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω)) (hψm : @IsPointMeasurable Ω 𝓦 R L r G ψ)
    {xL : Ω → Fin (nL + 1) → ℝ} {xR : Ω → Fin (nR + 1) → ℝ}
    (hxLm : Measurable[MeasurableSpace.comap Subtype.val 𝓦] (fun ω : A => xL ω))
    (hxRm : Measurable[MeasurableSpace.comap Subtype.val 𝓦] (fun ω : A => xR ω))
    {ε₀ : Type u} [MeasurableSpace ε₀] [StandardBorelSpace ε₀] {E₀ : Ω → ε₀} (hE₀ : Measurable[𝓦] E₀)
    (hgen : 𝓦 ≤ MeasurableSpace.comap E₀ inferInstance ⊔ Ito.nullSets P) :
    PocketErasure 𝓦 P A (travAll R L r η ψ) xL xR η := by
  have hηm' : ∀ u, 0 ≤ u → Measurable[wallsRatSigma 𝓦 η] fun ω => η ω u := fun u hu =>
    (measurable_apply_of_rat hηc (fun q => (measurable_pi_apply q).comp (comap_measurable _)) hu).mono
      le_sup_right le_rfl
  have hγm := PocketTraversalMeasRand.traversalMeasStatement_of_measurable (mΩ := wallsRatSigma 𝓦 η)
    (le_sup_left : 𝓦 ≤ wallsRatSigma 𝓦 η) hRm hLm hGm hcfg hηm' A
    (le_sup_left (b := MeasurableSpace.comap (fun ω (q : ℚ≥0) => η ω q) inferInstance) _ hA) hAG ψ hψ hψm
  exact pocketErasure_of_driven h𝓦 hA hηm (fun ω hω => ((hcfg ω (hAG hω)).isDrivenCurve (hψ ω hω)).1) hγm
    hxLm hxRm hE₀ hgen

/-- **The measurable pocket erasure for a change pocket opening at the flow seed** (with
`PocketSeedOpen.measurable_travSubInf` for the σ-algebra `𝓦 ∨ σ(η|_ℚ)`). -/
theorem pocketErasure_cfPocketInf [IsProbabilityMeasure P] {nL nR : ℕ} (h𝓦 : 𝓦 ≤ mΩ) {R L : Ω → ℝ≥0 → ℂ}
    {r : ℝ≥0} (hRm : ∀ t, Measurable[𝓦] fun ω => R ω t) (hLm : ∀ t, Measurable[𝓦] fun ω => L ω t)
    {G : Set Ω} (hGm : MeasurableSet[𝓦] G) {W : Ω → ℝ → ℝ} {η : Ω → ℝ → ℂ}
    (hcfg : ∀ ω ∈ G, IsCfPocketConfigInf (R ω) (L ω) r (W ω) (η ω)) (hηc : ∀ ω, ContinuousOn (η ω) (Ici 0))
    (hηm : ∀ u, 0 ≤ u → Measurable fun ω => η ω u) {A : Set Ω} (hA : MeasurableSet[𝓦] A) (hAG : A ⊆ G)
    {ψ : Ω → ℂ → ℂ} (hψ : ∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω))
    (hψm : @IsPointMeasurableInf Ω 𝓦 R L r G ψ) {xL : Ω → Fin (nL + 1) → ℝ} {xR : Ω → Fin (nR + 1) → ℝ}
    (hxLm : Measurable[MeasurableSpace.comap Subtype.val 𝓦] (fun ω : A => xL ω))
    (hxRm : Measurable[MeasurableSpace.comap Subtype.val 𝓦] (fun ω : A => xR ω))
    {ε₀ : Type u} [MeasurableSpace ε₀] [StandardBorelSpace ε₀] {E₀ : Ω → ε₀} (hE₀ : Measurable[𝓦] E₀)
    (hgen : 𝓦 ≤ MeasurableSpace.comap E₀ inferInstance ⊔ Ito.nullSets P) :
    PocketErasure 𝓦 P A (travAllInf R L r η ψ) xL xR η := by
  have hηm' : ∀ u, 0 ≤ u → Measurable[wallsRatSigma 𝓦 η] fun ω => η ω u := fun u hu =>
    (measurable_apply_of_rat hηc (fun q => (measurable_pi_apply q).comp (comap_measurable _)) hu).mono
      le_sup_right le_rfl
  have hγm : ∀ u, 0 ≤ u → Measurable[MeasurableSpace.comap Subtype.val (wallsRatSigma 𝓦 η)]
      fun ω : A => travAllInf R L r η ψ ω u := fun u hu =>
    measurable_travSubInf (mΩ := wallsRatSigma 𝓦 η) (le_sup_left : 𝓦 ≤ wallsRatSigma 𝓦 η) hRm hLm hGm hcfg hηm'
      hAG hψ hψm hu
  exact pocketErasure_of_driven h𝓦 hA hηm (fun ω hω => ((hcfg ω (hAG hω)).isDrivenCurve (hψ ω hω)).1) hγm
    hxLm hxRm hE₀ hgen

end Erase

end InteractingSLE.Sec7.Lemma725RefChart
