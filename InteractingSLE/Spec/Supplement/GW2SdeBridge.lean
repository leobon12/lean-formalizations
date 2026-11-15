/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4RelMatch
import InteractingSLE.Spec.Supplement.GW2JDetR12StopRule
import InteractingSLE.Spec.Ito.FiltrationBasic
import InteractingSLE.Spec.Sec2.Assembly2Stage
import InteractingSLE.Spec.Sec5.GlueCond

/-!
# GW2's retained stopped SDE: from a stopped driver match to the stopped local dynamics

Packet PROVE-GW2-SDE (Theorem 1.4's GW2; ruling R106). JOINTDET's R11 property
`GW2JDetR11.RetainedStoppedSDEStatement` asks, under the full retained kernel, for local dynamics
(`GW2JDetR11.LocalDynamics.IsStopped`) of the future physical piece. GB6's engine, run on a record that
generates the retained σ-algebra (`GW2Rd.ae_isStopDrvMatch_rec`), gives only the STOPPED DRIVER MATCH: the relative
driver `R` is the canonical driver code of the relative field before its stop `V`. This file turns that match,
under an arbitrary probability measure `ν` on a space in `Type u` (in the application: the regular conditional law
given the retained record), into the stopped SDE with the PHYSICAL driver and the physical stop:

* **`exists_isStopped_of_stopDrvMatch`**: if `X` is a GFF with the data of a sorted word `c₀` under `ν`, `R` is a
  continuous measurable driver from `0` which `ν`-almost surely matches the canonical code of `(c₀, X)` before `V`,
  and `τ` is (almost surely) a stopping rule `τ₀` of the killed path `(R, V)` with `τ ≤ V` and `τ < V` when finite,
  then for every presentation `(xL, xR, ρL, ρR)` of the angle-`0` flow-line word of `c₀` (`FCDet.IsFlowType`) there
  are local dynamics with driver EXACTLY `R` and stop EXACTLY `τ` satisfying `LocalDynamics.IsStopped ν κ …`.

Route: Theorem 1.2 at universe `u` gives the field-determined driver `BRLeaf.cfDrv` of `X`, which drives an optional
hull coupling (`Exist.Staged.isOptionalHullCoupling_drv`), hence an integrated `SLE_κ(ρ)` evolution; GW4's bridge
(`GW4Rel.ae_cfDrv_eq_of_match`) identifies it with `R` before `V`; the stopping rule takes the same value on the two
killed paths (`stopRule_eq_of_agree`), so `τ` is almost surely a stopping time of the coupling's filtration; on the
usual augmentation (which contains the null sets and keeps the Brownian motion) the physical driver, the killed force
points and the stop are adapted, and the path conditions only see the paths before the stop.

**R48.** Theorem 1.4 work: Theorems 1.2–1.3 at universe `u` are used (`h12p`, `h13`), as GB6/GW4 do.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn)
open QuantumZipper (chiC)

universe u

namespace InteractingSLE.Theorem14.GW2Sde

open GW2KM2 Restart

/-! ### Killed paths that agree before a time -/

/-- Two killed paths agree up to time `t`: the same liveness and the same values at every live time `r ≤ t`. -/
def AgreeUpTo (t : ℝ≥0) (e e' : (ℝ≥0 → ℝ) × ℝ≥0∞) : Prop :=
  ∀ r : ℝ≥0, r ≤ t → (((r : ℝ≥0∞) < e.2 ↔ (r : ℝ≥0∞) < e'.2) ∧ ((r : ℝ≥0∞) < e.2 → e.1 r = e'.1 r))

/-- Every event of `pathKilledSigma t` contains both or neither of two killed paths that agree up to `t`. -/
theorem mem_iff_of_agreeUpTo {t : ℝ≥0} {e e' : (ℝ≥0 → ℝ) × ℝ≥0∞} (h : AgreeUpTo t e e')
    {S : Set ((ℝ≥0 → ℝ) × ℝ≥0∞)} (hS : MeasurableSet[pathKilledSigma t] S) : e ∈ S ↔ e' ∈ S := by
  induction hS with
  | basic S hS =>
    obtain ⟨r, hrt, A, -, rfl⟩ := hS
    obtain ⟨h1, h2⟩ := h r hrt
    simp only [mem_ofPred_eq]
    constructor
    · rintro ⟨hr, hA⟩
      exact ⟨h1.1 hr, (h2 hr) ▸ hA⟩
    · rintro ⟨hr, hA⟩
      exact ⟨h1.2 hr, (h2 (h1.2 hr)).symm ▸ hA⟩
  | empty => simp only [mem_empty_iff_false]
  | compl S _ ih => simp only [mem_compl_iff, ih]
  | iUnion f _ ih => simp only [mem_iUnion, ih]

/-- **A stopping rule of the killed path takes the same value on two killed paths** that agree up to every time
before `T`, provided its value on the first path is below `T` (or `T = ⊤`). -/
theorem stopRule_eq_of_agree {τ₀ : (ℝ≥0 → ℝ) × ℝ≥0∞ → ℝ≥0∞}
    (hτ₀ : ∀ t : ℝ≥0, MeasurableSet[pathKilledSigma t] {e | τ₀ e ≤ (t : ℝ≥0∞)})
    {e e' : (ℝ≥0 → ℝ) × ℝ≥0∞} {T : ℝ≥0∞} (h : ∀ t : ℝ≥0, (t : ℝ≥0∞) < T → AgreeUpTo t e e')
    (hT : τ₀ e < T ∨ T = ⊤) : τ₀ e' = τ₀ e := by
  have hiff : ∀ t : ℝ≥0, (t : ℝ≥0∞) < T → (τ₀ e ≤ t ↔ τ₀ e' ≤ t) := fun t ht =>
    mem_iff_of_agreeUpTo (h t ht) (hτ₀ t)
  have key : τ₀ e < T → τ₀ e' = τ₀ e := by
    intro hlt
    have hs : ((τ₀ e).toNNReal : ℝ≥0∞) = τ₀ e := ENNReal.coe_toNNReal (ne_top_of_lt hlt)
    have h1 : τ₀ e' ≤ τ₀ e := by
      have := (hiff (τ₀ e).toNNReal (hs ▸ hlt)).1 hs.ge
      rwa [hs] at this
    refine le_antisymm h1 (not_lt.1 fun hlt' => ?_)
    have hs' : ((τ₀ e').toNNReal : ℝ≥0∞) = τ₀ e' := ENNReal.coe_toNNReal (ne_top_of_lt hlt')
    have h2 := (hiff (τ₀ e').toNNReal (hs' ▸ hlt'.trans hlt)).2 hs'.ge
    rw [hs'] at h2
    exact absurd (h2.trans_lt hlt') (lt_irrefl _)
  rcases hT with hT | hT
  · exact key hT
  · by_cases hfin : τ₀ e = ⊤
    · rw [hfin]
      by_contra hne
      have hs' : ((τ₀ e').toNNReal : ℝ≥0∞) = τ₀ e' := ENNReal.coe_toNNReal hne
      have h2 := (hiff (τ₀ e').toNNReal (hT ▸ ENNReal.coe_lt_top)).2 hs'.ge
      rw [hfin] at h2
      exact absurd h2 (not_le.2 ENNReal.coe_lt_top)
    · exact key (hT ▸ lt_top_iff_ne_top.2 hfin)

/-! ### Almost sure modifications in the usual augmentation -/

/-- A measurable set that is almost surely equal to an event of the usual augmentation is an event of it. -/
theorem measurableSet_usualAugmentation_of_ae_iff {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ν : Measure Ω} {t : ℝ≥0} {S S' : Set Ω} (hS : MeasurableSet S)
    (hS' : MeasurableSet[usualAugmentation 𝓕 ν t] S') (h : ∀ᵐ ω ∂ν, ω ∈ S ↔ ω ∈ S') :
    MeasurableSet[usualAugmentation 𝓕 ν t] S := by
  set N := toMeasurable ν {ω | ¬(ω ∈ S ↔ ω ∈ S')} with hNdef
  have hN0 : ν N = 0 := by rw [hNdef, measure_toMeasurable]; exact ae_iff.1 h
  have hNm : MeasurableSet N := measurableSet_toMeasurable _ _
  have hNa := Ito.measurableSet_usualAugmentation_of_null (𝓕 := 𝓕) hNm hN0 t
  have hSN := Ito.measurableSet_usualAugmentation_of_null (𝓕 := 𝓕) (hS.inter hNm)
    (measure_mono_null inter_subset_right hN0) t
  have e : S = (S' ∩ Nᶜ) ∪ (S ∩ N) := by
    ext ω
    by_cases hω : ω ∈ N
    · simp only [hω, mem_union, mem_inter_iff, mem_compl_iff, not_true_eq_false, and_false, and_true, false_or]
    · have hiff : ω ∈ S ↔ ω ∈ S' := by
        by_contra hc
        exact hω (subset_toMeasurable _ _ hc)
      simp only [hω, hiff, mem_union, mem_inter_iff, mem_compl_iff, not_false_eq_true, and_true, and_false, or_false]
  rw [e]
  exact (hS'.inter hNa.compl).union hSN

/-! ### The stopped SDE from the stopped driver match -/

/-- The force points of the field-determined coupling, killed at its lifetime (their initial values after it). -/
def killMark {Ω : Type*} {n : ℕ} (x : Fin n → ℝ) (V : Fin n → ℝ≥0 → Ω → ℝ) (L : Ω → ℝ≥0∞) :
    Fin n → ℝ≥0 → Ω → ℝ :=
  fun i t ω => if (t : ℝ≥0∞) < L ω then V i t ω else x i

/-- **The stopped local dynamics of a physical driver from its stopped driver match** (conditional helper: the
match, the conditional GFF and the protected stopping rule are hypotheses; the dynamics are constructed). -/
theorem exists_isStopped_of_stopDrvMatch (h12p : Exist.Staged.Theorem12ParamStatement.{u})
    (h13 : Exist.Theorem13Statement.{u}) {κ : ℝ} (hκ : 0 < κ)
    {F : BoundaryWord × DistOn upperHalfPlaneOpens → Sec2.Assembly.PCode × ℝ≥0∞}
    (hF : Restart.IsCanonicalDriverCode κ 0 F) {c₀ : BoundaryWord} (hc₀ : c₀.IsSorted)
    {Ω : Type u} [mΩ : MeasurableSpace Ω] {ν : Measure Ω} [IsProbabilityMeasure ν]
    {X : Ω → DistOn upperHalfPlaneOpens} (hX : IsGFFWithBoundaryData ν X c₀.fn c₀.jumps)
    {R : ℝ≥0 → Ω → ℝ} (hRm : ∀ t, Measurable (R t)) (hRc : ∀ ω, Continuous fun t => R t ω)
    (hR0 : ∀ ω, R 0 ω = 0) {V : Ω → ℝ≥0∞}
    (hmatch : ∀ᵐ ω ∂ν, Supp8.GB6.RelDrv.IsStopDrvMatch (F (c₀, X ω)) (fun t => R t ω) (V ω))
    (τ₀ : (ℝ≥0 → ℝ) × ℝ≥0∞ → ℝ≥0∞)
    (hτ₀ : ∀ t : ℝ≥0, MeasurableSet[pathKilledSigma t] {e | τ₀ e ≤ (t : ℝ≥0∞)})
    {τ : Ω → ℝ≥0∞} (hτm : Measurable τ) (hτ : ∀ᵐ ω ∂ν, τ ω = τ₀ ((fun t => R t ω), V ω))
    (hτV : ∀ᵐ ω ∂ν, τ ω ≤ V ω) (hprot : ∀ᵐ ω ∂ν, τ ω ≠ ⊤ → τ ω < V ω)
    {nL nR : ℕ} {xL ρL : Fin nL → ℝ} {xR ρR : Fin nR → ℝ}
    (hw : Restart.FCDet.IsFlowType κ 0 c₀ xL xR ρL ρR) :
    ∃ d : GW2JDetR11.LocalDynamics Ω nL nR, d.W = R ∧ d.stop = τ ∧ d.IsStopped ν κ xL ρL xR ρR := by
  obtain ⟨eL, eR, hxL, hxR, hρL, hρR⟩ := hw
  subst eL eR
  simp only [Fin.cast_eq_self] at hxL hxR hρL hρR
  replace hxL : xL = _ := hxL
  replace hxR : xR = _ := hxR
  replace hρL : ρL = _ := hρL
  replace hρR : ρR = _ := hρR
  subst hxL hxR hρL hρR
  -- the field-determined driver of Theorem 1.2 drives an optional hull coupling of `X`
  set E : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞ := fun ω => BRLeaf.cfDrv h12p hκ c₀ (X ω) with hEdef
  have hEm : Measurable E := (BRLeaf.measurable_cfDrv h12p hκ c₀).comp hX.1
  have hgff := Exist.isGFFWithBoundaryData_flowField hκ c₀.isPiecewiseConstantBoundaryData 0 0 hX
  have hff : (fun ω => Exist.flowField 0 (0 * chiC κ) (X ω)) = X := funext fun ω => by
    rw [zero_mul]; exact Sec5.GlueCond.flowField_zero_zero _
  rw [hff] at hgff
  obtain ⟨𝓕, VL, VR, B, hCpl⟩ := Exist.Staged.isOptionalHullCoupling_drv h12p h13 hκ
    (Theorem15.isOrderedForceWord_flowLine c₀.fn c₀.jumps 0) hgff hEm (Eventually.of_forall fun _ => rfl)
  have hEv := hCpl.1
  -- the stop as a rule of the field-determined killed driver: a stopping time of `𝓕`
  set τ' : Ω → ℝ≥0∞ := fun ω => τ₀ (E ω) with hτ'def
  have hτ'st : ∀ t : ℝ≥0, MeasurableSet[𝓕 t] {ω | τ' ω ≤ (t : ℝ≥0∞)} := fun t =>
    GW2JDetR12.killedDriverSigma_le_filtration ⟨𝓕, fun t ω => (E ω).1 t, VL, VR, B, fun ω => (E ω).2⟩
      hEv.isSLEEvolutionUpTo t _ (measurableSet_killedDriverSigma_preimage E t (hτ₀ t))
  -- the almost sure identifications
  have hcmp := GW4Rel.ae_cfDrv_eq_of_match h12p h13 hκ hF hc₀ hX hRc hmatch
  have hkey : ∀ᵐ ω ∂ν, V ω ≤ (E ω).2 ∧ (∀ t : ℝ≥0, (t : ℝ≥0∞) < V ω → (E ω).1 t = R t ω) ∧
      τ ω ≤ V ω ∧ (τ ω ≠ ⊤ → τ ω < V ω) ∧ τ ω = τ' ω := by
    filter_upwards [hcmp, hτ, hτV, hprot] with ω h1 h2 h3 h4
    refine ⟨h1.1, h1.2, h3, h4, ?_⟩
    rw [h2]
    refine (stopRule_eq_of_agree hτ₀ (T := V ω) (fun t ht r hr => ?_) ?_).symm
    · have hrV : (r : ℝ≥0∞) < V ω := lt_of_le_of_lt (by exact_mod_cast hr) ht
      exact ⟨⟨fun _ => lt_of_lt_of_le hrV h1.1, fun _ => hrV⟩, fun _ => (h1.2 r hrV).symm⟩
    · rw [← h2]
      by_cases hτt : τ ω = ⊤
      · right
        rw [hτt] at h3
        exact top_le_iff.1 h3
      · exact Or.inl (h4 hτt)
  have hpath := hEv.2.2.2.2
  set 𝓖 := usualAugmentation 𝓕 ν with h𝓖def
  have h𝓕𝓖 : ∀ t, 𝓕 t ≤ 𝓖 t := fun t => Ito.le_usualAugmentation 𝓕 ν t
  have hτlt : ∀ t : ℝ≥0, MeasurableSet {ω | (t : ℝ≥0∞) < τ ω} := fun t => measurableSet_lt measurable_const hτm
  have hE2 : ∀ t : ℝ≥0, MeasurableSet {ω | (t : ℝ≥0∞) < (E ω).2} := fun t =>
    measurableSet_lt measurable_const (measurable_snd.comp hEm)
  -- adaptedness of a killed force point
  have hadK : ∀ {n : ℕ} (x : Fin n → ℝ) (Vf : Fin n → ℝ≥0 → Ω → ℝ),
      (∀ i, AdaptedBefore 𝓕 (fun ω => (E ω).2) (Vf i)) →
      ∀ i, AdaptedBefore 𝓖 τ (killMark x Vf (fun ω => (E ω).2) i) := by
    intro n x Vf hVf i t A hA
    have hS : MeasurableSet {ω | (t : ℝ≥0∞) < τ ω ∧ killMark x Vf (fun ω => (E ω).2) i t ω ∈ A} := by
      have e : {ω | (t : ℝ≥0∞) < τ ω ∧ killMark x Vf (fun ω => (E ω).2) i t ω ∈ A} =
          {ω | (t : ℝ≥0∞) < τ ω} ∩ ({ω | (t : ℝ≥0∞) < (E ω).2 ∧ Vf i t ω ∈ A} ∪
            ({ω | (t : ℝ≥0∞) < (E ω).2}ᶜ ∩ {_ω | x i ∈ A})) := by
        ext ω
        by_cases h : (t : ℝ≥0∞) < (E ω).2 <;>
          simp only [killMark, h, ↓reduceIte, mem_ofPred_eq, mem_inter_iff, mem_union, mem_compl_iff,
            not_true_eq_false, not_false_eq_true, true_and, false_and, or_false, false_or]
      rw [e]
      exact (hτlt t).inter ((𝓕.le t _ (hVf i t A hA)).union ((hE2 t).compl.inter (MeasurableSet.const _)))
    refine measurableSet_usualAugmentation_of_ae_iff hS
      (h𝓕𝓖 t _ ((hτ'st t).compl.inter (hVf i t A hA))) ?_
    filter_upwards [hkey] with ω hω
    obtain ⟨h1, -, h3, -, h5⟩ := hω
    rw [h5] at h3
    simp only [mem_ofPred_eq, mem_inter_iff, mem_compl_iff, not_le, h5]
    constructor
    · rintro ⟨ht, hA'⟩
      have htE : (t : ℝ≥0∞) < (E ω).2 := lt_of_lt_of_le ht (h3.trans h1)
      simp only [killMark, htE, ↓reduceIte] at hA'
      exact ⟨ht, htE, hA'⟩
    · rintro ⟨ht, htE, hA'⟩
      simp only [killMark, htE, ↓reduceIte]
      exact ⟨ht, hA'⟩
  set VLk := killMark (flowLineXL c₀.fn c₀.jumps 0) VL (fun ω => (E ω).2) with hVLk
  set VRk := killMark (flowLineXR c₀.fn c₀.jumps 0) VR (fun ω => (E ω).2) with hVRk
  -- adaptedness of the physical driver before the physical stop
  have hadW : AdaptedBefore 𝓖 τ R := by
    intro t A hA
    have hS : MeasurableSet {ω | (t : ℝ≥0∞) < τ ω ∧ R t ω ∈ A} := (hτlt t).inter (hRm t hA)
    refine measurableSet_usualAugmentation_of_ae_iff hS
      (h𝓕𝓖 t _ ((hτ'st t).compl.inter (hEv.2.1 t A hA))) ?_
    filter_upwards [hkey] with ω hω
    obtain ⟨h1, h2, h3, -, h5⟩ := hω
    simp only [mem_ofPred_eq, mem_inter_iff, mem_compl_iff, not_le, ← h5]
    constructor
    · rintro ⟨ht, hA'⟩
      have htV : (t : ℝ≥0∞) < V ω := lt_of_lt_of_le ht h3
      refine ⟨ht, lt_of_lt_of_le htV h1, ?_⟩
      rw [h2 t htV]
      exact hA'
    · rintro ⟨ht, -, hA'⟩
      have htV : (t : ℝ≥0∞) < V ω := lt_of_lt_of_le ht h3
      refine ⟨ht, ?_⟩
      rw [← h2 t htV]
      exact hA'
  -- the local evolution with the physical driver, the killed force points and the physical stop
  have hevo : Sec2.IsSLEEvolutionUpTo κ (flowLineXL c₀.fn c₀.jumps 0) (flowLineXR c₀.fn c₀.jumps 0)
      (flowLineRhoL κ c₀.fn c₀.jumps 0 0) (flowLineRhoR κ c₀.fn c₀.jumps 0 0) ν 𝓖 R VLk VRk B τ := by
    refine ⟨Ito.isFilteredBrownianReal_usualAugmentation hEv.1, hadW, hadK _ VL hEv.2.2.1,
      hadK _ VR hEv.2.2.2.1, ?_⟩
    filter_upwards [hkey, hpath] with ω hω hp
    obtain ⟨h1, h2, h3, -, -⟩ := hω
    have hup := (hp.isSLEPathUpTo le_rfl).mono (h3.trans h1)
    have hup0 := hp.isSLEPathUpTo le_rfl
    refine Sec2.Assembly2.isSLEPathUpTo_congr hup ?_ ?_ ?_ ?_ ?_ ?_ (fun _ _ => rfl)
    · rw [hR0]
      exact hup0.w_zero.symm
    · intro i
      by_cases h0 : ((0 : ℝ≥0) : ℝ≥0∞) < (E ω).2
      · simp only [hVLk, killMark, h0, ↓reduceIte]
      · simp only [hVLk, killMark, h0, ↓reduceIte]
        exact (hup0.vL_zero i).symm
    · intro j
      by_cases h0 : ((0 : ℝ≥0) : ℝ≥0∞) < (E ω).2
      · simp only [hVRk, killMark, h0, ↓reduceIte]
      · simp only [hVRk, killMark, h0, ↓reduceIte]
        exact (hup0.vR_zero j).symm
    · intro t ht
      exact (h2 t (lt_of_lt_of_le ht h3)).symm
    · intro t ht i
      simp only [hVLk, killMark, lt_of_lt_of_le ht (h3.trans h1), ↓reduceIte]
    · intro t ht j
      simp only [hVRk, killMark, lt_of_lt_of_le ht (h3.trans h1), ↓reduceIte]
  refine ⟨⟨𝓖, R, VLk, VRk, B, τ⟩, rfl, rfl, hevo, ?_⟩
  filter_upwards [hkey, hpath] with ω hω hp t ht
  obtain ⟨h1, -, -, h4, -⟩ := hω
  have hτfin : τ ω ≠ ⊤ := by
    change (t : ℝ≥0∞) = τ ω at ht
    rw [← ht]
    exact ENNReal.coe_ne_top
  have htE : (t : ℝ≥0∞) < (E ω).2 := by
    change (t : ℝ≥0∞) = τ ω at ht
    rw [ht]
    exact lt_of_lt_of_le (h4 hτfin) h1
  have hup := hp.isSLEPathUpTo le_rfl
  have hsub : Iic t ⊆ {v : ℝ≥0 | (v : ℝ≥0∞) < (E ω).2} := fun v hv =>
    lt_of_le_of_lt (ENNReal.coe_le_coe.2 hv) htE
  show ContinuousOn (fun v => (R v ω, fun i => VLk i v ω, fun j => VRk j v ω)) (Iic t)
  refine (hRc ω).continuousOn.prodMk ((continuousOn_pi.2 fun i => ?_).prodMk (continuousOn_pi.2 fun j => ?_))
  · refine ((hup.continuousOn_vL i).mono hsub).congr fun v hv => ?_
    have hv' : (v : ℝ≥0∞) < (E ω).2 := hsub hv
    simp only [hVLk, killMark, hv', ↓reduceIte]
  · refine ((hup.continuousOn_vR j).mono hsub).congr fun v hv => ?_
    have hv' : (v : ℝ≥0∞) < (E ω).2 := hsub hv
    simp only [hVRk, killMark, hv', ↓reduceIte]

end InteractingSLE.Theorem14.GW2Sde
