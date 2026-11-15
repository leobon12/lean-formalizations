/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketStopActive
import InteractingSLE.Spec.Sec7.PocketUnionPtGeom
import InteractingSLE.Spec.Sec7.PocketTraversalMeas
import InteractingSLE.Spec.Sec7.PocketStopFieldChart
import InteractingSLE.Spec.Coupling.SafeCompact
import InteractingSLE.Spec.Coupling.MartMeans2Chart
import InteractingSLE.Spec.Restart.DomainMarkov

/-!
# Theorem 1.2's R.7: the explored pocket set is measurable for the walls and the traversal's prefix

Packet PROVE-PHASECONT. To compare the pocket's conditional laws at two relative capacity times `q ≤ r`, the germ
of the earlier canonical set `K_q = activeCompl q` is retained in the marks of the later union law
(`Lemma725RefMarks.isHistoryAvoidanceLocal_sup_germSigma`, "the germ of a smaller marked local set can be added to the
marks of a larger one", R69). That lemma needs `K_q` to be measurable for the later history
`𝓦 ∨ σ(A ∩ prefix events up to r)`. This file proves it (`measurable_activeCompl_locPrefixSigma`).

On the live event, `K_q = ℍ ∖ (C ∩ ψ⁻¹(ℍ ∖ K^{rel}_q))` (`K^{rel}_q` the relative Loewner hull, `ψ` the pocket
coordinate). For an open `U ⊆ ℍ`, `U` avoids `K_q` iff every rational closed ball `B ⊆ U` lies in `C` and `ψ(B)`
avoids `K^{rel}_q`; the latter is the safe condition of `ψ(B)` at some positive level, which is read on a countable
dense family of points (`Coupling.IsSafeAt.of_dense`) through the safe events of single points (adapted to the prefix
filtration, `Coupling.measurableSet_isSafeAt`) and the walls-measurable values `ψ ω z`.

## Main results

* `inv_image_diff_eq`: the chart preimage of `ℍ ∖ X` is `C ∩ ψ⁻¹(X)ᶜ`;
* `measurableSet_safe_point`: the safe event of one point is a prefix event;
* `measurableSet_subset_pocket_avoid`: the event that a compact set lies in `C` with image avoiding the hull;
* **`measurable_activeCompl_locPrefixSigma`**, **`measurable_activeCompl_locPrefixSigma_of_le`**.

Ruling R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any result taking
them as hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open QuantumZipper (H fwdHull IsForwardSol)
open SupercriticalConformalCovariance (IsConformalBijection)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PhaseCont

open PocketStop PocketTraversal PocketAdapt Lemma71C PocketCoupling PocketUnionPt Coupling Ito

/-! ### The chart preimage of a hull complement -/

theorem inv_image_diff_eq {c : Chart} (hc : c.IsConformal) {C : Set ℂ} (hdom : (c.dom : Set ℂ) = C)
    {ψ : ℂ → ℂ} (hfwd : EqOn c.1 ψ C) (hψ : IsConformalBijection ψ C H) (X : Set ℂ) :
    c.2.1 '' (H \ X) = {z | z ∈ C ∧ ψ z ∉ X} := by
  refine inv_image_eq_of_image hc hdom hfwd hψ.2.injOn (fun z hz => hz.1) ?_
  ext w
  constructor
  · rintro ⟨z, ⟨hzC, hzX⟩, rfl⟩
    exact ⟨hψ.2.mapsTo hzC, hzX⟩
  · rintro ⟨hwH, hwX⟩
    obtain ⟨z, hzC, rfl⟩ := hψ.2.surjOn hwH
    exact ⟨z, ⟨hzC, hwX⟩, rfl⟩

/-! ### Events of the subtype read on the ambient space -/

theorem measurableSet_of_comap_val {Ω' : Type*} {ℳ : MeasurableSpace Ω'} {A : Set Ω'} (hA : MeasurableSet[ℳ] A)
    {p : Ω' → Prop} (hp : MeasurableSet[MeasurableSpace.comap (Subtype.val : A → Ω') ℳ] {ω : A | p ω}) :
    MeasurableSet[ℳ] {ω | ω ∈ A ∧ p ω} := by
  obtain ⟨S, hS, hSe⟩ := hp
  have e : {ω | ω ∈ A ∧ p ω} = A ∩ S := by
    ext ω
    constructor
    · rintro ⟨hω, hp⟩
      refine ⟨hω, ?_⟩
      have : (⟨ω, hω⟩ : A) ∈ Subtype.val ⁻¹' S := by rw [hSe]; exact hp
      exact this
    · rintro ⟨hω, hωS⟩
      refine ⟨hω, ?_⟩
      have : (⟨ω, hω⟩ : A) ∈ Subtype.val ⁻¹' S := hωS
      rw [hSe] at this
      exact this
  rw [e]
  exact hA.inter hS

variable {Ω : Type*}

theorem locPrefixSigma_mono (𝓦 : MeasurableSpace Ω) (A : Set Ω) (γ : Ω → ℝ → ℂ) {q r : ℝ≥0} (hqr : q ≤ r) :
    locPrefixSigma 𝓦 A γ q ≤ locPrefixSigma 𝓦 A γ r := by
  refine sup_le_sup_left (MeasurableSpace.generateFrom_mono ?_) _
  rintro E ⟨s, hs, n, k, rfl⟩
  exact ⟨s, hs.trans hqr, n, k, rfl⟩

/-! ### The safe event of one point -/

section Safe

variable {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]

/-- **The safe event of one point is an event of the walls and the traversal's prefix.** -/
theorem measurableSet_safe_point (h𝓦 : 𝓦 ≤ mΩ) {A : Set Ω} (hA : MeasurableSet[𝓦] A) {γ : Ω → ℝ → ℂ}
    (hγ : ∀ ω ∈ A, IsDrivenCurve (γ ω)) (hγm : ∀ u, 0 ≤ u → Measurable fun ω : A => γ ω u) {y : ℂ} (hy : y ∈ H)
    (δ : ℝ) (q : ℝ≥0) :
    MeasurableSet[locPrefixSigma 𝓦 A γ q]
      {ω | ω ∈ A ∧ IsSafeAt {y} δ q q (capLife (γ ω)) (fun t => segDriver (γ ω) t) q} := by
  have h𝓔 : MeasurableSpace.comap Subtype.val 𝓦 ≤ (inferInstance : MeasurableSpace A) :=
    MeasurableSpace.comap_mono h𝓦
  have hdrive : ∀ ω : A, IsDrivenCurve (γ ω) := fun ω => hγ ω ω.2
  have hm : ∀ r n k, MeasurableSet (prefixEvent (fun ω : A => γ ω) r n k) := fun r n k =>
    PocketMeas.measurableSet_prefixEvent hdrive hγm r n k
  set 𝓗 := prefixFilt (MeasurableSpace.comap Subtype.val 𝓦) h𝓔 (fun ω : A => γ ω) hm with h𝓗def
  have hpre : IsPrefixAdapted 𝓗 (fun ω : A => γ ω) := isPrefixAdapted_prefixFilt h𝓔 hm
  have hWa := adaptedBefore_segDriver_of_isDrivenCurve hdrive hpre
  have hS := measurableSet_isSafeAt (G := univ) hWa (fun ω _ => (hdrive ω).segDriver_spec.2.1) MeasurableSet.univ
    (countable_singleton y) (singleton_subset_iff.2 hy) (σ₀ := fun _ => q) (isStoppingTime_const 𝓗 q) δ q q
  have h𝓗q : 𝓗 q = MeasurableSpace.comap Subtype.val (locPrefixSigma 𝓦 A γ q) := by
    rw [comap_locPrefixSigma]; rfl
  rw [h𝓗q] at hS
  refine measurableSet_of_comap_val (le_sup_left (b := MeasurableSpace.generateFrom _) _ hA) ?_
  simpa only [mem_univ, true_and] using hS

end Safe

/-! ### A compact set inside the pocket whose image avoids the hull -/

section Avoid

variable {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]

/-- **The event that a compact set lies in the pocket and its image avoids the relative hull at `q`** (on the live
event) is an event of the walls and the traversal's prefix up to `q`. -/
theorem measurableSet_compact_avoid (h𝓦 : 𝓦 ≤ mΩ) {A : Set Ω} (hA : MeasurableSet[𝓦] A) {γ : Ω → ℝ → ℂ}
    (hγ : ∀ ω ∈ A, IsDrivenCurve (γ ω)) (hγm : ∀ u, 0 ≤ u → Measurable fun ω : A => γ ω u)
    {C : Ω → Set ℂ} (hCo : ∀ ω ∈ A, IsOpen (C ω)) (hCH : ∀ ω ∈ A, C ω ⊆ H) {ψ : Ω → ℂ → ℂ}
    (hψ : ∀ ω ∈ A, IsConformalBijection (ψ ω) (C ω) H) (hCm : ∀ z, MeasurableSet[𝓦] {ω | ω ∈ A ∧ z ∈ C ω})
    (hψm : ∀ z, Measurable[𝓦] ({ω | ω ∈ A ∧ z ∈ C ω}.indicator fun ω => ψ ω z))
    (hCin : ∀ U : Set ℂ, IsOpen U → U ⊆ H → MeasurableSet[𝓦] {ω | ω ∈ A ∧ U ⊆ C ω})
    {K : Set ℂ} (hK : IsCompact K) (q : ℝ≥0) :
    MeasurableSet[locPrefixSigma 𝓦 A γ q] {ω | ω ∈ A ∧ (q : ℝ≥0∞) < capLife (γ ω) ∧ K ⊆ C ω ∧
      Disjoint (ψ ω '' K) (fwdHull (fun s : ℝ => segDriver (γ ω) s.toNNReal) q)} := by
  classical
  have h𝓦ℳ : 𝓦 ≤ locPrefixSigma 𝓦 A γ q := le_sup_left
  -- `K ⊆ C` through open thickenings
  have hKC : MeasurableSet[𝓦] {ω | ω ∈ A ∧ K ⊆ C ω} := by
    have e : {ω | ω ∈ A ∧ K ⊆ C ω} = ⋃ k : ℕ, {ω | ω ∈ A ∧ thickening (1 / ((k : ℝ) + 1)) K ⊆ C ω} := by
      ext ω
      simp only [mem_ofPred_eq, mem_iUnion]
      constructor
      · rintro ⟨hω, hKω⟩
        obtain ⟨δ, hδ, hsub⟩ := hK.exists_thickening_subset_open (hCo ω hω) hKω
        obtain ⟨k, hk⟩ := exists_nat_one_div_lt hδ
        exact ⟨k, hω, (thickening_mono hk.le K).trans hsub⟩
      · rintro ⟨k, hω, hsub⟩
        exact ⟨hω, (self_subset_thickening (by positivity) K).trans hsub⟩
    rw [e]
    refine MeasurableSet.iUnion fun k => ?_
    by_cases hTH : thickening (1 / ((k : ℝ) + 1)) K ⊆ H
    · exact hCin _ isOpen_thickening hTH
    · have : {ω | ω ∈ A ∧ thickening (1 / ((k : ℝ) + 1)) K ⊆ C ω} = ∅ := by
        ext ω
        simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
        exact fun hω hsub => hTH (hsub.trans (hCH ω hω))
      rw [this]; exact @MeasurableSet.empty _ 𝓦
  -- countable dense subsets of `K` and of `ℍ`
  obtain ⟨Kd, hKdK, hKdc, hKdd⟩ := (TopologicalSpace.IsSeparable.of_separableSpace K).exists_countable_dense_subset
  obtain ⟨Yd, hYdH, hYdc, hYdd⟩ := (TopologicalSpace.IsSeparable.of_separableSpace H).exists_countable_dense_subset
  set Ev : ℕ → ℂ → ℂ → Set Ω := fun k z y => {ω | ω ∈ A ∧ z ∈ C ω ∧ ‖ψ ω z - y‖ < 1 / ((k : ℝ) + 1)} with hEv
  set Sf : ℕ → ℂ → Set Ω := fun m y => {ω | ω ∈ A ∧
    IsSafeAt {y} (1 / ((m : ℝ) + 1)) q q (capLife (γ ω)) (fun t => segDriver (γ ω) t) q} with hSf
  have hEvm : ∀ k z y, MeasurableSet[𝓦] (Ev k z y) := by
    intro k z y
    have e : Ev k z y = {ω | ω ∈ A ∧ z ∈ C ω} ∩
        {ω | ‖({ω | ω ∈ A ∧ z ∈ C ω}.indicator fun ω => ψ ω z) ω - y‖ < 1 / ((k : ℝ) + 1)} := by
      ext ω
      simp only [hEv, mem_ofPred_eq, mem_inter_iff]
      constructor
      · rintro ⟨hω, hz, hlt⟩
        refine ⟨⟨hω, hz⟩, ?_⟩
        rwa [indicator_of_mem (show ω ∈ {ω | ω ∈ A ∧ z ∈ C ω} from ⟨hω, hz⟩)]
      · rintro ⟨⟨hω, hz⟩, hlt⟩
        rw [indicator_of_mem (show ω ∈ {ω | ω ∈ A ∧ z ∈ C ω} from ⟨hω, hz⟩)] at hlt
        exact ⟨hω, hz, hlt⟩
    rw [e]
    exact (hCm z).inter (((continuous_norm.comp (continuous_sub_right y)).measurable.comp (hψm z))
      measurableSet_Iio)
  have hSfm : ∀ m, ∀ y ∈ Yd, MeasurableSet[locPrefixSigma 𝓦 A γ q] (Sf m y) := fun m y hy =>
    measurableSet_safe_point h𝓦 hA hγ hγm (hYdH hy) _ q
  have hL : MeasurableSet[locPrefixSigma 𝓦 A γ q] {ω | ω ∈ A ∧ (q : ℝ≥0∞) < capLife (γ ω)} :=
    measurableSet_live A γ q
  have e : {ω | ω ∈ A ∧ (q : ℝ≥0∞) < capLife (γ ω) ∧ K ⊆ C ω ∧
      Disjoint (ψ ω '' K) (fwdHull (fun s : ℝ => segDriver (γ ω) s.toNNReal) q)} =
      {ω | ω ∈ A ∧ (q : ℝ≥0∞) < capLife (γ ω)} ∩ {ω | ω ∈ A ∧ K ⊆ C ω} ∩
        ⋃ m : ℕ, ⋂ k : ℕ, ⋂ z ∈ Kd, ⋃ y ∈ Yd, Ev k z y ∩ Sf m y := by
    ext ω
    simp only [mem_ofPred_eq, mem_inter_iff, mem_iUnion, mem_iInter, exists_prop]
    have key : ∀ (hω : ω ∈ A) (hlive : (q : ℝ≥0∞) < capLife (γ ω)) (hKω : K ⊆ C ω),
        Disjoint (ψ ω '' K) (fwdHull (fun s : ℝ => segDriver (γ ω) s.toNNReal) q) ↔
          ∃ m : ℕ, ∀ k : ℕ, ∀ z ∈ Kd, ∃ y ∈ Yd, ω ∈ Ev k z y ∧ ω ∈ Sf m y := by
      intro hω hlive hKω
      have hwc : ContinuousOn (fun t => segDriver (γ ω) t) {t : ℝ≥0 | (t : ℝ≥0∞) < capLife (γ ω)} :=
        (hγ ω hω).segDriver_spec.2.1
      have hw0 : segDriver (γ ω) 0 = 0 := (hγ ω hω).segDriver_spec.1
      have hψc : ContinuousOn (ψ ω) (C ω) := (hψ ω hω).1.continuousOn
      have hψH : ∀ z ∈ C ω, ψ ω z ∈ H := fun z hz => (hψ ω hω).2.mapsTo hz
      constructor
      · intro hdis
        have hK' : IsCompact (ψ ω '' K) := hK.image_of_continuousOn (hψc.mono hKω)
        have hsub : ψ ω '' K ⊆ H \ fwdHull (rpath fun t => segDriver (γ ω) t) q := by
          rintro _ ⟨z, hz, rfl⟩
          exact ⟨hψH z (hKω hz), Set.disjoint_left.1 hdis (mem_image_of_mem _ hz)⟩
        obtain ⟨ρ, hρ, hρsub⟩ := hK'.exists_cthickening_subset_open
          (Coupling.MartMeans2.isOpen_H_diff_fwdHull_rpath hwc hlive) hsub
        have hK₁ : IsCompact (cthickening ρ (ψ ω '' K)) := hK'.cthickening
        obtain ⟨δ, hδ, hsafe⟩ := Restart.DomainMarkov.exists_isSafeAt_self hwc hw0 hK₁
          (fun z hz => (hρsub hz).1) hlive fun z hz => exists_isForwardSol_of_mem q.coe_nonneg (hρsub hz)
        obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ
        refine ⟨m, fun k z hz => ?_⟩
        have hzC : z ∈ C ω := hKω (hKdK hz)
        have hε : 0 < min ρ (1 / ((k : ℝ) + 1)) := lt_min hρ (by positivity)
        obtain ⟨y, hyY, hy⟩ := Metric.mem_closure_iff.1 (hYdd (hψH z hzC)) _ hε
        have hyK₁ : y ∈ cthickening ρ (ψ ω '' K) :=
          mem_cthickening_of_dist_le y (ψ ω z) ρ _ (mem_image_of_mem _ (hKdK hz))
            (by rw [dist_comm]; exact hy.le.trans (min_le_left _ _))
        refine ⟨y, hyY, ⟨hω, hzC, ?_⟩, hω, ?_⟩
        · rw [← dist_eq_norm]; exact hy.trans_le (min_le_right _ _)
        · exact (hsafe.subset (singleton_subset_iff.2 hyK₁)).mono hm.le le_rfl le_rfl
      · rintro ⟨m, hm⟩
        set Y : Set ℂ := {y | y ∈ Yd ∧
          IsSafeAt {y} (1 / ((m : ℝ) + 1)) q q (capLife (γ ω)) (fun t => segDriver (γ ω) t) q} with hYdef
        have hY : IsSafeAt Y (1 / ((m : ℝ) + 1)) q q (capLife (γ ω)) (fun t => segDriver (γ ω) t) q :=
          ⟨hlive, le_rfl, le_rfl, fun y hy => hy.2.2.2.2 y (mem_singleton y)⟩
        have hdense : ψ ω '' K ⊆ closure Y := by
          have hKd' : ψ ω '' Kd ⊆ closure Y := by
            rintro _ ⟨z, hz, rfl⟩
            refine Metric.mem_closure_iff.2 fun ε hε => ?_
            obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
            obtain ⟨y, hyY, ⟨-, -, hlt⟩, -, hys⟩ := hm k z hz
            refine ⟨y, ⟨hyY, hys⟩, ?_⟩
            rw [dist_eq_norm]; exact hlt.trans hk
          rintro _ ⟨z₀, hz₀, rfl⟩
          have hcw : ContinuousWithinAt (ψ ω) Kd z₀ :=
            (hψc.continuousWithinAt (hKω hz₀)).mono fun z hz => hKω (hKdK hz)
          exact closure_minimal hKd' isClosed_closure (hcw.mem_closure_image (hKdd hz₀))
        have hK₂H : ψ ω '' K ∪ Y ⊆ H := union_subset (fun _ ⟨z, hz, hzw⟩ => hzw ▸ hψH z (hKω hz))
          fun y hy => hYdH hy.1
        have hsafe := IsSafeAt.of_dense hwc hK₂H (union_subset hdense subset_closure) subset_union_right
          (by positivity) hY
        exact (Restart.DomainMarkov.disjoint_fwdHull_of_isSafeAt hwc hK₂H hsafe).mono_left subset_union_left
    constructor
    · rintro ⟨hω, hlive, hKω, hdis⟩
      exact ⟨⟨⟨hω, hlive⟩, hω, hKω⟩, (key hω hlive hKω).1 hdis⟩
    · rintro ⟨⟨⟨hω, hlive⟩, -, hKω⟩, hex⟩
      exact ⟨hω, hlive, hKω, (key hω hlive hKω).2 hex⟩
  rw [e]
  refine (hL.inter (h𝓦ℳ _ hKC)).inter (MeasurableSet.iUnion fun m => MeasurableSet.iInter fun k => ?_)
  refine MeasurableSet.biInter hKdc fun z _ => MeasurableSet.biUnion hYdc fun y hy => ?_
  exact (h𝓦ℳ _ (hEvm k z y)).inter (hSfm m y hy)

end Avoid

/-! ### The canonical set at `q` is a prefix-measurable random closed set -/

section Main

variable {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]

/-- **The canonical set `K_q = activeCompl q` is measurable for the walls and the traversal's prefix up to `q`**
(hitting σ-algebra). -/
theorem measurable_activeCompl_locPrefixSigma (h𝓦 : 𝓦 ≤ mΩ) {A : Set Ω} (hA : MeasurableSet[𝓦] A)
    {γ : Ω → ℝ → ℂ} (hγ : ∀ ω ∈ A, IsDrivenCurve (γ ω)) (hγm : ∀ u, 0 ≤ u → Measurable fun ω : A => γ ω u)
    {C : Ω → Set ℂ} (hCo : ∀ ω ∈ A, IsOpen (C ω)) (hCH : ∀ ω ∈ A, C ω ⊆ H) {ψ : Ω → ℂ → ℂ}
    (hψ : ∀ ω ∈ A, IsConformalBijection (ψ ω) (C ω) H) (hCm : ∀ z, MeasurableSet[𝓦] {ω | ω ∈ A ∧ z ∈ C ω})
    (hψm : ∀ z, Measurable[𝓦] ({ω | ω ∈ A ∧ z ∈ C ω}.indicator fun ω => ψ ω z))
    (hCin : ∀ U : Set ℂ, IsOpen U → U ⊆ H → MeasurableSet[𝓦] {ω | ω ∈ A ∧ U ⊆ C ω}) {c : Ω → Chart}
    (hc : ∀ ω ∈ A, (c ω).IsConformal ∧ ((c ω).dom : Set ℂ) = C ω ∧ EqOn (c ω).1 (ψ ω) (C ω)) (q : ℝ≥0) :
    Measurable[locPrefixSigma 𝓦 A γ q, hittingSigma] (activeCompl A γ c q) := by
  classical
  refine @measurable_generateFrom Ω (Set ℂ) (locPrefixSigma 𝓦 A γ q) _ _ ?_
  rintro _ ⟨U, hUo, hUH, rfl⟩
  show MeasurableSet[locPrefixSigma 𝓦 A γ q] {ω | (activeCompl A γ c q ω ∩ U).Nonempty}
  rcases U.eq_empty_or_nonempty with rfl | hUne
  · simp only [inter_empty, Set.not_nonempty_empty, ofPred_false]
    exact @MeasurableSet.empty _ (locPrefixSigma 𝓦 A γ q)
  set Eb : ℚ × ℚ × ℚ → Set Ω := fun b => {ω | ω ∈ A ∧ (q : ℝ≥0∞) < capLife (γ ω) ∧ ratCBall b ⊆ C ω ∧
    Disjoint (ψ ω '' ratCBall b) (fwdHull (fun s : ℝ => segDriver (γ ω) s.toNNReal) q)} with hEb
  have hEbm : ∀ b, MeasurableSet[locPrefixSigma 𝓦 A γ q] (Eb b) := fun b =>
    measurableSet_compact_avoid h𝓦 hA hγ hγm hCo hCH hψ hCm hψm hCin (isCompact_ratCBall b) q
  have e : {ω | (activeCompl A γ c q ω ∩ U).Nonempty} =
      ({ω | ω ∈ A ∧ (q : ℝ≥0∞) < capLife (γ ω)} ∩ ⋂ b : ℚ × ℚ × ℚ, {ω | ratCBall b ⊆ U → ω ∈ Eb b})ᶜ := by
    ext ω
    simp only [mem_ofPred_eq, mem_compl_iff, mem_inter_iff, mem_iInter]
    have hiff : U ⊆ activeDom A γ c q ω ↔
        (ω ∈ A ∧ (q : ℝ≥0∞) < capLife (γ ω)) ∧ ∀ b : ℚ × ℚ × ℚ, ratCBall b ⊆ U → ω ∈ Eb b := by
      constructor
      · intro hU
        obtain ⟨z₀, hz₀⟩ := hUne
        obtain ⟨hω, hlive, -⟩ := hU hz₀
        obtain ⟨hcc, hdom, hfwd⟩ := hc ω hω
        have hact : ∀ z ∈ U, z ∈ C ω ∧ ψ ω z ∉ fwdHull (fun s : ℝ => segDriver (γ ω) s.toNNReal) q := by
          intro z hz
          have h := (hU hz).2.2
          rw [inv_image_diff_eq hcc hdom hfwd (hψ ω hω)] at h
          exact h
        refine ⟨⟨hω, hlive⟩, fun b hb => ⟨hω, hlive, fun z hz => (hact z (hb hz)).1, ?_⟩⟩
        refine Set.disjoint_left.2 ?_
        rintro _ ⟨z, hz, rfl⟩
        exact (hact z (hb hz)).2
      · rintro ⟨⟨hω, hlive⟩, hall⟩ z hz
        obtain ⟨hcc, hdom, hfwd⟩ := hc ω hω
        obtain ⟨b, hzb, hbU⟩ := exists_ratCBall_mem_subset hUo hz
        obtain ⟨-, -, hbC, hdis⟩ := hall b hbU
        refine ⟨hω, hlive, ?_⟩
        rw [inv_image_diff_eq hcc hdom hfwd (hψ ω hω)]
        exact ⟨hbC hzb, Set.disjoint_left.1 hdis (mem_image_of_mem _ hzb)⟩
    rw [← hiff]
    constructor
    · rintro ⟨z, hzK, hzU⟩ hsub
      exact hzK.2 (hsub hzU)
    · intro hns
      rw [not_subset] at hns
      obtain ⟨z, hzU, hzD⟩ := hns
      exact ⟨z, ⟨hUH hzU, hzD⟩, hzU⟩
  rw [e]
  refine MeasurableSet.compl ((measurableSet_live A γ q).inter (MeasurableSet.iInter fun b => ?_))
  by_cases hb : ratCBall b ⊆ U
  · have : {ω | ratCBall b ⊆ U → ω ∈ Eb b} = Eb b := by
      ext ω; simp only [mem_ofPred_eq, hb, forall_true_left]
    rw [this]; exact hEbm b
  · have : {ω | ratCBall b ⊆ U → ω ∈ Eb b} = univ := by
      ext ω; simp only [mem_ofPred_eq, hb, false_implies, mem_univ]
    rw [this]; exact @MeasurableSet.univ _ (locPrefixSigma 𝓦 A γ q)

/-- The canonical set at `q` is measurable for the prefix σ-algebra at every later time. -/
theorem measurable_activeCompl_locPrefixSigma_of_le (h𝓦 : 𝓦 ≤ mΩ) {A : Set Ω} (hA : MeasurableSet[𝓦] A)
    {γ : Ω → ℝ → ℂ} (hγ : ∀ ω ∈ A, IsDrivenCurve (γ ω)) (hγm : ∀ u, 0 ≤ u → Measurable fun ω : A => γ ω u)
    {C : Ω → Set ℂ} (hCo : ∀ ω ∈ A, IsOpen (C ω)) (hCH : ∀ ω ∈ A, C ω ⊆ H) {ψ : Ω → ℂ → ℂ}
    (hψ : ∀ ω ∈ A, IsConformalBijection (ψ ω) (C ω) H) (hCm : ∀ z, MeasurableSet[𝓦] {ω | ω ∈ A ∧ z ∈ C ω})
    (hψm : ∀ z, Measurable[𝓦] ({ω | ω ∈ A ∧ z ∈ C ω}.indicator fun ω => ψ ω z))
    (hCin : ∀ U : Set ℂ, IsOpen U → U ⊆ H → MeasurableSet[𝓦] {ω | ω ∈ A ∧ U ⊆ C ω}) {c : Ω → Chart}
    (hc : ∀ ω ∈ A, (c ω).IsConformal ∧ ((c ω).dom : Set ℂ) = C ω ∧ EqOn (c ω).1 (ψ ω) (C ω)) {q r : ℝ≥0}
    (hqr : q ≤ r) :
    Measurable[locPrefixSigma 𝓦 A γ r, hittingSigma] (activeCompl A γ c q) :=
  (measurable_activeCompl_locPrefixSigma h𝓦 hA hγ hγm hCo hCH hψ hCm hψm hCin hc q).mono
    (locPrefixSigma_mono 𝓦 A γ hqr) le_rfl

end Main

end InteractingSLE.Sec7.PhaseCont
