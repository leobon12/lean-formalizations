/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5EnlFwd

/-!
# The domain events of a relative chart at a random capacity

Packet PROVE-R5-OUTERLAW (ruling R88). On an outer pocket the reference chart of Lemma R.5 is the relative chart at
the random capacity `Q = visitCap s` reached at the original time `s`. Its domain is the component of the reference
complement incident to the pocket target, not the whole complement `ℍ ∖ B`; so its domain events can no longer be
read off the reference set `B` (`R5Enl.measurableSet_inter_mem_dom_of_hitting`). They are read off the traversal's
prefix instead, through the safe events of single points (`PhaseCont.measurableSet_safe_point`):

* **`notMem_fwdHull_iff_safe`** (pathwise): a point `y ∈ ℍ` is outside the hull at `Q` iff for some levels
  `1/(m+1)`, `1/(k+1)`, every point of a countable dense `Yd ⊆ ℍ` within `1/(k+1)` of `y` is safe at level
  `1/(m+1)` at every rational time `d ≤ Q`. The converse direction uses the density lemma
  `Coupling.IsSafeAt.of_dense` and the closedness of the safe condition at its exit time
  (`Coupling.isSafeAt_safeExitTime`), so that nothing is read at the exact random time `Q`;
* **`measurableSet_mem_dom_relChart_rand`**: the domain events `G₀ ∩ {z ∈ dom}` of the relative chart at `Q` are
  events of any record `ℳ ≥ 𝓦` in which the relative-prefix events at fixed capacities `q`, cut to
  `G₀ ∩ {q ≤ Q}`, are events (`htrans`, the Galmarino property used by `R5Enl.measurable_indicator_fwd_relChart_rand`);
* **`measurable_indicator_fwd_relChart_rand'`**: `hfwd` at `Q` with this `hdom` discharged.

Conditional helpers with distinct names; nothing here uses Theorem 1.2/1.3 or any `*_of_param` (R43, R48).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H fwdHull)
open SupercriticalConformalCovariance (IsConformalBijection)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R5OLaw

open Coupling Ito PocketStop PocketStopSide PocketCoupling PocketTraversal PocketAdapt Lemma71C PocketUnionPt

/-! ### The safe criterion at a random time -/

section Path

variable {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-- The safe condition at the time `d` depends on the bounds `σ₀`, `N` only through `d ≤ σ₀`, `d ≤ N`. -/
theorem isSafeAt_iff_self {K : Set ℂ} {δ N : ℝ} {σ₀ d : ℝ≥0} (hσ : d ≤ σ₀) (hN : (d : ℝ) ≤ N) :
    IsSafeAt K δ N σ₀ ζ w d ↔ IsSafeAt K δ d d ζ w d :=
  ⟨fun h => ⟨h.1, le_rfl, le_rfl, h.2.2.2⟩, fun h => ⟨h.1, hσ, hN, h.2.2.2⟩⟩

/-- **A point off the hull at a random time, through rational times only**: `y ∈ ℍ` is outside the hull at `Q`
(`Q` live) iff, for some `m k`, every point of the countable dense set `Yd` within `1/(k+1)` of `y` is safe at level
`1/(m+1)` at every rational time `d ≤ Q`. -/
theorem notMem_fwdHull_iff_safe (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) (hw0 : w 0 = 0) {Q : ℝ≥0}
    (hQ : (Q : ℝ≥0∞) < ζ) {Yd : Set ℂ} (hYdH : Yd ⊆ H) (hYd : H ⊆ closure Yd) {y : ℂ} (hy : y ∈ H) :
    y ∉ fwdHull (rpath w) Q ↔ ∃ m k : ℕ, ∀ y' ∈ Yd, ‖y' - y‖ < 1 / ((k : ℝ) + 1) →
      ∀ d : ℚ, (d : ℝ).toNNReal ≤ Q →
        IsSafeAt {y'} (1 / ((m : ℝ) + 1)) (d : ℝ).toNNReal (d : ℝ).toNNReal ζ w (d : ℝ).toNNReal := by
  constructor
  · intro hyK
    have hyo : y ∈ H \ fwdHull (rpath w) Q := ⟨hy, hyK⟩
    obtain ⟨ρ, hρ, hρsub⟩ := (isCompact_singleton (x := y)).exists_cthickening_subset_open
      (MartMeans2.isOpen_H_diff_fwdHull_rpath hw hQ) (singleton_subset_iff.2 hyo)
    have hKH : cthickening ρ ({y} : Set ℂ) ⊆ H := fun z hz => (hρsub hz).1
    obtain ⟨δ, hδ, hsafe⟩ := Restart.DomainMarkov.exists_isSafeAt_self hw hw0 isCompact_singleton.cthickening
      hKH hQ fun z hz => exists_isForwardSol_of_mem Q.coe_nonneg (hρsub hz)
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hρ
    refine ⟨m, k, fun y' _ hyy' d hd => ?_⟩
    have hy'K : y' ∈ cthickening ρ ({y} : Set ℂ) := by
      refine mem_cthickening_of_dist_le y' y ρ {y} (mem_singleton y) ?_
      rw [dist_eq_norm]
      exact (hyy'.trans hk).le
    have h1 := ((hsafe.anti hw hKH hd).subset (singleton_subset_iff.2 hy'K)).mono hm.le le_rfl le_rfl
    exact (isSafeAt_iff_self hd (by exact_mod_cast hd)).1 h1
  · rintro ⟨m, k, hall⟩
    set δ : ℝ := 1 / ((m : ℝ) + 1) with hδdef
    have hδ : 0 < δ := by positivity
    set D : Set ℂ := Yd ∩ ball y (1 / ((k : ℝ) + 1)) with hD
    have hyD : y ∈ closure D := by
      refine Metric.mem_closure_iff.2 fun ε hε => ?_
      have hr : 0 < min ε (1 / ((k : ℝ) + 1)) := lt_min hε (by positivity)
      obtain ⟨y', hy'U, hy'Y⟩ := mem_closure_iff.1 (hYd hy) (ball y (min ε (1 / ((k : ℝ) + 1))))
        isOpen_ball (mem_ball_self hr)
      have hd := mem_ball'.1 hy'U
      exact ⟨y', ⟨hy'Y, mem_ball'.2 (hd.trans_le (min_le_right _ _))⟩, hd.trans_le (min_le_left _ _)⟩
    obtain ⟨y₀, hy₀⟩ : D.Nonempty := by
      obtain ⟨y₀, hy₀, -⟩ := Metric.mem_closure_iff.1 hyD 1 one_pos
      exact ⟨y₀, hy₀⟩
    have hnorm : ∀ y' ∈ D, ‖y' - y‖ < 1 / ((k : ℝ) + 1) := fun y' hy' => by
      rw [← dist_eq_norm]
      exact mem_ball.1 hy'.2
    have hKH : insert y D ⊆ H := insert_subset hy fun y' hy' => hYdH hy'.1
    -- the safe condition for `y` at every rational time up to `Q`
    have hSy : ∀ d : ℚ, (d : ℝ).toNNReal ≤ Q → IsSafeAt {y} δ Q Q ζ w (d : ℝ).toNNReal := by
      intro d hd
      have hDs : IsSafeAt D δ (d : ℝ).toNNReal (d : ℝ).toNNReal ζ w (d : ℝ).toNNReal :=
        ⟨(hall y₀ hy₀.1 (hnorm y₀ hy₀) d hd).1, le_rfl, le_rfl, fun z hz =>
          (hall z hz.1 (hnorm z hz) d hd).2.2.2 z (mem_singleton z)⟩
      have hK := IsSafeAt.of_dense hw hKH (insert_subset hyD subset_closure) (subset_insert y D) hδ hDs
      exact (isSafeAt_iff_self hd (by exact_mod_cast hd)).2
        (hK.subset (singleton_subset_iff.2 (mem_insert y D)))
    -- the exit time of `{y}` is `Q`
    have hKy : ({y} : Set ℂ) ⊆ H := singleton_subset_iff.2 hy
    have hle : Q ≤ safeExitTime {y} δ Q Q ζ w := by
      refine le_of_forall_lt_imp_le_of_dense fun t htQ => le_safeExitTime_of_forall fun s hst => ?_
      obtain ⟨d, htd, hdQ⟩ := exists_rat_btwn (show (t : ℝ) < Q by exact_mod_cast htQ)
      have hd0 : (0 : ℝ) ≤ d := t.coe_nonneg.trans htd.le
      have hdQ' : (d : ℝ).toNNReal ≤ Q := by
        rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hd0]
        exact hdQ.le
      have hsd : s ≤ (d : ℝ).toNNReal := by
        rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hd0]
        exact (show (s : ℝ) ≤ t by exact_mod_cast hst).trans htd.le
      exact (hSy d hdQ').anti hw hKy hsd
    have hexit : safeExitTime {y} δ Q Q ζ w = Q := le_antisymm safeExitTime_le_sigma hle
    have h0 : IsSafeAt {y} δ Q Q ζ w 0 := by
      have h := hSy 0 (by rw [Rat.cast_zero, Real.toNNReal_zero]; exact zero_le)
      rwa [Rat.cast_zero, Real.toNNReal_zero] at h
    have hQs := isSafeAt_safeExitTime hw hKy hδ hQ h0
    rw [hexit] at hQs
    exact Set.disjoint_left.1 (Restart.DomainMarkov.disjoint_fwdHull_of_isSafeAt hw hKy hQs) (mem_singleton y)

end Path

/-! ### The domain events at a random capacity -/

section Meas

variable {Ω : Type*} {𝓦 ℳ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]

/-- **The domain events of the relative chart at a random capacity `Q`** are events of a record `ℳ ≥ 𝓦` in which the
relative-prefix events at every fixed capacity `q`, cut to `G₀ ∩ {q ≤ Q}`, are events (`htrans`). On `G₀`
(inside the test `A`, `Q` live), `z ∈ dom` iff `z ∈ C` and `ψ z` is off the relative hull at `Q`, which is read on
rational times `d ≤ Q` through the safe events of the points of a countable dense set (`notMem_fwdHull_iff_safe`). -/
theorem measurableSet_mem_dom_relChart_rand (h𝓦 : 𝓦 ≤ mΩ) {A : Set Ω} (hA : MeasurableSet[𝓦] A)
    {γ : Ω → ℝ → ℂ} (hγ : ∀ ω ∈ A, IsDrivenCurve (γ ω)) (hγm : ∀ u, 0 ≤ u → Measurable fun ω : A => γ ω u)
    {C : Ω → Set ℂ} {ψ : Ω → ℂ → ℂ} (hψ : ∀ ω ∈ A, IsConformalBijection (ψ ω) (C ω) H)
    (hCm : ∀ z, MeasurableSet[𝓦] {ω | ω ∈ A ∧ z ∈ C ω})
    (hψm : ∀ z, Measurable[𝓦] ({ω | ω ∈ A ∧ z ∈ C ω}.indicator fun ω => ψ ω z)) {c : Ω → Chart}
    (hc : ∀ ω ∈ A, (c ω).IsConformal ∧ ((c ω).dom : Set ℂ) = C ω ∧ EqOn (c ω).1 (ψ ω) (C ω))
    (h𝓦ℳ : 𝓦 ≤ ℳ) {Q : Ω → ℝ≥0} {G₀ : Set Ω} (hG₀ : MeasurableSet[ℳ] G₀) (hG₀A : G₀ ⊆ A)
    (hQlive : ∀ ω ∈ G₀, (Q ω : ℝ≥0∞) < capLife (γ ω))
    (htrans : ∀ (q : ℝ≥0) (M : Set Ω), MeasurableSet[locPrefixSigma 𝓦 A γ q] M →
      MeasurableSet[ℳ] (G₀ ∩ {ω | q ≤ Q ω} ∩ M)) (z : ℂ) :
    MeasurableSet[ℳ] (G₀ ∩ {ω | z ∈ (relChart c γ (Q ω) ω).dom}) := by
  classical
  obtain ⟨Yd, hYdH, hYdc, hYdd⟩ := (TopologicalSpace.IsSeparable.of_separableSpace H).exists_countable_dense_subset
  set Cz : Set Ω := {ω | ω ∈ A ∧ z ∈ C ω} with hCz
  set Ev : ℕ → ℂ → Set Ω := fun k y => {ω | ω ∈ A ∧ z ∈ C ω ∧ ‖ψ ω z - y‖ < 1 / ((k : ℝ) + 1)} with hEv
  set Sf : ℕ → ℂ → ℚ → Set Ω := fun m y d => {ω | ω ∈ A ∧ IsSafeAt {y} (1 / ((m : ℝ) + 1)) (d : ℝ).toNNReal
    (d : ℝ).toNNReal (capLife (γ ω)) (fun t => segDriver (γ ω) t) (d : ℝ).toNNReal} with hSf
  set Le : ℚ → Set Ω := fun d => G₀ ∩ {ω | (d : ℝ).toNNReal ≤ Q ω} with hLe
  have hEvm : ∀ k y, MeasurableSet[𝓦] (Ev k y) := by
    intro k y
    have e : Ev k y = Cz ∩ {ω | ‖(Cz.indicator fun ω => ψ ω z) ω - y‖ < 1 / ((k : ℝ) + 1)} := by
      ext ω
      simp only [hEv, hCz, mem_ofPred_eq, mem_inter_iff]
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
  have hLem : ∀ d, MeasurableSet[ℳ] (Le d) := fun d => by
    have h := htrans (d : ℝ).toNNReal univ (@MeasurableSet.univ _ (locPrefixSigma 𝓦 A γ _))
    rwa [inter_univ] at h
  have hSfm : ∀ m, ∀ y ∈ Yd, ∀ d, MeasurableSet[ℳ] (Le d ∩ Sf m y d) := fun m y hy d =>
    htrans _ _ (PhaseCont.measurableSet_safe_point h𝓦 hA hγ hγm (hYdH hy) _ _)
  have e : G₀ ∩ {ω | z ∈ (relChart c γ (Q ω) ω).dom} = G₀ ∩ Cz ∩ ⋃ m : ℕ, ⋃ k : ℕ, ⋂ y ∈ Yd, ⋂ d : ℚ,
      ((Ev k y)ᶜ ∪ (Le d)ᶜ ∪ (Le d ∩ Sf m y d)) := by
    ext ω
    simp only [mem_inter_iff, mem_ofPred_eq, mem_iUnion, mem_iInter, mem_union, mem_compl_iff, hCz, hEv, hLe,
      hSf]
    constructor
    · rintro ⟨hG, hzd⟩
      have hω := hG₀A hG
      have hQ := hQlive ω hG
      obtain ⟨hcc, hcdom, hcfwd⟩ := hc ω hω
      rw [← SetLike.mem_coe, ← activeDom_eq_relChart_dom hω hQ (hγ ω hω) hcc, activeDom_eq hω hQ,
        PhaseCont.inv_image_diff_eq hcc hcdom hcfwd (hψ ω hω)] at hzd
      obtain ⟨hzC, hzK⟩ := hzd
      have hψH : ψ ω z ∈ H := (hψ ω hω).2.mapsTo hzC
      obtain ⟨m, k, hmk⟩ := (notMem_fwdHull_iff_safe (hγ ω hω).segDriver_spec.2.1 (hγ ω hω).segDriver_spec.1 hQ
        hYdH hYdd hψH).1 hzK
      refine ⟨⟨hG, hω, hzC⟩, m, k, fun y hy d => ?_⟩
      by_cases hyz : ‖ψ ω z - y‖ < 1 / ((k : ℝ) + 1)
      · by_cases hdQ : (d : ℝ).toNNReal ≤ Q ω
        · exact Or.inr ⟨⟨hG, hdQ⟩, hω, hmk y hy (by rwa [norm_sub_rev]) d hdQ⟩
        · exact Or.inl (Or.inr fun h => hdQ h.2)
      · exact Or.inl (Or.inl fun h => hyz h.2.2)
    · rintro ⟨⟨hG, hω, hzC⟩, m, k, hall⟩
      have hQ := hQlive ω hG
      obtain ⟨hcc, hcdom, hcfwd⟩ := hc ω hω
      refine ⟨hG, ?_⟩
      rw [← SetLike.mem_coe, ← activeDom_eq_relChart_dom hω hQ (hγ ω hω) hcc, activeDom_eq hω hQ,
        PhaseCont.inv_image_diff_eq hcc hcdom hcfwd (hψ ω hω)]
      have hψH : ψ ω z ∈ H := (hψ ω hω).2.mapsTo hzC
      refine ⟨hzC, (notMem_fwdHull_iff_safe (hγ ω hω).segDriver_spec.2.1 (hγ ω hω).segDriver_spec.1 hQ
        hYdH hYdd hψH).2 ⟨m, k, fun y hy hyz d hdQ => ?_⟩⟩
      rcases hall y hy d with (h | h) | h
      · exact absurd ⟨hω, hzC, by rwa [norm_sub_rev]⟩ h
      · exact absurd ⟨hG, hdQ⟩ h
      · exact h.2.2
  rw [e]
  refine (hG₀.inter (h𝓦ℳ _ (hCm z))).inter (MeasurableSet.iUnion fun m => MeasurableSet.iUnion fun k =>
    MeasurableSet.biInter hYdc fun y hy => MeasurableSet.iInter fun d => ?_)
  exact ((h𝓦ℳ _ (hEvm k y)).compl.union (hLem d).compl).union (hSfm m y hy d)

/-- **`hfwd` for the relative chart at a random capacity, with its domain events discharged**
(`R5Enl.measurable_indicator_fwd_relChart_rand` with `hdom` from `measurableSet_mem_dom_relChart_rand`). -/
theorem measurable_indicator_fwd_relChart_rand' (h𝓦 : 𝓦 ≤ mΩ) {A : Set Ω} (hA : MeasurableSet[𝓦] A)
    {γ : Ω → ℝ → ℂ} (hγ : ∀ ω ∈ A, IsDrivenCurve (γ ω)) (hγm : ∀ u, 0 ≤ u → Measurable fun ω : A => γ ω u)
    {C : Ω → Set ℂ} {ψ : Ω → ℂ → ℂ} (hψ : ∀ ω ∈ A, IsConformalBijection (ψ ω) (C ω) H)
    (hCm : ∀ z, MeasurableSet[𝓦] {ω | ω ∈ A ∧ z ∈ C ω})
    (hψm : ∀ z, Measurable[𝓦] ({ω | ω ∈ A ∧ z ∈ C ω}.indicator fun ω => ψ ω z)) {c : Ω → Chart}
    (hc : ∀ ω ∈ A, (c ω).IsConformal ∧ ((c ω).dom : Set ℂ) = C ω ∧ EqOn (c ω).1 (ψ ω) (C ω))
    (hcfwd : ∀ z, Measurable[𝓦] ((A ∩ {ω | z ∈ (c ω).dom}).indicator fun ω => (c ω).1 z))
    (hKm : ∀ q : ℝ≥0, Measurable[locPrefixSigma 𝓦 A γ q, hittingSigma] (activeCompl A γ c q))
    (h𝓦ℳ : 𝓦 ≤ ℳ) {Q : Ω → ℝ≥0} {G₀ : Set Ω} (hG₀ : MeasurableSet[ℳ] G₀) (hG₀A : G₀ ⊆ A)
    (hQlive : ∀ ω ∈ G₀, (Q ω : ℝ≥0∞) < capLife (γ ω))
    (htrans : ∀ (q : ℝ≥0) (M : Set Ω), MeasurableSet[locPrefixSigma 𝓦 A γ q] M →
      MeasurableSet[ℳ] (G₀ ∩ {ω | q ≤ Q ω} ∩ M)) (z : ℂ) :
    MeasurableSet[ℳ] (G₀ ∩ {ω | z ∈ (relChart c γ (Q ω) ω).dom}) ∧
      Measurable[ℳ] ((G₀ ∩ {ω | z ∈ (relChart c γ (Q ω) ω).dom}).indicator
        fun ω => (relChart c γ (Q ω) ω).1 z) := by
  have hdom := measurableSet_mem_dom_relChart_rand h𝓦 hA hγ hγm hψ hCm hψm hc h𝓦ℳ hG₀ hG₀A hQlive htrans z
  exact ⟨hdom, R5Enl.measurable_indicator_fwd_relChart_rand hγ (fun ω hω => (hc ω hω).1) hcfwd hKm hG₀ hG₀A
    hQlive htrans z hdom⟩

end Meas

end InteractingSLE.Sec7.R5OLaw
