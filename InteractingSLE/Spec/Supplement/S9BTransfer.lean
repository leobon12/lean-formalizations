/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.S9BSide

/-!
# Supplement §9 (continued): transferring an ordered completion to a new completion of the first path

Packet PROVE-SUPP9-B. Convention W0 (p. 528): `HasOrderedProperCompletions α a β c` says that the finite prefixes
`α([0, a])`, `β([0, c])` have proper completions `α'`, `β'` with `β'` in the closed left side of `α'`.

**Transfer lemma** (`exists_isProperCompletion_subset_closedLeftSide`). Let `α'`, `β'` be such completions, and
let `α''` be *any other* proper completion of `α([0, a])` whose new part `α''([a, ∞))` avoids `β([0, c])`. Then
`β([0, c])` has a proper completion `β''` in the closed left side of `α''`: follow `β'` until it first meets
`α''([a, ∞))`, then follow `α''` to infinity. Every point of `β''` before the junction lies on the left of `α''`:
the part of `β'` after its last visit of `α([0, a])` (or all of it, from the left seed) is connected and avoids
`α''`, and near the visited point it lies on the left of `α'` (which it does not meet there), hence on the left of
`α''` by the side principle (`eventually_mem_leftSide_of_eqOn`).

**Duality** (`range_subset_closedRightSide`): `β' ⊆ closedLeftSide α'` implies `α' ⊆ closedRightSide β'`, by
Jordan separation and the frontier property of the right side; with the reflection `z ↦ −z̄` this makes the order
symmetric (`hasOrderedProperCompletions_reflect`), so that every one-sided extension is an extension of the first
path of some ordered pair.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric Complex Bornology
open scoped NNReal

namespace InteractingSLE

namespace Supp9B

variable {α β α' β' α'' : ℝ≥0 → ℂ} {a c : ℝ≥0}

theorem isClosed_seedRayClosure {γ : ℝ≥0 → ℂ} (hγ : IsProperCurve γ) : IsClosed (seedRayClosure γ) := by
  have h1 : IsClosed (range γ) := by rw [← image_univ]; exact isClosed_image hγ isClosed_univ
  have h2 : IsClosed {z : ℂ | z.re = (γ 0).re ∧ z.im ≤ (γ 0).im} :=
    (isClosed_eq continuous_re continuous_const).inter (isClosed_le continuous_im continuous_const)
  exact h1.union h2

theorem eq_of_re_eq_of_im_eq_zero {z w : ℂ} (hre : z.re = w.re) (hz : z.im = 0) (hw : w.im = 0) : z = w :=
  Complex.ext hre (hz.trans hw.symm)

/-- **The pieces argument.** Let `α'`, `α''` be proper curves from the same real seed agreeing on `[0, a]`, and let
`β'` be a proper curve from a real seed weakly to the left, contained in the closed left side of `α'`. If
`β'([0, t])` avoids `α''([a, ∞))`, then `β'(t)` lies in the closed left side of `α''`. -/
theorem mem_closedLeftSide_of_avoid (hα' : IsProperCurve α') (hα'' : IsProperCurve α'')
    (h0 : (α' 0).im = 0) (hagree : ∀ t ≤ a, α'' t = α' t) (hβ' : IsProperCurve β')
    (hβ0 : (β' 0).im = 0) (hseed : (β' 0).re ≤ (α' 0).re) (hord : range β' ⊆ closedLeftSide α')
    {t : ℝ≥0} (havoid : ∀ u ≤ t, ∀ s, a ≤ s → β' u ≠ α'' s) : β' t ∈ closedLeftSide α'' := by
  have hag0 : α'' 0 = α' 0 := hagree 0 zero_le
  have h0'' : (α'' 0).im = 0 := by rw [hag0]; exact h0
  set S := seedRayClosure α'' with hS
  by_cases hzS : β' t ∈ S
  · exact Or.inr hzS
  refine Or.inl ?_
  have hSc : IsClosed S := isClosed_seedRayClosure hα''
  -- the visits of the closed curve `S` up to time `t`
  set V := {u : ℝ≥0 | u ≤ t ∧ β' u ∈ S} with hV
  have hVc : IsClosed V := isClosed_Iic.inter (hSc.preimage hβ'.1)
  -- a connected piece avoiding `S` and containing `β' t` lies on one side
  have hpiece : ∀ u ≤ t, (∀ v, u ≤ v → v ≤ t → β' v ∉ S) → β' u ∈ leftSide α'' →
      β' t ∈ leftSide α'' := by
    intro u hut hav hu
    have hpc : IsPreconnected (β' '' Icc u t) := isPreconnected_Icc.image _ hβ'.1.continuousOn
    have hsub : β' '' Icc u t ⊆ Sᶜ := by
      rintro _ ⟨v, hv, rfl⟩; exact hav v hv.1 hv.2
    have := hpc.subset_connectedComponentIn ⟨u, ⟨le_rfl, hut⟩, rfl⟩ hsub
    rw [← connectedComponentIn_eq hu] at this
    exact this ⟨t, ⟨hut, le_rfl⟩, rfl⟩
  rcases V.eq_empty_or_nonempty with hVe | hVne
  · -- no visit: the piece starts at the left seed
    have hav : ∀ v, 0 ≤ v → v ≤ t → β' v ∉ S := fun v _ hvt hv =>
      (hVe ▸ (show v ∈ V from ⟨hvt, hv⟩) : v ∈ (∅ : Set ℝ≥0))
    refine hpiece 0 zero_le hav ?_
    have hb0S : β' 0 ∉ S := hav 0 le_rfl zero_le
    have hne : (β' 0).re ≠ (α'' 0).re := fun h =>
      hb0S (Or.inl ⟨0, (eq_of_re_eq_of_im_eq_zero h hβ0 h0'').symm⟩)
    have hlt : (β' 0).re < (α'' 0).re := lt_of_le_of_ne (hag0 ▸ hseed) hne
    have := ofReal_mem_leftSide hα''.2.2.1 h0'' hlt (by
      rwa [show ((β' 0).re : ℂ) = β' 0 from (eq_of_re_eq_of_im_eq_zero (by simp) (by simp) hβ0)])
    rwa [show ((β' 0).re : ℂ) = β' 0 from (eq_of_re_eq_of_im_eq_zero (by simp) (by simp) hβ0)] at this
  · -- the last visit `u₀`
    have hbdd : BddAbove V := ⟨t, fun u hu => hu.1⟩
    set u₀ := sSup V with hu₀
    have hu₀V : u₀ ∈ V := hVc.csSup_mem hVne hbdd
    have hu₀t : u₀ < t := lt_of_le_of_ne hu₀V.1 fun h => hzS (h ▸ hu₀V.2)
    have hafter : ∀ v, u₀ < v → v ≤ t → β' v ∉ S := fun v hv hvt hvS =>
      absurd (le_csSup hbdd ⟨hvt, hvS⟩) (not_le.2 hv)
    -- the visited point is on the common arc, strictly before `a`
    obtain ⟨s₀, hs₀a, hs₀⟩ : ∃ s₀, s₀ < a ∧ β' u₀ = α' s₀ := by
      have hm := hu₀V.2
      have hmr : β' u₀ ∈ range α'' := by
        rcases hm with h | ⟨hre, him⟩
        · exact h
        · have him0 : (β' u₀).im = 0 := le_antisymm (h0'' ▸ him) (hβ'.2.2.1 u₀)
          exact ⟨0, (eq_of_re_eq_of_im_eq_zero hre him0 h0'').symm⟩
      obtain ⟨s₀, hs₀⟩ := hmr
      refine ⟨s₀, lt_of_not_ge fun h => havoid u₀ hu₀V.1 s₀ h hs₀.symm, ?_⟩
      rw [← hs₀, hagree s₀ (le_of_lt (lt_of_not_ge fun h => havoid u₀ hu₀V.1 s₀ h hs₀.symm))]
    -- near the visited point, the left side of `α'` is in the left side of `α''`
    have hSP := eventually_mem_leftSide_of_eqOn hα' hα'' h0 hagree hs₀a
    have hfar : ∀ᶠ w in 𝓝 (α' s₀), w ∉ α' '' Ici a := by
      refine (isClosed_image hα' isClosed_Ici).isOpen_compl.mem_nhds ?_
      rintro ⟨s, hs, hss⟩
      exact absurd (hα'.2.1 hss ▸ hs : a ≤ s₀) (not_le.2 hs₀a)
    have hev : ∀ᶠ u in 𝓝[>] u₀, (β' u ∈ leftSide α' → β' u ∈ leftSide α'') ∧ β' u ∉ α' '' Ici a :=
      (hβ'.1.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).eventually
        (hs₀ ▸ hSP.and hfar)
    obtain ⟨u, ⟨hSPu, hfaru⟩, huu₀, hut⟩ := (hev.and (Ioc_mem_nhdsGT hu₀t)).exists
    have huS : β' u ∉ S := hafter u huu₀ hut
    have huL' : β' u ∈ leftSide α' := by
      rcases hord ⟨u, rfl⟩ with h | h
      · exact h
      · exfalso
        rcases h with ⟨s, hs⟩ | ⟨hre, him⟩
        · by_cases hsa : s ≤ a
          · exact huS (Or.inl ⟨s, by rw [hagree s hsa]; exact hs⟩)
          · exact hfaru ⟨s, le_of_lt (not_le.1 hsa), hs⟩
        · exact huS (Or.inr ⟨by rw [hag0]; exact hre, by rw [hag0]; exact him⟩)
    exact hpiece u hut (fun v hv hvt => hafter v (lt_of_lt_of_le huu₀ hv) hvt) (hSPu huL')

/-! ### The junction of two curves -/

/-- Follow `β'` up to time `T`, then `α''` from time `S` on. -/
def junction (β' α'' : ℝ≥0 → ℂ) (T S : ℝ≥0) (t : ℝ≥0) : ℂ :=
  if t ≤ T then β' t else α'' (S + (t - T))

theorem junction_of_le {T S t : ℝ≥0} (ht : t ≤ T) : junction β' α'' T S t = β' t := by
  simp [junction, ht]

theorem junction_of_lt {T S t : ℝ≥0} (ht : T < t) : junction β' α'' T S t = α'' (S + (t - T)) := by
  simp [junction, not_le.2 ht]

theorem isProperCurve_junction {T S : ℝ≥0} (hβ' : IsProperCurve β') (hα'' : IsProperCurve α'')
    (hj : β' T = α'' S) (hdisj : ∀ u < T, ∀ s, S ≤ s → β' u ≠ α'' s) :
    IsProperCurve (junction β' α'' T S) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine Continuous.if_le hβ'.1 (hα''.1.comp (continuous_const.add (continuous_id.sub continuous_const)))
      continuous_id continuous_const fun t ht => ?_
    rw [show t = T from ht, tsub_self, add_zero, hj]
  · intro u v huv
    by_cases hu : u ≤ T <;> by_cases hv : v ≤ T
    · rw [junction_of_le hu, junction_of_le hv] at huv; exact hβ'.2.1 huv
    · rw [junction_of_le hu, junction_of_lt (not_le.1 hv)] at huv
      exfalso
      rcases hu.lt_or_eq with hu' | rfl
      · exact hdisj u hu' _ le_self_add huv
      · rw [hj] at huv
        have h1 := hα''.2.1 huv
        have : v - u = 0 := by
          have := congrArg (fun x => x - S) h1
          simpa using this.symm
        exact hv (tsub_eq_zero_iff_le.1 this)
    · rw [junction_of_lt (not_le.1 hu), junction_of_le hv] at huv
      exfalso
      rcases hv.lt_or_eq with hv' | rfl
      · exact hdisj v hv' _ le_self_add huv.symm
      · rw [hj] at huv
        have h1 := hα''.2.1 huv
        have : u - v = 0 := by
          have := congrArg (fun x => x - S) h1
          simpa using this
        exact hu (tsub_eq_zero_iff_le.1 this)
    · rw [junction_of_lt (not_le.1 hu), junction_of_lt (not_le.1 hv)] at huv
      have h1 := add_left_cancel (hα''.2.1 huv)
      exact (tsub_left_inj (le_of_lt (not_le.1 hu)) (le_of_lt (not_le.1 hv))).1 h1
  · intro t
    by_cases ht : t ≤ T
    · rw [junction_of_le ht]; exact hβ'.2.2.1 t
    · rw [junction_of_lt (not_le.1 ht)]; exact hα''.2.2.1 _
  · have h1 : Tendsto (fun t : ℝ≥0 => S + (t - T)) atTop atTop := by
      refine tendsto_atTop_atTop.2 fun b => ⟨b + T, fun t ht => ?_⟩
      have : b ≤ t - T := le_tsub_of_add_le_right ht
      exact this.trans le_add_self
    refine (hα''.2.2.2.comp h1).congr' ?_
    filter_upwards [eventually_gt_atTop T] with t ht
    simp only [Function.comp, junction_of_lt ht]

/-! ### The transfer lemma -/

/-- **Transfer of an ordered completion to a new completion of the first path.** If `α'`, `β'` are ordered
proper completions of `α([0, a])`, `β([0, c])` from real seeds with `β(0) ≤ α(0)`, and `α''` is any proper
completion of `α([0, a])` whose new part `α''([a, ∞))` avoids `β([0, c])`, then `β([0, c])` has a proper
completion in the closed left side of `α''`. -/
theorem exists_isProperCompletion_subset_closedLeftSide (hα' : IsProperCompletion α a α')
    (hβ' : IsProperCompletion β c β') (hord : range β' ⊆ closedLeftSide α') (h0 : (α 0).im = 0)
    (hβ0 : (β 0).im = 0) (hseed : (β 0).re ≤ (α 0).re) (hα'' : IsProperCompletion α a α'')
    (htail : ∀ s, a ≤ s → ∀ y ≤ c, α'' s ≠ β y) :
    ∃ β'', IsProperCompletion β c β'' ∧ range β'' ⊆ closedLeftSide α'' := by
  have P' := isProperCurve_of_isProperCompletion hα'
  have P'' := isProperCurve_of_isProperCompletion hα''
  have Q' := isProperCurve_of_isProperCompletion hβ'
  have hagree : ∀ t ≤ a, α'' t = α' t := fun t ht => (hα''.2.2.2.2 t ht).trans (hα'.2.2.2.2 t ht).symm
  have ha0 : α' 0 = α 0 := hα'.2.2.2.2 0 zero_le
  have hb0 : β' 0 = β 0 := hβ'.2.2.2.2 0 zero_le
  have h0' : (α' 0).im = 0 := by rw [ha0]; exact h0
  have hβ0' : (β' 0).im = 0 := by rw [hb0]; exact hβ0
  have hseed' : (β' 0).re ≤ (α' 0).re := by rw [ha0, hb0]; exact hseed
  have hpre : ∀ u ≤ c, ∀ s, a ≤ s → β' u ≠ α'' s := fun u hu s hs h =>
    htail s hs u hu (by rw [← h, hβ'.2.2.2.2 u hu])
  set F := α'' '' Ici a with hF
  have hFc : IsClosed F := isClosed_image P'' isClosed_Ici
  set Hs := {t : ℝ≥0 | c ≤ t ∧ β' t ∈ F} with hHs
  have hHc : IsClosed Hs := isClosed_Ici.inter (hFc.preimage Q'.1)
  rcases Hs.eq_empty_or_nonempty with hHe | hHne
  · refine ⟨β', hβ', ?_⟩
    rintro _ ⟨t, rfl⟩
    refine mem_closedLeftSide_of_avoid P' P'' h0' hagree Q' hβ0' hseed' hord fun u _ s hs h => ?_
    by_cases huc : u ≤ c
    · exact hpre u huc s hs h
    · have : u ∈ Hs := ⟨le_of_lt (not_le.1 huc), ⟨s, hs, h.symm⟩⟩
      rw [hHe] at this; exact this
  · set T := sInf Hs with hT
    have hTH : T ∈ Hs := hHc.csInf_mem hHne (OrderBot.bddBelow Hs)
    obtain ⟨S, hSa, hS⟩ := hTH.2
    have hbefore : ∀ u < T, ∀ s, a ≤ s → β' u ≠ α'' s := by
      intro u hu s hs h
      by_cases huc : u ≤ c
      · exact hpre u huc s hs h
      · exact absurd (csInf_le (OrderBot.bddBelow Hs) ⟨le_of_lt (not_le.1 huc), ⟨s, hs, h.symm⟩⟩)
          (not_le.2 hu)
    have hJ := isProperCurve_junction Q' P'' hS.symm fun u hu s hs => hbefore u hu s (hSa.trans hs)
    refine ⟨junction β' α'' T S, ⟨hJ.1, hJ.2.1, hJ.2.2.1, hJ.2.2.2, fun t ht => ?_⟩, ?_⟩
    · rw [junction_of_le (ht.trans hTH.1)]; exact hβ'.2.2.2.2 t ht
    · rintro _ ⟨t, rfl⟩
      by_cases htT : t ≤ T
      · rw [junction_of_le htT]
        rcases htT.lt_or_eq with htT' | rfl
        · exact mem_closedLeftSide_of_avoid P' P'' h0' hagree Q' hβ0' hseed' hord
            fun u hu s hs => hbefore u (lt_of_le_of_lt hu htT') s hs
        · exact Or.inr (Or.inl ⟨S, hS⟩)
      · rw [junction_of_lt (not_le.1 htT)]
        exact Or.inr (Or.inl ⟨_, rfl⟩)

/-- **Extension of the first path** (W4, the extended path is the first one): if `𝓔(α([0, a]), β([0, c]))`
holds and `α([0, a'])`, `a ≤ a'`, has some proper completion whose part after `a` avoids `β([0, c])`, then
`𝓔(α([0, a']), β([0, c]))`. -/
theorem hasOrderedProperCompletions_of_completion {a' : ℝ≥0}
    (h : HasOrderedProperCompletions α a β c) (h0 : (α 0).im = 0) (hβ0 : (β 0).im = 0)
    (hseed : (β 0).re ≤ (α 0).re) (haa' : a ≤ a') (hα'' : IsProperCompletion α a' α'')
    (htail : ∀ s, a ≤ s → ∀ y ≤ c, α'' s ≠ β y) : HasOrderedProperCompletions α a' β c := by
  obtain ⟨α', β', hα', hβ', hord⟩ := h
  have hα''a : IsProperCompletion α a α'' :=
    ⟨hα''.1, hα''.2.1, hα''.2.2.1, hα''.2.2.2.1, fun t ht => hα''.2.2.2.2 t (ht.trans haa')⟩
  obtain ⟨β'', hβ'', hord''⟩ :=
    exists_isProperCompletion_subset_closedLeftSide hα' hβ' hord h0 hβ0 hseed hα''a htail
  exact ⟨α'', β'', hα'', hβ'', hord''⟩

/-! ### Duality and reflection -/

/-- The closed right side of a curve closed along its lower vertical ray. -/
def closedRightSide (γ : ℝ≥0 → ℂ) : Set ℂ := rightSide γ ∪ seedRayClosure γ

/-- **Duality.** If `β'` lies in the closed left side of `α'` (seeds `β'(0) ≤ α'(0)` real), then `α'` lies in
the closed right side of `β'`. -/
theorem range_subset_closedRightSide (hα' : IsProperCurve α') (hβ' : IsProperCurve β')
    (h0 : (α' 0).im = 0) (hβ0 : (β' 0).im = 0) (hseed : (β' 0).re ≤ (α' 0).re)
    (hord : range β' ⊆ closedLeftSide α') : range α' ⊆ closedRightSide β' := by
  -- the closed second curve lies in the closed left side of the first
  have hS : seedRayClosure β' ⊆ closedLeftSide α' := by
    rintro z (hz | ⟨hre, him⟩)
    · exact hord hz
    · rw [hβ0] at him
      rcases him.lt_or_eq with hlt | heq
      · rcases hseed.lt_or_eq with hs | hs
        · exact Or.inl (lowerLeft_subset_leftSide hα'.2.2.1 h0 ⟨hre ▸ hs, hlt⟩)
        · exact Or.inr (Or.inr ⟨hre.trans hs, by rw [h0]; exact hlt.le⟩)
      · exact hord ⟨0, (eq_of_re_eq_of_im_eq_zero hre heq hβ0).symm⟩
  have hdisj := disjoint_leftSide_rightSide hα' h0
  have hRS : rightSide α' ⊆ (seedRayClosure β')ᶜ := fun z hzR hzS => by
    rcases hS hzS with h | h
    · exact Set.disjoint_left.1 hdisj h hzR
    · exact connectedComponentIn_subset _ _ hzR h
  have hRR : rightSide α' ⊆ rightSide β' := by
    have hx : rightRef α' ∈ rightSide β' :=
      lowerRight_subset_rightSide hβ'.2.2.1 hβ0 ⟨by simp [rightRef]; linarith, by simp [rightRef, h0]⟩
    have := isPreconnected_connectedComponentIn.subset_connectedComponentIn
      (rightRef_mem_rightSide hα'.2.2.1 h0) hRS
    rwa [← connectedComponentIn_eq hx] at this
  rintro _ ⟨t, rfl⟩
  by_cases hz : α' t ∈ seedRayClosure β'
  · exact Or.inr hz
  refine Or.inl ?_
  have hcl := seedRayClosure_subset_closure_rightSide hα' h0 (Or.inl ⟨t, rfl⟩)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (isClosed_seedRayClosure hβ').isOpen_compl _ hz
  obtain ⟨w, hwB, hwR⟩ := Metric.mem_closure_iff.1 hcl ε hε
  have hwR' := hRR hwB
  have := (convex_ball (α' t) ε).isPreconnected.subset_connectedComponentIn
    (show w ∈ ball (α' t) ε by rw [mem_ball, dist_comm]; exact hwR) hball
  rw [← connectedComponentIn_eq hwR'] at this
  exact this (mem_ball_self hε)

/-- The reflection `z ↦ −z̄` in the imaginary axis. -/
def refl (z : ℂ) : ℂ := -(starRingEnd ℂ z)

@[simp] theorem refl_re (z : ℂ) : (refl z).re = -z.re := by simp [refl]

@[simp] theorem refl_im (z : ℂ) : (refl z).im = z.im := by simp [refl]

@[simp] theorem refl_refl (z : ℂ) : refl (refl z) = z := by simp [refl]

theorem continuous_refl : Continuous refl := (continuous_conj).neg

theorem refl_injective : Function.Injective refl := fun z w h => by
  rw [← refl_refl z, h, refl_refl]

/-- The reflected curve. -/
def reflectCurve (γ : ℝ≥0 → ℂ) : ℝ≥0 → ℂ := fun t => refl (γ t)

@[simp] theorem reflectCurve_reflectCurve (γ : ℝ≥0 → ℂ) : reflectCurve (reflectCurve γ) = γ := by
  funext t; simp [reflectCurve]

theorem isProperCompletion_reflectCurve {γ γ' : ℝ≥0 → ℂ} {a : ℝ≥0} (h : IsProperCompletion γ a γ') :
    IsProperCompletion (reflectCurve γ) a (reflectCurve γ') := by
  refine ⟨continuous_refl.comp h.1, refl_injective.comp h.2.1, fun t => by simp [reflectCurve, h.2.2.1 t],
    ?_, fun t ht => by simp [reflectCurve, h.2.2.2.2 t ht]⟩
  simpa [reflectCurve, refl] using h.2.2.2.1

theorem refl_image_seedRayClosure_subset (γ : ℝ≥0 → ℂ) :
    refl '' seedRayClosure γ ⊆ seedRayClosure (reflectCurve γ) := by
  rintro _ ⟨z, ⟨t, rfl⟩ | ⟨hre, him⟩, rfl⟩
  · exact Or.inl ⟨t, rfl⟩
  · exact Or.inr ⟨by simp [reflectCurve, hre], by simpa [reflectCurve] using him⟩

theorem refl_image_rightSide_subset {γ : ℝ≥0 → ℂ} (hγ : ∀ t, 0 ≤ (γ t).im) (h0 : (γ 0).im = 0) :
    refl '' rightSide γ ⊆ leftSide (reflectCurve γ) := by
  have hx : γ 0 + 1 - I ∈ (seedRayClosure γ)ᶜ :=
    lowerRight_subset_compl hγ (right_ref_mem_lowerRight h0)
  have h1 := continuous_refl.continuousOn.image_connectedComponentIn_subset (s := (seedRayClosure γ)ᶜ) hx
  have h2 : refl '' (seedRayClosure γ)ᶜ ⊆ (seedRayClosure (reflectCurve γ))ᶜ := by
    rintro _ ⟨z, hz, rfl⟩ hzS
    have := refl_image_seedRayClosure_subset (reflectCurve γ) ⟨_, hzS, rfl⟩
    rw [refl_refl, reflectCurve_reflectCurve] at this
    exact hz this
  have hr : refl (γ 0 + 1 - I) = reflectCurve γ 0 - 1 - I := by
    apply Complex.ext
    · simp [reflectCurve]; ring
    · simp [reflectCurve, h0]
  rw [hr] at h1
  exact h1.trans (connectedComponentIn_mono _ h2)

/-- **Reflection symmetry of the order.** `𝓔(α([0, a]), β([0, c]))` for real seeds `β(0) ≤ α(0)` gives
`𝓔(ρβ([0, c]), ρα([0, a]))` for the reflection `ρ(z) = −z̄`. -/
theorem hasOrderedProperCompletions_reflect (h : HasOrderedProperCompletions α a β c) (h0 : (α 0).im = 0)
    (hβ0 : (β 0).im = 0) (hseed : (β 0).re ≤ (α 0).re) :
    HasOrderedProperCompletions (reflectCurve β) c (reflectCurve α) a := by
  obtain ⟨α', β', hα', hβ', hord⟩ := h
  have ha0 : α' 0 = α 0 := hα'.2.2.2.2 0 zero_le
  have hb0 : β' 0 = β 0 := hβ'.2.2.2.2 0 zero_le
  have hβ0' : (β' 0).im = 0 := by rw [hb0]; exact hβ0
  have hdual := range_subset_closedRightSide (isProperCurve_of_isProperCompletion hα')
    (isProperCurve_of_isProperCompletion hβ') (by rw [ha0]; exact h0) hβ0'
    (by rw [ha0, hb0]; exact hseed) hord
  refine ⟨reflectCurve β', reflectCurve α', isProperCompletion_reflectCurve hβ',
    isProperCompletion_reflectCurve hα', ?_⟩
  rintro _ ⟨t, rfl⟩
  rcases hdual ⟨t, rfl⟩ with hR | hS
  · exact Or.inl (refl_image_rightSide_subset hβ'.2.2.1 hβ0' ⟨_, hR, rfl⟩)
  · exact Or.inr (refl_image_seedRayClosure_subset β' ⟨_, hS, rfl⟩)

/-- **Extension of the second path** (W4, the extended path is the second one): if `𝓔(α([0, a]), β([0, c]))`
holds and `β([0, c'])`, `c ≤ c'`, has some proper completion whose part after `c` avoids `α([0, a])`, then
`𝓔(α([0, a]), β([0, c']))`. -/
theorem hasOrderedProperCompletions_of_completion_right {c' : ℝ≥0} {β'' : ℝ≥0 → ℂ}
    (h : HasOrderedProperCompletions α a β c) (h0 : (α 0).im = 0) (hβ0 : (β 0).im = 0)
    (hseed : (β 0).re ≤ (α 0).re) (hcc' : c ≤ c') (hβ'' : IsProperCompletion β c' β'')
    (htail : ∀ s, c ≤ s → ∀ x ≤ a, β'' s ≠ α x) : HasOrderedProperCompletions α a β c' := by
  have hr := hasOrderedProperCompletions_reflect h h0 hβ0 hseed
  have hr' := hasOrderedProperCompletions_of_completion hr (by simp [reflectCurve, hβ0])
    (by simp [reflectCurve, h0]) (by simp [reflectCurve, hseed]) hcc'
    (isProperCompletion_reflectCurve hβ'') fun s hs x hx h' => htail s hs x hx (refl_injective h')
  have := hasOrderedProperCompletions_reflect hr' (by simp [reflectCurve, hβ0])
    (by simp [reflectCurve, h0]) (by simp [reflectCurve, hseed])
  simpa using this

end Supp9B

end InteractingSLE
