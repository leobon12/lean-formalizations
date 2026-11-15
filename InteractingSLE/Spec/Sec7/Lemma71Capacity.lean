import InteractingSLE.Spec.Sec6.DrivingUnconditional
import InteractingSLE.Foundations.Loewner.HullFilling
import InteractingSLE.Foundations.SLE.SpaceFilling.Swallow
import InteractingSLE.Frozen.Spec.IsGeneratingTrace
import InteractingSLE.Spec.Dimension.TraceBridge
import InteractingSLE.Foundations.Loewner.ConformalImageLoewner

/-!
# Lemma 7.1: the capacity clock and the generating trace of the mapped pocket segment

Packet PROVE-LEMMA71. Specification §7.1, Lemma 7.1 and its proof (`source/spec/p193-240.md` L576–L586,
L596–L606, pp. 223–225), with Remark 6.14 (L478–L493, pp. 217–218).

The mapped middle-curve segment `η_ψ = ψ(η_C)` is "a continuous simple path in `ℍ̄`" from `0` that "tends to `∞`
at the end of its capacity lifetime" (Lemma 7.1). Remark 6.14 reduces it to Proposition 6.12: "That proposition
gives a continuous Loewner driver up to the terminal capacity time of `ψ(η_C)`". The proof of Lemma 7.1 then
excludes a finite terminal capacity: "Otherwise the globally defined admissible two-seed driving process would
have a bounded driver on that finite interval, and the elementary Loewner hull bounds would put the entire mapped
prefix in a bounded rectangle, contrary to its limit at `∞`" (p. 225).

This file proves the deterministic part of these two sentences. Let `γ : [0, ∞) → ℍ̄` be continuous and
injective with `γ 0 = 0`, `‖γ t‖ → ∞`, and real-boundary times with empty interior. Suppose every filled prefix
`fill(γ[0, t])` is a Loewner hull `K_s` of one continuous driver `W` defined on all of `[0, ∞)` (the globally
defined driving process). Then:

* `exists_clock_of_fwdHull_eq`: the capacity times `s = σ(t)` form a continuous strictly increasing clock with
  `σ 0 = 0` (Proposition 6.12 on every `[0, S]`, `Sec6.exists_driver_of_injOn`, and the uniqueness of the clock,
  `Sec6.eqOn_clock_and_driver_of_fwdHull_eq`);
* `not_bddAbove_clock`: **the terminal capacity is infinite**: a bounded clock would put every filled prefix in
  the bounded hull `K_c` of the driver on the finite interval `[0, c]` (`isBounded_fwdHull`), hence the whole path
  in a bounded set (`norm_le_of_forall_im_pos` handles the real-boundary times), contrary to `γ → ∞`;
* **`exists_isGeneratingTrace_of_fwdHull_eq`**: the clock is an order isomorphism `e` of `[0, ∞)`, and the
  capacity reparametrization `η = γ ∘ e⁻¹` is a continuous generating trace of `W` on `[0, ∞)` in the frozen
  sense (`IsGeneratingTrace (W ·) ⊤ η`) with `‖η s‖ → ∞`;
* **`exists_global_driver_iff`** (Proposition 6.12 on `[0, ∞)`): without a given driver, one continuous driver on
  `[0, ∞)` generates every filled prefix of `γ` if and only if the half-plane capacities of the prefixes are
  unbounded (the drivers of Proposition 6.12 on `[0, n + 1]` agree on overlaps and are glued; the converse is
  `not_bddAbove_clock`). So the probabilistic content of "its terminal capacity cannot be finite" is exactly the
  unboundedness of these capacities.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open QuantumZipper (H Hbar)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.Lemma71

variable {γ : ℝ → ℂ} {W : ℝ → ℝ}

/-- A path in `ℍ̄` whose real-boundary times have empty interior, and which is bounded by `R` at its
upper-half-plane times, is bounded by `R` at every positive time. -/
theorem norm_le_of_forall_im_pos {R : ℝ} (hc : ContinuousOn γ (Ici 0)) (hH : MapsTo γ (Ici 0) Hbar)
    (hR : interior {u ∈ Ici (0 : ℝ) | 0 < u ∧ (γ u).im = 0} = ∅)
    (hb : ∀ u, 0 < u → 0 < (γ u).im → ‖γ u‖ ≤ R) {u : ℝ} (hu : 0 < u) : ‖γ u‖ ≤ R := by
  by_contra hlt
  rw [not_le] at hlt
  have hcu : ContinuousAt γ u := hc.continuousAt (Ici_mem_nhds hu)
  have hev : ∀ᶠ v in 𝓝 u, R < ‖γ v‖ :=
    (continuous_norm.continuousAt.comp hcu).eventually (lt_mem_nhds hlt)
  have hev2 : ∀ᶠ v in 𝓝 u, 0 < v := lt_mem_nhds hu
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 (hev.and hev2)
  have hsub : Ioo (u - ε) (u + ε) ⊆ {v ∈ Ici (0 : ℝ) | 0 < v ∧ (γ v).im = 0} := by
    intro v hv
    have hd : dist v u < ε := by
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith [hv.1, hv.2]
    obtain ⟨h1, h2⟩ := hball hd
    refine ⟨h2.le, h2, ?_⟩
    have him : 0 ≤ (γ v).im := hH (show v ∈ Ici (0 : ℝ) from h2.le)
    rcases him.lt_or_eq with h | h
    · exact absurd (hb v h2 h) (not_le.2 h1)
    · exact h.symm
  have hint : Ioo (u - ε) (u + ε) ⊆ interior {v ∈ Ici (0 : ℝ) | 0 < v ∧ (γ v).im = 0} :=
    interior_maximal hsub isOpen_Ioo
  rw [hR] at hint
  exact hint (show u ∈ Ioo (u - ε) (u + ε) from ⟨by linarith, by linarith⟩)

/-- A path with `‖γ t‖ → ∞` has unbounded futures (the hypothesis of `Sec6.exists_driver_of_injOn`). -/
theorem not_isBounded_image_Ici (hinf : Tendsto (fun t => ‖γ t‖) atTop atTop) :
    ∀ u ∈ Ici (0 : ℝ), ¬ Bornology.IsBounded (γ '' (Ici 0 ∩ Ici u)) := by
  intro u _ hb
  obtain ⟨M, hM⟩ := hb.subset_closedBall 0
  obtain ⟨t, ht1, ht2⟩ := ((hinf.eventually_gt_atTop M).and (eventually_ge_atTop (max u 0))).exists
  have hmem : γ t ∈ closedBall (0 : ℂ) M :=
    hM ⟨t, ⟨le_trans (le_max_right u 0) ht2, le_trans (le_max_left u 0) ht2⟩, rfl⟩
  rw [mem_closedBall_zero_iff] at hmem
  linarith

/-- **The capacity clock** (Remark 6.14 with Proposition 6.12). If every filled prefix `fill(γ[0, t])` of a
continuous simple path in `ℍ̄` (real-boundary times with empty interior, unbounded futures) is a Loewner hull of
the continuous driver `W`, then the corresponding capacity times form a continuous strictly increasing clock `σ`
with `σ 0 = 0` and `K_{σ(t)} = fill(γ[0, t])`. -/
theorem exists_clock_of_fwdHull_eq (hW : Continuous W) (hW0 : W 0 = 0)
    (hc : ContinuousOn γ (Ici 0)) (hinj : InjOn γ (Ici 0)) (hH : MapsTo γ (Ici 0) Hbar)
    (h0 : γ 0 = 0) (hunb : ∀ u ∈ Ici (0 : ℝ), ¬ Bornology.IsBounded (γ '' (Ici 0 ∩ Ici u)))
    (hR : interior {u ∈ Ici (0 : ℝ) | 0 < u ∧ (γ u).im = 0} = ∅)
    (hK : ∀ t, 0 ≤ t → ∃ s, 0 ≤ s ∧ QuantumZipper.fwdHull W s = fillH (γ '' Icc 0 t)) :
    ∃ σ : ℝ → ℝ, σ 0 = 0 ∧ StrictMonoOn σ (Ici 0) ∧ ContinuousOn σ (Ici 0) ∧
      ∀ t, 0 ≤ t → 0 ≤ σ t ∧ QuantumZipper.fwdHull W (σ t) = fillH (γ '' Icc 0 t) := by
  classical
  set σ : ℝ → ℝ := fun t => if ht : 0 ≤ t then Classical.choose (hK t ht) else 0 with hσdef
  have hσ : ∀ t, 0 ≤ t → 0 ≤ σ t ∧ QuantumZipper.fwdHull W (σ t) = fillH (γ '' Icc 0 t) :=
    fun t ht => by
      simp only [hσdef, ht, ↓reduceDIte]
      exact Classical.choose_spec (hK t ht)
  -- on every `[0, S]` the clock is Proposition 6.12's
  have hloc : ∀ S, 0 < S → ∃ σS : ℝ → ℝ, σS 0 = 0 ∧ StrictMonoOn σS (Icc 0 S) ∧
      ContinuousOn σS (Icc 0 S) ∧ EqOn σS σ (Icc 0 S) := by
    intro S hS
    obtain ⟨WS, hWSc, hWS0, σS, hσS0, hσSm, hσSc, hσS⟩ :=
      Sec6.exists_driver_of_injOn ordConnected_Ici hc hinj hH self_mem_Ici h0 hunb hR hS
        (show S ∈ Ici (0 : ℝ) from hS.le)
    refine ⟨σS, hσS0, hσSm, hσSc, ?_⟩
    exact (Sec6.eqOn_clock_and_driver_of_fwdHull_eq hWSc hW hWS0 hW0 hS.le hσS0 hσSm.monotoneOn hσSc
      (fun t ht => (hσ t ht.1).1) fun t ht => by rw [(hσS t ht).2.1, (hσ t ht.1).2]).1
  refine ⟨σ, ?_, ?_, ?_, hσ⟩
  · obtain ⟨σS, h0', -, -, heq⟩ := hloc 1 one_pos
    rw [← heq ⟨le_rfl, zero_le_one⟩, h0']
  · intro a ha b hb hab
    have hb0 : (0 : ℝ) ≤ b := hb
    obtain ⟨σS, -, hm, -, heq⟩ := hloc (b + 1) (by linarith)
    have ha' : a ∈ Icc 0 (b + 1) := ⟨ha, by linarith⟩
    have hb' : b ∈ Icc 0 (b + 1) := ⟨hb0, by linarith⟩
    rw [← heq ha', ← heq hb']
    exact hm ha' hb' hab
  · intro t ht
    have ht0 : (0 : ℝ) ≤ t := ht
    obtain ⟨σS, -, -, hcS, heq⟩ := hloc (t + 1) (by linarith)
    have hnhds : Icc 0 (t + 1) ∈ 𝓝[Ici 0] t := by
      rw [← Ici_inter_Iic]
      exact Filter.inter_mem self_mem_nhdsWithin
        (mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds (by linarith)))
    have hcw : ContinuousWithinAt σS (Ici 0) t :=
      (hcS t ⟨ht0, by linarith⟩).mono_of_mem_nhdsWithin hnhds
    refine hcw.congr_of_eventuallyEq ?_ (heq ⟨ht0, by linarith⟩).symm
    exact Filter.mem_of_superset hnhds fun r hr => (heq hr).symm

/-- **The terminal capacity is infinite** (proof of Lemma 7.1, p. 225). If the filled prefixes of a path tending
to `∞` are the hulls `K_{σ(t)}` of one continuous driver, the clock `σ` is unbounded: on a bounded clock the hulls
stay in the bounded hull `K_c` of the driver on the finite interval `[0, c]`, so the path would be bounded. -/
theorem not_bddAbove_clock {σ : ℝ → ℝ} (hW : Continuous W) (hc : ContinuousOn γ (Ici 0))
    (hH : MapsTo γ (Ici 0) Hbar) (h0 : γ 0 = 0) (hinf : Tendsto (fun t => ‖γ t‖) atTop atTop)
    (hR : interior {u ∈ Ici (0 : ℝ) | 0 < u ∧ (γ u).im = 0} = ∅)
    (hσ : ∀ t, 0 ≤ t → QuantumZipper.fwdHull W (σ t) = fillH (γ '' Icc 0 t)) :
    ¬ BddAbove (σ '' Ici 0) := by
  rintro ⟨c, hcb⟩
  obtain ⟨R, hRb⟩ := (isBounded_fwdHull hW c).subset_closedBall 0
  have hupper : ∀ u, 0 < u → 0 < (γ u).im → ‖γ u‖ ≤ R := by
    intro u hu him
    have hmem : γ u ∈ fillH (γ '' Icc 0 u) :=
      ⟨him, Or.inl (subset_closure ⟨u, ⟨hu.le, le_rfl⟩, rfl⟩)⟩
    rw [← hσ u hu.le] at hmem
    have hle : σ u ≤ c := hcb ⟨u, (show u ∈ Ici (0 : ℝ) from hu.le), rfl⟩
    have := hRb ((QuantumZipper.fwdHull_mono (W := W)).1 hle hmem)
    rwa [mem_closedBall_zero_iff] at this
  have hall : ∀ u, 0 ≤ u → ‖γ u‖ ≤ max R 0 := by
    intro u hu
    rcases hu.eq_or_lt with rfl | hu
    · rw [h0, norm_zero]
      exact le_max_right _ _
    · exact (norm_le_of_forall_im_pos hc hH hR hupper hu).trans (le_max_left _ _)
  obtain ⟨t, ht1, ht2⟩ := ((hinf.eventually_gt_atTop (max R 0)).and (eventually_ge_atTop 0)).exists
  linarith [hall t ht2]

/-- **The generating trace of the mapped segment** (Lemma 7.1: "It is a continuous simple path in `ℍ̄` and tends
to `∞` at the end of its capacity lifetime"; Remark 6.14 with Proposition 6.12). Let `γ` be a continuous simple path
in `ℍ̄` from `0` with `‖γ t‖ → ∞` and real-boundary times with empty interior, and let every filled prefix of `γ`
be a Loewner hull of the continuous driver `W` on `[0, ∞)`. Then the capacity clock is an order isomorphism `e` of
`[0, ∞)`, `K_{e(t)} = fill(γ[0, t])`, and the capacity reparametrization `γ ∘ e⁻¹` is a continuous generating trace
of `W` on `[0, ∞)` tending to `∞`. -/
theorem exists_isGeneratingTrace_of_fwdHull_eq (hW : Continuous W) (hW0 : W 0 = 0)
    (hc : ContinuousOn γ (Ici 0)) (hinj : InjOn γ (Ici 0)) (hH : MapsTo γ (Ici 0) Hbar)
    (h0 : γ 0 = 0) (hinf : Tendsto (fun t => ‖γ t‖) atTop atTop)
    (hR : interior {u ∈ Ici (0 : ℝ) | 0 < u ∧ (γ u).im = 0} = ∅)
    (hK : ∀ t, 0 ≤ t → ∃ s, 0 ≤ s ∧ QuantumZipper.fwdHull W s = fillH (γ '' Icc 0 t)) :
    ∃ e : ℝ≥0 ≃o ℝ≥0, (∀ t : ℝ≥0, QuantumZipper.fwdHull W (e t) = fillH (γ '' Icc 0 t)) ∧
      IsGeneratingTrace (fun s : ℝ≥0 => W s) ⊤ (fun s => γ (e.symm s)) ∧
      Tendsto (fun s : ℝ≥0 => ‖γ (e.symm s)‖) atTop atTop := by
  obtain ⟨σ, hσ0, hσm, hσc, hσ⟩ := exists_clock_of_fwdHull_eq hW hW0 hc hinj hH h0
    (not_isBounded_image_Ici hinf) hR hK
  have hunbd := not_bddAbove_clock hW hc hH h0 hinf hR fun t ht => (hσ t ht).2
  set σ' : ℝ≥0 → ℝ≥0 := fun t => ⟨σ t, (hσ t t.2).1⟩ with hσ'
  have hσ'm : StrictMono σ' := fun a b hab => by
    show σ a < σ b
    exact hσm (show (a : ℝ) ∈ Ici 0 from a.2) (show (b : ℝ) ∈ Ici 0 from b.2) hab
  have hσ's : Function.Surjective σ' := by
    intro s
    obtain ⟨T, hT0, hTs⟩ : ∃ T, 0 ≤ T ∧ (s : ℝ) ≤ σ T := by
      by_contra hne
      push Not at hne
      exact hunbd ⟨s, by rintro _ ⟨T, hT, rfl⟩; exact (hne T hT).le⟩
    have hivt := intermediate_value_Icc hT0 (hσc.mono Icc_subset_Ici_self)
    rw [hσ0] at hivt
    obtain ⟨t, ht, hts⟩ := hivt ⟨s.2, hTs⟩
    exact ⟨⟨t, ht.1⟩, Subtype.ext hts⟩
  set e : ℝ≥0 ≃o ℝ≥0 := StrictMono.orderIsoOfSurjective σ' hσ'm hσ's with he
  have heσ : ∀ x : ℝ≥0, (e x : ℝ) = σ x := fun x => rfl
  have he0 : e.symm 0 = 0 := by
    have : e 0 = 0 := NNReal.eq (by rw [heσ, NNReal.coe_zero, hσ0])
    rw [e.symm_apply_eq, this]
  have hcont : Continuous fun s : ℝ≥0 => γ (e.symm s) :=
    hc.comp_continuous (NNReal.continuous_coe.comp e.symm.continuous) fun s => (e.symm s).2
  have himg : ∀ t : ℝ≥0, (fun s : ℝ≥0 => γ (e.symm s)) '' Icc 0 t = γ '' Icc 0 (e.symm t : ℝ) := by
    intro t
    ext z
    constructor
    · rintro ⟨s, ⟨-, hst⟩, rfl⟩
      exact ⟨e.symm s, ⟨(e.symm s).2, by exact_mod_cast e.symm.monotone hst⟩, rfl⟩
    · rintro ⟨u, ⟨hu0, hut⟩, rfl⟩
      refine ⟨e u.toNNReal, ⟨zero_le, ?_⟩, ?_⟩
      · exact (e.le_symm_apply).1 (Real.toNNReal_le_iff_le_coe.2 hut)
      · show γ (e.symm (e u.toNNReal) : ℝ) = γ u
        rw [e.symm_apply_apply, Real.coe_toNNReal _ hu0]
  refine ⟨e, fun t => (hσ t t.2).2, ⟨?_, hcont.continuousOn, fun t _ => ?_⟩, ?_⟩
  · simp only [he0, NNReal.coe_zero, h0]
  · have hdrv : QuantumZipper.fwdHull (fun s : ℝ => (fun s : ℝ≥0 => W s) s.toNNReal) t =
        QuantumZipper.fwdHull W t :=
      fwdHull_congr_drive (fun s hs => by simp only [Real.coe_toNNReal _ hs]) _
    have hK' : QuantumZipper.fwdHull W t = fillH (γ '' Icc 0 (e.symm t : ℝ)) := by
      rw [← (hσ (e.symm t : ℝ) (e.symm t).2).2, ← heσ, e.apply_symm_apply]
    rw [hdrv, hK', himg]
    exact isFilling_fillH ((isCompact_Icc).image_of_continuousOn (hc.mono Icc_subset_Ici_self))
  · exact hinf.comp (NNReal.tendsto_coe_atTop.2 e.symm.tendsto_atTop)

/-! ### Proposition 6.12 on `[0, ∞)`: a global driver exists exactly when the terminal capacity is infinite -/

/-- The half-plane capacity of a Loewner hull `K_s` is `2s`. -/
theorem hcapSet_eq_of_fwdHull_eq (hW : Continuous W) (hW0 : W 0 = 0) {s : ℝ} (hs : 0 ≤ s)
    {A : Set ℂ} (h : QuantumZipper.fwdHull W s = A) : ConformalImage.hcapSet A = 2 * s := by
  subst h
  rw [ConformalImage.hcapSet_eq (isHPHull_fwdHull hW hs), hcap_fwdHull hW hW0 hs]

/-- **Proposition 6.12 on `[0, ∞)`** (Remark 6.14: "That proposition gives a continuous Loewner driver up to the
terminal capacity time of `ψ(η_C)`"; proof of Lemma 7.1: "Its terminal capacity cannot be finite"). For a continuous
simple path `γ` in `ℍ̄` from `0` tending to `∞` whose real-boundary times have empty interior, one continuous driver
on `[0, ∞)` generates every filled prefix `fill(γ[0, t])` if and only if the capacities of these prefixes are
unbounded. (`⇐`: the drivers of Proposition 6.12 on the intervals `[0, n + 1]` agree on overlaps and are glued;
`⇒`: `not_bddAbove_clock`.) -/
theorem exists_global_driver_iff (hc : ContinuousOn γ (Ici 0)) (hinj : InjOn γ (Ici 0))
    (hH : MapsTo γ (Ici 0) Hbar) (h0 : γ 0 = 0) (hinf : Tendsto (fun t => ‖γ t‖) atTop atTop)
    (hR : interior {u ∈ Ici (0 : ℝ) | 0 < u ∧ (γ u).im = 0} = ∅) :
    (∃ W : ℝ → ℝ, Continuous W ∧ W 0 = 0 ∧
      ∀ t, 0 ≤ t → ∃ s, 0 ≤ s ∧ QuantumZipper.fwdHull W s = fillH (γ '' Icc 0 t)) ↔
      ¬ BddAbove ((fun t => ConformalImage.hcapSet (fillH (γ '' Icc 0 t))) '' Ici 0) := by
  have hunb := not_isBounded_image_Ici hinf
  constructor
  · rintro ⟨W, hW, hW0, hK⟩ ⟨c, hcb⟩
    obtain ⟨σ, -, -, -, hσ⟩ := exists_clock_of_fwdHull_eq hW hW0 hc hinj hH h0 hunb hR hK
    refine not_bddAbove_clock hW hc hH h0 hinf hR (fun t ht => (hσ t ht).2) ⟨c / 2, ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    have h1 : ConformalImage.hcapSet (fillH (γ '' Icc 0 t)) ≤ c := hcb ⟨t, ht, rfl⟩
    rw [hcapSet_eq_of_fwdHull_eq hW hW0 (hσ t ht).1 (hσ t ht).2] at h1
    linarith
  · intro hcap
    -- Proposition 6.12 on `[0, n + 1]`
    have hP : ∀ n : ℕ, ∃ Wn : ℝ → ℝ, Continuous Wn ∧ Wn 0 = 0 ∧ ∃ σn : ℝ → ℝ, σn 0 = 0 ∧
        StrictMonoOn σn (Icc 0 ((n : ℝ) + 1)) ∧ ContinuousOn σn (Icc 0 ((n : ℝ) + 1)) ∧
        ∀ t ∈ Icc 0 ((n : ℝ) + 1), 0 ≤ σn t ∧
          QuantumZipper.fwdHull Wn (σn t) = fillH (γ '' Icc 0 t) := by
      intro n
      obtain ⟨Wn, h1, h2, σn, h3, h4, h5, h6⟩ := Sec6.exists_driver_of_injOn ordConnected_Ici hc hinj hH
        self_mem_Ici h0 hunb hR (show (0 : ℝ) < n + 1 by positivity)
        (show (n : ℝ) + 1 ∈ Ici 0 from mem_Ici.2 (by positivity))
      exact ⟨Wn, h1, h2, σn, h3, h4, h5, fun t ht => ⟨(h6 t ht).1, (h6 t ht).2.1⟩⟩
    choose Wn hWc hW0 σn hσ0 hσm hσc hσ using hP
    -- the drivers agree on overlaps
    have hcons : ∀ m n : ℕ, m ≤ n → EqOn (Wn m) (Wn n) (Icc 0 (σn m ((m : ℝ) + 1))) := by
      intro m n hmn
      have hmn' : (m : ℝ) + 1 ≤ n + 1 := by exact_mod_cast Nat.succ_le_succ hmn
      refine (Sec6.eqOn_clock_and_driver_of_fwdHull_eq (hWc m) (hWc n) (hW0 m) (hW0 n)
        (by positivity) (hσ0 m) (hσm m).monotoneOn (hσc m)
        (fun t ht => (hσ n t ⟨ht.1, ht.2.trans hmn'⟩).1) fun t ht => ?_).2
      rw [(hσ m t ht).2, (hσ n t ⟨ht.1, ht.2.trans hmn'⟩).2]
    -- the clocks are unbounded
    have hunbc : ∀ s : ℝ, ∃ n : ℕ, s < σn n ((n : ℝ) + 1) := by
      intro s
      by_contra hne
      push Not at hne
      refine hcap ⟨2 * s, ?_⟩
      rintro _ ⟨t, ht, rfl⟩
      have ht0 : (0 : ℝ) ≤ t := ht
      set n := ⌈t⌉₊ with hn
      have htn : t ≤ (n : ℝ) + 1 := (Nat.le_ceil t).trans (by linarith)
      have hmem : t ∈ Icc 0 ((n : ℝ) + 1) := ⟨ht0, htn⟩
      have hmem' : (n : ℝ) + 1 ∈ Icc 0 ((n : ℝ) + 1) := ⟨by positivity, le_rfl⟩
      show ConformalImage.hcapSet (fillH (γ '' Icc 0 t)) ≤ 2 * s
      rw [hcapSet_eq_of_fwdHull_eq (hWc n) (hW0 n) (hσ n t hmem).1 (hσ n t hmem).2]
      have := (hσm n).monotoneOn hmem hmem' htn
      linarith [hne n]
    classical
    set N : ℝ → ℕ := fun s => Nat.find (hunbc (max s 0)) with hN
    set W : ℝ → ℝ := fun s => Wn (N s) (max s 0) with hWdef
    have hkey : ∀ (n : ℕ) (s : ℝ), max s 0 < σn n ((n : ℝ) + 1) → W s = Wn n (max s 0) := by
      intro n s hs
      have hle : N s ≤ n := Nat.find_min' (hunbc (max s 0)) hs
      have hspec : max s 0 < σn (N s) ((N s : ℝ) + 1) := Nat.find_spec (hunbc (max s 0))
      exact hcons (N s) n hle ⟨le_max_right s 0, hspec.le⟩
    refine ⟨W, ?_, ?_, ?_⟩
    · refine continuous_iff_continuousAt.2 fun s₀ => ?_
      obtain ⟨n, hn⟩ := hunbc (max s₀ 0)
      have hopen : IsOpen {s : ℝ | max s 0 < σn n ((n : ℝ) + 1)} :=
        isOpen_lt (continuous_id.max continuous_const) continuous_const
      have hev : (fun s => Wn n (max s 0)) =ᶠ[𝓝 s₀] W :=
        Filter.mem_of_superset (hopen.mem_nhds hn) fun s hs => (hkey n s hs).symm
      exact ((hWc n).comp (continuous_id.max continuous_const)).continuousAt.congr hev
    · obtain ⟨n, hn⟩ := hunbc 0
      rw [hkey n 0 (by simpa using hn), max_self, hW0 n]
    · intro t ht
      set n := ⌈t⌉₊ with hnd
      have htn : t < (n : ℝ) + 1 := (Nat.le_ceil t).trans_lt (by linarith)
      have hmem : t ∈ Icc 0 ((n : ℝ) + 1) := ⟨ht, htn.le⟩
      have hmem' : (n : ℝ) + 1 ∈ Icc 0 ((n : ℝ) + 1) := ⟨by positivity, le_rfl⟩
      have hlt : σn n t < σn n ((n : ℝ) + 1) := (hσm n) hmem hmem' htn
      refine ⟨σn n t, (hσ n t hmem).1, ?_⟩
      rw [← (hσ n t hmem).2]
      refine fwdHull_eq_of_eqOn (hσ n t hmem).1 (t₂ := (σn n t + σn n ((n : ℝ) + 1)) / 2)
        (by linarith) fun r hr => ?_
      have hr' : max r 0 = r := max_eq_left hr.1
      rw [hkey n r (by rw [hr']; linarith [hr.2]), hr']

end InteractingSLE.Sec7.Lemma71
