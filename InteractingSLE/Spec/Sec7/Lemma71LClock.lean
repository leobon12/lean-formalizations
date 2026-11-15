/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma71KSpace
import InteractingSLE.Spec.Sec7.Lemma71JRule

/-!
# Lemma 7.1: the visit clock of the middle curve through the pocket

Packet PROVE-LEMMA71L. Specification §7.1 (`source/spec/p193-240.md` L576–L606, pp. 223–225): "if `γ` visits `D` at
all, it does so between these two first hits and has `γ([σ_D, τ_D]) ⊆ D̄`; […] this proves the asserted traversal,
including that it does not return after `τ_D`."

For the mapped segment `Γ(u) = Ψ(M̃(segClock σ τ u))` of PROVE-LEMMA71K (`Lemma71K.isSegCurve_of_isMarkedPocket`), the
original time at the mapped time `u` is the **visit clock** `κ(u) = arcTime (segClock σ τ u)`. This file proves the
traversal hypotheses that PROVE-LEMMA71J's capacity rule (`Lemma71Pin.levelRule_capFamily_eq`) asks for, collected in
`IsVisitClock`, and the two facts about the closing point `y₀ = α̃ b` that the capacity stopping time needs (`EndOK`):
the middle curve stays away from `y₀` before every finite clock time, and a time before which it stays away from `y₀`
bounds the mapped time.

* `visitClock`, `IsVisitClock`, `EndOK` (definitions);
* **`visitClock_of_isMarkedPocket`** (deterministic).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric Complex Bornology
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec7.Lemma71L

open QuantumZipper (H Hbar)
open QuantumZipper.CA (cayley cayleyInv)
open Lemma71K Sec6

/-- The original time of the middle curve `M` at the mapped time `u` of its traversal of the closed disc pocket `U`. -/
def visitClock (M : ℝ≥0 → ℂ) (U : Set ℂ) (u : ℝ) : ℝ :=
  WangWu.arcTime (Lemma71.segClock (openTime M U) (closeTime M U) u)

/-- **A visit clock** of the curve `γ` through the open pocket `C`, for the chart `F` and the mapped segment `Γ`: the
hypotheses of `Lemma71Pin.levelRule_capFamily_eq` on the clock `κ` (continuous, strictly increasing, `κ 0 ≥ 0`; `F`
tends to `Γ u` at `γ (κ u)`; every visit is a clock time; visits are dense in the mapped time). -/
def IsVisitClock (C : Set ℂ) (F : ℂ → ℂ) (γ : ℝ≥0 → ℂ) (Γ : ℝ → ℂ) (κ : ℝ → ℝ) : Prop :=
  ContinuousOn κ (Ici 0) ∧ StrictMonoOn κ (Ici 0) ∧ 0 ≤ κ 0 ∧
    (∀ u, 0 ≤ u → Tendsto F (𝓝[C] (γ (κ u).toNNReal)) (𝓝 (Γ u))) ∧
    (∀ t : ℝ≥0, γ t ∈ C → ∃ u, 0 ≤ u ∧ κ u = t) ∧
    (∀ u₁ u₂, 0 ≤ u₁ → u₁ < u₂ → ∃ u ∈ Ioo u₁ u₂, γ (κ u).toNNReal ∈ C)

/-- **The end condition** at the disc point `Y`: the Cayley images of the coordinates `c q`, `q ≤ T`, stay a positive
distance away from `Y`. -/
def EndOK (Y : ℂ) (T : ℝ≥0∞) (c : ℚ≥0 → ℂ) : Prop :=
  ∃ m : ℕ, ∀ q : ℚ≥0, ((q : ℝ≥0) : ℝ≥0∞) ≤ T → 1 / ((m : ℝ) + 1) ≤ dist (cayley (c q)) Y

theorem EndOK.mono {Y : ℂ} {T T' : ℝ≥0∞} {c : ℚ≥0 → ℂ} (h : EndOK Y T c) (hT : T' ≤ T) : EndOK Y T' c := by
  obtain ⟨m, hm⟩ := h
  exact ⟨m, fun q hq => hm q (hq.trans hT)⟩

theorem endOK_congr {Y : ℂ} {T : ℝ≥0∞} {c c' : ℚ≥0 → ℂ}
    (h : ∀ q : ℚ≥0, ((q : ℝ≥0) : ℝ≥0∞) ≤ T → c q = c' q) : EndOK Y T c ↔ EndOK Y T c' := by
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨m, fun q hq => by rw [← h q hq]; exact hm q hq⟩
  · rintro ⟨m, hm⟩
    exact ⟨m, fun q hq => by rw [h q hq]; exact hm q hq⟩

theorem measurableSet_endOK {X : Type*} [MeasurableSpace X] {Y : X → ℂ} (hY : Measurable Y)
    {T : X × (ℚ≥0 → ℂ) → ℝ≥0∞} (hT : Measurable T) :
    MeasurableSet {z : X × (ℚ≥0 → ℂ) | EndOK (Y z.1) (T z) z.2} := by
  have heq : {z : X × (ℚ≥0 → ℂ) | EndOK (Y z.1) (T z) z.2} = ⋃ m : ℕ, ⋂ q : ℚ≥0,
      ({z : X × (ℚ≥0 → ℂ) | ((q : ℝ≥0) : ℝ≥0∞) ≤ T z}ᶜ ∪
        {z | 1 / ((m : ℝ) + 1) ≤ dist (cayley (z.2 q)) (Y z.1)}) := by
    ext z
    simp only [EndOK, mem_ofPred_eq, mem_iUnion, mem_iInter, mem_union, mem_compl_iff]
    refine exists_congr fun m => forall_congr' fun q => ?_
    tauto
  rw [heq]
  refine MeasurableSet.iUnion fun m => MeasurableSet.iInter fun q => ?_
  refine (measurableSet_le measurable_const hT).compl.union (measurableSet_le measurable_const ?_)
  have hc : Measurable fun z : X × (ℚ≥0 → ℂ) => cayley (z.2 q) := by
    have hq : Measurable fun z : X × (ℚ≥0 → ℂ) => z.2 q := (measurable_pi_apply q).comp measurable_snd
    have : cayley = fun w : ℂ => (w - I) / (w + I) := rfl
    rw [this]
    exact (hq.sub measurable_const).div (hq.add measurable_const)
  exact hc.dist (hY.comp measurable_fst)

/-! ### The disc time -/

theorem discTime_le_discTime {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    WangWu.discTime x ≤ WangWu.discTime y := by
  have hy : 0 ≤ y := hx.trans hxy
  rw [WangWu.discTime, WangWu.discTime, div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

theorem continuousOn_discTime : ContinuousOn WangWu.discTime (Ici 0) := by
  refine continuousOn_id.div (continuousOn_const.add continuousOn_id) fun x hx => ?_
  have : (0 : ℝ) ≤ x := hx
  show (1 : ℝ) + x ≠ 0
  linarith

/-! ### The visit clock of a marked pocket -/

/-- **The traversal of a marked pocket along the visit clock** (Lemma 7.1, pp. 223–224; deterministic). Under the
hypotheses of `Lemma71K.isSegCurve_of_isMarkedPocket`, for a middle curve in `ℍ̄` and a chart `F = Ψ ∘ cayley` of the
pocket onto `ℍ`: the visit clock `κ = visitClock M (closure (cayley '' C))` is a visit clock of `M` through `C`
for `F` and the mapped segment `Γ u = Ψ (segPt M … u)`; the middle curve stays away from the closing point `α̃ b`
before every clock time; and a finite time before which it stays away from `α̃ b` bounds the mapped times. -/
theorem visitClock_of_isMarkedPocket {R M L : ℝ≥0 → ℂ}
    (h : WangWu.IsOrderedArcs (Lemma71I.realPath R) (Lemma71I.realPath M) (Lemma71I.realPath L))
    (hcR : interior {t ∈ Ici (0 : ℝ) | Lemma71I.realPath M t ∈ WangWu.arcRange (Lemma71I.realPath R)} = ∅)
    (hcL : interior {t ∈ Ici (0 : ℝ) | Lemma71I.realPath M t ∈ WangWu.arcRange (Lemma71I.realPath L)} = ∅)
    {C : Set ℂ} (hC : C ∈ betweenComponents (range R) (range L)) {a b : ℝ} (hM : IsMarkedPocket R C a b)
    {Ψ : ℂ → ℂ} (hΨc : ContinuousOn Ψ (closure (cayley '' C) \ {wallPt R b}))
    (hΨi : InjOn Ψ (closure (cayley '' C) \ {wallPt R b}))
    (hΨH : MapsTo Ψ (closure (cayley '' C) \ {wallPt R b}) Hbar) (hΨ0 : Ψ (wallPt R a) = 0)
    (hΨinf : Tendsto (fun x => ‖Ψ x‖) (𝓝[closure (cayley '' C) \ {wallPt R b}] (wallPt R b)) atTop)
    (hCo : IsOpen C) (hCH : C ⊆ H) (hMH : ∀ t, M t ∈ Hbar) {F : ℂ → ℂ} (hF : ∀ x ∈ C, F x = Ψ (cayley x))
    (hFm : ∀ z ∈ C, F z ∈ H) (hFs : ∀ w ∈ H, ∃ z ∈ C, F z = w) :
    IsVisitClock C F M (fun u => Ψ (segPt M (closure (cayley '' C)) u)) (visitClock M (closure (cayley '' C))) ∧
      (∀ u, 0 ≤ u → cayley (M (visitClock M (closure (cayley '' C)) u).toNNReal) =
        segPt M (closure (cayley '' C)) u) ∧
      (∀ u, 0 ≤ u → 0 < (Ψ (segPt M (closure (cayley '' C)) u)).im →
        M (visitClock M (closure (cayley '' C)) u).toNNReal ∈ C) ∧
      (∀ u, 0 ≤ u →
        EndOK (wallPt R b) (ENNReal.ofReal (visitClock M (closure (cayley '' C)) u)) (Sec6.pathCoord M)) ∧
      (∀ T : ℝ≥0, EndOK (wallPt R b) T (Sec6.pathCoord M) →
        ∃ U, ∀ u, 0 ≤ u → visitClock M (closure (cayley '' C)) u ≤ T → u ≤ U) := by
  have hΨC : ∀ z ∈ C, Ψ (cayley z) ∈ H := fun z hz => by rw [← hF z hz]; exact hFm z hz
  obtain ⟨-, -, -, hsegE, hsc, -⟩ := isSegCurve_of_isMarkedPocket h hcR hcL hC hM hΨc hΨi hΨH hΨ0 hΨinf hΨC
  -- the traversal data, as in `isSegCurve_of_isMarkedPocket`
  have hC' := hC
  rw [← Lemma71I.arcRange_realPath R, ← Lemma71I.arcRange_realPath L] at hC'
  obtain ⟨a₁, b₁, hg, hCU, σ, τ, hσ0, hστ, hτ1, -, hτb, hin, hout, -⟩ := h.traverse_disc hcR hcL hC'
  have hα := h.right.isDiscCrosscut_toDisc
  have hβ := h.left.isDiscCrosscut_toDisc
  have hμ := h.middle.isDiscCrosscut_toDisc
  have hord' := (WangWu.disjoint_rightSideOf_iff h.right h.left).1 h.right_left
  set U := cayley '' C with hU
  rw [← hCU] at hin hout
  have hI₁ := wallTimes_eq_Icc_of_contactGap hα hβ hord' hg
  rw [← hCU] at hI₁
  obtain ⟨-, -, -, hI, -, -, hpb, -⟩ := hM
  have hIeq : Icc a₁ b₁ = Icc a b := hI₁.symm.trans hI
  obtain ⟨-, hb₁⟩ := (Icc_eq_Icc_iff hg.2.2.1.le).1 hIeq
  rw [hb₁] at hτb
  have hIM : {t ∈ Icc (0 : ℝ) 1 | wallPt M t ∈ closure U} = Icc σ τ := by
    ext t
    constructor
    · rintro ⟨ht01, htU⟩
      by_contra hnot
      exact hout t ht01 hnot htU
    · intro ht
      exact ⟨⟨hσ0.trans ht.1, ht.2.trans hτ1⟩, hin t ht⟩
  obtain ⟨eσ, eτ⟩ := openTime_closeTime_eq hσ0 hστ hτ1 hIM
  set q := wallPt R b with hqdef
  have hDo : IsOpen U := Lemma71F.isOpen_cayley_image hCo hCH
  have hqU : q ∉ U := by
    have hpb' := hpb
    rw [hDo.frontier_eq] at hpb'
    exact hpb'.2
  have hUE : U ⊆ closure U \ {q} := fun x hx => ⟨subset_closure hx, fun hxq => hqU (mem_singleton_iff.1 hxq ▸ hx)⟩
  have hηq : WangWu.toDisc (Lemma71I.realPath M) τ = q := hτb
  have hτ01 : τ ∈ Icc (0 : ℝ) 1 := ⟨hσ0.trans hστ.le, hτ1⟩
  have hsegσ : ∀ u, 0 ≤ u → Lemma71.segClock σ τ u ∈ Ico σ τ := fun u hu =>
    (Lemma71.image_segClock hστ) ▸ (⟨u, hu, rfl⟩ : Lemma71.segClock σ τ u ∈ Lemma71.segClock σ τ '' Ici 0)
  have hsegI : ∀ u, 0 ≤ u → Lemma71.segClock σ τ u ∈ Ico (0 : ℝ) 1 := fun u hu =>
    ⟨hσ0.trans (hsegσ u hu).1, (hsegσ u hu).2.trans_le hτ1⟩
  have hκfun : visitClock M (closure U) = fun u => WangWu.arcTime (Lemma71.segClock σ τ u) := by
    funext u
    rw [visitClock, eσ, eτ]
  have hsegPt : ∀ u, 0 ≤ u →
      segPt M (closure U) u = WangWu.toDisc (Lemma71I.realPath M) (Lemma71.segClock σ τ u) := fun u _ => by
    rw [segPt, eσ, eτ]
    rfl
  have hcay : ∀ u, 0 ≤ u → cayley (M (visitClock M (closure U) u).toNNReal) = segPt M (closure U) u :=
    fun u hu => by
      rw [hsegPt u hu, WangWu.toDisc_of_lt (hsegI u hu).2, hκfun]
      rfl
  -- a point of `ℍ` in the mapped segment comes from a visit
  have hreal : ∀ u, 0 ≤ u → M (visitClock M (closure U) u).toNNReal ∉ C →
      (Ψ (segPt M (closure U) u)).im = 0 := by
    intro u hu hnot
    have hmem := hΨH (hsegE u hu)
    rcases (show (0 : ℝ) ≤ (Ψ (segPt M (closure U) u)).im from hmem).eq_or_lt with h0 | hpos
    · exact h0.symm
    obtain ⟨z, hz, hFz⟩ := hFs _ hpos
    rw [hF z hz] at hFz
    have hcz : cayley z = segPt M (closure U) u := hΨi (hUE ⟨z, hz, rfl⟩) (hsegE u hu) hFz
    rw [← hcay u hu] at hcz
    have hzM : z = M (visitClock M (closure U) u).toNNReal :=
      WangWu.cayley_injOn_Hbar (show (0 : ℝ) ≤ z.im from le_of_lt (hCH hz)) (hMH _) hcz
    exact absurd (hzM ▸ hz) hnot
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, hcay, fun u hu hpos => ?_, ?_, ?_⟩
  · rw [hκfun]
    exact WangWu.continuousOn_arcTime.comp (Lemma71.continuousOn_segClock σ τ) fun u hu => (hsegI u hu).2
  · rw [hκfun]
    exact WangWu.strictMonoOn_arcTime.comp (Lemma71.strictMonoOn_segClock hστ) fun u hu => hsegI u hu
  · rw [hκfun]
    exact WangWu.arcTime_nonneg (hsegI 0 le_rfl)
  · intro u hu
    set p := M (visitClock M (closure U) u).toNNReal
    have hcp : cayley p ∈ closure U \ {q} := by
      rw [hcay u hu]
      exact hsegE u hu
    have h1 : Tendsto cayley (𝓝[C] p) (𝓝[closure U \ {q}] (cayley p)) :=
      tendsto_nhdsWithin_iff.2 ⟨(WangWu.continuousAt_cayley_of_mem_Hbar (hMH _)).tendsto.mono_left
        nhdsWithin_le_nhds, eventually_mem_nhdsWithin.mono fun z hz => hUE ⟨z, hz, rfl⟩⟩
    have h2 := ((hΨc _ hcp).tendsto.comp h1)
    rw [hcay u hu] at h2
    exact h2.congr' (eventually_mem_nhdsWithin.mono fun z hz => (hF z hz).symm)
  · intro t ht
    have hs01 := WangWu.discTime_mem_Ico (NNReal.coe_nonneg t)
    have hηs : WangWu.toDisc (Lemma71I.realPath M) (WangWu.discTime t) = cayley (M t) := by
      rw [WangWu.toDisc_discTime (Lemma71I.realPath M) (NNReal.coe_nonneg t), Lemma71I.realPath_coe]
    have hsI : WangWu.discTime t ∈ Icc σ τ := by
      rw [← hIM]
      refine ⟨Ico_subset_Icc_self hs01, ?_⟩
      show WangWu.toDisc (Lemma71I.realPath M) (WangWu.discTime t) ∈ closure U
      rw [hηs]
      exact subset_closure ⟨_, ht, rfl⟩
    have hsτ : WangWu.discTime t ≠ τ := fun h' => hqU (by
      rw [← hηq, ← h', hηs]
      exact ⟨_, ht, rfl⟩)
    obtain ⟨u, hu, hsu⟩ : WangWu.discTime t ∈ Lemma71.segClock σ τ '' Ici 0 := by
      rw [Lemma71.image_segClock hστ]
      exact ⟨hsI.1, lt_of_le_of_ne hsI.2 hsτ⟩
    refine ⟨u, hu, ?_⟩
    rw [hκfun]
    simp only
    rw [hsu, WangWu.arcTime_discTime (NNReal.coe_nonneg t)]
  · intro u₁ u₂ hu₁ h12
    by_contra hne
    push Not at hne
    have hsub : Ioo u₁ u₂ ⊆
        {u ∈ Ici (0 : ℝ) | 0 < u ∧ ((fun u => Ψ (segPt M (closure U) u)) u).im = 0} := by
      intro u hu
      have hu0 : 0 < u := lt_of_le_of_lt hu₁ hu.1
      exact ⟨hu0.le, hu0, hreal u hu0.le (hne u hu)⟩
    have hint := interior_maximal hsub isOpen_Ioo
    rw [hsc.2.2.2.2.2] at hint
    exact (nonempty_Ioo.2 h12).ne_empty (subset_empty_iff.1 hint)
  · by_contra hnot
    exact absurd (hreal u hu hnot) hpos.ne'
  · -- before every clock time the curve stays away from the closing point
    intro u hu
    set s₀ := Lemma71.segClock σ τ u with hs₀
    have hs₀τ : s₀ < τ := (hsegσ u hu).2
    have hsub : Icc (0 : ℝ) s₀ ⊆ Icc 0 1 := fun x hx => ⟨hx.1, hx.2.trans (hsegI u hu).2.le⟩
    set K := WangWu.toDisc (Lemma71I.realPath M) '' Icc 0 s₀ with hK
    have hKc : IsCompact K := isCompact_Icc.image_of_continuousOn (hμ.cont.mono hsub)
    have hKne : K.Nonempty := ⟨_, mem_image_of_mem _ ⟨le_rfl, (hsegI u hu).1⟩⟩
    have hqK : q ∉ K := by
      rintro ⟨x, hx, hxq⟩
      rw [← hηq] at hxq
      have := hμ.inj (hsub hx) hτ01 hxq
      linarith [hx.2]
    have hδ : 0 < infDist q K := (hKc.isClosed.notMem_iff_infDist_pos hKne).1 hqK
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ
    refine ⟨m, fun r hr => ?_⟩
    have hκu : 0 ≤ visitClock M (closure U) u := by
      rw [hκfun]; exact WangWu.arcTime_nonneg (hsegI u hu)
    have hr' : ((r : ℝ≥0) : ℝ) ≤ visitClock M (closure U) u := by
      rwa [← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_le_ofReal_iff hκu] at hr
    have hds : WangWu.discTime ((r : ℝ≥0) : ℝ) ≤ s₀ := by
      have := discTime_le_discTime (NNReal.coe_nonneg _) hr'
      rwa [hκfun, WangWu.discTime_arcTime (hsegI u hu).2] at this
    have hmemK : cayley (Sec6.pathCoord M r) ∈ K := by
      refine ⟨WangWu.discTime ((r : ℝ≥0) : ℝ), ⟨(WangWu.discTime_mem_Ico (NNReal.coe_nonneg _)).1, hds⟩, ?_⟩
      rw [WangWu.toDisc_discTime (Lemma71I.realPath M) (NNReal.coe_nonneg _), Lemma71I.realPath_coe]
      rfl
    rw [dist_comm]
    exact (hm.trans_le (infDist_le_dist_of_mem hmemK)).le
  · -- a time before which the curve stays away from the closing point bounds the mapped times
    intro T hT
    obtain ⟨m, hm⟩ := hT
    have hε : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
    have hclaim : ∀ u, 0 ≤ u → visitClock M (closure U) u ≤ T →
        1 / ((m : ℝ) + 1) ≤ dist (WangWu.toDisc (Lemma71I.realPath M) (Lemma71.segClock σ τ u)) q := by
      intro u hu hκT
      by_contra hlt
      push Not at hlt
      set x₀ := visitClock M (closure U) u with hx₀
      have hx₀0 : 0 ≤ x₀ := by rw [hx₀, hκfun]; exact WangWu.arcTime_nonneg (hsegI u hu)
      have hgx₀ : WangWu.toDisc (Lemma71I.realPath M) (WangWu.discTime x₀) =
          WangWu.toDisc (Lemma71I.realPath M) (Lemma71.segClock σ τ u) := by
        rw [hx₀, hκfun]
        simp only
        rw [WangWu.discTime_arcTime (hsegI u hu).2]
      -- continuity of `x ↦ dist (M̃ (discTime x)) q` at `x₀`
      have hcont : ContinuousWithinAt
          (fun x => dist (WangWu.toDisc (Lemma71I.realPath M) (WangWu.discTime x)) q) (Ici 0) x₀ := by
        have h1 : ContinuousWithinAt WangWu.discTime (Ici 0) x₀ := continuousOn_discTime x₀ hx₀0
        have h2 : ContinuousWithinAt (WangWu.toDisc (Lemma71I.realPath M)) (Icc 0 1)
            (WangWu.discTime x₀) := hμ.cont _ (Ico_subset_Icc_self (WangWu.discTime_mem_Ico hx₀0))
        exact (h2.comp h1 fun x hx => Ico_subset_Icc_self (WangWu.discTime_mem_Ico hx)).dist
          continuousWithinAt_const
      rw [← hgx₀] at hlt
      obtain ⟨δ, hδ, hball⟩ := Metric.continuousWithinAt_iff.1 hcont _ (sub_pos.2 hlt)
      obtain ⟨r, hr, hrd⟩ := Lemma71I.exists_nnrat_le_dist_lt x₀.toNNReal hδ
      have hr0 : (0 : ℝ) ≤ ((r : ℝ≥0) : ℝ) := NNReal.coe_nonneg _
      have hrx : ((r : ℝ≥0) : ℝ) ≤ x₀ := by
        have := NNReal.coe_le_coe.2 hr
        rwa [Real.coe_toNNReal _ hx₀0] at this
      have hdist : dist ((r : ℝ≥0) : ℝ) x₀ < δ := by
        rw [NNReal.dist_eq, Real.coe_toNNReal _ hx₀0] at hrd
        rwa [Real.dist_eq]
      have hval := hball (show ((r : ℝ≥0) : ℝ) ∈ Ici (0 : ℝ) from hr0) hdist
      rw [Real.dist_eq] at hval
      have hlt' : dist (WangWu.toDisc (Lemma71I.realPath M) (WangWu.discTime ((r : ℝ≥0) : ℝ))) q <
          1 / ((m : ℝ) + 1) := by
        have := (abs_lt.1 hval).2
        linarith
      have hrT : ((r : ℝ≥0) : ℝ≥0∞) ≤ (T : ℝ≥0∞) := by
        rw [ENNReal.coe_le_coe, ← NNReal.coe_le_coe]
        exact hrx.trans hκT
      have hge := hm r hrT
      rw [WangWu.toDisc_discTime (Lemma71I.realPath M) hr0, Lemma71I.realPath_coe] at hlt'
      exact absurd hge (not_le.2 hlt')
    have h1 : Tendsto (Lemma71.segClock σ τ) atTop (𝓝[Icc 0 1] τ) :=
      tendsto_nhdsWithin_iff.2 ⟨(Lemma71.tendsto_segClock hστ).mono_right nhdsWithin_le_nhds,
        (eventually_ge_atTop 0).mono fun u hu => Ico_subset_Icc_self (hsegI u hu)⟩
    have hlim : Tendsto (fun u => WangWu.toDisc (Lemma71I.realPath M) (Lemma71.segClock σ τ u)) atTop (𝓝 q) := by
      rw [← hηq]
      exact (hμ.cont τ hτ01).tendsto.comp h1
    obtain ⟨U₀, hU₀⟩ := eventually_atTop.1 ((Metric.tendsto_nhds.1 hlim) _ hε)
    refine ⟨U₀, fun u hu hκT => ?_⟩
    by_contra hlt
    exact absurd (hclaim u hu hκT) (not_le.2 (hU₀ u (not_le.1 hlt).le))

end InteractingSLE.Sec7.Lemma71L
