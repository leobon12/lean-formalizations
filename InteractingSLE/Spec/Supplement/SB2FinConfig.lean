/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2FinHull
import InteractingSLE.Spec.Supplement.SB2FinChain

/-!
# SB2(1)'s relative configuration: the relative chain of the lifted upper flow and its hull identities

Packet PROVE-T14-SB2FIN. Lemma SB2(1) (supplement pp. 630–633, `source/spec/p625-671.md` L113–L150), "Geometry of
the erasure": "Thus the erased initial portion lies in `K_A`, and the later tail lies in `closure D_A` with the unique
lift selected by its free one-sided collar. In the first assertion this is the injective, proper lift of the witness;
the actual available upper flow is its initial restriction […] On every ordinary piece the strict angle comparison
excludes a common open arc with the other history […] An original-real open arc cannot belong to an ordinary flow.
Consequently the relative capacity is continuous and strictly increasing on each retained ordinary piece."

Deterministic content, in Lemma S2's setting (a compact retained set `A`, an S1 witness `β'` of the upper prefix,
the left entry chart `c` of `D_A` at `L` with its continuous boundary extension `g`, the S2 lift `γ`,
`g ∘ γ = β'(t_L + ·)`):

* `fillH_union_of_im_eq_zero`, **`interior_real_times_eq_empty`**: a Loewner trace spends no open time interval on
  `ℝ` ("an original-real open arc cannot belong to an ordinary flow": the hull would stop growing while the capacity
  grows);
* `interior_union_eq_empty`: two closed contact conditions with empty interior have a union with empty interior;
* `g_ofReal_mem`: the boundary extension of the chart inverse sends real points into `closure A ∪ ℝ`;
* **`interior_lift_real_eq_empty`**: if the post-`t_L` witness spends no open time interval on `closure A` (the
  no-common-arc input) nor on `ℝ`, the lift spends no open time interval on `ℝ`;
* **`exists_relConfig`** (SB2(1)'s relative chain and hulls): a continuous relative driver `Wr` from `0` with a
  continuous Loewner trace `ηr`, the relative clock `a = capClock (γ ∘ toNNReal)` (continuous, strictly increasing,
  `a 0 = 0`), the relative trace at `a s` is `γ s`, and at every `s ≤ S₀` the two hull fields of
  `SB.Union.IsRelConfigJ` hold for the filled retained set `fill A` and the physical prefix `β'([0, t_L + s])`:
  `hullIn` (a point of the physical filling off `fill A` has its chart image in the relative hull) and `hullFr` (a
  point of `D_A` whose chart image is on the frontier of the relative hull lies in the physical filling).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdHull)
open InteractingSLE.Supp9B (IsProperCurve closedRightSide)

namespace InteractingSLE.Theorem14.SB.FinRel

open Sec7.Lemma71C

/-! ### A Loewner trace spends no open time interval on `ℝ` -/

/-- Adding real points does not change a filling. -/
theorem fillH_union_of_im_eq_zero {X S : Set ℂ} (hS : ∀ z ∈ S, z.im = 0) : fillH (X ∪ S) = fillH X := by
  have hSc : closure S ⊆ {z : ℂ | z.im = 0} :=
    closure_minimal hS (isClosed_eq Complex.continuous_im continuous_const)
  have hHS : ∀ z ∈ H, z ∉ closure S := fun z hz hzS => (ne_of_gt (show 0 < z.im from hz)) (hSc hzS)
  have hdiff : H \ closure (X ∪ S) = H \ closure X := by
    ext z
    rw [closure_union]
    constructor
    · exact fun h => ⟨h.1, fun hX => h.2 (Or.inl hX)⟩
    · exact fun h => ⟨h.1, fun hXS => hXS.elim h.2 (hHS z h.1)⟩
  ext z
  show (z ∈ H ∧ (z ∈ closure (X ∪ S) ∨ IsBounded (connectedComponentIn (H \ closure (X ∪ S)) z))) ↔
    (z ∈ H ∧ (z ∈ closure X ∨ IsBounded (connectedComponentIn (H \ closure X) z)))
  rw [hdiff, closure_union]
  constructor
  · rintro ⟨hz, (h | h) | h⟩
    · exact ⟨hz, Or.inl h⟩
    · exact absurd h (hHS z hz)
    · exact ⟨hz, Or.inr h⟩
  · rintro ⟨hz, h | h⟩
    · exact ⟨hz, Or.inl (Or.inl h)⟩
    · exact ⟨hz, Or.inr h⟩

/-- **A Loewner trace spends no open time interval on `ℝ`** before its horizon: on such an interval `[a, b]` the
filling of the trace would not grow, while the capacity of the hull at time `t` is `2t`. -/
theorem interior_real_times_eq_empty {W : ℝ → ℝ} {T : ℝ} {η : ℝ → ℂ} (hη : IsLoewnerTraceLT W T η)
    (hW : Continuous W) (hW0 : W 0 = 0) : interior {r ∈ Ioo (0 : ℝ) T | (η r).im = 0} = ∅ := by
  by_contra hne
  obtain ⟨r, hr⟩ := nonempty_iff_ne_empty.2 hne
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_interior r hr
  have hrI := interior_subset hr
  have hab : r < r + ε / 2 := by linarith
  have hb : ∀ x ∈ Icc r (r + ε / 2), x ∈ {r ∈ Ioo (0 : ℝ) T | (η r).im = 0} := fun x hx => interior_subset
    (hball (by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [hx.1, hx.2]))
  have ha0 : 0 ≤ r := (hrI.1.1).le
  have hbT : r + ε / 2 < T := (hb _ ⟨hab.le, le_rfl⟩).1.2
  have hcapb := Sec7.Lemma71.hcapSet_eq_of_fwdHull_eq hW hW0 (ha0.trans hab.le)
    (hη.2.2 _ (ha0.trans hab.le) hbT)
  have hfill : fillH (η '' Icc 0 (r + ε / 2)) = fillH (η '' Icc 0 r) := by
    rw [← Icc_union_Icc_eq_Icc ha0 hab.le, image_union]
    exact fillH_union_of_im_eq_zero fun z ⟨x, hx, hxz⟩ => hxz ▸ (hb x hx).2
  have hcapa := Sec7.Lemma71.hcapSet_eq_of_fwdHull_eq hW hW0 ha0 (hη.2.2 r ha0 (lt_trans hab hbT))
  rw [← hfill, hcapb] at hcapa
  linarith

/-- **The post-`t_L` witness spends no open time interval on `ℝ`** while it is a generating trace (the frozen
`IsGeneratingTrace` of the physical flow, e.g. from `IsFlowLine`): the hypothesis `hnR` of `exists_relConfig`. -/
theorem interior_post_real_eq_empty {w : ℝ≥0 → ℝ} {T : ℝ≥0∞} {η : ℝ≥0 → ℂ} (hη : IsGeneratingTrace w T η)
    (hw : Continuous w) (hw0 : w 0 = 0) {β' : ℝ≥0 → ℂ} {tL : ℝ≥0} {S : ℝ} (hS : 0 ≤ S)
    (hT : ENNReal.ofReal (tL + S) < T) (hβη : ∀ r : ℝ≥0, (r : ℝ) < tL + S → β' r = η r) :
    interior {r ∈ Ioo (0 : ℝ) S | β' (tL + r.toNNReal) ∈ {z : ℂ | z.im = 0}} = ∅ := by
  have hLT := hη.isLoewnerTraceLT hT
  have hI := interior_real_times_eq_empty hLT (continuous_frozenDrive hw.continuousOn)
    (by rw [frozenDrive_zero (by positivity), hw0])
  set U := interior {r ∈ Ioo (0 : ℝ) S | β' (tL + r.toNNReal) ∈ {z : ℂ | z.im = 0}}
  have hsub : (fun r : ℝ => (tL : ℝ) + r) '' U ⊆
      interior {r ∈ Ioo (0 : ℝ) (tL + S) | (η r.toNNReal).im = 0} := by
    refine interior_maximal ?_ (isOpenMap_add_left _ U isOpen_interior)
    rintro _ ⟨r, hr, rfl⟩
    obtain ⟨⟨hr0, hrS⟩, hre⟩ := interior_subset hr
    have hx : (((tL : ℝ) + r).toNNReal : ℝ) < tL + S := by
      rw [Real.coe_toNNReal _ (by positivity)]
      linarith
    have heq : ((tL : ℝ) + r).toNNReal = tL + r.toNNReal := by
      rw [Real.toNNReal_add tL.coe_nonneg hr0.le, Real.toNNReal_coe]
    refine ⟨⟨by positivity, by linarith⟩, ?_⟩
    rw [← hβη _ hx, heq]
    exact hre
  rw [hI] at hsub
  exact subset_empty_iff.1 fun r hr => (hsub ⟨r, hr, rfl⟩ : ((tL : ℝ) + r) ∈ (∅ : Set ℝ)).elim

/-! ### Two closed contact conditions -/

/-- **Splitting the contact times**: if `f` is continuous on `I`, `F₁` is closed, and the times in `I` at
which `f` is in `F₁`, resp. in `F₂` (closed), have empty interior, so have the times at which `f ∈ F₁ ∪ F₂`. -/
theorem interior_union_eq_empty {f : ℝ → ℂ} {I : Set ℝ} (hf : ContinuousOn f I) {F₁ F₂ : Set ℂ}
    (hF₁ : IsClosed F₁) (h₁ : interior {r ∈ I | f r ∈ F₁} = ∅) (h₂ : interior {r ∈ I | f r ∈ F₂} = ∅) :
    interior {r ∈ I | f r ∈ F₁ ∪ F₂} = ∅ := by
  set U := interior {r ∈ I | f r ∈ F₁ ∪ F₂}
  have hUI : U ⊆ I := fun r hr => (interior_subset hr).1
  have hV : IsOpen (U ∩ f ⁻¹' F₁ᶜ) := (hf.mono hUI).isOpen_inter_preimage isOpen_interior hF₁.isOpen_compl
  have hVsub : U ∩ f ⁻¹' F₁ᶜ ⊆ interior {r ∈ I | f r ∈ F₂} := interior_maximal (fun r hr => by
    obtain ⟨hrI, h⟩ := interior_subset hr.1
    exact ⟨hrI, h.resolve_left hr.2⟩) hV
  rw [h₂] at hVsub
  have hU1 : U ⊆ interior {r ∈ I | f r ∈ F₁} := interior_maximal (fun r hr => by
    refine ⟨hUI hr, ?_⟩
    by_contra h
    exact hVsub ⟨hr, h⟩) isOpen_interior
  rw [h₁] at hU1
  exact subset_empty_iff.1 hU1

/-! ### Real points under the boundary extension of the chart inverse -/

section Ext

variable {A : Set ℂ} {c : Chart} {g : ℂ → ℂ}

/-- **Real points land in `closure A ∪ ℝ`**: the boundary value `g x` at a real point is a limit of points of `D_A`
and not in `D_A`, so it is real or on the frontier of `fill A` inside `ℍ`, which lies on `closure A`. -/
theorem g_ofReal_mem (hD : IsDomainChart (H \ fillH A) c) (hgc : ContinuousOn g {z | 0 ≤ z.im})
    (hgi : EqOn g c.2.1 H) (x : ℝ) : g x ∈ closure A ∪ {z : ℂ | z.im = 0} := by
  have him := SB.im_g_nonneg hD hgc hgi (show 0 ≤ ((x : ℂ)).im by simp)
  rcases him.lt_or_eq with hpos | h0
  · left
    have hgH : g x ∈ H := hpos
    have hnD := SB.g_ofReal_notMem hD hgc hgi x
    have hfill : g x ∈ fillH A := by
      by_contra h
      exact hnD ⟨hgH, h⟩
    have hcl : g x ∈ closure (H \ fillH A) := by
      refine mem_closure_of_tendsto (SB.tendsto_g_vertical hgc x) ?_
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact SB.g_mem_of_mem_H hD hgi (show 0 < ((x : ℂ) + (y : ℂ) * I).im by simpa using hy)
    have hfr : g x ∈ frontier (fillH A) := by
      rw [frontier_eq_closure_inter_closure]
      exact ⟨subset_closure hfill, closure_mono (fun z hz => hz.2) hcl⟩
    exact frontier_fillH_inter_H_subset A ⟨hfr, hgH⟩
  · right
    exact h0.symm

/-- **The lift spends no open time interval on `ℝ`** if the post-`t_L` witness spends none on `closure A` (no common
arc with the retained history) and none on `ℝ` (no original-real arc). -/
theorem interior_lift_real_eq_empty (hD : IsDomainChart (H \ fillH A) c) (hgc : ContinuousOn g {z | 0 ≤ z.im})
    (hgi : EqOn g c.2.1 H) {β' γ : ℝ≥0 → ℂ} {tL : ℝ≥0} (hβc : Continuous β') (hlift : ∀ s, g (γ s) = β' (tL + s))
    {S : ℝ} (hA : interior {r ∈ Ioo (0 : ℝ) S | β' (tL + r.toNNReal) ∈ closure A} = ∅)
    (hRe : interior {r ∈ Ioo (0 : ℝ) S | β' (tL + r.toNNReal) ∈ {z : ℂ | z.im = 0}} = ∅) :
    interior {r ∈ Ioo (0 : ℝ) S | (γ r.toNNReal).im = 0} = ∅ := by
  have hf : ContinuousOn (fun r : ℝ => β' (tL + r.toNNReal)) (Ioo 0 S) :=
    (hβc.comp (continuous_const.add continuous_real_toNNReal)).continuousOn
  have hU := interior_union_eq_empty (f := fun r : ℝ => β' (tL + r.toNNReal)) hf isClosed_closure hA hRe
  refine subset_empty_iff.1 (hU ▸ interior_mono fun r hr => ⟨hr.1, ?_⟩)
  have hγr : γ r.toNNReal = ((γ r.toNNReal).re : ℂ) := Complex.ext (by simp) (by simp [hr.2])
  show β' (tL + r.toNNReal) ∈ closure A ∪ {z : ℂ | z.im = 0}
  rw [← hlift, hγr]
  exact g_ofReal_mem hD hgc hgi _

end Ext

/-! ### SB2(1)'s relative configuration -/

section Config

variable {A : Set ℂ} {L : ℝ} {c : Chart} {g : ℂ → ℂ} {β' γ : ℝ≥0 → ℂ} {tL : ℝ≥0}

/-- A proper curve read on real times is a simple path on `[0, ∞)` in `closure ℍ` tending to `∞`. -/
theorem isProperCurve_real (hγ : IsProperCurve γ) :
    ContinuousOn (fun r : ℝ => γ r.toNNReal) (Ici 0) ∧ InjOn (fun r : ℝ => γ r.toNNReal) (Ici 0) ∧
      MapsTo (fun r : ℝ => γ r.toNNReal) (Ici 0) Hbar ∧
      Tendsto (fun r : ℝ => ‖γ r.toNNReal‖) atTop atTop := by
  refine ⟨(hγ.1.comp continuous_real_toNNReal).continuousOn, fun r hr r' hr' h => ?_, fun r _ => hγ.2.2.1 _,
    hγ.2.2.2.comp tendsto_real_toNNReal_atTop⟩
  have := hγ.2.1 h
  rw [← Real.coe_toNNReal r hr, ← Real.coe_toNNReal r' hr', this]

/-- The physical prefix meets `D_A` only at `g`-images of the relative prefix: before `t_L` it lies in `K_A`, after it
is `g ∘ γ`. -/
theorem physPrefix_inter_subset (hpre : β' '' Icc 0 tL ⊆ hullK A) (hlift : ∀ s, g (γ s) = β' (tL + s)) (s : ℝ≥0) :
    β' '' Icc 0 (tL + s) ∩ (H \ fillH A) ⊆ g '' (γ '' Icc 0 s) := by
  rintro _ ⟨⟨r, hr, rfl⟩, hD⟩
  by_cases hrt : r ≤ tL
  · exact absurd (hpre ⟨r, ⟨hr.1, hrt⟩, rfl⟩) (SB.notMem_hullK_of_mem_D hD)
  · have hle : tL ≤ r := le_of_lt (not_le.1 hrt)
    refine ⟨γ (r - tL), ⟨r - tL, ⟨zero_le, tsub_le_iff_left.2 hr.2⟩, rfl⟩, ?_⟩
    rw [hlift, add_tsub_cancel_of_le hle]

/-- **SB2(1)'s relative configuration** (Lemma SB2, pp. 631–632): in S2's setting — a bounded retained set `A` with
`A ∪ {Im ≤ 0}` preconnected, the left entry chart `c` of `D_A = ℍ ∖ fill A` at `L` with the continuous boundary
extension `g` of its inverse, an S1 witness `β'` whose portion through `t_L` lies in `K_A`, and the S2 lift `γ`
(`g ∘ γ = β'(t_L + ·)`) — suppose that on `(0, S)` the post-`t_L` witness spends no open time interval on
`closure A` (no common arc) nor on `ℝ` (no original-real arc). Then for every `S₀ < S` there are a continuous
relative driver `Wr` from `0` and a continuous Loewner trace `ηr` of it, with the relative clock
`a = capClock (γ ∘ toNNReal)` (`a 0 = 0`, continuous and strictly increasing on `[0, S₀]`), such that for every
`s ≤ S₀`: the relative trace at `a s` is `γ s`, the relative hull at `a s` is `fill γ([0, s])`, and the hull fields
of `SB.Union.IsRelConfigJ` hold between the filled retained set `fill A`, the physical prefix `β'([0, t_L + s])` and
the relative hull at `a s`. -/
theorem exists_relConfig (hAb : IsBounded A) (hAc : IsPreconnected (A ∪ {z : ℂ | z.im ≤ 0}))
    (hc : IsLeftEntryChart A L c) (hgc : ContinuousOn g {z | 0 ≤ z.im}) (hgi : EqOn g c.2.1 H)
    (hβ' : IsProperCurve β') (hpre : β' '' Icc 0 tL ⊆ hullK A) (hγ : IsProperCurve γ) (hγ0 : γ 0 = 0)
    (hlift : ∀ s, g (γ s) = β' (tL + s)) {S S₀ : ℝ} (hS₀ : 0 ≤ S₀) (hS₀S : S₀ < S)
    (hnA : interior {r ∈ Ioo (0 : ℝ) S | β' (tL + r.toNNReal) ∈ closure A} = ∅)
    (hnR : interior {r ∈ Ioo (0 : ℝ) S | β' (tL + r.toNNReal) ∈ {z : ℂ | z.im = 0}} = ∅) :
    ∃ (Wr : ℝ → ℝ) (ηr : ℝ → ℂ), Continuous Wr ∧ Wr 0 = 0 ∧ IsLoewnerTrace Wr ηr ∧
      capClock (fun r : ℝ => γ r.toNNReal) 0 = 0 ∧
      StrictMonoOn (capClock (fun r : ℝ => γ r.toNNReal)) (Icc 0 S₀) ∧
      ContinuousOn (capClock (fun r : ℝ => γ r.toNNReal)) (Icc 0 S₀) ∧
      ∀ s ∈ Icc 0 S₀, 0 ≤ capClock (fun r : ℝ => γ r.toNNReal) s ∧
        ηr (capClock (fun r : ℝ => γ r.toNNReal) s) = γ s.toNNReal ∧
        fwdHull Wr (capClock (fun r : ℝ => γ r.toNNReal) s) = fillH (γ '' Icc 0 s.toNNReal) ∧
        (∀ z ∈ fillH (β' '' Icc 0 (tL + s.toNNReal)), z ∉ fillH A →
          c.1 z ∈ fwdHull Wr (capClock (fun r : ℝ => γ r.toNNReal) s)) ∧
        (∀ z ∈ H \ fillH A, c.1 z ∈ frontier (fwdHull Wr (capClock (fun r : ℝ => γ r.toNNReal) s)) →
          z ∈ fillH (β' '' Icc 0 (tL + s.toNNReal))) := by
  have hD := hc.1
  obtain ⟨hcr, hinj, hH, hinf⟩ := isProperCurve_real hγ
  have h0 : (fun r : ℝ => γ r.toNNReal) 0 = 0 := by simp only [Real.toNNReal_zero, hγ0]
  have hR := interior_lift_real_eq_empty hD hgc hgi hβ'.1 hlift hnA hnR
  obtain ⟨Wr, ηr, hWr, hWr0, hηr, hc0, hcm, hcc, hK⟩ := exists_relChain hcr hinj hH h0 hinf
    (lt_of_le_of_lt hS₀ hS₀S) hR hS₀ hS₀S
  obtain ⟨C₁, C₂, hC₁, hgrow⟩ := SB.exists_norm_le_norm_g hc hAb hAc hgc hgi
  have hgrow' : ∀ w ∈ H, ‖w‖ ≤ C₁ * ‖c.2.1 w‖ + C₂ := fun w hw => by
    have := hgrow w (le_of_lt (show 0 < w.im from hw))
    rwa [hgi hw] at this
  refine ⟨Wr, ηr, hWr, hWr0, hηr, hc0, hcm, hcc, fun s hs => ?_⟩
  obtain ⟨ha0, hηa, hKa⟩ := hK s hs
  have himg : (fun r : ℝ => γ r.toNNReal) '' Icc 0 s = γ '' Icc 0 s.toNNReal := image_toNNReal_Icc γ hs.1
  rw [himg] at hKa
  have hYc : IsClosed (γ '' Icc 0 s.toNNReal) := (isCompact_Icc.image hγ.1).isClosed
  have hXc : IsClosed (β' '' Icc 0 (tL + s.toNNReal)) := (isCompact_Icc.image hβ'.1).isClosed
  refine ⟨ha0, hηa, hKa, fun z hz hzA => ?_, fun z hz hfr => ?_⟩
  · rw [hKa]
    exact fwd_mem_fillH_of_mem_fillH hD hgc hgi hC₁ hgrow' hXc hYc (fun _ ⟨r, _, hr⟩ => hr ▸ hγ.2.2.1 r)
      (physPrefix_inter_subset hpre hlift _) hz hzA
  · rw [hKa] at hfr
    refine mem_fillH_of_fwd_mem_frontier_fillH hD hgi hYc ?_ hz hfr
    rintro _ ⟨r, hr, rfl⟩ -
    rw [hlift]
    exact ⟨tL + r, ⟨zero_le, add_le_add_right hr.2 tL⟩, rfl⟩

/-- **The relative chain of SB2(1) and its hull fields** (the conclusion of `exists_relConfig`, as a predicate of the
relative driver `Wr` and trace `ηr`): `Wr` is continuous from `0` with the continuous Loewner trace `ηr`; the relative
clock `a = capClock (γ ∘ toNNReal)` starts at `0` and is continuous and strictly increasing on `[0, S₀]`; at every
`s ≤ S₀` the relative trace at `a s` is `γ s`, the relative hull is `fill γ([0, s])`, and the fields `hullIn`,
`hullFr` of `SB.Union.IsRelConfigJ` hold for `fill A` and the physical prefix `β'([0, t_L + s])`. -/
def IsSB2RelChain (A : Set ℂ) (c : Chart) (β' γ : ℝ≥0 → ℂ) (tL : ℝ≥0) (S₀ : ℝ) (Wr : ℝ → ℝ) (ηr : ℝ → ℂ) :
    Prop :=
  Continuous Wr ∧ Wr 0 = 0 ∧ IsLoewnerTrace Wr ηr ∧
    capClock (fun r : ℝ => γ r.toNNReal) 0 = 0 ∧
    StrictMonoOn (capClock (fun r : ℝ => γ r.toNNReal)) (Icc 0 S₀) ∧
    ContinuousOn (capClock (fun r : ℝ => γ r.toNNReal)) (Icc 0 S₀) ∧
    ∀ s ∈ Icc 0 S₀, 0 ≤ capClock (fun r : ℝ => γ r.toNNReal) s ∧
      ηr (capClock (fun r : ℝ => γ r.toNNReal) s) = γ s.toNNReal ∧
      fwdHull Wr (capClock (fun r : ℝ => γ r.toNNReal) s) = fillH (γ '' Icc 0 s.toNNReal) ∧
      (∀ z ∈ fillH (β' '' Icc 0 (tL + s.toNNReal)), z ∉ fillH A →
        c.1 z ∈ fwdHull Wr (capClock (fun r : ℝ => γ r.toNNReal) s)) ∧
      (∀ z ∈ H \ fillH A, c.1 z ∈ frontier (fwdHull Wr (capClock (fun r : ℝ => γ r.toNNReal) s)) →
        z ∈ fillH (β' '' Icc 0 (tL + s.toNNReal)))

/-- **SB2(1)'s relative configuration from the retained path** (Lemma S2 and `exists_relConfig`): for the retained
history `A = p([0, 1])` (a continuous path from `0` in `closure ℍ`), an S1 witness `β'` with `A` on its closed right
side, the left entry chart `c` of `D_A` at `L = min(A ∩ ℝ)` whose inverse has the continuous finite-fibre extension
`g`, and the no-common-arc / no-real-arc conditions after the entrance on `(0, S)`: the witness visits `L` at `t_L`,
its portion through `t_L` lies in `K_A`, the post-`t_L` portion has the proper S2 lift `γ`, and for every `S₀ < S`
the relative chain of `γ` with its hull fields exists (`IsSB2RelChain`). -/
theorem exists_relConfig_of_path {p : ℝ → ℂ} (hp : ContinuousOn p (Icc 0 1)) (hp0 : p 0 = 0)
    (hpH : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (p s).im) (hβ' : IsProperCurve β') (hβ'0 : β' 0 = 0)
    (hA : p '' Icc 0 1 ⊆ closedRightSide β') (hc : IsLeftEntryChart (p '' Icc 0 1) (realMin (p '' Icc 0 1)) c)
    (hgc : ContinuousOn g {z | 0 ≤ z.im}) (hgi : EqOn g c.2.1 H)
    (hfin : ∀ z, (g ⁻¹' {z} ∩ {w | 0 ≤ w.im}).Finite) {S S₀ : ℝ} (hS₀ : 0 ≤ S₀) (hS₀S : S₀ < S)
    (hnA : ∀ t : ℝ≥0, β' t = realMin (p '' Icc 0 1) →
      interior {r ∈ Ioo (0 : ℝ) S | β' (t + r.toNNReal) ∈ closure (p '' Icc 0 1)} = ∅)
    (hnR : ∀ t : ℝ≥0, β' t = realMin (p '' Icc 0 1) →
      interior {r ∈ Ioo (0 : ℝ) S | β' (t + r.toNNReal) ∈ {z : ℂ | z.im = 0}} = ∅) :
    ∃ (tL : ℝ≥0) (γ : ℝ≥0 → ℂ), β' tL = realMin (p '' Icc 0 1) ∧ β' '' Icc 0 tL ⊆ hullK (p '' Icc 0 1) ∧
      IsProperCurve γ ∧ γ 0 = 0 ∧ (∀ s, g (γ s) = β' (tL + s)) ∧
      ∃ (Wr : ℝ → ℝ) (ηr : ℝ → ℂ), IsSB2RelChain (p '' Icc 0 1) c β' γ tL S₀ Wr ηr := by
  obtain ⟨-, tL, htL, -, hpre, -⟩ := SB.s2HullStatement p β' hp hp0 hpH hβ' hβ'0 hA
  obtain ⟨γ, hγ, hγ0, hlift⟩ := SB.s2LiftStatement p β' hp hp0 hpH hβ' hβ'0 hA c g hc hgc hgi hfin tL htL
  have hAb : IsBounded (p '' Icc 0 1) := (isCompact_Icc.image_of_continuousOn hp).isBounded
  have hAc : IsPreconnected (p '' Icc 0 1 ∪ {z : ℂ | z.im ≤ 0}) :=
    (isPreconnected_Icc.image p hp).union 0 ⟨0, ⟨le_rfl, zero_le_one⟩, hp0⟩ (show (0 : ℂ).im ≤ 0 by simp)
      isPreconnected_lowerHalf
  exact ⟨tL, γ, htL, hpre, hγ, hγ0, hlift, exists_relConfig hAb hAc hc hgc hgi hβ' hpre hγ hγ0 hlift hS₀ hS₀S
    (hnA tL htL) (hnR tL htL)⟩

end Config

end InteractingSLE.Theorem14.SB.FinRel
