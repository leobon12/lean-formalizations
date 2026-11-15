/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Aux37AssemblyStrip

/-!
# Aux. lemma 37 at one rational witness: the hull bridges of the witness frame

Packet PROVE-STRIPSYS39, item (2) (bridges (a)–(c) of `planning/handoffs/PROVE-STRIPSYS36.md` §5, partly).
Specification §6.2, Aux. lemma 37's proof (`source/spec/p193-240.md` L114–L116, pp. 198–199: "The compact arc
`J = α_i([v₁, v₂])` is disjoint from `R_r`, is contained in `R_{T_v}` …").

Deterministic facts about the counterflow `η` (a continuous Loewner trace of `W` in the chart `R`) and the witness
collar (`Aux37Attach.IsAttachWitness.collar`):

* `ball_inter_fwdHull_eq_empty_of_later`: a trace point `η(T)` in `ℍ` at positive distance `δ` from `η([0, r])`,
  `r ≤ T`, has the whole ball `B(η(T), δ)` outside the hull `K_r` ("a later trace point is never interior to an
  earlier filled hull": `Sec6.trace_notMem_fwdHull`, then `Aux37Germ.inter_fillH_eq_empty_of_avoid`);
* `exists_ball_negInv_image_inter_eq_empty`: the same in the flow chart (`m(K_r)` misses a ball around `m(η(T))`);
* `negInv_mem_negInv_image_fwdHull`: a point visited by time `s` lies in `m(K_s)` (in the flow chart);
* `IsAttachWitness.exists_visit`: each arc point `α(x)`, `x ∈ [v, v₂]`, is `η(T′)`, `r ≤ T′ ≤ s`, at positive distance
  from `η([0, r])`;
* **`IsAttachWitness.exists_ball_hull_r`**, **`IsAttachWitness.mem_hull_s`**: for a witness of attachment progress on
  an arc `α` of a reverse-contained pocket, every arc point `α(x)`, `x ∈ [v, v₂]`, in `ℍ` has a ball around its
  flow-chart image `m(α(x))` that misses `m(K_r)` (the frame's G1 input), and `m(α(x)) ∈ m(K_s)`;
* `negInv_cfArcR`: the arc parameter ↔ wall time bridge (a): `m(cfArcR R L r x) = R(t)` at the wall time
  `t = arcTime(σ)⁺` of the disc parameter `σ = rightLo + x(rightHi − rightLo) < 1`.

No Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement`, `*_of_param` (R43, R48).
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter Topology Function
open scoped NNReal Real

namespace InteractingSLE.Sec7.Aux37Assembly

open QuantumZipper (H Hbar fwdHull)
open WangWu (negInv)

section Hull

variable {W : ℝ → ℝ} {η : ℝ → ℂ}

/-- **A later trace point at positive distance from `η([0, r])` has a ball outside `K_r`.** -/
theorem ball_inter_fwdHull_eq_empty_of_later (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    {r T : ℝ} (hr : 0 ≤ r) (hrT : r ≤ T) (hTH : η T ∈ H) {δ : ℝ} (hδ : 0 < δ)
    (hdist : ∀ y ∈ η '' Icc 0 r, δ ≤ dist (η T) y) : ball (η T) δ ∩ fwdHull W r = ∅ := by
  have hnot : η T ∉ η '' Icc 0 r := fun hm => by
    have := hdist _ hm
    rw [dist_self] at this
    linarith
  have hK := Sec6.trace_notMem_fwdHull hη hW hW0 hr hrT hnot
  have hcpt : IsCompact (η '' Icc 0 r) :=
    isCompact_Icc.image_of_continuousOn (hη.2.1.mono fun t ht => ht.1)
  have hav : ball (η T) δ ∩ closure (η '' Icc 0 r) = ∅ := by
    rw [hcpt.isClosed.closure_eq, eq_empty_iff_forall_notMem]
    rintro z ⟨hz, hzA⟩
    have h1 := hdist z hzA
    rw [mem_ball, dist_comm] at hz
    linarith
  rw [hη.2.2 r hr] at hK ⊢
  exact Aux37Germ.inter_fillH_eq_empty_of_avoid hav (mem_ball_self hδ) hTH hK

/-- **The flow-chart image of a set missing a ball misses a ball** (`m(z) = −1/z` is continuous off `0` and an
involution). -/
theorem exists_ball_negInv_image_inter_eq_empty {K : Set ℂ} {p : ℂ} (hp : p ≠ 0) {δ : ℝ} (hδ : 0 < δ)
    (h : ball p δ ∩ K = ∅) : ∃ ε > 0, negInv '' K ∩ ball (negInv p) ε = ∅ := by
  have hq : negInv p ≠ 0 := by simp [negInv, hp]
  have hc := WangWu.continuousAt_negInv hq
  obtain ⟨ε, hε, hεδ⟩ := Metric.continuousAt_iff.1 hc δ hδ
  refine ⟨ε, hε, eq_empty_iff_forall_notMem.2 ?_⟩
  rintro z ⟨⟨k, hk, rfl⟩, hz⟩
  have hkb := hεδ (mem_ball.1 hz)
  simp only [WangWu.negInv_negInv] at hkb
  rw [← mem_ball] at hkb
  exact (eq_empty_iff_forall_notMem.1 h) k ⟨hkb, hk⟩

/-- **A point visited by time `s` lies in the hull `K_s`** (read in the flow chart). -/
theorem negInv_mem_negInv_image_fwdHull (hη : IsLoewnerTrace W η) {s T : ℝ} (hs : 0 ≤ s) (hT : T ∈ Icc 0 s)
    (hTH : η T ∈ H) : negInv (η T) ∈ negInv '' fwdHull W s := by
  refine ⟨η T, ?_, rfl⟩
  rw [hη.2.2 s hs]
  exact ⟨hTH, Or.inl (subset_closure ⟨T, hT, rfl⟩)⟩

end Hull

section Witness

variable {W : ℝ → ℝ} {η : ℝ → ℂ} {C : Set ℂ} {α₁ α₂ β α : ℝ → ℂ} {τ σ r s v v₁ v₂ : ℝ}

theorem ne_zero_of_mem_H {z : ℂ} (hz : z ∈ H) : z ≠ 0 := fun h0 => by
  rw [h0] at hz
  exact lt_irrefl _ (show (0 : ℂ).im > 0 from hz)

/-- The arc points `α(x)`, `x ∈ [v, v₂]`, of a witness are visited after `r` and by `s`: `α(x) = η(T′)` with
`r ≤ T′ ≤ s`, at distance at least `δ > 0` from `η([0, r])`. -/
theorem IsAttachWitness.exists_visit (hP : Sec6.IsReversePocket W η C α₁ α₂ β τ σ) (hα : α = α₁ ∨ α = α₂)
    (hw : Aux37Attach.IsAttachWitness η C α τ σ r s v v₁ v₂) {x : ℝ} (hx : x ∈ Icc v v₂) :
    ∃ T' ∈ Icc r s, α x = η T' ∧ ∃ δ > 0, ∀ y ∈ η '' Icc 0 r, δ ≤ dist (η T') y := by
  obtain ⟨⟨T, hT, -, -, hvis⟩, ⟨δ, hδ, hdist⟩, -, -⟩ := hw.collar hP hα
  obtain ⟨hc, -, -, -, -, -⟩ := hP.arm hα
  have hmem := Sec6.firstVisit_mem (R := fun t => η '' Icc 0 t) hc hP.isClosed_range
    (Aux37Attach.exists_visited hP hα hw.1)
  have hx1 : x ∈ Icc v 1 := ⟨hx.1, hx.2.trans ((le_of_lt hw.2.2.2.2.2.2.2).trans hmem.1.2)⟩
  obtain ⟨T', hT', hT'e⟩ := hvis x hx1
  have hrT' : r ≤ T' := by
    by_contra hlt
    have hm : α x ∈ η '' Icc 0 r := ⟨T', ⟨hT'.1, (not_le.1 hlt).le⟩, hT'e⟩
    have := hdist x hx _ hm
    rw [dist_self] at this
    linarith
  exact ⟨T', ⟨hrT', hT'.2.trans hT.2⟩, hT'e.symm, δ, hδ, fun y hy => hT'e ▸ hdist x hx y hy⟩

/-- **G1's hull input at a witness** (bridge (b)): every arc point `α(x)`, `x ∈ [v, v₂]`, in `ℍ` has, in the flow
chart, a ball around `m(α(x))` that misses `m(K_r)`. -/
theorem IsAttachWitness.exists_ball_hull_r (hP : Sec6.IsReversePocket W η C α₁ α₂ β τ σ) (hα : α = α₁ ∨ α = α₂)
    (hw : Aux37Attach.IsAttachWitness η C α τ σ r s v v₁ v₂) (hW : Continuous W) (hW0 : W 0 = 0)
    (hη : IsLoewnerTrace W η) (hr : 0 ≤ r) {x : ℝ} (hx : x ∈ Icc v v₂) (hxH : α x ∈ H) :
    ∃ ε > 0, negInv '' fwdHull W r ∩ ball (negInv (α x)) ε = ∅ := by
  obtain ⟨T', hT', hT'e, δ, hδ, hdist⟩ := IsAttachWitness.exists_visit hP hα hw hx
  rw [hT'e] at hxH ⊢
  exact exists_ball_negInv_image_inter_eq_empty (ne_zero_of_mem_H hxH) hδ
    (ball_inter_fwdHull_eq_empty_of_later hη hW hW0 hr hT'.1 hxH hδ hdist)

/-- **G2's hull membership at a witness** (bridge (c), first half): every arc point `α(x)`, `x ∈ [v, v₂]`, in `ℍ` lies,
in the flow chart, in `m(K_s)`. -/
theorem IsAttachWitness.mem_hull_s (hP : Sec6.IsReversePocket W η C α₁ α₂ β τ σ) (hα : α = α₁ ∨ α = α₂)
    (hw : Aux37Attach.IsAttachWitness η C α τ σ r s v v₁ v₂) (hη : IsLoewnerTrace W η) (hr : 0 ≤ r)
    {x : ℝ} (hx : x ∈ Icc v v₂) (hxH : α x ∈ H) : negInv (α x) ∈ negInv '' fwdHull W s := by
  obtain ⟨T', hT', hT'e, -⟩ := IsAttachWitness.exists_visit hP hα hw hx
  rw [hT'e] at hxH ⊢
  exact negInv_mem_negInv_image_fwdHull hη (hr.trans hT'.1 |>.trans hT'.2) ⟨hr.trans hT'.1, hT'.2⟩ hxH

end Witness

section Arc

open PocketJordan

/-- **Arc parameter ↔ wall time** (bridge (a)): at a disc parameter `σ = rightLo + x(rightHi − rightLo) < 1`, the
flow-chart image of the right arc point is the wall point at the time `arcTime σ` (when that point is in `ℍ̄ ∖ {0}`). -/
theorem negInv_cfArcR {R L : ℝ≥0 → ℂ} {r : ℝ≥0} {x : ℝ}
    (hσ : rightLo R L r + x * (rightHi R L r - rightLo R L r) < 1)
    (hH : R (WangWu.arcTime (rightLo R L r + x * (rightHi R L r - rightLo R L r))).toNNReal ∈ Hbar)
    (h0 : R (WangWu.arcTime (rightLo R L r + x * (rightHi R L r - rightLo R L r))).toNNReal ≠ 0) :
    negInv (cfArcR R L r x) =
      R (WangWu.arcTime (rightLo R L r + x * (rightHi R L r - rightLo R L r))).toNNReal := by
  simp only [cfArcR, WangWu.toDisc, hσ, ↓reduceIte, Lemma71I.realPath]
  rw [cfPt_cayley hH h0, WangWu.negInv_negInv]

end Arc

end InteractingSLE.Sec7.Aux37Assembly
