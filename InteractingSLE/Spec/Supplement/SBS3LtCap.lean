/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBS3LtCore
import InteractingSLE.Spec.Supplement.SBS3AsmLower
import InteractingSLE.Spec.Supplement.SBS3AsmChart
import InteractingSLE.Spec.Supplement.SBS3WalkSplit
import InteractingSLE.Spec.Supplement.WalkSideInputs
import InteractingSLE.Spec.Supplement.SB2JqDense

/-!
# Lemma S3 for SB2(2)'s lower tail: the capped walk as the second history

Worker PROVE-R6-CORNER (Theorem 1.4, Lemma S3 with the roles exchanged, supplement p. 631). Deterministic. The second
history of the comparison is the lower walk up to the cut: the walk's first `j` instructions followed by its piece `j`
stopped at the own time `q` (`WalkSide.capSpec`).

* `angle_eq_of_mem_capSpec`, `StageSide.sideH_cap`: the capped walk's side heights are the walk's, `±λ + (π/2)χ`;
* `stagedPiecesRegular_capSpec`: piece regularity passes to the capped program;
* `prefixPhysSet_capSpec_succ`: its physical prefix is the walk's prefix and the piece up to `q`;
* **`second_sample_facts_walk`**: from the capped stage's mean and side labels and the walk bookkeeping
  (`Walk.walk_second_chart_inputs`), the second inputs of `exists_protectedWordComparison_lower` (composed core chart
  `Canon.comp_chart_facts`, hull model, canonical logarithm, labels at interior landings);
* `exists_piece_of_mem_H`, `trace_mem_H_of_piece_mem_H`: a walk point in `ℍ` is on a launched piece, at a trace point
  in `ℍ` (`Lk.tip_inter_old_real`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Complex Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdMap fwdMapInv chiC)

universe u

namespace InteractingSLE.Theorem14.SB.S3.Asm

open Exist.Staged Exist.StagedLaw Restart WalkSide

/-- Every ordinary instruction of a capped boundary walk has the walk's angle, when the cap has it too. -/
theorem angle_eq_of_mem_capSpec {b : ℝ → ℝ} {jumps : Finset ℝ} {θ θ' : ℝ} {r : Bool} {ℓ : ℕ} {τ t : ℝ≥0∞}
    (h : (Sum.inl (θ', t) : Instr) ∈ (capSpec (boundaryWalkSpec b jumps θ r) ℓ θ τ).2.2) : θ' = θ := by
  simp only [capSpec, List.mem_append, List.mem_singleton, Sum.inl.injEq, Prod.mk.injEq] at h
  rcases h with h | ⟨rfl, -⟩
  · exact angle_eq_of_mem_boundaryWalkSpec (List.mem_of_mem_take h)
  · rfl

/-- The physical side heights of a capped boundary walk of angle `θ` are those of the schedule `[(θ, 0)]`. -/
theorem StageSide.sideH_cap {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {θ : ℝ} {r : Bool} {ℓ : ℕ} {τ : ℝ≥0∞}
    {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {n : ℕ} {v : ℝ}
    (hv : StageSide κ b jumps (capSpec (boundaryWalkSpec b jumps θ r) ℓ θ τ) D n v) :
    Lh.SideH κ [(θ, 0)] v := by
  obtain ⟨j, -, hl, he⟩ := hv
  obtain ⟨⟨c, θ'⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hl
  have hsp := (eq_launch_of_launches _ _ hcθ).1
  have hang : instrAngle (capSpec (boundaryWalkSpec b jumps θ r) ℓ θ τ) j = θ' := by
    unfold instrAngle
    rw [hsp]
  have hθ' : θ' = θ := angle_eq_of_mem_capSpec (List.mem_of_getElem? hsp)
  refine ⟨(θ, 0), List.mem_singleton_self _, ?_⟩
  rw [← hθ', ← hang]
  exact he

/-- **Piece regularity passes to a capped program** (cap at a finite own time of an unstopped flow). -/
theorem stagedPiecesRegular_capSpec {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {w : ExplSpec} {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hR : StagedPiecesRegular κ b jumps P w E)
    {ℓ : ℕ} (hℓ : ℓ ≤ w.2.2.length) {θ : ℝ} (hwℓ : w.2.2[ℓ]? = some (Sum.inl (θ, ⊤))) (q : ℝ≥0) :
    StagedPiecesRegular κ b jumps P (capSpec w ℓ θ q) E := by
  filter_upwards [hR] with ω hr
  intro k θ' t c hk hl
  rcases lt_trichotomy k ℓ with hkl | rfl | hkl
  · rw [capSpec_getElem?_of_lt hkl hℓ] at hk
    rw [run_capSpec_of_le hℓ _ (Nat.succ_le_of_lt hkl)] at hl
    exact hr k θ' t c hk hl
  · rw [capSpec_getElem?_self hℓ] at hk
    have hθt := Prod.mk.inj (Sum.inl.inj (Option.some.inj hk))
    have hθ' : θ' = θ := hθt.1.symm
    have ht : t = (q : ℝ≥0∞) := hθt.2.symm
    subst hθ' ht
    rw [launches_run_capSpec_succ hℓ hwℓ] at hl
    obtain ⟨h0, hc, η, hη, -⟩ := hr k θ' ⊤ c hwℓ hl
    have hle : min (q : ℝ≥0∞) (E k ω).2 ≤ min ⊤ (E k ω).2 := min_le_min_right _ le_top
    refine ⟨h0, hc.mono fun s hs => (show (s : ℝ≥0∞) ≤ _ from hs).trans hle,
      η, BRLeaf.isGeneratingTrace_of_le hη hle, fun htop => ?_⟩
    exact absurd htop (ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_left _ _))
  · rw [capSpec_getElem?_of_gt hkl hℓ] at hk
    cases hk

end InteractingSLE.Theorem14.SB.S3.Asm

namespace InteractingSLE.Theorem14.SB.S3.Asm

open Exist.Staged Exist.StagedLaw Restart WalkSide Geo Canon GW1Bookkeep

/-- **The physical prefix of the capped walk** after its last instruction: the walk's prefix before the piece and
the piece up to its own time `q`, read through the launch chart's boundary map. -/
theorem prefixPhysSet_capSpec_succ {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {θ : ℝ} {r : Bool}
    {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {j : ℕ} {c : Chart} {θ' : ℝ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ r) D (j + 1)).2.2.2.1 j = some (c, θ'))
    {gc : ℂ → ℂ} (hgc : ContinuousOn gc Hbar) (hgi : EqOn gc c.2.1 H)
    {α : ℝ≥0 → ℂ} (hα : IsGeneratingTrace (D j).1 (D j).2 α)
    (hW0 : (D j).1 0 = 0) (hWc : ContinuousOn (D j).1 {s | (s : ℝ≥0∞) ≤ (D j).2})
    {q : ℝ≥0} (hq : (q : ℝ≥0∞) < (D j).2) :
    prefixPhysSet κ b jumps (capSpec (boundaryWalkSpec b jumps θ r) j θ q) D (j + 1) =
      statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ r) D j) ∪ gc '' (α '' Icc 0 q) := by
  set w := boundaryWalkSpec b jumps θ r with hw
  set sc := capSpec w j θ (q : ℝ≥0∞) with hsc
  obtain ⟨hi, he, hcr⟩ := eq_launch_of_launches w D hl
  have hjl : j < w.2.2.length := by
    by_contra hc
    rw [List.getElem?_eq_none (not_lt.1 hc)] at hi
    cases hi
  have hθ' : θ' = θ := angle_eq_of_mem_boundaryWalkSpec (List.mem_of_getElem? hi)
  have htop : instrTime w j = ⊤ := Lx.instrTime_boundaryWalk_of_launch hl
  have hwj : w.2.2[j]? = some (Sum.inl (θ, ⊤)) := by rw [hi, hθ', htop]
  have hpieces := pieces_run_capSpec_succ hjl.le hwj D hl (q : ℝ≥0∞)
  -- the capped run launches at `j` too
  have hlc : (ExplState.run κ b jumps sc D (j + 1)).2.2.2.1 j = some (c, θ') := by
    rw [launches_run_capSpec_succ hjl.le hwj]; exact hl
  obtain ⟨-, hec, -⟩ := eq_launch_of_launches sc D hlc
  have harcs : (ExplState.run κ b jumps sc D (j + 1)).2.1 = (ExplState.run κ b jumps w D j).2.1 := by
    rw [hec, GW2aCont.arcs_launch, run_capSpec_of_le hjl.le D le_rfl]
  -- the tip set of the capped piece
  have hmin : min (q : ℝ≥0∞) (D j).2 = q := min_eq_left hq.le
  have hαq : IsGeneratingTrace (D j).1 (q : ℝ≥0∞) α := BRLeaf.isGeneratingTrace_of_le hα hq.le
  have hWcq : ContinuousOn (D j).1 {s | (s : ℝ≥0∞) ≤ (q : ℝ≥0∞)} :=
    hWc.mono fun s (hs : (s : ℝ≥0∞) ≤ q) => show (s : ℝ≥0∞) ≤ (D j).2 from hs.trans hq.le
  have hWlt : ContinuousOn (D j).1 {s | (s : ℝ≥0∞) < (D j).2} :=
    hWc.mono fun s (hs : (s : ℝ≥0∞) < (D j).2) => show (s : ℝ≥0∞) ≤ (D j).2 from hs.le
  have hcs : c = (ExplState.run κ b jumps w D j).2.2.2.2.1 := hcr
  have htip : (recPiece (ExplState.run κ b jumps w D j) (D j) (q : ℝ≥0∞)).1.tipSet
      (recPiece (ExplState.run κ b jumps w D j) (D j) (q : ℝ≥0∞)).2.1
      (recPiece (ExplState.run κ b jumps w D j) (D j) (q : ℝ≥0∞)).2.2 = gc '' (α '' Icc 0 q) := by
    show ((ExplState.run κ b jumps w D j).2.2.2.2.1).tipSet
      (fun r : ℝ≥0 => (D j).1 (min (r : ℝ≥0∞) (min (q : ℝ≥0∞) (D j).2)).toNNReal) (min (q : ℝ≥0∞) (D j).2) = _
    rw [hmin, ← hcs]
    rw [CounterflowRange.tipSet_stopped_eq_of_tendsto (f := gc) hαq hWcq hW0 fun t ht => ?_]
    · have hset : {t : ℝ≥0 | (t : ℝ≥0∞) ≤ (q : ℝ≥0∞)} = Icc 0 q := by
        ext t
        simp only [mem_setOf_eq, mem_Icc, zero_le, true_and, ENNReal.coe_le_coe]
      rw [hset]
    · have hαH : α t ∈ Hbar := Sec7.IsGeneratingTrace.mem_Hbar hα hWlt hW0 (ht.trans hq.le)
      refine ((hgc _ hαH).tendsto.mono_left (nhdsWithin_mono _ fun z hz =>
        le_of_lt (show (0 : ℝ) < z.im from hz))).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with z hz using hgi hz
  show {((sc.1 : ℝ) : ℂ)} ∪ (⋃ p ∈ (ExplState.run κ b jumps sc D (j + 1)).1, p.1.tipSet p.2.1 p.2.2) ∪
    ⋃ a ∈ (ExplState.run κ b jumps sc D (j + 1)).2.1, ((↑) : ℝ → ℂ) '' a =
    {((w.1 : ℝ) : ℂ)} ∪ (⋃ p ∈ (ExplState.run κ b jumps w D j).1, p.1.tipSet p.2.1 p.2.2) ∪
      (⋃ a ∈ (ExplState.run κ b jumps w D j).2.1, ((↑) : ℝ → ℂ) '' a) ∪ gc '' (α '' Icc 0 q)
  rw [hpieces, harcs]
  ext z
  simp only [mem_union, mem_iUnion, List.mem_append, List.mem_singleton, exists_prop]
  constructor
  · rintro ((h | ⟨p, hp | rfl, hz⟩) | h)
    · exact Or.inl (Or.inl (Or.inl h))
    · exact Or.inl (Or.inl (Or.inr ⟨p, hp, hz⟩))
    · exact Or.inr (htip ▸ hz)
    · exact Or.inl (Or.inr h)
  · rintro (((h | ⟨p, hp, hz⟩) | h) | h)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr ⟨p, Or.inl hp, hz⟩)
    · exact Or.inr h
    · exact Or.inl (Or.inr ⟨_, Or.inr rfl, htip.symm ▸ h⟩)

end InteractingSLE.Theorem14.SB.S3.Asm

namespace InteractingSLE.Theorem14.SB.S3.Asm

open Exist.Staged Exist.StagedLaw Restart WalkSide Geo Canon GW1Bookkeep

/-- **The second side of the lower-tail comparison at one sample** (deterministic). For the lower walk run with
drivers `D` (regular launched pieces), a piece launched at `j` with the run-chart package of its launch chart `c`
(domain chart of `ℍ ∖ fill P` with `P` the walk's prefix, hull model `c + s₁`, finite-fibre boundary map `ĝ` within
bounded distance of the identity), its generating trace `α` cut at the own time `q` with `α(q) ∈ ℍ`, and a split of
the range of a proper parametrization `β₀` of the walk at `ĝ(α(q)) = β₀(σ)`: the capped program's physical prefix
after `j + 1` instructions is `β₀([0, σ])`, and from the capped stage's mean (word `β₂`, harmonic representative
`v₂`) and its physical side labels, the second inputs of `exists_protectedWordComparison_lower` hold — a core chart
`(f, Φ)` of `β₀` up to `σ`, holomorphic with finite fibres and open domain, a hull model `f + e₂`, the mean formula
with the canonical logarithm of `fill β₀([0, σ])`, and the lower-walk side labels at interior landings of `Φ`. -/
theorem second_sample_facts_walk {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hreg : ∀ k c θ', (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) D (k + 1)).2.2.2.1 k =
        some (c, θ') → GW1P.PieceRegular (D k).1
          (min (instrTime (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k) (D k).2))
    {j : ℕ} {c : Chart} {θ' : ℝ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) D (j + 1)).2.2.2.1 j =
      some (c, θ'))
    {s₁ Cg : ℝ} {gc : ℂ → ℂ}
    (hD : IsDomainChart (H \ fillH (statePhysicalSet 0
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) D j))) c)
    (hPc : IsCompact (statePhysicalSet 0
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) D j)))
    (hPh : IsHPHull (fillH (statePhysicalSet 0
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) D j))))
    (hmo : IsMapOut (fillH (statePhysicalSet 0
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) D j))) (fun z => c.1 z + (s₁ : ℂ)))
    (hgc : ContinuousOn gc Hbar) (hgi : EqOn gc c.2.1 H) (hC' : ∀ p ∈ Hbar, ‖gc p - p‖ ≤ Cg)
    (hgf : ∀ z, (gc ⁻¹' {z} ∩ {v | 0 ≤ v.im}).Finite)
    (h0P : (0 : ℂ) ∈ statePhysicalSet 0
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) D j))
    {α : ℝ≥0 → ℂ} (hα : IsGeneratingTrace (D j).1 (D j).2 α) (hinj : InjOn α {t | (t : ℝ≥0∞) ≤ (D j).2})
    {q : ℝ≥0} (hq : (q : ℝ≥0∞) < (D j).2) (hq0 : 0 < q) (hαq : α q ∈ H)
    (hPc' : IsPreconnected (statePhysicalSet 0
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) D j) ∪ gc '' (α '' Icc 0 q)))
    {β₀ : ℝ≥0 → ℂ} (hβ : Supp9B.IsProperCurve β₀) (hβ0 : β₀ 0 = 0)
    (hsplit : ∃ T : Set ℂ, range β₀ = (statePhysicalSet 0
        (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) D j) ∪ gc '' (α '' Icc 0 q)) ∪ T ∧
      IsPreconnected T ∧ ¬ Bornology.IsBounded T ∧ gc (α q) ∈ T ∧
      ∀ z ∈ T, z ∈ statePhysicalSet 0
        (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) D j) ∪ gc '' (α '' Icc 0 q) →
        z = gc (α q))
    {σ : ℝ≥0} (hσ : β₀ σ = gc (α q))
    {β₂ : BoundaryWord} {v₂ u₀ : ℂ → ℝ}
    (hmean : EqOn (fun z => v₂ z + u₀ z + chiC κ * (ExplState.run κ b jumps
        (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j (-(Real.pi / 2)) q) D (j + 1)).2.2.2.2.1.2.2 z)
      (fun z => β₂.mean ((ExplState.run κ b jumps
        (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j (-(Real.pi / 2)) q) D (j + 1)).2.2.2.2.1.1 z))
      (ExplState.run κ b jumps
        (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j (-(Real.pi / 2)) q) D (j + 1)).2.2.2.2.1.dom)
    (hside : HasInteriorStageSides κ b jumps
      (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j (-(Real.pi / 2)) q) D (j + 1) β₂) :
    β₀ '' Icc 0 σ = prefixPhysSet κ b jumps
      (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j (-(Real.pi / 2)) q) D (j + 1) ∧
    ∃ (f Φ : ℂ → ℂ) (e₂ : ℝ),
      IsChartCore β₀ σ f Φ ∧ DifferentiableOn ℂ f (H \ fillH (β₀ '' Icc 0 σ)) ∧
      (∀ z, (Φ ⁻¹' {z} ∩ {v | 0 ≤ v.im}).Finite) ∧ IsOpen (H \ fillH (β₀ '' Icc 0 σ)) ∧
      IsMapOut (fillH (β₀ '' Icc 0 σ)) (fun z => f z + (e₂ : ℂ)) ∧
      EqOn (fun z => v₂ z + u₀ z + chiC κ * (canonDerivLog (fillH (β₀ '' Icc 0 σ)) z).im)
        (fun z => β₂.mean (f z)) (H \ fillH (β₀ '' Icc 0 σ)) ∧
      ∀ y : ℝ, y ∉ β₂.jumps → Φ y ∈ H → Lh.SideH κ [(-(Real.pi / 2), 0)] (β₂.fn y) := by
  set w := boundaryWalkSpec b jumps (-(Real.pi / 2)) true with hw
  set sc := capSpec w j (-(Real.pi / 2)) (q : ℝ≥0∞) with hsc
  set P := statePhysicalSet 0 (ExplState.run κ b jumps w D j) with hPdef
  obtain ⟨hi, -, hcr⟩ := eq_launch_of_launches w D hl
  have hjl : j < w.2.2.length := by
    by_contra hc
    rw [List.getElem?_eq_none (not_lt.1 hc)] at hi
    cases hi
  have hθ' : θ' = -(Real.pi / 2) := angle_eq_of_mem_boundaryWalkSpec (List.mem_of_getElem? hi)
  have htop : instrTime w j = ⊤ := Lx.instrTime_boundaryWalk_of_launch hl
  have hwj : w.2.2[j]? = some (Sum.inl (-(Real.pi / 2), ⊤)) := by rw [hi, hθ', htop]
  have hPR := hreg j c θ' hl
  rw [htop, min_top_left] at hPR
  obtain ⟨hW0, hWc, -⟩ := hPR
  have hw' : ContinuousOn (D j).1 {s | (s : ℝ≥0∞) < (D j).2} :=
    hWc.mono fun s (hs : (s : ℝ≥0∞) < (D j).2) => show (s : ℝ≥0∞) ≤ (D j).2 from hs.le
  -- the physical prefix is the initial arc of `β₀`
  obtain ⟨T, hr, hTc, hTu, hqT, hTP⟩ := hsplit
  have hqmem : gc (α q) ∈ P ∪ gc '' (α '' Icc 0 q) := Or.inr ⟨α q, ⟨q, ⟨zero_le, le_rfl⟩, rfl⟩, rfl⟩
  have hβeq : β₀ '' Icc 0 σ = P ∪ gc '' (α '' Icc 0 q) :=
    Walk.image_Icc_eq_of_split hβ hβ0 hr hTc hTu (hσ ▸ hqT) (fun z hz hzP => hσ ▸ hTP z hz hzP) hPc'
      (Or.inl h0P) (hσ ▸ hqmem)
  have hpre : prefixPhysSet κ b jumps sc D (j + 1) = P ∪ gc '' (α '' Icc 0 q) :=
    prefixPhysSet_capSpec_succ hl hgc hgi hα hW0 hWc hq
  refine ⟨hβeq.trans hpre.symm, ?_⟩
  -- the composed core chart
  have hη0 : (β₀ 0).im = 0 := by rw [hβ0, Complex.zero_im]
  obtain ⟨hcore, hfd, hfin, hDo, hmo₂⟩ := comp_chart_facts hD hPc hPh hmo hgc hgi hC' hgf hα hw' hW0 hinj hq hq0 hαq
    hβ.1.continuousOn hη0 (by rw [hβeq]) hσ (by rw [hβeq]; exact subset_union_right)
    (fun x hx => by rw [hβeq]; exact Or.inl (Walk.boundary_mem_of_mem_H hPc.isClosed hD hgc hgi hx))
  set W' : ℝ → ℝ := fun r : ℝ => (D j).1 r.toNNReal with hW'def
  set f : ℂ → ℂ := fun z => fwdMap W' q (c.1 z) with hfdef
  set Φ : ℂ → ℂ := fun v => gc (extendFrom H (fwdMapInv W' q) v) with hΦdef
  -- the capped run chart is the composed chart
  set c₂ := (ExplState.run κ b jumps sc D (j + 1)).2.2.2.2.1 with hc₂
  have hmin : min (q : ℝ≥0∞) (D j).2 = q := min_eq_left hq.le
  have hc₂form : c₂ = c.loewner
      (fun x : ℝ => (D j).1 (min ((x.toNNReal : ℝ≥0) : ℝ≥0∞) (min (q : ℝ≥0∞) (D j).2)).toNNReal)
      ((min (q : ℝ≥0∞) (D j).2).toNNReal : ℝ) := by
    rw [hc₂, chart_run_capSpec_succ hjl.le hwj D hl q, ← hcr]
  set Ws : ℝ → ℝ := fun x : ℝ => (D j).1 (min ((x.toNNReal : ℝ≥0) : ℝ≥0∞) (min (q : ℝ≥0∞) (D j).2)).toNNReal
    with hWsdef
  have hWs : ∀ x : ℝ, Ws x = (D j).1 (min x.toNNReal q) := fun x => by
    simp only [hWsdef, hmin, ← ENNReal.coe_min, ENNReal.toNNReal_coe]
  have hT : ((min (q : ℝ≥0∞) (D j).2).toNNReal : ℝ) = q := by rw [hmin, ENNReal.toNNReal_coe]
  have hDc' : ContinuousOn (D j).1 (Iic q) := by
    refine hWc.mono fun s (hs : s ≤ q) => ?_
    show (s : ℝ≥0∞) ≤ (D j).2
    exact (ENNReal.coe_le_coe.2 hs).trans hq.le
  have hWsc : Continuous Ws := by
    have h1 : Continuous fun x : ℝ => min x.toNNReal q := continuous_real_toNNReal.min continuous_const
    have h2 : Continuous fun x : ℝ => (D j).1 (min x.toNNReal q) :=
      hDc'.comp_continuous h1 fun x => Set.mem_Iic.2 (min_le_right _ _)
    exact h2.congr fun x => (hWs x).symm
  have hWs0 : Ws 0 = 0 := by rw [hWs, Real.toNNReal_zero, min_eq_left zero_le, hW0]
  have heqI : ∀ r ∈ Icc (0 : ℝ) q, Ws r = W' r := fun r hr => by
    have hr' : r.toNNReal ≤ q := Real.toNNReal_le_iff_le_coe.2 hr.2
    rw [hWs, min_eq_left hr']
  have hfwd : fwdMap Ws q = fwdMap W' q := QuantumZipper.CharFunRhs.fwdMap_eq_of_eqOn heqI
  obtain ⟨t'', hqt'', ht''ζ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hq
  have hW'c : ContinuousOn W' (Icc 0 (t'' : ℝ)) := by
    refine hw'.comp continuous_real_toNNReal.continuousOn fun r hr => ?_
    show ((r.toNNReal : ℝ≥0) : ℝ≥0∞) < (D j).2
    exact lt_of_le_of_lt (ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hr.2)) ht''ζ
  have hinv : ∀ v, fwdMapInv Ws q v = fwdMapInv W' q v := fun v =>
    LocalExt.fwdMapInv_congr_of_continuousOn hWsc.continuousOn hW'c q.2 (by exact_mod_cast hqt'') heqI v
  have hc₂1 : c₂.1 = f := funext fun z => by
    rw [hc₂form]
    show fwdMap Ws ((min (q : ℝ≥0∞) (D j).2).toNNReal : ℝ) (c.1 z) = _
    rw [hT, hfwd]
  have hΦc : ContinuousOn (fwdMapInv W' q) H := by
    have h := continuousOn_fwdMapInv hWsc hWs0 q.2
    exact h.congr fun v _ => (hinv v).symm
  have hΦH : ∀ v ∈ H, extendFrom H (fwdMapInv W' q) v = fwdMapInv W' q v := extendFrom_extends hΦc
  obtain ⟨hchα, -⟩ := secondChart_facts hα hw' hW0 hinj hq hq0
  have hc₂2 : EqOn c₂.2.1 Φ H := fun v hv => by
    have hm : fwdMapInv W' q v ∈ H := by
      have := (IsChart.toCore hchα).inv_mem hv
      rw [hΦH v hv] at this
      exact this.1
    rw [hc₂form]
    show c.2.1 (fwdMapInv Ws ((min (q : ℝ≥0∞) (D j).2).toNNReal : ℝ) v) = gc (extendFrom H (fwdMapInv W' q) v)
    rw [hT, hinv, hΦH v hv, hgi hm]
  -- the chart domain is `ℍ ∖ fill β₀[0, σ]`
  have hregc := pieceRegular_capSpec D hjl.le hwj hreg q
  have hcc : c₂.IsConformal :=
    (GW2aCont.isConformal_runChart (κ := κ) (b := b) (jumps := jumps) sc D (j + 1)
      fun k _ c' θ'' h => hregc k c' θ'' h).1
  set F := fillH (β₀ '' Icc 0 σ) with hF
  have hdom : (c₂.dom : Set ℂ) = H \ F := by
    rw [hcc.coe_dom]
    ext z
    constructor
    · rintro ⟨v, hv, rfl⟩
      rw [hc₂2 hv]
      exact hcore.inv_mem hv
    · intro hz
      refine ⟨f z, hcore.maps hz, ?_⟩
      rw [hc₂2 (hcore.maps hz)]
      exact hcore.inv_f z hz
  obtain ⟨M⟩ := WalkIntCanon.exists_hullModel_runChart (κ := κ) (b := b) (jumps := jumps) sc D (j + 1)
    fun k _ => hregc k
  have hN := WalkIntCanon.isNormalized_runChart (κ := κ) (b := b) (jumps := jumps) sc D (j + 1)
    fun k _ c' θ'' h => hregc k c' θ'' h
  have hMF : M.hull = F := by
    have h1 : H \ M.hull = H \ F := M.dom_eq.symm.trans hdom
    have hM : M.hull ⊆ H := M.isHull.1
    have hFH : F ⊆ H := fun z hz => hz.1
    ext z
    constructor
    · intro hz
      by_contra hzF
      have : z ∈ H \ F := ⟨hM hz, hzF⟩
      rw [← h1] at this
      exact this.2 hz
    · intro hz
      by_contra hzM
      have : z ∈ H \ M.hull := ⟨hFH hz, hzM⟩
      rw [h1] at this
      exact this.2 hz
  refine ⟨f, Φ, W' q + s₁, hcore, hfd, hfin, hDo, ?_, ?_, ?_⟩
  · have e : (fun z => f z + ((W' q + s₁ : ℝ) : ℂ)) =
        fun z => fwdMap (fun r : ℝ => (D j).1 r.toNNReal) q (c.1 z) + (((D j).1 q + s₁ : ℝ) : ℂ) := by
      funext z
      simp [hfdef, hW'def]
    rw [e]
    exact hmo₂
  · intro z hz
    have hzd : z ∈ (c₂.dom : Set ℂ) := by rw [hdom]; exact hz
    have he := hmean hzd
    have hlift := M.lift_eq_canonDerivLog hN (show z ∈ H \ M.hull by rw [hMF]; exact hz)
    simp only at he ⊢
    rw [← hMF, ← hc₂1]
    show v₂ z + u₀ z + chiC κ * (canonDerivLog M.hull z).im = β₂.mean (c₂.1 z)
    have hl' : c₂.2.2 z = (canonDerivLog M.hull z).im := hlift
    rw [← hl']
    exact he
  · intro y hy hyH
    have hyb : (y : ℂ) ∈ Hbar := by simp [Hbar]
    have hlim : Tendsto c₂.2.1 (𝓝[H] (y : ℂ)) (𝓝 (Φ y)) := by
      refine ((hcore.inv_cont _ hyb).tendsto.mono_left (nhdsWithin_mono _ fun z hz =>
        le_of_lt (show (0 : ℝ) < z.im from hz))).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with z hz using (hc₂2 hz).symm
    have hbd : LuM.bdVal c₂ (y : ℂ) = Φ y := LuM.bdVal_eq_of_tendsto (by simp) hlim
    have hyH' : LuM.bdVal c₂ (y : ℂ) ∈ H := by rw [hbd]; exact hyH
    exact StageSide.sideH_cap (hside y hy hyH')

end InteractingSLE.Theorem14.SB.S3.Asm

namespace InteractingSLE.Theorem14.SB.S3.Asm

open Exist.Staged Exist.StagedLaw Restart WalkSide Geo Canon GW1Bookkeep

/-- **A point of `ℍ` on a run's physical set lies on a recorded piece**: on the tip set of the piece of some launch
`ℓ < n`, launched in the run chart before `ℓ`. -/
theorem exists_piece_of_mem_H {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {spec : ExplSpec}
    {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {n : ℕ} {x : ℝ} {z : ℂ}
    (hz : z ∈ statePhysicalSet x (ExplState.run κ b jumps spec D n)) (hzH : z ∈ H) :
    ∃ ℓ < n, ∃ θ' : ℝ, (ExplState.run κ b jumps spec D (ℓ + 1)).2.2.2.1 ℓ =
        some ((ExplState.run κ b jumps spec D ℓ).2.2.2.2.1, θ') ∧
      z ∈ (recPiece (ExplState.run κ b jumps spec D ℓ) (D ℓ) (instrTime spec ℓ)).1.tipSet
        (recPiece (ExplState.run κ b jumps spec D ℓ) (D ℓ) (instrTime spec ℓ)).2.1
        (recPiece (ExplState.run κ b jumps spec D ℓ) (D ℓ) (instrTime spec ℓ)).2.2 := by
  rcases hz with (hz | hz) | hz
  · rw [mem_singleton_iff.1 hz] at hzH
    exact absurd hzH (WalkPiece.ofReal_notMem_H x)
  · obtain ⟨pc, hpc, hzp⟩ := mem_iUnion₂.1 hz
    obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hpc
    obtain ⟨ℓ, hℓ, θ', hl, -, rfl⟩ := exists_launch_of_pieces_eq spec D n hsplit
    exact ⟨ℓ, hℓ, θ', hl, hzp⟩
  · obtain ⟨a, -, y, -, rfl⟩ := mem_iUnion₂.1 hz
    exact absurd hzH (WalkPiece.ofReal_notMem_H y)

open Lk in
/-- **A launched walk piece's points of `ℍ` come from trace points in `ℍ`** (piece simplicity in tip-set form,
`Lk.tip_inter_old_real`, and interior boundary values of the launch chart lying on the prefix). -/
theorem trace_mem_H_of_piece_mem_H {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hW : WalkChainFacts κ b jumps (-(Real.pi / 2)) D) {j : ℕ} {c : Chart} {θ' : ℝ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) D (j + 1)).2.2.2.1 j =
      some (c, θ'))
    (hD : IsDomainChart (H \ fillH (statePhysicalSet 0
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) D j))) c)
    (hPc : IsCompact (statePhysicalSet 0
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) D j)))
    {gc : ℂ → ℂ} (hgc : ContinuousOn gc Hbar) (hgi : EqOn gc c.2.1 H)
    {α : ℝ≥0 → ℂ} (hα : IsGeneratingTrace (D j).1 (D j).2 α) (hW0 : (D j).1 0 = 0)
    (hWc : ContinuousOn (D j).1 {s | (s : ℝ≥0∞) ≤ (D j).2})
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) ≤ (D j).2) (htH : gc (α t) ∈ H) : α t ∈ H := by
  set w := boundaryWalkSpec b jumps (-(Real.pi / 2)) true with hw
  have hWlt : ContinuousOn (D j).1 {s | (s : ℝ≥0∞) < (D j).2} :=
    hWc.mono fun s (hs : (s : ℝ≥0∞) < (D j).2) => show (s : ℝ≥0∞) ≤ (D j).2 from hs.le
  have hαH : α t ∈ Hbar := Sec7.IsGeneratingTrace.mem_Hbar hα hWlt hW0 ht
  by_contra hn
  have him : (α t).im = 0 := le_antisymm (not_lt.1 hn) hαH
  have hαr : α t = (((α t).re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [him])
  have hP : gc (α t) ∈ statePhysicalSet 0 (ExplState.run κ b jumps w D j) := by
    rw [hαr] at htH ⊢
    exact Walk.boundary_mem_of_mem_H hPc.isClosed hD hgc hgi htH
  have hcs : c = stChart (ExplState.run κ b jumps w D j) := (eq_launch_of_launches w D hl).2.2
  have htip : gc (α t) ∈ (newPc (ExplState.run κ b jumps w D j) (D j)).1.tipSet
      (newPc (ExplState.run κ b jumps w D j) (D j)).2.1 (newPc (ExplState.run κ b jumps w D j) (D j)).2.2 := by
    show gc (α t) ∈ (stChart (ExplState.run κ b jumps w D j)).tipSet
      (fun r : ℝ≥0 => (D j).1 (min (r : ℝ≥0∞) (min ⊤ (D j).2)).toNNReal) (min ⊤ (D j).2)
    rw [min_top_left, ← hcs]
    rw [CounterflowRange.tipSet_stopped_eq_of_tendsto (f := gc) hα hWc hW0 fun t' ht' => ?_]
    · exact ⟨α t, ⟨t, ht, rfl⟩, rfl⟩
    · have hαH' : α t' ∈ Hbar := Sec7.IsGeneratingTrace.mem_Hbar hα hWlt hW0 ht'
      refine ((hgc _ hαH').tendsto.mono_left (nhdsWithin_mono _ fun z hz =>
        le_of_lt (show (0 : ℝ) < z.im from hz))).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with z hz using hgi hz
  have hl' : (ExplState.run κ b jumps w D (j + 1)).2.2.2.1 j ≠ none := by
    rw [hl]; exact Option.some_ne_none _
  have hre := tip_inter_old_real hW hl' ⟨htip, hP⟩
  exact absurd htH (by
    show ¬ (0 : ℝ) < (gc (α t)).im
    rw [show (gc (α t)).im = 0 from hre]
    exact lt_irrefl 0)

end InteractingSLE.Theorem14.SB.S3.Asm
