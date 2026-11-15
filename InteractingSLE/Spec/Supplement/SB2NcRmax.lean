/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2NcOff
import InteractingSLE.Spec.Supplement.SBTail2SidePhys

/-!
# F2b′: the right end `R = max (A ∩ ℝ)` of the upper prefix, read measurably

Packet PROVE-AUX61-NOJUMP (round 21, D34, component A). The relative piece's seed `R` is the largest real point of
the upper prefix `A`. It is random; this file reads it measurably from the dense codes of the pieces and the real
connectors (`Side.exists_measurable_piece_dense_code`, `Side.exists_measurable_arc_dense_code`):

* `rayC q = [q, ∞) ⊆ ℝ ⊆ ℂ`, `HitRay G q` (the code `G` comes within distance `0` of the ray) and `hitRay_iff` (for
  a compact closure, this is a real point `≥ q` in the closure);
* **`codeMax`**: `⨆_{q ∈ ℚ} q · 1[q ≤ 0 or some code hits the ray at q]`, and `codeMax_eq` (it is the largest real
  point of `[u, 0] ∪ ⋃ closure (range code)` when that set is compact);
* **`exists_measurable_realMax_upper`**: a measurable `Rt` with `Rt = max (A ∩ ℝ)` almost surely where `A` is
  compact.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.SB.Nc

open Exist Exist.Staged Exist.StagedLaw GW1Bookkeep Mz

/-! ### Rays and hits -/

/-- The closed real ray `[q, ∞)` in `ℂ`. -/
def rayC (q : ℝ) : Set ℂ := {z | z.im = 0 ∧ q ≤ z.re}

theorem isClosed_rayC (q : ℝ) : IsClosed (rayC q) :=
  (isClosed_eq Complex.continuous_im continuous_const).inter (isClosed_le continuous_const Complex.continuous_re)

/-- The code `G` comes within distance `0` of the ray `[q, ∞)`. -/
def HitRay {ι : Type*} (G : ι → ℂ) (q : ℝ) : Prop := ⨅ i, infEDist (G i) (rayC q) = 0

theorem hitRay_iff {ι : Type*} {G : ι → ℂ} (hc : IsCompact (closure (range G))) (q : ℝ) :
    HitRay G q ↔ ∃ x : ℝ, q ≤ x ∧ (x : ℂ) ∈ closure (range G) := by
  constructor
  · intro h
    by_cases hne : (closure (range G)).Nonempty
    · obtain ⟨p, hp, hmin⟩ := hc.exists_isMinOn hne continuous_infEDist.continuousOn
      have hp0 : infEDist p (rayC q) = 0 := by
        refine le_antisymm ?_ zero_le
        rw [← h]
        exact le_iInf fun i => hmin (subset_closure (mem_range_self i))
      rw [← mem_iff_infEDist_zero_of_closed (isClosed_rayC q)] at hp0
      refine ⟨p.re, hp0.2, ?_⟩
      have e : ((p.re : ℝ) : ℂ) = p := Complex.ext (by simp) (by simp [hp0.1])
      rw [e]; exact hp
    · exfalso
      have hι : IsEmpty ι := ⟨fun i => hne ⟨G i, subset_closure (mem_range_self i)⟩⟩
      simp [HitRay] at h
  · rintro ⟨x, hx, hxc⟩
    refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_) zero_le
    obtain ⟨_, ⟨i, rfl⟩, hi⟩ := EMetric.mem_closure_iff.1 hxc ε (by exact_mod_cast hε)
    have hxr : (x : ℂ) ∈ rayC q := ⟨by simp, by simpa using hx⟩
    calc ⨅ j, infEDist (G j) (rayC q) ≤ infEDist (G i) (rayC q) := iInf_le _ i
      _ ≤ infEDist (x : ℂ) (rayC q) + edist (G i) (x : ℂ) := infEDist_le_infEDist_add_edist
      _ = edist (G i) (x : ℂ) := by rw [infEDist_zero_of_mem hxr, zero_add]
      _ ≤ 0 + ε := by rw [edist_comm, zero_add]; exact hi.le

theorem measurableSet_hitRay {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι] {G : Ω → ι → ℂ}
    (hG : ∀ i, Measurable fun ω => G ω i) (q : ℝ) : MeasurableSet {ω | HitRay (G ω) q} :=
  (Measurable.iInf fun i => measurable_infEDist.comp (hG i)) (measurableSet_singleton 0)

/-! ### The largest real point from codes -/

/-- The largest real point of a compact set is in it (when it has a real point). -/
theorem realMax_mem {X : Set ℂ} (hX : IsCompact X) {x : ℝ} (hx : (x : ℂ) ∈ X) : ((realMax X : ℝ) : ℂ) ∈ X := by
  have hS : IsCompact {y : ℝ | (y : ℂ) ∈ X} :=
    Complex.isometry_ofReal.isClosedEmbedding.isCompact_preimage hX
  exact hS.sSup_mem ⟨x, hx⟩

open Classical in
/-- **The code maximum**: the supremum of the rationals `q` such that `q ≤ 0` or one of the codes `G j`, `j < k`,
hits the ray `[q, ∞)` (other rationals contribute `0`). -/
def codeMax {ι : Type*} (G : ℕ → ι → ℂ) (k : ℕ) : ℝ :=
  ⨆ q : ℚ, if (q : ℝ) ≤ 0 ∨ ∃ j < k, HitRay (G j) q then (q : ℝ) else 0

/-- **The code maximum is the largest real point** of `[u, 0] ∪ ⋃_{j < k} closure (range (G j))` when this set is
compact. -/
theorem codeMax_eq {ι : Type*} {G : ℕ → ι → ℂ} {k : ℕ} {u : ℝ} (hu : u ≤ 0) {X : Set ℂ} (hX : IsCompact X)
    (hXe : X = ((↑) : ℝ → ℂ) '' Icc u 0 ∪ ⋃ j ∈ Finset.range k, closure (range (G j))) :
    codeMax G k = realMax X := by
  classical
  have h0 : ((0 : ℝ) : ℂ) ∈ X := by rw [hXe]; exact Or.inl ⟨0, ⟨hu, le_rfl⟩, rfl⟩
  have hR0 : 0 ≤ realMax X := Lx.le_realMax_of_mem hX h0
  have hsub : ∀ j < k, closure (range (G j)) ⊆ X := fun j hj => by
    rw [hXe]; exact subset_union_of_subset_right (subset_biUnion_of_mem (u := fun j => closure (range (G j)))
      (Finset.mem_coe.2 (Finset.mem_range.2 hj))) _
  have hkey : ∀ q : ℝ, (q ≤ 0 ∨ ∃ j < k, HitRay (G j) q) ↔ q ≤ realMax X := by
    intro q
    constructor
    · rintro (hq | ⟨j, hj, hh⟩)
      · exact hq.trans hR0
      · obtain ⟨x, hqx, hx⟩ := (hitRay_iff (hX.of_isClosed_subset isClosed_closure (hsub j hj)) q).1 hh
        exact hqx.trans (Lx.le_realMax_of_mem hX (hsub j hj hx))
    · intro hq
      have hm := (Set.ext_iff.1 hXe _).1 (realMax_mem hX h0)
      rcases hm with ⟨y, hy, hye⟩ | hm
      · left
        have : y = realMax X := by exact_mod_cast hye
        exact hq.trans (this ▸ hy.2)
      · obtain ⟨j, hj, hjm⟩ := mem_iUnion₂.1 hm
        have hj' := Finset.mem_range.1 hj
        exact Or.inr ⟨j, hj', (hitRay_iff (hX.of_isClosed_subset isClosed_closure (hsub j hj')) q).2
          ⟨realMax X, hq, hjm⟩⟩
  have hf : (fun q : ℚ => if (q : ℝ) ≤ 0 ∨ ∃ j < k, HitRay (G j) q then (q : ℝ) else 0) =
      fun q : ℚ => if (q : ℝ) ≤ realMax X then (q : ℝ) else 0 := by
    funext q
    exact if_congr (hkey q) rfl rfl
  unfold codeMax
  rw [hf]
  have hle : ∀ q : ℚ, (if (q : ℝ) ≤ realMax X then (q : ℝ) else 0) ≤ realMax X := fun q => by
    split_ifs with hq
    · exact hq
    · exact hR0
  have hbdd : BddAbove (range fun q : ℚ => if (q : ℝ) ≤ realMax X then (q : ℝ) else 0) :=
    ⟨realMax X, by rintro _ ⟨q, rfl⟩; exact hle q⟩
  refine le_antisymm (ciSup_le hle) ?_
  by_contra hlt
  push Not at hlt
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlt
  have := le_ciSup hbdd q
  simp only [hq2.le, ↓reduceIte] at this
  linarith

theorem measurable_codeMax {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι] {G : Ω → ℕ → ι → ℂ}
    (hG : ∀ j i, Measurable fun ω => G ω j i) (k : ℕ) : Measurable fun ω => codeMax (G ω) k := by
  classical
  refine Measurable.iSup fun q => Measurable.ite ?_ measurable_const measurable_const
  have e : {ω | (q : ℝ) ≤ 0 ∨ ∃ j < k, HitRay (G ω j) q} =
      {_ω | (q : ℝ) ≤ 0} ∪ ⋃ j, ({_ω | j < k} ∩ {ω | HitRay (G ω j) q}) := by
    ext ω
    simp only [mem_ofPred_eq, mem_union, mem_iUnion, mem_inter_iff]
  rw [e]
  exact (MeasurableSet.const _).union (MeasurableSet.iUnion fun j =>
    (MeasurableSet.const _).inter (measurableSet_hitRay (fun i => hG j i) q))

/-! ### The upper prefix -/

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- **The right end of the upper prefix is almost surely a measurable function** where the prefix is compact. -/
theorem exists_measurable_realMax_upper (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type u}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {u : ℝ} {l : List (ℝ × ℝ≥0)}
    (hEm : ∀ j, Measurable (E (Lu.upperSpec u l) j))
    (hR : StagedPiecesRegular κ b jumps P (Lu.upperSpec u l) (E (Lu.upperSpec u l))) (hu : u ≤ 0) (k : ℕ) :
    ∃ Rt : Ω → ℝ, Measurable Rt ∧ ∀ᵐ ω ∂P, IsCompact (upperPrefix κ b jumps E u l k ω) →
      Rt ω = realMax (upperPrefix κ b jumps E u l k ω) := by
  classical
  set su := Lu.upperSpec u l with hsudef
  set E' := StagedReg.regHist su (E su) with hE'def
  have hR' := WalkLaw.stagedPiecesRegular_regHist hR
  obtain ⟨M, hMae, hMm, hMp⟩ := hR'.ae_pieceRegular.exists_measurable_mem
  obtain ⟨T, hTm, hT⟩ := Side.exists_measurable_piece_dense_code hb su
    (E := E') (StagedReg.measurable_regHist hEm) StagedReg.isRegularDriver_regHist hMm hMp
  obtain ⟨A, hAm, hA⟩ := Side.exists_measurable_arc_dense_code (κ := κ) hb su
    (E := E') (StagedReg.measurable_regHist hEm) StagedReg.isRegularDriver_regHist
  set G : Ω → ℕ → (Unit ⊕ (ℕ × ℕ)) ⊕ (Unit ⊕ ℚ) → ℂ := fun ω j => Sum.elim (T j ω) (A j ω) with hGdef
  have hGm : ∀ j i, Measurable fun ω => G ω j i := by
    rintro j (i | i)
    · exact hTm j i
    · exact hAm j i
  refine ⟨fun ω => codeMax (G ω) k, measurable_codeMax hGm k, ?_⟩
  filter_upwards [hMae, StagedReg.ae_run_regHist hR] with ω hωM hrun hc
  refine codeMax_eq hu hc ?_
  have hsu1 : su.1 = u := rfl
  have hU : ((u : ℝ) : ℂ) ∈ ((↑) : ℝ → ℂ) '' Icc u 0 := ⟨u, ⟨le_rfl, hu⟩, rfl⟩
  have hpre : SB.prefixPhysSet κ b jumps su (fun j => E su j ω) k =
      statePhysicalSet u (ExplState.run κ b jumps su (fun j => E' j ω) k) := by
    unfold SB.prefixPhysSet statePhysicalSet
    rw [hrun k]
    rfl
  have hcl : ∀ j, closure (range (G ω j)) = ({(u : ℂ)} ∪ GW2aCont.pieceTips κ b jumps su (fun i => E' i ω) j) ∪
      ({(u : ℂ)} ∪ ((↑) : ℝ → ℂ) '' GW2aCont.arcAt κ b jumps su (fun i => E' i ω) j) := fun j => by
    rw [hGdef]
    simp only
    rw [Set.Sum.elim_range, closure_union, hT ω hωM j, hA ω j]
    rfl
  show SB.prefixPhysSet κ b jumps su (fun j => E su j ω) k ∪ ((↑) : ℝ → ℂ) '' Icc u 0 = _
  rw [hpre, statePhysicalSet_run_eq]
  simp_rw [hcl]
  ext z
  simp only [mem_union, mem_iUnion, mem_singleton_iff, exists_prop, Finset.mem_range]
  constructor
  · rintro (((rfl | ⟨j, hj, h⟩) | ⟨j, hj, h⟩) | h)
    · exact Or.inl hU
    · exact Or.inr ⟨j, hj, Or.inl (Or.inr h)⟩
    · exact Or.inr ⟨j, hj, Or.inr (Or.inr h)⟩
    · exact Or.inl h
  · rintro (h | ⟨j, hj, ((rfl | h) | (rfl | h))⟩)
    · exact Or.inr h
    · exact Or.inr hU
    · exact Or.inl (Or.inl (Or.inr ⟨j, hj, h⟩))
    · exact Or.inr hU
    · exact Or.inl (Or.inr ⟨j, hj, h⟩)

end InteractingSLE.Theorem14.SB.Nc
