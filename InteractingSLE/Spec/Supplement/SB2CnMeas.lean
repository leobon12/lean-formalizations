/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2CnCode
import InteractingSLE.Spec.Supplement.SB2MjFilt
import InteractingSLE.Spec.Supplement.SBTail2SideArcs

/-!
# The root time is an almost-sure stopping time of the capped pasts; the stopped filtration

Packet PROVE-SB2-CONDFIN (round 6; root route, step 1, R4.3 with the corrections of R4.4 and R5.1). The root time
`Cm.rootTime` (`Ck.entrTime` of B's piece `ℓ` at the seed `R = max (A ∩ ℝ)` on the launch event, `⊤` off it):

* **`exists_measurable_realMax_upperW`**: a measurable `Rt` with `Rt = realMax (upperPrefix …)` almost surely (no
  compactness of the prefix needed: `Cn.measurable_realMax_of_hit` on the dense codes of the pieces and arcs);
* **`exists_measurableSet_rootTime_le`**: `{rootTime ≤ s}` agrees almost surely with a measurable event (the tip code
  of the regularized piece at the measurable seed, `Cn.entrTime_le_iff_code`, transported from the raw piece by
  `Cl.entrTime_le_iff_of_retOf_eq`);
* **`measurableSet_aeSigma_rootTime_le`**: `{rootTime ≤ s}` is an event of the completed capped past at `s`
  (frozenness `Cm.ae_ae_rootTime_frozen` with `WalkLaw.mem_aeSigma_of_frozen`), and
  `measurableSet_aeSigma_rootTime_add_le`: so is `{rootTime + t ≤ r}` at `r` (`capPast_mono`);
* `stoppedFilt`: the σ-algebras of a family stopped at `τ + t` form a filtration when every `{τ + t ≤ r}` is an event
  of the family at `r`;
* **`exists_rootFilt`**: the filtration of R5.1's corrected premise exists:
  `MeasurableSet[𝓖 t] A ↔ MeasurableSet A ∧ ∀ r, MeasurableSet[aeSigma (Na.capPast … ℓ r) P] (A ∩ {rootTime + t ≤ r})`;
* `rootTime_eq_rootEntry`: on the launch event with a visit of `R` the root time is `Na.rootEntry`.

All statements are standard (no input).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.SB.Cn

open Exist Exist.Staged Exist.StagedLaw Lk GW1W LuM WalkLaw LocalSets GW1Bookkeep

/-! ### Stopped σ-algebras -/

section Stopped

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- **The σ-algebras of a family `𝒞` stopped at `τ + t`**: `A` is an event at `t` iff it is measurable and every
`A ∩ {τ + t ≤ r}` is an event of `𝒞 r`. A filtration when every `{τ + t ≤ r}` is an event of `𝒞 r`. -/
def stoppedFilt (𝒞 : ℝ≥0 → MeasurableSpace Ω) (τ : Ω → ℝ≥0∞)
    (hτ : ∀ t r : ℝ≥0, MeasurableSet[𝒞 r] {ω | τ ω + t ≤ r}) : Filtration ℝ≥0 mΩ where
  seq t :=
    { MeasurableSet' := fun A => MeasurableSet A ∧ ∀ r : ℝ≥0, MeasurableSet[𝒞 r] (A ∩ {ω | τ ω + t ≤ r})
      measurableSet_empty := ⟨MeasurableSet.empty, fun r => by
        rw [empty_inter]
        exact @MeasurableSet.empty _ (𝒞 r)⟩
      measurableSet_compl := fun A ⟨hA, hAr⟩ => ⟨hA.compl, fun r => by
        have e : Aᶜ ∩ {ω | τ ω + t ≤ r} = {ω | τ ω + t ≤ r} \ (A ∩ {ω | τ ω + t ≤ r}) := by
          ext ω
          simp only [mem_inter_iff, mem_compl_iff, Set.mem_sdiff, mem_ofPred_eq, not_and]
          tauto
        rw [e]
        exact @MeasurableSet.diff _ (𝒞 r) _ _ (hτ t r) (hAr r)⟩
      measurableSet_iUnion := fun f hf => ⟨MeasurableSet.iUnion fun i => (hf i).1, fun r => by
        rw [iUnion_inter]
        exact @MeasurableSet.iUnion _ _ (𝒞 r) _ _ fun i => (hf i).2 r⟩ }
  mono' := fun t t' htt' A hA => ⟨hA.1, fun r => by
    have e : A ∩ {ω | τ ω + t' ≤ r} = (A ∩ {ω | τ ω + t ≤ r}) ∩ {ω | τ ω + t' ≤ r} := by
      ext ω
      simp only [mem_inter_iff, mem_ofPred_eq]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨⟨h1, (add_le_add le_rfl (ENNReal.coe_le_coe.2 htt')).trans h2⟩, h2⟩
      · rintro ⟨⟨h1, -⟩, h2⟩
        exact ⟨h1, h2⟩
    rw [e]
    exact @MeasurableSet.inter _ (𝒞 r) _ _ (hA.2 r) (hτ t' r)⟩
  le' := fun _ _ hA => hA.1

theorem measurableSet_stoppedFilt_iff (𝒞 : ℝ≥0 → MeasurableSpace Ω) (τ : Ω → ℝ≥0∞)
    (hτ : ∀ t r : ℝ≥0, MeasurableSet[𝒞 r] {ω | τ ω + t ≤ r}) (t : ℝ≥0) (A : Set Ω) :
    MeasurableSet[stoppedFilt 𝒞 τ hτ t] A ↔
      MeasurableSet A ∧ ∀ r : ℝ≥0, MeasurableSet[𝒞 r] (A ∩ {ω | τ ω + t ≤ r}) :=
  Iff.rfl

/-- `x + t ≤ r` iff `x ≤ r - t`, for `t ≤ r` in `ℝ≥0`. -/
theorem add_le_iff_le_sub {x : ℝ≥0∞} {t r : ℝ≥0} (htr : t ≤ r) :
    x + t ≤ r ↔ x ≤ ((r - t : ℝ≥0) : ℝ≥0∞) := by
  induction x using ENNReal.recTopCoe with
  | top => simp
  | coe y =>
    rw [← ENNReal.coe_add, ENNReal.coe_le_coe, ENNReal.coe_le_coe]
    exact (le_tsub_iff_right htr).symm

end Stopped

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-! ### The seed, read measurably -/

section Seed

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {E : ExplSpec → ℕ → Ω → Drv} {u : ℝ}
  {l : List (ℝ × ℝ≥0)}

/-- **The seed `R = max (A ∩ ℝ)` of the upper prefix is almost surely a measurable function** (no compactness of the
prefix needed). -/
theorem exists_measurable_realMax_upperW (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hEm : ∀ j, Measurable (E (Lu.upperSpec u l) j))
    (hR : StagedPiecesRegular κ b jumps P (Lu.upperSpec u l) (E (Lu.upperSpec u l))) (k : ℕ) :
    ∃ Rt : Ω → ℝ, Measurable Rt ∧ ∀ᵐ ω ∂P, Rt ω = realMax (upperPrefix κ b jumps E u l k ω) := by
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
  set C : Set ℂ := {(u : ℂ)} ∪ ((↑) : ℝ → ℂ) '' Icc u 0 with hC
  refine ⟨fun ω => realMax (C ∪ ⋃ j ∈ Finset.range k, closure (range (G ω j))),
    measurable_realMax_of_hit fun K hK => measurableSet_hit_codes hGm C k hK, ?_⟩
  filter_upwards [hMae, StagedReg.ae_run_regHist hR] with ω hωM hrun
  congr 1
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
  show _ = SB.prefixPhysSet κ b jumps su (fun j => E su j ω) k ∪ ((↑) : ℝ → ℂ) '' Icc u 0
  rw [hpre, Mz.statePhysicalSet_run_eq]
  simp_rw [hcl]
  ext z
  simp only [hC, mem_union, mem_iUnion, mem_singleton_iff, exists_prop, Finset.mem_range]
  constructor
  · rintro ((rfl | h) | ⟨j, hj, ((rfl | h) | (rfl | h))⟩)
    · exact Or.inl (Or.inl (Or.inl rfl))
    · exact Or.inr h
    · exact Or.inl (Or.inl (Or.inl rfl))
    · exact Or.inl (Or.inl (Or.inr ⟨j, hj, h⟩))
    · exact Or.inl (Or.inl (Or.inl rfl))
    · exact Or.inl (Or.inr ⟨j, hj, h⟩)
  · rintro (((rfl | ⟨j, hj, h⟩) | ⟨j, hj, h⟩) | h)
    · exact Or.inl (Or.inl rfl)
    · exact Or.inr ⟨j, hj, Or.inl (Or.inr h)⟩
    · exact Or.inr ⟨j, hj, Or.inr (Or.inr h)⟩
    · exact Or.inl (Or.inr h)

end Seed

/-! ### The root time -/

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {E : ExplSpec → ℕ → Ω → Drv} {u : ℝ} {l : List (ℝ × ℝ≥0)}
  {k ℓ : ℕ}

omit mΩ [StandardBorelSpace Ω] in
/-- On the launch event with a visit of `R`, the root time is `Na.rootEntry`. -/
theorem rootTime_eq_rootEntry {ω : Ω}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none)
    (hv : ∃ t : ℝ≥0, (t : ℝ≥0∞) ≤ (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2 ∧
      pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) ℓ)
        (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω) t =
          ((realMax (upperPrefix κ b jumps E u l k ω) : ℝ) : ℂ)) :
    Cm.rootTime κ b jumps E u l k ℓ ω = (Na.rootEntry κ b jumps E u l k ℓ ω : ℝ≥0∞) := by
  classical
  unfold Cm.rootTime
  rw [ite_eq_left hl, Ck.entrTime_eq_visitTime hv]
  rfl

/-- **`{rootTime ≤ s}` agrees almost surely with a measurable event.** -/
theorem exists_measurableSet_rootTime_le (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hEu : IsStagedHistory κ b jumps P h (Lu.upperSpec u l) (E (Lu.upperSpec u l)))
    (hRu : StagedPiecesRegular κ b jumps P (Lu.upperSpec u l) (E (Lu.upperSpec u l)))
    (hEl : IsStagedHistory κ b jumps P h (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)))
    (hRl : StagedPiecesRegular κ b jumps P (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))) (s : ℝ≥0) :
    ∃ S : Set Ω, MeasurableSet S ∧ ∀ᵐ ω ∂P, (Cm.rootTime κ b jumps E u l k ℓ ω ≤ s ↔ ω ∈ S) := by
  classical
  set lw := boundaryWalkSpec b jumps (-(Real.pi / 2)) true with hlw
  set Fl := StagedReg.regHist lw (E lw) with hFl
  have hFlm : ∀ j, Measurable (Fl j) := StagedReg.measurable_regHist hEl.1
  have hFlr : ∀ j ω, IsRegularDriver (Fl j ω) := fun j ω => StagedReg.isRegularDriver_regHist j ω
  have hRl' := WalkLaw.stagedPiecesRegular_regHist hRl
  obtain ⟨M, hMae, hMm, hMp⟩ := hRl'.ae_pieceRegular.exists_measurable_mem
  obtain ⟨Rt, hRtm, hRt⟩ := exists_measurable_realMax_upperW (κ := κ) hb hEu.1 hRu k
  choose Y hYm hY using fun (p : ℕ × ℕ) (n : ℕ) =>
    exists_measurable_tipApprox hb lw hFlm hFlr hMm hMp ℓ (qTime p.1 p.2) n
  set V : ℕ × ℕ → Ω → ℂ := fun p ω => limUnder atTop (fun n => Y p n ω) with hV
  have hVm : ∀ p, Measurable (V p) := fun p =>
    (StronglyMeasurable.limUnder fun n => (hYm p n).stronglyMeasurable).measurable
  set Lau : Set Ω := {ω | (ExplState.run κ b jumps lw (fun j => Fl j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none} with hLau
  have hLaum : MeasurableSet Lau := (runMeasStatement κ b jumps hb lw Fl hFlm hFlr ℓ).1
  have hTm : Measurable fun ω => tipCode (fun p => V p ω) (Fl ℓ ω).2 s (Rt ω) := by
    unfold tipCode
    refine Measurable.iInf fun p => Measurable.ite ?_
      ((Complex.continuous_ofReal.measurable.comp hRtm).edist (hVm p)) measurable_const
    exact measurableSet_le measurable_const (measurable_const.min (measurable_snd.comp (hFlm ℓ)))
  refine ⟨Lau ∩ ({ω | (Fl ℓ ω).2 ≤ s} ∪ {ω | tipCode (fun p => V p ω) (Fl ℓ ω).2 s (Rt ω) = 0}),
    hLaum.inter ((measurableSet_le (measurable_snd.comp (hFlm ℓ)) measurable_const).union
      (hTm (measurableSet_singleton 0))), ?_⟩
  filter_upwards [hMae, hRt, StagedReg.ae_run_regHist hRl, GW1W.regLaunches_of_stagedPiecesRegular hRl] with
    ω hωM hRω hrun hPE
  have hPF : RegLaunches κ b jumps lw (fun j => Fl j ω) := fun j c θ hj => hMp ω hωM j c θ hj
  have hlaunch : (ExplState.run κ b jumps lw (fun j => Fl j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none ↔
      (ExplState.run κ b jumps lw (fun j => E lw j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none := by
    rw [hrun (ℓ + 1)]
  unfold Cm.rootTime
  by_cases hl : (ExplState.run κ b jumps lw (fun j => E lw j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none
  · have hlF := hlaunch.2 hl
    rw [ite_eq_left hl, ← hRω]
    have hrec : retOf (s : ℝ≥0∞) (E lw ℓ ω) = retOf (s : ℝ≥0∞) (Fl ℓ ω) :=
      (Cm.retOf_regHist_eq hPE hl (s : ℝ≥0∞)).symm
    rw [Cl.entrTime_le_iff_of_retOf_eq hPE hPF hl (hrun ℓ).symm hrec (Rt ω),
      entrTime_le_iff_code hPF hlF (Rt ω) s]
    have hVω : (fun p : ℕ × ℕ => limUnder atTop
        (fun m => tipApprox κ b jumps lw (fun j => Fl j ω) ℓ (qTime p.1 p.2) m)) = fun p => V p ω := by
      funext p
      exact congrArg (limUnder atTop) (funext fun n => hY p n ω hωM hlF)
    rw [hVω]
    simp only [mem_inter_iff, mem_union, mem_ofPred_eq]
    exact ⟨fun h => ⟨hlF, h⟩, fun h => h.2⟩
  · rw [ite_eq_right hl]
    simp only [mem_inter_iff]
    refine iff_of_false (fun h => ?_) (fun h => hl (hlaunch.1 h.1))
    exact absurd h (not_le.2 ENNReal.coe_lt_top)

omit [StandardBorelSpace Ω] in
/-- The capped pasts are sub-σ-algebras. -/
theorem capPast_le (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hEu : ∀ j, Measurable (E (Lu.upperSpec u l) j))
    (hEl : ∀ j, Measurable (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j)) (r : ℝ≥0) :
    Na.capPast κ b jumps E u l k ℓ r ≤ mΩ :=
  sup_le (Mz.pastSigma_le hb _ (StagedReg.measurable_regHist hEu) (fun j ω => StagedReg.isRegularDriver_regHist j ω) k)
    (Mz.pastSigma_le hb _ (StagedReg.measurable_regHist hEl) (fun j ω => StagedReg.isRegularDriver_regHist j ω)
      (ℓ + 1))

omit mΩ [StandardBorelSpace Ω] in
/-- The capped pasts increase with the cap. -/
theorem capPast_mono (hℓ : ℓ ≤ (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2.length)
    (hwℓ : (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2[ℓ]? = some (Sum.inl (-(Real.pi / 2), ⊤)))
    {r r' : ℝ≥0} (hrr' : r ≤ r') :
    Na.capPast κ b jumps E u l k ℓ r ≤ Na.capPast κ b jumps E u l k ℓ r' :=
  sup_le_sup_left (Mj.pastSigma_capSpec_mono_real _ (fun j ω => StagedReg.isRegularDriver_regHist j ω) hℓ hwℓ
    (ENNReal.coe_le_coe.2 hrr')) _

/-- **`{rootTime ≤ s}` is an event of the completed capped past at `s`.** -/
theorem measurableSet_aeSigma_rootTime_le (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hEu : IsStagedHistory κ b jumps P h (Lu.upperSpec u l) (E (Lu.upperSpec u l)))
    (hRu : StagedPiecesRegular κ b jumps P (Lu.upperSpec u l) (E (Lu.upperSpec u l)))
    (hEl : IsStagedHistory κ b jumps P h (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)))
    (hRl : StagedPiecesRegular κ b jumps P (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)))
    (hℓ : ℓ ≤ (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2.length)
    (hwℓ : (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2[ℓ]? = some (Sum.inl (-(Real.pi / 2), ⊤)))
    (s : ℝ≥0) :
    MeasurableSet[aeSigma (Na.capPast κ b jumps E u l k ℓ s) P] {ω | Cm.rootTime κ b jumps E u l k ℓ ω ≤ s} := by
  obtain ⟨S, hS, hSae⟩ := exists_measurableSet_rootTime_le (k := k) (ℓ := ℓ) hb hEu hRu hEl hRl s
  exact mem_aeSigma_of_frozen (capPast_le hb hEu.1 hEl.1 s) hS
    (M := {ω | Cm.rootTime κ b jumps E u l k ℓ ω ≤ s ↔ ω ∈ S}) hSae (fun ω hω => hω)
    (Cm.ae_ae_rootTime_frozen hb hEu hRu hEl hRl hℓ hwℓ s)

/-- **`{rootTime + t ≤ r}` is an event of the completed capped past at `r`.** -/
theorem measurableSet_aeSigma_rootTime_add_le (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hEu : IsStagedHistory κ b jumps P h (Lu.upperSpec u l) (E (Lu.upperSpec u l)))
    (hRu : StagedPiecesRegular κ b jumps P (Lu.upperSpec u l) (E (Lu.upperSpec u l)))
    (hEl : IsStagedHistory κ b jumps P h (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)))
    (hRl : StagedPiecesRegular κ b jumps P (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)))
    (hℓ : ℓ ≤ (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2.length)
    (hwℓ : (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2[ℓ]? = some (Sum.inl (-(Real.pi / 2), ⊤)))
    (t r : ℝ≥0) :
    MeasurableSet[aeSigma (Na.capPast κ b jumps E u l k ℓ r) P]
      {ω | Cm.rootTime κ b jumps E u l k ℓ ω + t ≤ r} := by
  by_cases htr : t ≤ r
  · have e : {ω | Cm.rootTime κ b jumps E u l k ℓ ω + t ≤ r} =
        {ω | Cm.rootTime κ b jumps E u l k ℓ ω ≤ ((r - t : ℝ≥0) : ℝ≥0∞)} := by
      ext ω
      exact add_le_iff_le_sub htr
    rw [e]
    have hmono : aeSigma (Na.capPast κ b jumps E u l k ℓ (r - t)) P ≤ aeSigma (Na.capPast κ b jumps E u l k ℓ r) P :=
      fun A ⟨A', hA', he⟩ => ⟨A', capPast_mono hℓ hwℓ tsub_le_self _ hA', he⟩
    exact hmono _ (measurableSet_aeSigma_rootTime_le hb hEu hRu hEl hRl hℓ hwℓ (r - t))
  · push Not at htr
    have e : {ω | Cm.rootTime κ b jumps E u l k ℓ ω + t ≤ r} = ∅ := by
      ext ω
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_le]
      exact (ENNReal.coe_lt_coe.2 htr).trans_le le_add_self
    rw [e]
    exact @MeasurableSet.empty _ (aeSigma (Na.capPast κ b jumps E u l k ℓ r) P)

/-- **The filtration of the corrected root-variant premise (R5.1) exists**: the completed capped pasts stopped at
`rootTime + t`. -/
theorem exists_rootFilt (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hEu : IsStagedHistory κ b jumps P h (Lu.upperSpec u l) (E (Lu.upperSpec u l)))
    (hRu : StagedPiecesRegular κ b jumps P (Lu.upperSpec u l) (E (Lu.upperSpec u l)))
    (hEl : IsStagedHistory κ b jumps P h (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)))
    (hRl : StagedPiecesRegular κ b jumps P (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)))
    (hℓ : ℓ ≤ (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2.length)
    (hwℓ : (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2[ℓ]? = some (Sum.inl (-(Real.pi / 2), ⊤))) :
    ∃ 𝓖 : Filtration ℝ≥0 mΩ, ∀ (t : ℝ≥0) (A : Set Ω), MeasurableSet[𝓖 t] A ↔
      MeasurableSet A ∧ ∀ r : ℝ≥0, MeasurableSet[aeSigma (Na.capPast κ b jumps E u l k ℓ r) P]
        (A ∩ {ω | Cm.rootTime κ b jumps E u l k ℓ ω + t ≤ r}) :=
  ⟨stoppedFilt (fun r => aeSigma (Na.capPast κ b jumps E u l k ℓ r) P) (Cm.rootTime κ b jumps E u l k ℓ)
    (measurableSet_aeSigma_rootTime_add_le hb hEu hRu hEl hRl hℓ hwℓ), fun _ _ => Iff.rfl⟩

end InteractingSLE.Theorem14.SB.Cn
