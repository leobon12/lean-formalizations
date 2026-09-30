import QuantumZipper.Proofs.Zipper.LocLenR6cCont

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# D75 / R6h (3): continuity of the open-arc right length, `L⁺_0 = 0` (`LenRightRegArcStmt`)

The right-side mirror of `LocLenR6cCont` (Sheffield arXiv:1012.4797 §1.4, p. 70): in the chart of
time `T`, the right side of `η[t₀,T]` is `(0, p(t₀))`, `p(t₀) = 0₊^{vrev W T}(T − t₀)`
(`Thm18Asm.G4Core.ae_sideImages_zipCapDown`, `ae_zeroPlus_facts`), so by the right half of the
pair cocycle `L⁺_{t₀} + ν_T (0, p(t₀)) = L⁺_T`; `ν_T` is finite and atomless on `(0, O⁺_T)`.

* `LenRightRegArcStmt` (open-arc copy of `F1.LenRightRegStmt`, F1LenReg.lean:107).
* `stage_arcLen_eq_right`, `continuousOn_measure_Ioo_right_r6c`,
  `continuousOn_arc_of_stage_right` (deterministic).
* **`lenRightRegArc_of_yMergeOffTip`**.
Bookkeeping own.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace LocLen

open WedgeUnzip

/-- **Regularity of the right open-arc length** (open-arc copy of `F1.LenRightRegStmt`). -/
def LenRightRegArcStmt : Prop :=
  ∀ (κ : ℝ) {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Y : Ω' → FieldSample) (B' : ℝ≥0 → Ω' → ℝ), Thm13Asm.IsPStarSample κ P' Y B' →
    ∀ᵐ ω ∂P', ContinuousOn
        (fun t => (unzipLengthsArc (Real.sqrt κ) (F1.pcfg κ Y B' ω) t).2.toReal) (Ici 0) ∧
      (unzipLengthsArc (Real.sqrt κ) (F1.pcfg κ Y B' ω) 0).2 = 0

/-- **The restarted right length read at time `T`** (mirror of `stage_arcLen_eq`). -/
theorem stage_arcLen_eq_right {γ : ℝ} {c : FieldSample × (ℝ → ℝ)} {t₀ T p : ℝ}
    (hcap : RegEq (unzippedField γ (zipCapDown γ t₀ c) (T - t₀)) (unzippedField γ c T))
    (hside : (sideImages (zipCapDown γ t₀ c).2 (T - t₀)).2 = p)
    (hp : p ≤ (sideImages c.2 T).2) (hm : (sideImages c.2 T).1 ≤ 0)
    (hr : IsRegularSample (unzippedField γ c T)) {ν : Measure ℝ}
    (hν : HasBdryLimitOn γ (unzippedField γ c T) (offSet c.2 T)ᶜ ν) :
    (unzipLengthsArc γ (zipCapDown γ t₀ c) (T - t₀)).2 = ν (Ioo 0 p) := by
  show arcLen γ (unzippedField γ (zipCapDown γ t₀ c) (T - t₀)) 0
    (sideImages (zipCapDown γ t₀ c).2 (T - t₀)).2 = _
  rw [hside, arcLen_congr (B3d.avgReg_eq_of_regEq hcap)]
  unfold arcLen
  rw [IsLQGGoodOff.qBoundaryMeasureOn_eq hr hν isOpen_Ioo
    ((Ioo_right_disjoint_offSet c.2 T hm).mono_left (Ioo_subset_Ioo_right hp)),
    Measure.restrict_apply_self]

/-- Distribution function of an atomless finite measure on `[0, b]`, left endpoint fixed. -/
theorem continuousOn_measure_Ioo_right_r6c {ν : Measure ℝ} {b : ℝ}
    (hat : ∀ p ∈ Ioo 0 b, ν {p} = 0) (hfin : ν (Ioo 0 b) ≠ ⊤) :
    ContinuousOn (fun x => (ν (Ioo 0 x)).toReal) (Icc 0 b) := by
  set μ := ν.restrict (Ioo 0 b) with hμ
  have hμat : ∀ x, μ {x} = 0 := fun x => by
    rw [hμ, Measure.restrict_apply (measurableSet_singleton x)]
    by_cases hx : x ∈ Ioo 0 b
    · rw [inter_eq_left.2 (singleton_subset_iff.2 hx)]; exact hat x hx
    · rw [singleton_inter_eq_empty.2 hx, measure_empty]
  have : NullSingletonClass μ := ⟨hμat⟩
  have hfin' : μ (Icc 0 b) ≠ ⊤ := by
    rw [hμ, Measure.restrict_apply measurableSet_Icc]
    exact ne_top_of_le_ne_top hfin (measure_mono inter_subset_right)
  have hi : IntegrableOn (fun _ => (1 : ℝ)) (Icc 0 b) μ := integrableOn_const hfin'
  refine (intervalIntegral.continuousOn_primitive_Icc hi).congr fun x hx => ?_
  have e : ν (Ioo 0 x) = μ (Icc 0 x) := by
    rw [← measure_congr (Ioo_ae_eq_Icc (μ := μ)), hμ, Measure.restrict_apply measurableSet_Ioo,
      inter_eq_left.2 (Ioo_subset_Ioo_right hx.2)]
  show (ν (Ioo 0 x)).toReal = _
  rw [e]
  simp [Measure.real]

/-- **Deterministic continuity on `[0,T)`, right side.** -/
theorem continuousOn_arc_of_stage_right {L : ℝ → ℝ≥0∞} {ν : Measure ℝ} {p : ℝ → ℝ} {b T : ℝ}
    (hp : ContinuousOn p (Icc 0 T)) (hpI : ∀ t₀ ∈ Icc 0 T, 0 ≤ p t₀ ∧ p t₀ ≤ b)
    (hat : ∀ q ∈ Ioo 0 b, ν {q} = 0) (hfin : ν (Ioo 0 b) ≠ ⊤) (hLT : L T ≠ ⊤)
    (heq : ∀ t₀ ∈ Ico 0 T, L t₀ + ν (Ioo 0 (p t₀)) = L T) :
    ContinuousOn (fun t => (L t).toReal) (Ico 0 T) := by
  have hg := continuousOn_measure_Ioo_right_r6c hat hfin
  have hcomp : ContinuousOn (fun t₀ => (ν (Ioo 0 (p t₀))).toReal) (Ico 0 T) :=
    hg.comp (hp.mono Ico_subset_Icc_self) fun t₀ ht₀ => ⟨(hpI t₀ (Ico_subset_Icc_self ht₀)).1,
      (hpI t₀ (Ico_subset_Icc_self ht₀)).2⟩
  refine ((continuousOn_const (c := (L T).toReal)).sub hcomp).congr fun t₀ ht₀ => ?_
  have e := heq t₀ ht₀
  have h1 : L t₀ ≠ ⊤ := fun h => hLT (by rw [← e, h, top_add])
  have h2 : ν (Ioo 0 (p t₀)) ≠ ⊤ := fun h => hLT (by rw [← e, h, add_top])
  show (L t₀).toReal = (L T).toReal - (ν (Ioo 0 (p t₀))).toReal
  rw [← e, ENNReal.toReal_add h1 h2]
  ring

/-- **`LenRightRegArcStmt` from the capacity field cocycle, goodness and atomlessness off the
root images, the pair cocycle and finiteness.** -/
theorem lenRightRegArc_of_parts
    (hCap : ∀ (κ : ℝ) {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω')
      [IsProbabilityMeasure P'] (Y : Ω' → FieldSample) (B' : ℝ≥0 → Ω' → ℝ),
      Thm13Asm.IsPStarSample κ P' Y B' →
      ∀ᵐ ω ∂P', Thm18Asm.UnzipCapRegData (Real.sqrt κ) (Y ω, drive κ B' ω))
    (hPG : PStarGoodOffAllStmt)
    (hAt : ∀ (κ : ℝ) {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω')
      [IsProbabilityMeasure P'] (Y : Ω' → FieldSample) (B' : ℝ≥0 → Ω' → ℝ),
      Thm13Asm.IsPStarSample κ P' Y B' → ∀ᵐ ω ∂P', ∀ t : ℝ, 0 < t → AtomOff (Real.sqrt κ)
        (unzippedField (Real.sqrt κ) (Y ω, drive κ B' ω) t) (offSet (drive κ B' ω) t))
    (hC : LenPairCocycleArcStmt) (hF : LenFiniteArcStmt) : LenRightRegArcStmt := by
  intro κ Ω' _ P' _ Y B' hP
  have hS := F1.thm18Setting_of_pstar hP
  have e2 : Real.sqrt κ ^ 2 = κ := Real.sq_sqrt hP.1.le
  have hZP := Thm18Asm.G4Core.ae_zeroPlus_facts hS
  have hSI := Thm18Asm.G4Core.ae_sideImages_zipCapDown hS
  simp only [e2, wedgeConfig] at hZP hSI
  filter_upwards [hCap κ P' Y B' hP, hPG κ P' Y B' hP, hAt κ P' Y B' hP, hC κ P' Y B' hP,
    ae_unzipLengthsArc_lt_top_all hC hF κ P' Y B' hP, hZP, hSI,
    hP.2.2.2.1.cont, hP.2.2.2.1.eval_zero_ae_eq_zero]
    with ω hcap hg hat hc hf hz hsi hcB h0
  set W := drive κ B' ω with hWdef
  have hW : Continuous W := by
    rw [hWdef]; unfold drive
    exact continuous_const.mul (hcB.comp continuous_real_toNNReal)
  have hW0 : W 0 = 0 := by simp [hWdef, drive, h0]
  set L : ℝ → ℝ≥0∞ := fun t => (unzipLengthsArc (Real.sqrt κ) (F1.pcfg κ Y B' ω) t).2 with hL
  have key : ∀ T : ℝ, 0 < T → ∃ ν : Measure ℝ,
      (∀ q ∈ Ioo 0 (sideImages W T).2, ν {q} = 0) ∧ ν (Ioo 0 (sideImages W T).2) = L T ∧
      ∀ t₀ ∈ Ico 0 T, L t₀ + ν (Ioo 0 (zeroPlus (B2.vrev W T) (T - t₀))) = L T := by
    intro T hT
    obtain ⟨-, hmono, -, hO⟩ := hz T hT
    obtain ⟨hr, ⟨ν, hν⟩, -⟩ := hg T hT.le
    obtain ⟨ν', hν', hat'⟩ := hat T hT
    have hνν : ν = ν' := hν.unique (isClosed_offSet _ T).isOpen_compl hν'
    have hm := sideImages_fst_nonpos_of_cont hW hW0 hT.le
    refine ⟨ν, fun q hq => by
      rw [hνν]; exact hat' q (disjoint_left.1 (Ioo_right_disjoint_offSet _ T hm) hq), ?_, ?_⟩
    · show _ = arcLen (Real.sqrt κ) (unzippedField (Real.sqrt κ) (F1.pcfg κ Y B' ω) T) 0
        (sideImages W T).2
      unfold arcLen
      rw [IsLQGGoodOff.qBoundaryMeasureOn_eq hr hν isOpen_Ioo (Ioo_right_disjoint_offSet _ T hm),
        Measure.restrict_apply_self]
    · intro t₀ ht₀
      have hple : zeroPlus (B2.vrev W T) (T - t₀) ≤ (sideImages W T).2 := by
        rw [hO]
        exact hmono.monotoneOn ⟨sub_nonneg.2 ht₀.2.le, by linarith [ht₀.1]⟩ ⟨hT.le, le_rfl⟩
          (by linarith [ht₀.1])
      have hcapT := hcap t₀ (T - t₀) ht₀.1 (sub_nonneg.2 ht₀.2.le)
      rw [add_sub_cancel] at hcapT
      have h := (hc t₀ (T - t₀) ht₀.1 (sub_nonneg.2 ht₀.2.le)).2
      rw [add_sub_cancel] at h
      have hside := (hsi T (T - t₀) ⟨sub_pos.2 ht₀.2, by linarith [ht₀.1]⟩).2
      rw [sub_sub_cancel] at hside
      simp only [hL]
      rw [h, stage_arcLen_eq_right (c := F1.pcfg κ Y B' ω) hcapT hside hple hm hr hν]
  refine lenLeftRegArc_det (L := L) (fun T hT => ?_) (fun _ => ?_) (hf 1 zero_le_one).2.ne
  · obtain ⟨ν, hat, hνL, heq⟩ := key T hT
    obtain ⟨hcont, hmono, hz0, hO⟩ := hz T hT
    refine continuousOn_arc_of_stage_right (b := (sideImages W T).2)
      (p := fun t₀ => zeroPlus (B2.vrev W T) (T - t₀)) ?_ ?_ hat
      (by rw [hνL]; exact (hf T hT.le).2.ne) (hf T hT.le).2.ne heq
    · exact hcont.comp (continuousOn_const.sub continuousOn_id) fun t₀ ht₀ =>
        ⟨sub_nonneg.2 ht₀.2, by linarith [ht₀.1]⟩
    · intro t₀ ht₀
      refine ⟨?_, ?_⟩
      · rw [← hz0]
        exact hmono.monotoneOn ⟨le_rfl, hT.le⟩ ⟨sub_nonneg.2 ht₀.2, by linarith [ht₀.1]⟩
          (sub_nonneg.2 ht₀.2)
      · rw [hO]
        exact hmono.monotoneOn ⟨sub_nonneg.2 ht₀.2, by linarith [ht₀.1]⟩ ⟨hT.le, le_rfl⟩
          (by linarith [ht₀.1])
  · obtain ⟨ν, -, hνL, heq⟩ := key 1 one_pos
    obtain ⟨-, -, -, hO⟩ := hz 1 one_pos
    have := heq 0 ⟨le_rfl, one_pos⟩
    rw [sub_zero, ← hO, hνL] at this
    exact this

/-- **`LenRightRegArcStmt`, closed form.** -/
theorem lenRightRegArc_of_yMergeOffTip (hYO : WedgeUnzip.YMergeOffTipStmt)
    (hC : LenPairCocycleArcStmt) (hF : LenFiniteArcStmt) : LenRightRegArcStmt :=
  lenRightRegArc_of_parts (pStarCapRegOff_of_yMergeOffTip hYO)
    (pStarGoodOffAll_of_yMergeOffTip hYO) (pStarAtomOff_of_yMergeOffTip hYO) hC hF

end LocLen
end QuantumZipper
