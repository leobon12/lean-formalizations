import QuantumZipper.Proofs.Zipper.LocLenR6cCap
import QuantumZipper.Proofs.Zipper.LocLenF1Flow

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# D75 / R6c: strict monotonicity of the open-arc left length (`LenStrictMonoArcStmt`)

Sheffield, arXiv:1012.4797, §1.4 and §5.4 p. 70 ("`L⁻_t` is strictly increasing"): for
`t₀ < T`, the left side of `η[0,t₀]` is mapped at time `T` onto `[O⁻_T, m]` and the left side of
`η[t₀,T]` onto `[m, 0]`, `m = 0₋^{vrev W T}(T − t₀) < 0`; lengths add
(`LenPairCocycleArcStmt`), and the second summand is the mass of the nonempty open arc `(m,0)`
for the local boundary measure of the field at time `T`, which is positive
(`PStarBdryPosAllArcStmt`, Sheffield p. 56). This is the paper's short argument (the
open-arc copy of `F1.strictMonoOn_of_cov_pos`, F1LenFlow.lean:48, with the conformal-invariance
input `LenLeftCovStmt` replaced by the pair cocycle and the capacity field cocycle).

* `stage_arcLen_eq` (deterministic): the restarted left length is `ν_T (m, 0)`.
* `strictMonoOn_arc_of_stage` (deterministic).
* `lenStrictMonoArc_of_parts`, closed form **`lenStrictMonoArc_of_yMergeOffTip`**
  (inputs: `YMergeOffTip`, `LenPairCocycleArcStmt` (R6a), `LenFiniteArcStmt` (X1, R6g)).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace LocLen

open WedgeUnzip

/-- **The restarted left length read at time `T`** (deterministic): if the field of
`zipCapDown t₀ c` unzipped by `T − t₀` is `RegEq` to the field of `c` at `T`, its left side
image is `m ∈ [O⁻_T, 0)`, and the field at `T` has the local boundary limit `ν` off
`offSet c.2 T`, then the restarted left open-arc length is `ν (m, 0)`. -/
theorem stage_arcLen_eq {γ : ℝ} {c : FieldSample × (ℝ → ℝ)} {t₀ T m : ℝ}
    (hcap : RegEq (unzippedField γ (zipCapDown γ t₀ c) (T - t₀)) (unzippedField γ c T))
    (hside : (sideImages (zipCapDown γ t₀ c).2 (T - t₀)).1 = m)
    (hm : (sideImages c.2 T).1 ≤ m) (hp : 0 ≤ (sideImages c.2 T).2)
    (hr : IsRegularSample (unzippedField γ c T)) {ν : Measure ℝ}
    (hν : HasBdryLimitOn γ (unzippedField γ c T) (offSet c.2 T)ᶜ ν) :
    (unzipLengthsArc γ (zipCapDown γ t₀ c) (T - t₀)).1 = ν (Ioo m 0) := by
  show arcLen γ (unzippedField γ (zipCapDown γ t₀ c) (T - t₀))
    (sideImages (zipCapDown γ t₀ c).2 (T - t₀)).1 0 = _
  rw [hside, arcLen_congr (B3d.avgReg_eq_of_regEq hcap)]
  unfold arcLen
  rw [IsLQGGoodOff.qBoundaryMeasureOn_eq hr hν isOpen_Ioo
    ((Ioo_left_disjoint_offSet c.2 T hp).mono_left (Ioo_subset_Ioo_left hm)),
    Measure.restrict_apply_self]

/-- **Deterministic strict monotonicity** from additivity, finiteness and positivity of the
restarted lengths. -/
theorem strictMonoOn_arc_of_stage {γ : ℝ} {c : FieldSample × (ℝ → ℝ)}
    (hcoc : ∀ u s : ℝ, 0 ≤ u → 0 ≤ s → (unzipLengthsArc γ c (u + s)).1 =
      (unzipLengthsArc γ c u).1 + (unzipLengthsArc γ (zipCapDown γ u c) s).1)
    (hfin : ∀ t : ℝ, 0 ≤ t → (unzipLengthsArc γ c t).1 ≠ ⊤)
    (hpos : ∀ t₀ T : ℝ, 0 ≤ t₀ → t₀ < T →
      0 < (unzipLengthsArc γ (zipCapDown γ t₀ c) (T - t₀)).1) :
    StrictMonoOn (fun t => (unzipLengthsArc γ c t).1) (Ici 0) := by
  intro t₀ ht₀ T _ hlt
  have h := hcoc t₀ (T - t₀) ht₀ (sub_nonneg.2 hlt.le)
  rw [add_sub_cancel] at h
  show (unzipLengthsArc γ c t₀).1 < (unzipLengthsArc γ c T).1
  rw [h]
  exact ENNReal.lt_add_right (hfin t₀ (mem_Ici.1 ht₀)) (hpos t₀ T ht₀ hlt).ne'

/-- **`LenStrictMonoArcStmt` from the capacity field cocycle, goodness off the root images,
open-arc positivity, the pair cocycle and finiteness.** -/
theorem lenStrictMonoArc_of_parts
    (hCap : ∀ (κ : ℝ) {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω')
      [IsProbabilityMeasure P'] (Y : Ω' → FieldSample) (B' : ℝ≥0 → Ω' → ℝ),
      Thm13Asm.IsPStarSample κ P' Y B' →
      ∀ᵐ ω ∂P', Thm18Asm.UnzipCapRegData (Real.sqrt κ) (Y ω, drive κ B' ω))
    (hPG : PStarGoodOffAllStmt) (hPos : PStarBdryPosAllArcStmt)
    (hC : LenPairCocycleArcStmt) (hF : LenFiniteArcStmt) : LenStrictMonoArcStmt := by
  intro κ Ω' _ P' _ Y B' hP
  filter_upwards [hCap κ P' Y B' hP, hPG κ P' Y B' hP, hPos κ P' Y B' hP, hC κ P' Y B' hP,
    ae_unzipLengthsArc_lt_top_all hC hF κ P' Y B' hP, ae_pstar_zeroMinus_facts hP,
    hP.2.2.2.1.cont, hP.2.2.2.1.eval_zero_ae_eq_zero]
    with ω hcap hg hpos hc hf hz hcB h0
  have hW : Continuous (drive κ B' ω) := by
    unfold drive
    exact continuous_const.mul (hcB.comp continuous_real_toNNReal)
  have hW0 : drive κ B' ω 0 = 0 := by simp [drive, h0]
  refine strictMonoOn_arc_of_stage (fun u s hu hs => (hc u s hu hs).1)
    (fun t ht => (hf t ht).1.ne) ?_
  intro t₀ T ht₀ hlt
  have hT : 0 < T := ht₀.trans_lt hlt
  obtain ⟨-, hanti, hz0, hO, hside⟩ := hz T hT
  obtain ⟨hr, ⟨ν, hν⟩, -⟩ := hg T hT.le
  have hmle : (sideImages (drive κ B' ω) T).1 ≤
      zeroMinus (B2.vrev (drive κ B' ω) T) (T - t₀) := by
    rw [hO]
    exact hanti.antitoneOn ⟨sub_nonneg.2 hlt.le, by linarith⟩ ⟨hT.le, le_rfl⟩ (by linarith)
  have hm0 : zeroMinus (B2.vrev (drive κ B' ω) T) (T - t₀) < 0 := by
    have := hanti ⟨le_rfl, hT.le⟩ ⟨(sub_pos.2 hlt).le, by linarith⟩ (sub_pos.2 hlt)
    rwa [hz0] at this
  have hcapT := hcap t₀ (T - t₀) ht₀ (sub_nonneg.2 hlt.le)
  rw [add_sub_cancel] at hcapT
  rw [stage_arcLen_eq (c := F1.pcfg κ Y B' ω) hcapT (hside t₀ ht₀ hlt) hmle
    (sideImages_snd_nonneg_of_cont hW hW0 hT.le) hr hν]
  have := hpos T hT _ 0 hmle hm0 le_rfl
  rwa [qBoundaryMeasureOn_eq_of_hasBdryLimitOn hr (isClosed_offSet _ T).isOpen_compl hν] at this

/-- **`LenStrictMonoArcStmt`, closed form**: from the offset merging input, the open-arc pair
cocycle (R6a) and the fixed-time finiteness of the open-arc lengths (X1 in `P_*` form). -/
theorem lenStrictMonoArc_of_yMergeOffTip (hYO : WedgeUnzip.YMergeOffTipStmt)
    (hC : LenPairCocycleArcStmt) (hF : LenFiniteArcStmt) : LenStrictMonoArcStmt :=
  lenStrictMonoArc_of_parts (pStarCapRegOff_of_yMergeOffTip hYO)
    (pStarGoodOffAll_of_yMergeOffTip hYO)
    (pStarBdryPosAllArc_of_core pStarRealizeStmt_holds (yGoodOffAll_of_yMergeOffTip hYO)
      (wedgeGoodOffAll_of_yMergeOffTip hYO) (wedgeExactAll_of_yMergeOffTip hYO)
      (wedgeContinuum_of_x WDec.wedgeDecompStmt_holds xContinuumStmt_holds)
      (pStarGoodOffAll_of_yMergeOffTip hYO))
    hC hF

end LocLen
end QuantumZipper

