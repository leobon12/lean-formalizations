import QuantumZipper.Proofs.Thm18.RTMeasCoord

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# RT-MEAS, part 2: `DownLenScaleFieldReadStmt` from the regularity of the pieces and the scale

The Borel readers of `DownLenScaleFieldReadStmt` (R18RTMeasDrv.lean) are built here:

* lengths at rational times: `lenRd q p`, the open-arc reader `LocLen.arcRd` (LocLenMeasArc.lean)
  of the coordinate field `fromCoords (ucoord …)` of the unzipped pieces on the arc
  `(O⁻_q, 0)` given by the side-image reader `G4Core.sideR`. It is exact as soon as the local
  boundary limit of the unzipped pieces exists on that arc (`LocLen.arcRd_eq_arcLen`);
* circle coordinates of the rescaled unzipped field: `fldRd Sc`, `rescCoord` of the same
  coordinate field at the scale read by `Sc` (RTMeasCoord.lean).

What remains are two strictly smaller nodes:

* `PiecesLenRegStmt`: a Borel set of full law carrying the path certificate `PathGoodAll`, the
  existence of the local boundary limits of the unzipped pieces on `(O⁻_q, 0)` at rational
  times `q`, and the monotonicity of their lengths (the monotonicity clause of
  `DownLenScaleFieldReadStmt`, verbatim). The pieces `configOfData (offData c₀)` carry the junk
  value `0` of `readOffField` at circles meeting the curve, so these are statements about the
  unzipped *pieces* (D82), not about the unzipped configuration (for which they are known,
  `LocLen.lenReadRegMeasArc_of_yMergeOffTip`); they follow from the latter by the masked
  exactness of unzipping at all rational times (RT2 core, `MaskPullCoreStmt`), not available
  here in that form.
* `ScaleReadStmt`: the scale clause of `DownLenScaleFieldReadStmt` alone (Borel reading of
  `areaScale` of the transported area of the pieces); proved in RTMeasScale.lean
  (`scaleReadStmt_of`) from `PiecesLenRegStmt` and the area regularity `AreaRegStmt`.

Own elementary bookkeeping (measurability the paper leaves implicit; Sheffield,
arXiv:1012.4797, p. 26 treats `Z^LEN_{−ℓ}` as a measurable map).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace R18
namespace RTMeas

open Thm18Asm Thm18Asm.G4Core CoordsFull

/-- **Regularity of the pieces** (open): a Borel set of full law on which the driver has the path
certificate, the unzipped pieces have a local boundary limit on `(O⁻_q, 0)` at every rational
time `q ≥ 0`, and their lengths are nondecreasing in the time. -/
def PiecesLenRegStmt : Prop :=
  ∀ (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample),
    Thm18Setting γ P B Y → Thm18Inputs γ P B Y →
      ∃ G : Set PX, MeasurableSet G ∧
        (∀ d : E6.FullData, πd d ∈ G → F1.PathGoodAll d.2 ∧ (Continuous d.2 →
          (∀ q : ℚ, 0 ≤ q → ∃ ν : Measure ℝ,
            IsVagueLimitOnR (Ioo (sideImages (drvOfData d) q).1 0)
              (bdryApprox γ (unzippedField γ (configOfData γ d).toPair q)) ν) ∧
          ∀ s t : ℝ, 0 ≤ s → s ≤ t → (unzipLengthsOpen γ (configOfData γ d).toPair s).1 ≤
            (unzipLengthsOpen γ (configOfData γ d).toPair t).1)) ∧
        ∀ᵐ ω ∂P, πd (offData (wedgeAConfig γ B Y ω).toPair) ∈ G

/-- **The scale clause of `DownLenScaleFieldReadStmt`** (open). -/
def ScaleReadStmt : Prop :=
  ∀ (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample),
    Thm18Setting γ P B Y → Thm18Inputs γ P B Y →
    ∀ ℓ : ℝ, 0 < ℓ →
      ∃ (G₂ : Set (PX × ℝ)) (Sc : PX × ℝ → ℝ), MeasurableSet G₂ ∧ Measurable Sc ∧
        (∀ (d : E6.FullData) (t : ℝ), (πd d, t) ∈ G₂ → Continuous d.2 →
          Sc (πd d, t) = areaScale (zipCapDownA γ t (configOfData γ d)).area) ∧
        ∀ᵐ ω ∂P, (πd (offData (wedgeAConfig γ B Y ω).toPair),
          lenTimeOpen γ ℓ (configOfData γ (offData (wedgeAConfig γ B Y ω).toPair)).toPair) ∈ G₂

/-- The coordinate field of the unzipped pieces at time `t`. -/
def zfld (γ : ℝ) (p : PX) (t : ℝ) : FieldSample :=
  ESM.fromCoords (ucoord γ (readOffField (dfull p)) (pcode p).2 t)

theorem measurable_zfld (γ : ℝ) : Measurable fun q : PX × ℝ => zfld γ q.1 q.2 := by
  have h1 : Measurable fun q : PX × ℝ =>
      (((readOffField (dfull q.1), (pcode q.1).2) : FieldSample × (ℕ → ℝ)), q.2) :=
    ((measurable_readOffField.comp (measurable_dfull.comp measurable_fst)).prodMk
      (measurable_snd.comp (measurable_pcode.comp measurable_fst))).prodMk measurable_snd
  exact ESM.measurable_fromCoords
    (c := fun q : PX × ℝ => ucoord γ (readOffField (dfull q.1)) (pcode q.1).2 q.2)
    (Measurable.comp (g := fun r : (FieldSample × (ℕ → ℝ)) × ℝ => ucoord γ r.1.1 r.1.2 r.2)
      (f := fun q : PX × ℝ =>
        (((readOffField (dfull q.1), (pcode q.1).2) : FieldSample × (ℕ → ℝ)), q.2))
      (measurable_ucoord γ) h1)

theorem coordsFull_zfld (γ : ℝ) {d : E6.FullData} (hc : Continuous d.2)
    (hp : F1.PathGoodAll d.2) {t : ℝ} (ht : 0 ≤ t) :
    coordsFull (zfld γ (πd d) t) = coordsFull (unzippedField γ (configOfData γ d).toPair t) := by
  rw [zfld, ← coordsFull_unzipped_configOfData γ hc hp ht, F1.coordsFull_fromCoords_coordsFull]

/-- The length reader at rational times. -/
def lenRd (γ : ℝ) (q : ℚ) (p : PX) : ℝ≥0∞ :=
  LocLen.arcRd γ (zfld γ p q) (sideR (pcode p).2 q).1 0

theorem measurable_lenRd (γ : ℝ) (q : ℚ) : Measurable (lenRd γ q) := by
  have hX : Measurable fun p : PX => zfld γ p q :=
    Measurable.comp (g := fun r : PX × ℝ => zfld γ r.1 r.2) (f := fun p : PX => (p, (q : ℝ)))
      (measurable_zfld γ) (measurable_id.prodMk measurable_const)
  refine LocLen.measurable_arcRd_comp γ hX ?_ measurable_const
  exact (measurable_sideR.comp ((measurable_snd.comp measurable_pcode).prodMk
    measurable_const)).fst

theorem lenRd_eq (γ : ℝ) {d : E6.FullData} (hc : Continuous d.2) (hp : F1.PathGoodAll d.2)
    {q : ℚ} (hq : 0 ≤ q) {ν : Measure ℝ}
    (hν : IsVagueLimitOnR (Ioo (sideImages (drvOfData d) q).1 0)
      (bdryApprox γ (unzippedField γ (configOfData γ d).toPair q)) ν) :
    (unzipLengthsOpen γ (configOfData γ d).toPair q).1 = lenRd γ q (πd d) := by
  have hq' : (0 : ℝ) ≤ q := by exact_mod_cast hq
  have hb : bdryApprox γ (unzippedField γ (configOfData γ d).toPair q) =
      bdryApprox γ (zfld γ (πd d) q) :=
    NuMeas.bdryApprox_congr_coordsFull γ (coordsFull_zfld γ hc hp hq').symm
  have hs : sideImages (drvOfData d) q = sideR (pcode (πd d)).2 q := by
    rw [drvOfData_eq_readDrv hc, pcode_πd]
    exact sideImages_eq_sideR hp hq'
  rw [hb, hs] at hν
  unfold lenRd
  rw [LocLen.arcRd_eq_arcLen isOpen_Ioo hν subset_rfl, LocLen.arcLen_congr_bdry hb.symm, ← hs]
  rfl

/-- The reader of the circle coordinates of the rescaled unzipped field. -/
def fldRd (γ : ℝ) (Sc : PX × ℝ → ℝ) (q : PX × ℝ) : ℕ → ℝ :=
  rescCoord γ (zfld γ q.1 q.2) (Sc q)

theorem measurable_fldRd (γ : ℝ) {Sc : PX × ℝ → ℝ} (hSc : Measurable Sc) :
    Measurable (fldRd γ Sc) :=
  Measurable.comp (g := fun r : FieldSample × ℝ => rescCoord γ r.1 r.2)
    (f := fun q : PX × ℝ => (zfld γ q.1 q.2, Sc q)) (measurable_rescCoord γ)
    ((measurable_zfld γ).prodMk hSc)

theorem fldRd_eq (γ : ℝ) {d : E6.FullData} (hc : Continuous d.2) (hp : F1.PathGoodAll d.2)
    {t : ℝ} (ht : 0 ≤ t) {Sc : PX × ℝ → ℝ}
    (hS : Sc (πd d, t) = areaScale (zipCapDownA γ t (configOfData γ d)).area) :
    fldRd γ Sc (πd d, t) =
      coordsFull (canonAConfig γ (zipCapDownA γ t (configOfData γ d))).fld := by
  unfold fldRd
  rw [hS, rescCoord_congr γ (coordsFull_zfld γ hc hp ht)]
  rfl

/-- **`DownLenScaleFieldReadStmt` from the regularity of the pieces and the scale reading.** -/
theorem downLenScaleFieldReadStmt_of (hR : PiecesLenRegStmt) (hS : ScaleReadStmt) :
    DownLenScaleFieldReadStmt := by
  intro γ Ω _ P _ B Y hSet hIn ℓ hℓ
  obtain ⟨G, hG, hGp, haeG⟩ := hR γ P B Y hSet hIn
  obtain ⟨G₂, Sc, hG₂, hSc, hSeq, haeG₂⟩ := hS γ P B Y hSet hIn ℓ hℓ
  refine ⟨G, lenRd γ, {x | x ∈ G₂ ∧ x.1 ∈ G ∧ 0 ≤ x.2}, Sc, fldRd γ Sc, hG,
    measurable_lenRd γ, hG₂.inter ((hG.preimage measurable_fst).inter
      (measurableSet_le measurable_const measurable_snd)), hSc, measurable_fldRd γ hSc,
    fun d hd hc => ?_, fun d t hd hc => ?_, ?_⟩
  · obtain ⟨hp, hreg⟩ := hGp d hd
    obtain ⟨hlim, hmono⟩ := hreg hc
    refine ⟨fun q hq => ?_, hmono⟩
    obtain ⟨ν, hν⟩ := hlim q hq
    exact lenRd_eq γ hc hp hq hν
  · obtain ⟨h2, h1, ht⟩ := hd
    exact ⟨hSeq d t h2 hc, fldRd_eq γ hc (hGp d h1).1 ht (hSeq d t h2 hc)⟩
  · filter_upwards [haeG, haeG₂] with ω h1 h2
    exact ⟨h1, h2, h1, Real.sInf_nonneg fun s hs => hs.1⟩

end RTMeas
end R18
end QuantumZipper
