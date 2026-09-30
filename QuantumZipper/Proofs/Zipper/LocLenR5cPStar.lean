import QuantumZipper.Proofs.Zipper.LocLenR5cMain
import QuantumZipper.Proofs.Zipper.HitScaleZip

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R5c (D75): `HitScaleZipArcStmt`, `LocalAbsRichArcStmt` and `UnzipMeasArcStmt` for `P_*`

Open-arc copy (`handoff/FOLLOW-PAPER-13.md`, task R5c) of `LocHitScalePStar.lean` and
`HitScaleZip.lean:44–172`: the zipper behaviour needed for the local reading, with open-arc
lengths and goodness off `offSet W t` (from `PStarGoodOffAllStmt`, no global boundary limit and
no tip estimate).

* `HitScaleZipArc`, `HitScaleZipArcStmt`, `localAbsRichArcStmt_of_hitScaleZip`,
  `unzipMeasArc_of_hitScaleZip`;
* `PStarLenStartArcStmt`, `PStarLenInfArcStmt` (open-arc copies of `E6.PStarLenStartStmt`,
  `E6.PStarLenInfStmt`); **`hitScaleZipArcStmt_of`** (copy of `E6.hitScaleZipStmt_of`).

Sheffield arXiv:1012.4797 §5.4, pp. 70–72 (the left side of `η[0,t]` has quantum length
tending to `0` as `t → 0` and to `∞` as `t → ∞`; unzipping preserves the area measure's local
finiteness and infinite total mass); the reduction is own elementary bookkeeping, as for the
originals.
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped NNReal ENNReal Topology

namespace QuantumZipper.LocLen.R5c

open E6 D3Plus MeasUnzip CharFun

/-- Copy of `E6.HitScaleZip` (LocHitScalePStar.lean:31) with open-arc lengths and goodness off
`offSet`. -/
structure HitScaleZipArc (γ ℓ : ℝ) (y : Cfg) : Prop where
  lim : ∀ q : ℚ, 0 < (q : ℝ) → IsLQGGoodOff γ (unzippedField γ y q) (offSet y.2 q)
  mono : ∀ s t : ℝ, 0 ≤ s → s ≤ t → (unzipLengthsArc γ y s).1 ≤ (unzipLengthsArc γ y t).1
  reach : ∃ s : ℝ, 0 ≤ s ∧ ENNReal.ofReal ℓ ≤ (unzipLengthsArc γ y s).1
  pos : 0 < lenTimeArc γ ℓ y
  area : ∃ μ, IsVagueLimitOn H (areaApprox γ (unzippedField γ y (lenTimeArc γ ℓ y))) μ
  scale : 0 < scaleParam γ (unzippedField γ y (lenTimeArc γ ℓ y))

/-- Copy of `E6.HitScaleZipStmt` (LocHitScalePStar.lean:41). -/
def HitScaleZipArcStmt : Prop :=
  ∀ (κ : ℝ) {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Y : Ω' → FieldSample) (B' : ℝ≥0 → Ω' → ℝ), Thm13Asm.IsPStarSample κ P' Y B' →
    ∀ ℓ₁ : ℝ, 0 < ℓ₁ → ∀ᵐ ω' ∂P', HitScaleZipArc (Real.sqrt κ) ℓ₁ (Y ω', drive κ B' ω')

/-- Copy of `E6.locHitScaleStmt_pstar`. -/
theorem locHitScaleArcStmt_pstar (h : HitScaleZipArcStmt) (κ : ℝ) {Ω' : Type}
    [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P'] (Y : Ω' → FieldSample)
    (B' : ℝ≥0 → Ω' → ℝ) (hP : Thm13Asm.IsPStarSample κ P' Y B') (ℓ₁ : ℝ) (hℓ : 0 < ℓ₁) :
    LocHitScaleArcStmt (Real.sqrt κ) ℓ₁ P' (fun ω' => (Y ω', drive κ B' ω')) := by
  have hB := hP.2.2.2.1
  refine locHitScaleArcStmt_of_good (κ := κ) hP.1 (aemeasurable_locRich_pstar hP) ?_
  filter_upwards [h κ P' Y B' hP ℓ₁ hℓ, hB.cont, hB.toIsPreBrownianReal.eval_zero_ae_eq_zero,
    RS.ae_real_alive hB hP.1 hP.2.1.le] with ω hz hc h0 hal
  exact ⟨continuous_const.mul (hc.comp continuous_real_toNNReal), by simp [drive, h0],
    fun z hz s hs => hal z hz s hs, hz.lim, hz.mono, hz.reach, hz.pos, hz.area, hz.scale⟩

/-- **B5 locality `LocalAbsRichArcStmt` from `HitScaleZipArcStmt`** (copy of
`E6.localAbsRichStmt_of_hitScaleZip`). -/
theorem localAbsRichArcStmt_of_hitScaleZip (h : HitScaleZipArcStmt) : LocalAbsRichArcStmt :=
  localAbsRichArcStmt_of_hitScale fun κ _ _ P' _ Y B' hP ℓ₁ hℓ =>
    locHitScaleArcStmt_pstar h κ P' Y B' hP ℓ₁ hℓ

/-- **`UnzipMeasArcStmt` from `HitScaleZipArcStmt`.** -/
theorem unzipMeasArc_of_hitScaleZip (h : HitScaleZipArcStmt) : UnzipMeasArcStmt :=
  unzipMeasArc_of_localAbsRich (localAbsRichArcStmt_of_hitScaleZip h)

/-! ## `HitScaleZipArcStmt` from goodness off the tip and the length nodes -/

/-- Open-arc copy of `E6.PStarLenStartStmt` (HitScaleZip.lean:47). -/
def PStarLenStartArcStmt : Prop :=
  ∀ (κ : ℝ) {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Y : Ω' → FieldSample) (B' : ℝ≥0 → Ω' → ℝ), Thm13Asm.IsPStarSample κ P' Y B' →
    ∀ᵐ ω ∂P', Tendsto (fun t => (unzipLengthsArc (Real.sqrt κ) (Y ω, drive κ B' ω) t).1)
      (𝓝[>] 0) (𝓝 0)

/-- Open-arc copy of `E6.PStarLenInfStmt` (HitScaleZip.lean:54). -/
def PStarLenInfArcStmt : Prop :=
  ∀ (κ : ℝ) {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Y : Ω' → FieldSample) (B' : ℝ≥0 → Ω' → ℝ), Thm13Asm.IsPStarSample κ P' Y B' →
    ∀ᵐ ω ∂P', ⨆ t ∈ Ici (0 : ℝ), (unzipLengthsArc (Real.sqrt κ) (Y ω, drive κ B' ω) t).1 = ⊤

theorem exists_reachArc_of_iSup_eq_top {γ ℓ : ℝ} {y : Cfg}
    (h : ⨆ t ∈ Ici (0 : ℝ), (unzipLengthsArc γ y t).1 = ⊤) :
    ∃ s : ℝ, 0 ≤ s ∧ ENNReal.ofReal ℓ ≤ (unzipLengthsArc γ y s).1 := by
  have hlt : ENNReal.ofReal ℓ < ⨆ t ∈ Ici (0 : ℝ), (unzipLengthsArc γ y t).1 :=
    h ▸ ENNReal.ofReal_lt_top
  obtain ⟨t, ht⟩ := lt_iSup_iff.1 hlt
  obtain ⟨ht0, hl⟩ := lt_iSup_iff.1 ht
  exact ⟨t, ht0, hl.le⟩

theorem lenTimeArc_nonneg (γ ℓ : ℝ) (y : Cfg) : 0 ≤ lenTimeArc γ ℓ y :=
  Real.sInf_nonneg fun _ hs => hs.1

/-- Copy of `E6.tHit_pos_of`. -/
theorem lenTimeArc_pos_of {γ ℓ : ℝ} {y : Cfg} (hℓ : 0 < ℓ)
    (hmono : MonotoneOn (fun t => (unzipLengthsArc γ y t).1) (Ici 0))
    (h0 : Tendsto (fun t => (unzipLengthsArc γ y t).1) (𝓝[>] 0) (𝓝 0))
    (hreach : ∃ s : ℝ, 0 ≤ s ∧ ENNReal.ofReal ℓ ≤ (unzipLengthsArc γ y s).1) :
    0 < lenTimeArc γ ℓ y := by
  have hlt : ∀ᶠ t in 𝓝[>] (0 : ℝ), (unzipLengthsArc γ y t).1 < ENNReal.ofReal ℓ :=
    h0 (gt_mem_nhds (ENNReal.ofReal_pos.2 hℓ))
  obtain ⟨δ, hδlt, hδ⟩ := (hlt.and self_mem_nhdsWithin).exists
  have hδ0 : (0 : ℝ) < δ := hδ
  obtain ⟨s₀, hs₀⟩ := hreach
  refine hδ0.trans_le (le_csInf ⟨s₀, hs₀⟩ fun s hs => ?_)
  by_contra hsδ
  rw [not_le] at hsδ
  exact absurd (hs.2.trans (hmono hs.1 hδ0.le hsδ.le)) (not_le.2 hδlt)

/-- The area limit of a sample good off `S` (as `Prop16Area.G.isVagueLimitOn_H_of_good`; the
area part of `IsLQGGoodOff` is untouched by D75). -/
theorem isVagueLimitOn_H_of_goodOff {γ : ℝ} {x : FieldSample} {S : Set ℝ}
    (hx : IsLQGGoodOff γ x S) : ∃ μ, IsVagueLimitOn H (areaApprox γ x) μ := by
  obtain ⟨⟨F, hF⟩, -, μ, hμ⟩ := hx
  exact ⟨μ, hμ.1, hμ.2.1, fun f hf hfc hfU =>
    ((hμ.2.2 f hf hfc hfU).comp GoodSample.tendsto_one_goodFilter).congr fun k => by
      simp only [Function.comp, goodRad, GoodSample.areaR_radius γ hF]⟩

/-- **`HitScaleZipArcStmt` from goodness off the tip and the length/area nodes** (copy of
`E6.hitScaleZipStmt_of`, HitScaleZip.lean:158). -/
theorem hitScaleZipArcStmt_of (hG : PStarGoodOffAllStmt) (hM : LenStrictMonoArcStmt)
    (hS : PStarLenStartArcStmt) (hI : PStarLenInfArcStmt) (hA : E6.PStarAreaAllStmt) :
    HitScaleZipArcStmt := by
  intro κ Ω' _ P' _ Y B' hP ℓ₁ hℓ
  filter_upwards [hG κ P' Y B' hP, hM κ P' Y B' hP, hS κ P' Y B' hP, hI κ P' Y B' hP,
    hA κ P' Y B' hP] with ω hg hm hs hi ha
  have hmono : MonotoneOn
      (fun t => (unzipLengthsArc (Real.sqrt κ) (Y ω, drive κ B' ω) t).1) (Ici 0) :=
    hm.monotoneOn
  have hreach := exists_reachArc_of_iSup_eq_top (ℓ := ℓ₁) hi
  have hτ := lenTimeArc_nonneg (Real.sqrt κ) ℓ₁ (Y ω, drive κ B' ω)
  exact ⟨fun q hq => hg q hq.le,
    fun s t hs hst => hmono hs (hs.trans hst) hst, hreach, lenTimeArc_pos_of hℓ hmono hs hreach,
    isVagueLimitOn_H_of_goodOff (hg _ hτ),
    scaleParam_pos_of_area (ha _ hτ).1 (ha _ hτ).2⟩

end QuantumZipper.LocLen.R5c
