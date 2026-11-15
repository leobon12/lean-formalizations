/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SdqCross
import InteractingSLE.Spec.Supplement.GW2RuLive

/-!
# The near structure (N3), step F″: the gap family from the junction SPAN, and its positivity

Packet PROVE-GW2-SDE (round 17; D29). The structure lemma (`GW2Sdp.nearStruct_of_sideInv`) only reads the junction
span `jR − jL`, which never shrinks (`GW2Sdp.junction_span`). So the gap reads the root prefix's span, which is
positive as soon as the root prefix has positive relative capacity (the hull's two sides separate,
`MartChar.RealFlow.rightImg_add_rightImg_neg_ge`), with no interior-tip input:

* `spanFun p = 17/35 · min ((markPos 0 − markPosL 0)/2, 1)`, **`four_sqrt_le_span`** (`4√T ≤ markPos 0 − markPosL 0`),
  `spanFun_pos`;
* `refFun2` (the liminf along ROOTX's strict root-`x` family of the root stage, clamped), measurable for the ambient
  σ-algebra and for the null-completion of `c.sigma (x,0) []`; **`gapFam2`**, **`measurable_gapFam2`** (`hgap`),
  `ae_gapFam2_eq`;
* **`ae_refFun2_eq`**: on a good counterflow record with the root time before the root-stage contact, `refFun2` is
  eventually `spanFun` of the version's prefix record, and the clock at the root time is below the cap;
* **`ae_gapFam2_pos`** (`hpos` of the scaled-cover top): the gap is positive almost surely on every cover event
  (ROOTX's `GW2Ru.ae_alive_goodX`, `GW2Ru.ae_nil_lt_contactX`, the clock strictly increasing before the contact).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Sdr

open Restart Exist.StagedLaw GW2Rz GW2Rd GW2Sde GW2Sdq GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31
  Sec7.StripSideHeightProb

/-- **The span functional of a record**: `17/35 · min ((markPos 0 − markPosL 0)/2, 1)`. -/
def spanFun (p : RecData) : ℝ :=
  17 / 35 * min ((markPos (rdrv p) (rtime p) 0 - markPosL (rdrv p) (rtime p) 0) / 2) 1

theorem measurable_spanFun : Measurable spanFun :=
  measurable_const.mul
    (((Supp8.GB6.measurable_markPos_rec.sub Supp8.GB6.measurable_markPosL_rec).div_const 2).min measurable_const)

/-- **The two sides of a hull separate**: `4√T ≤ markPos 0 − markPosL 0`. -/
theorem four_sqrt_le_span (p : RecData) :
    4 * Real.sqrt (rtime p) ≤ markPos (rdrv p) (rtime p) 0 - markPosL (rdrv p) (rtime p) 0 := by
  have h := MartChar.RealFlow.rightImg_add_rightImg_neg_ge (continuous_rdrv p) 0 0 (rtime_nonneg p)
  have hR := rightImg_sub_le_markPos (continuous_rdrv p) (rdrv_zero p) (rtime_nonneg p)
  have hL := markPosL_le_neg_rightImg (continuous_rdrv p) (rdrv_zero p) (rtime_nonneg p)
  linarith

theorem spanFun_nonneg (p : RecData) : 0 ≤ spanFun p := by
  have := four_sqrt_le_span p
  have hs := Real.sqrt_nonneg (rtime p)
  unfold spanFun
  exact mul_nonneg (by norm_num) (le_min (by linarith) zero_le_one)

theorem spanFun_le (p : RecData) : spanFun p ≤ 17 / 35 := by
  unfold spanFun
  have := min_le_right ((markPos (rdrv p) (rtime p) 0 - markPosL (rdrv p) (rtime p) 0) / 2) 1
  nlinarith

theorem spanFun_pos {p : RecData} (hp : 0 < rtime p) : 0 < spanFun p := by
  have := four_sqrt_le_span p
  have hs := Real.sqrt_pos.2 hp
  unfold spanFun
  exact mul_pos (by norm_num) (lt_min (by linarith) one_pos)

/-- The span bound read off the functional: `2 · (35/17) · spanFun p ≤ markPos 0 − markPosL 0`. -/
theorem span_ge_of_spanFun (p : RecData) :
    70 / 17 * spanFun p ≤ markPos (rdrv p) (rtime p) 0 - markPosL (rdrv p) (rtime p) 0 := by
  unfold spanFun
  have := min_le_left ((markPos (rdrv p) (rtime p) 0 - markPosL (rdrv p) (rtime p) 0) / 2) 1
  nlinarith

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]

section Ref

variable (h13 : Exist.Theorem13Statement.{u}) (c : SourceData Ω) (x : RootIdx c.Θ c.Q) (hx : 0 ≤ rootPt x)

/-- **The reference junction span**: the limit inferior along the versions, clamped to `[0, 17/35]`. -/
def refFun2 (ω : Ω) : ℝ :=
  max 0 (min (liminf (fun n => spanFun (refPre h13 c x hx n ω)) atTop) (17 / 35))

variable (hs : 0 < c.s)

include hs in
theorem refFun2_measurable : Measurable (refFun2 h13 c x hx) :=
  measurable_const.max ((Measurable.liminf fun n => measurable_spanFun.comp
    (refPre_measurable h13 c x hx hs n)).min measurable_const)

include hs in
theorem refFun2_aeSigma : Measurable[LocalSets.aeSigma (c.sigma (x, 0) []) c.P] (refFun2 h13 c x hx) := by
  have hl : Measurable[LocalSets.aeSigma (c.sigma (x, 0) []) c.P]
      fun ω => liminf (fun n => spanFun (refPre h13 c x hx n ω)) atTop :=
    Measurable.liminf fun n => measurable_spanFun.comp (refPre_aeSigma h13 c x hx hs n)
  exact measurable_const.max (hl.min measurable_const)

theorem abs_refFun2_le (ω : Ω) : |refFun2 h13 c x hx ω| ≤ 17 / 35 := by
  unfold refFun2
  rw [abs_of_nonneg (le_max_left _ _)]
  exact max_le (by norm_num) (min_le_right _ _)

include hs in
theorem exists_gapVersion2 :
    ∃ g : Ω → ℝ, Measurable[c.sigma (x, 0) []] g ∧ refFun2 h13 c x hx =ᵐ[c.P] g :=
  exists_measurable_ae_eq_of_aeSigma (stageSigma_le c.hβA.1 c.hh.1 c.hcf c.s _ _)
    (refFun2_measurable h13 c x hx hs) (refFun2_aeSigma h13 c x hx hs) (abs_refFun2_le h13 c x hx)

include hs in
/-- **On the good event, before the root-stage contact, the reference span is that of every late version's prefix
record.** -/
theorem ae_refFun2_eq : ∀ᵐ ω ∂c.P, cfRec c.s c.W c.ζ ω ∈ goodX (rootPt x) c.s →
    (historyTime c (x, 0) [] : ℝ≥0∞) < contactX (rootPt x) c.s (schedTr c (x, 0) [] 0) c.α ω →
    ∀ᶠ n in atTop, refFun2 h13 c x hx ω = spanFun (refPre h13 c x hx n ω) ∧
      ENNReal.ofReal (clockX (rootPt x) c.s c.W c.ζ (schedW c (x, 0) [] 0) (historyTime c (x, 0) []) ω) <
        (refVer h13 c x hx).2 n ω := by
  have hspec := refVer_spec h13 c x hx
  have hpair : ∀ᵐ ω ∂c.P, ∀ n m : ℕ, cfRec c.s c.W c.ζ ω ∈ goodX (rootPt x) c.s →
      ((historyTime c (x, 0) [] : ℝ≥0∞) < contactX (rootPt x) c.s (schedTr c (x, 0) [] 0) c.α ω ∧
        ENNReal.ofReal (clockX (rootPt x) c.s c.W c.ζ (schedW c (x, 0) [] 0) (historyTime c (x, 0) []) ω) <
          (refVer h13 c x hx).2 n ω) →
      ((historyTime c (x, 0) [] : ℝ≥0∞) < contactX (rootPt x) c.s (schedTr c (x, 0) [] 0) c.α ω ∧
        ENNReal.ofReal (clockX (rootPt x) c.s c.W c.ζ (schedW c (x, 0) [] 0) (historyTime c (x, 0) []) ω) <
          (refVer h13 c x hx).2 m ω) →
      refPre h13 c x hx n ω = refPre h13 c x hx m ω :=
    ae_all_iff.2 fun n => ae_all_iff.2 fun m =>
      GW2Sdo.ae_stgPreRecX_sched_eq h13 c (x, 0) [] 0 0 hs hx (hspec.1 n).1.1 (hspec.1 m).1.1
  filter_upwards [hspec.2.2.2.2, hpair] with ω hex hpω hcf hTc
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hex hcf _ hTc)
  have hconst : ∀ n ≥ N, spanFun (refPre h13 c x hx n ω) = spanFun (refPre h13 c x hx N ω) := fun n hn =>
    by rw [hpω n N hcf ⟨hTc, hN n hn⟩ ⟨hTc, hN N le_rfl⟩]
  have hlim : liminf (fun n => spanFun (refPre h13 c x hx n ω)) atTop = spanFun (refPre h13 c x hx N ω) :=
    (tendsto_const_nhds.congr' (eventually_atTop.2 ⟨N, fun n hn => (hconst n hn).symm⟩)).liminf_eq
  have hval : refFun2 h13 c x hx ω = spanFun (refPre h13 c x hx N ω) := by
    unfold refFun2
    rw [hlim, min_eq_left (spanFun_le _), max_eq_right (spanFun_nonneg _)]
  filter_upwards [eventually_ge_atTop N] with n hn
  exact ⟨hval.trans (hconst n hn).symm, hN n hn⟩

end Ref

/-! ### The gap family -/

open Classical in
/-- **The gap at a root** (span version): a `c.sigma (x, ·) []`-measurable version of the reference span at good
roots, `1` elsewhere. -/
def gapAt2 (c : SourceData Ω) (x : RootIdx c.Θ c.Q) : Ω → ℝ :=
  if h : 0 ≤ rootPt x ∧ 0 < c.s then
    (exists_gapVersion2 Sec5.Aux61Cpt.theorem13Statement_of_cptCover.{u} c x h.1 h.2).choose
  else fun _ => 1

/-- **The scaled cover's gap family** (span version; REVIEW-FABLE-T14 T0, D24 (3)). -/
def gapFam2 : RootCv.GapFamily.{u} := fun _ _ _ c x => gapAt2 c x

/-- **`hgap`**: the gap is known at the root's stage start. -/
theorem measurable_gapFam2 (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) : Measurable[c.sigma r []] (gapFam2 Ω c r.1) := by
  classical
  change Measurable[c.sigma r []] (gapAt2 c r.1)
  unfold gapAt2
  split_ifs with h
  · exact (exists_gapVersion2 Sec5.Aux61Cpt.theorem13Statement_of_cptCover.{u} c r.1 h.1 h.2).choose_spec.1
  · exact measurable_const

theorem ae_gapFam2_eq (c : SourceData Ω) (x : RootIdx c.Θ c.Q) (h : 0 ≤ rootPt x ∧ 0 < c.s) :
    refFun2 Sec5.Aux61Cpt.theorem13Statement_of_cptCover.{u} c x h.1 =ᵐ[c.P] gapFam2 Ω c x := by
  classical
  change refFun2 _ c x h.1 =ᵐ[c.P] gapAt2 c x
  unfold gapAt2
  simp only [h, and_self, ↓reduceDIte]
  exact (exists_gapVersion2 Sec5.Aux61Cpt.theorem13Statement_of_cptCover.{u} c x h.1 h.2).choose_spec.2

/-! ### Positivity -/

/-- **The root-`x` clock is positive at a positive time before the contact** (strictly increasing from `0`). -/
theorem clockX_pos {Ω' : Type*} {x₀ : ℝ} {s : ℝ≥0} {W' : ℝ≥0 → Ω' → ℝ} {ζ' : Ω' → ℝ≥0∞} {w : ℝ≥0 → Ω' → ℝ}
    {γ α : Ω' → ℝ≥0 → ℂ} {ω : Ω'} (hω : PhysGoodX x₀ s W' ζ' w γ α ω) (hs : 0 < s) (hx : 0 ≤ x₀) {T : ℝ≥0}
    (hT0 : 0 < T) (hTc : (T : ℝ≥0∞) < contactX x₀ s γ α ω) : 0 < clockX x₀ s W' ζ' w T ω := by
  obtain ⟨⟨hwc, hw0, hγ⟩, ⟨hα, hW, hW0, hζ⟩, harc, -, -⟩ := hω
  obtain ⟨h0, hm, -⟩ := clock_props W' ζ' ω hα hW hW0 hζ hs hx harc hwc hw0 hγ
  have hc0 := contact_pos W' ω hα hx harc hγ
  have h := hm (show ((0 : ℝ≥0) : ℝ≥0∞) < _ by rw [ENNReal.coe_zero]; exact hc0) hTc hT0
  change 0 < RootH29.forwardCapacity x₀ s T (cfRec s W' ζ' ω, recOf (T : ℝ≥0∞) ((fun t => w t ω), ⊤))
  rw [← h0]
  exact h

/-- **`hpos`: the gap is positive almost surely on every cover event** (Theorem 1.3, R48). -/
theorem ae_gapFam2_pos (c : SourceData Ω) (x : RootIdx c.Θ c.Q) :
    ∀ᵐ ω ∂c.P, ω ∈ RootCv.coverEvent c (x, 0) → 0 < gapFam2 Ω c x ω := by
  classical
  by_cases h : 0 ≤ rootPt x ∧ 0 < c.s
  · have h13 : Exist.Theorem13Statement.{u} := Sec5.Aux61Cpt.theorem13Statement_of_cptCover.{u}
    obtain ⟨hGT, -, hGTae⟩ := schedGTX_spec h13 c (x, 0) [] 0
    filter_upwards [ae_gapFam2_eq c x h, ae_refFun2_eq h13 c x h.1 h.2, GW2Ru.ae_alive_goodX h13 c (x, 0),
      GW2Ru.ae_nil_lt_contactX h13 c (x, 0), hGTae] with ω hgap href hgood hnil hGTω hcov
    have halive : ω ∈ (RootJ32.experiment c (x, 0)).data.alive ((RootJ32.construction c).G (x, 0)) [] := hcov
    have hcf := hgood [] halive
    have hTc := hnil 0 halive
    obtain ⟨n, hn1, hn2⟩ := (href hcf hTc).exists
    have hval : gapFam2 Ω c x ω = spanFun (refPre h13 c x h.1 n ω) := hgap.symm.trans hn1
    rw [hval]
    refine spanFun_pos ?_
    have hT0 : 0 < historyTime c (x, 0) [] := by
      rw [GW2Ru.historyTime_nil]
      exact c.hQpos _ x.2.2.2
    have hclk := clockX_pos (hGT ω (hGTω.2 hcf)) h.2 h.1 hT0 hTc
    have hS := GW2Sdo.stgStartX_eq_clockX hGT h.2 h.1 (hGTω.2 hcf) hTc hn2
    change 0 < (((min ((stgStartX (rootPt x) c.s c.W c.ζ (schedW c (x, 0) [] 0) (schedGTX h13 c (x, 0) [] 0)
      ((refVer h13 c x h.1).2 n) (historyTime c (x, 0) []) ω : ℝ≥0) : ℝ≥0∞) ⊤).toNNReal : ℝ≥0) : ℝ)
    rw [min_eq_left le_top, ENNReal.toNNReal_coe, hS, Real.coe_toNNReal _ hclk.le]
    exact hclk
  · refine Eventually.of_forall fun ω _ => ?_
    change 0 < gapAt2 c x ω
    unfold gapAt2
    simp only [h, ↓reduceDIte]
    exact one_pos

end InteractingSLE.Theorem14.GW2Sdr
