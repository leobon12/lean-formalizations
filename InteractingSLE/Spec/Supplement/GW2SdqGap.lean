/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SdqMod
import InteractingSLE.Spec.Supplement.GW2SdpRoot
import InteractingSLE.Spec.Supplement.GW2SdoWord
import InteractingSLE.Spec.Supplement.GW2RvStrict
import InteractingSLE.Spec.Supplement.GW2RvPkg
import InteractingSLE.Spec.Sec5.Aux61CptThm

/-!
# The near structure (N3), step F: the scaled cover's gap family

Packet PROVE-GW2-SDE (round 16; D24 (3), REVIEW-FABLE-T14 T0). The gap is `17/35` times the root stage word's
junction distance: the two junctions `markPosL 0 < 0 < markPos 0` of the root prefix in the root-`x` stage chart
(the root stage word's seed-side positions; with them the far-label clause of (N3) is exact, `GW2Sdp`):

* `junctionFun p = 17/35 · min (−markPosL 0, markPos 0, 1)` of a record, measurable, in `[0, 17/35]`;
* `refPre n`: the root-stage prefix record of ROOTX's root-`x` instance (root `(x, 0)`, empty history, candidate
  `0`) with version `n` of ROOTX's strict family (`GW2Rv.exists_schedVersionsXA_strict`); `refFun`: the limit inferior
  of the junction functional along the versions, clamped to `[0, 17/35]` — measurable for the ambient σ-algebra and for
  the null-completion of the root's retained σ-algebra (`GW2Rz.comap_stgPreRecX_le_aeSigma`);
* **`gapFam`**: a `c.sigma r []`-measurable version of `refFun` (`GW2Sdq.exists_measurable_ae_eq_of_aeSigma`) at good
  roots (`0 ≤ rootPt`, `0 < s`), `1` elsewhere; **`measurable_gapFam`** (the scale `r.2` does not enter
  `c.sigma r []`); **`ae_gapFam_eq`**: almost surely it is `refFun` at good roots.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Sdq

open Restart Exist.StagedLaw GW2Rz GW2Rd GW2Sde GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31
  Sec7.StripSideHeightProb

/-- **The junction functional of a record**: `17/35 · min (−markPosL 0, markPos 0, 1)`. -/
def junctionFun (p : RecData) : ℝ :=
  17 / 35 * min (min (-markPosL (rdrv p) (rtime p) 0) (markPos (rdrv p) (rtime p) 0)) 1

theorem measurable_junctionFun : Measurable junctionFun :=
  measurable_const.mul
    (((Supp8.GB6.measurable_markPosL_rec.neg).min Supp8.GB6.measurable_markPos_rec).min measurable_const)

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]

section Ref

variable (h13 : Exist.Theorem13Statement.{u}) (c : SourceData Ω) (x : RootIdx c.Θ c.Q) (hx : 0 ≤ rootPt x)

/-- The reference version family: ROOTX's strict root-`x` family of the root stage (root `(x, 0)`, history `[]`,
candidate `0`). -/
def refVer : (ℕ → ℝ≥0 → Ω → ℝ) × (ℕ → Ω → ℝ≥0∞) :=
  ((GW2Rv.exists_schedVersionsXA_strict h13 c (x, 0) [] 0 hx).choose,
    (GW2Rv.exists_schedVersionsXA_strict h13 c (x, 0) [] 0 hx).choose_spec.choose)

theorem refVer_spec :
    (∀ n, IsRelVersionXA (rootPt x) c.s c.P c.W c.ζ (schedW c (x, 0) [] 0) (schedTr c (x, 0) [] 0) c.α
      ((refVer h13 c x hx).1 n) ((refVer h13 c x hx).2 n)) ∧
      (∀ n ω, (refVer h13 c x hx).2 n ω ≤ (refVer h13 c x hx).2 (n + 1) ω) ∧
      (∀ᵐ ω ∂c.P, cfRec c.s c.W c.ζ ω ∈ goodX (rootPt x) c.s → ∀ n,
        (refVer h13 c x hx).2 n ω < (refVer h13 c x hx).2 (n + 1) ω) ∧
      (∀ n ω, (refVer h13 c x hx).2 n ω ≠ ⊤) ∧
      ∀ᵐ ω ∂c.P, cfRec c.s c.W c.ζ ω ∈ goodX (rootPt x) c.s → ∀ t : ℝ≥0,
        (t : ℝ≥0∞) < contactX (rootPt x) c.s (schedTr c (x, 0) [] 0) c.α ω →
        ∀ᶠ n in atTop, ENNReal.ofReal (clockX (rootPt x) c.s c.W c.ζ (schedW c (x, 0) [] 0) t ω) <
          (refVer h13 c x hx).2 n ω :=
  (GW2Rv.exists_schedVersionsXA_strict h13 c (x, 0) [] 0 hx).choose_spec.choose_spec

/-- **The root-stage prefix record of version `n`.** -/
def refPre (n : ℕ) : Ω → RecData :=
  stgPreRecX (rootPt x) c.s c.W c.ζ (schedW c (x, 0) [] 0) (schedGTX h13 c (x, 0) [] 0) ((refVer h13 c x hx).2 n)
    (historyTime c (x, 0) []) ((refVer h13 c x hx).1 n)

/-- **The reference junction distance**: the limit inferior along the versions, clamped to `[0, 17/35]`. -/
def refFun (ω : Ω) : ℝ :=
  max 0 (min (liminf (fun n => junctionFun (refPre h13 c x hx n ω)) atTop) (17 / 35))

variable (hs : 0 < c.s)

include hs in
theorem refPre_aeSigma (n : ℕ) :
    Measurable[LocalSets.aeSigma (c.sigma (x, 0) []) c.P] (refPre h13 c x hx n) := by
  obtain ⟨hGT, hGTm, hGTae⟩ := schedGTX_spec h13 c (x, 0) [] 0
  have h := comap_stgPreRecX_le_aeSigma hGT hs hx (measurable_gb6Rec_src c) (measurable_schedW c (x, 0) [] 0)
    hGTm hGTae ((refVer_spec h13 c x hx).1 n).1 (historyTime c (x, 0) [])
    ((GW2Rd.measurable_cfRec_sigma c (x, 0) []).comap_le.trans (LocalSets.le_aeSigma _ _))
    fun t ht => (comap_schedW_le_sigma c (x, 0) [] 0 ht).trans (LocalSets.le_aeSigma _ _)
  exact measurable_iff_comap_le.2 h

include hs in
theorem refPre_measurable (n : ℕ) : Measurable (refPre h13 c x hx n) := by
  obtain ⟨hGT, hGTm, hGTae⟩ := schedGTX_spec h13 c (x, 0) [] 0
  have hrec := measurable_gb6Rec_src c
  have hWm := measurable_schedW c (x, 0) [] 0
  have h := measurable_stgPreRecX hGT hs hx hrec hWm (measurableSet_goodSetX_physFilt hrec hWm hGTm hGTae)
    ((refVer_spec h13 c x hx).1 n).1 (historyTime c (x, 0) [])
  refine h.mono ?_ le_rfl
  exact sup_le (Supp8.RelSafe.physSigma_le hrec hWm _) (Ito.nullSets_le c.P)

include hs in
theorem refFun_measurable : Measurable (refFun h13 c x hx) :=
  measurable_const.max ((Measurable.liminf fun n => measurable_junctionFun.comp
    (refPre_measurable h13 c x hx hs n)).min measurable_const)

include hs in
theorem refFun_aeSigma : Measurable[LocalSets.aeSigma (c.sigma (x, 0) []) c.P] (refFun h13 c x hx) := by
  have hl : Measurable[LocalSets.aeSigma (c.sigma (x, 0) []) c.P]
      fun ω => liminf (fun n => junctionFun (refPre h13 c x hx n ω)) atTop :=
    Measurable.liminf fun n => measurable_junctionFun.comp (refPre_aeSigma h13 c x hx hs n)
  exact measurable_const.max (hl.min measurable_const)

theorem abs_refFun_le (ω : Ω) : |refFun h13 c x hx ω| ≤ 17 / 35 := by
  unfold refFun
  rw [abs_of_nonneg (le_max_left _ _)]
  exact max_le (by norm_num) (min_le_right _ _)

include hs in
theorem exists_gapVersion :
    ∃ g : Ω → ℝ, Measurable[c.sigma (x, 0) []] g ∧ refFun h13 c x hx =ᵐ[c.P] g :=
  exists_measurable_ae_eq_of_aeSigma
    (stageSigma_le c.hβA.1 c.hh.1 c.hcf c.s _ _) (refFun_measurable h13 c x hx hs) (refFun_aeSigma h13 c x hx hs)
    (abs_refFun_le h13 c x hx)

theorem junctionFun_nonneg (p : RecData) : 0 ≤ junctionFun p := by
  have h1 := markPosL_nonpos (continuous_rdrv p) (rdrv_zero p) (rtime_nonneg p) (le_refl (0 : ℝ))
  have h2 := markPos_nonneg (continuous_rdrv p) (rdrv_zero p) (rtime_nonneg p) (le_refl (0 : ℝ))
  unfold junctionFun
  exact mul_nonneg (by norm_num) (le_min (le_min (by linarith) h2) zero_le_one)

theorem junctionFun_le (p : RecData) : junctionFun p ≤ 17 / 35 := by
  unfold junctionFun
  have := min_le_right (min (-markPosL (rdrv p) (rtime p) 0) (markPos (rdrv p) (rtime p) 0)) 1
  nlinarith

include hs in
/-- **On the good event, before the contact, the reference junction distance is that of every late version's
prefix record** (the versions agree up to the stage start, `GW2Sdo.ae_stgPreRecX_sched_eq`). -/
theorem ae_refFun_eq : ∀ᵐ ω ∂c.P, cfRec c.s c.W c.ζ ω ∈ goodX (rootPt x) c.s →
    (historyTime c (x, 0) [] : ℝ≥0∞) < contactX (rootPt x) c.s (schedTr c (x, 0) [] 0) c.α ω →
    ∀ᶠ n in atTop, refFun h13 c x hx ω = junctionFun (refPre h13 c x hx n ω) ∧
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
  have hconst : ∀ n ≥ N, junctionFun (refPre h13 c x hx n ω) = junctionFun (refPre h13 c x hx N ω) := fun n hn =>
    by rw [hpω n N hcf ⟨hTc, hN n hn⟩ ⟨hTc, hN N le_rfl⟩]
  have hlim : liminf (fun n => junctionFun (refPre h13 c x hx n ω)) atTop =
      junctionFun (refPre h13 c x hx N ω) :=
    (tendsto_const_nhds.congr' (eventually_atTop.2 ⟨N, fun n hn => (hconst n hn).symm⟩)).liminf_eq
  have hval : refFun h13 c x hx ω = junctionFun (refPre h13 c x hx N ω) := by
    unfold refFun
    rw [hlim, min_eq_left (junctionFun_le _), max_eq_right (junctionFun_nonneg _)]
  filter_upwards [eventually_ge_atTop N] with n hn
  exact ⟨hval.trans (hconst n hn).symm, hN n hn⟩

end Ref

/-! ### The gap family -/

open Classical in
/-- **The gap at a root**: a `c.sigma (x, ·) []`-measurable version of the reference junction distance at good roots
(`0 ≤ rootPt x`, `0 < s`), `1` elsewhere (Theorem 1.3, R48). -/
def gapAt (c : SourceData Ω) (x : RootIdx c.Θ c.Q) : Ω → ℝ :=
  if h : 0 ≤ rootPt x ∧ 0 < c.s then
    (exists_gapVersion Sec5.Aux61Cpt.theorem13Statement_of_cptCover.{u} c x h.1 h.2).choose
  else fun _ => 1

/-- **The scaled cover's gap family** (REVIEW-FABLE-T14 T0, D24 (3)). -/
def gapFam : RootCv.GapFamily.{u} := fun _ _ _ c x => gapAt c x

/-- **The gap is known at the root's stage start** (the field `hgap` of the scaled-cover top). -/
theorem measurable_gapFam (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) : Measurable[c.sigma r []] (gapFam Ω c r.1) := by
  classical
  change Measurable[c.sigma r []] (gapAt c r.1)
  unfold gapAt
  split_ifs with h
  · exact (exists_gapVersion Sec5.Aux61Cpt.theorem13Statement_of_cptCover.{u} c r.1 h.1 h.2).choose_spec.1
  · exact measurable_const

/-- **At good roots the gap is the reference junction distance**, almost surely. -/
theorem ae_gapFam_eq (c : SourceData Ω) (x : RootIdx c.Θ c.Q) (h : 0 ≤ rootPt x ∧ 0 < c.s) :
    refFun Sec5.Aux61Cpt.theorem13Statement_of_cptCover.{u} c x h.1 =ᵐ[c.P] gapFam Ω c x := by
  classical
  change refFun _ c x h.1 =ᵐ[c.P] gapAt c x
  unfold gapAt
  simp only [h, and_self, ↓reduceDIte]
  exact (exists_gapVersion Sec5.Aux61Cpt.theorem13Statement_of_cptCover.{u} c x h.1 h.2).choose_spec.2

end InteractingSLE.Theorem14.GW2Sdq
