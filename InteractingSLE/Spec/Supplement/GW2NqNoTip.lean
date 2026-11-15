/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2NqTip
import InteractingSLE.Spec.Supplement.GW2UcTip

/-!
# At a first contact of the current stage the relative trace has a finite limit, almost surely (D84/D87)

Packet PROVE-GW2-NEARIMG2, decisions D84 item (1) and D87. RELDET's `GW2Rd.ae_noTip_stage` (`GW2UcTip`) excludes a
first contact at the tip almost surely, from `TipUnbStatement`. That statement is false: a tip contact through a
non-tip prime end of a double point has a finite relative limit, see `GW2NqTip`. This file proves the corrected
conclusion by the same argument. Almost surely on guarded histories, at a first contact strictly after the history
time and at or before the stop, **the relative trace has a finite limit** at the contact. Suppose it has none. The
clock is either unbounded (RELDET's `tipCode_unbounded`, unchanged) or bounded, and then `cDrv` is unbounded below
the life (`exists_cDrv_gt_of_not_tendsto`, `TipUnbLimStatement`'s sample form) and `tipCode_bounded` applies. Either
way the stage code is in `TipCode`, which it avoids almost surely.

The proof is RELDET's, with `TipUnbStatement` replaced by `exists_cDrv_gt_of_not_tendsto`. It does not need the
contact to be at the tip.

* **`ae_tendsto_stage`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC)

universe u

namespace InteractingSLE.Theorem14.GW2Ni

open Exist Staged StagedLaw Restart GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31 GW2Rz GW2Rv GW2Sde
  GW2Sdh Supp8.GB6 Supp8.GB6.CoordB Sec5.Prop513Schedule GW2Rd

/-- **At a first contact of the current stage the relative trace has a finite limit**, almost surely on guarded
histories (RELDET's `ae_noTip_stage` with the conclusion corrected, D84). -/
theorem ae_tendsto_stage (h13₀ : Exist.Theorem13Statement.{0}) (hsw : FlowSwallowStatement.{0})
    (hfield : StageFieldLawXStatement.{u})
    (hcode : ∀ κ : ℝ, 0 < κ → ∃ F : BoundaryWord × LQGMetric.DistOn upperHalfPlaneOpens → Sec2.Assembly.PCode × ℝ≥0∞,
      IsCanonicalDriverCode κ 0 F)
    (ψx : GW2Bh.PsiFam.{u}) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (hg : GoodRoot c r)
    (hgd : Wire.T14Gd.Guard c r l) :
    ∀ᵐ ξ ∂c.P, cfRec c.s c.W c.ζ ξ ∈ goodX (rootPt r.1) c.s → oldSuccess c r l ξ → ∀ τ : ℝ≥0,
      contactX (rootPt r.1) c.s (schedTr c r l a) c.α ξ = τ → historyTime c r l < τ →
      (τ : ℝ≥0∞) ≤ ((historyTime c r l + GW2Psm.candStop c r l a ξ : ℝ≥0) : ℝ≥0∞) →
      ∃ ℓ : ℂ, Tendsto (fun t => relBdry (rdrv (cfRec c.s c.W c.ζ ξ)) c.s
        ((rootPt r.1 : ℂ) + schedTr c r l a ξ t) - relBdry (rdrv (cfRec c.s c.W c.ζ ξ)) c.s (rootPt r.1))
        (𝓝[<] τ) (𝓝 ℓ) := by
  obtain ⟨hx, hs⟩ := hg
  obtain ⟨Fd, hFd⟩ := hcode c.κ c.hκ
  have hTO : TimeOrdered 0 (historyProgram c r l) := Gm.timeOrdered_of_pairwise_lt hgd.1
  have hI := instInputsX_tip ψx
  have hgood := fun n => hI.goodX hTO ⟨hx, hs⟩ a n
  -- the almost sure facts, for every version
  have A1 := ae_all_iff.2 fun n => ae_isStopDrvMatch_inst (hgood n) hFd
  have A2 := ae_all_iff.2 fun n => ae_not_tipCode_stage h13₀ hsw hfield _ c r l (rootPt r.1)
    (measurable_schedW c r l a) (hI.openLines Ω c r l hTO ⟨hx, hs⟩ a n) (hgood n).measurable_β (hgood n).isSorted
    (hgood n).measurable_Hr hFd
  have A3 := ae_all_iff.2 fun n => ((Wire.T14Rp.oneVerS ψx Ω c r l a).isA hx n).1.1.2.2.2.2.2.2
  have A4 := ae_all_iff.2 fun n => (hgood n).V_eq
  have A5 := ae_exhausts_of_contact Wire.T14Asm7.h13 c r l a hx hs hTO
  have A6 := ae_all_iff.2 fun n => ae_srecX_mem_launchBadRec_iff Wire.T14Asm7.h13 c r l a
    (instX Wire.T14Asm7.h13 (Wire.T14Rp.oneVerS ψx)
      (Wire.T14Cur.chL (Wire.T14Gd.guardBase (Wire.T14Cur.baseWm GW2Bh.cwSrc))) Ω c r l a n hx) (rootPt r.1)
  have A7 := GW2Nz.ae_candLife_pos_succ Wire.T14Asm7.h13 c r l a hgd.1
  have A8 := (schedGTX_spec Wire.T14Asm7.h13 c r l a).2.2
  filter_upwards [A1, A2, A3, A4, A5, A6, A7, A8] with ξ h1 h2 h3 h4 h5 h6 h7 h8 hgx hold τ hτ hTτ hτstop
  by_contra hnl
  -- the sample
  have hξ : ξ ∈ schedGTX Wire.T14Asm7.h13 c r l a := h8.2 hgx
  have hGT := (schedGTX_spec Wire.T14Asm7.h13 c r l a).1
  obtain ⟨⟨hwc, hw0, hγ⟩, ⟨hα, hW, hW0, hζ⟩, harc, -, -⟩ := hGT ξ hξ
  have hlife := h7 hold
  have hTc : ((historyTime c r l : ℝ≥0) : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ξ := by
    rw [hτ]
    exact_mod_cast hTτ
  -- the versions at the sample
  have hRξ : ∀ n, VersionAtX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α
      ((Wire.T14Rp.oneVerS ψx Ω c r l a).R n) ((Wire.T14Rp.oneVerS ψx Ω c r l a).V n) ξ := fun n =>
    ⟨((Wire.T14Rp.oneVerS ψx Ω c r l a).isA hx n).1.1.2.1 ξ, ((Wire.T14Rp.oneVerS ψx Ω c r l a).isA hx n).1.1.2.2.1 ξ,
      (h3 n hgx).2.2⟩
  have hVcl : ∀ n (u : ℝ≥0), (u : ℝ≥0∞) < (Wire.T14Rp.oneVerS ψx Ω c r l a).V n ξ → ∃ t : ℝ≥0, t < τ ∧
      (u : ℝ) < clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ξ := fun n u hu => by
    obtain ⟨t, ht, hut⟩ := (h3 n hgx).2.1 u hu
    refine ⟨t, ?_, hut⟩
    rw [hτ] at ht
    exact_mod_cast ht
  -- the re-indexed family exhausts the clock before the contact
  have hexh : ∀ t : ℝ≥0, t < τ → ∀ᶠ n in atTop,
      ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ξ) <
        (Wire.T14Rp.oneVerS ψx Ω c r l a).V n ξ := fun t ht => by
    have htc : (t : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ξ := by
      rw [hτ]
      exact_mod_cast ht
    obtain ⟨N, hN⟩ := (h5 hgx hold (hτ ▸ hτstop) t htc).exists_forall_of_atTop
    exact eventually_atTop.2 ⟨N, fun m hm => hN _ (hm.trans (Nat.le_add_left _ _))⟩
  -- the versions alive at the stage start: record events, matches, `TipCode` avoided
  have hP : physClockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX Wire.T14Asm7.h13 c r l a)
      (historyTime c r l) ξ = ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (historyTime c r l) ξ) :=
    physClockX_eq_clockX hGT hs hx hξ hTc
  have hrec : ∀ n, stgStartMX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX Wire.T14Asm7.h13 c r l a)
      ((Wire.T14Rp.oneVerS ψx Ω c r l a).V n) (historyTime c r l) ξ < (Wire.T14Rp.oneVerS ψx Ω c r l a).V n ξ →
      (instX Wire.T14Asm7.h13 (Wire.T14Rp.oneVerS ψx)
        (Wire.T14Cur.chL (Wire.T14Gd.guardBase (Wire.T14Cur.baseWm GW2Bh.cwSrc))) Ω c r l a n hx).srecX c r l
          (rootPt r.1) ξ ∈ (instX Wire.T14Asm7.h13 (Wire.T14Rp.oneVerS ψx)
        (Wire.T14Cur.chL (Wire.T14Gd.guardBase (Wire.T14Cur.baseWm GW2Bh.cwSrc))) Ω c r l a n hx).E := fun n hn => by
    refine srecX_mem_E ψx c r l a n hx hgd hgx hold (fun hm => hlife.ne' ((h6 n hold).1 hm)) (h4 n) ?_
    have hne := ne_top_of_lt hn
    show ((stgStartMX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX Wire.T14Asm7.h13 c r l a)
      ((Wire.T14Rp.oneVerS ψx Ω c r l a).V n) (historyTime c r l) ξ).toNNReal : ℝ≥0∞) < _
    rw [ENNReal.coe_toNNReal hne]
    exact hn
  -- a version alive at the stage start
  have halive : ∀ᶠ n in atTop, stgStartMX (rootPt r.1) c.s c.W c.ζ (schedW c r l a)
      (schedGTX Wire.T14Asm7.h13 c r l a) ((Wire.T14Rp.oneVerS ψx Ω c r l a).V n) (historyTime c r l) ξ <
        (Wire.T14Rp.oneVerS ψx Ω c r l a).V n ξ := by
    filter_upwards [hexh (historyTime c r l) hTτ] with n hn
    have hPV : physClockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX Wire.T14Asm7.h13 c r l a)
        (historyTime c r l) ξ < (Wire.T14Rp.oneVerS ψx Ω c r l a).V n ξ := by rw [hP]; exact hn
    exact (min_le_left _ _).trans_lt hPV
  obtain ⟨n₀, hn₀⟩ := halive.exists
  -- STAGEMEAN's far premises at `n₀` (the guarded choice is the unguarded one)
  have hy := hrec n₀ hn₀
  have hch := chL_guard (Ω := Ω) (c := c) (r := r) (l := l) GW2Bh.cwSrc a hgd
  have hy' : (schedInstSX c r l a (schedGTX Wire.T14Asm7.h13 c r l a)
      ((Wire.T14Rp.oneVerS ψx Ω c r l a).isA hx n₀)
      (Wire.T14Cur.chL (Wire.T14Cur.baseWm GW2Bh.cwSrc) Ω c r l a)).srecX c r l (rootPt r.1) ξ ∈
      (schedInstSX c r l a (schedGTX Wire.T14Asm7.h13 c r l a) ((Wire.T14Rp.oneVerS ψx Ω c r l a).isA hx n₀)
        (Wire.T14Cur.chL (Wire.T14Cur.baseWm GW2Bh.cwSrc) Ω c r l a)).E := by
    rw [← hch]
    exact hy
  obtain ⟨hJ, -, hfar⟩ := GW2Pq.flowSwallow_premises_schedInstSX GW2Bh.cwSrc c r l a _ _ hy'
  have hβeq : (Wire.T14Cur.chL (Wire.T14Gd.guardBase (Wire.T14Cur.baseWm GW2Bh.cwSrc)) Ω c r l a).β =
      (Wire.T14Cur.chL (Wire.T14Cur.baseWm GW2Bh.cwSrc) Ω c r l a).β := by rw [hch]
  have hθ := GW2Pq.candAngle_mem_Ioo c r l a
  have hneg : markPosL (rdrv (cfRec c.s c.W c.ζ ξ)) (rtime (cfRec c.s c.W c.ζ ξ)) 0 < 0 := hgx.1.2.2.2
  have hfar' : GW2Ni.FarRAt ((Wire.T14Cur.chL (Wire.T14Gd.guardBase (Wire.T14Cur.baseWm GW2Bh.cwSrc)) Ω c r l a).β
      ((instX Wire.T14Asm7.h13 (Wire.T14Rp.oneVerS ψx)
        (Wire.T14Cur.chL (Wire.T14Gd.guardBase (Wire.T14Cur.baseWm GW2Bh.cwSrc))) Ω c r l a n₀ hx).srecX c r l
          (rootPt r.1) ξ))
      (sleLambda (16 / c.κ) - Real.pi * chiC c.κ + candAngle c r l a * chiC c.κ)
      (GW2Ni.farJunctionX (rootPt r.1) c.s (historyProgram c r l) ((entryList l).length + 1)
        (length_historyProgram c r l) ((instX Wire.T14Asm7.h13 (Wire.T14Rp.oneVerS ψx)
          (Wire.T14Cur.chL (Wire.T14Gd.guardBase (Wire.T14Cur.baseWm GW2Bh.cwSrc))) Ω c r l a n₀ hx).srecX c r l
            (rootPt r.1) ξ)) := by
    rw [hβeq]
    exact hfar
  have hnt := h2 n₀ hy
  -- both shapes of the clock give `TipCode`
  by_cases hunb : ∀ y : ℝ, ∃ v : ℝ≥0, v < τ ∧ y < clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) v ξ
  · refine hnt (tipCode_unbounded c r l a hGT hs hx (fun n => ((Wire.T14Rp.oneVerS ψx Ω c r l a).isA hx n).1.1)
      (fun n => (Wire.T14Rp.oneVerS ψx Ω c r l a).fin n) hTO hξ hRξ hold hτ hTτ hunb hneg _ _ _ n₀ hn₀
      (fun U => ?_) (fun n hn => h1 n (hrec n hn)) hθ hJ hfar')
    obtain ⟨v, hvτ, hv⟩ := hunb ((U : ℝ) + clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (historyTime c r l) ξ)
    obtain ⟨n, hn1, hn2⟩ := ((hexh v hvτ).and halive).exists
    refine ⟨n, ?_, hn2⟩
    have hcT0 : 0 ≤ clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (historyTime c r l) ξ :=
      RootJ32.forwardCapacity_nonneg _ _ _ _
    have hPV : physClockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX Wire.T14Asm7.h13 c r l a)
        (historyTime c r l) ξ ≤ (Wire.T14Rp.oneVerS ψx Ω c r l a).V n ξ := by
      by_contra h
      rw [not_le] at h
      have e : stgStartMX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX Wire.T14Asm7.h13 c r l a)
          ((Wire.T14Rp.oneVerS ψx Ω c r l a).V n) (historyTime c r l) ξ =
          (Wire.T14Rp.oneVerS ψx Ω c r l a).V n ξ := min_eq_right h.le
      rw [e] at hn2
      exact lt_irrefl _ hn2
    have hM : stgStartMX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX Wire.T14Asm7.h13 c r l a)
        ((Wire.T14Rp.oneVerS ψx Ω c r l a).V n) (historyTime c r l) ξ =
        ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (historyTime c r l) ξ) := by
      rw [← hP]
      exact min_eq_left hPV
    show (U : ℝ≥0∞) < (Wire.T14Rp.oneVerS ψx Ω c r l a).V n ξ -
      ((stgStartMX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX Wire.T14Asm7.h13 c r l a)
        ((Wire.T14Rp.oneVerS ψx Ω c r l a).V n) (historyTime c r l) ξ).toNNReal : ℝ≥0∞)
    rw [hM, ENNReal.coe_toNNReal ENNReal.ofReal_ne_top, lt_tsub_iff_left, ← ENNReal.ofReal_coe_nnreal,
      ← ENNReal.ofReal_add hcT0 U.coe_nonneg]
    refine lt_of_le_of_lt (ENNReal.ofReal_le_ofReal ?_) hn1
    linarith
  · simp only [not_forall, not_exists, not_and, not_lt] at hunb
    obtain ⟨M, hM⟩ := hunb
    have htip' := exists_cDrv_gt_of_not_tendsto c.W c.ζ ξ hα hW hW0 hζ hs hx harc hwc hw0 hγ hτ hM hnl
    refine hnt (tipCode_bounded c r l a hGT hs hx hξ hRξ hτ hTτ hM htip' (fun u hu => ?_) hVcl _ _ _ n₀ hn₀
      (fun n hn => h1 n (hrec n hn)))
    obtain ⟨v, hvτ, hv⟩ := hu
    obtain ⟨n, hn1, hn2⟩ := ((hexh v hvτ).and halive).exists
    refine ⟨n, hn2, lt_of_le_of_lt ?_ hn1⟩
    rw [← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal hv.le

end InteractingSLE.Theorem14.GW2Ni
