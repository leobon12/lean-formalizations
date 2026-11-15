/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2VeAsm
import InteractingSLE.Spec.Supplement.SBS3DwBase
import InteractingSLE.Spec.Supplement.SBS3DwVeIn
import InteractingSLE.Spec.Supplement.SB2VeIn
import InteractingSLE.Spec.Supplement.SBS3DwDrvLineIfaceR
import InteractingSLE.Spec.Supplement.SBS3DwTcRec
import InteractingSLE.Spec.Supplement.SBS3DwVcAe
import InteractingSLE.Spec.Supplement.SBS3DwVdAe
import InteractingSLE.Spec.Supplement.SBS3DwVdDrvAe
import InteractingSLE.Spec.Supplement.SBS3DwVhLife

/-!
# Successor of `SB2VeAsm` with the upper angle `ψ ≤ π/2` (decision D22, ruling R121)

Worker PROVE-R6-CORNER (round 8). The declarations of `SB2VeAsm` that use Lemma S3 in SB2(1)'s form,
restated so that Lemma S3 enters as `Tc.SB2EntranceNoCommonArcLeStatement` (upper angle `ψ ≤ π/2`, PROVED
from Theorems 1.2–1.3 as `Tc.sb2EntranceNoCommonArcLeStatement_of_thm`). Every launch problem carries the bound
as an instance argument `[Fact (ψ ≤ Real.pi / 2)]`; the proofs are those of the original file. Names: the
original names with the suffix `Le` (statements: `…LeStatement`).

* `sb2LineVersionRStatement_of_inputsLe`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Ve

open Lv Restart Restart.DomainMarkov Restart.DomainMarkov.K2 Exist Exist.Staged Exist.StagedLaw Supp8.Q3Stop
  Sec7.PocketTraversal

/-! ### Deterministic helpers -/

/-! ### The assembly -/

/-- **`SB2LineVersionRLeStatement` from Theorem 1.3, Lemma S3 (SB2(1)'s form), E7 and the measurable version.** -/
theorem sb2LineVersionRStatement_of_inputsLe (h13 : Exist.Theorem13Statement.{u})
    (hS3 : Tc.SB2EntranceNoCommonArcLeStatement.{u}) (hE7 : Vh.SB2RemainderLifeLeStatement.{u})
    (hMV : SB2MeasVersionLeStatement.{u}) : SB2LineVersionRLeStatement.{u} := by
  intro κ b jumps Ω _ _ P _ h E k u ψ η ζ HP _ I u₀ _hu₀ D
  obtain ⟨W, Γ, Vg, ηr, a, ha, hW0, hWc, hac, ham, ha0, hWad, hsS, hsL, hae⟩ :=
    hMV κ b jumps P h E k u ψ η ζ HP I u₀ D
  have hlink : ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) →
      firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω)) < ζ ω →
      IsGeneratingTrace (fun t => W t ω) (Vg ω) (Γ ω) ∧
        IsRemainderLink (Lv.launchChart κ b jumps E (k + 1) ω) (η ω) (ζ ω)
          (realMin (lowerPrefix κ b jumps E (k + 1) u ω))
          (fun t => Γ ω t + launchEntry κ b jumps E (k + 1) u ω) (Vg ω) := by
    filter_upwards [hae] with ω hω hF hT
    exact ⟨(hω hF hT).1, (hω hF hT).2.1⟩
  have hlife := Vh.life_of_remainderLifeLe hE7 HP I D hW0 hWc hlink
  -- on a seed cell: the launch, the entrance, the clock, and `Vg = thr`
  have hcell : ∀ w ∈ I.types, ∀ᵐ ω ∂P, ω ∈ seedCell κ ψ I.word D.event w →
      ω ∈ launchSet κ b jumps E (k + 1) ∧ entT κ b jumps E k u η ζ ω < ζ ω ∧
      (∀ t, a t ω = Vc.clockOf (flowLift κ b jumps E k u η ζ ω) (entT κ b jumps E k u η ζ ω).toNNReal (ζ ω) t) ∧
      FCDet.thr (typedRhoL w) (typedRhoR w) W (cellXL κ ψ I.word w) (cellXR κ ψ I.word w) ω =
        ⨆ (s : ℝ≥0) (_ : (((entT κ b jumps E k u η ζ ω).toNNReal + s : ℝ≥0) : ℝ≥0∞) < ζ ω),
          ENNReal.ofReal (Sec7.Lemma71C.capClock (fun r : ℝ => flowLift κ b jumps E k u η ζ ω r.toNNReal) s) := by
    intro w hw
    filter_upwards [hlife w hw, hae, D.ae_mem_event_iff] with ω hlω hω hev hc
    have hevω : ω ∈ D.event := hc.1.1
    have hl : ω ∈ launchSet κ b jumps E (k + 1) := D.event_subset hevω
    have hT := (hev hl).1 hevω
    obtain ⟨-, -, hclock, hVg, -, -⟩ := hω hl hT
    exact ⟨hl, hT, hclock, (hlω hl hT hc.1).symm.trans hVg⟩
  refine ⟨{
    𝓗 := Tc.tcFilt (D.lineFiltC HP) a ha, W := W, Γ := Γ, Vg := Vg, a := a,
    marks_le := Tc.le_tcFilt_zero (D.marks_le_lineFiltC HP), W_zero := hW0, W_cont := hWc, W_adapted := hWad,
    link := hlink, life := hlife, clock_cont := hac, clock_mono := ham, clock_zero := ha0, clock_meas := ha,
    timeChange := fun q D' hD' t => Tc.tcFilt_inter q D' hD' t,
    reach := ?_, reg := ?_, safeS := hsS, safeL := hsL, chain := ?_, alive := ?_ }⟩
  · -- reach: the clock reaches every level below the relative lifetime `= thr`
    intro w hw q
    filter_upwards [hcell w hw] with ω hω hc hq
    obtain ⟨-, -, hclock, hthr⟩ := hω hc
    rw [hthr] at hq
    obtain ⟨s, hs⟩ := lt_iSup_iff.1 hq
    obtain ⟨hsζ, hs'⟩ := lt_iSup_iff.1 hs
    refine ⟨(entT κ b jumps E k u η ζ ω).toNNReal + s, ?_⟩
    rw [hclock]
    unfold Vc.clockOf
    exact le_iSup₂_of_le s le_rfl (le_iSup_of_le hsζ hs'.le)
  · -- reg
    intro w _
    exact Filter.Eventually.of_forall fun ω _ => Vh.reg_of_continuous hW0 hWc _ _ _ _ ω
  · -- chain: the per-time record
    intro w hw t
    filter_upwards [hcell w hw, hae, Vc.ae_lineGeom_liftOfLe h13 hS3 HP, ae_flowDriver HP]
      with ω hω hae' hrec hfd hc hlt
    obtain ⟨hl, hT, hclock, hthr⟩ := hω hc
    obtain ⟨-, -, -, -, hLT, hηr⟩ := hae' hl hT
    have htζ : (t : ℝ≥0∞) < ζ ω := by
      by_contra hζt
      rw [not_lt] at hζt
      rw [hclock, Vd.clockOf_eq_sup_of_le hζt, ← hthr] at hlt
      exact lt_irrefl _ hlt
    set TL := entT κ b jumps E k u η ζ ω with hTLdef
    have hTLtop : TL ≠ ⊤ := ne_top_of_lt hT
    have hTLc : ((TL.toNNReal : ℝ≥0) : ℝ≥0∞) = TL := ENNReal.coe_toNNReal hTLtop
    have hTLr : TL.toReal = (TL.toNNReal : ℝ) := rfl
    obtain ⟨T, hmT, hTζ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 (max_lt htζ hT)
    have htT : (t : ℝ) < T := NNReal.coe_lt_coe.2 (ENNReal.coe_lt_coe.1 ((le_max_left _ _).trans_lt hmT))
    have hTLT' : TL < T := (le_max_right _ _).trans_lt hmT
    have hLT' : (TL.toNNReal : ℝ) < T := by
      have h1 := hTLT'
      rw [← hTLc] at h1
      exact NNReal.coe_lt_coe.2 (ENNReal.coe_lt_coe.1 h1)
    set m : ℝ := max (t : ℝ) (TL.toNNReal : ℝ) with hm
    have hmT' : m < T := max_lt htT hLT'
    set S₁ : ℝ := (m - TL.toNNReal + ((T : ℝ) - TL.toNNReal)) / 2 with hS₁
    have hS₁pos : 0 < S₁ := by rw [hS₁]; linarith [le_max_right (t : ℝ) (TL.toNNReal : ℝ)]
    have hS₁T : TL.toReal + S₁ < T := by rw [hTLr, hS₁]; linarith
    have htS : (t : ℝ) < (TL.toNNReal : ℝ) + S₁ := by
      rw [hS₁]; linarith [le_max_left (t : ℝ) (TL.toNNReal : ℝ)]
    obtain ⟨p, g, β', γ, tL, Wr₀, ηr₀, hp, hch, hw', hag, ⟨hchain, hnoR⟩, hγeq⟩ :=
      hrec hl T hTζ.le hTLT' S₁ hS₁pos hS₁T
    have htt : tL = TL.toNNReal := by
      rw [← ENNReal.coe_inj, hTLc]; exact hw'.2.2.2.2.1
    subst htt
    have hfl : ∀ s : ℝ≥0, (s : ℝ) < S₁ → γ s = flowLift κ b jumps E k u η ζ ω s := hγeq
    have hcapEq : ∀ x : ℝ, 0 ≤ x → x < S₁ → Sec7.Lemma71C.capClock (fun r : ℝ => γ r.toNNReal) x =
        Sec7.Lemma71C.capClock (fun r : ℝ => flowLift κ b jumps E k u η ζ ω r.toNNReal) x := fun x hx hxS =>
      Vc.capClock_congr fun r hr => hfl r (by
        have h1 := NNReal.coe_le_coe.2 hr
        rw [Real.coe_toNNReal _ hx] at h1
        linarith)
    have hTS : (TL.toNNReal : ℝ) + S₁ ≤ T := by rw [hTLr] at hS₁T; linarith
    obtain ⟨wf, hwfc, hwf0, hwfg⟩ := hfd
    obtain ⟨wP, ηw, hwPc, hwP0, hwPL, hηw⟩ := exists_physDriver hwfg hwfc hwf0 hTζ
    have h0 : Sec7.Lemma71C.capClock (fun r : ℝ => flowLift κ b jumps E k u η ζ ω r.toNNReal) 0 = 0 := by
      rw [← hcapEq 0 le_rfl hS₁pos]; exact (hchain 0 le_rfl hS₁pos).2.2.2.1
    refine ⟨p, g, β', γ, TL.toNNReal, S₁, fun r => W r.toNNReal ω, ηr ω, wP, ηw, htS, hp, hch, hw', hag,
      ⟨hS₁pos, fun S₀ hS₀ hS₀S => chain_with_driver (hchain S₀ hS₀ hS₀S)
        ((hWc ω).comp continuous_real_toNNReal) (by simp [hW0]) hLT fun s hs => ?_, hnoR⟩,
      physClause hwPc hwP0 hwPL hTS hηw hag, fun q _ => by simp, fun t' ht' => ?_, fun t' ht1 ht2 => ?_⟩
    · -- the global trace reads the lift in the capacity clock
      have hs1 : s < S₁ := hs.2.trans_lt hS₀S
      have hsζ : ((TL.toNNReal + s.toNNReal : ℝ≥0) : ℝ≥0∞) < ζ ω := by
        refine lt_of_lt_of_le (ENNReal.coe_lt_coe.2 (NNReal.coe_lt_coe.1 ?_)) hTζ.le
        rw [NNReal.coe_add, Real.coe_toNNReal _ hs.1]
        linarith
      have h1 := hηr s.toNNReal hsζ
      rw [Real.coe_toNNReal _ hs.1] at h1
      rw [hcapEq s hs.1 hs1, hfl s.toNNReal (by rw [Real.coe_toNNReal _ hs.1]; exact hs1)]
      exact h1
    · -- the clock vanishes up to the entrance
      show a t' ω = 0
      rw [hclock]
      exact Vc.clockOf_eq_zero_of_le (NNReal.coe_le_coe.1 ht') h0
    · -- the clock is the capacity clock of the lift after the entrance
      have hx0 : 0 ≤ (t' : ℝ) - TL.toNNReal := by linarith
      have hxS : (t' : ℝ) - TL.toNNReal < S₁ := by linarith
      have ht'ζ : (t' : ℝ≥0∞) < ζ ω := by
        refine lt_of_lt_of_le (ENNReal.coe_lt_coe.2 (NNReal.coe_lt_coe.1 ?_)) hTζ.le
        linarith
      have hmono : MonotoneOn (Sec7.Lemma71C.capClock fun r : ℝ => flowLift κ b jumps E k u η ζ ω r.toNNReal)
          (Icc 0 ((t' : ℝ) - TL.toNNReal)) :=
        ((hchain _ hx0 hxS).2.2.2.2.1.monotoneOn).congr fun y hy => hcapEq y hy.1 (hy.2.trans_lt hxS)
      show a t' ω = _
      rw [hclock, Vc.clockOf_eq (NNReal.coe_le_coe.1 ht1) ht'ζ hmono, ← hcapEq _ hx0 hxS]
      rfl
  · -- alive: from the lifetime on, the clock is the relative lifetime `= thr`
    intro w hw t
    filter_upwards [hcell w hw] with ω hω hc hlt
    obtain ⟨-, -, hclock, hthr⟩ := hω hc
    by_contra hζt
    rw [not_lt] at hζt
    rw [hclock, Vd.clockOf_eq_sup_of_le hζt, ← hthr] at hlt
    exact lt_irrefl _ hlt

end InteractingSLE.Theorem14.SB.Ve
