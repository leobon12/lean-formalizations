/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2BxFacts
import InteractingSLE.Spec.Supplement.GW2UcLaw

/-!
# nearImg's almost-sure facts from the guarded stopped stage law (decisions D84, D87)

Packet PROVE-GW2-BUF (round 22). Round 21's `ae_bundleS` (same proof) with RELDET's PROVED stopped stage law in the
guarded form of D84/D87, `GW2Rd.StageLawXSGTStatement` (the extra premises `Wire.T14Gd.Guard c r l` and, at the
sample, the history time before the candidate's contact), at a guarded history. The agreement of the versions is
asked where the history time is before the contact (it is, on the alive event).

* **`ae_bundleSG`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Bh

open Restart Exist Exist.StagedLaw GW2TipSystem GW2TipSystem.RootC24 GW2Rz GW2Rd GW2Rv GW2Sde GW2Sdh GW2Sdx

variable (h13 : Exist.Theorem13Statement.{u}) (ver₀ : SchedVerXFamily.{u}) (ch : SchedChoiceFamily.{u})

/-- **nearImg's almost-sure facts** on a base family, from the guarded stopped stage law. -/
theorem ae_bundleSG
    (hlaw : GW2Rd.StageLawXSGTStatement h13 ver₀)
    (hcov : Wire.T14Rk.VerCovers ver₀)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (hx : 0 ≤ rootPt r.1) (hs : 0 < c.s) (hTO : GW2Sdx.HistOrdered c r l)
    (hgd : Wire.T14Gd.Guard c r l) :
    ∀ᵐ ξ ∂c.P,
      (ξ ∈ ((GW2Sdz.J32S GW2Sdq.gapFam Ω c).experiment r).data.alive ((GW2Sdz.J32S GW2Sdq.gapFam Ω c).G r) l →
        (cfRec c.s c.W c.ζ ξ ∈ goodX (rootPt r.1) c.s ∧
          ∀ a, ((RootJ31.historyTime c r l : ℝ≥0) : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ξ) ∧
        (∀ a j : ℕ, ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (RootJ31.historyTime c r l) ξ) <
            (ver₀ Ω c r l a).V j ξ →
          stgPreRecX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a) ((ver₀ Ω c r l a).V j)
            (RootJ31.historyTime c r l) ((ver₀ Ω c r l a).R j) ξ = GW2Rl.refPreV h13 ver₀ Ω c r l ξ) ∧
        (GW2Bf.histStart c r l ξ < 2 + 1 / 8 ∧
          (lamL l : ℝ) * (2 + 1 / 8 - GW2Bf.histStart c r l ξ) ≤ 2 + 1 / 8) ∧
        RootJ31.oldSuccess c r l ξ ∧ (∀ a, ξ ∈ schedGTX h13 c r l a) ∧
        GW2Rl.refPreV h13 (verS h13 ver₀ ch) Ω c r l ξ = GW2Rl.refPreV h13 ver₀ Ω c r l ξ) ∧
      (∀ a m : ℕ, ∀ (lam : ℝ) (τ : ℝ≥0∞) (t : ℝ≥0), 0 < lam →
        GW2Bf.histStart c r l ξ < 2 + 1 / 8 → lam * (2 + 1 / 8 - GW2Bf.histStart c r l ξ) ≤ 2 + 1 / 8 →
        τ ≤ (GW2Sdg.rootGain c r l a ξ : ℝ≥0∞) →
        τ ≤ (verS h13 ver₀ ch Ω c r l a).V m ξ - (GW2Sdg.rootHistCap c r l a ξ : ℝ≥0∞) →
        (t : ℝ≥0∞) < (4 : ℝ≥0∞) ^ r.2 * τ →
        2 + 1 / 8 < lam * ((-1 : ℝ) ^ l.length * ((2 : ℝ) ^ r.2 *
          (instX h13 (verS h13 ver₀ ch) ch Ω c r l a m hx).drvX c (rootPt r.1) (t / (4 : ℝ≥0) ^ r.2) ξ)) →
        RootJ32.sourceSample c r l a ξ ∈ RootD25.reachSet) ∧
      (∀ a : ℕ, 0 < (RootJ31.sourceSample c r l a ξ).1 →
        physClockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a) (RootJ31.historyTime c r l) ξ =
          ((GW2Sdg.rootHistCap c r l a ξ : ℝ≥0) : ℝ≥0∞)) ∧
      (∀ a : ℕ, ξ ∈ schedGTX h13 c r l a → RootJ31.oldSuccess c r l ξ →
        ((RootJ31.historyTime c r l : ℝ≥0) : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ξ →
        ∀ (j j' : ℕ) (q : ℝ≥0), j ≤ j' → (q : ℝ≥0∞) < (ver₀ Ω c r l a).V j ξ →
          (ver₀ Ω c r l a).R j' q ξ = (ver₀ Ω c r l a).R j q ξ) := by
  have hGTE : ∀ᵐ ξ ∂c.P, ∀ a, ξ ∈ schedGTX h13 c r l a ↔ cfRec c.s c.W c.ζ ξ ∈ goodX (rootPt r.1) c.s :=
    ae_all_iff.2 fun a => (schedGTX_spec h13 c r l a).2.2
  have hcovS := GW2Rl.verCovers_verU hcov (psiGoodS h13 ver₀ ch)
  have hagE : ∀ᵐ ξ ∂c.P, ∀ a : ℕ, ξ ∈ schedGTX h13 c r l a → RootJ31.oldSuccess c r l ξ →
      ((RootJ31.historyTime c r l : ℝ≥0) : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ξ →
      ∀ (j j' : ℕ) (q : ℝ≥0), j ≤ j' → (q : ℝ≥0∞) < (ver₀ Ω c r l a).V j ξ →
        (ver₀ Ω c r l a).R j' q ξ = (ver₀ Ω c r l a).R j q ξ := by
    refine ae_all_iff.2 fun a => (hlaw Ω c r l a ⟨hx, hs⟩ hTO hgd).mono fun ξ h hGT hold hTc j j' q hjj hq => ?_
    obtain ⟨Wc, -, -, hagr, -, -⟩ := h hGT hold hTc
    have hmono : (ver₀ Ω c r l a).V j ξ ≤ (ver₀ Ω c r l a).V j' ξ :=
      (monotone_nat_of_le_succ fun k => (ver₀ Ω c r l a).mono k ξ) hjj
    rw [hagr j' q (hq.trans_le hmono), hagr j q hq]
  filter_upwards [GW2Ru.ae_alive_goodEvent_scaled h13 GW2Sdq.gapFam c r,
    ae_slotRec_eq_refV h13 c r l ver₀ GW2Sdq.gapFam ⟨hx, hs⟩, ae_startBand h13 GW2Sdq.gapFam c r l, hGTE,
    hcovS Ω c r l 0 ⟨hx, hs⟩, ae_refPreV_verU_eq h13 ver₀ c r l (psiGoodS h13 ver₀ ch) GW2Sdq.gapFam ⟨hx, hs⟩,
    ae_all_iff.2 fun a => ae_all_iff.2 fun m =>
      ae_reach_of_visit_instX h13 c r l a hx hTO ((verS h13 ver₀ ch Ω c r l a).isA hx m) (ch Ω c r l a),
    ae_all_iff.2 fun a => ae_physClockX_eq_histCap h13 c r l a hx, hagE]
    with ξ h1 h2 h3 hGT hcov0 hrefE hreach hphys hag
  refine ⟨fun halive => ?_, hreach, hphys, hag⟩
  have halive32 := GW2Sdz.alive_scaled_subset GW2Sdq.gapFam Ω c r l halive
  obtain ⟨hcf, hcon⟩ := h1 l halive
  obtain ⟨n₀, hn₀⟩ := (hcov0 halive32 hcf (hcon 0)).exists
  have hex : ∃ p : ℕ, ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l (Nat.unpair p).1)
      (RootJ31.historyTime c r l) ξ) < (GW2Rl.verU ver₀ (psiGoodS h13 ver₀ ch) Ω c r l (Nat.unpair p).1).V
        (Nat.unpair p).2 ξ := by
    refine ⟨Nat.pair 0 n₀, ?_⟩
    rw [Nat.unpair_pair]
    exact hn₀
  exact ⟨⟨hcf, hcon⟩, h2 halive, h3 halive, RootJ32.oldSuccess_of_alive c r l ξ halive32,
    fun a => (hGT a).2 hcf, hrefE halive hex⟩

end InteractingSLE.Theorem14.GW2Bh
