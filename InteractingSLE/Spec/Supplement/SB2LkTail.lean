/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2LkFree

/-!
# SB2(2) at the later launches: reduction to the erasure identity

Packet PROVE-T14-SB2LIFT. PROVE-T14-SB2LOW's named input `Lh.SB2LowerLaunchLiftSuccStatement` (SB2(2)'s combined
target, ruling R104a, at the launches `k ≥ 1`) asks for an output `(m, EL)` of SB2(2) whose completed lower tail lifts.
This file separates the law clauses, which hold for ANY regular staged lower walk of the conditional field, from the
erasure identity, which ties such a walk to the actual lower walk:

* `TailIdent`, **`SB2LowerTailIdentStatement`** (named input, the erasure identity of SB2(2), supplement p. 631: "Erase
  `B` through its unique visit to `R` and lift the remaining tail into `D_A`. The result is again a finite simple
  proper lower walk of the retained conditional field"): at the later launches, for every regular staged history `EL`
  of the conditional field on the relative lower program, almost surely under the retained kernel, `EL`'s physical set
  is the actual lower walk outside the filled upper prefix (the set link of R99) and every proper parametrization of
  the actual lower walk has its tail after `R` lifted onto `EL`'s walk (`Lf.IsTailLiftOf`, R104a);
* **`exists_relLowerWalk`**: the conditional field has a regular staged lower walk adding only right records
  (Theorems 1.2–1.3 under the retained kernel, `exists_isStagedHistory_regular_all_of_thm12_thm13`, regularized; the
  right records from the word half's admissibility left of `0`);
* **`sb2LowerLaunchLiftSuccStatement_of_tailIdent`**: the combined target at the later launches from Theorems 1.2–1.3
  and the erasure identity: `m = −e_R`; the word clauses (PROVE-T14-SB2LOW's word half), the entry value, the
  canonical relative walk, the free point left of `A ∪ {0}` (`LowerWalkLeftFreeStatement`, proved in `SB2LkFree`);
* **`sb2LowerLaunchLiftStatement_of_tailIdent`**: SB2(2)'s combined target (R104a) at every launch, and
  `sb2LowerLaunchEntryAdmStatement_of_tailIdent`: R99's form.

R48: Theorems 1.2–1.3 appear only as hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lk

open Supp9B Lx Lu Leaf FlowDilate Sec4 Exist Exist.Staged Exist.StagedLaw

/-! ### The erasure identity -/

/-- **SB2(2)'s erasure identity at one launch**: for `m = −e_R` and every regular staged lower walk `EL` of the
conditional field (frame `affField m h'`, data `affData 1 m b'`), almost surely under the retained kernel, `EL`'s
physical set through the recentred launch chart is the actual lower walk outside the filled upper prefix, and the tail
after `R = max (A ∩ ℝ)` of every proper parametrization of the actual lower walk from `0` lifts onto `EL`'s walk. -/
def TailIdent (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (u : ℝ)
    (l : List (ℝ × ℝ≥0)) (k : ℕ) (ω₀ : Ω) (c : Chart) (b' : ℝ → ℝ) (J' : Finset ℝ)
    (h' : Ω → DistOn upperHalfPlaneOpens) : Prop :=
  ∀ m : ℝ, m = -upperEntry κ b jumps E u l k ω₀ → ∀ EL : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
    IsStagedHistory κ (affData 1 m b') (affJumps 1 m J')
      (condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀)
      (fun ω => affField m one_pos (h' ω)) (relLowerSpec b' J' m) EL →
    StagedPiecesRegular κ (affData 1 m b') (affJumps 1 m J')
      (condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀)
      (relLowerSpec b' J' m) EL →
    ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
      (lowerWalkSet κ b jumps E ω ∩ (H \ fillH (upperPrefix κ b jumps E u l k ω)) ⊆
          relPhysSet κ (affData 1 m b') (affJumps 1 m J') (c.recenter (-m))
            (relLowerSpec b' J' m) (fun j => EL j ω) ∧
        relPhysSet κ (affData 1 m b') (affJumps 1 m J') (c.recenter (-m))
            (relLowerSpec b' J' m) (fun j => EL j ω) ⊆ lowerWalkSet κ b jumps E ω) ∧
      ∀ β₀ : ℝ≥0 → ℂ, IsProperCurve β₀ → β₀ 0 = 0 → range β₀ = lowerWalkSet κ b jumps E ω →
        Lf.IsTailLiftOf c (realMax (upperPrefix κ b jumps E u l k ω₀)) m β₀
          (relWalkSet κ (affData 1 m b') (affJumps 1 m J') EL ω)

/-- **Named input: SB2(2)'s erasure identity at the later launches** (supplement p. 631 and the proof pp. 631–633:
the geometry of the erasure (S2 reflected), the initial and optional Gaussian kernels of the marked union, BW3a/BW3 for
the restarted stages and integrated uniqueness identify the actual relative ordinary flows). In SB2(2)'s setting, at
almost every launch `k ≥ 1` and for every witness of the conditional launch law: `TailIdent`. -/
def SB2LowerTailIdentStatement : Prop :=
  Lf.SB2LowerSetting.{u} fun κ b jumps _ _ _ P _ E u l k ω₀ c b' J' h' =>
    0 < k → TailIdent κ b jumps P E u l k ω₀ c b' J' h'

/-! ### The relative lower walk of the conditional field -/

/-- **The conditional field has a regular staged lower walk adding only right records** (Theorems 1.2–1.3 under any
probability measure; the regularized family has regular drivers at every sample; the right records come from the
admissibility of the data left of `0`). -/
theorem exists_relLowerWalk (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u}) {κ : ℝ}
    (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData Q h b jumps)
    (hadm : Ly.LowerLeftAdmissible κ b jumps) :
    ∃ EL : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      IsStagedHistory κ b jumps Q h (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) EL ∧
        StagedPiecesRegular κ b jumps Q (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) EL ∧
        ∀ᵐ ω ∂Q, WalkRightAdds κ b jumps (fun _ => EL) ω := by
  obtain ⟨E₁, hE₁⟩ := exists_isStagedHistory_regular_all_of_thm12_thm13 h12 h13 hκ hκ4 hb hh
  obtain ⟨hE₁', hreg₁, -⟩ := StagedReg.regFam_spec hb (fun s hs => (hE₁ s).2 hs) (fun s _ => (hE₁ s).1)
  set lw := boundaryWalkSpec b jumps (-(Real.pi / 2)) true with hlw
  have hlwp : IsBoundaryContinuedProgram lw.2.2 :=
    isBoundaryContinuedProgram_boundaryWalkSpec b jumps ⟨le_rfl, by linarith [Real.pi_pos]⟩ true
  have hst := hE₁' lw hlwp
  have hamb : ∀ t, t < 0 → t ∉ jumps → b t + -(Real.pi / 2) * chiC κ < sleLambda κ := by
    intro t ht htJ
    have h1 := hadm t ht htJ
    have hl := sleLambda_pos hκ
    unfold cumWeightLeft at h1
    have h2 : -(b t + -(Real.pi / 2) * chiC κ) / sleLambda κ = -((b t + -(Real.pi / 2) * chiC κ) / sleLambda κ) :=
      neg_div _ _
    have h3 : (b t + -(Real.pi / 2) * chiC κ) / sleLambda κ < 1 := by linarith
    exact (div_lt_one hl).1 h3
  refine ⟨StagedReg.regFam E₁ lw, hst, stagedPiecesRegular_of_regular h13 hκ hb hst (hreg₁ lw), ?_⟩
  exact Ly.ae_walkRightAdds_of_bound h13 hκ hb hh hst (hreg₁ lw) hamb

/-! ### The combined target -/

/-- **SB2(2)'s combined target at the later launches from the erasure identity** (and Theorems 1.2–1.3): `m = −e_R`;
the word clauses from PROVE-T14-SB2LOW's word half, the entry value `Lu.ae_isRightEntryValue_upperEntry`, the
relative walk `exists_relLowerWalk` of the conditional field (admissible left of `0` by
`Lz.lowerLeftAdmissible_of_activeHighWord`), the set link and the lift from `SB2LowerTailIdentStatement`, and the free
real point from `LowerWalkLeftFreeStatement` (transported to the retained kernel at a level below `0` and `A`). -/
theorem sb2LowerLaunchLiftSuccStatement_of_tailIdent (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (h12₀ : Exist.Theorem12Statement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) (hid : SB2LowerTailIdentStatement.{u}) :
    Lh.SB2LowerLaunchLiftSuccStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft
  have hsp : IsBoundaryContinuedProgram (upperSpec u l).2.2 := isBoundaryContinuedProgram_upperSpec hlθ
  obtain ⟨hnn, hword⟩ := Lh.sb2LowerWordStatement_of_theorem13 h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE
    hER u l k hu hlp hlθ hL hleft
  have hfree := lowerWalkLeftFreeStatement_of_thm12_thm13 h12 h13 h12₀ h13₀
  have hfreeN : ∀ᵐ ω ∂P, ∀ n : ℕ, ∃ y : ℝ, y < -(n : ℝ) ∧ (y : ℂ) ∉ lowerWalkSet κ b jumps E ω :=
    ae_all_iff.2 fun n => hfree κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER (-(n : ℝ))
  filter_upwards [hnn, hword, hid κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    ae_isRightEntryValue_upperEntry (hER _ hsp) k,
    KernelTower.ae_ae_condExpKernel_of_ae ((hE _ hsp).2.1 k) hfreeN] with ω₀ hnn₀ hword₀ hid₀ hent₀ hfree₀
  intro c θ hlaunch b' J' h' hb' hT' hG' hk
  have hF := mem_upperLaunchSet hlaunch
  have hent := hent₀ hF
  rw [upperLaunchChart_eq hlaunch] at hent
  obtain ⟨hadm, hact⟩ := hword₀ c θ hlaunch b' J' h' hb' hT' hG' _ rfl
  have hb'' := isPiecewiseConstantBoundaryData_affData (m := -upperEntry κ b jumps E u l k ω₀) one_pos hb'
  have hG'' := hG'.affine_finset (m := -upperEntry κ b jumps E u l k ω₀) one_pos
  have hla := Lz.lowerLeftAdmissible_of_activeHighWord hκ hκ4 (fun p hp => (hlθ p hp).1) hL hadm hact
  obtain ⟨EL, hst, hreg, hra⟩ := exists_relLowerWalk h12 h13 hκ hκ4 hb'' hG'' hla
  have hidQ := hid₀ c θ hlaunch b' J' h' hb' hT' hG' hk _ rfl EL hst hreg
  refine ⟨-upperEntry κ b jumps E u l k ω₀, EL, ⟨neg_nonpos.2 (hnn₀ hF), hadm, ?_, hact, hst, hreg, hra, ?_⟩, ?_⟩
  · rw [neg_neg]; exact hent
  · filter_upwards [hidQ] with ω hω
    exact hω.1
  · filter_upwards [hidQ, hfree₀] with ω hω hfω
    refine ⟨?_, hω.2⟩
    obtain ⟨n, hn⟩ := exists_nat_ge (-(min 0 (realMin (upperPrefix κ b jumps E u l k ω₀))))
    obtain ⟨y, hy, hyB⟩ := hfω n
    refine ⟨y, ?_, ?_, hyB⟩
    · have := min_le_left 0 (realMin (upperPrefix κ b jumps E u l k ω₀)); linarith
    · have := min_le_right 0 (realMin (upperPrefix κ b jumps E u l k ω₀)); linarith

/-- **SB2(2)'s combined target (R104a) from the erasure identity** (and Theorems 1.2–1.3): the first launch by
PROVE-T14-SB2LOW's `Lh.sb2LowerLaunchLift_zero` (with `LowerWalkLeftFreeStatement` proved), the later launches by
`sb2LowerLaunchLiftSuccStatement_of_tailIdent`. -/
theorem sb2LowerLaunchLiftStatement_of_tailIdent (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (h12₀ : Exist.Theorem12Statement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) (hid : SB2LowerTailIdentStatement.{u}) :
    Lh.SB2LowerLaunchLiftStatement.{u} :=
  sb2LowerLaunchLiftStatement_of_succ' h12 h13 h12₀ h13₀
    (sb2LowerLaunchLiftSuccStatement_of_tailIdent h12 h13 h12₀ h13₀ hid)

/-- **SB2(2) in R99's form from the erasure identity** (and Theorems 1.2–1.3). -/
theorem sb2LowerLaunchEntryAdmStatement_of_tailIdent (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (h12₀ : Exist.Theorem12Statement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) (hid : SB2LowerTailIdentStatement.{u}) :
    Lz.SB2LowerLaunchEntryAdmStatement.{u} :=
  Lh.sb2LowerLaunchEntryAdmStatement_of_lift (sb2LowerLaunchLiftStatement_of_tailIdent h12 h13 h12₀ h13₀ hid)

end InteractingSLE.Theorem14.SB.Lk
