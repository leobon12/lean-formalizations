/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2CtRoot
import InteractingSLE.Spec.Supplement.SB2FpBase

/-!
# SB2(2)'s relative root with F3LAW's corrected root-word identity (D76)

Packet PROVE-SB2-CONDFIN, round 13 (decision D76, item 1). `Ct.SB2LowerRootWordStatement` (round 11) is not
derivable as stated: `Mz.CanonIdentOn` does not fix the offset `x₀`, and `G` contains non-root samples. F3LAW proved
the corrected form `Fp.RootWordAtX` (the word is one constant data word of the relative field wherever the root chart
identity `(hullChart (fill K) x₀).1 = (physRelChart c₀ (init chart) m).1` holds on `ℍ ∖ fill K`), for its base word
(`Fp.SB2LowerBaseWordStatement`, landed 5dec32ef7). The assembly has that chart identity: `Mz.ident_rel_stage` at
relative stage `0` gives it (`hfwd`).

* `RootCanonAtX`, `SB2LowerRootCanonXStatement`; **`sb2LowerRootCanonXStatement_of_ident`** (from CANON's step 3,
  `Ct.SB2LowerRootIdentStatement`, and F3LAW's landed base word);
* **`sb2LowerRootDetWStatement_of_canonX`** (`Ct.sb2LowerRootDetWStatement_of_canon` with `hweqω N hG hfwd`);
* **`sb2LowerRelPosWRootStatement_of_ident`**: `Cf.SB2LowerRelPosWRootStatement` from CANON's step 3 alone.

R48: Theorems 1.2–1.3 appear only as hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
open QuantumZipper (H chiC)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Cy

open Supp9B Lx Lu Leaf FlowDilate Sec4 Exist Exist.Staged Exist.StagedLaw Lk Mx Mn Mq Mz Restart Ct

section Defs

variable (h12p : Theorem12ParamStatement.{u}) {κ : ℝ} (hκ : 0 < κ) (b : ℝ → ℝ) (jumps : Finset ℝ)
  {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
  (h : Ω → DistOn upperHalfPlaneOpens) (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (u : ℝ) (l : List (ℝ × ℝ≥0))
  (k : ℕ)

/-- **The canonical objects of the relative root at B's stage `ℓ`, with F3LAW's corrected root-word identity**
(`Ct.RootCanonAt` with `Fp.RootWordAtX` for `Ct.RootWordAt`, D76). -/
def RootCanonAtX (ℓ : ℕ) : Prop :=
  ∃ (G : Set Ω) (c : Ω → BoundaryWord) (K : Ω → Set ℂ) (x₀ : Ω → ℝ) (Dr : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (hKc : ∀ ω, IsCompact (K ω)) (hKp : ∀ ω, IsPreconnected (K ω ∪ Restart.lowerHalf)),
    Ct.RootCover (κ := κ) b jumps P E u l k ℓ G ∧ Mz.CanonIdentOn h12p hκ b jumps P h E u l k ℓ G c K x₀ Dr hKc hKp ∧
      Fp.RootWordAtX κ b jumps P h E u l k G K x₀ c

end Defs

/-- **The canonical root objects with the corrected root-word identity at every B-stage.** -/
def SB2LowerRootCanonXStatement (h12p : Theorem12ParamStatement.{u}) : Prop :=
  ∀ κ : ℝ, ∀ hκ : 0 < κ, κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
    ∀ (u : ℝ) (l : List (ℝ × ℝ≥0)) (k : ℕ), u ≤ 0 → l.Pairwise (fun p q => p.2 < q.2) →
      (∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2)) →
      (∀ x ∈ Ioo u 0, x ∉ jumps → -2 < Sec4.cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ)) →
      (∀ᵐ ω ∂P, ω ∈ upperLaunchSet κ b jumps E u l k →
        upperPrefix κ b jumps E u l k ω ∩ rightSideOf (lowerWalkSet κ b jumps E ω) = ∅) →
      0 < k → ∀ ℓ : ℕ, RootCanonAtX h12p hκ b jumps P h E u l k ℓ

/-- **CANON's step 3 and F3LAW's base word give the corrected root objects** (Theorems 1.2–1.3): the base word of
`Fp.SB2LowerBaseWordStatement` (landed, `Fp.sb2LowerBaseWordStatement_of_thms`) has the base law `Ct.BaseLawFor` at
every stage, so CANON's root objects exist for it, and its root-word identity `Fp.RootWordAtX` holds for every root
object family. -/
theorem sb2LowerRootCanonXStatement_of_ident (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
    (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0})
    (hI : Ct.SB2LowerRootIdentStatement.{u} (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13)) :
    SB2LowerRootCanonXStatement.{u} (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13) := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft hk ℓ
  obtain ⟨β, hβm, hword, hbase⟩ := Fp.sb2LowerBaseWordStatement_of_thms h12 h13 h12₀ h13₀ κ hκ hκ4 b jumps hb P h hh
    W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft
  have hB : Ct.BaseLawFor (κ := κ) b jumps P h E u l k ℓ β := by
    refine ⟨hβm, fun 𝓖 A₁ h𝓖 hA₁ => ?_⟩
    obtain ⟨K, G, Y, M, h1, h2, -⟩ := hbase ℓ 𝓖 A₁ h𝓖 hA₁
    exact ⟨K, G, Y, M, h1, h2⟩
  obtain ⟨G, K, x₀, Dr, hKc, hKp, hcov, hid⟩ :=
    hI κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft hk ℓ β hB
  exact ⟨G, _, K, x₀, Dr, hKc, hKp, hcov, hid, hword G K x₀ hKc hKp⟩

/-- **The relative root determined** (Theorems 1.2–1.3) from the canonical root objects with F3LAW's corrected
root-word identity `Fp.RootWordAtX` (D76: the word is constant where the root chart identity holds, which
`Mz.ident_rel_stage` gives at relative stage `0`). -/
theorem sb2LowerRootDetWStatement_of_canonX (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
    (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0})
    (hroot : SB2LowerRootCanonXStatement.{u} (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13)) :
    Ch.SB2LowerRootDetWStatement.{u} (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13) := by
  set h12p := Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13 with hh12p
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft
  by_cases hk : 0 < k
  swap
  · exact Eventually.of_forall fun ω₀ c θ hlaunch b' J' h' hb' hT' hG' hk' => absurd hk' hk
  have hsp : IsBoundaryContinuedProgram (upperSpec u l).2.2 := isBoundaryContinuedProgram_upperSpec hlθ
  have hspl : IsBoundaryContinuedProgram (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2 :=
    isBoundaryContinuedProgram_boundaryWalkSpec b jumps
      ⟨le_rfl, by linarith [Real.pi_pos]⟩ true
  have hEu := hE _ hsp
  have hRu := hER _ hsp
  have hRl := hER _ hspl
  have hm𝒢 := hEu.2.1 k
  have hT := hroot κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft hk
  choose G cw K x₀ Dr hKc hKp hT' using hT
  have hcovQ := KernelTower.ae_ae_condExpKernel_of_ae hm𝒢 (ae_all_iff.2 fun n => (hT' n).1)
  have hidQ := KernelTower.ae_ae_condExpKernel_of_ae hm𝒢 (ae_all_iff.2 fun n => (hT' n).2.1.2.2)
  have hwordP := ae_all_iff.2 fun n => (hT' n).2.2
  have hRP := sb2LowerStageChainStatementWAP_of_thms h12 h13 h12₀ h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf
    hζ' E hE hER u l k hu hlp hlθ hL hleft
  have hrun := Retain.ae_ae_run_eq (upperSpec u l) hRu hm𝒢 (le_refl _)
  have hBregQ := KernelTower.ae_ae_condExpKernel_of_ae hm𝒢 (GW1W.regLaunches_of_stagedPiecesRegular hRl)
  have hUreg := GW1W.regLaunches_of_stagedPiecesRegular hRu
  have hβex := KernelTower.ae_ae_condExpKernel_of_ae hm𝒢
    (Mn.rightWalkProperReg_of_thms h12 h13 h12₀ h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER)
  have htl := sb2LowerTailLiftCurve h13 κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft
  filter_upwards [hcovQ, hidQ, hwordP, hRP, hrun, hBregQ, hUreg, hβex, htl] with ω₀ hcov₀ hid₀ hword₀ hRP₀ hrun₀
    hB₀ hU₀ hβ₀ htl₀
  intro c θ hlaunch b' J' h' hb' hT'' hG' hk' hκ' m hm EL hELm hELr hcl
  obtain ⟨hTW, hSF, hRF⟩ := hcl
  have hcN : WalkIntCanon.IsNormalized c := isNormalized_launchChart (upperSpec u l) hU₀ hlaunch
  -- the words of the root-word identity and the witness
  choose w hwlaw hweq using fun n => hword₀ n c θ hlaunch b' J' h' hb' hT'' hG' m hm
  set Y₀ : Ω → DistOn upperHalfPlaneOpens := fun ω => flowField 0 0 (affField m one_pos (h' ω)) with hY₀
  have hY₀e : Y₀ = fun ω => affField m one_pos (h' ω) :=
    funext fun ω => Sec7.Prop74B.flowField_zero_zero _
  have hlaw : ∀ n, IsGFFWithBoundaryData
      (condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀) Y₀ (w n).fn (w n).jumps :=
    fun n => by rw [hY₀e]; exact hwlaw n
  have hh'm : Measurable fun ω => affField m one_pos (h' ω) := (measurable_affField one_pos).comp hG'.1
  have hW₀ : IsStageWitness κ (affData 1 m b') (affJumps 1 m J')
      (condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀)
      (fun ω => affField m one_pos (h' ω)) (relLowerSpec b' J' m) EL 0 (fun _ => w 0) Y₀ :=
    isStageWitness_zero_of_law (spec := relLowerSpec b' J' m) hh'm (hlaw 0)
  have hswitch : ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀), ∀ n,
      IsDriverCodeMatch (driverCode h12p hκ' (-(Real.pi / 2)) (w 0, Y₀ ω))
        (driverOf h12p hκ' (-(Real.pi / 2)) (w n, Y₀ ω)).1 (driverOf h12p hκ' (-(Real.pi / 2)) (w n, Y₀ ω)).2 :=
    ae_all_iff.2 fun n => ae_codeMatch_switch h12p h13 hκ' hb' m hh'm (hlaw n) (hlaw 0)
  have hweqQ := ae_all_iff.2 hweq
  -- the per-sample facts under the upper kernel (as in the tail template)
  have hRPQ := hRP₀ c θ hlaunch b' J' h' hb' hT'' hG' hk' m hm EL hELm hELr hTW hSF
  have hupQ : ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
      upperPrefix κ b jumps E u l k ω = upperPrefix κ b jumps E u l k ω₀ ∧ ω ∈ upperLaunchSet κ b jumps E u l k := by
    filter_upwards [hrun₀] with ω hω
    refine ⟨?_, ?_⟩
    · show SB.prefixPhysSet κ b jumps (upperSpec u l) (fun j => E (upperSpec u l) j ω) k ∪ _ =
        SB.prefixPhysSet κ b jumps (upperSpec u l) (fun j => E (upperSpec u l) j ω₀) k ∪ _
      unfold SB.prefixPhysSet
      rw [hω]
    · show (ExplState.run κ b jumps (upperSpec u l) (fun j => E (upperSpec u l) j ω) (k + 1)).2.2.2.1 k ≠ none
      rw [launches_run_succ_of_run_eq (upperSpec u l) hω, hlaunch]
      exact Option.some_ne_none _
  have hELregQ : ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
      SB.LuM.RegLaunches κ (affData 1 m b') (affJumps 1 m J') (relLowerSpec b' J' m) (fun i => EL i ω) := by
    filter_upwards [hSF] with ω hf
    exact Mn.regLaunches_of_facts (fun j => hELr j ω) (fun j hl hz => (hf j hl hz).1.2.2.2.2.2.2)
  have hRmemQ : ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
      ((realMax (upperPrefix κ b jumps E u l k ω₀) : ℝ) : ℂ) ∈
        ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (lowerD b jumps E ω) := by
    filter_upwards [hβ₀, htl₀ c θ hlaunch b' J' h' hb' hT'' hG' m hm] with ω hβω htlω
    obtain ⟨β₀, hβ, hβ0, hβr⟩ := hβω
    obtain ⟨tL, γ, hγ⟩ := htlω β₀ hβ hβ0 hβr
    rw [← hγ.1]
    have hmem : β₀ tL ∈ range β₀ := mem_range_self tL
    rw [hβr] at hmem
    exact hmem
  refine ⟨fun _ => w 0, Y₀, hW₀, ?_⟩
  filter_upwards [hcov₀, hid₀, hweqQ, hswitch, hRPQ, hupQ, hB₀, hELregQ, hRmemQ, hRF] with ω hcovω hidω hweqω
    hswω hRPω hupω hBω hELω hRmω hRFω
  intro hz
  set N := 0 + relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω₀)) (lowerD b jumps E ω)
    with hN
  -- (1) the positive root lies in the canonical event at `N`
  obtain ⟨hZ0, -, -⟩ := hRFω
  have hnz : ¬ (ZeroRoot κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω₀))
      (lowerD b jumps E ω) ∨ (lowerD b jumps E ω (relOff κ (-(Real.pi / 2)) b jumps
        (realMax (upperPrefix κ b jumps E u l k ω₀)) (lowerD b jumps E ω))).2 -
      (shiftD κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω₀)) (lowerD b jumps E ω) 0 :
        ℝ≥0∞) = 0) := fun h0 => hz ((congrArg Prod.snd (hZ0 h0)).trans rfl)
  have hl := relRun_one_launches κ b' J' m EL ω
  obtain ⟨hBl, -⟩ := hRPω.1 0 _ _ hl hz
  have hpos : PosRootAt (κ := κ) b jumps E u l k N ω := by
    refine ⟨hBl, ?_, ?_⟩
    · rw [hupω.1, hN, zero_add]
      exact ⟨ent_relOff_of_not_zeroRoot hRmω fun h0 => hnz (Or.inl h0), rfl⟩
    · rw [hupω.1, hN, zero_add]
      exact fun h0 => hnz (Or.inr h0)
  have hG : ω ∈ G N := hcovω N hupω.2 hpos
  obtain ⟨hfill, hC, hD, -⟩ := hidω N hG
  -- (2) the identification at relative stage `0`
  have hc₁N := isNormalized_launchChart _ hELω hl
  have hK : IsHPHull (fillH (K N ω)) := Mo.isHPHull_fillH (hKc N) (hKp N) ω
  obtain ⟨hl1, hl2, hfwd, hlift⟩ := ident_rel_stage hRPω.1 hRPω.2 hupω.1 hl hz hcN hc₁N
    (isNormalized_walkStageChart hBω _) hK hfill hC hD
  have hPd : IsDomainChart (H \ fillH (K N ω)) (Mo.physRelChart c (ExplState.init 0).2.2.2.2.1 m) := by
    have h1 := hRPω.2 0 _ _ hl hz
    have hY : retY (κ := κ) b jumps E u l k N ω = upperPrefix κ b jumps E u l k ω₀ ∪ SB.prefixPhysSet κ b jumps
        (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) N := by
      show upperPrefix κ b jumps E u l k ω ∪ _ = _
      rw [hupω.1]
    rw [hfill, hY]
    exact h1
  have htr := isChartTransport_run_of_phys hcN.conformal hc₁N.conformal (continuousOn_lift_inv_of_normalized hcN)
    (continuousOn_lift_inv_of_normalized hc₁N) (Mo.isDomainChart_hullChart hK (x₀ N ω)) hPd hfwd hlift (hT'' ω)
  have hZ : Chart.chartTransport (Mu.isConformal_canon (x₀ N) (hKc N) (hKp N) ω) 1 0 (chiC κ) (h ω) = Y₀ ω :=
    GW2aPiece.eq_flowField_of_isChartTransport htr
  -- (3) the word identity and the switch
  rw [hZ, hweqω N hG hfwd] at hl1 hl2
  refine isDriverCodeMatch_congr (hswω N) hl1 ?_ fun t ht => hl2 t (hl1 ▸ ht)
  rw [(hELr 0 ω).2.1, (Mz.isRegularDriver_driverOf h12p hκ' _ _).2.1]


/-- **SB2(2)'s relative root: the code match of a positive root from CANON's step 3 alone** (Theorems 1.2–1.3;
D76: the root-word identity is F3LAW's landed `Fp.RootWordAtX`). -/
theorem sb2LowerRelPosWRootStatement_of_ident (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
    (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0})
    (hI : Ct.SB2LowerRootIdentStatement.{u} (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13)) :
    Cf.SB2LowerRelPosWRootStatement.{u} (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13) :=
  Ch.sb2LowerRelPosWRootStatement_of_det h12 h13 h12₀ h13₀
    (sb2LowerRootDetWStatement_of_canonX h12 h13 h12₀ h13₀ (sb2LowerRootCanonXStatement_of_ident h12 h13 h12₀ h13₀ hI))

end InteractingSLE.Theorem14.SB.Cy
