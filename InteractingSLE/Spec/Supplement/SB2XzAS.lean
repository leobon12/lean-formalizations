/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2XwAS
import InteractingSLE.Spec.Supplement.SB2XzSample
import InteractingSLE.Spec.Supplement.SB2XzTail
import InteractingSLE.Spec.Supplement.SB2XzArcs

/-!
# SB2(2)'s per-stage correspondence over the bundle without `tail`

Packet PROVE-T14-SB2LIFT (round 30; the corrected T bundle, handoff §R29.3): `stageChain_sampleW`,
**`ClauseTW`** (`ClauseTR` without `tail`), `tailArc_of_bundle`, **`sb2LowerStageChainStatementWA_of_thms`** (R2 over `ClauseTW`, Theorems
1.2–1.3) and `sb2LowerStageChainStatementW_of_WA`.
The statements and proofs are those of the landed originals, with `tail` replaced by its connector form
`TailArc` (`SB2XzArc`); the full `tail` is false (handoff §R29.1).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar chiC)

universe u

namespace InteractingSLE.Theorem14.SB.Mn

open Supp9B Lx Lu Leaf FlowDilate Sec4 Exist Exist.Staged Exist.StagedLaw Lk LuM GW1W GW1Bookkeep
open Sec7.PocketTraversal Sec7.Lemma71C
open FinRel (IsSB2RelChain)

variable {κ θ : ℝ} {b₁ b₂ : ℝ → ℝ} {J₁ J₂ : Finset ℝ} {R : ℝ} {ι : ℝ → ℝ} {β₀ γ : ℝ≥0 → ℂ} {tL : ℝ≥0}
  {D₁ D₂ : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {o : ℕ} {c : Chart} {m : ℝ}

/-- **The per-stage correspondence at one sample** at every launching relative stage of positive lifetime, from the
corrected bundle at offset `o`, the per-stage facts and the head of the start piece. -/
theorem stageChain_sampleW (hι : RayCorr b₁ J₁ b₂ J₂ R ι)
    (hC : CurveInputsW κ θ b₁ J₁ R ι D₁ β₀ γ tL) (hreg₂ : ∀ j, IsRegularDriver (D₂ j))
    (hP₁ : RegLaunches κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁) (hW₁ : WalkChainFacts κ b₁ J₁ θ D₁)
    (hlm₁ : ∀ j, NoLeftMove κ b₁ J₁ θ D₁ j) (hlh₁ : ∀ j, NoLeftHit κ b₁ J₁ θ D₁ j)
    (hallow : ∀ k, 2 + o ≤ k → AllowedSt κ b₁ (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ k))
    (hexit₁ : ∀ k, 2 + o ≤ k → (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (k + 1)).2.2.2.1 k ≠ none →
        (D₁ k).2 ≠ ⊤ → (D₁ k).2 ≠ 0 →
      ∃ x : ℝ, stRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ k) < x ∧ lHit (stChart (ExplState.run
          κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ k)) ⊤ (D₁ k) x)
    (hβp : Supp9B.IsProperCurve β₀) (hγp : Supp9B.IsProperCurve γ) (hβ0 : β₀ 0 = 0)
    (hD : LiftCurveData β₀ γ tL R ι)
    (hB : (∃ N : ℕ, RunInputs'' κ θ b₁ J₁ b₂ J₂ R ι D₁ D₂ β₀ γ tL o N ∧
        (ArcStart κ θ b₁ J₁ R D₁ D₂ β₀ tL o ∨ PieceStartV κ θ b₁ J₁ b₂ J₂ R ι D₁ D₂ β₀ γ tL o)) ∨
      (PieceStartV κ θ b₁ J₁ b₂ J₂ R ι D₁ D₂ β₀ γ tL o ∧ (D₁ o).2 = ⊤))
    {A : Set ℂ} {ĝ : ℂ → ℂ} {Cg : ℝ} (hc : IsDomainChart (H \ fillH A) c) (hA : IsCompact A)
    (hĝ : ∀ p ∈ Hbar, Tendsto c.2.1 (𝓝[H] p) (𝓝 (ĝ p))) (hCg : ∀ p ∈ Hbar, ‖ĝ p - p‖ ≤ Cg)
    (hγ : IsTailLiftCurve c R m β₀ tL γ) (hhead : β₀ '' Icc 0 tL ⊆ hullK A) {t₀ : ℝ≥0}
    (ht₀ : (t₀ : ℝ≥0∞) ≤ (D₁ o).2)
    (hfacts : ∀ j, (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ (j + 1)).2.2.2.1 j ≠ none →
      (D₂ j).2 ≠ 0 →
      StageFacts c m (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (j + o)) (D₁ (j + o))
          (if j = 0 then t₀ else 0) (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ j) (D₂ j) ∧
        (j = 0 → ∀ r ≤ t₀, pcPt (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ o) (D₁ o) r ∈ hullK A)) :
    ∀ (j : ℕ) (c₁ : Chart) (θ' : ℝ),
      (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ (j + 1)).2.2.2.1 j = some (c₁, θ') → (D₂ j).2 ≠ 0 →
      (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (j + o + 1)).2.2.2.1 (j + o) ≠ none ∧
      IsDomainChart (H \ stageRetained (stChart (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (j + o)))
          (A ∪ SB.prefixPhysSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (j + o)))
        (stageRelChart (stChart (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (j + o))) c c₁ m) ∧
      ∃ (tL' : ℝ≥0) (γ' : ℝ≥0 → ℂ),
        (∀ s : ℝ≥0, ((tL' + s : ℝ≥0) : ℝ≥0∞) < (D₁ (j + o)).2 →
          Tendsto (stageRelChart (stChart (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (j + o))) c c₁
            m).2.1 (𝓝[H] (γ' s)) (𝓝 (LuM.trOf (D₁ (j + o)) (tL' + s)))) ∧
        (∀ S₀ : ℝ≥0, ((tL' + S₀ : ℝ≥0) : ℝ≥0∞) < (D₁ (j + o)).2 →
          ∃ (Wr : ℝ → ℝ) (ηr : ℝ → ℂ),
            (∀ r : ℝ, 0 ≤ r → r ≤ capClock (fun r : ℝ => γ' r.toNNReal) (S₀ : ℝ) →
              Wr r = (D₂ j).1 r.toNNReal ∧ ηr r = LuM.trOf (D₂ j) r.toNNReal) ∧
            IsSB2RelChain (stageRetained (stChart (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (j + o)))
                (A ∪ SB.prefixPhysSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (j + o)))
              (stageRelChart (stChart (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (j + o))) c c₁ m)
              (LuM.trOf (D₁ (j + o))) γ' tL' (S₀ : ℝ) Wr ηr) ∧
        (D₂ j).2 = ⨆ (S₀ : ℝ≥0) (_ : ((tL' + S₀ : ℝ≥0) : ℝ≥0∞) < (D₁ (j + o)).2),
          ENNReal.ofReal (capClock (fun r : ℝ => γ' r.toNNReal) (S₀ : ℝ)) := by
  intro j c₁ θ' hl hz
  have hl' : (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ (j + 1)).2.2.2.1 j ≠ none := by
    rw [hl]; simp
  rcases Nat.lt_or_ge j 2 with hj | hj
  · -- the root (a relative launch is at an even stage)
    obtain ⟨hev, -⟩ := GW1W.even_of_launches_walk hl'
    obtain rfl : j = 0 := by omega
    have hPV : PieceStartV κ θ b₁ J₁ b₂ J₂ R ι D₁ D₂ β₀ γ tL o := by
      rcases hB with ⟨N, -, hA' | hPV⟩ | ⟨hPV, -⟩
      · exact absurd hA'.zero₀ hz
      · exact hPV
      · exact hPV
    obtain ⟨hF, hst⟩ := hfacts 0 hl' hz
    simp only [↓reduceIte, zero_add] at hF ⊢
    exact stageChain_zero hPV hP₁ hβp hC.inj hC.range_eq hc hA hĝ hCg hγ hhead ht₀ (hst rfl) hF c₁ θ' hl
  · rcases hB with ⟨N, hR, hS⟩ | ⟨hPV, htop⟩
    · refine stageChain_twoW hι hC hR hreg₂ hP₁ hW₁ hlm₁ hlh₁ hallow hexit₁ hβp hγp hβ0 hD hS hc hA hĝ hCg hγ hhead
        (fun i hi hli hzi => ?_) j c₁ θ' hj hl hz
      have := (hfacts i hli hzi).1
      simpa only [show i ≠ 0 by omega, ↓reduceIte] using this
    · -- an infinite start piece: the relative walk is done after its root
      exfalso
      have h2top : (D₂ 0).2 = ⊤ := hPV.top.2 htop
      have hdone1 : stStatus (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ 1) = stDone := by
        rw [run_one_walk]
        exact (launch_eq_of_top _ 0 (D₂ 0) θ ⊤ (by rw [h2top, min_self])).2.2.2.2.1
      exact WalkIntRunChron.not_done_of_launch _ D₂ hl (done_of_le hdone1 (by omega))


/-! ### The corrected bundle without `tail` -/

/-- **The corrected bundle** (handoff §R29.3): `ClauseTR` without its field `tail`, which is false (§R29.1). The
connector form of `tail` it needs is a consequence of the start data (`tailArc_of_bundle`). -/
def ClauseTW (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (u : ℝ)
    (l : List (ℝ × ℝ≥0)) (k : ℕ) (ω₀ : Ω) (c : Chart) (b' : ℝ → ℝ) (J' : Finset ℝ) (m : ℝ)
    (EL : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) : Prop :=
  ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
    ∀ β₀ : ℝ≥0 → ℂ, IsProperCurve β₀ → β₀ 0 = 0 → range β₀ = lowerWalkSet κ b jumps E ω →
      ∀ (tL : ℝ≥0) (γ : ℝ≥0 → ℂ), IsTailLiftCurve c (lR κ b jumps E u l k ω₀) m β₀ tL γ →
        ∃ ι : ℝ → ℝ,
          RayCorr b jumps (affData 1 m b') (affJumps 1 m J') (lR κ b jumps E u l k ω₀) ι ∧
          RayChartLim c (lR κ b jumps E u l k ω₀) m ι ∧
          (∀ s, ∀ x : ℝ, lR κ b jumps E u l k ω₀ < x → β₀ (tL + s) = x → γ s = ι x) ∧
          ((∃ N : ℕ, RunInputs'' κ (-(Real.pi / 2)) b jumps (affData 1 m b') (affJumps 1 m J')
              (lR κ b jumps E u l k ω₀) ι (lD₁ b jumps E ω) (fun j => EL j ω) β₀ γ tL
              (relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω)) N ∧
            (ArcStart κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω) (fun j => EL j ω) β₀ tL
                (relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω)) ∨
              PieceStartV κ (-(Real.pi / 2)) b jumps (affData 1 m b') (affJumps 1 m J') (lR κ b jumps E u l k ω₀) ι
                (lD₁ b jumps E ω) (fun j => EL j ω) β₀ γ tL
                (relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω)))) ∨
          (PieceStartV κ (-(Real.pi / 2)) b jumps (affData 1 m b') (affJumps 1 m J') (lR κ b jumps E u l k ω₀) ι
              (lD₁ b jumps E ω) (fun j => EL j ω) β₀ γ tL
              (relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω)) ∧
            (lD₁ b jumps E ω (relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω))).2 = ⊤))

/-- `ClauseTR` gives the corrected bundle (it drops `tail`). -/
theorem ClauseTR.clauseTW {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [MeasurableSpace Ω]
    [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    {u : ℝ} {l : List (ℝ × ℝ≥0)} {k : ℕ} {ω₀ : Ω} {c : Chart} {b' : ℝ → ℝ} {J' : Finset ℝ} {m : ℝ}
    {EL : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (h : ClauseTR κ b jumps P E u l k ω₀ c b' J' m EL) :
    ClauseTW κ b jumps P E u l k ω₀ c b' J' m EL := by
  filter_upwards [h] with ω hω
  intro β₀ hβ hβ0 hβr tL γ hγ
  obtain ⟨ι, h1, h2, -, h4, h5⟩ := hω β₀ hβ hβ0 hβr tL γ hγ
  exact ⟨ι, h1, h2, h4, h5⟩

/-- **The connector form of `tail` from the start data** (`tailArc_of_arcStart`, `tailArc_of_pieceStart`). -/
theorem tailArc_of_bundle {κ θ : ℝ} {b₁ b₂ : ℝ → ℝ} {J₁ J₂ : Finset ℝ} {R : ℝ} {ι : ℝ → ℝ}
    {D₁ D₂ : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {β₀ γ : ℝ≥0 → ℂ} {tL : ℝ≥0} {o : ℕ} (hβp : IsProperCurve β₀)
    (hβr : range β₀ = ExplState.physSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁) (hβL : β₀ tL = R)
    (hhead : ∀ t ≤ tL, ∀ x : ℝ, β₀ t = x → x ≤ R)
    (harc : ∀ n, ∀ a ∈ (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n).2.1, a ⊆ Ici 0)
    (hP : RegLaunches κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁) (hlm : ∀ j, NoLeftMove κ b₁ J₁ θ D₁ j)
    (hlh : ∀ j, NoLeftHit κ b₁ J₁ θ D₁ j)
    (hS : (∃ N : ℕ, RunInputs'' κ θ b₁ J₁ b₂ J₂ R ι D₁ D₂ β₀ γ tL o N ∧
        (ArcStart κ θ b₁ J₁ R D₁ D₂ β₀ tL o ∨ PieceStartV κ θ b₁ J₁ b₂ J₂ R ι D₁ D₂ β₀ γ tL o)) ∨
      (PieceStartV κ θ b₁ J₁ b₂ J₂ R ι D₁ D₂ β₀ γ tL o ∧ (D₁ o).2 = ⊤)) :
    TailArc κ θ b₁ J₁ D₁ R β₀ tL := by
  rcases hS with ⟨N, -, hA | hV⟩ | ⟨hV, -⟩
  · exact tailArc_of_arcStart hβp hβr hβL hhead harc hP hlm hlh hA
  · exact tailArc_of_pieceStart hβp hβL harc hP hlm hlh hV
  · exact tailArc_of_pieceStart hβp hβL harc hP hlm hlh hV

/-- **SB2(2)'s per-stage correspondence over the bundle without `tail`**: `SB2LowerStageChainStatementW` with
`ClauseTW` in place of `ClauseTR`. -/
def SB2LowerStageChainStatementWA : Prop :=
  Lf.SB2LowerSetting.{u} fun κ b jumps _ _ _ P _ E u l k ω₀ c b' J' _ =>
    0 < k → ∀ m : ℝ, m = -upperEntry κ b jumps E u l k ω₀ → ∀ EL : ℕ → _ → Drv,
      (∀ j, Measurable (EL j)) → (∀ j ω, IsRegularDriver (EL j ω)) →
      ClauseTW κ b jumps P E u l k ω₀ c b' J' m EL → StageFactsAS κ b jumps P E u l k ω₀ c b' J' m EL →
      ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
        StageChainAtR2 κ b jumps E u l k ω₀ c b' J' m EL ω

/-- **SB2(2)'s per-stage correspondence over the bundle without `tail`, PROVED** (Theorems 1.2–1.3). -/
theorem sb2LowerStageChainStatementWA_of_thms (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (h12₀ : Exist.Theorem12Statement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) : SB2LowerStageChainStatementWA.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft
  have hsp : IsBoundaryContinuedProgram (upperSpec u l).2.2 := isBoundaryContinuedProgram_upperSpec hlθ
  have hm𝒢 := (hE _ hsp).2.1 k
  have hβex := KernelTower.ae_ae_condExpKernel_of_ae hm𝒢
    (rightWalkProperReg_of_thms h12 h13 h12₀ h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER)
  filter_upwards [hβex, GW1W.regLaunches_of_stagedPiecesRegular (hER _ hsp),
    sb2LowerTailLiftCurve h13 κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerHead κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerHeadHull κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerAllowed h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerRightHits h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerActualInputs h12 h13 h12₀ h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL
      hleft,
    Lk.sb2LowerArcsIci h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft]
    with ω₀ hβ₀ hup hT₀ hH₀ hK₀ hA₀ hX₀ hI₀ hZ₀
  intro c θ hlaunch b' J' h' hb' hT' hG' _ m hm EL _ hreg hCl hFa
  obtain ⟨hcD, hcA, ĝ, Cg, hĝ, hCg⟩ := upperChart_facts hup hlaunch
  filter_upwards [hβ₀, hT₀ c θ hlaunch b' J' h' hb' hT' hG' m hm, hH₀ c θ hlaunch b' J' h' hb' hT' hG',
    hK₀ c θ hlaunch b' J' h' hb' hT' hG', hA₀ c θ hlaunch b' J' h' hb' hT' hG',
    hX₀ c θ hlaunch b' J' h' hb' hT' hG', hI₀ c θ hlaunch b' J' h' hb' hT' hG', hZ₀ c θ hlaunch b' J' h' hb' hT' hG',
    hCl, hFa]
    with ω hβω hTω hHω hKω hAω hXω hIω hZω hClω hFaω
  obtain ⟨β₀, hβ, hβ0, hβr⟩ := hβω
  obtain ⟨tL, γ, hγ⟩ := hTω β₀ hβ hβ0 hβr
  obtain ⟨ι, hι, hlim, hray, hS⟩ := hClω β₀ hβ hβ0 hβr tL γ hγ
  obtain ⟨hP₁, hW₁, hn⟩ := hIω
  have hhead := hHω β₀ hβ hβ0 hβr tL hγ.1
  have hhull := hKω β₀ hβ hβ0 hβr tL hγ.1
  have htail := tailArc_of_bundle hβ hβr hγ.1 hhead hZω hP₁ (fun j => (hn j).1) (fun j => (hn j).2.1) hS
  have hC : CurveInputsW κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) ι (lD₁ b jumps E ω) β₀ γ tL :=
    ⟨hβr, hβ.2.1, hγ.1, hγ.2.2.1, hhead, htail, hray⟩
  have hD : LiftCurveData β₀ γ tL (lR κ b jumps E u l k ω₀) ι :=
    ⟨hβ.1, hβ.2.2.1, hγ.2.1.1, hγ.2.1.2.2.1, hγ.1, hγ.2.2.1,
      fun t ht him => hhead t ht _ (Complex.ext (by simp) (by simp [him])), hray, back_of_rayChartLim hγ hlim⟩
  intro j c₁ θ' hl hz
  exact stageChain_sampleW hι hC (fun j => hreg j ω) hP₁ hW₁ (fun j => (hn j).1) (fun j => (hn j).2.1)
    (fun j hj => hAω j (by omega)) (fun j _ => hXω j) hβ hγ.2.1 hβ0 hD hS hcD hcA hĝ hCg hγ hhull
    (visitTime_le _ _ _) (fun i hli hzi => hFaω i hli hzi) j c₁ θ' hl hz

/-- The statement over `ClauseTR` follows from the one over the corrected bundle. -/
theorem sb2LowerStageChainStatementW_of_WA (h : SB2LowerStageChainStatementWA.{u}) :
    SB2LowerStageChainStatementW.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h' hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft
  filter_upwards [h κ hκ hκ4 b jumps hb P h' hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft] with ω₀ h₀
  intro c θ hlaunch b' J' h'' hb' hT' hG' hk m hm EL hEL hreg hCl hFa
  exact h₀ c θ hlaunch b' J' h'' hb' hT' hG' hk m hm EL hEL hreg hCl.clauseTW hFa

end InteractingSLE.Theorem14.SB.Mn
