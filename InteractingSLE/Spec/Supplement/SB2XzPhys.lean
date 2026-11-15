/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2XxPhys
import InteractingSLE.Spec.Supplement.SB2XzAS

/-!
# The physical domain identity over the bundle without `tail`

Packet PROVE-T14-SB2LIFT (round 30; the corrected T bundle, handoff §R29.3): `stageChainPhys_sampleW` and
**`sb2LowerStageChainStatementWAP_of_thms`** (R2 with the D5 identity over `ClauseTW`).
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

variable {κ θ : ℝ} {b₁ b₂ : ℝ → ℝ} {J₁ J₂ : Finset ℝ} {R : ℝ} {ι : ℝ → ℝ} {β₀ γ : ℝ≥0 → ℂ} {tL : ℝ≥0}
  {D₁ D₂ : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {o : ℕ} {c : Chart} {m : ℝ}

/-- **The physical domain identity at one sample** at every launching relative stage of positive lifetime. -/
theorem stageChainPhys_sampleW (hι : RayCorr b₁ J₁ b₂ J₂ R ι)
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
    (hγ : IsTailLiftCurve c R m β₀ tL γ) (hhead : β₀ '' Icc 0 tL ⊆ hullK A) :
    ∀ (j : ℕ) (c₁ : Chart) (θ' : ℝ),
      (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ (j + 1)).2.2.2.1 j = some (c₁, θ') → (D₂ j).2 ≠ 0 →
      IsDomainChart (H \ fillH (A ∪ SB.prefixPhysSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (j + o)))
        (Mo.physRelChart c c₁ m) := by
  intro j c₁ θ' hl hz
  have hl' : (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ (j + 1)).2.2.2.1 j ≠ none := by
    rw [hl]; simp
  have hcl : IsClosed (β₀ '' Ici tL) := (isClosedEmbedding_of_isProperCurve hβp).isClosedMap _ isClosed_Ici
  obtain ⟨-, -, hc₁⟩ := eq_launch_of_launches (κ := κ) (b := b₂) (jumps := J₂) _ D₂ hl
  subst hc₁
  rcases Nat.lt_or_ge j 2 with hj | hj
  · obtain ⟨hev, -⟩ := GW1W.even_of_launches_walk hl'
    obtain rfl : j = 0 := by omega
    have hPV : PieceStartV κ θ b₁ J₁ b₂ J₂ R ι D₁ D₂ β₀ γ tL o := by
      rcases hB with ⟨N, -, hA' | hPV⟩ | ⟨hPV, -⟩
      · exact absurd hA'.zero₀ hz
      · exact hPV
      · exact hPV
    simp only [zero_add]
    have hl₁ : (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (o + 1)).2.2.2.1 o ≠ none := by
      rw [hPV.launch, launches_launch, Function.update_self]; simp
    obtain ⟨⟨c₀, θ₀⟩, hl₁'⟩ := Option.ne_none_iff_exists'.1 hl₁
    have hnot₁ := WalkIntRunChron.not_done_of_launch _ D₁ hl₁'
    have hrun0 : ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ 0 = ExplState.init 0 := rfl
    have hch : stChart (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ 0) = Chart.id.recenter 0 := by
      rw [hrun0]; rfl
    set Bp := SB.prefixPhysSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ o with hBp
    set Rel := liftImage β₀ tL γ Bp with hRel
    have hRel0 : Rel ⊆ {0} := by
      rintro _ ⟨s, hs, rfl⟩
      obtain ⟨t, ht, hts⟩ := hPV.head hs
      have h1 : tL + s = t := hC.inj hts.symm
      have h2 : s = 0 := by
        have : tL + s ≤ tL := h1 ▸ ht
        exact le_antisymm (by simpa using this) bot_le
      rw [h2, hγ.2.2.1]
      rfl
    have hRelf : fillH Rel = ∅ := YuanCharacterisation.fillH_eq_empty_of_subset fun z hz => by
      rw [hRel0 hz]; simp
    have hRelc : IsCompact Rel := (Set.subsingleton_singleton.anti hRel0).isCompact
    have hRelH : Rel ⊆ Hbar := fun z hz => by
      rw [hRel0 hz]; show (0 : ℝ) ≤ (0 : ℂ).im; simp
    have h₁ : IsDomainChart (H \ fillH Rel)
        (stChart (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ 0)) := by
      rw [hRelf, sdiff_empty, hch, Chart.recenter_zero]
      exact isDomainChart_id
    have hB' := Lx.isCompact_prefixPhysSet_run (κ := κ) (b := b₁) (jumps := J₁) _ D₁ hP₁ o hnot₁
    have hk₁ := (GW1W.even_of_launches_walk hl₁).2
    have hBr : Bp ⊆ range β₀ := by
      rw [hC.range_eq]
      exact prefix_subset_physSet D₁ (n := o) hk₁.le
    exact isDomainChart_phys_of_lift hc h₁ hA hĝ hCg hRelc hRelH hγ hβp.1 rfl hB' hBr hhead hcl
  · rcases hB with ⟨N, hR, hS⟩ | ⟨hPV, htop⟩
    · have hl₁ := actual_launch_of_bundlesW hι hC hR hreg₂ hP₁ hW₁ hlm₁ hlh₁ hallow hexit₁ hβp hγp hβ0 hD hS j
        hl' hz
      obtain ⟨⟨c₀, θ₀⟩, hl₁'⟩ := Option.ne_none_iff_exists'.1 hl₁
      have hnot₁ := WalkIntRunChron.not_done_of_launch _ D₁ hl₁'
      have hnot₂ := WalkIntRunChron.not_done_of_launch _ D₂ hl
      have h₁ := Lw.isDomainChart_runChart (κ := κ) (b := b₂) (jumps := J₂) _ D₂ hR.reg₂ j hnot₂
      have hB' := Lx.isCompact_prefixPhysSet_run (κ := κ) (b := b₁) (jumps := J₁) _ D₁ hP₁ (j + o) hnot₁
      have hRelEq := prefix_lift_of_bundlesW hι hC hR hreg₂ hP₁ hW₁ hlm₁ hlh₁ hallow hexit₁ hβp hγp hβ0 hD hS j
        hj hl'
      have hRel := Lx.isCompact_prefixPhysSet_run (κ := κ) (b := b₂) (jumps := J₂) _ D₂ hR.reg₂ j hnot₂
      have hRelH : SB.prefixPhysSet κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ j ⊆ Hbar := by
        rw [hRelEq]
        rintro _ ⟨s, -, rfl⟩
        exact hγp.2.2.1 s
      have hk₁ := (GW1W.even_of_launches_walk hl₁).2
      have hBr : SB.prefixPhysSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (j + o) ⊆ range β₀ := by
        rw [hC.range_eq]
        exact prefix_subset_physSet D₁ (n := j + o) hk₁.le
      exact isDomainChart_phys_of_lift hc h₁ hA hĝ hCg hRel hRelH hγ hβp.1 hRelEq hB' hBr hhead hcl
    · exfalso
      have h2top : (D₂ 0).2 = ⊤ := hPV.top.2 htop
      have hdone1 : stStatus (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ 1) = stDone := by
        rw [run_one_walk]
        exact (launch_eq_of_top _ 0 (D₂ 0) θ ⊤ (by rw [h2top, min_self])).2.2.2.2.1
      exact WalkIntRunChron.not_done_of_launch _ D₂ hl (done_of_le hdone1 (by omega))


/-! ### The almost-sure statement with the physical domain identity, over the bundle without `tail` -/

/-- **SB2(2)'s per-stage correspondence with the physical domain identity over the bundle without `tail`**:
`SB2LowerStageChainStatementWP` with `ClauseTW` in place of `ClauseTR`. -/
def SB2LowerStageChainStatementWAP : Prop :=
  Lf.SB2LowerSetting.{u} fun κ b jumps _ _ _ P _ E u l k ω₀ c b' J' _ =>
    0 < k → ∀ m : ℝ, m = -upperEntry κ b jumps E u l k ω₀ → ∀ EL : ℕ → _ → Drv,
      (∀ j, Measurable (EL j)) → (∀ j ω, IsRegularDriver (EL j ω)) →
      ClauseTW κ b jumps P E u l k ω₀ c b' J' m EL → StageFactsAS κ b jumps P E u l k ω₀ c b' J' m EL →
      ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
        StageChainAtR2 κ b jumps E u l k ω₀ c b' J' m EL ω ∧ StageChainPhys κ b jumps E u l k ω₀ c b' J' m EL ω

/-- **SB2(2)'s per-stage correspondence with the physical domain identity over the bundle without `tail`,
PROVED** (Theorems 1.2–1.3). -/
theorem sb2LowerStageChainStatementWAP_of_thms (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (h12₀ : Exist.Theorem12Statement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) : SB2LowerStageChainStatementWAP.{u} := by
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
  refine ⟨fun j c₁ θ' hl hz => ?_, fun j c₁ θ' hl hz => ?_⟩
  · exact stageChain_sampleW hι hC (fun j => hreg j ω) hP₁ hW₁ (fun j => (hn j).1) (fun j => (hn j).2.1)
      (fun j hj => hAω j (by omega)) (fun j _ => hXω j) hβ hγ.2.1 hβ0 hD hS hcD hcA hĝ hCg hγ hhull
      (visitTime_le _ _ _) (fun i hli hzi => hFaω i hli hzi) j c₁ θ' hl hz
  · exact stageChainPhys_sampleW hι hC (fun j => hreg j ω) hP₁ hW₁ (fun j => (hn j).1) (fun j => (hn j).2.1)
      (fun j hj => hAω j (by omega)) (fun j _ => hXω j) hβ hγ.2.1 hβ0 hD hS hcD hcA hĝ hCg hγ hhull j c₁ θ' hl hz

/-- The statement over `ClauseTR` follows from the one over the corrected bundle. -/
theorem sb2LowerStageChainStatementWP_of_WAP (h : SB2LowerStageChainStatementWAP.{u}) :
    SB2LowerStageChainStatementWP.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h' hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft
  filter_upwards [h κ hκ hκ4 b jumps hb P h' hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft] with ω₀ h₀
  intro c θ hlaunch b' J' h'' hb' hT' hG' hk m hm EL hEL hreg hCl hFa
  exact h₀ c θ hlaunch b' J' h'' hb' hT' hG' hk m hm EL hEL hreg hCl.clauseTW hFa

end InteractingSLE.Theorem14.SB.Mn
