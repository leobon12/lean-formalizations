/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2CfCore
import InteractingSLE.Spec.Supplement.SB2JvHead

/-!
# SB2(2)'s root record (Target 1)

Packet PROVE-SB2-CONDFIN (Target 1; LCMEAN's D32 item). **`sb2LowerRootRecRFStatement`** proves
**`SB2LowerRootRecRFStatement`**: in SB2(2)'s setting, for every measurable, everywhere regular relative family `EL`
with LIFTSET's root facts (D25, `Lk.RootFactsAS`), the record of the relative root is, almost surely under the upper
kernel, the record of a regular driver `Dr₀ relOff` known to the marks after B's stage `relOff`
(`Ms.stageMarks (relOff + 1)`). It is LCMEAN's `Mz.SB2LowerRootRecStatement` with the bundle hypothesis replaced by the
root facts alone, so it serves every bundle that carries them (the corrected bundle `ClauseTW ∧ StageFactsAS ∧
RootFactsAS` of D36 in particular; the `ClauseTR` bundle is false, SB2LIFT §R29.1).

Route (LCMEAN's R16.1 (a)–(d), all proved here): for each B-stage `n`, the root event `RootEv n` (`R` entered by stage
`n`, offset `n`) is decided by B's runs up to `n + 1` (`rootEv_congr`), and on it the root's record is a function of
those runs (`recOf_root_eq`: retained datum, chosen-trace congruence `trOf_congr`, stage facts); off the root event at
the offset the root is the zero root (`Lk.mem_succ_of_not_zeroRoot`, B's walk passes `R`). The runs are frozen under
the conditional laws given the marks (`CondDriverBridge.ae_ae_run_eq_of_le`, regularized family), the root event has a
measurable version on the regular event (`exists_measurableSet_rootEv`), and `exists_rootRec_of_frozen` gives `Dr₀`.

Inputs: Theorems 1.2–1.3 only (B's walk passes `R`: `Mn.rightWalkProperReg_of_thms`, `sb2LowerTailLiftCurve`; the
launch at the offset off a zero root: `Lk.sb2LowerLaunchRelOff`). R48: they appear only as hypotheses (Theorem 1.4).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.SB.Cf

open Supp9B Lx Lu Leaf FlowDilate Sec4 Exist Exist.Staged Exist.StagedLaw Lk Mz Restart

/-- **Named statement (the root record over the root facts)**: in SB2(2)'s setting, for every measurable, everywhere
regular relative family with the root facts (D25), the record of the relative root is, almost surely under the upper
kernel, the record of a regular driver `Dr₀ relOff` known to the marks after B's stage `relOff`. -/
def SB2LowerRootRecRFStatement : Prop :=
  Lf.SB2LowerSetting.{u} fun κ b jumps _ _ _ P _ E u l k ω₀ c b' J' _ =>
    0 < k → ∀ m : ℝ, m = -upperEntry κ b jumps E u l k ω₀ → ∀ EL : ℕ → _ → Drv,
      (∀ j, Measurable (EL j)) → (∀ j ω, IsRegularDriver (EL j ω)) →
      RootFactsAS κ b jumps P E u l k ω₀ c b' J' m EL →
      ∃ Dr₀ : ℕ → _ → Drv, (∀ n, Measurable[Ms.stageMarks κ b jumps E u l k (n + 1)] (Dr₀ n)) ∧
        (∀ n ω, IsRegularDriver (Dr₀ n ω)) ∧
        ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
          recOf ⊤ (EL 0 ω) = recOf ⊤ (Dr₀ (relOff κ (-(Real.pi / 2)) b jumps
            (realMax (upperPrefix κ b jumps E u l k ω₀)) (lowerD b jumps E ω)) ω)

/-- **SB2(2)'s root record** (Target 1), from Theorems 1.2–1.3. -/
theorem sb2LowerRootRecRFStatement (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
    (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0}) : SB2LowerRootRecRFStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft
  set spec := boundaryWalkSpec b jumps (-(Real.pi / 2)) true with hspec
  have hsp : IsBoundaryContinuedProgram (upperSpec u l).2.2 := isBoundaryContinuedProgram_upperSpec hlθ
  have hspl : IsBoundaryContinuedProgram spec.2.2 :=
    isBoundaryContinuedProgram_boundaryWalkSpec b jumps ⟨le_rfl, by linarith [Real.pi_pos]⟩ true
  have hEu := hE _ hsp
  have hEl := hE _ hspl
  have hRl := hER _ hspl
  have hm𝒢 := hEu.2.1 k
  have hR' := WalkLaw.stagedPiecesRegular_regHist hRl
  obtain ⟨M, hMae, hMm, hMp⟩ := hR'.ae_pieceRegular.exists_measurable_mem
  have hrunreg := StagedReg.ae_run_regHist hRl
  have hβex := KernelTower.ae_ae_condExpKernel_of_ae hm𝒢
    (Mn.rightWalkProperReg_of_thms h12 h13 h12₀ h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER)
  have htl := sb2LowerTailLiftCurve h13 κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft
  have hlo := sb2LowerLaunchRelOff h12 h13 h12₀ h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp
    hlθ hL hleft
  filter_upwards [KernelTower.ae_ae_condExpKernel_of_ae hm𝒢 hMae, KernelTower.ae_ae_condExpKernel_of_ae hm𝒢 hrunreg,
    hβex, htl, hlo] with ω₀ hM₀ hrun₀ hβ₀ htl₀ hlo₀
  intro c θ hlaunch b' J' h' hb' hT' hG' _ m hm EL hELm hELr hRF
  set Q := condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀ with hQ
  set R₀ := realMax (upperPrefix κ b jumps E u l k ω₀) with hR₀
  -- B's walk passes `R`
  have hRmemQ : ∀ᵐ ω ∂Q, (R₀ : ℂ) ∈ ExplState.physSet κ b jumps spec (lowerD b jumps E ω) := by
    filter_upwards [hβ₀, htl₀ c θ hlaunch b' J' h' hb' hT' hG' m hm] with ω hβω htlω
    obtain ⟨β₀, hβ, hβ0, hβr⟩ := hβω
    obtain ⟨tL, γ, hγ⟩ := htlω β₀ hβ hβ0 hβr
    rw [← hγ.1]
    have hmem : β₀ tL ∈ range β₀ := mem_range_self tL
    rw [hβr] at hmem
    exact hmem
  have h𝓜 : ∀ n, Ms.stageMarks κ b jumps E u l k (n + 1) ≤ ‹MeasurableSpace Ω› := fun n =>
    (stageMarks_le_marksQ (n + 1)).trans (marksQ_le (k := k) hb hEu hEl (n + 1))
  -- the root events, measurably on the regular event
  have hS : ∀ n, ∃ S : Set Ω, MeasurableSet S ∧ ∀ ω ∈ M,
      (RootEv κ (-(Real.pi / 2)) b jumps R₀ (fun i => StagedReg.regHist spec (E spec) i ω) n ↔ ω ∈ S) :=
    fun n => exists_measurableSet_rootEv hb (-(Real.pi / 2)) (D := StagedReg.regHist spec (E spec))
      (StagedReg.measurable_regHist hEl.1) StagedReg.isRegularDriver_regHist hMm hMp R₀ n
  choose S hSm hSiff using hS
  -- the good event
  set G : Set Ω := {ω | ω ∈ M ∧ (∀ i, ExplState.run κ b jumps spec (fun j => StagedReg.regHist spec (E spec) j ω) i =
      ExplState.run κ b jumps spec (fun j => E spec j ω) i) ∧
    RootFactsAt κ (-(Real.pi / 2)) b jumps (affData 1 m b') (affJumps 1 m J') R₀ c m (lowerD b jumps E ω)
      (fun j => EL j ω) ∧
    (¬ ZeroRoot κ (-(Real.pi / 2)) b jumps R₀ (lowerD b jumps E ω) →
      (wRun κ (-(Real.pi / 2)) b jumps (lowerD b jumps E ω)
        (relOff κ (-(Real.pi / 2)) b jumps R₀ (lowerD b jumps E ω) + 1)).2.2.2.1
          (relOff κ (-(Real.pi / 2)) b jumps R₀ (lowerD b jumps E ω)) ≠ none)} with hGdef
  have hGQ : ∀ᵐ ω ∂Q, ω ∈ G := by
    filter_upwards [hM₀, hrun₀, hRF, hlo₀ c θ hlaunch b' J' h' hb' hT' hG'] with ω h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  have hSG : ∀ ω ∈ G, ∀ n, (ω ∈ S n ↔ RootEv κ (-(Real.pi / 2)) b jumps R₀ (lowerD b jumps E ω) n) :=
    fun ω hω n => by
      rw [← hSiff n ω hω.1]
      exact rootEv_congr R₀ n fun i _ => hω.2.1 i
  -- the regularized runs are frozen under the conditional laws given the marks
  have hfrr : ∀ n, ∀ᵐ ω₁ ∂Q, ∀ᵐ ω ∂(condExpKernel Q (Ms.stageMarks κ b jumps E u l k (n + 1)) ω₁), ∀ i, i ≤ n + 1 →
      ExplState.run κ b jumps spec (fun j => StagedReg.regHist spec (E spec) j ω) i =
        ExplState.run κ b jumps spec (fun j => StagedReg.regHist spec (E spec) j ω₁) i := by
    intro n
    have hi : ∀ i, ∀ᵐ ω₁ ∂Q, ∀ᵐ ω ∂(condExpKernel Q (Ms.stageMarks κ b jumps E u l k (n + 1)) ω₁), i ≤ n + 1 →
        ExplState.run κ b jumps spec (fun j => StagedReg.regHist spec (E spec) j ω) i =
          ExplState.run κ b jumps spec (fun j => StagedReg.regHist spec (E spec) j ω₁) i := by
      intro i
      by_cases hin : i ≤ n + 1
      · filter_upwards [CondDriverBridge.ae_ae_run_eq_of_le (P := Q) (κ := κ) (b := b) (jumps := jumps) spec
          (E := StagedReg.regHist spec (E spec)) (k := i) (fun j _ ω => StagedReg.isRegularDriver_regHist j ω)
          (h𝓜 n) ((pastSigma_mono spec _ hin).trans le_sup_right)] with ω₁ h₁
        filter_upwards [h₁] with ω hω _
        exact hω
      · exact Eventually.of_forall fun _ => Eventually.of_forall fun _ h => absurd h hin
    filter_upwards [ae_all_iff.2 hi] with ω₁ h₁
    filter_upwards [ae_all_iff.2 h₁] with ω hω i hi'
    exact hω i hi'
  -- the masked record is frozen
  have hfr : ∀ n, ∀ᵐ ω₁ ∂Q, ∀ᵐ ω ∂(condExpKernel Q (Ms.stageMarks κ b jumps E u l k (n + 1)) ω₁),
      (ω ∈ S n ↔ ω₁ ∈ S n) ∧ (ω₁ ∈ S n → recOf ⊤ (EL 0 ω) = recOf ⊤ (EL 0 ω₁)) := by
    intro n
    filter_upwards [hGQ, KernelTower.ae_ae_condExpKernel_of_ae (P := Q) (h𝓜 n) hGQ, hfrr n] with ω₁ hG₁ hGκ hfκ
    filter_upwards [hGκ, hfκ] with ω hGω hrω
    have hrunE : ∀ i ≤ n + 1, wRun κ (-(Real.pi / 2)) b jumps (lowerD b jumps E ω₁) i =
        wRun κ (-(Real.pi / 2)) b jumps (lowerD b jumps E ω) i := fun i hi =>
      ((hG₁.2.1 i).symm.trans (hrω i hi).symm).trans (hGω.2.1 i)
    refine ⟨?_, fun h₁ => ?_⟩
    · rw [hSG ω hGω n, hSG ω₁ hG₁ n]
      exact (rootEv_congr R₀ n hrunE).symm
    · rw [hSG ω₁ hG₁ n] at h₁
      exact (recOf_root_eq hrunE h₁ hG₁.2.2.2 hG₁.2.2.1 hGω.2.2.1 (hELr 0 ω₁) (hELr 0 ω)).symm
  -- off the root event at the offset, the root is the zero root
  have hoff : ∀ᵐ ω ∂Q, ω ∉ S (relOff κ (-(Real.pi / 2)) b jumps R₀ (lowerD b jumps E ω)) → EL 0 ω = Lk.zeroDrv := by
    filter_upwards [hGQ, hRmemQ] with ω hGω hRω hnS
    have hnent : ¬ Ent κ (-(Real.pi / 2)) b jumps R₀ (lowerD b jumps E ω)
        (relOff κ (-(Real.pi / 2)) b jumps R₀ (lowerD b jumps E ω)) := fun he =>
      hnS ((hSG ω hGω _).2 ⟨he, rfl⟩)
    have hZ : ZeroRoot κ (-(Real.pi / 2)) b jumps R₀ (lowerD b jumps E ω) := by
      by_contra hZ
      exact hnent (mem_succ_of_not_zeroRoot hRω hZ)
    exact hGω.2.2.1.1 (Or.inl hZ)
  have hc : ∀ᵐ ω ∂Q, ContinuousOn (EL 0 ω).1 {s | (s : ℝ≥0∞) ≤ min ⊤ (EL 0 ω).2} := by
    filter_upwards [hGQ] with ω hGω
    exact continuousOn_root hGω.2.2.1
  exact exists_rootRec_of_frozen (Q := Q) (𝓜 := fun n => Ms.stageMarks κ b jumps E u l k (n + 1)) (hELm 0)
    (hELr 0) (off := fun ω => relOff κ (-(Real.pi / 2)) b jumps R₀ (lowerD b jumps E ω)) hSm hfr hoff hc

end InteractingSLE.Theorem14.SB.Cf
