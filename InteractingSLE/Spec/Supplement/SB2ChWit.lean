/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2CgTop

/-!
# SB2(2)'s root: from one witness matched at the positive roots to every witness

Packet PROVE-SB2-CONDFIN (round 3, D39). At the relative root (stage `0`) the relative past is trivial, so no marks
are needed in the final step: if one witness `(β₀, Y₀)` of the stage-`0` law under the upper kernel is matched by the
root at its positive-lifetime samples, then every witness is (**`sb2LowerRelPosWRootStatement_of_det`**). The
zero-lifetime samples are matched by any witness (`Cf.ae_codeMatch_relRoot_zeroW`), so `(β₀, Y₀)` is matched on the
whole launch event, and LCMEAN's code-match core `Mx.ae_codeMatch_of_lawCode` (with the σ-algebra `pastSigma … 0` of
the stage itself) transfers the match to every witness.

* **`SB2LowerRootDetWStatement`**: the root determination in witness form (the statement the root package proves);
* **`sb2LowerRelPosWRootStatement_of_det`**: `Cf.SB2LowerRelPosWRootStatement` from it (Theorems 1.2–1.3).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
open QuantumZipper (H chiC)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Ch

open Supp9B Lx Lu Leaf FlowDilate Sec4 Exist Exist.Staged Exist.StagedLaw Lk Mn Mq Restart

/-- **The root determination in witness form**: for every relative family with the corrected bundle, some witness of
the relative stage-`0` law under the upper kernel is matched by the root at its positive-lifetime samples. -/
def SB2LowerRootDetWStatement (h12p : Theorem12ParamStatement.{u}) : Prop :=
  Lf.SB2LowerSetting.{u} fun κ b jumps _ _ _ P _ E u l k ω₀ c b' J' h' =>
    0 < k → ∀ hκ : 0 < κ, ∀ m : ℝ, m = -upperEntry κ b jumps E u l k ω₀ → ∀ EL : ℕ → _ → Drv,
      (∀ j, Measurable (EL j)) → (∀ j ω, IsRegularDriver (EL j ω)) →
      Cf.RelDataClauseW κ b jumps P E u l k ω₀ c b' J' m EL →
      ∃ (β₀ : _ → BoundaryWord) (Y₀ : _ → DistOn upperHalfPlaneOpens),
        IsStageWitness κ (affData 1 m b') (affJumps 1 m J')
          (condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀)
          (fun ω => affField m one_pos (h' ω)) (relLowerSpec b' J' m) EL 0 β₀ Y₀ ∧
        ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
          (EL 0 ω).2 ≠ 0 →
          IsDriverCodeMatch (driverCode h12p hκ (-(Real.pi / 2)) (β₀ ω, Y₀ ω)) (fun t => (EL 0 ω).1 t) (EL 0 ω).2

/-- **The root's code match for every witness from one matched witness** (Theorems 1.2–1.3). -/
theorem sb2LowerRelPosWRootStatement_of_det (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
    (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0})
    (hdet : SB2LowerRootDetWStatement.{u} (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13)) :
    Cf.SB2LowerRelPosWRootStatement.{u} (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13) := by
  set h12p := Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13 with hh12p
  have hPR := Mr.rightWalkProperRegStatement_of_thms h12 h13 h12₀ h13₀
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft
  have hsp : IsBoundaryContinuedProgram (upperSpec u l).2.2 := isBoundaryContinuedProgram_upperSpec hlθ
  have hm𝒢 := (hE _ hsp).2.1 k
  have hβP := hPR κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER
  filter_upwards [hdet κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerTailLiftCurve h13 κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    KernelTower.ae_ae_condExpKernel_of_ae hm𝒢 hβP] with ω₀ hdet₀ hC₀ hβ₀
  intro c θ hlaunch b' J' h' hb' hT' hG' hk hκ' m hm EL hELm hELr hcl β Y hW
  obtain ⟨β₀, Y₀, hW₀, hpos₀⟩ := hdet₀ c θ hlaunch b' J' h' hb' hT' hG' hk hκ' m hm EL hELm hELr hcl
  set Q := condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀ with hQ
  have hb'' := isPiecewiseConstantBoundaryData_affData (m := m) one_pos hb'
  have h𝒢 : pastSigma κ (affData 1 m b') (affJumps 1 m J') (relLowerSpec b' J' m) EL 0 ≤ ‹MeasurableSpace Ω› := by
    rw [pastSigma_eq_comap]
    exact (measurable_pastMap runMeasStatement hb'' (relLowerSpec b' J' m) (fun j _ => hELm j)
      (fun j _ => hELr j) 0 le_rfl).comap_le
  have hlaunch0 : ∀ ω, (ExplState.run κ (affData 1 m b') (affJumps 1 m J') (relLowerSpec b' J' m)
      (fun i => EL i ω) (0 + 1)).2.2.2.1 0 ≠ none := fun ω => by
    rw [relRun_one_launches κ b' J' m EL ω]
    exact Option.some_ne_none _
  have hzero := Cf.ae_codeMatch_relRoot_zeroW h12p h13 hκ' hb' hG' hELm hELr hcl.1 hβ₀
    (hC₀ c θ hlaunch b' J' h' hb' hT' hG' m hm) hW₀
  have hmain := Mx.ae_codeMatch_of_lawCode (P := Q) h12p h13 hκ' (-(Real.pi / 2)) hb'' hELm hELr
    ⟨_, h𝒢⟩ (LocalSets.le_aeSigma _ Q) ((measurable_affField one_pos).comp hG'.1) hW₀.1 (G := univ)
    (by
      filter_upwards [hW₀.2.2.2] with ω₁ h1 _
      exact h1 (hlaunch0 ω₁))
    (by
      filter_upwards [hpos₀, hzero] with ω h1 h2 _
      refine ⟨mem_univ ω, ?_⟩
      by_cases hz : (EL 0 ω).2 = 0
      · exact h2 hz
      · exact h1 hz)
    (by
      filter_upwards [KernelTower.ae_ae_condExpKernel_of_ae h𝒢 hW₀.2.2.1] with ω₁ h1 _
      filter_upwards [h1] with ω hω
      exact (hω (hlaunch0 ω)).2.2)
    hW
  filter_upwards [hmain] with ω h1 _
  exact h1 (hlaunch0 ω)

end InteractingSLE.Theorem14.SB.Ch
