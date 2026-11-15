/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2NeThr

/-!
# F2b′ (tail stages, joint `A₂`) PROVED from Theorems 1.2–1.3

Packet PROVE-AUX61-NOJUMP (round 22). **`sb2LowerStageVersionStatement5`**: `Nd.SB2LowerStageVersionStatement5`
from Theorems 1.2–1.3 (at universes `u` and `0`), with no named input.

* at a flow instruction `ℓ`: the stage objects (`Nc.exists_stageObj`), the stop inputs (`Ne.exists_stopIn`: D34's
  clause, B's physical piece on the original real line, the relative facts), the versions
  (`Nd.StopIn.versionS`), and the clauses (`ae_cover`, `ae_V_le_thr`, `ae_thr_le`);
* at any other `ℓ` the stage event is empty (`Nc.stageEvent_eq_empty`) and the trivial version works
  (`Nc.trivVersionS`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC fwdHull)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Nd

open Restart Restart.DomainMarkov Restart.DomainMarkov.K2 Exist Exist.Staged Exist.StagedLaw WalkSide LocalSets
  WholeField Supp8.Q3Stop Sec7.PocketTraversal Lv Supp9B Lx Lk Mf Ms Nb Nc

/-- **F2b′ at the tail stages with the joint second set, PROVED** (Theorems 1.2–1.3). -/
theorem sb2LowerStageVersionStatement5 (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
    (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0}) : SB2LowerStageVersionStatement5.{u} := by
  intro κ hκ hκ4 b jumps hb Ω mΩ hSB P hP h hh W' ζ' hcf hζ' E hE hER u l k hu hlpair hlθ hleftW hleft ℓ 𝓖 A₁ A₂
    h𝓖 hA β₁ types hβm hsorted htypes u₀ hu₀ hmean hheight
  classical
  by_cases hflow : ℓ < (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2.length ∧
      (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2[ℓ]? = some (Sum.inl (-(Real.pi / 2), ⊤))
  · obtain ⟨hℓ, hwℓ⟩ := hflow
    obtain ⟨S⟩ := exists_stageObj h12 h13 h12₀ h13₀ hκ hκ4 hb hh hcf hζ' hE hER hu hlθ k ℓ hleft hℓ hwℓ hu₀
    have h𝓖' : ∀ t, 𝓖 t = lineSigmaT κ b jumps E u l k ℓ t := h𝓖
    have h0 : lineSigma0 κ b jumps E u l k ℓ ≤ mΩ :=
      (lineSigma0_le_T hb hE hER hℓ hwℓ 0).trans (lineSigmaT_le hb hE hER hlθ hℓ hwℓ 0)
    have hC0 : lineC0 P κ b jumps E u l k ℓ ≤ lineFiltC P 𝓖 0 := by
      show mΩ ⊓ aeSigma (lineSigma0 κ b jumps E u l k ℓ) P ≤ mΩ ⊓ aeSigma (𝓖 0) P
      rw [h𝓖' 0]
    have h0C : lineSigma0 κ b jumps E u l k ℓ ≤ lineC0 P κ b jumps E u l k ℓ :=
      le_inf h0 fun s hs => ⟨s, hs, EventuallyEq.rfl⟩
    have hA0 : ∀ᵐ ω ∂P, A₁ 0 ω = stageFill κ b jumps E u l k ℓ ω := (hA 0).mono fun ω hω => hω.1
    refine ⟨S.K, S.x₀, bPc κ b jumps E ℓ, fun _ => 0, fun ω => Sec7.Lemma71C.capLife (S.ρM ω), S.F,
      fun n k' => hC0 _ (S.hK n k'), S.hKc, S.hKp, ?_, S.hx₀.mono hC0 le_rfl, hC0 _ (h0C _ S.hF), S.hFae, ?_⟩
    · filter_upwards [S.hEgae, hA0] with ω hEg hAω hF
      have hg := S.good ω (hEg hF)
      rw [hg.fill, ← hg.stfill, hAω]
    · intro hcover
      obtain ⟨T, rfl, hcwe, hend⟩ := Ne.exists_stopIn h13₀ hκ hκ4 hb hh hcf hζ' hE hER hlθ hℓ hwℓ S hA0 hβm
        htypes hheight hcover
      exact ⟨T.versionS hE hER hlθ hℓ hwℓ h𝓖' hA hcwe types, fun t => T.ae_cover t,
        fun m w _ => T.ae_V_le_thr hcwe m w, fun w _ Wc hWc => T.ae_thr_le hend hcwe w Wc hWc⟩
  · have hSE := stageEvent_eq_empty (κ := κ) E u l k ℓ hflow
    refine ⟨fun _ => ∅, fun _ => 0, fun _ _ => 0, fun _ => 0, fun _ => 0, ∅, fun n k' => by simp,
      fun _ => isCompact_empty, fun _ => by rw [empty_union]; exact Mf.isPreconnected_lowerHalf,
      Eventually.of_forall fun _ h => absurd h (notMem_empty _),
      (measurable_const : Measurable[lineFiltC P 𝓖 0] fun _ : Ω => (0 : ℝ)),
      @MeasurableSet.empty Ω (lineFiltC P 𝓖 0),
      Eventually.of_forall fun ω => ?_, fun _ => ⟨trivVersionS, ?_, ?_, ?_⟩⟩
    · rw [hSE]
      simp
    · exact fun _ => Eventually.of_forall fun _ h => absurd h (notMem_empty _)
    · exact fun _ _ _ => Eventually.of_forall fun _ h => absurd h.1 (notMem_empty _)
    · exact fun _ _ _ _ => Eventually.of_forall fun _ h => absurd h notMem_seedCell_empty

end InteractingSLE.Theorem14.SB.Nd
