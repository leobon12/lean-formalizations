/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2NfRVerT
import InteractingSLE.Spec.Supplement.SB2NfStmt9F
import InteractingSLE.Spec.Supplement.SB2YkRel

/-!
# F2b′'s root variant from Theorems 1.2–1.3: 9F and 9E (D79)

Packet PROVE-AUX61-NOJUMP (round 22, D79).

* **`sb2LowerRootVersionStatement9F_of_rel`**: `SB2LowerRootVersionStatement9F` from Theorems 1.2–1.3 and the root's
  relative facts (`RootRelFactsStatement`); the versions are `RootStop.versionST` with `tL = Na.rootEntry`
  (`RootObj.ae_rootEntry_eq`); F3's mean premise is not used;
* **`sb2LowerRootVersionStatement9F`**, **`sb2LowerRootVersionStatement9E`**: both from Theorems 1.2–1.3 alone, with
  PROVE-T14-SB2LIFT's `Sx.rootRelFactsStatement` (D77).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar chiC fwdHull)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Nf

open Restart Restart.DomainMarkov Restart.DomainMarkov.K2 Exist Exist.Staged Exist.StagedLaw WalkSide LocalSets
  WholeField Supp8.Q3Stop Sec7.PocketTraversal Lv Supp9B Lx Lk Mf Ms Nb Nc Nd Vs Supp8.GB6 Supp8.GB6.HullId

/-- **9F from Theorems 1.2–1.3 and the root's relative facts.** -/
theorem sb2LowerRootVersionStatement9F_of_rel (hrel : RootRelFactsStatement.{u})
    (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
    (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0}) : SB2LowerRootVersionStatement9F.{u} := by
  intro κ hκ hκ4 b jumps hb Ω mΩ hSB P hP h hh W' ζ' hcf hζ' E hE hER u l k hu hlpair hlθ hleftW hleft ℓ 𝓖 A₁ A₂
    h𝓖 hA β₁ types hβm hsorted htypes u₀ hu₀ hmean hheight
  classical
  by_cases hflow : ℓ < (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2.length ∧
      (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2[ℓ]? = some (Sum.inl (-(Real.pi / 2), ⊤))
  · obtain ⟨hℓ, hwℓ⟩ := hflow
    obtain ⟨S⟩ := exists_rootObj h12 h13 h12₀ h13₀ hκ hκ4 hb hh hcf hζ' hE hER hu hlθ k ℓ hleft hℓ hwℓ hu₀
    have h𝓖' : ∀ t, 𝓖 t = lineSigmaT κ b jumps E u l k ℓ t := h𝓖
    have h0 : lineSigma0 κ b jumps E u l k ℓ ≤ mΩ :=
      (lineSigma0_le_T hb hE hER hℓ hwℓ 0).trans (lineSigmaT_le hb hE hER hlθ hℓ hwℓ 0)
    have hC0 : lineC0 P κ b jumps E u l k ℓ ≤ lineFiltC P 𝓖 0 := by
      show mΩ ⊓ aeSigma (lineSigma0 κ b jumps E u l k ℓ) P ≤ mΩ ⊓ aeSigma (𝓖 0) P
      rw [h𝓖' 0]
    have h0C : lineSigma0 κ b jumps E u l k ℓ ≤ lineC0 P κ b jumps E u l k ℓ :=
      le_inf h0 fun s hs => ⟨s, hs, EventuallyEq.rfl⟩
    have hA0 : ∀ᵐ ω ∂P, A₁ 0 ω = stageFill κ b jumps E u l k ℓ ω := (hA 0).mono fun ω hω => hω.1
    refine ⟨S.K, S.x₀, bPc κ b jumps E ℓ, fun ω => Sec7.Lemma71C.capLife (S.ρM ω), S.FB, S.Eg,
      fun n k' => hC0 _ (S.hK n k'), S.hKc, S.hKp, ?_, S.hx₀.mono hC0 le_rfl, hC0 _ (h0C _ S.hFB),
      fun ω => rfl, Eventually.of_forall fun ω hω => (S.geo hω).entry,
      Eventually.of_forall fun ω hω => (S.good₀ ω hω.1).x0, S.hFBae, S.ae_mem_Eg_iff,
      Eventually.of_forall fun ω hω => S.hEg₀FB hω.1, ?_⟩
    · filter_upwards [S.hEg₀ae, hA0] with ω hEg hAω hF
      have hg := S.good₀ ω (hEg hF)
      rw [hg.fill, ← hg.stfill, hAω]
    · intro hcover
      obtain ⟨T, rfl, hcwe, htyp, hend⟩ := exists_rootStop hrel h13₀ hκ hκ4 hb hh hcf hζ' hE hER hlθ hℓ hwℓ S hA0
        hβm htypes hheight hcover
      refine ⟨T.versionST hE hER hlθ hℓ hwℓ h𝓖' hA hcwe types T.S.ae_rootEntry_eq, fun m => ?_, ?_,
        fun t => T.ae_cover t, fun m w _ => T.ae_V_le_thr hcwe m w,
        fun w _ Wc hWc => T.toG.ae_thr_le hend hcwe w Wc hWc⟩
      · refine Eventually.of_forall fun ω hω t ht => T.S.a_eq_zero_of_le t ?_
        have hfin : Nd.entrR κ b jumps E u l k ℓ ω ≠ ⊤ := (T.S.entr_lt hω).ne_top
        unfold rSh
        rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal hfin]
        exact ht
      · refine Eventually.of_forall fun ω hω => ?_
        have hfin : Nd.entrR κ b jumps E u l k ℓ ω ≠ ⊤ := (T.S.entr_lt hω).ne_top
        rw [← tL_eq_rootEntry (T.S.Eg_subset_rootEv hω), ENNReal.coe_toNNReal hfin]
  · have hSE := stageEvent_eq_empty (κ := κ) E u l k ℓ hflow
    have hR : Ne.rootEv κ b jumps E u l k ℓ = ∅ :=
      eq_empty_of_forall_notMem fun ω hω => by have := hω.1; rw [hSE] at this; exact this
    refine ⟨fun _ => ∅, fun _ => 0, bPc κ b jumps E ℓ, fun _ => 0, ∅, ∅, fun n k' => by simp,
      fun _ => isCompact_empty, fun _ => by rw [empty_union]; exact Mf.isPreconnected_lowerHalf,
      Eventually.of_forall fun _ h => absurd h (notMem_empty _),
      (measurable_const : Measurable[lineFiltC P 𝓖 0] fun _ : Ω => (0 : ℝ)),
      @MeasurableSet.empty Ω (lineFiltC P 𝓖 0), fun _ => rfl,
      Eventually.of_forall fun _ h => absurd h (notMem_empty _),
      Eventually.of_forall fun _ h => absurd h (notMem_empty _),
      Eventually.of_forall fun ω => ?_, Eventually.of_forall fun ω => ?_,
      Eventually.of_forall fun _ h => absurd h (notMem_empty _), fun _ => ⟨trivRootVersionS, ?_, ?_, ?_, ?_, ?_⟩⟩
    · rw [hSE]; simp
    · rw [hR]
    · exact fun _ => Eventually.of_forall fun _ h => absurd h (notMem_empty _)
    · exact Eventually.of_forall fun _ h => absurd h (notMem_empty _)
    · exact fun _ => Eventually.of_forall fun _ h => absurd h (notMem_empty _)
    · exact fun _ _ _ => Eventually.of_forall fun _ h => absurd h.1 (notMem_empty _)
    · exact fun _ _ _ _ => Eventually.of_forall fun _ h => absurd h Nc.notMem_seedCell_empty

/-- **9F, PROVED** (Theorems 1.2–1.3). -/
theorem sb2LowerRootVersionStatement9F (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
    (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0}) : SB2LowerRootVersionStatement9F.{u} :=
  sb2LowerRootVersionStatement9F_of_rel Sx.rootRelFactsStatement h12 h13 h12₀ h13₀

/-- **9E, PROVED** (Theorems 1.2–1.3). -/
theorem sb2LowerRootVersionStatement9E (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
    (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0}) : Ne.SB2LowerRootVersionStatement9E.{u} :=
  sb2LowerRootVersionStatement9E_of_rel Sx.rootRelFactsStatement h12 h13 h12₀ h13₀

end InteractingSLE.Theorem14.SB.Nf
