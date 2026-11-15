/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2BvSrc
import InteractingSLE.Spec.Supplement.GW2BuAlive
import InteractingSLE.Spec.Supplement.GW2SdeWire
import InteractingSLE.Spec.Supplement.GW2BsDeath

/-!
# The instance layer at the kernel samples

Packet PROVE-GW2-BUF (round 19). The near family is chosen at the conditioning sample `ω₀` from the near base word
`pkgNb ω₀`. The near stop reads the record of the kernel sample `ξ`. They match because:

* `outer_ctrl_of_nearShapeBot`: the rightward family has its outermost labels controlled;
* **`ae_ae_condExpKernel_eq_of_comap_le`**: a map retained up to null sets (`comap f ≤ aeSigma 𝒢 P`), with values in
  a second-countable `T₁` space, is fixed by the conditional law;
* **`ae_slotRec_eq_ref`**: almost surely on the alive event, every slot of the final version family that passes the
  history's clock has the reference prefix record, so its base word is `pkgNb`;
* **`ae_kernel_pkgNb_eq`**: for almost every alive `ω₀`, `pkgNb ξ = pkgNb ω₀` for almost every kernel sample `ξ`. The
  slots' prefix records are retained (`GoodX.prefix_retained`), and the slots pass the clock eventually at both
  samples.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Bh

open Restart Exist Exist.StagedLaw GW2TipSystem GW2TipSystem.RootC24 GW2Rz GW2Rd GW2Rv GW2Sde GW2Sdh GW2Sdx
  GW2Sdy GW2Sdo

/-- **The rightward family has its outermost labels controlled.** -/
theorem outer_ctrl_of_nearShapeBot {κ : ℝ} {f : RootN4.NearCrossingFamily.{u} κ} {s : ℝ≥0} {flip : Bool}
    {c : BoundaryWord} (hsh : famShapeB f = nearShapeBot s flip c) (hbot : NearStructBot κ s flip c) :
    f.mL ≤ f.nL - 1 ∧ f.mR ≤ f.nR - 1 := by
  simp only [famShapeB, nearShapeBot, Prod.mk.injEq] at hsh
  obtain ⟨h1, h2, h3, h4, -⟩ := hsh
  exact ⟨by rw [h1, h3], by rw [h2, h4]; exact cutR_le _ hbot.xp⟩

/-- **A map retained up to null sets is fixed by the conditional law.** -/
theorem ae_ae_condExpKernel_eq_of_comap_le {Ω E : Type*} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] [TopologicalSpace E]
    [SecondCountableTopology E] [T1Space E] [MeasurableSpace E] [OpensMeasurableSpace E] (h𝒢 : 𝒢 ≤ mΩ)
    {f : Ω → E} (hc : MeasurableSpace.comap f inferInstance ≤ LocalSets.aeSigma 𝒢 P) :
    ∀ᵐ ω₀ ∂P, ∀ᵐ ξ ∂(condExpKernel P 𝒢 ω₀), f ξ = f ω₀ := by
  set 𝓑 := TopologicalSpace.countableBasis E with h𝓑
  have h𝓑c : 𝓑.Countable := TopologicalSpace.countable_countableBasis E
  have h𝓑o : ∀ U ∈ 𝓑, IsOpen U := fun U hU => TopologicalSpace.isOpen_of_mem_countableBasis hU
  have hU : ∀ᵐ ω₀ ∂P, ∀ U ∈ 𝓑, f ω₀ ∉ U → condExpKernel P 𝒢 ω₀ (f ⁻¹' U) = 0 := by
    rw [ae_ball_iff h𝓑c]
    intro U hU
    obtain ⟨J, hJm, hJe⟩ : ∃ J, MeasurableSet[𝒢] J ∧ f ⁻¹' U =ᵐ[P] J :=
      hc _ ⟨U, (h𝓑o U hU).measurableSet, rfl⟩
    have hset : ∀ᵐ ω ∂P, (ω ∈ f ⁻¹' U ↔ ω ∈ J) := Filter.eventuallyEqSet_iff.1 hJe
    filter_upwards [Sec7.Aux122Disint.ae_condExpKernel_apply_eq_indicator h𝒢 hJm, hset,
      Sec7.Aux122Disint.ae_ae_condExpKernel h𝒢 hset] with ω₀ hind hω₀ hker hn
    have hJ0 : ω₀ ∉ J := fun h => hn (hω₀.2 h)
    rw [Set.indicator_of_notMem hJ0] at hind
    rw [measure_congr (Filter.eventuallyEqSet_iff.2 hker)]
    exact hind
  filter_upwards [hU] with ω₀ hω₀
  have hsub : {ω | ¬ f ω = f ω₀} ⊆ ⋃ U ∈ {U ∈ 𝓑 | f ω₀ ∉ U}, f ⁻¹' U := by
    intro ω hω
    obtain ⟨U, hU𝓑, hyU, hUsub⟩ := (TopologicalSpace.isBasis_countableBasis E).exists_subset_of_mem_open
      (show f ω ∈ ({f ω₀}ᶜ : Set E) from hω) isOpen_compl_singleton
    exact mem_biUnion ⟨hU𝓑, fun h => hUsub h rfl⟩ hyU
  rw [ae_iff]
  exact measure_mono_null hsub
    ((measure_biUnion_null_iff (h𝓑c.mono (sep_subset _ _))).2 fun U hU => hω₀ U hU.1 hU.2)

variable (h13 : Exist.Theorem13Statement.{u}) (h12 : Exist.Theorem12Statement.{u})

section Slots

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
  (l : List (EntryIdx c.Θ c.Q))

/-- **Slots passing the clock have the reference prefix record** (almost surely on the alive event). -/
theorem ae_slotRec_eq_ref (gap : RootCv.GapFamily.{u}) (hg : GoodRoot c r) :
    ∀ᵐ ξ ∂c.P, ξ ∈ ((GW2Sdz.J32S gap Ω c).experiment r).data.alive ((GW2Sdz.J32S gap Ω c).G r) l →
      ∀ a j : ℕ, ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (RootJ31.historyTime c r l) ξ) <
          (schedVerXDeathFamily h13 Ω c r l a).V j ξ →
        stgPreRecX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a)
            ((schedVerXDeathFamily h13 Ω c r l a).V j) (RootJ31.historyTime c r l)
            ((schedVerXDeathFamily h13 Ω c r l a).R j) ξ = refPre h13 Ω c r l ξ := by
  classical
  obtain ⟨hx, hs⟩ := hg
  set T := RootJ31.historyTime c r l with hTdef
  have hpair : ∀ᵐ ω ∂c.P, ∀ p q : ℕ × ℕ, cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s →
      ((T : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l p.1) c.α ω ∧
        ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l p.1) T ω) <
          (schedVerXDeathFamily h13 Ω c r l p.1).V p.2 ω) →
      ((T : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l q.1) c.α ω ∧
        ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l q.1) T ω) <
          (schedVerXDeathFamily h13 Ω c r l q.1).V q.2 ω) →
      stgPreRecX (rootPt r.1) c.s c.W c.ζ (schedW c r l p.1) (schedGTX h13 c r l p.1)
          ((schedVerXDeathFamily h13 Ω c r l p.1).V p.2) T ((schedVerXDeathFamily h13 Ω c r l p.1).R p.2) ω =
        stgPreRecX (rootPt r.1) c.s c.W c.ζ (schedW c r l q.1) (schedGTX h13 c r l q.1)
          ((schedVerXDeathFamily h13 Ω c r l q.1).V q.2) T ((schedVerXDeathFamily h13 Ω c r l q.1).R q.2) ω :=
    ae_all_iff.2 fun p => ae_all_iff.2 fun q =>
      GW2Sdo.ae_stgPreRecX_sched_eq h13 c r l p.1 q.1 hs hx ((schedVerXDeathFamily h13 Ω c r l p.1).isA hx p.2).1.1
        ((schedVerXDeathFamily h13 Ω c r l q.1).isA hx q.2).1.1
  filter_upwards [hpair, GW2Ru.ae_alive_goodEvent_scaled h13 gap c r] with ξ hpξ hgoodEv halive a j hslot
  obtain ⟨hcf, hcon⟩ := hgoodEv l halive
  have hex0 : ∃ p : ℕ, ξ ∈ covEv h13 c r l (Nat.unpair p).1 (Nat.unpair p).2 :=
    ⟨Nat.pair a j, by simp only [Nat.unpair_pair]; exact hslot⟩
  simp only [refPre, hex0, ↓reduceDIte]
  exact hpξ (a, j) ((Nat.unpair (Nat.find hex0)).1, (Nat.unpair (Nat.find hex0)).2) hcf ⟨hcon a, hslot⟩
    ⟨hcon _, Nat.find_spec hex0⟩

/-- **The base word of a final slot is retained up to null sets.** -/
theorem comap_wordD_slot_le (hI : InstInputsX h13 (pkgVerF h13 h12) (pkgCh h13 h12 cwSrc))
    (hTO : HistOrdered c r l) (hg : GoodRoot c r) (a m : ℕ) :
    MeasurableSpace.comap (fun ξ => wordD c r l
        ((instX h13 (pkgVerF h13 h12) (pkgCh h13 h12 cwSrc) Ω c r l a m hg.1).srecX c r l (rootPt r.1) ξ))
      inferInstance ≤ LocalSets.aeSigma (c.sigma r l) c.P := by
  have hgood := hI.goodX hTO hg a m
  have h1 : MeasurableSpace.comap ((instX h13 (pkgVerF h13 h12) (pkgCh h13 h12 cwSrc) Ω c r l a m hg.1).srecX c r l
      (rootPt r.1)) inferInstance ≤ LocalSets.aeSigma (c.sigma r l) c.P := by
    change MeasurableSpace.comap (augRec (stageEncRec c r l) (stgPreRecX (rootPt r.1) c.s c.W c.ζ
      (schedW c r l a) (schedGTX h13 c r l a) ((pkgVerF h13 h12 Ω c r l a).V m) (RootJ31.historyTime c r l)
      ((pkgVerF h13 h12 Ω c r l a).R m))) inferInstance ≤ _
    rw [GW2Sde.comap_augRec]
    exact sup_le ((GW2Rd.comap_stageEncRec_sigma c r l).le.trans (LocalSets.le_aeSigma _ _))
      hgood.prefix_retained
  have h2 := (measurable_wordD c r l).comap_le
  calc MeasurableSpace.comap (fun ξ => wordD c r l
        ((instX h13 (pkgVerF h13 h12) (pkgCh h13 h12 cwSrc) Ω c r l a m hg.1).srecX c r l (rootPt r.1) ξ))
        inferInstance
      = MeasurableSpace.comap ((instX h13 (pkgVerF h13 h12) (pkgCh h13 h12 cwSrc) Ω c r l a m hg.1).srecX c r l
          (rootPt r.1)) (MeasurableSpace.comap (wordD c r l) inferInstance) := by
        rw [MeasurableSpace.comap_comp]
        rfl
    _ ≤ MeasurableSpace.comap ((instX h13 (pkgVerF h13 h12) (pkgCh h13 h12 cwSrc) Ω c r l a m hg.1).srecX c r l
          (rootPt r.1)) inferInstance := MeasurableSpace.comap_mono h2
    _ ≤ _ := h1

/-- **The near base word is fixed by the conditional law** (almost every alive conditioning sample). -/
theorem ae_kernel_pkgNb_eq (hI : InstInputsX h13 (pkgVerF h13 h12) (pkgCh h13 h12 cwSrc)) :
    ∀ᵐ ω₀ ∂c.P, ω₀ ∈ ((GW2Sdz.J32S GW2Sdq.gapFam Ω c).experiment r).data.alive
        ((GW2Sdz.J32S GW2Sdq.gapFam Ω c).G r) l →
      ∀ᵐ ξ ∂condExpKernel c.P (c.sigma r l) ω₀, pkgNb h13 cwSrc Ω c r l ξ = pkgNb h13 cwSrc Ω c r l ω₀ := by
  by_cases hg : GoodRoot c r
  swap
  · filter_upwards [GW2Sds.ae_goodRoot_of_alive h13 c r l] with ω hω halive
    exact absurd (hω (GW2Sdz.alive_scaled_subset GW2Sdq.gapFam Ω c r l halive)) hg
  by_cases hTO : HistOrdered c r l
  swap
  · exact Eventually.of_forall fun ω halive => absurd
      (RootJ32.timeOrdered_historyProgram_of_alive c r l ω (GW2Sdz.alive_scaled_subset GW2Sdq.gapFam Ω c r l halive))
      hTO
  obtain ⟨hx, hs⟩ := hg
  -- the slots passing the clock read `pkgNb`
  have hslot : ∀ᵐ ξ ∂c.P, ξ ∈ ((GW2Sdz.J32S GW2Sdq.gapFam Ω c).experiment r).data.alive
        ((GW2Sdz.J32S GW2Sdq.gapFam Ω c).G r) l →
      ∀ᶠ m in atTop, wordD c r l
          ((instX h13 (pkgVerF h13 h12) (pkgCh h13 h12 cwSrc) Ω c r l 0 m hx).srecX c r l (rootPt r.1) ξ) =
        pkgNb h13 cwSrc Ω c r l ξ := by
    filter_upwards [ae_slotRec_eq_ref h13 c r l GW2Sdq.gapFam ⟨hx, hs⟩,
      GW2Sdt.hcov_death h13 Ω c r l 0 ⟨hx, hs⟩, GW2Ru.ae_alive_goodEvent_scaled h13 GW2Sdq.gapFam c r,
      ae_eventually_cov_all h13 (psiGoodFam h13 h12) Ω c r l hx] with ξ href hcov hgoodEv hcovm halive
    have halive32 := GW2Sdz.alive_scaled_subset GW2Sdq.gapFam Ω c r l halive
    obtain ⟨hcf, hcon⟩ := hgoodEv l halive
    have hex : ∃ k, ξ ∈ covEv h13 c r l 0 k := (hcov halive32 hcf (hcon 0)).exists
    filter_upwards [hcovm] with m hm
    have hpass := hm 0 hex
    have h1 := href halive 0 (pkgPsi h13 (psiGoodFam h13 h12) Ω c r l 0 m + m) hpass
    change wordD c r l (augRec (stageEncRec c r l) (stgPreRecX (rootPt r.1) c.s c.W c.ζ (schedW c r l 0)
      (schedGTX h13 c r l 0) ((schedVerXDeathFamily h13 Ω c r l 0).V (pkgPsi h13 (psiGoodFam h13 h12) Ω c r l 0 m + m))
      (RootJ31.historyTime c r l)
      ((schedVerXDeathFamily h13 Ω c r l 0).R (pkgPsi h13 (psiGoodFam h13 h12) Ω c r l 0 m + m))) ξ) = _
    unfold pkgNb wordD
    simp only [augRec, h1]
    rfl
  have hfix : ∀ᵐ ω₀ ∂c.P, ∀ m : ℕ, ∀ᵐ ξ ∂condExpKernel c.P (c.sigma r l) ω₀,
      wordD c r l ((instX h13 (pkgVerF h13 h12) (pkgCh h13 h12 cwSrc) Ω c r l 0 m hx).srecX c r l (rootPt r.1) ξ) =
        wordD c r l ((instX h13 (pkgVerF h13 h12) (pkgCh h13 h12 cwSrc) Ω c r l 0 m hx).srecX c r l (rootPt r.1) ω₀) :=
    ae_all_iff.2 fun m => ae_ae_condExpKernel_eq_of_comap_le (sigma_le_ambient c r l)
      (comap_wordD_slot_le h13 h12 c r l hI hTO ⟨hx, hs⟩ 0 m)
  filter_upwards [hslot, Sec7.Aux122Disint.ae_ae_condExpKernel (sigma_le_ambient c r l) hslot, hfix,
    ae_kernel_alive_gapFam h13 c r l] with ω₀ hslot₀ hslotK hfix₀ halK halive₀
  have hfixK : ∀ᵐ ξ ∂condExpKernel c.P (c.sigma r l) ω₀, ∀ m : ℕ,
      wordD c r l ((instX h13 (pkgVerF h13 h12) (pkgCh h13 h12 cwSrc) Ω c r l 0 m hx).srecX c r l (rootPt r.1) ξ) =
        wordD c r l ((instX h13 (pkgVerF h13 h12) (pkgCh h13 h12 cwSrc) Ω c r l 0 m hx).srecX c r l (rootPt r.1) ω₀) :=
    ae_all_iff.2 hfix₀
  filter_upwards [hslotK, hfixK, halK halive₀] with ξ hsξ hfξ haξ
  obtain ⟨m, hm⟩ := ((hsξ haξ).and (hslot₀ halive₀)).exists
  rw [← hm.1, hfξ m, hm.2]

end Slots

end InteractingSLE.Theorem14.GW2Bh
