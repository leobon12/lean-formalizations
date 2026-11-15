/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2BvShare
import InteractingSLE.Spec.Supplement.GW2RlBot
import InteractingSLE.Spec.Supplement.GW2RkTop

/-!
# The reference record of a version family and its near base under the conditional law

Packet PROVE-GW2-BUF (round 21; nearImg on the stop family, D75). Round 19's `ae_slotRec_eq_ref` and
`ae_kernel_pkgNb_eq` for ROOTX's reference record `GW2Rl.refPreV h13 ver` (the first slot of `ver` passing the
history's clock) and near base `GW2Rl.refNb h13 ver cwSrc`, for any version family:

* **`ae_slotRec_eq_refV2`**: almost surely on the alive event, every slot of a family `ver₁` passing the clock has the
  reference record of a family `ver₂` (when some slot of `ver₂` passes the clock); **`ae_slotRec_eq_refV`** for one
  family;
* `comap_wordD_slotV_le`, **`ae_kernel_refNb_eq`**: for almost every alive `ω₀`, `refNb ξ = refNb ω₀` for almost
  every kernel sample `ξ` (the owners' instance inputs for `ver`, and `ver` covering the clock).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Bh

open Restart Exist Exist.StagedLaw GW2TipSystem GW2TipSystem.RootC24 GW2Rz GW2Rd GW2Rv GW2Sde GW2Sdh GW2Sdx

variable (h13 : Exist.Theorem13Statement.{u}) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q))

/-- **Slots of `ver₁` passing the clock have the reference record of `ver₂`** (almost surely on the alive event). -/
theorem ae_slotRec_eq_refV2 (ver₁ ver₂ : SchedVerXFamily.{u}) (gap : RootCv.GapFamily.{u}) (hg : GoodRoot c r) :
    ∀ᵐ ξ ∂c.P, ξ ∈ ((GW2Sdz.J32S gap Ω c).experiment r).data.alive ((GW2Sdz.J32S gap Ω c).G r) l →
      ∀ a j : ℕ, ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (RootJ31.historyTime c r l) ξ) <
          (ver₁ Ω c r l a).V j ξ →
      (∃ p : ℕ, ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l (Nat.unpair p).1)
          (RootJ31.historyTime c r l) ξ) < (ver₂ Ω c r l (Nat.unpair p).1).V (Nat.unpair p).2 ξ) →
        stgPreRecX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a)
            ((ver₁ Ω c r l a).V j) (RootJ31.historyTime c r l) ((ver₁ Ω c r l a).R j) ξ =
          GW2Rl.refPreV h13 ver₂ Ω c r l ξ := by
  obtain ⟨hx, hs⟩ := hg
  set T := RootJ31.historyTime c r l with hTdef
  have hpair : ∀ᵐ ω ∂c.P, ∀ p q : ℕ × ℕ, cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s →
      ((T : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l p.1) c.α ω ∧
        ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l p.1) T ω) < (ver₁ Ω c r l p.1).V p.2 ω) →
      ((T : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l q.1) c.α ω ∧
        ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l q.1) T ω) < (ver₂ Ω c r l q.1).V q.2 ω) →
      stgPreRecX (rootPt r.1) c.s c.W c.ζ (schedW c r l p.1) (schedGTX h13 c r l p.1)
          ((ver₁ Ω c r l p.1).V p.2) T ((ver₁ Ω c r l p.1).R p.2) ω =
        stgPreRecX (rootPt r.1) c.s c.W c.ζ (schedW c r l q.1) (schedGTX h13 c r l q.1)
          ((ver₂ Ω c r l q.1).V q.2) T ((ver₂ Ω c r l q.1).R q.2) ω :=
    ae_all_iff.2 fun p => ae_all_iff.2 fun q =>
      GW2Sdo.ae_stgPreRecX_sched_eq h13 c r l p.1 q.1 hs hx ((ver₁ Ω c r l p.1).isA hx p.2).1.1
        ((ver₂ Ω c r l q.1).isA hx q.2).1.1
  filter_upwards [hpair, GW2Ru.ae_alive_goodEvent_scaled h13 gap c r] with ξ hpξ hgoodEv halive a j hslot hex0
  obtain ⟨hcf, hcon⟩ := hgoodEv l halive
  unfold GW2Rl.refPreV
  rw [dite_eq_left hex0]
  exact hpξ (a, j) (_, _) hcf ⟨hcon a, hslot⟩ ⟨hcon _, Nat.find_spec hex0⟩

/-- **Slots passing the clock have the family's reference record** (almost surely on the alive event). -/
theorem ae_slotRec_eq_refV (ver : SchedVerXFamily.{u}) (gap : RootCv.GapFamily.{u}) (hg : GoodRoot c r) :
    ∀ᵐ ξ ∂c.P, ξ ∈ ((GW2Sdz.J32S gap Ω c).experiment r).data.alive ((GW2Sdz.J32S gap Ω c).G r) l →
      ∀ a j : ℕ, ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (RootJ31.historyTime c r l) ξ) <
          (ver Ω c r l a).V j ξ →
        stgPreRecX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a)
            ((ver Ω c r l a).V j) (RootJ31.historyTime c r l) ((ver Ω c r l a).R j) ξ =
          GW2Rl.refPreV h13 ver Ω c r l ξ := by
  filter_upwards [ae_slotRec_eq_refV2 h13 c r l ver ver gap hg] with ξ h halive a j hj
  refine h halive a j hj ⟨Nat.pair a j, ?_⟩
  rw [Nat.unpair_pair]
  exact hj

/-- **The base word of a slot is retained up to null sets** (any family with the owners' instance inputs). -/
theorem comap_wordD_slotV_le (ver : SchedVerXFamily.{u}) (ch : SchedChoiceFamily.{u}) (hI : InstInputsX h13 ver ch)
    (hTO : HistOrdered c r l) (hg : GoodRoot c r) (a m : ℕ) :
    MeasurableSpace.comap (fun ξ => wordD c r l
        ((instX h13 ver ch Ω c r l a m hg.1).srecX c r l (rootPt r.1) ξ))
      inferInstance ≤ LocalSets.aeSigma (c.sigma r l) c.P := by
  have hgood := hI.goodX hTO hg a m
  have h1 : MeasurableSpace.comap ((instX h13 ver ch Ω c r l a m hg.1).srecX c r l (rootPt r.1)) inferInstance ≤
      LocalSets.aeSigma (c.sigma r l) c.P := by
    change MeasurableSpace.comap (augRec (stageEncRec c r l) (stgPreRecX (rootPt r.1) c.s c.W c.ζ
      (schedW c r l a) (schedGTX h13 c r l a) ((ver Ω c r l a).V m) (RootJ31.historyTime c r l)
      ((ver Ω c r l a).R m))) inferInstance ≤ _
    rw [GW2Sde.comap_augRec]
    exact sup_le ((GW2Rd.comap_stageEncRec_sigma c r l).le.trans (LocalSets.le_aeSigma _ _))
      hgood.prefix_retained
  have h2 := (measurable_wordD c r l).comap_le
  calc MeasurableSpace.comap (fun ξ => wordD c r l
        ((instX h13 ver ch Ω c r l a m hg.1).srecX c r l (rootPt r.1) ξ)) inferInstance
      = MeasurableSpace.comap ((instX h13 ver ch Ω c r l a m hg.1).srecX c r l (rootPt r.1))
          (MeasurableSpace.comap (wordD c r l) inferInstance) := by
        rw [MeasurableSpace.comap_comp]
        rfl
    _ ≤ MeasurableSpace.comap ((instX h13 ver ch Ω c r l a m hg.1).srecX c r l (rootPt r.1)) inferInstance :=
        MeasurableSpace.comap_mono h2
    _ ≤ _ := h1

/-- **The reference near base is fixed by the conditional law** (almost every alive conditioning sample). -/
theorem ae_kernel_refNb_eq (ver : SchedVerXFamily.{u}) (ch : SchedChoiceFamily.{u}) (hI : InstInputsX h13 ver ch)
    (hcov : Wire.T14Rk.VerCovers ver) :
    ∀ᵐ ω₀ ∂c.P, ω₀ ∈ ((GW2Sdz.J32S GW2Sdq.gapFam Ω c).experiment r).data.alive
        ((GW2Sdz.J32S GW2Sdq.gapFam Ω c).G r) l →
      ∀ᵐ ξ ∂condExpKernel c.P (c.sigma r l) ω₀,
        GW2Rl.refNb h13 ver cwSrc Ω c r l ξ = GW2Rl.refNb h13 ver cwSrc Ω c r l ω₀ := by
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
  -- the slots passing the clock read `refNb`
  have hslot : ∀ᵐ ξ ∂c.P, ξ ∈ ((GW2Sdz.J32S GW2Sdq.gapFam Ω c).experiment r).data.alive
        ((GW2Sdz.J32S GW2Sdq.gapFam Ω c).G r) l →
      ∀ᶠ m in atTop, wordD c r l ((instX h13 ver ch Ω c r l 0 m hx).srecX c r l (rootPt r.1) ξ) =
        GW2Rl.refNb h13 ver cwSrc Ω c r l ξ := by
    filter_upwards [ae_slotRec_eq_refV h13 c r l ver GW2Sdq.gapFam ⟨hx, hs⟩, hcov Ω c r l 0 ⟨hx, hs⟩,
      GW2Ru.ae_alive_goodEvent_scaled h13 GW2Sdq.gapFam c r] with ξ href hcovξ hgoodEv halive
    have halive32 := GW2Sdz.alive_scaled_subset GW2Sdq.gapFam Ω c r l halive
    obtain ⟨hcf, hcon⟩ := hgoodEv l halive
    filter_upwards [hcovξ halive32 hcf (hcon 0)] with m hm
    have h1 := href halive 0 m hm
    change wordD c r l (augRec (stageEncRec c r l) (stgPreRecX (rootPt r.1) c.s c.W c.ζ (schedW c r l 0)
      (schedGTX h13 c r l 0) ((ver Ω c r l 0).V m) (RootJ31.historyTime c r l) ((ver Ω c r l 0).R m)) ξ) = _
    unfold GW2Rl.refNb wordD
    simp only [augRec, h1]
    rfl
  have hfix : ∀ᵐ ω₀ ∂c.P, ∀ m : ℕ, ∀ᵐ ξ ∂condExpKernel c.P (c.sigma r l) ω₀,
      wordD c r l ((instX h13 ver ch Ω c r l 0 m hx).srecX c r l (rootPt r.1) ξ) =
        wordD c r l ((instX h13 ver ch Ω c r l 0 m hx).srecX c r l (rootPt r.1) ω₀) :=
    ae_all_iff.2 fun m => ae_ae_condExpKernel_eq_of_comap_le (sigma_le_ambient c r l)
      (comap_wordD_slotV_le h13 c r l ver ch hI hTO ⟨hx, hs⟩ 0 m)
  filter_upwards [hslot, Sec7.Aux122Disint.ae_ae_condExpKernel (sigma_le_ambient c r l) hslot, hfix,
    ae_kernel_alive_gapFam h13 c r l] with ω₀ hslot₀ hslotK hfix₀ halK halive₀
  have hfixK : ∀ᵐ ξ ∂condExpKernel c.P (c.sigma r l) ω₀, ∀ m : ℕ,
      wordD c r l ((instX h13 ver ch Ω c r l 0 m hx).srecX c r l (rootPt r.1) ξ) =
        wordD c r l ((instX h13 ver ch Ω c r l 0 m hx).srecX c r l (rootPt r.1) ω₀) :=
    ae_all_iff.2 hfix₀
  filter_upwards [hslotK, hfixK, halK halive₀] with ξ hsξ hfξ haξ
  obtain ⟨m, hm⟩ := ((hsξ haξ).and (hslot₀ halive₀)).exists
  rw [← hm.1, hfξ m, hm.2]

end InteractingSLE.Theorem14.GW2Bh
