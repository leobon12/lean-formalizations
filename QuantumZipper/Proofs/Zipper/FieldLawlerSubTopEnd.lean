import QuantumZipper.Proofs.Zipper.FieldLawlerSubTopArc
import QuantumZipper.Proofs.Zipper.FieldLawlerSubTopLim

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# FL-IMAGETOP (partial): a maximal arc of `H_t ∩ C_ε` maps to a crosscut of `ℍ`

Task FL-IMAGETOP (helper of FL-THM, D75). Field–Lawler, EJP 20 (2015), proof of Prop. 3.4
(p. 9, first display): the `Z_t`-image of an arc `ηⱼ` of `D ∩ C_ε` (`D = H_t`) is a crosscut of
`ℍ`. Here: if `{ε e^{iθ} : α < θ < β} ⊆ H_t` and both end points `ε e^{iα}`, `ε e^{iβ}` lie
outside `H_t`, then `flArc W t ε α β` is an `IsCrosscutH` whose real end points `a, b` satisfy
`F a = ε e^{iα}`, `F b = ε e^{iβ}` (`flArc_crosscut`). The end limits exist by
`fl_tendsto_real_of_subseq` (cluster set argument) with the non-constancy of the Carathéodory
extension on real intervals (`CaraR.RevExt.noConst`) and the subsequential limits of
`lwfSide_limit`.
-/

noncomputable section

open Set Filter Metric Complex
open scoped Topology Real

namespace QuantumZipper
namespace FieldLawler

open Thm18Asm.LWFar

variable {W : ℝ → ℝ} {t : ℝ} {F : ℂ → ℂ}

/-- The left end limit of the image of a circle arc (any orientation). -/
theorem flArc_tendsto_left (hc : SideCtx W t F)
    (hnc : ∀ a b : ℝ, a < b → ∀ c : ℂ, ¬ ∀ s ∈ Ioo a b, F s = c) {ε α β : ℝ}
    (hD : ∀ s ∈ Ioo (0 : ℝ) 1, flCirc ε (flAng α β s) ∈ H \ fwdHull W t)
    (hx₀ : flCirc ε α ∉ H \ fwdHull W t) :
    ∃ a : ℝ, F a = flCirc ε α ∧ Tendsto (flArc W t ε α β) (𝓝[>] 0) (𝓝 (a : ℂ)) := by
  have hcont : ContinuousOn (flArc W t ε α β) (Ioo 0 1) :=
    hc.continuousOn_fwdMap.comp
      ((flCirc_continuous ε).comp (by unfold flAng; fun_prop)).continuousOn hD
  refine fl_tendsto_real_of_subseq hcont hnc fun ns hns => ?_
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hns.eventually (Ioo_mem_nhdsGT (one_pos : (0 : ℝ) < 1)))
  set x : ℕ → ℂ := fun n => flCirc ε (flAng α β (ns (n + N))) with hxdef
  have hx : ∀ n, x n ∈ H \ fwdHull W t := fun n => hD _ (hN _ (Nat.le_add_left N n))
  have hns0 : Tendsto (fun n => ns (n + N)) atTop (𝓝 0) :=
    (hns.mono_right nhdsWithin_le_nhds).comp (tendsto_add_atTop_nat N)
  have hcf : Continuous fun s : ℝ => flCirc ε (flAng α β s) :=
    (flCirc_continuous ε).comp (by unfold flAng; fun_prop)
  have hlim : Tendsto x atTop (𝓝 (flCirc ε α)) := by
    have := (hcf.tendsto 0).comp hns0
    rw [hxdef]
    simpa [flAng, Function.comp_def] using this
  obtain ⟨φ, hφ, a, ha, hl⟩ := lwfSide_limit hc hx hx₀ hlim
  exact ⟨fun n => φ n + N, fun m n h => Nat.add_lt_add_right (hφ h) N, a, ha, hl⟩

lemma flArc_rev (W : ℝ → ℝ) (t ε α β s : ℝ) :
    flArc W t ε α β (1 - s) = flArc W t ε β α s := by
  unfold flArc flAng; congr 2; ring

/-- **A maximal arc of `H_t ∩ C_ε` maps to a crosscut of `ℍ`** with real end points `a, b`,
`F a = ε e^{iα}`, `F b = ε e^{iβ}`, inside the level set `‖Z_t⁻¹‖ = ε`. -/
theorem flArc_crosscut (hc : SideCtx W t F)
    (hnc : ∀ a b : ℝ, a < b → ∀ c : ℂ, ¬ ∀ s ∈ Ioo a b, F s = c) {ε α β : ℝ} (hε : 0 < ε)
    (hab : α < β) (h0α : 0 ≤ α) (hβπ : β ≤ π)
    (hD : ∀ θ ∈ Ioo α β, flCirc ε θ ∈ H \ fwdHull W t)
    (hα : flCirc ε α ∉ H \ fwdHull W t) (hβ : flCirc ε β ∉ H \ fwdHull W t) :
    ∃ a b : ℝ, F a = flCirc ε α ∧ F b = flCirc ε β ∧ IsCrosscutH (flArc W t ε α β) ∧
      Tendsto (flArc W t ε α β) (𝓝[>] 0) (𝓝 (a : ℂ)) ∧
      Tendsto (flArc W t ε α β) (𝓝[<] 1) (𝓝 (b : ℂ)) ∧
      arcH (flArc W t ε α β) ⊆ {p | ‖fwdMapInv W t p‖ = ε} := by
  obtain ⟨h1, h2, h3, h4⟩ := flArc_props hc hε hab h0α hβπ hD
  have hD1 : ∀ s ∈ Ioo (0 : ℝ) 1, flCirc ε (flAng α β s) ∈ H \ fwdHull W t := fun s hs =>
    hD _ (flAng_mem hab hs)
  have hD2 : ∀ s ∈ Ioo (0 : ℝ) 1, flCirc ε (flAng β α s) ∈ H \ fwdHull W t := fun s hs => by
    have : flAng β α s = flAng α β (1 - s) := by unfold flAng; ring
    rw [this]; exact hD1 _ ⟨by linarith [hs.2], by linarith [hs.1]⟩
  obtain ⟨a, ha, hla⟩ := flArc_tendsto_left hc hnc hD1 hα
  obtain ⟨b, hb, hlb⟩ := flArc_tendsto_left hc hnc hD2 hβ
  have hrev : Tendsto (fun s : ℝ => 1 - s) (𝓝[<] 1) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Tendsto (fun s : ℝ => 1 - s) (𝓝 1) (𝓝 (1 - 1)) :=
        (continuous_const.sub continuous_id).tendsto 1
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact sub_pos.2 (show s < 1 from hs)
  have hlb' : Tendsto (flArc W t ε α β) (𝓝[<] 1) (𝓝 (b : ℂ)) := by
    have := hlb.comp hrev
    refine this.congr fun s => ?_
    simp only [Function.comp_apply]
    rw [← flArc_rev, sub_sub_cancel]
  exact ⟨a, b, ha, hb, ⟨h1, h2, h3, ⟨a, hla⟩, ⟨b, hlb'⟩⟩, hla, hlb', h4⟩

end FieldLawler
end QuantumZipper
