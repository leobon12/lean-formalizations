import QuantumZipper.Proofs.Zipper.FieldLawler4ChainP3
import QuantumZipper.Proofs.Zipper.FieldLawler4Jint
import QuantumZipper.Proofs.Zipper.FieldLawler4Assemble
import QuantumZipper.Proofs.Zipper.FieldLawler4Sign
import QuantumZipper.Proofs.Zipper.FieldLawler3Wire

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# FL4-CHAIN+ (part 4): `FL4PerArc 1`

The per-crosscut input of `fl4_imageSumBound_of` for positive feet: the angles of the preimage
arc (`fl4_arc_chart`, `fl4sign_ends_pos`, `fl4sign_arc_subset`) and Field–Lawler's chain
(EJP 20 (2015), p. 9) `ℰ(η, (−∞, 0]) ≤ ℰ_{D₁}(ηD, C_R)` (`fl4chain_bound`), for either
orientation of the crosscut (reversal `fl_rev_crosscut`). Own bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Metric Complex
open scoped Topology Real ENNReal

namespace QuantumZipper
namespace FieldLawler

open Thm18Asm.LWFar

/-- **FL4PerArc for positive feet.** -/
theorem fl4_perArc_pos : FL4PerArc 1 := by
  intro W hW hW0 t R ε ht hR hε hR4 htr0 hcont hinj hH hhull hlt htip _ η a b h hη ha hb hsa hsb
    hsub hh
  rw [one_mul] at hsa hsb
  obtain ⟨F, hc⟩ := flWire_ctx hW hW0 ht hR htr0 hcont hinj hH hhull htip
  have hεR : ε < R := by linarith
  have htH : trace W t ∈ H := hH t ⟨hc.tpos, le_rfl⟩
  have hle : ∀ z ∈ fwdHull W t, ‖z‖ ≤ R := by
    rw [hhull]; rintro _ ⟨u, hu, rfl⟩
    rcases hu.2.lt_or_eq with h' | h'
    · exact (hlt u ⟨hu.1.le, h'⟩).le
    · rw [h', htip]
  obtain ⟨α, β, h0α, hαβ, hβπ, heq, hαD, hβD, hfeet, σ, hσ, hU, himg⟩ :=
    fl4_arc_chart hc hε hη ha hb hsub
  obtain ⟨hβπ', hendα, hendβ⟩ := fl4sign_ends_pos hc hinj hε h0α hαβ hβπ hαD hβD hfeet hsa hsb
  refine ⟨α, β, ⟨by rw [if_pos one_pos]; exact h0α, hαβ, by rw [if_pos one_pos]; exact hβπ'⟩,
    heq, ⟨by simp only [one_mul]; exact hendα, by simp only [one_mul]; exact hendβ⟩,
    fl4sign_arc_subset hc hη heq, ?_⟩
  intro g hg
  rw [if_pos one_pos]
  have hne : a ≠ b := by
    rintro rfl
    have e : flCirc ε α = flCirc ε β := by
      rcases hfeet with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [← h1, h2]
      · rw [← h2, h1]
    exact hαβ.ne (flCirc_injOn hε ⟨h0α, by linarith⟩ ⟨by linarith, hβπ⟩ e)
  have key : ∀ (η' : ℝ → ℂ) (a' b' : ℝ), IsCrosscutH η' → Tendsto η' (𝓝[>] 0) (𝓝 (a' : ℂ)) →
      Tendsto η' (𝓝[<] 1) (𝓝 (b' : ℂ)) → 0 < a' → a' < b' → arcH η' = arcH η →
      excR h (Iic 0) ≤ fl2FluxR R g := by
    intro η' a' b' hη' ha' hb' ha0 hab' hA
    have hC : hullComp η' = hullComp η := by unfold hullComp; rw [hA]
    rw [← hC] at hU hh
    rw [← hA] at heq himg hh
    obtain ⟨p₀, hp, hpU, hcl, hAr⟩ := fl4cwd_base (R := R) hc hε hεR h0α hαβ hβπ hσ hη' heq hU
    exact fl4chain_bound hc hinj hε hεR htH htip hle hlt hη' ha0 ha' hb' hab' heq h0α hαβ hβπ
      hαD hβD hσ hU himg hh hp hpU hcl hAr
      (fl4WdJ_eq_Ioo hc hε hεR hlt htip htH hη' ha' hb' hab' heq hp hpU) hg
  rcases lt_or_gt_of_ne hne with hab | hba
  · exact key η a b hη ha hb hsa hab rfl
  · exact key (fun s => η (1 - s)) b a (fl_rev_crosscut hη) (hb.comp fl_rev_tendsto0)
      (ha.comp fl_rev_tendsto1) hsb hba (fl_rev_arcH η)

end FieldLawler
end QuantumZipper
