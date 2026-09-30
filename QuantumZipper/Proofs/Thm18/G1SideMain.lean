import QuantumZipper.Proofs.Thm18.G1SideMainDet
import QuantumZipper.Proofs.Thm18.G1SideOff2
import QuantumZipper.Proofs.Thm18.G1SideScale
import QuantumZipper.Proofs.Thm18.G1SideSelDefs
import QuantumZipper.Proofs.Thm18.G1RestRed
import QuantumZipper.Proofs.Thm18.G1RegLogDeriv
import QuantumZipper.Proofs.Thm18.G1ZA1aAff
import QuantumZipper.Proofs.Thm18.G1SideWireB
import QuantumZipper.Proofs.LQG.WedgeCanonical4

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1-SIDE (11): the side-limit node at the selected side maps is proved

`Thm18Asm.g1Z4SideLimSelStmt_holds : G1Z4SideLimSelStmt` (decision D83), and the headline
`R18.theorem1_8Paper_of_frontier8` (`theorem1_8Paper_of_frontier7` without the node).

Proof: for almost every path the selected side map `ψ = Ψ left a` is measurable, conformal on `ℍ`
with values in `ℍ`, with locally integrable `log |ψ'|` on folded circles (`G1.invFunOn_props`,
`G1.choiceRegular_logDeriv`), and the pulled-back canonical field satisfies RC3
(`G1Rest.ae_rc3_rep`). Given reflection data `Φ`, for every rational window `[p,q]` of the side
half-line and every box `N`, the dilation family of `exists_dilFamily` on the widened window
`[min (p/2) p, max q (q/2)]` has the three a.s. inputs (`ae_wedge_offset_uniform`,
`ae_wedge_family_exact`, `ae_wedge_family_continuum`); countably many windows are combined by
`ae_all_iff`, and `sideBdryLim_of_winGood` concludes, with the canonical scale
`scaleParam γ w > 0` a.s. (`WedgeCan4.ae_wedge_canonical_spec_of_inputs`).
Sources: Sheffield, arXiv:1012.4797, §1.6 and proof of Thm 1.8 (pp. 69–71); Duplantier–Sheffield
2011 Prop. 2.1; Sheffield–Wang arXiv:1605.06171 Thm 4.3 (through the cited repository nodes).
Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace G1Side

open Thm18Asm

/-- The widened window stays in the side half-line. -/
theorem widen_subset {left : Bool} {p q : ℝ} (hpq : p < q) (hI : Icc p q ⊆ g1SideHalf left) :
    Icc (min (p / 2) p) (max q (q / 2)) ⊆ g1SideHalf left := by
  cases left
  · have hp0 : 0 < p := by simpa [g1SideHalf] using hI ⟨le_rfl, hpq.le⟩
    intro x hx
    simp only [g1SideHalf, Bool.false_eq_true, ↓reduceIte, mem_Ioi]
    have : 0 < min (p / 2) p := lt_min (by linarith) hp0
    linarith [hx.1]
  · have hq0 : q < 0 := by simpa [g1SideHalf] using hI ⟨hpq.le, le_rfl⟩
    intro x hx
    simp only [g1SideHalf, ↓reduceIte, mem_Iio]
    have : max q (q / 2) < 0 := max_lt hq0 (by linarith)
    linarith [hx.2]

theorem div_mem_widen {p q c t : ℝ} (hc : c ∈ Icc (1 : ℝ) 2) (ht : t ∈ Icc p q) :
    t / c ∈ Icc (min (p / 2) p) (max q (q / 2)) := by
  have hc0 : 0 < c := by linarith [hc.1]
  have hu : t = c * (t / c) := by field_simp
  rcases le_total 0 t with h0 | h0
  · have hu0 : 0 ≤ t / c := div_nonneg h0 hc0.le
    constructor
    · exact (min_le_left _ _).trans (by nlinarith [ht.1, hc.2])
    · exact le_trans (by nlinarith [ht.2, hc.1]) (le_max_left _ _)
  · have hu0 : t / c ≤ 0 := div_nonpos_of_nonpos_of_nonneg h0 hc0.le
    constructor
    · exact (min_le_right _ _).trans (by nlinarith [ht.1, hc.1])
    · exact le_trans (by nlinarith [ht.2, hc.2]) (le_max_right _ _)

/-- **All rational windows are good, a.s.** -/
theorem ae_winGood {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < Qc γ)
    {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {X : Ω' → FieldSample} {A : ℝ → Ω' → ℝ} (hX : IsFreeGFFModConstH X P')
    (hA : IsWedgeProcess α (Qc γ) A P') (hI : IndepFun X (fun ω t => A t ω) P')
    {ψ : ℂ → ℂ} {left : Bool} {Φ : ℝ ≃o ℝ} (hR : SideReflGood left ψ Φ)
    (hH : ∀ z ∈ H, ψ z ∈ H) :
    ∀ᵐ ω ∂P', ∀ p q : ℚ, ∀ N : ℕ, (p : ℝ) < q → Icc (p : ℝ) q ⊆ g1SideHalf left → 1 ≤ N →
      WinGood γ (wedgeField (lateralPart (X ω)) (fun t => A t ω) (Qc γ)) ψ left Φ p q N := by
  rw [ae_all_iff]; intro p
  rw [ae_all_iff]; intro q
  rw [ae_all_iff]; intro N
  by_cases h : (p : ℝ) < q ∧ Icc (p : ℝ) q ⊆ g1SideHalf left ∧ 1 ≤ N
  swap
  · exact ae_of_all _ fun ω h1 h2 h3 => absurd ⟨h1, h2, h3⟩ h
  obtain ⟨hpq, hIpq, hN⟩ := h
  have hab' : min ((p : ℝ) / 2) p < max (q : ℝ) (q / 2) :=
    (min_le_right _ _).trans_lt (hpq.trans_le (le_max_left _ _))
  have hS' := widen_subset hpq hIpq
  obtain ⟨Ψe, a, b, ρ, M, m, L, R, c₀, ha, hb, -, -, -, hab, hρ, hm, hL, hcl, hlip, hπ, hπK,
    hπid, hR0, hKR, hK, hc₀, hsep, hHb, hEqH, hbv⟩ := exists_dilFamily hR hH hab' hS' N hN
  filter_upwards [ae_wedge_offset_uniform hγ hγ2 hα hX hA hI (dilFam Ψe) (dilBox N) hab hρ hm hL
      hcl hlip hπ hπK hπid hR0 hKR hK hc₀ hsep hHb,
    ae_wedge_family_exact hγ hγ2 hα hX hA hab hρ hm hL hcl hlip hπ hπK hπid hc₀ hsep hHb,
    ae_wedge_family_continuum hγ hγ2 hα hX hA hI hab hρ hm hL hcl hlip hπ hπK hπid hc₀ hsep hHb]
    with ω hO hE hC _ _ _
  exact ⟨Ψe, a, b, _, _, ha, hb, hS', fun c hc t ht => div_mem_widen hc ht, hEqH, hbv, hE, hC,
    hO⟩

end G1Side

namespace Thm18Asm

/-- **Node S2 at the selected side maps (D83) is proved.** -/
theorem g1Z4SideLimSelStmt_holds : G1Z4SideLimSelStmt := by
  intro γ hγ hγ2 Ω _ P _ B hB Ω' _ P' _ X A hX hA hXA Ψ hΨ
  have hα : γ - 2 / γ < Qc γ := alpha_lt_Qc hγ hγ2
  have hPath := G1RC.ae_map_pathOf_of_chord G1RC.g1RegPathChordStmt hγ hγ2 hB hΨ
    (fun ms => ∀ left : Bool, Measurable (ms left) ∧ (∀ z ∈ H, deriv (ms left) z ≠ 0) ∧
      (∀ z ∈ H, ms left z ∈ H) ∧ ∀ d ∈ Hbar, ∀ r > 0,
        Integrable (fun z => Real.log ‖deriv (ms left) z‖) (foldedCircle d r)) (by
      intro a hc hs left
      obtain ⟨φ₀, hφ₀, hΨa⟩ := hΨ.2.2 a hc hs left
      simp only
      rw [hΨa]
      have hD : IsOpen (sideDom (pathTrace (γ ^ 2) a) left) := G1.isOpen_component hs left
      obtain ⟨-, h0, hm, hmaps⟩ := G1.invFunOn_props hD hφ₀
      exact ⟨hm, h0, fun z hz => G1ZA1a.sideDom_subset_H _ left (hmaps hz),
        G1.choiceRegular_logDeriv hD hφ₀⟩)
  have hRC := G1Rest.ae_rc3_rep γ hγ hγ2 P B hB P' X A hX hA hXA Ψ hΨ
  filter_upwards [hPath, hRC] with a hPa hRa left Φ hR
  obtain ⟨hm, h0, hH, hi⟩ := hPa left
  filter_upwards [hRa left, G1Side.ae_winGood hγ hγ2 hα hX hA hXA hR hH,
    WedgeBdry.ae_bReg_wedgeField hγ hγ2 hα hX hA hXA,
    WedgeCan4.ae_wedge_canonical_spec_of_inputs (WedgeFinZero.wedgeFiniteNearZero_holds hγ hγ2 hα)
      (WedgeInf.wedgeInfiniteTotal hγ hγ2 hα) hγ hγ2 hα hX hA hXA] with ω' hrc hwin hW hspec
  exact G1Side.sideBdryLim_of_winGood hγ hW.1 hm h0 hH hi hspec.1 hrc hR.1 hwin

end Thm18Asm

namespace R18

open Thm18Asm

end R18
end QuantumZipper
