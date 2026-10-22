import HigherDimLQGMetric.LfppTight.TightTransfer
import HigherDimLQGMetric.LfppTight.CrossMain
import HigherDimLQGMetric.Law.Main

/-! Packet L6a: normalized LFPP tightness and proper metric limit laws. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l6a_tight (hL1e : L1e_law) :
    ∀ (d : ℕ) (ξ : ℝ) (κ : Rd d → ℝ), L6a_tight d ξ κ := by
  intro d ξ κ hB2
  obtain ⟨Q, hDGZ, hAdapter⟩ := hB2
  intro Ω _ P _ h hh
  have hh' : IsLGFPlusBddCont h P := hh
  obtain ⟨_, f, hfm, hfb, hb⟩ := hh
  let b : Ω → DistRd d := fun ω => h ω - ofCont (f ω)
  have hb' : IsWholeSpaceLGF b P := hb
  have hconv : ∀ᵐ ω ∂P, b ω ∈ convSet d :=
    hb'.ae_exists_tendsto_sphereAvgSeq hDGZ.dim one_pos 0
  let g : Ω → DistRd d := fun ω =>
    addConst (b ω) (-sphereAvg (b ω) 1 0)
  have hg : IsNormalizedLGF g P :=
    hb'.isNormalizedLGF_normalize (by have := hDGZ.dim; omega) hconv
  let c : Ω → ℝ := fun ω => sphereAvg (b ω) 1 0
  have hc : Measurable c := (measurable_sphereAvg_left 1 0).comp hb'.measurable
  have hbc (ω : Ω) : b ω = addConst (g ω) (c ω) := by
    dsimp [g, c]
    rw [addConst_addConst, neg_add_cancel, addConst_zero]
  have hhb (ω : Ω) : h ω = addFun (b ω) (f ω) := by
    dsimp [b, addFun]
    abel
  have hTb : TightFamily P (fun ε ω => toCMapRd
      ((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (b ω))) (Ioo (0 : ℝ) 1) :=
    l6a_tightFamily_addConst hL1e hDGZ hAdapter P g b hg hb' c hc hbc
  have hTh : TightFamily P (fun ε ω => toCMapRd
      ((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω))) (Ioo (0 : ℝ) 1) :=
    l6a_tightFamily_addBddCont hDGZ P b h hb' hh' f hfm hfb hhb hTb
  exact ⟨fun ε hε => l6a_aEps_pos hDGZ.dim κ hDGZ.kernel ξ hε.1, hTh⟩

theorem l6a_tight' : ∀ (d : ℕ) (ξ : ℝ) (κ : Rd d → ℝ),
    L6a_tight d ξ κ := l6a_tight l1e_law

end HigherDimLQGMetric
