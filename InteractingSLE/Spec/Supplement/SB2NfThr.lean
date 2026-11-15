/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2NfStop
import InteractingSLE.Spec.Supplement.SB2NeThr

/-!
# The threshold clause for general stops

Packet PROVE-AUX61-NOJUMP (round 22, the root variant). `Nd.StopIn.ae_thr_le` for `StopG`
(**`StopG.ae_thr_le`**): given the convergence of the relative trace to a bad relative point right of the seed at a
finite relative lifetime, every continuation of the frozen drivers reaches its threshold by the relative lifetime.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)

universe u

namespace InteractingSLE.Theorem14.SB.Nf

open Vs Exist.StagedLaw Supp8.GB6 Supp8.GB6.HullId Supp8.GB6.RelDrv.Version Supp8.Q3Stop Sec7.PocketTraversal
  Sec7.Lemma71C Restart Exist Exist.Staged Lv Ms Mf WalkSide LocalSets Lk LuM Nc Dv Vr Nd

namespace StopG

variable {κ : ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} (T : StopG P κ (-(Real.pi / 2)))

/-- **Clause (iii): every continuation of the frozen drivers reaches its threshold by the relative lifetime.** -/
theorem ae_thr_le
    (hend : ∀ ω ∈ T.Eg ∩ T.Gr, capLife (T.ρ ω) ≠ ⊤ → ∃ y : ℝ, 0 < y ∧
      Tendsto (capTrace (T.ρ ω)) (𝓝[<] (capLife (T.ρ ω)).toNNReal) (𝓝 (y : ℂ)) ∧
      Vq.IsBadPoint (cellXL κ (-(Real.pi / 2)) T.cw (angleWordType κ (-(Real.pi / 2)) (T.cw ω)) ω)
        (cellXR κ (-(Real.pi / 2)) T.cw (angleWordType κ (-(Real.pi / 2)) (T.cw ω)) ω)
        (typedRhoL (angleWordType κ (-(Real.pi / 2)) (T.cw ω)))
        (typedRhoR (angleWordType κ (-(Real.pi / 2)) (T.cw ω))) (y : ℂ))
    {β : Ω → BoundaryWord} (hβ : ∀ᵐ ω ∂P, T.cw ω = β ω) (w : WordType) (Wc : ℝ≥0 → Ω → ℝ)
    (hWc : ∀ ω, Continuous fun t => Wc t ω) :
    ∀ᵐ ω ∂P, ω ∈ seedCell κ (-(Real.pi / 2)) β T.Eg w → capLife (T.ρ ω) < ⊤ →
      (∀ m, ∀ t : ℝ≥0, (t : ℝ≥0∞) < T.V m ω → Wc t ω = T.W m t ω) →
      FCDet.thr (typedRhoL w) (typedRhoR w) Wc (cellXL κ (-(Real.pi / 2)) β w)
        (cellXR κ (-(Real.pi / 2)) β w) ω ≤ capLife (T.ρ ω) := by
  filter_upwards [T.ae_mem_Gs, hβ] with ω hG hβω hc hfin hagree
  have hGω := hG hc.1.1
  have hd := T.hd ω
  have hfin' : capLife (T.ρ ω) ≠ ⊤ := hfin.ne
  obtain ⟨y, hy, hz, hbad⟩ := hend ω hGω hfin'
  have hw : angleWordType κ (-(Real.pi / 2)) (T.cw ω) = w := by rw [hβω]; exact hc.1.2
  have hWr : ∀ t : ℝ≥0, (t : ℝ≥0∞) < capLife (T.ρ ω) → Wc t ω = T.Wr t ω := fun t ht => by
    rw [← T.V_sup hGω] at ht
    obtain ⟨m, hm⟩ := lt_iSup_iff.1 ht
    rw [hagree m t hm, T.W_eq_Wr hGω (by rw [← T.V_eq hGω]; exact hm.le)]
  have hgen := isGeneratingTrace_capExt hd hfin' hz (Wr := fun t => T.Wr t ω)
    (fun V hV => T.isGeneratingTrace_Wr ω hV) (Wc := fun t => Wc t ω) hWr
  have hpos0 := Vk.capLife_pos hd
  have hT0 : 0 < (capLife (T.ρ ω)).toNNReal := ENNReal.toNNReal_pos hpos0.ne' hfin'
  have hTU : (((capLife (T.ρ ω)).toNNReal : ℝ≥0) : ℝ≥0∞) = capLife (T.ρ ω) := ENNReal.coe_toNNReal hfin'
  have hval : capExt (T.ρ ω) (y : ℂ) (capLife (T.ρ ω)).toNNReal = y := by
    unfold capExt
    simp only [hTU, lt_irrefl, ↓reduceIte]
  have hW0 : Wc 0 ω = 0 := by
    rw [hWr 0 (by simpa using hpos0), T.Wr_zero]
  obtain ⟨-, hb⟩ := hbad
  rcases hb with ⟨-, hwR⟩ | ⟨hle, -⟩
  · rw [hw, show cellXR κ (-(Real.pi / 2)) T.cw w ω = cellXR κ (-(Real.pi / 2)) β w ω by
      simp only [cellXR, hβω]] at hwR
    have h := Wf.thr_le_of_bad_right (W := Wc) (ω := ω) (xL := cellXL κ (-(Real.pi / 2)) β w)
      (xR := cellXR κ (-(Real.pi / 2)) β w) (ρL := typedRhoL w) (ρR := typedRhoR w) (hWc ω) hW0 hgen hT0
      hTU.le (by rw [hval]; simp) (by rw [hval]; simpa using hy) (by rw [hval]; simpa using hwR)
    exact h.trans hTU.le
  · exfalso
    have : (0 : ℝ) < ((y : ℝ) : ℂ).re := by simpa using hy
    linarith

end StopG

end InteractingSLE.Theorem14.SB.Nf
