/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedRemoteMap

/-!
# The opposite map at protected seed accesses

Packet PROVE-ZHAN-GT4-A22. Generalize the driver-only reflected-map identification
in `DualD6` to every protected real coordinate. The coordinate can be an integrated
seed on the first hull boundary: no inverse physical mark is used.
-/

set_option autoImplicit false
noncomputable section
open Complex Set Filter Topology Metric
namespace InteractingSLE.ZhanGT4
open QuantumZipper (IsForwardSol fwdMap fwdHull)

namespace OwnData

/-- A reflected own map agrees locally with any holomorphic map out of the same
image hull at every protected real coordinate, including a seed access. -/
theorem eqOn_ownExt_at_clear_of_isMapOut
    {W a W' : ℝ → ℝ} {A : Set ℂ} {φ : ℂ → ℂ} {T t v ρ δ : ℝ}
    (h : OwnData W A φ T a W') (ht : t ∈ Icc (0 : ℝ) T) (hρ : 0 < ρ)
    (hclear : Disjoint (ball (v : ℂ) ρ) ((fun z => fwdMap W t z + W t) '' A))
    {R : ℂ → ℂ} (hR : IsMapOut ((fun z => fwdMap W t z + W t) '' A) R)
    (hδ : 0 < δ) (hRd : DifferentiableOn ℂ R (ball (v : ℂ) δ)) :
    ∃ ε > (0 : ℝ), EqOn (ownExt W W' a φ t) R (ball (v : ℂ) ε) := by
  obtain ⟨hd, -, -, -, -, he⟩ := h.ownExt_props ht hclear
  have hε : 0 < min (ρ / 2) δ := lt_min (by positivity) hδ
  have hsub₁ := ball_subset_ball (min_le_left (ρ / 2) δ) (x := (v : ℂ))
  have hsub₂ := ball_subset_ball (min_le_right (ρ / 2) δ) (x := (v : ℂ))
  refine ⟨min (ρ / 2) δ, hε, ConformalImageFull.eqOn_ball_of_eqOn_upper hε
    (hd.mono hsub₁) (hRd.mono hsub₂) ?_⟩
  intro z hz
  exact he R hR ⟨hsub₁ hz.1, hz.2⟩

/-- The opposite image chain is alive at every protected real coordinate of the
first chart. Clearance is imposed in that chart, not at a physical boundary mark. -/
theorem exists_transposed_sol_of_clear
    {W₁ W₂ b U : ℝ → ℝ} {s T v ρ : ℝ}
    (h₂ : ImgData W₂ (fwdHull W₁ s) (frzChart W₁ s) T b U)
    (hρ : 0 < ρ)
    (hclear : Disjoint (ball (v : ℂ) ρ)
      ((fun z => fwdMap W₁ s z + W₁ s) '' fwdHull W₂ T)) :
    ∃ q : ℝ → ℂ, IsForwardSol U (v : ℂ) (b T) q := by
  have hT : T ∈ Icc (0 : ℝ) T := ⟨h₂.pos.le, le_rfl⟩
  have hb : 0 < b T := by
    have hm := h₂.mono (left_mem_Icc.2 h₂.pos.le) hT h₂.pos
    rwa [h₂.a0] at hm
  have hd : Disjoint (ball (v : ℂ) ρ) (fwdHull U (b T)) := by
    rwa [h₂.img T hT]
  have hne : v ≠ U 0 := by
    intro he
    have hn := notMem_ball_of_mem_closure hd (start_mem_closure_fwdHull h₂.contW' hb)
    apply hn
    rw [← he]
    exact mem_ball_self hρ
  exact exists_isForwardSol_of_disjoint_ball_gen h₂.contW' hne hb.le hρ hd

/-- The opposite image flow represents all complex derivatives at a protected
seed access. This includes order zero, with the hydrodynamic translation. -/
theorem iterate_deriv_ownExt_eq_transposed_at_clear
    {W₁ W₂ a W' b U : ℝ → ℝ} {S s T t v ρ : ℝ}
    (h₁ : OwnData W₁ (fwdHull W₂ t) (frzChart W₂ t) S a W')
    (hs : s ∈ Icc (0 : ℝ) S)
    (h₂ : ImgData W₂ (fwdHull W₁ s) (frzChart W₁ s) T b U)
    (ht : t ∈ Icc (0 : ℝ) T) (hρ : 0 < ρ)
    (hclear : Disjoint (ball (v : ℂ) ρ)
      ((fun z => fwdMap W₁ s z + W₁ s) '' fwdHull W₂ t))
    {q : ℝ → ℂ} (hq : IsForwardSol U (v : ℂ) (b T) q) (k : ℕ) :
    deriv^[k] (ownExt W₁ W' a (frzChart W₂ t) s) v =
      deriv^[k] (fun z => fwdMap U (b t) z + U (b t)) v := by
  have hR : IsMapOut ((fun z => fwdMap W₁ s z + W₁ s) '' fwdHull W₂ t)
      (fun z => fwdMap U (b t) z + U (b t)) := by
    change IsMapOut (frzChart W₁ s '' fwdHull W₂ t) _
    rw [← h₂.img t ht]
    exact isMapOut_fwdMap_gen h₂.contW' (h₂.mapsTo_clock_Icc ht).1
  have hbT : 0 ≤ b T := (h₂.mapsTo_clock_Icc ⟨h₂.pos.le, le_rfl⟩).1
  obtain ⟨δ, hδ, hlow, -⟩ := exists_aliveDisc_self hq hbT
  have hd := (differentiableOn_fwdMap_aliveDisc h₂.contW' hq hδ hlow
    (h₂.mapsTo_clock_Icc ht)).add_const ((U (b t) : ℝ) : ℂ)
  obtain ⟨ε, hε, he⟩ := h₁.eqOn_ownExt_at_clear_of_isMapOut hs hρ hclear hR
    (aliveRad_pos hδ) hd
  have hev := Filter.eventuallyEq_of_mem (ball_mem_nhds (v : ℂ) hε) he
  exact (eventuallyEq_iterate_deriv hev k).eq_of_nhds

end OwnData
end InteractingSLE.ZhanGT4
