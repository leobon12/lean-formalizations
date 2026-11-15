/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2GCusp

/-!
# Off the relative hull the joint approach is one-sided with respect to the upper hull

Packet PROVE-T14-SB2FIN2 (Theorem 1.4's SB2, item (1) of the orchestrator's continuation: `hpinch`). The field `finK`
of `IsRelConfigJC` asks that only finitely many `x` off the closed relative hull land on `closure (K_t ∖ A)`; its only
consumer (`IsRelConfigJC.hasUnionWordBoundaryOnC`, through `retained_side_rel`'s `hpK`) uses it to get, at the other
`x`, the one-sided condition "near the landing `p`, the joint approach stays in the `K_t`-free components of
`(ℍ ∖ A) ∩ B(p, r)`" (`freeNear K_t A p r`). The landed route derives `finK` from finitely many pinch points of `∂D_A`
(`finK_of_finite_pinch`), which fails as soon as `A` has a two-sided arc (every interior point of a slit has two real
preimages under `g`).

* **`eventually_freeNearK_of_notMem_closure`**: the one-sided condition holds at **every** `x` whose relative landing is
  off the closed relative hull, given only finite fibres of `g` (`Lv.finite_fibre_of_isLeftEntryChart`).

## Proof (a crosscut)

`v = F(x)` is real and off `closure K̃`; take `δ` with `B(v, δ) ∩ K̃ = ∅` and `δ' ∈ (0, δ)` with `g(v ± δ') ≠ g(v)`
(finite fibre). The crosscut `C = g(semicircle of radius δ' over v)` is compact and misses `p = g(v)` (its interior
points lie in `D_A ∌ p`), so `B(p, ρ) ∩ C = ∅` for some `ρ > 0`. For `y` near `x`, `F(y) ∈ B(v, δ')` and the joint point
`g(F y)` is in `B(p, ρ)`. Its component `W` in `(ℍ ∖ A) ∩ B(p, ρ)` is mapped by the chart into `ℍ` off the semicircle
(a point of `c.fwd(W)` on it would put a point of `W` on `C`), so `c.fwd(W) ⊆ B(v, δ')` (preconnected, contains
`F(y)`); a point of `W ∩ K_t` would have `c.fwd` in `K̃` (`hullIn`), but `B(v, δ') ∩ K̃ = ∅`. Deterministic.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Set Topology Complex Metric
open scoped NNReal
open QuantumZipper (H Hbar fwdMapInv fwdHull)

namespace InteractingSLE.Theorem14.SB.FinRel

open Supp8.BHMean (jointInv)
open InteractingSLE.Theorem14.WalkWords (semiPt exists_semiPt_eq semiPt_mem_H semiPt_mem_Hbar semiPt_zero semiPt_pi
  continuous_semiPt)

/-- **One-sidedness with respect to the upper hull off the relative hull** (the condition `finK` stands for). -/
theorem eventually_freeNearK_of_notMem_closure {A Kt : Set ℂ} {c : Chart} {g : ℂ → ℂ}
    (hD : IsDomainChart (H \ fillH A) c) (hgc : ContinuousOn g {z | 0 ≤ z.im}) (hgi : EqOn g c.2.1 H)
    (hgf : ∀ z, (g ⁻¹' {z} ∩ {w | 0 ≤ w.im}).Finite) {Wr : ℝ → ℝ} {ηr : ℝ → ℂ} {u : ℝ} (hWr : Continuous Wr)
    (hWr0 : Wr 0 = 0) (hηr : IsLoewnerTrace Wr ηr) (hu : 0 ≤ u)
    (hIn : ∀ z ∈ Kt, z ∉ fillH A → c.1 z ∈ fwdHull Wr u) {x : ℝ}
    (hx : extendFrom H (fwdMapInv Wr u) (x : ℂ) ∉ closure (fwdHull Wr u)) :
    ∃ ρ > 0, ∀ᶠ y in 𝓝[H] (x : ℂ), jointInv c.2.1 Wr u y ∈
      freeNear Kt (fillH A) (extendFrom H (jointInv c.2.1 Wr u) (x : ℂ)) ρ := by
  set F := extendFrom H (fwdMapInv Wr u) with hF
  have hxb : (x : ℂ) ∈ Hbar := show (0 : ℝ) ≤ ((x : ℂ)).im by simp
  have hvim : (F x).im = 0 := Supp8.BHMean.im_extendFrom_eq_zero_of_notMem_closure hηr hWr hWr0 hu hx
  set vr : ℝ := (F x).re with hvr
  have hv : F x = (vr : ℂ) := Complex.ext (by simp [hvr]) (by simp [hvim])
  set p : ℂ := g (vr : ℂ) with hp
  have hland : extendFrom H (jointInv c.2.1 Wr u) (x : ℂ) = p := by
    rw [extendFrom_jointInv_eq hgc hgi hWr hWr0 hηr hu hxb, ← hF, hv]
  rw [hland]
  -- a ball around `v` missing the relative hull
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 isClosed_closure.isOpen_compl _ hx
  rw [hv] at hball
  -- a radius whose endpoints avoid the fibre of `p`
  have hBfin : {d : ℝ | d ∈ Ioo 0 δ ∧ (g ((vr - d : ℝ) : ℂ) = p ∨ g ((vr + d : ℝ) : ℂ) = p)}.Finite := by
    set S := g ⁻¹' {p} ∩ {w : ℂ | 0 ≤ w.im} with hS
    refine (((hgf p).image fun w : ℂ => vr - w.re).union ((hgf p).image fun w : ℂ => w.re - vr)).subset ?_
    rintro d ⟨-, h | h⟩
    · exact Or.inl ⟨((vr - d : ℝ) : ℂ), ⟨h, by simp⟩, by simp⟩
    · exact Or.inr ⟨((vr + d : ℝ) : ℂ), ⟨h, by simp⟩, by simp⟩
  obtain ⟨δ', hδ'I, hδ'B⟩ := ((Set.Ioo_infinite hδ).sdiff hBfin).nonempty
  have hδ'0 : 0 < δ' := hδ'I.1
  have hδ'p : g ((vr - δ' : ℝ) : ℂ) ≠ p ∧ g ((vr + δ' : ℝ) : ℂ) ≠ p := by
    refine ⟨fun h => hδ'B ⟨hδ'I, Or.inl h⟩, fun h => hδ'B ⟨hδ'I, Or.inr h⟩⟩
  -- the crosscut
  set C := (fun θ => g (semiPt vr δ' θ)) '' Icc 0 Real.pi with hC
  have hCc : IsCompact C := isCompact_Icc.image_of_continuousOn
    (hgc.comp (continuous_semiPt vr δ').continuousOn fun θ hθ => semiPt_mem_Hbar hδ'0.le hθ)
  have hpD : p ∉ H \ fillH A := SB.g_ofReal_notMem hD hgc hgi vr
  have hpC : p ∉ C := by
    rintro ⟨θ, hθ, he⟩
    rcases eq_or_lt_of_le hθ.1 with h0 | h0
    · simp only [← h0, semiPt_zero] at he
      exact hδ'p.2 he
    rcases eq_or_lt_of_le hθ.2 with hπ | hπ
    · simp only [hπ, semiPt_pi] at he
      exact hδ'p.1 he
    have hH := semiPt_mem_H (c := vr) hδ'0 ⟨h0, hπ⟩
    simp only at he
    exact hpD (he ▸ SB.g_mem_of_mem_H hD hgi hH)
  obtain ⟨ρ, hρ, hρC⟩ := Metric.isOpen_iff.1 hCc.isClosed.isOpen_compl p hpC
  refine ⟨ρ, hρ, ?_⟩
  -- the approach
  have hFl : Tendsto F (𝓝[H] (x : ℂ)) (𝓝[{z : ℂ | 0 ≤ z.im}] (vr : ℂ)) := by
    obtain ⟨-, hFc, -, -⟩ := hηr.fiber_hyps hWr hWr0 hu
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun y hy => ?_⟩
    · rw [← hv]; exact ((hFc _ hxb).mono QuantumZipper.H_subset_Hbar).tendsto
    · rw [hF, ZhanGT4.extendFrom_eq_fwdMapInv hWr hWr0 hu hy]
      exact le_of_lt (show 0 < (fwdMapInv Wr u y).im from QuantumZipper.RS.fwdMapInv_mem_H hWr hWr0 hu hy)
  have hgt : Tendsto (fun y => g (F y)) (𝓝[H] (x : ℂ)) (𝓝 p) :=
    (hgc (vr : ℂ) (show (0 : ℝ) ≤ ((vr : ℂ)).im by simp)).tendsto.comp hFl
  have hev1 : ∀ᶠ y in 𝓝[H] (x : ℂ), F y ∈ ball (vr : ℂ) δ' :=
    (hFl.mono_right nhdsWithin_le_nhds).eventually (ball_mem_nhds _ hδ'0)
  have hev2 : ∀ᶠ y in 𝓝[H] (x : ℂ), g (F y) ∈ ball p ρ := hgt.eventually (ball_mem_nhds _ hρ)
  filter_upwards [hev1, hev2, self_mem_nhdsWithin] with y hy1 hy2 hyH
  have hFy : F y = fwdMapInv Wr u y := ZhanGT4.extendFrom_eq_fwdMapInv hWr hWr0 hu hyH
  have hFyH : fwdMapInv Wr u y ∈ H := QuantumZipper.RS.fwdMapInv_mem_H hWr hWr0 hu hyH
  have hj : jointInv c.2.1 Wr u y = g (F y) := by
    simp only [jointInv]; rw [hFy, hgi hFyH]
  rw [hj]
  have hjD : g (F y) ∈ H \ fillH A := by rw [hFy]; exact SB.g_mem_of_mem_H hD hgi hFyH
  refine ⟨⟨hjD, hy2⟩, Set.disjoint_left.2 fun w hwW hwK => ?_⟩
  set U := (H \ fillH A) ∩ ball p ρ with hU
  have hWU : connectedComponentIn U (g (F y)) ⊆ U := connectedComponentIn_subset _ _
  -- the chart image of the component stays in the half-disc
  have hcont : ContinuousOn c.1 (H \ fillH A) := hD.differentiableOn_fwd.continuousOn
  have hpre : IsPreconnected (c.1 '' connectedComponentIn U (g (F y))) :=
    isPreconnected_connectedComponentIn.image _ (hcont.mono fun z hz => (hWU hz).1)
  have hsplit : c.1 '' connectedComponentIn U (g (F y)) ⊆ ball (vr : ℂ) δ' ∪ (closedBall (vr : ℂ) δ')ᶜ := by
    rintro _ ⟨z, hz, rfl⟩
    have hzU := hWU hz
    rcases lt_trichotomy ‖c.1 z - vr‖ δ' with h | h | h
    · exact Or.inl (by rw [mem_ball, dist_eq_norm]; exact h)
    · exfalso
      obtain ⟨θ, hθ, hθe⟩ := exists_semiPt_eq hδ'0 (hD.fwd_mem hzU.1) h
      have hzC : z ∈ C := ⟨θ, Ioo_subset_Icc_self hθ, by
        show g (semiPt vr δ' θ) = z
        rw [hθe, hgi (hD.fwd_mem hzU.1), hD.inv_fwd hzU.1]⟩
      exact hρC hzU.2 hzC
    · exact Or.inr (by rw [mem_compl_iff, mem_closedBall, dist_eq_norm, not_le]; exact h)
  have hyimg : F y ∈ c.1 '' connectedComponentIn U (g (F y)) := by
    refine ⟨g (F y), mem_connectedComponentIn ⟨hjD, hy2⟩, ?_⟩
    rw [hFy, hgi hFyH, hD.fwd_inv hFyH]
  have hin : c.1 '' connectedComponentIn U (g (F y)) ⊆ ball (vr : ℂ) δ' :=
    hpre.subset_left_of_subset_union isOpen_ball
      (Metric.isClosed_closedBall (x := (vr : ℂ)) (ε := δ')).isOpen_compl
      (Set.disjoint_left.2 fun z h1 (h2 : z ∉ closedBall (vr : ℂ) δ') => h2 (ball_subset_closedBall h1)) hsplit
      ⟨F y, hyimg, hy1⟩
  have hwK' := hIn w hwK (hWU hwW).1.2
  have hwB : c.1 w ∈ ball (vr : ℂ) δ := ball_subset_ball hδ'I.2.le (hin ⟨w, hwW, rfl⟩)
  exact hball hwB (subset_closure hwK')

end InteractingSLE.Theorem14.SB.FinRel
