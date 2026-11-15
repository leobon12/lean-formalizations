/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.PocketShapeFinPartition

/-!
# Connectedness of the two closed pieces of a Jordan boundary

PROVE-POCKETSHAPE continuation. The existing Jordan coordinate parametrizes the boundary
minus one contact by the real line. The real-line partition lemma then recovers the two
closed arcs without assuming connectedness of either piece in the definition.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Bornology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)
open LQGMetric.JordanMap (IsJordanCurve)

namespace InteractingSLE.Theorem14.PocketShapeFin

/-- The closed-half-plane version of `GW3.tendsto_cobounded_of_coord`, needed for
the real boundary parametrization rather than just interior approaches. -/
theorem tendsto_coord_on_Hbar {C : Set ℂ} (hCb : IsBounded C)
    {ψ G : ℂ → ℂ} {e : ℂ} (hψc : ContinuousOn ψ (closure C \ {e}))
    (hψG : ∀ w ∈ Hbar, ψ (G w) = w) (hGm : MapsTo G Hbar (closure C \ {e})) :
    Tendsto G (cobounded ℂ ⊓ 𝓟 Hbar) (𝓝 e) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  let K : Set ℂ := closure C ∩ (ball e ε)ᶜ
  have hK : IsCompact K := hCb.isCompact_closure.inter_right isOpen_ball.isClosed_compl
  have hKs : K ⊆ closure C \ {e} := fun z hz =>
    ⟨hz.1, fun he => hz.2 (by rw [mem_singleton_iff.1 he]; exact mem_ball_self hε)⟩
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hψc.mono hKs)
  have hev : ∀ᶠ w : ℂ in cobounded ℂ, M < ‖w‖ :=
    tendsto_norm_cobounded_atTop.eventually_gt_atTop M
  filter_upwards [mem_inf_of_left hev, mem_inf_of_right (mem_principal_self Hbar)] with w hw hwH
  by_contra hn
  have hwK : G w ∈ K := ⟨(hGm hwH).1, fun he => hn (mem_ball.1 he)⟩
  have hbound := hM _ hwK
  rw [hψG w hwH] at hbound
  exact (not_lt_of_ge hbound) hw

/-- The two closed pieces of a Jordan boundary meeting exactly at two distinct points
are connected, as are the pieces with those two points deleted. -/
theorem connected_parts_of_jordan {C A B : Set ℂ} (hCo : IsOpen C)
    (hCc : IsConnected C) (hCb : IsBounded C) (hJ : IsJordanCurve (frontier C))
    (hA : IsClosed A) (hB : IsClosed B) (hfr : frontier C = A ∪ B)
    {a e : ℂ} (hAB : A ∩ B = {a, e}) (hae : a ≠ e)
    (hAn : (A \ {a, e}).Nonempty) (hBn : (B \ {a, e}).Nonempty) :
    (IsPreconnected A ∧ IsPreconnected (A \ {a, e})) ∧
      (IsPreconnected B ∧ IsPreconnected (B \ {a, e})) := by
  obtain ⟨p, hp⟩ := hCc.nonempty
  have hDeq := connectedComponentIn_compl_frontier_eq hCo hCc hp
  have hpΓ : p ∈ (frontier C)ᶜ := fun hpf => (hCo.frontier_eq ▸ hpf).2 hp
  have haAB : a ∈ A ∩ B := by rw [hAB]; exact Or.inl rfl
  have heAB : e ∈ A ∩ B := by rw [hAB]; exact Or.inr rfl
  have haΓ : a ∈ frontier C := hfr ▸ Or.inl haAB.1
  have heΓ : e ∈ frontier C := hfr ▸ Or.inl heAB.1
  obtain ⟨ψ, G, hψc, -, hGc, hGm, hGψ, hψG, hconf, hreal, hψa, -⟩ :=
    Sec6.exists_jordanCoord hJ hpΓ (by rw [hDeq]; exact hCb) heΓ haΓ
  rw [hDeq] at hψc hGm hGψ hconf
  let f : ℝ → ℂ := fun x => G x
  have hfc : Continuous f := hGc.comp_continuous Complex.continuous_ofReal GB11Chart.ofReal_mem_Hbar
  have hfi : Function.Injective f := by
    intro x y hxy
    apply Complex.ofReal_injective
    rw [← hψG x (GB11Chart.ofReal_mem_Hbar x), ← hψG y (GB11Chart.ofReal_mem_Hbar y)]
    exact congrArg ψ hxy
  have hf0 : f 0 = a := by
    change G (0 : ℂ) = a
    rw [← hψa]
    exact hGψ a ⟨frontier_subset_closure haΓ, hae⟩
  have hfrange : range f = (A ∪ B) \ {e} := by
    apply Subset.antisymm
    · rintro _ ⟨x, rfl⟩
      have hm := hGm (GB11Chart.ofReal_mem_Hbar x)
      refine ⟨?_, hm.2⟩
      rw [← hfr, hCo.frontier_eq]
      refine ⟨hm.1, fun hz => ?_⟩
      have hh := hconf.2.mapsTo hz
      rw [hψG x (GB11Chart.ofReal_mem_Hbar x)] at hh
      change (0 : ℝ) < (x : ℂ).im at hh
      exact (lt_irrefl (0 : ℝ)) (by simpa only [Complex.ofReal_im] using hh)
    · intro z hz
      have hzΓ : z ∈ frontier C := hfr ▸ hz.1
      have hzcl : z ∈ closure C \ {e} := ⟨frontier_subset_closure hzΓ, hz.2⟩
      have him : (ψ z).im = 0 := hreal z ⟨hzΓ, hz.2⟩
      have hcast : (((ψ z).re : ℝ) : ℂ) = ψ z := Complex.ext (by simp) (by simp [him])
      refine ⟨(ψ z).re, ?_⟩
      change G (((ψ z).re : ℝ) : ℂ) = z
      rw [hcast, hGψ z hzcl]
  have hGinf := tendsto_coord_on_Hbar hCb hψc hψG hGm
  have hft : Tendsto f atTop (𝓝 e) := hGinf.comp (tendsto_inf.2
    ⟨RCLike.tendsto_ofReal_atTop_cobounded ℂ,
      tendsto_principal.2 (Eventually.of_forall GB11Chart.ofReal_mem_Hbar)⟩)
  have hfb : Tendsto f atBot (𝓝 e) := hGinf.comp (tendsto_inf.2
    ⟨RCLike.tendsto_ofReal_atBot_cobounded ℂ,
      tendsto_principal.2 (Eventually.of_forall GB11Chart.ofReal_mem_Hbar)⟩)
  exact connected_partition_of_real_param hA hB hAB hae hAn hBn hfc hfi hf0 hfrange hft hfb

end InteractingSLE.Theorem14.PocketShapeFin
