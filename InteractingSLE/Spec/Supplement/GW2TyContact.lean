/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2KxB0Stmt
import InteractingSLE.Spec.Supplement.GW2PsmContact
import InteractingSLE.Spec.Supplement.GW2PsmTip

/-!
# Claim(k)'s root-`x` base: the root piece's kernel-side readings at index `0`

Packet PROVE-GW2-RELDET (round 35, decision D62), for PROVE-GW2-GEOM2's root-`x` base (its handoff, "For RELDET
(D62)"). **`sampleContactRoot0XStatement`** proves GEOM2's `GW2Kx.SampleContactRoot0XStatement` as stated: at one
sample of the history `l = []` on success, with BR4a's datum at index `0` (the launch chart `recenter x`, the kernel
counterflow `Wk` with trace `γk`, the clock `ℓ` up to the first tip at `x`) and the product-form no-contact reading up
to the root piece's end `T`, there is `t₀` with

* `ℓ t₀ = s`: the no-contact reading at `u = 0` (the explored trace starts at `0`) is `x · α v + 1 ≠ 0` for `v ≤ s`,
  so `s` is before the counterflow's first tip at `x` (`GW2Kx.lt_firstTipTime_pt_iff`), hence in the clock's range;
* `γk t₀ ∈ ℍ`: the kernel tip at `t₀` corresponds to the counterflow's tip `−(α s)⁻¹ ∈ ℍ` at `s`, which lies in the
  domain `ℍ` of `recenter x` (`GW2Psm.trace_mem_H_of_tipAt`);
* `T < firstContactTime α (sphereInv ∘ γk '' [0, t₀])`: the root piece's trace is the explored trace up to `T`
  (`GW2Kb.chosenTrace_eq_schedTr`), translated by `x` it misses the inverted counterflow prefix (the no-contact
  reading), so `GW2Psm.lt_firstContactTime_launch` applies with the boundary extension `p ↦ p + x`; the root piece
  lives past `T` on success (`GW2Kb.oldSuccess_nil_iff`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

universe u

namespace InteractingSLE.Theorem14.GW2Rd

open GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31 GW2TipSystem.Swc GW2Schedule GW2Tip Exist Exist.Staged
  Exist.StagedLaw GW2Omx GW2Xk GW2Kb
open Supp8.GB6 (sphereInv firstContactTime)

/-- **GEOM2's `SampleContactRoot0XStatement`**: the root piece's kernel-side readings at index `0` at a root `x ≥ 0`.
-/
theorem sampleContactRoot0XStatement : GW2Kx.SampleContactRoot0XStatement.{u} := by
  intro Ω _ c r a ω hx0 hold hgood hc0 hreg α hα hW' hW'0 hcα hcα0 hsζ hs0 hαs hηe hnc Wk γk hWk hWk0 hγk hγk0 ℓ
    hℓc hℓm hℓr hiff
  -- the clock reaches `s`
  have hη0 : GW2Rd.schedTr c r [] a ω 0 = 0 := hηe.1
  have hgap : ∀ v ≤ c.s, ((rootPt r.1 : ℝ) : ℂ) * c.α ω v + 1 ≠ 0 := fun v hv => by
    have h := hnc v ⟨zero_le, hv⟩ 0 zero_le
    rw [hη0, add_zero, mul_comm] at h
    exact h
  have hsr : c.s ∈ range ℓ := by
    rw [hℓr]
    exact (GW2Kx.lt_firstTipTime_pt_iff hcα hW' hW'0 (rootPt r.1) c.s).2 hgap
  obtain ⟨t₀, ht₀⟩ := hsr
  have hℓ0 : ℓ 0 = 0 := GW2Sgk.clock_zero_of_range hℓm hℓr
  have ht₀pos : 0 < t₀ := by
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t₀) with h | h
    · rw [← h, hℓ0] at ht₀
      exact absurd ht₀.symm hs0.ne'
    · exact h
  -- the launch chart `recenter x` and its boundary extension `p ↦ p + x`
  have hconf : (Chart.id.recenter (rootPt r.1)).IsConformal := Chart.isConformal_id.recenter (rootPt r.1)
  have hf : ∀ p ∈ Hbar, Tendsto (Chart.id.recenter (rootPt r.1)).2.1 (𝓝[H] p)
      (𝓝 ((fun q : ℂ => q + ((rootPt r.1 : ℝ) : ℂ)) p)) := fun p _ =>
    (CounterflowRange.continuous_recenter_id_inv (rootPt r.1)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  -- the interior kernel tip
  have hαs0 : c.α ω c.s ≠ 0 := fun h => by
    have : (0 : ℝ) < (c.α ω c.s).im := hαs
    rw [h, Complex.zero_im] at this
    exact lt_irrefl 0 this
  have hzH : -(c.α ω c.s)⁻¹ ∈ H := by
    show 0 < (-(c.α ω c.s)⁻¹).im
    have h1 : 0 < (c.α ω c.s).im := hαs
    rw [Complex.neg_im, Complex.inv_im, neg_div, neg_neg]
    exact div_pos h1 (Complex.normSq_pos.2 hαs0)
  have hz : -(c.α ω c.s)⁻¹ ∈ ((Chart.id.recenter (rootPt r.1)).dom : Set ℂ) := by
    rw [GW2Kx.coe_dom_recenter_id]
    exact hzH
  have htip : ((Chart.id.recenter (rootPt r.1)).trans infinitySourceChart).tipAt Wk t₀ (-(c.α ω c.s)⁻¹) := by
    rw [hiff, ht₀]
    exact GW2Psm.tipAt_infinitySourceChart_of_trace hW' hW'0 hcα hαs0
  have hγt₀ : γk t₀ ∈ H := GW2Psm.trace_mem_H_of_tipAt hconf hf hWk hWk0 hγk (hγk0 t₀ ht₀pos) htip hz
  -- the root piece lives past `T`, and its trace is the explored trace up to `T`
  have hTζ := (GW2Kb.oldSuccess_nil_iff c r a ω).1 hold
  obtain ⟨T', hTT', hT'ζ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hTζ
  have hTT'' : historyTime c r [] < T' := by exact_mod_cast hTT'
  have hαc : ContinuousOn α (Icc 0 T') := hα.2.1.mono fun u hu => (ENNReal.coe_le_coe.2 hu.2).trans hT'ζ.le
  have htr : ∀ u ≤ historyTime c r [],
      (fun q => ((rootPt r.1 : ℝ) : ℂ) + GW2Rd.schedTr c r [] a ω q) (0 + u) =
        (fun q : ℂ => q + ((rootPt r.1 : ℝ) : ℂ)) (α u) := fun u hu => by
    simp only [zero_add]
    rw [GW2Kb.chosenTrace_eq_schedTr c r a hold hgood hc0 hreg hα hηe hu, add_comm]
  have hphys : ∀ u ≤ historyTime c r [], ∀ v ≤ c.s, 0 < v →
      (fun q => ((rootPt r.1 : ℝ) : ℂ) + GW2Rd.schedTr c r [] a ω q) (0 + u) ≠ -(c.α ω v)⁻¹ := by
    intro u hu v hv hv0 heq
    simp only [zero_add] at heq
    apply hnc v ⟨zero_le, hv⟩ u hu
    rw [heq]
    field_simp [hcα0 v hv0]
    ring
  exact ⟨t₀, ht₀, hγt₀, GW2Psm.lt_firstContactTime_launch
    (ηe := fun q => ((rootPt r.1 : ℝ) : ℂ) + GW2Rd.schedTr c r [] a ω q) (T := 0) hf hWk hWk0 hγk hγk0 hW' hW'0 hcα
    hcα0 hℓm hℓ0 hiff ht₀ hTT'' hαc htr hphys⟩

end InteractingSLE.Theorem14.GW2Rd
