/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4SafeRLambdaLanding
import InteractingSLE.Spec.Sec7.R5WallCore

/-! # GW4: ambient seed bounds also at real physical landings -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Filter Topology Metric Complex
open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv)

namespace InteractingSLE.Theorem14.GW4Fix

open Sec7.R5Lift Sec7.PocketStopSide MartChar.RealFlow

/-- An original real point with an alive forward characteristic is off
the closed hull, by the existing alive-disc neighborhood theorem. -/
theorem notMem_closure_fwdHull_of_surviving_real {W : ℝ → ℝ} (hW : Continuous W)
    {s x : ℝ} (hs : 0 ≤ s) {a : ℝ → ℂ} (ha : QuantumZipper.IsForwardSol W x s a) :
    (x : ℂ) ∉ closure (fwdHull W s) := by
  obtain ⟨r, hr, hBall⟩ := Metric.mem_nhdsWithin_iff.1 (ZhanGT4.eventually_not_mem_fwdHull hW hs ha)
  intro hx
  obtain ⟨z, hzK, hzx⟩ := Metric.mem_closure_iff.1 hx r hr
  exact (hBall ⟨by simpa only [mem_ball, dist_comm] using hzx, hzK.1⟩).2 hzK

/-- If a whole open boundary interval lands on the closed ambient hull,
its reflected ambient coordinates lie strictly between the ambient seeds.
This strengthens the H-landing version of R.5 to original-real contacts. -/
theorem ambient_seed_interval_of_closed_landings {cur : Chart} (hcur : cur.IsConformal)
    {Fc : ℂ → ℂ} (hFc : EqOn Fc cur.2.1 H) (hFcc : ContinuousOn Fc Hbar)
    {W : ℝ → ℝ} {η : ℝ → ℂ} (hη : IsLoewnerTrace W η) (hW : Continuous W)
    (hW0 : W 0 = 0) {T : ℝ} (hT : 0 ≤ T)
    (hK : (cur.dom : Set ℂ) ⊆ H \ fwdHull W T) {a b : ℝ}
    (hland : ∀ u ∈ Ioo a b, Fc u ∉ H \ fwdHull W T)
    (hclosed : ∀ u ∈ Ioo a b, Fc u ∈ closure (fwdHull W T)) :
    ∀ u ∈ Ioo a b, ∀ x' : ℝ,
      Tendsto (fun z => fwdMap W T (cur.2.1 z)) (𝓝[H] (u : ℂ)) (𝓝 (x' : ℂ)) →
      x' ∈ Ioo (-rightImg (fun r => -W r) 0 T - W T) (rightImg W 0 T - W T) := by
  let S : ℂ → ℂ := fun z => fwdMap W T (cur.2.1 z)
  let g : ℂ → ℂ := extendFrom H S
  let φ : ℝ → ℝ := fun u => (g u).re
  have hdat : ∀ u ∈ Ioo a b, Tendsto S (𝓝[H] (u : ℂ)) (𝓝 (g u)) ∧
      (g u).im = 0 ∧ 0 < deriv φ u := by
    intro u hu
    obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 isOpen_Ioo u hu
    obtain ⟨-, hgc, hgr, hm, hi, hgd, hlim⟩ := reflect_data_of_notMem (x := u) (ρ := ρ)
      hcur hFc hFcc hη hW hW0 hT hK fun v hv => hland v (hball (mem_ball_of_ofReal_mem_ball hv))
    obtain ⟨c, hc, hder⟩ := exists_pos_hasDerivAt_re_boundary hρ hgd hgc hgr hm hi
    exact ⟨hlim u ⟨ofReal_mem_Hbar u, mem_ball_self hρ⟩,
      hgr u (mem_ball_self hρ) (ofReal_im u), by change 0 < deriv (fun v : ℝ => (g v).re) u; rwa [hder.deriv]⟩
  have hφlim (u : ℝ) (hu : u ∈ Ioo a b) : Tendsto S (𝓝[H] (u : ℂ)) (𝓝 (φ u : ℂ)) := by
    have he : g u = (φ u : ℂ) := Complex.ext rfl (by rw [ofReal_im]; exact (hdat u hu).2.1)
    rw [← he]
    exact (hdat u hu).1
  have hφbd : ∀ u ∈ Ioo a b,
      -rightImg (fun r => -W r) 0 T - W T ≤ φ u ∧ φ u ≤ rightImg W 0 T - W T := by
    intro u hu
    by_contra h
    have hside : φ u < -rightImg (fun r => -W r) 0 T - W T ∨ rightImg W 0 T - W T < φ u := by
      simpa only [not_and_or, not_le] using h
    obtain ⟨x, v, -, hv, hvφ⟩ := Sec7.R5Wall.exists_surviving_of_wall hW hT hside
    have hStoH : Tendsto S (𝓝[H] (u : ℂ)) (𝓝[H] (φ u : ℂ)) :=
      tendsto_nhdsWithin_iff.2 ⟨hφlim u hu, eventually_nhdsWithin_of_forall fun y hy =>
        QuantumZipper.FwdHolo.mapsTo_fwdMap hW hT (hK (hcur.inv_mem_dom hy))⟩
    have hInv := tendsto_inverse_of_surviving_real hW hW0 hT hv
    rw [hvφ] at hInv
    have hPhys : Tendsto cur.2.1 (𝓝[H] (u : ℂ)) (𝓝 (x : ℂ)) :=
      (hInv.mono_right nhdsWithin_le_nhds |>.comp hStoH).congr'
        (eventually_nhdsWithin_of_forall fun y hy => QuantumZipper.RS.fwdMapInv_fwdMap hW hW0 hT
          (hK (hcur.inv_mem_dom hy)))
    have hFcLim : Tendsto cur.2.1 (𝓝[H] (u : ℂ)) (𝓝 (Fc u)) :=
      ((hFcc u (ofReal_mem_Hbar u)).tendsto.mono_left (nhdsWithin_mono _ QuantumZipper.H_subset_Hbar)).congr'
        (eventually_nhdsWithin_of_forall fun y hy => hFc hy)
    have := nhdsWithin_H_neBot u
    have hEq := tendsto_nhds_unique hFcLim hPhys
    exact notMem_closure_fwdHull_of_surviving_real hW hT hv (hEq ▸ hclosed u hu)
  have hφc : ContinuousOn φ (Ioo a b) :=
    continuousOn_of_tendsto_nhdsWithin_H (f := fun z => (S z).re) fun u hu =>
      (continuous_re.tendsto _).comp (hdat u hu).1
  have hm : StrictMonoOn φ (Ioo a b) := strictMonoOn_of_deriv_pos (convex_Ioo a b) hφc (by
    intro u hu
    rw [isOpen_Ioo.interior_eq] at hu
    exact (hdat u hu).2.2)
  intro u hu x' hx'
  have := nhdsWithin_H_neBot u
  have he : x' = φ u := congrArg Complex.re (tendsto_nhds_unique hx' (hφlim u hu))
  rw [he]
  obtain ⟨v, hav, hvu⟩ := exists_between hu.1
  obtain ⟨w, huw, hwb⟩ := exists_between hu.2
  exact ⟨(hφbd v ⟨hav, hvu.trans hu.2⟩).1.trans_lt (hm ⟨hav, hvu.trans hu.2⟩ hu hvu),
    (hm hu ⟨hu.1.trans huw, hwb⟩ huw).trans_le (hφbd w ⟨hu.1.trans huw, hwb⟩).2⟩

end InteractingSLE.Theorem14.GW4Fix
