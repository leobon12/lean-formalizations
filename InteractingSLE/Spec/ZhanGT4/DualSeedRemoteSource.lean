/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedRemoteRegularity

/-!
# Positive-time seed rates and original-source variational equations

Packet PROVE-ZHAN-GT4-A22. These adapters supply the ODE and continuity
inputs of A21 from the integrated seed coordinates and the original flow.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory

namespace InteractingSLE.ZhanGT4

open QuantumZipper (IsForwardSol fwdMap)

/-- An integrated seed coordinate satisfies the force ODE at every positive
time, with the derivative within its lifetime interval at the endpoint. -/
theorem IsSeedCoordinate.hasDerivWithinAt_pos {W V : ℝ → ℝ} {T t : ℝ}
    (h : IsSeedCoordinate W V T) (hW : Continuous W) (ht : t ∈ Ioc (0 : ℝ) T) :
    HasDerivWithinAt V (2 / (V t - W t)) (Ioc 0 T) t := by
  have hc : ContinuousOn (fun u => 2 / (V u - W u)) (Ioc 0 T) :=
    continuousOn_const.div ((h.cont.mono Ioc_subset_Icc_self).sub hW.continuousOn)
      (fun u hu => sub_ne_zero.2 (h.ne u hu))
  have : Fact (t ∈ Icc (0 : ℝ) T) := ⟨Ioc_subset_Icc_self ht⟩
  have he : Ioi (0 : ℝ) ∩ Icc 0 T = Ioc 0 T := by
    ext u
    exact ⟨fun hu => ⟨hu.1, hu.2.2⟩, fun hu => ⟨hu.1, hu.1.le, hu.2⟩⟩
  have hEq := nhdsWithin_inter_of_mem
    (nhdsWithin_le_nhds (Ioi_mem_nhds ht.1) : Ioi (0 : ℝ) ∈ 𝓝[Icc 0 T] t)
  rw [he] at hEq
  have hct := hc t ht
  change Tendsto (fun u => 2 / (V u - W u)) (𝓝[Ioc 0 T] t) (𝓝 (2 / (V t - W t))) at hct
  have hmeas := hc.stronglyMeasurableAtFilter_nhdsWithin (μ := volume) measurableSet_Ioc t
  rw [hEq] at hct hmeas
  have hd := intervalIntegral.integral_hasDerivWithinAt_right (s := Icc 0 T)
    (h.integrable t (Ioc_subset_Icc_self ht))
    hmeas hct
  exact ((hd.const_add (V 0)).congr (fun u hu => h.eq u hu)
    (h.eq t (Ioc_subset_Icc_self ht))).mono Ioc_subset_Icc_self

/-- The original other-source coordinate and its derivative obey the
Loewner equation and the real variational equation on the closed interval. -/
theorem source_gmap_rates {W : ℝ → ℝ} (hW : Continuous W) {p T t : ℝ}
    {v : ℝ → ℂ} (hv : IsForwardSol W (p : ℂ) T v) (ht : t ∈ Icc (0 : ℝ) T) :
    HasDerivWithinAt (fun u => (fwdMap W u p).re + W u)
      (2 / (((fwdMap W t p).re + W t) - W t)) (Icc 0 T) t ∧
    HasDerivWithinAt (fun u => (deriv (fwdMap W u) p).re)
      (-2 * (deriv (fwdMap W t) p).re / (((fwdMap W t p).re + W t) - W t) ^ 2) (Icc 0 T) t := by
  have hT := ht.1.trans ht.2
  have hmap := hasDerivWithinAt_gmap_clock hW hv (a := id) (fun _ hu => hu) ht
    (hasDerivWithinAt_id t (Icc 0 T))
  have hvar := hasDerivWithinAt_deriv_fwdMap_clock hW hv (a := id) (fun _ hu => hu) ht
    (hasDerivWithinAt_id t (Icc 0 T))
  have hf : fwdMap W t p = (((fwdMap W t p).re : ℝ) : ℂ) :=
    Complex.ext rfl (by simpa using fwdMap_real_im hW hv ht)
  have hd : deriv (fwdMap W t) p = (((deriv (fwdMap W t) p).re : ℝ) : ℂ) :=
    Complex.ext rfl (by simpa using (deriv_fwdMap_real hW hv ht).1)
  obtain ⟨δ, hδ, hlow, hp⟩ := exists_aliveDisc_self hv hT
  have hde := deriv_fwdMap_aliveDisc hW hv hδ hlow hp ht
  simp only [id_eq] at hmap hvar
  rw [← hde, hd, hf] at hvar
  rw [hf] at hmap
  have hm := Complex.reCLM.hasFDerivAt.comp_hasDerivWithinAt t hmap
  have hv' := Complex.reCLM.hasFDerivAt.comp_hasDerivWithinAt t hvar
  constructor
  · simpa only [Function.comp_def, Complex.reCLM_apply, Complex.add_re, Complex.ofReal_re,
      Complex.ofReal_one, one_mul, ← Complex.ofReal_ofNat,
      ← Complex.ofReal_div, add_sub_cancel_right] using hm
  · simpa only [Function.comp_def, Complex.reCLM_apply, ← Complex.ofReal_ofNat, ← Complex.ofReal_mul,
      ← Complex.ofReal_div, ← Complex.ofReal_pow, ← Complex.ofReal_neg, Complex.ofReal_re,
      add_sub_cancel_right, neg_div, neg_mul, one_mul] using hv'

end InteractingSLE.ZhanGT4
