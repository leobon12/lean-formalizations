/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RdStgEngine
import InteractingSLE.Spec.Sec5.MarkovFlow
import InteractingSLE.GFF.PushforwardLoewner

/-!
# GW2's stage identity: the stage chain (deterministic part)

Packet PROVE-GW2-RELDET, ruling R106. The whole physical schedule is ONE explored Loewner chain (root `0`), read in
the counterflow's joint chart `c = relChart rec`, where it has the relative driver `R`. Stage `n` starts at the relative
time `a = a(T_n)` (`T_n` the deterministic physical start of piece `n`). Pathwise, stage `n` is the relative chain
restarted at `a`:

* `stgDrv R a u = R (a + u) − R a`: the stage relative driver (from `0`);
* `stgChart c R a = c.loewner (rpath R) a`: the stage chart — the joint chart followed by the centred Loewner map of
  the relative driver at `a` (`f_a ∘ Ψ`);
* **`stgChart_inv_image`** (the stage shape): the stage chart's inverse carries the complement of the stage hull at
  `u` onto the joint chart's inverse image of the complement of the WHOLE relative hull at `a + u`
  (`Sec5.Markov.image_fwdMapInv_diff_fwdHull`, the Loewner domain Markov property). With GB6's shape at the physical
  time `T_n + t` (`H \ B = Ψ⁻¹(H \ K^R_{a(T_n+t)})`) this is the stage shape `hBK` of
  `GW2Rd.hasRelSafe_of_lines_rec` for the stage chart;
* `isConformal_stgChart`, `continuous_stgDrv`, `stgDrv_zero`, `measurable_stgDrv` (at a random start).

Deterministic; no probabilistic content.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull fwdMap fwdMapInv)

namespace InteractingSLE.Theorem14.GW2Rd

/-! ### The stage relative driver -/

/-- **The stage relative driver**: the relative driver restarted at the relative time `a`. -/
def stgDrv (R : ℝ≥0 → ℝ) (a : ℝ≥0) (u : ℝ≥0) : ℝ := R (a + u) - R a

theorem stgDrv_zero (R : ℝ≥0 → ℝ) (a : ℝ≥0) : stgDrv R a 0 = 0 := by
  simp only [stgDrv, add_zero, sub_self]

theorem continuous_stgDrv {R : ℝ≥0 → ℝ} (hR : Continuous R) (a : ℝ≥0) : Continuous (stgDrv R a) :=
  (hR.comp (continuous_const.add continuous_id)).sub continuous_const

/-- The real path of the stage driver is the restarted real path of the relative driver, on `[0, ∞)`. -/
theorem rpath_stgDrv_eq (R : ℝ≥0 → ℝ) (a : ℝ≥0) {r : ℝ} (hr : 0 ≤ r) :
    Ito.rpath (stgDrv R a) r = Ito.rpath R ((a : ℝ) + r) - Ito.rpath R a := by
  simp only [Ito.rpath, stgDrv, Real.toNNReal_coe]
  congr 2
  rw [← NNReal.coe_inj, NNReal.coe_add, Real.coe_toNNReal _ hr,
    Real.coe_toNNReal _ (add_nonneg a.coe_nonneg hr)]

/-- The stage hull is the hull of the restarted real path. -/
theorem fwdHull_stgDrv {R : ℝ≥0 → ℝ} (a : ℝ≥0) (u : ℝ≥0) :
    fwdHull (Ito.rpath (stgDrv R a)) u =
      fwdHull (fun r => Ito.rpath R ((a : ℝ) + r) - Ito.rpath R a) u :=
  fwdHull_eq_of_eqOn u.coe_nonneg (lt_add_one (u : ℝ)) fun _ hr => rpath_stgDrv_eq R a hr.1

/-- **The stage driver at a random start is measurable** (the relative driver measurable at every time and
continuous, the start measurable). -/
theorem measurable_stgDrv {Ω : Type*} [MeasurableSpace Ω] {R : ℝ≥0 → Ω → ℝ} (hRm : ∀ t, Measurable (R t))
    (hRc : ∀ ω, Continuous fun t => R t ω) {a : Ω → ℝ≥0} (ha : Measurable a) (u : ℝ≥0) :
    Measurable fun ω => stgDrv (fun t => R t ω) (a ω) u := by
  have hj : Measurable fun p : ℝ≥0 × Ω => R p.1 p.2 :=
    measurable_uncurry_of_continuous_of_measurable (u := fun t ω => R t ω) hRc hRm
  exact (hj.comp ((ha.add measurable_const).prodMk measurable_id)).sub (hj.comp (ha.prodMk measurable_id))

/-! ### The stage chart -/

/-- **The stage chart**: the chart `c` followed by the centred Loewner map of the relative driver at `a`. -/
def stgChart (c : Chart) (R : ℝ≥0 → ℝ) (a : ℝ≥0) : Chart := c.loewner (Ito.rpath R) a

theorem isConformal_stgChart {c : Chart} (hc : c.IsConformal) {R : ℝ≥0 → ℝ} (hR : Continuous R) (hR0 : R 0 = 0)
    (a : ℝ≥0) : (stgChart c R a).IsConformal :=
  hc.loewner (hR.comp continuous_real_toNNReal) (by simp [hR0]) a.coe_nonneg

theorem stgChart_inv (c : Chart) (R : ℝ≥0 → ℝ) (a : ℝ≥0) (w : ℂ) :
    (stgChart c R a).2.1 w = c.2.1 (fwdMapInv (Ito.rpath R) a w) := rfl

/-- **The stage shape**: the stage chart's inverse carries the complement of the stage hull at `u` onto the chart's
inverse image of the complement of the whole relative hull at `a + u`. -/
theorem stgChart_inv_image (c : Chart) {R : ℝ≥0 → ℝ} (hR : Continuous R) (hR0 : R 0 = 0) (a u : ℝ≥0) :
    (stgChart c R a).2.1 '' (H \ fwdHull (Ito.rpath (stgDrv R a)) u) =
      c.2.1 '' (H \ fwdHull (Ito.rpath R) ((a + u : ℝ≥0) : ℝ)) := by
  have hw : Continuous (Ito.rpath R) := hR.comp continuous_real_toNNReal
  have hw0 : Ito.rpath R 0 = 0 := by simp [Ito.rpath, hR0]
  have e : (stgChart c R a).2.1 = c.2.1 ∘ fwdMapInv (Ito.rpath R) a := rfl
  rw [e, image_comp, fwdHull_stgDrv, Sec5.Markov.image_fwdMapInv_diff_fwdHull hw hw0 a.coe_nonneg u.coe_nonneg,
    NNReal.coe_add]

end InteractingSLE.Theorem14.GW2Rd
