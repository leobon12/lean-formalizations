/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop513Trace
import InteractingSLE.Spec.Sec7.StripSysField

/-!
# Geometry and bounded harmonic means of the strip counterflow chart

The exceptional set consists of the image of the old exceptional set and the
point `-1`, where the inverse Möbius chart has its pole.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped Real NNReal ENNReal

namespace InteractingSLE.Sec5.Prop513Field

open QuantumZipper Sec4 Sec7.StripSysField

/-- The real inverse of `M_q`. -/
def realInv (q x : ℝ) : ℝ := -(1 + q) / (x + 1)

/-- Boundary data of a signed chart transport with coefficients `(-1,a,k)`. -/
def data (q a k : ℝ) (b : ℝ → ℝ) (x : ℝ) : ℝ :=
  -b (realInv q x) + a + k * liftBoundary (realInv q x)

/-- The old exceptional points mapped by `M_q`, together with its inverse pole. -/
def jumps (q : ℝ) (J : Finset ℝ) : Finset ℝ :=
  insert (-1) (J.image fun x => -1 - (1 + q) / x)

theorem isConformal {q : ℝ} (hq : 0 < q) : (stripCounterflowChart q).IsConformal := by
  refine ⟨fun z hz => ?_, (fun z hz => stripCounterflowChart_inv_mem_H hq hz), fun z hz => ?_⟩
  · have hz1 : z + 1 ≠ 0 := by
      intro h
      have he := congrArg Complex.im h
      simp only [Complex.add_im, Complex.one_im, add_zero, Complex.zero_im] at he
      exact (ne_of_gt hz) he
    have hd : DifferentiableAt ℂ (fun w : ℂ => (w + 1)⁻¹) z :=
      (differentiableAt_inv hz1).comp z (differentiableAt_id.add_const (1 : ℂ))
    exact (hd.const_mul (-(1 + (q : ℂ)))).differentiableWithinAt
  · exact stripCounterflowChart_fwd_inv hq (fun he => by
      have hi := congrArg Complex.im he
      simp only [Complex.neg_im, Complex.one_im, neg_zero] at hi
      exact (ne_of_gt hz) hi)

theorem dom_eq {q : ℝ} (hq : 0 < q) : (stripCounterflowChart q).dom = upperHalfPlaneOpens := by
  apply SetLike.coe_injective
  rw [(isConformal hq).coe_dom, image_stripCounterflowChart_inv hq]
  rfl

theorem inv_ofReal (q x : ℝ) :
    (stripCounterflowChart q).2.1 (x : ℂ) = (realInv q x : ℝ) := by
  simp only [stripCounterflowChart, realInv, div_eq_mul_inv, Complex.ofReal_mul,
    Complex.ofReal_neg, Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_inv]

theorem realInv_ne_zero {q x : ℝ} (hq : 0 < q) (hx : x ≠ -1) : realInv q x ≠ 0 :=
  div_ne_zero (neg_ne_zero.2 (by linarith)) (fun he => hx (eq_neg_of_add_eq_zero_left he))

theorem realInv_notMem {q x : ℝ} (hq : 0 < q) {J : Finset ℝ}
    (hx : x ∉ jumps q J) : realInv q x ∉ J := by
  intro hm
  have hx1 : x ≠ -1 := fun he => hx (he ▸ Finset.mem_insert_self _ _)
  have hc : 1 + q ≠ 0 := by linarith
  have hd : x + 1 ≠ 0 := fun he => hx1 (eq_neg_of_add_eq_zero_left he)
  apply hx
  apply Finset.mem_insert_of_mem
  refine Finset.mem_image.2 ⟨realInv q x, hm, ?_⟩
  dsimp only [realInv]
  field_simp
  ring

theorem continuousAt_realInv {q x : ℝ} (hx : x ≠ -1) : ContinuousAt (realInv q) x :=
  continuousAt_const.div (continuousAt_id.add continuousAt_const)
    (fun he => hx (eq_neg_of_add_eq_zero_left he))

theorem isPiecewiseConstant_data {q : ℝ} (hq : 0 < q) (a k : ℝ)
    {b : ℝ → ℝ} {J : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b J) :
    IsPiecewiseConstantBoundaryData (data q a k b) (jumps q J) := by
  intro x hx
  have hx1 : x ≠ -1 := fun he => hx (he ▸ Finset.mem_insert_self _ _)
  have hlim := (continuousAt_realInv (q := q) hx1).tendsto
  filter_upwards [hlim.eventually (hb _ (realInv_notMem hq hx)),
    hlim.eventually (eventually_liftBoundary_eq (realInv_ne_zero hq hx1))] with y hy hl
  simp only [data, hy, hl]

theorem tendsto_inv_H {q x : ℝ} (hq : 0 < q) (hx : x ≠ -1) :
    Tendsto (stripCounterflowChart q).2.1 (𝓝[H] (x : ℂ))
      (𝓝[H] (realInv q x : ℂ)) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_,
    eventually_nhdsWithin_of_forall fun z hz => stripCounterflowChart_inv_mem_H hq hz⟩
  rw [← inv_ofReal]
  have hx1 : (x : ℂ) + 1 ≠ 0 := by
    exact_mod_cast (show x + 1 ≠ 0 from fun he => hx (eq_neg_of_add_eq_zero_left he))
  exact (continuousAt_const.mul
    ((continuousAt_id.add continuousAt_const).inv₀ hx1)).tendsto.mono_left nhdsWithin_le_nhds

theorem continuousOn_lift_inv {q : ℝ} (hq : 0 < q) :
    ContinuousOn (fun z => (stripCounterflowChart q).2.2 ((stripCounterflowChart q).2.1 z)) H :=
  continuousOn_infinitySourceChart_lift'.comp (isConformal hq).1.continuousOn
    (fun _ hz => stripCounterflowChart_inv_mem_H hq hz)

/-- The bounded harmonic mean, with its exact finite-exception boundary limits. -/
theorem harmonicExtension {q : ℝ} (hq : 0 < q) (a k : ℝ)
    {b : ℝ → ℝ} {J : Finset ℝ} {u : ℂ → ℝ}
    (hu : IsBoundedHarmonicExtension b J u) :
    IsBoundedHarmonicExtension (data q a k b) (jumps q J)
      (fun z => -u ((stripCounterflowChart q).2.1 z) + a +
        k * (stripCounterflowChart q).2.2 ((stripCounterflowChart q).2.1 z)) := by
  have hc := isConformal hq
  have hcomp := LQGMetric.harmonicOnNhd_comp_holo QuantumZipper.isOpen_H QuantumZipper.isOpen_H
    hu.1 hc.1 (fun z hz => stripCounterflowChart_inv_mem_H hq hz)
  have hlift := LQGMetric.harmonicOnNhd_comp_holo QuantumZipper.isOpen_H QuantumZipper.isOpen_H
    harmonicOnNhd_infinitySourceChart_lift hc.1 (fun z hz => stripCounterflowChart_inv_mem_H hq hz)
  obtain ⟨C, hC⟩ := hu.2.1
  refine ⟨fun z hz => ?_, ⟨C + |a| + |k| * (2 * Real.pi), fun z hz => ?_⟩,
    fun x hx => ?_⟩
  · convert ((hcomp z hz).neg.add (InnerProductSpace.harmonicAt_const a)).add
      ((hlift z hz).const_smul (c := k)) using 1
    rfl
  · calc
      _ ≤ |u ((stripCounterflowChart q).2.1 z)| + |a| +
          |k| * |(stripCounterflowChart q).2.2 ((stripCounterflowChart q).2.1 z)| := by
        simpa only [abs_neg, abs_mul] using abs_add_three
          (-u ((stripCounterflowChart q).2.1 z)) a
          (k * (stripCounterflowChart q).2.2 ((stripCounterflowChart q).2.1 z))
      _ ≤ C + |a| + |k| * (2 * Real.pi) := by
        gcongr
        · exact hC _ (stripCounterflowChart_inv_mem_H hq hz)
        · exact abs_infinitySourceChart_lift_le _
  · have hx1 : x ≠ -1 := fun he => hx (he ▸ Finset.mem_insert_self _ _)
    have hlim := tendsto_inv_H hq hx1
    exact (((hu.2.2 _ (realInv_notMem hq hx)).comp hlim).neg.add_const a).add
      (((tendsto_infinitySourceChart_lift (realInv_ne_zero hq hx1)).comp hlim).const_mul k)

end InteractingSLE.Sec5.Prop513Field
