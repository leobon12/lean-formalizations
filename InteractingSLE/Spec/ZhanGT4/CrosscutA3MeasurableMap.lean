/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.CrosscutA3MeasurableRecon
import InteractingSLE.Spec.Sec7.FanTipFiberSimul
import InteractingSLE.Spec.Sec7.FanTipFiber
import InteractingSLE.Foundations.Measure.StoppedPathExtension
import QuantumZipper.Proofs.ItoLite.Dynkin

/-!
# A.3.2: the inverse Loewner map at the end of the strip life, as a measurable function of the strip path

Packet PROVE-ZHAN-A35. Source: Astra, *Follow-up proofs and dependency audit*, §A.3.2
(`source/external/AstraIG1/ig1_followup_proofs.txt` L686–L720, ruling R38). The mixture identity (G3) transfers
null sets of strip paths, so the first-swallow crosscut property must be read off the strip path by countably many
measurable operations. Here, for a family `X : α → ℝ≥0 → ℝ` of **continuous** paths with measurable coordinates (in
the application, the dyadic regularization of an arbitrary path, `CrosscutA3Measurable.lean`):

* `truncDrv X n`: the reconstructed chordal driver `reconDrv (X a)` stopped at the chordal time `C(n)` of strip time
  `n` (minus its initial value): continuous in time, measurable in `a`;
* `approxMap X n p a = f_{C(n)}(p)` for this driver, `limMap X p a = lim_n approxMap X n p a`, and the boundary
  values `bdryVal X v a = lim_j limMap X (v + i/(j+1)) a` at real `v`: all measurable in `a`;
* `limMap_eq`, `bdryVal_eq`: if `X a` starts at `0`, `reconEnd (X a) = σ` is finite and `W` is a continuous driver
  with `W 0 = 0` that agrees with the reconstruction on `[0, σ)`, then `limMap X p a = f_σ(p)` (for `p ∈ ℍ`), and
  `bdryVal X v a = F(v)` for every continuous extension `F` of `f_σ` to `ℍ̄`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory Complex
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A35

open A34 QuantumZipper

/-- The approach point `v + i/(j+1)` above a real `v`. -/
def apprPt (v : ℝ) (j : ℕ) : ℂ := (v : ℂ) + (((j : ℝ) + 1)⁻¹ : ℝ) * I

theorem apprPt_mem_H (v : ℝ) (j : ℕ) : apprPt v j ∈ H := by
  show 0 < (apprPt v j).im
  simp only [apprPt, add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero, zero_add]
  positivity

theorem tendsto_apprPt (v : ℝ) : Tendsto (apprPt v) atTop (𝓝[Hbar] (v : ℂ)) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun j =>
    (show (0 : ℝ) < (apprPt v j).im from apprPt_mem_H v j).le⟩
  have h : Tendsto (fun j : ℕ => (((j : ℝ) + 1)⁻¹ : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.congr fun j => by rw [one_div]
  have h2 := (continuous_ofReal.tendsto 0).comp h
  have h3 : Tendsto (apprPt v) atTop (𝓝 ((v : ℂ) + ((0 : ℝ) : ℂ) * I)) :=
    (tendsto_const_nhds (x := (v : ℂ))).add (h2.mul_const I)
  rwa [ofReal_zero, zero_mul, add_zero] at h3

section Family

variable {α : Type*} [MeasurableSpace α] {X : α → ℝ≥0 → ℝ}

/-! ### The reconstruction is measurable -/

theorem measurable_reconClock (hXm : ∀ t, Measurable fun a => X a t) (hXc : ∀ a, Continuous (X a)) (t : ℝ) :
    Measurable fun a => reconClock (X a) t :=
  Dynkin.measurable_intervalIntegral_of_continuous
    (Y := fun r a => Real.exp (2 * (Strip.extPath (X a) r - r)))
    (fun _ => Real.measurable_exp.comp (measurable_const.mul ((hXm _).sub measurable_const)))
    (fun a => continuous_clockIntegrand (hXc a)) 0 t

theorem measurable_reconMark (hXm : ∀ t, Measurable fun a => X a t) (hXc : ∀ a, Continuous (X a)) (t : ℝ) :
    Measurable fun a => reconMark (X a) t := by
  have h := Dynkin.measurable_intervalIntegral_of_continuous
    (Y := fun r a => Real.exp (Strip.extPath (X a) r - r))
    (fun _ => Real.measurable_exp.comp ((hXm _).sub measurable_const))
    (fun a => continuous_markIntegrand (hXc a)) 0 t
  exact measurable_const.sub (measurable_const.mul h)

theorem measurable_reconVal (hXm : ∀ t, Measurable fun a => X a t) (hXc : ∀ a, Continuous (X a)) (t : ℝ) :
    Measurable fun a => reconVal (X a) t :=
  (measurable_reconMark hXm hXc t).add (Real.measurable_exp.comp ((hXm _).sub measurable_const))

theorem measurable_uncurry_reconVal (hXm : ∀ t, Measurable fun a => X a t) (hXc : ∀ a, Continuous (X a)) :
    Measurable fun p : ℝ × α => reconVal (X p.2) p.1 :=
  measurable_uncurry_of_continuous_of_measurable (u := fun t a => reconVal (X a) t)
    (fun a => continuous_reconVal (hXc a)) (measurable_reconVal hXm hXc)

theorem measurable_reconEnd (hXm : ∀ t, Measurable fun a => X a t) (hXc : ∀ a, Continuous (X a)) :
    Measurable fun a => reconEnd (X a) := by
  have h : (fun a => reconEnd (X a)) = fun a => ⨆ n : ℕ, ENNReal.ofReal (reconClock (X a) n) :=
    funext fun a => reconEnd_eq_iSup_nat (hXc a)
  rw [h]
  exact Measurable.iSup fun n => ENNReal.measurable_ofReal.comp (measurable_reconClock hXm hXc n)

/-! ### The reconstructed driver stopped at strip time `n` -/

/-- The chordal time `s`, clamped to `[0, C(n)]`. -/
def truncArg (X : α → ℝ≥0 → ℝ) (n : ℕ) (s : ℝ) (a : α) : ℝ := min (max s 0) (reconClock (X a) n)

/-- The strip time of the clamped chordal time. -/
def truncTime (X : α → ℝ≥0 → ℝ) (n : ℕ) (s : ℝ) (a : α) : ℝ := reconTime (X a) (truncArg X n s a)

/-- **The reconstructed driver stopped at the chordal time `C(n)`**, minus its initial value. -/
def truncDrv (X : α → ℝ≥0 → ℝ) (n : ℕ) (s : ℝ≥0) (a : α) : ℝ :=
  reconVal (X a) (truncTime X n s a) - reconVal (X a) (truncTime X n 0 a)

omit [MeasurableSpace α] in
theorem truncArg_mem (hXc : ∀ a, Continuous (X a)) (n : ℕ) (s : ℝ) (a : α) :
    truncArg X n s a ∈ lifeSet (X a) := by
  have hC0 : 0 ≤ reconClock (X a) n := reconClock_nonneg (hXc a) (Nat.cast_nonneg n)
  refine ⟨le_min (le_max_right _ _) hC0, lt_of_le_of_lt ?_ (ofReal_reconClock_lt (hXc a) (Nat.cast_nonneg n))⟩
  exact ENNReal.ofReal_le_ofReal (min_le_right _ _)

theorem measurable_truncArg (hXm : ∀ t, Measurable fun a => X a t) (hXc : ∀ a, Continuous (X a)) (n : ℕ)
    (s : ℝ) : Measurable (truncArg X n s) :=
  measurable_const.min (measurable_reconClock hXm hXc n)

theorem measurable_truncTime (hXm : ∀ t, Measurable fun a => X a t) (hXc : ∀ a, Continuous (X a)) (n : ℕ)
    (s : ℝ) : Measurable (truncTime X n s) := by
  refine measurable_of_Iic fun τ => ?_
  rcases lt_or_ge τ 0 with hτ | hτ
  · have : truncTime X n s ⁻¹' Iic τ = ∅ := by
      ext a
      simp only [mem_preimage, mem_Iic, mem_empty_iff_false, iff_false, not_le]
      exact lt_of_lt_of_le hτ (reconTime_nonneg _ _)
    rw [this]; exact MeasurableSet.empty
  · have : truncTime X n s ⁻¹' Iic τ = {a | truncArg X n s a ≤ reconClock (X a) τ} := by
      ext a
      simp only [mem_preimage, mem_Iic, truncTime]
      exact reconTime_le_iff (hXc a) (truncArg_mem hXc n s a) hτ
    rw [this]
    exact measurableSet_le (measurable_truncArg hXm hXc n s) (measurable_reconClock hXm hXc τ)

omit [MeasurableSpace α] in
theorem continuous_truncTime (hXc : ∀ a, Continuous (X a)) (n : ℕ) (a : α) :
    Continuous fun s => truncTime X n s a := by
  have harg : Continuous fun s => truncArg X n s a :=
    (continuous_id.max continuous_const).min continuous_const
  exact (continuousOn_reconTime (hXc a)).comp_continuous harg fun s => truncArg_mem hXc n s a

theorem measurable_truncDrv (hXm : ∀ t, Measurable fun a => X a t) (hXc : ∀ a, Continuous (X a)) (n : ℕ)
    (s : ℝ≥0) : Measurable (truncDrv X n s) := by
  have hV := measurable_uncurry_reconVal hXm hXc
  have hc : ∀ s' : ℝ, Measurable fun a => reconVal (X a) (truncTime X n s' a) := fun s' =>
    Measurable.comp (g := fun p : ℝ × α => reconVal (X p.2) p.1) (f := fun a => (truncTime X n s' a, a)) hV
      ((measurable_truncTime hXm hXc n s').prodMk measurable_id)
  unfold truncDrv
  exact (hc s).sub (hc 0)

omit [MeasurableSpace α] in
theorem continuous_truncDrv (hXc : ∀ a, Continuous (X a)) (n : ℕ) (a : α) :
    Continuous fun s : ℝ≥0 => truncDrv X n s a :=
  ((continuous_reconVal (hXc a)).comp ((continuous_truncTime hXc n a).comp NNReal.continuous_coe)).sub
    continuous_const

omit [MeasurableSpace α] in
@[simp] theorem truncDrv_zero (n : ℕ) (a : α) : truncDrv X n 0 a = 0 := by
  simp [truncDrv]

/-! ### The inverse Loewner map at the chordal time `C(n)`, and its limit -/

/-- `f_{C(n)}(p)` for the stopped reconstructed driver. -/
def approxMap (X : α → ℝ≥0 → ℝ) (n : ℕ) (p : ℂ) (a : α) : ℂ :=
  fwdMapInv (drive 1 (truncDrv X n) a) (reconClock (X a) n) p

/-- The limit of `approxMap` along the integer strip times (the inverse map at the end of the strip life). -/
def limMap (X : α → ℝ≥0 → ℝ) (p : ℂ) (a : α) : ℂ := limUnder atTop fun n : ℕ => approxMap X n p a

/-- The boundary value at a real point `v`: the limit of `limMap` along `v + i/(j+1)`. -/
def bdryVal (X : α → ℝ≥0 → ℝ) (v : ℝ) (a : α) : ℂ := limUnder atTop fun j : ℕ => limMap X (apprPt v j) a

omit [MeasurableSpace α] in
theorem continuous_drive_truncDrv (hXc : ∀ a, Continuous (X a)) (n : ℕ) (a : α) :
    Continuous (drive 1 (truncDrv X n) a) :=
  continuous_const.mul ((continuous_truncDrv hXc n a).comp continuous_real_toNNReal)

omit [MeasurableSpace α] in
theorem drive_truncDrv_zero (n : ℕ) (a : α) : drive 1 (truncDrv X n) a 0 = 0 := by
  simp [drive]

theorem measurable_approxMap (hXm : ∀ t, Measurable fun a => X a t) (hXc : ∀ a, Continuous (X a)) (n : ℕ)
    {p : ℂ} (hp : p ∈ H) : Measurable (approxMap X n p) := by
  set u : ℝ≥0 → α → ℂ := fun t a => fwdMapInv (drive 1 (truncDrv X n) a) t p with hu
  have hcont : ∀ a, Continuous fun t => u t a := fun a =>
    Sec7.continuous_fwdMapInv_time (continuous_drive_truncDrv hXc n a) (drive_truncDrv_zero n a) hp
  have hmeas : ∀ t, Measurable (u t) := fun t =>
    RS.measurable_fwdMapInv_drive (measurable_truncDrv hXm hXc n) (continuous_truncDrv hXc n)
      (fun a => truncDrv_zero n a) 1 t.coe_nonneg hp
  have hj : Measurable (Function.uncurry u) := measurable_uncurry_of_continuous_of_measurable hcont hmeas
  have hT : Measurable fun a => (reconClock (X a) n).toNNReal :=
    measurable_real_toNNReal.comp (measurable_reconClock hXm hXc n)
  have h : Measurable fun a => Function.uncurry u ((reconClock (X a) n).toNNReal, a) :=
    Measurable.comp (g := Function.uncurry u) (f := fun a => ((reconClock (X a) n).toNNReal, a)) hj
      (hT.prodMk measurable_id)
  have heq : approxMap X n p = fun a => Function.uncurry u ((reconClock (X a) n).toNNReal, a) := by
    funext a
    simp only [Function.uncurry_apply_pair, hu, approxMap,
      Real.coe_toNNReal _ (reconClock_nonneg (hXc a) (Nat.cast_nonneg n))]
  rw [heq]; exact h

theorem measurable_limMap (hXm : ∀ t, Measurable fun a => X a t) (hXc : ∀ a, Continuous (X a))
    {p : ℂ} (hp : p ∈ H) : Measurable (limMap X p) :=
  StoppedPath.measurable_limUnder_atTop fun n => measurable_approxMap hXm hXc n hp

theorem measurable_bdryVal (hXm : ∀ t, Measurable fun a => X a t) (hXc : ∀ a, Continuous (X a)) (v : ℝ) :
    Measurable (bdryVal X v) :=
  StoppedPath.measurable_limUnder_atTop fun j => measurable_limMap hXm hXc (apprPt_mem_H v j)

/-! ### Identification with the inverse map at the end of the strip life -/

section Ident

variable (hXc : ∀ a, Continuous (X a)) {a : α} (h0 : X a 0 = 0) (hfin : reconEnd (X a) < ⊤) {W : ℝ → ℝ}
  (hW : Continuous W) (hW0 : W 0 = 0) (hWeq : ∀ s ∈ Ico (0 : ℝ) (reconEnd (X a)).toReal, W s = reconDrv (X a) s)

omit [MeasurableSpace α] in
include hXc h0 hfin hW hW0 hWeq in
theorem approxMap_eq (n : ℕ) {p : ℂ} (hp : p ∈ H) :
    approxMap X n p a = fwdMapInv W (reconClock (X a) n) p := by
  have hCn : 0 ≤ reconClock (X a) n := reconClock_nonneg (hXc a) (Nat.cast_nonneg n)
  have hCσ := reconClock_lt_toReal (hXc a) hfin (Nat.cast_nonneg (α := ℝ) n)
  refine Sec7.fwdMapInv_eqOn_of_eqOn (continuous_drive_truncDrv hXc n a) (drive_truncDrv_zero n a) hW hW0 hCn
    (fun r hr => ?_) hp
  have hr0 : 0 ≤ r := hr.1
  have harg : truncArg X n (r.toNNReal : ℝ) a = r := by
    simp only [truncArg, Real.coe_toNNReal _ hr0, max_eq_left hr0, min_eq_left hr.2]
  have harg0 : truncArg X n 0 a = 0 := by
    simp only [truncArg, max_self, min_eq_left hCn]
  show Real.sqrt 1 * truncDrv X n r.toNNReal a = W r
  simp only [Real.sqrt_one, one_mul, truncDrv, truncTime, harg, harg0]
  rw [← reconDrv_eq_reconVal, ← reconDrv_eq_reconVal, reconDrv_zero (hXc a) h0, sub_zero,
    hWeq r ⟨hr0, lt_of_le_of_lt hr.2 hCσ⟩]

omit [MeasurableSpace α] in
include hXc h0 hfin hW hW0 hWeq in
theorem tendsto_approxMap {p : ℂ} (hp : p ∈ H) :
    Tendsto (fun n => approxMap X n p a) atTop (𝓝 (fwdMapInv W (reconEnd (X a)).toReal p)) := by
  have hc := Sec7.continuous_fwdMapInv_time hW hW0 hp
  have hT : Tendsto (fun n : ℕ => (reconClock (X a) n).toNNReal) atTop
      (𝓝 ((reconEnd (X a)).toReal.toNNReal)) :=
    (continuous_real_toNNReal.tendsto _).comp (tendsto_reconClock_nat (hXc a) hfin)
  have h := (hc.tendsto _).comp hT
  rw [Real.coe_toNNReal _ ENNReal.toReal_nonneg] at h
  refine h.congr fun n => ?_
  simp only [Function.comp_apply, Real.coe_toNNReal _ (reconClock_nonneg (hXc a) (Nat.cast_nonneg n))]
  exact (approxMap_eq hXc h0 hfin hW hW0 hWeq n hp).symm

omit [MeasurableSpace α] in
include hXc h0 hfin hW hW0 hWeq in
theorem limMap_eq {p : ℂ} (hp : p ∈ H) : limMap X p a = fwdMapInv W (reconEnd (X a)).toReal p :=
  (tendsto_approxMap hXc h0 hfin hW hW0 hWeq hp).limUnder_eq

omit [MeasurableSpace α] in
include hXc h0 hfin hW hW0 hWeq in
/-- **The boundary values are read off the strip path**: for a continuous extension `F` of `f_σ` to `ℍ̄`,
`bdryVal X v a = F(v)`. -/
theorem bdryVal_eq {F : ℂ → ℂ} (hFeq : EqOn F (fwdMapInv W (reconEnd (X a)).toReal) H)
    (hFc : ContinuousOn F Hbar) (v : ℝ) : bdryVal X v a = F v := by
  have hv : (v : ℂ) ∈ Hbar := show (0 : ℝ) ≤ (v : ℂ).im by simp
  have h1 : Tendsto (fun j => F (apprPt v j)) atTop (𝓝 (F v)) := (hFc _ hv).tendsto.comp (tendsto_apprPt v)
  refine (h1.congr fun j => ?_).limUnder_eq
  rw [limMap_eq hXc h0 hfin hW hW0 hWeq (apprPt_mem_H v j), hFeq (apprPt_mem_H v j)]

end Ident

end Family

end InteractingSLE.ZhanGT4.A35
