import QuantumZipper.Proofs.Zipper.RegContRandom
import QuantumZipper.Proofs.Zipper.JointModDet

/-!
# MEAS-UNZIP (1): the unzipped field is jointly measurable in (driver path, field, time)

Shared library for the measurability nodes of the unzipping functionals
(`E6.LocRichComapStmt`, `B5.LocLengthsMeasStmt`, `F1.ReadLenAEMeasStmt`, Cor 1.5 `hZc`/`hZy`).

For a continuous path `f` on `[0,T]` with `Wof κ T hT f 0 = 0` (driver `W = √κ f`), a time
`s ∈ [0,T]` and a point `u ∈ ℍ`, the inverse forward map `ψ_s(u) = fwdMapInv W s u` and
`log ‖ψ_s'(u)‖` are

* measurable in `f` for fixed `(s, u)` (time reversal: `ψ_s = revMap (Wof κ s (revPath f)) s` on
  `ℍ`, `UnzipInvariance.fwdMapInv_eq_revMap_timeRev`, `RegCont.Wof_revPath_eqOn`, and the
  jointly measurable reverse flow `CharFun.Fm`, `CharFun.Dm`);
* jointly continuous in `(s, u)` on `[0,T] × ℍ` (`RegUnif.continuousOn_fwdMapInv_joint`,
  `RegUnif.continuousOn_log_deriv_fwdMapInv_joint`).

A Carathéodory function is jointly measurable (mathlib,
`measurable_uncurry_of_continuous_of_measurable`, here in a form restricted to measurable sets,
`measurable_uncurry_of_continuousOn`). Hence `flowJ`, `logJ` (the two maps, junk `0` off the good
set) are jointly measurable in `(f, s, u)`, and the raw value of the unzipped field at every
s-finite measure `μ` carried by `ℍ`,
`coordChange x (fwdMapInv W s) (Qc γ) μ = evalReg x (μ.map ψ_s) + Q ∫ log ‖ψ_s'‖ dμ`,
equals `unzRawJ` (`unzRawJ_eq`), which is jointly measurable in `((f, x), s)`
(`measurable_unzRawJ`).

Own elementary bookkeeping (Carathéodory's joint measurability is standard, e.g. Aliprantis–Border,
*Infinite Dimensional Analysis*, 3rd ed., Lemma 4.51; mathlib's version is used).
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology

namespace QuantumZipper.MeasUnzip

open CharFun RegCont UnzipInvariance TopologicalSpace
open scoped Classical

/-! ## Carathéodory functions on measurable sets -/

/-- **Carathéodory on measurable sets**: if `u a` is continuous on the measurable set `K` of a
second-countable metrizable space for `a ∈ S`, and `a ↦ u a i` is measurable on `S` for `i ∈ K`,
then `(a, i) ↦ u a i` is jointly measurable on `S × K` (junk `b` elsewhere). -/
theorem measurable_uncurry_of_continuousOn {α ι β : Type*} [MeasurableSpace α]
    [TopologicalSpace ι] [MetrizableSpace ι] [SecondCountableTopology ι] [MeasurableSpace ι]
    [OpensMeasurableSpace ι] [TopologicalSpace β] [PseudoMetrizableSpace β] [MeasurableSpace β]
    [BorelSpace β] {b : β} {S : Set α} (hS : MeasurableSet S) {K : Set ι} (hK : MeasurableSet K)
    {u : α → ι → β} (hc : ∀ a ∈ S, ContinuousOn (u a) K)
    (hm : ∀ i ∈ K, Measurable fun a => if a ∈ S then u a i else b) :
    Measurable fun p : α × ι => if p.1 ∈ S ∧ p.2 ∈ K then u p.1 p.2 else b := by
  classical
  set v : K → α → β := fun i a => if a ∈ S then u a i else b with hv
  have hvc : ∀ a, Continuous fun i : K => v i a := by
    intro a
    by_cases ha : a ∈ S
    · simp only [hv, ha, ite_true]
      exact (hc a ha).domRestrict
    · simp only [hv, ha, ite_false]
      exact continuous_const
  have hvm : ∀ i : K, Measurable (v i) := fun i => hm i i.2
  have hU : Measurable (Function.uncurry v) := measurable_uncurry_of_continuous_of_measurable hvc hvm
  have hK' : MeasurableSet {p : α × ι | p.2 ∈ K} := measurable_snd hK
  have hsub : Measurable fun p : {p : α × ι | p.2 ∈ K} => ((⟨p.1.2, p.2⟩ : K), p.1.1) :=
    ((measurable_snd.comp measurable_subtype_coe).subtype_mk).prodMk
      (measurable_fst.comp measurable_subtype_coe)
  have key : Measurable fun p : α × ι =>
      if h : p ∈ {p : α × ι | p.2 ∈ K} then Function.uncurry v ((⟨p.2, h⟩ : K), p.1) else b :=
    Measurable.dite (hU.comp hsub) measurable_const hK'
  convert key using 1
  funext p
  by_cases h2 : p.2 ∈ K
  · have h2' : p ∈ {p : α × ι | p.2 ∈ K} := h2
    rw [dif_pos h2']
    by_cases h1 : p.1 ∈ S
    · simp [hv, h1, h2]
    · simp [hv, h1]
  · have h2' : p ∉ {p : α × ι | p.2 ∈ K} := h2
    rw [dif_neg h2']
    simp [h2]

/-! ## The flow and its log-derivative, jointly in `(f, s, u)` -/

variable {T : ℝ} (hT : 0 ≤ T)

/-- Paths whose driver starts at `0`. -/
def PZ (κ : ℝ) : Set C(Icc (0 : ℝ) T, ℝ) := {f | Wof κ T hT f 0 = 0}

theorem measurableSet_PZ (κ : ℝ) : MeasurableSet (PZ hT κ) := by
  have h : Measurable fun f : C(Icc (0 : ℝ) T, ℝ) => Wof κ T hT f 0 :=
    measurable_const.mul (continuous_eval_const _).measurable
  exact measurableSet_eq_fun h measurable_const

/-- The time-space window `[0,T] × ℍ`. -/
def KT (T : ℝ) : Set (ℝ × ℂ) := Icc 0 T ×ˢ H

theorem measurableSet_KT (T : ℝ) : MeasurableSet (KT T) :=
  measurableSet_Icc.prod isOpen_H.measurableSet

theorem revMap_revPath_eq (κ : ℝ) (f : C(Icc (0 : ℝ) T, ℝ)) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) T) :
    revMap (vRev (Wof κ T hT f) s) s = revMap (Wof κ s hs.1 (revPath hT s hs.1 f)) s :=
  funext fun z => (ReverseFlow.revMap_congr_drive z (Wof_revPath_eqOn hT κ hs f)).symm

theorem fwdMapInv_Wof_eq (κ : ℝ) {f : C(Icc (0 : ℝ) T, ℝ)} (hf : f ∈ PZ hT κ) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) T) {u : ℂ} (hu : u ∈ H) :
    fwdMapInv (Wof κ T hT f) s u = Fm κ s hs.1 (revPath hT s hs.1 f, u) := by
  rw [fwdMapInv_eq_revMap_timeRev _ (continuous_Wof κ T hT f) hf hs.1 hu]
  exact congrFun (revMap_revPath_eq hT κ f hs) u

theorem log_deriv_fwdMapInv_Wof_eq (κ : ℝ) {f : C(Icc (0 : ℝ) T, ℝ)} (hf : f ∈ PZ hT κ) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) T) {u : ℂ} (hu : u ∈ H) :
    Real.log ‖deriv (fwdMapInv (Wof κ T hT f) s) u‖ =
      Real.log ‖Dm κ s hs.1 (revPath hT s hs.1 f, u)‖ := by
  rw [deriv_fwdMapInv_eq (continuous_Wof κ T hT f) hf hs.1 hu, revMap_revPath_eq hT κ f hs,
    Dm_eq κ s hs.1 _ hu]

/-- The inverse forward map `ψ_s(u)` of the driver `Wof κ T hT f`, junk `0` off
`PZ × [0,T] × ℍ`. -/
def flowJ (κ : ℝ) (p : C(Icc (0 : ℝ) T, ℝ) × (ℝ × ℂ)) : ℂ :=
  if p.1 ∈ PZ hT κ ∧ p.2 ∈ KT T then fwdMapInv (Wof κ T hT p.1) p.2.1 p.2.2 else 0

/-- `log ‖ψ_s'(u)‖`, junk `0` off `PZ × [0,T] × ℍ`. -/
def logJ (κ : ℝ) (p : C(Icc (0 : ℝ) T, ℝ) × (ℝ × ℂ)) : ℝ :=
  if p.1 ∈ PZ hT κ ∧ p.2 ∈ KT T then Real.log ‖deriv (fwdMapInv (Wof κ T hT p.1) p.2.1) p.2.2‖
  else 0

theorem measurable_flowJ (κ : ℝ) : Measurable (flowJ hT κ) := by
  classical
  refine measurable_uncurry_of_continuousOn (u := fun f (i : ℝ × ℂ) => fwdMapInv (Wof κ T hT f) i.1 i.2)
    (measurableSet_PZ hT κ) (measurableSet_KT T)
    (fun f hf => RegUnif.continuousOn_fwdMapInv_joint (continuous_Wof κ T hT f) hf T) ?_
  rintro ⟨s, u⟩ ⟨hs, hu⟩
  have heq : (fun f => if f ∈ PZ hT κ then fwdMapInv (Wof κ T hT f) s u else 0) =
      fun f => if f ∈ PZ hT κ then Fm κ s hs.1 (revPath hT s hs.1 f, u) else 0 := by
    funext f
    split_ifs with hf
    · exact fwdMapInv_Wof_eq hT κ hf hs hu
    · rfl
  simp only
  rw [heq]
  exact Measurable.ite (measurableSet_PZ hT κ)
    ((measurable_Fm κ s hs.1).comp ((measurable_revPath hT s hs.1).prodMk measurable_const))
    measurable_const

theorem measurable_logJ (κ : ℝ) : Measurable (logJ hT κ) := by
  classical
  refine measurable_uncurry_of_continuousOn
    (u := fun f (i : ℝ × ℂ) => Real.log ‖deriv (fwdMapInv (Wof κ T hT f) i.1) i.2‖)
    (measurableSet_PZ hT κ) (measurableSet_KT T)
    (fun f hf => RegUnif.continuousOn_log_deriv_fwdMapInv_joint (continuous_Wof κ T hT f) hf T) ?_
  rintro ⟨s, u⟩ ⟨hs, hu⟩
  have heq : (fun f => if f ∈ PZ hT κ then Real.log ‖deriv (fwdMapInv (Wof κ T hT f) s) u‖
      else 0) =
      fun f => if f ∈ PZ hT κ then Real.log ‖Dm κ s hs.1 (revPath hT s hs.1 f, u)‖ else 0 := by
    funext f
    split_ifs with hf
    · exact log_deriv_fwdMapInv_Wof_eq hT κ hf hs hu
    · rfl
  simp only
  rw [heq]
  exact Measurable.ite (measurableSet_PZ hT κ)
    (Real.measurable_log.comp (((measurable_Dm κ s hs.1).comp
      ((measurable_revPath hT s hs.1).prodMk measurable_const)).norm))
    measurable_const

/-! ## The raw values of the unzipped field -/

/-- The raw value of the unzipped field of `(x, Wof κ T hT f)` at time `s` and measure `μ`,
written with the jointly measurable `flowJ`, `logJ`. -/
def unzRawJ (γ κ : ℝ) (μ : Measure ℂ) (q : (C(Icc (0 : ℝ) T, ℝ) × FieldSample) × ℝ) : ℝ :=
  limUnder atTop (fun k => ∫ u, avgReg q.1.2 k (flowJ hT κ (q.1.1, (q.2, u))) ∂μ) +
    Qc γ * ∫ u, logJ hT κ (q.1.1, (q.2, u)) ∂μ

theorem measurable_unzRawJ (γ κ : ℝ) (μ : Measure ℂ) [SFinite μ] :
    Measurable (unzRawJ hT γ κ μ) := by
  unfold unzRawJ
  have hflow : Measurable fun r : ((C(Icc (0 : ℝ) T, ℝ) × FieldSample) × ℝ) × ℂ =>
      flowJ hT κ (r.1.1.1, (r.1.2, r.2)) :=
    (measurable_flowJ hT κ).comp ((measurable_fst.comp (measurable_fst.comp measurable_fst)).prodMk
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  have h1 : ∀ k : ℕ, StronglyMeasurable fun q : (C(Icc (0 : ℝ) T, ℝ) × FieldSample) × ℝ =>
      ∫ u, avgReg q.1.2 k (flowJ hT κ (q.1.1, (q.2, u))) ∂μ := by
    intro k
    have hm : Measurable fun r : ((C(Icc (0 : ℝ) T, ℝ) × FieldSample) × ℝ) × ℂ =>
        avgReg r.1.1.2 k (flowJ hT κ (r.1.1.1, (r.1.2, r.2))) :=
      (measurable_avgReg k).comp ((measurable_snd.comp (measurable_fst.comp measurable_fst)).prodMk
        hflow)
    exact hm.stronglyMeasurable.integral_prod_right'
  have hlog : Measurable fun r : ((C(Icc (0 : ℝ) T, ℝ) × FieldSample) × ℝ) × ℂ =>
      logJ hT κ (r.1.1.1, (r.1.2, r.2)) :=
    (measurable_logJ hT κ).comp ((measurable_fst.comp (measurable_fst.comp measurable_fst)).prodMk
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  exact (StronglyMeasurable.limUnder h1).measurable.add
    (hlog.stronglyMeasurable.integral_prod_right'.measurable.const_mul _)

/-- **The raw values of the unzipped field are `unzRawJ`**: for a path in `PZ`, a time
`s ∈ [0,T]` and a measure `μ` carried by `ℍ`. -/
theorem unzRawJ_eq (γ κ : ℝ) {f : C(Icc (0 : ℝ) T, ℝ)} (hf : f ∈ PZ hT κ) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) T) (x : FieldSample) {μ : Measure ℂ} (hμ : μ Hᶜ = 0) :
    unzippedField γ (x, Wof κ T hT f) s μ = unzRawJ hT γ κ μ ((f, x), s) := by
  have hae : ∀ᵐ u ∂μ, u ∈ H := ae_iff.2 hμ
  have hfl : fwdMapInv (Wof κ T hT f) s =ᵐ[μ] fun u => flowJ hT κ (f, (s, u)) := by
    filter_upwards [hae] with u hu
    simp only [flowJ, if_pos (And.intro hf (show (s, u) ∈ KT T from ⟨hs, hu⟩))]
  have hmf : Measurable fun u => flowJ hT κ (f, (s, u)) :=
    (measurable_flowJ hT κ).comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  have hmap : μ.map (fwdMapInv (Wof κ T hT f) s) = μ.map fun u => flowJ hT κ (f, (s, u)) :=
    Measure.map_congr hfl
  have hint : ∀ k, ∫ w, avgReg x k w ∂(μ.map (fwdMapInv (Wof κ T hT f) s)) =
      ∫ u, avgReg x k (flowJ hT κ (f, (s, u))) ∂μ := by
    intro k
    rw [hmap, integral_map hmf.aemeasurable
      (show Measurable fun w => avgReg x k w from
        (measurable_avgReg k).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable]
  have hlog : ∫ u, Real.log ‖deriv (fwdMapInv (Wof κ T hT f) s) u‖ ∂μ =
      ∫ u, logJ hT κ (f, (s, u)) ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hae] with u hu
    simp only [logJ, if_pos (And.intro hf (show (s, u) ∈ KT T from ⟨hs, hu⟩))]
  simp only [unzippedField, coordChange, evalReg, unzRawJ, hint, hlog]

end QuantumZipper.MeasUnzip
