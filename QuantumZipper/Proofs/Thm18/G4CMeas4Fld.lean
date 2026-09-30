import QuantumZipper.Proofs.Thm18.G4CMeas4Drv
import QuantumZipper.Proofs.Zipper.F1ReadMeasLoc

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# JOINT-LEN-READER, part D2: the circle coordinates of the unzipped field, jointly in time

* `Psi a t z`: the inverse map `psiR` read on all of `ℂ` (through `selC`, the identity on `ℍ`).
* `measurable_logDeriv_uncurry`: `(t, z, a) ↦ log ‖(psiR a t)'(z)‖` is jointly measurable on
  `ℝ × ℍ × code` (Carathéodory: continuity in `(t, z)` from
  `RegUnif.continuousOn_log_deriv_fwdMapInv_joint`; measurability in the code through difference
  quotients).
* `vcoord γ k t`: the circle coordinates of the unzipped field read from the code;
  `measurable_vcoord`, and `vcoord_lcode`: on good data at `t ≥ 0` they are the circle
  coordinates of `unzippedField γ (F1.readCfg d) t`.

Own elementary argument.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G4Core

/-- The identity on `ℍ`, `i` elsewhere. -/
def selC (z : ℂ) : ℂ := if 0 < z.im then z else Complex.I

theorem selC_im_pos (z : ℂ) : 0 < (selC z).im := by
  unfold selC; split_ifs with h
  · exact h
  · simp

theorem measurable_selC : Measurable selC :=
  Measurable.ite (measurableSet_lt measurable_const Complex.measurable_im) measurable_id
    measurable_const

theorem selC_of_mem {z : ℂ} (hz : z ∈ H) : selC z = z := if_pos hz

/-- The inverse map on all of `ℂ`. -/
def Psi (a : ℕ → ℝ) (t : ℝ) (z : ℂ) : ℂ := psiR a t (selC z)

/-- `selC` into the subtype `ℍ`. -/
def selS (z : ℂ) : {z : ℂ // 0 < z.im} := ⟨selC z, selC_im_pos z⟩

theorem measurable_selS : Measurable selS := measurable_selC.subtype_mk

/-- The parameter map feeding the Carathéodory families. -/
def parMap (p : ((ℕ → ℝ) × ℝ) × ℂ) : (ℝ × {z : ℂ // 0 < z.im}) × (ℕ → ℝ) :=
  ((p.1.2, selS p.2), p.1.1)

theorem measurable_parMap : Measurable parMap :=
  ((measurable_snd.comp measurable_fst).prodMk (measurable_selS.comp measurable_snd)).prodMk
    (measurable_fst.comp measurable_fst)

theorem measurable_Psi : Measurable fun p : ((ℕ → ℝ) × ℝ) × ℂ => Psi p.1.1 p.1.2 p.2 := by
  have e : (fun p : ((ℕ → ℝ) × ℝ) × ℂ => Psi p.1.1 p.1.2 p.2) =
      (fun q : (ℝ × {z : ℂ // 0 < z.im}) × (ℕ → ℝ) => psiR q.2 q.1.1 q.1.2.1) ∘ parMap := rfl
  rw [e]
  exact measurable_psiR_uncurry.comp measurable_parMap

theorem psiR_max (a : ℕ → ℝ) (t : ℝ) : psiR a (max t 0) = psiR a t := by
  funext z; simp only [psiR, max_eq_left (le_max_right t 0)]

/-- The derivative of `psiR` is that of the inverse forward map. -/
theorem deriv_psiR (a : ℕ → ℝ) (t : ℝ) {z : ℂ} (hz : z ∈ H) :
    deriv (psiR a t) z = deriv (fwdMapInv (wg a) (max t 0)) z := by
  refine (Filter.EventuallyEq.deriv_eq ?_).symm
  filter_upwards [isOpen_H.mem_nhds hz] with w hw
  rw [fwdMapInv_eq_psiR a (le_max_right t 0) hw, psiR_max]

theorem hasDerivAt_psiR (a : ℕ → ℝ) (t : ℝ) {z : ℂ} (hz : z ∈ H) :
    HasDerivAt (psiR a t) (deriv (psiR a t) z) z := by
  have hd := (differentiableOn_revMap _ (continuous_vrev_wg a t) (le_max_right t 0) z hz)
  exact (hd.differentiableAt (isOpen_H.mem_nhds hz)).hasDerivAt
where
  continuous_vrev_wg (a : ℕ → ℝ) (t : ℝ) : Continuous (B2.vrev (wg a) (max t 0)) :=
    (RegUnif.continuous_vrev_joint (continuous_wg a)).comp (continuous_const.prodMk continuous_id)

theorem measurable_deriv_psiR {t : ℝ} {z : ℂ} (hz : 0 < z.im) :
    Measurable fun a : ℕ → ℝ => deriv (psiR a t) z := by
  set h : ℕ → ℂ := fun n => z + ((1 : ℂ) / ((n : ℂ) + 1)) with hh
  have hhim : ∀ n, 0 < (h n).im := fun n => by
    have : ((1 : ℂ) / ((n : ℂ) + 1)).im = 0 := by
      rw [show ((n : ℂ) + 1) = ((n + 1 : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_one,
        ← Complex.ofReal_div, Complex.ofReal_im]
    simp only [hh, Complex.add_im, this, add_zero]; exact hz
  have hlim : Tendsto h atTop (𝓝[≠] z) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => ?_⟩
    · have h0 : Tendsto (fun n : ℕ => (1 : ℂ) / ((n : ℂ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      simpa [hh] using (tendsto_const_nhds (x := z)).add h0
    · simp only [hh, mem_compl_iff, mem_singleton_iff, add_eq_left, one_div, inv_eq_zero]
      exact_mod_cast Nat.succ_ne_zero n
  refine measurable_of_tendsto_metrizable (f := fun n a => slope (psiR a t) z (h n))
    (fun n => ?_) (tendsto_pi_nhds.2 fun a => ((hasDerivAt_psiR a t hz).tendsto_slope).comp hlim)
  simp only [slope, vsub_eq_sub]
  exact Measurable.const_smul (g := fun a => psiR a t (h n) - psiR a t z)
    ((measurable_psiR_apply (hhim n)).sub (measurable_psiR_apply hz)) ((h n - z)⁻¹)

theorem measurable_logDeriv_uncurry :
    Measurable fun p : (ℝ × {z : ℂ // 0 < z.im}) × (ℕ → ℝ) =>
      Real.log ‖deriv (psiR p.2 p.1.1) p.1.2.1‖ := by
  refine measurable_uncurry_of_continuous_of_measurable
    (u := fun (i : ℝ × {z : ℂ // 0 < z.im}) (a : ℕ → ℝ) => Real.log ‖deriv (psiR a i.1) i.2.1‖)
    (fun a => ?_) (fun i => (measurable_deriv_psiR i.2.2).norm.log)
  rw [continuous_iff_continuousAt]
  intro i
  set T : ℝ := max i.1 0 + 1 with hT
  have hF := RegUnif.continuousOn_log_deriv_fwdMapInv_joint (continuous_wg a) (wg_zero a) T
  have hG : Continuous fun j : ℝ × {z : ℂ // 0 < z.im} =>
      Real.log ‖deriv (fwdMapInv (wg a) (min (max j.1 0) T)) j.2.1‖ :=
    hF.comp_continuous (f := fun j : ℝ × {z : ℂ // 0 < z.im} => (min (max j.1 0) T, j.2.1))
      (by fun_prop) fun j => ⟨⟨le_min (le_max_right _ _) (by positivity), min_le_right _ _⟩, j.2.2⟩
  refine hG.continuousAt.congr_of_eventuallyEq ?_
  have hopen : IsOpen {j : ℝ × {z : ℂ // 0 < z.im} | max j.1 0 < T} :=
    isOpen_lt (continuous_fst.max continuous_const) continuous_const
  filter_upwards [hopen.mem_nhds (show max i.1 0 < T by rw [hT]; linarith)] with j hj
  have hj : max j.1 0 < T := hj
  show Real.log ‖deriv (psiR a j.1) j.2.1‖ = _
  rw [deriv_psiR a j.1 j.2.2, min_eq_left hj.le]

/-- The log-derivative on all of `ℂ`. -/
def LD (a : ℕ → ℝ) (t : ℝ) (z : ℂ) : ℝ := Real.log ‖deriv (psiR a t) (selC z)‖

theorem measurable_LD : Measurable fun p : ((ℕ → ℝ) × ℝ) × ℂ => LD p.1.1 p.1.2 p.2 := by
  have e : (fun p : ((ℕ → ℝ) × ℝ) × ℂ => LD p.1.1 p.1.2 p.2) =
      (fun q : (ℝ × {z : ℂ // 0 < z.im}) × (ℕ → ℝ) =>
        Real.log ‖deriv (psiR q.2 q.1.1) q.1.2.1‖) ∘ parMap := rfl
  rw [e]
  exact measurable_logDeriv_uncurry.comp measurable_parMap

/-! ## The coordinates -/

/-- The `i`-th folded circle of the coordinate family. -/
abbrev circI (i : ℕ) : Measure ℂ :=
  foldedCircle (CoordsFull.fullIndex i).1 (CoordsFull.fullIndex i).2

/-- **The circle coordinates of the unzipped field read from the code.** -/
def vcoord (γ : ℝ) (k : LCode) (t : ℝ) : ℕ → ℝ := fun i =>
  limUnder atTop (fun m => ∫ z, avgReg (Factorization.reconstruct (WedgeCan4.piC k.1)) m
      (Psi k.2 t z) ∂circI i) +
    Qc γ * ∫ z, LD k.2 t z ∂circI i

theorem measurable_vcoord (γ : ℝ) : Measurable fun q : LCode × ℝ => vcoord γ q.1 q.2 := by
  refine measurable_pi_iff.2 fun i => ?_
  have hA : ∀ m : ℕ, StronglyMeasurable fun q : LCode × ℝ =>
      ∫ z, avgReg (Factorization.reconstruct (WedgeCan4.piC q.1.1)) m (Psi q.1.2 q.2 z) ∂circI i := by
    intro m
    refine StronglyMeasurable.integral_prod_right' (f := fun p : (LCode × ℝ) × ℂ =>
      avgReg (Factorization.reconstruct (WedgeCan4.piC p.1.1.1)) m (Psi p.1.1.2 p.1.2 p.2)) ?_
    refine ((measurable_avgReg m).comp (((Factorization.measurable_reconstruct.comp
      WedgeCan4.measurable_piC).comp (measurable_fst.comp (measurable_fst.comp measurable_fst))).prodMk
      (measurable_Psi.comp (((measurable_snd.comp (measurable_fst.comp measurable_fst)).prodMk
        (measurable_snd.comp measurable_fst)).prodMk measurable_snd)))).stronglyMeasurable
  have hL : StronglyMeasurable fun q : LCode × ℝ => ∫ z, LD q.1.2 q.2 z ∂circI i := by
    refine StronglyMeasurable.integral_prod_right' (f := fun p : (LCode × ℝ) × ℂ =>
      LD p.1.1.2 p.1.2 p.2) ?_
    exact (measurable_LD.comp (((measurable_snd.comp (measurable_fst.comp measurable_fst)).prodMk
      (measurable_snd.comp measurable_fst)).prodMk measurable_snd)).stronglyMeasurable
  exact (StronglyMeasurable.limUnder hA).measurable.add (hL.measurable.const_mul _)

theorem ae_mem_H_circI (i : ℕ) : ∀ᵐ z ∂circI i, z ∈ H :=
  ae_iff.2 (ESM.foldedCircle_compl_H_eq_zero _ (UnzipFull.fullIndex_radius_pos i))

theorem fwdMapInv_ae_Psi {d : E6.FullData} (hp : F1.PathGoodAll d.2) {t : ℝ} (ht : 0 ≤ t)
    (i : ℕ) : fwdMapInv (F1.readDrv d.2) t =ᵐ[circI i] Psi (lcode d).2 t := by
  filter_upwards [ae_mem_H_circI i] with z hz
  rw [← wg_lcode hp, Psi, selC_of_mem hz, ← fwdMapInv_eq_psiR _ ht hz]

theorem evalReg_eq_code {d : E6.FullData} (hp : F1.PathGoodAll d.2) {t : ℝ} (ht : 0 ≤ t)
    (i : ℕ) (x : FieldSample) :
    evalReg x ((circI i).map (fwdMapInv (F1.readDrv d.2) t)) =
      limUnder atTop (fun m => ∫ z, avgReg x m (Psi (lcode d).2 t z) ∂circI i) := by
  have hΨm : Measurable (Psi (lcode d).2 t) :=
    measurable_Psi.comp (f := fun z : ℂ => (((lcode d).2, t), z))
      (measurable_const.prodMk measurable_id)
  rw [Measure.map_congr (fwdMapInv_ae_Psi hp ht i)]
  unfold evalReg
  congr 1
  funext m
  exact integral_map hΨm.aemeasurable
    ((measurable_avgReg m).comp (f := fun w : ℂ => (x, w))
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable

theorem logInt_eq_code {d : E6.FullData} (hp : F1.PathGoodAll d.2) {t : ℝ} (ht : 0 ≤ t)
    (i : ℕ) : ∫ z, Real.log ‖deriv (fwdMapInv (F1.readDrv d.2) t) z‖ ∂circI i =
      ∫ z, LD (lcode d).2 t z ∂circI i := by
  refine integral_congr_ae ?_
  filter_upwards [ae_mem_H_circI i] with z hz
  rw [LD, selC_of_mem hz, deriv_psiR _ t hz, max_eq_left ht, wg_lcode hp]

/-- **On good data at `t ≥ 0`, the code coordinates are those of the unzipped field.** -/
theorem vcoord_lcode (γ : ℝ) {d : E6.FullData} (hp : F1.PathGoodAll d.2) {t : ℝ} (ht : 0 ≤ t) :
    vcoord γ (lcode d) t = CoordsFull.coordsFull (unzippedField γ (F1.readCfg d) t) := by
  funext i
  have e : CoordsFull.coordsFull (unzippedField γ (F1.readCfg d) t) i =
      evalReg (Factorization.reconstruct (WedgeCan4.piC d.1.1))
          ((circI i).map (fwdMapInv (F1.readDrv d.2) t)) +
        Qc γ * ∫ z, Real.log ‖deriv (fwdMapInv (F1.readDrv d.2) t) z‖ ∂circI i := by
    simp only [CoordsFull.coordsFull, unzippedField, coordChange, F1.readCfg]
  rw [e, evalReg_eq_code hp ht, logInt_eq_code hp ht]
  rfl

end G4Core
end Thm18Asm
end QuantumZipper
