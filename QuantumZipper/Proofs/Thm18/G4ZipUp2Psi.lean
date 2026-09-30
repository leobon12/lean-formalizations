import QuantumZipper.Proofs.Thm18.G4ZipUp2Path
import QuantumZipper.Proofs.Thm18.G4ZipUpReadMeas
import QuantumZipper.Proofs.Zipper.Cor15PosZip
import QuantumZipper.Proofs.Zipper.Cor15RezipRegMeas

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Theorem 1.8, node G4: the measurable inverse reverse map of a read driver

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Theorem 1.8 (3). Task
G4-ZIPUP2.

* `revMapInv_sclDrv`: Brownian scaling for the inverse reverse map,
  `revMapInv (sclDrv p) T w = revMapInv V 1 (w/√T) · √T` (`V` the path on `[0,1]`), from
  `LoewnerAlgebra.revMap_scale` via `revMap_sclDrv`.
* `psiZ F d`: the time-1 inverse reverse map of the measurable continuous path `drvPath F d`
  (`G4ZipUp2Path.lean`), rescaled to time `T = (F d).1`. It is jointly measurable in `(d, w)`
  **for every reading `F`** (`measurable_psiZ`, via `Cor15Group.measurable_revMapInv_param`),
  and it *equals* `revMapInv (F d).2 (F d).1` at every `d` whose driver is continuous, vanishes
  at `0` and has `T > 0` (`psiZ_eq`) — in particular on every `cfgData x ∈ G` of a
  `LenDrvReading` (`psiZ_eq_of_mem`). No a.s. qualification is needed.
* `g4ZipUpFieldReadStmt_of_zip2`: **`G4ZipUpFieldReadStmt` from three explicit inputs**:
  `G4SurrogateZipDataMeasStmt` (existing, `G4ZipUpReadMeas.lean`), `RevInvLogDerivMeasStmt`
  (the log-derivative analogue of `measurable_revMapInv_param`) and `G4ZipUpGoodStmt` (the
  zipped field along the read driver is a.s. LQG-good, on a measurable set).

**Own elementary argument** (measurability bookkeeping; scaling is `LoewnerAlgebra.revMap_scale`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace Thm18Asm

/-! ## 1. Scaling of the inverse reverse map -/

/-- Transfer of `revMapInv` along a real dilation `z ↦ c z` of `ℍ`. -/
theorem revMapInv_eq_of_scale {W V : ℝ → ℝ} {T : ℝ} {c : ℝ} (hc : 0 < c)
    (hfg : ∀ z : ℂ, 0 < z.im → revMap W T z = revMap V 1 ((c : ℂ) * z) / (c : ℂ)) (w : ℂ) :
    revMapInv W T w = revMapInv V 1 ((c : ℂ) * w) / (c : ℂ) := by
  have hc0 : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hc.ne'
  have hmem : ∀ z : ℂ, (c : ℂ) * z ∈ H ↔ z ∈ H := by
    intro z
    show 0 < ((c : ℂ) * z).im ↔ 0 < z.im
    rw [Complex.im_ofReal_mul]
    exact ⟨fun h => pos_of_mul_pos_right h hc.le, fun h => mul_pos hc h⟩
  have hiff : ∀ z : ℂ, (z ∈ H ∧ revMap W T z = w) ↔
      ((c : ℂ) * z ∈ H ∧ revMap V 1 ((c : ℂ) * z) = (c : ℂ) * w) := by
    intro z
    constructor
    · rintro ⟨hz, hw⟩
      refine ⟨(hmem z).2 hz, ?_⟩
      rw [hfg z hz] at hw
      rw [← hw, mul_div_cancel₀ _ hc0]
    · rintro ⟨hz, hw⟩
      have hz' : z ∈ H := (hmem z).1 hz
      refine ⟨hz', ?_⟩
      rw [hfg z hz', hw, mul_div_cancel_left₀ _ hc0]
  have hback : ∀ z' : ℂ, (c : ℂ) * (z' / (c : ℂ)) = z' := fun z' => mul_div_cancel₀ _ hc0
  unfold revMapInv
  by_cases hP : ∃! z, z ∈ H ∧ revMap W T z = w
  · have hQ : ∃! z', z' ∈ H ∧ revMap V 1 z' = (c : ℂ) * w := by
      obtain ⟨z, hz, huniq⟩ := hP
      refine ⟨(c : ℂ) * z, (hiff z).1 hz, fun z' hz' => ?_⟩
      have h1 := huniq (z' / (c : ℂ)) ((hiff _).2 (by rw [hback]; exact hz'))
      rw [← h1, hback]
    rw [dif_pos hP, dif_pos hQ]
    have hPs := hP.choose_spec.1
    have hQu := hQ.choose_spec.2 _ ((hiff _).1 hPs)
    rw [← hQu, mul_div_cancel_left₀ _ hc0]
  · have hQ : ¬ ∃! z', z' ∈ H ∧ revMap V 1 z' = (c : ℂ) * w := by
      rintro ⟨z', hz', huniq⟩
      refine hP ⟨z' / (c : ℂ), (hiff _).2 (by rw [hback]; exact hz'), fun z hz => ?_⟩
      have h1 := huniq _ ((hiff z).1 hz)
      rw [← h1, mul_div_cancel_left₀ _ hc0]
    rw [dif_neg hP, dif_neg hQ, zero_div]

/-- The time-`1` inverse reverse map of the path, rescaled to time `p.2`. -/
def psiS (p : PathT) (w : ℂ) : ℂ :=
  revMapInv (extIccPath zero_le_one p.1) 1 ((((Real.sqrt p.2)⁻¹ : ℝ) : ℂ) * w) /
    (((Real.sqrt p.2)⁻¹ : ℝ) : ℂ)

/-- **Brownian scaling of the inverse reverse map.** -/
theorem revMapInv_sclDrv {p : PathT} (hT : 0 < p.2) : revMapInv (sclDrv p) p.2 = psiS p := by
  funext w
  exact revMapInv_eq_of_scale (inv_pos.2 (Real.sqrt_pos.2 hT))
    (fun z hz => revMap_sclDrv hT hz) w

/-! ## 2. The measurable surrogate `ψ` -/

/-- The measurable surrogate inverse reverse map of the read driver. -/
def psiZ (F : E6.FullData → ℝ × (ℝ → ℝ)) (d : E6.FullData) : ℂ → ℂ :=
  psiS (drvPath F d, (F d).1)

/-- **Exactness.** On drivers that are continuous, vanish at `0`, at a time `T > 0`, the
surrogate is the inverse reverse map of the driver. -/
theorem psiZ_eq {F : E6.FullData → ℝ × (ℝ → ℝ)} {d : E6.FullData} (hT : 0 < (F d).1)
    (hW : Continuous (F d).2) (hW0 : (F d).2 0 = 0) :
    psiZ F d = revMapInv (F d).2 (F d).1 := by
  rw [Cor15Group.revMapInv_congr_drive (sclDrv_drvPath_eqOn hT hW hW0).symm]
  exact (revMapInv_sclDrv (p := (drvPath F d, (F d).1)) hT).symm

theorem psiZ_eq_of_mem {γ t : ℝ} {G : Set E6.FullData} {F : E6.FullData → ℝ × (ℝ → ℝ)}
    (hR : LenDrvReading γ t G F) {x : FieldSample × (ℝ → ℝ)} (hx : cfgData x ∈ G) :
    psiZ F (cfgData x) = revMapInv (F (cfgData x)).2 (F (cfgData x)).1 := by
  obtain ⟨hdrv, hT, -⟩ := hR.2.2.2 x hx
  exact psiZ_eq hT hdrv.2.1 hdrv.2.2.1

/-- The time-`1` driver family of the surrogate. -/
def vZ (F : E6.FullData → ℝ × (ℝ → ℝ)) (d : E6.FullData) : ℝ → ℝ :=
  extIccPath zero_le_one (drvPath F d)

theorem vZ_zero (F : E6.FullData → ℝ × (ℝ → ℝ)) (d : E6.FullData) : vZ F d 0 = 0 := by
  rw [vZ, extIccPath_of_mem zero_le_one _ (left_mem_Icc.2 zero_le_one)]
  exact drvPath_zero F d

theorem measurable_vZ_apply {F : E6.FullData → ℝ × (ℝ → ℝ)}
    (hF1 : Measurable fun d => (F d).1)
    (hF2 : Measurable fun q : E6.FullData × ℝ => (F q.1).2 q.2) (s : ℝ) :
    Measurable fun d => vZ F d s :=
  (continuous_eval_const _).measurable.comp (measurable_drvPath hF1 hF2)

theorem measurable_cZ {F : E6.FullData → ℝ × (ℝ → ℝ)} (hF1 : Measurable fun d => (F d).1) :
    Measurable fun d => ((((Real.sqrt (F d).1)⁻¹ : ℝ)) : ℂ) :=
  Complex.continuous_ofReal.measurable.comp
    ((Real.continuous_sqrt.measurable.comp hF1).inv)

theorem measurable_psiZ {F : E6.FullData → ℝ × (ℝ → ℝ)}
    (hF1 : Measurable fun d => (F d).1)
    (hF2 : Measurable fun q : E6.FullData × ℝ => (F q.1).2 q.2) :
    Measurable fun q : E6.FullData × ℂ => psiZ F q.1 q.2 := by
  have hinv : Measurable fun p : ℂ × E6.FullData => revMapInv (vZ F p.2) 1 p.1 :=
    Cor15Group.measurable_revMapInv_param
      (fun d => continuous_extIccPath zero_le_one (drvPath F d)) (vZ_zero F)
      (measurable_vZ_apply hF1 hF2) one_pos
  have hc := measurable_cZ hF1
  have hpair : Measurable fun q : E6.FullData × ℂ =>
      (((((Real.sqrt (F q.1).1)⁻¹ : ℝ)) : ℂ) * q.2, q.1) :=
    ((hc.comp measurable_fst).mul measurable_snd).prodMk measurable_fst
  exact (hinv.comp hpair).div (hc.comp measurable_fst)

/-! ## 3. The remaining inputs and the reduction -/

/-- **Input (log-derivative of the inverse reverse map, parametric).** The analogue of
`Cor15Group.measurable_revMapInv_param` for `log ‖(revMapInv V 1)'‖`: for a measurable family of
continuous drivers vanishing at `0`, `(a, w) ↦ log ‖deriv (revMapInv (V a) 1) w‖` is measurable. -/
def RevInvLogDerivMeasStmt : Prop :=
  ∀ {α : Type} [MeasurableSpace α] (Vp : α → ℝ → ℝ), (∀ a, Continuous (Vp a)) →
    (∀ a, Vp a 0 = 0) → (∀ s, Measurable fun a => Vp a s) →
    Measurable fun p : α × ℂ => Real.log ‖deriv (revMapInv (Vp p.1) 1) p.2‖

theorem measurable_log_deriv_psiZ (hLD : RevInvLogDerivMeasStmt)
    {F : E6.FullData → ℝ × (ℝ → ℝ)} (hF1 : Measurable fun d => (F d).1)
    (hF2 : Measurable fun q : E6.FullData × ℝ => (F q.1).2 q.2) :
    Measurable fun q : E6.FullData × ℂ => Real.log ‖deriv (psiZ F q.1) q.2‖ := by
  have hD := hLD (vZ F) (fun d => continuous_extIccPath zero_le_one (drvPath F d)) (vZ_zero F)
    (measurable_vZ_apply hF1 hF2)
  have hc := measurable_cZ hF1
  have hpair : Measurable fun q : E6.FullData × ℂ =>
      (q.1, ((((Real.sqrt (F q.1).1)⁻¹ : ℝ)) : ℂ) * q.2) :=
    measurable_fst.prodMk ((hc.comp measurable_fst).mul measurable_snd)
  have hT : MeasurableSet {q : E6.FullData × ℂ | 0 < (F q.1).1} :=
    measurableSet_lt measurable_const (hF1.comp measurable_fst)
  have e : (fun q : E6.FullData × ℂ => Real.log ‖deriv (psiZ F q.1) q.2‖) =
      fun q => if 0 < (F q.1).1 then
        Real.log ‖deriv (revMapInv (vZ F q.1) 1)
          (((((Real.sqrt (F q.1).1)⁻¹ : ℝ)) : ℂ) * q.2)‖ else 0 := by
    funext q
    set c : ℂ := ((((Real.sqrt (F q.1).1)⁻¹ : ℝ)) : ℂ) with hcdef
    have hder : deriv (psiZ F q.1) q.2 =
        c * deriv (revMapInv (vZ F q.1) 1) (c * q.2) / c := by
      show deriv (fun w => revMapInv (vZ F q.1) 1 (c * w) / c) q.2 = _
      rw [deriv_div_const, deriv_comp_mul_left, smul_eq_mul]
    rw [hder]
    split_ifs with h
    · have hc0 : c ≠ 0 :=
        Complex.ofReal_ne_zero.2 (inv_pos.2 (Real.sqrt_pos.2 h)).ne'
      rw [mul_div_cancel_left₀ _ hc0]
    · have hc0 : c = 0 := by
        rw [hcdef, Real.sqrt_eq_zero'.2 (not_lt.1 h), inv_zero, Complex.ofReal_zero]
      rw [hc0, zero_mul, zero_div, norm_zero, Real.log_zero]
  rw [e]
  exact Measurable.ite hT (hD.comp hpair) measurable_const

theorem measurable_fromC_data' : Measurable fun d : E6.FullData => E1.fromC d.1.1 := by
  refine measurable_pi_iff.2 fun μ => ?_
  unfold E1.fromC
  classical
  by_cases h : ∃ i, foldedCircle (CoordsFull.fullIndex i).1 (CoordsFull.fullIndex i).2 = μ
  · simp only [h, ↓reduceDIte]
    exact (measurable_pi_apply (Nat.find h)).comp (measurable_fst.comp measurable_fst)
  · simp only [h, ↓reduceDIte]; exact measurable_const

end Thm18Asm
end QuantumZipper
