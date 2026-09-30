import QuantumZipper.Proofs.Zipper.LocLenStmtsPos
import QuantumZipper.Proofs.Zipper.LocLenXGood
import QuantumZipper.Proofs.Zipper.LocLenB5UArc
import QuantumZipper.Proofs.Zipper.T13MiscTransferY
import QuantumZipper.Proofs.Zipper.F2Step3DensSign
import QuantumZipper.Proofs.Zipper.F1StrictMonoAllT
import QuantumZipper.Proofs.Zipper.Thm13HeadlineV9

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# D75 / R8a (1): open-arc positivity of the unzipped `Γ⁰` and `x` fields at all times

Open-arc copy of `T13Misc.ae_pos_unzY_all` (T13MiscTransferY.lean) and
`Thm18Asm.ae_pos_unzX_all` (T13MiscTransfer.lean), without the global window identities UW and
without the global rule (5.1) statement `F2.Step3LocalDensityStmt`.

* `PosOff γ x S lo`: `x` has a local boundary limit `ν` off the closed set `S` which charges
  every nonempty open subinterval of `[lo, 0]`. Transfer rules (deterministic): coordinates
  (`PosOff.congr_coords`), restriction (`PosOff.mono`), rule (5.1) (`PosOff.add_ofFun`: the
  density `e^{γφ/2}` is positive), rescaling (`PosOff.rescale`), and reading
  (`PosOff.qBoundaryMeasureOn_pos`).
* `ae_posOff_unzY`: a.s. for all `t > 0`, the `Γ⁰` field `y_t` is `PosOff` off the tip with
  `lo = O⁻_t`. Proof of the old lemma: in the fixed chart `T = ⌊t⌋ + 1 > t` the boundary measure
  of `h⁰_T` charges every interval (`B5.ae_nu0_regular`, from the proved
  `RevCouplingReg.revCouplingBoundaryMeasureRegular`); a subarc `(a,b)` of `[O⁻_t,0]` contains
  the image of a rational window of chart `T` (`T13Misc.exists_rat_window`), whose chart-`T`
  mass is the open-arc length at time `t` (`ae_windows_local_of_anchor`, proved from AW), i.e.
  the local limit of `y_t` off the tip (`YGoodOffAllStmt`).
* `ae_posOff_unzX`: the same for `x_t` off `offSet`: `x_t` and `y_t + ψ_t` share coordinates,
  `ψ_t` is continuous off the root images, and rule (5.1) (`HasBdryLimitOn.add_ofFun`, as in
  `xGoodOffAll_of_yGoodOff`) multiplies the limit by the positive density `e^{γψ_t/2}`.

Paper: Sheffield arXiv:1012.4797 p. 56 and §5.4 rule (5.1); Berestycki–Powell
arXiv:2404.16642 Def 8.12 p. 281. Bookkeeping own (as in the old proofs).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace LocLen

/-- `x` has a local boundary limit off `S` charging every nonempty open subinterval of
`[lo, 0]`. -/
def PosOff (γ : ℝ) (x : FieldSample) (S : Set ℝ) (lo : ℝ) : Prop :=
  ∃ ν : Measure ℝ, HasBdryLimitOn γ x Sᶜ ν ∧
    ∀ u v : ℝ, lo ≤ u → u < v → v ≤ 0 → 0 < ν (Ioo u v)

variable {γ : ℝ} {x : FieldSample} {S : Set ℝ} {lo : ℝ}

theorem PosOff.congr_coords {y : FieldSample}
    (h : Factorization.coords x = Factorization.coords y) (hy : PosOff γ y S lo) :
    PosOff γ x S lo := by
  obtain ⟨ν, hν, hpos⟩ := hy
  have havg : avgReg x = avgReg y := by
    rw [← Factorization.avgReg_reconstruct_coords x, h, Factorization.avgReg_reconstruct_coords]
  exact ⟨ν, (hasBdryLimitOn_congr_avg havg).2 hν, hpos⟩

theorem PosOff.mono {S' : Set ℝ} (hx : PosOff γ x S lo) (hS' : IsClosed S') (hSS' : S ⊆ S')
    (hdis : ∀ u v : ℝ, lo ≤ u → u < v → v ≤ 0 → Ioo u v ⊆ S'ᶜ) : PosOff γ x S' lo := by
  obtain ⟨ν, hν, hpos⟩ := hx
  refine ⟨_, hν.mono hS'.isOpen_compl (compl_subset_compl.2 hSS'), fun u v hu huv hv => ?_⟩
  rw [Measure.restrict_apply measurableSet_Ioo, inter_eq_left.2 (hdis u v hu huv hv)]
  exact hpos u v hu huv hv

/-- **Rule (5.1) preserves positivity**: the density `e^{γφ/2}` is positive. -/
theorem PosOff.add_ofFun (hx : IsRegularSample x) (hS : IsClosed S) (h : PosOff γ x S lo)
    {φ : ℂ → ℝ} {W : Set ℂ} (hW : IsOpen W) (hUW : ∀ t ∈ Sᶜ, (t : ℂ) ∈ W)
    (hφ : ContinuousOn φ (W ∩ Hbar))
    (hdis : ∀ u v : ℝ, lo ≤ u → u < v → v ≤ 0 → Ioo u v ⊆ Sᶜ) :
    PosOff γ (x + ofFun φ) S lo := by
  obtain ⟨ν, hν, hpos⟩ := h
  refine ⟨_, hν.add_ofFun hx hS.isOpen_compl hW hUW hφ, fun u v hu huv hv => ?_⟩
  have hsub := hdis u v hu huv hv
  have hcont : ContinuousOn (fun t : ℝ => ENNReal.ofReal (Real.exp (γ / 2 * φ t))) (Ioo u v) :=
    ENNReal.continuous_ofReal.comp_continuousOn ((continuousOn_const.mul
      (hφ.comp Complex.continuous_ofReal.continuousOn
        fun t ht => ⟨hUW t (hsub ht), show (0 : ℝ) ≤ ((t : ℂ)).im by simp⟩)).rexp)
  have hae := hcont.aemeasurable (μ := ν) measurableSet_Ioo
  refine lt_of_lt_of_le ?_ (withDensity_apply_le _ _)
  rw [pos_iff_ne_zero, Ne, lintegral_eq_zero_iff' hae]
  intro h0
  have hF : ∀ᵐ t ∂ν.restrict (Ioo u v), False :=
    h0.mono fun t ht => by
      simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero] at ht
      exact absurd ht (not_le.2 (Real.exp_pos _))
  rw [ae_iff] at hF
  simp only [not_false_eq_true, ofPred_true, Measure.restrict_apply_univ] at hF
  exact (hpos u v hu huv hv).ne' hF

theorem PosOff.rescale (hx : IsRegularSample x) (hγ : 0 < γ) (h : PosOff γ x S lo) {a : ℝ}
    (ha : 0 < a) :
    PosOff γ (rescale x (Qc γ) a) ((fun u => a * u) ⁻¹' S) (lo / a) := by
  obtain ⟨ν, hν, hpos⟩ := h
  refine ⟨_, by rw [← preimage_compl]; exact hν.rescale hx hγ ha, fun u v hu huv hv => ?_⟩
  have hpre : (fun x : ℝ => x / a) ⁻¹' Ioo u v = Ioo (u * a) (v * a) := by
    ext x
    simp only [mem_preimage, mem_Ioo, lt_div_iff₀ ha, div_lt_iff₀ ha]
  rw [Measure.map_apply (f := fun x : ℝ => x / a) (by fun_prop) measurableSet_Ioo, hpre]
  exact hpos (u * a) (v * a) ((div_le_iff₀ ha).1 hu) (mul_lt_mul_of_pos_right huv ha)
    (by nlinarith)

theorem PosOff.qBoundaryMeasureOn_pos (hx : IsRegularSample x) (hS : IsClosed S)
    (h : PosOff γ x S lo) :
    ∀ u v : ℝ, lo ≤ u → u < v → v ≤ 0 → 0 < qBoundaryMeasureOn γ x Sᶜ (Ioo u v) := by
  obtain ⟨ν, hν, hpos⟩ := h
  intro u v hu huv hv
  rw [qBoundaryMeasureOn_eq_of_hasBdryLimitOn hx hS.isOpen_compl hν]
  exact hpos u v hu huv hv

open B2 B5

/-- **`Γ⁰` open-arc positivity at all times** (copy of `T13Misc.ae_pos_unzY_all`, UW replaced
by the local window identities, the global measure at time `t` by the local limit off the tip). -/
theorem ae_posOff_unzY (hYG : YGoodOffAllStmt) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {Ω : Type}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    {X : Ω → FieldSample}
    (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) (hI : IndepFun (pathOf B) X P) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → PosOff (Real.sqrt κ) (F2.unzY κ (X ω) (drive κ B ω) t) {0}
      (sideImages (drive κ B ω) t).1 := by
  have hposN : ∀ᵐ ω ∂P, ∀ n : ℕ, 0 < n → ∀ u v : ℝ, u < v →
      0 < qBoundaryMeasure (Real.sqrt κ) (h0f κ n B X ω) (Ioo u v) := by
    rw [ae_all_iff]
    intro n
    by_cases hn : 0 < n
    · have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
      filter_upwards [ae_nu0_regular RevCouplingReg.revCouplingBoundaryMeasureRegular hκ hκ4
        hn0 hB hX hI] with ω hω _ u v huv
      exact hω.2.1 u v huv
    · exact Eventually.of_forall fun ω h => absurd h hn
  have hAW := RegUnif.anchorWindowAllStmt_of_extAll hκ hκ4 hB hX hI
    (E5.extAllInput_holds κ P B X hκ hκ4 hB hX hI)
  have hUWN : ∀ᵐ ω ∂P, ∀ n : ℕ, 0 < n → ∀ s ∈ Ioc (0 : ℝ) n, ∀ u v : ℚ,
      zeroMinus (Vr κ n B ω) n < u → (u : ℝ) < v → (v : ℝ) < zeroMinus (Vr κ n B ω) (n - s) →
      qBoundaryMeasure (Real.sqrt κ) (h0f κ n B X ω) (Ioo u v) =
        arcLen (Real.sqrt κ) (h0f κ s B X ω)
          (realRevMap (Vr κ n B ω) (n - s) u) (realRevMap (Vr κ n B ω) (n - s) v) := by
    rw [ae_all_iff]
    intro n
    by_cases hn : 0 < n
    · have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
      filter_upwards [ae_windows_local_of_anchor hκ hκ4 hn0 hB hX hI (hAW n hn0)] with ω hω _
        using hω
    · exact Eventually.of_forall fun ω h => absurd h hn
  filter_upwards [hposN, hUWN, hYG κ hκ hκ4 P B X hB hX hI,
    RegUnif.ae_forall_isSimpleCurveHull_revHull_Vr RS.rohdeSchrammSimple hκ hκ4.le P B hB,
    RS.ae_real_alive hB hκ hκ4.le, hB.cont, hB.eval_zero_ae_eq_zero]
    with ω hpos huw hyg hK halive hc h0 t ht
  obtain ⟨hreg, ⟨ν, hν⟩, -⟩ := hyg t ht.le
  refine ⟨ν, hν, fun a b ha hab hb => ?_⟩
  have hWc : Continuous (drive κ B ω) := Thm14FromThm13.continuous_drive hc
  have hW0 : drive κ B ω 0 = 0 := by simp [drive, h0]
  set n : ℕ := ⌊t⌋₊ + 1 with hndef
  have hn : 0 < n := Nat.succ_pos _
  have hlt : t < n := by rw [hndef]; push_cast; exact Nat.lt_floor_add_one t
  have hKs : IsSimpleCurveHull (revHull (vrev (drive κ B ω) t) t) := hK t ht
  have hKn : IsSimpleCurveHull (revHull (vrev (drive κ B ω) n) n) :=
    hK n (by exact_mod_cast hn)
  have hside : (sideImages (drive κ B ω) t).1 = zeroMinus (vrev (drive κ B ω) t) t :=
    sideImages_fst_eq_zeroMinus_vrev hWc hW0 ht hKs fun x hx => halive x hx t ht.le
  rw [hside] at ha
  obtain ⟨u, v, hu, huv, hv, hsub⟩ := T13Misc.exists_rat_window hWc ht hlt hKn hKs ha hab hb
  have e := huw n hn t ⟨ht, hlt.le⟩ u v hu huv hv
  set p := realRevMap (Vr κ n B ω) (n - t) u
  set q := realRevMap (Vr κ n B ω) (n - t) v
  have hdisj : Disjoint (Ioo p q) ({0} : Set ℝ) := by
    rw [disjoint_singleton_right]
    intro h
    have := (hsub h).2
    linarith
  calc (0 : ℝ≥0∞) < qBoundaryMeasure (Real.sqrt κ) (h0f κ n B X ω) (Ioo u v) :=
        hpos n hn u v huv
    _ = arcLen (Real.sqrt κ) (h0f κ t B X ω) p q := e
    _ = ν (Ioo p q) := by
        unfold arcLen
        rw [F2.h0f_eq_unzY, IsLQGGoodOff.qBoundaryMeasureOn_eq hreg hν isOpen_Ioo hdisj,
          Measure.restrict_apply measurableSet_Ioo, inter_self]
    _ ≤ ν (Ioo a b) := measure_mono hsub

/-- **`x`-level open-arc positivity at all times** (copy of `Thm18Asm.ae_pos_unzX_all`, rule
(5.1) applied locally as in `xGoodOffAll_of_yGoodOff`). -/
theorem ae_posOff_unzX (hYG : YGoodOffAllStmt) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {Ω : Type}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    {X : Ω → FieldSample}
    (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) (hI : IndepFun (pathOf B) X P) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → PosOff (Real.sqrt κ) (F2.unzX κ (X ω) (drive κ B ω) t)
      (offSet (drive κ B ω) t) (sideImages (drive κ B ω) t).1 := by
  filter_upwards [WedgeUnzip.coords_unzX_eq hκ hκ4 hB hX hI, ae_posOff_unzY hYG hκ hκ4 hB hX hI,
    hYG κ hκ hκ4 P B X hB hX hI,
    WedgeUnzip.globalCaraStmt_holds κ hκ hκ4 P B hB,
    WedgeUnzip.extNonvanishStmt_holds κ hκ hκ4 P B hB,
    F2.step3SideSign_holds κ hκ hκ4 P B X hB hX hI]
    with ω hco hyP hyω hCω hNVω hsgn t ht
  refine PosOff.congr_coords (hco t ht.le) ?_
  have hψ : ContinuousOn (WedgeUnzip.logTipFun κ (drive κ B ω) t)
      ((((↑) : ℝ → ℂ) '' WedgeUnzip.tipSet (drive κ B ω) t)ᶜ ∩ Hbar) := by
    intro u hu
    have hc : ContinuousWithinAt (F2.extInv (drive κ B ω) t)
        ((((↑) : ℝ → ℂ) '' WedgeUnzip.tipSet (drive κ B ω) t)ᶜ ∩ Hbar) u :=
      (hCω t ht.le u hu.2).mono inter_subset_right
    have hne : F2.extInv (drive κ B ω) t u ≠ 0 := hNVω t ht.le u hu.2 hu.1
    have hlog : ContinuousWithinAt (fun v => Real.log ‖F2.extInv (drive κ B ω) t v‖)
        ((((↑) : ℝ → ℂ) '' WedgeUnzip.tipSet (drive κ B ω) t)ᶜ ∩ Hbar) u :=
      hc.norm.log (norm_ne_zero_iff.2 hne)
    exact (hlog.const_mul (Real.sqrt κ)).neg
  have hWo : IsOpen ((((↑) : ℝ → ℂ) '' WedgeUnzip.tipSet (drive κ B ω) t)ᶜ) :=
    ((WedgeUnzip.isCompact_tipSet _ t).image Complex.continuous_ofReal).isClosed.isOpen_compl
  have hUW : ∀ s ∈ (offSet (drive κ B ω) t)ᶜ,
      (s : ℂ) ∈ (((↑) : ℝ → ℂ) '' WedgeUnzip.tipSet (drive κ B ω) t)ᶜ := by
    rintro s hs ⟨u, hu, hus⟩
    obtain rfl := Complex.ofReal_injective hus
    apply hs
    rcases hu with rfl | rfl <;> simp [offSet]
  have hdis : ∀ u v : ℝ, (sideImages (drive κ B ω) t).1 ≤ u → u < v → v ≤ 0 →
      Ioo u v ⊆ (offSet (drive κ B ω) t)ᶜ := fun u v hu _ hv z hz =>
    disjoint_left.1 (Ioo_left_disjoint_offSet _ t (hsgn t ht.le).2)
      (Ioo_subset_Ioo hu hv hz)
  exact ((hyP t ht).mono (isClosed_offSet _ t) (singleton_subset_iff.2 (by simp [offSet]))
    hdis).add_ofFun (hyω t ht.le).1 (isClosed_offSet _ t) hWo hUW hψ hdis

end LocLen
end QuantumZipper
