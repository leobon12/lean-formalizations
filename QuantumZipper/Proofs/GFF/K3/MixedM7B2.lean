import QuantumZipper.Proofs.GFF.K3.MixedM7B1
import QuantumZipper.Proofs.GFF.K3.MixedM6Cont
import QuantumZipper.Proofs.GFF.K3.HarmonicPart
import QuantumZipper.Proofs.GFF.CoordRegSwap

/-!
# K3-mixed M7-a2′, part 2: harmonicity and Poisson reproduction inside the half-disc

For `w` in the gradient closure of the mixed space with `w ⊥ H_supp(U)`, `U = ball t r ∩ H`,
the function `u z = ⟪v_{fold_{retr z, s₀}}, w⟫` (`retr` = fold into `Hbar` and retract onto
`closedBall t ρ₁`) is continuous, even, and has the mean-value property on `ball t ρ₁`
(`MixedM7B1`), hence is harmonic there (Weyl's lemma, `harmonicOnNhd_of_meanValue`;
Gilbarg–Trudinger Thm 2.7 and the Weyl lemma), and the half-disc Poisson formula
(`integral_halfDiscPoisson_of_harmonic`; Axler–Bourdon–Ramey, *Harmonic Function Theory*,
Thm 1.17) gives

* `inner_rieszVec_bal_eq_m7b`: `⟪v_μ, w⟫ = ⟪v_{bal t ρ μ}, w⟫` for every `ρ ∈ (r', r)` and every
  admissible `μ` carried by `closedBall t r'`.

This is Sheffield's Thm 2.17 (PTRF 139 (2007), p. 14) for the smaller half-discs
`ball t ρ ∩ H`, `ρ < r`; the passage `ρ → r` is in `MixedM7B3`.
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Real Topology ComplexConjugate ENNReal NNReal RealInnerProductSpace

namespace QuantumZipper.K3

theorem continuous_retr_m7b (t : ℝ) {ρ : ℝ} (hρ : 0 < ρ) : Continuous (retr t ρ) := by
  refine (LipschitzWith.of_dist_le_mul (K := 2) fun z w => ?_).continuous
  rw [dist_eq_norm, dist_eq_norm]
  exact_mod_cast norm_retr_sub_retr_le hρ z w

theorem retr_foldH_m7b (t ρ : ℝ) (z : ℂ) : retr t ρ (foldH z) = retr t ρ z := by
  unfold retr
  rw [CircleFubini.foldH_of_mem' (CircleFubini.foldH_mem_Hbar' z)]

theorem retr_conj_m7b (t ρ : ℝ) (z : ℂ) : retr t ρ (conj z) = retr t ρ z := by
  unfold retr
  rw [foldH_conj_k3]

section Harm

variable {D : Set ℂ} {c d t r ρ₁ s₀ : ℝ} {w : GradSpace D}

/-- The pairing function `z ↦ ⟪v_{fold_{z,s₀}}, w⟫`. -/
def pairFn (D : Set ℂ) (c d s₀ : ℝ) (w : GradSpace D) (z : ℂ) : ℝ :=
  ⟪rieszVec D (mixedSpace D (realSet (Icc c d))) (foldedCircle z s₀), w⟫

/-- Its even, globally continuous extension from `closedBall t ρ₁ ∩ Hbar`. -/
def harmFn (D : Set ℂ) (c d t ρ₁ s₀ : ℝ) (w : GradSpace D) (z : ℂ) : ℝ :=
  pairFn D c d s₀ w (retr t ρ₁ z)

theorem harmFn_eq_m7b {z : ℂ} (hz : z ∈ Hbar) (hzt : ‖z - t‖ ≤ ρ₁) :
    harmFn D c d t ρ₁ s₀ w z = pairFn D c d s₀ w z := by
  rw [harmFn, retr_eq_self hz hzt]

theorem continuous_harmFn_m7b (hgeom : Prop16Geometry D c d) (hsub : ball (t : ℂ) r ∩ H ⊆ D)
    (hρ₁ : 0 < ρ₁) (hρ₁r : ρ₁ < r) (hs₀ : 0 < s₀) (hs₀r : s₀ < (r - ρ₁) / 4) :
    Continuous (harmFn D c d t ρ₁ s₀ w) := by
  have h := mixedLocalHyp_halfDisc_m7b hgeom hρ₁r hsub
  have hc := (continuousOn_rieszVec_foldedCircle h hs₀ hs₀r).inner continuousOn_const (𝕜 := ℝ)
    (g := fun _ => w)
  refine hc.comp_continuous (continuous_retr_m7b t hρ₁) fun z => ⟨?_, retr_mem_Hbar hρ₁ z⟩
  exact mem_closedBall_iff_norm.2 (norm_retr_sub_le hρ₁ z)

/-- Mean value over folded circles at points of the closed upper half plane. -/
theorem integral_foldedCircle_harmFn_m7b (hgeom : Prop16Geometry D c d)
    (hsub : ball (t : ℂ) r ∩ H ⊆ D) (hρ₁ : 0 < ρ₁) (hρ₁r : ρ₁ < r) (hs₀ : 0 < s₀)
    (hs₀r : s₀ < (r - ρ₁) / 4)
    (hwG : w ∈ gradClosure D (mixedSpace D (realSet (Icc c d))))
    (hw : w ∈ (localClosure D (mixedSpace D (realSet (Icc c d))) t r)ᗮ)
    {z : ℂ} (hz : z ∈ Hbar) {σ : ℝ} (hσ : 0 < σ) (hzσ : ‖z - t‖ + σ < ρ₁) :
    ∫ x, harmFn D c d t ρ₁ s₀ w x ∂foldedCircle z σ = harmFn D c d t ρ₁ s₀ w z := by
  have hK : foldedCircle z σ (closedBall (t : ℂ) ρ₁ ∩ Hbar)ᶜ = 0 := by
    refine measure_mono_null (compl_subset_compl.2 fun x hx => ⟨?_, hx.2⟩)
      (foldedCircle_compl_eq_zero hz hσ.le)
    have hx1 := mem_closedBall_iff_norm.1 hx.1
    rw [mem_closedBall_iff_norm]
    calc ‖x - t‖ = ‖(x - z) + (z - t)‖ := by ring_nf
      _ ≤ ‖x - z‖ + ‖z - t‖ := norm_add_le _ _
      _ ≤ ρ₁ := by linarith
  have hrep := inner_rieszVec_eq_integral_halfDisc_m7b hgeom hρ₁r hsub
    (isAdmissibleH_foldedCircle hz hσ) hK hs₀ (by linarith) hwG hw
  have hae : (fun x => harmFn D c d t ρ₁ s₀ w x) =ᵐ[foldedCircle z σ]
      fun x => pairFn D c d s₀ w x := by
    filter_upwards [mem_ae_iff.2 hK] with x hx
    exact harmFn_eq_m7b hx.2 (mem_closedBall_iff_norm.1 hx.1)
  rw [integral_congr_ae hae, harmFn_eq_m7b hz (by linarith), pairFn]
  simp only [pairFn]
  rw [← hrep]
  -- radius independence
  have hzr : ‖z - t‖ + max σ s₀ < r := by
    rcases le_total σ s₀ with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
  rcases lt_trichotomy σ s₀ with h | h | h
  · exact inner_rieszVec_foldedCircle_eq_m7b hgeom hsub hz hσ h
      (by rw [max_eq_right h.le] at hzr; exact hzr) hw
  · rw [h]
  · exact (inner_rieszVec_foldedCircle_eq_m7b hgeom hsub hz hs₀ h
      (by rw [max_eq_left h.le] at hzr; exact hzr) hw).symm

/-- **Weyl step.** `harmFn` is harmonic on `ball t ρ₁`. -/
theorem harmonicOnNhd_harmFn_m7b (hgeom : Prop16Geometry D c d)
    (hsub : ball (t : ℂ) r ∩ H ⊆ D) (hρ₁ : 0 < ρ₁) (hρ₁r : ρ₁ < r) (hs₀ : 0 < s₀)
    (hs₀r : s₀ < (r - ρ₁) / 4)
    (hwG : w ∈ gradClosure D (mixedSpace D (realSet (Icc c d))))
    (hw : w ∈ (localClosure D (mixedSpace D (realSet (Icc c d))) t r)ᗮ) :
    InnerProductSpace.HarmonicOnNhd (harmFn D c d t ρ₁ s₀ w) (ball (t : ℂ) ρ₁) := by
  have hcont := continuous_harmFn_m7b (w := w) hgeom hsub hρ₁ hρ₁r hs₀ hs₀r
  refine harmonicOnNhd_of_meanValue hcont isOpen_ball fun z _ σ hσ hball => ?_
  have hzσ := add_lt_of_closedBall_subset_ball hσ hball
  have hfold : ∫ x, harmFn D c d t ρ₁ s₀ w x ∂circleUnif z σ =
      ∫ x, harmFn D c d t ρ₁ s₀ w x ∂foldedCircle z σ := by
    rw [foldedCircle, integral_map measurable_foldH.aemeasurable
      hcont.aestronglyMeasurable]
    simp only [harmFn, retr_foldH_m7b]
  rw [hfold]
  by_cases hz : z ∈ Hbar
  · exact integral_foldedCircle_harmFn_m7b hgeom hsub hρ₁ hρ₁r hs₀ hs₀r hwG hw hz hσ hzσ
  · have hz' : conj z ∈ Hbar := by
      have : z.im < 0 := lt_of_not_ge hz
      show 0 ≤ (conj z).im
      simp only [Complex.conj_im]; linarith
    rw [← CoordReg.integral_foldedCircle_conj hcont.measurable,
      integral_foldedCircle_harmFn_m7b hgeom hsub hρ₁ hρ₁r hs₀ hs₀r hwG hw hz' hσ
        (by rw [norm_conj_sub_ofReal_k3]; exact hzσ)]
    simp only [harmFn, retr_conj_m7b]

/-- **Poisson reproduction for the smaller half-discs.** For `w ⊥ H_supp(U)` in the gradient
closure, admissible `μ` carried by `closedBall t r'` and `r' < ρ < r`,
`⟪v_μ, w⟫ = ⟪v_{bal t ρ μ}, w⟫`. -/
theorem inner_rieszVec_bal_eq_m7b {D : Set ℂ} {c d t r r' ρ : ℝ}
    (hgeom : Prop16Geometry D c d) (hsub : ball (t : ℂ) r ∩ H ⊆ D) (hr' : 0 < r')
    (hr'ρ : r' < ρ) (hρr : ρ < r) {μ : Measure ℂ} (hμ : IsAdmissibleH μ)
    (hμK : μ (closedBall (t : ℂ) r')ᶜ = 0) {w : GradSpace D}
    (hwG : w ∈ gradClosure D (mixedSpace D (realSet (Icc c d))))
    (hw : w ∈ (localClosure D (mixedSpace D (realSet (Icc c d))) t r)ᗮ) :
    ⟪rieszVec D (mixedSpace D (realSet (Icc c d))) μ, w⟫ =
      ⟪rieszVec D (mixedSpace D (realSet (Icc c d))) (bal t ρ μ), w⟫ := by
  set ρ₁ : ℝ := (ρ + r) / 2 with hρ₁def
  set s₀ : ℝ := (r - ρ₁) / 8 with hs₀def
  have hρ : 0 < ρ := hr'.trans hr'ρ
  have hρρ₁ : ρ < ρ₁ := by rw [hρ₁def]; linarith
  have hρ₁ : 0 < ρ₁ := hρ.trans hρρ₁
  have hρ₁r : ρ₁ < r := by rw [hρ₁def]; linarith
  have hs₀ : 0 < s₀ := by rw [hs₀def]; linarith
  have hs₀r : s₀ < (r - ρ₁) / 4 := by rw [hs₀def]; linarith
  have hμf := hμ.1
  have hHbar : μ Hbarᶜ = 0 := by
    obtain ⟨-, ⟨K, -, hKH, hK⟩, -⟩ := hμ
    exact measure_mono_null (compl_subset_compl.2 hKH) hK
  have hμK1 : μ (closedBall (t : ℂ) ρ₁ ∩ Hbar)ᶜ = 0 := by
    rw [compl_inter]
    exact measure_union_null (measure_mono_null (compl_subset_compl.2
      (closedBall_subset_closedBall (by linarith))) hμK) hHbar
  have hbA := isAdmissibleH_bal hρ hr'ρ hμK
  have hbf := isFiniteMeasure_bal hρ hr'ρ hμK
  have hbK : bal t ρ μ (closedBall (t : ℂ) ρ₁ ∩ Hbar)ᶜ = 0 := by
    refine bal_null_of_forall (isClosed_closedBall.measurableSet.inter
      isClosed_Hbar.measurableSet).compl fun z => ?_
    refine measure_mono_null (compl_subset_compl.2 fun x hx => ⟨?_, hx.2⟩)
      (halfDiscPoisson_compl_eq_zero hρ z)
    exact closedBall_subset_closedBall hρρ₁.le (sphere_subset_closedBall hx.1)
  have e1 := inner_rieszVec_eq_integral_halfDisc_m7b hgeom hρ₁r hsub hμ hμK1 hs₀ (by linarith)
    hwG hw
  have e2 := inner_rieszVec_eq_integral_halfDisc_m7b hgeom hρ₁r hsub hbA hbK hs₀ (by linarith)
    hwG hw
  rw [e1, e2]
  set u := harmFn D c d t ρ₁ s₀ w with hudef
  have hu := continuous_harmFn_m7b (w := w) hgeom hsub hρ₁ hρ₁r hs₀ hs₀r
  have hH := harmonicOnNhd_harmFn_m7b hgeom hsub hρ₁ hρ₁r hs₀ hs₀r hwG hw
  have hKc : IsCompact (closedBall (t : ℂ) ρ₁ ∩ Hbar) :=
    (isCompact_closedBall _ _).inter_right isClosed_Hbar
  have a1 : ∀ ν : Measure ℂ, ν (closedBall (t : ℂ) ρ₁ ∩ Hbar)ᶜ = 0 →
      ∫ z, ⟪rieszVec D (mixedSpace D (realSet (Icc c d))) (foldedCircle z s₀), w⟫ ∂ν =
        ∫ z, u z ∂ν := by
    intro ν hν
    refine integral_congr_ae ?_
    filter_upwards [mem_ae_iff.2 hν] with x hx
    exact (harmFn_eq_m7b hx.2 (mem_closedBall_iff_norm.1 hx.1)).symm
  rw [a1 μ hμK1, a1 _ hbK]
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn hu.continuousOn
  have hbd : ∀ z, ‖u z‖ ≤ C := by
    intro z
    have hmem : retr t ρ₁ z ∈ closedBall (t : ℂ) ρ₁ ∩ Hbar :=
      ⟨mem_closedBall_iff_norm.2 (norm_retr_sub_le hρ₁ z), retr_mem_Hbar hρ₁ z⟩
    have e : u z = u (retr t ρ₁ z) := by
      rw [hudef, harmFn_eq_m7b hmem.2 (mem_closedBall_iff_norm.1 hmem.1)]; rfl
    rw [e]; exact hC _ hmem
  have hint : Integrable u (bal t ρ μ) :=
    (integrable_const C).mono' hu.aestronglyMeasurable (ae_of_all _ hbd)
  rw [(integral_bal hint).2]
  refine integral_congr_ae ?_
  filter_upwards [mem_ae_iff.2 hμK] with z hz
  have hzt : ‖z - t‖ ≤ r' := mem_closedBall_iff_norm.1 hz
  refine (integral_halfDiscPoisson_of_harmonic hρ (mem_ball_of_le_k3 hr'ρ hzt)
    (fun x hx => hH x (closedBall_subset_ball hρρ₁ hx)) fun x _ => ?_).symm
  simp only [hudef, harmFn, retr_conj_m7b]

end Harm

end QuantumZipper.K3
