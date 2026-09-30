import QuantumZipper.Proofs.Zipper.LocLenStep3Defs
import QuantumZipper.Proofs.Zipper.F2S3Param
import QuantumZipper.Proofs.Zipper.F2S3Weld
import QuantumZipper.Proofs.Zipper.BaseFinReduce

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# D75, task R7a: welding invariance with open arcs (`Step3WeldArcStmt`)

`step3WeldArc_of_parts : Step3GammaArcsStmt → Step3InvDensityArcStmt → BaseFin.BaseFiniteStmt →
Step3WeldArcStmt`, the open-arc copy of `F2.step3Weld_of_arcs_x` (F2S3Param.lean:279, via
`F2.step3Weld_of_param`, F2S3Weld.lean:123). Sheffield arXiv:1012.4797 §5.4 pp. 70–72: the
boundary measure of the unzipped field is transported by the unzipping maps, and the two sides of
`η[0,s]` are the preimages of the initial segments of the two arcs at the horizon `t`, so if the
two `x`-lengths agree at all times `s ≤ t`, the capture-time images of `ν_{x_t}` on the two arcs
agree, and `∫ g∘F_t dν_{x_t}` agrees on both sides ("the density is the same on both sides").

Changes from the old proof (own bookkeeping): the stage measures are the local limits on
`(offSet W t)ᶜ` (no mass at `O^±_t`, `0`, so `Icc`/`Ioo` masses agree), the deterministic core
`F2.param_of_stages` is reused verbatim, and the finiteness of the capture-time images (automatic
for the old locally finite global measure) comes from base finiteness X1 (`BaseFiniteStmt`,
B-P arXiv:2404.16642 p. 285 "L(1) < ∞") at an integer horizon `q ≥ t`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace LocLen

/-- `LswArcs` only reads the lengths on `[0, s]`. -/
theorem lswArcs_congr_len {ν : Measure ℝ} {O : ℝ × ℝ} {s : ℝ} {L L' : ℝ → ℝ≥0∞ × ℝ≥0∞}
    {Ψ η : ℝ → ℂ} (h : ∀ r ∈ Icc 0 s, L r = L' r) (hA : F1.LswArcs ν O s L Ψ η) :
    F1.LswArcs ν O s L' Ψ η := by
  obtain ⟨hΨ, a, b, ha, hb, hma, hmb, ha0, has, hb0, hbs, hsub, hpt⟩ := hA
  exact ⟨hΨ, a, b, ha, hb, hma, hmb, ha0, has, hb0, hbs,
    fun r hr => by rw [← h r hr]; exact hsub r hr, hpt⟩

/-- **Deterministic core** (copy of `F2.lintegral_sides_eq_of_param` with finiteness of the left
arc in place of local finiteness of `ν`). -/
theorem lintegral_sides_eq_of_param_fin {ν : Measure ℝ} {a b t : ℝ}
    {η : ℝ → ℂ} {φm φp : ℝ → ℝ} {F : ℝ → ℂ} (hη : Measurable η) (hm : Measurable φm)
    (hp : Measurable φp) (ht : 0 ≤ t) (hfin : ν (Icc a 0) ≠ ⊤)
    (hFm : ∀ w ∈ Icc a 0, φm w ∈ Icc 0 t ∧ F w = η (φm w))
    (hFp : ∀ w ∈ Icc 0 b, φp w ∈ Icc 0 t ∧ F w = η (φp w))
    (hlen : ∀ s ∈ Icc (0 : ℝ) t,
      ν (Icc a 0 ∩ φm ⁻¹' Iic s) = ν (Icc 0 b ∩ φp ⁻¹' Iic s))
    {g : ℂ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ w in Icc a 0, g (F w) ∂ν = ∫⁻ w in Icc 0 b, g (F w) ∂ν := by
  have hm' : ∀ w ∈ Icc a 0, φm w ∈ Icc 0 t := fun w hw => (hFm w hw).1
  have hp' : ∀ w ∈ Icc 0 b, φp w ∈ Icc 0 t := fun w hw => (hFp w hw).1
  have : IsFiniteMeasure (ν.restrict (Icc a 0)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hfin.lt_top⟩
  have heq : (ν.restrict (Icc a 0)).map φm = (ν.restrict (Icc 0 b)).map φp := by
    refine Measure.ext_of_Iic _ _ fun s => ?_
    rw [Measure.map_apply hm measurableSet_Iic, Measure.map_apply hp measurableSet_Iic,
      Measure.restrict_apply (hm measurableSet_Iic), Measure.restrict_apply (hp measurableSet_Iic),
      inter_comm, inter_comm (φp ⁻¹' _)]
    rcases lt_or_ge s 0 with hs | hs
    · rw [F2.inter_preimage_Iic_neg hm' hs, F2.inter_preimage_Iic_neg hp' hs]
    · rw [F2.inter_preimage_Iic_min hm' s, F2.inter_preimage_Iic_min hp' s]
      exact hlen _ ⟨le_min hs ht, min_le_right _ _⟩
  calc ∫⁻ w in Icc a 0, g (F w) ∂ν = ∫⁻ w in Icc a 0, (g ∘ η) (φm w) ∂ν :=
        setLIntegral_congr_fun measurableSet_Icc fun w hw => by simp [(hFm w hw).2]
    _ = ∫⁻ y, (g ∘ η) y ∂((ν.restrict (Icc a 0)).map φm) := (lintegral_map (hg.comp hη) hm).symm
    _ = ∫⁻ y, (g ∘ η) y ∂((ν.restrict (Icc 0 b)).map φp) := by rw [heq]
    _ = ∫⁻ w in Icc 0 b, (g ∘ η) (φp w) ∂ν := lintegral_map (hg.comp hη) hp
    _ = ∫⁻ w in Icc 0 b, g (F w) ∂ν :=
        (setLIntegral_congr_fun measurableSet_Icc fun w hw => by simp [(hFp w hw).2]).symm

/-- Facts about the local measures at one time `s ≥ 0`, from `Step3InvDensityArcStmt`. -/
theorem step3_local_facts {γ : ℝ} {x y : FieldSample} {W : ℝ → ℝ} {s : ℝ} {ρ : ℝ → ℝ≥0∞}
    (h : (sideImages W s).1 ≤ 0 ∧ 0 ≤ (sideImages W s).2 ∧ IsRegularSample x ∧
      IsRegularSample y ∧ ∃ νx νy : Measure ℝ, HasBdryLimitOn γ x (offSet W s)ᶜ νx ∧
        HasBdryLimitOn γ y (offSet W s)ᶜ νy ∧ νx = νy.withDensity ρ) :
    (sideImages W s).1 ≤ 0 ∧ 0 ≤ (sideImages W s).2 ∧
      qBoundaryMeasureOn γ x (offSet W s)ᶜ (offSet W s) = 0 ∧
      qBoundaryMeasureOn γ y (offSet W s)ᶜ (offSet W s) = 0 ∧
      qBoundaryMeasureOn γ x (offSet W s)ᶜ =
        (qBoundaryMeasureOn γ y (offSet W s)ᶜ).withDensity ρ ∧
      ∀ a b : ℝ, Ioo a b ⊆ (offSet W s)ᶜ →
        arcLen γ x a b = qBoundaryMeasureOn γ x (offSet W s)ᶜ (Ioo a b) := by
  obtain ⟨h1, h2, hrx, hry, νx, νy, hx, hy, hd⟩ := h
  have hU : IsOpen (offSet W s)ᶜ := (isClosed_offSet W s).isOpen_compl
  rw [qBoundaryMeasureOn_eq_of_hasBdryLimitOn hrx hU hx,
    qBoundaryMeasureOn_eq_of_hasBdryLimitOn hry hU hy]
  refine ⟨h1, h2, by simpa using hx.1, by simpa using hy.1, hd, fun a b hab => ?_⟩
  exact arcLen_eq_of_hasBdryLimitOn hrx hx hab

theorem step3_Ioo_subset_left {W : ℝ → ℝ} {s : ℝ} (h2 : 0 ≤ (sideImages W s).2) :
    Ioo (sideImages W s).1 0 ⊆ (offSet W s)ᶜ := by
  rintro w ⟨hw1, hw2⟩ hw
  rcases hw with hw | hw | hw
  · exact hw1.ne' hw
  · exact hw2.ne hw
  · rw [hw] at hw2; exact (hw2.trans_le h2).false

theorem step3_Ioo_subset_right {W : ℝ → ℝ} {s : ℝ} (h1 : (sideImages W s).1 ≤ 0) :
    Ioo 0 (sideImages W s).2 ⊆ (offSet W s)ᶜ := by
  rintro w ⟨hw1, hw2⟩ hw
  rcases hw with hw | hw | hw
  · rw [hw] at hw1; exact (h1.trans_lt hw1).false
  · exact hw1.ne' hw
  · exact hw2.ne hw

theorem step3_null_left {ν : Measure ℝ} {W : ℝ → ℝ} {s : ℝ} (h : ν (offSet W s) = 0) :
    ν {(sideImages W s).1} = 0 ∧ ν {(0 : ℝ)} = 0 ∧ ν {(sideImages W s).2} = 0 :=
  ⟨measure_mono_null (by simp [offSet]) h, measure_mono_null (by simp [offSet]) h,
    measure_mono_null (by simp [offSet]) h⟩

/-- **Welding invariance with open arcs.** -/
theorem step3WeldArc_of_parts (hA : Step3GammaArcsStmt) (hI : Step3InvDensityArcStmt)
    (hX1 : BaseFin.BaseFiniteStmt) : Step3WeldArcStmt := by
  intro κ hκ hκ4 Ω _ P _ B X hB hX hind
  have hX1' := ae_all_iff.2 fun n : ℕ =>
    hX1 κ hκ hκ4 P B X hB hX hind ((n : ℝ) + 1) (by positivity)
  filter_upwards [hA κ hκ hκ4 P B X hB hX hind, hI κ hκ hκ4 P B X hB hX hind, hX1',
    WedgeUnzip.globalCaraStmt_holds κ hκ hκ4 P B hB] with ω hAω hIω hFω hCω
  intro t₀ M hL t ht htt₀ htM g hg
  obtain ⟨hLfin, η, hη, hArc⟩ := hAω
  have hfacts := fun s (hs : 0 ≤ s) => step3_local_facts (hIω s hs)
  have hLxs : ∀ s, 0 ≤ s →
      unzipLengthsArc (Real.sqrt κ) (X ω + F2.logSingField κ, drive κ B ω) s =
        (qBoundaryMeasureOn (Real.sqrt κ) (F2.unzX κ (X ω) (drive κ B ω) s)
            (offSet (drive κ B ω) s)ᶜ (Icc (sideImages (drive κ B ω) s).1 0),
          qBoundaryMeasureOn (Real.sqrt κ) (F2.unzX κ (X ω) (drive κ B ω) s)
            (offSet (drive κ B ω) s)ᶜ (Icc 0 (sideImages (drive κ B ω) s).2)) := by
    intro s hs
    obtain ⟨h1, h2, hx0, -, -, harc⟩ := hfacts s hs
    obtain ⟨na, n0, nb⟩ := step3_null_left hx0
    simp only [unzipLengthsArc]
    rw [show unzippedField (Real.sqrt κ) (X ω + F2.logSingField κ, drive κ B ω) s =
        F2.unzX κ (X ω) (drive κ B ω) s from rfl,
      harc _ _ (step3_Ioo_subset_left h2), harc _ _ (step3_Ioo_subset_right h1),
      measure_congr (Ioo_ae_eq_Icc' na n0), measure_congr (Ioo_ae_eq_Icc' n0 nb)]
  -- the capture-time parametrization at every horizon
  have hpar := fun (h : ℝ) (hh : 0 ≤ h) => F2.param_of_stages
    (νΓ := fun s => qBoundaryMeasureOn (Real.sqrt κ) (F2.unzY κ (X ω) (drive κ B ω) s)
      (offSet (drive κ B ω) s)ᶜ)
    (νx := fun s => qBoundaryMeasureOn (Real.sqrt κ) (F2.unzX κ (X ω) (drive κ B ω) s)
      (offSet (drive κ B ω) s)ᶜ)
    (O := fun s => sideImages (drive κ B ω) s) (Ψ := fun s w => F2.invBdry (drive κ B ω) s w)
    (L := fun r => unzipLengthsArc (Real.sqrt κ) (B2.cfg κ B X ω) (max r 0))
    (Lx := fun r => unzipLengthsArc (Real.sqrt κ) (X ω + F2.logSingField κ, drive κ B ω) r)
    (g := fun z => ENNReal.ofReal (Real.exp (Real.sqrt κ / 2 * F1.lswPhi κ (fun _ => 0) z)))
    hη (F1.measurable_lswDens (G := fun _ => 0) continuous_const hη)
    (fun r => hLfin (max r 0) (le_max_right _ _))
    (fun s hs => by
      have h := (hCω s hs).comp_continuous Complex.continuous_ofReal
        (fun x => show (0 : ℝ) ≤ ((x : ℝ) : ℂ).im by simp)
      simpa [Function.comp_def] using h)
    (fun s hs => lswArcs_congr_len (fun r hr =>
      (congrArg (unzipLengthsArc (Real.sqrt κ) (B2.cfg κ B X ω)) (max_eq_left hr.1)).symm)
      (by simpa only [F2.extInv_ofReal] using hArc s hs))
    (fun s hs => by
      obtain ⟨-, -, -, hy0, hd, -⟩ := hfacts s hs
      rw [Measure.restrict_eq_self_of_ae_mem (measure_mono_null (fun w hw => by
        simp only [mem_setOf_eq, mem_compl_iff, not_not, mem_insert_iff,
          mem_singleton_iff] at hw
        rcases hw with hw | hw <;> simp [offSet, hw]) hy0), hd]
      rfl)
    hLxs hh
  obtain ⟨η', φm, φp, hη', hm, hp, hFm, hFp, hlen⟩ := hpar t ht
  obtain ⟨-, -, hx0, -, -, -⟩ := hfacts t ht
  obtain ⟨na, n0, nb⟩ := step3_null_left hx0
  -- finiteness of the left arc at the horizon `t`, from X1 at an integer horizon `q ≥ t`
  have hfin : qBoundaryMeasureOn (Real.sqrt κ) (F2.unzX κ (X ω) (drive κ B ω) t)
      (offSet (drive κ B ω) t)ᶜ (Icc (sideImages (drive κ B ω) t).1 0) ≠ ⊤ := by
    obtain ⟨n, hn⟩ := exists_nat_ge t
    have hq : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
    have htq : t ∈ Icc (0 : ℝ) ((n : ℝ) + 1) := ⟨ht, by linarith⟩
    obtain ⟨ηq, φmq, φpq, -, -, -, -, -, hlenq⟩ := hpar ((n : ℝ) + 1) hq
    have e1 := congrArg Prod.fst (hLxs t ht)
    have e2 := congrArg Prod.fst (hLxs _ hq)
    dsimp only at e1 e2
    rw [← e1, (hlenq t htq).1]
    refine ne_top_of_le_ne_top ?_ (measure_mono inter_subset_left)
    rw [← e2]
    exact (hFω n).1.ne
  rw [setLIntegral_congr (Ioo_ae_eq_Icc' na n0), setLIntegral_congr (Ioo_ae_eq_Icc' n0 nb)]
  exact lintegral_sides_eq_of_param_fin hη' hm hp ht hfin hFm hFp (fun s hs => by
    rw [← (hlen s hs).1, ← (hlen s hs).2]
    exact hL s hs.1 (hs.2.trans htt₀) fun r hr => htM r ⟨hr.1, hr.2.trans hs.2⟩) hg

end LocLen
end QuantumZipper
