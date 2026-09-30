import QuantumZipper.Proofs.Zipper.B5LocF1Coord
import QuantumZipper.Proofs.Zipper.B5LocF1Side
import QuantumZipper.Proofs.Zipper.LocLenMeasLoc
import QuantumZipper.Proofs.Zipper.LocLenLocality

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Follow-the-paper campaign (D75), task R6d: B5 locality for F1 with open-arc lengths

Open-arc copy of `B5.f1LocalityStmt_of_inputs` / `B5.locality_core` (B5LocF1Assembly.lean) and
of `F1.F1LocalityStmt` (F1GermFam.lean:168). The deterministic locality core is now **B4**
`LocLen.unzipLengthsArc_eq_of_dyCircAgree` (no global boundary limit), the measurable reader is
`F1.locLengthsMeasArcStmt_holds`, and input (R1) (global limits of the unzipped wedge field at
the times `1/(m+1)`) is replaced by local limits on the two open arcs (`ArcLimits`), which is
what good-off-the-tip gives. Sheffield arXiv:1012.4797 §5.4 pp. 70–72; Berestycki–Powell
arXiv:2404.16642 proof of Lemma 8.27, p. 294 ("this is clear"). Own bookkeeping (as the old
file).
-/

noncomputable section

set_option warn.classDefReducibility false

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace B5

open F1

/-- Local boundary limits of the unzipped field on the two open arcs `(O⁻_t,0)`, `(0,O⁺_t)`. -/
def ArcLimits (γ : ℝ) (c : FieldSample × (ℝ → ℝ)) (t : ℝ) : Prop :=
  (∃ ν, IsVagueLimitOnR (Ioo (sideImages c.2 t).1 0) (bdryApprox γ (unzippedField γ c t)) ν) ∧
    ∃ ν, IsVagueLimitOnR (Ioo 0 (sideImages c.2 t).2) (bdryApprox γ (unzippedField γ c t)) ν

/-- Open-arc copy of `F1.F1LocalityStmt`. -/
def F1LocalityArcStmt (γ α κ : ℝ) : Prop :=
  0 < κ → κ < 4 → γ = Real.sqrt κ → α < Qc γ →
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → FieldSample) (A : ℝ → Ω → ℝ)
    (B : ℝ≥0 → Ω → ℝ), IsProbabilityMeasure P → IsFreeGFFModConstH X P →
    IsWedgeProcess α (Qc γ) A P → IsBrownianReal B P → (∀ t, Measurable (A t)) →
    (∀ t, Measurable (B t)) → iIndep (srcSigma X A B) P →
    ∀ n : ℕ, ∃ (E : ℕ → Set Ω) (h : ℕ → Ω → ℝ≥0∞ × ℝ≥0∞),
      (∀ m, MeasurableSet[⨆ i ∈ (Finset.univ : Finset (Fin 3)), germFam X P A B i n] (E m)) ∧
      (∀ m, Measurable[⨆ i ∈ (Finset.univ : Finset (Fin 3)), germFam X P A B i n] (h m)) ∧
      (∀ᵐ ω ∂P, ∀ᶠ m in atTop, ω ∈ E m) ∧
      ∀ᵐ ω ∂P, ∀ m, ω ∈ E m →
        LocLen.unzipLengthsArc γ (unscaledConfig γ κ X A B ω) (GermZeroOne.epsSeq m : ℝ) = h m ω

/-- Replacement of input (R1): a.s. the unzipped wedge field has local limits on the two open
arcs at every time `1/(m+1)`. -/
def WedgeUnzipArcLimitStmt (γ α κ : ℝ) : Prop :=
  0 < κ → κ < 4 → γ = Real.sqrt κ → α < Qc γ →
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → FieldSample) (A : ℝ → Ω → ℝ)
    (B : ℝ≥0 → Ω → ℝ), IsProbabilityMeasure P → IsFreeGFFModConstH X P →
    IsWedgeProcess α (Qc γ) A P → IsBrownianReal B P → (∀ t, Measurable (A t)) →
    (∀ t, Measurable (B t)) → iIndep (srcSigma X A B) P →
    ∀ᵐ ω ∂P, ∀ m : ℕ, ArcLimits γ (unscaledConfig γ κ X A B ω) (GermZeroOne.epsSeq m : ℝ)

theorem locality_coreArc {γ κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → FieldSample} {A : ℝ → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (hR2 : SideSmallStmt)
    (hR4 : F1.LocLengthsMeasArcStmt γ κ)
    (hlim : ∀ᵐ ω ∂P, ∀ m : ℕ, ArcLimits γ (unscaledConfig γ κ X A B ω) (GermZeroOne.epsSeq m : ℝ))
    (n : ℕ) {ρ : ℝ} (hρ : 0 < ρ) {j₀ : ℕ} {Y : Ω → FieldSample}
    (hYm : Measurable[levelSigma X P A B n] Y)
    (hYag : ∀ᵐ ω ∂P, DyCircAgree (unscaledConfig γ κ X A B ω).1 (Y ω) (Metric.ball 0 ρ) j₀) :
    ∃ (E : ℕ → Set Ω) (h : ℕ → Ω → ℝ≥0∞ × ℝ≥0∞),
      (∀ m, MeasurableSet[⨆ i ∈ (Finset.univ : Finset (Fin 3)), germFam X P A B i n] (E m)) ∧
      (∀ m, Measurable[⨆ i ∈ (Finset.univ : Finset (Fin 3)), germFam X P A B i n] (h m)) ∧
      (∀ᵐ ω ∂P, ∀ᶠ m in atTop, ω ∈ E m) ∧
      ∀ᵐ ω ∂P, ∀ m, ω ∈ E m →
        LocLen.unzipLengthsArc γ (unscaledConfig γ κ X A B ω) (GermZeroOne.epsSeq m : ℝ) =
          h m ω := by
  obtain ⟨M₁, hM₁, t₀, ht₀, hside⟩ := hR2 (ρ / 8) (by positivity)
  set M : ℝ := min M₁ (ρ / 48) with hMdef
  have hM : 0 < M := lt_min hM₁ (by positivity)
  have hε : Tendsto (fun m => (GermZeroOne.epsSeq m : ℝ)) atTop (𝓝 0) := by
    have := (NNReal.continuous_coe.tendsto 0).comp GermZeroOne.tendsto_epsSeq
    simpa [Function.comp_def] using this
  obtain ⟨m₀, hm₀⟩ := eventually_atTop.1
    (hε.eventually (ge_mem_nhds (lt_min ht₀ (by positivity : (0 : ℝ) < (ρ / 24) ^ 2))))
  set u : ℝ≥0 := GermZeroOne.epsSeq n with hu
  set pn : Ω → (Set.Iic u → ℝ) := fun ω t => B t ω with hpn
  have hle := bmPast_le_levelSigma X P A B n
  have hpnm : Measurable[levelSigma X P A B n] pn :=
    Measurable.mono (comap_measurable pn) hle le_rfl
  have hΦ : ∀ m, n ≤ m → ∃ Φ : FieldSample × (Set.Iic u → ℝ) → ℝ≥0∞ × ℝ≥0∞, Measurable Φ ∧
      ∀ q : FieldSample × (Set.Iic u → ℝ), Continuous q.2 → q.2 ⟨0, Set.mem_Iic.2 zero_le⟩ = 0 →
        (∀ x : ℝ, x ≠ 0 → ∃ v, IsForwardSol (clampDrive κ u q.2) (x : ℂ)
          (GermZeroOne.epsSeq m : ℝ) v) →
        |(sideImages (clampDrive κ u q.2) (GermZeroOne.epsSeq m : ℝ)).1| < ρ / 8 →
        |(sideImages (clampDrive κ u q.2) (GermZeroOne.epsSeq m : ℝ)).2| < ρ / 8 →
        (∃ ν, IsVagueLimitOnR (Ioo (sideImages (clampDrive κ u q.2) (GermZeroOne.epsSeq m : ℝ)).1 0)
          (bdryApprox γ (unzippedField γ (q.1, clampDrive κ u q.2) (GermZeroOne.epsSeq m : ℝ))) ν) →
        (∃ ν, IsVagueLimitOnR (Ioo 0 (sideImages (clampDrive κ u q.2) (GermZeroOne.epsSeq m : ℝ)).2)
          (bdryApprox γ (unzippedField γ (q.1, clampDrive κ u q.2) (GermZeroOne.epsSeq m : ℝ))) ν) →
        Φ q = LocLen.unzipLengthsArc γ (q.1, clampDrive κ u q.2) (GermZeroOne.epsSeq m : ℝ) :=
      fun m hm =>
    hR4 u (ρ / 8) _ (by positivity) (by exact_mod_cast GermZeroOne.epsSeq_pos m)
      (by exact_mod_cast GermZeroOne.epsSeq_antitone hm)
  choose! Φ hΦm hΦeq using hΦ
  classical
  refine ⟨fun m => if n ≤ m ∧ m₀ ≤ m then ⋂ q : ℚ, {ω | 0 ≤ (q : ℝ) →
      (q : ℝ) ≤ (GermZeroOne.epsSeq m : ℝ) → |drive κ B ω (q : ℝ)| ≤ M} else ∅,
    fun m ω => if n ≤ m then Φ m (Y ω, pn ω) else 0, ?_, ?_, ?_, ?_⟩
  · -- measurability of the events
    intro m
    by_cases hc : n ≤ m ∧ m₀ ≤ m
    · simp only [if_pos hc]
      refine MeasurableSet.iInter fun q => ?_
      by_cases hq : 0 ≤ (q : ℝ) ∧ (q : ℝ) ≤ (GermZeroOne.epsSeq m : ℝ)
      · have e : {ω | 0 ≤ (q : ℝ) → (q : ℝ) ≤ (GermZeroOne.epsSeq m : ℝ) →
            |drive κ B ω (q : ℝ)| ≤ M} = {ω | |drive κ B ω (q : ℝ)| ≤ M} := by
          ext ω; simp [hq.1, hq.2]
        rw [e]
        have hqu : (q : ℝ).toNNReal ≤ u := by
          rw [Real.toNNReal_le_iff_le_coe]
          exact hq.2.trans (by exact_mod_cast GermZeroOne.epsSeq_antitone hc.1)
        have hBq : Measurable[levelSigma X P A B n] fun ω => B (q : ℝ).toNNReal ω :=
          (measurable_pi_apply (⟨(q : ℝ).toNNReal, hqu⟩ : Set.Iic u)).comp hpnm
        exact measurableSet_le (continuous_abs.measurable.comp (measurable_const.mul hBq)) measurable_const
      · have e : {ω | 0 ≤ (q : ℝ) → (q : ℝ) ≤ (GermZeroOne.epsSeq m : ℝ) →
            |drive κ B ω (q : ℝ)| ≤ M} = univ := by
          ext ω
          simp only [mem_setOf_eq, mem_univ, iff_true]
          intro h1 h2
          exact absurd ⟨h1, h2⟩ hq
        rw [e]
        exact @MeasurableSet.univ _ (levelSigma X P A B n)
    · simp only [if_neg hc]
      exact @MeasurableSet.empty _ (levelSigma X P A B n)
  · -- measurability of the lengths functionals
    intro m
    by_cases hm : n ≤ m
    · simp only [if_pos hm]
      exact (hΦm m hm).comp (hYm.prodMk hpnm)
    · simp only [if_neg hm]
      exact measurable_const
  · -- the events eventually occur
    filter_upwards [hB.cont, hB.toIsPreBrownianReal.eval_zero_ae_eq_zero] with ω hc h0
    have hWc : Continuous (drive κ B ω) := drive_continuous hc
    obtain ⟨δ, hδ, hδW⟩ := Metric.continuous_iff.1 hWc 0 M hM
    filter_upwards [eventually_ge_atTop n, eventually_ge_atTop m₀,
      hε.eventually (gt_mem_nhds hδ)] with m h1 h2 h3
    simp only [if_pos (And.intro h1 h2), mem_iInter, mem_setOf_eq]
    intro q hq0 hqe
    have := hδW (q : ℝ) (by rw [Real.dist_eq, sub_zero, abs_of_nonneg hq0]; linarith)
    rw [Real.dist_eq, drive_zero h0, sub_zero] at this
    exact this.le
  · -- on the events, the lengths are the functionals
    filter_upwards [hlim, hB.cont, hB.toIsPreBrownianReal.eval_zero_ae_eq_zero, hYag,
      RS.ae_real_alive hB hκ hκ4.le] with ω hl hc h0 hag halive m hmE
    by_cases hcm : n ≤ m ∧ m₀ ≤ m
    swap
    · simp only [if_neg hcm] at hmE
      exact absurd hmE (notMem_empty _)
    simp only [if_pos hcm, mem_iInter, mem_setOf_eq] at hmE
    simp only [if_pos hcm.1]
    set t : ℝ := (GermZeroOne.epsSeq m : ℝ) with htdef
    have ht : 0 < t := by exact_mod_cast GermZeroOne.epsSeq_pos m
    have htt : t ≤ min t₀ ((ρ / 24) ^ 2) := hm₀ m hcm.2
    have htu : t ≤ (u : ℝ) := by exact_mod_cast GermZeroOne.epsSeq_antitone hcm.1
    set W : ℝ → ℝ := drive κ B ω with hWdef
    have hWc : Continuous W := drive_continuous hc
    have hW0 : W 0 = 0 := drive_zero h0
    have hMW : ∀ r ∈ Icc (0 : ℝ) t, |W r| ≤ M := abs_le_of_forall_rat hWc ht hmE
    obtain ⟨hs₁, hs₂⟩ := hside W hWc hW0 t ⟨ht, htt.trans (min_le_left _ _)⟩
      (fun x hx => halive x hx t ht.le) (fun r hr => (hMW r hr).trans (min_le_left _ _))
    have hsq : Real.sqrt t ≤ ρ / 24 := by
      calc Real.sqrt t ≤ Real.sqrt ((ρ / 24) ^ 2) :=
            Real.sqrt_le_sqrt (htt.trans (min_le_right _ _))
        _ = ρ / 24 := Real.sqrt_sq (by positivity)
    have hM48 : M ≤ ρ / 48 := min_le_right _ _
    set W' : ℝ → ℝ := clampDrive κ u (pn ω) with hW'def
    have hW'eq : W' = fun r => Real.sqrt κ * B (min r.toNNReal u) ω := by rw [hW'def, hpn]; rfl
    have hW'c : Continuous W' := by
      rw [hW'eq]
      exact continuous_const.mul (hc.comp (continuous_real_toNNReal.min continuous_const))
    have hW'0 : W' 0 = 0 := by rw [hW'eq]; simp [h0]
    have hWW' : ∀ r ∈ Icc (0 : ℝ) t, W r = W' r := by
      intro r hr
      rw [hW'eq, hWdef]
      have : min r.toNNReal u = r.toNNReal :=
        min_eq_left ((Real.toNNReal_le_iff_le_coe).2 (hr.2.trans htu))
      simp only [drive, this]
    have hU₁ : Ioo (sideImages W t).1 0 ⊆ Ioo (-(ρ / 8)) (ρ / 8) := by
      intro y hy
      have := (abs_lt.1 hs₁).1
      exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
    have hU₂ : Ioo 0 (sideImages W t).2 ⊆ Ioo (-(ρ / 8)) (ρ / 8) := by
      intro y hy
      have := (abs_lt.1 hs₂).2
      exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
    have hψ : ∀ v ∈ H, (∃ s ∈ Ioo (-(ρ / 8)) (ρ / 8), dist v (s : ℂ) < ρ / 8) →
        fwdMapInv W t v ∈ Metric.ball 0 ρ := by
      rintro v hv ⟨s, hs, hvs⟩
      rw [Metric.mem_ball, dist_zero_right]
      have h1 := norm_fwdMapInv_sub_le hWc hW0 ht hMW hv
      have h2 : ‖v‖ < 2 * (ρ / 8) := by
        have hs' : ‖((s : ℝ) : ℂ)‖ < ρ / 8 := by
          rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_lt.2 ⟨hs.1, hs.2⟩
        calc ‖v‖ ≤ ‖v - (s : ℂ)‖ + ‖((s : ℝ) : ℂ)‖ := norm_le_norm_sub_add _ _
          _ < 2 * (ρ / 8) := by rw [← dist_eq_norm]; linarith
      calc ‖fwdMapInv W t v‖ ≤ ‖fwdMapInv W t v - v‖ + ‖v‖ := norm_le_norm_sub_add _ _
        _ < ρ := by linarith
    have key := LocLen.unzipLengthsArc_eq_of_dyCircAgree (γ := γ) (unscaledConfig γ κ X A B ω).1
      (Y ω) hWc hW'c hW0 hW'0 ht.le hWW' hU₁ hU₂ Metric.isOpen_ball (by positivity) hψ hag
    have hloc := eventually_avgReg_unzipped_eq (γ := γ) (unscaledConfig γ κ X A B ω).1 (Y ω)
      hWc hW'c hW0 hW'0 ht.le hWW' Metric.isOpen_ball (by positivity) hψ hag
    have htr : ∀ V : Set ℝ, IsOpen V → V ⊆ Ioo (-(ρ / 8)) (ρ / 8) →
        (∃ ν, IsVagueLimitOnR V (bdryApprox γ (unzippedField γ (unscaledConfig γ κ X A B ω) t)) ν) →
        ∃ ν, IsVagueLimitOnR V (bdryApprox γ (unzippedField γ (Y ω, W') t)) ν := by
      rintro V hV hVU ⟨ν, hν⟩
      refine ⟨ν, hν.1, hν.2.1, fun f hf hfc hfV => (hν.2.2 f hf hfc hfV).congr' ?_⟩
      filter_upwards [hloc] with k hk
      exact PalmNorm.integral_eq_of_restrict_eq'
        (PalmNorm.bdryApprox_restrict_eq hV.measurableSet fun s hs => hk s (hVU hs))
        (fun s hs => image_eq_zero_of_notMem_tsupport fun h' => hs (hfV h'))
    have hside' : sideImages W' t = sideImages W t := (ESM.sideImages_congr_drive ht.le hWW').symm
    have halive' : ∀ x : ℝ, x ≠ 0 → ∃ v, IsForwardSol W' (x : ℂ) t v := fun x hx => by
      obtain ⟨v, hv⟩ := halive x hx t ht.le
      exact ⟨v, isForwardSol_of_eqOn hv hWW'⟩
    have hex₁ := htr _ isOpen_Ioo hU₁ (hl m).1
    have hex₂ := htr _ isOpen_Ioo hU₂ (hl m).2
    rw [show unscaledConfig γ κ X A B ω = ((unscaledConfig γ κ X A B ω).1, W) from rfl, key]
    exact (hΦeq m hcm.1 (Y ω, pn ω) (hc.comp continuous_subtype_val) h0 halive'
      (by rw [hside']; exact hs₁) (by rw [hside']; exact hs₂)
      (by rw [hside']; exact hex₁) (by rw [hside']; exact hex₂)).symm

/-- **B5 locality for F1, open arcs**, from the arc limits (R1′), (R2) `sideSmallStmt`,
(R3) `wedgeLocalCoordStmt` and (R4′) `locLengthsMeasArcStmt_holds` (all but R1′ proved). -/
theorem f1LocalityArcStmt_of_arcLimits {γ α κ : ℝ} (hR1 : WedgeUnzipArcLimitStmt γ α κ) :
    F1LocalityArcStmt γ α κ := by
  intro hκ hκ4 hγ hα Ω _ P X A B hP hX hA hB hAm hBm hind n
  have := hP
  obtain ⟨ρ, hρ, j₀, Y, hYm, hYag⟩ :=
    wedgeLocalCoordStmt γ α κ hκ hκ4 hγ hα Ω P X A B hP hX hA hB hAm hBm hind n
  exact locality_coreArc hκ hκ4 hB sideSmallStmt (F1.locLengthsMeasArcStmt_holds γ κ)
    (hR1 hκ hκ4 hγ hα Ω P X A B hP hX hA hB hAm hBm hind) n hρ hYm hYag

end B5
end QuantumZipper
