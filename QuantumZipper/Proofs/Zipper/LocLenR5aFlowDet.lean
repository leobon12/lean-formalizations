import QuantumZipper.Proofs.Zipper.LocLenR5aZip
import QuantumZipper.Proofs.Zipper.LocLenR5aPalm
import QuantumZipper.Proofs.Zipper.LocLenR5cPStar
import QuantumZipper.Proofs.Zipper.ZipLenField

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R5a (D75): good zipper behaviour of the canonicalized capacity flow, open arcs

* `isRegularSample_unzippedField_canon_pt`: copy of `B3d.ZipLen.zipLen_field_pt`
  (ZipLenField.lean:68) ending with the raw folded-circle form
  `WedgeUnzip.unzippedField_canonConfig_fc` instead of the `RegEq` form: the unzipped fields of
  the canonicalized collided configuration are regular samples (needed because goodness off a
  set, `IsLQGGoodOff`, includes regularity of the field itself).
* `hitScaleGoodArc_canon`: copy of `E6.hitScaleGood_canon` (E6FlowGood.lean:48) with open-arc
  lengths (`unzipLengthsArc_canon_fst`) and goodness off the chart tip.

Sources: Sheffield arXiv:1012.4797 §5.1 (rule (5.1), pp. 60–62) and §5.4 pp. 70–72; own
bookkeeping (verbatim copies of the old proofs).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace LocLen

open B2 E1 D3Plus E6 R5c

variable {γ : ℝ} {y₀ : FieldSample} {W : ℝ → ℝ}

/-- **Regularity of the unzipped canonicalized collided fields** (copy of
`B3d.ZipLen.zipLen_field_pt`, raw folded-circle ending). -/
theorem isRegularSample_unzippedField_canon_pt (hW : Continuous W) (hW0 : W 0 = 0)
    (hG : ∀ t : ℝ, 0 ≤ t → IsRegularSample (unzippedField γ (y₀, W) t))
    (hE : ∀ t : ℝ, 0 ≤ t → ∀ d ∈ Hbar, ∀ r > 0,
      evalReg (unzippedField γ (y₀, W) t) (foldedCircle d r) =
        unzippedField γ (y₀, W) t (foldedCircle d r))
    (hRC : ∀ u s : ℝ, 0 ≤ u → 0 ≤ s → ∀ d ∈ Hbar, ∀ r : ℝ, 0 < r →
      evalReg (unzippedField γ (y₀, W) u)
          ((foldedCircle d r).map (revMap (B2.vrev W (u + s)) s)) =
        unzippedField γ (y₀, W) u ((foldedCircle d r).map (revMap (B2.vrev W (u + s)) s)))
    (hC : ∀ u t : ℝ, 0 ≤ u → 0 ≤ t → ∀ (c : ℂ) (r : ℝ), 0 < r →
      ∃ L : ℝ, Tendsto (fun ρ => ∫ v, evalReg (unzippedField γ (y₀, W) u) (foldedCircle v ρ)
          ∂((foldedCircle c r).map (fwdMapInv (F1.shiftDrv W u) t))) (𝓝[>] 0) (𝓝 L))
    {u : ℝ} (hu : 0 ≤ u) (k : ℝ)
    (ha : 0 < scaleParam γ (addConst (zipCapDown γ u (y₀, W)).1 k)) {s : ℝ} (hs : 0 ≤ s) :
    IsRegularSample (unzippedField γ (canonConfig γ
        (addConst (zipCapDown γ u (y₀, W)).1 k, (zipCapDown γ u (y₀, W)).2)) s) := by
  obtain ⟨hWc, hWc0, hWcmax⟩ := F1.zipCapDown_snd_props (γ := γ) (τ := u) (c := (y₀, W)) hW
  set Yu := (zipCapDown γ u (y₀, W)).1 with hYu_def
  set Wc := (zipCapDown γ u (y₀, W)).2 with hWc_def
  set a := scaleParam γ (addConst Yu k) with ha_def
  have hYu : IsRegularSample Yu := hG u hu
  have has : 0 ≤ a ^ 2 * s := mul_nonneg (sq_nonneg a) hs
  have hCD : ∀ t : ℝ, 0 ≤ t → ∀ (c : ℂ) (r : ℝ), 0 < r →
      F1.ContData Yu ((foldedCircle c r).map (fwdMapInv Wc t)) := by
    intro t ht c r hr
    rw [hWc_def, B3d.ZipLen.fc_map_zipCapDown_snd hW hu ht c hr]
    exact ⟨fun ρ hρ => F1.integrable_smoothed_of_regular hYu hWc
      hWc0 ht c hr hρ, hC u t hu ht c r hr⟩
  have hRS : ∀ t : ℝ, 0 ≤ t → ∀ d ∈ Hbar, ∀ r : ℝ, 0 < r →
      E1.RegShift Yu ((foldedCircle d r).map (fwdMapInv Wc t)) := fun t ht d _ r hr =>
    F1.regShift_of_contData hYu (F1.fc_map_fwdMapInv_props hWc hWc0 ht d hr).2 (hCD t ht d r hr)
  have hK : ∀ t : ℝ, 0 ≤ t → RegEq (unzippedField γ (addConst Yu k, Wc) t)
      (addConst (unzippedField γ (Yu, Wc) t) k) := fun t ht =>
    F1.regEq_unzippedField_addConst_of_regShift (hRS t ht)
  have hraw : ∀ t : ℝ, 0 ≤ t → ∀ d ∈ Hbar, ∀ r : ℝ, 0 < r →
      unzippedField γ (Yu, Wc) t (foldedCircle d r) =
        unzippedField γ (y₀, W) (u + t) (foldedCircle d r) := fun t ht d hd r hr =>
    F1.flow_raw_cocycle_of_rc3 γ y₀ hW hW0 hu ht d hr (hRC u t hu ht d hd r hr)
  have hsc : ∀ (d : ℂ) (r : ℝ), 0 < r → Thm18Asm.G1.ScaleConsistentAt (addConst Yu k) (Qc γ) a
      ((foldedCircle d r).map (fwdMapInv (canonConfig γ (addConst Yu k, Wc)).2 s)) := by
    intro d r hr
    rw [B3d.canonConfig_snd_of_max hWcmax]
    have hy : IsRegularSample (addConst Yu k) := hYu.addConst' k
    obtain ⟨hint, L, hL⟩ := hCD (a ^ 2 * s) has ((a : ℂ) * d) (a * r) (mul_pos ha hr)
    have := (F1.fc_map_fwdMapInv_props hWc hWc0 has ((a : ℂ) * d) (mul_pos ha hr)).1
    refine WedgeUnzip.scaleConsistent_of_continuum hy (Qc γ) hWc hWc0 ha hs d hr
      (fun ρ hρ => F1.integrable_smoothed_of_regular hy hWc hWc0 has _ (mul_pos ha hr) hρ)
      ⟨L + ∫ _v, k ∂((foldedCircle ((a : ℂ) * d) (a * r)).map (fwdMapInv Wc (a ^ 2 * s))), ?_⟩
    refine (hL.add_const _).congr' (eventually_mem_nhdsWithin.mono fun ρ hρ => ?_)
    have hρ' : (0 : ℝ) < ρ := hρ
    simp_rw [B3d.ZipLen.evalReg_addConst_fc_of_regular hYu k _ hρ']
    exact (integral_add (hint ρ hρ') (integrable_const k)).symm
  have hDreg : IsRegularSample (unzippedField γ (Yu, Wc) (a ^ 2 * s)) :=
    F1.isRegularSample_of_fc_Hbar (hraw _ has) (hG _ (add_nonneg hu has))
  have hUfc : ∀ d ∈ Hbar, ∀ r : ℝ, 0 < r →
      unzippedField γ (addConst Yu k, Wc) (a ^ 2 * s) (foldedCircle d r) =
        unzippedField γ (Yu, Wc) (a ^ 2 * s) (foldedCircle d r) + k := fun d hd r hr =>
    F2.coordChange_addConst_fc k (hRS _ has d hd r hr)
  have hexact : ∀ d ∈ Hbar, ∀ r > 0,
      evalReg (unzippedField γ (addConst Yu k, Wc) (a ^ 2 * s)) (foldedCircle d r) =
        unzippedField γ (addConst Yu k, Wc) (a ^ 2 * s) (foldedCircle d r) := by
    intro d hd r hr
    have hDeq := F1.regEq_of_fc_Hbar (hraw _ has)
    have h1 : evalReg (unzippedField γ (addConst Yu k, Wc) (a ^ 2 * s)) =
        evalReg (addConst (unzippedField γ (Yu, Wc) (a ^ 2 * s)) k) :=
      Factorization.evalReg_congr (B3d.avgReg_eq_of_regEq (hK _ has))
    have h3 : evalReg (unzippedField γ (Yu, Wc) (a ^ 2 * s)) (foldedCircle d r) =
        unzippedField γ (y₀, W) (u + a ^ 2 * s) (foldedCircle d r) := by
      rw [Factorization.evalReg_congr (B3d.avgReg_eq_of_regEq hDeq)]
      exact hE _ (add_nonneg hu has) d hd r hr
    rw [h1, B3d.ZipLen.evalReg_addConst_fc_of_regular hDreg k d hr, h3, hUfc d hd r hr,
      hraw _ has d hd r hr]
  have hVreg : IsRegularSample (unzippedField γ (addConst Yu k, Wc) (a ^ 2 * s)) :=
    F1.isRegularSample_of_fc_Hbar (fun d hd r hr => by
      rw [hUfc d hd r hr]; simp [addConst]) (hDreg.addConst' k)
  have hfc := WedgeUnzip.unzippedField_canonConfig_fc (γ := γ) (y := addConst Yu k)
    (W := Wc) hWc hWc0 hWcmax ha hs hsc hexact
  exact F1.isRegularSample_of_fc_Hbar (fun d _ r hr => hfc d r hr) (hVreg.rescale' (Qc γ) ha)

/-- **Deterministic core, open arcs** (copy of `E6.hitScaleGood_canon`). -/
theorem hitScaleGoodArc_canon {k ℓ : ℝ} (hγ : 0 < γ) (hℓ : 0 < ℓ) {c : FieldSample × (ℝ → ℝ)}
    (hc : Continuous c.2) (hc0 : c.2 0 = 0) (hWmax : ∀ s, c.2 (max s 0) = c.2 s)
    (halive : ∀ x : ℝ, x ≠ 0 → ∀ S : ℝ, 0 ≤ S → ∃ v, IsForwardSol c.2 (x : ℂ) S v)
    (ha : 0 < scaleParam γ (addConst c.1 k))
    (hb : ∀ t, 0 ≤ t → 0 < scaleParam γ (addConst (unzippedField γ c t) k))
    (hside : ∀ t, 0 ≤ t → ∃ l, Tendsto (fun r : ℝ => (fwdMap c.2 t r).re) (𝓝[<] (0 : ℝ)) (𝓝 l))
    (hgood : ∀ t, 0 ≤ t → IsLQGGoodOff γ (unzippedField γ c t) {0})
    (hfield : ∀ s, 0 ≤ s → RegEq (unzippedField γ (canonConfig γ (addConst c.1 k, c.2)) s)
      (rescale (addConst (unzippedField γ c (scaleParam γ (addConst c.1 k) ^ 2 * s)) k) (Qc γ)
        (scaleParam γ (addConst c.1 k))))
    (hregY : ∀ s, 0 ≤ s →
      IsRegularSample (unzippedField γ (canonConfig γ (addConst c.1 k, c.2)) s))
    (hmono : MonotoneOn (fun t => (unzipLengthsArc γ c t).1) (Ici 0))
    (h0 : Tendsto (fun t => (unzipLengthsArc γ c t).1) (𝓝[>] 0) (𝓝 0))
    (hinf : ⨆ t ∈ Ici (0 : ℝ), (unzipLengthsArc γ c t).1 = ⊤) :
    HitScaleGoodArc γ ℓ (canonConfig γ (addConst c.1 k, c.2)) := by
  set a := scaleParam γ (addConst c.1 k) with ha_def
  set y := canonConfig γ (addConst c.1 k, c.2) with hy
  have ha2 : 0 < a ^ 2 := by positivity
  have hy2 : y.2 = fun r => c.2 (a ^ 2 * r) / a := B3d.canonConfig_snd_of_max hWmax
  -- goodness of the unzipped fields of `y`, off the tip
  have hGY : ∀ s, 0 ≤ s → IsLQGGoodOff γ (unzippedField γ y s) {0} := by
    intro s hs
    have h1 := ((hgood _ (by positivity : 0 ≤ a ^ 2 * s)).addConst k).rescale hγ ha
    have hpre : (fun u => a * u) ⁻¹' ({0} : Set ℝ) = {0} := by
      ext z; simp [ha.ne']
    rw [hpre] at h1
    exact isLQGGoodOff_of_regEq_r5a (hregY s hs) (hfield s hs) h1
  have hU : ∀ s, 0 ≤ s → avgReg (unzippedField γ y s) =
      avgReg (rescale (addConst (unzippedField γ c (a ^ 2 * s)) k) (Qc γ) a) :=
    fun s hs => B3d.avgReg_eq_of_regEq (hfield s hs)
  set e : ℝ≥0∞ := ENNReal.ofReal (Real.exp (γ * k / 2)) with he
  have he0 : e ≠ 0 := (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
  have het : e ≠ ⊤ := ENNReal.ofReal_ne_top
  have hL : ∀ s, 0 ≤ s → (unzipLengthsArc γ y s).1 = e * (unzipLengthsArc γ c (a ^ 2 * s)).1 :=
    fun s hs => unzipLengthsArc_canon_fst (x := c.1) (W := c.2) hγ ha hWmax hs
      (hside _ (by positivity)) (hgood _ (by positivity)) (hfield s hs)
  have hmonoY : ∀ s t : ℝ, 0 ≤ s → s ≤ t →
      (unzipLengthsArc γ y s).1 ≤ (unzipLengthsArc γ y t).1 := by
    intro s t hs hst
    rw [hL s hs, hL t (hs.trans hst)]
    exact mul_le_mul_right (hmono (mem_Ici.2 (by positivity))
      (mem_Ici.2 (mul_nonneg ha2.le (hs.trans hst)))
      (mul_le_mul_of_nonneg_left hst ha2.le)) _
  have hreach : ∃ s : ℝ, 0 ≤ s ∧ ENNReal.ofReal ℓ ≤ (unzipLengthsArc γ y s).1 := by
    have hlt : ENNReal.ofReal ℓ / e < ⨆ t ∈ Ici (0 : ℝ), (unzipLengthsArc γ c t).1 :=
      hinf ▸ ENNReal.div_lt_top ENNReal.ofReal_ne_top he0
    obtain ⟨t, ht⟩ := lt_iSup_iff.1 hlt
    obtain ⟨ht0, hl⟩ := lt_iSup_iff.1 ht
    have ht0' : (0 : ℝ) ≤ t := ht0
    refine ⟨t / a ^ 2, div_nonneg ht0' ha2.le, ?_⟩
    rw [hL _ (div_nonneg ht0' ha2.le), mul_div_cancel₀ t ha2.ne']
    calc ENNReal.ofReal ℓ = e * (ENNReal.ofReal ℓ / e) := (ENNReal.mul_div_cancel he0 het).symm
      _ ≤ e * (unzipLengthsArc γ c t).1 := mul_le_mul_right hl.le _
  have h0Y : Tendsto (fun t => (unzipLengthsArc γ y t).1) (𝓝[>] 0) (𝓝 0) := by
    have hmap : Tendsto (fun t : ℝ => a ^ 2 * t) (𝓝[>] 0) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have : Tendsto (fun t : ℝ => a ^ 2 * t) (𝓝 0) (𝓝 (a ^ 2 * 0)) :=
          (continuous_const.mul continuous_id).tendsto 0
        rw [mul_zero] at this
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
        exact mul_pos ha2 ht
    have h1 := ENNReal.Tendsto.const_mul (h0.comp hmap) (Or.inr het) (a := e)
    rw [mul_zero] at h1
    refine h1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    exact (hL t ht.le).symm
  have hmonoY' : MonotoneOn (fun t => (unzipLengthsArc γ y t).1) (Ici 0) :=
    fun s hs t _ hst => hmonoY s t hs hst
  have hτ := lenTimeArc_nonneg γ ℓ y
  refine ⟨?_, ?_, ?_, fun q hq => ?_, fun s t hs hst => hmonoY s t hs hst, hreach,
    lenTimeArc_pos_of hℓ hmonoY' h0Y hreach, isVagueLimitOn_H_of_goodOff (hGY _ hτ), ?_⟩
  · rw [hy2]
    exact (hc.comp (continuous_const.mul continuous_id)).div_const a
  · rw [hy2]
    simp [hc0]
  · intro z hz s hs
    obtain ⟨v, hv⟩ := halive (a * z) (mul_ne_zero ha.ne' hz) (a ^ 2 * s) (by positivity)
    rw [Complex.ofReal_mul] at hv
    have h := LoewnerAlgebra.isForwardSol_scale ha hv
    rw [mul_div_cancel_left₀ s ha2.ne'] at h
    rw [hy2]
    exact ⟨_, h⟩
  · exact (hGY q hq.le).mono (isClosed_offSet _ _) (by simp [offSet])
  · obtain ⟨hGr, -, μG, hμG⟩ := (hgood _ (by positivity : 0 ≤ a ^ 2 * lenTimeArc γ ℓ y)).addConst k
    rw [Factorization.scaleParam_congr (hU _ hτ), scaleParam_rescale_r5a hGr hμG hγ ha]
    exact div_pos (hb _ (by positivity)) ha

end LocLen
end QuantumZipper
