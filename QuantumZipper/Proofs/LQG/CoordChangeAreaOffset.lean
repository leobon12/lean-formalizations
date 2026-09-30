import QuantumZipper.Proofs.LQG.CoordChangeAreaRC3

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Coordinate change of the area measure, uniformly over the radius offsets (COORD-CHANGE, D98)

`CoordChangeArea.ae_hasAreaLimit_coordChange_free`: for the free-boundary GFF `X` on `ℍ` and a
deterministic conformal map `ψ : ℍ → ℍ`, almost surely
`HasAreaLimit γ (X ω ∘ ψ + Q log|ψ'|) (ψ^* μ_{X ω})`, i.e. the area approximations at all radii
`α 2^{-k}`, `α ∈ [1,2]`, converge to the pullback uniformly in the offset `α` (the form needed
for dilations, e.g. the canonical description (1.8): `GoodSample.hasAreaLimit_rescale`).
Duplantier–Sheffield, Invent. Math. 185 (2011), Prop. 2.1, along Sheffield–Wang arXiv:1605.06171,
Thm 1.4, (3.5)–(3.7): the offset distortion bound `pushErrR` is the primed core's third conjunct
once the regularized values of the coordinate change at the offset circles are identified with
the raw ones (`CoordChangeArea.evalReg_coordChange_fc`, RC3) and `log|ψ'|` is replaced by its
circle mean (harmonicity, `SWCore.swcNA2_integral_log_deriv_fc`); then
`SWCore.a9_tendsto_goodFilter`. Own bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Function Metric
open scoped Topology ENNReal

namespace QuantumZipper
namespace CoordChangeArea

open SWCore GoodSample G1Side E6

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

/-- The offset distortion bound of the primed core, read on a rectangle. -/
theorem ae_pushed_offset_err [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    {ψ : ℂ → ℂ} {x₁ x₂ y₁ y₂ ρ M m : ℝ} (hx : x₁ ≤ x₂) (hy0 : 0 < y₁) (hy : y₁ ≤ y₂)
    (hρ : 0 < ρ) (hm : 0 < m) (hψ : ψ ∈ AreaClass x₁ x₂ y₁ y₂ ρ M m) :
    ∃ k₀ : ℕ, ∀ᵐ ω ∂P, ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop, ∀ α ∈ Icc (1 : ℝ) 2,
      ∀ z ∈ rectC x₁ x₂ y₁ y₂,
        |evalReg (X ω) ((foldedCircle z (α * radius k)).map ψ) -
          evalReg (X ω) (foldedCircle (ψ z) (α * radius k * ‖deriv ψ z‖))| ≤ η := by
  obtain ⟨k₀, hae⟩ := swcNA2I_primed hX (constFam_unif hx hy0 hy hρ hm hψ)
  refine ⟨k₀, ?_⟩
  obtain ⟨R, hR⟩ := exists_nat_ge (|x₁| + |x₂| + |y₁| + |y₂| + 2)
  filter_upwards [hae] with ω hω η hη
  obtain ⟨-, -, hE⟩ := hω
  obtain ⟨K, hK⟩ := eventually_atTop.1 (hE R η hη)
  refine eventually_atTop.2 ⟨K + k₀, fun k hk α hα z hz => ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j, k = j + k₀ := ⟨k - k₀, by omega⟩
  have hq : qdα (z, α) ∈ KolmD.boxD (d := 5) R := by
    obtain ⟨⟨hz1, hz2⟩, ⟨hz3, hz4⟩⟩ := hz
    have a1 := le_abs_self x₁; have a2 := neg_abs_le x₁
    have a3 := le_abs_self x₂; have a4 := neg_abs_le x₂
    have a5 := le_abs_self y₁; have a6 := neg_abs_le y₁
    have a7 := le_abs_self y₂; have a8 := neg_abs_le y₂
    have b1 := abs_nonneg x₁; have b2 := abs_nonneg x₂
    have b3 := abs_nonneg y₁; have b4 := abs_nonneg y₂
    have hre : |z.re| ≤ R := abs_le.2 ⟨by linarith, by linarith⟩
    have him : |z.im| ≤ R := abs_le.2 ⟨by linarith, by linarith⟩
    have hαR : |α| ≤ R := abs_le.2 ⟨by linarith [hα.1], by linarith [hα.2]⟩
    intro i
    fin_cases i <;> simp [qdα] <;> first | linarith | exact_mod_cast (by linarith : (0 : ℝ) ≤ R)
  have h := hK j (by omega) (qdα (z, α)) hq
  have hc : a7Cen x₁ x₂ y₁ y₂ (qdα (z, α)) = z := by
    apply Complex.ext
    · simp [qdα, a7Cen, clampI_eq hz.1]
    · simp [qdα, a7Cen, clampI_eq hz.2]
  have ha : a7Rad (qdα (z, α)) = α := by simp [qdα, a7Rad, clampI_eq hα]
  simp only [hc, ha] at h
  exact h

theorem closedBall_sub_recR_succ {n : ℕ} {z : ℂ} (hz : z ∈ recR n) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : t ≤ 1 / ((n + 1 : ℝ) * (n + 2))) : closedBall z t ⊆ recR (n + 1) := by
  intro u hu
  have hd := mem_closedBall.1 hu
  have h1 := Complex.abs_re_le_norm (u - z)
  have h2 := Complex.abs_im_le_norm (u - z)
  rw [← dist_eq_norm, Complex.sub_re] at h1
  rw [← dist_eq_norm, Complex.sub_im] at h2
  obtain ⟨h1a, h1b⟩ := abs_le.1 h1
  obtain ⟨h2a, h2b⟩ := abs_le.1 h2
  obtain ⟨⟨hz1, hz2⟩, ⟨hz3, hz4⟩⟩ := hz
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have ht1 : t ≤ 1 / 2 := ht.trans (by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith)
  have hq : 1 / (n + 1 : ℝ) - 1 / ((n + 1 : ℝ) * (n + 2)) = 1 / ((n + 1 : ℕ) + 1 : ℝ) := by
    push_cast; field_simp; ring
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> push_cast at * <;> linarith

set_option maxHeartbeats 1600000 in
/-- **Coordinate change of the area measure, uniformly over the radius offsets** (free field;
DS11 Prop. 2.1 in the `HasAreaLimit` form). -/
theorem ae_hasAreaLimit_coordChange_free [IsProbabilityMeasure P]
    (hX : IsFreeGFFModConstH X P) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {ψ : ℂ → ℂ}
    (hψm : Measurable ψ) (hψd : DifferentiableOn ℂ ψ H) (hψi : InjOn ψ H)
    (hψH : MapsTo ψ H H) (hψ0 : ∀ z ∈ H, deriv ψ z ≠ 0) :
    ∀ᵐ ω ∂P, HasAreaLimit γ (coordChange (X ω) ψ (Qc γ)) (pullMu (qAreaMeasure γ (X ω)) ψ) := by
  have hcls : ∀ n : ℕ, ∃ ρ M m : ℝ, 0 < ρ ∧ 0 < m ∧ ψ ∈ AreaClass (-((n + 1 : ℕ) : ℝ))
      ((n + 1 : ℕ) : ℝ) (1 / (((n + 1 : ℕ) : ℝ) + 1)) ((n + 1 : ℕ) : ℝ) ρ M m := fun n =>
    exists_areaClass hψd hψi hψH hψ0 (by positivity)
  have hy : ∀ n : ℕ, 1 / (((n + 1 : ℕ) : ℝ) + 1) ≤ ((n + 1 : ℕ) : ℝ) := fun n => by
    have hN : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
      push_cast; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have hx : ∀ n : ℕ, -((n + 1 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := fun n => by
    have : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  choose ρc Mc mc hρc hmc hclc using hcls
  have hA : ∀ n : ℕ, ∃ k₀ : ℕ, ∀ᵐ ω ∂P, ∀ k ≥ k₀,
      TendstoUniformlyOn (fun j (p : ℂ × ℝ) =>
          ∫ u, avgReg (X ω) j u ∂((foldedCircle p.1 (p.2 * radius k)).map ψ))
        (fun p => evalReg (X ω) ((foldedCircle p.1 (p.2 * radius k)).map ψ)) atTop
        (recR (n + 1) ×ˢ Icc 1 2) ∧
      ContinuousOn (fun p : ℂ × ℝ => evalReg (X ω) ((foldedCircle p.1 (p.2 * radius k)).map ψ))
        (recR (n + 1) ×ˢ Icc 1 2) := fun n =>
    ae_pushed_regular_alpha hX (hx n) (by positivity) (hy n) (hρc n) (hmc n) (hclc n)
  have hB : ∀ n : ℕ, ∃ k₀ : ℕ, ∀ᵐ ω ∂P, ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop,
      ∀ α ∈ Icc (1 : ℝ) 2, ∀ z ∈ recR (n + 1),
        |evalReg (X ω) ((foldedCircle z (α * radius k)).map ψ) -
          evalReg (X ω) (foldedCircle (ψ z) (α * radius k * ‖deriv ψ z‖))| ≤ η := fun n =>
    ae_pushed_offset_err hX (hx n) (by positivity) (hy n) (hρc n) (hmc n) (hclc n)
  choose kA hkA using hA
  choose kB hkB using hB
  have hΦc : ContinuousOn ψ H := hψd.continuousOn
  filter_upwards [ae_all_iff.2 hkA, ae_all_iff.2 hkB,
    freeWindowStmt_of_splitR hγ hγ2 (swWindowSplitStmtR_holds hγ hγ2) P X hX,
    RegSample.ae_isRegularSample hX, AreaOffsets.ae_hasAreaLimit hX hγ hγ2]
    with ω hAω hBω hW hreg hμ
  have hμK : ∀ K, IsCompact K → K ⊆ H → qAreaMeasure γ (X ω) K < ⊤ := hμ.2.1
  obtain ⟨F, hF⟩ := hreg
  refine ⟨pullMu_compl_H hΦc hψi, fun K hK hKH => ?_, fun f hf hfc hfH => ?_⟩
  · rw [pullMu_apply hΦc hψi hK.isClosed.measurableSet, inter_eq_left.2 hKH]
    exact hμK _ (hK.image_of_continuousOn (hΦc.mono hKH)) (hψH.image_subset.trans' (image_mono hKH))
  obtain ⟨n, hn⟩ := exists_recR hfc hfH
  set a : ℚ := -(n : ℚ) with ha
  set b : ℚ := (n : ℚ) with hb
  set c : ℚ := 1 / ((n : ℚ) + 1) with hcq
  set d : ℚ := (n : ℚ) with hd
  have hrect : rectC (a : ℝ) b c d = recR n := by
    simp only [recR, ha, hb, hcq, hd]; push_cast; rfl
  have hc0 : (0 : ℝ) < c := by rw [hcq]; push_cast; positivity
  obtain ⟨ρ', M', m', hρ', hm', hcl'⟩ := exists_areaClass (a := a) (b := b) (d := d)
    hψd hψi hψH hψ0 hc0
  obtain ⟨ρq, hρq0, hρq⟩ := exists_rat_btwn hρ'
  obtain ⟨Mq, hMq⟩ := exists_rat_gt M'
  obtain ⟨mq, hmq0, hmq⟩ := exists_rat_btwn hm'
  have hcl : ψ ∈ AreaClass a b c d ρq Mq mq := areaClass_mono hcl' hρq.le hMq.le hmq.le
  have hfK : tsupport f ⊆ interior (rectC (a : ℝ) b c d) := by rw [hrect]; exact hn
  -- the offset distortion bound on `R_n`
  set δ : ℝ := 1 / (2 * ((n + 1 : ℝ) * (n + 2))) with hδdef
  have hδ : 0 < δ := by positivity
  have hδ2 : δ + δ = 1 / ((n + 1 : ℝ) * (n + 2)) := by rw [hδdef]; field_simp; ring
  have hErr : ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop, ∀ α ∈ Icc (1 : ℝ) 2,
      ∀ z ∈ rectC (a : ℝ) b c d, |pushErrR γ (X ω) ψ (α * radius k) z| ≤ η := by
    intro η hη
    have hsmall : ∀ᶠ k in atTop, kA n ≤ k ∧ 2 * radius k ≤ δ :=
      (eventually_ge_atTop (kA n)).and ((RegClosure.tendsto_radius_nhdsGT.mono_right
        nhdsWithin_le_nhds).eventually (ge_mem_nhds (by linarith : (0 : ℝ) < δ / 2)) |>.mono
        fun k hk => by linarith)
    filter_upwards [hBω n η hη, hsmall] with k hk hk2 α hα z hz
    rw [hrect] at hz
    have hr := radius_pos k
    have hρ : 0 < α * radius k := mul_pos (by linarith [hα.1]) hr
    have hρδ : α * radius k ≤ δ := by nlinarith [hα.2]
    have hball : closedBall z (α * radius k + δ) ⊆ recR (n + 1) :=
      closedBall_sub_recR_succ hz (by linarith) (by linarith)
    have hrc3 := evalReg_coordChange_fc hF hψm hψd hψ0 hψH (recR_subset_H (n + 1))
      (fun k' hk' => (hAω n k' hk').1) (fun k' hk' => (hAω n k' hk').2) (Qc γ) hρ hδ hball
      hk2.1 hα rfl
    have hBH : closedBall z (α * radius k) ⊆ H :=
      (closedBall_subset_closedBall (by linarith)).trans (hball.trans (recR_subset_H (n + 1)))
    have h2im := two_mul_le_im_of_closedBall_subset hρ.le ((closedBall_subset_closedBall
      (by linarith)).trans (hball.trans (recR_subset_H (n + 1))))
    have hlog := swcNA2_integral_log_deriv_fc isOpen_H hψd hψ0 hρ (by linarith) hBH
    unfold pushErrR
    rw [hrc3]
    show |evalReg (X ω) ((foldedCircle z (α * radius k)).map ψ) +
        Qc γ * ∫ u, Real.log ‖deriv ψ u‖ ∂foldedCircle z (α * radius k) -
        Qc γ * Real.log ‖deriv ψ z‖ -
        evalReg (X ω) (foldedCircle (ψ z) (α * radius k * ‖deriv ψ z‖))| ≤ η
    rw [hlog]
    have := hk α hα z (recR_subset_succ n hz)
    calc _ = |evalReg (X ω) ((foldedCircle z (α * radius k)).map ψ) -
          evalReg (X ω) (foldedCircle (ψ z) (α * radius k * ‖deriv ψ z‖))| := by ring_nf
      _ ≤ η := this
  have h9 := a9_tendsto_goodFilter hγ (tendsto_swC γ) (tendsto_swC' γ) hW hμK
    (measurable_supWin ⟨F, hF⟩ γ) (measurable_infWin ⟨F, hF⟩ γ) hc0 (by exact_mod_cast hρq0)
    (by exact_mod_cast hmq0) hcl hErr hf hfc hfK
  rw [integral_pullMu hΦc hψi (hrect ▸ recR_subset_H n) hf (hfK.trans interior_subset)]
  exact h9

end CoordChangeArea
end QuantumZipper
