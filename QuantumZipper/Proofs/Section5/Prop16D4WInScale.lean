import QuantumZipper.Proofs.Section5.Prop16D4WInLocal

/-!
# D4⁺ʷ inputs (part 3): the local scale of the unperturbed zoomed field, deterministic part

For a sample `x₀` locally nice on `D ∪ (a,b)` (`IsLocNiceOn`) and a boundary point
`t ∈ (a,b)` with `B(t,r) ∩ ℍ ⊆ D`, the local area measure of `F_C = x₀(· + t) + C/γ + k` on
`D − t` is `e^{γ(ψ(·+t) + C/γ + k)} · μ_{y(·+t)}` (local rule), with `ψ(·+t)` bounded near `0`,
`μ_{y(·+t)}(B_a ∩ ℍ)` finite and positive. Hence (`scale_family`):
* for every `δ > 0`, eventually in `C`, `0 < a_C < δ` (`a_C` the local scale of `F_C`);
* the event `¬(0 < a_C < δ)` is antitone in `C` (the area grows with `C`).
These are the deterministic inputs of clause `hsc0` of `Prop16D4WInputsStmt`.

Own elementary argument (in the paper this is the remark that the zoomed area near the marked
point is finite and positive; Sheffield, arXiv:1012.4797, proof of Prop. 1.6, p. 25).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal

namespace QuantumZipper

namespace Prop16Asm

open Prop16Area.G

/-- Monotonicity of the local scale sets under a pointwise increase of the measure. -/
theorem sInf_scale_le {ν ν' : Measure ℂ} (hνν : ∀ a, ν (ball 0 a ∩ H) ≤ ν' (ball 0 a ∩ H))
    (hne : {a : ℝ | 0 < a ∧ 1 ≤ ν (ball 0 a ∩ H)}.Nonempty) :
    sInf {a : ℝ | 0 < a ∧ 1 ≤ ν' (ball 0 a ∩ H)} ≤ sInf {a : ℝ | 0 < a ∧ 1 ≤ ν (ball 0 a ∩ H)} :=
  csInf_le_csInf ⟨0, fun _ ha => ha.1.le⟩ hne fun a ha => ⟨ha.1, ha.2.trans (hνν a)⟩

/-- **Abstract scale family.** -/
theorem scale_family {γ k M r1 : ℝ} (hγ : 0 < γ) {μ1 : Measure ℂ} {U : Set ℂ} {f : ℂ → ℝ}
    (hr1 : 0 < r1) (hU : ball 0 r1 ∩ H ⊆ U) (hM : ∀ u ∈ ball (0 : ℂ) r1 ∩ H, |f u| ≤ M)
    (hfin : μ1 (ball 0 r1 ∩ H) < ⊤) (hpos : ∀ a, 0 < a → 0 < μ1 (ball 0 a ∩ H))
    (ν : ℝ → Measure ℂ) (hν : ∀ C, ν C = (μ1.restrict U).withDensity
      (fun u => ENNReal.ofReal (Real.exp (γ * (f u + C / γ + k))))) :
    (∀ δ > 0, ∀ᶠ C in atTop, 0 < sInf {a : ℝ | 0 < a ∧ 1 ≤ ν C (ball 0 a ∩ H)} ∧
      sInf {a : ℝ | 0 < a ∧ 1 ≤ ν C (ball 0 a ∩ H)} < δ) ∧
    (∀ δ C' C, C' ≤ C → ¬ (0 < sInf {a : ℝ | 0 < a ∧ 1 ≤ ν C (ball 0 a ∩ H)} ∧
      sInf {a : ℝ | 0 < a ∧ 1 ≤ ν C (ball 0 a ∩ H)} < δ) →
      ¬ (0 < sInf {a : ℝ | 0 < a ∧ 1 ≤ ν C' (ball 0 a ∩ H)} ∧
      sInf {a : ℝ | 0 < a ∧ 1 ≤ ν C' (ball 0 a ∩ H)} < δ)) := by
  have hbm : ∀ a : ℝ, MeasurableSet (ball (0 : ℂ) a ∩ H) := fun a =>
    (isOpen_ball.inter isOpen_H).measurableSet
  have happ : ∀ C a, ν C (ball 0 a ∩ H) = ∫⁻ u in ball 0 a ∩ H ∩ U,
      ENNReal.ofReal (Real.exp (γ * (f u + C / γ + k))) ∂μ1 := fun C a => by
    rw [hν, withDensity_apply _ (hbm a), Measure.restrict_restrict (hbm a)]
  -- monotonicity in `C`
  have hmono : ∀ C' C, C' ≤ C → ∀ a, ν C' (ball 0 a ∩ H) ≤ ν C (ball 0 a ∩ H) := by
    intro C' C hCC a
    rw [happ, happ]
    refine lintegral_mono fun u => ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
    have : C' / γ ≤ C / γ := div_le_div_of_nonneg_right hCC hγ.le
    nlinarith
  -- two-sided bounds on small half-balls
  have hsub : ∀ a, a ≤ r1 → ball (0 : ℂ) a ∩ H ⊆ ball 0 r1 ∩ H := fun a ha =>
    inter_subset_inter_left _ (ball_subset_ball ha)
  have hinter : ∀ a, a ≤ r1 → ball (0 : ℂ) a ∩ H ∩ U = ball 0 a ∩ H := fun a ha =>
    inter_eq_left.2 ((hsub a ha).trans hU)
  have hup : ∀ C a, a ≤ r1 → ν C (ball 0 a ∩ H) ≤
      ENNReal.ofReal (Real.exp (γ * (M + C / γ + k))) * μ1 (ball 0 a ∩ H) := by
    intro C a ha
    rw [happ, hinter a ha, ← setLIntegral_const]
    refine lintegral_mono_ae ((ae_restrict_iff' (hbm a)).2 (Eventually.of_forall fun u hu => ?_))
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
    have := (abs_le.1 (hM u (hsub a ha hu))).2
    nlinarith
  have hlow : ∀ C a, a ≤ r1 → ENNReal.ofReal (Real.exp (γ * (-M + C / γ + k))) *
      μ1 (ball 0 a ∩ H) ≤ ν C (ball 0 a ∩ H) := by
    intro C a ha
    rw [happ, hinter a ha, ← setLIntegral_const]
    refine lintegral_mono_ae ((ae_restrict_iff' (hbm a)).2 (Eventually.of_forall fun u hu => ?_))
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
    have := (abs_le.1 (hM u (hsub a ha hu))).1
    nlinarith
  -- small half-balls have small measure
  have hsmall : ∀ E : ℝ≥0∞, E ≠ ⊤ → ∃ a1, 0 < a1 ∧ a1 ≤ r1 ∧ E * μ1 (ball 0 a1 ∩ H) < 1 := by
    intro E hE
    set A : ℕ → Set ℂ := fun n => ball (0 : ℂ) (r1 / (n + 1)) ∩ H with hA
    have hAa : Antitone A := fun m n hmn => inter_subset_inter_left _ (ball_subset_ball
      (div_le_div_of_nonneg_left hr1.le (by positivity) (by exact_mod_cast Nat.succ_le_succ hmn)))
    have hA0 : μ1 (⋂ n, A n) = 0 := by
      refine measure_mono_null (fun z hz => ?_) measure_empty
      simp only [hA, mem_iInter, mem_inter_iff, mem_ball, dist_zero_right] at hz
      have hz0 : ‖z‖ = 0 := by
        refine le_antisymm (le_of_forall_pos_lt_add fun ε hε => ?_) (norm_nonneg z)
        obtain ⟨n, hn⟩ := exists_nat_gt (r1 / ε)
        have h1 := (hz n).1
        have h2 : r1 / (n + 1) < ε := by
          rw [div_lt_iff₀ (by positivity)]
          rw [div_lt_iff₀ hε] at hn
          nlinarith
        linarith
      have : z = 0 := norm_eq_zero.1 hz0
      have h3 := (hz 0).2
      rw [this] at h3
      exact absurd h3 (by simp [H])
    have hlim := tendsto_measure_iInter_atTop (μ := μ1) (fun n => (hbm _).nullMeasurableSet) hAa
      ⟨0, by simp only [Nat.cast_zero, zero_add, div_one]; exact hfin.ne⟩
    rw [hA0] at hlim
    have h2 := ENNReal.Tendsto.const_mul hlim (Or.inr hE)
    rw [mul_zero] at h2
    obtain ⟨n, hn⟩ := (h2.eventually (gt_mem_nhds zero_lt_one)).exists
    exact ⟨r1 / (n + 1), by positivity,
      div_le_self hr1.le (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]), hn⟩
  -- positivity of the scale whenever the scale set is nonempty
  have hposS : ∀ C, {a : ℝ | 0 < a ∧ 1 ≤ ν C (ball 0 a ∩ H)}.Nonempty →
      0 < sInf {a : ℝ | 0 < a ∧ 1 ≤ ν C (ball 0 a ∩ H)} := by
    intro C hne
    obtain ⟨a1, ha1, ha1r, ha1E⟩ := hsmall (ENNReal.ofReal
      (Real.exp (γ * (M + C / γ + k)))) ENNReal.ofReal_ne_top
    refine lt_of_lt_of_le ha1 (le_csInf hne fun a ha => ?_)
    by_contra hlt
    push_neg at hlt
    have h1 : ν C (ball 0 a ∩ H) ≤ ν C (ball 0 a1 ∩ H) :=
      measure_mono (inter_subset_inter_left _ (ball_subset_ball hlt.le))
    exact absurd (ha.2.trans (h1.trans (hup C a1 ha1r))) (not_le.2 ha1E)
  refine ⟨fun δ hδ => ?_, fun δ C' C hCC hC hC' => hC ?_⟩
  · set a0 := min (δ / 2) r1 with ha0
    have ha0p : 0 < a0 := lt_min (by linarith) hr1
    have hm0 := hpos a0 ha0p
    have hm0t : μ1 (ball 0 a0 ∩ H) ≠ ⊤ :=
      (measure_mono (hsub a0 (min_le_right _ _)) |>.trans_lt hfin).ne
    have hm0r : 0 < (μ1 (ball 0 a0 ∩ H)).toReal := ENNReal.toReal_pos hm0.ne' hm0t
    have htend : Tendsto (fun C : ℝ => γ * (-M + C / γ + k)) atTop atTop := by
      refine Tendsto.const_mul_atTop hγ ?_
      refine tendsto_atTop_add_const_right _ k ?_
      exact tendsto_atTop_add_const_left _ (-M) (tendsto_id.atTop_div_const hγ)
    filter_upwards [(Real.tendsto_exp_atTop.comp htend).eventually_ge_atTop
      (μ1 (ball 0 a0 ∩ H)).toReal⁻¹] with C hC
    have hin : a0 ∈ {a : ℝ | 0 < a ∧ 1 ≤ ν C (ball 0 a ∩ H)} := by
      refine ⟨ha0p, le_trans ?_ (hlow C a0 (min_le_right _ _))⟩
      calc (1 : ℝ≥0∞) = ENNReal.ofReal (μ1 (ball 0 a0 ∩ H)).toReal⁻¹ * μ1 (ball 0 a0 ∩ H) := by
            rw [ENNReal.ofReal_inv_of_pos hm0r, ENNReal.ofReal_toReal hm0t,
              ENNReal.inv_mul_cancel hm0.ne' hm0t]
        _ ≤ _ := by gcongr; exact hC
    exact ⟨hposS C ⟨a0, hin⟩, (csInf_le ⟨0, fun _ ha => ha.1.le⟩ hin).trans_lt
      (lt_of_le_of_lt (min_le_left _ _) (by linarith))⟩
  · have hne : {a : ℝ | 0 < a ∧ 1 ≤ ν C' (ball 0 a ∩ H)}.Nonempty := by
      by_contra h
      rw [not_nonempty_iff_eq_empty] at h
      rw [h, Real.sInf_empty] at hC'
      exact lt_irrefl _ hC'.1
    exact ⟨hposS C (hne.mono fun a ha => ⟨ha.1, ha.2.trans (hmono C' C hCC a)⟩),
      (sInf_scale_le (hmono C' C hCC) hne).trans_lt hC'.2⟩

/-- **The local scale of the unperturbed zoomed field at a boundary point** (deterministic). -/
theorem scale_point {γ : ℝ} (hγ : 0 < γ) {D : Set ℂ} (hD : IsOpen D) (hDH : D ⊆ H) {a b : ℝ}
    {x0 : FieldSample} (hx : IsLocNiceOn γ (D ∪ realSet (Ioo a b)) x0) {t : ℝ}
    (ht : t ∈ Ioo a b) {r : ℝ} (hr : 0 < r) (hrD : ball (t : ℂ) r ∩ H ⊆ D) (k : ℝ) :
    (∀ δ > 0, ∀ᶠ C in atTop,
      0 < scaleParamOn γ (addConst (zoomField γ C x0 t) k) (zoomDomain D t) ∧
      scaleParamOn γ (addConst (zoomField γ C x0 t) k) (zoomDomain D t) < δ) ∧
    (∀ δ C' C, C' ≤ C →
      ¬ (0 < scaleParamOn γ (addConst (zoomField γ C x0 t) k) (zoomDomain D t) ∧
        scaleParamOn γ (addConst (zoomField γ C x0 t) k) (zoomDomain D t) < δ) →
      ¬ (0 < scaleParamOn γ (addConst (zoomField γ C' x0 t) k) (zoomDomain D t) ∧
        scaleParamOn γ (addConst (zoomField γ C' x0 t) k) (zoomDomain D t) < δ)) := by
  obtain ⟨W, hWo, hWV, y, ψ, hy, hfin, hpos, hψ, hag⟩ := hx
  obtain ⟨hat, htb⟩ := ht
  set r1 := min (r / 2) (min ((t - a) / 2) ((b - t) / 2)) with hr1
  have hr1p : 0 < r1 := lt_min (by linarith) (lt_min (by linarith) (by linarith))
  have hr1r : r1 < r := (min_le_left _ _).trans_lt (by linarith)
  have hr1a : r1 < t - a := ((min_le_right _ _).trans (min_le_left _ _)).trans_lt (by linarith)
  have hr1b : r1 < b - t := ((min_le_right _ _).trans (min_le_right _ _)).trans_lt (by linarith)
  have hball : ∀ u : ℂ, ‖u‖ < r → 0 < u.im → u + (t : ℂ) ∈ D := fun u hu him =>
    hrD ⟨by rw [mem_ball, dist_eq_norm]; simpa using hu, show 0 < (u + (t : ℂ)).im by simpa using him⟩
  -- the compact neighbourhood where `ψ(· + t)` is bounded
  have hK : closedBall (0 : ℂ) r1 ∩ Hbar ⊆ zoomNbhd D a b t := by
    intro u hu
    have hun : ‖u‖ ≤ r1 := by simpa using hu.1
    rcases (show 0 ≤ u.im from hu.2).lt_or_eq with him | him
    · exact Or.inl (hball u (hun.trans_lt hr1r) him)
    · refine Or.inr ⟨u.re + t, ⟨?_, ?_⟩, ?_⟩
      · have := (abs_le.1 ((Complex.abs_re_le_norm u).trans hun)).1; linarith
      · have := (abs_le.1 ((Complex.abs_re_le_norm u).trans hun)).2; linarith
      · apply Complex.ext <;> simp [← him]
  obtain ⟨M, hM⟩ := (Prop16Area.G.isCompact_closedBall_inter_Hbar 0 r1).exists_bound_of_continuousOn
    ((continuousOn_comp_add hψ t).mono hK)
  have hM' : ∀ u ∈ ball (0 : ℂ) r1 ∩ H, |ψ (u + t)| ≤ M := fun u hu => by
    rw [← Real.norm_eq_abs]
    exact hM u ⟨ball_subset_closedBall hu.1, show (0 : ℝ) ≤ u.im from le_of_lt hu.2⟩
  have hU : ball (0 : ℂ) r1 ∩ H ⊆ zoomDomain D t := fun u hu =>
    hball u (by simpa using (mem_ball.1 hu.1).trans hr1r) hu.2
  -- the area measure of the translated good sample
  set μ1 := qAreaMeasure γ (translate y (t : ℂ)) with hμ1
  have hbm : ∀ a : ℝ, MeasurableSet (ball (0 : ℂ) a ∩ H) := fun a =>
    (isOpen_ball.inter isOpen_H).measurableSet
  have hsubm : Measurable fun z : ℂ => z - (t : ℂ) := (continuous_id.sub continuous_const).measurable
  have hμ1a : ∀ a, μ1 (ball 0 a ∩ H) = qAreaMeasure γ y ((fun z => z - (t : ℂ)) ⁻¹' (ball 0 a ∩ H)) :=
    fun a => by rw [hμ1, GoodTransforms.qAreaMeasure_translate hy t, Measure.map_apply hsubm (hbm a)]
  have hfin1 : μ1 (ball 0 r1 ∩ H) < ⊤ := by
    rw [hμ1a]
    have hsub' : (fun z => z - (t : ℂ)) ⁻¹' (ball 0 r1 ∩ H) ⊆ ball 0 (r1 + ‖(t : ℂ)‖) ∩ H := by
      intro z hz
      refine ⟨?_, ?_⟩
      · have h1 : ‖z - t‖ < r1 := by simpa using hz.1
        rw [mem_ball, dist_zero_right]
        calc ‖z‖ = ‖(z - t) + t‖ := by ring_nf
          _ ≤ ‖z - t‖ + ‖(t : ℂ)‖ := norm_add_le _ _
          _ < r1 + ‖(t : ℂ)‖ := by linarith
      · have h2 : 0 < (z - (t : ℂ)).im := hz.2
        show 0 < z.im
        simpa using h2
    exact (measure_mono hsub').trans_lt (hfin (r1 + ‖(t : ℂ)‖))
  have hpos1 : ∀ a, 0 < a → 0 < μ1 (ball 0 a ∩ H) := fun a ha => by
    rw [hμ1a]
    refine hpos _ ((isOpen_ball.inter isOpen_H).preimage (continuous_id.sub continuous_const))
      (fun z hz => ?_) ⟨(t : ℂ) + (a / 2 : ℝ) * Complex.I, ?_, ?_⟩
    · have h2 : 0 < (z - (t : ℂ)).im := hz.2
      show 0 < z.im
      simpa using h2
    · show (t : ℂ) + (a / 2 : ℝ) * Complex.I - t ∈ ball 0 a
      rw [add_sub_cancel_left, mem_ball, dist_zero_right, norm_mul,
        Complex.norm_I, mul_one, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
      linarith
    · show 0 < ((t : ℂ) + (a / 2 : ℝ) * Complex.I - t).im
      simp; linarith
  -- the local rule
  set Wt := (fun z => z + (t : ℂ)) ⁻¹' W with hWt
  have hWto : IsOpen Wt := hWo.preimage (continuous_id.add continuous_const)
  have hWtV : Wt ∩ Hbar = zoomNbhd D a b t := by
    rw [hWt, preimage_add_inter_Hbar, hWV]; rfl
  have hUo : IsOpen (zoomDomain D t) := hD.preimage (continuous_id.add continuous_const)
  have hUH : zoomDomain D t ⊆ H := fun z hz => by
    have : 0 < (z + (t : ℂ)).im := hDH hz
    show 0 < z.im
    simpa using this
  have hUW : zoomDomain D t ⊆ Wt := fun z hz => by
    have : z ∈ zoomNbhd D a b t := (preimage_mono subset_union_left : zoomDomain D t ⊆ _) hz
    rw [← hWtV] at this
    exact this.1
  have hν : ∀ C, qAreaMeasureOn γ (addConst (zoomField γ C x0 t) k) (zoomDomain D t) =
      (μ1.restrict (zoomDomain D t)).withDensity
        (fun u => ENNReal.ofReal (Real.exp (γ * (ψ (u + t) + C / γ + k)))) := fun C =>
    qAreaMeasureOn_eq_withDensity_of_agree hWto (hy.translate t)
      (hWtV ▸ ((continuousOn_comp_add hψ t).add continuousOn_const).add continuousOn_const)
      (circAgree_zoomFree hWo hWV hy hψ hag C t k) hUo hUH hUW
  exact scale_family hγ hr1p hU hM' hfin1 hpos1 _ hν

end Prop16Asm

end QuantumZipper
