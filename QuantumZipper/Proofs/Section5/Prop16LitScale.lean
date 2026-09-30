import QuantumZipper.Proofs.Section5.Prop16LitFin

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Proposition 1.6: the canonical scale of the zoomed field tends to `0` (node `Prop16ScaleStmt`)

`Prop16Lit.prop16ScaleStmt_holds`: under the weighted law, the (1.8)-scale of the actual zoomed
field `h(· + x) + C/γ` on `D − x` tends to `0` in probability, and is positive with probability
tending to `1`. Input: the same statement for the unperturbed zoomed field `zoomFree`
(`Prop16Asm.prop16_hsc0`, D3⁺(iii)). Near the zoom point the two local area measures have
densities `e^{γ(ψ + 𝔥₀(·+x)) + C}` and `e^{γ(ψ + 𝔥₀(x)) + C}` with respect to the same measure,
so on a half-disc where `|𝔥₀(·+x) − 𝔥₀(x)| ≤ 1` the first is sandwiched between the second at
levels `C − γ` and `C + γ` (`scale_sandwich`); an a.e.-subsequence argument handles the
sample-dependent radius. Own elementary argument (AGENT_GUIDE cost rule).
-/

noncomputable section

open Filter Set Metric MeasureTheory ProbabilityTheory
open scoped Topology ENNReal

namespace QuantumZipper

namespace Prop16Lit

open LitChart Prop16Asm Prop16Area.G

/-- **Scale sandwich.** -/
theorem scale_sandwich {μ νl νu : Measure ℂ} {ρ δ' : ℝ}
    (hlow : ∀ s, 0 < s → s ≤ ρ → νl (ball 0 s ∩ H) ≤ μ (ball 0 s ∩ H))
    (hup : ∀ s, 0 < s → s ≤ ρ → μ (ball 0 s ∩ H) ≤ νu (ball 0 s ∩ H))
    (hu : 0 < scaleOf νu) (hl0 : 0 < scaleOf νl) (hl : scaleOf νl < δ') (hδ'ρ : δ' ≤ ρ) :
    0 < scaleOf μ ∧ scaleOf μ ≤ δ' := by
  have hδ'0 : 0 < δ' := hl0.trans hl
  have hnel : {a : ℝ | 0 < a ∧ 1 ≤ νl (ball 0 a ∩ H)}.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have : scaleOf νl = 0 := by simp only [scaleOf, h, Real.sInf_empty]
    linarith
  obtain ⟨s, ⟨hs0, hs1⟩, hsδ⟩ := exists_lt_of_csInf_lt hnel hl
  have hmem : δ' ∈ {a : ℝ | 0 < a ∧ 1 ≤ μ (ball 0 a ∩ H)} := by
    refine ⟨hδ'0, ?_⟩
    calc (1 : ℝ≥0∞) ≤ νl (ball 0 s ∩ H) := hs1
      _ ≤ νl (ball 0 δ' ∩ H) := measure_mono (inter_subset_inter_left _ (ball_subset_ball hsδ.le))
      _ ≤ μ (ball 0 δ' ∩ H) := hlow δ' hδ'0 hδ'ρ
  refine ⟨?_, csInf_le (scaleOf_bdd μ) hmem⟩
  have hmin : 0 < min (scaleOf νu) ρ := lt_min hu (hδ'0.trans_le hδ'ρ)
  refine hmin.trans_le (le_csInf ⟨δ', hmem⟩ fun u ⟨hu0, hu1⟩ => ?_)
  by_contra hlt
  push Not at hlt
  have huρ : u ≤ ρ := (lt_min_iff.1 hlt).2.le
  have : u ∈ {a : ℝ | 0 < a ∧ 1 ≤ νu (ball 0 a ∩ H)} := ⟨hu0, hu1.trans (hup u hu0 huρ)⟩
  have := csInf_le (scaleOf_bdd νu) this
  have := (lt_min_iff.1 hlt).1
  simp only [scaleOf] at *
  linarith

/-- The local-area comparison of the zoomed field with the unperturbed one at shifted levels,
for one locally good sample. -/
theorem sandwich_point {γ : ℝ} (hγ : 0 < γ) {D : Set ℂ} (hD : IsOpen D) (hDH : D ⊆ H)
    {a b c d : ℝ} (hhd : ∀ t ∈ Ioo c d, ∃ r > 0, ball (t : ℂ) r ∩ H ⊆ D) (hca : c ≤ a)
    (hbd : b ≤ d) {h0 : ℂ → ℝ} (hh0 : ContinuousOn h0 (D ∪ realSet (Ioo a b)))
    {x0 : FieldSample} (hx : IsLocallyGoodOn γ (D ∪ realSet (Ioo a b)) x0) {t : ℝ}
    (ht : t ∈ Ioo a b) :
    ∃ ρ > 0, ∀ C s : ℝ, 0 < s → s ≤ ρ →
      qAreaMeasureOn γ (addConst (zoomField γ (C - γ) x0 t) (h0 t)) (zoomDomain D t)
          (ball 0 s ∩ H) ≤
        qAreaMeasureOn γ (zoomField γ C (ofFun h0 + x0) t) (zoomDomain D t) (ball 0 s ∩ H) ∧
      qAreaMeasureOn γ (zoomField γ C (ofFun h0 + x0) t) (zoomDomain D t) (ball 0 s ∩ H) ≤
        qAreaMeasureOn γ (addConst (zoomField γ (C + γ) x0 t) (h0 t)) (zoomDomain D t)
          (ball 0 s ∩ H) := by
  obtain ⟨W, hWo, hWV, y, ψ, hy, hψ, hag⟩ := hx
  obtain ⟨r₁, hr₁, hr₁D⟩ := hhd t ⟨lt_of_le_of_lt hca ht.1, lt_of_lt_of_le ht.2 hbd⟩
  have htV : ((t : ℂ)) ∈ D ∪ realSet (Ioo a b) := Or.inr ⟨t, ht, rfl⟩
  obtain ⟨ρ₀, hρ₀, hρ₀h⟩ := Metric.continuousWithinAt_iff.1 (hh0 _ htV) 1 one_pos
  set ρ := min ρ₀ (min r₁ (min (t - a) (b - t))) / 2 with hρ
  have hm0 : 0 < min (t - a) (b - t) := lt_min (by linarith [ht.1]) (by linarith [ht.2])
  have hρ0 : 0 < ρ := by positivity
  have hρρ₀ : ρ < ρ₀ := by
    have := min_le_left ρ₀ (min r₁ (min (t - a) (b - t))); rw [hρ]; linarith
  have hρr₁ : ρ < r₁ := by
    have := min_le_right ρ₀ (min r₁ (min (t - a) (b - t)))
    have := min_le_left r₁ (min (t - a) (b - t))
    have : 0 < min ρ₀ (min r₁ (min (t - a) (b - t))) := by positivity
    rw [hρ]; linarith
  have hρab : ρ < min (t - a) (b - t) := by
    have := min_le_right ρ₀ (min r₁ (min (t - a) (b - t)))
    have := min_le_right r₁ (min (t - a) (b - t))
    have : 0 < min ρ₀ (min r₁ (min (t - a) (b - t))) := by positivity
    rw [hρ]; linarith
  -- points of `B(0,ρ) ∩ ℍ` shifted by `t` lie in `D`, and `𝔥₀` is `1`-close to `𝔥₀(t)` there
  have hclose : ∀ u : ℂ, u ∈ ball (0 : ℂ) ρ ∩ H → |h0 (u + t) - h0 t| ≤ 1 := by
    intro u ⟨hu, huH⟩
    rw [mem_ball, dist_zero_right] at hu
    have hmemD : u + (t : ℂ) ∈ D := hr₁D ⟨by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_right]; linarith, show 0 < (u + (t : ℂ)).im by
        have : 0 < u.im := huH
        simpa using this⟩
    have := hρ₀h (Or.inl hmemD) (by rw [dist_eq_norm, add_sub_cancel_right]; linarith)
    rw [Real.dist_eq] at this; exact this.le
  refine ⟨ρ, hρ0, fun C s hs hsρ => ?_⟩
  set Wt := (fun z => z + (t : ℂ)) ⁻¹' W with hWt
  have hWto : IsOpen Wt := hWo.preimage (continuous_id.add continuous_const)
  have hWtV : Wt ∩ Hbar = zoomNbhd D a b t := by
    rw [hWt, preimage_add_inter_Hbar, hWV]; rfl
  have hyt : IsLQGGood γ (translate y (t : ℂ)) := hy.translate t
  have hψt : ContinuousOn (fun u => ψ (u + t)) (zoomNbhd D a b t) := continuousOn_comp_add hψ t
  have hh0t : ContinuousOn (fun u => h0 (u + t)) (zoomNbhd D a b t) := continuousOn_comp_add hh0 t
  have hUo : IsOpen (zoomDomain D t) := hD.preimage (continuous_id.add continuous_const)
  have hUH : zoomDomain D t ⊆ H := fun z hz => by
    have : 0 < (z + (t : ℂ)).im := hDH hz
    show 0 < z.im
    simpa using this
  have hUW : zoomDomain D t ⊆ Wt := fun z hz => by
    have : z ∈ zoomNbhd D a b t := preimage_mono subset_union_left hz
    rw [← hWtV] at this
    exact this.1
  -- densities
  have hag' := circAgree_ofFun_add hWV hψ hh0 hag
  have hY := fcAgree_zoomField hWo hWV hy (hψ.add hh0) hag' C t
  have hφY : ContinuousOn (fun u => (ψ (u + t) + h0 (u + t)) + C / γ) (Wt ∩ Hbar) := by
    rw [hWtV]; exact (hψt.add hh0t).add continuousOn_const
  have hF : ∀ C' : ℝ, qAreaMeasureOn γ (addConst (zoomField γ C' x0 t) (h0 t)) (zoomDomain D t) =
      ((qAreaMeasure γ (translate y (t : ℂ))).restrict (zoomDomain D t)).withDensity
        (fun u => ENNReal.ofReal (Real.exp (γ * (ψ (u + t) + C' / γ + h0 t)))) := fun C' => by
    have hφF : ContinuousOn (fun u => ψ (u + t) + C' / γ + h0 t) (Wt ∩ Hbar) := by
      rw [hWtV]; exact (hψt.add continuousOn_const).add continuousOn_const
    exact qAreaMeasureOn_eq_withDensity_of_agree hWto hyt hφF
      (circAgree_zoomFree hWo hWV hy hψ hag C' t (h0 t)) hUo hUH hUW
  rw [hF, hF, qAreaMeasureOn_eq_withDensity_of_agree hWto hyt hφY hY.circAgree hUo hUH hUW]
  have hS : MeasurableSet (ball (0 : ℂ) s ∩ H) :=
    measurableSet_ball.inter (isOpen_lt continuous_const Complex.continuous_im).measurableSet
  rw [withDensity_apply _ hS, withDensity_apply _ hS, withDensity_apply _ hS]
  have hsub : ∀ u ∈ ball (0 : ℂ) s ∩ H, |h0 (u + t) - h0 t| ≤ 1 := fun u hu =>
    hclose u ⟨ball_subset_ball hsρ hu.1, hu.2⟩
  have hγ' : γ * (C / γ) = C := by field_simp
  have hγm : γ * ((C - γ) / γ) = C - γ := by field_simp
  have hγp : γ * ((C + γ) / γ) = C + γ := by field_simp
  constructor
  · refine setLIntegral_mono' hS fun u hu => ENNReal.ofReal_le_ofReal
      (Real.exp_le_exp.2 ?_)
    have h1 := (abs_le.1 (hsub u hu)).1
    have e1 : γ * (ψ (u + t) + (C - γ) / γ + h0 t) =
        γ * ψ (u + t) + (C - γ) + γ * h0 t := by rw [mul_add, mul_add, hγm]
    have e2 : γ * (ψ (u + t) + h0 (u + t) + C / γ) =
        γ * ψ (u + t) + γ * h0 (u + t) + C := by rw [mul_add, mul_add, hγ']
    rw [e1, e2]
    nlinarith
  · refine setLIntegral_mono' hS fun u hu => ENNReal.ofReal_le_ofReal
      (Real.exp_le_exp.2 ?_)
    have h1 := (abs_le.1 (hsub u hu)).2
    have e1 : γ * (ψ (u + t) + (C + γ) / γ + h0 t) =
        γ * ψ (u + t) + (C + γ) + γ * h0 t := by rw [mul_add, mul_add, hγp]
    have e2 : γ * (ψ (u + t) + h0 (u + t) + C / γ) =
        γ * ψ (u + t) + γ * h0 (u + t) + C := by rw [mul_add, mul_add, hγ']
    rw [e1, e2]
    nlinarith

/-- **The straight canonical scale tends to `0` in probability** (`Prop16ScaleStmt`). -/
theorem prop16ScaleStmt_holds : Prop16ScaleStmt := by
  intro γ D c d a b h0 Ω _ P X hdat δ hδ
  have hloc := prop16LocGoodStmt_of_coupling prop16MixedFreeLocCoupling_mm
  have hν := prop16NuMeasStmt_of_loc hloc γ D c d a b h0 P X hdat
  have hnice := prop16LocNiceStmt_of_coupling prop16MixedFreeLocCoupling_mm γ D c d a b h0 P X
    hdat
  have hsc0 := prop16_hsc0 hdat hν hnice
  have hlg : ∀ᵐ ω ∂P, IsLocallyGoodOn γ (D ∪ realSet (Ioo a b)) (X ω) :=
    hnice.mono fun _ h => h.isLocallyGoodOn
  have hdat' := hdat
  obtain ⟨hγ, -, ⟨hDo, -, -, hDH, -, -, hhd⟩, -, hca, hbd, hh0, -, hX, hpos, hfin⟩ := hdat'
  haveI : IsProbabilityMeasure (prop16Q γ h0 a b P X) :=
    isProbabilityMeasure_prop16Law hν hpos hfin
  set Q := prop16Q γ h0 a b P X with hQ
  set A : ℝ → Ω × ℝ → ℝ := fun C p =>
    scaleParamOn γ (zoomField γ C (ofFun h0 + X p.1) p.2) (zoomDomain D p.2) with hA
  set A' : ℝ → Ω × ℝ → ℝ := fun C p =>
    scaleParamOn γ (zoomFree γ C h0 X p) (zoomDomain D p.2) with hA'
  have hAm : ∀ C, AEMeasurable (A C) Q := fun C =>
    Prop16Area.Meas.aemeasurable_scaleParam_prop16 γ C h0 hDo hDH hX.measurable_coord
      (Prop16Area.Meas.nullMeasurableSet_of_ae
        (prop16ZoomAreaStmt_of_loc hloc γ D c d a b h0 P X hdat C))
  have hsand : ∀ᵐ p ∂Q, ∃ ρ > 0, ∀ C s : ℝ, 0 < s → s ≤ ρ →
      qAreaMeasureOn γ (zoomFree γ (C - γ) h0 X p) (zoomDomain D p.2) (ball 0 s ∩ H) ≤
        qAreaMeasureOn γ (zoomField γ C (ofFun h0 + X p.1) p.2) (zoomDomain D p.2)
          (ball 0 s ∩ H) ∧
      qAreaMeasureOn γ (zoomField γ C (ofFun h0 + X p.1) p.2) (zoomDomain D p.2)
          (ball 0 s ∩ H) ≤
        qAreaMeasureOn γ (zoomFree γ (C + γ) h0 X p) (zoomDomain D p.2) (ball 0 s ∩ H) :=
    ae_prop16Law_of_ae (G := fun ω t => ∃ ρ > 0, ∀ C s : ℝ, 0 < s → s ≤ ρ →
        qAreaMeasureOn γ (addConst (zoomField γ (C - γ) (X ω) t) (h0 t)) (zoomDomain D t)
            (ball 0 s ∩ H) ≤
          qAreaMeasureOn γ (zoomField γ C (ofFun h0 + X ω) t) (zoomDomain D t) (ball 0 s ∩ H) ∧
        qAreaMeasureOn γ (zoomField γ C (ofFun h0 + X ω) t) (zoomDomain D t) (ball 0 s ∩ H) ≤
          qAreaMeasureOn γ (addConst (zoomField γ (C + γ) (X ω) t) (h0 t)) (zoomDomain D t)
            (ball 0 s ∩ H))
      (aemeasurable_prop16Kernel' hν hfin) (fun ω => sFinite_prop16Nu γ h0 a b (X ω))
      (fun ω => prop16Nu_compl_Ioo γ h0 a b (X ω))
      (hlg.mono fun ω hω t ht => sandwich_point hγ hDo hDH hhd hca hbd hh0 hω ht)
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  set gp : ℕ → Ω × ℝ → ℝ := fun n p =>
    if 0 < A' (ns n + γ) p then A' (ns n + γ) p else 1 with hgp
  set gm : ℕ → Ω × ℝ → ℝ := fun n p =>
    if 0 < A' (ns n - γ) p then A' (ns n - γ) p else 1 with hgm
  set g : ℕ → Ω × ℝ → ℝ := fun n p => max (gp n p) (gm n p) with hg
  have hnsp : Tendsto (fun n => ns n + γ) atTop atTop := tendsto_atTop_add_const_right _ _ hns
  have hnsm : Tendsto (fun n => ns n - γ) atTop atTop := tendsto_atTop_add_const_right _ _ hns
  have hgmeas : TendstoInMeasure Q g atTop (fun _ => (0 : ℝ)) := by
    rw [tendstoInMeasure_iff_dist]
    intro ε hε
    have h1 := (hsc0 _ (lt_min hε one_pos)).comp hnsp
    have h2 := (hsc0 _ (lt_min hε one_pos)).comp hnsm
    have h3 := h1.add h2
    rw [add_zero] at h3
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h3 (fun _ => bot_le)
      fun n => (measure_mono fun p hp => ?_).trans (measure_union_le _ _)
    simp only [mem_ofPred_eq, Function.comp_apply] at hp ⊢
    by_contra hcon
    simp only [mem_union, mem_ofPred_eq, not_or, not_not] at hcon
    obtain ⟨⟨hp1, hp2⟩, ⟨hm1, hm2⟩⟩ := hcon
    have e1 : gp n p = A' (ns n + γ) p := by simp only [hgp]; rw [if_pos hp1]
    have e2 : gm n p = A' (ns n - γ) p := by simp only [hgm]; rw [if_pos hm1]
    rw [Real.dist_eq, sub_zero] at hp
    have : g n p < ε := by
      simp only [hg, e1, e2]
      exact max_lt (hp2.trans_le (min_le_left _ _)) (hm2.trans_le (min_le_left _ _))
    have : 0 ≤ g n p := by simp only [hg, e1, e2]; exact le_max_of_le_left hp1.le
    rw [abs_of_nonneg this] at hp
    linarith
  obtain ⟨ms, hms, hmsae⟩ := hgmeas.exists_seq_tendsto_ae
  refine ⟨ms, ?_⟩
  set E : ℕ → Set (Ω × ℝ) := fun k => {p | ¬ (0 < A (ns (ms k)) p ∧ A (ns (ms k)) p < δ)}
    with hE
  have hEm : ∀ k, NullMeasurableSet (E k) Q := fun k =>
    ((nullMeasurableSet_lt aemeasurable_const (hAm _)).inter
      (nullMeasurableSet_lt (hAm _) aemeasurable_const)).compl
  have hlim := tendsto_lintegral_filter_of_dominated_convergence' (μ := Q) (l := atTop)
    (F := fun k => (E k).indicator (1 : Ω × ℝ → ℝ≥0∞)) (f := fun _ => 0) (fun _ => 1)
    (Eventually.of_forall fun k => aemeasurable_const.indicator₀ (hEm k))
    (Eventually.of_forall fun k => ae_of_all _ fun p => Set.indicator_le (fun _ _ => le_rfl) p)
    (by simp) ?_
  · have h' : Tendsto (fun k => Q (E k)) atTop (𝓝 0) := by
      simpa [lintegral_indicator₀ (hEm _)] using hlim
    exact h'
  filter_upwards [hmsae, hsand] with p hp hps
  obtain ⟨ρ, hρ, hρs⟩ := hps
  set δ' := min (δ / 2) ρ with hδ'
  have hδ'0 : 0 < δ' := lt_min (half_pos hδ) hρ
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [hp.eventually (gt_mem_nhds (lt_min hδ'0 one_pos))] with k hk
  have hk1 : g (ms k) p < 1 := hk.trans_le (min_le_right _ _)
  have hkδ : g (ms k) p < δ' := hk.trans_le (min_le_left _ _)
  have hp1 : 0 < A' (ns (ms k) + γ) p := by
    by_contra hneg
    have : gp (ms k) p = 1 := by simp only [hgp]; rw [if_neg hneg]
    have := le_max_left (gp (ms k) p) (gm (ms k) p)
    simp only [hg] at hk1
    linarith
  have hm1 : 0 < A' (ns (ms k) - γ) p := by
    by_contra hneg
    have : gm (ms k) p = 1 := by simp only [hgm]; rw [if_neg hneg]
    have := le_max_right (gp (ms k) p) (gm (ms k) p)
    simp only [hg] at hk1
    linarith
  have hm2 : A' (ns (ms k) - γ) p < δ' := by
    have e2 : gm (ms k) p = A' (ns (ms k) - γ) p := by simp only [hgm]; rw [if_pos hm1]
    have := le_max_right (gp (ms k) p) (gm (ms k) p)
    simp only [hg] at hkδ
    linarith
  obtain ⟨h1, h2⟩ := scale_sandwich (ρ := ρ)
    (fun s hs hsρ => (hρs (ns (ms k)) s hs hsρ).1) (fun s hs hsρ => (hρs (ns (ms k)) s hs hsρ).2)
    hp1 hm1 hm2 (min_le_right _ _)
  have hnot : p ∉ E k := by
    simp only [hE, mem_ofPred_eq, not_not]
    refine ⟨h1, lt_of_le_of_lt h2 ?_⟩
    have := min_le_left (δ / 2) ρ
    linarith
  simp [indicator_of_notMem hnot]

end Prop16Lit

end QuantumZipper
