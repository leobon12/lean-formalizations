import SupercriticalLQGUniqueness.B2.PfeLocal.R68LocCoupled
import SupercriticalLQGUniqueness.B2.PfeAxioms.S2PatchWitness
import SupercriticalLQGUniqueness.B2.PfeAxioms.NormalizedCanonicalModel

 























set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory Metric
open scoped ENNReal
open LQGMetric (DistC normGFFLaw heatMollify)

namespace SupercriticalLQGUniqueness.B2.PfeLocal

open Uniqueness.Toolkit.CompactPathInfimum

 

def R68PatchWeyl (ξ : Set.Ioi (0 : ℝ)) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (ε : ℕ → Set.Ioi (0 : ℝ)) (Φ : DistC → LSCMetric) : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
    IsNormalizedWholePlaneGFF h P →
    ∀ᵐ ω ∂P, ∀ F : C(ℂ, ℝ), LQGMetric.addFun (h ω) F ∈ PfeAxioms.patchLocus ξ m ε ∧
      ∀ p, PfeAxioms.patchWitness ξ m ε (LQGMetric.addFun (h ω) F) p =
        weylScale (ξ : ℝ) F (Φ (h ω)) p

 

theorem r68_ae_frequently_of_tendsto_one {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {s : ℕ → Set Ω} (hs : ∀ n, MeasurableSet (s n))
    (h : Tendsto (fun n => P (s n)) atTop (𝓝 1)) : ∀ᵐ ω ∂P, ∃ᶠ n in atTop, ω ∈ s n := by
  have hc : Tendsto (fun n => P (s n)ᶜ) atTop (𝓝 0) := by
    have : (fun n => P (s n)ᶜ) = fun n => 1 - P (s n) := funext fun n => prob_compl_eq_one_sub (hs n)
    rw [this]
    simpa using ENNReal.Tendsto.sub (tendsto_const_nhds (x := (1 : ℝ≥0∞))) h (Or.inl ENNReal.one_ne_top)
  have hN : ∀ N : ℕ, P (⋂ n ≥ N, (s n)ᶜ) = 0 := by
    intro N
    refine le_antisymm (ge_of_tendsto hc ?_) bot_le
    filter_upwards [eventually_ge_atTop N] with n hn
    exact measure_mono (biInter_subset_of_mem hn)
  have hnull : P (⋃ N : ℕ, ⋂ n ≥ N, (s n)ᶜ) = 0 := measure_iUnion_null hN
  rw [ae_iff]
  refine measure_mono_null (fun ω hω => ?_) hnull
  simp only [mem_ofPred_eq, not_frequently] at hω
  obtain ⟨N, hN'⟩ := eventually_atTop.1 hω
  exact mem_iUnion.2 ⟨N, mem_iInter₂.2 fun n hn => hN' n hn⟩

theorem r68_measurable_addFun (F : C(ℂ, ℝ)) : Measurable fun g : DistC => LQGMetric.addFun g F :=
  LQGMetric.measurable_distOn_iff.2 fun ψ => by
    show Measurable fun g : DistC => (g + LQGMetric.ofCont F) ψ
    exact (LQGMetric.measurable_distOn_apply ψ).add_const _

theorem r68_measurable_Y (ξ : ℝ) (a : Set.Ioi (0 : ℝ)) {V : Set.Ioi (0 : ℝ) → DistC → C(ℂ, ℝ)}
    (hVm : ∀ δ, Measurable (V δ)) (ε : Set.Ioi (0 : ℝ)) (F : C(ℂ, ℝ)) (M : ℝ)
    (hM : ∀ z, |F z| ≤ M) {K : Set ℂ} (hK : IsCompact K) (b₁ b₂ : ℚ × ℚ × ℚ) (η : ℝ) :
    Measurable fun g => r68Y (PfeWeyl.normalizedLFPPMetric ξ a (r68Wt V ε F M hM g)) K b₁ b₂ η := by
  refine (compactPathInf_measurable hK.cthickening (l5Ball_isCompact _).cthickening
    (l5Ball_isCompact _).cthickening).comp ?_
  refine PfeAxioms.measurable_normalizedLFPPMetric_comp ξ a fun z => ?_
  show Measurable fun g => V ε g z + LQGMetric.LFPP.mollCont (ε : ℝ) ε.property.ne' F M hM z
  exact ((continuous_eval_const z).measurable.comp (hVm ε)).add_const _

theorem r68_measurable_Z (ξ : Set.Ioi (0 : ℝ)) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (ε : ℕ → Set.Ioi (0 : ℝ)) (F : C(ℂ, ℝ)) {K : Set ℂ} (hK : IsCompact K)
    (b₁ b₂ : ℚ × ℚ × ℚ) :
    Measurable fun g => r68Z (PfeAxioms.patchWitness ξ m ε (LQGMetric.addFun g F)) K b₁ b₂ :=
  (compactPathInf_measurable hK (l5Ball_isCompact _) (l5Ball_isCompact _)).comp
    ((PfeAxioms.measurable_patchWitness ξ m ε).comp (r68_measurable_addFun F))

 
theorem r68_fixedField_liminf_le {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ}
    {m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)} {e : ℕ → Set.Ioi (0 : ℝ)}
    {c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)} {V : Set.Ioi (0 : ℝ) → DistC → C(ℂ, ℝ)}
    {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {h' : Ω' → DistC} {hN : ℕ → Ω' → DistC} {L : Ω' → LSCMetric}
    (hB : Final.DG20CouplingData ξ Q m e c V P' h' hN L)
    (hSA : Final.CoupledSmallAnnuli ξ m e V P' hN L) (hAT : Final.CoupledAcrossTails P' L)
    {Φ : DistC → LSCMetric} (hII : ∀ᵐ ω ∂P', L ω = Φ (h' ω)) (hpatch : R68PatchWeyl ξ m e Φ)
    (F : C(ℂ, ℝ)) (M : ℝ) (hM : ∀ z, |F z| ≤ M) {K : Set ℂ} (hK : IsCompact K)
    (b₁ b₂ : ℚ × ℚ × ℚ) {η : ℝ} (hη : 0 < η)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P) :
    ∀ᵐ ω ∂P, liminf (fun n => r68Y (PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (m (e n))
      (r68Wt V (e n) F M hM (h ω))) K b₁ b₂ η) atTop ≤
        r68Z (PfeAxioms.patchWitness ξ m e (LQGMetric.addFun (h ω) F)) K b₁ b₂ := by
  set Y : ℕ → DistC → ℝ≥0∞ := fun n g =>
    r68Y (PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (m (e n)) (r68Wt V (e n) F M hM g)) K b₁ b₂ η
    with hYdef
  set Z : DistC → ℝ≥0∞ := fun g =>
    r68Z (PfeAxioms.patchWitness ξ m e (LQGMetric.addFun g F)) K b₁ b₂ with hZdef
  have hYm : ∀ n, Measurable (Y n) := fun n =>
    r68_measurable_Y (ξ : ℝ) _ hB.heat_measurable _ F M hM hK b₁ b₂ η
  have hZm : Measurable Z := r68_measurable_Z ξ m e F hK b₁ b₂
  have hh'm : Measurable h' := hB.limit_field.1.measurable
  have hh'law : P'.map h' = normGFFLaw :=
    (PfeAxioms.normGFFLaw_eq_of_normalized P' h' hB.limit_field).symm
  have hlaw : P.map h = normGFFLaw := (PfeAxioms.normGFFLaw_eq_of_normalized P h hh).symm
  have hpairJ := l6_ae_tendsto_pairJ (DG20Lim.ae_pairing_tendsto_of_ae_tendsto hB.field_tendsto)
  have : IsProbabilityMeasure (normGFFLaw : Measure DistC) := PfeAxioms.normalized_canonical_model.1
  
  have hlimsup : ∀ᵐ ω ∂P', limsup (fun n => Y n (hN n ω)) atTop ≤ Z (h' ω) := by
    filter_upwards [r68_coupled_weyl_limsup hB hSA hAT F M hM, hII,
      hpatch P' h' hB.limit_field] with ω ⟨E, hE, hlim⟩ hIIω hpω
    have hEq : PfeAxioms.patchWitness ξ m e (LQGMetric.addFun (h' ω) F) = E := by
      refine Subtype.ext (funext fun p => ?_)
      show PfeAxioms.patchWitness ξ m e (LQGMetric.addFun (h' ω) F) p = E p
      rw [(hpω F).2 p, hE p, hIIω]
    have := hlim K hK b₁ b₂ η hη
    simp only [hZdef, hEq]
    exact this
  
  set A : ℕ → ℕ → ℕ → Set DistC := fun M' k n =>
    {g | min (Y n g) (M' : ℝ≥0∞) ≤ Z g + ENNReal.ofReal (1 / ((k : ℝ) + 1))} with hAdef
  have hAm : ∀ M' k n, MeasurableSet (A M' k n) := fun M' k n =>
    measurableSet_le ((hYm n).min measurable_const) (hZm.add measurable_const)
  have hcoupled : ∀ M' k : ℕ, Tendsto (fun n => P' (hN n ⁻¹' A M' k n)) atTop (𝓝 1) := by
    intro M' k
    set δ : ℝ := 1 / ((k : ℝ) + 1) with hδ
    have hδ0 : 0 < δ := by positivity
    set T : DistC → ℝ := fun g => (min (Z g) (M' : ℝ≥0∞)).toReal with hT
    have hTm : Measurable T := (hZm.min measurable_const).ennreal_toReal
    have hTprob := l6_prob_comp hh'm hh'law hB.field_measurable hB.field_law hpairJ T hTm
      (δ / 2) (half_pos hδ0)
    
    have hBev : ∀ᵐ ω ∂P', ∀ᶠ n in atTop, ω ∈ {ω | min (Y n (hN n ω)) (M' : ℝ≥0∞) ≤
        min (Z (h' ω)) (M' : ℝ≥0∞) + ENNReal.ofReal (δ / 2)} := by
      filter_upwards [hlimsup] with ω hω
      by_cases hZ : (M' : ℝ≥0∞) ≤ Z (h' ω)
      · exact Eventually.of_forall fun n => by
          show min _ _ ≤ min _ _ + _
          rw [min_eq_right hZ]; exact (min_le_right _ _).trans le_self_add
      · have hZlt : Z (h' ω) < (M' : ℝ≥0∞) := lt_of_not_ge hZ
        have hZt : Z (h' ω) ≠ ∞ := ne_top_of_lt hZlt
        have hlt : limsup (fun n => Y n (hN n ω)) atTop < Z (h' ω) + ENNReal.ofReal (δ / 2) :=
          lt_of_le_of_lt hω (ENNReal.lt_add_right hZt
            (ENNReal.ofReal_pos.2 (half_pos hδ0)).ne')
        filter_upwards [eventually_lt_of_limsup_lt hlt] with n hn
        show min _ _ ≤ min _ _ + _
        rw [min_eq_left hZlt.le]
        exact (min_le_left _ _).trans hn.le
    have hB1 := l6_tendsto_measure_of_ae_eventually hBev
    
    have hC0 : Tendsto (fun n => P' {ω | δ / 2 ≤ |‖T (hN n ω) - T (h' ω)‖|}) atTop (𝓝 0) :=
      hTprob
    
    have hcompl : ∀ n, P' (hN n ⁻¹' A M' k n)ᶜ ≤
        P' {ω | min (Y n (hN n ω)) (M' : ℝ≥0∞) ≤
          min (Z (h' ω)) (M' : ℝ≥0∞) + ENNReal.ofReal (δ / 2)}ᶜ +
        P' {ω | δ / 2 ≤ |‖T (hN n ω) - T (h' ω)‖|} := by
      intro n
      refine (measure_mono fun ω hω => ?_).trans (measure_union_le _ _)
      by_contra hn
      simp only [mem_union, mem_compl_iff, mem_ofPred_eq, not_or, not_le] at hn
      obtain ⟨h1, h2⟩ := hn
      replace h1 := not_lt.1 h1
      apply hω
      show min (Y n (hN n ω)) (M' : ℝ≥0∞) ≤ Z (hN n ω) + ENNReal.ofReal δ
      have hfin : ∀ g, min (Z g) (M' : ℝ≥0∞) = ENNReal.ofReal (T g) := fun g =>
        (ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_right _ _))).symm
      have h2' : T (h' ω) < T (hN n ω) + δ / 2 := by
        rw [Real.norm_eq_abs, abs_abs] at h2
        have := (abs_lt.1 h2).1; linarith
      have hTn : 0 ≤ T (hN n ω) := ENNReal.toReal_nonneg
      calc min (Y n (hN n ω)) (M' : ℝ≥0∞)
          ≤ min (Z (h' ω)) (M' : ℝ≥0∞) + ENNReal.ofReal (δ / 2) := h1
        _ = ENNReal.ofReal (T (h' ω)) + ENNReal.ofReal (δ / 2) := by rw [hfin]
        _ ≤ ENNReal.ofReal (T (hN n ω) + δ / 2) + ENNReal.ofReal (δ / 2) := by
            gcongr
        _ = ENNReal.ofReal (T (hN n ω)) + ENNReal.ofReal δ := by
            rw [ENNReal.ofReal_add hTn (half_pos hδ0).le, add_assoc,
              ← ENNReal.ofReal_add (half_pos hδ0).le (half_pos hδ0).le, add_halves]
        _ = min (Z (hN n ω)) (M' : ℝ≥0∞) + ENNReal.ofReal δ := by rw [hfin]
        _ ≤ Z (hN n ω) + ENNReal.ofReal δ := by gcongr; exact min_le_left _ _
    have hB1c : Tendsto (fun n => P' {ω | min (Y n (hN n ω)) (M' : ℝ≥0∞) ≤
        min (Z (h' ω)) (M' : ℝ≥0∞) + ENNReal.ofReal (δ / 2)}ᶜ) atTop (𝓝 0) := by
      have hmeas : ∀ n, MeasurableSet {ω | min (Y n (hN n ω)) (M' : ℝ≥0∞) ≤
          min (Z (h' ω)) (M' : ℝ≥0∞) + ENNReal.ofReal (δ / 2)} := fun n =>
        measurableSet_le (((hYm n).comp (hB.field_measurable n)).min measurable_const)
          (((hZm.comp hh'm).min measurable_const).add measurable_const)
      have : (fun n => P' {ω | min (Y n (hN n ω)) (M' : ℝ≥0∞) ≤
          min (Z (h' ω)) (M' : ℝ≥0∞) + ENNReal.ofReal (δ / 2)}ᶜ) = fun n =>
          1 - P' {ω | min (Y n (hN n ω)) (M' : ℝ≥0∞) ≤
            min (Z (h' ω)) (M' : ℝ≥0∞) + ENNReal.ofReal (δ / 2)} :=
        funext fun n => prob_compl_eq_one_sub (hmeas n)
      rw [this]
      simpa using ENNReal.Tendsto.sub (tendsto_const_nhds (x := (1 : ℝ≥0∞))) hB1
        (Or.inl ENNReal.one_ne_top)
    have hsum := hB1c.add hC0
    rw [add_zero] at hsum
    have hAc : Tendsto (fun n => P' (hN n ⁻¹' A M' k n)ᶜ) atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun n => zero_le)
        hcompl
    have heq : (fun n => P' (hN n ⁻¹' A M' k n)) = fun n => 1 - P' (hN n ⁻¹' A M' k n)ᶜ :=
      funext fun n => by
        rw [prob_compl_eq_one_sub ((hAm M' k n).preimage (hB.field_measurable n)),
          ENNReal.sub_sub_cancel ENNReal.one_ne_top prob_le_one]
    rw [heq]
    simpa using ENNReal.Tendsto.sub (tendsto_const_nhds (x := (1 : ℝ≥0∞))) hAc
      (Or.inl ENNReal.one_ne_top)
  
  have hfixed : ∀ M' k : ℕ, Tendsto (fun n => P (h ⁻¹' A M' k n)) atTop (𝓝 1) := by
    intro M' k
    refine (hcoupled M' k).congr fun n => ?_
    rw [← Measure.map_apply (hB.field_measurable n) (hAm M' k n), hB.field_law,
      ← hlaw, Measure.map_apply hh.1.measurable (hAm M' k n)]
  have hfreq : ∀ᵐ ω ∂P, ∀ M' k : ℕ, ∃ᶠ n in atTop, h ω ∈ A M' k n :=
    ae_all_iff.2 fun M' => ae_all_iff.2 fun k =>
      r68_ae_frequently_of_tendsto_one (fun n => (hAm M' k n).preimage hh.1.measurable)
        (hfixed M' k)
  filter_upwards [hfreq] with ω hω
  by_cases hZt : Z (h ω) = ∞
  · change _ ≤ Z (h ω); rw [hZt]; exact le_top
  refine ENNReal.le_of_forall_pos_le_add fun θ hθ _ => ?_
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt (NNReal.coe_pos.2 hθ)
  obtain ⟨M', hM'⟩ := exists_nat_gt ((Z (h ω)).toReal + 1)
  have hM'gt : Z (h ω) + ENNReal.ofReal (1 / ((k : ℝ) + 1)) < (M' : ℝ≥0∞) := by
    have h1 : ENNReal.ofReal (1 / ((k : ℝ) + 1)) ≤ 1 := by
      rw [← ENNReal.ofReal_one]; refine ENNReal.ofReal_le_ofReal ?_
      rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    calc Z (h ω) + ENNReal.ofReal (1 / ((k : ℝ) + 1)) ≤ Z (h ω) + 1 := by gcongr
      _ = ENNReal.ofReal ((Z (h ω)).toReal + 1) := by
          rw [ENNReal.ofReal_add ENNReal.toReal_nonneg zero_le_one, ENNReal.ofReal_toReal hZt,
            ENNReal.ofReal_one]
      _ < ENNReal.ofReal (M' : ℝ) := (ENNReal.ofReal_lt_ofReal_iff
          (by linarith [ENNReal.toReal_nonneg (a := Z (h ω))])).2 hM'
      _ = (M' : ℝ≥0∞) := ENNReal.ofReal_natCast M'
  have hfr : ∃ᶠ n in atTop, Y n (h ω) ≤ Z (h ω) + ENNReal.ofReal (1 / ((k : ℝ) + 1)) := by
    refine (hω M' k).mono fun n hn => ?_
    have hn' : min (Y n (h ω)) (M' : ℝ≥0∞) ≤ Z (h ω) + ENNReal.ofReal (1 / ((k : ℝ) + 1)) := hn
    rcases le_total (Y n (h ω)) (M' : ℝ≥0∞) with hle | hle
    · rwa [min_eq_left hle] at hn'
    · rw [min_eq_right hle] at hn'; exact absurd (lt_of_le_of_lt hn' hM'gt) (lt_irrefl _)
  have hli := liminf_le_of_frequently_le' hfr
  refine hli.trans ?_
  gcongr
  rw [ENNReal.ofReal_le_iff_le_toReal ENNReal.coe_ne_top]
  exact hk.le

end SupercriticalLQGUniqueness.B2.PfeLocal
