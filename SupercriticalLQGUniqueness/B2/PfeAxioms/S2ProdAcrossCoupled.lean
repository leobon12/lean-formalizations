import SupercriticalLQGUniqueness.B2.PfeAxioms.S2ProdAcross
import SupercriticalLQGUniqueness.B2.PfeAxioms.NormalizedCanonicalModel
import SupercriticalLQGUniqueness.B2.Final.OpenInputs

 

























set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal NNReal
open LQGMetric (DistC normGFFLaw heatMollify)
open SupercriticalLQGUniqueness.B2.Iface

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

 
theorem isHeatSmoothing_canonical_of_heat_ae {V : Ioi (0 : ℝ) → DistC → C(ℂ, ℝ)}
    (hV : ∀ δ : Ioi (0 : ℝ), ∀ᵐ g ∂normGFFLaw, ∀ z, V δ g z = heatMollify (δ : ℝ) g z)
    (e : Ioi (0 : ℝ)) : IsHeatSmoothing normGFFLaw (id : DistC → DistC) e (V e) := by
  have hhCan := normalized_canonical_model.2
  have hh : LQGMetric.IsGFFPlusBddCont (id : DistC → DistC) normGFFLaw :=
    LQGMetric.DFGPS.isGFFPlusBddCont_of_wp hhCan.1
  obtain ⟨X, hXe, hX⟩ := exists_heatVersion_bdd hh e
  intro z
  filter_upwards [hXe, hX z, hV e] with g hg hXg hVg
  dsimp only [id] at hg hXg ⊢
  simpa only [hg z, hVg z] using hXg

 
theorem acrossTailInput_of_dg20CouplingData
    (hS4 : DG20Section4) (hPerc : DG20PercEstimate') (hPos : DG20ExponentPositive)
    {ξ : Ioi (0 : ℝ)} {Q : ℝ} {m : Ioi (0 : ℝ) → Ioi (0 : ℝ)} {e : ℕ → Ioi (0 : ℝ)}
    {c : Ioi (0 : ℝ) → Ioi (0 : ℝ)} {V : Ioi (0 : ℝ) → DistC → C(ℂ, ℝ)}
    {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {h' : Ω' → DistC} {hN : ℕ → Ω' → DistC} {L : Ω' → LSCMetric}
    (hB : Final.DG20CouplingData ξ Q m e c V P' h' hN L) (k : ℕ) :
    PfeWeyl.AcrossTailInput P' L ((k : ℝ) + 1) (Nat.cast_add_one_pos k) := by
  have : IsProbabilityMeasure (normGFFLaw : Measure DistC) := normalized_canonical_model.1
  have hhCan := normalized_canonical_model.2
  have hXcan : ∀ δ, IsHeatSmoothing normGFFLaw (id : DistC → DistC) δ (V δ) :=
    isHeatSmoothing_canonical_of_heat_ae hB.heat_ae
  intro T hT η hη
  by_cases hηtop : η = ⊤
  · exact Eventually.of_forall fun R => hηtop ▸ le_top
  set T' : ℝ := T.toReal + 1 with hT'
  have hT'pos : 0 < T' := by positivity
  have hηr : 0 < η.toReal := ENNReal.toReal_pos hη.ne' hηtop
  obtain ⟨R₀, ε₀, hR₀, hε₀, htail⟩ := B2.DG20Lim.exists_large_circle_lower_tail_any_of_inputs
    hS4 hPerc hPos ξ Q hB.exponent m hB.normalizer (2 * T') η.toReal (by positivity) hηr
  
  set r₀ : ℝ := max R₀ (2 * ((k : ℝ) + 1) + 1) with hr₀
  have hr₀1 : 1 < r₀ := lt_of_lt_of_le hR₀ (le_max_left _ _)
  let r : Ioi (1 : ℝ) := ⟨r₀, hr₀1⟩
  have hrpos : (0 : ℝ) < r₀ := lt_trans one_pos hr₀1
  
  obtain ⟨N₀, hN₀⟩ := (eventually_atTop.1 ((hB.scale_tendsto.eventually (gt_mem_nhds hε₀)).and
    (hB.scale_tendsto.eventually (gt_mem_nhds one_pos))))
  
  have hconv : ∀ᵐ ω ∂P', Tendsto (fun n => PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (m (e (n + N₀)))
      (V (e (n + N₀)) (hN (n + N₀) ω))) atTop (𝓝 (L ω)) := by
    filter_upwards [hB.metric_tendsto] with ω hω
    exact hω.comp (tendsto_add_atTop_nat N₀)
  refine eventually_atTop.2 ⟨⟨2 * r₀ + 1, by
    have : 2 * ((k : ℝ) + 1) < r₀ := lt_of_lt_of_le (by linarith) (le_max_right _ _)
    show 2 * ((k : ℝ) + 1) < 2 * r₀ + 1
    linarith⟩, fun R hR => ?_⟩
  have hR' : 2 * r₀ < (R : ℝ) := by
    have : (2 * r₀ + 1 : ℝ) ≤ R := hR
    linarith
  set Abig := PfeWeyl.outerAnnulus ((k : ℝ) + 1) (Nat.cast_add_one_pos k) R
  set Asm := centeredDoubleAnnulus r₀ hrpos
  
  have hlim : ∀ᵐ ω ∂P', limsup (fun n => acrossDist (PfeWeyl.normalizedLFPPMetric (ξ : ℝ)
      (m (e (n + N₀))) (V (e (n + N₀)) (hN (n + N₀) ω))) Asm) atTop ≤ acrossDist (L ω) Abig := by
    filter_upwards [hconv] with ω hω
    exact limsup_acrossDist_le_of_tendsto hω
      (fun _ => PfeWeyl.isLengthSpace_normalizedLFPPMetric _ _ _)
      (fun _ => finitePathsEuclideanContinuous_normalizedLFPPMetric _ _ _) Abig Asm rfl
      (by
        show 2 * ((k : ℝ) + 1) < r₀
        exact lt_of_lt_of_le (by linarith) (le_max_right _ _))
      (by show 2 * r₀ < (R : ℝ); exact hR')
  
  have hfin : ∀ n, P' {ω | acrossDist (PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (m (e (n + N₀)))
      (V (e (n + N₀)) (hN (n + N₀) ω))) Asm < ENNReal.ofReal (2 * T')} ≤
        ENNReal.ofReal η.toReal := by
    intro n
    obtain ⟨h1, h2⟩ := hN₀ (n + N₀) (Nat.le_add_left _ _)
    set E : Ioi (0 : ℝ) := e (n + N₀)
    set F : DistC → ℝ≥0∞ := fun g =>
      acrossDist (PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (m E) (V E g)) Asm with hF
    have hFm : Measurable F :=
      (SupercriticalLQGUniqueness.measurable_acrossDist Asm).comp
        (measurable_normalizedLFPPMetric_comp (ξ : ℝ) (m E)
          fun z => (continuous_eval_const z).measurable.comp (hB.heat_measurable E))
    have hlaw : P' {ω | F (hN (n + N₀) ω) < ENNReal.ofReal (2 * T')} =
        normGFFLaw {g | F g < ENNReal.ofReal (2 * T')} := by
      rw [← hB.field_law (n + N₀), Measure.map_apply (hB.field_measurable _)
        (measurableSet_lt hFm measurable_const)]
      rfl
    have hT := htail normGFFLaw (id : DistC → DistC) hhCan V hXcan r
      ⟨(E : ℝ), E.property, h2⟩ (le_max_left _ _) h1
    change P' {ω | F (hN (n + N₀) ω) < ENNReal.ofReal (2 * T')} ≤ _
    rw [hlaw]
    refine le_trans (measure_mono fun g hg => ?_) hT
    exact lt_of_le_of_lt (setDist_le_acrossDist_dilate (ξ : ℝ) _ _ r) hg
  have hfinal := uniform_lower_tail_of_ae_limsup_le P'
    (fun (_ : Unit) n ω => acrossDist (PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (m (e (n + N₀)))
      (V (e (n + N₀)) (hN (n + N₀) ω))) Asm)
    (fun (_ : Unit) ω => acrossDist (L ω) Abig) (2 * T') η.toReal (by positivity)
    (fun _ n => hfin n) (fun _ => hlim) ()
  rw [ENNReal.ofReal_toReal hηtop] at hfinal
  refine le_trans (measure_mono fun ω hω => ?_) hfinal
  have hω' : acrossDist (L ω) Abig ≤ T := hω
  show acrossDist (L ω) Abig < ENNReal.ofReal (2 * T' / 2)
  have h2 : 2 * T' / 2 = T.toReal + 1 := by rw [hT']; ring
  rw [h2]
  calc acrossDist (L ω) Abig ≤ T := hω'
    _ = ENNReal.ofReal T.toReal := (ENNReal.ofReal_toReal hT).symm
    _ < ENNReal.ofReal (T.toReal + 1) :=
        (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (by linarith)

 
theorem coupledAcrossTails_of_dg20CouplingData
    (hS4 : DG20Section4) (hPerc : DG20PercEstimate') (hPos : DG20ExponentPositive)
    {ξ : Ioi (0 : ℝ)} {Q : ℝ} {m : Ioi (0 : ℝ) → Ioi (0 : ℝ)} {e : ℕ → Ioi (0 : ℝ)}
    {c : Ioi (0 : ℝ) → Ioi (0 : ℝ)} {V : Ioi (0 : ℝ) → DistC → C(ℂ, ℝ)}
    {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {h' : Ω' → DistC} {hN : ℕ → Ω' → DistC} {L : Ω' → LSCMetric}
    (hB : Final.DG20CouplingData ξ Q m e c V P' h' hN L) : Final.CoupledAcrossTails P' L :=
  fun k => acrossTailInput_of_dg20CouplingData hS4 hPerc hPos hB k

 
theorem dg20CoupledAcrossTailsInput_proved : Final.DG20CoupledAcrossTailsInput := by
  intro hI ξ Q m e c V Ω' _ _ P' _ h' hN L hB
  obtain ⟨hS4, hPerc, -, -, hPos, -⟩ := hI
  exact coupledAcrossTails_of_dg20CouplingData hS4 hPerc hPos hB

end SupercriticalLQGUniqueness.B2.PfeAxioms
