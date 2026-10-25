import SupercriticalLQGUniqueness.B2.PfeLocal.L5Copy
import SupercriticalLQGUniqueness.B2.PfeLocal.L1Main

 






















set_option autoImplicit false
noncomputable section

open Set MeasureTheory ProbabilityTheory Filter Topology Metric
open scoped ENNReal NNReal
open LQGMetric (CondIndepEv DistC IsWholePlaneGFF TestC heatMollify)
open LQGMetric LQGMetric.DDDF

namespace SupercriticalLQGUniqueness.B2.PfeLocal

open Uniqueness.Toolkit.CompactPathInfimum

 
theorem l5_copy_eq_of_obsLocality {Ω' : Type} [MeasurableSpace Ω'] [StandardBorelSpace Ω']
    [Nonempty Ω'] (P' : Measure Ω') [IsProbabilityMeasure P'] {h' : Ω' → DistC}
    (hh' : IsWholePlaneGFF h' P') {L : Ω' → LSCMetric} (hL : Measurable L)
    (hgeo : ∀ᵐ ω ∂P', L5Geo (L ω)) (K : ℝ≥0) (hK : 1 ≤ K)
    (hbilip : ∀ᵐ p ∂(l4Copy P' h' hh'.measurable), ∀ q q' : ℚ × ℚ × ℚ,
      l5CircDist (L p.2) q q' ≤ K * l5CircDist (L p.1) q q' ∧
        l5CircDist (L p.1) q q' ≤ K * l5CircDist (L p.2) q q')
    (hloc : Inputs.L5ObsLocality P' h' L) :
    ∀ᵐ p ∂(l4Copy P' h' hh'.measurable), L p.1 = L p.2 := by
  have hm := hh'.measurable
  set κ := condDistrib id h' P'
  have hcd : ∀ q q' : ℚ × ℚ × ℚ, Measurable fun ω => l5CircDist (L ω) q q' := fun q q' =>
    (measurable_l5CircDist q q').comp hL
  have hSb : MeasurableSet {p : Ω' × Ω' | ∀ q q' : ℚ × ℚ × ℚ,
      l5CircDist (L p.2) q q' ≤ K * l5CircDist (L p.1) q q' ∧
        l5CircDist (L p.1) q q' ≤ K * l5CircDist (L p.2) q q'} := by
    simp only [setOf_forall]
    refine MeasurableSet.iInter fun q => MeasurableSet.iInter fun q' => ?_
    exact (measurableSet_le ((hcd q q').comp measurable_snd)
      (((hcd q q').comp measurable_fst).const_mul _)).inter
      (measurableSet_le ((hcd q q').comp measurable_fst)
        (((hcd q q').comp measurable_snd).const_mul _))
  have hk1 := l5_kernel_pair_of_copy P' hm hSb hbilip
  have hk2 := l5_kernel_ae P' hm (G := {ω | L5Geo (L ω)}) hgeo
  have hk3 := l5_grid_pi hh' hL hloc
  have hcp : ∀ (R : ℕ) (q q' : ℚ × ℚ × ℚ), Measurable fun ω =>
      compactPathInf (L ω) (closedBall 0 (R : ℝ)) (l5Circ q) (l5Circ q') := fun R q q' =>
    (compactPathInf_measurable (isCompact_closedBall _ _) (isCompact_sphere _ _)
      (isCompact_sphere _ _)).comp hL
  set Seq : Set (Ω' × Ω') := {p | ∀ (R : ℕ) (q q' : ℚ × ℚ × ℚ),
    compactPathInf (L p.1) (closedBall 0 (R : ℝ)) (l5Circ q) (l5Circ q') =
      compactPathInf (L p.2) (closedBall 0 (R : ℝ)) (l5Circ q) (l5Circ q')}
  have hSeq : MeasurableSet Seq := by
    simp only [Seq, setOf_forall]
    refine MeasurableSet.iInter fun R => MeasurableSet.iInter fun q =>
      MeasurableSet.iInter fun q' => ?_
    exact isClosed_diagonal.measurableSet.preimage
      (((hcp R q q').comp measurable_fst).prodMk ((hcp R q q').comp measurable_snd))
  have hk4 : ∀ᵐ g ∂P'.map h', ∀ᵐ ω ∂κ g, ∀ᵐ ω₂ ∂κ g, (ω, ω₂) ∈ Seq := by
    filter_upwards [hk1, hk2, hk3] with g hg1 hg2 hg3
    have hgeo_g : ∀ᵐ ω ∂κ g, L5Geo (L ω) := hg2.mono fun ω hω => hω.2
    have hpair_g : ∀ᵐ ω₂ ∂κ g, ∀ᵐ ω₁ ∂κ g, ∀ q q' : ℚ × ℚ × ℚ,
        l5CircDist (L ω₂) q q' ≤ K * l5CircDist (L ω₁) q q' :=
      hg1.mono fun ω hω => hω.mono fun ω₂ h2 q q' => (h2 q q').2
    obtain ⟨G₀, hG₀, hcmp⟩ := l5_good_set (κ g) L K hK hgeo_g hpair_g
    have hconst : ∀ (R : ℕ) (q q' : ℚ × ℚ × ℚ), ∃ c : ℝ≥0∞, ∀ᵐ ω ∂κ g,
        compactPathInf (L ω) (closedBall 0 (R : ℝ)) (l5Circ q) (l5Circ q') = c :=
      fun R q q' => l5_var_zero (κ g) L hL K hK G₀ hG₀
        (fun ω₁ h₁ ω₂ h₂ => (hcmp ω₁ h₁ ω₂ h₂).2) (R : ℝ) (isCompact_sphere _ _)
        (isCompact_sphere _ _) (hg3 R)
    choose c hc using hconst
    have hall : ∀ᵐ ω ∂κ g, ∀ (R : ℕ) (q q' : ℚ × ℚ × ℚ),
        compactPathInf (L ω) (closedBall 0 (R : ℝ)) (l5Circ q) (l5Circ q') = c R q q' :=
      ae_all_iff.2 fun R => ae_all_iff.2 fun q => ae_all_iff.2 fun q' => hc R q q'
    filter_upwards [hall] with ω hω
    filter_upwards [hall] with ω₂ hω₂
    intro R q q'
    rw [hω R q q', hω₂ R q q']
  have hcopyEq := l5_copy_of_kernel_pair P' hm hSeq hk4
  filter_upwards [hcopyEq, l4Copy_ae_fst P' h' hm hgeo, l4Copy_ae_snd P' h' hm hgeo] with
    p hp hg1 hg2
  refine l5_eq_of_circDist _ _ hg1 hg2 fun q q' => ?_
  rw [l5_circDist_eq_iInf _ hg1, l5_circDist_eq_iInf _ hg2]
  congr 1
  funext R
  exact hp R q q'

 
theorem l5_bilip_codes {Ω' : Type} [MeasurableSpace Ω'] [StandardBorelSpace Ω'] [Nonempty Ω']
    {P' : Measure Ω'} [IsProbabilityMeasure P'] {h' : Ω' → DistC} {hh' : Measurable h'}
    {L : Ω' → LSCMetric} (K : ℝ≥0) (hK : 1 ≤ K)
    (hcopy : ∀ᵐ p ∂(l4Copy P' h' hh'), ∀ O O' : Set ℂ, Iface.IsRationalCircle O →
      Iface.IsRationalCircle O' →
      Iface.setDistance (L p.2).1 O O' ≤ K * Iface.setDistance (L p.1).1 O O' ∧
        Iface.setDistance (L p.1).1 O O' ≤ K * Iface.setDistance (L p.2).1 O O') :
    ∀ᵐ p ∂(l4Copy P' h' hh'), ∀ q q' : ℚ × ℚ × ℚ,
      l5CircDist (L p.2) q q' ≤ K * l5CircDist (L p.1) q q' ∧
        l5CircDist (L p.1) q q' ≤ K * l5CircDist (L p.2) q q' := by
  have hK0 : (K : ℝ≥0∞) ≠ 0 := by
    have : (0 : ℝ≥0) < K := lt_of_lt_of_le one_pos hK
    exact_mod_cast this.ne'
  have htop : ∀ D : LSCMetric, ∀ q q' : ℚ × ℚ × ℚ, (q.2.2 < 0 ∨ q'.2.2 < 0) →
      l5CircDist D q q' = ∞ := by
    intro D q q' hneg
    rcases hneg with h | h
    · have : l5Circ q = ∅ := by
        rw [l5Circ]; exact sphere_eq_empty_of_neg (by exact_mod_cast h)
      simp [l5CircDist, Iface.setDistance, this]
    · have : l5Circ q' = ∅ := by
        rw [l5Circ]; exact sphere_eq_empty_of_neg (by exact_mod_cast h)
      simp [l5CircDist, Iface.setDistance, this]
  filter_upwards [hcopy] with p hp q q'
  by_cases hq : 0 ≤ q.2.2
  · by_cases hq' : 0 ≤ q'.2.2
    · exact hp _ _ (l5Circ_isRationalCircle q hq) (l5Circ_isRationalCircle q' hq')
    · rw [htop (L p.1) q q' (Or.inr (not_le.1 hq')), htop (L p.2) q q' (Or.inr (not_le.1 hq')),
        ENNReal.mul_top hK0]
      exact ⟨le_rfl, le_rfl⟩
  · rw [htop (L p.1) q q' (Or.inl (not_le.1 hq)), htop (L p.2) q q' (Or.inl (not_le.1 hq)),
      ENNReal.mul_top hK0]
    exact ⟨le_rfl, le_rfl⟩

 


theorem l5_axiomII_of_obsLocality (hS4 : Iface.DG20Section4) (hPerc : Iface.DG20PercEstimate')
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)) (hm : ∀ ε, IsLFPPNormalizer ξ ε (m ε))
    (V : Set.Ioi (0 : ℝ) → DistC → C(ℂ, ℝ)) (hVm : ∀ δ, Measurable (V δ))
    (hV : ∀ δ : Set.Ioi (0 : ℝ), ∀ᵐ g ∂normGFFLaw, ∀ z, V δ g z = heatMollify (δ : ℝ) g z)
    (e : ℕ → Set.Ioi (0 : ℝ)) (he : Tendsto (fun n => (e n : ℝ)) atTop (𝓝 0))
    (c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (hc : ∀ r : ℚ, ∀ hr : 0 < r,
      Tendsto (fun n => (r : ℝ) *
        (m ⟨(e n : ℝ) / (r : ℝ), Set.mem_Ioi.mpr (div_pos (e n).2 (Rat.cast_pos.mpr hr))⟩ : ℝ) /
        (m (e n) : ℝ)) atTop (𝓝 (c ⟨(r : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr hr)⟩ : ℝ)))
    {Ω' : Type} [MeasurableSpace Ω'] [StandardBorelSpace Ω'] [Nonempty Ω']
    (P' : Measure Ω') [IsProbabilityMeasure P']
    (h' : Ω' → DistC) (hh' : IsNormalizedWholePlaneGFF h' P')
    (hN : ℕ → Ω' → DistC) (hNm : ∀ n, Measurable (hN n))
    (hNlaw : ∀ n, P'.map (hN n) = normGFFLaw)
    (hpair : ∀ φ : TestC, ∀ᵐ ω ∂P', Tendsto (fun n => hN n ω φ) atTop (𝓝 (h' ω φ)))
    (L : Ω' → LSCMetric) (hL : Measurable L)
    (hconv : ∀ᵐ ω ∂P', Tendsto (fun n =>
      PfeWeyl.normalizedLFPPMetric ξ (m (e n)) (V (e n) (hN n ω))) atTop (𝓝 (L ω)))
    (hgeo : ∀ᵐ ω ∂P', L5Geo (L ω))
    (hloc : Inputs.L5ObsLocality P' h' L) :
    ∃ Φ : DistC → LSCMetric, Measurable Φ ∧ ∀ᵐ ω ∂P', L ω = Φ (h' ω) := by
  have hm' : Measurable h' := hh'.1.measurable
  obtain ⟨C, c₀, hc₀, hcount⟩ := l1_coupled_iteration hS4 hPerc ξ Q hQ m hm V hVm hV e he c hc
    P' h' hh' hN hNm hNlaw hpair L hconv (5 * Real.log 16)
    (by have := Real.log_pos (by norm_num : (1 : ℝ) < 16); positivity) (3 / 4) (by norm_num)
    (by norm_num)
  have hcopy := l4_bilip_copy P' h' hm' L hL (ξ : ℝ) c C c₀ hc₀ hcount hgeo
  have hC1 : (1 : ℝ) < C := C.2
  set K : ℝ≥0 := ⟨(C : ℝ) ^ 2, by positivity⟩
  have hK : 1 ≤ K := by
    show (1 : ℝ) ≤ (C : ℝ) ^ 2
    nlinarith
  have hKe : ENNReal.ofReal ((C : ℝ) ^ 2) = (K : ℝ≥0∞) := by
    rw [ENNReal.ofReal_eq_coe_nnreal (by positivity)]
    rfl
  rw [hKe] at hcopy
  have hbil := l5_bilip_codes K hK hcopy
  exact l5_exists_measurable_of_copy P' hm' hL
    (l5_copy_eq_of_obsLocality P' hh'.1 hL hgeo K hK hbil hloc)

 


theorem l5_hconv_of_obsLocality (hS4 : Iface.DG20Section4) (hPerc : Iface.DG20PercEstimate')
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)) (hm : ∀ ε, IsLFPPNormalizer ξ ε (m ε))
    (V : Set.Ioi (0 : ℝ) → DistC → C(ℂ, ℝ)) (hVm : ∀ δ, Measurable (V δ))
    (hV : ∀ δ : Set.Ioi (0 : ℝ), ∀ᵐ g ∂normGFFLaw, ∀ z, V δ g z = heatMollify (δ : ℝ) g z)
    (e : ℕ → Set.Ioi (0 : ℝ)) (he : Tendsto (fun n => (e n : ℝ)) atTop (𝓝 0))
    (c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (hc : ∀ r : ℚ, ∀ hr : 0 < r,
      Tendsto (fun n => (r : ℝ) *
        (m ⟨(e n : ℝ) / (r : ℝ), Set.mem_Ioi.mpr (div_pos (e n).2 (Rat.cast_pos.mpr hr))⟩ : ℝ) /
        (m (e n) : ℝ)) atTop (𝓝 (c ⟨(r : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr hr)⟩ : ℝ)))
    {Ω' : Type} [MeasurableSpace Ω'] [StandardBorelSpace Ω'] [Nonempty Ω']
    (P' : Measure Ω') [IsProbabilityMeasure P']
    (h' : Ω' → DistC) (hh' : IsNormalizedWholePlaneGFF h' P')
    (hN : ℕ → Ω' → DistC) (hNm : ∀ n, Measurable (hN n))
    (hNlaw : ∀ n, P'.map (hN n) = normGFFLaw)
    (hpair : ∀ φ : TestC, ∀ᵐ ω ∂P', Tendsto (fun n => hN n ω φ) atTop (𝓝 (h' ω φ)))
    (L : Ω' → LSCMetric) (hL : Measurable L)
    (hconv : ∀ᵐ ω ∂P', Tendsto (fun n =>
      PfeWeyl.normalizedLFPPMetric ξ (m (e n)) (V (e n) (hN n ω))) atTop (𝓝 (L ω)))
    (hgeo : ∀ᵐ ω ∂P', L5Geo (L ω))
    (hloc : Inputs.L5ObsLocality P' h' L) :
    ∃ Φ : DistC → LSCMetric, Measurable Φ ∧ (∀ᵐ ω ∂P', L ω = Φ (h' ω)) ∧
      ∀ᵐ ω ∂P', Tendsto (fun n =>
        PfeWeyl.normalizedLFPPMetric ξ (m (e n)) (V (e n) (hN n ω))) atTop (𝓝 (Φ (h' ω))) := by
  obtain ⟨Φ, hΦ, hII⟩ := l5_axiomII_of_obsLocality hS4 hPerc ξ Q hQ m hm V hVm hV e he c hc P' h'
    hh' hN hNm hNlaw hpair L hL hconv hgeo hloc
  refine ⟨Φ, hΦ, hII, ?_⟩
  filter_upwards [hconv, hII] with ω h1 h2
  rw [← h2]
  exact h1

end SupercriticalLQGUniqueness.B2.PfeLocal
