import QuantumZipper.Proofs.Section5.Prop16D4WInWedge

/-!
# D4⁺ʷ inputs (part 7): clauses `hgrow` and `htight` under the weighted law

`clause_core`: an event of the unperturbed zoomed field which, on the good event (local goodness,
positive scale `< 1`, canonical domain `⊇ B_R ∩ ℍ`), forces `locField (R+1)` of the canonical
field into a measurable set `S`, has probability at most `4ε` eventually in `C`, provided the
wedge gives `S` probability `≤ ε`. `prop16_hgrow` and `prop16_htight` apply it with the squeeze
of `Prop16D4WInGrow.lean`. Own elementary arguments.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal

namespace QuantumZipper

namespace Prop16Asm

open Prop16Area Prop16Area.G TV Factorization

variable {Ω : Type} [MeasurableSpace Ω] {γ : ℝ} {D : Set ℂ} {c d a b : ℝ} {h0 : ℂ → ℝ}
  {P : Measure Ω} {X : Ω → FieldSample} {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'}
  {W : Ω' → FieldSample}

/-- The canonical description of the unperturbed zoomed field. -/
abbrev zCan (γ C : ℝ) (h0 : ℂ → ℝ) (D : Set ℂ) (X : Ω → FieldSample) (p : Ω × ℝ) :
    FieldSample :=
  canonicalOn γ (zoomFree γ C h0 X p) (zoomDomain D p.2)

theorem clause_core (hdat : Prop16Data γ D c d a b h0 P X)
    (hν : AEMeasurable (fun ω => prop16Nu γ h0 a b (X ω)) P)
    (hlg : ∀ᵐ ω ∂P, IsLocallyGoodOn γ (D ∪ realSet (Ioo a b)) (X ω))
    (hZm : ∀ C, AEMeasurable (fun p => coords (zCan γ C h0 D X p)) (prop16Q γ h0 a b P X))
    (hTV : ∀ R : ℕ, Tendsto (fun C => tvDist ((prop16Q γ h0 a b P X).map fun p =>
      locField R (zCan γ C h0 D X p)) (P'.map fun ω => locField R (W ω))) atTop (𝓝 0))
    (hsc0 : ∀ δ > 0, Tendsto (fun C => prop16Q γ h0 a b P X
      {p | ¬ (0 < scaleParamOn γ (zoomFree γ C h0 X p) (zoomDomain D p.2) ∧
        scaleParamOn γ (zoomFree γ C h0 X p) (zoomDomain D p.2) < δ)}) atTop (𝓝 0))
    (R : ℕ) {S : Set (ℕ → ℝ)} (hS : MeasurableSet S) (B : ℝ → Set (Ω × ℝ))
    (himp : ∀ C p, IsLocallyGoodOn γ (zoomNbhd D a b p.2) (zoomFree γ C h0 X p) →
      zoomDomain D p.2 ⊆ zoomNbhd D a b p.2 →
      0 < scaleParamOn γ (zoomFree γ C h0 X p) (zoomDomain D p.2) →
      hball R ⊆ canonicalDomainOn γ (zoomFree γ C h0 X p) (zoomDomain D p.2) →
      p ∈ B C → locField (R + 1) (zCan γ C h0 D X p) ∈ S)
    {ε : ℝ≥0∞} (hε : 0 < ε) (hWS : (P'.map fun ω => locField (R + 1) (W ω)) S ≤ ε) :
    ∀ᶠ C in atTop, prop16Q γ h0 a b P X (B C) ≤ ε + ε + (ε + ε) := by
  have hdat' := hdat
  obtain ⟨-, -, ⟨-, -, -, -, -, -, hhd⟩, -, hca, hbd, -, -, -, hpos, hfin⟩ := hdat'
  set Q := prop16Q γ h0 a b P X
  have : IsProbabilityMeasure Q := isProbabilityMeasure_prop16Law' hν hpos hfin
  have hta : ∀ᵐ p ∂Q, p.2 ∈ Ioo a b :=
    ae_prop16Law_of_ae (G := fun _ t => t ∈ Ioo a b) (aemeasurable_prop16Kernel' hν hfin)
      (fun ω => sFinite_prop16Nu γ h0 a b (X ω)) (fun ω => prop16Nu_compl_Ioo γ h0 a b (X ω))
      (ae_of_all _ fun _ _ ht => ht)
  have hdom := tendsto_prob_hdom Q hca hbd hhd Prod.snd measurable_snd hta
    (fun C p => zoomFree γ C h0 X p) hsc0 R
  filter_upwards [(ENNReal.tendsto_nhds_zero.1 (hsc0 1 one_pos)) ε hε,
    (ENNReal.tendsto_nhds_zero.1 hdom) ε hε,
    (ENNReal.tendsto_nhds_zero.1 (hTV (R + 1))) ε hε] with C h1 h2 h3
  have hb := tv_event_bound (ν := P'.map fun ω => locField (R + 1) (W ω))
    (aemeasurable_locField_of_coords (hZm C) (R + 1)) hS
    (A := {p | ¬ (0 < scaleParamOn γ (zoomFree γ C h0 X p) (zoomDomain D p.2) ∧
        scaleParamOn γ (zoomFree γ C h0 X p) (zoomDomain D p.2) < 1)} ∪
      {p | ¬ hball R ⊆ canonicalDomainOn γ (zoomFree γ C h0 X p) (zoomDomain D p.2)})
    (B := B C) (by
      filter_upwards [prop16_hloc hdat hν hlg C] with p hp hpB
      by_contra hc
      simp only [mem_union, mem_ofPred_eq, not_or, not_not] at hc
      exact hc.2 (himp C p hp.1 hp.2.1 hc.1.1.1 hc.1.2 hpB))
  refine hb.trans (add_le_add ((measure_union_le _ _).trans (add_le_add h1 h2))
    (add_le_add hWS h3))

/-- **Clause `hgrow` of `Prop16D4WInputsStmt`.** -/
theorem prop16_hgrow (hdat : Prop16Data γ D c d a b h0 P X)
    (hν : AEMeasurable (fun ω => prop16Nu γ h0 a b (X ω)) P)
    (hlg : ∀ᵐ ω ∂P, IsLocallyGoodOn γ (D ∪ realSet (Ioo a b)) (X ω))
    [IsProbabilityMeasure P'] (hWm : ∀ N, AEMeasurable (fun ω => locField N (W ω)) P')
    (hWp : ∀ᵐ ω ∂P', IsLQGGood γ (W ω) ∧ ProfileWeak γ (W ω) ∧
      qAreaMeasure γ (W ω) (ball 0 1 ∩ H) = 1)
    (hZm : ∀ C, AEMeasurable (fun p => coords (zCan γ C h0 D X p)) (prop16Q γ h0 a b P X))
    (hTV : ∀ R : ℕ, Tendsto (fun C => tvDist ((prop16Q γ h0 a b P X).map fun p =>
      locField R (zCan γ C h0 D X p)) (P'.map fun ω => locField R (W ω))) atTop (𝓝 0))
    (hsc0 : ∀ δ > 0, Tendsto (fun C => prop16Q γ h0 a b P X
      {p | ¬ (0 < scaleParamOn γ (zoomFree γ C h0 X p) (zoomDomain D p.2) ∧
        scaleParamOn γ (zoomFree γ C h0 X p) (zoomDomain D p.2) < δ)}) atTop (𝓝 0)) :
    ∀ κ > 0, κ < 1 → ∀ θ > 0, ∃ c > 1, ∀ᶠ C in atTop, prop16Q γ h0 a b P X {p | ¬ (
      qAreaMeasureOn γ (zoomFree γ C h0 X p) (zoomDomain D p.2)
          (ball 0 ((1 - κ) * scaleParamOn γ (zoomFree γ C h0 X p) (zoomDomain D p.2)) ∩ H) <
        ENNReal.ofReal c⁻¹ ∧ ENNReal.ofReal c <
      qAreaMeasureOn γ (zoomFree γ C h0 X p) (zoomDomain D p.2)
          (ball 0 ((1 + κ) * scaleParamOn γ (zoomFree γ C h0 X p) (zoomDomain D p.2)) ∩ H))} ≤ θ := by
  intro κ hκ hκ1 θ hθ
  obtain ⟨hγ, -, ⟨hDo, -, -, hDH, -⟩, -⟩ := id hdat
  set cn : ℕ → ℝ := fun n => 1 + 1 / ((n : ℝ) + 1) with hcn
  have hcn1 : ∀ n, 1 < cn n := fun n => by
    have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    simp only [hcn]; linarith
  have hcnt : Tendsto cn atTop (𝓝 1) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_add 1
    simpa [hcn] using this
  have hcanti : Antitone cn := fun m n hmn => by
    simp only [hcn]
    have : 1 / ((n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.succ_le_succ hmn)
    linarith
  set gm := rbump (1 - κ) (1 - κ / 2)
  set gp := rbump (1 + κ / 2) (1 + κ)
  set S : ℕ → Set (ℕ → ℝ) := fun n => {v | ENNReal.ofReal (cn n)⁻¹ ≤ phiN γ 2 gm v} ∪
    {v | phiN γ 2 gp v ≤ ENNReal.ofReal (cn n)} with hS
  have hSm : ∀ n, MeasurableSet (S n) := fun n =>
    (measurableSet_le measurable_const (measurable_phiN γ 2 (continuous_rbump _ _).measurable)).union
      (measurableSet_le (measurable_phiN γ 2 (continuous_rbump _ _).measurable) measurable_const)
  have hSa : Antitone S := fun m n hmn v hv => by
    rcases hv with hv | hv
    · refine Or.inl (le_trans (ENNReal.ofReal_le_ofReal ?_) hv)
      exact inv_anti₀ (by linarith [hcn1 n]) (hcanti hmn)
    · exact Or.inr (hv.trans (ENNReal.ofReal_le_ofReal (hcanti hmn)))
  have hW0 : ∀ᵐ ω ∂P', locField (2 + 1) (W ω) ∉ ⋂ n, S n := by
    filter_upwards [hWp] with ω ⟨hg, hprof, h1⟩ hmem
    obtain ⟨-, hsm⟩ := hprof
    have hlo : qAreaMeasure γ (W ω) (ball 0 (1 - κ / 2) ∩ H) < 1 := by
      rw [← h1]
      exact hsm (show (0 : ℝ) ≤ 1 - κ / 2 by linarith) (show (0 : ℝ) ≤ 1 by norm_num)
        (by linarith)
    have hhi : 1 < qAreaMeasure γ (W ω) (ball 0 (1 + κ / 2) ∩ H) := by
      rw [← h1]
      exact hsm (show (0 : ℝ) ≤ 1 by norm_num) (show (0 : ℝ) ≤ 1 + κ / 2 by linarith)
        (by linarith)
    have hm := (wedge_point hg (R := 2) (show 1 - κ < 1 - κ / 2 by linarith)
      (by norm_num; linarith)).2
    have hp := (wedge_point hg (R := 2) (show 1 + κ / 2 < 1 + κ by linarith)
      (by norm_num; linarith)).1
    have t1 : Tendsto (fun n => ENNReal.ofReal (cn n)⁻¹) atTop (𝓝 1) := by
      have := ENNReal.tendsto_ofReal (hcnt.inv₀ one_ne_zero)
      simpa using this
    have t2 : Tendsto (fun n => ENNReal.ofReal (cn n)) atTop (𝓝 1) := by
      have := ENNReal.tendsto_ofReal hcnt
      simpa using this
    obtain ⟨n, hn1, hn2⟩ := ((t1.eventually (lt_mem_nhds (hm.trans_lt hlo))).and
      (t2.eventually (gt_mem_nhds (hhi.trans_le hp)))).exists
    rcases mem_iInter.1 hmem n with h | h
    · exact absurd h (not_le.2 hn1)
    · exact absurd h (not_le.2 hn2)
  have hlim := map_antitone_tendsto (hWm (2 + 1)) hSm hSa hW0
  obtain ⟨n0, hn0⟩ := ((ENNReal.tendsto_nhds_zero.1 hlim) _ (quarter_pos hθ)).exists
  refine ⟨cn n0, hcn1 n0, ?_⟩
  have hc := clause_core hdat hν hlg hZm hTV hsc0 2 (hSm n0) (B := fun C => {p | ¬ (
      qAreaMeasureOn γ (zoomFree γ C h0 X p) (zoomDomain D p.2)
          (ball 0 ((1 - κ) * scaleParamOn γ (zoomFree γ C h0 X p) (zoomDomain D p.2)) ∩ H) <
        ENNReal.ofReal (cn n0)⁻¹ ∧ ENNReal.ofReal (cn n0) <
      qAreaMeasureOn γ (zoomFree γ C h0 X p) (zoomDomain D p.2)
          (ball 0 ((1 + κ) * scaleParamOn γ (zoomFree γ C h0 X p) (zoomDomain D p.2)) ∩ H))})
    (fun C p hx hUV ha hR hpB => ?_) (quarter_pos hθ) hn0
  · filter_upwards [hc] with C hC
    exact hC.trans (quarter_sum θ).le
  have hUo : IsOpen (zoomDomain D p.2) := hDo.preimage (continuous_id.add continuous_const)
  have hUH : zoomDomain D p.2 ⊆ H := fun z hz => by
    have : 0 < (z + (p.2 : ℂ)).im := hDH hz
    show 0 < z.im
    simpa using this
  have lo := (canon_point hγ hx hUo hUH hUV ha hR (s1 := 1 - κ) (s2 := 1 - κ / 2)
    (by linarith) (by push_cast; linarith)).1
  have hi := (canon_point hγ hx hUo hUH hUV ha hR (s1 := 1 + κ / 2) (s2 := 1 + κ)
    (by linarith) (by push_cast; linarith)).2
  rcases not_and_or.1 hpB with h | h
  · exact Or.inl (le_trans (not_lt.1 h) lo)
  · exact Or.inr (hi.trans (not_lt.1 h))

/-- **Clause `htight` of `Prop16D4WInputsStmt`.** -/
theorem prop16_htight (hdat : Prop16Data γ D c d a b h0 P X)
    (hν : AEMeasurable (fun ω => prop16Nu γ h0 a b (X ω)) P)
    (hlg : ∀ᵐ ω ∂P, IsLocallyGoodOn γ (D ∪ realSet (Ioo a b)) (X ω))
    [IsProbabilityMeasure P'] (hWm : ∀ N, AEMeasurable (fun ω => locField N (W ω)) P')
    (hWp : ∀ᵐ ω ∂P', IsLQGGood γ (W ω) ∧ ProfileWeak γ (W ω))
    (hZm : ∀ C, AEMeasurable (fun p => coords (zCan γ C h0 D X p)) (prop16Q γ h0 a b P X))
    (hTV : ∀ R : ℕ, Tendsto (fun C => tvDist ((prop16Q γ h0 a b P X).map fun p =>
      locField R (zCan γ C h0 D X p)) (P'.map fun ω => locField R (W ω))) atTop (𝓝 0))
    (hsc0 : ∀ δ > 0, Tendsto (fun C => prop16Q γ h0 a b P X
      {p | ¬ (0 < scaleParamOn γ (zoomFree γ C h0 X p) (zoomDomain D p.2) ∧
        scaleParamOn γ (zoomFree γ C h0 X p) (zoomDomain D p.2) < δ)}) atTop (𝓝 0)) :
    ∀ ρ > 0, ∀ θ > 0, ∃ M : ℝ, ∀ᶠ C in atTop, prop16Q γ h0 a b P X
      {p | ¬ qAreaMeasureOn γ (zoomFree γ C h0 X p) (zoomDomain D p.2)
        (ball 0 (ρ * scaleParamOn γ (zoomFree γ C h0 X p) (zoomDomain D p.2))) ≤
          ENNReal.ofReal M} ≤ θ := by
  intro ρ hρ θ hθ
  obtain ⟨hγ, -, ⟨hDo, -, -, hDH, -⟩, -⟩ := id hdat
  obtain ⟨R, hR⟩ := exists_nat_ge (ρ + 1)
  set g := rbump ρ (ρ + 1)
  set S : ℕ → Set (ℕ → ℝ) := fun n => {v | (n : ℝ≥0∞) < phiN γ R g v} with hS
  have hSm : ∀ n, MeasurableSet (S n) := fun n =>
    measurableSet_lt measurable_const (measurable_phiN γ R (continuous_rbump _ _).measurable)
  have hSa : Antitone S := fun m n hmn v (hv : (n : ℝ≥0∞) < phiN γ R g v) =>
    show (m : ℝ≥0∞) < phiN γ R g v from lt_of_le_of_lt (by exact_mod_cast hmn) hv
  have hW0 : ∀ᵐ ω ∂P', locField (R + 1) (W ω) ∉ ⋂ n, S n := by
    filter_upwards [hWp] with ω ⟨hg, hprof⟩ hmem
    have hup := (wedge_point hg (R := R) (show ρ < ρ + 1 by linarith) hR).2
    obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt (hprof.1 (ρ + 1))
    exact absurd (mem_iInter.1 hmem n) (not_lt.2 (hup.trans hn.le))
  have hlim := map_antitone_tendsto (hWm (R + 1)) hSm hSa hW0
  obtain ⟨n0, hn0⟩ := ((ENNReal.tendsto_nhds_zero.1 hlim) _ (quarter_pos hθ)).exists
  refine ⟨n0, ?_⟩
  have hc := clause_core hdat hν hlg hZm hTV hsc0 R (hSm n0) (B := fun C =>
      {p | ¬ qAreaMeasureOn γ (zoomFree γ C h0 X p) (zoomDomain D p.2)
        (ball 0 (ρ * scaleParamOn γ (zoomFree γ C h0 X p) (zoomDomain D p.2))) ≤
          ENNReal.ofReal n0})
    (fun C p hx hUV ha hRc hpB => ?_) (quarter_pos hθ) hn0
  · filter_upwards [hc] with C hC
    exact hC.trans (quarter_sum θ).le
  have hUo : IsOpen (zoomDomain D p.2) := hDo.preimage (continuous_id.add continuous_const)
  have hUH : zoomDomain D p.2 ⊆ H := fun z hz => by
    have : 0 < (z + (p.2 : ℂ)).im := hDH hz
    show 0 < z.im
    simpa using this
  have lo := (canon_point hγ hx hUo hUH hUV ha hRc (s1 := ρ) (s2 := ρ + 1)
    (by linarith) hR).1
  have hH : qAreaMeasureOn γ (zoomFree γ C h0 X p) (zoomDomain D p.2) Hᶜ = 0 :=
    measure_mono_null (compl_subset_compl.2 hUH) (qAreaMeasureOn_compl _ _ _)
  have hbH : qAreaMeasureOn γ (zoomFree γ C h0 X p) (zoomDomain D p.2)
      (ball 0 (ρ * scaleParamOn γ (zoomFree γ C h0 X p) (zoomDomain D p.2))) ≤
      qAreaMeasureOn γ (zoomFree γ C h0 X p) (zoomDomain D p.2)
      (ball 0 (ρ * scaleParamOn γ (zoomFree γ C h0 X p) (zoomDomain D p.2)) ∩ H) := by
    refine measure_mono_ae ?_
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hH] with z hz hzb
    exact ⟨hzb, not_not.1 hz⟩
  show (n0 : ℝ≥0∞) < _
  rw [← ENNReal.ofReal_natCast]
  exact (not_le.1 hpB).trans_le (hbH.trans lo)

end Prop16Asm

end QuantumZipper
