import QuantumZipper.Proofs.Section5.Prop16LitScale

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Proposition 1.6, literal form: the covariance node level by level (COORD-CHANGE, D98)

`Prop16Lit.theorem1_6_literal_of_nodes` uses `Prop16LitCovStmt` one level `C` at a time
(`∀ C, ∀ᵐ p` in the pointwise closeness step). `Prop16LitCovEachStmt` is the same identity with
the quantifiers in that order, a genuinely weaker node (`prop16LitCovEachStmt_of_cov`). It removes
the uncountable intersection over the level from the measurability node of the Palm transfer
(`Prop16LitRepMeasAtStmt` in place of `Prop16LitRepMeasStmt`). The proof is the one of
`theorem1_6_literal_of_nodes`, verbatim.
-/

noncomputable section

open Filter Set Metric MeasureTheory ProbabilityTheory
open scoped Topology ENNReal

namespace QuantumZipper

namespace Prop16Lit

open LitChart Prop16Asm Prop16Area.G

/-- **Node (DS11 Prop. 2.1 at quantum-typical points), level by level.** -/
def Prop16LitCovEachStmt : Prop :=
  ∀ (γ : ℝ) (D : Set ℂ) (c d a b : ℝ) (h0 : ℂ → ℝ) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → FieldSample), Prop16Data γ D c d a b h0 P X →
    ∀ (ψ : ℝ → ℂ → ℂ) (r₀ : ℝ → ℝ), LitFamily D a b ψ r₀ → ∀ C : ℝ,
    ∀ᵐ p ∂(prop16Q γ h0 a b P X),
      (qAreaMeasureOn γ (zoomFieldLit γ C (ofFun h0 + X p.1) p.2 (ψ p.2))
          (ball 0 (r₀ p.2) ∩ H)).map (ψ p.2) =
        (qAreaMeasureOn γ (zoomField γ C (ofFun h0 + X p.1) p.2) (zoomDomain D p.2)).restrict
          (ψ p.2 '' (ball 0 (r₀ p.2) ∩ H)) ∧
      (0 < scaleParamOn γ (zoomFieldLit γ C (ofFun h0 + X p.1) p.2 (ψ p.2))
          (ball 0 (r₀ p.2) ∩ H) →
        qAreaMeasureOn γ (canonicalOn γ (zoomFieldLit γ C (ofFun h0 + X p.1) p.2 (ψ p.2))
            (ball 0 (r₀ p.2) ∩ H))
          (canonicalDomainOn γ (zoomFieldLit γ C (ofFun h0 + X p.1) p.2 (ψ p.2))
            (ball 0 (r₀ p.2) ∩ H)) =
        (qAreaMeasureOn γ (zoomFieldLit γ C (ofFun h0 + X p.1) p.2 (ψ p.2))
            (ball 0 (r₀ p.2) ∩ H)).map fun z => z /
          (scaleParamOn γ (zoomFieldLit γ C (ofFun h0 + X p.1) p.2 (ψ p.2))
            (ball 0 (r₀ p.2) ∩ H) : ℂ))

/-- **Proposition 1.6, literal form, from the covariance, measurability, scale and finiteness
nodes.** -/
theorem theorem1_6_literal_of_nodes_each (hCov : Prop16LitCovEachStmt) (hMeas : Prop16LitMeasStmt)
    (hScale : Prop16ScaleStmt) (hFin : Prop16LitFinStmt) : theorem1_6_literal := by
  intro γ hγ hγ2 D c d a b hDo hDc hDb hDH hcd hfr hhd hab hca hbd h0 hh0 Ω _ P hP X hX hpos
    hfin ψ r₀ hψm hr₀m hch
  have hdat : Prop16Data γ D c d a b h0 P X :=
    ⟨hγ, hγ2, ⟨hDo, hDc, hDb, hDH, hcd, hfr, hhd⟩, hab, hca, hbd, hh0, hP, hX, hpos, hfin⟩
  have hfam : LitFamily D a b ψ r₀ := ⟨hψm, hr₀m, hch⟩
  obtain ⟨Ω', _, P', W, hP', hW, hconv⟩ := theorem1_6_proved γ hγ hγ2 D c d a b hDo hDc hDb
    hDH hcd hfr hhd hab hca hbd h0 hh0 P X hX hpos hfin
  refine ⟨Ω', _, P', W, hP', hW, ?_⟩
  intro m f hfc hfs F hFc hFb
  have hloc := prop16LocGoodStmt_of_coupling prop16MixedFreeLocCoupling_mm
  have hν := prop16NuMeasStmt_of_loc hloc γ D c d a b h0 P X hdat
  haveI hQ : IsProbabilityMeasure (prop16Q γ h0 a b P X) :=
    isProbabilityMeasure_prop16Law hν hpos hfin
  set Q := prop16Q γ h0 a b P X with hQdef
  have hZo : IsOpen (zoomDomain D 0) := hDo.preimage (continuous_id.add continuous_const)
  -- the three random vectors
  set Xv : ℝ → Ω × ℝ → (Fin m → ℝ) := fun C p j =>
    canPair γ (zoomField γ C (ofFun h0 + X p.1) p.2) (zoomDomain D p.2) (f j) with hXv
  set Yv : ℝ → Ω × ℝ → (Fin m → ℝ) := fun C p j =>
    canPair γ (zoomFieldLit γ C (ofFun h0 + X p.1) p.2 (ψ p.2)) (ball 0 (r₀ p.2) ∩ H) (f j)
    with hYv
  set Zv : Ω' → (Fin m → ℝ) := fun ω j => ∫ z, f j z ∂qAreaMeasure γ (W ω) with hZv
  -- measurability
  have hpair : ∀ (C : ℝ) (g : ℂ → ℝ), Continuous g → HasCompactSupport g →
      AEMeasurable (fun p => canPair γ (zoomField γ C (ofFun h0 + X p.1) p.2)
        (zoomDomain D p.2) g) Q := fun C g hg hgs =>
    Prop16Area.Meas.aemeasurable_integral_prop16Y γ C h0 hDo hDH hX.measurable_coord
      (Prop16Area.Meas.nullMeasurableSet_of_ae (prop16ZoomAreaStmt_of_loc hloc γ D c d a b h0 P X
        hdat C))
      (Prop16Area.Meas.nullMeasurableSet_of_ae (prop16CanonAreaStmt_of_loc hloc γ D c d a b h0 P
        X hdat C)) hg hgs
  have hXm : ∀ C, AEMeasurable (Xv C) Q := fun C =>
    AEMeasurable.of_eval fun j => hpair C (f j) (hfc j) (hfs j)
  have hYm : ∀ C, AEMeasurable (Yv C) Q := fun C =>
    AEMeasurable.of_eval fun j =>
      hMeas γ D c d a b h0 P X hdat ψ r₀ hfam C (f j) (hfc j) (hfs j)
  have hZm : AEMeasurable Zv P' :=
    AEMeasurable.of_eval fun j => aemeasurable_wedge_pair hγ hγ2 hW (hfc j) (hfs j)
  -- tightness of the straight vector
  have htight := LitSlutsky.tight_of_tendsto Q P' Xv Zv hXm hZm
    (fun G hG hGb => hconv m f hfc hfs G hG hGb)
  -- the common support radius and the bump
  have hRj : ∀ j, ∃ R : ℝ, ∀ u : ℂ, R ≤ ‖u‖ → f j u = 0 := by
    intro j
    obtain ⟨R₀, hR₀⟩ := (isBounded_iff_subset_ball (0 : ℂ)).1 (hfs j).isCompact.isBounded
    refine ⟨R₀, fun u hu => ?_⟩
    by_contra hne
    have := hR₀ (subset_tsupport _ hne)
    rw [mem_ball, dist_zero_right] at this
    linarith
  choose Rj hRj using hRj
  set Rf := max 1 (∑ j, |Rj j|) with hRfdef
  have hRf1 : 1 ≤ Rf := le_max_left _ _
  have hfR : ∀ j (u : ℂ), Rf ≤ ‖u‖ → f j u = 0 := fun j u hu => hRj j u (by
    have h1 : Rj j ≤ |Rj j| := le_abs_self _
    have h2 : |Rj j| ≤ ∑ i, |Rj i| :=
      Finset.single_le_sum (f := fun i => |Rj i|) (fun i _ => abs_nonneg _) (Finset.mem_univ j)
    have h3 := le_max_right 1 (∑ j, |Rj j|)
    linarith)
  set φ : ℂ → ℝ := fun z => min 1 (max 0 (4 * Rf + 1 - ‖z‖)) with hφdef
  have hφc : Continuous φ :=
    continuous_const.min (continuous_const.max (continuous_const.sub continuous_norm))
  have hφ0 : ∀ z, 0 ≤ φ z := fun z => le_min zero_le_one (le_max_left _ _)
  have hφ1 : ∀ z, φ z ≤ 1 := fun z => min_le_left _ _
  have hφin : ∀ z : ℂ, ‖z‖ < 4 * Rf → φ z = 1 := fun z hz =>
    min_eq_left (le_max_of_le_right (by linarith))
  have hφout : ∀ z : ℂ, 4 * Rf + 1 ≤ ‖z‖ → φ z = 0 := fun z hz => by
    simp only [hφdef]; rw [max_eq_left (by linarith), min_eq_right zero_le_one]
  have hφs : HasCompactSupport φ :=
    HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) (4 * Rf + 1)) fun z hz => hφout z (by
      rw [mem_closedBall, dist_zero_right, not_le] at hz; exact hz.le)
  -- the scale, the bump pairing and its tightness
  set A : ℝ → Ω × ℝ → ℝ := fun C p =>
    scaleParamOn γ (zoomField γ C (ofFun h0 + X p.1) p.2) (zoomDomain D p.2) with hAdef
  set Φ : ℝ → Ω × ℝ → ℝ := fun C p =>
    canPair γ (zoomField γ C (ofFun h0 + X p.1) p.2) (zoomDomain D p.2) φ with hΦdef
  have hΦm : ∀ C, AEMeasurable (Φ C) Q := fun C => hpair C φ hφc hφs
  have hΦt : ∀ θ > 0, ∃ M : ℝ, ∀ᶠ C in atTop, Q {p | M < Φ C p} ≤ ENNReal.ofReal θ := by
    intro θ hθ
    obtain ⟨M, hM⟩ := LitSlutsky.tight_of_tendsto (m := 1) Q P' (fun C p _ => Φ C p)
      (fun ω _ => ∫ z, φ z ∂qAreaMeasure γ (W ω))
      (fun C => AEMeasurable.of_eval fun _ => hΦm C)
      (AEMeasurable.of_eval fun _ => aemeasurable_wedge_pair hγ hγ2 hW hφc hφs)
      (fun G hG hGb => hconv 1 (fun _ => φ) (fun _ => hφc) (fun _ => hφs) G hG hGb) θ hθ
    refine ⟨M, hM.mono fun C hC => (measure_mono fun p hp => ?_).trans hC⟩
    have hp' : M < Φ C p := hp
    show M < ‖fun _ : Fin 1 => Φ C p‖
    rw [pi_norm_const, Real.norm_eq_abs]
    exact hp'.trans_le (le_abs_self _)
  -- the pointwise input
  have hlg : ∀ᵐ ω ∂P, IsLocallyGoodOn γ (D ∪ realSet (Ioo a b)) (X ω) :=
    (prop16LocNiceStmt_of_coupling prop16MixedFreeLocCoupling_mm γ D c d a b h0 P X hdat).mono
      fun _ h => h.isLocallyGoodOn
  have hta : ∀ᵐ p ∂Q, p.2 ∈ Ioo a b :=
    ae_prop16Law_of_ae (G := fun _ t => t ∈ Ioo a b) (aemeasurable_prop16Kernel' hν hfin)
      (fun ω => sFinite_prop16Nu γ h0 a b (X ω)) (fun ω => prop16Nu_compl_Ioo γ h0 a b (X ω))
      (ae_of_all _ fun _ _ ht => ht)
  have hZH : ∀ t : ℝ, zoomDomain D t ⊆ H := fun t z hz => by
    have h1 : (0 : ℝ) < (z + (t : ℂ)).im := hDH hz
    show 0 < z.im
    simpa using h1
  have hpt : ∀ ε₀ > 0, ∃ δ : Ω × ℝ → ℝ, (∀ᵐ p ∂Q, 0 < δ p) ∧ ∀ C, ∀ᵐ p ∂Q,
      0 < A C p → A C p < δ p → ‖Yv C p - Xv C p‖ ≤ ε₀ * Φ C p := by
    intro ε₀ hε₀
    classical
    set Good : Ω × ℝ → Prop := fun p => p.2 ∈ Ioo a b ∧ ∃ t > 0, ∀ C : ℝ,
      qAreaMeasureOn γ (zoomField γ C (ofFun h0 + X p.1) p.2) (zoomDomain D p.2)
        (ball 0 t ∩ H) < ⊤ with hGood
    have hcore : ∀ p, ∀ hp : Good p, ∃ δ > 0, ∀ (Y Z : FieldSample) (V U : Set ℂ), IsOpen U →
        U ⊆ H → U ⊆ V → IsLocallyGoodOn γ V Y →
        qAreaMeasureOn γ Y U (ball 0 (Classical.choose hp.2) ∩ H) < ⊤ →
        (qAreaMeasureOn γ Z (ball 0 (r₀ p.2) ∩ H)).map (ψ p.2) =
          (qAreaMeasureOn γ Y U).restrict (ψ p.2 '' (ball 0 (r₀ p.2) ∩ H)) →
        (0 < scaleParamOn γ Z (ball 0 (r₀ p.2) ∩ H) →
          qAreaMeasureOn γ (canonicalOn γ Z (ball 0 (r₀ p.2) ∩ H))
              (canonicalDomainOn γ Z (ball 0 (r₀ p.2) ∩ H)) =
            (qAreaMeasureOn γ Z (ball 0 (r₀ p.2) ∩ H)).map
              fun z => z / (scaleParamOn γ Z (ball 0 (r₀ p.2) ∩ H) : ℂ)) →
        0 < scaleParamOn γ Y U → scaleParamOn γ Y U < δ →
        ‖(fun j => canPair γ Z (ball 0 (r₀ p.2) ∩ H) (f j)) - (fun j => canPair γ Y U (f j))‖ ≤
          ε₀ * canPair γ Y U φ := by
      intro p hp
      have ht := Classical.choose_spec hp.2
      exact core_pointwise hγ (hch p.2 hp.1)
        (hψm.comp (measurable_const.prodMk measurable_id)) (hZH p.2) hfc hfs hRf1 hfR hφc hφ0
        hφ1 hφin hφout ht.1 hε₀
    refine ⟨fun p => if h : Good p then Classical.choose (hcore p h) else 1,
      ae_of_all _ fun p => ?_, fun C => ?_⟩
    · by_cases h : Good p
      · simp only [dif_pos h]; exact (Classical.choose_spec (hcore p h)).1
      · simp only [dif_neg h]; exact one_pos
    · have hcov := hCov γ D c d a b h0 P X hdat ψ r₀ hfam C
      have hl := prop16_hloc hdat hν hlg C
      filter_upwards [hcov, hl, hFin γ D c d a b h0 P X hdat, hta] with p hcp hlp hfp hxp
      intro ha0 haδ
      have hg : Good p := ⟨hxp, hfp⟩
      have haδ' : A C p < Classical.choose (hcore p hg) := by simpa [hg] using haδ
      have hsp := (Classical.choose_spec (hcore p hg)).2
      exact hsp _ _ _ _ (hDo.preimage (continuous_id.add continuous_const)) (hZH p.2) hlp.2.1
        hlp.2.2.2.1 ((Classical.choose_spec hg.2).2 C) hcp.1 hcp.2 ha0 haδ'
  have hclose := LitSlutsky.tendsto_close_of_pointwise Q Xv Yv hXm hYm A Φ hΦm
    (hScale γ D c d a b h0 P X hdat) hΦt hpt
  obtain ⟨B, hB⟩ := hFb
  have key := LitSlutsky.tendsto_integral_sub Q Xv Yv hXm hYm hFc hB htight hclose
  have h2 := hconv m f hfc hfs F hFc ⟨B, hB⟩
  have := key.add h2
  rw [zero_add] at this
  exact this.congr fun C => sub_add_cancel _ _

/-- **Proposition 1.6, literal form, from the level-by-level covariance node and
measurability** (scale and finiteness nodes proved). -/
theorem theorem1_6_literal_of_covEach_meas (hCov : Prop16LitCovEachStmt)
    (hMeas : Prop16LitMeasStmt) : theorem1_6_literal :=
  theorem1_6_literal_of_nodes_each hCov hMeas prop16ScaleStmt_holds prop16LitFinStmt_holds

end Prop16Lit

end QuantumZipper
