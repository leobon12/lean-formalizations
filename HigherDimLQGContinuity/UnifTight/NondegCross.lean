import HigherDimLQGContinuity.UnifTight.Internal
import HigherDimLQGContinuity.UnifTight.NondegPt
import HigherDimLQGMetric.DGZ.TightNondegCross

/-!
# Uniform DGZ Lemma 6.6 and its extension: crossing distances are not too small (packet U4)

Blueprint Part D, `d:lem-u65`(b) (NA3 §2.7, N-M4; [8]-bp `r2:lem:66`). Ports of
`HigherDimLQGMetric.DGZ.nondeg_cross_pos` and `nondeg_cross_unit` (`DGZ/TightNondegCross.lean`) with every
constant chosen before `ξ ∈ S(b, μ)`.

* **`nondeg_cross_pos_unif`**: there is `q₂ = q₂(d, κ, b, μ) ∈ (0, 1)` such that for `q ∈ [q₂, 1)` and
  `0 < r ≤ 1/(10√d)` there is `c = c(d, κ, b, μ, q, r) > 0` with
  `P[D^ξ_n(across B_{2r}(0) \ B_r(0)) > c a^ξ_n(q)] ≥ c` for every `ξ ∈ S(b, μ)`, every dyadic realization and
  **every** `n` (the blueprint's `n ≥ N` and `p₀` hold with `N = 0`, `p₀ = c`).
* **`nondeg_cross_unit_unif`**: the same for `B₂(0) \ B₁(0)` (the blueprint's "The same holds for `Q₂(0) \ Q₁(0)`").

**Uniformity.** The Hölder exponent of the sealed proof, `ξ(Q - √(2d))/2`, depends on `ξ`; here it is `β₀ := μ/2`
(`< μ`), so Lemma 6.2's `q₂ := q₁(μ/2)` and `M` come from `holder_internal_unif` before `ξ`. The point witness `c'`
is `nondeg_pt_unif`'s (every `ξ ≥ 0`). The radius `ρ` of the small boxes, the covers and the FKG products depend
only on `(c', M, β₀, r, d)`. The neighbourhood events are box distances `D_n(B_ρ(g), B_ρ(g'); B_{3r}(0))` inside a
domain containing all crossing paths (NA3 N-M4, `DGZ.lfppSetDist_lsph_le_acrossDist`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric HigherDimLQGMetric.DGZ
open HigherDimLFPP HigherDimLFPP.Perc
open HigherDimLFPP.DGZ (latPt cbox obox)

variable {d : ℕ}

/-- **Uniform DGZ Lemma 6.6** (Part D `d:lem-u65`(b); port of `DGZ.nondeg_cross_pos`): there is `q₂ ∈ (0, 1)` such
that for every `q ∈ [q₂, 1)` and `0 < r ≤ 1/(10√d)` there is `c > 0` with
`P[D^ξ_n(across B_{2r}(0) \ B_r(0)) > c a^ξ_n(q)] ≥ c` for every `ξ ∈ S(b, μ)`, every dyadic realization and every
`n`. -/
theorem nondeg_cross_pos_unif (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) {b μ : ℝ}
    (hb : 0 < b) (hμ : 0 < μ) :
    ∃ q₂ : ℝ≥0∞, 0 < q₂ ∧ q₂ < 1 ∧ ∀ q : ℝ≥0∞, q₂ ≤ q → q < 1 → ∀ r : ℝ, 0 < r →
      r * (10 * Real.sqrt d) ≤ 1 → ∃ c : ℝ, 0 < c ∧ ∀ ξ : ℝ, UHyp d κ b μ ξ →
        ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ)
          (H : ℕ → Rd d → Ω → ℝ), IsDyadicRealization κ P W H → ∀ n : ℕ,
            ENNReal.ofReal c ≤
              P {ω | c * aQ P H ξ n q < acrossDist ξ (fun z => H n z ω) 0 (2 * r) r} := by
  have hd0 : 0 < d := by omega
  set β₀ : ℝ := μ / 2 with hβ₀
  have hβ₀0 : 0 < β₀ := by positivity
  have hβ₀μ : β₀ < μ := by rw [hβ₀]; linarith
  obtain ⟨q₂, hq₂0, hq₂1, hint⟩ := holder_internal_unif hd hκ hb hμ hβ₀0 hβ₀μ
  refine ⟨q₂, hq₂0, hq₂1, fun q hq₂q hq1 r hr hrd => ?_⟩
  have hq0 : 0 < q := hq₂0.trans_le hq₂q
  -- Lemma 6.5, uniformly in `ξ ≥ 0`
  obtain ⟨c', hc', hpt⟩ := nondeg_pt_unif hd hκ hq0 hq1 hr hrd
  -- the Hölder event on `T = B̄_{5r/2}(0)` inside `U = B_{3r}(0)`
  set U : Set (Rd d) := obox (0 : Rd d) (3 * r) with hU
  set T : Set (Rd d) := cbox (0 : Rd d) (5 * r / 2) with hT
  have hTU : T ⊆ U := cbox_subset_obox (by linarith)
  have hTc : IsPreconnected T := (tn_convex_cbox 0 _).isPreconnected
  obtain ⟨M, hM, hMb⟩ := hint q hq₂q hq1 U T (HigherDimLFPP.DGZ.isOpen_obox 0 _)
    (isCompact_cbox 0 _) hTc hTU (c' / 4) (by positivity)
  -- the radius `ρ` of the small boxes
  set ρ : ℝ := min (r / 2) ((c' / (4 * M)) ^ β₀⁻¹ / (Real.sqrt d + 1)) with hρ
  have hρ0 : 0 < ρ := lt_min (by positivity) (by positivity)
  have hρr : ρ ≤ r / 2 := min_le_left _ _
  have hρM : M * (Real.sqrt d * ρ) ^ β₀ ≤ c' / 4 := by
    have h1 : Real.sqrt d * ρ ≤ (c' / (4 * M)) ^ β₀⁻¹ := by
      have h2 : ρ ≤ (c' / (4 * M)) ^ β₀⁻¹ / (Real.sqrt d + 1) := min_le_right _ _
      have h3 : 0 ≤ (c' / (4 * M)) ^ β₀⁻¹ := by positivity
      rw [le_div_iff₀ (by positivity)] at h2
      nlinarith [Real.sqrt_nonneg (d : ℝ)]
    have h4 : (Real.sqrt d * ρ) ^ β₀ ≤ c' / (4 * M) := by
      calc (Real.sqrt d * ρ) ^ β₀ ≤ ((c' / (4 * M)) ^ β₀⁻¹) ^ β₀ :=
            Real.rpow_le_rpow (by positivity) h1 hβ₀0.le
        _ = c' / (4 * M) := Real.rpow_inv_rpow (by positivity) hβ₀0.ne'
    calc M * (Real.sqrt d * ρ) ^ β₀ ≤ M * (c' / (4 * M)) := mul_le_mul_of_nonneg_left h4 hM.le
      _ = c' / 4 := by field_simp
  -- finite covers of the two spheres
  obtain ⟨X, hXs, hXcov⟩ := tn_exists_obox_cover (tn_isCompact_lsph (0 : Rd d) r) hρ0
  obtain ⟨Y, hYs, hYcov⟩ := tn_exists_obox_cover (tn_isCompact_lsph (0 : Rd d) (2 * r)) hρ0
  have hA : (lsph (0 : Rd d) r).Nonempty := lsph_nonempty hd0 0 hr.le
  have hB : (lsph (0 : Rd d) (2 * r)).Nonempty := lsph_nonempty hd0 0 (by linarith)
  have hXY : (X ×ˢ Y).Nonempty := by
    obtain ⟨a, ha⟩ := hA
    obtain ⟨b', hb'⟩ := hB
    obtain ⟨g, hg, -⟩ := mem_iUnion₂.1 (hXcov ha)
    obtain ⟨g', hg', -⟩ := mem_iUnion₂.1 (hYcov hb')
    exact ⟨(g, g'), Finset.mem_product.2 ⟨hg, hg'⟩⟩
  set N : ℕ := (X ×ˢ Y).card with hN
  set c : ℝ := min (c' / 4) ((c' / 2) ^ N) with hc
  have hc0 : 0 < c := lt_min (by positivity) (by positivity)
  refine ⟨c, hc0, fun ξ hξU Ω _ P W H hH n => ?_⟩
  have hξ : 0 < ξ := hξU.base.xi_pos
  have hW := hH.whiteNoise
  have := hW.isProbabilityMeasure
  have hX := hH.band n
  set a := aQ P H ξ n q with ha
  have ha0 : 0 < a := tight_aQ_pos hd0 hH ξ n hq0 hq1
  set G : Set Ω := {ω | ∃ x ∈ T, ∃ y ∈ T, M * a * ‖x - y‖ ^ β₀ <
    lfppDistOn ξ (fun z => H n z ω) U x y} with hG
  have hPG : P G ≤ ENNReal.ofReal (c' / 4) := hMb ξ hξU Ω P W H hH n
  -- one pair of boxes
  have hpair : ∀ p ∈ X ×ˢ Y, ENNReal.ofReal (c' / 2) ≤
      P {ω | c' * a / 4 < lfppSetDist ξ (fun z => H n z ω) U (obox p.1 ρ) (obox p.2 ρ)} := by
    intro p hp
    obtain ⟨hgX, hgY⟩ := Finset.mem_product.1 hp
    set g := p.1
    set g' := p.2
    have hg := hXs g hgX
    have hg' := hYs g' hgY
    have hgT : g ∈ T := cbox_mono (by linarith) (lsph_subset_cbox 0 r hg)
    have hg'T : g' ∈ T := cbox_mono (by linarith) (lsph_subset_cbox 0 (2 * r) hg')
    have hBT : obox g ρ ⊆ T := (tn_obox_subset_cbox (lsph_subset_cbox 0 r hg)).trans
      (cbox_mono (by linarith))
    have hB'T : obox g' ρ ⊆ T := (tn_obox_subset_cbox (lsph_subset_cbox 0 (2 * r) hg')).trans
      (cbox_mono (by linarith))
    have h1 := hpt ξ hξ.le Ω P W H hH n g hg g' hg'
    have hincl : {ω | c' * a < lfppDistOn ξ (fun z => H n z ω) (obox (0 : Rd d) (3 * r)) g g'} ⊆
        {ω | c' * a / 4 < lfppSetDist ξ (fun z => H n z ω) U (obox g ρ) (obox g' ρ)} ∪ G := by
      intro ω hω
      by_cases hωG : ω ∈ G
      · exact Or.inr hωG
      left
      simp only [hG, mem_ofPred_eq, not_exists, not_and, not_lt] at hωG
      simp only [mem_ofPred_eq] at hω ⊢
      have hφ : Continuous (fun z => H n z ω) := hX.continuous ω
      have hUo : IsOpen U := HigherDimLFPP.DGZ.isOpen_obox 0 _
      have hUc : IsPreconnected U := (HigherDimLFPP.DGZ.convex_obox 0 _).isPreconnected
      have hsmall : ∀ u ∈ obox g ρ, lfppDistOn ξ (fun z => H n z ω) U g u ≤ c' * a / 4 := by
        intro u hu
        calc lfppDistOn ξ (fun z => H n z ω) U g u ≤ M * a * ‖g - u‖ ^ β₀ :=
              hωG g hgT u (hBT hu)
          _ ≤ M * a * (Real.sqrt d * ρ) ^ β₀ := by
              gcongr
              exact tn_norm_sub_le hu
          _ = a * (M * (Real.sqrt d * ρ) ^ β₀) := by ring
          _ ≤ a * (c' / 4) := mul_le_mul_of_nonneg_left hρM ha0.le
          _ = c' * a / 4 := by ring
      have hsmall' : ∀ v ∈ obox g' ρ, lfppDistOn ξ (fun z => H n z ω) U v g' ≤ c' * a / 4 := by
        intro v hv
        calc lfppDistOn ξ (fun z => H n z ω) U v g' ≤ M * a * ‖v - g'‖ ^ β₀ :=
              hωG v (hB'T hv) g' hg'T
          _ ≤ M * a * (Real.sqrt d * ρ) ^ β₀ := by
              gcongr
              rw [norm_sub_rev]
              exact tn_norm_sub_le hv
          _ = a * (M * (Real.sqrt d * ρ) ^ β₀) := by ring
          _ ≤ a * (c' / 4) := mul_le_mul_of_nonneg_left hρM ha0.le
          _ = c' * a / 4 := by ring
      have hlow : c' * a / 2 ≤ lfppSetDist ξ (fun z => H n z ω) U (obox g ρ) (obox g' ρ) := by
        refine le_lfppSetDist ⟨g, tn_mem_obox_self g hρ0⟩ ⟨g', tn_mem_obox_self g' hρ0⟩
          fun u hu v hv => ?_
        have t1 := lfppDistOn_triangle_of_isPreconnected (ξ := ξ) hUo hUc hφ (hTU hgT)
          (hTU (hBT hu)) (hTU hg'T)
        have t2 := lfppDistOn_triangle_of_isPreconnected (ξ := ξ) hUo hUc hφ (hTU (hBT hu))
          (hTU (hB'T hv)) (hTU hg'T)
        have e1 := hsmall u hu
        have e2 := hsmall' v hv
        linarith
      have : c' * a / 4 < c' * a / 2 := by nlinarith
      linarith
    have h2 : ENNReal.ofReal c' ≤
        P {ω | c' * a / 4 < lfppSetDist ξ (fun z => H n z ω) U (obox g ρ) (obox g' ρ)} +
          ENNReal.ofReal (c' / 4) :=
      h1.trans ((measure_mono hincl).trans ((measure_union_le _ _).trans (add_le_add le_rfl hPG)))
    have h3 : ENNReal.ofReal (c' / 2) + ENNReal.ofReal (c' / 4) ≤ ENNReal.ofReal c' := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      exact ENNReal.ofReal_le_ofReal (by linarith)
    exact (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).1 (h3.trans h2)
  -- FKG for the increasing events over all pairs of boxes
  have hfkg := fkg_increasing hκ hW (tb_inv_two_pow_pos n) hX (isCompact_cbox (0 : Rd d) (3 * r))
    (X ×ˢ Y) (F := fun p φ => lfppSetDist ξ φ U (obox p.1 ρ) (obox p.2 ρ))
    (fun p _ => isSupContinuousOn_lfppSetDist (HigherDimLFPP.DGZ.obox_subset_cbox 0 _) ξ _ _)
    (fun p _ => isMonotoneFunctional_lfppSetDist hξ.le _ _ _) (fun _ => c' * a / 4)
  have hprod : ENNReal.ofReal ((c' / 2) ^ N) ≤ ∏ p ∈ X ×ˢ Y,
      P {ω | c' * a / 4 < lfppSetDist ξ (fun z => H n z ω) U (obox p.1 ρ) (obox p.2 ρ)} := by
    rw [ENNReal.ofReal_pow (by positivity), hN, ← Finset.prod_const]
    exact Finset.prod_le_prod hpair
  have hca : c * a ≤ c' * a / 4 := by
    have : c ≤ c' / 4 := min_le_left _ _
    nlinarith
  refine (ENNReal.ofReal_le_ofReal (min_le_right _ _)).trans (hprod.trans (hfkg.trans ?_))
  refine measure_mono fun ω hω => ?_
  simp only [mem_iInter, mem_ofPred_eq] at hω ⊢
  have hφ : Continuous (fun z => H n z ω) := hX.continuous ω
  have hinf : c' * a / 4 < (X ×ˢ Y).inf' hXY
      (fun p => lfppSetDist ξ (fun z => H n z ω) U (obox p.1 ρ) (obox p.2 ρ)) :=
    (Finset.lt_inf'_iff hXY).2 hω
  have h1 := inf'_le_lfppSetDist_of_subset (ξ := ξ) (φ := fun z => H n z ω) (V := U) X Y hXY
    (fun g => obox g ρ) (fun g => obox g ρ) hXcov hYcov hA hB
  have h2 := lfppSetDist_lsph_le_acrossDist (ξ := ξ) hφ (c := (0 : Rd d))
    (by linarith : r < 2 * r) (V := U)
    (fun z hz => cbox_subset_obox (by linarith : 2 * r < 3 * r) hz.1)
  linarith

/-- **Uniform DGZ Lemma 6.6, extended to `B₂(0) \ B₁(0)`** (Part D `d:lem-u65`(b), last sentence; port of
`DGZ.nondeg_cross_unit`): there is `q₂ ∈ (0, 1)` such that for `q ∈ [q₂, 1)` there is `c > 0` with
`P[D^ξ_n(across B₂(0) \ B₁(0)) > c a^ξ_n(q)] ≥ c` for every `ξ ∈ S(b, μ)`, every dyadic realization and every
`n`. -/
theorem nondeg_cross_unit_unif (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) {b μ : ℝ}
    (hb : 0 < b) (hμ : 0 < μ) :
    ∃ q₂ : ℝ≥0∞, 0 < q₂ ∧ q₂ < 1 ∧ ∀ q : ℝ≥0∞, q₂ ≤ q → q < 1 → ∃ c : ℝ, 0 < c ∧
      ∀ ξ : ℝ, UHyp d κ b μ ξ →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ)
        (H : ℕ → Rd d → Ω → ℝ), IsDyadicRealization κ P W H → ∀ n : ℕ,
          ENNReal.ofReal c ≤ P {ω | c * aQ P H ξ n q < acrossDist ξ (fun z => H n z ω) 0 2 1} := by
  have hd0 : 0 < d := by omega
  obtain ⟨q₂, hq₂0, hq₂1, hcross⟩ := nondeg_cross_pos_unif hd hκ hb hμ
  refine ⟨q₂, hq₂0, hq₂1, fun q hq₂q hq1 => ?_⟩
  have hq0 : 0 < q := hq₂0.trans_le hq₂q
  set r : ℝ := 1 / (10 * Real.sqrt d + 4) with hr
  have hr0 : 0 < r := by positivity
  have hrd : r * (10 * Real.sqrt d) ≤ 1 := by
    rw [hr, div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]
    linarith
  have hr4 : r ≤ 1 / 4 := by
    rw [hr]
    exact one_div_le_one_div_of_le (by norm_num) (by linarith [Real.sqrt_nonneg (d : ℝ)])
  obtain ⟨c₀, hc₀, hc₀b⟩ := hcross q hq₂q hq1 r hr0 hrd
  obtain ⟨Z, hZs, hZcov⟩ := tn_exists_obox_cover (tn_isCompact_lsph (0 : Rd d) (3 / 2)) hr0
  have hZne : Z.Nonempty := by
    obtain ⟨p, hp⟩ := lsph_nonempty hd0 (0 : Rd d) (by norm_num : (0 : ℝ) ≤ 3 / 2)
    obtain ⟨g, hg, -⟩ := mem_iUnion₂.1 (hZcov hp)
    exact ⟨g, hg⟩
  set c : ℝ := min c₀ (c₀ ^ Z.card) with hc
  have hc0 : 0 < c := lt_min hc₀ (by positivity)
  refine ⟨c, hc0, fun ξ hξU Ω _ P W H hH n => ?_⟩
  have hξ : 0 < ξ := hξU.base.xi_pos
  have hW := hH.whiteNoise
  have := hW.isProbabilityMeasure
  have hX := hH.band n
  set a := aQ P H ξ n q with ha
  have ha0 : 0 < a := tight_aQ_pos hd0 hH ξ n hq0 hq1
  -- each small shell, through the translated realization
  have hshell : ∀ g ∈ Z, ENNReal.ofReal c₀ ≤
      P {ω | c₀ * a < acrossDist ξ (fun z => H n z ω) g (2 * r) r} := by
    intro g _
    have hH' := isDyadicRealization_translate_tight hκ hH g
    have hb' := hc₀b ξ hξU Ω P _ _ hH' n
    rw [aQ_eq_of_isDyadicRealization hH' hH] at hb'
    have e : ∀ ω, acrossDist ξ (fun z => H n z ω) g (2 * r) r =
        acrossDist ξ (fun z => H n (g + z) ω) 0 (2 * r) r := by
      intro ω
      have := acrossDist_smul_add g ξ (fun z => H n z ω) one_pos 0 (2 * r) r
      simpa only [smul_zero, add_zero, one_mul, one_smul] using this
    simp_rw [e]
    exact hb'
  -- FKG over the finite family of shells
  have hfkg := fkg_increasing hκ hW (tb_inv_two_pow_pos n) hX (isCompact_cbox (0 : Rd d) 2) Z
    (F := fun g φ => acrossDist ξ φ g (2 * r) r)
    (fun g hg => isSupContinuousOn_acrossDist (by linarith : r < 2 * r)
      ((tn_cbox_subset_cbox (lsph_subset_cbox 0 (3 / 2) (hZs g hg))).trans
        (cbox_mono (by linarith))) ξ)
    (fun g _ => isMonotoneFunctional_acrossDist hξ.le g (by linarith : r < 2 * r))
    (fun _ => c₀ * a)
  have hprod : ENNReal.ofReal (c₀ ^ Z.card) ≤ ∏ g ∈ Z,
      P {ω | c₀ * a < acrossDist ξ (fun z => H n z ω) g (2 * r) r} := by
    rw [ENNReal.ofReal_pow hc₀.le, ← Finset.prod_const]
    exact Finset.prod_le_prod hshell
  have hca : c * a ≤ c₀ * a := mul_le_mul_of_nonneg_right (min_le_left _ _) ha0.le
  refine (ENNReal.ofReal_le_ofReal (min_le_right _ _)).trans (hprod.trans (hfkg.trans ?_))
  refine measure_mono fun ω hω => ?_
  simp only [mem_iInter, mem_ofPred_eq] at hω ⊢
  have hinf : c₀ * a < Z.inf' hZne (fun g => acrossDist ξ (fun z => H n z ω) g (2 * r) r) :=
    (Finset.lt_inf'_iff hZne).2 hω
  have h1 := acrossDist_unit_ge_inf' hd0 (ξ := ξ) (hX.continuous ω) hr0 hr4 hZne hZs hZcov
  linarith

end HigherDimLQGContinuity
