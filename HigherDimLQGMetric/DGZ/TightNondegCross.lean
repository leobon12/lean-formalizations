import HigherDimLQGMetric.DGZ.TightInternal
import HigherDimLQGMetric.DGZ.TightNondegPt
import HigherDimLQGMetric.DGZ.FunctionalsBounds

/-!
# DGZ Lemma 6.6 and its extension: crossing distances are not too small (packet L5a)

Source: Ding–Gwynne–Zhuang, arXiv:2310.03996v5 ([2]), Lemma 6.6 (TeX l. 3007–3050, p. 59) and the
extension to `B₂(0) \ B₁(0)` used in the proof of Lemma 6.7 ("easily extend", TeX l. 3091);
planning audit `planning/audits/MA7-ref2-sections-4-6.md`, Details (a) D-6.5–6.7 (G20); blueprint
Part C, Lemma `r2:lem:66`.

* **`nondeg_cross_pos`** (Lemma 6.6): there is `q₂ < 1` such that for `q ∈ [q₂, 1)` and
  `0 < r ≤ 1/(10√d)` there is `c > 0` with `P[D_n(across B_{2r}(0) \ B_r(0)) > c a^{(q)}_n] ≥ c` for
  every dyadic realization and **every** `n` (DGZ: `liminf_n > 0`).
* **`nondeg_cross_unit`** (the extension): the same for `B₂(0) \ B₁(0)`.

**Proof of Lemma 6.6** (D-6.5–6.7). Let `c'` be the constant of Lemma 6.5 (`nondeg_pt`). By the
Hölder bound of Lemma 6.2 (`holder_internal`, `U = B_{3r}(0)`, `T = B̄_{5r/2}(0)`,
`β₀ = ξ(Q - √(2d))/2`), outside an event of probability `≤ c'/4` every pair `u, v ∈ T` has
`D_n(u, v; U) ≤ M a ‖u - v‖^{β₀}`; with `ρ` small (`M (√d ρ)^{β₀} ≤ c'/4`), the triangle inequality
gives `D_n(B_ρ(g), B_ρ(g'); U) ≥ c'a/2` whenever `D_n(g, g'; U) > c'a` (`g ∈ ∂B_r`, `g' ∈ ∂B_{2r}`),
so `P[D_n(B_ρ(g), B_ρ(g'); U) > c'a/4] ≥ c'/2`. Finitely many boxes `B_ρ(g)`, `g ∈ X ⊆ ∂B_r(0)`
(`B_ρ(g')`, `g' ∈ Y ⊆ ∂B_{2r}(0)`) cover the two spheres (compactness). Minimizing paths can be
confined to the closed shell (`lfppSetDist_lsph_le_acrossDist`), so
`D_n(across) ≥ min_{(g,g')} D_n(B_ρ(g), B_ρ(g'); U)`, and FKG for the increasing events
(`fkg_increasing`) gives `P[D_n(across) > c'a/4] ≥ (c'/2)^{#X #Y}`.

**Extension** (blueprint `r2:lem:66`). Every crossing of `B₂(0) \ B₁(0)` passes through
`∂B_{3/2}(0)` (`IsShellPair.exists_crossing_of_le`) at a point of some `B_r(g)`,
`g ∈ Z ⊆ ∂B_{3/2}(0)` finite, and then leaves `B_{2r}(g)` (`r ≤ 1/4`); hence
`D_n(across B₂ \ B₁) ≥ min_{g ∈ Z} D_n(across B_{2r}(g) \ B_r(g))` (`acrossDist_unit_ge_inf'`).
Each shell is handled by Lemma 6.6 for the translated realization
(`isDyadicRealization_translate_tight`, `acrossDist_smul_add`), and FKG over `Z` concludes.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGMetric

namespace DGZ

open HigherDimLFPP HigherDimLFPP.Perc
open HigherDimLFPP.DGZ (latPt cbox obox)

variable {d : ℕ}

/-! ### Small geometric facts -/

lemma tn_isCompact_lsph (c : Rd d) (r : ℝ) : IsCompact (lsph c r) :=
  (isCompact_cbox c r).of_isClosed_subset (isClosed_lsph c r) (lsph_subset_cbox c r)

/-- Closed boxes are convex. -/
lemma tn_convex_cbox (c : Rd d) (r : ℝ) : Convex ℝ (cbox c r) := by
  intro z hz w hw a b ha hb hab i
  have h1 := hz i
  have h2 := hw i
  have e : (a • z + b • w) i - c i = a * (z i - c i) + b * (w i - c i) := by
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    have : c i = (a + b) * c i := by rw [hab, one_mul]
    linear_combination -this
  rw [e]
  calc |a * (z i - c i) + b * (w i - c i)| ≤ |a * (z i - c i)| + |b * (w i - c i)| :=
        abs_add_le _ _
    _ = a * |z i - c i| + b * |w i - c i| := by rw [abs_mul, abs_mul, abs_of_nonneg ha,
        abs_of_nonneg hb]
    _ ≤ a * r + b * r := add_le_add (mul_le_mul_of_nonneg_left h1 ha)
        (mul_le_mul_of_nonneg_left h2 hb)
    _ = r := by rw [← add_mul, hab, one_mul]

lemma tn_mem_obox_self (c : Rd d) {ρ : ℝ} (hρ : 0 < ρ) : c ∈ obox c ρ := fun i => by
  rw [sub_self, abs_zero]; exact hρ

/-- A finite cover of a compact set by boxes `B_ρ(g)` centred on it. -/
lemma tn_exists_obox_cover {S : Set (Rd d)} (hS : IsCompact S) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ X : Finset (Rd d), (∀ g ∈ X, g ∈ S) ∧ S ⊆ ⋃ g ∈ X, obox g ρ :=
  hS.elim_nhds_subcover (fun g => obox g ρ) fun g _ =>
    (HigherDimLFPP.DGZ.isOpen_obox g ρ).mem_nhds (tn_mem_obox_self g hρ)

/-- `‖u - g‖ ≤ √d ρ` for `u ∈ B_ρ(g)`. -/
lemma tn_norm_sub_le {g u : Rd d} {ρ : ℝ} (hu : u ∈ obox g ρ) : ‖g - u‖ ≤ Real.sqrt d * ρ :=
  norm_sub_le_of_forall_abs_le fun i => by rw [abs_sub_comm]; exact (hu i).le

/-- `B_ρ(g) ⊆ B̄_{R+ρ}(0)` for `g ∈ B̄_R(0)`. -/
lemma tn_obox_subset_cbox {g : Rd d} {R ρ : ℝ} (hg : g ∈ cbox (0 : Rd d) R) :
    obox g ρ ⊆ cbox (0 : Rd d) (R + ρ) := fun u hu i => by
  have h1 := hu i
  have h2 := hg i
  simp only [PiLp.zero_apply, sub_zero] at h2 ⊢
  calc |u i| ≤ |u i - g i| + |g i| := by
        have := abs_add_le (u i - g i) (g i); rwa [sub_add_cancel] at this
    _ ≤ R + ρ := by linarith

/-! ### DGZ Lemma 6.6 -/

/-- **DGZ Lemma 6.6** (blueprint `r2:lem:66`, MA7 D-6.5–6.7): under `Cor52Shape` and `DGZHyp`
there is `q₂ ∈ (0, 1)` such that for every `q ∈ [q₂, 1)` and `0 < r ≤ 1/(10√d)` there is `c > 0`
with `P[D_n(across B_{2r}(0) \ B_r(0)) > c a^{(q)}_n] ≥ c` for every dyadic realization and every
`n`. -/
theorem nondeg_cross_pos {κ : Rd d → ℝ} {ξ Q : ℝ} (hC52 : Cor52Shape d κ ξ Q)
    (h : DGZHyp d κ ξ Q) :
    ∃ q₂ : ℝ≥0∞, 0 < q₂ ∧ q₂ < 1 ∧ ∀ q : ℝ≥0∞, q₂ ≤ q → q < 1 → ∀ r : ℝ, 0 < r →
      r * (10 * Real.sqrt d) ≤ 1 → ∃ c : ℝ, 0 < c ∧
        ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ)
          (H : ℕ → Rd d → Ω → ℝ), IsDyadicRealization κ P W H → ∀ n : ℕ,
            ENNReal.ofReal c ≤
              P {ω | c * aQ P H ξ n q < acrossDist ξ (fun z => H n z ω) 0 (2 * r) r} := by
  have hd := h.dim
  have hd0 : 0 < d := by omega
  have hξ := h.xi_pos
  have hκ := h.kernel
  have hsub : 0 < ξ * (Q - Real.sqrt (2 * d)) := by
    have := h.subcritical
    exact mul_pos hξ (by linarith)
  set β₀ : ℝ := ξ * (Q - Real.sqrt (2 * d)) / 2 with hβ₀
  have hβ₀0 : 0 < β₀ := by positivity
  have hβ₀1 : β₀ < ξ * (Q - Real.sqrt (2 * d)) := by linarith
  obtain ⟨q₂, hq₂0, hq₂1, hint⟩ := holder_internal hC52 h hβ₀0 hβ₀1
  refine ⟨q₂, hq₂0, hq₂1, fun q hq₂q hq1 r hr hrd => ?_⟩
  have hq0 : 0 < q := hq₂0.trans_le hq₂q
  -- Lemma 6.5
  obtain ⟨c', hc', hpt⟩ := nondeg_pt h hq0 hq1 hr hrd
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
    obtain ⟨b, hb⟩ := hB
    obtain ⟨g, hg, -⟩ := mem_iUnion₂.1 (hXcov ha)
    obtain ⟨g', hg', -⟩ := mem_iUnion₂.1 (hYcov hb)
    exact ⟨(g, g'), Finset.mem_product.2 ⟨hg, hg'⟩⟩
  set N : ℕ := (X ×ˢ Y).card with hN
  set c : ℝ := min (c' / 4) ((c' / 2) ^ N) with hc
  have hc0 : 0 < c := lt_min (by positivity) (by positivity)
  refine ⟨c, hc0, fun Ω _ P W H hH n => ?_⟩
  have hW := hH.whiteNoise
  have := hW.isProbabilityMeasure
  have hX := hH.band n
  set a := aQ P H ξ n q with ha
  have ha0 : 0 < a := tight_aQ_pos hd0 hH ξ n hq0 hq1
  set G : Set Ω := {ω | ∃ x ∈ T, ∃ y ∈ T, M * a * ‖x - y‖ ^ β₀ <
    lfppDistOn ξ (fun z => H n z ω) U x y} with hG
  have hPG : P G ≤ ENNReal.ofReal (c' / 4) := hMb Ω P W H hH n
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
    have h1 := hpt Ω P W H hH n g hg g' hg'
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

/-! ### The extension to `B₂(0) \ B₁(0)` -/

/-- `B̄_ρ(g) ⊆ B̄_{R+ρ}(0)` for `g ∈ B̄_R(0)`. -/
lemma tn_cbox_subset_cbox {g : Rd d} {R ρ : ℝ} (hg : g ∈ cbox (0 : Rd d) R) :
    cbox g ρ ⊆ cbox (0 : Rd d) (R + ρ) := fun u hu i => by
  have h1 := hu i
  have h2 := hg i
  simp only [PiLp.zero_apply, sub_zero] at h2 ⊢
  calc |u i| ≤ |u i - g i| + |g i| := by
        have := abs_add_le (u i - g i) (g i); rwa [sub_add_cancel] at this
    _ ≤ R + ρ := by linarith

/-- **Crossings of `B₂(0) \ B₁(0)` cross a small shell** (blueprint `r2:lem:66`, extension): if the
boxes `B_r(g)`, `g ∈ Z ⊆ ∂B_{3/2}(0)`, cover `∂B_{3/2}(0)` and `r ≤ 1/4`, then
`min_{g ∈ Z} D(across B_{2r}(g) \ B_r(g)) ≤ D(across B₂(0) \ B₁(0))` for every continuous field. -/
theorem acrossDist_unit_ge_inf' (hd0 : 0 < d) {ξ : ℝ} {φ : Rd d → ℝ} (hφ : Continuous φ) {r : ℝ}
    (hr : 0 < r) (hr4 : r ≤ 1 / 4) {Z : Finset (Rd d)} (hZne : Z.Nonempty)
    (hZs : ∀ g ∈ Z, g ∈ lsph (0 : Rd d) (3 / 2))
    (hZcov : lsph (0 : Rd d) (3 / 2) ⊆ ⋃ g ∈ Z, obox g r) :
    Z.inf' hZne (fun g => acrossDist ξ φ g (2 * r) r) ≤ acrossDist ξ φ 0 2 1 := by
  rw [acrossDist]
  refine le_lfppSetDist (lsph_nonempty hd0 0 zero_le_one) (lsph_nonempty hd0 0 zero_le_two)
    fun x hx y hy => ?_
  refine HigherDimLFPP.le_lfppDistOn (pcwJoined_univ x y) fun γ hγ _ => ?_
  have hsh := isShellPair_box (0 : Rd d) (by norm_num : (3 : ℝ) / 2 < 2)
  obtain ⟨t₀, t₁, ht₀, ht₀₁, ht₁, hγt₀, -, -, -⟩ := hsh.exists_crossing_of_le zero_le_one
    hγ.continuousOn (by rw [hγ.source]; exact cbox_mono (by norm_num) hx.1)
    (by rw [hγ.target]; exact hy.2)
  obtain ⟨g, hg, hpg⟩ := mem_iUnion₂.1 (hZcov hγt₀)
  have hy2 : γ 1 ∉ obox g (2 * r) := by
    rw [hγ.target]
    intro hyo
    have hyn := hy.2
    simp only [HigherDimLFPP.DGZ.obox, mem_ofPred_eq, not_forall, not_lt] at hyn
    obtain ⟨j, hj⟩ := hyn
    have h1 := hyo j
    have h2 := (hZs g hg).1 j
    simp only [PiLp.zero_apply, sub_zero] at hj h2
    have := abs_sub_abs_le_abs_sub (y j) (g j)
    linarith
  have h1 : acrossDist ξ φ g (2 * r) r ≤ ∫ t in t₀..1, lfppIntegrand ξ φ γ t :=
    acrossDist_le_integral hφ (by linarith) hγ ht₀ (by linarith) le_rfl
      (Or.inl ⟨HigherDimLFPP.DGZ.obox_subset_cbox g r hpg, hy2⟩)
  have h2 := integral_le_lfppLength (ξ := ξ) hφ hγ ht₀ (by linarith) le_rfl
  exact (Finset.inf'_le _ hg).trans (h1.trans h2)

/-- **DGZ Lemma 6.6, extended to `B₂(0) \ B₁(0)`** (blueprint `r2:lem:66`; [2] l. 3091): there is
`q₂ ∈ (0, 1)` such that for `q ∈ [q₂, 1)` there is `c > 0` with
`P[D_n(across B₂(0) \ B₁(0)) > c a^{(q)}_n] ≥ c` for every dyadic realization and every `n`. -/
theorem nondeg_cross_unit {κ : Rd d → ℝ} {ξ Q : ℝ} (hC52 : Cor52Shape d κ ξ Q)
    (h : DGZHyp d κ ξ Q) :
    ∃ q₂ : ℝ≥0∞, 0 < q₂ ∧ q₂ < 1 ∧ ∀ q : ℝ≥0∞, q₂ ≤ q → q < 1 → ∃ c : ℝ, 0 < c ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ)
        (H : ℕ → Rd d → Ω → ℝ), IsDyadicRealization κ P W H → ∀ n : ℕ,
          ENNReal.ofReal c ≤ P {ω | c * aQ P H ξ n q < acrossDist ξ (fun z => H n z ω) 0 2 1} := by
  have hd := h.dim
  have hd0 : 0 < d := by omega
  have hξ := h.xi_pos
  have hκ := h.kernel
  obtain ⟨q₂, hq₂0, hq₂1, hcross⟩ := nondeg_cross_pos hC52 h
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
  refine ⟨c, hc0, fun Ω _ P W H hH n => ?_⟩
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
    have hb := hc₀b Ω P _ _ hH' n
    rw [aQ_eq_of_isDyadicRealization hH' hH] at hb
    have e : ∀ ω, acrossDist ξ (fun z => H n z ω) g (2 * r) r =
        acrossDist ξ (fun z => H n (g + z) ω) 0 (2 * r) r := by
      intro ω
      have := acrossDist_smul_add g ξ (fun z => H n z ω) one_pos 0 (2 * r) r
      simpa only [smul_zero, add_zero, one_mul, one_smul] using this
    simp_rw [e]
    exact hb
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

end DGZ

end HigherDimLQGMetric
