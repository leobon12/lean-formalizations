import HigherDimLQGMetric.Events.AnnulusGeometry
import HigherDimLQGMetric.Sharp.TightWeak

/-!
# Internal diameter from compactness and a modulus

The generic deterministic estimate and its uniform probability consequence for
the buffered annulus. This is the diameter part of D-R.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open MeasureTheory Set Metric
open HigherDimLFPP (Rd)
open scoped ENNReal

variable {d : ℕ}

theorem diamIn_smul {C : ℝ} (hC : 0 < C) (D : ContMetric d)
    (V K : Set (Rd d)) :
    diamIn (D.smul C hC) V K = ENNReal.ofReal C * diamIn D V K := by
  unfold diamIn
  simp_rw [ContMetric.internal_smul hC]
  simp only [ENNReal.mul_iSup]

theorem diamIn_affine {r : ℝ} (hr : r ≠ 0) (z : Rd d)
    (D : ContMetric d) (V K : Set (Rd d)) :
    diamIn (D.affine r hr z) V K =
      diamIn D ((fun u => r • u + z) '' V) ((fun u => r • u + z) '' K) := by
  unfold diamIn
  simp_rw [ContMetric.internal_affine hr z D]
  simp only [iSup_image]

theorem weakScaledMetric_diamIn (ξ : ℝ) (D : DistRd d → ContMetric d)
    (c : ℝ → ℝ) (g : DistRd d) {r : ℝ} (hr : 0 < r)
    (z : Rd d) (hc : 0 < c r) :
    diamIn (weakScaledMetric ξ D c g hr z hc)
      (ann 0 (3 / 4) 3) (annCl 0 (7 / 8) (5 / 2)) =
      ENNReal.ofReal ((c r)⁻¹ * Real.exp (-ξ * sphereAvg g r z)) *
        diamIn (D g) (ann z (3 * r / 4) (3 * r))
          (annCl z (7 * r / 8) (5 * r / 2)) := by
  unfold weakScaledMetric
  rw [diamIn_smul, diamIn_affine hr.ne' z,
    image_ann_affine hr z (3 / 4) 3,
    image_annCl_affine hr z (7 / 8) (5 / 2)]
  congr 2 <;> ring

/-- Chain and collar control imply an internal diameter bound. -/
theorem diamIn_le_of_chain_modulus {K V : Set (Rd d)}
    (hV : IsOpen V) (hKV : K ⊆ V) {b : ℝ} {N : ℕ}
    (hN : ∀ u ∈ K, ∀ v ∈ K, ∀ (δ : Rd d → Rd d → ℝ≥0∞),
      (∀ x ∈ K, δ x x = 0) → (∀ x y z, δ x z ≤ δ x y + δ y z) →
      ∀ M : ℝ≥0∞,
        (∀ x y, sharpShortStep K b x y → δ x y ≤ M) →
        δ u v ≤ (N : ℝ≥0∞) * M)
    (D : ContMetric d) (hD : D.IsLength) {a : ℝ} (ha : 0 < a)
    (hsep : ∀ u ∈ K, ∀ v ∈ frontier V, a < D.1 (u, v))
    (hmod : ∀ u ∈ K, ∀ v ∈ K, ‖u - v‖ ≤ b → D.1 (u, v) < a) :
    diamIn D V K ≤ (N : ℝ≥0∞) * ENNReal.ofReal a := by
  unfold diamIn
  refine iSup_le fun u => iSup_le fun hu => iSup_le fun v => iSup_le fun hv => ?_
  refine hN u hu v hv (D.internal V) (fun x hx => D.internal_self (hKV hx))
    (D.internal_triangle V) (ENNReal.ofReal a) ?_
  intro x y hxy
  have hxV : x ∈ V := hKV hxy.1
  have hxylt : edist (D.pt x) (D.pt y) < ENNReal.ofReal a := by
    rw [edist_dist]
    exact (ENNReal.ofReal_lt_ofReal_iff ha).2
      (hmod x hxy.1 y hxy.2.1 hxy.2.2.le)
  have hfront : ENNReal.ofReal a ≤
      Metric.infEDist (D.pt x) (D.pt '' frontier V) := by
    apply Metric.le_infEDist.2
    rintro _ ⟨w, hw, rfl⟩
    rw [edist_dist]
    exact ENNReal.ofReal_le_ofReal (hsep x hxy.1 w hw).le
  rw [(ContMetric.internal_eq_of_lt_infEDist_frontier hD hV hxV
    (hxylt.trans_le hfront)).2, edist_dist]
  exact ENNReal.ofReal_le_ofReal
    (hmod x hxy.1 y hxy.2.1 hxy.2.2.le).le

private theorem bufferAnn_subset_outerAnn :
    annCl (0 : Rd d) (7 / 8) (5 / 2) ⊆ ann 0 (3 / 4) 3 := by
  intro x hx
  dsimp [ann, annCl] at hx ⊢
  constructor <;> linarith

private theorem compact_frontier_outerAnn :
    IsCompact (frontier (ann (0 : Rd d) (3 / 4) 3)) := by
  let V : Set (Rd d) := ann 0 (3 / 4) 3
  have hsub : frontier V ⊆ closedBall (0 : Rd d) 3 := by
    intro x hx
    have hc : x ∈ annCl (0 : Rd d) (3 / 4) 3 :=
      closure_minimal (ann_subset_annCl _ _ _) (isClosed_annCl _ _ _)
        (frontier_subset_closure hx)
    simpa only [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hc.2
  exact (isCompact_closedBall _ _).of_isClosed_subset isClosed_frontier hsub

private theorem buffer_frontier_offDiag (p : Rd d × Rd d)
    (hp : p ∈ annCl (0 : Rd d) (7 / 8) (5 / 2) ×ˢ
      frontier (ann 0 (3 / 4) 3)) : p.1 ≠ p.2 := by
  intro heq
  have hm : p.1 ∈ ann (0 : Rd d) (3 / 4) 3 ∩
      frontier (ann 0 (3 / 4) 3) :=
    ⟨bufferAnn_subset_outerAnn hp.1, heq ▸ hp.2⟩
  rw [(isOpen_ann (0 : Rd d) (3 / 4) 3).inter_frontier_eq] at hm
  exact hm

/-- Uniform normalized annular internal diameter for the centered weak metric. -/
theorem IsWeakExpMetric.scaledAnnulusDiameter
    {ξ : ℝ} {D : DistRd d → ContMetric d} {c : ℝ → ℝ}
    (hD : IsWeakExpMetric d ξ D c) (hd : 2 ≤ d)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (h : Ω → DistRd d), IsWholeSpaceLGF h P →
        ∀ (r : ℝ) (hr : 0 < r) (z : Rd d),
          P {ω | ENNReal.ofReal C <
            diamIn (weakScaledMetric ξ D c (h ω) hr z
              (hD.c_pos r hr))
              (ann 0 (3 / 4) 3) (annCl 0 (7 / 8) (5 / 2))} < ε := by
  have hε2 : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  let K : Set (Rd d) := annCl 0 (7 / 8) (5 / 2)
  let V : Set (Rd d) := ann 0 (3 / 4) 3
  obtain ⟨a, ha, Hsep⟩ := hD.scaledLowerOffDiag hd
    (isCompact_bufferAnn.prod compact_frontier_outerAnn)
    buffer_frontier_offDiag hε2
  obtain ⟨b, hb, Hmod⟩ := hD.scaledModulus hd isCompact_bufferAnn ha hε2
  obtain ⟨N, hN⟩ := compact_connected_chain_bound
    isCompact_bufferAnn (isConnected_bufferAnn hd) hb
  let C : ℝ := (N + 1) * a
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro Ω _ P _ h hh r hr z
  have hgood (ω : Ω) (hl : (D (h ω)).IsLength)
      (hs : ∀ p ∈ K ×ˢ frontier V, a < scaledField ξ D c r z (h ω) p)
      (hm : ∀ u ∈ K, ∀ v ∈ K, ‖u - v‖ ≤ b →
        scaledField ξ D c r z (h ω) (u, v) < a) :
      diamIn (weakScaledMetric ξ D c (h ω) hr z (hD.c_pos r hr)) V K ≤
        ENNReal.ofReal C := by
    let M : ContMetric d := weakScaledMetric ξ D c (h ω) hr z (hD.c_pos r hr)
    have hMlen : M.IsLength := weakScaledMetric_isLength ξ D c (h ω) hr z _ hl
    have hsep : ∀ u ∈ K, ∀ v ∈ frontier V, a < M.1 (u, v) := by
      intro u hu v hv
      rw [weakScaledMetric_apply]
      exact hs (u, v) ⟨hu, hv⟩
    have hmod : ∀ u ∈ K, ∀ v ∈ K, ‖u - v‖ ≤ b → M.1 (u, v) < a := by
      intro u hu v hv huv
      rw [weakScaledMetric_apply]
      exact hm u hu v hv huv
    have hdiam := diamIn_le_of_chain_modulus (isOpen_ann _ _ _)
      bufferAnn_subset_outerAnn hN M hMlen ha hsep hmod
    have hle : (N : ℝ≥0∞) * ENNReal.ofReal a ≤ ENNReal.ofReal C := by
      have hNa : (N : ℝ) * a ≤ C := by dsimp [C]; nlinarith
      calc
        (N : ℝ≥0∞) * ENNReal.ofReal a = ENNReal.ofReal ((N : ℝ) * a) := by
          rw [ENNReal.ofReal_mul (p := (N : ℝ)) (by positivity), ENNReal.ofReal_natCast]
        _ ≤ ENNReal.ofReal C := ENNReal.ofReal_le_ofReal hNa
    exact hdiam.trans hle
  have hbad : P {ω | ENNReal.ofReal C <
      diamIn (weakScaledMetric ξ D c (h ω) hr z (hD.c_pos r hr)) V K} ≤
      P ({ω | ¬ ∀ p ∈ K ×ˢ frontier V, a < scaledField ξ D c r z (h ω) p} ∪
        {ω | ¬ ∀ u ∈ K, ∀ v ∈ K, ‖u - v‖ ≤ b →
          scaledField ξ D c r z (h ω) (u, v) < a}) := by
    refine measure_mono_ae ?_
    filter_upwards [hD.length P h hh.isLGFPlusCont] with ω hl hω
    by_contra hnot
    simp only [mem_union, mem_ofPred_eq, not_or, not_not] at hnot
    exact (not_lt_of_ge (hgood ω hl hnot.1 hnot.2)) hω
  calc
    P {ω | ENNReal.ofReal C < diamIn
      (weakScaledMetric ξ D c (h ω) hr z (hD.c_pos r hr)) V K} ≤ P _ := hbad
    _ ≤ P {ω | ¬ ∀ p ∈ K ×ˢ frontier V, a < scaledField ξ D c r z (h ω) p} +
        P {ω | ¬ ∀ u ∈ K, ∀ v ∈ K, ‖u - v‖ ≤ b →
          scaledField ξ D c r z (h ω) (u, v) < a} := measure_union_le _ _
    _ < ε / 2 + ε / 2 := ENNReal.add_lt_add (Hsep P h hh r hr z) (Hmod P h hh r hr z)
    _ = ε := ENNReal.add_halves ε

private theorem coreAnn_subset_bufferAnn :
    annCl (0 : Rd d) 1 2 ⊆ annCl 0 (7 / 8) (5 / 2) := by
  intro x hx
  dsimp [annCl] at hx ⊢
  constructor <;> linarith

/-- Uniform small-step internal modulus on the core annulus. -/
theorem IsWeakExpMetric.scaledAnnulusModulus
    {ξ : ℝ} {D : DistRd d → ContMetric d} {c : ℝ → ℝ}
    (hD : IsWeakExpMetric d ξ D c) (hd : 2 ≤ d)
    {L : ℝ} (hL : 0 < L) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ β : ℝ, 0 < β ∧ β < 1 ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (h : Ω → DistRd d), IsWholeSpaceLGF h P →
        ∀ (r : ℝ) (hr : 0 < r) (z : Rd d),
          P {ω | ¬ ∀ u ∈ annCl (0 : Rd d) 1 2,
            ∀ v ∈ annCl 0 1 2, ‖u - v‖ ≤ β →
              (weakScaledMetric ξ D c (h ω) hr z (hD.c_pos r hr)).internal
                (ann 0 (3 / 4) 3) u v < ENNReal.ofReal L} < ε := by
  have hε2 : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  let K : Set (Rd d) := annCl 0 (7 / 8) (5 / 2)
  let V : Set (Rd d) := ann 0 (3 / 4) 3
  obtain ⟨a, ha, Hsep⟩ := hD.scaledLowerOffDiag hd
    (isCompact_bufferAnn.prod compact_frontier_outerAnn)
    buffer_frontier_offDiag hε2
  have hmin : 0 < min a L := lt_min ha hL
  obtain ⟨b, hb, Hmod⟩ := hD.scaledModulus hd isCompact_bufferAnn hmin hε2
  let β : ℝ := min b (1 / 2)
  have hβ : 0 < β := lt_min hb (by norm_num)
  have hβ1 : β < 1 := (min_le_right _ _).trans_lt (by norm_num)
  refine ⟨β, hβ, hβ1, ?_⟩
  intro Ω _ P _ h hh r hr z
  have hgood (ω : Ω) (hl : (D (h ω)).IsLength)
      (hs : ∀ p ∈ K ×ˢ frontier V, a < scaledField ξ D c r z (h ω) p)
      (hm : ∀ u ∈ K, ∀ v ∈ K, ‖u - v‖ ≤ b →
        scaledField ξ D c r z (h ω) (u, v) < min a L) :
      ∀ u ∈ annCl (0 : Rd d) 1 2,
        ∀ v ∈ annCl 0 1 2, ‖u - v‖ ≤ β →
          (weakScaledMetric ξ D c (h ω) hr z (hD.c_pos r hr)).internal V u v <
            ENNReal.ofReal L := by
    intro u hu v hv huv
    let M : ContMetric d := weakScaledMetric ξ D c (h ω) hr z (hD.c_pos r hr)
    have hMlen : M.IsLength := weakScaledMetric_isLength ξ D c (h ω) hr z _ hl
    have huK : u ∈ K := coreAnn_subset_bufferAnn hu
    have hvK : v ∈ K := coreAnn_subset_bufferAnn hv
    have huV : u ∈ V := bufferAnn_subset_outerAnn huK
    have hMuv : M.1 (u, v) < min a L := by
      rw [weakScaledMetric_apply]
      exact hm u huK v hvK (huv.trans (min_le_left _ _))
    have hfront : ENNReal.ofReal a ≤ Metric.infEDist (M.pt u) (M.pt '' frontier V) := by
      apply Metric.le_infEDist.2
      rintro _ ⟨w, hw, rfl⟩
      rw [edist_dist, M.dist_pt, weakScaledMetric_apply]
      exact ENNReal.ofReal_le_ofReal (hs (u, w) ⟨huK, hw⟩).le
    have hlt : edist (M.pt u) (M.pt v) < Metric.infEDist (M.pt u) (M.pt '' frontier V) := by
      rw [edist_dist]
      exact ((ENNReal.ofReal_lt_ofReal_iff ha).2 (hMuv.trans_le (min_le_left _ _))).trans_le hfront
    rw [(ContMetric.internal_eq_of_lt_infEDist_frontier hMlen (isOpen_ann _ _ _) huV hlt).2,
      edist_dist]
    exact (ENNReal.ofReal_lt_ofReal_iff hL).2 (hMuv.trans_le (min_le_right _ _))
  have hbad : P {ω | ¬ ∀ u ∈ annCl (0 : Rd d) 1 2,
      ∀ v ∈ annCl 0 1 2, ‖u - v‖ ≤ β →
        (weakScaledMetric ξ D c (h ω) hr z (hD.c_pos r hr)).internal V u v <
          ENNReal.ofReal L} ≤
      P ({ω | ¬ ∀ p ∈ K ×ˢ frontier V, a < scaledField ξ D c r z (h ω) p} ∪
        {ω | ¬ ∀ u ∈ K, ∀ v ∈ K, ‖u - v‖ ≤ b →
          scaledField ξ D c r z (h ω) (u, v) < min a L}) := by
    refine measure_mono_ae ?_
    filter_upwards [hD.length P h hh.isLGFPlusCont] with ω hl hω
    by_contra hnot
    simp only [mem_union, mem_ofPred_eq, not_or, not_not] at hnot
    exact hω (hgood ω hl hnot.1 hnot.2)
  calc
    P {ω | ¬ ∀ u ∈ annCl (0 : Rd d) 1 2,
      ∀ v ∈ annCl 0 1 2, ‖u - v‖ ≤ β →
        (weakScaledMetric ξ D c (h ω) hr z (hD.c_pos r hr)).internal V u v <
          ENNReal.ofReal L} ≤ P _ := hbad
    _ ≤ P {ω | ¬ ∀ p ∈ K ×ˢ frontier V, a < scaledField ξ D c r z (h ω) p} +
        P {ω | ¬ ∀ u ∈ K, ∀ v ∈ K, ‖u - v‖ ≤ b →
          scaledField ξ D c r z (h ω) (u, v) < min a L} := measure_union_le _ _
    _ < ε / 2 + ε / 2 := ENNReal.add_lt_add (Hsep P h hh r hr z) (Hmod P h hh r hr z)
    _ = ε := ENNReal.add_halves ε

end HigherDimLQGMetric
