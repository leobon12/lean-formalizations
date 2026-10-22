import HigherDimLQGContinuity.SiteEvents.RefsProb
import HigherDimLQGContinuity.Events.Measurability
import HigherDimLQGContinuity.Events.Local

/-! Locality and null-measurability of the site references. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HigherDimLQGContinuity

open MeasureTheory Metric Set
open HigherDimLQGMetric
open HigherDimLFPP (Rd)

variable {d : ℕ}

/-- A countable test for the doubled-ball estimate. -/
theorem q10_dUpper_iff_dense {G : ContMetric d} {W : Set (Rd d)} {H σ : ℝ}
    (hH : 0 ≤ H) (hσ : 0 ≤ σ) :
    DUpper G W H σ ↔ ∀ (n : ℕ) (q : ℚ), 0 < (q : ℝ) →
      closedBall (TopologicalSpace.denseSeq (Rd d) n) (2 * q) ⊆ W →
      ∀ x ∈ ball (TopologicalSpace.denseSeq (Rd d) n) q,
        ∀ y ∈ ball (TopologicalSpace.denseSeq (Rd d) n) q,
          G.internal (ball (TopologicalSpace.denseSeq (Rd d) n) (2 * q)) x y ≤
            ENNReal.ofReal (H * (q : ℝ) ^ σ) := by
  constructor
  · intro h n q hq hball x hx y hy
    have hpoint : G.internal (ball (TopologicalSpace.denseSeq (Rd d) n) (2 * q)) x y ≤
        diamIn G (ball (TopologicalSpace.denseSeq (Rd d) n) (2 * q))
          (ball (TopologicalSpace.denseSeq (Rd d) n) q) := by
      exact le_iSup₂_of_le x hx (le_iSup₂_of_le y hy le_rfl)
    exact hpoint.trans (h _ _ hq hball)
  · intro h z ρ hρ hball
    refine iSup₂_le fun x hx => iSup₂_le fun y hy => ?_
    rw [mem_ball] at hx hy
    set δ := ρ - max (dist x z) (dist y z) with hδ
    have hδpos : 0 < δ := sub_pos.2 (max_lt hx hy)
    have hxz : dist x z ≤ ρ - δ := by rw [hδ]; simp
    have hyz : dist y z ≤ ρ - δ := by rw [hδ]; simp
    have hδρ : δ ≤ ρ := by
      have : 0 ≤ max (dist x z) (dist y z) := le_max_of_le_left dist_nonneg
      linarith
    obtain ⟨n, hn⟩ := (TopologicalSpace.denseRange_denseSeq (Rd d)).exists_dist_lt z
      (show 0 < δ / 4 by positivity)
    set zn := TopologicalSpace.denseSeq (Rd d) n with hzn
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show ρ - 3 * δ / 4 < ρ - δ / 8 by linarith)
    have hq0 : 0 < (q : ℝ) := by linarith
    have hzz : dist zn z < δ / 4 := by rw [dist_comm]; exact hn
    have hcl : closedBall zn (2 * q) ⊆ ball z (2 * ρ) := by
      intro w hw
      rw [mem_closedBall] at hw
      rw [mem_ball]
      calc dist w z ≤ dist w zn + dist zn z := dist_triangle _ _ _
        _ < 2 * ρ := by linarith
    have hsub : ball zn (2 * q) ⊆ ball z (2 * ρ) := ball_subset_closedBall.trans hcl
    have hxn : x ∈ ball zn q := by
      rw [mem_ball]
      calc dist x zn ≤ dist x z + dist z zn := dist_triangle _ _ _
        _ < q := by rw [dist_comm z zn]; linarith
    have hyn : y ∈ ball zn q := by
      rw [mem_ball]
      calc dist y zn ≤ dist y z + dist z zn := dist_triangle _ _ _
        _ < q := by rw [dist_comm z zn]; linarith
    calc G.internal (ball z (2 * ρ)) x y ≤ G.internal (ball zn (2 * q)) x y :=
          G.internal_anti hsub x y
      _ ≤ ENNReal.ofReal (H * (q : ℝ) ^ σ) :=
          h n q hq0 (hcl.trans (ball_subset_closedBall.trans hball)) x hxn y hyn
      _ ≤ ENNReal.ofReal (H * ρ ^ σ) :=
          ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow hq0.le (by linarith) hσ) hH)

/-- The Borel-chain representative of the doubled-ball condition. -/
def q10DUpperChain (G : ContMetric d) (W : Set (Rd d)) (H σ : ℝ) : Prop :=
  ∀ (n : ℕ) (q : ℚ), 0 < (q : ℝ) →
    closedBall (TopologicalSpace.denseSeq (Rd d) n) (2 * q) ⊆ W →
      ∀ x ∈ ball (TopologicalSpace.denseSeq (Rd d) n) q,
        ∀ y ∈ ball (TopologicalSpace.denseSeq (Rd d) n) q,
          G.chainInf (ball (TopologicalSpace.denseSeq (Rd d) n) (2 * q)) x y ≤
            ENNReal.ofReal (H * (q : ℝ) ^ σ)

theorem q10_dUpper_iff_chain {G : ContMetric d} (hG : G.IsLength)
    {W : Set (Rd d)} {H σ : ℝ} (hH : 0 ≤ H) (hσ : 0 ≤ σ) :
    DUpper G W H σ ↔ q10DUpperChain G W H σ := by
  rw [q10_dUpper_iff_dense hH hσ]
  simp only [q10DUpperChain]
  apply forall_congr'
  intro n
  apply forall_congr'
  intro q
  by_cases hq : 0 < (q : ℝ)
  · have hball : IsOpen (ball (TopologicalSpace.denseSeq (Rd d) n) (2 * q)) := isOpen_ball
    simp only [hq, true_implies]
    apply imp_congr_right
    intro _
    simp only [← G.internal_eq_chainInf hG hball]
  · simp [hq]

/-- The chain representative is universally measurable for any fixed ambient set. -/
theorem q10_uMeasurableSet_dUpperChain (W : Set (Rd d)) (H σ : ℝ) :
    LQGMetric.UMeasurableSet {G : ContMetric d | q10DUpperChain G W H σ} := by
  have hfixed (n : ℕ) (q : ℚ) :
      LQGMetric.UMeasurableSet {G : ContMetric d |
        0 < (q : ℝ) →
        closedBall (TopologicalSpace.denseSeq (Rd d) n) (2 * q) ⊆ W →
        ∀ x ∈ ball (TopologicalSpace.denseSeq (Rd d) n) q,
          ∀ y ∈ ball (TopologicalSpace.denseSeq (Rd d) n) q,
            G.chainInf (ball (TopologicalSpace.denseSeq (Rd d) n) (2 * q)) x y ≤
              ENNReal.ofReal (H * (q : ℝ) ^ σ)} := by
    by_cases hq : 0 < (q : ℝ)
    · by_cases hb : closedBall (TopologicalSpace.denseSeq (Rd d) n) (2 * q) ⊆ W
      · have hK : MeasurableSet
            (ball (TopologicalSpace.denseSeq (Rd d) n) q ×ˢ
              ball (TopologicalSpace.denseSeq (Rd d) n) q) :=
          isOpen_ball.measurableSet.prod isOpen_ball.measurableSet
        have hr : MeasurableSet {p : ContMetric d × (Rd d × Rd d) |
            p.1.chainInf (ball (TopologicalSpace.denseSeq (Rd d) n) (2 * q)) p.2.1 p.2.2 ≤
              ENNReal.ofReal (H * (q : ℝ) ^ σ)} :=
          measurableSet_le (p5b_measurable_chainInf_pair _) measurable_const
        convert uMeasurableSet_forall_mem _ hK hr using 1
        ext G
        simp only [mem_ofPred_eq, mem_prod, hq, hb, true_implies]
        constructor
        · intro h p hp
          exact h p.1 hp.1 p.2 hp.2
        · intro h x hx y hy
          exact h (x, y) ⟨hx, hy⟩
      · simpa [hb] using (LQGMetric.UMeasurableSet.of_measurableSet (MeasurableSet.univ : MeasurableSet (univ : Set (ContMetric d))))
    · simpa [hq] using (LQGMetric.UMeasurableSet.of_measurableSet (MeasurableSet.univ : MeasurableSet (univ : Set (ContMetric d))))
  have h : LQGMetric.UMeasurableSet
      (⋂ (n : ℕ) (q : ℚ), {G : ContMetric d |
        0 < (q : ℝ) →
        closedBall (TopologicalSpace.denseSeq (Rd d) n) (2 * q) ⊆ W →
        ∀ x ∈ ball (TopologicalSpace.denseSeq (Rd d) n) q,
          ∀ y ∈ ball (TopologicalSpace.denseSeq (Rd d) n) q,
            G.chainInf (ball (TopologicalSpace.denseSeq (Rd d) n) (2 * q)) x y ≤
              ENNReal.ofReal (H * (q : ℝ) ^ σ)}) :=
    LQGMetric.UMeasurableSet.iInter fun n => LQGMetric.UMeasurableSet.iInter fun q => hfixed n q
  convert h using 1
  ext G
  simp only [q10DUpperChain, mem_iInter, mem_ofPred_eq]

/-- Chain representative of all five site-reference clauses. -/
def q10SiteRefsChain (G : ContMetric d) (Hup s Hlo b mc A0 : ℝ) : Prop :=
  q10DUpperChain G (siteA d) Hup s ∧
  (∀ x ∈ siteC d, ∀ y ∈ siteC d,
    ENNReal.ofReal (Hlo⁻¹ * ‖x - y‖ ^ b) ≤ G.chainInf (siteA d) x y) ∧
  (∀ x ∈ sphere (0 : Rd d) 1, ∀ y ∈ sphere 0 (3 / 2),
    ENNReal.ofReal mc ≤ G.chainInf (siteA d) x y) ∧
  (∀ x ∈ sphere (0 : Rd d) (5 / 2), ∀ y ∈ sphere 0 3,
    ENNReal.ofReal mc ≤ G.chainInf (siteA d) x y) ∧
  (∀ x ∈ siteC d, ∀ y ∈ siteC d,
    G.chainInf (siteA d) x y ≤ ENNReal.ofReal A0)

theorem q10_siteRefs_iff_chain {G : ContMetric d} (hG : G.IsLength)
    {Hup s Hlo b mc A0 : ℝ} (hH : 0 ≤ Hup) (hs : 0 ≤ s) :
    SiteRefs Hup s Hlo b mc A0 G ↔ q10SiteRefsChain G Hup s Hlo b mc A0 := by
  rw [SiteRefs, q10SiteRefsChain, q10_dUpper_iff_chain hG hH hs]
  simp only [setDistIn, diamIn, le_iInf_iff, iSup_le_iff]
  have hA : IsOpen (siteA d) := isOpen_annA
  simp_rw [G.internal_eq_chainInf hG hA]

theorem q10_uMeasurableSet_siteRefsChain (Hup s Hlo b mc A0 : ℝ) :
    LQGMetric.UMeasurableSet
      {G : ContMetric d | q10SiteRefsChain G Hup s Hlo b mc A0} := by
  have hC : MeasurableSet (siteC d ×ˢ siteC d) :=
    (isClosed_annCl _ _ _).measurableSet.prod (isClosed_annCl _ _ _).measurableSet
  have hS₁ : MeasurableSet (sphere (0 : Rd d) 1 ×ˢ sphere (0 : Rd d) (3 / 2)) :=
    isClosed_sphere.measurableSet.prod isClosed_sphere.measurableSet
  have hS₂ : MeasurableSet (sphere (0 : Rd d) (5 / 2) ×ˢ sphere (0 : Rd d) 3) :=
    isClosed_sphere.measurableSet.prod isClosed_sphere.measurableSet
  have hc := p5b_measurable_chainInf_pair (d := d) (siteA d)
  have hr₂ : MeasurableSet {p : ContMetric d × (Rd d × Rd d) |
      ENNReal.ofReal (Hlo⁻¹ * ‖p.2.1 - p.2.2‖ ^ b) ≤ p.1.chainInf (siteA d) p.2.1 p.2.2} :=
    measurableSet_le (ENNReal.measurable_ofReal.comp
      (measurable_const.mul (p5b_measurable_normSub.pow_const b))) hc
  have hr₃ : MeasurableSet {p : ContMetric d × (Rd d × Rd d) |
      ENNReal.ofReal mc ≤ p.1.chainInf (siteA d) p.2.1 p.2.2} :=
    measurableSet_le measurable_const hc
  have hr₄ : MeasurableSet {p : ContMetric d × (Rd d × Rd d) |
      p.1.chainInf (siteA d) p.2.1 p.2.2 ≤ ENNReal.ofReal A0} :=
    measurableSet_le hc measurable_const
  have u₂ := uMeasurableSet_forall_mem _ hC hr₂
  have u₃ := uMeasurableSet_forall_mem _ hS₁ hr₃
  have u₄ := uMeasurableSet_forall_mem _ hS₂ hr₃
  have u₅ := uMeasurableSet_forall_mem _ hC hr₄
  have u := (q10_uMeasurableSet_dUpperChain (d := d) (siteA d) Hup s).inter
    (u₂.inter (u₃.inter (u₄.inter u₅)))
  convert u using 1
  ext G
  simp only [q10SiteRefsChain, mem_inter_iff, mem_ofPred_eq, mem_prod]
  constructor
  · rintro ⟨h₁, h₂, h₃, h₄, h₅⟩
    refine ⟨h₁, ?_, ?_, ?_, ?_⟩
    · intro p hp; exact h₂ p.1 hp.1 p.2 hp.2
    · intro p hp; exact h₃ p.1 hp.1 p.2 hp.2
    · intro p hp; exact h₄ p.1 hp.1 p.2 hp.2
    · intro p hp; exact h₅ p.1 hp.1 p.2 hp.2
  · rintro ⟨h₁, h₂, h₃, h₄, h₅⟩
    refine ⟨h₁, ?_, ?_, ?_, ?_⟩
    · intro x hx y hy; exact h₂ (x, y) ⟨hx, hy⟩
    · intro x hx y hy; exact h₃ (x, y) ⟨hx, hy⟩
    · intro x hx y hy; exact h₄ (x, y) ⟨hx, hy⟩
    · intro x hx y hy; exact h₅ (x, y) ⟨hx, hy⟩

/-- Null-measurability follows from the chain representatives on the a.s. length event. -/
theorem q10_nullMeasurableSet_dUpper {D : DistRd d → ContMetric d} (hD : Measurable D)
    (μ : Measure (DistRd d)) [IsFiniteMeasure μ]
    (hl : ∀ᵐ g ∂μ, (rho D g).IsLength) {W : Set (Rd d)} {H σ : ℝ}
    (hH : 0 ≤ H) (hσ : 0 ≤ σ) :
    NullMeasurableSet {g | DUpper (rho D g) W H σ} μ := by
  have hT := ((q10_uMeasurableSet_dUpperChain (d := d) W H σ).preimage
    (measurable_rho hD)).nullMeasurableSet μ
  refine hT.congr ?_
  filter_upwards [hl] with g hg
  exact propext (q10_dUpper_iff_chain hg hH hσ).symm

theorem q10_nullMeasurableSet_siteRefs {D : DistRd d → ContMetric d} (hD : Measurable D)
    (μ : Measure (DistRd d)) [IsFiniteMeasure μ]
    (hl : ∀ᵐ g ∂μ, (rho D g).IsLength) {Hup s Hlo b mc A0 : ℝ}
    (hH : 0 ≤ Hup) (hs : 0 ≤ s) :
    NullMeasurableSet {g | SiteRefs Hup s Hlo b mc A0 (rho D g)} μ := by
  have hT := ((q10_uMeasurableSet_siteRefsChain (d := d) Hup s Hlo b mc A0).preimage
    (measurable_rho hD)).nullMeasurableSet μ
  refine hT.congr ?_
  filter_upwards [hl] with g hg
  exact propext (q10_siteRefs_iff_chain hg hH hs).symm

/-- Internal equality on a set extends to all endpoint pairs, with `∞` outside the set. -/
theorem q10_internal_eq_all_of_on {G G' : ContMetric d} {U : Set (Rd d)}
    (h : ∀ x ∈ U, ∀ y ∈ U, G.internal U x y = G'.internal U x y) :
    ∀ x y, G.internal U x y = G'.internal U x y := by
  intro x y
  by_cases hx : x ∈ U
  · by_cases hy : y ∈ U
    · exact h x hx y hy
    · rw [G.internal_eq_top_of_notMem_right hy, G'.internal_eq_top_of_notMem_right hy]
  · rw [G.internal_eq_top_of_notMem_left hx, G'.internal_eq_top_of_notMem_left hx]

/-- A profile on `U` determines every smaller internal metric. -/
theorem q10_internal_eq_of_subset {G G' : ContMetric d} {U W : Set (Rd d)}
    (hWU : W ⊆ U)
    (h : ∀ x ∈ U, ∀ y ∈ U, G.internal U x y = G'.internal U x y) (x y : Rd d) :
    G.internal W x y = G'.internal W x y := by
  have hU : G.internal U = G'.internal U :=
    funext fun a => funext fun b => q10_internal_eq_all_of_on h a b
  rw [← G.internalWith_internal hWU, ← G'.internalWith_internal hWU, hU]

theorem q10_dUpper_saturated {G G' : ContMetric d} {U W : Set (Rd d)}
    (hWU : W ⊆ U)
    (h : ∀ x ∈ U, ∀ y ∈ U, G.internal U x y = G'.internal U x y)
    {H σ : ℝ} (hG : DUpper G W H σ) : DUpper G' W H σ := by
  intro z r hr hball
  have hb : ball z (2 * r) ⊆ U := (ball_subset_closedBall.trans hball).trans hWU
  rw [diamIn_congr_internal (G := G) (G' := G') fun x _ y _ =>
    (q10_internal_eq_of_subset hb h x y).symm]
  exact hG z r hr hball

theorem q10_siteRefs_saturated {G G' : ContMetric d}
    (h : ∀ x ∈ siteA d, ∀ y ∈ siteA d,
      G.internal (siteA d) x y = G'.internal (siteA d) x y)
    {Hup s Hlo b mc A0 : ℝ} (hG : SiteRefs Hup s Hlo b mc A0 G) :
    SiteRefs Hup s Hlo b mc A0 G' := by
  have hall := q10_internal_eq_all_of_on h
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := hG
  refine ⟨q10_dUpper_saturated (U := siteA d) (W := siteA d) Subset.rfl h h₁,
    ?_, ?_, ?_, ?_⟩
  · intro x hx y hy
    rw [← hall x y]
    exact h₂ x hx y hy
  · simpa only [setDistIn, hall] using h₃
  · simpa only [setDistIn, hall] using h₄
  · simpa only [diamIn, hall] using h₅

theorem q10_siteA_subset_ann4 :
    siteA d ⊆ ann (0 : Rd d) (1 / 2) 4 := by
  intro x hx
  change x ∈ annA d at hx
  rw [mem_annA_iff] at hx
  exact ⟨by simpa using hx.1, by simpa using lt_trans hx.2 (by norm_num : (7 / 2 : ℝ) < 4)⟩

theorem q10_pinSphere_subset_ann4 :
    sphere (0 : Rd d) 1 ⊆ ann (0 : Rd d) (1 / 2) 4 := by
  intro x hx
  have hn : ‖x‖ = 1 := by simpa using hx
  change (1 / 2 : ℝ) < ‖x - 0‖ ∧ ‖x - 0‖ < 4
  simp [hn]
  norm_num

/-- Locality of the doubled-ball reference at the unit pin. -/
theorem dupper_aeEventIn (hd : 2 ≤ d) {ξ : ℝ} (hξ : 0 < ξ)
    {D : DistRd d → ContMetric d} (hD : IsStrongExpMetric d ξ (distExp d ξ) D)
    {H σ : ℝ} (hH : 0 ≤ H) (hσ : 0 ≤ σ) :
    AEEventIn (pinLaw d 1) (fieldSigma0 id (ann (0 : Rd d) (1 / 2) 4))
      {g | DUpper (rho D g) (siteA d) H σ} := by
  have := isProbabilityMeasure_pinLaw hd (1 : ℝ)
  have hl := p5b_ae_isLength_rho hd hD one_pos
  exact p5b_aeEventIn_of_profile_one hd hξ hD one_pos isOpen_annA
    (p5b_annA_nonempty (d := d) (by omega)) (isOpen_ann _ _ _)
    q10_siteA_subset_ann4 q10_pinSphere_subset_ann4
    (q10_nullMeasurableSet_dUpper hD.measurable _ hl hH hσ)
    (fun g₁ g₂ _ _ he hB => q10_dUpper_saturated (U := siteA d) (W := siteA d)
      Subset.rfl he hB)

/-- Locality of all site references at the unit pin. -/
theorem siteRefs_aeEventIn (hd : 2 ≤ d) {ξ : ℝ} (hξ : 0 < ξ)
    {D : DistRd d → ContMetric d} (hD : IsStrongExpMetric d ξ (distExp d ξ) D)
    {Hup s Hlo b mc A0 : ℝ} (hH : 0 ≤ Hup) (hs : 0 ≤ s) :
    AEEventIn (pinLaw d 1) (fieldSigma0 id (ann (0 : Rd d) (1 / 2) 4))
      {g | SiteRefs Hup s Hlo b mc A0 (rho D g)} := by
  have := isProbabilityMeasure_pinLaw hd (1 : ℝ)
  have hl := p5b_ae_isLength_rho hd hD one_pos
  exact p5b_aeEventIn_of_profile_one hd hξ hD one_pos isOpen_annA
    (p5b_annA_nonempty (d := d) (by omega)) (isOpen_ann _ _ _)
    q10_siteA_subset_ann4 q10_pinSphere_subset_ann4
    (q10_nullMeasurableSet_siteRefs hD.measurable _ hl hH hs)
    (fun g₁ g₂ _ _ he hB => q10_siteRefs_saturated he hB)

/-- Lemma `b:lem-refs4-prob`, doubled-ball part, including the locality clause. -/
theorem dupper_prob (hd : 2 ≤ d) {ξbar : ℝ}
    (hU : UniformEstimates d ξbar 1) {p : ℝ} (hp : 0 < p) :
    ∃ Hsd σsd : ℝ, 1 ≤ Hsd ∧ 0 < σsd ∧ σsd ≤ 1 ∧
      ∀ ξ ∈ Ioc (0 : ℝ) ξbar, ∀ D : DistRd d → ContMetric d,
        IsStrongExpMetric d ξ (distExp d ξ) D →
          pinLaw d 1 {g | ¬ DUpper (rho D g) (siteA d) Hsd σsd} ≤ ENNReal.ofReal p ∧
          AEEventIn (pinLaw d 1) (fieldSigma0 id (ann (0 : Rd d) (1 / 2) 4))
            {g | DUpper (rho D g) (siteA d) Hsd σsd} := by
  obtain ⟨Hsd, σsd, hHsd, hσsd, hσsd1, hprob⟩ := dupper_prob_bound hd hU hp
  refine ⟨Hsd, σsd, hHsd, hσsd, hσsd1, ?_⟩
  intro ξ hξ D hD
  exact ⟨hprob ξ hξ D hD, dupper_aeEventIn hd hξ.1 hD (by linarith) hσsd.le⟩

/-- Lemma `b:lem-refs4-prob`, site-reference part, including the locality clause. -/
theorem siteRefs_prob (hd : 2 ≤ d) {ξbar : ℝ}
    (hU : UniformEstimates d ξbar 1) {p : ℝ} (hp : 0 < p) :
    ∃ Hup σ Hlo β mc A0 : ℝ,
      1 ≤ Hup ∧ 0 < σ ∧ σ ≤ 1 ∧ 1 ≤ Hlo ∧ 1 ≤ β ∧ 0 < mc ∧ Hlo⁻¹ ≤ A0 ∧
      ∀ ξ ∈ Ioc (0 : ℝ) ξbar, ∀ D : DistRd d → ContMetric d,
        IsStrongExpMetric d ξ (distExp d ξ) D →
          pinLaw d 1 {g | ¬ SiteRefs Hup σ Hlo β mc A0 (rho D g)} ≤ ENNReal.ofReal p ∧
          AEEventIn (pinLaw d 1) (fieldSigma0 id (ann (0 : Rd d) (1 / 2) 4))
            {g | SiteRefs Hup σ Hlo β mc A0 (rho D g)} := by
  obtain ⟨Hup, σ, Hlo, β, mc, A0, hHup, hσ, hσ1, hHlo, hβ, hmc, hA0, hprob⟩ :=
    siteRefs_prob_bound hd hU hp
  refine ⟨Hup, σ, Hlo, β, mc, A0, hHup, hσ, hσ1, hHlo, hβ, hmc, hA0, ?_⟩
  intro ξ hξ D hD
  exact ⟨hprob ξ hξ D hD, siteRefs_aeEventIn hd hξ.1 hD (by linarith) hσ.le⟩

end HigherDimLQGContinuity
