/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2JvRoot
import InteractingSLE.Spec.Supplement.SB2JvEnd
import InteractingSLE.Spec.Supplement.SBS3DvStage
import InteractingSLE.Spec.Supplement.SB2MtLift

/-!
# SB2(2): carrying CORNER's F2a from the canonical chart to the run chart

Packet PROVE-SB2-LIFTSET (round 18). CORNER's F2a (`Dv.SB2LowerStageDrivenStatement`) gives drivenness of the
canonical stage curve `Dv.canonCurve X x₀ p L` (the hull chart of the physical retained union `X`). LIFTSET's stage
curve `stCurvep c m p L s₂` reads the same piece through the upper chart `c`, the shift `m` and the relative run chart
`stChart s₂`, i.e. through `Mo.physRelChart c (stChart s₂) m`. The deterministic transfer:

* **`stValp_eq_canonVal`** / **`stCurvep_eq_canonCurve`**: if on `ℍ ∖ fill X` the physical relative chart is the
  hull chart with offset `x₀` (`Mt.physRelChart_eq_hullChart`) and the two good sets agree (the piece's points off
  `fill A` are off `fill X`), the two stage curves are equal;
* `canonVal_offset`: changing the offset translates the canonical curve;
* **`isDrivenCurve_stCurvep_of_canon`**: hence drivenness of the canonical curve at some offset gives drivenness of
  LIFTSET's stage curve, as soon as the latter starts at `0`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.SB.Lk

open Exist Exist.Staged Exist.StagedLaw Sec7.PocketTraversal Sec7.Lemma71C

variable {c : Chart} {m : ℝ} {p : ℝ≥0 → ℂ} {L : ℝ≥0∞} {s₂ : ExplState} {X : Set ℂ} {x₀ : ℝ}

/-- **The run-chart stage values are the canonical values** when the charts and the good sets agree. -/
theorem stValp_eq_canonVal
    (hΦ : ∀ z ∈ H \ fillH X, (stChart s₂).1 (c.1 z + (m : ℂ)) = (Mo.hullChart (fillH X) x₀).1 z)
    (hgood : goodTp c p L = Dv.canonGood X p L) (t : ℝ≥0) :
    stValp c m p L s₂ t = Dv.canonVal X x₀ p L t := by
  classical
  have hval : ∀ t' ∈ goodTp c p L, relValp c m p s₂ t' = (Mo.hullChart (fillH X) x₀).1 (p t') := fun t' ht' => by
    have hX : p t' ∈ H \ fillH X := by rw [hgood] at ht'; exact ht'.2
    exact hΦ _ hX
  unfold stValp Dv.canonVal
  by_cases hg : t ∈ goodTp c p L
  · have hg' : t ∈ Dv.canonGood X p L := hgood ▸ hg
    simp only [hg, hg', ↓reduceIte]
    exact hval t hg
  · have hg' : t ∉ Dv.canonGood X p L := hgood ▸ hg
    simp only [hg, hg', ↓reduceIte]
    rw [← hgood]
    unfold limUnder
    rw [Filter.map_congr (eventually_nhdsWithin_of_forall hval)]

/-- **The run-chart stage curve is the canonical curve.** -/
theorem stCurvep_eq_canonCurve
    (hΦ : ∀ z ∈ H \ fillH X, (stChart s₂).1 (c.1 z + (m : ℂ)) = (Mo.hullChart (fillH X) x₀).1 z)
    (hgood : goodTp c p L = Dv.canonGood X p L) : stCurvep c m p L s₂ = Dv.canonCurve X x₀ p L := by
  funext u
  unfold stCurvep Dv.canonCurve
  exact stValp_eq_canonVal hΦ hgood _

/-- **A driven canonical curve reads `0` at the start along the good times.** -/
theorem tendsto_canon_zero (hF : IsDrivenCurve (Dv.canonCurve X x₀ p L)) :
    Tendsto (fun t => (Mo.hullChart (fillH X) x₀).1 (p t))
      (𝓝[Dv.canonGood X p L ∩ {t | (t : ℝ≥0∞) < L}] 0) (𝓝 0) := by
  classical
  rcases eq_or_ne L 0 with hL0 | hL0
  · have he : Dv.canonGood X p L ∩ {t : ℝ≥0 | (t : ℝ≥0∞) < L} = ∅ := by
      ext t; simp [hL0]
    rw [he, nhdsWithin_empty]; exact tendsto_bot
  have hlt : ∀ t : ℝ≥0, (t : ℝ≥0∞) < L → L ≠ ⊤ → (t : ℝ) < L.toReal := fun t ht hL => by
    have := ENNReal.toReal_strict_mono hL ht
    simpa using this
  -- the parameter of an actual time before the lifetime
  set u : ℝ≥0 → ℝ := fun t => if L = ⊤ then (t : ℝ) else (t : ℝ) / (L.toReal - t) with hudef
  have hu0 : u 0 = 0 := by simp [hudef]
  have huc : ContinuousWithinAt u {t : ℝ≥0 | (t : ℝ≥0∞) < L} 0 := by
    by_cases hL : L = ⊤
    · simp only [hudef, hL, ↓reduceIte]; exact NNReal.continuous_coe.continuousWithinAt
    · simp only [hudef, hL, ↓reduceIte]
      have hLpos : 0 < L.toReal - ((0 : ℝ≥0) : ℝ) := by
        rw [NNReal.coe_zero, sub_zero]; exact ENNReal.toReal_pos hL0 hL
      exact (NNReal.continuous_coe.continuousAt.div (continuous_const.sub NNReal.continuous_coe).continuousAt
        hLpos.ne').continuousWithinAt
  have hval : ∀ t ∈ Dv.canonGood X p L ∩ {t | (t : ℝ≥0∞) < L},
      (Mo.hullChart (fillH X) x₀).1 (p t) = Dv.canonCurve X x₀ p L (u t) := fun t ht => by
    have hcv : Dv.canonVal X x₀ p L t = (Mo.hullChart (fillH X) x₀).1 (p t) := by
      unfold Dv.canonVal; simp only [ht.1, ↓reduceIte]
    rw [← hcv]
    unfold Dv.canonCurve
    by_cases hL : L = ⊤
    · simp only [hudef, hL, ↓reduceIte, Real.toNNReal_coe]
    · have ht' := hlt t ht.2 hL
      simp only [hudef, hL, ↓reduceIte]
      rw [Sec7.PocketLife.clockOf_div_sub (ENNReal.toReal_pos hL0 hL) ht', Real.toNNReal_coe]
  have hnn : ∀ t ∈ Dv.canonGood X p L ∩ {t | (t : ℝ≥0∞) < L}, u t ∈ Ici (0 : ℝ) := fun t ht => by
    by_cases hL : L = ⊤
    · simp only [hudef, hL, ↓reduceIte, mem_Ici]; exact t.2
    · simp only [hudef, hL, ↓reduceIte, mem_Ici]
      exact div_nonneg t.2 (sub_nonneg.2 (hlt t ht.2 hL).le)
  have hρ0 : Tendsto (Dv.canonCurve X x₀ p L) (𝓝[Ici 0] (u 0)) (𝓝 0) := by
    rw [hu0, ← hF.zero]; exact hF.continuousOn 0 self_mem_Ici
  have hut : Tendsto u (𝓝[Dv.canonGood X p L ∩ {t | (t : ℝ≥0∞) < L}] 0) (𝓝[Ici 0] (u 0)) :=
    tendsto_nhdsWithin_iff.2 ⟨(huc.mono inter_subset_right).tendsto, eventually_nhdsWithin_of_forall hnn⟩
  exact (hρ0.comp hut).congr' (eventually_nhdsWithin_of_forall fun t ht => (hval t ht).symm)

/-- **F2a carried to the run chart**: if on `ℍ ∖ fill X` the physical relative chart is the hull chart with offset
`x₁`, the good sets agree, the canonical curve is driven at some offset `x₀`, and the run-chart values tend to `0` at
the start along the good times, then the offsets agree and LIFTSET's stage curve is the canonical curve, hence
driven. -/
theorem isDrivenCurve_stCurvep_of_canon {x₁ : ℝ}
    (hΦ : ∀ z ∈ H \ fillH X, (stChart s₂).1 (c.1 z + (m : ℂ)) = (Mo.hullChart (fillH X) x₁).1 z)
    (hgood : goodTp c p L = Dv.canonGood X p L) (hF : IsDrivenCurve (Dv.canonCurve X x₀ p L))
    (h0 : Tendsto (relValp c m p s₂) (𝓝[goodTp c p L ∩ {t | (t : ℝ≥0∞) < L}] 0) (𝓝 0))
    (hne : (𝓝[goodTp c p L ∩ {t | (t : ℝ≥0∞) < L}] (0 : ℝ≥0)).NeBot) :
    IsDrivenCurve (stCurvep c m p L s₂) ∧ stCurvep c m p L s₂ = Dv.canonCurve X x₀ p L := by
  have hc0 := tendsto_canon_zero hF
  rw [← hgood] at hc0
  have hrel : ∀ t ∈ goodTp c p L ∩ {t | (t : ℝ≥0∞) < L}, relValp c m p s₂ t =
      (Mo.hullChart (fillH X) x₀).1 (p t) + ((x₀ - x₁ : ℝ) : ℂ) := fun t ht => by
    have hX : p t ∈ H \ fillH X := by rw [hgood] at ht; exact ht.1.2
    unfold relValp liftPt
    rw [hΦ _ hX, Mo.hullChart_fwd, Mo.hullChart_fwd]
    push_cast; ring
  have h1 : Tendsto (relValp c m p s₂) (𝓝[goodTp c p L ∩ {t | (t : ℝ≥0∞) < L}] 0)
      (𝓝 (0 + ((x₀ - x₁ : ℝ) : ℂ))) :=
    (hc0.add_const _).congr' (eventually_nhdsWithin_of_forall fun t ht => (hrel t ht).symm)
  have hx : ((x₀ - x₁ : ℝ) : ℂ) = 0 := by
    rw [zero_add] at h1; exact tendsto_nhds_unique h1 h0
  have hx' : x₁ = x₀ := by
    have := congrArg Complex.re hx
    simp at this; linarith
  subst hx'
  have heq := stCurvep_eq_canonCurve hΦ hgood
  exact ⟨heq ▸ hF, heq⟩

/-- **The domain clause from the physical domain identity**: a point off `fill X` lifts into the relative chart's
domain, when the physical relative chart `Mo.physRelChart c c₁ m` has domain `ℍ ∖ fill X`. -/
theorem liftPt_mem_of_phys {c₁ : Chart} (hΦ : (Mo.physRelChart c c₁ m).2.1 '' H = H \ fillH X)
    (hc1 : ∀ w ∈ H, c.1 (c.2.1 w) = w) (hc₁ : ∀ y ∈ H, c₁.2.1 y ∈ H) {z : ℂ} (hz : z ∈ H \ fillH X) :
    liftPt c m z ∈ c₁.2.1 '' H := by
  rw [← hΦ] at hz
  obtain ⟨y, hy, hyz⟩ := hz
  have hw : c₁.2.1 y - (m : ℂ) ∈ H := by
    show 0 < (c₁.2.1 y - (m : ℂ)).im
    simpa using (show (0 : ℝ) < (c₁.2.1 y).im from hc₁ y hy)
  refine ⟨y, hy, ?_⟩
  rw [← hyz, Mo.physRelChart_inv, liftPt, hc1 _ hw, sub_add_cancel]

/-- **The stage domain clause at a lockstep stage**: if the good points of the piece are off `fill X` (the piece stays
in the unexplored domain of the retained union), every lifted good point is in the relative chart's domain. -/
theorem stage_dom_of_phys (hΦ : (Mo.physRelChart c (stChart s₂) m).2.1 '' H = H \ fillH X)
    (hc1 : ∀ w ∈ H, c.1 (c.2.1 w) = w) (hcH : ∀ w ∈ H, c.2.1 w ∈ H) (hc₂ : ∀ y ∈ H, (stChart s₂).2.1 y ∈ H)
    (hoff : ∀ t ∈ goodTp c p L, p t ∉ fillH X) :
    ∀ t ∈ goodTp c p L, liftPt c m (p t) ∈ (stChart s₂).2.1 '' H := fun t ht => by
  obtain ⟨w, hw, hwe⟩ := ht.2
  have hpH : p t ∈ H := by rw [← hwe]; exact hcH w hw
  exact liftPt_mem_of_phys hΦ hc1 hc₂ ⟨hpH, hoff t ht⟩

/-- **A lockstep stage's relative facts from F2a (finite piece)**: with the physical domain identity (the run chart
reads the hull chart of the retained union `X` with offset `x₁`, and its domain is `ℍ ∖ fill X`), the piece's good
points off `fill X`, F2a's canonical drivenness at some offset, the run-chart values tending to `0` at the start, the
canonical curve converging at `∞` inside `ℍ̄`, and the relative run chart's generic facts. -/
theorem stageRelFinP_of_canon {x₁ : ℝ} {e₂ : Drv}
    (hΦ : ∀ z ∈ H \ fillH X, (stChart s₂).1 (c.1 z + (m : ℂ)) = (Mo.hullChart (fillH X) x₁).1 z)
    (hΦd : (Mo.physRelChart c (stChart s₂) m).2.1 '' H = H \ fillH X)
    (hgood : goodTp c p L = Dv.canonGood X p L) (hF : IsDrivenCurve (Dv.canonCurve X x₀ p L))
    (h0 : Tendsto (relValp c m p s₂) (𝓝[goodTp c p L ∩ {t | (t : ℝ≥0∞) < L}] 0) (𝓝 0))
    (hne : (𝓝[goodTp c p L ∩ {t | (t : ℝ≥0∞) < L}] (0 : ℝ≥0)).NeBot)
    {z : ℂ} (hz : Tendsto (Dv.canonCurve X x₀ p L) atTop (𝓝 z))
    (hHbar : ∀ u, 0 ≤ u → Dv.canonCurve X x₀ p L u ∈ Hbar)
    (he₂ : e₂.2 = capLife (stCurvep c m p L s₂))
    (hgen : ∀ T < capLife (stCurvep c m p L s₂), IsGeneratingTrace e₂.1 T (capTrace (stCurvep c m p L s₂)))
    (hreg : IsRegularDriver e₂) (hc1 : ∀ w ∈ H, c.1 (c.2.1 w) = w) (hcH' : ∀ w ∈ H, c.2.1 w ∈ H)
    (hB : HasBdryLimits (stChart s₂).2.1) (hcH₂ : ContinuousOn (stChart s₂).2.1 H)
    (hc1₂ : ∀ w ∈ H, (stChart s₂).1 ((stChart s₂).2.1 w) = w) (hc₂ : ∀ y ∈ H, (stChart s₂).2.1 y ∈ H) :
    IsDrivenCurve (stCurvep c m p L s₂) ∧ StageRelFinP c m p L s₂ e₂ := by
  obtain ⟨hdr, heq⟩ := isDrivenCurve_stCurvep_of_canon hΦ hgood hF h0 hne
  have hoff : ∀ t ∈ goodTp c p L, p t ∉ fillH X := fun t ht => by
    rw [hgood] at ht; exact ht.2.2
  refine ⟨hdr, stageRelFinP_of hdr he₂ hgen hreg (heq ▸ hz) (heq ▸ hHbar) hB hcH₂ hc1₂ ?_⟩
  exact stage_dom_of_phys hΦd hc1 hcH' hc₂ hoff

/-- **A lockstep stage's relative facts from F2a (infinite piece)**, given transience, an infinite capacity lifetime
and the relative chart's boundary map within bounded distance of the identity. -/
theorem stageRelInfP_of_canon {x₁ : ℝ} {e₂ : Drv}
    (hΦ : ∀ z ∈ H \ fillH X, (stChart s₂).1 (c.1 z + (m : ℂ)) = (Mo.hullChart (fillH X) x₁).1 z)
    (hΦd : (Mo.physRelChart c (stChart s₂) m).2.1 '' H = H \ fillH X)
    (hgood : goodTp c p L = Dv.canonGood X p L) (hF : IsDrivenCurve (Dv.canonCurve X x₀ p L))
    (h0 : Tendsto (relValp c m p s₂) (𝓝[goodTp c p L ∩ {t | (t : ℝ≥0∞) < L}] 0) (𝓝 0))
    (hne : (𝓝[goodTp c p L ∩ {t | (t : ℝ≥0∞) < L}] (0 : ℝ≥0)).NeBot)
    (htr : Tendsto (fun u => ‖Dv.canonCurve X x₀ p L u‖) atTop atTop)
    (htop : capLife (Dv.canonCurve X x₀ p L) = ⊤)
    (hHbar : ∀ u, 0 ≤ u → Dv.canonCurve X x₀ p L u ∈ Hbar)
    (he₂ : e₂.2 = capLife (stCurvep c m p L s₂)) (hreg : IsRegularDriver e₂) (hc1 : ∀ w ∈ H, c.1 (c.2.1 w) = w)
    (hcH' : ∀ w ∈ H, c.2.1 w ∈ H) (hB : HasBdryLimits (stChart s₂).2.1) {C : ℝ}
    (hC : ∀ q ∈ Hbar, ‖extendFrom H (stChart s₂).2.1 q - q‖ ≤ C) (hcH₂ : ContinuousOn (stChart s₂).2.1 H)
    (hc1₂ : ∀ w ∈ H, (stChart s₂).1 ((stChart s₂).2.1 w) = w) (hc₂ : ∀ y ∈ H, (stChart s₂).2.1 y ∈ H) :
    IsDrivenCurve (stCurvep c m p L s₂) ∧ StageRelInfP c m p L s₂ e₂ := by
  obtain ⟨hdr, heq⟩ := isDrivenCurve_stCurvep_of_canon hΦ hgood hF h0 hne
  have hoff : ∀ t ∈ goodTp c p L, p t ∉ fillH X := fun t ht => by
    rw [hgood] at ht; exact ht.2.2
  refine ⟨hdr, stageRelInfP_of hdr he₂ hreg (heq ▸ htop) (heq ▸ htr) (heq ▸ hHbar) hB hC hcH₂ hc1₂ ?_⟩
  exact stage_dom_of_phys hΦd hc1 hcH' hc₂ hoff

end InteractingSLE.Theorem14.SB.Lk
