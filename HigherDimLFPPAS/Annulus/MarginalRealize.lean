import HigherDimLFPPAS.Annulus.MarginalScale
import HigherDimLQGMetric.Select.Internal
import HigherDimLQGMetric.DGZ.FunctionalsMeas
import HigherDimLQGMetric.Field.LGFPlusCont

/-!
# Lemma 3.2, marginal part — Step 2: realization of `Ẽ` on the pinned field (packet L32p)

Source: `planning/audits/MA1-sections-1-3.md` Details A10.3 (realization): the rescaled event `Ẽ` (`l32pUnitGood`) is a
measurable condition on pairs of length metrics (countable reductions by continuity of internal metrics on open sets,
`ContMetric.continuousOn_internal`; Borel versions of internal metrics, `HigherDimLQGMetric.measurable_internal`), so
equality in law of the rescaled pair (`Core.PairLaw`) transfers its probability to the pinned field `h`.

* `l32p_measurable_MepsR`: `g ↦ 𝔐_{ε,ε/r}(g)` is measurable (an LFPP metric of a field that is continuous and
  measurable in `g`; `DGZ.measurable_continuousMap_of_eq_lfppMetric`). Needed because Mathlib's `Measure.map` of a
  non-a.e.-measurable map is a Dirac mass, so `PairLaw`'s equality alone does not make the recentred pair measurable.
* `l32p_exists_measurable_unitGood`: a measurable `B` with `(G, G') ∈ B ↔ Ẽ(G, G')` for length metrics.
* `l32p_prob_eq_of_map_eq`: the abstract law transfer; `l32p_prob_unit_eq`: `P[Ẽ(D_g, 𝔐(g))] = P[Ẽ(D_h, 𝔐(h))]`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace HigherDimLFPPAS.Annulus

open HigherDimLFPPAS.Core HigherDimLQGMetric
open HigherDimLFPP (Rd)

variable {d : ℕ}

/-! ### Measurability of the rescaled localized metric -/

/-- `g ↦ 𝔐_{ε,ε/r}(g)` is measurable (smooth kernel, positive radius, positive normalizer). -/
theorem l32p_measurable_MepsR {κ : Rd d → ℝ} {ξ ε r : ℝ}
    (hK : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (convKernel κ)) (hs : 0 < locRad ε / r)
    (ha : 0 < aEps κ ξ (ε / r)) :
    Measurable (fun g : DistRd d => MepsR κ ξ ε r g) := by
  have hcont : ∀ g : DistRd d, Continuous (locFieldR κ ε r g) := l32p_continuous_locFieldR hK hs
  have hval : Measurable (fun g : DistRd d => (MepsR κ ξ ε r g).1) := by
    refine DGZ.measurable_continuousMap_of_eq_lfppMetric (H := fun x g => locFieldR κ ε r g x)
      (fun g => hcont g) (fun x => ?_) ξ (aEps κ ξ (ε / r))⁻¹ (fun g p => ?_)
    · unfold locFieldR
      exact measurable_const.mul (measurable_distOn_apply _)
    · rw [l32p_MepsR_apply (hcont g) ha]
      rfl
  exact hval.subtype_mk

/-! ### Dense sequences and countable reductions -/

/-- A nonempty subset of a second-countable space has a dense sequence. -/
theorem l32p_exists_denseSeq {X : Type*} [TopologicalSpace X] [SecondCountableTopology X]
    {S : Set X} (hS : S.Nonempty) :
    ∃ q : ℕ → X, (∀ n, q n ∈ S) ∧ S ⊆ closure (range q) := by
  have : Nonempty S := hS.to_subtype
  refine ⟨fun n => (TopologicalSpace.denseSeq S n : X), fun n => (TopologicalSpace.denseSeq S n).2, ?_⟩
  intro p hp
  rw [_root_.mem_closure_iff]
  intro o ho hpo
  obtain ⟨n, hn⟩ := (TopologicalSpace.denseRange_denseSeq S).exists_mem_open
    (ho.preimage continuous_subtype_val) ⟨⟨p, hp⟩, hpo⟩
  exact ⟨_, hn, n, rfl⟩

/-- An inequality between two functions continuous on `S` that holds along a dense sequence of `S` holds on `S`. -/
theorem l32p_le_of_dense {X : Type*} [TopologicalSpace X] {f g : X → ℝ≥0∞} {S : Set X}
    (hf : ContinuousOn f S) (hg : ContinuousOn g S) {ι : Type*} {q : ι → X} (hq : ∀ n, q n ∈ S)
    (hdense : S ⊆ closure (range q)) (hle : ∀ n, f (q n) ≤ g (q n)) {p : X} (hp : p ∈ S) :
    f p ≤ g p := by
  let H : X → ℝ≥0∞ × ℝ≥0∞ := fun p => (f p, g p)
  have hH : ContinuousOn H S := hf.prodMk hg
  have hqS : range q ⊆ S := by
    rintro x ⟨n, rfl⟩
    exact hq n
  have hmem : H p ∈ closure (H '' range q) :=
    ContinuousWithinAt.mem_closure_image ((hH p hp).mono hqS) (hdense hp)
  have hclosed : IsClosed {x : ℝ≥0∞ × ℝ≥0∞ | x.1 ≤ x.2} :=
    isClosed_le continuous_fst continuous_snd
  have hrel : H p ∈ {x : ℝ≥0∞ × ℝ≥0∞ | x.1 ≤ x.2} := by
    apply closure_minimal ?_ hclosed hmem
    rintro _ ⟨x, ⟨n, rfl⟩, rfl⟩
    exact hle n
  exact hrel

theorem l32p_mem_ann_zero {x : Rd d} {a b : ℝ} : x ∈ ann 0 a b ↔ a < ‖x‖ ∧ ‖x‖ < b := by
  change a < ‖x - 0‖ ∧ ‖x - 0‖ < b ↔ _
  rw [sub_zero]

theorem l32p_mem_annCl_zero {x : Rd d} {a b : ℝ} : x ∈ annCl 0 a b ↔ a ≤ ‖x‖ ∧ ‖x‖ ≤ b := by
  change a ≤ ‖x - 0‖ ∧ ‖x - 0‖ ≤ b ↔ _
  rw [sub_zero]

/-- The radii of `Ẽ` lie in the annuli where its internal metrics are taken. -/
theorem l32p_sphere_subset_ann {t a b : ℝ} (hat : a < t) (htb : t < b) :
    sphere (0 : Rd d) t ⊆ ann 0 a b := by
  intro x hx
  rw [mem_sphere_zero_iff_norm] at hx
  rw [l32p_mem_ann_zero, hx]
  exact ⟨hat, htb⟩

/-- Connection pairs of `Ẽ` (with `b ≤ 1/4`) lie in `A_{1/4,2}²`, in fact in `Ā_{1/2,3/2}²`. -/
theorem l32p_conn_mem {x w : Rd d} {b : ℝ} (hb4 : b ≤ 1 / 4) (hx : x ∈ annCl (0 : Rd d) (3 / 4) 1)
    (hw : w ∈ ball x b) : w ∈ annCl (0 : Rd d) (1 / 2) (3 / 2) := by
  rw [l32p_mem_annCl_zero] at hx ⊢
  rw [mem_ball, dist_eq_norm] at hw
  have h1 : ‖x‖ ≤ ‖w‖ + ‖w - x‖ := by
    calc ‖x‖ = ‖w - (w - x)‖ := by rw [sub_sub_cancel]
      _ ≤ ‖w‖ + ‖w - x‖ := norm_sub_le _ _
  have h2 : ‖w‖ ≤ ‖x‖ + ‖w - x‖ := by
    calc ‖w‖ = ‖x + (w - x)‖ := by rw [add_sub_cancel]
      _ ≤ ‖x‖ + ‖w - x‖ := norm_add_le _ _
  constructor <;> linarith [hx.1, hx.2]

theorem l32p_annCl_subset_ann {a b a' b' : ℝ} (ha : a' < a) (hb : b < b') :
    annCl (0 : Rd d) a b ⊆ ann 0 a' b' := by
  intro x hx
  rw [l32p_mem_annCl_zero] at hx
  rw [l32p_mem_ann_zero]
  exact ⟨lt_of_lt_of_le ha hx.1, lt_of_le_of_lt hx.2 hb⟩

theorem l32p_continuousOn_const_mul {X : Type*} [TopologicalSpace X] {S : Set X} {f : X → ℝ≥0∞}
    (a : ℝ) (hf : ContinuousOn f S) : ContinuousOn (fun p => ENNReal.ofReal a * f p) S :=
  (ENNReal.continuous_const_mul ENNReal.ofReal_ne_top).comp_continuousOn hf

/-! ### `Ẽ` is a measurable condition on pairs of length metrics -/

/-- **`Ẽ` is measurable on length pairs** (MA1 A10.3): for `0 < b ≤ 1/4` there is a measurable
`B ⊆ ContMetric d × ContMetric d` with `(G, G') ∈ B ↔ Ẽ(G, G'; A, η, b)` whenever `G, G'` are length metrics. The
quantifiers over spheres, the connection pairs and the infima defining the set distances are reduced to dense
sequences by continuity of internal metrics on open sets; the internal metrics are replaced by their Borel versions. -/
theorem l32p_exists_measurable_unitGood (hd : 1 ≤ d) (A η : ℝ) {b : ℝ} (hb : 0 < b)
    (hb4 : b ≤ 1 / 4) :
    ∃ B : Set (ContMetric d × ContMetric d), MeasurableSet B ∧
      ∀ G G' : ContMetric d, G.IsLength → G'.IsLength →
        ((G, G') ∈ B ↔ l32pUnitGood G G' A η b) := by
  have hd0 : 0 < d := hd
  have he : ‖HigherDimLFPP.e₁ d‖ = 1 := HigherDimLFPP.norm_e₁ hd0
  have hSi_ne : (sphere (0 : Rd d) (3 / 4)).Nonempty :=
    ⟨(3 / 4 : ℝ) • HigherDimLFPP.e₁ d, by rw [mem_sphere_zero_iff_norm, norm_smul, he]; norm_num⟩
  have hSo_ne : (sphere (0 : Rd d) 1).Nonempty :=
    ⟨HigherDimLFPP.e₁ d, by rw [mem_sphere_zero_iff_norm, he]⟩
  have hS3_ne : {p : Rd d × Rd d | p.1 ∈ annCl (0 : Rd d) (3 / 4) 1 ∧ p.2 ∈ ball p.1 b}.Nonempty :=
    ⟨((3 / 4 : ℝ) • HigherDimLFPP.e₁ d, (3 / 4 : ℝ) • HigherDimLFPP.e₁ d), by
      refine ⟨?_, mem_ball_self hb⟩
      rw [l32p_mem_annCl_zero, norm_smul, he]; norm_num⟩
  obtain ⟨qI, hqI, hdI⟩ := l32p_exists_denseSeq hSi_ne
  obtain ⟨qO, hqO, hdO⟩ := l32p_exists_denseSeq hSo_ne
  obtain ⟨q3, hq3, hd3⟩ := l32p_exists_denseSeq hS3_ne
  obtain ⟨FU, hFU, hFUeq⟩ := measurable_internal (d := d) (isOpen_ann 0 (1 / 4) 2)
  obtain ⟨FV, hFV, hFVeq⟩ := measurable_internal (d := d) (isOpen_ann 0 (1 / 2) (3 / 2))
  obtain ⟨Δ, hΔdef⟩ : ∃ Δ : ContMetric d → ℝ≥0∞, Δ = fun G => ⨅ i, ⨅ j, FU (G, qI i, qO j) :=
    ⟨_, rfl⟩
  obtain ⟨B, hBdef⟩ : ∃ B : Set (ContMetric d × ContMetric d), B = {p |
      (∀ i j, FU (p.2, qI i, qO j) ≤ ENNReal.ofReal (1 + η) * FV (p.1, qI i, qO j)) ∧
      (∀ i j, FU (p.1, qI i, qO j) ≤ ENNReal.ofReal (1 + η) * FV (p.2, qI i, qO j)) ∧
      (∀ i j, FU (p.1, qI i, qI j) ≤ ENNReal.ofReal A * Δ p.1) ∧
      (∀ i j, FU (p.2, qI i, qI j) ≤ ENNReal.ofReal A * Δ p.2) ∧
      (∀ n, FU (p.2, (q3 n).1, (q3 n).2) ≤ ENNReal.ofReal η * Δ p.1) ∧
      (∀ n, FU (p.1, (q3 n).1, (q3 n).2) ≤ ENNReal.ofReal η * Δ p.2)} := ⟨_, rfl⟩
  -- measurability
  have hm1 : ∀ x y : Rd d, Measurable fun p : ContMetric d × ContMetric d => FU (p.1, x, y) :=
    fun x y => hFU.comp (measurable_fst.prodMk measurable_const)
  have hm2 : ∀ x y : Rd d, Measurable fun p : ContMetric d × ContMetric d => FU (p.2, x, y) :=
    fun x y => hFU.comp (measurable_snd.prodMk measurable_const)
  have hn1 : ∀ x y : Rd d, Measurable fun p : ContMetric d × ContMetric d => FV (p.1, x, y) :=
    fun x y => hFV.comp (measurable_fst.prodMk measurable_const)
  have hn2 : ∀ x y : Rd d, Measurable fun p : ContMetric d × ContMetric d => FV (p.2, x, y) :=
    fun x y => hFV.comp (measurable_snd.prodMk measurable_const)
  have hΔ : Measurable Δ := by
    rw [hΔdef]
    exact Measurable.iInf fun i => Measurable.iInf fun j =>
      hFU.comp (measurable_id.prodMk measurable_const)
  have hB : MeasurableSet B := by
    rw [hBdef]
    refine measurableSet_setOfPred.2 ?_
    refine Measurable.and ?_ (Measurable.and ?_ (Measurable.and ?_ (Measurable.and ?_
      (Measurable.and ?_ ?_))))
    · exact Measurable.forall fun i => Measurable.forall fun j =>
        measurableSet_setOfPred.1 (measurableSet_le (hm2 _ _) ((hn1 _ _).const_mul _))
    · exact Measurable.forall fun i => Measurable.forall fun j =>
        measurableSet_setOfPred.1 (measurableSet_le (hm1 _ _) ((hn2 _ _).const_mul _))
    · exact Measurable.forall fun i => Measurable.forall fun j =>
        measurableSet_setOfPred.1 (measurableSet_le (hm1 _ _) ((hΔ.comp measurable_fst).const_mul _))
    · exact Measurable.forall fun i => Measurable.forall fun j =>
        measurableSet_setOfPred.1 (measurableSet_le (hm2 _ _) ((hΔ.comp measurable_snd).const_mul _))
    · exact Measurable.forall fun n =>
        measurableSet_setOfPred.1 (measurableSet_le (hm2 _ _) ((hΔ.comp measurable_fst).const_mul _))
    · exact Measurable.forall fun n =>
        measurableSet_setOfPred.1 (measurableSet_le (hm1 _ _) ((hΔ.comp measurable_snd).const_mul _))
  refine ⟨B, hB, fun G G' hG hG' => ?_⟩
  -- geometry of the sets
  have hSiU : sphere (0 : Rd d) (3 / 4) ⊆ ann 0 (1 / 4) 2 :=
    l32p_sphere_subset_ann (by norm_num) (by norm_num)
  have hSiV : sphere (0 : Rd d) (3 / 4) ⊆ ann 0 (1 / 2) (3 / 2) :=
    l32p_sphere_subset_ann (by norm_num) (by norm_num)
  have hSoU : sphere (0 : Rd d) 1 ⊆ ann 0 (1 / 4) 2 :=
    l32p_sphere_subset_ann (by norm_num) (by norm_num)
  have hSoV : sphere (0 : Rd d) 1 ⊆ ann 0 (1 / 2) (3 / 2) :=
    l32p_sphere_subset_ann (by norm_num) (by norm_num)
  have hS3U : {p : Rd d × Rd d | p.1 ∈ annCl (0 : Rd d) (3 / 4) 1 ∧ p.2 ∈ ball p.1 b} ⊆
      ann 0 (1 / 4) 2 ×ˢ ann 0 (1 / 4) 2 := by
    rintro ⟨x, w⟩ ⟨hx, hw⟩
    exact ⟨l32p_annCl_subset_ann (by norm_num) (by norm_num) hx,
      l32p_annCl_subset_ann (by norm_num) (by norm_num) (l32p_conn_mem hb4 hx hw)⟩
  have hdIO : sphere (0 : Rd d) (3 / 4) ×ˢ sphere (0 : Rd d) 1 ⊆ closure (range (Prod.map qI qO)) := by
    intro p hp
    rw [range_prodMap, closure_prod_eq]
    exact ⟨hdI hp.1, hdO hp.2⟩
  have hdII : sphere (0 : Rd d) (3 / 4) ×ˢ sphere (0 : Rd d) (3 / 4) ⊆
      closure (range (Prod.map qI qI)) := by
    intro p hp
    rw [range_prodMap, closure_prod_eq]
    exact ⟨hdI hp.1, hdI hp.2⟩
  -- the Borel versions agree with the internal metrics, `Δ` with the set distance
  have hΔeq : ∀ K : ContMetric d, K.IsLength →
      Δ K = setDistIn K (ann 0 (1 / 4) 2) (sphere 0 (3 / 4)) (sphere 0 1) := by
    intro K hK
    have hcK := K.continuousOn_internal hK (isOpen_ann (0 : Rd d) (1 / 4) 2)
    apply le_antisymm
    · unfold setDistIn
      refine le_iInf₂ fun x hx => le_iInf₂ fun y hy => ?_
      exact l32p_le_of_dense (f := fun _ => Δ K)
        (g := fun p : Rd d × Rd d => K.internal (ann 0 (1 / 4) 2) p.1 p.2)
        continuousOn_const (hcK.mono (prod_mono hSiU hSoU)) (q := Prod.map qI qO)
        (fun n => ⟨hqI n.1, hqO n.2⟩) hdIO
        (fun n => by
          change Δ K ≤ K.internal (ann 0 (1 / 4) 2) (qI n.1) (qO n.2)
          rw [hFUeq K hK, hΔdef]
          exact (iInf_le _ n.1).trans (iInf_le _ n.2))
        (p := (x, y)) ⟨hx, hy⟩
    · rw [hΔdef]
      refine le_iInf fun i => le_iInf fun j => ?_
      rw [← hFUeq K hK]
      unfold setDistIn
      exact (iInf₂_le (qI i) (hqI i)).trans (iInf₂_le (qO j) (hqO j))
  have hmem : (G, G') ∈ B ↔
      ((∀ i j, G'.internal (ann 0 (1 / 4) 2) (qI i) (qO j) ≤
          ENNReal.ofReal (1 + η) * G.internal (ann 0 (1 / 2) (3 / 2)) (qI i) (qO j)) ∧
        (∀ i j, G.internal (ann 0 (1 / 4) 2) (qI i) (qO j) ≤
          ENNReal.ofReal (1 + η) * G'.internal (ann 0 (1 / 2) (3 / 2)) (qI i) (qO j)) ∧
        (∀ i j, G.internal (ann 0 (1 / 4) 2) (qI i) (qI j) ≤
          ENNReal.ofReal A * setDistIn G (ann 0 (1 / 4) 2) (sphere 0 (3 / 4)) (sphere 0 1)) ∧
        (∀ i j, G'.internal (ann 0 (1 / 4) 2) (qI i) (qI j) ≤
          ENNReal.ofReal A * setDistIn G' (ann 0 (1 / 4) 2) (sphere 0 (3 / 4)) (sphere 0 1)) ∧
        (∀ n, G'.internal (ann 0 (1 / 4) 2) (q3 n).1 (q3 n).2 ≤
          ENNReal.ofReal η * setDistIn G (ann 0 (1 / 4) 2) (sphere 0 (3 / 4)) (sphere 0 1)) ∧
        (∀ n, G.internal (ann 0 (1 / 4) 2) (q3 n).1 (q3 n).2 ≤
          ENNReal.ofReal η * setDistIn G' (ann 0 (1 / 4) 2) (sphere 0 (3 / 4)) (sphere 0 1))) := by
    rw [hBdef, Set.mem_ofPred_eq]
    simp only [hFUeq G hG, hFUeq G' hG', hFVeq G hG, hFVeq G' hG', ← hΔeq G hG, ← hΔeq G' hG']
  rw [hmem]
  have hcGU := G.continuousOn_internal hG (isOpen_ann (0 : Rd d) (1 / 4) 2)
  have hcGV := G.continuousOn_internal hG (isOpen_ann (0 : Rd d) (1 / 2) (3 / 2))
  have hcG'U := G'.continuousOn_internal hG' (isOpen_ann (0 : Rd d) (1 / 4) 2)
  have hcG'V := G'.continuousOn_internal hG' (isOpen_ann (0 : Rd d) (1 / 2) (3 / 2))
  constructor
  · rintro ⟨c1, c2, c3, c4, c5, c6⟩
    refine ⟨fun x hx y hy => ⟨?_, ?_⟩, fun x hx y hy => ⟨?_, ?_⟩, fun x hx w hw => ⟨?_, ?_⟩⟩
    · exact l32p_le_of_dense (f := fun p : Rd d × Rd d => G'.internal (ann 0 (1 / 4) 2) p.1 p.2)
        (g := fun p : Rd d × Rd d =>
          ENNReal.ofReal (1 + η) * G.internal (ann 0 (1 / 2) (3 / 2)) p.1 p.2)
        (hcG'U.mono (prod_mono hSiU hSoU))
        (l32p_continuousOn_const_mul _ (hcGV.mono (prod_mono hSiV hSoV)))
        (q := Prod.map qI qO) (fun n => ⟨hqI n.1, hqO n.2⟩) hdIO (fun n => c1 n.1 n.2)
        (p := (x, y)) ⟨hx, hy⟩
    · exact l32p_le_of_dense (f := fun p : Rd d × Rd d => G.internal (ann 0 (1 / 4) 2) p.1 p.2)
        (g := fun p : Rd d × Rd d =>
          ENNReal.ofReal (1 + η) * G'.internal (ann 0 (1 / 2) (3 / 2)) p.1 p.2)
        (hcGU.mono (prod_mono hSiU hSoU))
        (l32p_continuousOn_const_mul _ (hcG'V.mono (prod_mono hSiV hSoV)))
        (q := Prod.map qI qO) (fun n => ⟨hqI n.1, hqO n.2⟩) hdIO (fun n => c2 n.1 n.2)
        (p := (x, y)) ⟨hx, hy⟩
    · exact l32p_le_of_dense (f := fun p : Rd d × Rd d => G.internal (ann 0 (1 / 4) 2) p.1 p.2)
        (g := fun _ => ENNReal.ofReal A *
          setDistIn G (ann 0 (1 / 4) 2) (sphere 0 (3 / 4)) (sphere 0 1))
        (hcGU.mono (prod_mono hSiU hSiU)) continuousOn_const
        (q := Prod.map qI qI) (fun n => ⟨hqI n.1, hqI n.2⟩) hdII (fun n => c3 n.1 n.2)
        (p := (x, y)) ⟨hx, hy⟩
    · exact l32p_le_of_dense (f := fun p : Rd d × Rd d => G'.internal (ann 0 (1 / 4) 2) p.1 p.2)
        (g := fun _ => ENNReal.ofReal A *
          setDistIn G' (ann 0 (1 / 4) 2) (sphere 0 (3 / 4)) (sphere 0 1))
        (hcG'U.mono (prod_mono hSiU hSiU)) continuousOn_const
        (q := Prod.map qI qI) (fun n => ⟨hqI n.1, hqI n.2⟩) hdII (fun n => c4 n.1 n.2)
        (p := (x, y)) ⟨hx, hy⟩
    · exact l32p_le_of_dense (f := fun p : Rd d × Rd d => G'.internal (ann 0 (1 / 4) 2) p.1 p.2)
        (g := fun _ => ENNReal.ofReal η *
          setDistIn G (ann 0 (1 / 4) 2) (sphere 0 (3 / 4)) (sphere 0 1))
        (hcG'U.mono hS3U) continuousOn_const (q := q3) hq3 hd3 (fun n => c5 n)
        (p := (x, w)) ⟨hx, hw⟩
    · exact l32p_le_of_dense (f := fun p : Rd d × Rd d => G.internal (ann 0 (1 / 4) 2) p.1 p.2)
        (g := fun _ => ENNReal.ofReal η *
          setDistIn G' (ann 0 (1 / 4) 2) (sphere 0 (3 / 4)) (sphere 0 1))
        (hcGU.mono hS3U) continuousOn_const (q := q3) hq3 hd3 (fun n => c6 n)
        (p := (x, w)) ⟨hx, hw⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨fun i j => (h1 _ (hqI i) _ (hqO j)).1, fun i j => (h1 _ (hqI i) _ (hqO j)).2,
      fun i j => (h2 _ (hqI i) _ (hqI j)).1, fun i j => (h2 _ (hqI i) _ (hqI j)).2,
      fun n => (h3 _ (hq3 n).1 _ (hq3 n).2).1, fun n => (h3 _ (hq3 n).1 _ (hq3 n).2).2⟩

/-! ### The law transfer -/

/-- **Abstract realization** (MA1 A10.3): two a.e.-measurable random pairs of metrics with the same law, both pairs of
length metrics almost surely, give the same (outer) probability to a condition that agrees with a measurable set on
length pairs. -/
theorem l32p_prob_eq_of_map_eq {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X Y : Ω → ContMetric d × ContMetric d} (hX : AEMeasurable X P) (hY : AEMeasurable Y P)
    (hlaw : Measure.map X P = Measure.map Y P)
    (hXl : ∀ᵐ ω ∂P, (X ω).1.IsLength ∧ (X ω).2.IsLength)
    (hYl : ∀ᵐ ω ∂P, (Y ω).1.IsLength ∧ (Y ω).2.IsLength)
    {E : ContMetric d → ContMetric d → Prop} {B : Set (ContMetric d × ContMetric d)}
    (hB : MeasurableSet B)
    (hBE : ∀ G G' : ContMetric d, G.IsLength → G'.IsLength → ((G, G') ∈ B ↔ E G G')) :
    P {ω | E (X ω).1 (X ω).2} = P {ω | E (Y ω).1 (Y ω).2} := by
  have h1 : {ω | E (X ω).1 (X ω).2} =ᵐ[P] X ⁻¹' B := by
    filter_upwards [hXl] with ω hω
    exact propext (hBE _ _ hω.1 hω.2).symm
  have h2 : {ω | E (Y ω).1 (Y ω).2} =ᵐ[P] Y ⁻¹' B := by
    filter_upwards [hYl] with ω hω
    exact propext (hBE _ _ hω.1 hω.2).symm
  rw [measure_congr h1, measure_congr h2, ← Measure.map_apply_of_aemeasurable hX hB, hlaw,
    Measure.map_apply_of_aemeasurable hY hB]

/-- **Step 2** (MA1 A10.3): for `0 < ε < 1`, `ε ≤ r ≤ 1`, every centre `z` and `0 < b ≤ 1/4`, the rescaled event has
the same probability for the recentred field `g = recentAff r z h` as for the pinned field `h`. -/
theorem l32p_prob_unit_eq {ξ Q : ℝ} {κ : Rd d → ℝ} {D : DistRd d → ContMetric d}
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistRd d}
    (hS : Setting d ξ Q κ D P h) (hpl : PairLaw κ ξ D P h) {ε r : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hεr : ε ≤ r) (hr1 : r ≤ 1) (z : Rd d) (A η : ℝ) {b : ℝ} (hb : 0 < b) (hb4 : b ≤ 1 / 4) :
    P {ω | l32pUnitGood (D (recentAff r z (h ω))) (MepsR κ ξ ε r (recentAff r z (h ω))) A η b} =
      P {ω | l32pUnitGood (D (h ω)) (MepsR κ ξ ε r (h ω)) A η b} := by
  have hd2 : 2 ≤ d := le_trans (by norm_num) hS.dim
  have hr : 0 < r := lt_of_lt_of_le hε hεr
  have hs : 0 < locRad ε / r := div_pos (l32p_locRad_pos hε hε1) hr
  have har : 0 < aEps κ ξ (ε / r) := hS.seed.aEps_pos ξ (ε / r) (div_pos hε hr)
  have hMm := l32p_measurable_MepsR (ξ := ξ) hS.seed.kernelSmooth hs har
  have hDm : Measurable D := hS.strong.measurable
  have hgN : IsNormalizedLGF (fun ω => recentAff r z (h ω)) P :=
    isNormalizedLGF_recentAff hd2 hS.field.1 hr z
  have hX : Measurable fun ω => (D (recentAff r z (h ω)), MepsR κ ξ ε r (recentAff r z (h ω))) :=
    (hDm.comp hgN.1.measurable).prodMk (hMm.comp hgN.1.measurable)
  have hY : Measurable fun ω => (D (h ω), MepsR κ ξ ε r (h ω)) :=
    (hDm.comp hS.field.1.measurable).prodMk (hMm.comp hS.field.1.measurable)
  obtain ⟨B, hB, hBE⟩ := l32p_exists_measurable_unitGood (le_trans (by norm_num) hS.dim) A η hb hb4
  exact l32p_prob_eq_of_map_eq (E := fun G G' => l32pUnitGood G G' A η b) hX.aemeasurable
    hY.aemeasurable (hpl ε r hε hεr hr1 z).2
    (by
      filter_upwards [hS.strong.length P _ hgN.1.isLGFPlusCont] with ω hω
      exact ⟨hω, l32p_MepsR_isLength κ ξ ε r _⟩)
    (by
      filter_upwards [hS.strong.length P h hS.field.1.isLGFPlusCont] with ω hω
      exact ⟨hω, l32p_MepsR_isLength κ ξ ε r _⟩)
    hB hBE

end HigherDimLFPPAS.Annulus
