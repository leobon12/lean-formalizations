import HigherDimLQGContinuity.LabelEvents.Profile
import HigherDimLQGContinuity.LabelEvents.Source

/-!
# Borel validity of source events (packet Q5; Part B `b:lem-src-meas`(a))

Source: blueprint Part B `b:lem-src-meas`(a) and its proof; planning audit NA2, items 12–13, R8 ("source event of a
label at a field: ∃ arc ∈ ArcSpace, ∃ ℓ ∈ [ℓ₀, ℓ₁], closed conditions in (profiles, arc, ℓ) ⇒ closed in the profiles
(`isClosed_exists_arc`)"); the remark after `b:def-dupper` (the doubled-ball reference holds for all real centres
and radii once it holds for countably many).

**Statement** (`siteSource_borel`). For countably many edges with positive seed radii and closed geometric
predicates, and nonnegative doubled-ball constants and exponents, there is a Borel set
`S ⊆ ContMetric d × ContMetric d` with `(D, E) ∈ S ↔ SiteSource … D E` for all continuous **length** metrics `D, E`.

**Proof.** On length metrics every clause is a condition on internal profiles (`LabelEvents/Profile.lean`):
* `DUpper G W H σ` is equivalent to its restriction to the centres of a dense sequence and rational radii
  (`q5_dUpper_iff_dense`: shrink the ball and use `ρ ↦ H ρ^σ` nondecreasing), and for each such ball the bound is a
  closed condition on the profile of the ball (`q5_measurableSet_forall_internal`);
* the references (R2)–(R4) are closed conditions on the profile on `A`;
* the existence part of (V2) for one edge is the preimage of the closed set `q5_isClosed_edgeArcSet` of pairs of
  profiles on the seed inspection: (a)–(e) are closed relative to `profiles × ArcSpace × [ℓ₀, ℓ₁]` (the profile
  evaluation is continuous at points of the open inspection, which contains the seed shell and its first-exit
  spheres), and the projection along the compact factor is closed (`isClosed_exists_arc_of_inter`).
Countable intersections and `q5_exists_measurableSet_of_len` give the Borel set.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal
open HigherDimLFPP (Rd)

namespace HigherDimLQGContinuity

open HigherDimLQGMetric

variable {d : ℕ}

/-! ## The doubled-ball reference on countably many balls -/

/-- **Rational form of `DUpper`** (remark after `b:def-dupper`): it suffices to check centres of the dense sequence of
`ℝ^d` and rational radii (for `H, σ ≥ 0`; any continuous metric). -/
theorem q5_dUpper_iff_dense {G : ContMetric d} {W : Set (Rd d)} {H σ : ℝ} (hH : 0 ≤ H) (hσ : 0 ≤ σ) :
    DUpper G W H σ ↔ ∀ (n : ℕ) (q : ℚ), 0 < (q : ℝ) →
      closedBall (TopologicalSpace.denseSeq (Rd d) n) (2 * q) ⊆ W →
      ∀ x ∈ ball (TopologicalSpace.denseSeq (Rd d) n) q, ∀ y ∈ ball (TopologicalSpace.denseSeq (Rd d) n) q,
        G.internal (ball (TopologicalSpace.denseSeq (Rd d) n) (2 * q)) x y ≤
          ENNReal.ofReal (H * (q : ℝ) ^ σ) := by
  constructor
  · intro h n q hq hball x hx y hy
    refine le_trans ?_ (h _ _ hq hball)
    unfold diamIn
    exact le_iSup₂_of_le x hx (le_iSup₂_of_le y hy le_rfl)
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
    calc G.internal (ball z (2 * ρ)) x y ≤ G.internal (ball zn (2 * q)) x y := G.internal_anti hsub x y
      _ ≤ ENNReal.ofReal (H * (q : ℝ) ^ σ) :=
          h n q hq0 (hcl.trans (ball_subset_closedBall.trans hball)) x hxn y hyn
      _ ≤ ENNReal.ofReal (H * ρ ^ σ) :=
          ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow hq0.le (by linarith) hσ) hH)

/-! ## Measurable conditions on internal profiles -/

open Classical in
/-- For length metrics, `∀ x ∈ S, ∀ y ∈ T, G(x, y; W) ∈ P x y` with `S, T ⊆ W` and closed sets `P x y` is a
measurable condition. -/
theorem q5_measurableSet_forall_internal {W : Set (Rd d)} (hW : IsOpen W) {S T : Set (Rd d)} (hS : S ⊆ W)
    (hT : T ⊆ W) (P : Rd d → Rd d → Set ℝ≥0∞) (hP : ∀ x y, IsClosed (P x y)) :
    MeasurableSet {G : Q5LenMetric d | ∀ x ∈ S, ∀ y ∈ T, G.1.internal W x y ∈ P x y} := by
  let C : W × W → Set ℝ≥0∞ := fun p =>
    if (p.1 : Rd d) ∈ S ∧ (p.2 : Rd d) ∈ T then P p.1 p.2 else univ
  have hC : ∀ p, IsClosed (C p) := by
    intro p
    dsimp only [C]
    split_ifs
    · exact hP _ _
    · exact isClosed_univ
  have e : {G : Q5LenMetric d | ∀ x ∈ S, ∀ y ∈ T, G.1.internal W x y ∈ P x y} =
      {G | q5Prof hW G ∈ {f : C(W × W, ℝ≥0∞) | ∀ p, f p ∈ C p}} := by
    ext G
    simp only [mem_ofPred_eq]
    constructor
    · intro h p
      dsimp only [C]
      split_ifs with hp
      · exact h p.1 hp.1 p.2 hp.2
      · exact mem_univ _
    · intro h x hx y hy
      have hp := h (⟨x, hS hx⟩, ⟨y, hT hy⟩)
      simp only [C, hx, hy, and_self, ite_true] at hp
      exact hp
  rw [e]
  exact q5_measurableSet_prof_preimage hW (q5_isClosed_forall_mem C hC)

/-- `DUpper` on an arbitrary set is a measurable condition on length metrics (`H, σ ≥ 0`). -/
theorem q5_measurableSet_dUpper (W : Set (Rd d)) {H σ : ℝ} (hH : 0 ≤ H) (hσ : 0 ≤ σ) :
    MeasurableSet {G : Q5LenMetric d | DUpper G.1 W H σ} := by
  have e : {G : Q5LenMetric d | DUpper G.1 W H σ} = ⋂ (n : ℕ) (q : ℚ),
      {G : Q5LenMetric d | 0 < (q : ℝ) → closedBall (TopologicalSpace.denseSeq (Rd d) n) (2 * q) ⊆ W →
        ∀ x ∈ ball (TopologicalSpace.denseSeq (Rd d) n) q, ∀ y ∈ ball (TopologicalSpace.denseSeq (Rd d) n) q,
          G.1.internal (ball (TopologicalSpace.denseSeq (Rd d) n) (2 * q)) x y ≤
            ENNReal.ofReal (H * (q : ℝ) ^ σ)} := by
    ext G
    simp only [mem_iInter, mem_ofPred_eq]
    exact q5_dUpper_iff_dense hH hσ
  rw [e]
  refine MeasurableSet.iInter fun n => MeasurableSet.iInter fun q => ?_
  set zn := TopologicalSpace.denseSeq (Rd d) n
  by_cases hq : 0 < (q : ℝ)
  · by_cases hb : closedBall zn (2 * q) ⊆ W
    · have hsub : ball zn q ⊆ ball zn (2 * q) := ball_subset_ball (by linarith)
      have hm := q5_measurableSet_forall_internal (d := d) isOpen_ball hsub hsub
        (fun _ _ => Iic (ENNReal.ofReal (H * (q : ℝ) ^ σ))) (fun _ _ => isClosed_Iic)
      have hset : {G : Q5LenMetric d | 0 < (q : ℝ) → closedBall zn (2 * q) ⊆ W →
          ∀ x ∈ ball zn q, ∀ y ∈ ball zn q,
            G.1.internal (ball zn (2 * q)) x y ≤ ENNReal.ofReal (H * (q : ℝ) ^ σ)} =
          {G : Q5LenMetric d | ∀ x ∈ ball zn q, ∀ y ∈ ball zn q,
            G.1.internal (ball zn (2 * q)) x y ∈ Iic (ENNReal.ofReal (H * (q : ℝ) ^ σ))} := by
        ext G
        simp only [mem_ofPred_eq, mem_Iic]
        exact ⟨fun h => h hq hb, fun h _ _ => h⟩
      rw [hset]
      exact hm
    · have hset : {G : Q5LenMetric d | 0 < (q : ℝ) → closedBall zn (2 * q) ⊆ W →
          ∀ x ∈ ball zn q, ∀ y ∈ ball zn q,
            G.1.internal (ball zn (2 * q)) x y ≤ ENNReal.ofReal (H * (q : ℝ) ^ σ)} = univ := by
        ext G
        simp only [mem_ofPred_eq, mem_univ, iff_true]
        exact fun _ h => absurd h hb
      rw [hset]
      exact MeasurableSet.univ
  · have hset : {G : Q5LenMetric d | 0 < (q : ℝ) → closedBall zn (2 * q) ⊆ W →
        ∀ x ∈ ball zn q, ∀ y ∈ ball zn q,
          G.1.internal (ball zn (2 * q)) x y ≤ ENNReal.ofReal (H * (q : ℝ) ^ σ)} = univ := by
      ext G
      simp only [mem_ofPred_eq, mem_univ, iff_true]
      exact fun h => absurd h hq
    rw [hset]
    exact MeasurableSet.univ

theorem q5_siteC_subset_siteA : siteC d ⊆ siteA d := by
  intro x hx
  rw [siteA, mem_annA_iff]
  obtain ⟨h1, h2⟩ := hx
  rw [sub_zero] at h1 h2
  constructor <;> linarith

theorem q5_sphere_subset_siteA {a : ℝ} (ha1 : 1 / 2 < a) (ha2 : a < 7 / 2) : sphere (0 : Rd d) a ⊆ siteA d := by
  intro x hx
  rw [mem_sphere_zero_iff_norm] at hx
  rw [siteA, mem_annA_iff, hx]
  exact ⟨ha1, ha2⟩

/-- The site references are a measurable condition on length metrics (`Hup, s ≥ 0`). -/
theorem q5_measurableSet_siteRefs {Hup s Hlo b mc A0 : ℝ} (hHup : 0 ≤ Hup) (hs : 0 ≤ s) :
    MeasurableSet {G : Q5LenMetric d | SiteRefs Hup s Hlo b mc A0 G.1} := by
  have hA : IsOpen (siteA d) := isOpen_annA
  have hC := q5_siteC_subset_siteA (d := d)
  have m2 := q5_measurableSet_forall_internal (d := d) hA hC hC
    (fun x y => Ici (ENNReal.ofReal (Hlo⁻¹ * ‖x - y‖ ^ b))) (fun _ _ => isClosed_Ici)
  have m3 := q5_measurableSet_forall_internal (d := d) hA (q5_sphere_subset_siteA (a := 1) (by norm_num)
    (by norm_num)) (q5_sphere_subset_siteA (a := 3 / 2) (by norm_num) (by norm_num))
    (fun _ _ => Ici (ENNReal.ofReal mc)) (fun _ _ => isClosed_Ici)
  have m4 := q5_measurableSet_forall_internal (d := d) hA (q5_sphere_subset_siteA (a := 5 / 2) (by norm_num)
    (by norm_num)) (q5_sphere_subset_siteA (a := 3) (by norm_num) (by norm_num))
    (fun _ _ => Ici (ENNReal.ofReal mc)) (fun _ _ => isClosed_Ici)
  have m5 := q5_measurableSet_forall_internal (d := d) hA hC hC
    (fun _ _ => Iic (ENNReal.ofReal A0)) (fun _ _ => isClosed_Iic)
  have e : {G : Q5LenMetric d | SiteRefs Hup s Hlo b mc A0 G.1} =
      {G : Q5LenMetric d | DUpper G.1 (siteA d) Hup s} ∩
        ({G : Q5LenMetric d | ∀ x ∈ siteC d, ∀ y ∈ siteC d,
            G.1.internal (siteA d) x y ∈ Ici (ENNReal.ofReal (Hlo⁻¹ * ‖x - y‖ ^ b))} ∩
          ({G : Q5LenMetric d | ∀ x ∈ sphere (0 : Rd d) 1, ∀ y ∈ sphere (0 : Rd d) (3 / 2),
              G.1.internal (siteA d) x y ∈ Ici (ENNReal.ofReal mc)} ∩
            ({G : Q5LenMetric d | ∀ x ∈ sphere (0 : Rd d) (5 / 2), ∀ y ∈ sphere (0 : Rd d) 3,
                G.1.internal (siteA d) x y ∈ Ici (ENNReal.ofReal mc)} ∩
              {G : Q5LenMetric d | ∀ x ∈ siteC d, ∀ y ∈ siteC d,
                G.1.internal (siteA d) x y ∈ Iic (ENNReal.ofReal A0)}))) := by
    ext G
    simp only [SiteRefs, mem_inter_iff, mem_ofPred_eq, mem_Ici, mem_Iic, setDistIn, le_iInf_iff, diamIn,
      iSup_le_iff]
  rw [e]
  exact (q5_measurableSet_dUpper (siteA d) hHup hs).inter (m2.inter (m3.inter (m4.inter m5)))

/-! ## Relative closedness -/

section RelClosed

variable {Y : Type*} [TopologicalSpace Y] {F : Set Y}

theorem q5_isClosed_inter_le (hF : IsClosed F) {φ ψ : Y → ℝ≥0∞} (hφ : ContinuousOn φ F)
    (hψ : ContinuousOn ψ F) : IsClosed (F ∩ {y | φ y ≤ ψ y}) :=
  (hφ.prodMk hψ).preimage_isClosed_of_isClosed hF (isClosed_le continuous_fst continuous_snd)

theorem q5_isClosed_inter_eq (hF : IsClosed F) {φ ψ : Y → ℝ≥0∞} (hφ : ContinuousOn φ F)
    (hψ : ContinuousOn ψ F) : IsClosed (F ∩ {y | φ y = ψ y}) :=
  (hφ.prodMk hψ).preimage_isClosed_of_isClosed hF (isClosed_eq continuous_fst continuous_snd)

theorem q5_isClosed_inter_inter {A B : Set Y} (hA : IsClosed (F ∩ A)) (hB : IsClosed (F ∩ B)) :
    IsClosed (F ∩ (A ∩ B)) := by
  have e : F ∩ (A ∩ B) = (F ∩ A) ∩ (F ∩ B) := by
    ext y
    simp only [mem_inter_iff]
    tauto
  rw [e]
  exact hA.inter hB

theorem q5_isClosed_inter_iInter {ι : Sort*} (hF : IsClosed F) {A : ι → Set Y}
    (hA : ∀ i, IsClosed (F ∩ A i)) : IsClosed (F ∩ ⋂ i, A i) := by
  have e : F ∩ ⋂ i, A i = F ∩ ⋂ i, (F ∩ A i) := by
    ext y
    simp only [mem_inter_iff, mem_iInter]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun i => ⟨h1, h2 i⟩⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun i => (h2 i).2⟩
  rw [e]
  exact hF.inter (isClosed_iInter hA)

end RelClosed

/-- The evaluation of a varying profile at varying points is continuous on a set where the points stay in `W`. -/
theorem q5_continuousOn_ev_comp {Y : Type*} [TopologicalSpace Y] {W : Set (Rd d)} (hW : IsOpen W)
    {F : Set Y} {f : Y → C(W × W, ℝ≥0∞)} {a b : Y → Rd d} (hf : Continuous f) (ha : Continuous a)
    (hb : Continuous b) (haW : ∀ y ∈ F, a y ∈ W) (hbW : ∀ y ∈ F, b y ∈ W) :
    ContinuousOn (fun y => q5Ev (f y) (a y) (b y)) F := by
  intro y hy
  have h1 := q5_continuousAt_ev hW (f y) (haW y hy) (hbW y hy)
  have h2 : ContinuousAt (fun y => (f y, a y, b y)) y := (hf.prodMk (ha.prodMk hb)).continuousAt
  exact (ContinuousAt.comp (g := fun p : C(W × W, ℝ≥0∞) × Rd d × Rd d => q5Ev p.1 p.2.1 p.2.2)
    (f := fun y => (f y, a y, b y)) h1 h2).continuousWithinAt

/-! ## The edge relation and its closed existence set -/

/-- The relation (V2)(a)–(e) between a pair of profiles `(f_D, f_E)` on the seed inspection `W`, an arc and an own
length (the first-exit clause in the form `|u| = r/8`). -/
def q5EdgeRel (W : Set (Rd d)) (d₀ v r : ℝ) (Geo : C(unitInterval, Rd d) → Prop) :
    Set ((C(W × W, ℝ≥0∞) × C(W × W, ℝ≥0∞)) × C(unitInterval, Rd d) × ℝ) :=
  {y | (∀ s t : unitInterval, q5Ev y.1.2 (y.2.1 s) (y.2.1 t) = ENNReal.ofReal (y.2.2 * |(s : ℝ) - t|)) ∧
    ENNReal.ofReal d₀ ≤ q5Ev y.1.1 (y.2.1 0) (y.2.1 1) ∧
    ENNReal.ofReal y.2.2 ≤ ENNReal.ofReal (1 + 4 * v) * q5Ev y.1.1 (y.2.1 0) (y.2.1 1) ∧
    (∀ u : Rd d, ‖u‖ = r / 8 → q5Ev y.1.1 (y.2.1 0) (y.2.1 1) ≤ q5Ev y.1.1 (y.2.1 0) (y.2.1 0 + u)) ∧
    Geo y.2.1}

/-- **The existence part of (V2) is closed in the profiles** (`b:lem-src-meas`(a) via `b:lem-arcspace`(b)). -/
theorem q5_isClosed_edgeArcSet {W K : Set (Rd d)} (hW : IsOpen W) (hK : IsCompact K) (hKW : K ⊆ W)
    {A α β ℓ₀ ℓ₁ d₀ v r : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hsph : ∀ x ∈ K, ∀ u : Rd d, ‖u‖ = r / 8 → x + u ∈ W)
    {Geo : C(unitInterval, Rd d) → Prop} (hGeo : IsClosed {γ | Geo γ}) :
    IsClosed {x : C(W × W, ℝ≥0∞) × C(W × W, ℝ≥0∞) |
      ∃ γ ∈ ArcSpace K A α β, ∃ lam ∈ Icc ℓ₀ ℓ₁, (x, γ, lam) ∈ q5EdgeRel W d₀ v r Geo} := by
  refine isClosed_exists_arc_of_inter hK hα hβ _ ?_
  set F : Set ((C(W × W, ℝ≥0∞) × C(W × W, ℝ≥0∞)) × C(unitInterval, Rd d) × ℝ) :=
    univ ×ˢ (ArcSpace K A α β ×ˢ Icc ℓ₀ ℓ₁) with hFdef
  have hF : IsClosed F := isClosed_univ.prod ((isClosed_arcSpace hK.isClosed hβ.le).prod isClosed_Icc)
  have hγW : ∀ t : unitInterval, ∀ y ∈ F, y.2.1 t ∈ W := fun t y hy => hKW (hy.2.1.1 t)
  have hcγ : ∀ t : unitInterval,
      Continuous fun y : (C(W × W, ℝ≥0∞) × C(W × W, ℝ≥0∞)) × C(unitInterval, Rd d) × ℝ => y.2.1 t :=
    fun t => (continuous_eval_const t).comp (continuous_fst.comp continuous_snd)
  have hc1 : Continuous fun y : (C(W × W, ℝ≥0∞) × C(W × W, ℝ≥0∞)) × C(unitInterval, Rd d) × ℝ => y.1.1 :=
    continuous_fst.comp continuous_fst
  have hc2 : Continuous fun y : (C(W × W, ℝ≥0∞) × C(W × W, ℝ≥0∞)) × C(unitInterval, Rd d) × ℝ => y.1.2 :=
    continuous_snd.comp continuous_fst
  have hlam : Continuous fun y : (C(W × W, ℝ≥0∞) × C(W × W, ℝ≥0∞)) × C(unitInterval, Rd d) × ℝ => y.2.2 :=
    continuous_snd.comp continuous_snd
  have hD01 : ContinuousOn (fun y : (C(W × W, ℝ≥0∞) × C(W × W, ℝ≥0∞)) × C(unitInterval, Rd d) × ℝ =>
      q5Ev y.1.1 (y.2.1 0) (y.2.1 1)) F :=
    q5_continuousOn_ev_comp hW hc1 (hcγ 0) (hcγ 1) (hγW 0) (hγW 1)
  -- (a)
  have Ha : IsClosed (F ∩ {y | ∀ s t : unitInterval,
      q5Ev y.1.2 (y.2.1 s) (y.2.1 t) = ENNReal.ofReal (y.2.2 * |(s : ℝ) - t|)}) := by
    simp only [ofPred_forall]
    refine q5_isClosed_inter_iInter hF fun s => q5_isClosed_inter_iInter hF fun t => ?_
    exact q5_isClosed_inter_eq hF (q5_continuousOn_ev_comp hW hc2 (hcγ s) (hcγ t) (hγW s) (hγW t))
      (ENNReal.continuous_ofReal.comp (hlam.mul continuous_const)).continuousOn
  -- (b)
  have Hb : IsClosed (F ∩ {y | ENNReal.ofReal d₀ ≤ q5Ev y.1.1 (y.2.1 0) (y.2.1 1)}) :=
    q5_isClosed_inter_le hF continuousOn_const hD01
  -- (c)
  have Hc : IsClosed (F ∩ {y | ENNReal.ofReal y.2.2 ≤
      ENNReal.ofReal (1 + 4 * v) * q5Ev y.1.1 (y.2.1 0) (y.2.1 1)}) :=
    q5_isClosed_inter_le hF (ENNReal.continuous_ofReal.comp hlam).continuousOn
      ((ENNReal.continuous_const_mul ENNReal.ofReal_ne_top).comp_continuousOn hD01)
  -- (d)
  have Hd : IsClosed (F ∩ {y | ∀ u : Rd d, ‖u‖ = r / 8 →
      q5Ev y.1.1 (y.2.1 0) (y.2.1 1) ≤ q5Ev y.1.1 (y.2.1 0) (y.2.1 0 + u)}) := by
    have e : {y : (C(W × W, ℝ≥0∞) × C(W × W, ℝ≥0∞)) × C(unitInterval, Rd d) × ℝ | ∀ u : Rd d, ‖u‖ = r / 8 →
        q5Ev y.1.1 (y.2.1 0) (y.2.1 1) ≤ q5Ev y.1.1 (y.2.1 0) (y.2.1 0 + u)} =
        ⋂ u : {u : Rd d // ‖u‖ = r / 8},
          {y | q5Ev y.1.1 (y.2.1 0) (y.2.1 1) ≤ q5Ev y.1.1 (y.2.1 0) (y.2.1 0 + u.1)} := by
      ext y
      simp only [mem_ofPred_eq, mem_iInter, Subtype.forall]
    rw [e]
    refine q5_isClosed_inter_iInter hF fun u => q5_isClosed_inter_le hF hD01 ?_
    exact q5_continuousOn_ev_comp hW hc1 (hcγ 0) ((hcγ 0).add continuous_const) (hγW 0)
      (fun y hy => hsph _ (hy.2.1.1 0) u.1 u.2)
  -- (e)
  have He : IsClosed (F ∩ {y : (C(W × W, ℝ≥0∞) × C(W × W, ℝ≥0∞)) × C(unitInterval, Rd d) × ℝ |
      Geo y.2.1}) :=
    hF.inter (hGeo.preimage (continuous_fst.comp continuous_snd))
  have e : q5EdgeRel W d₀ v r Geo ∩ F =
      F ∩ ({y | ∀ s t : unitInterval,
          q5Ev y.1.2 (y.2.1 s) (y.2.1 t) = ENNReal.ofReal (y.2.2 * |(s : ℝ) - t|)} ∩
        ({y | ENNReal.ofReal d₀ ≤ q5Ev y.1.1 (y.2.1 0) (y.2.1 1)} ∩
          ({y | ENNReal.ofReal y.2.2 ≤ ENNReal.ofReal (1 + 4 * v) * q5Ev y.1.1 (y.2.1 0) (y.2.1 1)} ∩
            ({y | ∀ u : Rd d, ‖u‖ = r / 8 →
                q5Ev y.1.1 (y.2.1 0) (y.2.1 1) ≤ q5Ev y.1.1 (y.2.1 0) (y.2.1 0 + u)} ∩
              {y | Geo y.2.1})))) := by
    rw [inter_comm]
    rfl
  rw [e]
  exact q5_isClosed_inter_inter Ha (q5_isClosed_inter_inter Hb (q5_isClosed_inter_inter Hc
    (q5_isClosed_inter_inter Hd He)))

/-- For length metrics, the existence part of (V2) is the membership of the pair of seed profiles in the closed set
of `q5_isClosed_edgeArcSet`. -/
theorem q5_edgeSource_iff {D E : ContMetric d} (hD : D.IsLength) (hE : E.IsLength)
    {HE sE A α β ℓ₀ ℓ₁ d₀ v : ℝ} {c : Rd d} {r : ℝ} (hr : 0 < r) {Geo : C(unitInterval, Rd d) → Prop} :
    EdgeSource HE sE A α β ℓ₀ ℓ₁ d₀ v c r Geo D E ↔
      DUpper E (srcSeedA c r) HE sE ∧
        (q5Prof (isOpen_srcSeedA c hr) ⟨D, hD⟩, q5Prof (isOpen_srcSeedA c hr) ⟨E, hE⟩) ∈
          {x : C(srcSeedA c r × srcSeedA c r, ℝ≥0∞) × C(srcSeedA c r × srcSeedA c r, ℝ≥0∞) |
            ∃ γ ∈ ArcSpace (srcSeedK c r) A α β, ∃ lam ∈ Icc ℓ₀ ℓ₁,
              (x, γ, lam) ∈ q5EdgeRel (srcSeedA c r) d₀ v r Geo} := by
  simp only [EdgeSource, q5EdgeRel, mem_ofPred_eq, q5Ev_prof]
  refine and_congr Iff.rfl (exists_congr fun γ => and_congr Iff.rfl (exists_congr fun lam =>
    and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl (and_congr ?_ Iff.rfl))))))
  constructor
  · intro h u hu
    exact h (γ 0 + u) (by rw [add_sub_cancel_left]; exact hu)
  · intro h w hw
    have := h (w - γ 0) hw
    rwa [add_sub_cancel] at this

/-- One edge's validity is a measurable condition on pairs of length metrics. -/
theorem q5_measurableSet_edgeSource {HE sE A α β ℓ₀ ℓ₁ d₀ v : ℝ} (hHE : 0 ≤ HE) (hsE : 0 ≤ sE)
    (hα : 0 < α) (hβ : 0 < β) (c : Rd d) {r : ℝ} (hr : 0 < r) {Geo : C(unitInterval, Rd d) → Prop}
    (hGeo : IsClosed {γ | Geo γ}) :
    MeasurableSet {p : Q5LenMetric d × Q5LenMetric d |
      EdgeSource HE sE A α β ℓ₀ ℓ₁ d₀ v c r Geo p.1.1 p.2.1} := by
  have hW := isOpen_srcSeedA c hr
  have hT := q5_isClosed_edgeArcSet (A := A) (ℓ₀ := ℓ₀) (ℓ₁ := ℓ₁) (d₀ := d₀) (v := v) hW
    (isCompact_srcSeedK c r) (srcSeedK_subset_srcSeedA c hr) hα hβ
    (fun x hx u hu => mem_srcSeedA_of_norm_sub hr hx (by rw [add_sub_cancel_left]; exact hu)) hGeo
  have m1 : MeasurableSet {p : Q5LenMetric d × Q5LenMetric d | DUpper p.2.1 (srcSeedA c r) HE sE} :=
    measurable_snd (q5_measurableSet_dUpper (srcSeedA c r) hHE hsE)
  have m2 := q5_measurableSet_prof_pair_preimage hW hT
  have e : {p : Q5LenMetric d × Q5LenMetric d | EdgeSource HE sE A α β ℓ₀ ℓ₁ d₀ v c r Geo p.1.1 p.2.1} =
      {p : Q5LenMetric d × Q5LenMetric d | DUpper p.2.1 (srcSeedA c r) HE sE} ∩
        {p : Q5LenMetric d × Q5LenMetric d | (q5Prof hW p.1, q5Prof hW p.2) ∈
          {x : C(srcSeedA c r × srcSeedA c r, ℝ≥0∞) × C(srcSeedA c r × srcSeedA c r, ℝ≥0∞) |
            ∃ γ ∈ ArcSpace (srcSeedK c r) A α β, ∃ lam ∈ Icc ℓ₀ ℓ₁,
              (x, γ, lam) ∈ q5EdgeRel (srcSeedA c r) d₀ v r Geo}} := by
    ext p
    rw [mem_ofPred_eq, q5_edgeSource_iff p.1.2 p.2.2 hr]
    rfl
  rw [e]
  exact m1.inter m2

/-! ## Borel validity -/

/-- **Borel validity of source events** (Part B `b:lem-src-meas`(a); part (ii) of `SiteCertOfLabel`): for countably
many edges with positive seed radii and closed geometric predicates, and nonnegative doubled-ball constants and
exponents, there is a Borel set `S` of pairs of continuous metrics with `(D, E) ∈ S ↔ SiteSource … D E` for all
continuous length metrics `D, E`. -/
theorem siteSource_borel {Hup s Hlo b mc A0 HE sE A α β ℓ₀ ℓ₁ d₀ v : ℝ} (hHup : 0 ≤ Hup) (hs : 0 ≤ s)
    (hHE : 0 ≤ HE) (hsE : 0 ≤ sE) (hα : 0 < α) (hβ : 0 < β) {Edge : Type*} [Countable Edge]
    (c : Edge → Rd d) (r : Edge → ℝ) (hr : ∀ e, 0 < r e) (Geo : Edge → C(unitInterval, Rd d) → Prop)
    (hGeo : ∀ e, IsClosed {γ | Geo e γ}) :
    ∃ S : Set (ContMetric d × ContMetric d), MeasurableSet S ∧
      ∀ D E : ContMetric d, D.IsLength → E.IsLength →
        ((D, E) ∈ S ↔ SiteSource Hup s Hlo b mc A0 HE sE A α β ℓ₀ ℓ₁ d₀ v c r Geo D E) := by
  refine q5_exists_measurableSet_of_len ?_
  have e : {p : Q5LenMetric d × Q5LenMetric d |
      SiteSource Hup s Hlo b mc A0 HE sE A α β ℓ₀ ℓ₁ d₀ v c r Geo p.1.1 p.2.1} =
      {p : Q5LenMetric d × Q5LenMetric d | SiteRefs Hup s Hlo b mc A0 p.1.1} ∩
        ⋂ e, {p : Q5LenMetric d × Q5LenMetric d |
          EdgeSource HE sE A α β ℓ₀ ℓ₁ d₀ v (c e) (r e) (Geo e) p.1.1 p.2.1} := by
    ext p
    simp only [SiteSource, mem_inter_iff, mem_iInter, mem_ofPred_eq]
  rw [e]
  exact (measurable_fst (q5_measurableSet_siteRefs hHup hs)).inter
    (MeasurableSet.iInter fun e => q5_measurableSet_edgeSource hHE hsE hα hβ (c e) (hr e) (hGeo e))

end HigherDimLQGContinuity
