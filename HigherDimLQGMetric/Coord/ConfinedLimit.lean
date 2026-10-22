import HigherDimLQGMetric.Coord.RecoveryFull
import HigherDimLQGMetric.Metric.Lemma21

/-! # Compactness and lower semicontinuity for confined weighted distances -/

set_option autoImplicit false

noncomputable section

open Set Filter Topology BoundedContinuousFunction unitInterval
open scoped ENNReal

namespace HigherDimLQGMetric

theorem compact_positive_weight_bounds
    {X : Type*} [TopologicalSpace X] {K : Set X}
    (hK : IsCompact K) {w : X → ℝ} (hw : ContinuousOn w K)
    (hpos : ∀ x ∈ K, 0 < w x) :
    ∃ m M : ℝ, 0 < m ∧ 0 ≤ M ∧
      ∀ x ∈ K, m ≤ w x ∧ w x ≤ M := by
  obtain ⟨m, hm, hlow⟩ := hK.exists_forall_le' hw hpos
  obtain ⟨M₀, hM₀⟩ := (hK.image_of_continuousOn hw).bddAbove
  refine ⟨m, max 0 M₀, hm, le_max_left _ _, ?_⟩
  intro x hx
  exact ⟨hlow x hx, (hM₀ ⟨x, hx, rfl⟩).trans (le_max_right _ _)⟩

theorem weylDistOnWith_anti_set {X : Type*} [PseudoEMetricSpace X]
    (E : X → X → ℝ≥0∞) (w : X → ℝ) {S T : Set X}
    (hST : S ⊆ T) (x y : X) :
    weylDistOnWith E w T x y ≤ weylDistOnWith E w S x y := by
  unfold weylDistOnWith
  refine le_iInf fun P => le_iInf fun hPc => le_iInf fun hP0 =>
    le_iInf fun hP1 => le_iInf fun hPS => ?_
  exact weylDistOnWith_le hPc hP0 hP1 (fun t ht => hST (hPS ht))

theorem weylDistOnWith_triangle
    {X : Type*} [MetricSpace X]
    (E : X → X → ℝ≥0∞)
    (htri : ∀ p q r, E p r ≤ E p q + E q r)
    (w : X → ℝ) (S : Set X) (x y z : X) :
    weylDistOnWith E w S x z ≤
      weylDistOnWith E w S x y + weylDistOnWith E w S y z := by
  rw [← tsub_le_iff_right]
  unfold weylDistOnWith
  refine le_iInf fun P₁ => le_iInf fun hc₁ => le_iInf fun h₁0 =>
    le_iInf fun h₁1 => le_iInf fun hS₁ => ?_
  rw [tsub_le_iff_right, ← tsub_le_iff_left]
  refine le_iInf fun P₂ => le_iInf fun hc₂ => le_iInf fun h₂0 =>
    le_iInf fun h₂1 => le_iInf fun hS₂ => ?_
  rw [tsub_le_iff_left]
  let γ₁ : Path x y := Path.ofLine hc₁ h₁0 h₁1
  let γ₂ : Path y z := Path.ofLine hc₂ h₂0 h₂1
  have hγ₁S : ∀ t : I, γ₁ t ∈ S := fun t => hS₁ t.property
  have hγ₂S : ∀ t : I, γ₂ t ∈ S := fun t => hS₂ t.property
  have htransS : ∀ t : I, (γ₁.trans γ₂) t ∈ S := by
    intro t
    rw [Path.trans_apply]
    split_ifs with ht
    · exact hγ₁S _
    · exact hγ₂S _
  have hcost₁ : coordinatePathWeightedLength E w γ₁ = weightedLengthWith E w P₁ 0 1 := by
    unfold coordinatePathWeightedLength
    apply weightedLengthWith_congr_path
    intro t ht
    rw [Path.extend_apply _ ht]
    rfl
  have hcost₂ : coordinatePathWeightedLength E w γ₂ = weightedLengthWith E w P₂ 0 1 := by
    unfold coordinatePathWeightedLength
    apply weightedLengthWith_congr_path
    intro t ht
    rw [Path.extend_apply _ ht]
    rfl
  calc
    weylDistOnWith E w S x z ≤ coordinatePathWeightedLength E w (γ₁.trans γ₂) :=
      weylDistOnWith_le (P := (γ₁.trans γ₂).extend)
        (γ₁.trans γ₂).continuous_extend.continuousOn
        (γ₁.trans γ₂).extend_zero (γ₁.trans γ₂).extend_one
        (fun t ht => by rw [Path.extend_apply _ ht]; exact htransS ⟨t, ht⟩)
    _ = weightedLengthWith E w P₁ 0 1 + weightedLengthWith E w P₂ 0 1 := by
      rw [coordinatePathWeightedLength_trans htri, hcost₁, hcost₂]

theorem exists_near_confined_competitor
    {X : Type*} [MetricSpace X]
    (E : X → X → ℝ≥0∞) (w : X → ℝ) (S : Set X) (x y : X)
    (hfin : weylDistOnWith E w S x y ≠ ∞)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ Q : I →ᵇ X, (∀ t, Q t ∈ S) ∧ Q 0 = x ∧ Q 1 = y ∧
      weightedLengthWith E w (Set.IccExtend zero_le_one Q) 0 1 <
        weylDistOnWith E w S x y + ENNReal.ofReal ε := by
  have hstrict : weylDistOnWith E w S x y <
      weylDistOnWith E w S x y + ENNReal.ofReal ε :=
    ENNReal.lt_add_right hfin (ne_of_gt (ENNReal.ofReal_pos.mpr hε))
  unfold weylDistOnWith at hstrict
  obtain ⟨P, hstrict⟩ := iInf_lt_iff.mp hstrict
  obtain ⟨hPc, hstrict⟩ := iInf_lt_iff.mp hstrict
  obtain ⟨hP0, hstrict⟩ := iInf_lt_iff.mp hstrict
  obtain ⟨hP1, hstrict⟩ := iInf_lt_iff.mp hstrict
  obtain ⟨hPS, hstrict⟩ := iInf_lt_iff.mp hstrict
  let Q : I →ᵇ X := mkOfCompact
    ⟨fun t => P t, hPc.comp_continuous continuous_subtype_val Subtype.prop⟩
  refine ⟨Q, fun t => hPS t.property, ?_, ?_, ?_⟩
  · exact hP0
  · exact hP1
  · change weightedLengthWith E w P 0 1 <
        weylDistOnWith E w S x y + ENNReal.ofReal ε at hstrict
    have heq : weightedLengthWith E w (Set.IccExtend zero_le_one Q) 0 1 =
        weightedLengthWith E w P 0 1 :=
      weightedLengthWith_congr_path (fun t ht => by
        rw [Set.IccExtend_of_mem _ _ ht]
        rfl)
    rwa [heq]

theorem confined_short_connector_bound
    {X : Type*} [MetricSpace X] (ρ : X × X → ℝ) (w : X → ℝ)
    {O Y' : Set X} (hOY : closure O ⊆ Y')
    {M : ℝ} (hM : 0 ≤ M)
    (hw : ∀ z ∈ closure O, w z ≤ M)
    {x y : X}
    (hlocal : ∃ R : I →ᵇ X, (∀ t, R t ∈ closure O) ∧
      R 0 = x ∧ R 1 = y ∧
      curveLengthWith (fun u v => ENNReal.ofReal (ρ (u, v)))
        (Set.IccExtend zero_le_one R) 0 1 = ENNReal.ofReal (ρ (x, y))) :
    weylDistOnWith (fun u v => ENNReal.ofReal (ρ (u, v))) w Y' x y ≤
      ENNReal.ofReal (M * ρ (x, y)) := by
  obtain ⟨R, hRO, hR0, hR1, hRlen⟩ := hlocal
  have hcost := weightedLengthWith_le_ofReal_mul_curveLengthWith
    (δ := fun u v => ENNReal.ofReal (ρ (u, v))) (w := w)
    (P := Set.IccExtend zero_le_one R) (a := 0) (b := 1) (M := M) (by
      intro t ht
      rw [Set.IccExtend_of_mem _ _ ht]
      exact hw _ (hRO ⟨t, ht⟩))
  have hdist := weylDistOnWith_le
    (E := fun u v => ENNReal.ofReal (ρ (u, v)))
    (w := w) (S := Y') (x := x) (y := y)
    (P := Set.IccExtend zero_le_one R)
    (continuous_IccExtend_iff.mpr R.continuous).continuousOn
    (by rw [Set.IccExtend_of_mem _ _ (show (0 : ℝ) ∈ Icc 0 1 from ⟨le_rfl, zero_le_one⟩)]; exact hR0)
    (by rw [Set.IccExtend_of_mem _ _ (show (1 : ℝ) ∈ Icc 0 1 from ⟨zero_le_one, le_rfl⟩)]; exact hR1)
    (fun t ht => by rw [Set.IccExtend_of_mem _ _ ht]; exact hOY (hRO ⟨t, ht⟩))
  calc
    _ ≤ weightedLengthWith (fun u v => ENNReal.ofReal (ρ (u, v))) w
        (Set.IccExtend zero_le_one R) 0 1 := hdist
    _ ≤ ENNReal.ofReal M * ENNReal.ofReal (ρ (x, y)) := by simpa [hRlen] using hcost
    _ = ENNReal.ofReal (M * ρ (x, y)) := (ENNReal.ofReal_mul hM).symm

theorem coordinate_moving_pair_tendsto
    {X : Type*} [MetricSpace X] {C : Set X}
    (ρ : ℕ → X × X → ℝ) (ρlim : X × X → ℝ)
    (hρlim : IsCoordinate ρlim)
    (hconv : TendstoUniformlyOn ρ ρlim atTop (C ×ˢ C))
    (xn yn : ℕ → X) (x y : X)
    (hxn : Tendsto xn atTop (𝓝 x)) (hyn : Tendsto yn atTop (𝓝 y))
    (hx : x ∈ C) (hy : y ∈ C)
    (hmem : ∀ n, xn n ∈ C ∧ yn n ∈ C) :
    Tendsto (fun n => ρ n (xn n, yn n)) atTop (𝓝 (ρlim (x, y))) := by
  have hpair : Tendsto (fun n => (xn n, yn n)) atTop (𝓝[C ×ˢ C] (x, y)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hxn.prodMk_nhds hyn,
      Eventually.of_forall fun n => hmem n⟩
  exact hconv.tendsto_comp (hρlim.continuous.continuousOn (x, y) ⟨hx, hy⟩) hpair

/-- Sequential bounds for arbitrary moving points and subsequences become
uniform bounds on a compact square. -/
theorem eventually_uniform_on_compact_square
    {X : Type*} [MetricSpace X] {Y : Set X} (hY : IsCompact Y)
    (R : ℕ → X → X → Prop)
    (hmove : ∀ ns : ℕ → ℕ, Tendsto ns atTop atTop →
      ∀ xs ys : ℕ → X, (∀ k, xs k ∈ Y ∧ ys k ∈ Y) →
      ∀ x ∈ Y, ∀ y ∈ Y,
        Tendsto xs atTop (𝓝 x) → Tendsto ys atTop (𝓝 y) →
        ∀ᶠ k in atTop, R (ns k) (xs k) (ys k)) :
    ∀ᶠ n in atTop, ∀ x ∈ Y, ∀ y ∈ Y, R n x y := by
  classical
  by_contra hnot
  have hfreq : ∃ᶠ n in atTop, ∃ x ∈ Y, ∃ y ∈ Y, ¬ R n x y := by
    exact (Filter.not_eventually.mp hnot).mono (fun n hn => by
      push Not at hn
      exact hn)
  obtain ⟨φ, hφ, hbad⟩ := extraction_of_frequently_atTop hfreq
  choose xs hxs hrest using hbad
  choose ys hys hbad' using hrest
  obtain ⟨⟨x, y⟩, hxy, ψ, hψ, hxyconv⟩ :=
    (hY.prod hY).tendsto_subseq (x := fun k => (xs k, ys k))
      (fun k => ⟨hxs k, hys k⟩)
  have hψtop : Tendsto ψ atTop atTop := hψ.tendsto_atTop
  have hns : Tendsto (φ ∘ ψ) atTop atTop := hφ.tendsto_atTop.comp hψtop
  have hxconv : Tendsto (xs ∘ ψ) atTop (𝓝 x) :=
    (continuous_fst.tendsto (x, y)).comp hxyconv
  have hyconv : Tendsto (ys ∘ ψ) atTop (𝓝 y) :=
    (continuous_snd.tendsto (x, y)).comp hxyconv
  have hgood := hmove (φ ∘ ψ) hns (xs ∘ ψ) (ys ∘ ψ)
    (fun k => ⟨hxs (ψ k), hys (ψ k)⟩)
    x hxy.1 y hxy.2 hxconv hyconv
  obtain ⟨k, hk⟩ := hgood.exists
  exact (hbad' (ψ k)) hk

theorem tendstoUniformlyOn_subseq
    {α β : Type*} [UniformSpace β] {F : ℕ → α → β} {f : α → β}
    {S : Set α} (h : TendstoUniformlyOn F f atTop S)
    (ns : ℕ → ℕ) (hns : Tendsto ns atTop atTop) :
    TendstoUniformlyOn (fun k => F (ns k)) f atTop S := by
  rw [tendstoUniformlyOn_iff_tendsto] at h ⊢
  exact h.comp ((hns.comp tendsto_fst).prodMk tendsto_snd)

/-- Positive weights turn a bound on weighted speed into a coordinate-speed
bound, the equicontinuity input of Lemma CC. -/
theorem weighted_speed_coordinate_speed
    {X : Type*} [MetricSpace X] (ρ : X × X → ℝ)
    (hρ : LQGMetric.MetricGeometry.IsMetricFun ρ)
    (w : X → ℝ) (P : I →ᵇ X)
    {m A : ℝ} (hm : 0 < m) (hA : 0 ≤ A)
    (hw : ∀ t, m ≤ w (P t))
    (hspeed : ∀ s t : I, (s : ℝ) ≤ t →
      weightedLengthWith (fun u v => ENNReal.ofReal (ρ (u, v))) w
        (Set.IccExtend zero_le_one P) s t ≤
          ENNReal.ofReal (A * ((t : ℝ) - s))) :
    ∀ s t : I, ρ (P s, P t) ≤ (A / m) * dist s t := by
  intro s t
  have hordered {s t : I} (hst : (s : ℝ) ≤ t) :
      ρ (P s, P t) ≤ (A / m) * dist s t := by
    let Q := Set.IccExtend zero_le_one P
    have hmem (u : ℝ) (hu : u ∈ Icc (s : ℝ) t) : u ∈ Icc (0 : ℝ) 1 :=
      ⟨s.property.1.trans hu.1, hu.2.trans t.property.2⟩
    have hw' : ∀ u ∈ Icc (s : ℝ) t, m ≤ w (Q u) := by
      intro u hu
      change m ≤ w ((Set.IccExtend zero_le_one P) u)
      rw [Set.IccExtend_of_mem _ _ (hmem u hu)]
      exact hw ⟨u, hmem u hu⟩
    have hlen := ofReal_mul_curveLengthWith_le_weightedLengthWith
      (δ := fun u v => ENNReal.ofReal (ρ (u, v))) hst hw'
    have hdist := le_curveLengthWith
      (δ := fun u v => ENNReal.ofReal (ρ (u, v))) (P := Q) hst
    have hupper := (mul_le_mul' le_rfl hdist).trans (hlen.trans (hspeed s t hst))
    have hρpos : 0 ≤ ρ (P s, P t) := by
      change 0 ≤ dist (LQGMetric.MetricGeometry.MetricFunSpace.pt ρ hρ (P s))
        (LQGMetric.MetricGeometry.MetricFunSpace.pt ρ hρ (P t))
      exact dist_nonneg
    have hAr : 0 ≤ A * ((t : ℝ) - s) := mul_nonneg hA (sub_nonneg.mpr hst)
    have hρreal : m * ρ (P s, P t) ≤ A * ((t : ℝ) - s) := by
      have hupper' : ENNReal.ofReal m * ENNReal.ofReal (ρ (P s, P t)) ≤
          ENNReal.ofReal (A * ((t : ℝ) - s)) := by
        simpa [Q, Set.IccExtend_of_mem] using hupper
      rw [← ENNReal.ofReal_mul hm.le] at hupper'
      exact (ENNReal.ofReal_le_ofReal_iff hAr).1 hupper'
    rw [Subtype.dist_eq, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hst)]
    have hquot : ρ (P s, P t) ≤ (A * ((t : ℝ) - s)) / m :=
      (le_div_iff₀ hm).2 (by nlinarith)
    convert hquot using 1; ring
  rcases le_total (s : ℝ) t with hst | hts
  · exact hordered hst
  · rw [hρ.symm, dist_comm]
    exact hordered hts

/-- The compactness half of MA1 Lemma 2.5′(b).  Convergence of the
confined distances is supplied separately by part (a). -/
theorem lemma25b_of_distance_convergence
    {X : Type*} [MetricSpace X] {Y' : Set X} (hY' : IsCompact Y')
    (ρ : ℕ → X × X → ℝ) (ρlim : X × X → ℝ)
    (hρcont : ∀ n, ContinuousOn (ρ n) (Y' ×ˢ Y'))
    (hconv : TendstoUniformlyOn ρ ρlim atTop (Y' ×ˢ Y'))
    (hmod : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ n, ∀ u ∈ Y', ∀ v ∈ Y', ρ n (u, v) < δ → dist u v < ε)
    (w : X → ℝ) (hw : ContinuousOn w Y')
    (xseq yseq : ℕ → X) (x y : X)
    (hx : Tendsto xseq atTop (𝓝 x)) (hy : Tendsto yseq atTop (𝓝 y))
    (Dseq : ℕ → ℝ≥0∞) (D : ℝ≥0∞) (hD : Tendsto Dseq atTop (𝓝 D))
    (_hDfin : D ≠ ∞)
    (P : ℕ → I →ᵇ X) (hPY : ∀ n t, P n t ∈ Y')
    (hP0 : ∀ n, P n 0 = xseq n) (hP1 : ∀ n, P n 1 = yseq n)
    (A : ℝ) (hspeed : ∀ n : ℕ, ∀ s t : I,
      ρ n (P n s, P n t) ≤ A * dist s t)
    (e : ℕ → ℝ) (he : Tendsto e atTop (𝓝 0))
    (hcost : ∀ n,
      weightedLengthWith (fun u v => ENNReal.ofReal (ρ n (u, v))) w
        (Set.IccExtend zero_le_one (P n)) 0 1 ≤ Dseq n + ENNReal.ofReal (e n))
    (hlower : ∀ Q : I →ᵇ X, (∀ t, Q t ∈ Y') → Q 0 = x → Q 1 = y →
      D ≤ weightedLengthWith (fun u v => ENNReal.ofReal (ρlim (u, v))) w
        (Set.IccExtend zero_le_one Q) 0 1) :
    ∃ Q : I →ᵇ X, (∀ t, Q t ∈ Y') ∧ Q 0 = x ∧ Q 1 = y ∧
      weightedLengthWith (fun u v => ENNReal.ofReal (ρlim (u, v))) w
        (Set.IccExtend zero_le_one Q) 0 1 = D ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        TendstoUniformly (fun n t => P (φ n) t) Q atTop := by
  obtain ⟨Q, hQY, φ, hφ, hPconv, -, -, hwls⟩ :=
    lemmaCC zero_le_one hY' ρ ρlim hρcont hconv A P hPY hmod hspeed
  have hφtop : Tendsto φ atTop atTop := hφ.tendsto_atTop
  have hQ0 : Q 0 = x :=
    tendsto_nhds_unique (hPconv.tendsto_at 0)
      (by simpa only [Function.comp_def, hP0] using hx.comp hφtop)
  have hQ1 : Q 1 = y :=
    tendsto_nhds_unique (hPconv.tendsto_at 1)
      (by simpa only [Function.comp_def, hP1] using hy.comp hφtop)
  have hεlim : Tendsto (fun n => ENNReal.ofReal (e (φ n))) atTop (𝓝 (0 : ℝ≥0∞)) := by
    simpa using ENNReal.tendsto_ofReal (he.comp hφtop)
  have hupperlim : Tendsto (fun n => Dseq (φ n) + ENNReal.ofReal (e (φ n)))
      atTop (𝓝 D) := by
    convert (hD.comp hφtop).add hεlim using 1 <;> simp
  have hweighted : weightedLengthWith (fun u v => ENNReal.ofReal (ρlim (u, v))) w
      (Set.IccExtend zero_le_one Q) 0 1 ≤ D := by
    calc
      _ ≤ liminf (fun n => weightedLengthWith
          (fun u v => ENNReal.ofReal (ρ (φ n) (u, v))) w
          (Set.IccExtend zero_le_one (P (φ n))) 0 1) atTop :=
        hwls w hw le_rfl zero_le_one le_rfl
      _ ≤ liminf (fun n => Dseq (φ n) + ENNReal.ofReal (e (φ n))) atTop :=
        Filter.liminf_le_liminf (Eventually.of_forall fun n => hcost (φ n))
      _ = D := hupperlim.liminf_eq
  refine ⟨Q, hQY, hQ0, hQ1, le_antisymm hweighted (hlower Q hQY hQ0 hQ1),
    φ, hφ, hPconv⟩

end HigherDimLQGMetric
