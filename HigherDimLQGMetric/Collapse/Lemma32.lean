import HigherDimLQGMetric.Collapse.ShortcutSeq

/-! # Lemma 3.2′: transfer of a forced marked arc -/

set_option autoImplicit false

open Set Filter Topology BoundedContinuousFunction
open scoped ENNReal

namespace HigherDimLQGMetric

open LQGMetric.MetricGeometry

/-- Complete ordered traversal of an arc by a curve on its geodesic time interval. -/
def TraversesMarkedArc {X : Type*} [MetricSpace X] {T ℓ : ℝ}
    (hℓT : ℓ ≤ T) (Q : Icc (0 : ℝ) T →ᵇ X)
    (σ : ℝ → X) : Prop :=
  ∃ s t : ℝ, ∃ hs : 0 ≤ s, ∃ hst : s ≤ t, ∃ ht : t ≤ ℓ,
    Q ⟨s, ⟨hs, hst.trans (ht.trans hℓT)⟩⟩ = σ 0 ∧
    Q ⟨t, ⟨hs.trans hst, ht.trans hℓT⟩⟩ = σ 1 ∧
    ∀ r ∈ Icc (0 : ℝ) 1, ∃ q : ℝ, s ≤ q ∧ q ≤ t ∧
      ∃ hq : q ∈ Icc (0 : ℝ) T, Q ⟨q, hq⟩ = σ r

/-- One confined weighted geodesic between separated points of the closed tube.
`L` is its normalized weighted length and `P` is constant from `L` to `T`. -/
structure CollapseGeodesicCandidate {X : Type*} [MetricSpace X]
    (Y K : Set X) (lam eta : ℕ → ℝ) (w : ℕ → X → ℝ)
    (T b : ℝ) (n : ℕ) where
  x : X
  y : X
  u : X
  v : X
  hx : x ∈ Y
  hy : y ∈ Y
  hu : u ∈ K
  hv : v ∈ K
  hxu : dist x u ≤ eta n
  hyv : dist y v ≤ eta n
  hsep : b ≤ dist x y
  L : ℝ
  hLdef : L = ((ENNReal.ofReal (lam n))⁻¹ * weylDistOn (w n) Y x y).toReal
  P : ℝ → X
  hPc : ContinuousOn P (Icc 0 T)
  hPY : MapsTo P (Icc 0 T) Y
  hP0 : P 0 = x
  hPL : P L = y
  hLT : L ≤ T
  hparam : ∀ s t, 0 ≤ s → s ≤ t → t ≤ L →
    weightedLength (w n) P s t = ENNReal.ofReal (lam n * (t - s))
  hconst : ∀ t, L ≤ t → t ≤ T → P t = P L

/-- The conclusion of Lemma 3.2′ for one weighted geodesic. -/
def HasMarkedShortcut {X : Type*} [MetricSpace X]
    {Y K : Set X} {lam eta : ℕ → ℝ} {w : ℕ → X → ℝ}
    {T b : ℝ} {n : ℕ}
    (E : X → X → ℝ≥0∞) (a₁ c₁ : ℝ)
    (C : CollapseGeodesicCandidate Y K lam eta w T b n) : Prop :=
  ∃ s t : ℝ, 0 ≤ s ∧ s ≤ t ∧ t ≤ C.L ∧
    ENNReal.ofReal (lam n * (a₁ / 2)) ≤ weightedLength (w n) C.P s t ∧
    ∃ S : ℝ → X, ContinuousOn S (Icc 0 1) ∧
      S 0 = C.P s ∧ S 1 = C.P t ∧ MapsTo S (Icc 0 1) Y ∧
      weightedLengthWith E (w n) S 0 1 ≤
        ENNReal.ofReal c₁ * weightedLength (w n) C.P s t

/-- An arc family with both orientations available. -/
def orientedMarkedArc {X I : Type*} (σ : I → ℝ → X) : I × Bool → ℝ → X :=
  fun j r => if j.2 then σ j.1 (1 - r) else σ j.1 r

/-- Local form of Lemma 3.2′: a finite family of marked arcs forced on every
macroscopic intrinsic geodesic yields a shortcut, uniformly over all confined
weighted geodesics at sufficiently large indices. -/
theorem lemma32_shortcut_oriented {X I : Type*} [MetricSpace X] [Fintype I]
    (Y K : Set X) (hY : IsCompact Y) (hK : IsCompact K) (hKY : K ⊆ Y)
    (hKfin : ∀ p ∈ K, ∀ q ∈ K, internalEDist K p q ≠ ⊤)
    (hKcont : ContinuousOn (fun p : X × X => internalEDist K p.1 p.2) (K ×ˢ K))
    (δ : ℝ) (hδ : 0 < δ)
    (hreal : ∀ p ∈ Y, ∀ q ∈ K, dist p q < δ → ∃ A : ℝ → X,
      ContinuousOn A (Icc 0 1) ∧ A 0 = p ∧ A 1 = q ∧
      MapsTo A (Icc 0 1) Y ∧ curveLength A 0 1 = edist p q)
    (lam eta : ℕ → ℝ) (hlam0 : ∀ n, 0 < lam n)
    (hlam : Tendsto lam atTop (𝓝 0))
    (heta0 : ∀ n, 0 < eta n)
    (heta : Tendsto (fun n => eta n / lam n) atTop (𝓝 0))
    (a₀ : ℝ) (ha₀ : 0 < a₀) (w : ℕ → X → ℝ)
    (hw : ∀ n, Continuous (w n))
    (hw1 : ∀ n p, lam n ≤ w n p ∧ w n p ≤ 1)
    (hwK : ∀ n, ∀ p ∈ K, w n p = lam n)
    (hwoff : ∀ n p, eta n ≤ Metric.infDist p K → a₀ ≤ w n p)
    (T : ℝ) (hT : 0 ≤ T) (b : ℝ)
    (E : X → X → ℝ≥0∞)
    (hEtri : ∀ p ∈ Y, ∀ q ∈ Y, ∀ r ∈ Y,
      E p r ≤ E p q + E q r)
    (M : ℝ) (hM : 0 < M)
    (hEM : ∀ p ∈ Y, ∀ q ∈ Y, E p q ≤ ENNReal.ofReal M * edist p q)
    (σ : I → ℝ → X)
    (hσc : ∀ i, ContinuousOn (σ i) (Icc 0 1))
    (hσK : ∀ i, MapsTo (σ i) (Icc 0 1) K)
    (c₀ c₁ a₁ : ℝ) (hc₀ : 0 ≤ c₀) (hc₁ : c₀ < c₁) (ha₁ : 0 < a₁)
    (hσlen : ∀ i, curveLengthWith E (σ i) 0 1 ≤
      ENNReal.ofReal c₀ * edist (σ i 0) (σ i 1))
    (hσsep : ∀ i, a₁ ≤ dist (σ i 0) (σ i 1))
    (hforce : ∀ (p q : X) (_hp : p ∈ K) (_hq : q ∈ K), b ≤ dist p q →
      ∀ (Q : Icc (0 : ℝ) T →ᵇ X) (_hQK : ∀ t, Q t ∈ K)
        (_hQ0 : (Set.IccExtend hT Q) 0 = p)
        (ℓ : ℝ) (hℓ0 : 0 ≤ ℓ) (hℓT : ℓ ≤ T),
        Q ⟨ℓ, ⟨hℓ0, hℓT⟩⟩ = q →
        (∀ s ∈ Icc (0 : ℝ) ℓ, ∀ t ∈ Icc (0 : ℝ) ℓ, s ≤ t →
          internalEDist K ((Set.IccExtend hT Q) s) ((Set.IccExtend hT Q) t) =
            ENNReal.ofReal (t - s)) →
        ∃ i : I, TraversesMarkedArc hℓT Q (σ i)) :
    ∀ᶠ n in atTop,
      ∀ C : CollapseGeodesicCandidate Y K lam eta w T b n,
        HasMarkedShortcut E a₁ c₁ C := by
  classical
  by_contra hnot
  have hfreq : ∃ᶠ n in atTop,
      ∃ C : CollapseGeodesicCandidate Y K lam eta w T b n,
        ¬ HasMarkedShortcut E a₁ c₁ C := by
    simpa only [Filter.not_eventually, not_forall, not_not] using hnot
  obtain ⟨ns, hns, hbad⟩ := exists_seq_forall_of_frequently hfreq
  let C (n : ℕ) : CollapseGeodesicCandidate Y K lam eta w T b (ns n) :=
    Classical.choose (hbad n)
  have hCbad (n : ℕ) : ¬ HasMarkedShortcut E a₁ c₁ (C n) :=
    (Classical.choose_spec (hbad n))
  obtain ⟨uLim, huK, φu, hφu, huLim⟩ :=
    hK.isSeqCompact (fun n => (C n).hu)
  obtain ⟨vLim, hvK, φv, hφv, hvLim⟩ :=
    hK.isSeqCompact (fun n => (C (φu n)).hv)
  let ρ : ℕ → ℕ := φu ∘ φv
  have hρ : StrictMono ρ := hφu.comp hφv
  have hρtop : Tendsto ρ atTop atTop := hρ.tendsto_atTop
  have hnsρ : Tendsto (ns ∘ ρ) atTop atTop := hns.comp hρtop
  have huLim' : Tendsto (fun n => (C (ρ n)).u) atTop (𝓝 uLim) := by
    change Tendsto ((fun n => (C n).u) ∘ φu ∘ φv) atTop (𝓝 uLim)
    exact huLim.comp hφv.tendsto_atTop
  have hvLim' : Tendsto (fun n => (C (ρ n)).v) atTop (𝓝 vLim) := by
    change Tendsto ((fun n => (C (φu n)).v) ∘ φv) atTop (𝓝 vLim)
    exact hvLim
  let ix : ℕ → ℕ := ns ∘ ρ
  let x : ℕ → X := fun n => (C (ρ n)).x
  let y : ℕ → X := fun n => (C (ρ n)).y
  let u : ℕ → X := fun n => (C (ρ n)).u
  let v : ℕ → X := fun n => (C (ρ n)).v
  let P : ℕ → ℝ → X := fun n => (C (ρ n)).P
  let L : ℕ → ℝ := fun n => (C (ρ n)).L
  have hetaLim : Tendsto eta atTop (𝓝 0) := by
    have hp : Tendsto (fun n => eta n / lam n * lam n) atTop (𝓝 0) := by
      simpa using heta.mul hlam
    have heq : (fun n => eta n / lam n * lam n) = eta := by
      funext n
      exact div_mul_cancel₀ _ (ne_of_gt (hlam0 n))
    simpa only [heq] using hp
  have hxLim : Tendsto x atTop (𝓝 uLim) := by
    have hd : Tendsto (fun n => dist (u n) (x n)) atTop (𝓝 0) := by
      apply squeeze_zero (fun n => dist_nonneg) (fun n => by
        simpa only [x, u, dist_comm] using (C (ρ n)).hxu)
      exact hetaLim.comp hnsρ
    exact huLim'.congr_dist hd
  have hyLim : Tendsto y atTop (𝓝 vLim) := by
    have hd : Tendsto (fun n => dist (v n) (y n)) atTop (𝓝 0) := by
      apply squeeze_zero (fun n => dist_nonneg) (fun n => by
        simpa only [y, v, dist_comm] using (C (ρ n)).hyv)
      exact hetaLim.comp hnsρ
    exact hvLim'.congr_dist hd
  have hsepLim : b ≤ dist uLim vLim := by
    apply isClosed_Ici.mem_of_tendsto (hxLim.dist hyLim)
    exact Eventually.of_forall (fun n => (C (ρ n)).hsep)
  have hnorm : ∀ n, L n =
      ((ENNReal.ofReal (lam (ix n)))⁻¹ *
        weylDistOn (w (ix n)) Y (x n) (y n)).toReal :=
    fun n => (C (ρ n)).hLdef
  have hPc : ∀ n, ContinuousOn (P n) (Icc 0 T) :=
    fun n => (C (ρ n)).hPc
  have hPY : ∀ n, MapsTo (P n) (Icc 0 T) Y :=
    fun n => (C (ρ n)).hPY
  have hP0 : ∀ n, P n 0 = x n := fun n => (C (ρ n)).hP0
  have hPL : ∀ n, P n (L n) = y n := fun n => (C (ρ n)).hPL
  have hLT : ∀ n, L n ≤ T := fun n => (C (ρ n)).hLT
  have hparam : ∀ n s t, 0 ≤ s → s ≤ t → t ≤ L n →
      weightedLength (w (ix n)) (P n) s t =
        ENNReal.ofReal (lam (ix n) * (t - s)) :=
    fun n s t hs hst ht => (C (ρ n)).hparam s t hs hst ht
  have hconst : ∀ n t, L n ≤ t → t ≤ T → P n t = P n (L n) :=
    fun n t hnt htT => (C (ρ n)).hconst t hnt htT
  have hcollapse := lemma31_collapse Y K hY hK hKY hKfin hKcont δ hδ hreal
    (lam ∘ ix) (eta ∘ ix)
    (fun n => hlam0 (ix n)) (hlam.comp hnsρ)
    (fun n => heta0 (ix n)) (heta.comp hnsρ)
    a₀ ha₀ (w ∘ ix) (fun n => hw (ix n))
    (fun n z => hw1 (ix n) z) (fun n z hz => hwK (ix n) z hz)
    (fun n z hz => hwoff (ix n) z hz)
    x y u v uLim vLim
    (fun n => (C (ρ n)).hx) (fun n => (C (ρ n)).hy)
    (fun n => (C (ρ n)).hu) (fun n => (C (ρ n)).hv)
    (fun n => (C (ρ n)).hxu) (fun n => (C (ρ n)).hyv)
    huLim' hvLim'
  have hdfin : internalEDist K uLim vLim ≠ ⊤ := hKfin uLim huK vLim hvK
  have hLlim : Tendsto L atTop
      (𝓝 (internalEDist K uLim vLim).toReal) := by
    have htemp := (ENNReal.tendsto_toReal hdfin).comp hcollapse
    have heq : (fun n =>
        ((ENNReal.ofReal ((lam ∘ ix) n))⁻¹ *
          weylDistOn ((w ∘ ix) n) Y (x n) (y n)).toReal) = L := by
      funext n
      exact (hnorm n).symm
    change Tendsto (fun n =>
      ((ENNReal.ofReal ((lam ∘ ix) n))⁻¹ *
        weylDistOn ((w ∘ ix) n) Y (x n) (y n)).toReal) atTop
      (𝓝 (internalEDist K uLim vLim).toReal) at htemp
    rwa [heq] at htemp
  obtain ⟨Q, hQK, φ, hφ, hlim, hQ0, hℓ, hQℓ, hgeo, htail, hest⟩ :=
    lemma31_geodesic_subseq Y K hY hK hKY hKfin hKcont δ hδ hreal
      (lam ∘ ix) (eta ∘ ix)
      (fun n => hlam0 (ix n)) (hlam.comp hnsρ)
      (fun n => heta0 (ix n)) (heta.comp hnsρ)
      a₀ ha₀ (w ∘ ix) (fun n => hw (ix n))
      (fun n z => hw1 (ix n) z) (fun n z hz => hwK (ix n) z hz)
      (fun n z hz => hwoff (ix n) z hz)
      x y u v uLim vLim
      (fun n => (C (ρ n)).hx) (fun n => (C (ρ n)).hy)
      (fun n => (C (ρ n)).hu) (fun n => (C (ρ n)).hv)
      (fun n => (C (ρ n)).hxu) (fun n => (C (ρ n)).hyv)
      huLim' hvLim' T hT P hPc hPY hP0
      (fun n => by
        change P n (((ENNReal.ofReal (lam (ix n)))⁻¹ *
          weylDistOn (w (ix n)) Y (x n) (y n)).toReal) = y n
        rw [← hnorm n]
        exact hPL n)
      (fun n => by
        change ((ENNReal.ofReal (lam (ix n)))⁻¹ *
          weylDistOn (w (ix n)) Y (x n) (y n)).toReal ≤ T
        rw [← hnorm n]
        exact hLT n)
      (fun n s t hs hst ht => hparam n s t hs hst (by
        change t ≤ ((ENNReal.ofReal (lam (ix n)))⁻¹ *
          weylDistOn (w (ix n)) Y (x n) (y n)).toReal at ht
        rwa [← hnorm n] at ht))
      (fun n t hnt htT => by
        change ((ENNReal.ofReal (lam (ix n)))⁻¹ *
          weylDistOn (w (ix n)) Y (x n) (y n)).toReal ≤ t at hnt
        change P n t = P n (((ENNReal.ofReal (lam (ix n)))⁻¹ *
          weylDistOn (w (ix n)) Y (x n) (y n)).toReal)
        rw [← hnorm n] at hnt ⊢
        exact hconst n t hnt htT)
  let ℓ : ℝ := (internalEDist K uLim vLim).toReal
  obtain ⟨i, s, t, hs, hst, htℓ, hQs, hQt, _⟩ :=
    hforce uLim vLim huK hvK hsepLim Q hQK hQ0 ℓ hℓ.1 hℓ.2
      hQℓ hgeo
  have hsT : s ∈ Icc (0 : ℝ) T := ⟨hs, hst.trans (htℓ.trans hℓ.2)⟩
  have htT : t ∈ Icc (0 : ℝ) T := ⟨hs.trans hst, htℓ.trans hℓ.2⟩
  have hQse : Q ⟨s, hsT⟩ = σ i 0 := hQs
  have hQte : Q ⟨t, htT⟩ = σ i 1 := hQt
  have hdu : dist (σ i 0) (σ i 1) ≤ t - s := by
    have hgeo' := hgeo s ⟨hs, hst.trans htℓ⟩ t ⟨hs.trans hst, htℓ⟩ hst
    have hds : edist (σ i 0) (σ i 1) ≤ ENNReal.ofReal (t - s) := by
      calc
        edist (σ i 0) (σ i 1) ≤ internalEDist K (σ i 0) (σ i 1) :=
          edist_le_internalEDist K _ _
        _ = ENNReal.ofReal (t - s) := by
          simpa only [Set.IccExtend_of_mem hT Q hsT,
            Set.IccExtend_of_mem hT Q htT, hQse, hQte] using hgeo'
    have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hds
    simpa only [edist_dist, ENNReal.toReal_ofReal dist_nonneg,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hst)] using hreal
  have hconn0 : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      (ENNReal.ofReal (lam (ix (φ n))))⁻¹ *
        weylDistOn (w (ix (φ n))) Y (P (φ n) s) (σ i 0) <
          ENNReal.ofReal ε := by
    intro ε hε
    filter_upwards [hest ε hε] with n hn
    have h := hn ⟨s, hsT⟩
    simpa only [Function.comp_apply, hQse] using h
  have hconn1 : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      (ENNReal.ofReal (lam (ix (φ n))))⁻¹ *
        weylDistOn (w (ix (φ n))) Y (σ i 1) (P (φ n) t) <
          ENNReal.ofReal ε := by
    intro ε hε
    filter_upwards [hest ε hε] with n hn
    have h := hn ⟨t, htT⟩
    rw [hQte] at h
    rw [weylDistOn_comm] at h
    exact h
  have hshort := lemma32_shortcut_along_marked_limit
    (Y := Y) (K := K) (E := E) (M := M) (c₀ := c₀)
    (c₁ := c₁) (a₁ := a₁) (T := T) (ℓ := ℓ)
    (s := s) (t := t) (u := σ i 0) (v := σ i 1) (σ := σ i)
    hM hc₀ hc₁ ha₁ hEtri hEM hKY (hσc i) rfl rfl (hσK i)
    (hσlen i) (hσsep i) hdu hs htℓ hℓ.2
    (lam := fun n => lam (ix (φ n)))
    (fun n => hlam0 (ix (φ n)))
    (w := fun n => w (ix (φ n)))
    (fun n z hz => hwK (ix (φ n)) z hz)
    (P := fun n => P (φ n)) (L := fun n => L (φ n))
    (hLlim.comp hφ.tendsto_atTop)
    (fun n => hLT (φ n))
    (fun n a b ha hab hb => hparam (φ n) a b ha hab hb)
    (fun n r hr hRT => hconst (φ n) r hr hRT)
    hconn0 hconn1
  obtain ⟨n, hn⟩ := hshort.exists
  obtain ⟨τ, hsτ, hτL, _hτT, hcost, S, hSc, hS0, hS1, hSY, hSbudget⟩ := hn
  have hgood : HasMarkedShortcut E a₁ c₁ (C (ρ (φ n))) := by
    exact ⟨s, τ, hs, hsτ, hτL, hcost, S, hSc, hS0, hS1, hSY,
      le_of_lt hSbudget⟩
  exact hCbad (ρ (φ n)) hgood

/-- Lemma 3.2′ with unoriented traversal, as in the source: a limiting
geodesic may cross a marked arc in either direction. -/
theorem lemma32_shortcut {X I : Type*} [MetricSpace X] [Fintype I]
    (Y K : Set X) (hY : IsCompact Y) (hK : IsCompact K) (hKY : K ⊆ Y)
    (hKfin : ∀ p ∈ K, ∀ q ∈ K, internalEDist K p q ≠ ⊤)
    (hKcont : ContinuousOn (fun p : X × X => internalEDist K p.1 p.2) (K ×ˢ K))
    (δ : ℝ) (hδ : 0 < δ)
    (hreal : ∀ p ∈ Y, ∀ q ∈ K, dist p q < δ → ∃ A : ℝ → X,
      ContinuousOn A (Icc 0 1) ∧ A 0 = p ∧ A 1 = q ∧
      MapsTo A (Icc 0 1) Y ∧ curveLength A 0 1 = edist p q)
    (lam eta : ℕ → ℝ) (hlam0 : ∀ n, 0 < lam n)
    (hlam : Tendsto lam atTop (𝓝 0))
    (heta0 : ∀ n, 0 < eta n)
    (heta : Tendsto (fun n => eta n / lam n) atTop (𝓝 0))
    (a₀ : ℝ) (ha₀ : 0 < a₀) (w : ℕ → X → ℝ)
    (hw : ∀ n, Continuous (w n))
    (hw1 : ∀ n p, lam n ≤ w n p ∧ w n p ≤ 1)
    (hwK : ∀ n, ∀ p ∈ K, w n p = lam n)
    (hwoff : ∀ n p, eta n ≤ Metric.infDist p K → a₀ ≤ w n p)
    (T : ℝ) (hT : 0 ≤ T) (b : ℝ)
    (E : X → X → ℝ≥0∞)
    (hEtri : ∀ p ∈ Y, ∀ q ∈ Y, ∀ r ∈ Y,
      E p r ≤ E p q + E q r)
    (hEsymm : ∀ p ∈ Y, ∀ q ∈ Y, E p q = E q p)
    (M : ℝ) (hM : 0 < M)
    (hEM : ∀ p ∈ Y, ∀ q ∈ Y, E p q ≤ ENNReal.ofReal M * edist p q)
    (σ : I → ℝ → X)
    (hσc : ∀ i, ContinuousOn (σ i) (Icc 0 1))
    (hσK : ∀ i, MapsTo (σ i) (Icc 0 1) K)
    (c₀ c₁ a₁ : ℝ) (hc₀ : 0 ≤ c₀) (hc₁ : c₀ < c₁) (ha₁ : 0 < a₁)
    (hσlen : ∀ i, curveLengthWith E (σ i) 0 1 ≤
      ENNReal.ofReal c₀ * edist (σ i 0) (σ i 1))
    (hσsep : ∀ i, a₁ ≤ dist (σ i 0) (σ i 1))
    (hforce : ∀ (p q : X) (_hp : p ∈ K) (_hq : q ∈ K), b ≤ dist p q →
      ∀ (Q : Icc (0 : ℝ) T →ᵇ X) (_hQK : ∀ t, Q t ∈ K)
        (_hQ0 : (Set.IccExtend hT Q) 0 = p)
        (ℓ : ℝ) (hℓ0 : 0 ≤ ℓ) (hℓT : ℓ ≤ T),
        Q ⟨ℓ, ⟨hℓ0, hℓT⟩⟩ = q →
        (∀ s ∈ Icc (0 : ℝ) ℓ, ∀ t ∈ Icc (0 : ℝ) ℓ, s ≤ t →
          internalEDist K ((Set.IccExtend hT Q) s) ((Set.IccExtend hT Q) t) =
            ENNReal.ofReal (t - s)) →
        ∃ i : I, TraversesMarkedArc hℓT Q (σ i) ∨
          TraversesMarkedArc hℓT Q (fun r => σ i (1 - r))) :
    ∀ᶠ n in atTop,
      ∀ C : CollapseGeodesicCandidate Y K lam eta w T b n,
        HasMarkedShortcut E a₁ c₁ C := by
  let arc : I × Bool → ℝ → X := orientedMarkedArc σ
  have harcc : ∀ j, ContinuousOn (arc j) (Icc 0 1) := by
    intro ⟨i, side⟩
    cases side with
    | false =>
        change ContinuousOn (σ i) (Icc 0 1)
        exact hσc i
    | true =>
        change ContinuousOn (fun r => σ i (1 - r)) (Icc 0 1)
        exact (hσc i).comp (by fun_prop) (fun r hr => ⟨by linarith [hr.2], by linarith [hr.1]⟩)
  have harcK : ∀ j, MapsTo (arc j) (Icc 0 1) K := by
    intro ⟨i, side⟩ r hr
    cases side with
    | false => simpa [arc, orientedMarkedArc] using hσK i hr
    | true =>
        change σ i (1 - r) ∈ K
        exact hσK i ⟨by linarith [hr.2], by linarith [hr.1]⟩
  have harclen : ∀ j, curveLengthWith E (arc j) 0 1 ≤
      ENNReal.ofReal c₀ * edist (arc j 0) (arc j 1) := by
    intro ⟨i, side⟩
    cases side with
    | false =>
        change curveLengthWith E (σ i) 0 1 ≤
          ENNReal.ofReal c₀ * edist (σ i 0) (σ i 1)
        exact hσlen i
    | true =>
        have hreverse := curveLengthWith_reflect_of_symm hEsymm
          ((hσK i).mono_right hKY)
        change curveLengthWith E (fun r => σ i (1 - r)) 0 1 ≤
          ENNReal.ofReal c₀ * edist (σ i (1 - 0)) (σ i (1 - 1))
        simpa only [sub_zero, sub_self, edist_comm] using hreverse.trans_le (hσlen i)
  have harcsep : ∀ j, a₁ ≤ dist (arc j 0) (arc j 1) := by
    intro ⟨i, side⟩
    cases side with
    | false => simpa [arc, orientedMarkedArc] using hσsep i
    | true => simpa [arc, orientedMarkedArc, dist_comm] using hσsep i
  apply lemma32_shortcut_oriented Y K hY hK hKY hKfin hKcont δ hδ hreal
    lam eta hlam0 hlam heta0 heta a₀ ha₀ w hw hw1 hwK hwoff T hT b E hEtri
    M hM hEM arc harcc harcK c₀ c₁ a₁ hc₀ hc₁ ha₁ harclen harcsep
  intro p q hp hq hpq Q hQK hQ0 ℓ hℓ0 hℓT hQℓ hgeo
  obtain ⟨i, htrav | htrav⟩ := hforce p q hp hq hpq Q hQK hQ0 ℓ hℓ0 hℓT hQℓ hgeo
  · exact ⟨(i, false), by change TraversesMarkedArc hℓT Q (σ i); exact htrav⟩
  · exact ⟨(i, true), by
      change TraversesMarkedArc hℓT Q (fun r => σ i (1 - r))
      exact htrav⟩

end HigherDimLQGMetric
