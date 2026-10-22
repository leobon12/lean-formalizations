import HigherDimLQGMetric.Config.Tight

/-! Constructing monotone bound data from countably many scale estimates. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace HigherDimLQGMetric

open Set MeasureTheory
open scoped ENNReal
open HigherDimLFPP (Rd)

variable {X : Type*} [MetricSpace X]

private def lowerCandidates (lo : ℕ → ℕ → ℝ) (m : ℕ) (η : ℝ) : Set ℝ :=
  {0} ∪ {x | ∃ n : ℕ, x = lo m n ∧ (1 : ℝ) / (n + 1) ≤ η}

private def upperCandidates (A : ℕ → ℝ) (δ : ℕ → ℕ → ℝ)
    (m : ℕ) (η : ℝ) : Set ℝ :=
  {2 * A m} ∪ {x | ∃ n : ℕ, x = (1 : ℝ) / (n + 1) ∧ η ≤ δ m n}

private theorem lowerCandidates_nonempty (lo : ℕ → ℕ → ℝ) (m : ℕ) (η : ℝ) :
    (lowerCandidates lo m η).Nonempty := ⟨0, Or.inl rfl⟩

private theorem lowerCandidates_bddAbove (lo : ℕ → ℕ → ℝ)
    (hlo : ∀ m n, lo m n ≤ 1) (m : ℕ) (η : ℝ) :
    BddAbove (lowerCandidates lo m η) := by
  refine ⟨1, ?_⟩
  rintro x (rfl | ⟨n, rfl, _⟩)
  · norm_num
  · exact hlo m n

private theorem upperCandidates_nonempty (A : ℕ → ℝ) (δ : ℕ → ℕ → ℝ)
    (m : ℕ) (η : ℝ) :
    (upperCandidates A δ m η).Nonempty := ⟨2 * A m, Or.inl rfl⟩

private theorem upperCandidates_bddBelow (A : ℕ → ℝ) (hA : ∀ m, 0 ≤ A m)
    (δ : ℕ → ℕ → ℝ) (m : ℕ) (η : ℝ) :
    BddBelow (upperCandidates A δ m η) := by
  refine ⟨0, ?_⟩
  rintro x (rfl | ⟨n, rfl, _⟩)
  · exact mul_nonneg (by norm_num) (hA m)
  · positivity

/-- The canonical bound datum extracted from upper, lower, and continuity
estimates at reciprocal integer scales. -/
def configDatumFromScales (A : ℕ → ℝ) (hA : ∀ m, 0 ≤ A m)
    (lo : ℕ → ℕ → ℝ) (hlo0 : ∀ m n, 0 < lo m n)
    (hlo1 : ∀ m n, lo m n ≤ 1)
    (δ : ℕ → ℕ → ℝ) (hδ : ∀ m n, 0 < δ m n) : ConfigBoundDatum X where
  upper := A
  upper_nonneg := hA
  lower := fun m η => sSup (lowerCandidates lo m η)
  lower_zero := by
    intro m
    have heq : lowerCandidates lo m 0 = {0} := by
      ext x
      simp only [lowerCandidates, mem_union, mem_singleton_iff, mem_ofPred_eq]
      constructor
      · rintro (rfl | ⟨n, _, hn⟩)
        · rfl
        · have : (0 : ℝ) < 1 / (n + 1) := by positivity
          exact (not_le_of_gt this hn).elim
      · intro hx
        exact Or.inl hx
    simp [heq]
  lower_pos := by
    intro m η hη
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hη
    have hmem : lo m n ∈ lowerCandidates lo m η :=
      Or.inr ⟨n, rfl, hn.le⟩
    exact lt_of_lt_of_le (hlo0 m n)
      (le_csSup (lowerCandidates_bddAbove lo hlo1 m η) hmem)
  lower_mono := by
    intro m η η' hη
    apply csSup_le_csSup (lowerCandidates_bddAbove lo hlo1 m η')
      (lowerCandidates_nonempty lo m η)
    rintro x (hx | ⟨n, hxn, hn⟩)
    · exact Or.inl hx
    · exact Or.inr ⟨n, hxn, hn.trans hη⟩
  modulus := fun m η => sInf (upperCandidates A δ m η)
  modulus_nonneg := by
    intro m η
    apply le_csInf (upperCandidates_nonempty A δ m η)
    rintro x (rfl | ⟨n, rfl, _⟩)
    · exact mul_nonneg (by norm_num) (hA m)
    · positivity
  modulus_mono := by
    intro m η η' hη
    apply csInf_le_csInf (upperCandidates_bddBelow A hA δ m η)
      (upperCandidates_nonempty A δ m η')
    rintro x (hx | ⟨n, hxn, hn⟩)
    · exact Or.inl hx
    · exact Or.inr ⟨n, hxn, hη.trans hn⟩
  modulus_small := by
    intro m ε hε
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    refine ⟨δ m n, hδ m n, ?_⟩
    exact lt_of_le_of_lt
      (csInf_le (upperCandidates_bddBelow A hA δ m (δ m n))
        (Or.inr ⟨n, rfl, le_rfl⟩)) hn

theorem configBoundOne_of_scales
    (K : CompactExhaustion X) (f : C(X × X, ℝ))
    (A : ℕ → ℝ) (hA : ∀ m, 0 ≤ A m)
    (lo : ℕ → ℕ → ℝ) (hlo0 : ∀ m n, 0 < lo m n)
    (hlo1 : ∀ m n, lo m n ≤ 1)
    (δ : ℕ → ℕ → ℝ) (hδ : ∀ m n, 0 < δ m n)
    (hf0 : ∀ p : X × X, 0 ≤ f p)
    (hfA : ∀ m (p : X × X), p.1 ∈ K m → p.2 ∈ K m → f p ≤ A m)
    (hflo : ∀ m (n : ℕ) (p : X × X), p.1 ∈ K m → p.2 ∈ K m →
      (1 : ℝ) / (n + 1) ≤ dist p.1 p.2 → lo m n ≤ f p)
    (hfδ : ∀ m (n : ℕ) (p q : X × X), p.1 ∈ K m → p.2 ∈ K m →
      q.1 ∈ K m → q.2 ∈ K m → dist p q ≤ δ m n →
      dist (f p) (f q) ≤ (1 : ℝ) / (n + 1)) :
    f ∈ configBoundOne K
      (configDatumFromScales A hA lo hlo0 hlo1 δ hδ) := by
  constructor
  · intro m p hp₁ hp₂
    constructor
    · apply csSup_le (lowerCandidates_nonempty lo m (dist p.1 p.2))
      rintro x (rfl | ⟨n, rfl, hn⟩)
      · exact hf0 p
      · exact hflo m n p hp₁ hp₂ hn
    · exact hfA m p hp₁ hp₂
  · intro m p q hp₁ hp₂ hq₁ hq₂ η _hη hpq
    apply le_csInf (upperCandidates_nonempty A δ m η)
    rintro x (rfl | ⟨n, rfl, hn⟩)
    · rw [Real.dist_eq]
      have hp0 := hf0 p
      have hq0 := hf0 q
      have hpA := hfA m p hp₁ hp₂
      have hqA := hfA m q hq₁ hq₂
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    · exact hfδ m n p q hp₁ hp₂ hq₁ hq₂ (hpq.trans hn)

/-- A countable union bound for one continuous coordinate.  `Nat.unpair`
enumerates every pair of compact-set and resolution indices. -/
theorem configBoundOne_failure_le
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (K : CompactExhaustion X) (F : Ω → C(X × X, ℝ))
    (A : ℕ → ℝ) (hA : ∀ m, 0 ≤ A m)
    (lo : ℕ → ℕ → ℝ) (hlo0 : ∀ m n, 0 < lo m n)
    (hlo1 : ∀ m n, lo m n ≤ 1)
    (δ : ℕ → ℕ → ℝ) (hδ : ∀ m n, 0 < δ m n)
    (w : ℕ → ℝ≥0∞)
    (hF0 : ∀ᵐ ω ∂P, ∀ p : X × X, 0 ≤ F ω p)
    (hup : ∀ k,
      P {ω | ¬ ∀ (p : X × X), p.1 ∈ K k → p.2 ∈ K k → F ω p ≤ A k} ≤ w k)
    (hlo : ∀ k,
      let m := (Nat.unpair k).1
      let n := (Nat.unpair k).2
      P {ω | ¬ ∀ (p : X × X), p.1 ∈ K m → p.2 ∈ K m →
        (1 : ℝ) / (n + 1) ≤ dist p.1 p.2 → lo m n ≤ F ω p} ≤ w k)
    (hmod : ∀ k,
      let m := (Nat.unpair k).1
      let n := (Nat.unpair k).2
      P {ω | ¬ ∀ (p q : X × X), p.1 ∈ K m → p.2 ∈ K m →
        q.1 ∈ K m → q.2 ∈ K m → dist p q ≤ δ m n →
        dist (F ω p) (F ω q) ≤ (1 : ℝ) / (n + 1)} ≤ w k) :
    P {ω | F ω ∉ configBoundOne K
      (configDatumFromScales A hA lo hlo0 hlo1 δ hδ)} ≤
        3 * ∑' k, w k := by
  let E₁ : ℕ → Set Ω := fun k =>
    {ω | ¬ ∀ (p : X × X), p.1 ∈ K k → p.2 ∈ K k → F ω p ≤ A k}
  let E₂ : ℕ → Set Ω := fun k =>
    let m := (Nat.unpair k).1
    let n := (Nat.unpair k).2
    {ω | ¬ ∀ (p : X × X), p.1 ∈ K m → p.2 ∈ K m →
      (1 : ℝ) / (n + 1) ≤ dist p.1 p.2 → lo m n ≤ F ω p}
  let E₃ : ℕ → Set Ω := fun k =>
    let m := (Nat.unpair k).1
    let n := (Nat.unpair k).2
    {ω | ¬ ∀ (p q : X × X), p.1 ∈ K m → p.2 ∈ K m →
      q.1 ∈ K m → q.2 ∈ K m → dist p q ≤ δ m n →
      dist (F ω p) (F ω q) ≤ (1 : ℝ) / (n + 1)}
  have hsub : ∀ᵐ ω ∂P, ω ∈ {ω | F ω ∉ configBoundOne K
      (configDatumFromScales A hA lo hlo0 hlo1 δ hδ)} →
      ω ∈ (⋃ k, E₁ k) ∪ ((⋃ k, E₂ k) ∪ (⋃ k, E₃ k)) := by
    filter_upwards [hF0] with ω hzero hω
    by_contra hnot
    simp only [mem_union, not_or, mem_iUnion, not_exists] at hnot
    have hA' : ∀ m (p : X × X), p.1 ∈ K m → p.2 ∈ K m → F ω p ≤ A m := by
      intro m
      exact not_not.mp (hnot.1 m)
    have hlo' : ∀ m (n : ℕ) (p : X × X), p.1 ∈ K m → p.2 ∈ K m →
        (1 : ℝ) / (n + 1) ≤ dist p.1 p.2 → lo m n ≤ F ω p := by
      intro m n
      simpa only [E₂, Nat.unpair_pair] using not_not.mp (hnot.2.1 (Nat.pair m n))
    have hmod' : ∀ m (n : ℕ) (p q : X × X), p.1 ∈ K m → p.2 ∈ K m →
        q.1 ∈ K m → q.2 ∈ K m → dist p q ≤ δ m n →
        dist (F ω p) (F ω q) ≤ (1 : ℝ) / (n + 1) := by
      intro m n
      simpa only [E₃, Nat.unpair_pair] using not_not.mp (hnot.2.2 (Nat.pair m n))
    exact hω (configBoundOne_of_scales K (F ω) A hA lo hlo0 hlo1 δ hδ
      hzero hA' hlo' hmod')
  have h₁ : P (⋃ k, E₁ k) ≤ ∑' k, w k :=
    (measure_iUnion_le E₁).trans (ENNReal.tsum_le_tsum fun k => hup k)
  have h₂ : P (⋃ k, E₂ k) ≤ ∑' k, w k :=
    (measure_iUnion_le E₂).trans (ENNReal.tsum_le_tsum fun k => hlo k)
  have h₃ : P (⋃ k, E₃ k) ≤ ∑' k, w k :=
    (measure_iUnion_le E₃).trans (ENNReal.tsum_le_tsum fun k => hmod k)
  calc
    P _ ≤ P ((⋃ k, E₁ k) ∪ ((⋃ k, E₂ k) ∪ (⋃ k, E₃ k))) := measure_mono_ae hsub
    _ ≤ P (⋃ k, E₁ k) + (P (⋃ k, E₂ k) + P (⋃ k, E₃ k)) :=
      (measure_union_le _ _).trans (add_le_add le_rfl (measure_union_le _ _))
    _ ≤ (∑' k, w k) + ((∑' k, w k) + (∑' k, w k)) :=
      add_le_add h₁ (add_le_add h₂ h₃)
    _ = 3 * ∑' k, w k := by ring

/-- The normalized internal coordinate, with the a.s. length proof displayed
as an argument. -/
def configSharpInternalCoord {d : ℕ} (ξ Q : ℝ)
    (D : DistRd d → ContMetric d) (g : DistRd d)
    (hl : (D g).IsLength) {U : Set (Rd d)}
    (hU : IsOpen U) (hUc : IsPreconnected U)
    {r : ℝ} (hr : 0 < r) (z : Rd d) : C(U × U, ℝ) :=
  internalC (configScaledMetric (D g) (sNorm_pos ξ Q g hr z) hr z)
    (configScaledMetric_isLength (D g) hl (sNorm_pos ξ Q g hr z) hr z)
    hU hUc

theorem configSharpInternalCoord_nonneg {d : ℕ} (ξ Q : ℝ)
    (D : DistRd d → ContMetric d) (g : DistRd d)
    (hl : (D g).IsLength) {U : Set (Rd d)}
    (hU : IsOpen U) (hUc : IsPreconnected U)
    {r : ℝ} (hr : 0 < r) (z : Rd d) (q : U × U) :
    0 ≤ configSharpInternalCoord ξ Q D g hl hU hUc hr z q := by
  change 0 ≤ ((configScaledMetric (D g) (sNorm_pos ξ Q g hr z) hr z).internal
    U q.1.1 q.2.1).toReal
  exact ENNReal.toReal_nonneg

/-- Transfer uniform one-scale tails to a measurable-version coordinate,
then apply the countable bound-data lemma. -/
theorem configCoordinate_failure_le_of_tails
    {d : ℕ} {U : Set (Rd d)} (hU : IsOpen U) (hUc : IsPreconnected U)
    (E : CompactExhaustion U) (ξ Q : ℝ)
    (D : DistRd d → ContMetric d)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (h : Ω → DistRd d) {r : ℝ} (hr : 0 < r) (z : Rd d)
    (F : Ω → C(U × U, ℝ))
    (hF0 : ∀ᵐ ω ∂P, ∀ p : U × U, 0 ≤ F ω p)
    (hFeq : ∀ᵐ ω ∂P, ∃ hl : (D (h ω)).IsLength,
      F ω = configSharpInternalCoord ξ Q D (h ω) hl hU hUc hr z)
    (A A₀ : ℕ → ℝ) (hA : ∀ m, 0 ≤ A m) (hA₀ : ∀ m, A₀ m ≤ A m)
    (lo lo₀ : ℕ → ℕ → ℝ) (hlo0 : ∀ m n, 0 < lo m n)
    (hlo1 : ∀ m n, lo m n ≤ 1)
    (hlo₀ : ∀ m n, lo m n ≤ lo₀ m n)
    (δ δ₀ : ℕ → ℕ → ℝ) (hδ : ∀ m n, 0 < δ m n)
    (hδ₀ : ∀ m n, δ m n ≤ δ₀ m n)
    (w : ℕ → ℝ≥0∞)
    (hup : ∀ m,
      P {ω | ¬ ∀ hl : (D (h ω)).IsLength,
        ∀ u ∈ E m, ∀ v ∈ E m,
          configSharpInternalCoord ξ Q D (h ω) hl hU hUc hr z (u,v) < A₀ m} ≤ w m)
    (hlow : ∀ k,
      let m := (Nat.unpair k).1
      let n := (Nat.unpair k).2
      P {ω | ¬ ∀ hl : (D (h ω)).IsLength,
        ∀ u ∈ E m, ∀ v ∈ E m,
          (1 : ℝ) / (n + 1) ≤ dist u v →
            lo₀ m n < configSharpInternalCoord ξ Q D (h ω) hl hU hUc hr z (u,v)} ≤ w k)
    (hmod : ∀ k,
      let m := (Nat.unpair k).1
      let n := (Nat.unpair k).2
      P {ω | ¬ ∀ hl : (D (h ω)).IsLength,
        ∀ p q : U × U,
          p.1 ∈ E m → p.2 ∈ E m → q.1 ∈ E m → q.2 ∈ E m →
          dist p q ≤ δ₀ m n →
            dist (configSharpInternalCoord ξ Q D (h ω) hl hU hUc hr z p)
              (configSharpInternalCoord ξ Q D (h ω) hl hU hUc hr z q) ≤
                (1 : ℝ) / (n + 1)} ≤ w k) :
    P {ω | F ω ∉ configBoundOne E
      (configDatumFromScales A hA lo hlo0 hlo1 δ hδ)} ≤
        3 * ∑' k, w k := by
  apply configBoundOne_failure_le P E F A hA lo hlo0 hlo1 δ hδ w hF0
  · intro k
    refine (measure_mono_ae ?_).trans (hup k)
    filter_upwards [hFeq] with ω ⟨hl, hEq⟩ hbad hgood
    apply hbad
    intro p hp₁ hp₂
    rw [hEq]
    exact (hgood hl p.1 hp₁ p.2 hp₂).le.trans (hA₀ k)
  · intro k
    let m := (Nat.unpair k).1
    let n := (Nat.unpair k).2
    refine (measure_mono_ae ?_).trans (hlow k)
    filter_upwards [hFeq] with ω ⟨hl, hEq⟩ hbad hgood
    apply hbad
    intro p hp₁ hp₂ hsep
    rw [hEq]
    exact (hlo₀ m n).trans (hgood hl p.1 hp₁ p.2 hp₂ hsep).le
  · intro k
    let m := (Nat.unpair k).1
    let n := (Nat.unpair k).2
    refine (measure_mono_ae ?_).trans (hmod k)
    filter_upwards [hFeq] with ω ⟨hl, hEq⟩ hbad hgood
    apply hbad
    intro p q hp₁ hp₂ hq₁ hq₂ hpq
    rw [hEq]
    exact hgood hl p q hp₁ hp₂ hq₁ hq₂ (hpq.trans (hδ₀ m n))

/-- One bound datum works simultaneously for the two normalized internal
metrics on a fixed annulus. -/
theorem config_pair_datum
    {d : ℕ} (hd : 2 ≤ d) (ξ Q : ℝ)
    (D Dt : DistRd d → ContMetric d)
    (hD : IsSharpWeakExpMetric d ξ Q D)
    (hDt : IsSharpWeakExpMetric d ξ Q Dt)
    (hE5 : E5SharpMoment d ξ Q D)
    (hE5t : E5SharpMoment d ξ Q Dt)
    {U : Set (Rd d)} (hU : IsOpen U) (hUc : IsPreconnected U)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hshape : U = ann 0 a b)
    (E : CompactExhaustion U)
    {p : ℝ} (hp : 0 < p)
    (hpmax : p < (Q + Real.sqrt (Q ^ 2 - 2 * d)) / ξ)
    (w : ℕ → ℝ≥0∞) (hw : ∀ k, 0 < w k) :
    ∃ β : ConfigBoundDatum U,
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        (h : Ω → DistRd d) (r : ℝ) (hr : 0 < r) (z : Rd d)
        (F Ft : Ω → C(U × U, ℝ))
        (_hF0 : ∀ᵐ ω ∂P, ∀ q : U × U, 0 ≤ F ω q)
        (_hFt0 : ∀ᵐ ω ∂P, ∀ q : U × U, 0 ≤ Ft ω q)
        (_hEq : ∀ᵐ ω ∂P,
          ∃ (hl : (D (h ω)).IsLength) (hlt : (Dt (h ω)).IsLength),
            F ω = configSharpInternalCoord ξ Q D (h ω) hl hU hUc hr z ∧
            Ft ω = configSharpInternalCoord ξ Q Dt (h ω) hlt hU hUc hr z)
        [IsProbabilityMeasure P] (_hh : IsWholeSpaceLGF h P),
        P {ω | F ω ∉ configBoundOne E β} ≤ 3 * ∑' k, w k ∧
        P {ω | Ft ω ∉ configBoundOne E β} ≤ 3 * ∑' k, w k := by
  let 𝔇 : Bool → DistRd d → ContMetric d := fun b => if b then Dt else D
  have h𝔇 (j : Bool) : IsSharpWeakExpMetric d ξ Q (𝔇 j) := by
    cases j with
    | false => exact hD
    | true => exact hDt
  have hE (j : Bool) : E5SharpMoment d ξ Q (𝔇 j) := by
    cases j with
    | false => exact hE5
    | true => exact hE5t
  have Hupper (b : Bool) (m : ℕ) :
      ∃ A : ℝ, 0 < A ∧
        ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
          [IsProbabilityMeasure P] (h : Ω → DistRd d)
          (hh : IsWholeSpaceLGF h P) (r : ℝ) (hr : 0 < r) (z : Rd d),
          P {ω | ¬ ∀ hl : ((𝔇 b) (h ω)).IsLength,
            ∀ u ∈ E m, ∀ v ∈ E m,
              configSharpInternalCoord ξ Q (𝔇 b) (h ω) hl hU hUc hr z (u,v) < A} < w m := by
    exact configE5_internal_upper_on_compact hd ξ Q (𝔇 b) (h𝔇 b) (hE b)
      hU hUc ha hab hshape (E.isCompact m) hp hpmax (hw m)
  choose A₀ hA₀ Hupper₀ using Hupper
  have Hlower (b : Bool) (m n : ℕ) :
      ∃ a : ℝ, 0 < a ∧
        ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
          [IsProbabilityMeasure P] (h : Ω → DistRd d), IsWholeSpaceLGF h P →
          ∀ (r : ℝ) (hr : 0 < r) (z : Rd d),
            P {ω | ¬ ∀ hl : ((𝔇 b) (h ω)).IsLength,
              ∀ u ∈ E m, ∀ v ∈ E m,
                (1 : ℝ) / (n + 1) ≤ dist u v →
                a < configSharpInternalCoord ξ Q (𝔇 b) (h ω) hl hU hUc hr z (u,v)} <
                  w (Nat.pair m n) := by
    simpa only [configSharpInternalCoord, Subtype.dist_eq] using
      (IsWeakExpMetric.configScaledLowerOffDiag (h𝔇 b) hd hU hUc
        (E.isCompact m) (by positivity : 0 < (1 : ℝ) / (n + 1))
        (hw (Nat.pair m n)))
  choose a₀ ha₀ Hlower₀ using Hlower
  have Hmod (b : Bool) (m n : ℕ) :
      ∃ δ : ℝ, 0 < δ ∧
        ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
          [IsProbabilityMeasure P] (h : Ω → DistRd d), IsWholeSpaceLGF h P →
          ∀ (r : ℝ) (hr : 0 < r) (z : Rd d),
            P {ω | ¬ ∀ hl : ((𝔇 b) (h ω)).IsLength,
              ∀ q q' : U × U,
                q.1 ∈ E m → q.2 ∈ E m → q'.1 ∈ E m → q'.2 ∈ E m →
                dist q q' ≤ δ →
                  dist (configSharpInternalCoord ξ Q (𝔇 b) (h ω) hl hU hUc hr z q)
                    (configSharpInternalCoord ξ Q (𝔇 b) (h ω) hl hU hUc hr z q') ≤
                    (1 : ℝ) / (n + 1)} < w (Nat.pair m n) := by
    exact IsWeakExpMetric.configScaledInternalModulusOnCompact (h𝔇 b) hd hU hUc
      (E.isCompact m) (by positivity : 0 < (1 : ℝ) / (n + 1))
      (hw (Nat.pair m n))
  choose δ₀ hδ₀ Hmod₀ using Hmod
  let A : ℕ → ℝ := fun m => max (A₀ false m) (A₀ true m)
  let lo : ℕ → ℕ → ℝ := fun m n => min 1 (min (a₀ false m n) (a₀ true m n))
  let δ : ℕ → ℕ → ℝ := fun m n => min (δ₀ false m n) (δ₀ true m n)
  have hA (m : ℕ) : 0 ≤ A m := by dsimp [A]; exact (hA₀ false m).le.trans (le_max_left _ _)
  have hlo0 (m n : ℕ) : 0 < lo m n := by
    dsimp [lo]
    exact lt_min (by norm_num) (lt_min (ha₀ false m n) (ha₀ true m n))
  have hlo1 (m n : ℕ) : lo m n ≤ 1 := min_le_left _ _
  have hδ (m n : ℕ) : 0 < δ m n :=
    lt_min (hδ₀ false m n) (hδ₀ true m n)
  let β : ConfigBoundDatum U := configDatumFromScales A hA lo hlo0 hlo1 δ hδ
  refine ⟨β, ?_⟩
  intro Ω _ P h r hr z F Ft hF0 hFt0 hEq _ hh
  have hfail (b : Bool) (G : Ω → C(U × U, ℝ))
      (hG0 : ∀ᵐ ω ∂P, ∀ q : U × U, 0 ≤ G ω q)
      (hGeq : ∀ᵐ ω ∂P, ∃ hl : ((𝔇 b) (h ω)).IsLength,
        G ω = configSharpInternalCoord ξ Q (𝔇 b) (h ω) hl hU hUc hr z) :
      P {ω | G ω ∉ configBoundOne E β} ≤ 3 * ∑' k, w k := by
    apply configCoordinate_failure_le_of_tails hU hUc E ξ Q (𝔇 b) P h hr z G
      hG0 hGeq A (A₀ b) hA
      (by cases b <;> simp [A])
      lo (a₀ b) hlo0 hlo1
      (by intro m n; cases b <;> simp [lo])
      δ (δ₀ b) hδ
      (by intro m n; cases b <;> simp [δ]) w
    · intro m
      exact (Hupper₀ b m P h hh r hr z).le
    · intro k
      simpa only [Nat.pair_unpair] using
        (Hlower₀ b (Nat.unpair k).1 (Nat.unpair k).2 P h hh r hr z).le
    · intro k
      simpa only [Nat.pair_unpair] using
        (Hmod₀ b (Nat.unpair k).1 (Nat.unpair k).2 P h hh r hr z).le
  constructor
  · apply hfail false F hF0
    filter_upwards [hEq] with ω ⟨hl, hlt, hF, hFt⟩
    exact ⟨hl, hF⟩
  · apply hfail true Ft hFt0
    filter_upwards [hEq] with ω ⟨hl, hlt, hF, hFt⟩
    exact ⟨hlt, hFt⟩

private theorem config_budget_sum {e : ℝ} (he : 0 ≤ e) :
    (∑' k : ℕ, ENNReal.ofReal (e / 100 * (1 / 2 : ℝ) ^ k)) =
      ENNReal.ofReal (e / 50) := by
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity)
    ((summable_geometric_two).mul_left (e / 100)),
    tsum_mul_left, tsum_geometric_two]
  ring_nf

/-- D-SF5: one deterministic compact bound family captures the four
normalized internal coordinates with probability arbitrarily close to one,
uniformly in the LGF, center, and scale. The configuration is supplied as a
measurable version because lengthness is only known almost surely. -/
theorem config_DSF5
    {d : ℕ} (hd : 2 ≤ d) (ξ Q : ℝ)
    (D Dt : DistRd d → ContMetric d)
    (hD : IsSharpWeakExpMetric d ξ Q D)
    (hDt : IsSharpWeakExpMetric d ξ Q Dt)
    (hE5 : E5SharpMoment d ξ Q D)
    (hE5t : E5SharpMoment d ξ Q Dt)
    {p : ℝ} (hp : 0 < p)
    (hpmax : p < (Q + Real.sqrt (Q ^ 2 - 2 * d)) / ξ)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ β : ConfigBounds d,
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (h : Ω → DistRd d)
        (_hh : IsWholeSpaceLGF h P) (r : ℝ) (hr : 0 < r) (z : Rd d),
      ∃ Ξ : Ω → ConfigC d, Measurable Ξ ∧
        (∀ᵐ ω ∂P, ∃ (hl : (D (h ω)).IsLength)
          (hlt : (Dt (h ω)).IsLength),
          Ξ ω = configC hd (D (h ω)) (Dt (h ω)) hl hlt
            (sNorm_pos ξ Q (h ω) hr z) hr z) ∧
        P {ω | Ξ ω ∉ configBoundSet β} < ε ∧
        1 - ε ≤ P {ω | Ξ ω ∈ configBoundSet β} := by
  obtain ⟨e, he, heε⟩ : ∃ e : ℝ, 0 < e ∧ ENNReal.ofReal e ≤ ε := by
    rcases eq_top_or_lt_top ε with htop | hfin
    · exact ⟨1, one_pos, by simp [htop]⟩
    · refine ⟨ε.toReal, ENNReal.toReal_pos hε.ne' hfin.ne, ?_⟩
      rw [ENNReal.ofReal_toReal hfin.ne]
  let w : ℕ → ℝ≥0∞ := fun k =>
    ENNReal.ofReal (e / 100 * (1 / 2 : ℝ) ^ k)
  have hw (k : ℕ) : 0 < w k := by
    dsimp [w]
    exact ENNReal.ofReal_pos.mpr (by positivity)
  have hsum : (∑' k, w k) = ENNReal.ofReal (e / 50) :=
    config_budget_sum he.le
  have hbudget : 12 * (∑' k, w k) < ε := by
    rw [hsum]
    have hle : 12 * (e / 50) < e := by linarith
    have hcast : (12 : ℝ≥0∞) = ENNReal.ofReal (12 : ℝ) := by norm_num
    rw [hcast, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 12)]
    exact ((ENNReal.ofReal_lt_ofReal_iff he).2 hle).trans_le heε
  obtain ⟨βo, Hβo⟩ := config_pair_datum hd ξ Q D Dt hD hDt hE5 hE5t
    configOuter_isOpen (configOuter_isPreconnected hd)
    (a := 1 / 2) (b := 5) (by norm_num) (by norm_num) rfl
    (configOuterExhaust d) hp hpmax w hw
  obtain ⟨βi, Hβi⟩ := config_pair_datum hd ξ Q D Dt hD hDt hE5 hE5t
    configInner_isOpen (configInner_isPreconnected hd)
    (a := 3 / 4) (b := 7 / 2) (by norm_num) (by norm_num) rfl
    (configInnerExhaust d) hp hpmax w hw
  let β : ConfigBounds d := ⟨βo, βi⟩
  refine ⟨β, ?_⟩
  intro Ω _ P _ h hh r hr z
  obtain ⟨Ξ, hΞm, hΞae⟩ := exists_measurable_configC_sharp_ae P hd ξ Q D Dt
    hD hDt h hh hr z
  have hOeq : ∀ᵐ ω ∂P,
      ∃ (hl : (D (h ω)).IsLength) (hlt : (Dt (h ω)).IsLength),
        (Ξ ω).1 = configSharpInternalCoord ξ Q D (h ω) hl
          configOuter_isOpen (configOuter_isPreconnected hd) hr z ∧
        (Ξ ω).2.1 = configSharpInternalCoord ξ Q Dt (h ω) hlt
          configOuter_isOpen (configOuter_isPreconnected hd) hr z := by
    filter_upwards [hΞae] with ω ⟨hl, hlt, hEq⟩
    refine ⟨hl, hlt, ?_, ?_⟩ <;> rw [hEq] <;> rfl
  have hIeq : ∀ᵐ ω ∂P,
      ∃ (hl : (D (h ω)).IsLength) (hlt : (Dt (h ω)).IsLength),
        (Ξ ω).2.2.1 = configSharpInternalCoord ξ Q D (h ω) hl
          configInner_isOpen (configInner_isPreconnected hd) hr z ∧
        (Ξ ω).2.2.2 = configSharpInternalCoord ξ Q Dt (h ω) hlt
          configInner_isOpen (configInner_isPreconnected hd) hr z := by
    filter_upwards [hΞae] with ω ⟨hl, hlt, hEq⟩
    refine ⟨hl, hlt, ?_, ?_⟩ <;> rw [hEq] <;> rfl
  have hO0 : ∀ᵐ ω ∂P, ∀ q : configOuter d × configOuter d, 0 ≤ (Ξ ω).1 q := by
    filter_upwards [hOeq] with ω ⟨hl, _, hEq, _⟩ q
    rw [hEq]
    exact configSharpInternalCoord_nonneg ξ Q D (h ω) hl _ _ hr z q
  have hOt0 : ∀ᵐ ω ∂P, ∀ q : configOuter d × configOuter d, 0 ≤ (Ξ ω).2.1 q := by
    filter_upwards [hOeq] with ω ⟨_, hlt, _, hEq⟩ q
    rw [hEq]
    exact configSharpInternalCoord_nonneg ξ Q Dt (h ω) hlt _ _ hr z q
  have hI0 : ∀ᵐ ω ∂P, ∀ q : configInner d × configInner d, 0 ≤ (Ξ ω).2.2.1 q := by
    filter_upwards [hIeq] with ω ⟨hl, _, hEq, _⟩ q
    rw [hEq]
    exact configSharpInternalCoord_nonneg ξ Q D (h ω) hl _ _ hr z q
  have hIt0 : ∀ᵐ ω ∂P, ∀ q : configInner d × configInner d, 0 ≤ (Ξ ω).2.2.2 q := by
    filter_upwards [hIeq] with ω ⟨_, hlt, _, hEq⟩ q
    rw [hEq]
    exact configSharpInternalCoord_nonneg ξ Q Dt (h ω) hlt _ _ hr z q
  have ⟨hO, hOt⟩ := Hβo P h r hr z
    (fun ω => (Ξ ω).1) (fun ω => (Ξ ω).2.1) hO0 hOt0 hOeq hh
  have ⟨hI, hIt⟩ := Hβi P h r hr z
    (fun ω => (Ξ ω).2.2.1) (fun ω => (Ξ ω).2.2.2) hI0 hIt0 hIeq hh
  have hbad : P {ω | Ξ ω ∉ configBoundSet β} < ε := by
    let E₁ : Set Ω := {ω | (Ξ ω).1 ∉ configBoundOne (configOuterExhaust d) βo}
    let E₂ : Set Ω := {ω | (Ξ ω).2.1 ∉ configBoundOne (configOuterExhaust d) βo}
    let E₃ : Set Ω := {ω | (Ξ ω).2.2.1 ∉ configBoundOne (configInnerExhaust d) βi}
    let E₄ : Set Ω := {ω | (Ξ ω).2.2.2 ∉ configBoundOne (configInnerExhaust d) βi}
    have hsub : {ω | Ξ ω ∉ configBoundSet β} ⊆ E₁ ∪ (E₂ ∪ (E₃ ∪ E₄)) := by
      intro ω hω
      simpa only [configBoundSet, β, not_and_or, mem_union, mem_ofPred_eq,
        not_and, E₁, E₂, E₃, E₄] using hω
    calc
      P _ ≤ P (E₁ ∪ (E₂ ∪ (E₃ ∪ E₄))) := measure_mono hsub
      _ ≤ P E₁ + (P E₂ + (P E₃ + P E₄)) := by
        exact (measure_union_le _ _).trans
          (add_le_add le_rfl ((measure_union_le _ _).trans
            (add_le_add le_rfl (measure_union_le _ _))))
      _ ≤ (3 * ∑' k, w k) + ((3 * ∑' k, w k) +
          ((3 * ∑' k, w k) + (3 * ∑' k, w k))) :=
        add_le_add hO (add_le_add hOt (add_le_add hI hIt))
      _ = 12 * ∑' k, w k := by ring
      _ < ε := hbudget
  have hBm : MeasurableSet {ω | Ξ ω ∈ configBoundSet β} :=
    (configBoundSet_isClosed β).measurableSet.preimage hΞm
  have hgood : 1 - ε ≤ P {ω | Ξ ω ∈ configBoundSet β} := by
    have hbc : P {ω | Ξ ω ∈ configBoundSet β} =
        1 - P {ω | Ξ ω ∉ configBoundSet β} := by
      have h := prob_compl_eq_one_sub (μ := P) hBm.compl
      simpa only [Set.compl_ofPred, not_not] using h
    rw [hbc]
    exact tsub_le_tsub_left hbad.le 1
  exact ⟨Ξ, hΞm, hΞae, hbad, hgood⟩

/-- D-SF5 under the paper's parameter range. The allowed (E5) moment
exponent is chosen halfway to its positive upper endpoint. -/
theorem config_DSF5_of_params
    {d : ℕ} (hd : 2 ≤ d) (ξ Q : ℝ)
    (hξ : 0 < ξ) (hQ : Real.sqrt (2 * d) < Q)
    (D Dt : DistRd d → ContMetric d)
    (hD : IsSharpWeakExpMetric d ξ Q D)
    (hDt : IsSharpWeakExpMetric d ξ Q Dt)
    (hE5 : E5SharpMoment d ξ Q D)
    (hE5t : E5SharpMoment d ξ Q Dt)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ β : ConfigBounds d,
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (h : Ω → DistRd d)
        (_hh : IsWholeSpaceLGF h P) (r : ℝ) (hr : 0 < r) (z : Rd d),
      ∃ Ξ : Ω → ConfigC d, Measurable Ξ ∧
        (∀ᵐ ω ∂P, ∃ (hl : (D (h ω)).IsLength)
          (hlt : (Dt (h ω)).IsLength),
          Ξ ω = configC hd (D (h ω)) (Dt (h ω)) hl hlt
            (sNorm_pos ξ Q (h ω) hr z) hr z) ∧
        P {ω | Ξ ω ∉ configBoundSet β} < ε ∧
        1 - ε ≤ P {ω | Ξ ω ∈ configBoundSet β} := by
  have hQ0 : 0 < Q := (Real.sqrt_nonneg _).trans_lt hQ
  have hendpoint : 0 < (Q + Real.sqrt (Q ^ 2 - 2 * d)) / ξ :=
    div_pos (add_pos_of_pos_of_nonneg hQ0 (Real.sqrt_nonneg _)) hξ
  let p : ℝ := ((Q + Real.sqrt (Q ^ 2 - 2 * d)) / ξ) / 2
  have hp : 0 < p := half_pos hendpoint
  have hpmax : p < (Q + Real.sqrt (Q ^ 2 - 2 * d)) / ξ := by
    dsimp [p]
    linarith
  exact config_DSF5 hd ξ Q D Dt hD hDt hE5 hE5t hp hpmax hε

/-- Under the pairwise comparison used to define `Orig`, the D-SF5 mass
bound also holds for the compact family `C(β)`. -/
theorem config_DSF5_compactFamily
    {d : ℕ} (hd : 2 ≤ d) (ξ Q : ℝ)
    (hξ : 0 < ξ) (hQ : Real.sqrt (2 * d) < Q)
    (D Dt : DistRd d → ContMetric d)
    (hD : IsSharpWeakExpMetric d ξ Q D)
    (hDt : IsSharpWeakExpMetric d ξ Q Dt)
    (hE5 : E5SharpMoment d ξ Q D)
    (hE5t : E5SharpMoment d ξ Q Dt)
    (c C : ℝ) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ β : ConfigBounds d,
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (h : Ω → DistRd d)
        (_hh : IsWholeSpaceLGF h P) (r : ℝ) (hr : 0 < r) (z : Rd d)
        (_hcmp : ∀ᵐ ω ∂P, ∀ u v : Rd d,
          c * (D (h ω)).1 (u,v) ≤ (Dt (h ω)).1 (u,v) ∧
          (Dt (h ω)).1 (u,v) ≤ C * (D (h ω)).1 (u,v)),
      ∃ Ξ : Ω → ConfigC d, Measurable Ξ ∧
        (∀ᵐ ω ∂P, ∃ (hl : (D (h ω)).IsLength)
          (hlt : (Dt (h ω)).IsLength),
          Ξ ω = configC hd (D (h ω)) (Dt (h ω)) hl hlt
            (sNorm_pos ξ Q (h ω) hr z) hr z) ∧
        1 - ε ≤ P {ω | Ξ ω ∈ configCompactFamily hd c C β} := by
  obtain ⟨β, Hβ⟩ := config_DSF5_of_params hd ξ Q hξ hQ D Dt hD hDt hE5 hE5t hε
  refine ⟨β, ?_⟩
  intro Ω _ P _ h hh r hr z hcmp
  obtain ⟨Ξ, hΞm, hΞae, _, hBmass⟩ := Hβ P h hh r hr z
  have hsub : ∀ᵐ ω ∂P, ω ∈ {ω | Ξ ω ∈ configBoundSet β} →
      ω ∈ {ω | Ξ ω ∈ configCompactFamily hd c C β} := by
    filter_upwards [hΞae, hcmp] with ω ⟨hl, hlt, hEq⟩ hcmpω hω
    have hOrig : Ξ ω ∈ configOriginal hd c C := by
      rw [hEq]
      exact configC_mem_original hd (D (h ω)) (Dt (h ω)) hl hlt
        (sNorm_pos ξ Q (h ω) hr z) hr z (hcmpω)
    exact subset_closure ⟨hOrig, hω⟩
  exact ⟨Ξ, hΞm, hΞae, hBmass.trans (measure_mono_ae hsub)⟩

end HigherDimLQGMetric
