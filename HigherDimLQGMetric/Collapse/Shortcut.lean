import HigherDimLQGMetric.Collapse.Lemma31b
import HigherDimLQGMetric.Coord.ConfinedLimit

/-! # Transferring a marked graph shortcut to weighted geodesics -/

set_option autoImplicit false

open Set Filter Topology
open scoped ENNReal

namespace HigherDimLQGMetric

open LQGMetric.MetricGeometry

/-- Weighted length additivity needs the triangle inequality only on the curve image. -/
theorem weightedLengthWith_add_on {X : Type*} {E : X → X → ℝ≥0∞}
    {w : X → ℝ} {P : ℝ → X} {Y : Set X} {a b c : ℝ}
    (htri : ∀ p ∈ Y, ∀ q ∈ Y, ∀ r ∈ Y,
      E p r ≤ E p q + E q r)
    (hPY : MapsTo P (Icc a c) Y)
    (hab : a ≤ b) (hbc : b ≤ c) :
    weightedLengthWith E w P a b + weightedLengthWith E w P b c =
      weightedLengthWith E w P a c := by
  unfold weightedLengthWith
  refine partitionSup_add (fun u x v hau hux hxv hvc => ?_) hab hbc
  have hlen := curveLengthWith_add (δ := E) (P := P)
    (fun p q r hup hpq hqr hrv =>
      htri (P p) (hPY ⟨hau.trans hup, (hpq.trans hqr).trans (hrv.trans hvc)⟩)
        (P q) (hPY ⟨hau.trans (hup.trans hpq), hqr.trans (hrv.trans hvc)⟩)
        (P r) (hPY ⟨hau.trans (hup.trans (hpq.trans hqr)), hrv.trans hvc⟩))
    hux hxv
  rw [← hlen, mul_add]
  exact add_le_add (mul_le_mul' (infAlong_anti le_rfl hxv) le_rfl)
    (mul_le_mul' (infAlong_anti hux le_rfl) le_rfl)

/-- Path concatenation for a distance function satisfying triangle only on the
confinement set. -/
theorem coordinatePathWeightedLength_trans_on {X : Type*} [TopologicalSpace X]
    {E : X → X → ℝ≥0∞} {Y : Set X}
    (htri : ∀ p ∈ Y, ∀ q ∈ Y, ∀ r ∈ Y,
      E p r ≤ E p q + E q r)
    (w : X → ℝ) {x y z : X} (γ : Path x y) (γ' : Path y z)
    (hγ : ∀ t : unitInterval, γ t ∈ Y)
    (hγ' : ∀ t : unitInterval, γ' t ∈ Y) :
    coordinatePathWeightedLength E w (γ.trans γ') =
      coordinatePathWeightedLength E w γ +
        coordinatePathWeightedLength E w γ' := by
  have htrans : ∀ t : unitInterval, (γ.trans γ') t ∈ Y := by
    intro t
    rw [Path.trans_apply]
    split_ifs
    · exact hγ _
    · exact hγ' _
  unfold coordinatePathWeightedLength
  rw [← weightedLengthWith_add_on htri
    (P := (γ.trans γ').extend) (Y := Y)
    (fun t ht => by rw [Path.extend_apply _ ht]; exact htrans ⟨t, ht⟩)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1)]
  have h1 : weightedLengthWith E w (γ.trans γ').extend 0 (1 / 2) =
      weightedLengthWith E w γ.extend 0 1 := by
    rw [weightedLengthWith_congr_path (Q := γ.extend ∘ fun t => 2 * t)
      (fun t ht => Path.extend_trans_of_le_half _ _ ht.2)]
    rw [weightedLengthWith_comp_monotoneOn E w γ.extend (by norm_num) (by fun_prop)
      (fun s _ t _ hst => by linarith)]
    norm_num
  have h2 : weightedLengthWith E w (γ.trans γ').extend (1 / 2) 1 =
      weightedLengthWith E w γ'.extend 0 1 := by
    rw [weightedLengthWith_congr_path (Q := γ'.extend ∘ fun t => 2 * t - 1)
      (fun t ht => Path.extend_trans_of_half_le _ _ ht.1)]
    rw [weightedLengthWith_comp_monotoneOn E w γ'.extend (by norm_num) (by fun_prop)
      (fun s _ t _ hst => by linarith)]
    norm_num
  rw [h1, h2]

/-- Confined weighted distance has the triangle inequality when `E` has it on
the confinement set. -/
theorem weylDistOnWith_triangle_on {X : Type*} [MetricSpace X]
    (E : X → X → ℝ≥0∞) (Y : Set X)
    (htri : ∀ p ∈ Y, ∀ q ∈ Y, ∀ r ∈ Y,
      E p r ≤ E p q + E q r)
    (w : X → ℝ) (x y z : X) :
    weylDistOnWith E w Y x z ≤
      weylDistOnWith E w Y x y + weylDistOnWith E w Y y z := by
  rw [← tsub_le_iff_right]
  unfold weylDistOnWith
  refine le_iInf fun P₁ => le_iInf fun hc₁ => le_iInf fun h₁0 =>
    le_iInf fun h₁1 => le_iInf fun hY₁ => ?_
  rw [tsub_le_iff_right, ← tsub_le_iff_left]
  refine le_iInf fun P₂ => le_iInf fun hc₂ => le_iInf fun h₂0 =>
    le_iInf fun h₂1 => le_iInf fun hY₂ => ?_
  rw [tsub_le_iff_left]
  let γ₁ : Path x y := Path.ofLine hc₁ h₁0 h₁1
  let γ₂ : Path y z := Path.ofLine hc₂ h₂0 h₂1
  have hγ₁Y : ∀ t : unitInterval, γ₁ t ∈ Y := fun t => hY₁ t.property
  have hγ₂Y : ∀ t : unitInterval, γ₂ t ∈ Y := fun t => hY₂ t.property
  have htransY : ∀ t : unitInterval, (γ₁.trans γ₂) t ∈ Y := by
    intro t
    rw [Path.trans_apply]
    split_ifs
    · exact hγ₁Y _
    · exact hγ₂Y _
  have hcost₁ : coordinatePathWeightedLength E w γ₁ =
      weightedLengthWith E w P₁ 0 1 := by
    unfold coordinatePathWeightedLength
    apply weightedLengthWith_congr_path
    intro t ht
    rw [Path.extend_apply _ ht]
    rfl
  have hcost₂ : coordinatePathWeightedLength E w γ₂ =
      weightedLengthWith E w P₂ 0 1 := by
    unfold coordinatePathWeightedLength
    apply weightedLengthWith_congr_path
    intro t ht
    rw [Path.extend_apply _ ht]
    rfl
  calc
    weylDistOnWith E w Y x z ≤ coordinatePathWeightedLength E w (γ₁.trans γ₂) :=
      weylDistOnWith_le (P := (γ₁.trans γ₂).extend)
        (γ₁.trans γ₂).continuous_extend.continuousOn
        (γ₁.trans γ₂).extend_zero (γ₁.trans γ₂).extend_one
        (fun t ht => by rw [Path.extend_apply _ ht]; exact htransY ⟨t, ht⟩)
    _ = weightedLengthWith E w P₁ 0 1 + weightedLengthWith E w P₂ 0 1 := by
      rw [coordinatePathWeightedLength_trans_on htri w γ₁ γ₂ hγ₁Y hγ₂Y,
        hcost₁, hcost₂]

/-- Reversing an arc preserves its `E`-length when `E` is symmetric on the arc image. -/
theorem curveLengthWith_reflect_of_symm {X : Type*} {E : X → X → ℝ≥0∞}
    {Y : Set X} {arc : ℝ → X}
    (hEsymm : ∀ p ∈ Y, ∀ q ∈ Y, E p q = E q p)
    (hArcY : MapsTo arc (Icc 0 1) Y) :
    curveLengthWith E (fun r => arc (1 - r)) 0 1 =
      curveLengthWith E arc 0 1 := by
  unfold curveLengthWith
  rw [← partitionSup_reflect (fun u v => E (arc u) (arc v)) 0 1]
  apply partitionSup_congr
  intro u v hu huv hv
  simp only [zero_add]
  exact hEsymm (arc (1 - u))
    (hArcY ⟨by linarith [hv], by linarith [hu]⟩)
    (arc (1 - v))
    (hArcY ⟨by linarith [hv], by linarith [hu]⟩)

/-- A strict bound for the confined `E` weighted distance has a witnessing curve. -/
theorem exists_weighted_competitor_with {X : Type*} [MetricSpace X]
    {E : X → X → ℝ≥0∞} {w : X → ℝ} {Y : Set X} {x y : X} {B : ℝ≥0∞}
    (h : weylDistOnWith E w Y x y < B) :
    ∃ S : ℝ → X, ContinuousOn S (Icc 0 1) ∧ S 0 = x ∧ S 1 = y ∧
      MapsTo S (Icc 0 1) Y ∧ weightedLengthWith E w S 0 1 < B := by
  unfold weylDistOnWith at h
  obtain ⟨P, hP⟩ := iInf_lt_iff.mp h
  obtain ⟨hc, hP⟩ := iInf_lt_iff.mp hP
  obtain ⟨h0, hP⟩ := iInf_lt_iff.mp hP
  obtain ⟨h1, hP⟩ := iInf_lt_iff.mp hP
  obtain ⟨hY, hP⟩ := iInf_lt_iff.mp hP
  exact ⟨P, hc, h0, h1, hY, hP⟩

/-- The `E`-weighted cost of a marked arc on which the weight is constant. -/
theorem marked_arc_weighted_cost {X : Type*} [MetricSpace X]
    {E : X → X → ℝ≥0∞} {w : X → ℝ} {K Y : Set X}
    {lam c₀ : ℝ} {u v : X} {σ : ℝ → X}
    (hKY : K ⊆ Y) (hσc : ContinuousOn σ (Icc 0 1))
    (hσ0 : σ 0 = u) (hσ1 : σ 1 = v)
    (hσK : MapsTo σ (Icc 0 1) K)
    (hwK : ∀ p ∈ K, w p = lam)
    (hσlen : curveLengthWith E σ 0 1 ≤ ENNReal.ofReal c₀ * edist u v) :
    weylDistOnWith E w Y u v ≤
      ENNReal.ofReal lam * (ENNReal.ofReal c₀ * edist u v) := by
  apply (weylDistOnWith_le hσc hσ0 hσ1 (hσK.mono_right hKY)).trans
  calc
    weightedLengthWith E w σ 0 1 ≤ ENNReal.ofReal lam * curveLengthWith E σ 0 1 :=
      weightedLengthWith_le_ofReal_mul_curveLengthWith
        (fun t ht => (hwK (σ t) (hσK ht)).le)
    _ ≤ ENNReal.ofReal lam * (ENNReal.ofReal c₀ * edist u v) :=
      mul_le_mul_right hσlen _

/-- Three confined pieces realize a strict shortcut once their proven cost budget
is below the cost of the geodesic subcurve. -/
theorem shortcut_from_marked_arc {X : Type*} [MetricSpace X]
    {Y K : Set X} {E : X → X → ℝ≥0∞} {w : X → ℝ}
    {M lam c₀ : ℝ} {u v p q : X} {σ : ℝ → X} {C : ℝ≥0∞}
    (hM : 0 < M)
    (hEtri : ∀ x ∈ Y, ∀ y ∈ Y, ∀ z ∈ Y,
      E x z ≤ E x y + E y z)
    (hEM : ∀ x ∈ Y, ∀ y ∈ Y, E x y ≤ ENNReal.ofReal M * edist x y)
    (hKY : K ⊆ Y) (hσc : ContinuousOn σ (Icc 0 1))
    (hσ0 : σ 0 = u) (hσ1 : σ 1 = v)
    (hσK : MapsTo σ (Icc 0 1) K)
    (hwK : ∀ z ∈ K, w z = lam)
    (hσlen : curveLengthWith E σ 0 1 ≤ ENNReal.ofReal c₀ * edist u v)
    (hbudget : ENNReal.ofReal M * weylDistOn w Y p u +
        ENNReal.ofReal lam * (ENNReal.ofReal c₀ * edist u v) +
        ENNReal.ofReal M * weylDistOn w Y v q < C) :
    ∃ S : ℝ → X, ContinuousOn S (Icc 0 1) ∧ S 0 = p ∧ S 1 = q ∧
      MapsTo S (Icc 0 1) Y ∧ weightedLengthWith E w S 0 1 < C := by
  have hcomp (x y : X) : weylDistOnWith E w Y x y ≤
      ENNReal.ofReal M * weylDistOn w Y x y := by
    exact (weylDistOnWith_compare
      (m := 0) (M := ENNReal.ofReal M)
      (fun _ _ _ _ => by simp) hEM
      (ENNReal.ofReal_pos.mpr hM).ne' ENNReal.ofReal_ne_top x y).2
  have hmiddle := marked_arc_weighted_cost hKY hσc hσ0 hσ1 hσK hwK hσlen
  have hbound : weylDistOnWith E w Y p q < C := by
    calc
      weylDistOnWith E w Y p q ≤
          weylDistOnWith E w Y p u + weylDistOnWith E w Y u q :=
        weylDistOnWith_triangle_on E Y hEtri w p u q
      _ ≤ weylDistOnWith E w Y p u +
          (weylDistOnWith E w Y u v + weylDistOnWith E w Y v q) :=
        add_le_add_right (weylDistOnWith_triangle_on E Y hEtri w u v q) _
      _ = weylDistOnWith E w Y p u +
          weylDistOnWith E w Y u v + weylDistOnWith E w Y v q := by
        rw [add_assoc]
      _ ≤ ENNReal.ofReal M * weylDistOn w Y p u +
          ENNReal.ofReal lam * (ENNReal.ofReal c₀ * edist u v) +
          ENNReal.ofReal M * weylDistOn w Y v q :=
        add_le_add (add_le_add (hcomp p u) hmiddle) (hcomp v q)
      _ < C := hbudget
  exact exists_weighted_competitor_with hbound

/-- Convert two normalized connection estimates and the strict slope gap into
the extended-real budget used by `shortcut_from_marked_arc`. -/
theorem marked_arc_shortcut_budget
    {lam M c₀ c₁ ε d D : ℝ} {A B : ℝ≥0∞}
    (hlam : 0 < lam) (hM : 0 ≤ M) (hc₀ : 0 ≤ c₀)
    (hε : 0 ≤ ε) (hd : 0 ≤ d)
    (hA : (ENNReal.ofReal lam)⁻¹ * A < ENNReal.ofReal ε)
    (hB : (ENNReal.ofReal lam)⁻¹ * B < ENNReal.ofReal ε)
    (hgap : 2 * M * ε + c₀ * d < c₁ * D) :
    ENNReal.ofReal M * A +
      ENNReal.ofReal lam * (ENNReal.ofReal c₀ * ENNReal.ofReal d) +
      ENNReal.ofReal M * B < ENNReal.ofReal (lam * (c₁ * D)) := by
  have hLam0 : ENNReal.ofReal lam ≠ 0 := (ENNReal.ofReal_pos.mpr hlam).ne'
  have hLamt : ENNReal.ofReal lam ≠ ⊤ := ENNReal.ofReal_ne_top
  have hcancel (Z : ℝ≥0∞) :
      ENNReal.ofReal lam * ((ENNReal.ofReal lam)⁻¹ * Z) = Z := by
    rw [← mul_assoc, ENNReal.mul_inv_cancel hLam0 hLamt, one_mul]
  have hA' : A ≤ ENNReal.ofReal (lam * ε) := by
    calc
      A = ENNReal.ofReal lam * ((ENNReal.ofReal lam)⁻¹ * A) := (hcancel A).symm
      _ ≤ ENNReal.ofReal lam * ENNReal.ofReal ε := mul_le_mul_right (le_of_lt hA) _
      _ = ENNReal.ofReal (lam * ε) := (ENNReal.ofReal_mul hlam.le).symm
  have hB' : B ≤ ENNReal.ofReal (lam * ε) := by
    calc
      B = ENNReal.ofReal lam * ((ENNReal.ofReal lam)⁻¹ * B) := (hcancel B).symm
      _ ≤ ENNReal.ofReal lam * ENNReal.ofReal ε := mul_le_mul_right (le_of_lt hB) _
      _ = ENNReal.ofReal (lam * ε) := (ENNReal.ofReal_mul hlam.le).symm
  have hnum : 0 ≤ 2 * M * ε + c₀ * d := by positivity
  have hfirst : 0 ≤ M * (lam * ε) :=
    mul_nonneg hM (mul_nonneg hlam.le hε)
  have hmid : 0 ≤ lam * (c₀ * d) :=
    mul_nonneg hlam.le (mul_nonneg hc₀ hd)
  calc
    ENNReal.ofReal M * A +
        ENNReal.ofReal lam * (ENNReal.ofReal c₀ * ENNReal.ofReal d) +
        ENNReal.ofReal M * B ≤
      ENNReal.ofReal M * ENNReal.ofReal (lam * ε) +
        ENNReal.ofReal lam * (ENNReal.ofReal c₀ * ENNReal.ofReal d) +
        ENNReal.ofReal M * ENNReal.ofReal (lam * ε) := by
      exact add_le_add (add_le_add (mul_le_mul_right hA' _) le_rfl)
        (mul_le_mul_right hB' _)
    _ = ENNReal.ofReal (lam * (2 * M * ε + c₀ * d)) := by
      rw [← ENNReal.ofReal_mul hM, ← ENNReal.ofReal_mul hc₀,
        ← ENNReal.ofReal_mul hlam.le]
      rw [← ENNReal.ofReal_add hfirst hmid,
        ← ENNReal.ofReal_add (add_nonneg hfirst hmid) hfirst]
      congr 1
      ring
    _ < ENNReal.ofReal (lam * (c₁ * D)) := by
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).2
        (mul_lt_mul_of_pos_left hgap hlam)

/-- Pointwise shortcut transfer at the two marked endpoint times. -/
theorem shortcut_at_marked_times {X : Type*} [MetricSpace X]
    {Y K : Set X} {E : X → X → ℝ≥0∞} {w : X → ℝ}
    {M lam c₀ c₁ ε a₁ s τ : ℝ} {u v : X} {σ P : ℝ → X}
    (hM : 0 < M) (hlam : 0 < lam) (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁)
    (hε : 0 ≤ ε)
    (hEtri : ∀ x ∈ Y, ∀ y ∈ Y, ∀ z ∈ Y,
      E x z ≤ E x y + E y z)
    (hEM : ∀ x ∈ Y, ∀ y ∈ Y, E x y ≤ ENNReal.ofReal M * edist x y)
    (hKY : K ⊆ Y) (hσc : ContinuousOn σ (Icc 0 1))
    (hσ0 : σ 0 = u) (hσ1 : σ 1 = v)
    (hσK : MapsTo σ (Icc 0 1) K)
    (hwK : ∀ z ∈ K, w z = lam)
    (hσlen : curveLengthWith E σ 0 1 ≤
      ENNReal.ofReal c₀ * edist u v)
    (hA : (ENNReal.ofReal lam)⁻¹ * weylDistOn w Y (P s) u < ENNReal.ofReal ε)
    (hB : (ENNReal.ofReal lam)⁻¹ * weylDistOn w Y v (P τ) < ENNReal.ofReal ε)
    (hgap : 2 * M * ε + c₀ * dist u v < c₁ * (τ - s))
    (hspan : a₁ / 2 ≤ τ - s)
    (hcost : weightedLength w P s τ = ENNReal.ofReal (lam * (τ - s))) :
    ENNReal.ofReal (lam * (a₁ / 2)) ≤ weightedLength w P s τ ∧
      ∃ S : ℝ → X, ContinuousOn S (Icc 0 1) ∧ S 0 = P s ∧ S 1 = P τ ∧
        MapsTo S (Icc 0 1) Y ∧
          weightedLengthWith E w S 0 1 <
            ENNReal.ofReal c₁ * weightedLength w P s τ := by
  have hlow : ENNReal.ofReal (lam * (a₁ / 2)) ≤ weightedLength w P s τ := by
    rw [hcost]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hspan hlam.le)
  have hbudget : ENNReal.ofReal M * weylDistOn w Y (P s) u +
      ENNReal.ofReal lam * (ENNReal.ofReal c₀ * edist u v) +
      ENNReal.ofReal M * weylDistOn w Y v (P τ) <
      ENNReal.ofReal (lam * (c₁ * (τ - s))) := by
    rw [edist_dist]
    exact marked_arc_shortcut_budget hlam hM.le hc₀ hε dist_nonneg hA hB hgap
  obtain ⟨S, hSc, hS0, hS1, hSY, hScost⟩ :=
    shortcut_from_marked_arc hM hEtri hEM hKY hσc hσ0 hσ1 hσK hwK hσlen hbudget
  refine ⟨hlow, S, hSc, hS0, hS1, hSY, ?_⟩
  calc
    weightedLengthWith E w S 0 1 <
        ENNReal.ofReal (lam * (c₁ * (τ - s))) := hScost
    _ = ENNReal.ofReal c₁ * weightedLength w P s τ := by
      rw [hcost, ← ENNReal.ofReal_mul hc₁]
      congr 1
      ring

end HigherDimLQGMetric
