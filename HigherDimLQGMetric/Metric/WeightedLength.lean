import HigherDimLQGMetric.Metric.Partition
import LQGMetric.Metric.WeylConcat

/-!
# Weighted lengths of curves (the integrals `∫_P w ds_D` of the source's Lemma 2.1)

Packet M1 (Phase A, block A2): the generic layer of the source's Lemma 2.1 (blueprint
`s2-compact.tex`, §`ssec:weighted` and Lemma `lem:21`; MA1 A2), for a pseudo-extended-metric space
`X` (any metric space, e.g. `(ℝ^d, D)` or a configuration coordinate on an open set).

For a curve `P : [a, b] → X` and a weight `w : X → ℝ`,
`weightedLength w P a b = ∫_P w ds = sup ∑_i (inf_{[t_i, t_{i+1}]} w ∘ P) · len(P|[t_i, t_{i+1}])`
(lower Darboux–Stieltjes sums over partitions; MA1's shape, `weightedLength_eq_iSup`). The infima
are taken in `[0, ∞]` (`infAlong`; they agree with MA1's real infima, `ofReal_iInf_eq_infAlong`).
`weightedLengthWith δ` measures the pieces with an arbitrary distance function `δ`.

* Bounds: `ofReal_mul_curveLength_le_weightedLength` (`m ≤ w` along `P`),
  `weightedLength_le_ofReal_mul_curveLength` (`w ≤ M` along `P`); infinite/finite weighted length
  (`weightedLength_eq_top`, `weightedLength_ne_top`).
* Monotone in the weight, local in the weight and the curve (`weightedLength_mono_weight`,
  `weightedLength_congr_weight`, `weightedLength_congr`).
* Additivity over adjacent intervals (`weightedLength_add`) and monotonicity in the interval.
* Invariance under continuous monotone reparametrization (`weightedLength_comp_monotoneOn`) and
  under reversal (`weightedLength_comp_reflect`).
* For a unit-speed curve, `∫_P w ds = ∫_a^b w(P t) dt` (`weightedLength_of_hasUnitSpeedOn`).

The comparison of metrics (Lemma 2.1(d): `lemma21_compare`, `weightedLengthWith_compare`) is in
`HigherDimLQGMetric.Metric.Lemma21`.

Elementary partition arguments; own proofs.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace HigherDimLQGMetric

open LQGMetric.MetricGeometry

/-! ### Infima along a curve -/

section InfAlong

variable {X : Type*} {w w' : X → ℝ} {P Q : ℝ → X} {u v u' v' : ℝ}

/-- `inf_{s ∈ [u, v]} w (P s)`, in `[0, ∞]` (negative weights count as `0`). -/
def infAlong (w : X → ℝ) (P : ℝ → X) (u v : ℝ) : ℝ≥0∞ :=
  ⨅ s ∈ Icc u v, ENNReal.ofReal (w (P s))

theorem infAlong_le {s : ℝ} (hs : s ∈ Icc u v) : infAlong w P u v ≤ ENNReal.ofReal (w (P s)) :=
  iInf₂_le s hs

theorem le_infAlong {c : ℝ≥0∞} (h : ∀ s ∈ Icc u v, c ≤ ENNReal.ofReal (w (P s))) :
    c ≤ infAlong w P u v :=
  le_iInf₂ h

theorem ofReal_le_infAlong {m : ℝ} (h : ∀ s ∈ Icc u v, m ≤ w (P s)) :
    ENNReal.ofReal m ≤ infAlong w P u v :=
  le_infAlong fun s hs => ENNReal.ofReal_le_ofReal (h s hs)

theorem infAlong_anti (hu : u ≤ u') (hv : v' ≤ v) : infAlong w P u v ≤ infAlong w P u' v' :=
  le_infAlong fun _ hs => infAlong_le ⟨hu.trans hs.1, hs.2.trans hv⟩

theorem infAlong_le_ofReal {M : ℝ} (huv : u ≤ v) (h : ∀ s ∈ Icc u v, w (P s) ≤ M) :
    infAlong w P u v ≤ ENNReal.ofReal M :=
  (infAlong_le ⟨le_rfl, huv⟩).trans (ENNReal.ofReal_le_ofReal (h u ⟨le_rfl, huv⟩))

theorem infAlong_ne_top (huv : u ≤ v) : infAlong w P u v ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (infAlong_le ⟨le_rfl, huv⟩)

theorem infAlong_mono_weight (h : ∀ s ∈ Icc u v, w (P s) ≤ w' (P s)) :
    infAlong w P u v ≤ infAlong w' P u v :=
  le_infAlong fun s hs => (infAlong_le hs).trans (ENNReal.ofReal_le_ofReal (h s hs))

theorem infAlong_congr (h : ∀ s ∈ Icc u v, w (P s) = w' (Q s)) :
    infAlong w P u v = infAlong w' Q u v := by
  simp only [infAlong]
  exact iInf_congr fun s => iInf_congr fun hs => by rw [h s hs]

/-- MA1's real infimum `⨅ s : Icc u v, w (P s)` clamped at `0` is `infAlong`. -/
theorem ofReal_iInf_eq_infAlong (huv : u ≤ v) :
    ENNReal.ofReal (⨅ s : Icc u v, w (P s)) = infAlong w P u v := by
  have : Nonempty (Icc u v) := ⟨⟨u, le_rfl, huv⟩⟩
  rw [infAlong, ← iInf_subtype'' (Icc u v) (fun s => ENNReal.ofReal (w (P s)))]
  by_cases hb : BddBelow (range fun s : Icc u v => w (P s))
  · exact Monotone.map_ciInf_of_continuousAt ENNReal.continuous_ofReal.continuousAt
      (fun _ _ h => ENNReal.ofReal_le_ofReal h) hb
  · rw [Real.iInf_of_not_bddBelow hb, ENNReal.ofReal_zero]
    obtain ⟨s, hs⟩ : ∃ s : Icc u v, w (P s) < 0 := by
      by_contra hne
      refine hb ⟨0, ?_⟩
      rintro _ ⟨s, rfl⟩
      exact not_lt.1 fun h => hne ⟨s, h⟩
    exact le_antisymm bot_le ((iInf_le _ s).trans (ENNReal.ofReal_eq_zero.2 hs.le).le)

/-- Reparametrization of the infimum by a continuous monotone `φ`. -/
theorem infAlong_comp_monotoneOn {φ : ℝ → ℝ} (huv : u ≤ v) (hφc : ContinuousOn φ (Icc u v))
    (hφm : MonotoneOn φ (Icc u v)) : infAlong w (P ∘ φ) u v = infAlong w P (φ u) (φ v) := by
  simp only [infAlong]
  rw [← hφc.image_Icc_of_monotoneOn huv hφm, iInf_image]
  rfl

/-- Reversal of the infimum. -/
theorem infAlong_comp_reflect (c d : ℝ) :
    infAlong w (fun t => P (c + d - t)) u v = infAlong w P (c + d - v) (c + d - u) := by
  simp only [infAlong]
  rw [← image_const_sub_Icc, iInf_image]

end InfAlong

/-! ### Weighted lengths -/

section Weighted

variable {X : Type*}

/-- The weighted length `∫_P w ds_δ`, the pieces measured with a distance function `δ`. -/
def weightedLengthWith (δ : X → X → ℝ≥0∞) (w : X → ℝ) (P : ℝ → X) (a b : ℝ) : ℝ≥0∞ :=
  partitionSup (fun u v => infAlong w P u v * curveLengthWith δ P u v) a b

variable [PseudoEMetricSpace X]

/-- The **weighted length** `∫_P w ds` (lower Darboux–Stieltjes sums; MA1's `weightedLength`, see
`weightedLength_eq_iSup`). -/
def weightedLength (w : X → ℝ) (P : ℝ → X) (a b : ℝ) : ℝ≥0∞ :=
  partitionSup (fun u v => infAlong w P u v * curveLength P u v) a b

variable {w w' : X → ℝ} {P Q : ℝ → X} {a b c : ℝ}

/-- MA1's literal shape of `weightedLength`. -/
theorem weightedLength_eq_iSup (w : X → ℝ) (P : ℝ → X) (a b : ℝ) :
    weightedLength w P a b = ⨆ (n : ℕ) (t : ℕ → ℝ) (_ : MonotoneOn t (Iic n)) (_ : t 0 = a)
      (_ : t n = b), ∑ i ∈ Finset.range n,
        ENNReal.ofReal (⨅ s : Icc (t i) (t (i + 1)), w (P s)) * curveLength P (t i) (t (i + 1)) := by
  rw [weightedLength, partitionSup_eq_iSup]
  refine iSup_congr fun n => iSup_congr fun t => iSup_congr fun ht => iSup_congr fun _ =>
    iSup_congr fun _ => Finset.sum_congr rfl fun i hi => ?_
  have hi' : i < n := Finset.mem_range.1 hi
  rw [ofReal_iInf_eq_infAlong (ht (mem_Iic.2 hi'.le) (mem_Iic.2 hi') (Nat.le_succ i))]

theorem weightedLengthWith_edist (w : X → ℝ) (P : ℝ → X) (a b : ℝ) :
    weightedLengthWith edist w P a b = weightedLength w P a b := by
  simp only [weightedLengthWith, weightedLength, curveLengthWith_edist]

/-- Splitting a piece does not decrease the lower sum. -/
theorem infAlong_mul_curveLength_split {u x v : ℝ} (hux : u ≤ x) (hxv : x ≤ v) :
    infAlong w P u v * curveLength P u v ≤
      infAlong w P u x * curveLength P u x + infAlong w P x v * curveLength P x v := by
  rw [← curveLength_add P hux hxv, mul_add]
  exact add_le_add (mul_le_mul' (infAlong_anti le_rfl hxv) le_rfl)
    (mul_le_mul' (infAlong_anti hux le_rfl) le_rfl)

/-- **Additivity** of weighted length over adjacent intervals. -/
theorem weightedLength_add (hab : a ≤ b) (hbc : b ≤ c) :
    weightedLength w P a b + weightedLength w P b c = weightedLength w P a c :=
  partitionSup_add (fun _ _ _ _ hux hxv _ => infAlong_mul_curveLength_split hux hxv) hab hbc

theorem weightedLength_mono_interval {s t : ℝ} (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b) :
    weightedLength w P s t ≤ weightedLength w P a b :=
  calc weightedLength w P s t ≤ weightedLength w P a s + (weightedLength w P s t +
        weightedLength w P t b) := le_add_self.trans (add_le_add le_rfl le_self_add)
    _ = weightedLength w P a b := by
        rw [weightedLength_add hst htb, weightedLength_add has (hst.trans htb)]

/-- Lower bound: `m ≤ w` along `P` gives `m · len(P) ≤ ∫_P w ds`. -/
theorem ofReal_mul_curveLength_le_weightedLength {m : ℝ} (hab : a ≤ b)
    (h : ∀ s ∈ Icc a b, m ≤ w (P s)) :
    ENNReal.ofReal m * curveLength P a b ≤ weightedLength w P a b :=
  (mul_le_mul' (ofReal_le_infAlong h) le_rfl).trans
    (le_partitionSup_single (g := fun u v => infAlong w P u v * curveLength P u v) hab)

/-- Upper bound: `w ≤ M` along `P` gives `∫_P w ds ≤ M · len(P)`. -/
theorem weightedLength_le_ofReal_mul_curveLength {M : ℝ} (h : ∀ s ∈ Icc a b, w (P s) ≤ M) :
    weightedLength w P a b ≤ ENNReal.ofReal M * curveLength P a b := by
  refine partitionSup_le fun p => ?_
  calc p.sum (fun u v => infAlong w P u v * curveLength P u v)
      ≤ ∑ i ∈ Finset.range p.n, ENNReal.ofReal M * curveLength P (p.t i) (p.t (i + 1)) := by
        refine Finset.sum_le_sum fun i hi => ?_
        obtain ⟨h1, h2, h3⟩ := p.step (Finset.mem_range.1 hi)
        exact mul_le_mul' (infAlong_le_ofReal h2 fun s hs => h s ⟨h1.trans hs.1, hs.2.trans h3⟩)
          le_rfl
    _ = ENNReal.ofReal M * curveLength P a b := by
        rw [← Finset.mul_sum]
        congr 1
        have hmono : Monotone fun i => p.t (min i p.n) := fun i j hij =>
          p.le_t (min_le_min_right p.n hij) (min_le_right _ _)
        have hsum := sum_curveLength_eq P hmono p.n
        simp only [min_self, Nat.zero_min, p.zero, p.last] at hsum
        rw [← hsum]
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [Finset.mem_range] at hi
        rw [min_eq_left hi.le, min_eq_left (by omega)]

theorem weightedLength_self (w : X → ℝ) (P : ℝ → X) (a : ℝ) : weightedLength w P a a = 0 := by
  refine le_antisymm ((weightedLength_le_ofReal_mul_curveLength (M := w (P a)) fun s hs => ?_).trans
    (by rw [curveLength_self, mul_zero])) bot_le
  rw [le_antisymm hs.2 hs.1]

theorem weightedLength_of_lt (h : b < a) : weightedLength w P a b = 0 :=
  partitionSup_of_lt h

/-- **Monotone in the weight.** -/
theorem weightedLength_mono_weight (h : ∀ s ∈ Icc a b, w (P s) ≤ w' (P s)) :
    weightedLength w P a b ≤ weightedLength w' P a b :=
  partitionSup_mono fun _ _ hu _ hv =>
    mul_le_mul' (infAlong_mono_weight fun s hs => h s ⟨hu.trans hs.1, hs.2.trans hv⟩) le_rfl

/-- **Local in the weight**: only the values of `w` along `P([a, b])` matter. -/
theorem weightedLength_congr_weight (h : ∀ s ∈ Icc a b, w (P s) = w' (P s)) :
    weightedLength w P a b = weightedLength w' P a b :=
  le_antisymm (weightedLength_mono_weight fun s hs => (h s hs).le)
    (weightedLength_mono_weight fun s hs => (h s hs).ge)

/-- Only the values of `P` on `[a, b]` matter. -/
theorem weightedLength_congr (h : EqOn P Q (Icc a b)) :
    weightedLength w P a b = weightedLength w Q a b :=
  partitionSup_congr fun _ _ hu _ hv => by
    have hsub : Icc _ _ ⊆ Icc a b := Icc_subset_Icc hu hv
    rw [infAlong_congr fun s hs => by rw [h (hsub hs)], curveLength_congr (h.mono hsub)]

/-- A curve of infinite length along which `w ≥ m > 0` has infinite weighted length. -/
theorem weightedLength_eq_top {m : ℝ} (hm : 0 < m) (hab : a ≤ b)
    (h : ∀ s ∈ Icc a b, m ≤ w (P s)) (hL : curveLength P a b = ⊤) :
    weightedLength w P a b = ⊤ := by
  have := ofReal_mul_curveLength_le_weightedLength hab h
  rw [hL, ENNReal.mul_top (by simpa using hm)] at this
  exact top_le_iff.1 this

/-- A curve of finite length along which `w` is bounded above has finite weighted length. -/
theorem weightedLength_ne_top {M : ℝ} (h : ∀ s ∈ Icc a b, w (P s) ≤ M)
    (hL : curveLength P a b ≠ ⊤) : weightedLength w P a b ≠ ⊤ :=
  ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hL)
    (weightedLength_le_ofReal_mul_curveLength h)

/-- **Reparametrization invariance**: `∫_{P ∘ φ} w ds = ∫_P w ds` for `φ` continuous and monotone
from `[c, d]` onto `[φ c, φ d]`. -/
theorem weightedLength_comp_monotoneOn {φ : ℝ → ℝ} {c d : ℝ} (hcd : c ≤ d)
    (hφc : ContinuousOn φ (Icc c d)) (hφm : MonotoneOn φ (Icc c d)) :
    weightedLength w (P ∘ φ) c d = weightedLength w P (φ c) (φ d) := by
  unfold weightedLength
  rw [← partitionSup_comp hcd hφc hφm]
  refine partitionSup_congr fun u v hu huv hv => ?_
  have hsub : Icc u v ⊆ Icc c d := Icc_subset_Icc hu hv
  rw [infAlong_comp_monotoneOn huv (hφc.mono hsub) (hφm.mono hsub),
    curveLength_comp_of_continuousOn_monotoneOn P huv (hφc.mono hsub) (hφm.mono hsub)]

/-- **Reversal**: `∫_{P(c + d - ·)} w ds = ∫_P w ds` on `[c, d]`. -/
theorem weightedLength_comp_reflect (c d : ℝ) :
    weightedLength w (fun t => P (c + d - t)) c d = weightedLength w P c d := by
  unfold weightedLength
  rw [← partitionSup_reflect (fun u v => infAlong w P u v * curveLength P u v) c d]
  refine partitionSup_congr fun u v _ huv _ => ?_
  rw [infAlong_comp_reflect]
  congr 1
  have := curveLength_comp_of_continuousOn_antitoneOn P (φ := fun t => c + d - t) huv
    (by fun_prop) (fun x _ y _ hxy => by simp only; linarith)
  simpa only [Function.comp_def] using this

/-- Affine reparametrization of `[a, b]` by `[0, 1]`. -/
theorem weightedLength_affine (hab : a ≤ b) :
    weightedLength w (fun s => P (a + s * (b - a))) 0 1 = weightedLength w P a b := by
  have h := weightedLength_comp_monotoneOn (w := w) (P := P) (φ := fun s => a + s * (b - a))
    zero_le_one (by fun_prop) (fun x _ y _ hxy => by
      simp only; nlinarith [sub_nonneg.2 hab])
  simp only [zero_mul, add_zero, one_mul, add_sub_cancel] at h
  exact h

end Weighted

/-! ### Unit-speed curves -/

section UnitSpeed

variable {X : Type*} [PseudoEMetricSpace X] {w : X → ℝ} {P : ℝ → X} {a b : ℝ}

/-- Telescoping set integrals over consecutive intervals `(u i, u (i + 1)]`. -/
theorem sum_setLIntegral_Ioc (F : ℝ → ℝ≥0∞) {u : ℕ → ℝ} (hu : Monotone u) (n : ℕ) :
    ∑ i ∈ Finset.range n, ∫⁻ τ in Ioc (u i) (u (i + 1)), F τ = ∫⁻ τ in Ioc (u 0) (u n), F τ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, ← lintegral_union measurableSet_Ioc
      (Ioc_disjoint_Ioc_of_le le_rfl), Ioc_union_Ioc_eq_Ioc (hu (Nat.zero_le n))
      (hu (Nat.le_succ n))]

/-- The uniform partition of `[a, b]` into `N` intervals of length `(b - a) / N`. -/
def IccPartition.uniform (hab : a ≤ b) (N : ℕ) (hN : 0 < N) : IccPartition a b where
  n := N
  t k := a + k * ((b - a) / N)
  mono := fun i _ j _ hij => by
    have : 0 ≤ (b - a) / N := div_nonneg (sub_nonneg.2 hab) (Nat.cast_nonneg N)
    show a + (i : ℝ) * ((b - a) / N) ≤ a + (j : ℝ) * ((b - a) / N)
    gcongr
  zero := by simp
  last := by
    have : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
    show a + (N : ℝ) * ((b - a) / N) = b
    field_simp
    ring

theorem IccPartition.uniform_t (hab : a ≤ b) (N : ℕ) (hN : 0 < N) (k : ℕ) :
    (IccPartition.uniform hab N hN).t k = a + k * ((b - a) / N) := rfl

theorem IccPartition.uniform_step (hab : a ≤ b) (N : ℕ) (hN : 0 < N) (k : ℕ) :
    (IccPartition.uniform hab N hN).t (k + 1) - (IccPartition.uniform hab N hN).t k =
      (b - a) / N := by
  simp only [IccPartition.uniform_t, Nat.cast_succ]; ring

theorem exists_uniform_fine (hab : a ≤ b) {δ : ℝ} (hδ : 0 < δ) :
    ∃ N : ℕ, 0 < N ∧ (b - a) / N < δ := by
  obtain ⟨N, hN⟩ := exists_nat_gt ((b - a) / δ)
  have hN0 : (0 : ℝ) < N := lt_of_le_of_lt (div_nonneg (sub_nonneg.2 hab) hδ.le) hN
  refine ⟨N, Nat.cast_pos.1 hN0, ?_⟩
  rw [div_lt_iff₀ hN0]
  rw [div_lt_iff₀ hδ] at hN
  linarith

/-- **Unit-speed curves**: `∫_P w ds = ∫_a^b w(P t) dt` when `P` has unit speed on `[a, b]` and
`w ∘ P` is continuous there. -/
theorem weightedLength_of_hasUnitSpeedOn (hab : a ≤ b) (hu : HasUnitSpeedOn P (Icc a b))
    (hw : ContinuousOn (fun t => w (P t)) (Icc a b)) :
    weightedLength w P a b = ∫⁻ τ in Icc a b, ENNReal.ofReal (w (P τ)) := by
  rw [hasUnitSpeedOn_Icc_iff'] at hu
  set F : ℝ → ℝ≥0∞ := fun τ => ENNReal.ofReal (w (P τ)) with hF
  apply le_antisymm
  · refine partitionSup_le fun p => ?_
    have hmono : Monotone fun i => p.t (min i p.n) := fun i j hij =>
      p.le_t (min_le_min_right p.n hij) (min_le_right _ _)
    calc p.sum (fun u v => infAlong w P u v * curveLength P u v)
        ≤ ∑ i ∈ Finset.range p.n, ∫⁻ τ in Ioc (p.t (min i p.n)) (p.t (min (i + 1) p.n)), F τ := by
          refine Finset.sum_le_sum fun i hi => ?_
          have hi' := Finset.mem_range.1 hi
          rw [min_eq_left hi'.le, min_eq_left (by omega)]
          obtain ⟨h1, h2, h3⟩ := p.step hi'
          show infAlong w P (p.t i) (p.t (i + 1)) * curveLength P (p.t i) (p.t (i + 1)) ≤ _
          rw [hu _ _ h1 h2 h3, ← Real.volume_Ioc, ← setLIntegral_const]
          exact setLIntegral_mono' measurableSet_Ioc fun τ hτ => infAlong_le ⟨hτ.1.le, hτ.2⟩
      _ = ∫⁻ τ in Ioc (p.t 0) (p.t p.n), F τ := by
          rw [sum_setLIntegral_Ioc F hmono p.n]
          simp only [Nat.zero_min, min_self]
      _ ≤ ∫⁻ τ in Icc a b, F τ := by
          rw [p.zero, p.last]
          exact lintegral_mono_set Ioc_subset_Icc_self
  · refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    -- uniform continuity of `w ∘ P` and a fine uniform partition
    set ε' : ℝ := ε / (b - a + 1) with hε'
    have hε'pos : 0 < ε' := div_pos (by exact_mod_cast hε) (by linarith)
    obtain ⟨δ, hδ, hδ'⟩ := Metric.uniformContinuousOn_iff.1
      (isCompact_Icc.uniformContinuousOn_of_continuous hw) ε' hε'pos
    obtain ⟨N, hN, hNδ⟩ := exists_uniform_fine hab hδ
    set p := IccPartition.uniform hab N hN with hp
    have hmono : Monotone p.t := fun i j hij => by
      simp only [hp, IccPartition.uniform_t]
      have : 0 ≤ (b - a) / N := div_nonneg (sub_nonneg.2 hab) (Nat.cast_nonneg N)
      gcongr
    have hstep : ∀ k, p.t (k + 1) - p.t k = (b - a) / N := IccPartition.uniform_step hab N hN
    have hh0 : 0 ≤ (b - a) / N := div_nonneg (sub_nonneg.2 hab) (Nat.cast_nonneg N)
    have hpiece : ∀ k < N, ∀ τ ∈ Icc (p.t k) (p.t (k + 1)),
        F τ ≤ infAlong w P (p.t k) (p.t (k + 1)) + ENNReal.ofReal ε' := by
      intro k hk τ hτ
      have hsub : Icc (p.t k) (p.t (k + 1)) ⊆ Icc a b :=
        Icc_subset_Icc (p.mem_Icc hk.le).1 (p.mem_Icc (Nat.succ_le_of_lt hk)).2
      rw [← tsub_le_iff_right]
      refine le_infAlong fun σ hσ => ?_
      rw [tsub_le_iff_right]
      have hdist : dist τ σ < δ := by
        rw [Real.dist_eq, abs_lt]
        have := hstep k
        constructor <;> linarith [hτ.1, hτ.2, hσ.1, hσ.2]
      have h1 := hδ' τ (hsub hτ) σ (hsub hσ) hdist
      rw [Real.dist_eq, abs_lt] at h1
      calc F τ = ENNReal.ofReal (w (P τ)) := rfl
        _ ≤ ENNReal.ofReal (w (P σ) + ε') := ENNReal.ofReal_le_ofReal (by linarith [h1.2])
        _ ≤ ENNReal.ofReal (w (P σ)) + ENNReal.ofReal ε' := ENNReal.ofReal_add_le
    have hlen : ∀ k < N, curveLength P (p.t k) (p.t (k + 1)) = ENNReal.ofReal ((b - a) / N) := by
      intro k hk
      rw [hu _ _ (p.mem_Icc hk.le).1 (p.le_t (Nat.le_succ k) (Nat.succ_le_of_lt hk))
        (p.mem_Icc (Nat.succ_le_of_lt hk)).2, hstep k]
    have hp0 : p.t 0 = a := p.zero
    have hpN : p.t N = b := p.last
    calc ∫⁻ τ in Icc a b, F τ = ∫⁻ τ in Ioc a b, F τ := (setLIntegral_congr Ioc_ae_eq_Icc).symm
      _ = ∑ k ∈ Finset.range N, ∫⁻ τ in Ioc (p.t k) (p.t (k + 1)), F τ := by
          rw [sum_setLIntegral_Ioc F hmono N, hp0, hpN]
      _ ≤ ∑ k ∈ Finset.range N, (infAlong w P (p.t k) (p.t (k + 1)) + ENNReal.ofReal ε') *
            ENNReal.ofReal ((b - a) / N) := by
          refine Finset.sum_le_sum fun k hk => ?_
          have hk' := Finset.mem_range.1 hk
          rw [← hstep k, ← Real.volume_Ioc, ← setLIntegral_const]
          exact setLIntegral_mono' measurableSet_Ioc fun τ hτ => hpiece k hk' τ ⟨hτ.1.le, hτ.2⟩
      _ = p.sum (fun u v => infAlong w P u v * curveLength P u v) +
            (N : ℝ≥0∞) * (ENNReal.ofReal ε' * ENNReal.ofReal ((b - a) / N)) := by
          simp only [add_mul, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
            nsmul_eq_mul]
          congr 1
          refine Finset.sum_congr rfl fun k hk => ?_
          show _ = infAlong w P (p.t k) (p.t (k + 1)) * curveLength P (p.t k) (p.t (k + 1))
          rw [hlen k (Finset.mem_range.1 hk)]
      _ ≤ weightedLength w P a b + ε := by
          refine add_le_add (le_partitionSup p) ?_
          rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul hε'pos.le,
            ← ENNReal.ofReal_mul (Nat.cast_nonneg N), ← ENNReal.ofReal_coe_nnreal]
          refine ENNReal.ofReal_le_ofReal ?_
          have hN0 : (0 : ℝ) < N := Nat.cast_pos.2 hN
          have hba : 0 ≤ b - a := sub_nonneg.2 hab
          rw [show (N : ℝ) * (ε' * ((b - a) / N)) = ε' * (b - a) by field_simp, hε',
            div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
          nlinarith [ε.coe_nonneg]

end UnitSpeed

end HigherDimLQGMetric
