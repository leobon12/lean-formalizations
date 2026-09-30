import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.EMetricSpace.Diam
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Dyadic tents and boxes in a half-plane chart (EXT-JS node A3)

Blueprint `blueprint/EXT_JS_BLUEPRINT.md`, §2 (notation) and §3 node A3.

For `R > 0`, `m ∈ ℕ`, `j < 2^m`: `ℓ_m = 2R/2^m`, `I_{m,j} = [-R + jℓ_m, -R + (j+1)ℓ_m]`, the
closed tent `T_{m,j} = I_{m,j} ×ℂ [0, ℓ_m]`, the top box `Q_{m,j} = I_{m,j} ×ℂ [ℓ_m/2, ℓ_m]` and the
enlarged box `Q*_{m,j} = (I_{m,j} ± ℓ_m/4) ×ℂ (ℓ_m/4, 5ℓ_m/4)`.

These dyadic Carleson boxes of the half-plane replace the Whitney cubes and their "shadows" of
Jones–Smirnov, *Removability theorems for Sobolev functions and quasiconformal maps*, Ark. Mat. 38
(2000) 263–279, §1 (Whitney decomposition and shadows, p. 265) and the chain argument in the proof
of Proposition 1 (pp. 271–272): the tent `T_{m,j}` is the chart preimage of a shadow, and the top
boxes are the chart preimages of Whitney cubes.

Main facts:
* children decomposition `dyI_succ`; ancestors `dyI_subset_of_div`, `tent_subset_of_div`;
  descendants `exists_dyI_desc`, `exists_mem_tent_desc`;
* vertical chains: every point of a tent with positive height lies in the top box of a descendant
  (`exists_mem_topBox_desc`);
* covering of `[-R, R]` at each level (`exists_dyI_of_mem_Icc`, `ofReal_image_Icc_subset_iUnion_tent`);
* bounded overlap: at most `2` enlarged boxes per level (`sum_indicator_bigBox_level_le_two`), at
  most `6` in total (`sum_indicator_bigBox_le_six`);
* location: `ball_subset_bigBox`, `bigBox_subset_layer`, `bigBox_subset_upper`.
-/

open Set Complex Filter Topology
open scoped ENNReal

namespace QuantumZipper.JS

noncomputable section

/-- Side length `ℓ_m = 2R/2^m` of the level-`m` dyadic intervals of `[-R, R]`. -/
def dyLen (R : ℝ) (m : ℕ) : ℝ := 2 * R / 2 ^ m

/-- The dyadic interval `I_{m,j} = [-R + jℓ_m, -R + (j+1)ℓ_m]`. -/
def dyI (R : ℝ) (m j : ℕ) : Set ℝ := Icc (-R + j * dyLen R m) (-R + (j + 1) * dyLen R m)

/-- The closed tent `T_{m,j} = I_{m,j} ×ℂ [0, ℓ_m]`. -/
def tent (R : ℝ) (m j : ℕ) : Set ℂ := dyI R m j ×ℂ Icc 0 (dyLen R m)

/-- The top box `Q_{m,j} = I_{m,j} ×ℂ [ℓ_m/2, ℓ_m]`. -/
def topBox (R : ℝ) (m j : ℕ) : Set ℂ := dyI R m j ×ℂ Icc (dyLen R m / 2) (dyLen R m)

/-- The open enlarged box `Q*_{m,j} = (I_{m,j} ± ℓ_m/4) ×ℂ (ℓ_m/4, 5ℓ_m/4)`. -/
def bigBox (R : ℝ) (m j : ℕ) : Set ℂ :=
  Ioo (-R + j * dyLen R m - dyLen R m / 4) (-R + (j + 1) * dyLen R m + dyLen R m / 4) ×ℂ
    Ioo (dyLen R m / 4) (5 * dyLen R m / 4)

/-- The shadow sum `Σ_{m,j} diam F(T_{m,j})²` (condition SH of the blueprint). -/
def shadowSum (R : ℝ) (F : ℂ → ℂ) : ℝ≥0∞ :=
  ∑' m : ℕ, ∑ j ∈ Finset.range (2 ^ m), Metric.ediam (F '' tent R m j) ^ 2

variable {R : ℝ}

/-! ### Side lengths -/

lemma dyLen_pos (hR : 0 < R) (m : ℕ) : 0 < dyLen R m := by unfold dyLen; positivity

lemma dyLen_nonneg (hR : 0 ≤ R) (m : ℕ) : 0 ≤ dyLen R m := by unfold dyLen; positivity

lemma dyLen_zero (R : ℝ) : dyLen R 0 = 2 * R := by simp [dyLen]

lemma dyLen_add (R : ℝ) (m n : ℕ) : dyLen R (m + n) = dyLen R m / 2 ^ n := by
  unfold dyLen; rw [pow_add, div_div]

lemma dyLen_succ (R : ℝ) (m : ℕ) : dyLen R (m + 1) = dyLen R m / 2 := by
  simpa using dyLen_add R m 1

lemma dyLen_le_of_le (hR : 0 ≤ R) {m k : ℕ} (h : m ≤ k) : dyLen R k ≤ dyLen R m := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [dyLen_add]
  exact div_le_self (dyLen_nonneg hR m) (one_le_pow₀ (by norm_num))

lemma dyLen_le (hR : 0 ≤ R) (m : ℕ) : dyLen R m ≤ 2 * R := by
  simpa [dyLen_zero] using dyLen_le_of_le hR (Nat.zero_le m)

lemma pow_mul_dyLen (R : ℝ) (m : ℕ) : (2 : ℝ) ^ m * dyLen R m = 2 * R := by
  unfold dyLen; field_simp

lemma tendsto_dyLen (R : ℝ) : Tendsto (dyLen R) atTop (𝓝 0) := by
  have h : dyLen R = fun m => 2 * R * (1 / 2 : ℝ) ^ m := by
    funext m; unfold dyLen; rw [one_div_pow]; ring
  rw [h]
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num)).const_mul (2 * R)

/-! ### Dyadic intervals: children, ancestors, descendants -/

/-- Children decomposition. -/
lemma dyI_succ (hR : 0 ≤ R) (m j : ℕ) :
    dyI R m j = dyI R (m + 1) (2 * j) ∪ dyI R (m + 1) (2 * j + 1) := by
  have hℓ := dyLen_nonneg hR m
  simp only [dyI, dyLen_succ]
  push_cast
  rw [Icc_union_Icc_eq_Icc (by nlinarith) (by nlinarith)]
  congr 1 <;> ring

lemma dyI_child_subset (hR : 0 ≤ R) (m j' : ℕ) : dyI R (m + 1) j' ⊆ dyI R m (j' / 2) := by
  rw [dyI_succ hR m (j' / 2)]
  rcases Nat.even_or_odd' j' with ⟨k, rfl | rfl⟩
  · have : 2 * k / 2 = k := by omega
    rw [this]; exact subset_union_left
  · have : (2 * k + 1) / 2 = k := by omega
    rw [this]; exact subset_union_right

/-- Ancestors: `I_{m+n, j'} ⊆ I_{m, j'/2^n}`. -/
lemma dyI_subset_of_div (hR : 0 ≤ R) {m n j j' : ℕ} (h : j' / 2 ^ n = j) :
    dyI R (m + n) j' ⊆ dyI R m j := by
  induction n generalizing j' with
  | zero => simp at h; subst h; simp
  | succ n ih =>
    have h' : j' / 2 / 2 ^ n = j := by
      rw [Nat.div_div_eq_div_mul, ← pow_succ']; exact h
    exact (dyI_child_subset hR (m + n) j').trans (ih h')

/-- The index bound for descendants. -/
lemma lt_two_pow_of_div {m n j j' : ℕ} (h : j' / 2 ^ n = j) (hj : j < 2 ^ m) :
    j' < 2 ^ (m + n) := by
  rw [← h, Nat.div_lt_iff_lt_mul (by positivity), ← pow_add] at hj
  exact hj

/-- Descendants: a point of `I_{m,j}` lies in some level-`(m+n)` descendant. -/
lemma exists_dyI_desc (hR : 0 ≤ R) {m j : ℕ} {x : ℝ} (hx : x ∈ dyI R m j) (n : ℕ) :
    ∃ j', j' / 2 ^ n = j ∧ x ∈ dyI R (m + n) j' := by
  induction n with
  | zero => exact ⟨j, by simp, hx⟩
  | succ n ih =>
    obtain ⟨j', hj', hx'⟩ := ih
    rw [dyI_succ hR] at hx'
    rcases hx' with hx' | hx'
    · refine ⟨2 * j', ?_, hx'⟩
      rw [pow_succ', ← Nat.div_div_eq_div_mul, show 2 * j' / 2 = j' by omega, hj']
    · refine ⟨2 * j' + 1, ?_, hx'⟩
      rw [pow_succ', ← Nat.div_div_eq_div_mul, show (2 * j' + 1) / 2 = j' by omega, hj']

lemma dyI_zero_zero (R : ℝ) : dyI R 0 0 = Icc (-R) R := by
  simp only [dyI, dyLen_zero]; push_cast; congr 1 <;> ring

/-- Covering of `[-R, R]` at every level. -/
lemma exists_dyI_of_mem_Icc (hR : 0 ≤ R) {x : ℝ} (hx : x ∈ Icc (-R) R) (m : ℕ) :
    ∃ j < 2 ^ m, x ∈ dyI R m j := by
  rw [← dyI_zero_zero] at hx
  obtain ⟨j', hj', hx'⟩ := exists_dyI_desc hR hx m
  exact ⟨j', by simpa using lt_two_pow_of_div hj' (by norm_num : 0 < 2 ^ 0), by simpa using hx'⟩

lemma dyI_subset_Icc (hR : 0 ≤ R) {m j : ℕ} (hj : j < 2 ^ m) : dyI R m j ⊆ Icc (-R) R := by
  have h0 := dyI_subset_of_div (R := R) (m := 0) (n := m) (j' := j) hR
    (Nat.div_eq_of_lt hj)
  rw [dyI_zero_zero, zero_add] at h0
  exact h0

/-! ### Tents and boxes -/

/-- Descendants for tents: a point of `T_{m,j}` of height `≤ ℓ_{m+n}` lies in a level-`(m+n)`
descendant tent. -/
lemma exists_mem_tent_desc (hR : 0 ≤ R) {m j : ℕ} {w : ℂ} (hw : w ∈ tent R m j) {n : ℕ}
    (hn : w.im ≤ dyLen R (m + n)) : ∃ j', j' / 2 ^ n = j ∧ w ∈ tent R (m + n) j' := by
  rw [tent, mem_reProdIm] at hw
  obtain ⟨j', hj', hx⟩ := exists_dyI_desc hR hw.1 n
  exact ⟨j', hj', mem_reProdIm.2 ⟨hx, hw.2.1, hn⟩⟩

/-- Vertical chains: a point of `T_{m,j}` with positive height lies in the top box of a
descendant. -/
lemma exists_mem_topBox_desc (hR : 0 < R) {m j : ℕ} {w : ℂ} (hw : w ∈ tent R m j)
    (him : 0 < w.im) : ∃ n j', j' / 2 ^ n = j ∧ w ∈ topBox R (m + n) j' := by
  have hex : ∃ n, dyLen R (m + n) < w.im := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (dyLen R m / w.im) (by norm_num : (1 : ℝ) < 2)
    refine ⟨n, ?_⟩
    rw [dyLen_add, div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ him] at hn
    linarith
  classical
  set n₀ := Nat.find hex
  have hw' := hw
  rw [tent, mem_reProdIm] at hw'
  have hn₀ : n₀ ≠ 0 := by
    intro h0
    have := Nat.find_spec hex
    rw [show Nat.find hex = 0 from h0, add_zero] at this
    linarith [hw'.2.2]
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hn₀
  have hle : w.im ≤ dyLen R (m + n) := by
    have := Nat.find_min hex (show n < n₀ by omega)
    exact not_lt.1 this
  have hlt : dyLen R (m + (n + 1)) < w.im := by
    have := Nat.find_spec hex
    rwa [show Nat.find hex = n + 1 from hn] at this
  rw [← add_assoc, dyLen_succ] at hlt
  obtain ⟨j', hj', hx⟩ := exists_mem_tent_desc hR.le hw hle
  rw [tent, mem_reProdIm] at hx
  exact ⟨n, j', hj', mem_reProdIm.2 ⟨hx.1, hlt.le, hle⟩⟩

lemma ofReal_mem_tent (hR : 0 ≤ R) {m j : ℕ} {x : ℝ} (hx : x ∈ dyI R m j) :
    (x : ℂ) ∈ tent R m j :=
  mem_reProdIm.2 ⟨by simpa using hx, by simpa using dyLen_nonneg hR m⟩

lemma tent_subset (hR : 0 ≤ R) {m j : ℕ} (hj : j < 2 ^ m) :
    tent R m j ⊆ Icc (-R) R ×ℂ Icc 0 (2 * R) := by
  intro w hw
  rw [tent, mem_reProdIm] at hw
  exact mem_reProdIm.2 ⟨dyI_subset_Icc hR hj hw.1, hw.2.1, hw.2.2.trans (dyLen_le hR m)⟩

lemma bigBox_subset_upper (hR : 0 ≤ R) (m j : ℕ) : bigBox R m j ⊆ {w : ℂ | 0 < w.im} := by
  intro w hw
  rw [bigBox, mem_reProdIm] at hw
  have := dyLen_nonneg hR m
  show 0 < w.im
  linarith [hw.2.1]

lemma isOpen_bigBox (R : ℝ) (m j : ℕ) : IsOpen (bigBox R m j) :=
  isOpen_Ioo.reProdIm isOpen_Ioo

lemma isCompact_tent (R : ℝ) (m j : ℕ) : IsCompact (tent R m j) :=
  isCompact_Icc.reProdIm isCompact_Icc

/-! ### Bounded overlap -/

/-- A finite set of naturals whose elements are pairwise within distance `k` has at most `k+1`
elements. -/
lemma card_le_of_gap (S : Finset ℕ) (k : ℕ) (h : ∀ i ∈ S, ∀ j ∈ S, i ≤ j → j ≤ i + k) :
    S.card ≤ k + 1 := by
  rcases S.eq_empty_or_nonempty with hS | hS
  · simp [hS]
  · have hsub : S ⊆ Finset.Icc (S.min' hS) (S.min' hS + k) := by
      intro j hj
      exact Finset.mem_Icc.2 ⟨S.min'_le j hj, h _ (S.min'_mem hS) j hj (S.min'_le j hj)⟩
    refine (Finset.card_le_card hsub).trans ?_
    rw [Nat.card_Icc]; omega

open Classical in
lemma sum_indicator_eq_card {ι : Type*} (s : Finset ι) (A : ι → Set ℂ) (w : ℂ) :
    ∑ j ∈ s, (A j).indicator (1 : ℂ → ℝ≥0∞) w = ((s.filter fun j => w ∈ A j).card : ℝ≥0∞) := by
  classical
  simp only [Set.indicator_apply, Pi.one_apply]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_one]

/-- At each level a point lies in at most two enlarged boxes. -/
lemma sum_indicator_bigBox_level_le_two (hR : 0 < R) (m : ℕ) (s : Finset ℕ) (w : ℂ) :
    ∑ j ∈ s, (bigBox R m j).indicator (1 : ℂ → ℝ≥0∞) w ≤ 2 := by
  classical
  rw [sum_indicator_eq_card]
  have hℓ := dyLen_pos hR m
  have : (s.filter fun j => w ∈ bigBox R m j).card ≤ 1 + 1 := by
    refine card_le_of_gap _ 1 fun i hi j hj _ => ?_
    have hi' := (Finset.mem_filter.1 hi).2
    have hj' := (Finset.mem_filter.1 hj).2
    rw [bigBox, mem_reProdIm] at hi' hj'
    have hlt : (j : ℝ) * dyLen R m < ((i : ℝ) + 3 / 2) * dyLen R m := by
      nlinarith [hi'.1.2, hj'.1.1]
    have hlt' : (j : ℝ) < (i : ℝ) + 2 := by nlinarith
    exact_mod_cast Nat.lt_succ_iff.1 (by exact_mod_cast hlt' : j < i + 2)
  exact_mod_cast this

/-- If a level-`m` enlarged box contains `w`, then `ℓ_m/4 < w.im < 5ℓ_m/4`. -/
lemma im_mem_of_mem_bigBox {m j : ℕ} {w : ℂ} (hw : w ∈ bigBox R m j) :
    dyLen R m / 4 < w.im ∧ w.im < 5 * dyLen R m / 4 :=
  (mem_reProdIm.1 hw).2

/-- **Bounded overlap.** Every point lies in at most `6` enlarged boxes. -/
theorem sum_indicator_bigBox_le_six (hR : 0 < R) (w : ℂ) :
    ∑' m : ℕ, ∑ j ∈ Finset.range (2 ^ m), (bigBox R m j).indicator (1 : ℂ → ℝ≥0∞) w ≤ 6 := by
  classical
  set f : ℕ → ℝ≥0∞ := fun m =>
    ∑ j ∈ Finset.range (2 ^ m), (bigBox R m j).indicator (1 : ℂ → ℝ≥0∞) w with hf
  -- levels where `w` meets an enlarged box
  have hsupp : ∀ m, f m ≠ 0 → ∃ j, w ∈ bigBox R m j := by
    intro m hm
    by_contra hcon
    push Not at hcon
    exact hm (Finset.sum_eq_zero fun j _ => Set.indicator_of_notMem (hcon j) _)
  by_cases hex : ∃ m, f m ≠ 0
  · set m₀ := Nat.find hex
    have hgap : ∀ m, f m ≠ 0 → m₀ ≤ m ∧ m ≤ m₀ + 2 := by
      intro m hm
      refine ⟨Nat.find_min' hex hm, ?_⟩
      obtain ⟨j₀, hj₀⟩ := hsupp m₀ (Nat.find_spec hex)
      obtain ⟨j, hj⟩ := hsupp m hm
      have h0 := im_mem_of_mem_bigBox hj₀
      have h1 := im_mem_of_mem_bigBox hj
      by_contra hlt
      push Not at hlt
      obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (Nat.find_min' hex hm)
      have hd3 : 3 ≤ d := by omega
      rw [hd, dyLen_add] at h1
      have hℓ := dyLen_pos hR m₀
      have hp : (8 : ℝ) ≤ 2 ^ d := by
        calc (8 : ℝ) = 2 ^ 3 := by norm_num
          _ ≤ 2 ^ d := pow_le_pow_right₀ (by norm_num) hd3
      have : dyLen R m₀ / 2 ^ d ≤ dyLen R m₀ / 8 := div_le_div_of_nonneg_left hℓ.le
        (by norm_num) hp
      linarith [h0.1, h1.2]
    rw [tsum_eq_sum (s := Finset.Icc m₀ (m₀ + 2))]
    · calc ∑ m ∈ Finset.Icc m₀ (m₀ + 2), f m ≤ (Finset.Icc m₀ (m₀ + 2)).card • (2 : ℝ≥0∞) :=
            Finset.sum_le_card_nsmul _ _ _ fun m _ =>
              sum_indicator_bigBox_level_le_two hR m _ w
        _ = 6 := by
            rw [Nat.card_Icc, show m₀ + 2 + 1 - m₀ = 3 by omega, nsmul_eq_mul]; norm_num
    · intro m hm
      by_contra hne
      exact hm (Finset.mem_Icc.2 (hgap m hne))
  · push Not at hex
    rw [show f = fun _ => 0 from funext hex, tsum_zero]
    exact zero_le

end

end QuantumZipper.JS
