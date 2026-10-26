import SupercriticalLFPPAS.Core.Interfaces
import SupercriticalLFPPAS.Contraction.GoodDisk
import SupercriticalLFPPAS.Contraction.AltChain
import SupercriticalLFPPAS.Contraction.Sorting
import SupercriticalLFPPAS.Contraction.FiniteSubcover
import SupercriticalLFPPAS.Contraction.CoveringArithmetic
import SupercriticalLFPPAS.Contraction.FinalCost

/-!
# Lemma 4.1′ (SB2 D6): the deterministic covering and joining argument, interface form

`lemma41_holds : Core.Lemma41Stmt` (paper Lemma 4.1, l. 402–470; SB2 §2.4 and Details D5–D6; SB3 §5(b)).

* **Close endpoints** (D6 step 1): if `|z − w| ≤ 1024 r_max`, the midpoint of `z, w` lies in both output balls and in
  `W` (convexity), so the internal set distance is `0`.
* **Far endpoints.** `l41_cert_exists` performs D6 steps 2–6: the segment `J = [a₀, b₀]`, a good disk and the
  excursion data (`l41_goodDisk_exc`) at every `τ ∈ J`, a finite subcover of `J` by the open excursion intervals,
  the greedy selection with `|J| ≤ 3S`, `S ≤ ℓ ≤ 4S`, `G ≥ S/A ≥ λℓ` (`d4_greedy_cover_good_fraction`), and the
  increasing enumeration of the selected intervals (`l41_sort_intervals`). The output is a certificate `L41Cert`.
* `l41_far_of_cert` performs D6 steps 7–9: for each slack `ϑ > 0` it chooses prior-comparison curves on the
  complementary segments and good-scale curves on the crossings (`l41_curve_of_internalSetDist`), joins them through
  the target separators by chain lemma J (`l41_join`), sums the costs to
  `C₀(ℓ − G) + (1 + d₀/10)KG + (d₀/5)KS + (2k+1)ϑ ≤ F(C₀, K)L + (2k+1)ϑ` (SB3 §5(b) split, `d4_final_cost_bound`)
  and lets `ϑ ↓ 0`.
-/

set_option autoImplicit false
noncomputable section

open Set Metric
open scoped ENNReal

namespace SupercriticalLFPPAS.Contraction

open SupercriticalLQGUniqueness
open LQGMetric.MetricGeometry (IsGeodesicCurve)

/-- A finite internal set distance bound yields an actual target curve in `W` with endpoints in the two sets and
length within any positive slack of the bound; it is Euclidean continuous because `W` is bounded. -/
theorem l41_curve_of_internalSetDist {d' : LSCMetric} {W : Set ℂ} (hWb : Bornology.IsBounded W)
    {E F : Set ℂ} {B ϑ : ℝ} (hB : 0 ≤ B) (hϑ : 0 < ϑ)
    (h : d'.internalSetDist W {y | (y : ℂ) ∈ E} {y | (y : ℂ) ∈ F} ≤ ENNReal.ofReal B) :
    ∃ (γ : ℝ → ℂ) (a b : ℝ), d'.IsCurve γ a b ∧ ContinuousOn γ (Icc a b) ∧
      (∀ u ∈ Icc a b, γ u ∈ W) ∧ γ a ∈ E ∧ γ b ∈ F ∧
      d'.len γ a b ≤ ENNReal.ofReal (B + ϑ) := by
  have hlt : d'.internalSetDist W {y | (y : ℂ) ∈ E} {y | (y : ℂ) ∈ F} <
      ENNReal.ofReal (B + ϑ) :=
    h.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by linarith))
  unfold LSCMetric.internalSetDist at hlt
  obtain ⟨x, hx⟩ := iInf_lt_iff.mp hlt
  obtain ⟨hxE, hx⟩ := iInf_lt_iff.mp hx
  obtain ⟨y, hy⟩ := iInf_lt_iff.mp hx
  obtain ⟨hyF, hy⟩ := iInf_lt_iff.mp hy
  unfold LSCMetric.internal at hy
  obtain ⟨γ, hγ⟩ := iInf_lt_iff.mp hy
  obtain ⟨a, ha⟩ := iInf_lt_iff.mp hγ
  obtain ⟨b, hb⟩ := iInf_lt_iff.mp ha
  obtain ⟨hcurve, hc⟩ := iInf_lt_iff.mp hb
  obtain ⟨hW, hw⟩ := iInf_lt_iff.mp hc
  obtain ⟨hγa, hγa'⟩ := iInf_lt_iff.mp hw
  obtain ⟨hγb, hlen⟩ := iInf_lt_iff.mp hγa'
  refine ⟨γ, a, b, hcurve, ?_, hW, ?_, ?_, hlen.le⟩
  · exact Uniqueness.Toolkit.PlanarSeparation.LSCMetric.continuousOn_euclidean_of_bounded d' γ hcurve
      (hWb.subset (by rintro _ ⟨u, hu, rfl⟩; exact hW u hu))
  · rw [hγa]
    exact hxE
  · rw [hγb]
    exact hyF

/-- Left end of the `i`-th complementary segment: `H₀` starts at `left`, `H_{i+1}` at `t_i`. -/
def l41HL (left : ℝ) (t : ℕ → ℝ) (i : ℕ) : ℝ := if i = 0 then left else t (i - 1)

/-- Right end of the `i`-th complementary segment: `H_i` ends at `s_i` for `i < k`, `H_k` at `right`. -/
def l41HR (k : ℕ) (right : ℝ) (s : ℕ → ℝ) (i : ℕ) : ℝ := if i < k then s i else right

/-- The complementary segments and the crossings tile `[left, right]`:
`∑_{i ≤ k} |H_i| = (right − left) − ∑_{i < k} |G_i|`. -/
theorem l41_H_telescope (k : ℕ) (left right : ℝ) (s t : ℕ → ℝ) :
    ∑ i ∈ Finset.range (k + 1), (l41HR k right s i - l41HL left t i) =
      (right - left) - ∑ i ∈ Finset.range k, (t i - s i) := by
  have h1 : ∀ i ∈ Finset.range k, l41HR k right s i - l41HL left t i =
      (l41HL left t (i + 1) - l41HL left t i) - (t i - s i) := by
    intro i hi
    have hik := Finset.mem_range.mp hi
    simp only [l41HR, l41HL, hik, ↓reduceIte, Nat.add_one_ne_zero, Nat.add_sub_cancel]
    ring
  rw [Finset.sum_range_succ, Finset.sum_congr rfl h1, Finset.sum_sub_distrib,
    Finset.sum_range_sub (fun i => l41HL left t i)]
  simp only [l41HR, lt_irrefl, ↓reduceIte]
  have h0 : l41HL left t 0 = left := by simp [l41HL]
  rw [h0]
  ring

/-- **The selection certificate** (output of SB2 D6 steps 2–6): `k` selected excursions `[α_i, β_i]` in increasing
order inside the hull `[left, right] ⊆ [0, L]`, each with its good disk data (`L41Exc`), the hull endpoints within
`76 r_max` of `z = P 0` and `w = P L`, `∑ |I_i| ≤ ℓ` and `λℓ ≤ ∑ |G_i|` with `λ = 1/(5A)`. -/
structure L41Cert (d' : LSCMetric) (W : Set ℂ) (P : ℝ → ℂ) (L η d₀ A Kf rmin rmax : ℝ) where
  k : ℕ
  left : ℝ
  right : ℝ
  c : ℕ → ℂ
  r : ℕ → ℝ
  α : ℕ → ℝ
  β : ℕ → ℝ
  s : ℕ → ℝ
  t : ℕ → ℝ
  left_nonneg : 0 ≤ left
  right_le : right ≤ L
  left_le_right : left ≤ right
  exc : ∀ i < k, rmin ≤ r i ∧ r i ≤ rmax ∧
    L41Exc d' W P L η d₀ A Kf (c i) (r i) (α i) (β i) (s i) (t i)
  first : 0 < k → left ≤ α 0
  step : ∀ i, i + 1 < k → β i ≤ α (i + 1)
  last : 0 < k → β (k - 1) ≤ right
  left_near : dist (P left) (P 0) ≤ 76 * rmax
  right_near : dist (P right) (P L) ≤ 76 * rmax
  S_le : ∑ i ∈ Finset.range k, (β i - α i) ≤ right - left
  G_ge : 1 / (5 * A) * (right - left) ≤ ∑ i ∈ Finset.range k, (t i - s i)

/-- The complementary segments `H_i = [l41HL i, l41HR i]`, `i ≤ k`, are (ordered) subsegments of `[0, L]`. -/
theorem L41Cert.H_bounds {d' : LSCMetric} {W : Set ℂ} {P : ℝ → ℂ} {L η d₀ A Kf rmin rmax : ℝ}
    (Q : L41Cert d' W P L η d₀ A Kf rmin rmax) (i : ℕ) (hi : i ≤ Q.k) :
    0 ≤ l41HL Q.left Q.t i ∧ l41HL Q.left Q.t i ≤ l41HR Q.k Q.right Q.s i ∧
      l41HR Q.k Q.right Q.s i ≤ L := by
  have hexc : ∀ j < Q.k, 0 < Q.α j ∧ Q.α j < Q.s j ∧ Q.s j < Q.t j ∧ Q.t j < Q.β j ∧ Q.β j < L :=
    fun j hj => by
      obtain ⟨_, _, hx⟩ := Q.exc j hj
      exact ⟨hx.α_pos, hx.α_lt_s, hx.s_lt_t, hx.t_lt_β, hx.β_lt⟩
  have hR : l41HR Q.k Q.right Q.s i ≤ L := by
    unfold l41HR
    split_ifs with h
    · obtain ⟨_, _, _, _, _⟩ := hexc i h
      linarith
    · exact Q.right_le
  refine ⟨?_, ?_, hR⟩
  · unfold l41HL
    split_ifs with h
    · exact Q.left_nonneg
    · obtain ⟨_, _, _, _, _⟩ := hexc (i - 1) (by omega)
      linarith
  · rcases Nat.eq_zero_or_pos i with h0 | hpos
    · subst h0
      unfold l41HL l41HR
      simp only [↓reduceIte]
      split_ifs with hk
      · obtain ⟨_, _, _, _, _⟩ := hexc 0 hk
        linarith [Q.first hk]
      · exact Q.left_le_right
    · have hne : i ≠ 0 := by omega
      unfold l41HL l41HR
      simp only [hne, ↓reduceIte]
      obtain ⟨_, _, _, h3, _⟩ := hexc (i - 1) (by omega)
      split_ifs with hk
      · have hstep := Q.step (i - 1) (by omega)
        rw [Nat.sub_add_cancel (by omega)] at hstep
        obtain ⟨_, h5, _, _, _⟩ := hexc i hk
        linarith
      · have hik : i = Q.k := by omega
        have hlast := Q.last (by omega)
        rw [← hik] at hlast
        linarith

/-- **Lemma 4.1′, far case** (SB2 D6 steps 7–9): a selection certificate gives the contraction bound. -/
theorem l41_far_of_cert {d' : LSCMetric} {W : Set ℂ} (hWb : Bornology.IsBounded W) {P : ℝ → ℂ}
    {L η d₀ A Kf C₀ rmin rmax ρold : ℝ} (hη : 0 < η) (hd₀ : 0 ≤ d₀) (hA : 1 ≤ A) (hKf : 0 ≤ Kf)
    (hC₀ : 0 ≤ C₀) (hρ : 0 < ρold) (hρold : ρold < η * rmin / 4)
    (hρr : ρold < rmax)
    (hprior : ∀ s t, 0 ≤ s → s ≤ t → t ≤ L →
      d'.internalSetDist W {y | (y : ℂ) ∈ ball (P s) ρold} {y | (y : ℂ) ∈ ball (P t) ρold} ≤
        ENNReal.ofReal (C₀ * (t - s)))
    (Q : L41Cert d' W P L η d₀ A Kf rmin rmax) :
    d'.internalSetDist W {y | (y : ℂ) ∈ ball (P 0) (513 * rmax)}
        {y | (y : ℂ) ∈ ball (P L) (513 * rmax)} ≤
      ENNReal.ofReal (SupercriticalLFPPAS.Iteration.contractionFactor C₀ Kf (1 / (5 * A)) d₀ * L) := by
  classical
  have hA0 : 0 < A := by linarith
  have hrmax : 0 < rmax := hρ.trans hρr
  set lam : ℝ := 1 / (5 * A) with hlam
  set F : ℝ := SupercriticalLFPPAS.Iteration.contractionFactor C₀ Kf lam d₀ with hF
  set ℓ : ℝ := Q.right - Q.left with hℓ
  set G : ℝ := ∑ i ∈ Finset.range Q.k, (Q.t i - Q.s i) with hG
  set Ssum : ℝ := ∑ i ∈ Finset.range Q.k, (Q.β i - Q.α i) with hS
  have hlam0 : 0 ≤ lam := by positivity
  have hlam1 : lam ≤ 1 := by
    rw [hlam, div_le_one (by positivity)]
    linarith
  have hℓ0 : 0 ≤ ℓ := sub_nonneg.mpr Q.left_le_right
  have hℓL : ℓ ≤ L := by linarith [Q.left_nonneg, Q.right_le]
  have hL0 : 0 ≤ L := hℓ0.trans hℓL
  have hGS : G ≤ Ssum := Finset.sum_le_sum fun i hi => by
    obtain ⟨_, _, hx⟩ := Q.exc i (Finset.mem_range.mp hi)
    linarith [hx.α_lt_s, hx.t_lt_β]
  have hG0 : 0 ≤ G := Finset.sum_nonneg fun i hi => by
    obtain ⟨_, _, hx⟩ := Q.exc i (Finset.mem_range.mp hi)
    linarith [hx.s_lt_t]
  have hS0 : 0 ≤ Ssum := hG0.trans hGS
  have hSℓ : Ssum ≤ ℓ := Q.S_le
  have hGℓ : G ≤ ℓ := hGS.trans hSℓ
  have hGfrac : lam * ℓ ≤ G := Q.G_ge
  have hFnn : 0 ≤ F := by
    have hmax : 0 ≤ max C₀ Kf := le_max_of_le_left hC₀
    have h1 : 0 ≤ (1 - lam) * max C₀ Kf := mul_nonneg (by linarith) hmax
    have h2 : 0 ≤ (lam + 3 * d₀) * Kf := mul_nonneg (by linarith) hKf
    show 0 ≤ (1 - lam) * max C₀ Kf + (lam + 3 * d₀) * Kf
    linarith
  -- the joining bound with an arbitrary slack `ϑ`
  have key : ∀ ϑ : ℝ, 0 < ϑ →
      d'.internalSetDist W {y | (y : ℂ) ∈ ball (P 0) (513 * rmax)}
          {y | (y : ℂ) ∈ ball (P L) (513 * rmax)} ≤
        ENNReal.ofReal (F * L + (2 * Q.k + 1) * ϑ) := by
    intro ϑ hϑ
    -- prior-comparison curves on the complementary segments
    have hHex : ∀ i ≤ Q.k, ∃ (γ : ℝ → ℂ) (a b : ℝ), d'.IsCurve γ a b ∧ ContinuousOn γ (Icc a b) ∧
        (∀ u ∈ Icc a b, γ u ∈ W) ∧ γ a ∈ ball (P (l41HL Q.left Q.t i)) ρold ∧
        γ b ∈ ball (P (l41HR Q.k Q.right Q.s i)) ρold ∧
        d'.len γ a b ≤
          ENNReal.ofReal (C₀ * (l41HR Q.k Q.right Q.s i - l41HL Q.left Q.t i) + ϑ) := by
      intro i hi
      obtain ⟨h0, hle, hL⟩ := Q.H_bounds i hi
      exact l41_curve_of_internalSetDist hWb (mul_nonneg hC₀ (sub_nonneg.mpr hle)) hϑ
        (hprior _ _ h0 hle hL)
    choose! γH aH bH hHc hHcont hHW hHa hHb hHlen using hHex
    -- good-scale curves on the crossings
    have hGex : ∀ i < Q.k, ∃ (γ : ℝ → ℂ) (a b : ℝ), d'.IsCurve γ a b ∧
        ContinuousOn γ (Icc a b) ∧ (∀ u ∈ Icc a b, γ u ∈ W) ∧
        γ a ∈ ball (P (Q.s i)) (η * Q.r i / 2) ∧ γ b ∈ ball (P (Q.t i)) (η * Q.r i / 2) ∧
        d'.len γ a b ≤ ENNReal.ofReal ((1 + d₀ / 10) * Kf * (Q.t i - Q.s i) + ϑ) := by
      intro i hi
      obtain ⟨_, _, hx⟩ := Q.exc i hi
      exact l41_curve_of_internalSetDist hWb
        (mul_nonneg (mul_nonneg (by positivity) hKf) (sub_nonneg.mpr hx.s_lt_t.le)) hϑ hx.cross
    choose! γG aG bG hGc hGcont hGW hGa hGb hGlen using hGex
    -- the target separators at `P s_i` and `P t_i`
    have hSex : ∀ i < Q.k, ∃ (σ : ℝ → ℂ) (a' b' : ℝ), d'.IsCurve σ a' b' ∧
        ContinuousOn σ (Icc a' b') ∧ σ '' Icc a' b' ⊆ ball (P (Q.s i)) (Q.r i / 10) ∧
        σ '' Icc a' b' ⊆ W ∧ P (Q.s i) ∉ σ '' Icc a' b' ∧
        ball (P (Q.s i)) (η * Q.r i) ⊆ connectedComponentIn (σ '' Icc a' b')ᶜ (P (Q.s i)) ∧
        Bornology.IsBounded (connectedComponentIn (σ '' Icc a' b')ᶜ (P (Q.s i))) ∧
        d'.len σ a' b' ≤ ENNReal.ofReal (d₀ / 10 * Kf * (Q.β i - Q.α i)) :=
      fun i hi => (Q.exc i hi).2.2.sep_s
    choose! σs aS bS hSc hScont hSball hSW _ hSsub hSbdd hSlen using hSex
    have hTex : ∀ i < Q.k, ∃ (σ : ℝ → ℂ) (a' b' : ℝ), d'.IsCurve σ a' b' ∧
        ContinuousOn σ (Icc a' b') ∧ σ '' Icc a' b' ⊆ ball (P (Q.t i)) (Q.r i / 10) ∧
        σ '' Icc a' b' ⊆ W ∧ P (Q.t i) ∉ σ '' Icc a' b' ∧
        ball (P (Q.t i)) (η * Q.r i) ⊆ connectedComponentIn (σ '' Icc a' b')ᶜ (P (Q.t i)) ∧
        Bornology.IsBounded (connectedComponentIn (σ '' Icc a' b')ᶜ (P (Q.t i))) ∧
        d'.len σ a' b' ≤ ENNReal.ofReal (d₀ / 10 * Kf * (Q.β i - Q.α i)) :=
      fun i hi => (Q.exc i hi).2.2.sep_t
    choose! σt aT bT hTc hTcont hTball hTW _ hTsub hTbdd hTlen using hTex
    -- radii facts
    have hrpos : ∀ i < Q.k, 0 < Q.r i := fun i hi => (Q.exc i hi).2.2.r_pos
    have hρη : ∀ i < Q.k, ρold < η * Q.r i := fun i hi => by
      have h1 : rmin ≤ Q.r i := (Q.exc i hi).1
      have h2 : η * rmin ≤ η * Q.r i := mul_le_mul_of_nonneg_left h1 hη.le
      nlinarith
    have hηr : ∀ i < Q.k, η * Q.r i / 2 ≤ η * Q.r i := fun i hi => by
      have := mul_pos hη (hrpos i hi)
      linarith
    have hnotB : ∀ i < Q.k, ∀ (p z : ℂ) (K : Set ℂ), K ⊆ ball p (Q.r i / 10) →
        ∀ x : ℂ, Bornology.IsBounded (connectedComponentIn Kᶜ x) →
          ¬ ball z (513 * rmax) ⊆ connectedComponentIn Kᶜ x := by
      intro i hi p z K hK x hbdd hsub
      have hr10 : 0 ≤ Q.r i / 10 := by have := hrpos i hi; positivity
      have hcomp := l41_component_subset_closedBall (hK.trans ball_subset_closedBall) hr10 hbdd
      have hrle : Q.r i ≤ rmax := (Q.exc i hi).2.1
      exact l41_ball_not_subset_closedBall hr10 (by linarith) (hsub.trans hcomp)
    -- the alternating chain
    let Qp : L41Pieces := ⟨Q.k, γH, aH, bH, γG, aG, bG, σs, aS, bS, fun i => P (Q.s i), σt, aT, bT,
      fun i => P (Q.t i)⟩
    have hvalid : Qp.Valid d' W (ball (P 0) (513 * rmax)) (ball (P L) (513 * rmax)) := by
      refine ⟨fun i hi => ⟨hHc i hi, hHcont i hi, hHW i hi⟩,
        fun i hi => ⟨hGc i hi, hGcont i hi, hGW i hi⟩, ?_, ?_, ?_, ?_⟩
      · intro i hi
        refine ⟨hSc i hi, hScont i hi, fun u hu => hSW i hi ⟨u, hu, rfl⟩,
          hnotB i hi _ _ _ (hSball i hi) _ (hSbdd i hi),
          hnotB i hi _ _ _ (hSball i hi) _ (hSbdd i hi), ?_, ?_⟩
        · have hb := hHb i hi.le
          have hi' : i < Q.k := hi
          have hhr : l41HR Q.k Q.right Q.s i = Q.s i := by simp [l41HR, hi']
          rw [hhr] at hb
          exact hSsub i hi (ball_subset_ball (hρη i hi).le hb)
        · exact hSsub i hi (ball_subset_ball (hηr i hi) (hGa i hi))
      · intro i hi
        refine ⟨hTc i hi, hTcont i hi, fun u hu => hTW i hi ⟨u, hu, rfl⟩,
          hnotB i hi _ _ _ (hTball i hi) _ (hTbdd i hi),
          hnotB i hi _ _ _ (hTball i hi) _ (hTbdd i hi), ?_, ?_⟩
        · exact hTsub i hi (ball_subset_ball (hηr i hi) (hGb i hi))
        · have ha := hHa (i + 1) (Nat.succ_le_of_lt hi)
          have hhl : l41HL Q.left Q.t (i + 1) = Q.t i := by
            simp [l41HL]
          rw [hhl] at ha
          exact hTsub i hi (ball_subset_ball (hρη i hi).le ha)
      · have ha := hHa 0 (Nat.zero_le _)
        have hhl : l41HL Q.left Q.t 0 = Q.left := by simp [l41HL]
        rw [hhl, mem_ball] at ha
        show dist (γH 0 (aH 0)) (P 0) < 513 * rmax
        have htri := dist_triangle (γH 0 (aH 0)) (P Q.left) (P 0)
        linarith [Q.left_near]
      · have hb := hHb Q.k le_rfl
        have hhr : l41HR Q.k Q.right Q.s Q.k = Q.right := by simp [l41HR]
        rw [hhr, mem_ball] at hb
        show dist (γH Q.k (bH Q.k)) (P L) < 513 * rmax
        have htri := dist_triangle (γH Q.k (bH Q.k)) (P Q.right) (P L)
        linarith [Q.right_near]
    have hjoin := l41_join d' W (convex_ball (P 0) (513 * rmax)).isPreconnected
      (convex_ball (P L) (513 * rmax)).isPreconnected Qp hvalid
    refine hjoin.trans ?_
    -- the four sums
    have hHnn : ∀ i ∈ Finset.range (Q.k + 1),
        0 ≤ C₀ * (l41HR Q.k Q.right Q.s i - l41HL Q.left Q.t i) + ϑ := fun i hi => by
      have hle := (Q.H_bounds i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))).2.1
      have := mul_nonneg hC₀ (sub_nonneg.mpr hle)
      linarith
    have hGnn : ∀ i ∈ Finset.range Q.k, 0 ≤ (1 + d₀ / 10) * Kf * (Q.t i - Q.s i) + ϑ :=
      fun i hi => by
        obtain ⟨_, _, hx⟩ := Q.exc i (Finset.mem_range.mp hi)
        have := mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ 1 + d₀ / 10) hKf)
          (sub_nonneg.mpr hx.s_lt_t.le)
        linarith
    have hSnn : ∀ i ∈ Finset.range Q.k, 0 ≤ d₀ / 10 * Kf * (Q.β i - Q.α i) := fun i hi => by
      obtain ⟨_, _, hx⟩ := Q.exc i (Finset.mem_range.mp hi)
      exact mul_nonneg (mul_nonneg (by positivity) hKf)
        (sub_nonneg.mpr (by linarith [hx.α_lt_s, hx.s_lt_t, hx.t_lt_β]))
    have hsumH : ∑ i ∈ Finset.range (Q.k + 1), d'.len (γH i) (aH i) (bH i) ≤
        ENNReal.ofReal (∑ i ∈ Finset.range (Q.k + 1),
          (C₀ * (l41HR Q.k Q.right Q.s i - l41HL Q.left Q.t i) + ϑ)) := by
      rw [ENNReal.ofReal_sum_of_nonneg hHnn]
      exact Finset.sum_le_sum fun i hi => hHlen i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
    have hsumG : ∑ i ∈ Finset.range Q.k, d'.len (γG i) (aG i) (bG i) ≤
        ENNReal.ofReal (∑ i ∈ Finset.range Q.k, ((1 + d₀ / 10) * Kf * (Q.t i - Q.s i) + ϑ)) := by
      rw [ENNReal.ofReal_sum_of_nonneg hGnn]
      exact Finset.sum_le_sum fun i hi => hGlen i (Finset.mem_range.mp hi)
    have hsumS : ∑ i ∈ Finset.range Q.k, d'.len (σs i) (aS i) (bS i) ≤
        ENNReal.ofReal (∑ i ∈ Finset.range Q.k, (d₀ / 10 * Kf * (Q.β i - Q.α i))) := by
      rw [ENNReal.ofReal_sum_of_nonneg hSnn]
      exact Finset.sum_le_sum fun i hi => hSlen i (Finset.mem_range.mp hi)
    have hsumT : ∑ i ∈ Finset.range Q.k, d'.len (σt i) (aT i) (bT i) ≤
        ENNReal.ofReal (∑ i ∈ Finset.range Q.k, (d₀ / 10 * Kf * (Q.β i - Q.α i))) := by
      rw [ENNReal.ofReal_sum_of_nonneg hSnn]
      exact Finset.sum_le_sum fun i hi => hTlen i (Finset.mem_range.mp hi)
    -- evaluation of the sums
    have hX : ∑ i ∈ Finset.range (Q.k + 1),
        (C₀ * (l41HR Q.k Q.right Q.s i - l41HL Q.left Q.t i) + ϑ) =
          C₀ * (ℓ - G) + (Q.k + 1) * ϑ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, l41_H_telescope, Finset.sum_const,
        Finset.card_range, nsmul_eq_mul]
      push_cast
      ring
    have hY : ∑ i ∈ Finset.range Q.k, ((1 + d₀ / 10) * Kf * (Q.t i - Q.s i) + ϑ) =
        (1 + d₀ / 10) * Kf * G + Q.k * ϑ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul]
    have hZ : ∑ i ∈ Finset.range Q.k, (d₀ / 10 * Kf * (Q.β i - Q.α i)) = d₀ / 10 * Kf * Ssum := by
      rw [← Finset.mul_sum]
    rw [hX] at hsumH
    rw [hY] at hsumG
    rw [hZ] at hsumS hsumT
    have hXnn : 0 ≤ C₀ * (ℓ - G) + (Q.k + 1) * ϑ := by
      have := mul_nonneg hC₀ (sub_nonneg.mpr hGℓ)
      have : 0 ≤ ((Q.k : ℝ) + 1) * ϑ := by positivity
      linarith
    have hYnn : 0 ≤ (1 + d₀ / 10) * Kf * G + Q.k * ϑ := by
      have := mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ 1 + d₀ / 10) hKf) hG0
      have : 0 ≤ (Q.k : ℝ) * ϑ := by positivity
      linarith
    have hZnn : 0 ≤ d₀ / 10 * Kf * Ssum := mul_nonneg (mul_nonneg (by positivity) hKf) hS0
    -- the cost algebra (SB3 §5(b))
    have hcost := d4_final_cost_bound (C := C₀) (K := Kf) (lam := lam) (d₀ := d₀) (ℓ := ℓ) (G := G)
      (L := L) hKf hlam0 hlam1 hd₀ hℓ0 hℓL hGℓ hGfrac
    have hFeq : d4CostFactor C₀ Kf lam d₀ = F := rfl
    rw [hFeq] at hcost
    have hextra1 : (1 + d₀ / 10) * Kf * G ≤ (1 + d₀) * Kf * G := by
      have : 0 ≤ d₀ * Kf * G := mul_nonneg (mul_nonneg hd₀ hKf) hG0
      nlinarith
    have hextra2 : 2 * (d₀ / 10 * Kf * Ssum) ≤ 2 * d₀ * Kf * ℓ := by
      have h1 : d₀ * Kf * Ssum ≤ d₀ * Kf * ℓ := mul_le_mul_of_nonneg_left hSℓ (mul_nonneg hd₀ hKf)
      have h2 : 0 ≤ d₀ * Kf * Ssum := mul_nonneg (mul_nonneg hd₀ hKf) hS0
      nlinarith
    calc (∑ i ∈ Finset.range (Qp.k + 1), d'.len (Qp.γH i) (Qp.aH i) (Qp.bH i) +
          ∑ i ∈ Finset.range Qp.k, d'.len (Qp.γG i) (Qp.aG i) (Qp.bG i)) +
        (∑ i ∈ Finset.range Qp.k, d'.len (Qp.σs i) (Qp.aS i) (Qp.bS i) +
          ∑ i ∈ Finset.range Qp.k, d'.len (Qp.σt i) (Qp.aT i) (Qp.bT i))
        ≤ (ENNReal.ofReal (C₀ * (ℓ - G) + (Q.k + 1) * ϑ) +
            ENNReal.ofReal ((1 + d₀ / 10) * Kf * G + Q.k * ϑ)) +
          (ENNReal.ofReal (d₀ / 10 * Kf * Ssum) + ENNReal.ofReal (d₀ / 10 * Kf * Ssum)) :=
          add_le_add (add_le_add hsumH hsumG) (add_le_add hsumS hsumT)
      _ = ENNReal.ofReal ((C₀ * (ℓ - G) + (Q.k + 1) * ϑ + ((1 + d₀ / 10) * Kf * G + Q.k * ϑ)) +
            (d₀ / 10 * Kf * Ssum + d₀ / 10 * Kf * Ssum)) := by
          rw [ENNReal.ofReal_add (add_nonneg hXnn hYnn) (add_nonneg hZnn hZnn),
            ENNReal.ofReal_add hXnn hYnn, ENNReal.ofReal_add hZnn hZnn]
      _ ≤ ENNReal.ofReal (F * L + (2 * Q.k + 1) * ϑ) := by
          apply ENNReal.ofReal_le_ofReal
          nlinarith
  -- remove the slack (SB2 D6 step 9)
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hk : (0 : ℝ) < 2 * Q.k + 1 := by positivity
  have hϑ : 0 < (ε : ℝ) / (2 * Q.k + 1) := div_pos hε hk
  calc _ ≤ ENNReal.ofReal (F * L + (2 * Q.k + 1) * ((ε : ℝ) / (2 * Q.k + 1))) := key _ hϑ
    _ = ENNReal.ofReal (F * L) + ε := by
      rw [mul_div_cancel₀ _ hk.ne', ENNReal.ofReal_add (mul_nonneg hFnn hL0) (NNReal.coe_nonneg ε),
        ENNReal.ofReal_coe_nnreal]

/-- **The selection** (SB2 D6 steps 2–6): in the far case `|z − w| > 1024 r_max`, the good disks along `P` produce a
selection certificate. -/
theorem l41_cert_exists {d d' : LSCMetric} {W : Set ℂ} {P : ℝ → ℂ} {L R η d₀ A Kf rmin rmax : ℝ}
    (hP : Core.IsGeodIn d P L R) (hη' : 2 * Real.sqrt η < 1 / 10) (hA : 1 ≤ A)
    (hrmin : 0 < rmin) (hrr : rmin ≤ rmax)
    (hcover : ∀ t ∈ Icc 0 L, ∃ c r, dist c (P t) < rmin / 10 ∧ r ∈ Icc rmin rmax ∧
      Core.GoodDiskIn d d' W P L η d₀ A Kf c r)
    (hfar : 1024 * rmax < dist (P 0) (P L)) :
    Nonempty (L41Cert d' W P L η d₀ A Kf rmin rmax) := by
  classical
  obtain ⟨hgeo, hunit, hPc, _⟩ := hP
  have hL : 0 ≤ L := hgeo.1
  have hrmax : 0 < rmax := hrmin.trans_le hrr
  have hA0 : 0 < A := by linarith
  -- the segment `J = [a₀, b₀]` (SB2 D6 step 2)
  obtain ⟨a₀, b₀, ha₀, hab₀, hb₀L, ha₀z, hb₀w, hJ⟩ :=
    l41_J_exists (ρ := 64 * rmax) hPc hL (by positivity) (by linarith)
  -- a good disk and its excursion at every time of `J` (SB2 D6 steps 3–5)
  have hex : ∀ τ ∈ Icc a₀ b₀, ∃ (c : ℂ) (r α β s t : ℝ), rmin ≤ r ∧ r ≤ rmax ∧ α < τ ∧ τ ≤ s ∧
      L41Exc d' W P L η d₀ A Kf c r α β s t := by
    intro τ hτ
    have hτL : τ ∈ Icc 0 L := ⟨ha₀.le.trans hτ.1, hτ.2.trans hb₀L⟩
    obtain ⟨c, r, hcτ, hr, hg⟩ := hcover τ hτL
    have hr0 : 0 < r := hg.pos
    have hτc : dist (P τ) c < r := by
      rw [dist_comm]
      linarith [hr.1]
    have h0 : 8 * r ≤ dist (P 0) c := by
      have h1 := (hJ τ hτ).1
      have htri := dist_triangle (P τ) c (P 0)
      rw [dist_comm c (P 0)] at htri
      linarith [hr.2]
    have hLc : 8 * r ≤ dist (P L) c := by
      have h1 := (hJ τ hτ).2
      have htri := dist_triangle (P τ) c (P L)
      rw [dist_comm c (P L)] at htri
      linarith [hr.2]
    obtain ⟨α, β, s, t, hατ, hτs, hx⟩ :=
      l41_goodDisk_exc hg hgeo hunit hPc hη' hA0.le hτL hτc h0 hLc
    exact ⟨c, r, α, β, s, t, hr.1, hr.2, hατ, hτs, hx⟩
  choose! cf rf αf βf sf tf hrmin' hrmax' hατ hτs hdata using hex
  -- the finite subcover of `J` and the greedy selection (SB2 D6 step 6)
  let I : ℝ → D4Interval := fun τ => (αf τ, βf τ)
  have hIgood : ∀ τ ∈ Icc a₀ b₀, (I τ).1 < (I τ).2 ∧ τ ∈ Ioo (I τ).1 (I τ).2 := by
    intro τ hτ
    have hx := hdata τ hτ
    have h1 := hατ τ hτ
    have h2 := hτs τ hτ
    exact ⟨show αf τ < βf τ by linarith [hx.α_lt_s, hx.s_lt_t, hx.t_lt_β],
      ⟨h1, show τ < βf τ by linarith [hx.s_lt_t, hx.t_lt_β]⟩⟩
  obtain ⟨F, hFpos, hFmeet, hFcover, hFidx⟩ := d4_finite_interval_subcover I hIgood
  choose! τJ hτJ hτJeq using hFidx
  obtain ⟨l, hRun⟩ := d4_exists_greedyRun F hFpos
  have hsub : ∀ J ∈ l.toFinset, J ∈ F := fun J hJ =>
    (d4_greedyRun_spec hFpos hRun).1 J (List.mem_toFinset.mp hJ)
  let good : D4Interval → ℝ := fun J => tf (τJ J) - sf (τJ J)
  have hgoodLower : ∀ J ∈ l.toFinset, d4IntervalLength J / A ≤ good J := by
    intro J hJ
    have hJF := hsub J hJ
    have hx := hdata (τJ J) (hτJ J hJF)
    have hEq := hτJeq J hJF
    rw [div_le_iff₀ hA0]
    have hlen : d4IntervalLength J = βf (τJ J) - αf (τJ J) := by
      unfold d4IntervalLength
      rw [congrArg Prod.fst hEq, congrArg Prod.snd hEq]
    rw [hlen]
    show βf (τJ J) - αf (τJ J) ≤ (tf (τJ J) - sf (τJ J)) * A
    linarith [hx.frac]
  have hgoodUpper : ∀ J ∈ l.toFinset, good J ≤ d4IntervalLength J := by
    intro J hJ
    have hJF := hsub J hJ
    have hx := hdata (τJ J) (hτJ J hJF)
    have hEq := hτJeq J hJF
    have hlen : d4IntervalLength J = βf (τJ J) - αf (τJ J) := by
      unfold d4IntervalLength
      rw [congrArg Prod.fst hEq, congrArg Prod.snd hEq]
    rw [hlen]
    show tf (τJ J) - sf (τJ J) ≤ βf (τJ J) - αf (τJ J)
    linarith [hx.α_lt_s, hx.t_lt_β]
  obtain ⟨left, right, hhull, hSle, -, -, hGge⟩ :=
    d4_greedy_cover_good_fraction hFpos hRun hab₀.le hFcover hFmeet hA0 rfl good hgoodLower
      hgoodUpper
  -- the increasing enumeration of the selected intervals
  have hdisjSel : ∀ J ∈ l.toFinset, ∀ J' ∈ l.toFinset, J ≠ J' →
      Disjoint (Ioo J.1 J.2) (Ioo J'.1 J'.2) := by
    intro J hJ J' hJ' hne
    have h := d4_greedyRun_pairwiseDisjoint hFpos hRun (Finset.mem_coe.mpr hJ)
      (Finset.mem_coe.mpr hJ') hne
    simp only [Function.onFun] at h
    rwa [d4IntervalBall_eq_Ioo, d4IntervalBall_eq_Ioo] at h
  obtain ⟨k, e, himg, hinj, hord⟩ :=
    l41_sort_intervals l.toFinset hdisjSel (fun J hJ => hFpos J (hsub J hJ))
  have hemem : ∀ i < k, e i ∈ l.toFinset := fun i hi => by
    rw [← himg]
    exact Finset.mem_image_of_mem e (Finset.mem_range.mpr hi)
  have hτe : ∀ i < k, τJ (e i) ∈ Icc a₀ b₀ := fun i hi => hτJ _ (hsub _ (hemem i hi))
  have he1 : ∀ i < k, (e i).1 = αf (τJ (e i)) := fun i hi =>
    congrArg Prod.fst (hτJeq (e i) (hsub _ (hemem i hi)))
  have he2 : ∀ i < k, (e i).2 = βf (τJ (e i)) := fun i hi =>
    congrArg Prod.snd (hτJeq (e i) (hsub _ (hemem i hi)))
  -- the endpoint estimates (`76 r_max`)
  have hleft : dist (P left) (P 0) ≤ 76 * rmax ∧ 0 ≤ left := by
    rcases hhull.left_extreme with h | ⟨J, hJ, hJleft⟩
    · rw [h]
      exact ⟨by linarith, ha₀.le⟩
    · have hJF := hsub J hJ
      have hτ := hτJ J hJF
      have hx := hdata (τJ J) hτ
      have hEq := hτJeq J hJF
      have hαl : αf (τJ J) = left := (congrArg Prod.fst hEq).symm.trans hJleft
      have ha₀I : a₀ ∈ Icc (αf (τJ J)) (βf (τJ J)) :=
        ⟨by rw [hαl]; exact hhull.left_le,
          by linarith [hτ.1, hτs (τJ J) hτ, hx.s_lt_t, hx.t_lt_β]⟩
      have h1 := hx.in6 a₀ ha₀I
      have h2 := hx.in6 (αf (τJ J)) ⟨le_rfl, by linarith [hx.α_lt_s, hx.s_lt_t, hx.t_lt_β]⟩
      have hrle := hrmax' (τJ J) hτ
      rw [hαl] at h2
      have htri := dist_triangle (P left) (cf (τJ J)) (P 0)
      have htri2 := dist_triangle (cf (τJ J)) (P a₀) (P 0)
      rw [dist_comm (cf (τJ J)) (P a₀)] at htri2
      refine ⟨by linarith, ?_⟩
      rw [← hαl]
      exact hx.α_pos.le
  have hright : dist (P right) (P L) ≤ 76 * rmax ∧ right ≤ L := by
    rcases hhull.right_extreme with h | ⟨J, hJ, hJright⟩
    · rw [h]
      exact ⟨by linarith, hb₀L⟩
    · have hJF := hsub J hJ
      have hτ := hτJ J hJF
      have hx := hdata (τJ J) hτ
      have hEq := hτJeq J hJF
      have hβr : βf (τJ J) = right := (congrArg Prod.snd hEq).symm.trans hJright
      have hb₀I : b₀ ∈ Icc (αf (τJ J)) (βf (τJ J)) :=
        ⟨by linarith [hτ.2, hατ (τJ J) hτ], by rw [hβr]; exact hhull.right_ge⟩
      have h1 := hx.in6 b₀ hb₀I
      have h2 := hx.in6 (βf (τJ J)) ⟨by linarith [hx.α_lt_s, hx.s_lt_t, hx.t_lt_β], le_rfl⟩
      have hrle := hrmax' (τJ J) hτ
      rw [hβr] at h2
      have htri := dist_triangle (P right) (cf (τJ J)) (P L)
      have htri2 := dist_triangle (cf (τJ J)) (P b₀) (P L)
      rw [dist_comm (cf (τJ J)) (P b₀)] at htri2
      refine ⟨by linarith, ?_⟩
      rw [← hβr]
      exact hx.β_lt.le
  -- the sums over the selected intervals, reindexed
  have hSsum : ∑ J ∈ l.toFinset, d4IntervalLength J =
      ∑ i ∈ Finset.range k, (βf (τJ (e i)) - αf (τJ (e i))) := by
    rw [← himg, Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hik := Finset.mem_range.mp hi
    show (e i).2 - (e i).1 = _
    rw [he1 i hik, he2 i hik]
  have hGsum : ∑ J ∈ l.toFinset, good J =
      ∑ i ∈ Finset.range k, (tf (τJ (e i)) - sf (τJ (e i))) := by
    rw [← himg, Finset.sum_image hinj]
  refine ⟨{
    k := k
    left := left
    right := right
    c := fun i => cf (τJ (e i))
    r := fun i => rf (τJ (e i))
    α := fun i => αf (τJ (e i))
    β := fun i => βf (τJ (e i))
    s := fun i => sf (τJ (e i))
    t := fun i => tf (τJ (e i))
    left_nonneg := hleft.2
    right_le := hright.2
    left_le_right := hhull.left_le.trans (hab₀.le.trans hhull.right_ge)
    exc := fun i hi => ⟨hrmin' _ (hτe i hi), hrmax' _ (hτe i hi), hdata _ (hτe i hi)⟩
    first := ?_
    step := ?_
    last := ?_
    left_near := hleft.1
    right_near := hright.1
    S_le := ?_
    G_ge := ?_ }⟩
  · intro hk
    have h := (hhull.intervals_inside (e 0) (hemem 0 hk)).1
    rw [he1 0 hk] at h
    exact h
  · intro i hi
    have h := hord i (i + 1) (Nat.lt_succ_self i) hi
    rw [he2 i (by omega), he1 (i + 1) hi] at h
    exact h
  · intro hk
    have h := (hhull.intervals_inside (e (k - 1)) (hemem (k - 1) (by omega))).2
    rw [he2 (k - 1) (by omega)] at h
    exact h
  · show ∑ i ∈ Finset.range k, (βf (τJ (e i)) - αf (τJ (e i))) ≤ right - left
    rw [← hSsum]
    exact hSle
  · show 1 / (5 * A) * (right - left) ≤ ∑ i ∈ Finset.range k, (tf (τJ (e i)) - sf (τJ (e i)))
    rw [← hGsum]
    exact hGge

/-- **Lemma 4.1′** (paper Lemma 4.1, l. 402–470; SB2 §2.4, Details D5–D6, SB3 §5(b)), in the interface form
`Core.Lemma41Stmt`: for a unit-speed source geodesic `P : [0, L] → B_R(0)` all of whose points have a good disk
within `r_min/10` with radius in `[r_min, r_max]`, and a prior comparison `(C₀, ρ_old < η r_min/4)` on all
subsegments, `d'(B_{513 r_max}(P 0), B_{513 r_max}(P L); W) ≤ F(C₀, K) L` with `λ = 1/(5A)`. -/
theorem lemma41_holds : Core.Lemma41Stmt := by
  intro d d' W R hWb hWc hWR P L hP η d₀ A Kf C₀ rmin rmax ρold hη hη' hd₀ hA hKf hC₀ hrmin hrr _
    hρ hρold hcover hprior
  have hL : 0 ≤ L := hP.1.1
  have hrmax : 0 < rmax := hrmin.trans_le hrr
  have hη1 : η < 1 := by
    have h1 : Real.sqrt η < 1 / 20 := by linarith
    have h2 := Real.sq_sqrt hη.le
    nlinarith [Real.sqrt_nonneg η]
  have hρr : ρold < rmax := by nlinarith
  by_cases hclose : dist (P 0) (P L) ≤ 1024 * rmax
  · -- the output balls overlap at the midpoint, which lies in `W` (SB2 D6 step 1)
    have hzW : P 0 ∈ W := hWR (ball_subset_ball (by linarith) (hP.2.2.2 0 ⟨le_rfl, hL⟩))
    have hwW : P L ∈ W := hWR (ball_subset_ball (by linarith) (hP.2.2.2 L ⟨hL, le_rfl⟩))
    have hpW : midpoint ℝ (P 0) (P L) ∈ W := hWc.midpoint_mem hzW hwW
    have hpz : midpoint ℝ (P 0) (P L) ∈ ball (P 0) (513 * rmax) := by
      rw [mem_ball, dist_comm, dist_left_midpoint]
      norm_num
      nlinarith
    have hpw : midpoint ℝ (P 0) (P L) ∈ ball (P L) (513 * rmax) := by
      rw [mem_ball, dist_midpoint_right]
      norm_num
      nlinarith
    have hself : d'.internal W (⟨midpoint ℝ (P 0) (P L), hpW⟩, ⟨midpoint ℝ (P 0) (P L), hpW⟩) = 0 :=
      (d'.isExtMetric_internal W).1 _
    calc d'.internalSetDist W {y | (y : ℂ) ∈ ball (P 0) (513 * rmax)}
          {y | (y : ℂ) ∈ ball (P L) (513 * rmax)}
        ≤ d'.internal W (⟨midpoint ℝ (P 0) (P L), hpW⟩, ⟨midpoint ℝ (P 0) (P L), hpW⟩) := by
          unfold LSCMetric.internalSetDist
          exact iInf₂_le_of_le ⟨midpoint ℝ (P 0) (P L), hpW⟩ hpz
            (iInf₂_le_of_le ⟨midpoint ℝ (P 0) (P L), hpW⟩ hpw le_rfl)
      _ = 0 := hself
      _ ≤ _ := zero_le
  · obtain ⟨Q⟩ := l41_cert_exists hP hη' hA hrmin hrr hcover (lt_of_not_ge hclose)
    exact l41_far_of_cert hWb hη hd₀ hA hKf hC₀ hρ hρold hρr hprior Q

end SupercriticalLFPPAS.Contraction
