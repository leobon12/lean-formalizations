import HigherDimLQGMetric.Sec6.Curves
import HigherDimLQGMetric.Sec6.Transfer

/-!
# [S] §6: collar, departure and return, geodesic segments, occupation sums

Packet S6a. The deterministic tools of MA3 D-6.2, *Proof of (T)*, for a trap annulus `A` (open), a
collector `V_z` (open, `closure V_z ⊆ A`) and a domain `W ⊇ closure A`, with a collar
`D₀(x, y; W) ≥ κ` for `x ∈ closure V_z`, `y ∈ frontier A`:

* `len_le_len_weyl`, `len_le_exp_mul_len_weyl`: for `D' = e^{ξ g}·D₀`, `len(P; D₀) ≤ len(P; D')` where
  `ξ g ≥ 0` along `P`, and `len(P; D₀) ≤ e^m len(P; D')` where `ξ g ≥ −m` along `P`;
* `collar_le_len`: a curve from `closure V_z` that leaves `A` has `D₀`-length `≥ κ` ((T1));
* `depart_return`: a curve from `closure V_z` to `closure V_z` that leaves `A` has `D'`-length `≥ 2κ`
  when `g = 0` on `closure A ∖ V_z` (departure and return portions);
* `len_le_internal_of_isGeodIn`, `len_le_of_isGeod`: segments of (internal) geodesics are minimal;
* `sum_len_le_of_pairwiseDisjoint`: lengths over pairwise disjoint subintervals of `[σ₁, σ₂]` sum to at
  most the length over `[σ₁, σ₂]` (for the occupation bound (T4)).

All helpers live in the namespace `HigherDimLQGMetric.S6a`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

namespace S6a

open Set Metric
open HigherDimLFPP (Rd)
open LQGMetric.MetricGeometry
open scoped ENNReal

variable {d : ℕ}

/-! ### Comparison of lengths under Weyl scaling -/

/-- Where the Weyl exponent is nonnegative along the curve, the Weyl-scaled length dominates. -/
theorem len_le_len_weyl {D₀ D' : ContMetric d} {ξ : ℝ} {g : C(Rd d, ℝ)}
    (hD' : IsWeylOf ξ g D₀ D') {P : ℝ → Rd d} {α β : ℝ} (hαβ : α ≤ β)
    (hP : ContinuousOn P (Icc α β)) (hg : ∀ t ∈ Icc α β, 0 ≤ ξ * g (P t)) :
    D₀.len P α β ≤ D'.len P α β := by
  rw [ContMetric.len_def, ContMetric.len_def, curveLength_eq_weightedLength_of_weyl hD' hP]
  have h := ofReal_mul_curveLength_le_weightedLength (w := D₀.weylWeight ξ g) (P := D₀.pt ∘ P)
    (m := 1) hαβ (fun t ht => by
      change (1 : ℝ) ≤ Real.exp (ξ * g (P t))
      exact Real.one_le_exp (hg t ht))
  rwa [ENNReal.ofReal_one, one_mul] at h

/-- Where the Weyl exponent is at least `−m` along the curve, `len(P; D₀) ≤ e^m len(P; D')`. -/
theorem len_le_exp_mul_len_weyl {D₀ D' : ContMetric d} {ξ : ℝ} {g : C(Rd d, ℝ)}
    (hD' : IsWeylOf ξ g D₀ D') {P : ℝ → Rd d} {α β : ℝ} (hαβ : α ≤ β)
    (hP : ContinuousOn P (Icc α β)) {m : ℝ} (hg : ∀ t ∈ Icc α β, -m ≤ ξ * g (P t)) :
    D₀.len P α β ≤ ENNReal.ofReal (Real.exp m) * D'.len P α β := by
  rw [ContMetric.len_def, ContMetric.len_def, curveLength_eq_weightedLength_of_weyl hD' hP]
  have h := ofReal_mul_curveLength_le_weightedLength (w := D₀.weylWeight ξ g) (P := D₀.pt ∘ P)
    (m := Real.exp (-m)) hαβ (fun t ht => by
      change Real.exp (-m) ≤ Real.exp (ξ * g (P t))
      exact Real.exp_le_exp.2 (hg t ht))
  calc curveLength (D₀.pt ∘ P) α β
      = ENNReal.ofReal (Real.exp m) *
          (ENNReal.ofReal (Real.exp (-m)) * curveLength (D₀.pt ∘ P) α β) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos m).le, ← Real.exp_add,
          add_neg_cancel, Real.exp_zero, ENNReal.ofReal_one, one_mul]
    _ ≤ _ := mul_le_mul' le_rfl h

/-! ### Collar, departure and return -/

/-- **(T1), general form.** A curve on `[α, β]` from `closure V_z` that is outside the open `A` at some
time has `D₀`-length at least the collar `κ`. -/
theorem collar_le_len (D₀ : ContMetric d) {A W Vz : Set (Rd d)} (hA : IsOpen A)
    (hVzA : closure Vz ⊆ A) (hAW : closure A ⊆ W) {κ : ℝ≥0∞}
    (hcol : ∀ x ∈ closure Vz, ∀ y ∈ frontier A, κ ≤ D₀.internal W x y)
    {P : ℝ → Rd d} {α β : ℝ} (hP : ContinuousOn P (Icc α β)) (hα : P α ∈ closure Vz)
    {t : ℝ} (ht : t ∈ Icc α β) (htA : P t ∉ A) : κ ≤ D₀.len P α β := by
  obtain ⟨τ, hτ, hτfr, hbefore⟩ := exists_first_exit hA hP (hVzA hα) ht htA
  have hτβ : τ ≤ β := hτ.2.trans ht.2
  have hmaps : MapsTo P (Icc α τ) W := by
    intro s hs
    apply hAW
    rcases hs.2.lt_or_eq with hlt | heq
    · exact subset_closure (hbefore s ⟨hs.1, hlt⟩)
    · rw [heq]
      exact frontier_subset_closure hτfr
  calc κ ≤ D₀.internal W (P α) (P τ) := hcol _ hα _ hτfr
    _ ≤ D₀.len P α τ := D₀.internal_le_len hτ.1 (hP.mono (Icc_subset_Icc le_rfl hτβ)) hmaps
    _ ≤ D₀.len P α β := D₀.len_mono P le_rfl hτβ

/-- **Departure and return** (MA3 D-6.2). Let `D' = e^{ξ g}·D₀` with `g = 0` on `closure A ∖ V_z`. A curve
on `[α, β]` from `closure V_z` to `closure V_z` that is outside `A` at some time has `D'`-length at least
`2κ`: after its last collector visit before the first exit it runs in `closure A ∖ V_z` up to `frontier A`
(departure), and before its first collector visit after the last entry it runs in `closure A ∖ V_z` from
`frontier A` (return); on both portions the weight is `1` and the collar applies. -/
theorem depart_return {D₀ D' : ContMetric d} {ξ : ℝ} {g : C(Rd d, ℝ)} (hD' : IsWeylOf ξ g D₀ D')
    {A W Vz : Set (Rd d)} (hA : IsOpen A) (hVz : IsOpen Vz) (hVzA : closure Vz ⊆ A)
    (hAW : closure A ⊆ W) (hg : ∀ x ∈ closure A, x ∉ Vz → g x = 0) {κ : ℝ≥0∞}
    (hcol : ∀ x ∈ closure Vz, ∀ y ∈ frontier A, κ ≤ D₀.internal W x y)
    {P : ℝ → Rd d} {α β : ℝ} (hP : ContinuousOn P (Icc α β)) (hα : P α ∈ closure Vz)
    (hβ : P β ∈ closure Vz) {t : ℝ} (ht : t ∈ Icc α β) (htA : P t ∉ A) :
    κ + κ ≤ D'.len P α β := by
  have hfrA : ∀ {y : Rd d}, y ∈ frontier A → y ∉ A := fun hy hyA => by
    rw [hA.frontier_eq] at hy
    exact hy.2 hyA
  -- departure: first exit `τe`, last collector visit `τd` before it
  obtain ⟨τe, hτe, hτefr, hbefore⟩ := exists_first_exit hA hP (hVzA hα) ht htA
  have hτeβ : τe ≤ β := hτe.2.trans ht.2
  have hτeA : P τe ∉ A := hfrA hτefr
  obtain ⟨τd, hτd, hτdV, hτdout⟩ :=
    exists_last_visit hVz (hP.mono (Icc_subset_Icc le_rfl hτeβ)) hτe.1 hα
      (fun h => hτeA (hVzA h))
  have hdepcl : ∀ s ∈ Icc τd τe, P s ∈ closure A := by
    intro s hs
    rcases hs.2.lt_or_eq with hlt | heq
    · exact subset_closure (hbefore s ⟨hτd.1.trans hs.1, hlt⟩)
    · rw [heq]
      exact frontier_subset_closure hτefr
  have hPd : ContinuousOn P (Icc τd τe) := hP.mono (Icc_subset_Icc hτd.1 hτeβ)
  have hdep : κ ≤ D'.len P τd τe :=
    calc κ ≤ D₀.internal W (P τd) (P τe) := hcol _ hτdV _ hτefr
      _ ≤ D₀.len P τd τe := D₀.internal_le_len hτd.2 hPd (fun s hs => hAW (hdepcl s hs))
      _ ≤ D'.len P τd τe := len_le_len_weyl hD' hτd.2 hPd (fun s hs => by
          rw [hg _ (hdepcl s hs) (hτdout s hs), mul_zero])
  -- return: last entry `τr ≥ τe`, first collector visit `τc` after it
  have hPe : ContinuousOn P (Icc τe β) := hP.mono (Icc_subset_Icc (hτe.1) le_rfl)
  obtain ⟨τr, hτr, hτrfr, hafter⟩ := exists_last_entry hA hPe (hVzA hβ) ⟨le_rfl, hτeβ⟩ hτeA
  have hτrV : P τr ∉ closure Vz := fun h => hfrA hτrfr (hVzA h)
  obtain ⟨τc, hτc, hτcV, hτcout⟩ :=
    exists_first_visit hVz (hP.mono (Icc_subset_Icc (hτe.1.trans hτr.1) le_rfl)) hτr.2 hβ hτrV
  have hretcl : ∀ s ∈ Icc τr τc, P s ∈ closure A := by
    intro s hs
    rcases hs.1.lt_or_eq with hlt | heq
    · exact subset_closure (hafter s ⟨hlt, hs.2.trans hτc.2⟩)
    · rw [← heq]
      exact frontier_subset_closure hτrfr
  have hPr : ContinuousOn P (Icc τr τc) :=
    hP.mono (Icc_subset_Icc (hτe.1.trans hτr.1) hτc.2)
  have hret : κ ≤ D'.len P τr τc :=
    calc κ ≤ D₀.internal W (P τc) (P τr) := hcol _ hτcV _ hτrfr
      _ = D₀.internal W (P τr) (P τc) := D₀.internal_comm _ _ _
      _ ≤ D₀.len P τr τc := D₀.internal_le_len hτc.1 hPr (fun s hs => hAW (hretcl s hs))
      _ ≤ D'.len P τr τc := len_le_len_weyl hD' hτc.1 hPr (fun s hs => by
          rw [hg _ (hretcl s hs) (hτcout s hs), mul_zero])
  -- combine `α ≤ τd ≤ τe ≤ τr ≤ τc ≤ β`
  calc κ + κ ≤ D'.len P τd τe + D'.len P τr τc := add_le_add hdep hret
    _ ≤ D'.len P τd τe + D'.len P τe τc := add_le_add le_rfl (D'.len_mono P hτr.1 le_rfl)
    _ = D'.len P τd τc := D'.len_add P hτd.2 (hτr.1.trans hτc.1)
    _ ≤ D'.len P α β := D'.len_mono P hτd.1 hτc.2

/-! ### Segments of geodesics -/

/-- A segment of an internal geodesic of finite length is minimal: `len(P|[σ₁,σ₂]) ≤ D(P σ₁, P σ₂; B)`. -/
theorem len_le_internal_of_isGeodIn {D : ContMetric d} {B : Set (Rd d)} {P : ℝ → Rd d}
    (hP : IsGeodIn D B P) (hfin : D.internal B (P 0) (P 1) ≠ ⊤) {σ₁ σ₂ : ℝ} (h0 : 0 ≤ σ₁)
    (h12 : σ₁ ≤ σ₂) (h2 : σ₂ ≤ 1) : D.len P σ₁ σ₂ ≤ D.internal B (P σ₁) (P σ₂) := by
  obtain ⟨hPc, hPB, hlen⟩ := hP
  have hsub : ∀ {a b : ℝ}, 0 ≤ a → b ≤ 1 → Icc a b ⊆ Icc 0 1 := fun ha hb =>
    Icc_subset_Icc ha hb
  have hmaps : ∀ {a b : ℝ}, 0 ≤ a → b ≤ 1 → MapsTo P (Icc a b) B := fun ha hb s hs =>
    hPB s (hsub ha hb hs)
  have hl1 : D.len P 0 σ₁ ≠ ⊤ :=
    ne_top_of_le_ne_top (hlen ▸ hfin) (D.len_mono P le_rfl (h12.trans h2))
  have hl3 : D.len P σ₂ 1 ≠ ⊤ :=
    ne_top_of_le_ne_top (hlen ▸ hfin) (D.len_mono P (h0.trans h12) le_rfl)
  have hsplit : D.len P 0 1 = D.len P 0 σ₁ + D.len P σ₁ σ₂ + D.len P σ₂ 1 := by
    rw [D.len_add P h0 h12, D.len_add P (h0.trans h12) h2]
  have htri : D.internal B (P 0) (P 1) ≤
      D.len P 0 σ₁ + D.internal B (P σ₁) (P σ₂) + D.len P σ₂ 1 := by
    calc D.internal B (P 0) (P 1)
        ≤ D.internal B (P 0) (P σ₂) + D.internal B (P σ₂) (P 1) := D.internal_triangle _ _ _ _
      _ ≤ (D.internal B (P 0) (P σ₁) + D.internal B (P σ₁) (P σ₂)) +
            D.internal B (P σ₂) (P 1) := add_le_add (D.internal_triangle _ _ _ _) le_rfl
      _ ≤ (D.len P 0 σ₁ + D.internal B (P σ₁) (P σ₂)) + D.len P σ₂ 1 := by
          refine add_le_add (add_le_add ?_ le_rfl) ?_
          · exact D.internal_le_len h0 (hPc.mono (hsub le_rfl (h12.trans h2)))
              (hmaps le_rfl (h12.trans h2))
          · exact D.internal_le_len h2 (hPc.mono (hsub (h0.trans h12) le_rfl))
              (hmaps (h0.trans h12) le_rfl)
  rw [← hlen, hsplit] at htri
  exact ENNReal.le_of_add_le_add_left hl1 (ENNReal.le_of_add_le_add_right hl3 htri)

/-- A segment of a (global) geodesic is minimal: `len(P|[σ₁,σ₂]) ≤ D(P σ₁, P σ₂)`. -/
theorem len_le_of_isGeod {D : ContMetric d} {P : ℝ → Rd d} (hP : IsGeod D P) {σ₁ σ₂ : ℝ}
    (h0 : 0 ≤ σ₁) (h12 : σ₁ ≤ σ₂) (h2 : σ₂ ≤ 1) :
    D.len P σ₁ σ₂ ≤ ENNReal.ofReal (D.1 (P σ₁, P σ₂)) := by
  obtain ⟨-, hlen⟩ := hP
  have hfin : D.len P 0 1 ≠ ⊤ := hlen ▸ ENNReal.ofReal_ne_top
  have hl1 : D.len P 0 σ₁ ≠ ⊤ := ne_top_of_le_ne_top hfin (D.len_mono P le_rfl (h12.trans h2))
  have hl3 : D.len P σ₂ 1 ≠ ⊤ := ne_top_of_le_ne_top hfin (D.len_mono P (h0.trans h12) le_rfl)
  have hsplit : D.len P 0 1 = D.len P 0 σ₁ + D.len P σ₁ σ₂ + D.len P σ₂ 1 := by
    rw [D.len_add P h0 h12, D.len_add P (h0.trans h12) h2]
  have htri3 : ∀ x y w : Rd d, ENNReal.ofReal (D.1 (x, w)) ≤
      ENNReal.ofReal (D.1 (x, y)) + ENNReal.ofReal (D.1 (y, w)) := fun x y w => by
    rw [← ENNReal.ofReal_add (D.nonneg x y) (D.nonneg y w)]
    exact ENNReal.ofReal_le_ofReal (D.2.triangle x y w)
  have htri : ENNReal.ofReal (D.1 (P 0, P 1)) ≤
      D.len P 0 σ₁ + ENNReal.ofReal (D.1 (P σ₁, P σ₂)) + D.len P σ₂ 1 := by
    calc ENNReal.ofReal (D.1 (P 0, P 1))
        ≤ ENNReal.ofReal (D.1 (P 0, P σ₂)) + ENNReal.ofReal (D.1 (P σ₂, P 1)) := htri3 _ _ _
      _ ≤ (ENNReal.ofReal (D.1 (P 0, P σ₁)) + ENNReal.ofReal (D.1 (P σ₁, P σ₂))) +
            ENNReal.ofReal (D.1 (P σ₂, P 1)) := add_le_add (htri3 _ _ _) le_rfl
      _ ≤ (D.len P 0 σ₁ + ENNReal.ofReal (D.1 (P σ₁, P σ₂))) + D.len P σ₂ 1 :=
          add_le_add (add_le_add (D.ofReal_le_len P h0) le_rfl) (D.ofReal_le_len P h2)
  rw [← hlen, hsplit] at htri
  exact ENNReal.le_of_add_le_add_left hl1 (ENNReal.le_of_add_le_add_right hl3 htri)

/-! ### Lengths over disjoint subintervals -/

/-- Lengths over finitely many subintervals of `[σ₁, σ₂]` with pairwise disjoint interiors sum to at most
the length over `[σ₁, σ₂]`. -/
theorem sum_len_le_of_pairwiseDisjoint (D : ContMetric d) (P : ℝ → Rd d) (σ₁ : ℝ)
    (I : Finset (ℝ × ℝ)) :
    (I : Set (ℝ × ℝ)).PairwiseDisjoint (fun p => Ioo p.1 p.2) → ∀ σ₂ : ℝ,
      (∀ p ∈ I, σ₁ ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ σ₂) →
      ∑ p ∈ I, D.len P p.1 p.2 ≤ D.len P σ₁ σ₂ := by
  classical
  refine Finset.induction_on_max_value (fun p : ℝ × ℝ => p.1)
    (motive := fun I => (I : Set (ℝ × ℝ)).PairwiseDisjoint (fun p => Ioo p.1 p.2) → ∀ σ₂ : ℝ,
      (∀ p ∈ I, σ₁ ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ σ₂) →
      ∑ p ∈ I, D.len P p.1 p.2 ≤ D.len P σ₁ σ₂) I ?_ ?_
  · intro _ σ₂ _
    rw [Finset.sum_empty]
    exact bot_le
  · intro a I haI hmax ih hdisj σ₂ hσ
    rw [Finset.sum_insert haI]
    have hdisjI : (I : Set (ℝ × ℝ)).PairwiseDisjoint (fun p => Ioo p.1 p.2) :=
      hdisj.subset (by rw [Finset.coe_insert]; exact subset_insert _ _)
    obtain ⟨ha1, ha12, ha2⟩ := hσ a (Finset.mem_insert_self a I)
    rcases ha12.lt_or_eq with hlt | heq
    · -- a non-degenerate interval: every other interval lies to its left
      have hleft : ∀ p ∈ I, σ₁ ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ a.1 := by
        intro p hp
        obtain ⟨hp1, hp12, -⟩ := hσ p (Finset.mem_insert_of_mem hp)
        refine ⟨hp1, hp12, ?_⟩
        by_contra hcon
        rw [not_le] at hcon
        have hpa : p.1 ≤ a.1 := hmax p hp
        have hne : a ≠ p := fun h => haI (h ▸ hp)
        have hd := hdisj (Finset.mem_coe.2 (Finset.mem_insert_self a I))
          (Finset.mem_coe.2 (Finset.mem_insert_of_mem hp)) hne
        have hm1 : a.1 < (a.1 + min a.2 p.2) / 2 := by
          have : a.1 < min a.2 p.2 := lt_min hlt hcon
          linarith
        have hm2 : (a.1 + min a.2 p.2) / 2 < min a.2 p.2 := by
          have : a.1 < min a.2 p.2 := lt_min hlt hcon
          linarith
        exact Set.disjoint_left.1 hd ⟨hm1, lt_of_lt_of_le hm2 (min_le_left _ _)⟩
          ⟨lt_of_le_of_lt hpa hm1, lt_of_lt_of_le hm2 (min_le_right _ _)⟩
      calc D.len P a.1 a.2 + ∑ p ∈ I, D.len P p.1 p.2
          ≤ D.len P a.1 a.2 + D.len P σ₁ a.1 := add_le_add le_rfl (ih hdisjI a.1 hleft)
        _ = D.len P σ₁ a.2 := by rw [add_comm, D.len_add P ha1 ha12]
        _ ≤ D.len P σ₁ σ₂ := D.len_mono P le_rfl ha2
    · -- a degenerate interval contributes `0`
      have h0 : D.len P a.1 a.2 = 0 := by
        rw [ContMetric.len_def, heq]
        exact curveLength_self _ _
      rw [h0, zero_add]
      exact ih hdisjI σ₂ (fun p hp => hσ p (Finset.mem_insert_of_mem hp))

end S6a

end HigherDimLQGMetric
