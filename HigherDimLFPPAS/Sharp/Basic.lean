import HigherDimLFPPAS.Core.Interfaces
import HigherDimLFPPAS.Windows.Constants
import HigherDimLFPPAS.Windows.Scales

/-!
# Proposition 5.1, deterministic part (packet P51)

Source: `planning/audits/MA2-sections-4-6.md` §§2.8–2.16 and Details D-B (items 1–3), MA4 §2.5 and
Details B.2–B.5, paper §5. Everything here is deterministic (no probability).

* Monotonicity of `Core.Comp` in the constant (`p51_comp_mono_C`) and in the endpoint exponent
  (`p51_comp_mono_q`, smaller exponent = larger endpoint balls for `ε ≤ 1`); set distances decrease
  when the domain and the endpoint sets grow (`p51_setDistIn_mono`).
* The initial comparison (MA2 §2.9): the good event of Lemma 2.7 at `q = 1/2`, `ρ = R + 1`
  (`p51Init`) gives `Comp(C₀, 1/2)` in both directions (`p51_comp_of_init`): enlarge the endpoint balls
  `ε^{1/2} → 8ε^{1/2}` and the domain `thickening (ε^{1/2}) B_{R+1} ⊆ B_{R+2}`; admissible paths have
  `len = D(·,·;B_{R+1})` (`p51_internal_eq_len`).
* The iteration lemma D-B3 (`p51_iterate`, `p51_select`): along an increasing chain of windows
  `0 = i₀ < i₁ < … < i_n ≤ M`, Proposition 4.1 with `(u, q₀) = (u_{i_j}, v_{i_{j−1}})` turns `Comp(C, v_{i_{j−1}})`
  into `Comp(winStep C, v_{i_j})`; after the chain, `Comp(winIter C₀ n, v_M)`.
* The recursion bound `winIter … n ≤ θ^N C₀ + m(1 + δ/10)` for `n ≥ N` (`p51_winIter_le_of_ge`) and the
  resulting constants `< 1` (low/high windows) and `< 1 + δ` (middle windows).
* Windows as finsets (`p51W`, junk-free; `= 𝒩_ε(u_i)` for `0 < ε < 1`), their cardinalities, positivity of
  their radii and of `c_ε(r)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace HigherDimLFPPAS.SharpComp

open HigherDimLQGMetric
open HigherDimLFPP (Rd e₁)
open HigherDimLFPPAS.Core
open HigherDimLFPPAS.Windows

variable {d : ℕ}

/-! ### Monotonicity of set distances and of `Comp` -/

/-- Set distances decrease when the domain and the endpoint sets grow. -/
theorem p51_setDistIn_mono (G : ContMetric d) {V V' A A' B B' : Set (Rd d)}
    (hV : V ⊆ V') (hA : A ⊆ A') (hB : B ⊆ B') :
    setDistIn G V' A' B' ≤ setDistIn G V A B := by
  unfold setDistIn
  refine le_iInf₂ fun u hu => le_iInf₂ fun v hv => ?_
  exact (iInf₂_le u (hA hu)).trans ((iInf₂_le v (hB hv)).trans (G.internal_anti hV u v))

/-- `Comp` is monotone in the constant. -/
theorem p51_comp_mono_C {G G' : ContMetric d} {R ε q C C' : ℝ} (hCC : C ≤ C')
    (h : Comp G G' R ε q C) : Comp G G' R ε q C' := by
  intro P T hP hPR
  exact (h P T hP hPR).trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal hCC) _)

/-- `Comp` is monotone in the endpoint exponent: for `0 < ε ≤ 1` a smaller exponent gives larger
endpoint balls, hence a smaller set distance. -/
theorem p51_comp_mono_q {G G' : ContMetric d} {R ε q q' C : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hqq : q' ≤ q) (h : Comp G G' R ε q C) : Comp G G' R ε q' C := by
  intro P T hP hPR
  have hpow : ε ^ q ≤ ε ^ q' := Real.rpow_le_rpow_of_exponent_ge hε0 hε1 hqq
  have hball : ∀ x : Rd d, ball x (8 * ε ^ q) ⊆ ball x (8 * ε ^ q') := fun x =>
    ball_subset_ball (by linarith)
  exact (p51_setDistIn_mono G' subset_rfl (hball _) (hball _)).trans (h P T hP hPR)

/-- For an internal geodesic the internal distance between the endpoints is the length. -/
theorem p51_internal_eq_len {G : ContMetric d} {V : Set (Rd d)} {P : ℝ → Rd d} {T : ℝ}
    (hP : IsInternalGeodesic G V P T) : G.internal V (P 0) (P T) = G.len P 0 T := by
  obtain ⟨hT, -, -, hint, hlen⟩ := hP
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT⟩
  have hT' : T ∈ Icc 0 T := ⟨hT, le_rfl⟩
  rw [hint 0 h0 T hT', hlen 0 h0 T hT' hT, sub_zero, abs_of_nonneg hT]

/-! ### The initial comparison (MA2 §2.9) -/

/-- The good event of Lemma 2.7 at `q = 1/2` and `ρ = R + 1`, for the ordered pair `(G, G')`
(`G = D`, `G' = M_ε`): both coarse comparisons (2.11)–(2.12) with constant `C₀` on `B_{R+1}`. -/
def p51Init (G G' : ContMetric d) (C₀ R ε : ℝ) : Prop :=
  ∀ x ∈ ball (0 : Rd d) (R + 1), ∀ y ∈ ball (0 : Rd d) (R + 1),
    setDistIn G' (thickening (ε ^ (1 / 2 : ℝ)) (ball 0 (R + 1))) (ball x (ε ^ (1 / 2 : ℝ)))
        (ball y (ε ^ (1 / 2 : ℝ))) ≤ ENNReal.ofReal C₀ * G.internal (ball 0 (R + 1)) x y ∧
      setDistIn G (thickening (ε ^ (1 / 2 : ℝ)) (ball 0 (R + 1))) (ball x (ε ^ (1 / 2 : ℝ)))
        (ball y (ε ^ (1 / 2 : ℝ))) ≤ ENNReal.ofReal C₀ * G'.internal (ball 0 (R + 1)) x y

/-- The initial comparison: on the good event of Lemma 2.7 (`q = 1/2`, `ρ = R + 1`) both
`Comp(C₀, 1/2)` properties hold (MA2 §2.9). -/
theorem p51_comp_of_init {G G' : ContMetric d} {C₀ R ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (h : p51Init G G' C₀ R ε) :
    Comp G G' R ε (1 / 2) C₀ ∧ Comp G' G R ε (1 / 2) C₀ := by
  have hs0 : 0 ≤ ε ^ (1 / 2 : ℝ) := Real.rpow_nonneg hε0.le _
  have hs1 : ε ^ (1 / 2 : ℝ) ≤ 1 := Real.rpow_le_one hε0.le hε1 (by norm_num)
  have hdom : thickening (ε ^ (1 / 2 : ℝ)) (ball (0 : Rd d) (R + 1)) ⊆ ball 0 (R + 2) :=
    (Metric.thickening_ball _ _ _).trans (ball_subset_ball (by linarith))
  have hball : ∀ x : Rd d, ball x (ε ^ (1 / 2 : ℝ)) ⊆ ball x (8 * ε ^ (1 / 2 : ℝ)) := fun x =>
    ball_subset_ball (by linarith)
  have hR : ball (0 : Rd d) R ⊆ ball 0 (R + 1) := ball_subset_ball (by linarith)
  constructor
  · intro P T hP hPR
    have hT : 0 ≤ T := hP.1
    have h0 := hR (hPR ⟨le_rfl, hT⟩)
    have hT' := hR (hPR ⟨hT, le_rfl⟩)
    calc setDistIn G' (ball 0 (R + 2)) (ball (P 0) (8 * ε ^ (1 / 2 : ℝ)))
          (ball (P T) (8 * ε ^ (1 / 2 : ℝ)))
        ≤ setDistIn G' (thickening (ε ^ (1 / 2 : ℝ)) (ball 0 (R + 1)))
            (ball (P 0) (ε ^ (1 / 2 : ℝ))) (ball (P T) (ε ^ (1 / 2 : ℝ))) :=
          p51_setDistIn_mono G' hdom (hball _) (hball _)
      _ ≤ ENNReal.ofReal C₀ * G.internal (ball 0 (R + 1)) (P 0) (P T) := (h _ h0 _ hT').1
      _ = ENNReal.ofReal C₀ * G.len P 0 T := by rw [p51_internal_eq_len hP]
  · intro P T hP hPR
    have hT : 0 ≤ T := hP.1
    have h0 := hR (hPR ⟨le_rfl, hT⟩)
    have hT' := hR (hPR ⟨hT, le_rfl⟩)
    calc setDistIn G (ball 0 (R + 2)) (ball (P 0) (8 * ε ^ (1 / 2 : ℝ)))
          (ball (P T) (8 * ε ^ (1 / 2 : ℝ)))
        ≤ setDistIn G (thickening (ε ^ (1 / 2 : ℝ)) (ball 0 (R + 1)))
            (ball (P 0) (ε ^ (1 / 2 : ℝ))) (ball (P T) (ε ^ (1 / 2 : ℝ))) :=
          p51_setDistIn_mono G hdom (hball _) (hball _)
      _ ≤ ENNReal.ofReal C₀ * G'.internal (ball 0 (R + 1)) (P 0) (P T) := (h _ h0 _ hT').2
      _ = ENNReal.ofReal C₀ * G'.len P 0 T := by rw [p51_internal_eq_len hP]

/-! ### Window exponents -/

theorem p51_winV_zero : winV 0 = 1 / 2 := by
  simp [winV, winU]

theorem p51_winV_pos (i : ℕ) : 0 < winV i := by
  unfold winV
  exact div_pos (winU_pos i) (by norm_num)

theorem p51_winU_le_one (i : ℕ) : winU i ≤ 1 := by
  unfold winU
  exact pow_le_one₀ (by norm_num) (by norm_num)

theorem p51_winV_lt_one (i : ℕ) : winV i < 1 := by
  unfold winV
  have := p51_winU_le_one i
  linarith

theorem p51_winV_anti {i j : ℕ} (hij : i ≤ j) : winV j ≤ winV i := by
  unfold winV
  exact div_le_div_of_nonneg_right (winU_antitone hij) (by norm_num)

/-! ### The recursion -/

theorem p51_winIter_step (θ η m C : ℝ) (n : ℕ) :
    winIter θ η m (winStep θ η m C) n = winIter θ η m C (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change winStep θ η m (winIter θ η m (winStep θ η m C) n) =
        winStep θ η m (winIter θ η m C (n + 1))
      rw [ih]

/-- After at least `N` contraction steps the constant is at most `θ^N C₀ + m(1 + δ/10)`
(closed form (5.5) with `η = (1−θ)δ/30`, MA2 D-B2). -/
theorem p51_winIter_le_of_ge {θ m C δ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hC : 0 ≤ C)
    (hm : 0 ≤ m) (hδ : 0 ≤ δ) {N n : ℕ} (hNn : N ≤ n) :
    winIter θ (winEta δ θ) m C n ≤ θ ^ N * C + m * (1 + δ / 10) := by
  rw [winIter_closed (ne_of_lt hθ1), win_fixed_factor δ θ (ne_of_lt hθ1)]
  have hpow : θ ^ n ≤ θ ^ N := pow_le_pow_of_le_one hθ0.le hθ1.le hNn
  have hpos : 0 ≤ θ ^ n := pow_nonneg hθ0.le n
  have hfac : 0 ≤ m * (1 + δ / 10) := mul_nonneg hm (by linarith)
  have h1 : θ ^ n * C ≤ θ ^ N * C := mul_le_mul_of_nonneg_right hpow hC
  have h2 : 0 ≤ m * (1 + δ / 10) * θ ^ n := mul_nonneg hfac hpos
  nlinarith

/-- The contraction constant of the low (and, reversed, high) windows: `λ₋ < 1` (MA2 §2.12). -/
theorem p51_lambda_minus_lt_one {δ θ C₀ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) (hθ1 : θ < 1)
    {N : ℕ} (hN : θ ^ N * C₀ < δ / 16) :
    θ ^ N * C₀ + winMMinus δ * (1 + δ / 10) < 1 := by
  have h := win_mminus_fixed_lt hδ hδ1 hθ1
  unfold winT at h
  linarith

/-- The constant of the middle windows: `λ₊ < 1 + δ` (MA2 §2.12). -/
theorem p51_lambda_plus_lt {δ θ C₀ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) (hθ1 : θ < 1)
    {N : ℕ} (hN : θ ^ N * C₀ < δ / 16) :
    θ ^ N * C₀ + winMPlus δ * (1 + δ / 10) < 1 + δ := by
  have h := win_mplus_fixed_lt hδ hδ1 hθ1
  linarith

theorem p51_winMMinus_pos {δ : ℝ} (hδ1 : δ < 1) : 0 < winMMinus δ := by
  unfold winMMinus winT
  linarith

theorem p51_winMMinus_lt_winMPlus {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    winMMinus δ < winMPlus δ := by
  unfold winMMinus winMPlus winT
  have hpos : 0 < 1 - δ / 4 := by linarith
  have hlt : 1 - δ / 4 < 1 := by linarith
  have h1 : 1 < (1 - δ / 4)⁻¹ := one_lt_inv_iff₀.2 ⟨hpos, hlt⟩
  linarith

/-! ### The iteration lemma (MA2 D-B3) -/

/-- The chain condition along a list: consecutive pairs (starting from `a`) satisfy `rel`. -/
def p51Chain (rel : ℕ → ℕ → Prop) : ℕ → List ℕ → Prop
  | _, [] => True
  | a, b :: l => rel a b ∧ p51Chain rel b l

/-- A strictly increasing list whose elements exceed `a` and satisfy `Q` is a chain for any
relation implied by `a < b ∧ Q b`. -/
theorem p51_chain_of_pairwise (rel : ℕ → ℕ → Prop) (Q : ℕ → Prop)
    (hrel : ∀ a b, a < b → Q b → rel a b) :
    ∀ (l : List ℕ) (a : ℕ), l.Pairwise (· < ·) → (∀ x ∈ l, a < x ∧ Q x) → p51Chain rel a l := by
  intro l
  induction l with
  | nil => intro a _ _; trivial
  | cons b l ih =>
      intro a hl hall
      rw [List.pairwise_cons] at hl
      have hb := hall b List.mem_cons_self
      refine ⟨hrel a b hb.1 hb.2, ?_⟩
      exact ih b hl.2 (fun x hx => ⟨hl.1 x hx, (hall x (List.mem_cons_of_mem b hx)).2⟩)

/-- **Iteration lemma** (MA2 D-B3, deterministic): if each admissible step `a → b` improves
`Comp(C, v_a)` to `Comp(winStep C, v_b)` (for `C ≥ m`), then along a chain from `a` the constant
becomes `winIter C n` and the exponent may be lowered to `v_M`. -/
theorem p51_iterate {G G' : ContMetric d} {R ε θ η m : ℝ} {M : ℕ} (rel : ℕ → ℕ → Prop)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hθ : 0 ≤ θ) (hη : 0 ≤ η) (hm : 0 ≤ m)
    (hrel : ∀ a b, rel a b → a < b ∧ b ≤ M)
    (step : ∀ a b, rel a b → ∀ C, m ≤ C → Comp G G' R ε (winV a) C →
      Comp G G' R ε (winV b) (winStep θ η m C)) :
    ∀ (l : List ℕ) (a : ℕ) (C : ℝ), a ≤ M → p51Chain rel a l → m ≤ C →
      Comp G G' R ε (winV a) C → Comp G G' R ε (winV M) (winIter θ η m C l.length) := by
  intro l
  induction l with
  | nil =>
      intro a C haM _ _ hC
      exact p51_comp_mono_q hε0 hε1 (p51_winV_anti haM) hC
  | cons b l ih =>
      intro a C _ hchain hmC hC
      obtain ⟨hab, hl⟩ := hchain
      obtain ⟨-, hbM⟩ := hrel a b hab
      have hstep := step a b hab C hmC hC
      have hres := ih b (winStep θ η m C) hbM hl (winStep_ge_of_ge hθ hη hm hmC) hstep
      rw [p51_winIter_step] at hres
      simpa only [List.length_cons] using hres

/-- The conclusion of Proposition 4.1 for the window pair `(a, b)` (`u = u_b`, `q₀ = v_a`) at a
fixed `ε`: the form in which `Core.Prop41Stmt` is consumed. -/
def p51P41At (d : ℕ) (A η ε : ℝ) (a b : ℕ) : Prop :=
  ∀ R : ℝ, 2 ≤ R → ∀ (G G' : ContMetric d) (Rε : Finset ℝ) (c : ℝ → ℝ) (m C : ℝ),
    (∀ r ∈ Rε, r ∈ window ε (winU b) ∧ 0 < c r ∧ c r ≤ m) →
    (∀ z ∈ mesh d ε (winU b) R, ∃ r ∈ Rε, GoodAnnulus G G' A η (c r) (8 * ε ^ (winV a)) z r) →
    Comp G G' R ε (winV a) C →
    Comp G G' R ε (winU b / 2) (A / (A + 1) * max C m + (1 - A / (A + 1) + 3 * η) * m)

/-- Proposition 4.1 at the window pair `(a, b)`, `a < b`, holds for all small `ε`. -/
theorem p51_P41At_eventually (hd : 1 ≤ d) (h41 : Prop41Stmt d) {A η : ℝ} (hA : 1 ≤ A)
    (hη : 0 < η) {a b : ℕ} (hab : a < b) : ∀ᶠ ε in 𝓝[>] (0 : ℝ), p51P41At d A η ε a b := by
  obtain ⟨ε₀, hε₀, h⟩ := h41 hd (winU b) (winV a) η A (winU_pos b) (winV_gt_winU_of_lt hab)
    (p51_winV_lt_one a) hη hA
  filter_upwards [Ioo_mem_nhdsGT hε₀] with ε hε
  exact h ε hε

/-- Proposition 4.1 at all window pairs `a < b ≤ M` simultaneously, for all small `ε`. -/
theorem p51_P41_eventually (hd : 1 ≤ d) (h41 : Prop41Stmt d) {A η : ℝ} (hA : 1 ≤ A)
    (hη : 0 < η) (M : ℕ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ a b : ℕ, a < b → b ≤ M → p51P41At d A η ε a b := by
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ b ∈ Finset.range (M + 1), ∀ a ∈ Finset.range b,
      p51P41At d A η ε a b := by
    rw [Filter.eventually_all_finset]
    intro b _
    rw [Filter.eventually_all_finset]
    intro a ha
    exact p51_P41At_eventually hd h41 hA hη (Finset.mem_range.1 ha)
  filter_upwards [hev] with ε hε a b hab hbM
  exact hε b (Finset.mem_range.2 (Nat.lt_succ_of_le hbM)) a (Finset.mem_range.2 hab)

/-- **Selection lemma** (MA2 D-B3 for a deterministic selection `S ⊆ [1, M]` of windows with radius
sets `Rs b ⊆ 𝒩_ε(u_b)`): the covering conditions of all pairs `a < b ∈ S` and `Comp(C₀, v₀)` give
`Comp(winIter C₀ |S|, v_M)`. -/
theorem p51_select {G G' : ContMetric d} {A η R ε m C₀ : ℝ} {M : ℕ}
    (hA : 1 ≤ A) (hη : 0 < η) (hR : 2 ≤ R) (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hm : 0 ≤ m)
    (hmC : m ≤ C₀) (hP41 : ∀ a b, a < b → b ≤ M → p51P41At d A η ε a b)
    (S : Finset ℕ) (hS : ∀ b ∈ S, 1 ≤ b ∧ b ≤ M) (Rs : ℕ → Finset ℝ) (c : ℝ → ℝ)
    (hRs : ∀ b ∈ S, ∀ r ∈ Rs b, r ∈ window ε (winU b) ∧ 0 < c r ∧ c r ≤ m)
    (hcov : ∀ b ∈ S, ∀ a < b, ∀ z ∈ mesh d ε (winU b) R, ∃ r ∈ Rs b,
      GoodAnnulus G G' A η (c r) (8 * ε ^ (winV a)) z r)
    (h0 : Comp G G' R ε (winV 0) C₀) :
    Comp G G' R ε (winV M) (winIter (A / (A + 1)) η m C₀ S.card) := by
  have hθ : 0 ≤ A / (A + 1) := div_nonneg (by linarith) (by linarith)
  let rel : ℕ → ℕ → Prop := fun a b => a < b ∧ b ≤ M ∧ b ∈ S
  have hstep : ∀ a b, rel a b → ∀ C, m ≤ C → Comp G G' R ε (winV a) C →
      Comp G G' R ε (winV b) (winStep (A / (A + 1)) η m C) := by
    intro a b hab C hC hcomp
    have h41 := hP41 a b hab.1 hab.2.1 R hR G G' (Rs b) c m C (hRs b hab.2.2)
      (hcov b hab.2.2 a hab.1) hcomp
    rw [max_eq_left hC] at h41
    exact h41
  have hsorted : (S.sort (· ≤ ·)).Pairwise (· < ·) :=
    ((Finset.pairwise_sort S (· ≤ ·)).and (Finset.sort_nodup S (· ≤ ·))).imp
      (fun h => lt_of_le_of_ne h.1 h.2)
  have hchain : p51Chain rel 0 (S.sort (· ≤ ·)) := by
    refine p51_chain_of_pairwise rel (fun x => x ≤ M ∧ x ∈ S)
      (fun a b hab hb => ⟨hab, hb.1, hb.2⟩) _ 0 hsorted ?_
    intro x hx
    have hxS := (Finset.mem_sort (· ≤ ·)).1 hx
    exact ⟨(hS x hxS).1, (hS x hxS).2, hxS⟩
  have hres := p51_iterate (M := M) rel hε0 hε1 hθ hη.le hm (fun a b h => ⟨h.1, h.2.1⟩) hstep
    (S.sort (· ≤ ·)) 0 C₀ (Nat.zero_le M) hchain hmC h0
  rwa [Finset.length_sort] at hres

/-! ### Windows as finsets; positivity -/

/-- The window `𝒩_ε(u_i)` as a finset: the radii `256^{-k}` for the integer indices
`⌈L⌉ ≤ k ≤ ⌊2L⌋`, `L = u_i log(1/ε) / (2 log 256)` (packet D6's `winIndexLower`). For `0 < ε < 1` its
coercion is exactly `Core.window ε u_i` (`p51_coe_W`). -/
def p51W (ε : ℝ) (i : ℕ) : Finset ℝ :=
  (Finset.Icc ⌈winIndexLower ε (winU i)⌉ ⌊2 * winIndexLower ε (winU i)⌋).image
    (fun k : ℤ => (256 : ℝ) ^ (-k))

theorem p51_coe_W {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (i : ℕ) :
    (↑(p51W ε i) : Set ℝ) = window ε (winU i) := by
  change _ = winRadiusWindow ε (winU i)
  unfold winRadiusWindow p51W
  rw [winRadiusIndices_eq_Icc hε0 hε1 (winU_pos i), Finset.coe_image, Finset.coe_Icc]

theorem p51_ncard_W {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (i : ℕ) :
    (window ε (winU i)).ncard = (p51W ε i).card := by
  rw [← p51_coe_W hε0 hε1 i, Set.ncard_coe_finset]

theorem p51_mem_W {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) {i : ℕ} {r : ℝ} (hr : r ∈ p51W ε i) :
    r ∈ window ε (winU i) := by
  rw [← p51_coe_W hε0 hε1 i]
  exact hr

/-- The radii of a window are positive. -/
theorem p51_pos_of_mem_window {ε u r : ℝ} (hr : r ∈ window ε u) : 0 < r := by
  obtain ⟨k, -, rfl⟩ := hr
  exact zpow_pos (by norm_num) _

/-- `c_ε(r) > 0` for `ε, r > 0` (the normalizers are positive). -/
theorem p51_cRatio_pos {κ : Rd d → ℝ} {ξ Q ε r : ℝ} (hpos : ∀ ε : ℝ, 0 < ε → 0 < aEps κ ξ ε)
    (hε : 0 < ε) (hr : 0 < r) : 0 < cRatio κ ξ Q ε r := by
  show 0 < r * aEps κ ξ (ε / r) / (r ^ (ξ * Q) * aEps κ ξ ε)
  exact div_pos (mul_pos hr (hpos _ (div_pos hε hr)))
    (mul_pos (Real.rpow_pos_of_pos hr _) (hpos _ hε))

/-! ### Filters -/

theorem p51_eventually_of_Ioo {Q : ℝ → Prop} (h : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε ∈ Ioo (0 : ℝ) ε₀, Q ε) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), Q ε := by
  obtain ⟨ε₀, hε₀, hQ⟩ := h
  filter_upwards [Ioo_mem_nhdsGT hε₀] with ε hε
  exact hQ ε hε

theorem p51_Ioo_of_eventually {Q : ℝ → Prop} (h : ∀ᶠ ε in 𝓝[>] (0 : ℝ), Q ε) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε ∈ Ioo (0 : ℝ) ε₀, Q ε := by
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 h
  exact ⟨u, hu, fun ε hε => hsub hε⟩

end HigherDimLFPPAS.SharpComp
