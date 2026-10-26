import SupercriticalConformalCovariance.BiLip.Chain
import SupercriticalConformalCovariance.Cover.Local

/-!
# Lemma 2.1, steps 5–6, deterministic core

Paper l. 139–148, for ONE sample, in an abstract form that serves both directions of (3):
* the **source** is a family of admissible paths (`Adm`) in `U` with an additive length `len`, a crossing
  cost `acr z r` charged to every admissible crossing of `A_{r/2,r}(z)`, and a function `d₁` which admissible
  paths approximate from above (for `e ≤ C d`: `D_h`-curves, `D_h.len`, `D_h(across)` and `d = D_h(·,·;U)`);
* the **target** is a function `e₂` together with confined metrics `conf C` on compact `C ⊆ U`: extended
  pseudometrics on `C`, antitone in `C`, lower semicontinuous on `C × C`, and above `e₂` (for `e ≤ C d`: the
  pulled-back target metric internal to `C`, which is Lemma 1.2's object);
* the **good events** `Good z r` give a target loop in `A_{r,2r}(z)` whose `conf (B̄_{2r}(z))`-diameter is
  less than `K · acr z r` (the event of (4));
* the **good covers** (`coverEvent`, along a deterministic sequence `ε_j → 0`): for every compact
  `L ⊆ U` and all large `j`, every point of `L` lies in `B_{r/2}(z)` for a good `(z, r)` of the finite family
  `coverFamily L ε_j`.

Results:
* `path_le_of_goodCovers` (l. 139–144): `e₂(P a, P b) ≤ K · len(P)` for every admissible path of finite length.
  The endpoints of the chain are only `O(ε_j)` from those of `P`; the chain stays in the fixed compact
  `K' = cl B_{δ'}(P[a,b]) ⋐ U`, and the lower semicontinuity of `conf K'` gives the exact endpoints (Lemma 1.2).
* `le_of_path_le` (l. 147, "Infimizing gives `e ≤ C0 d`").
* `le_of_goodCovers`: the two together.
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter Topology
open scoped ENNReal

namespace SupercriticalConformalCovariance.BiLip

open SupercriticalConformalCovariance.Cover (coverFamily coverFamily_radius coverFamily_centre coverFamily_finite)

/-- A finite set of pairs with positive values has a positive lower bound. -/
theorem exists_pos_le_of_finite {G : Set (ℂ × ℝ)} (hG : G.Finite) (f : ℂ × ℝ → ℝ)
    (hf : ∀ g ∈ G, 0 < f g) : ∃ μ₀ : ℝ, 0 < μ₀ ∧ ∀ g ∈ G, μ₀ ≤ f g := by
  rcases G.eq_empty_or_nonempty with hE | hne
  · exact ⟨1, one_pos, by simp [hE]⟩
  · obtain ⟨g₀, hg₀, hmin⟩ := Set.exists_min_image G f hG hne
    exact ⟨f g₀, hf g₀ hg₀, hmin⟩

/-- `B̄_s(z) ⊆ cl B_{ε+s}(L)` for `z ∈ cl B_ε(L)`. -/
theorem closedBall_subset_cthickening_of_mem {L : Set ℂ} {z : ℂ} {ε s : ℝ} (hε : 0 ≤ ε)
    (hs : 0 ≤ s) (hz : z ∈ cthickening ε L) : closedBall z s ⊆ cthickening (s + ε) L :=
  (closedBall_subset_cthickening hz s).trans (cthickening_cthickening_subset hs hε L)

/-- The good-pair property, required only at small scales around each compact set: for every compact
`L ⊆ U` there is `r₁ > 0` such that a good pair `(z, r)` with `z ∈ cl B_{r₁}(L)`, `0 < r ≤ r₁` has
`B̄_{2r}(z) ⊆ U`, a good loop of `conf (B̄_{2r}(z))`-diameter `< K · acr z r`, and the crossing charge
`acr z r ≤ len P τ t` for every admissible crossing of `A_{r/2,r}(z)`. -/
def GoodLocal (U : Set ℂ) (Adm : (ℝ → ℂ) → ℝ → ℝ → Prop) (len : (ℝ → ℂ) → ℝ → ℝ → ℝ≥0∞)
    (acr : ℂ → ℝ → ℝ≥0∞) (conf : Set ℂ → ℂ → ℂ → ℝ≥0∞) (Good : ℂ → ℝ → Prop) (K : ℝ≥0∞) :
    Prop :=
  ∀ L : Set ℂ, IsCompact L → L ⊆ U → ∃ r₁ : ℝ, 0 < r₁ ∧ ∀ z ∈ cthickening r₁ L,
    ∀ r ∈ Ioc (0 : ℝ) r₁, Good z r →
      closedBall z (2 * r) ⊆ U ∧
      IsGoodLoop (conf (closedBall z (2 * r))) (closedBall z (2 * r)) z r (K * acr z r) ∧
      ∀ P a b, Adm P a b → ∀ τ t : ℝ, a ≤ τ → τ ≤ t → t ≤ b →
        dist (P τ) z ≤ r / 2 → r ≤ dist (P t) z → acr z r ≤ len P τ t

/-- **Lemma 2.1, l. 139–144, deterministic:** good covers give `e₂(P a, P b) ≤ K · len(P)` for every
admissible path `P` in `U` of finite length. -/
theorem path_le_of_goodCovers {U : Set ℂ} (hU : IsOpen U)
    (Adm : (ℝ → ℂ) → ℝ → ℝ → Prop) (len : (ℝ → ℂ) → ℝ → ℝ → ℝ≥0∞)
    (hAdm_le : ∀ P a b, Adm P a b → a ≤ b)
    (hAdm_cont : ∀ P a b, Adm P a b → ContinuousOn P (Icc a b))
    (hadd : ∀ P a b, Adm P a b → ∀ s t u, a ≤ s → s ≤ t → t ≤ u → u ≤ b →
      len P s u = len P s t + len P t u)
    (acr : ℂ → ℝ → ℝ≥0∞)
    (e₂ : ℂ → ℂ → ℝ≥0∞) (conf : Set ℂ → ℂ → ℂ → ℝ≥0∞)
    (hconf_pm : ∀ C, IsCompact C → C ⊆ U → IsPMetricOn (conf C) C)
    (hconf_mono : ∀ C C', IsCompact C → IsCompact C' → C ⊆ C' → C' ⊆ U →
      ∀ x ∈ C, ∀ y ∈ C, conf C' x y ≤ conf C x y)
    (hconf_lsc : ∀ C, IsCompact C → C ⊆ U → ∀ x ∈ C, ∀ y ∈ C, ∀ xs ys : ℕ → ℂ,
      (∀ j, xs j ∈ C) → (∀ j, ys j ∈ C) → Tendsto xs atTop (𝓝 x) → Tendsto ys atTop (𝓝 y) →
      ∀ M : ℝ≥0∞, (∀ j, conf C (xs j) (ys j) ≤ M) → conf C x y ≤ M)
    (hconf_ge : ∀ C, IsCompact C → C ⊆ U → ∀ x ∈ C, ∀ y ∈ C, e₂ x y ≤ conf C x y)
    (Good : ℂ → ℝ → Prop) (K : ℝ≥0∞)
    (hGood : GoodLocal U Adm len acr conf Good K)
    (ε : ℕ → ℝ) (hεpos : ∀ j, 0 < ε j) (hεlim : Tendsto ε atTop (𝓝 0))
    (hcover : ∀ L : Set ℂ, IsCompact L → L ⊆ U → ∀ᶠ j in atTop, ∀ x ∈ L,
      ∃ zr ∈ coverFamily L (ε j), x ∈ ball zr.1 (zr.2 / 2) ∧ Good zr.1 zr.2)
    (P : ℝ → ℂ) (a b : ℝ) (hP : Adm P a b) (hPU : ∀ t ∈ Icc a b, P t ∈ U)
    (hlen : len P a b < ∞) :
    e₂ (P a) (P b) ≤ K * len P a b := by
  have hab := hAdm_le P a b hP
  have hPc := hAdm_cont P a b hP
  set L : Set ℂ := P '' Icc a b with hLdef
  have hLc : IsCompact L := isCompact_Icc.image_of_continuousOn hPc
  have hLU : L ⊆ U := by rintro _ ⟨t, ht, rfl⟩; exact hPU t ht
  obtain ⟨δ', hδ', hδ'U⟩ := hLc.exists_cthickening_subset_open hU hLU
  set K' : Set ℂ := cthickening δ' L with hK'def
  have hK'c : IsCompact K' := hLc.cthickening
  have hLK' : L ⊆ K' := self_subset_cthickening L
  have hPa : P a ∈ L := ⟨a, ⟨le_rfl, hab⟩, rfl⟩
  have hPb : P b ∈ L := ⟨b, ⟨hab, le_rfl⟩, rfl⟩
  obtain ⟨r₁, hr₁, hGL⟩ := hGood L hLc hLU
  -- for all large `j`: the cover, and `ε_j ≤ min (δ'/2) r₁`
  have hsmall : ∀ᶠ j in atTop, ε j ≤ min (δ' / 2) r₁ :=
    (hεlim.eventually (gt_mem_nhds (lt_min (by linarith : (0 : ℝ) < δ' / 2) hr₁))).mono
      fun _ h => h.le
  obtain ⟨j₀, hj₀⟩ := ((hcover L hLc hLU).and hsmall).exists_forall_of_atTop
  -- the chain at every scale `j ≥ j₀`
  have hstep : ∀ j, j₀ ≤ j → ∃ x₁ ∈ K', x₁ ∈ closedBall (P a) (4 * (ε j / 8)) ∧
      ∃ x₂ ∈ K', x₂ ∈ closedBall (P b) (4 * (ε j / 8)) ∧ conf K' x₁ x₂ ≤ K * len P a b := by
    intro j hj
    obtain ⟨hcov, hεj'⟩ := hj₀ j hj
    have hεj : ε j ≤ δ' / 2 := hεj'.trans (min_le_left _ _)
    have hεr : ε j ≤ r₁ := hεj'.trans (min_le_right _ _)
    have hε0 := hεpos j
    -- every good pair of the family has its ball `B̄_{2r}(z)` inside `K'`
    have hball : ∀ zr ∈ coverFamily L (ε j), closedBall zr.1 (2 * zr.2) ⊆ K' := by
      intro zr hzr
      have hr := coverFamily_radius hε0.le hzr
      refine (closedBall_subset_cthickening_of_mem hε0.le (by nlinarith [sq_nonneg (ε j)])
        (coverFamily_centre hzr)).trans (cthickening_mono ?_ L)
      linarith [hr.2]
    have hrpos : ∀ zr ∈ coverFamily L (ε j), 0 < zr.2 := fun zr hzr =>
      lt_of_lt_of_le (by positivity) (coverFamily_radius hε0.le hzr).1
    -- the positive lower bound `μ₀` of the crossing costs of the good pairs
    set G : Set (ℂ × ℝ) := {zr ∈ coverFamily L (ε j) | Good zr.1 zr.2} with hGdef
    have hGfin : G.Finite := (coverFamily_finite hLc.isBounded hε0).subset (sep_subset _ _)
    have hGG : ∀ zr ∈ G, _ := fun zr hzr => hGL zr.1
      (cthickening_mono hεr L (coverFamily_centre hzr.1)) zr.2
      ⟨hrpos zr hzr.1, ((coverFamily_radius hε0.le hzr.1).2).trans (by linarith)⟩ hzr.2
    have hloopG : ∀ zr ∈ G, IsGoodLoop (conf (closedBall zr.1 (2 * zr.2)))
        (closedBall zr.1 (2 * zr.2)) zr.1 zr.2 (K * acr zr.1 zr.2) := fun zr hzr =>
      (hGG zr hzr).2.1
    have hacr_ne : ∀ zr ∈ G, acr zr.1 zr.2 ≠ 0 := by
      intro zr hzr h0
      obtain ⟨_, _, _, _, _, _, _, L₀, hL₀, _⟩ := hloopG zr hzr
      rw [h0, mul_zero] at hL₀
      exact absurd hL₀ (not_lt.2 zero_le)
    obtain ⟨μ₀, hμ₀, hμ₀le⟩ := exists_pos_le_of_finite hGfin
      (fun zr => (min (acr zr.1 zr.2) 1).toReal) (fun zr hzr =>
        ENNReal.toReal_pos (by simp [hacr_ne zr hzr]) (min_lt_of_right_lt ENNReal.one_lt_top).ne)
    have hD₂ : IsPMetricOn (conf K') K' := hconf_pm K' hK'c (hδ'U)
    have hgood : ∀ t ∈ Icc a b, ChainGoodAt (len P) (conf K') K' K (ε j / 8) μ₀ P a b t := by
      intro t ht
      obtain ⟨zr, hzr, hxz, hG⟩ := hcov (P t) ⟨t, ht, rfl⟩
      have hzrG : zr ∈ G := ⟨hzr, hG⟩
      refine ⟨zr.1, zr.2, hrpos zr hzr, (coverFamily_radius hε0.le hzr).2, hxz,
        acr zr.1 zr.2, ?_, ?_, ?_⟩
      · calc ENNReal.ofReal μ₀ ≤ ENNReal.ofReal (min (acr zr.1 zr.2) 1).toReal :=
              ENNReal.ofReal_le_ofReal (hμ₀le zr hzrG)
          _ = min (acr zr.1 zr.2) 1 :=
              ENNReal.ofReal_toReal (min_lt_of_right_lt ENNReal.one_lt_top).ne
          _ ≤ acr zr.1 zr.2 := min_le_left _ _
      · intro τ t' haτ hτt' ht'b h1 h2
        exact (hGG zr hzrG).2.2 P a b hP τ t' haτ hτt' ht'b h1 h2
      · refine (hloopG zr hzrG).mono ?_ (hball zr hzr) le_rfl
        intro x hx y hy
        exact hconf_mono _ K' (isCompact_closedBall _ _) hK'c (hball zr hzr) hδ'U x hx y hy
    exact chain (len P) (conf K') K' hD₂ K (ε j / 8) μ₀ hμ₀ P hab hPc (hadd P a b hP) hlen hgood
  -- the limit `j → ∞`
  choose! x₁ hx₁K hx₁ x₂ hx₂K hx₂ hle using hstep
  have hρ : Tendsto (fun n : ℕ => 4 * (ε (j₀ + n) / 8)) atTop (𝓝 0) := by
    have := (hεlim.comp (tendsto_add_atTop_nat j₀)).div_const 8 |>.const_mul 4
    simpa [add_comm] using this
  have hconv : ∀ (z : ℂ) (x : ℕ → ℂ), (∀ n, x n ∈ closedBall z (4 * (ε (j₀ + n) / 8))) →
      Tendsto x atTop (𝓝 z) := by
    intro z x hx
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun _ => dist_nonneg) (fun n => mem_closedBall.1 (hx n)) hρ
  have hj : ∀ n : ℕ, j₀ ≤ j₀ + n := fun n => Nat.le_add_right j₀ n
  have hlim : conf K' (P a) (P b) ≤ K * len P a b :=
    hconf_lsc K' hK'c hδ'U (P a) (hLK' hPa) (P b) (hLK' hPb) (fun n => x₁ (j₀ + n))
      (fun n => x₂ (j₀ + n)) (fun n => hx₁K _ (hj n)) (fun n => hx₂K _ (hj n))
      (hconv _ _ fun n => hx₁ _ (hj n)) (hconv _ _ fun n => hx₂ _ (hj n)) _
      (fun n => hle _ (hj n))
  exact (hconf_ge K' hK'c hδ'U (P a) (hLK' hPa) (P b) (hLK' hPb)).trans hlim

/-- **"Infimizing gives `e ≤ C0 d`"** (l. 147): a path comparison and the approximation of `d₁` by
admissible paths give `e₂ ≤ K d₁` on `U`. -/
theorem le_of_path_le {U : Set ℂ} (Adm : (ℝ → ℂ) → ℝ → ℝ → Prop)
    (len : (ℝ → ℂ) → ℝ → ℝ → ℝ≥0∞) (d₁ e₂ : ℂ → ℂ → ℝ≥0∞) {K : ℝ≥0∞} (hK0 : K ≠ 0) (hKtop : K ≠ ∞)
    (hpath : ∀ P a b, Adm P a b → (∀ t ∈ Icc a b, P t ∈ U) → len P a b < ∞ →
      e₂ (P a) (P b) ≤ K * len P a b)
    (happrox : ∀ u ∈ U, ∀ v ∈ U, d₁ u v < ∞ → ∀ δ : ℝ≥0∞, 0 < δ →
      ∃ P a b, Adm P a b ∧ (∀ t ∈ Icc a b, P t ∈ U) ∧ P a = u ∧ P b = v ∧
        len P a b ≤ d₁ u v + δ) :
    ∀ u ∈ U, ∀ v ∈ U, e₂ u v ≤ K * d₁ u v := by
  intro u hu v hv
  rcases eq_top_or_lt_top (d₁ u v) with htop | hfin
  · rw [htop, ENNReal.mul_top hK0]; exact le_top
  have hbound : ∀ n : ℕ, e₂ u v ≤ K * (d₁ u v + ((n : ℝ≥0∞) + 1)⁻¹) := by
    intro n
    obtain ⟨P, a, b, hP, hPU, rfl, rfl, hlenle⟩ :=
      happrox u hu v hv hfin ((n : ℝ≥0∞) + 1)⁻¹ (ENNReal.inv_pos.2 (by simp))
    have hlt : len P a b < ∞ := lt_of_le_of_lt hlenle
      (ENNReal.add_lt_top.2 ⟨hfin, ENNReal.inv_lt_top.2 (by simp)⟩)
    exact (hpath P a b hP hPU hlt).trans (mul_le_mul_right hlenle K)
  have htend : Tendsto (fun n : ℕ => K * (d₁ u v + ((n : ℝ≥0∞) + 1)⁻¹)) atTop
      (𝓝 (K * d₁ u v)) := by
    have h1 : Tendsto (fun n : ℕ => ((n : ℝ≥0∞) + 1)⁻¹) atTop (𝓝 0) := by
      have := ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
      simpa [Function.comp_def] using this
    have h2 : Tendsto (fun n : ℕ => d₁ u v + ((n : ℝ≥0∞) + 1)⁻¹) atTop (𝓝 (d₁ u v)) := by
      simpa using tendsto_const_nhds.add h1
    exact ENNReal.Tendsto.const_mul h2 (Or.inr hKtop)
  exact ge_of_tendsto' htend hbound

/-- **Lemma 2.1, steps 5–6, deterministic core:** good covers along `ε_j → 0` give `e₂ ≤ K d₁` on `U`. -/
theorem le_of_goodCovers {U : Set ℂ} (hU : IsOpen U)
    (Adm : (ℝ → ℂ) → ℝ → ℝ → Prop) (len : (ℝ → ℂ) → ℝ → ℝ → ℝ≥0∞)
    (hAdm_le : ∀ P a b, Adm P a b → a ≤ b)
    (hAdm_cont : ∀ P a b, Adm P a b → ContinuousOn P (Icc a b))
    (hadd : ∀ P a b, Adm P a b → ∀ s t u, a ≤ s → s ≤ t → t ≤ u → u ≤ b →
      len P s u = len P s t + len P t u)
    (d₁ : ℂ → ℂ → ℝ≥0∞)
    (happrox : ∀ u ∈ U, ∀ v ∈ U, d₁ u v < ∞ → ∀ δ : ℝ≥0∞, 0 < δ →
      ∃ P a b, Adm P a b ∧ (∀ t ∈ Icc a b, P t ∈ U) ∧ P a = u ∧ P b = v ∧
        len P a b ≤ d₁ u v + δ)
    (acr : ℂ → ℝ → ℝ≥0∞)
    (e₂ : ℂ → ℂ → ℝ≥0∞) (conf : Set ℂ → ℂ → ℂ → ℝ≥0∞)
    (hconf_pm : ∀ C, IsCompact C → C ⊆ U → IsPMetricOn (conf C) C)
    (hconf_mono : ∀ C C', IsCompact C → IsCompact C' → C ⊆ C' → C' ⊆ U →
      ∀ x ∈ C, ∀ y ∈ C, conf C' x y ≤ conf C x y)
    (hconf_lsc : ∀ C, IsCompact C → C ⊆ U → ∀ x ∈ C, ∀ y ∈ C, ∀ xs ys : ℕ → ℂ,
      (∀ j, xs j ∈ C) → (∀ j, ys j ∈ C) → Tendsto xs atTop (𝓝 x) → Tendsto ys atTop (𝓝 y) →
      ∀ M : ℝ≥0∞, (∀ j, conf C (xs j) (ys j) ≤ M) → conf C x y ≤ M)
    (hconf_ge : ∀ C, IsCompact C → C ⊆ U → ∀ x ∈ C, ∀ y ∈ C, e₂ x y ≤ conf C x y)
    (Good : ℂ → ℝ → Prop) {K : ℝ≥0∞} (hK0 : K ≠ 0) (hKtop : K ≠ ∞)
    (hGood : GoodLocal U Adm len acr conf Good K)
    (ε : ℕ → ℝ) (hεpos : ∀ j, 0 < ε j) (hεlim : Tendsto ε atTop (𝓝 0))
    (hcover : ∀ L : Set ℂ, IsCompact L → L ⊆ U → ∀ᶠ j in atTop, ∀ x ∈ L,
      ∃ zr ∈ coverFamily L (ε j), x ∈ ball zr.1 (zr.2 / 2) ∧ Good zr.1 zr.2) :
    ∀ u ∈ U, ∀ v ∈ U, e₂ u v ≤ K * d₁ u v :=
  le_of_path_le Adm len d₁ e₂ hK0 hKtop
    (fun P a b hP hPU hlen => path_le_of_goodCovers hU Adm len hAdm_le hAdm_cont hadd acr
      e₂ conf hconf_pm hconf_mono hconf_lsc hconf_ge Good K hGood ε hεpos hεlim hcover P a b hP hPU
      hlen) happrox

end SupercriticalConformalCovariance.BiLip
