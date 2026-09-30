import QuantumZipper.Proofs.Complex.JSLayerShadowSum

/-!
# EXT-JS node C1, part 2b: the vertical chain along descendants

Blueprint `blueprint/EXT_JS_BLUEPRINT.md`, §2 ("(C1: layer decay LA ⇒ SH.)") and §3 node C1.

Source: P. W. Jones and S. K. Smirnov, *Removability theorems for Sobolev functions and
quasiconformal maps*, Ark. Mat. 38 (2000) 263–279, §2–3 and the proof of Proposition 1: a
Carleson box (here the tent `T_{m,j}`) is joined to its dyadic descendants by a vertical chain
of Whitney cubes (here the top boxes `Q_{m+k,j'}`), giving

`diam F(T_{m,j}) ≤ c Σ_{k ≥ 0} max_{j' descendant at level k} diam F(Q_{m+k,j'})`.

* `topDiam R F m j k` — that maximum (`Finset.sup` over `descIdx j k`);
* `edist_image_le_ediam_topBox`, `le_topDiam` — two points of a box bound by its image diameter;
* `topDiam_sq_le_sum` — `(sup)² ≤ Σ` of the squares;
* `edist_le_tsum_topDiam` — the chain bound for one point of the tent;
* `ediam_image_tent_le` — `diam F(T_{m,j}) ≤ 8 Σ_k topDiam R F m j k` for `j < 2^m`.

**Note on the hypothesis `j < 2 ^ m`.** The literal statement of `handoff/JS-C1.md` omits it,
and without it the statement is *false*: `F` is only assumed continuous on the chart box, so a
single modification of `F` at a boundary point `im = 0` outside the box (inside a tent with
`j ≥ 2^m`) makes `ediam (F '' tent R m j)` arbitrarily large while every `topDiam R F m j k`
stays the same. For `j < 2 ^ m` the tent lies in the closed chart box, which is exactly the case
the shadow sum uses.
-/

noncomputable section

set_option maxHeartbeats 800000

open Set Metric MeasureTheory Complex
open scoped ENNReal

namespace QuantumZipper
namespace JS

/-- The largest image diameter of a top box of a level-`k` descendant of `(m,j)`. -/
def topDiam (R : ℝ) (F : ℂ → ℂ) (m j k : ℕ) : ℝ≥0∞ :=
  (descIdx j k).sup fun j' => ediam (F '' topBox R (m + k) j')

lemma le_topDiam {R : ℝ} {F : ℂ → ℂ} {m j k j' : ℕ} (h : j' ∈ descIdx j k) :
    ediam (F '' topBox R (m + k) j') ≤ topDiam R F m j k :=
  Finset.le_sup (f := fun j' => ediam (F '' topBox R (m + k) j')) h

/-- Membership in `descIdx` from the division form of the ancestor relation. -/
lemma mem_descIdx_of_div {j k j' : ℕ} (h : j' / 2 ^ k = j) : j' ∈ descIdx j k := by
  rw [mem_descIdx_iff]
  refine ⟨j' % 2 ^ k, Nat.mod_lt _ (pow_pos (by norm_num : (0 : ℕ) < 2) k), ?_⟩
  rw [mul_comm j (2 ^ k), ← h]
  exact Nat.div_add_mod j' (2 ^ k)

/-- Two points of a top box are at distance at most the diameter of its image. -/
lemma edist_image_le_ediam_topBox {R : ℝ} {F : ℂ → ℂ} {m j : ℕ} {x y : ℂ}
    (hx : x ∈ topBox R m j) (hy : y ∈ topBox R m j) :
    edist (F x) (F y) ≤ ediam (F '' topBox R m j) :=
  edist_le_ediam_of_mem ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩

/-- A point of a top box, at any height between its top and its middle. -/
lemma mem_topBox_of_mem_dyI_of_mem_Icc {R : ℝ} {m j : ℕ} {x y : ℝ} (hx : x ∈ dyI R m j)
    (h1 : dyLen R m / 2 ≤ y) (h2 : y ≤ dyLen R m) :
    Complex.mk x y ∈ topBox R m j := by
  rw [topBox, mem_reProdIm]
  exact ⟨hx, h1, h2⟩ 

/-- The square of a finite supremum is at most the sum of the squares. -/
lemma sup_sq_le_sum (s : Finset ℕ) (f : ℕ → ℝ≥0∞) :
    (s.sup f) ^ 2 ≤ ∑ x ∈ s, f x ^ 2 := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  · obtain ⟨x, hx, hsup⟩ := Finset.exists_mem_eq_sup s hs f
    rw [hsup]
    simp only [pow_two]
    exact Finset.single_le_sum (s := s) (f := fun y => f y * f y) (fun _ _ => zero_le) hx

lemma topDiam_sq_le_sum (R : ℝ) (F : ℂ → ℂ) (m j k : ℕ) :
    topDiam R F m j k ^ 2 ≤ ∑ j' ∈ descIdx j k, ediam (F '' topBox R (m + k) j') ^ 2 :=
  sup_sq_le_sum _ _

/-! ### The vertical chain -/

/-- A point of a tent of positive height is at distance at most `Σ_k topDiam` from the point of
the top box `Q_{m,j}` above it: chain along the dyadic descendants. -/
lemma edist_le_tsum_topDiam {K : Set ℂ} {R : ℝ} {F : ℂ → ℂ} (hF : IsChart K R F) {m j : ℕ}
    {p : ℂ} (hp : p ∈ tent R m j) (him : 0 < p.im) :
    edist (F p) (F (Complex.mk p.re (dyLen R m))) ≤ ∑' k, topDiam R F m j k := by
  have hR := hF.pos
  obtain ⟨n, j', hj', hpbox⟩ := exists_mem_topBox_desc hR hp him
  have hpr : p.re ∈ dyI R (m + n) j' := (mem_reProdIm.1 hpbox).1
  -- the index of the ancestor at level `i` of the descendant `j'`
  have hjj : ∀ i ≤ n, (j' / 2 ^ (n - i)) / 2 ^ i = j := by
    intro i hi
    rw [Nat.div_div_eq_div_mul, ← pow_add, Nat.sub_add_cancel hi, hj']
  -- ancestors of `j'` and the dyadic intervals they carry
  have hsubi : ∀ i ≤ n, dyI R (m + n) j' ⊆ dyI R (m + i) (j' / 2 ^ (n - i)) := by
    intro i hi
    have := dyI_subset_of_div (R := R) (m := m + i) (n := n - i)
      (j := j' / 2 ^ (n - i)) (j' := j') hR.le rfl
    rwa [show m + i + (n - i) = m + n by omega] at this
  set Q : ℕ → ℂ := fun i => Complex.mk p.re (dyLen R (m + i)) with hQ
  have hmem : ∀ i ≤ n, Q i ∈ topBox R (m + i) (j' / 2 ^ (n - i)) := by
    intro i hi
    have h1 : dyLen R (m + i) / 2 ≤ dyLen R (m + i) :=
      div_le_self (dyLen_nonneg hR.le _) (by norm_num)
    exact mem_topBox_of_mem_dyI_of_mem_Icc (hsubi i hi hpr) h1 le_rfl
  -- one step of the chain
  have hstep : ∀ i < n, edist (F (Q (i + 1))) (F (Q i)) ≤ topDiam R F m j i := by
    intro i hi
    have hi' : i ≤ n := hi.le
    have hQ1 : Q (i + 1) ∈ topBox R (m + i) (j' / 2 ^ (n - i)) := by
      have h2 : dyLen R (m + i) / 2 ≤ dyLen R (m + i) :=
        div_le_self (dyLen_nonneg hR.le _) (by norm_num)
      have h2' : dyLen R (m + (i + 1)) = dyLen R (m + i) / 2 := by
        rw [show m + (i + 1) = m + i + 1 by omega, dyLen_succ]
      have h := mem_topBox_of_mem_dyI_of_mem_Icc (R := R) (m := m + i)
        (j := j' / 2 ^ (n - i)) (hsubi i hi' hpr) (le_refl (dyLen R (m + i) / 2)) h2
      simpa [hQ, h2'] using h
    calc edist (F (Q (i + 1))) (F (Q i))
        ≤ ediam (F '' topBox R (m + i) (j' / 2 ^ (n - i))) :=
          edist_image_le_ediam_topBox hQ1 (hmem i hi')
      _ ≤ topDiam R F m j i := le_topDiam (mem_descIdx_of_div (hjj i hi'))
  -- the chain from level `i` back to level `0`
  have hchain : ∀ i, i ≤ n → edist (F (Q i)) (F (Q 0)) ≤
      ∑ k ∈ Finset.range i, topDiam R F m j k := by
    intro i
    induction i with
    | zero => intro _; simp
    | succ i ih =>
      intro hi
      have hi' : i ≤ n := by omega
      calc edist (F (Q (i + 1))) (F (Q 0))
          ≤ edist (F (Q (i + 1))) (F (Q i)) + edist (F (Q i)) (F (Q 0)) :=
            edist_triangle _ _ _
        _ ≤ topDiam R F m j i + ∑ k ∈ Finset.range i, topDiam R F m j k :=
            add_le_add (hstep i (by omega)) (ih hi')
        _ = ∑ k ∈ Finset.range (i + 1), topDiam R F m j k := by
            rw [Finset.sum_range_succ, add_comm]
  -- the link from the point of the tent to the top of the chain
  have htop : edist (F p) (F (Q n)) ≤ topDiam R F m j n := by
    have hQn : Q n ∈ topBox R (m + n) j' := by
      simpa [hQ, Nat.add_sub_cancel] using hmem n le_rfl
    exact (edist_image_le_ediam_topBox hpbox hQn).trans (le_topDiam (mem_descIdx_of_div hj'))
  calc edist (F p) (F (Q 0))
      ≤ edist (F p) (F (Q n)) + edist (F (Q n)) (F (Q 0)) := edist_triangle _ _ _
    _ ≤ topDiam R F m j n + ∑ k ∈ Finset.range n, topDiam R F m j k :=
        add_le_add htop (hchain n le_rfl)
    _ = ∑ k ∈ Finset.range (n + 1), topDiam R F m j k := by
        rw [Finset.sum_range_succ, add_comm]
    _ ≤ ∑' k, topDiam R F m j k := ENNReal.sum_le_tsum _

/-- The tent of level `m` lies in the closed chart box when `j < 2^m`. -/
lemma tent_subset_chartBox {R : ℝ} (hR : 0 < R) {m j : ℕ} (hj : j < 2 ^ m) :
    tent R m j ⊆ Icc (-2 * R) (2 * R) ×ℂ Icc 0 (4 * R) := by
  refine (tent_subset hR.le hj).trans fun w hw => ?_
  rw [mem_reProdIm] at hw ⊢
  exact ⟨⟨by linarith [hw.1.1, hR.le], by linarith [hw.1.2, hR.le]⟩,
    ⟨hw.2.1, by linarith [hw.2.2, hR.le]⟩⟩

/-- The tent with positive height is dense in the closed tent. -/
lemma dense_pos_im_tent {R : ℝ} (hR : 0 < R) (m j : ℕ) :
    tent R m j = closure (tent R m j ∩ {w : ℂ | 0 < w.im}) := by
  refine Subset.antisymm (fun w hw => ?_)
    (closure_minimal (fun w hw => hw.1) (isCompact_tent R m j).isClosed)
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨hre, him0, himℓ⟩ := mem_reProdIm.1 hw
  have hℓ := dyLen_pos hR m
  set δ := min (ε / 2) ((dyLen R m - w.im) / 2) with hδ
  have hδ0 : 0 ≤ δ := le_min (by positivity) (by linarith)
  have hδℓ : δ ≤ (dyLen R m - w.im) / 2 := min_le_right _ _
  have hδε : δ ≤ ε / 2 := min_le_left _ _
  have hpos : 0 < w.im + δ := by
    rcases eq_or_lt_of_le hδ0 with h0 | h0
    · rcases eq_or_lt_of_le him0 with h1 | h1
      · exfalso
        have h2 : 0 < (dyLen R m - w.im) / 2 := by rw [← h1]; linarith
        have h3 : 0 < δ := lt_min (by linarith) h2
        rw [h0] at h3
        exact lt_irrefl _ h3
      · linarith
    · linarith
  refine ⟨Complex.mk w.re (w.im + δ), ⟨mem_reProdIm.2 ⟨hre, hpos.le, by linarith⟩, hpos⟩, ?_⟩
  rw [dist_eq_norm]
  have hre' : (w - Complex.mk w.re (w.im + δ)).re = 0 := by simp
  have him' : (w - Complex.mk w.re (w.im + δ)).im = -δ := by simp
  calc ‖w - Complex.mk w.re (w.im + δ)‖
      ≤ |(w - Complex.mk w.re (w.im + δ)).re| + |(w - Complex.mk w.re (w.im + δ)).im| :=
        norm_le_abs_re_add_abs_im _
    _ = δ := by rw [hre', him', abs_zero, zero_add, abs_neg, abs_of_nonneg hδ0]
    _ ≤ ε / 2 := hδε
    _ < ε := by linarith

/-- **The tent is no larger than the sum of its descendant top boxes** (Jones–Smirnov §2 chain
argument): `diam F(T_{m,j}) ≤ 8 Σ_k max_{j' ÷ 2^k = j} diam F(Q_{m+k,j'})` for `j < 2^m`, so that
the tent lies in the closed chart box where `F` is continuous. -/
theorem ediam_image_tent_le {K : Set ℂ} {R : ℝ} {F : ℂ → ℂ} (hF : IsChart K R F) {m j : ℕ}
    (hj : j < 2 ^ m) :
    ediam (F '' tent R m j) ≤ 8 * ∑' k, topDiam R F m j k := by
  have hR := hF.pos
  set S := ∑' k, topDiam R F m j k with hS
  -- points of the top box share the height `ℓ_m`
  have htopBoxOf : ∀ {p : ℂ}, p ∈ tent R m j → Complex.mk p.re (dyLen R m) ∈ topBox R m j := fun hp =>
    mem_topBox_of_mem_dyI_of_mem_Icc (mem_reProdIm.1 hp).1
      (div_le_self (dyLen_nonneg hR.le m) (by norm_num)) le_rfl
  have hjmem : j ∈ descIdx j 0 := by
    rw [mem_descIdx_iff]
    exact ⟨0, by norm_num, by simp⟩
  -- (1) pairs of points of positive height
  have hpair : ∀ p ∈ tent R m j, 0 < p.im → ∀ q ∈ tent R m j, 0 < q.im →
      edist (F p) (F q) ≤ 8 * S := by
    intro p hp him q hq hqim
    set p0 : ℂ := Complex.mk p.re (dyLen R m) with hp0def
    set q0 : ℂ := Complex.mk q.re (dyLen R m) with hq0def
    have hp0box : p0 ∈ topBox R m j := by rw [hp0def]; exact htopBoxOf hp
    have hq0box : q0 ∈ topBox R m j := by rw [hq0def]; exact htopBoxOf hq
    have hSp : edist (F p) (F p0) ≤ S := by rw [hp0def]; exact edist_le_tsum_topDiam hF hp him
    have hSq : edist (F q) (F q0) ≤ S := by rw [hq0def]; exact edist_le_tsum_topDiam hF hq hqim
    have hmid : edist (F p0) (F q0) ≤ S := by
      refine (edist_image_le_ediam_topBox hp0box hq0box).trans ?_
      refine ((le_topDiam (R := R) (F := F) (m := m) (j := j) (k := 0) hjmem).trans ?_)
      have h := ENNReal.sum_le_tsum ({0} : Finset ℕ) (f := fun k => topDiam R F m j k)
      simpa [hS] using h
    have h3 : edist (F q0) (F q) ≤ S := by rw [edist_comm]; exact hSq
    calc edist (F p) (F q)
        ≤ edist (F p) (F p0) + edist (F p0) (F q) := edist_triangle _ _ _
      _ ≤ edist (F p) (F p0) + (edist (F p0) (F q0) + edist (F q0) (F q)) :=
          add_le_add le_rfl (edist_triangle _ _ _)
      _ ≤ S + (S + S) := add_le_add hSp (add_le_add hmid h3)
      _ = 3 * S := by ring
      _ ≤ 8 * S := mul_le_mul_of_nonneg_right (by norm_num : (3 : ℝ≥0∞) ≤ 8) (by positivity)
  -- (2) the diameter of the image of the tent with positive height
  have him : ediam (F '' (tent R m j ∩ {w : ℂ | 0 < w.im})) ≤ 8 * S :=
    ediam_le fun x hx y hy => by
      obtain ⟨p, ⟨hp, hpi⟩, rfl⟩ := hx
      obtain ⟨q, ⟨hq, hqi⟩, rfl⟩ := hy
      exact hpair p hp hpi q hq hqi
  -- (3) extend to the closed tent by continuity on the chart box
  have hdense := dense_pos_im_tent hR m j
  have hcont : ContinuousOn F (tent R m j) := hF.cont.mono (tent_subset_chartBox hR hj)
  have hcont' : ContinuousOn F (closure (tent R m j ∩ {w : ℂ | 0 < w.im})) := by
    rw [← hdense]
    exact hcont
  have hsub := hcont'.image_closure
  rw [← hdense] at hsub
  calc ediam (F '' tent R m j)
      ≤ ediam (closure (F '' (tent R m j ∩ {w : ℂ | 0 < w.im}))) := ediam_mono hsub
    _ = ediam (F '' (tent R m j ∩ {w : ℂ | 0 < w.im})) := Metric.ediam_closure _
    _ ≤ 8 * S := him

end JS

end QuantumZipper
