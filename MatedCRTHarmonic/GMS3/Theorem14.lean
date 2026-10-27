import MatedCRTHarmonic.GMS3.Lemma34
import MatedCRTHarmonic.GMS3.Green
import MatedCRTHarmonic.Frozen.MatedCRTGraph

/-!
# GMS [18] Theorem 1.4 (recurrence), conditional on the inputs of Proposition 2.10 and Lemma 2.7

Source: GMS [18] Theorem 1.4 and its proof. The corresponding recurrence statement for the mated-CRT map is recorded as the frozen declaration `matedCRT_recurrent`.

[18] proves recurrence of the unit-mesh map `G¹` from: (i) for each `k`, the scaled cells of `G¹`
(scaling `R_{2^k}`, the joint scaling of the cone and the curve) are the cells of the mesh
`2^{-k}` map, for which the bound (1.8) holds outside an event of probability `O(2^{-αk})`; (ii) Borel–Cantelli.
This file proves the deterministic part: if, for infinitely many `k`, the cells `H k` of the graph satisfy
The event of [18] **Lemma 2.7** and the conclusions of [18] **Proposition 2.10** for the three pairs used by
Lemma 3.4 at mesh `ε k → 0`, then the graph is recurrent. The probabilistic inputs (Proposition 2.10,
Lemma 2.7, the joint scaling) are hypotheses here and are proved elsewhere in this library; `ae_recurrent_of_summable`
packages the Borel–Cantelli step.

* `Theorem14Inputs H ε ρ ρ₁ q β β' α A`: the four inputs at mesh `ε` (`s = ε^β`, `δ = ε^q`, `w = ε^{β'}`,
  `η = ε^α`);
* `tendsto_lemma34Bound`: the error term of `lemma34` tends to `0` when `3β < q`, `2β < β'`, `2β < α`;
* `theorem14_recurrent` (**[18] Theorem 1.4, recurrence, conditional form**);
* `ae_recurrent_of_summable` (the Borel–Cantelli step: summable failure probabilities give a.s. recurrence);
* `matedCRT_adj_succ`, `matedCRT_connected` (the mated-CRT map of Definition 1.12 is connected; proved
  here, the frozen anchor `matedCRT_graph_connected` is not imported) and `theorem14_matedCRT_recurrent`
  (the conditional statement for the frozen `MatedCRT.graph ε ω h`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Real Filter
open scoped ENNReal Topology

namespace MatedCRTHarmonic.GMS3

open LFMultigraph Harmonic

/-! ### Asymptotics of the Lemma 3.4 error term -/

section Asymptotics

variable {ε : ℕ → ℝ} (hε : ∀ k, 0 < ε k) (hε0 : Tendsto ε atTop (𝓝 0))
include hε hε0

omit hε in
theorem tendsto_rpow_of_tendsto_zero {γ : ℝ} (hγ : 0 < γ) :
    Tendsto (fun k => ε k ^ γ) atTop (𝓝 0) := by
  have h := ((Real.continuousAt_rpow_const 0 γ (Or.inr hγ.le)).tendsto).comp hε0
  rwa [Real.zero_rpow hγ.ne'] at h

theorem tendsto_rpow_div_pow {a b : ℝ} {n : ℕ} (h : n * b < a) :
    Tendsto (fun k => ε k ^ a / (ε k ^ b) ^ n) atTop (𝓝 0) := by
  have heq : (fun k => ε k ^ a / (ε k ^ b) ^ n) = fun k => ε k ^ (a - b * n) := by
    funext k
    rw [Real.rpow_sub (hε k), Real.rpow_mul_natCast (hε k).le]
  rw [heq]
  exact tendsto_rpow_of_tendsto_zero hε0 (by linarith)

theorem tendsto_log_div_rpow {ρ β : ℝ} (hρ : 0 < ρ) (hβ : 0 < β) :
    Tendsto (fun k => Real.log (ρ / ε k ^ β)) atTop atTop := by
  have hε' : Tendsto ε atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hε0, Eventually.of_forall hε⟩
  have hlog : Tendsto (fun k => Real.log (ε k)) atTop atBot := Real.tendsto_log_nhdsGT_zero.comp hε'
  have heq : (fun k => Real.log (ρ / ε k ^ β)) = fun k => Real.log ρ + (-β) * Real.log (ε k) := by
    funext k
    rw [Real.log_div hρ.ne' (Real.rpow_pos_of_pos (hε k) β).ne', Real.log_rpow (hε k)]
    ring
  rw [heq]
  exact tendsto_atTop_add_const_left _ _
    (Tendsto.const_mul_atBot_of_neg (neg_neg_of_pos hβ) hlog)

end Asymptotics

/-- An algebraic form of `lemma34Bound` (`X = log(ρ/s)⁻¹`). -/
theorem lemma34Bound_eq {s ρ δ w A η : ℝ} (hs : 0 < s) (hℓ : Real.log (ρ / s) ≠ 0) :
    lemma34Bound s ρ δ w A η =
      3 * A * (2 * π) * (Real.log (ρ / s))⁻¹ + 3 * η +
      6 * ((Real.log (ρ / s))⁻¹) ^ 2 * (δ / s ^ 3) * (A * (π * ρ ^ 2) + η) +
      12 * ((Real.log (ρ / s))⁻¹) ^ 2 *
        (A * (8 * π) * (w / s + 4 * (w / s) ^ 2 + ρ * (w / s ^ 2)) + η / s ^ 2) +
      384 * ((Real.log (ρ / s))⁻¹) ^ 2 * (δ / s ^ 2) ^ 2 *
        ((A * (π * ρ ^ 2) + η) + (A * (8 * π * w * (s + 2 * w) + 8 * π * w * (ρ + 2 * w)) + η)) := by
  unfold lemma34Bound
  field_simp
  ring

/-- **The Lemma 3.4 error term tends to `0`** along `s = ε^β`, `δ = ε^q`, `w = ε^{β'}`, `η = ε^α`, `ε → 0`,
when `3β < q`, `2β < β'` and `2β < α` (the leading term is `6πA/log(ρ/ε^β)`). -/
theorem tendsto_lemma34Bound {ε : ℕ → ℝ} (hε : ∀ k, 0 < ε k) (hε0 : Tendsto ε atTop (𝓝 0))
    {ρ β q β' α A : ℝ} (hρ : 0 < ρ) (hβ : 0 < β) (hq : 3 * β < q) (hβ' : 2 * β < β')
    (hα : 2 * β < α) :
    Tendsto (fun k => lemma34Bound (ε k ^ β) ρ (ε k ^ q) (ε k ^ β') A (ε k ^ α)) atTop (𝓝 0) := by
  have hL := tendsto_log_div_rpow hε hε0 hρ hβ
  have hX : Tendsto (fun k => (Real.log (ρ / ε k ^ β))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hL
  have heq : ∀ᶠ k in atTop, lemma34Bound (ε k ^ β) ρ (ε k ^ q) (ε k ^ β') A (ε k ^ α) =
      3 * A * (2 * π) * (Real.log (ρ / ε k ^ β))⁻¹ + 3 * ε k ^ α +
      6 * ((Real.log (ρ / ε k ^ β))⁻¹) ^ 2 * (ε k ^ q / (ε k ^ β) ^ 3) *
        (A * (π * ρ ^ 2) + ε k ^ α) +
      12 * ((Real.log (ρ / ε k ^ β))⁻¹) ^ 2 *
        (A * (8 * π) * (ε k ^ β' / (ε k ^ β) ^ 1 + 4 * (ε k ^ β' / (ε k ^ β) ^ 1) ^ 2 +
          ρ * (ε k ^ β' / (ε k ^ β) ^ 2)) + ε k ^ α / (ε k ^ β) ^ 2) +
      384 * ((Real.log (ρ / ε k ^ β))⁻¹) ^ 2 * (ε k ^ q / (ε k ^ β) ^ 2) ^ 2 *
        ((A * (π * ρ ^ 2) + ε k ^ α) + (A * (8 * π * ε k ^ β' * (ε k ^ β + 2 * ε k ^ β') +
          8 * π * ε k ^ β' * (ρ + 2 * ε k ^ β')) + ε k ^ α)) := by
    filter_upwards [hL.eventually_ne_atTop 0] with k hk
    rw [lemma34Bound_eq (Real.rpow_pos_of_pos (hε k) β) hk, pow_one]
  refine Tendsto.congr' (EventuallyEq.symm heq) ?_
  have hη := tendsto_rpow_of_tendsto_zero hε0 (show 0 < α by linarith)
  have hw := tendsto_rpow_of_tendsto_zero hε0 (show 0 < β' by linarith)
  have hs := tendsto_rpow_of_tendsto_zero hε0 hβ
  have r4 := tendsto_rpow_div_pow hε hε0 (a := q) (b := β) (n := 3) (by push_cast; linarith)
  have r1 := tendsto_rpow_div_pow hε hε0 (a := β') (b := β) (n := 1) (by push_cast; linarith)
  have r2 := tendsto_rpow_div_pow hε hε0 (a := β') (b := β) (n := 2) (by push_cast; linarith)
  have r3 := tendsto_rpow_div_pow hε hε0 (a := α) (b := β) (n := 2) (by push_cast; linarith)
  have r5 := tendsto_rpow_div_pow hε hε0 (a := q) (b := β) (n := 2) (by push_cast; linarith)
  have hlim := ((((hX.const_mul (3 * A * (2 * π))).add (hη.const_mul 3)).add
    (((hX.pow 2).const_mul 6).mul r4 |>.mul (hη.const_add (A * (π * ρ ^ 2))))).add
    ((hX.pow 2).const_mul 12 |>.mul
      ((((r1.add ((r1.pow 2).const_mul 4)).add (r2.const_mul ρ)).const_mul (A * (8 * π))).add r3))).add
    (((hX.pow 2).const_mul 384).mul (r5.pow 2) |>.mul
      ((hη.const_add (A * (π * ρ ^ 2))).add
        ((((((hw.const_mul (8 * π)).mul (hs.add (hw.const_mul 2))).add
          ((hw.const_mul (8 * π)).mul ((hw.const_mul 2).const_add ρ))).const_mul A)).add hη)))
  convert hlim using 2
  simp only [mul_add]
  ring

/-! ### Theorem 1.4, conditional form -/

variable {V E : Type*} {G : LFMultigraph V E} {o : V}

/-- **[18] (1.8), deterministic form** (Green's function on the diagonal): under the inputs of
`lemma34`, the Green function of the walk from the root `o` killed at the exit time `τ` from
`V(B_ρ(0))` satisfies `Gr_τ(o, o)/deg(o) ≥ 1/lemma34Bound s ρ δ w A η`; with `s = ε^β` the right side
is `≥ log(ρ ε^{-β})/(6πA + o(1))` (`tendsto_lemma34Bound`). -/
theorem theorem14_green (hconn : G.adj.Connected) (H : CellularEmbedding G o)
    {s ρ ρ₁ δ w A η : ℝ} (hs : 0 < s) (hsρ : s < ρ) (hδ0 : 0 ≤ δ) (h6 : 6 * δ ≤ s)
    (hδρ : δ < ρ - s) (hρ₁ : ρ + δ < ρ₁) (hw : 0 < w) (hδw : δ ≤ w) (hA : 0 ≤ A) (hη : 0 ≤ η)
    (h27 : CellDiamBound H ρ₁ δ)
    (hF : Prop210Bound H (annulusSet 0 s ρ) (fun u => ‖fderiv ℝ (logRad 0 ρ s) u‖ ^ 2) A η)
    (h1 : Prop210Bound H (annulusSet 0 s ρ) (fun _ => 1) A η)
    (hg : Prop210Bound H (ball 0 ρ₁) (lemma34Layer s ρ w) A η) :
    ENNReal.ofReal (G.deg o / lemma34Bound s ρ δ w A η) ≤ green G o (vFin H (ball 0 ρ)) := by
  obtain ⟨g, hgo, hg0, hgE⟩ := lemma34 H hs hsρ hδ0 h6 hδρ hρ₁ hw hδw hA hη h27 hF h1 hg
  have ho : o ∈ vFin H (ball 0 ρ) :=
    (mem_vFin H isBounded_ball).mpr ⟨0, H.zero_mem_root, mem_ball_self (hs.trans hsρ)⟩
  exact green_ge_of_energy_le G hconn ho hgo hg0 hgE

/-- The four inputs of Lemma 3.4 at mesh `ε`: the event of [18] **Lemma 2.7** on `B_{ρ₁}(0)` with
`δ = ε^q`, and the conclusions of [18] **Proposition 2.10** (constants `A`, `η = ε^α`) for
`(D, |∇f|²)`, `(D, 1)` and `(B_{ρ₁}(0), g)`, where `D = {ε^β < |u| < ρ}`, `f = log(ρ/|u|)/log(ρ/ε^β)` and
`g` is the boundary layer of `∂D` of width `ε^{β'}`. -/
def Theorem14Inputs (H : CellularEmbedding G o) (ε ρ ρ₁ q β β' α A : ℝ) : Prop :=
  CellDiamBound H ρ₁ (ε ^ q) ∧
    Prop210Bound H (annulusSet 0 (ε ^ β) ρ)
      (fun u => ‖fderiv ℝ (logRad 0 ρ (ε ^ β)) u‖ ^ 2) A (ε ^ α) ∧
    Prop210Bound H (annulusSet 0 (ε ^ β) ρ) (fun _ => 1) A (ε ^ α) ∧
    Prop210Bound H (ball 0 ρ₁) (lemma34Layer (ε ^ β) ρ (ε ^ β')) A (ε ^ α)

/-- **[18] Theorem 1.4 (recurrence), conditional form**: let `G` be a connected locally finite
multigraph with cellular embeddings `H k` (all rooted at `o`), `ε k → 0` positive meshes, and parameters
`0 < ρ < ρ₁`, `0 < β`, `3β < q`, `2β < β' ≤ q`, `2β < α`, `A ≥ 0`. If for infinitely many `k` the
inputs of Lemma 3.4 (Lemma 2.7 and Proposition 2.10, `Theorem14Inputs`) hold for `H k` at mesh `ε k`, then
simple random walk on `G` is recurrent. -/
theorem theorem14_recurrent (hconn : G.adj.Connected) (H : ℕ → CellularEmbedding G o)
    (ε : ℕ → ℝ) (hε : ∀ k, 0 < ε k) (hε0 : Tendsto ε atTop (𝓝 0))
    {ρ ρ₁ q β β' α A : ℝ} (hρ : 0 < ρ) (hρ₁ : ρ < ρ₁) (hβ : 0 < β) (hq : 3 * β < q)
    (hβ' : 2 * β < β') (hβ'q : β' ≤ q) (hα : 2 * β < α) (hA : 0 ≤ A)
    (hin : ∃ᶠ k in atTop, Theorem14Inputs (H k) (ε k) ρ ρ₁ q β β' α A) : G.Recurrent := by
  have hlim := tendsto_lemma34Bound hε hε0 (A := A) hρ hβ hq hβ' hα
  have hs := tendsto_rpow_of_tendsto_zero hε0 hβ
  have hδ := tendsto_rpow_of_tendsto_zero hε0 (show 0 < q by linarith)
  have hqβ := tendsto_rpow_div_pow hε hε0 (a := q) (b := β) (n := 1) (by push_cast; linarith)
  -- the side conditions of `lemma34` hold for all large `k`
  have hside : ∀ᶠ k in atTop, ε k < 1 ∧ ε k ^ β < ρ ∧ 6 * ε k ^ q ≤ ε k ^ β ∧
      ε k ^ q < ρ - ε k ^ β ∧ ρ + ε k ^ q < ρ₁ := by
    filter_upwards [hε0.eventually (gt_mem_nhds one_pos), hs.eventually (gt_mem_nhds (by linarith :
      (0 : ℝ) < ρ / 2)), hδ.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < ρ / 2)),
      hδ.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < ρ₁ - ρ)),
      hqβ.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 6))] with k h1 h2 h3 h4 h5
    have hsk := Real.rpow_pos_of_pos (hε k) β
    refine ⟨h1, by linarith, ?_, by linarith, by linarith⟩
    rw [pow_one, div_lt_iff₀ hsk] at h5
    linarith
  refine recurrent_of_effCond_le G hconn o (fun k => vFin (H k) (ball 0 ρ))
    (fun k => (mem_vFin (H k) isBounded_ball).mpr ⟨0, (H k).zero_mem_root, mem_ball_self hρ⟩)
    fun η hη => ?_
  obtain ⟨k, ⟨⟨h27, hF, h1, hg⟩, hε1, hsρ, h6, hδρ, hρ₁'⟩, hk⟩ :=
    ((hin.and_eventually hside).and_eventually (hlim.eventually (gt_mem_nhds hη))).exists
  refine ⟨k, (effCond_le_lemma34Bound (H k) hconn (Real.rpow_pos_of_pos (hε k) β) hsρ
    (Real.rpow_pos_of_pos (hε k) q).le h6 hδρ hρ₁' (Real.rpow_pos_of_pos (hε k) β')
    (Real.rpow_le_rpow_of_exponent_ge (hε k) hε1.le hβ'q) hA (Real.rpow_pos_of_pos (hε k) α).le
    h27 hF h1 hg).trans hk.le⟩

/-- **The Borel–Cantelli step of [18] Theorem 1.4**: for a random graph with random cellular
embeddings, if the probabilities that the inputs fail at mesh `ε k` are summable, then almost surely the
inputs hold for all large `k`, hence (with `theorem14_recurrent`) the graph is recurrent a.s. -/
theorem ae_recurrent_of_summable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {E' : Ω → Type*}
    (Gω : ∀ ω, LFMultigraph V (E' ω)) (oω : V) (hconn : ∀ᵐ ω ∂P, (Gω ω).adj.Connected)
    (H : ∀ ω, ℕ → CellularEmbedding (Gω ω) oω) (ε : ℕ → ℝ) (hε : ∀ k, 0 < ε k)
    (hε0 : Tendsto ε atTop (𝓝 0)) {ρ ρ₁ q β β' α A : ℝ} (hρ : 0 < ρ) (hρ₁ : ρ < ρ₁) (hβ : 0 < β)
    (hq : 3 * β < q) (hβ' : 2 * β < β') (hβ'q : β' ≤ q) (hα : 2 * β < α) (hA : 0 ≤ A)
    (hsum : ∑' k, P {ω | ¬ Theorem14Inputs (H ω k) (ε k) ρ ρ₁ q β β' α A} ≠ ⊤) :
    ∀ᵐ ω ∂P, (Gω ω).Recurrent := by
  have hbc := measure_limsup_atTop_eq_zero hsum
  have hev : ∀ᵐ ω ∂P, ∀ᶠ k in atTop, Theorem14Inputs (H ω k) (ε k) ρ ρ₁ q β β' α A := by
    rw [ae_iff]
    refine measure_mono_null (fun ω hω => ?_) hbc
    rw [Set.mem_ofPred_eq, Filter.not_eventually] at hω
    rw [Filter.limsup_eq_iInf_iSup_of_nat]
    simp only [Set.iInf_eq_iInter, Set.iSup_eq_iUnion, Set.mem_iInter, Set.mem_iUnion]
    intro n
    obtain ⟨k, hk, hkn⟩ := (Filter.frequently_atTop.mp hω) n
    exact ⟨k, hk, hkn⟩
  filter_upwards [hconn, hev] with ω hc he
  exact theorem14_recurrent hc (H ω) ε hε hε0 hρ hρ₁ hβ hq hβ' hβ'q hα hA he.frequently

/-! ### The mated-CRT map -/

/-- Consecutive vertices of the mated-CRT map are adjacent (Definition 1.12: the edge `(x, x + 1)`). -/
theorem matedCRT_adj_succ (ε : ℝ) (ω : MatedCRT.Path2) (h : MatedCRT.IsLocallyFinite ε ω)
    (x : ℤ) : (MatedCRT.graph ε ω h).adj.Adj x (x + 1) := by
  refine adj_of_edge (MatedCRT.graph ε ω h) (e := ⟨(x, x + 1, false), lt_add_one x,
    Or.inl ⟨rfl, rfl⟩⟩) ?_
  show x ≠ x + 1
  omega

/-- **The mated-CRT map is connected** (proved here; the frozen anchor `matedCRT_graph_connected` is
not imported). -/
theorem matedCRT_connected (ε : ℝ) (ω : MatedCRT.Path2) (h : MatedCRT.IsLocallyFinite ε ω) :
    (MatedCRT.graph ε ω h).adj.Connected := by
  have hreach : ∀ n : ℤ, (MatedCRT.graph ε ω h).adj.Reachable 0 n := by
    intro n
    induction n using Int.induction_on with
    | zero => exact SimpleGraph.Reachable.refl _
    | succ i ih => exact ih.trans (matedCRT_adj_succ ε ω h i).reachable
    | pred i ih =>
      refine ih.trans ?_
      have := (matedCRT_adj_succ ε ω h (-(i : ℤ) - 1)).reachable
      rw [show -(i : ℤ) - 1 + 1 = -(i : ℤ) by ring] at this
      exact this.symm
  exact SimpleGraph.connected_iff_exists_forall_reachable _ |>.mpr ⟨0, hreach⟩

/-- **[18] Theorem 1.4 for the frozen ε-mated-CRT map, conditional form**: if for infinitely many `k`
The cells `H k` of `MatedCRT.graph ε ω h` (rooted at the vertex `0`) satisfy the inputs of Lemma 2.7 and
Proposition 2.10 at meshes `εₖ → 0`, the walk on the map is recurrent. -/
theorem theorem14_matedCRT_recurrent (ε : ℝ) (ω : MatedCRT.Path2) (h : MatedCRT.IsLocallyFinite ε ω)
    (H : ℕ → CellularEmbedding (MatedCRT.graph ε ω h) 0) (εk : ℕ → ℝ) (hε : ∀ k, 0 < εk k)
    (hε0 : Tendsto εk atTop (𝓝 0)) {ρ ρ₁ q β β' α A : ℝ} (hρ : 0 < ρ) (hρ₁ : ρ < ρ₁) (hβ : 0 < β)
    (hq : 3 * β < q) (hβ' : 2 * β < β') (hβ'q : β' ≤ q) (hα : 2 * β < α) (hA : 0 ≤ A)
    (hin : ∃ᶠ k in atTop, Theorem14Inputs (H k) (εk k) ρ ρ₁ q β β' α A) :
    (MatedCRT.graph ε ω h).Recurrent :=
  theorem14_recurrent (matedCRT_connected ε ω h) H εk hε hε0 hρ hρ₁ hβ hq hβ' hβ'q hα hA hin

end MatedCRTHarmonic.GMS3
