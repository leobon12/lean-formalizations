import MatedCRTHarmonic.GMSMain.T13Energy
import MatedCRTHarmonic.BundleSec4.FixedInstance

/-!
# [18] Theorem 1.4 (Green's function on the diagonal) for a random dyadic cell family

Source: [18] Theorem 1.4 : with `τ^ε` the exit time of simple random
walk on `G^ε` from `V_{G^ε}(B_ρ(0))`, there are `α > 0` (depending only on `γ`) and `A > 0` (depending only on `ρ`, `γ`)
with `P[Gr^ε_{τ^ε}(0, 0)/deg(0; G^ε) ≥ (1/A) log ε⁻¹] ≥ 1 − O_ε(ε^α)` (1.8). Proof: [18]
and Details (c5); G3's deterministic `GMS3.theorem14_green` (`Gr ≥ deg(0)/lemma34Bound`).

* `t13_tendsto_lemma34Bound_mul_log` — `lemma34Bound(ε^β, ρ, ε^q, ε^{β'}, A, ε^α) · log(ρ/ε^β) → 6πA`;
* `t13_lemma34Bound_pos` — the bound is positive;
* `t13_theorem14Inputs_bad_le` — the union bound for the four inputs of Lemma 3.4 at one fine mesh;
* **`t13_green_of_family`** — (1.8) for any random dyadic cell family with connected graphs, the Lemma 2.7 bound and
  Proposition 2.10 at `(ρ_P, 100)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology Real
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMSMain

open MatedCRTHarmonic GMS3

/-- **The Lemma 3.4 error term is `≈ 6πA / log(ρ/ε^β)`**: `lemma34Bound · log(ρ/ε^β) → 6πA` along `s = ε^β`,
`δ = ε^q`, `w = ε^{β'}`, `η = ε^α`, `ε → 0`, when `3β < q`, `2β < β'`, `2β < α`. -/
theorem t13_tendsto_lemma34Bound_mul_log {ε : ℕ → ℝ} (hε : ∀ k, 0 < ε k) (hε0 : Tendsto ε atTop (𝓝 0))
    {ρ β q β' α A : ℝ} (hρ : 0 < ρ) (hβ : 0 < β) (hq : 3 * β < q) (hβ' : 2 * β < β') (hα : 2 * β < α) :
    Tendsto (fun k => lemma34Bound (ε k ^ β) ρ (ε k ^ q) (ε k ^ β') A (ε k ^ α) * Real.log (ρ / ε k ^ β))
      atTop (𝓝 (3 * A * (2 * π))) := by
  have hL := tendsto_log_div_rpow hε hε0 hρ hβ
  have hX : Tendsto (fun k => (Real.log (ρ / ε k ^ β))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hL
  have hε' : Tendsto ε atTop (𝓝[>] 0) := tendsto_nhdsWithin_iff.mpr ⟨hε0, Eventually.of_forall hε⟩
  have hα0 : 0 < α := by linarith
  have hlogmul : Tendsto (fun k => Real.log (ε k) * ε k ^ α) atTop (𝓝 0) :=
    (tendsto_log_mul_rpow_nhdsGT_zero hα0).comp hε'
  have hη := tendsto_rpow_of_tendsto_zero hε0 hα0
  have hηL : Tendsto (fun k => ε k ^ α * Real.log (ρ / ε k ^ β)) atTop (𝓝 0) := by
    have heq : (fun k => ε k ^ α * Real.log (ρ / ε k ^ β)) =
        fun k => Real.log ρ * ε k ^ α + (-β) * (Real.log (ε k) * ε k ^ α) := by
      funext k
      rw [Real.log_div hρ.ne' (Real.rpow_pos_of_pos (hε k) β).ne', Real.log_rpow (hε k)]
      ring
    rw [heq]
    simpa using (hη.const_mul (Real.log ρ)).add (hlogmul.const_mul (-β))
  have hw := tendsto_rpow_of_tendsto_zero hε0 (show 0 < β' by linarith)
  have hs := tendsto_rpow_of_tendsto_zero hε0 hβ
  have r4 := tendsto_rpow_div_pow hε hε0 (a := q) (b := β) (n := 3) (by push_cast; linarith)
  have r1 := tendsto_rpow_div_pow hε hε0 (a := β') (b := β) (n := 1) (by push_cast; linarith)
  have r2 := tendsto_rpow_div_pow hε hε0 (a := β') (b := β) (n := 2) (by push_cast; linarith)
  have r3 := tendsto_rpow_div_pow hε hε0 (a := α) (b := β) (n := 2) (by push_cast; linarith)
  have r5 := tendsto_rpow_div_pow hε hε0 (a := q) (b := β) (n := 2) (by push_cast; linarith)
  simp only [pow_one] at r1
  set S : ℕ → ℝ := fun k => 6 * (ε k ^ q / (ε k ^ β) ^ 3) * (A * (π * ρ ^ 2) + ε k ^ α) +
      12 * (A * (8 * π) * (ε k ^ β' / ε k ^ β + 4 * (ε k ^ β' / ε k ^ β) ^ 2 +
        ρ * (ε k ^ β' / (ε k ^ β) ^ 2)) + ε k ^ α / (ε k ^ β) ^ 2) +
      384 * (ε k ^ q / (ε k ^ β) ^ 2) ^ 2 * ((A * (π * ρ ^ 2) + ε k ^ α) +
        (A * (8 * π * ε k ^ β' * (ε k ^ β + 2 * ε k ^ β') + 8 * π * ε k ^ β' * (ρ + 2 * ε k ^ β')) +
          ε k ^ α)) with hS
  obtain ⟨S₀, hSlim⟩ : ∃ S₀, Tendsto S atTop (𝓝 S₀) :=
    ⟨_, (((r4.const_mul 6).mul (hη.const_add _)).add
      (((((r1.add ((r1.pow 2).const_mul 4)).add (r2.const_mul ρ)).const_mul (A * (8 * π))).add
        r3).const_mul 12)).add
      (((r5.pow 2).const_mul 384).mul ((hη.const_add _).add
        (((((hw.const_mul (8 * π)).mul (hs.add (hw.const_mul 2))).add
          ((hw.const_mul (8 * π)).mul ((hw.const_mul 2).const_add ρ))).const_mul A).add hη)))⟩
  have heq : ∀ᶠ k in atTop,
      lemma34Bound (ε k ^ β) ρ (ε k ^ q) (ε k ^ β') A (ε k ^ α) * Real.log (ρ / ε k ^ β) =
        3 * A * (2 * π) + 3 * (ε k ^ α * Real.log (ρ / ε k ^ β)) +
          (Real.log (ρ / ε k ^ β))⁻¹ * S k := by
    filter_upwards [hL.eventually_ne_atTop 0] with k hk
    have hsk : 0 < ε k ^ β := Real.rpow_pos_of_pos (hε k) β
    rw [lemma34Bound_eq hsk hk]
    simp only [hS]
    field_simp
    ring
  refine Tendsto.congr' (EventuallyEq.symm heq) ?_
  have hlim := ((tendsto_const_nhds (x := 3 * A * (2 * π))).add (hηL.const_mul 3)).add (hX.mul hSlim)
  simpa using hlim

/-- The Lemma 3.4 error term is positive. -/
theorem t13_lemma34Bound_pos {s ρ δ w A η : ℝ} (hs : 0 < s) (hsρ : s < ρ) (hδ : 0 ≤ δ) (hw : 0 ≤ w)
    (hA : 0 ≤ A) (hη : 0 < η) : 0 < lemma34Bound s ρ δ w A η := by
  have hρ : 0 < ρ := hs.trans hsρ
  have hℓ : 0 < Real.log (ρ / s) := Real.log_pos ((one_lt_div hs).mpr hsρ)
  unfold lemma34Bound
  positivity

/-- **The union bound for the four inputs of Lemma 3.4** at one mesh where the three Proposition 2.10 tests are
admissible. -/
theorem t13_theorem14Inputs_bad_le (F : CellFamily.RandomCellFamily) (k : ℕ)
    {ρ ρ₁ q β β' α A₂ ρP βG CP C27 : ℝ} (hCP : 0 ≤ CP) (hC27 : 0 ≤ C27)
    (h27 : F.P {ω | CellDiamBound (F.H k ω) ρ₁ (CellFamily.mesh k ^ q)}ᶜ ≤
      ENNReal.ofReal (C27 * CellFamily.mesh k ^ α))
    (h210 : ∀ (V : Set ℂ) (g : ℂ → ℝ), GMS4.Prop210Admissible (CellFamily.mesh k) ρP 100 βG V g →
      F.P (GMS4.Prop210Bad F k V g A₂ (CellFamily.mesh k ^ α)) ≤ ENNReal.ofReal (CP * CellFamily.mesh k ^ α))
    (hAdm : GMS4.Prop210Admissible (CellFamily.mesh k) ρP 100 βG
        (annulusSet 0 (CellFamily.mesh k ^ β) ρ)
        (fun u => ‖fderiv ℝ (logRad 0 ρ (CellFamily.mesh k ^ β)) u‖ ^ 2) ∧
      GMS4.Prop210Admissible (CellFamily.mesh k) ρP 100 βG
        (annulusSet 0 (CellFamily.mesh k ^ β) ρ) (fun _ => 1) ∧
      GMS4.Prop210Admissible (CellFamily.mesh k) ρP 100 βG
        (ball 0 ρ₁) (lemma34Layer (CellFamily.mesh k ^ β) ρ (CellFamily.mesh k ^ β'))) :
    F.P {ω | ¬ Theorem14Inputs (F.H k ω) (CellFamily.mesh k) ρ ρ₁ q β β' α A₂} ≤
      ENNReal.ofReal ((C27 + 3 * CP) * CellFamily.mesh k ^ α) := by
  have hm : 0 ≤ CellFamily.mesh k ^ α := Real.rpow_nonneg (BundleSec4.bundle_mesh_pos k).le α
  set B27 : Set F.Ω := {ω | CellDiamBound (F.H k ω) ρ₁ (CellFamily.mesh k ^ q)}ᶜ
  set Bf := GMS4.Prop210Bad F k (annulusSet 0 (CellFamily.mesh k ^ β) ρ)
    (fun u => ‖fderiv ℝ (logRad 0 ρ (CellFamily.mesh k ^ β)) u‖ ^ 2) A₂ (CellFamily.mesh k ^ α)
  set B1 := GMS4.Prop210Bad F k (annulusSet 0 (CellFamily.mesh k ^ β) ρ) (fun _ => 1) A₂ (CellFamily.mesh k ^ α)
  set Bg := GMS4.Prop210Bad F k (ball 0 ρ₁) (lemma34Layer (CellFamily.mesh k ^ β) ρ (CellFamily.mesh k ^ β')) A₂
    (CellFamily.mesh k ^ α)
  have hsub : {ω | ¬ Theorem14Inputs (F.H k ω) (CellFamily.mesh k) ρ ρ₁ q β β' α A₂} ⊆ B27 ∪ Bf ∪ B1 ∪ Bg := by
    intro ω hω
    by_contra hcon
    apply hω
    refine ⟨?_, ?_, ?_, ?_⟩
    · by_contra h
      exact hcon (Or.inl (Or.inl (Or.inl h)))
    · by_contra h
      exact hcon (Or.inl (Or.inl (Or.inr h)))
    · by_contra h
      exact hcon (Or.inl (Or.inr h))
    · by_contra h
      exact hcon (Or.inr h)
  calc F.P {ω | ¬ Theorem14Inputs (F.H k ω) (CellFamily.mesh k) ρ ρ₁ q β β' α A₂}
      ≤ F.P (B27 ∪ Bf ∪ B1 ∪ Bg) := measure_mono hsub
    _ ≤ ((F.P B27 + F.P Bf) + F.P B1) + F.P Bg :=
        (measure_union_le _ _).trans (add_le_add ((measure_union_le _ _).trans
          (add_le_add (measure_union_le _ _) le_rfl)) le_rfl)
    _ ≤ ((ENNReal.ofReal (C27 * CellFamily.mesh k ^ α) + ENNReal.ofReal (CP * CellFamily.mesh k ^ α)) +
          ENNReal.ofReal (CP * CellFamily.mesh k ^ α)) + ENNReal.ofReal (CP * CellFamily.mesh k ^ α) :=
        add_le_add (add_le_add (add_le_add h27 (h210 _ _ hAdm.1)) (h210 _ _ hAdm.2.1)) (h210 _ _ hAdm.2.2)
    _ = ENNReal.ofReal ((C27 + 3 * CP) * CellFamily.mesh k ^ α) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

/-- `2^{-k} → 0`. -/
theorem t13_mesh_tendsto_zero : Tendsto CellFamily.mesh atTop (𝓝 0) := by
  have hp : Tendsto (fun k : ℕ => (2 : ℝ) ^ k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  rw [show CellFamily.mesh = fun k : ℕ => ((2 : ℝ) ^ k)⁻¹ from by
    funext k; simp [CellFamily.mesh, zpow_neg, zpow_natCast]]
  exact tendsto_inv_atTop_zero.comp hp

/-- `log(1/2^{-k}) → ∞`. -/
theorem t13_tendsto_log_inv_mesh : Tendsto (fun k : ℕ => Real.log ((CellFamily.mesh k)⁻¹)) atTop atTop := by
  have hε' : Tendsto CellFamily.mesh atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨t13_mesh_tendsto_zero,
      Eventually.of_forall BundleSec4.bundle_mesh_pos⟩
  exact Real.tendsto_log_atTop.comp (tendsto_inv_nhdsGT_zero.comp hε')

/-- **[18] Theorem 1.4, (1.8), for a random dyadic cell family**: with connected graphs, the Lemma 2.7 bound on
`B_{ρ₁}(0)` and Proposition 2.10 at `(ρ_P, 100, β_G)` (threshold `A₂`, tolerance `ε^α`), for parameters
`0 < ρ < ρ₁ ≤ ρ_P < 1`, `3β < q`, `2β < β' ≤ q`, `2β < α`, `3β ≤ β_G`, `β' ≤ β_G`, there are `A > 0` and `C ≥ 0` such
that for every `k`, except on an event of probability `≤ C 2^{-kα}`,
`Gr_{τ}(0, 0) ≥ (1/A) log(2^k) deg(0)` for the walk on `G_k` killed on exiting `V(B_ρ(0))`. -/
theorem t13_green_of_family (F : CellFamily.RandomCellFamily) (hconn : ∀ k ω, (F.G k ω).adj.Connected)
    {ρ ρ₁ ρP q β β' α βG A₂ CP C27 : ℝ} (hρ : 0 < ρ) (hρρ₁ : ρ < ρ₁) (hρ₁P : ρ₁ ≤ ρP) (hρP1 : ρP < 1)
    (hβ : 0 < β) (hq : 3 * β < q) (hβ' : 2 * β < β') (hβ'q : β' ≤ q) (hα : 2 * β < α)
    (hβG : 0 < βG) (h3βG : 3 * β ≤ βG) (hβ'G : β' ≤ βG) (hA₂ : 0 ≤ A₂) (hCP : 0 ≤ CP) (hC27 : 0 ≤ C27)
    (h27 : ∀ k : ℕ, F.P {ω | CellDiamBound (F.H k ω) ρ₁ (CellFamily.mesh k ^ q)}ᶜ ≤
      ENNReal.ofReal (C27 * CellFamily.mesh k ^ α))
    (h210 : ∀ (k : ℕ) (V : Set ℂ) (g : ℂ → ℝ), GMS4.Prop210Admissible (CellFamily.mesh k) ρP 100 βG V g →
      F.P (GMS4.Prop210Bad F k V g A₂ (CellFamily.mesh k ^ α)) ≤ ENNReal.ofReal (CP * CellFamily.mesh k ^ α)) :
    ∃ A : ℝ, 0 < A ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ,
      F.P {ω | ¬ ENNReal.ofReal (Real.log ((CellFamily.mesh k)⁻¹) / A * (F.G k ω).deg 0) ≤
        green (F.G k ω) 0 (vFin (F.H k ω) (ball 0 ρ))} ≤ ENNReal.ofReal (C * CellFamily.mesh k ^ α) := by
  have hmesh := BundleSec4.bundle_mesh_pos
  have hmesh0 : Tendsto CellFamily.mesh atTop (𝓝 0) := t13_mesh_tendsto_zero
  have hα0 : 0 < α := by linarith
  set M : ℝ := 3 * A₂ * (2 * π) + 1 with hMdef
  have hM : 0 < M := by positivity
  set A : ℝ := 2 * M / β with hAdef
  have hA : 0 < A := by positivity
  -- the eventual conditions
  have hT := t13_tendsto_lemma34Bound_mul_log hmesh hmesh0 (A := A₂) hρ hβ hq hβ' hα
  have hTev : ∀ᶠ k in atTop, lemma34Bound (CellFamily.mesh k ^ β) ρ (CellFamily.mesh k ^ q)
      (CellFamily.mesh k ^ β') A₂ (CellFamily.mesh k ^ α) * Real.log (ρ / CellFamily.mesh k ^ β) ≤ M :=
    hT.eventually (ge_mem_nhds (by linarith))
  have hlogev : ∀ᶠ k in atTop, -Real.log ρ ≤ β / 2 * Real.log ((CellFamily.mesh k)⁻¹) ∧
      0 < Real.log ((CellFamily.mesh k)⁻¹) :=
    (t13_tendsto_log_inv_mesh.const_mul_atTop (by positivity : 0 < β / 2)).eventually_ge_atTop _ |>.and
      (t13_tendsto_log_inv_mesh.eventually_gt_atTop 0)
  have hs := tendsto_rpow_of_tendsto_zero hmesh0 hβ
  have hδ := tendsto_rpow_of_tendsto_zero hmesh0 (show 0 < q by linarith)
  have hqβ := tendsto_rpow_div_pow hmesh hmesh0 (a := q) (b := β) (n := 1) (by push_cast; linarith)
  have hside : ∀ᶠ k in atTop, CellFamily.mesh k ^ β < ρ ∧ 6 * CellFamily.mesh k ^ q ≤ CellFamily.mesh k ^ β ∧
      CellFamily.mesh k ^ q < ρ - CellFamily.mesh k ^ β ∧ ρ + CellFamily.mesh k ^ q < ρ₁ ∧
      CellFamily.mesh k ^ β ≤ ρ * Real.exp (-2) := by
    filter_upwards [hs.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < ρ / 2)),
      hδ.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < ρ / 2)),
      hδ.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < ρ₁ - ρ)),
      hqβ.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 6)),
      hs.eventually (ge_mem_nhds (by positivity : (0 : ℝ) < ρ * Real.exp (-2)))] with k h2 h3 h4 h5 h6
    have hsk := Real.rpow_pos_of_pos (hmesh k) β
    refine ⟨by linarith, ?_, by linarith, by linarith, h6⟩
    rw [pow_one, div_lt_iff₀ hsk] at h5
    linarith
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.1 (((hTev.and hlogev).and hside).and (eventually_ge_atTop 1))
  have hK1pos : 0 < CellFamily.mesh k₀ ^ α := Real.rpow_pos_of_pos (hmesh k₀) α
  set Kc : ℝ := (CellFamily.mesh k₀ ^ α)⁻¹ with hKcdef
  have hKc : 0 ≤ Kc := (inv_pos.2 hK1pos).le
  refine ⟨A, hA, C27 + 3 * CP + Kc, by positivity, fun k => ?_⟩
  have hmα : 0 ≤ CellFamily.mesh k ^ α := Real.rpow_nonneg (hmesh k).le α
  rcases le_or_gt k₀ k with hk | hk
  · obtain ⟨⟨⟨hTk, hlog1, hlog0⟩, hsρ, h6, hδρ, hρ₁', hsmall⟩, hk1⟩ := hk₀ k hk
    have hsk : 0 < CellFamily.mesh k ^ β := Real.rpow_pos_of_pos (hmesh k) β
    have hε1 : CellFamily.mesh k < 1 := GMSLemma27.mesh_lt_one (by omega)
    have hAdm := BundleSec4.bundle_recThreeAdmissible_of_small hk1 hρ hρρ₁ hρ₁P hρP1
      BundleSec4.bundle_sixteen_pi_le_hundred hβG hβ h3βG hβ'G hsmall (β' := β')
    have hbad := t13_theorem14Inputs_bad_le F k (ρ := ρ) (q := q) (β := β) (β' := β') hCP hC27 (h27 k)
      (h210 k) hAdm
    -- on the good event, the Green function bound
    have hsub : {ω | ¬ ENNReal.ofReal (Real.log ((CellFamily.mesh k)⁻¹) / A * (F.G k ω).deg 0) ≤
        green (F.G k ω) 0 (vFin (F.H k ω) (ball 0 ρ))} ⊆
        {ω | ¬ Theorem14Inputs (F.H k ω) (CellFamily.mesh k) ρ ρ₁ q β β' α A₂} := by
      intro ω hω hin
      apply hω
      obtain ⟨h27ω, hF, h1, hg⟩ := hin
      have hgreen := theorem14_green (hconn k ω) (F.H k ω) hsk hsρ
        (Real.rpow_pos_of_pos (hmesh k) q).le h6 hδρ hρ₁' (Real.rpow_pos_of_pos (hmesh k) β')
        (Real.rpow_le_rpow_of_exponent_ge (hmesh k) hε1.le hβ'q) hA₂ hmα h27ω hF h1 hg
      refine le_trans (ENNReal.ofReal_le_ofReal ?_) hgreen
      -- `log(1/ε)/A · deg ≤ deg / B`
      set Bk := lemma34Bound (CellFamily.mesh k ^ β) ρ (CellFamily.mesh k ^ q) (CellFamily.mesh k ^ β') A₂
        (CellFamily.mesh k ^ α) with hBk
      have hB : 0 < Bk := t13_lemma34Bound_pos hsk hsρ (Real.rpow_pos_of_pos (hmesh k) q).le
        (Real.rpow_pos_of_pos (hmesh k) β').le hA₂ (Real.rpow_pos_of_pos (hmesh k) α)
      set Λ := Real.log ((CellFamily.mesh k)⁻¹) with hΛ
      have hℓ : Real.log (ρ / CellFamily.mesh k ^ β) = Real.log ρ + β * Λ := by
        rw [Real.log_div hρ.ne' hsk.ne', Real.log_rpow (hmesh k), hΛ, Real.log_inv]
        ring
      have hℓlow : β / 2 * Λ ≤ Real.log (ρ / CellFamily.mesh k ^ β) := by rw [hℓ]; nlinarith
      have hBΛ : Bk * Λ ≤ A := by
        have h1 : Bk * (β / 2 * Λ) ≤ M :=
          (mul_le_mul_of_nonneg_left hℓlow hB.le).trans hTk
        rw [hAdef, le_div_iff₀ hβ]
        nlinarith
      have hdeg : (0 : ℝ) ≤ (F.G k ω).deg 0 := Nat.cast_nonneg _
      rw [div_mul_eq_mul_div, le_div_iff₀ hB, div_mul_eq_mul_div, div_le_iff₀ hA]
      nlinarith [mul_le_mul_of_nonneg_left hBΛ hdeg]
    refine (measure_mono hsub).trans (hbad.trans (ENNReal.ofReal_le_ofReal ?_))
    nlinarith
  · -- the coarse meshes
    have hmesh' : CellFamily.mesh k₀ ^ α ≤ CellFamily.mesh k ^ α :=
      Real.rpow_le_rpow (hmesh k₀).le (BundleSec4.bundle_mesh_anti hk.le) hα0.le
    have hone : (1 : ℝ) ≤ (C27 + 3 * CP + Kc) * CellFamily.mesh k ^ α := by
      have h1 : 1 ≤ Kc * CellFamily.mesh k ^ α := by
        calc (1 : ℝ) = Kc * CellFamily.mesh k₀ ^ α := (inv_mul_cancel₀ hK1pos.ne').symm
          _ ≤ Kc * CellFamily.mesh k ^ α := mul_le_mul_of_nonneg_left hmesh' hKc
      nlinarith
    calc _ ≤ (1 : ℝ≥0∞) := prob_le_one
      _ = ENNReal.ofReal 1 := ENNReal.ofReal_one.symm
      _ ≤ ENNReal.ofReal ((C27 + 3 * CP + Kc) * CellFamily.mesh k ^ α) := ENNReal.ofReal_le_ofReal hone

end MatedCRTHarmonic.GMSMain
