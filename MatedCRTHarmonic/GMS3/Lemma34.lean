import MatedCRTHarmonic.GMS3.Annulus
import MatedCRTHarmonic.GMS3.Recurrence

/-!
# GMS [18] Lemma 3.4, deterministic form, and the conductance bound behind Theorem 1.4

Source: GMS [18] Lemma 3.4 and the proof of Theorem 1.4 ([18]): (3.15) reads `A / log(ε⁻¹ ∧ s⁻¹)` (∧, not ∨), and the
Dirichlet-principle step of Theorem 1.4 is an inequality.

Fix a centre `z` and radii `0 < r₁ < r₂`, the open annulus `D = annulusSet z r₁ r₂` and the harmonic
function `logRad z r₂ r₁` (`0` on `∂B_{r₂}(z)`, `1` on `∂B_{r₁}(z)`). [18]'s `f^s_ε` of Lemma 3.4 is the
sampled function (3.11) on `V(D)`, extended by `1` on `V(B̄_{r₁}(z))` and by `0` elsewhere:

* `annRef H z r₁ r₂ x`: a reference point of the cell `H_x`, on the inner circle if the cell meets it,
  else on the outer circle if it meets it (so that the sampled boundary values are exactly `1`, resp. `0`);
* `annTest H z r₁ r₂`: the extended sampled function;
* `energy_annTest_le` (**pasting**): if every cell meeting `B̄_{r₂}(z)` has diameter `< r₂ − r₁`, then
  `annTest` vanishes off `V(B_{r₂}(z))` and its energy is at most `Energy(f^ε; G(V(D)))`;
* `lemma34` (**[18] Lemma 3.4 with the conductance bound of Theorem 1.4**, centre `0`): on the Lemma 2.7
  event and the three Proposition 2.10 inputs `(D, |∇f|²)`, `(D, 1)`, `(B_{ρ₁}(0), g)`, the effective
  conductance from the root to the complement of `V(B_ρ(0))` is at most an explicit
  `lemma34Bound s ρ δ w A η`, whose leading term is `6πA / log(ρ/s)`; every other term is a power of
  `δ, w, η` against inverse powers of `s` and of `log(ρ/s)` (the dyadic grid of (c4) is replaced by taking
  `s` itself as the parameter).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Real Filter
open scoped ENNReal Classical Topology

namespace MatedCRTHarmonic.GMS3

open LFMultigraph Harmonic

variable {V E : Type*} {G : LFMultigraph V E} {o : V} (H : CellularEmbedding G o)

/-! ### Reference points and the sampled test function -/

/-- A reference point of `H_x` for the annulus between `r₁` and `r₂` about `z`: on the inner circle if
The cell meets it, else on the outer circle if it meets it, else any point of the cell. -/
def annRef (z : ℂ) (r₁ r₂ : ℝ) (x : V) : ℂ :=
  if h : (H.cell x ∩ {u | ‖u - z‖ = r₁}).Nonempty then h.some
  else if h' : (H.cell x ∩ {u | ‖u - z‖ = r₂}).Nonempty then h'.some
  else (cell_nonempty H x).some

theorem annRef_mem (z : ℂ) (r₁ r₂ : ℝ) (x : V) : annRef H z r₁ r₂ x ∈ H.cell x := by
  unfold annRef
  split_ifs with h h'
  · exact h.some_mem.1
  · exact h'.some_mem.1
  · exact (cell_nonempty H x).some_mem

theorem norm_annRef_inner {z : ℂ} {r₁ r₂ : ℝ} {x : V}
    (h : (H.cell x ∩ {u | ‖u - z‖ = r₁}).Nonempty) : ‖annRef H z r₁ r₂ x - z‖ = r₁ := by
  unfold annRef
  rw [dite_eq_left h]
  exact h.some_mem.2

theorem norm_annRef_outer {z : ℂ} {r₁ r₂ : ℝ} {x : V}
    (h : ¬ (H.cell x ∩ {u | ‖u - z‖ = r₁}).Nonempty)
    (h' : (H.cell x ∩ {u | ‖u - z‖ = r₂}).Nonempty) : ‖annRef H z r₁ r₂ x - z‖ = r₂ := by
  unfold annRef
  rw [dite_eq_right h, dite_eq_left h']
  exact h'.some_mem.2

/-- [18]'s `f^s_ε` (Lemma 3.4): `1` on cells meeting `B̄_{r₁}(z)`, the sampled `logRad z r₂ r₁` on the
other cells of `V(D)`, `0` elsewhere. -/
def annTest (z : ℂ) (r₁ r₂ : ℝ) (x : V) : ℝ :=
  if (H.cell x ∩ closedBall z r₁).Nonempty then 1
  else if x ∈ vFin H (annulusSet z r₁ r₂) then logRad z r₂ r₁ (annRef H z r₁ r₂ x) else 0

/-- A cell is connected: if it has points with `|u − z| ≤ t` and `|u − z| ≥ t`, it meets the circle. -/
theorem cell_meets_circle {z : ℂ} {t : ℝ} {x : V} {a b : ℂ} (ha : a ∈ H.cell x) (hb : b ∈ H.cell x)
    (hat : ‖a - z‖ ≤ t) (htb : t ≤ ‖b - z‖) : (H.cell x ∩ {u | ‖u - z‖ = t}).Nonempty := by
  obtain ⟨c, hc, hct⟩ := exists_mem_eq_of_isPreconnected (H.isConnected_cell x).isPreconnected
    (continuous_norm_sub_const z) ha hb hat htb
  exact ⟨c, hc, hct⟩

/-- The two radii are far apart compared with the cells. -/
structure AnnulusSetup (z : ℂ) (r₁ r₂ δ : ℝ) : Prop where
  r₁_pos : 0 < r₁
  δ_nonneg : 0 ≤ δ
  δ_lt : δ < r₂ - r₁
  diam_le : ∀ x, (H.cell x ∩ closedBall z r₂).Nonempty → cellDiam H x ≤ δ

/-- `annTest = logRad ∘ annRef` on `V(D)`. -/
theorem annTest_eq_of_mem {z : ℂ} {r₁ r₂ δ : ℝ} (hS : AnnulusSetup H z r₁ r₂ δ) {x : V}
    (hx : x ∈ vFin H (annulusSet z r₁ r₂)) :
    annTest H z r₁ r₂ x = logRad z r₂ r₁ (annRef H z r₁ r₂ x) := by
  unfold annTest
  split_ifs with h
  · obtain ⟨a, ha, haB⟩ := h
    obtain ⟨b, hb, hbD⟩ := (mem_vFin H (isBounded_annulusSet z r₁ r₂)).mp hx
    have hin := cell_meets_circle H ha hb (by rwa [mem_closedBall, dist_eq_norm] at haB) hbD.1.le
    rw [logRad_of_norm_eq_right (by linarith [hS.r₁_pos, hS.δ_lt, hS.δ_nonneg])
      hS.r₁_pos (by linarith [hS.δ_lt, hS.δ_nonneg]) (norm_annRef_inner H hin)]
  · rfl

/-- **Pasting** (the extension of [18]): off `V(D)`, `annTest` is constant along edges. -/
theorem annTest_eq_of_adj_of_notMem {z : ℂ} {r₁ r₂ δ : ℝ} (hS : AnnulusSetup H z r₁ r₂ δ)
    {x y : V} (hadj : G.adj.Adj x y) (hx : x ∉ vFin H (annulusSet z r₁ r₂)) :
    annTest H z r₁ r₂ x = annTest H z r₁ r₂ y := by
  have hb := isBounded_annulusSet z r₁ r₂
  have hxD : ¬ (H.cell x ∩ annulusSet z r₁ r₂).Nonempty := fun h => hx ((mem_vFin H hb).mpr h)
  have hr : r₁ < r₂ := by linarith [hS.δ_lt, hS.δ_nonneg]
  -- every point of `H_x` is inside `B̄_{r₁}` or outside `B_{r₂}`
  have hpt : ∀ u ∈ H.cell x, ‖u - z‖ ≤ r₁ ∨ r₂ ≤ ‖u - z‖ := by
    intro u hu
    by_contra h
    push Not at h
    exact hxD ⟨u, hu, h.1, h.2⟩
  obtain ⟨c, hcx, hcy⟩ := H.inter_of_adj x y hadj
  rcases hpt c hcx with hc | hc
  · -- `H_x` meets `B̄_{r₁}`: both values are `1`
    have hx1 : (H.cell x ∩ closedBall z r₁).Nonempty :=
      ⟨c, hcx, by rw [mem_closedBall, dist_eq_norm]; exact hc⟩
    have hy1 : (H.cell y ∩ closedBall z r₁).Nonempty :=
      ⟨c, hcy, by rw [mem_closedBall, dist_eq_norm]; exact hc⟩
    unfold annTest
    rw [ite_eq_left hx1, ite_eq_left hy1]
  · -- `H_x` lies outside `B_{r₂}`
    have hxall : ∀ u ∈ H.cell x, r₂ ≤ ‖u - z‖ := by
      intro u hu
      rcases hpt u hu with h | h
      · exfalso
        obtain ⟨m, hm, hmt⟩ := cell_meets_circle H (z := z) (t := (r₁ + r₂) / 2) hu hcx
          (by linarith) (by linarith)
        exact hxD ⟨m, hm, by simp only [Set.mem_ofPred_eq] at hmt; constructor <;> linarith⟩
      · exact h
    have hx0 : ¬ (H.cell x ∩ closedBall z r₁).Nonempty := by
      rintro ⟨u, hu, huB⟩
      rw [mem_closedBall, dist_eq_norm] at huB
      linarith [hxall u hu]
    have hTx : annTest H z r₁ r₂ x = 0 := by
      unfold annTest
      rw [ite_eq_right hx0, ite_eq_right hx]
    rw [hTx]
    -- the cell of `y` has small diameter and contains `c`, with `|c − z| ≥ r₂`
    have hy0 : ¬ (H.cell y ∩ closedBall z r₁).Nonempty := by
      rintro ⟨u, hu, huB⟩
      rw [mem_closedBall, dist_eq_norm] at huB
      have hdy := hS.diam_le y ⟨u, hu, by
        rw [mem_closedBall, dist_eq_norm]; linarith⟩
      have := dist_le_cellDiam H hu hcy
      rw [dist_eq_norm] at this
      have h2 : ‖c - z‖ - ‖u - z‖ ≤ ‖u - c‖ := by
        have := norm_sub_norm_le (c - z) (u - z)
        rwa [sub_sub_sub_cancel_right, norm_sub_rev c u] at this
      linarith [hS.δ_lt]
    unfold annTest
    rw [ite_eq_right hy0]
    split_ifs with hyD
    · -- `y ∈ V(D)`: its reference point is on the outer circle
      obtain ⟨b, hb', hbD⟩ := (mem_vFin H hb).mp hyD
      have hout := cell_meets_circle H (t := r₂) hb' hcy hbD.2.le hc
      have hnin : ¬ (H.cell y ∩ {u | ‖u - z‖ = r₁}).Nonempty := by
        rintro ⟨u, hu, hu1⟩
        exact hy0 ⟨u, hu, by rw [mem_closedBall, dist_eq_norm]; exact hu1.le⟩
      rw [logRad_of_norm_eq_left (norm_annRef_outer H hnin hout)]
    · rfl

/-- `annTest` vanishes off `V(B_{r₂}(z))`. -/
theorem annTest_eq_zero_of_notMem {z : ℂ} {r₁ r₂ : ℝ} (hr : r₁ < r₂) {x : V}
    (hx : x ∉ vFin H (ball z r₂)) : annTest H z r₁ r₂ x = 0 := by
  have hxB : ¬ (H.cell x ∩ ball z r₂).Nonempty := fun h => hx ((mem_vFin H isBounded_ball).mpr h)
  unfold annTest
  rw [ite_eq_right, ite_eq_right]
  · intro h
    exact hxB ((mem_vFin H (isBounded_annulusSet z r₁ r₂)).mp h |>.mono
      (Set.inter_subset_inter_right _ (annulusSet_subset_ball z r₁ r₂)))
  · rintro ⟨u, hu, huB⟩
    exact hxB ⟨u, hu, closedBall_subset_ball hr huB⟩

theorem annTest_eq_one {z : ℂ} {r₁ r₂ : ℝ} {x : V} (hx : (H.cell x ∩ closedBall z r₁).Nonempty) :
    annTest H z r₁ r₂ x = 1 := by
  unfold annTest
  rw [ite_eq_left hx]

/-- **Pasting, energy form**: `Energy(annTest; G(nbhd V(B_{r₂}))) ≤ Energy(f^ε; G(V(D)))`. -/
theorem energy_annTest_le {z : ℂ} {r₁ r₂ δ : ℝ} (hS : AnnulusSetup H z r₁ r₂ δ) :
    energy G (nbhd G (vFin H (ball z r₂))) (annTest H z r₁ r₂) ≤
      energy G (vFin H (annulusSet z r₁ r₂)) (logRad z r₂ r₁ ∘ annRef H z r₁ r₂) := by
  set T := annTest H z r₁ r₂
  set A := vFin H (annulusSet z r₁ r₂)
  have key : ∀ e ∈ edgesIn G (nbhd G (vFin H (ball z r₂))),
      (T (G.src e) - T (G.tgt e)) ^ 2 ≠ 0 → e ∈ edgesIn G A ∧
        (T (G.src e) - T (G.tgt e)) ^ 2 =
          ((logRad z r₂ r₁ ∘ annRef H z r₁ r₂) (G.src e) -
            (logRad z r₂ r₁ ∘ annRef H z r₁ r₂) (G.tgt e)) ^ 2 := by
    intro e _ hne
    have hloop : G.src e ≠ G.tgt e := fun h => hne (by rw [h, sub_self, sq, mul_zero])
    have hadj := adj_of_edge G hloop
    have hsA : G.src e ∈ A := by
      by_contra h
      exact hne (by simp only [T]; rw [annTest_eq_of_adj_of_notMem H hS hadj h, sub_self, sq,
        mul_zero])
    have htA : G.tgt e ∈ A := by
      by_contra h
      exact hne (by simp only [T]; rw [← annTest_eq_of_adj_of_notMem H hS hadj.symm h, sub_self, sq,
        mul_zero])
    refine ⟨(mem_edgesIn G).mpr ⟨hsA, htA⟩, ?_⟩
    simp only [Function.comp, T, annTest_eq_of_mem H hS hsA, annTest_eq_of_mem H hS htA]
  unfold energy
  calc ∑ e ∈ edgesIn G (nbhd G (vFin H (ball z r₂))), (T (G.src e) - T (G.tgt e)) ^ 2
      = ∑ e ∈ (edgesIn G (nbhd G (vFin H (ball z r₂)))).filter
          (fun e => (T (G.src e) - T (G.tgt e)) ^ 2 ≠ 0), (T (G.src e) - T (G.tgt e)) ^ 2 :=
        (Finset.sum_filter_ne_zero _).symm
    _ = ∑ e ∈ (edgesIn G (nbhd G (vFin H (ball z r₂)))).filter
          (fun e => (T (G.src e) - T (G.tgt e)) ^ 2 ≠ 0),
          ((logRad z r₂ r₁ ∘ annRef H z r₁ r₂) (G.src e) -
            (logRad z r₂ r₁ ∘ annRef H z r₁ r₂) (G.tgt e)) ^ 2 :=
        Finset.sum_congr rfl fun e he =>
          (key e (Finset.mem_filter.mp he).1 (Finset.mem_filter.mp he).2).2
    _ ≤ ∑ e ∈ edgesIn G A, ((logRad z r₂ r₁ ∘ annRef H z r₁ r₂) (G.src e) -
            (logRad z r₂ r₁ ∘ annRef H z r₁ r₂) (G.tgt e)) ^ 2 := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (fun e he => ?_) fun _ _ _ => sq_nonneg _
        exact (key e (Finset.mem_filter.mp he).1 (Finset.mem_filter.mp he).2).1

/-! ### The Lemma 3.4 bound (centre `0`) -/

theorem ennreal_add_le_ofReal {x y : ℝ≥0∞} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hx : x ≤ ENNReal.ofReal a) (hy : y ≤ ENNReal.ofReal b) : x + y ≤ ENNReal.ofReal (a + b) := by
  rw [ENNReal.ofReal_add ha hb]; exact add_le_add hx hy

theorem ennreal_mul_le_ofReal {x y : ℝ≥0∞} {a b : ℝ} (ha : 0 ≤ a)
    (hx : x ≤ ENNReal.ofReal a) (hy : y ≤ ENNReal.ofReal b) : x * y ≤ ENNReal.ofReal (a * b) := by
  rw [ENNReal.ofReal_mul ha]; exact mul_le_mul' hx hy

/-- The explicit error term of the deterministic Lemma 3.4 (`ℓ = log(ρ/s)`):
`3 [A·2π/ℓ + η + L_F δ (A π ρ² + η) + M_F (A V_g + η)] + 24 Λ² δ² [A π ρ² + η + A V_g + η]` with
`Λ = 4/(ℓ s²)`, `L_F = 2/(ℓ² s³)`, `M_F = 4/(ℓ² s²)` and `V_g = 8πw(s + 2w) + 8πw(ρ + 2w)`. -/
def lemma34Bound (s ρ δ w A η : ℝ) : ℝ :=
  3 * ((A * (2 * π / Real.log (ρ / s)) + η) +
      2 * ((Real.log (ρ / s)) ^ 2 * s ^ 3)⁻¹ * δ * (A * (π * ρ ^ 2) + η) +
      ((Real.log (ρ / s)) ^ 2 * (s / 2) ^ 2)⁻¹ *
        (A * (8 * π * w * (s + 2 * w) + 8 * π * w * (ρ + 2 * w)) + η)) +
    24 * (Real.log (ρ / s) * (s / 2) ^ 2)⁻¹ ^ 2 * δ ^ 2 *
      ((A * (π * ρ ^ 2) + η) + (A * (8 * π * w * (s + 2 * w) + 8 * π * w * (ρ + 2 * w)) + η))

theorem lemma34Bound_nonneg {s ρ δ w A η : ℝ} (hs : 0 < s) (hsρ : s < ρ) (hδ : 0 ≤ δ) (hw : 0 ≤ w)
    (hA : 0 ≤ A) (hη : 0 ≤ η) : 0 ≤ lemma34Bound s ρ δ w A η := by
  have hρ : 0 < ρ := hs.trans hsρ
  have hℓ : 0 < Real.log (ρ / s) := Real.log_pos ((one_lt_div hs).mpr hsρ)
  unfold lemma34Bound
  positivity

/-- The boundary layer of the annulus `{s < |u| < ρ}` used by Lemma 3.4. -/
def lemma34Layer (s ρ w : ℝ) (u : ℂ) : ℝ := max (radialBump 0 s w u) (radialBump 0 ρ w u)

/-- **[18] Lemma 3.4**, deterministic form, with the test function of Theorem 1.4: on the event of
[18] Lemma 2.7 (cells meeting `B_{ρ₁}(0)` have diameter `≤ δ`) and the conclusions of [18] Proposition
2.10 for `(D, |∇f|²)`, `(D, 1)` and `(B_{ρ₁}(0), g)` (`D = {s < |u| < ρ}`, `f = log(ρ/|u|)/log(ρ/s)`,
`g` the boundary layer of width `w`), there is `g` with `g(o) = 1`, `g = 0` off `V(B_ρ(0))` and
`Energy(g) ≤ lemma34Bound s ρ δ w A η`. -/
theorem lemma34 {s ρ ρ₁ δ w A η : ℝ} (hs : 0 < s) (hsρ : s < ρ) (hδ0 : 0 ≤ δ) (h6 : 6 * δ ≤ s)
    (hδρ : δ < ρ - s) (hρ₁ : ρ + δ < ρ₁) (hw : 0 < w) (hδw : δ ≤ w) (hA : 0 ≤ A) (hη : 0 ≤ η)
    (h27 : CellDiamBound H ρ₁ δ)
    (hF : Prop210Bound H (annulusSet 0 s ρ) (fun u => ‖fderiv ℝ (logRad 0 ρ s) u‖ ^ 2) A η)
    (h1 : Prop210Bound H (annulusSet 0 s ρ) (fun _ => 1) A η)
    (hg : Prop210Bound H (ball 0 ρ₁) (lemma34Layer s ρ w) A η) :
    ∃ g : V → ℝ, g o = 1 ∧ (∀ x ∉ vFin H (ball 0 ρ), g x = 0) ∧
      energy G (nbhd G (vFin H (ball 0 ρ))) g ≤ lemma34Bound s ρ δ w A η := by
  have hρ : 0 < ρ := hs.trans hsρ
  set D := annulusSet 0 s ρ with hDdef
  have hDb := isBounded_annulusSet (0 : ℂ) s ρ
  have hDo := isOpen_annulusSet (0 : ℂ) s ρ
  set ℓ := Real.log (ρ / s) with hℓ
  have hℓpos : 0 < ℓ := Real.log_pos ((one_lt_div hs).mpr hsρ)
  have hlogsρ : Real.log (s / ρ) = -ℓ := by
    rw [hℓ, ← Real.log_inv, inv_div]
  have habs : |Real.log (s / ρ)| = ℓ := by rw [hlogsρ, abs_neg, abs_of_pos hℓpos]
  have hsq : (Real.log (s / ρ)) ^ 2 = ℓ ^ 2 := by rw [hlogsρ, neg_sq]
  have hS : AnnulusSetup H 0 s ρ δ :=
    { r₁_pos := hs, δ_nonneg := hδ0, δ_lt := hδρ
      diam_le := fun x ⟨u, hu, huB⟩ => h27 x ⟨u, hu, by
        rw [mem_ball]; rw [mem_closedBall] at huB; linarith⟩ }
  -- diameters of the cells of `V(D)`
  have hδD : ∀ x ∈ vFin H D, cellDiam H x ≤ δ := by
    intro x hx
    obtain ⟨u, hu, huD⟩ := (mem_vFin H hDb).mp hx
    refine h27 x ⟨u, hu, ?_⟩
    rw [mem_ball, dist_zero_right]
    have := huD.2
    rw [sub_zero] at this
    linarith
  -- reference points stay at distance `≥ s − δ` from `0`
  have hpfar : ∀ x ∈ vFin H D, s - δ < ‖annRef H 0 s ρ x‖ := by
    intro x hx
    obtain ⟨u, hu, huD⟩ := (mem_vFin H hDb).mp hx
    have hd := (dist_le_cellDiam H hu (annRef_mem H 0 s ρ x)).trans (hδD x hx)
    rw [dist_eq_norm] at hd
    have h1 : ‖u‖ - ‖annRef H 0 s ρ x‖ ≤ ‖u - annRef H 0 s ρ x‖ := norm_sub_norm_le _ _
    have h2 := huD.1
    rw [sub_zero] at h2
    linarith
  set O : Set ℂ := {u | s / 2 < ‖u - 0‖} with hOdef
  have hO : IsOpen O := isOpen_norm_sub_gt 0 (s / 2)
  have hdf : DifferentiableOn ℝ (logRad 0 ρ s) O := differentiableOn_logRad 0 ρ s (by positivity)
  set Λ := (ℓ * (s / 2) ^ 2)⁻¹ with hΛ
  have hΛ0 : 0 ≤ Λ := by positivity
  have hLip : ∀ u ∈ O, ∀ v ∈ O, ‖fderiv ℝ (logRad 0 ρ s) u - fderiv ℝ (logRad 0 ρ s) v‖ ≤
      Λ * ‖u - v‖ := by
    intro u hu v hv
    have := norm_fderiv_logRad_sub_le (z := 0) (a := ρ) (b := s) (c := s / 2) (by positivity)
      (le_of_lt hu) (le_of_lt hv)
    rwa [habs] at this
  have hseg : ∀ x ∈ vFin H D, ∀ y ∈ vFin H D, G.adj.Adj x y →
      segment ℝ (annRef H 0 s ρ x) (annRef H 0 s ρ y) ⊆ O := by
    intro x hx y hy hadj u hu
    have h1 := norm_sub_le_of_mem_segment hu
    have h2 : ‖annRef H 0 s ρ y - annRef H 0 s ρ x‖ ≤ 2 * δ := by
      rw [← dist_eq_norm, dist_comm]
      refine (dist_le_cellDiam_add_of_adj H hadj (annRef_mem H 0 s ρ x)
        (annRef_mem H 0 s ρ y)).trans ?_
      linarith [hδD x hx, hδD y hy]
    have h3 : ‖annRef H 0 s ρ x‖ - ‖u‖ ≤ ‖u - annRef H 0 s ρ x‖ := by
      rw [norm_sub_rev]; exact norm_sub_norm_le _ _
    show s / 2 < ‖u - 0‖
    rw [sub_zero]
    linarith [hpfar x hx]
  set LF := 2 * (ℓ ^ 2 * s ^ 3)⁻¹ with hLFdef
  have hLF0 : 0 ≤ LF := by positivity
  have hLipF : ∀ u ∈ D, ∀ v ∈ D, ‖fderiv ℝ (logRad 0 ρ s) u‖ ^ 2 ≤
      ‖fderiv ℝ (logRad 0 ρ s) v‖ ^ 2 + LF * dist u v := by
    intro u hu v hv
    have := sqGrad_le_add (z := 0) (a := ρ) (b := s) (c := s) hs hu.1.le hv.1.le
    rwa [hsq] at this
  set MF := (ℓ ^ 2 * (s / 2) ^ 2)⁻¹ with hMFdef
  have hMF : ∀ x ∈ vFin H D, ‖fderiv ℝ (logRad 0 ρ s) (annRef H 0 s ρ x)‖ ^ 2 ≤ MF := by
    intro x hx
    have := sqGrad_le (z := 0) (a := ρ) (b := s) (c := s / 2) (by positivity)
      (w := annRef H 0 s ρ x) (by rw [sub_zero]; linarith [hpfar x hx])
    rwa [hsq] at this
  have hbd : ∀ x ∈ vFin H D, (H.cell x ∩ frontier D).Nonempty →
      H.cell x ⊆ ball 0 ρ₁ ∧ ∀ u ∈ H.cell x, 1 ≤ lemma34Layer s ρ w u := by
    intro x hx ⟨c, hcx, hcfr⟩
    have hc := frontier_annulusSet_subset 0 s ρ hcfr
    have hdx := hδD x hx
    have hdiam : diam (H.cell x) ≤ δ := hdx
    refine ⟨fun u hu => ?_, fun u hu => ?_⟩
    · rw [mem_ball, dist_zero_right]
      have hd := (dist_le_cellDiam H hu hcx).trans hdx
      rw [dist_eq_norm] at hd
      have : ‖u‖ - ‖c‖ ≤ ‖u - c‖ := norm_sub_norm_le _ _
      have hc' : ‖c‖ ≤ ρ := by
        rcases hc with h | h <;> simp only [sub_zero] at h <;> linarith
      linarith
    · unfold lemma34Layer
      rcases hc with h | h
      · have := abs_norm_sub_le_of_diam (H.isCompact_cell x).isBounded hdiam hcx h hu
        rw [radialBump_eq_one hw (this.trans hδw)]
        exact le_max_left _ _
      · have := abs_norm_sub_le_of_diam (H.isCompact_cell x).isBounded hdiam hcx h hu
        rw [radialBump_eq_one hw (this.trans hδw)]
        exact le_max_right _ _
  -- Lemma 3.3 on `D`
  have h33 := lemma33 H hDo hDb hO hdf hΛ0 hLip (annRef H 0 s ρ) (annRef_mem H 0 s ρ) hseg hLF0
    hLipF hMF hδD hbd hF h1 hg
  -- the integrals
  have hE : eucEnergy (logRad 0 ρ s) D = ENNReal.ofReal (2 * π / ℓ) :=
    (eucEnergy_logRad_annulus (z := 0) hs hsρ).2
  have hvol : volume D ≤ ENNReal.ofReal (π * ρ ^ 2) := volume_annulusSet_le 0 s ρ
  have hgint : (∫⁻ u in ball (0 : ℂ) ρ₁, ENNReal.ofReal (lemma34Layer s ρ w u)) ≤
      ENNReal.ofReal (8 * π * w * (s + 2 * w) + 8 * π * w * (ρ + 2 * w)) := by
    refine (setLIntegral_le_lintegral _ _).trans ?_
    calc ∫⁻ u, ENNReal.ofReal (lemma34Layer s ρ w u)
        ≤ ∫⁻ u, (ENNReal.ofReal (radialBump 0 s w u) + ENNReal.ofReal (radialBump 0 ρ w u)) := by
          refine lintegral_mono fun u => ?_
          unfold lemma34Layer
          rcases le_total (radialBump 0 s w u) (radialBump 0 ρ w u) with h | h
          · rw [max_eq_right h]; exact le_add_self
          · rw [max_eq_left h]; exact le_self_add
      _ = (∫⁻ u, ENNReal.ofReal (radialBump 0 s w u)) +
            ∫⁻ u, ENNReal.ofReal (radialBump 0 ρ w u) :=
          lintegral_add_left (ENNReal.measurable_ofReal.comp
            (continuous_radialBump 0 s hw).measurable) _
      _ ≤ ENNReal.ofReal (8 * π * w * (s + 2 * w)) + ENNReal.ofReal (8 * π * w * (ρ + 2 * w)) :=
          add_le_add (lintegral_radialBump_le 0 hs.le hw)
            (lintegral_radialBump_le 0 (hs.trans hsρ).le hw)
      _ = ENNReal.ofReal (8 * π * w * (s + 2 * w) + 8 * π * w * (ρ + 2 * w)) :=
          (ENNReal.ofReal_add (by positivity) (by positivity)).symm
  refine ⟨annTest H 0 s ρ, annTest_eq_one H ⟨0, H.zero_mem_root, mem_closedBall_self hs.le⟩,
    fun x hx => annTest_eq_zero_of_notMem H hsρ hx, ?_⟩
  have hEnn := energy_nonneg G (vFin H D) (logRad 0 ρ s ∘ annRef H 0 s ρ)
  refine (energy_annTest_le H hS).trans ?_
  rw [← ENNReal.ofReal_le_ofReal_iff (lemma34Bound_nonneg hs hsρ hδ0 hw.le hA hη)]
  refine h33.trans ?_
  rw [hE]
  unfold lemma34Bound
  have hℓpos' : 0 < Real.log (ρ / s) := hℓpos
  have hVg : 0 ≤ 8 * π * w * (s + 2 * w) + 8 * π * w * (ρ + 2 * w) := by positivity
  have hP : ENNReal.ofReal A * ENNReal.ofReal (2 * π / ℓ) + ENNReal.ofReal η ≤
      ENNReal.ofReal (A * (2 * π / ℓ) + η) :=
    ennreal_add_le_ofReal (by positivity) hη (ennreal_mul_le_ofReal hA le_rfl le_rfl) le_rfl
  have hT : ENNReal.ofReal A * volume D + ENNReal.ofReal η ≤ ENNReal.ofReal (A * (π * ρ ^ 2) + η) :=
    ennreal_add_le_ofReal (by positivity) hη (ennreal_mul_le_ofReal hA le_rfl hvol) le_rfl
  have hU : ENNReal.ofReal A * (∫⁻ u in ball (0 : ℂ) ρ₁, ENNReal.ofReal (lemma34Layer s ρ w u)) +
      ENNReal.ofReal η ≤
      ENNReal.ofReal (A * (8 * π * w * (s + 2 * w) + 8 * π * w * (ρ + 2 * w)) + η) :=
    ennreal_add_le_ofReal (by positivity) hη (ennreal_mul_le_ofReal hA le_rfl hgint) le_rfl
  have h3 : (3 : ℝ≥0∞) = ENNReal.ofReal 3 := by norm_num
  rw [h3]
  refine ennreal_add_le_ofReal (by positivity) (by positivity)
    (ennreal_mul_le_ofReal (by norm_num) le_rfl ?_)
    (ennreal_mul_le_ofReal (by positivity) le_rfl (ennreal_add_le_ofReal (by positivity)
      (by positivity) hT hU))
  refine ennreal_add_le_ofReal (by positivity) (by positivity)
    (ennreal_add_le_ofReal (by positivity) (by positivity) hP ?_) ?_
  · exact ennreal_mul_le_ofReal (by positivity) le_rfl hT
  · exact ennreal_mul_le_ofReal (by positivity) le_rfl hU

/-- **Conductance form of [18] Lemma 3.4 / Theorem 1.4** ([18], Details (c5)): on a connected
graph, under the hypotheses of `lemma34`, the effective conductance from the root `o` to the complement
of `V(B_ρ(0))` is at most `lemma34Bound s ρ δ w A η`. -/
theorem effCond_le_lemma34Bound (hconn : G.adj.Connected) {s ρ ρ₁ δ w A η : ℝ} (hs : 0 < s)
    (hsρ : s < ρ) (hδ0 : 0 ≤ δ) (h6 : 6 * δ ≤ s) (hδρ : δ < ρ - s) (hρ₁ : ρ + δ < ρ₁) (hw : 0 < w)
    (hδw : δ ≤ w) (hA : 0 ≤ A) (hη : 0 ≤ η) (h27 : CellDiamBound H ρ₁ δ)
    (hF : Prop210Bound H (annulusSet 0 s ρ) (fun u => ‖fderiv ℝ (logRad 0 ρ s) u‖ ^ 2) A η)
    (h1 : Prop210Bound H (annulusSet 0 s ρ) (fun _ => 1) A η)
    (hg : Prop210Bound H (ball 0 ρ₁) (lemma34Layer s ρ w) A η) :
    effCond G o (vFin H (ball 0 ρ)) ≤ lemma34Bound s ρ δ w A η := by
  obtain ⟨g, hgo, hg0, hgE⟩ := lemma34 H hs hsρ hδ0 h6 hδρ hρ₁ hw hδw hA hη h27 hF h1 hg
  have ho : o ∈ vFin H (ball 0 ρ) :=
    (mem_vFin H isBounded_ball).mpr ⟨0, H.zero_mem_root, mem_ball_self (hs.trans hsρ)⟩
  exact (effCond_le_energy G hconn ho hgo hg0).trans hgE

end MatedCRTHarmonic.GMS3
