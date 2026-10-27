import MatedCRTHarmonic.GMSMain.T16DModel
import MatedCRTHarmonic.GMSMain.TopoMain

/-!
# [18] Corollary 1.6: maximal length of the embedded edges under the Tutte embedding

Source: [18] Corollary 1.6 : "Define the Tutte embedding `Φ^ε` with
identity boundary data as above. If `D ⊂ B_ρ(0)` is simply connected, then there exists `ξ' = ξ'(ρ, γ) > 0` such
that with probability tending to 1 as `ε → 0`, `max_{{x,y} ∈ E G^ε(D)} |Φ^ε(x) − Φ^ε(y)| ≤ O_ε(ε^{ξ'})` (1.10)."
Proof of [18]: Theorem 1.5 for `f = Re, Im` (1-Lipschitz, `χ = 1`) and Lemma 2.7
(cells meeting `B_ρ(0)` have diameter `≤ ε^q`); adjacent cells intersect, so `|η(x) − η(y)| ≤ 2ε^q` on an edge; hence
`ξ' = q ξ(ρ, 1, γ)` and `O_ε`-constant `(A₀^{Re} + A₀^{Im}) 2^ξ`.

Statements follow the draft surface v5 (anchor
`matedCRT_tutte_edge_le_of_matingOfTrees`, with the local copies `IsTutteEmbedding`, `IsHarmonicExtension`, `cellAt`
of its definitions) for every real mesh `ε ∈ (0, 1)`, with a main form using
`IsConnected D ∧ IsConnected Dᶜ` (a domain with connected complement) in place of "simply connected" (for bounded
open `D` implied by simple connectivity,`isConnected_compl_of_simplyConnected`, which gives the literal
`SimplyConnectedSpace` form `corollary16_tendsto_simplyConnected_of_theorem15`).

* `norm_sub_le_of_holder_bounds` — the deterministic step, for any cell map, any Tutte embedding and any edge.
* `TutteEdgeBad`, `HolderBad` — the bad events of (1.10) and of Theorem 1.5's (1.9), exactly the complements of the
  good events of the draft anchors (`∃ h, (∃ solution) ∧ ∀ solution, bound`); `CellDiamBad` (Lemma 2.7) and
  `EmbeddingBad` (cells not a cellular embedding; null, `measure_embeddingBad`).
* `tutteEdgeBad_subset` — the bad event of (1.10) lies in the union of the two coordinate Hölder bad events, the
  Lemma 2.7 bad event and `EmbeddingBad`.
* **`corollary16_of_theorem15`** (quantitative (1.10)) and **`corollary16_tendsto_of_theorem15`** ((1.10) as printed,
  `Tendsto (ε ↦ P[bad]) (𝓝[>] 0) (𝓝 0)`, the body of the draft anchor) for every frozen coupling, from ONE hypothesis:
  [18] Theorem 1.5 in the shape of the draft anchor `matedCRT_holder_of_matingOfTrees` ( main form), to be
  discharged theorem.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric Topology
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMSMain.T16D

open MatedCRTHarmonic GMS3 Harmonic

/-! ### The deterministic step -/

/-- Points of two intersecting bounded sets are at distance at most the sum of the diameters. -/
theorem dist_le_diam_add_diam_of_inter {S T : Set ℂ} (hS : Bornology.IsBounded S) (hT : Bornology.IsBounded T)
    (hST : (S ∩ T).Nonempty) {a b : ℂ} (ha : a ∈ S) (hb : b ∈ T) : dist a b ≤ diam S + diam T := by
  obtain ⟨c, hcS, hcT⟩ := hST
  calc dist a b ≤ dist a c + dist c b := dist_triangle _ _ _
    _ ≤ diam S + diam T := add_le_add (dist_le_diam_of_mem hS ha hcS) (dist_le_diam_of_mem hT hcT hb)

/-- **Deterministic step of [18] Corollary 1.6.** Let `J` be a cell map of `G` with bounded cells and intersecting
cells at adjacent vertices, `p x ∈ J x` marked points, and `Φ : V → ℂ` any function whose two coordinates satisfy the
Hölder bound (1.9), `|Φ^i(x) − Φ^i(y)| ≤ A_i (ε ∨ |p x − p y|)^ξ`, on `V(D)`, where every cell has diameter `≤ δ`.
Then every edge with both ends in `V(D)` has `‖Φ(x) − Φ(y)‖ ≤ (A₁ + A₂) (ε ∨ 2δ)^ξ`. -/
theorem norm_sub_le_of_holder_bounds {V E : Type*} {G : LFMultigraph V E} {J : V → Set ℂ} {D : Set ℂ}
    {Φ : V → ℂ} {p : V → ℂ} (hp : ∀ x, p x ∈ J x) (hJb : ∀ x, Bornology.IsBounded (J x))
    (hinter : ∀ x y, G.adj.Adj x y → (J x ∩ J y).Nonempty) {ε δ ξ A₁ A₂ : ℝ} (hε : 0 ≤ ε) (hξ : 0 < ξ)
    (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂) (hdiam : ∀ x ∈ verticesMeeting J D, diam (J x) ≤ δ)
    (h₁ : ∀ x ∈ verticesMeeting J D, ∀ y ∈ verticesMeeting J D,
      |(Φ x).re - (Φ y).re| ≤ A₁ * max ε (dist (p x) (p y)) ^ ξ)
    (h₂ : ∀ x ∈ verticesMeeting J D, ∀ y ∈ verticesMeeting J D,
      |(Φ x).im - (Φ y).im| ≤ A₂ * max ε (dist (p x) (p y)) ^ ξ)
    {e : E} (hs : G.src e ∈ verticesMeeting J D) (ht : G.tgt e ∈ verticesMeeting J D) :
    ‖Φ (G.src e) - Φ (G.tgt e)‖ ≤ (A₁ + A₂) * max ε (2 * δ) ^ ξ := by
  have hbase : 0 ≤ max ε (2 * δ) := le_max_of_le_left hε
  have hRHS : 0 ≤ (A₁ + A₂) * max ε (2 * δ) ^ ξ :=
    mul_nonneg (add_nonneg hA₁ hA₂) (Real.rpow_nonneg hbase _)
  by_cases hloop : G.src e = G.tgt e
  · rw [hloop, sub_self, norm_zero]
    exact hRHS
  have hadj : G.adj.Adj (G.src e) (G.tgt e) := adj_of_edge G hloop
  have hpd : dist (p (G.src e)) (p (G.tgt e)) ≤ 2 * δ := by
    calc dist (p (G.src e)) (p (G.tgt e)) ≤ diam (J (G.src e)) + diam (J (G.tgt e)) :=
          dist_le_diam_add_diam_of_inter (hJb _) (hJb _) (hinter _ _ hadj) (hp _) (hp _)
      _ ≤ 2 * δ := by linarith [hdiam _ hs, hdiam _ ht]
  have hmono : max ε (dist (p (G.src e)) (p (G.tgt e))) ^ ξ ≤ max ε (2 * δ) ^ ξ :=
    Real.rpow_le_rpow (le_max_of_le_left hε) (max_le_max le_rfl hpd) hξ.le
  have hnorm := Complex.norm_le_abs_re_add_abs_im (Φ (G.src e) - Φ (G.tgt e))
  rw [Complex.sub_re, Complex.sub_im] at hnorm
  calc ‖Φ (G.src e) - Φ (G.tgt e)‖
      ≤ |(Φ (G.src e)).re - (Φ (G.tgt e)).re| + |(Φ (G.src e)).im - (Φ (G.tgt e)).im| := hnorm
    _ ≤ A₁ * max ε (dist (p (G.src e)) (p (G.tgt e))) ^ ξ +
          A₂ * max ε (dist (p (G.src e)) (p (G.tgt e))) ^ ξ :=
        add_le_add (h₁ _ hs _ ht) (h₂ _ hs _ ht)
    _ ≤ A₁ * max ε (2 * δ) ^ ξ + A₂ * max ε (2 * δ) ^ ξ :=
        add_le_add (mul_le_mul_of_nonneg_left hmono hA₁) (mul_le_mul_of_nonneg_left hmono hA₂)
    _ = (A₁ + A₂) * max ε (2 * δ) ^ ξ := by ring

/-- `Re` is `1`-Lipschitz, hence `1`-Hölder with exponent `1` on every set. -/
theorem holderOnWith_re (s : Set ℂ) : HolderOnWith 1 1 (fun z : ℂ => z.re) s := by
  refine HolderWith.holderOnWith (LipschitzWith.holderWith ?_) s
  refine LipschitzWith.of_dist_le_mul fun z w => ?_
  rw [NNReal.coe_one, one_mul, Real.dist_eq, ← Complex.sub_re, dist_eq_norm]
  exact Complex.abs_re_le_norm _

/-- `Im` is `1`-Lipschitz, hence `1`-Hölder with exponent `1` on every set. -/
theorem holderOnWith_im (s : Set ℂ) : HolderOnWith 1 1 (fun z : ℂ => z.im) s := by
  refine HolderWith.holderOnWith (LipschitzWith.holderWith ?_) s
  refine LipschitzWith.of_dist_le_mul fun z w => ?_
  rw [NNReal.coe_one, one_mul, Real.dist_eq, ← Complex.sub_im, dist_eq_norm]
  exact Complex.abs_im_le_norm _

/-! ### The bad events of the draft anchors -/

section Bundle

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}

/-- **The bad event of (1.10)** at mesh `ε` (the complement of the good event of the draft anchor
`matedCRT_tutte_edge_le_of_matingOfTrees`): it is not the case that `G^ε` is locally finite, a Tutte embedding with
identity boundary data exists, and every one of them has `‖Φ(x) − Φ(y)‖ ≤ K ε^{ξ'}` on every edge of `G^ε(Dom)`. -/
def TutteEdgeBad (bm : Ω → MatedCRT.Path2) (η : Ω → C(ℝ, ℂ)) (Dom : Set ℂ) (K ξ' ε : ℝ) : Set Ω :=
  {ω | ¬ ∃ h : MatedCRT.IsLocallyFinite ε (bm ω),
    (∃ Φ : ℤ → ℂ, IsTutteEmbedding (MatedCRT.graph ε (bm ω) h) (cellAt ε (η ω)) Dom Φ) ∧
    ∀ Φ : ℤ → ℂ, IsTutteEmbedding (MatedCRT.graph ε (bm ω) h) (cellAt ε (η ω)) Dom Φ →
      ∀ e : MatedCRT.Edge ε (bm ω),
        (MatedCRT.graph ε (bm ω) h).src e ∈ verticesMeeting (cellAt ε (η ω)) Dom →
        (MatedCRT.graph ε (bm ω) h).tgt e ∈ verticesMeeting (cellAt ε (η ω)) Dom →
          ‖Φ ((MatedCRT.graph ε (bm ω) h).src e) - Φ ((MatedCRT.graph ε (bm ω) h).tgt e)‖ ≤ K * ε ^ ξ'}

/-- **The bad event of (1.9)** at mesh `ε` (the complement of the good event of the draft anchor
`matedCRT_holder_of_matingOfTrees`) for boundary data `f`, constant `A₀` and exponent `ξ`. -/
def HolderBad (bm : Ω → MatedCRT.Path2) (η : Ω → C(ℝ, ℂ)) (Dom : Set ℂ) (f : ℂ → ℝ) (A₀ ξ ε : ℝ) : Set Ω :=
  {ω | ¬ ∃ h : MatedCRT.IsLocallyFinite ε (bm ω),
    (∃ g : ℤ → ℝ, IsHarmonicExtension (MatedCRT.graph ε (bm ω) h) (cellAt ε (η ω)) Dom f g) ∧
    ∀ g : ℤ → ℝ, IsHarmonicExtension (MatedCRT.graph ε (bm ω) h) (cellAt ε (η ω)) Dom f g →
      ∀ x ∈ verticesMeeting (cellAt ε (η ω)) Dom, ∀ y ∈ verticesMeeting (cellAt ε (η ω)) Dom,
        |g x - g y| ≤ A₀ * (max ε (dist (η ω (ε * x)) (η ω (ε * y)))) ^ ξ}

/-- The bad event of [18] Lemma 2.7 at mesh `ε` on `B_ρ(0)`. -/
def CellDiamBad (η : Ω → C(ℝ, ℂ)) (ρ q ε : ℝ) : Set Ω :=
  {ω | ∀ x : ℤ, (cellAt ε (η ω) x ∩ ball (0 : ℂ) ρ).Nonempty → diam (cellAt ε (η ω) x) ≤ ε ^ q}ᶜ

/-- The (null) event where the cells do not form a cellular embedding of a locally finite `G^ε`. -/
def EmbeddingBad (bm : Ω → MatedCRT.Path2) (η : Ω → C(ℝ, ℂ)) (ε : ℝ) : Set Ω :=
  {ω | ∃ h : MatedCRT.IsLocallyFinite ε (bm ω),
    ∃ H : CellularEmbedding (MatedCRT.graph ε (bm ω) h) 0, H.cell = cellAt ε (η ω)}ᶜ

omit [MeasurableSpace Ω] in
/-- **The bad event of (1.10) is covered by the bad events of its inputs** (deterministic, every `ω`): for `ε ∈ (0, 1]`,
`q ≤ 1` and `Dom ⊂ B_ρ(0)`, with `K = (A₁ + A₂) 2^ξ` and `ξ' = qξ`. -/
theorem tutteEdgeBad_subset {Dom : Set ℂ} {ρ q ξ A₁ A₂ ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hq1 : q ≤ 1)
    (hξ : 0 < ξ) (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂) (hDsub : Dom ⊆ ball (0 : ℂ) ρ) :
    TutteEdgeBad bm η Dom ((A₁ + A₂) * 2 ^ ξ) (q * ξ) ε ⊆
      HolderBad bm η Dom (fun z => z.re) A₁ ξ ε ∪ HolderBad bm η Dom (fun z => z.im) A₂ ξ ε ∪
        CellDiamBad η ρ q ε ∪ EmbeddingBad bm η ε := by
  intro ω hω
  by_contra hcon
  simp only [mem_union, not_or] at hcon
  obtain ⟨⟨⟨hre, him⟩, h27⟩, hemb⟩ := hcon
  simp only [HolderBad, CellDiamBad, EmbeddingBad, mem_compl_iff, mem_ofPred_eq, not_not] at hre him h27 hemb
  obtain ⟨h₁, ⟨g₁, hg₁⟩, hb₁⟩ := hre
  obtain ⟨h₂, ⟨g₂, hg₂⟩, hb₂⟩ := him
  obtain ⟨h₃, H, hH⟩ := hemb
  apply hω
  refine ⟨h₁, ⟨fun x => ⟨g₁ x, g₂ x⟩, hg₁, hg₂⟩, fun Φ hΦ e hs ht => ?_⟩
  have hdiam : ∀ x ∈ verticesMeeting (cellAt ε (η ω)) Dom, diam (cellAt ε (η ω) x) ≤ ε ^ q := by
    rintro x ⟨z, hz1, hz2⟩
    exact h27 x ⟨z, hz1, hDsub hz2⟩
  have hinter : ∀ x y, (MatedCRT.graph ε (bm ω) h₁).adj.Adj x y →
      (cellAt ε (η ω) x ∩ cellAt ε (η ω) y).Nonempty := by
    intro x y hxy
    rw [← hH]
    exact H.inter_of_adj x y hxy
  have hb := norm_sub_le_of_holder_bounds (G := MatedCRT.graph ε (bm ω) h₁) (J := cellAt ε (η ω))
    (p := fun x => η ω (ε * x)) (fun x => mem_cellAt_self hε.le (η ω) x)
    (fun x => (isCompact_Icc.image (η ω).continuous).isBounded) hinter hε.le hξ hA₁ hA₂ hdiam
    (hb₁ _ hΦ.1) (hb₂ _ hΦ.2) hs ht
  rw [max_mesh_rpow_eq hε hε1 hq1] at hb
  calc _ ≤ (A₁ + A₂) * (2 ^ ξ * ε ^ (q * ξ)) := hb
    _ = (A₁ + A₂) * 2 ^ ξ * ε ^ (q * ξ) := by ring

variable (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)

include D in
/-- The cells form a cellular embedding almost surely: `EmbeddingBad` is null at every positive mesh. -/
theorem measure_embeddingBad {ε : ℝ} (hε : 0 < ε) : P (EmbeddingBad bm η ε) = 0 :=
  ae_iff.mp (ae_cellularEmbeddingAt D hε)

/-- `ε^α' ≤ ε^α` on `(0, 1]` for `α ≤ α'`. -/
theorem rpow_le_rpow_of_le_one {ε α α' : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (h : α ≤ α') : ε ^ α' ≤ ε ^ α :=
  Real.rpow_le_rpow_of_exponent_ge hε hε1 h

include D in
/-- **[18] Corollary 1.6, quantitative form, for the embedded mated-CRT map of a frozen coupling, at every real mesh,
from [18] Theorem 1.5.** The hypothesis `h15` is [18] Theorem 1.5 for this coupling in the shape of the draft anchor
`matedCRT_holder_of_matingOfTrees` : `α = α(γ)` before
`ρ, χ`; `ξ = ξ(ρ, χ, γ)` before `D, f`; `A₀ = A₀(f, D, γ)`; with probability `≥ 1 − C ε^α` the function `f_ε` exists and
every one satisfies (1.9). Conclusion: there is `α > 0` such that for every `ρ ∈ (0, 1)` there is `ξ' = ξ'(ρ, γ) > 0`
such that for every open connected `D ⊂ B_ρ(0)` with `ℂ \ D` connected there are `C ≥ 0` (the `O_ε`-constant of (1.10)) and `K`
with `P[(1.10) fails with constant C] ≤ K ε^α` for every `ε ∈ (0, 1)`. -/
theorem corollary16_of_theorem15 (hstd : StandardBorelSpace Ω) (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (h15 : ∃ α : ℝ, 0 < α ∧ ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∀ χ : ℝ≥0, 0 < χ → ∃ ξ : ℝ, 0 < ξ ∧
      ∀ Dom : Set ℂ, IsOpen Dom → Dom ⊆ ball (0 : ℂ) ρ → IsConnected Dom → IsConnected Domᶜ →
      ∀ f : ℂ → ℝ, (∃ K : ℝ≥0, HolderOnWith K χ f (frontier Dom)) →
      ∃ A₀ : ℝ, 0 < A₀ ∧ ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε < 1 →
        P {ω | ¬ ∃ h : MatedCRT.IsLocallyFinite ε (bm ω),
          (∃ g : ℤ → ℝ, IsHarmonicExtension (MatedCRT.graph ε (bm ω) h) (cellAt ε (η ω)) Dom f g) ∧
          ∀ g : ℤ → ℝ, IsHarmonicExtension (MatedCRT.graph ε (bm ω) h) (cellAt ε (η ω)) Dom f g →
            ∀ x ∈ verticesMeeting (cellAt ε (η ω)) Dom, ∀ y ∈ verticesMeeting (cellAt ε (η ω)) Dom,
              |g x - g y| ≤ A₀ * (max ε (dist (η ω (ε * x)) (η ω (ε * y)))) ^ ξ} ≤
          ENNReal.ofReal (C * ε ^ α)) :
    ∃ α : ℝ, 0 < α ∧ ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∃ ξ' : ℝ, 0 < ξ' ∧
      ∀ Dom : Set ℂ, IsOpen Dom → Dom ⊆ ball (0 : ℂ) ρ → IsConnected Dom → IsConnected Domᶜ →
        ∃ C : ℝ, 0 ≤ C ∧ ∃ K : ℝ, ∀ ε : ℝ, 0 < ε → ε < 1 →
          P (TutteEdgeBad bm η Dom C ξ' ε) ≤ ENNReal.ofReal (K * ε ^ α) := by
  obtain ⟨α₁, hα₁, h15'⟩ := h15
  set q : ℝ := 1 / (2 + γ) ^ 2 with hqdef
  have hden : 4 < (2 + γ) ^ 2 := by nlinarith [hγ.1]
  have hq0 : 0 < q := by rw [hqdef]; positivity
  have hq' : q < 2 / (2 + γ) ^ 2 := by
    rw [hqdef]; exact div_lt_div_of_pos_right (by norm_num) (by linarith)
  have hq1 : q ≤ 1 := by
    rw [hqdef, div_le_one (by linarith)]; linarith
  have hL := GMSLemma27.lemma27Exponent_pos hγ.1 hq0 hq'
  set α₃ : ℝ := GMSLemma27.lemma27Exponent q γ / 2 with hα₃def
  have hα₃ : 0 < α₃ := by rw [hα₃def]; linarith
  refine ⟨min α₁ α₃, lt_min hα₁ hα₃, fun ρ hρ0 hρ1 => ?_⟩
  obtain ⟨ξ, hξ, hξD⟩ := h15' ρ hρ0 hρ1 1 one_pos
  obtain ⟨C₃, -, hC₃⟩ := lemma27_cellAt D hstd hγ hq0 hq' ⟨hρ0, hρ1⟩ (α := α₃) (by rw [hα₃def]; linarith)
  refine ⟨q * ξ, mul_pos hq0 hξ, fun Dom hDo hDsub hc hcc => ?_⟩
  obtain ⟨A₁, hA₁, C₁, hC₁⟩ := hξD Dom hDo hDsub hc hcc (fun z => z.re) ⟨1, holderOnWith_re _⟩
  obtain ⟨A₂, hA₂, C₂, hC₂⟩ := hξD Dom hDo hDsub hc hcc (fun z => z.im) ⟨1, holderOnWith_im _⟩
  refine ⟨(A₁ + A₂) * 2 ^ ξ, mul_nonneg (add_nonneg hA₁.le hA₂.le) (Real.rpow_nonneg zero_le_two _),
    |C₁| + |C₂| + |C₃|, fun ε hε hε1 => ?_⟩
  have hle : ∀ (C a : ℝ), min α₁ α₃ ≤ a →
      ENNReal.ofReal (C * ε ^ a) ≤ ENNReal.ofReal (|C| * ε ^ min α₁ α₃) :=
    fun C a ha => ENNReal.ofReal_le_ofReal ((mul_le_mul_of_nonneg_right (le_abs_self C)
      (Real.rpow_nonneg hε.le _)).trans (mul_le_mul_of_nonneg_left
        (rpow_le_rpow_of_le_one hε hε1.le ha) (abs_nonneg C)))
  calc P (TutteEdgeBad bm η Dom ((A₁ + A₂) * 2 ^ ξ) (q * ξ) ε)
      ≤ P (HolderBad bm η Dom (fun z => z.re) A₁ ξ ε ∪ HolderBad bm η Dom (fun z => z.im) A₂ ξ ε ∪
          CellDiamBad η ρ q ε ∪ EmbeddingBad bm η ε) :=
        measure_mono (tutteEdgeBad_subset hε hε1.le hq1 hξ hA₁.le hA₂.le hDsub)
    _ ≤ P (HolderBad bm η Dom (fun z => z.re) A₁ ξ ε) + P (HolderBad bm η Dom (fun z => z.im) A₂ ξ ε) +
          P (CellDiamBad η ρ q ε) + P (EmbeddingBad bm η ε) :=
        (measure_union_le _ _).trans (add_le_add ((measure_union_le _ _).trans
          (add_le_add (measure_union_le _ _) le_rfl)) le_rfl)
    _ ≤ ENNReal.ofReal (|C₁| * ε ^ min α₁ α₃) + ENNReal.ofReal (|C₂| * ε ^ min α₁ α₃) +
          ENNReal.ofReal (|C₃| * ε ^ min α₁ α₃) + 0 := by
        refine add_le_add (add_le_add (add_le_add ?_ ?_) ?_) (le_of_eq (measure_embeddingBad D hε))
        · exact (hC₁ ε hε hε1).trans (hle C₁ α₁ (min_le_left _ _))
        · exact (hC₂ ε hε hε1).trans (hle C₂ α₁ (min_le_left _ _))
        · exact (hC₃ ε ⟨hε, hε1⟩).trans (hle C₃ α₃ (min_le_right _ _))
    _ = ENNReal.ofReal ((|C₁| + |C₂| + |C₃|) * ε ^ min α₁ α₃) := by
        have hr := Real.rpow_nonneg hε.le (min α₁ α₃)
        rw [add_zero, ← ENNReal.ofReal_add (mul_nonneg (abs_nonneg _) hr) (mul_nonneg (abs_nonneg _) hr),
          ← ENNReal.ofReal_add (add_nonneg (mul_nonneg (abs_nonneg _) hr) (mul_nonneg (abs_nonneg _) hr))
            (mul_nonneg (abs_nonneg _) hr)]
        congr 1
        ring

include D in
/-- **[18] Corollary 1.6, (1.10) as printed** ("with probability tending to 1 as `ε → 0`"), for the embedded
mated-CRT map of a frozen coupling, at every real mesh, from [18] Theorem 1.5 (hypothesis `h15`, the shape of the
draft anchor `matedCRT_holder_of_matingOfTrees`, main form). The conclusion is the body of the draft anchor
`matedCRT_tutte_edge_le_of_matingOfTrees` ( main form): for every `ρ ∈ (0, 1)` there is `ξ' = ξ'(ρ, γ) > 0`
such that for every open connected `D ⊂ B_ρ(0)` with `ℂ \ D` connected there is `C` with: the probability that `G^ε` is locally
finite, the Tutte embedding of `G^ε(D)` exists and every one has `max_{{x,y} ∈ E(G^ε(D))} ‖Φ^ε(x) − Φ^ε(y)‖ ≤ C ε^{ξ'}`
tends to `1` as `ε → 0+` (its complement tends to `0`). -/
theorem corollary16_tendsto_of_theorem15 (hstd : StandardBorelSpace Ω) (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (h15 : ∃ α : ℝ, 0 < α ∧ ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∀ χ : ℝ≥0, 0 < χ → ∃ ξ : ℝ, 0 < ξ ∧
      ∀ Dom : Set ℂ, IsOpen Dom → Dom ⊆ ball (0 : ℂ) ρ → IsConnected Dom → IsConnected Domᶜ →
      ∀ f : ℂ → ℝ, (∃ K : ℝ≥0, HolderOnWith K χ f (frontier Dom)) →
      ∃ A₀ : ℝ, 0 < A₀ ∧ ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε < 1 →
        P {ω | ¬ ∃ h : MatedCRT.IsLocallyFinite ε (bm ω),
          (∃ g : ℤ → ℝ, IsHarmonicExtension (MatedCRT.graph ε (bm ω) h) (cellAt ε (η ω)) Dom f g) ∧
          ∀ g : ℤ → ℝ, IsHarmonicExtension (MatedCRT.graph ε (bm ω) h) (cellAt ε (η ω)) Dom f g →
            ∀ x ∈ verticesMeeting (cellAt ε (η ω)) Dom, ∀ y ∈ verticesMeeting (cellAt ε (η ω)) Dom,
              |g x - g y| ≤ A₀ * (max ε (dist (η ω (ε * x)) (η ω (ε * y)))) ^ ξ} ≤
          ENNReal.ofReal (C * ε ^ α)) :
    ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∃ ξ' : ℝ, 0 < ξ' ∧
      ∀ Dom : Set ℂ, IsOpen Dom → Dom ⊆ ball (0 : ℂ) ρ → IsConnected Dom → IsConnected Domᶜ →
      ∃ C : ℝ, Tendsto (fun ε : ℝ =>
        P {ω | ¬ ∃ h : MatedCRT.IsLocallyFinite ε (bm ω),
          (∃ Φ : ℤ → ℂ, IsTutteEmbedding (MatedCRT.graph ε (bm ω) h) (cellAt ε (η ω)) Dom Φ) ∧
          ∀ Φ : ℤ → ℂ, IsTutteEmbedding (MatedCRT.graph ε (bm ω) h) (cellAt ε (η ω)) Dom Φ →
            ∀ e : MatedCRT.Edge ε (bm ω),
              (MatedCRT.graph ε (bm ω) h).src e ∈ verticesMeeting (cellAt ε (η ω)) Dom →
              (MatedCRT.graph ε (bm ω) h).tgt e ∈ verticesMeeting (cellAt ε (η ω)) Dom →
                ‖Φ ((MatedCRT.graph ε (bm ω) h).src e) - Φ ((MatedCRT.graph ε (bm ω) h).tgt e)‖ ≤
                  C * ε ^ ξ'}) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨α, hα, h⟩ := corollary16_of_theorem15 D hstd hγ h15
  intro ρ hρ0 hρ1
  obtain ⟨ξ', hξ', h'⟩ := h ρ hρ0 hρ1
  refine ⟨ξ', hξ', fun Dom hDo hDsub hc hcc => ?_⟩
  obtain ⟨C, -, K, hK⟩ := h' Dom hDo hDsub hc hcc
  refine ⟨C, ?_⟩
  have hup : Tendsto (fun ε : ℝ => ENNReal.ofReal (K * ε ^ α)) (𝓝[>] 0) (𝓝 0) := by
    have h0 : Tendsto (fun ε : ℝ => ε ^ α) (𝓝[>] 0) (𝓝 0) :=
      (GMSLemma27.tendsto_rpow_nhdsGT_zero hα).mono_right nhdsWithin_le_nhds
    have := ENNReal.tendsto_ofReal (h0.const_mul K)
    rwa [mul_zero, ENNReal.ofReal_zero] at this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
    (Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 from one_pos)] with ε hε
  exact hK ε hε.1 hε.2

include D in
/-- **[18] Corollary 1.6, literal form** (the body of the draft anchor
`matedCRT_tutte_edge_le_of_matingOfTrees_simplyConnected`): as `corollary16_tendsto_of_theorem15` with the printed
hypothesis "`D ⊂ B_ρ(0)` is simply connected" (`SimplyConnectedSpace D`, open `D`), from the main form and
`isConnected_compl_of_simplyConnected` (a bounded simply connected open `D ⊂ ℂ` has connected complement; simple
connectivity also gives that `D` is nonempty and connected). The hypothesis `h15` is [18] Theorem 1.5, main form. -/
theorem corollary16_tendsto_simplyConnected_of_theorem15 (hstd : StandardBorelSpace Ω)
    (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (h15 : ∃ α : ℝ, 0 < α ∧ ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∀ χ : ℝ≥0, 0 < χ → ∃ ξ : ℝ, 0 < ξ ∧
      ∀ Dom : Set ℂ, IsOpen Dom → Dom ⊆ ball (0 : ℂ) ρ → IsConnected Dom → IsConnected Domᶜ →
      ∀ f : ℂ → ℝ, (∃ K : ℝ≥0, HolderOnWith K χ f (frontier Dom)) →
      ∃ A₀ : ℝ, 0 < A₀ ∧ ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε < 1 →
        P {ω | ¬ ∃ h : MatedCRT.IsLocallyFinite ε (bm ω),
          (∃ g : ℤ → ℝ, IsHarmonicExtension (MatedCRT.graph ε (bm ω) h) (cellAt ε (η ω)) Dom f g) ∧
          ∀ g : ℤ → ℝ, IsHarmonicExtension (MatedCRT.graph ε (bm ω) h) (cellAt ε (η ω)) Dom f g →
            ∀ x ∈ verticesMeeting (cellAt ε (η ω)) Dom, ∀ y ∈ verticesMeeting (cellAt ε (η ω)) Dom,
              |g x - g y| ≤ A₀ * (max ε (dist (η ω (ε * x)) (η ω (ε * y)))) ^ ξ} ≤
          ENNReal.ofReal (C * ε ^ α)) :
    ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∃ ξ' : ℝ, 0 < ξ' ∧
      ∀ Dom : Set ℂ, IsOpen Dom → Dom ⊆ ball (0 : ℂ) ρ → SimplyConnectedSpace Dom →
      ∃ C : ℝ, Tendsto (fun ε : ℝ =>
        P {ω | ¬ ∃ h : MatedCRT.IsLocallyFinite ε (bm ω),
          (∃ Φ : ℤ → ℂ, IsTutteEmbedding (MatedCRT.graph ε (bm ω) h) (cellAt ε (η ω)) Dom Φ) ∧
          ∀ Φ : ℤ → ℂ, IsTutteEmbedding (MatedCRT.graph ε (bm ω) h) (cellAt ε (η ω)) Dom Φ →
            ∀ e : MatedCRT.Edge ε (bm ω),
              (MatedCRT.graph ε (bm ω) h).src e ∈ verticesMeeting (cellAt ε (η ω)) Dom →
              (MatedCRT.graph ε (bm ω) h).tgt e ∈ verticesMeeting (cellAt ε (η ω)) Dom →
                ‖Φ ((MatedCRT.graph ε (bm ω) h).src e) - Φ ((MatedCRT.graph ε (bm ω) h).tgt e)‖ ≤
                  C * ε ^ ξ'}) (𝓝[>] 0) (𝓝 0) := by
  intro ρ hρ0 hρ1
  obtain ⟨ξ', hξ', h⟩ := corollary16_tendsto_of_theorem15 D hstd hγ h15 ρ hρ0 hρ1
  refine ⟨ξ', hξ', fun Dom hDo hDsub hsc => ?_⟩
  have : SimplyConnectedSpace Dom := hsc
  have hconnD : IsConnected Dom := isConnected_iff_connectedSpace.mpr inferInstance
  have hcc : IsConnected Domᶜ :=
    isConnected_compl_of_simplyConnected hDo (isBounded_ball.subset hDsub) hconnD.nonempty
  exact h Dom hDo hDsub hconnD hcc

end Bundle

end MatedCRTHarmonic.GMSMain.T16D
