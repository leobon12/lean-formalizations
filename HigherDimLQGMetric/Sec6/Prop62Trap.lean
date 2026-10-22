import HigherDimLQGMetric.Sec6.Prop62Arc
import HigherDimLQGMetric.Routing.Lemma41OuterResult

/-!
# [S] Proposition 6.2: the trap at one configuration of `𝒢`

Packet S6b. Source: MA3 Details (a) **D-6.2** (*Construction*, last two paragraphs: "For `κ ∈ 𝒢`,
Lemma 4.1 applies …, then (L4.2)"), blueprint Part A §6 (`prop:62`, step (7)), source l. 1078–1101.

For a configuration `κ` of the compact family `C(β)` with witness paths in all central boxes of a
connected mesh subgraph, S2b's Lemma 4.1′ (`lemma41_outer_routing_coordinates`) builds the routing
graph and the marked arcs, and S3's Lemma 4.2′ (`lemma42_trap`) gives one smooth discount `f`, a
length constant `c` and a closeness radius `ε` such that every configuration of `C(β)` that is
`ε`-close to `κ` on `Ā_{1,3}` satisfies the stability properties (i)–(iii) (`S6bStable`).

* `s6b_hreal`: the local finite-length realization hypothesis of S2b, from M2b's P2;
* `S6bStable`: the stability properties (i)–(iii) of MA3 D-6.2 (the conclusion of `lemma42_trap`);
* `s6b_trap_at`: the construction at one configuration.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Set Filter BoundedContinuousFunction unitInterval
open _root_.Topology
open HigherDimLFPP (Rd)
open scoped ENNReal
open LQGMetric.MetricGeometry

variable {d : ℕ}

/-- S2b's local realization hypothesis `hreal` for a coordinate of `C(β)` (M2b's P2). -/
theorem s6b_hreal (hd : 2 ≤ d) {c C : ℝ} {β : ConfigBounds d} {q : ConfigC d}
    (hq : q ∈ configCompactFamily hd c C β) (hq1 : IsCoordinate q.1) :
    ∀ {O : Set (configOuter d)}, IsOpen O → ∀ x ∈ O, ∃ a : ℝ, 0 < a ∧
      ∀ y ∈ O, q.1 (x, y) < a →
        ∃ P : Path (MetricFunSpace.pt q.1 hq1.metric x) (MetricFunSpace.pt q.1 hq1.metric y),
          (∀ r, LQGMetric.metricFunSpaceVal q.1 hq1.metric (P r) ∈ O) ∧ pathLength P ≠ ∞ := by
  intro O hO x hx
  obtain ⟨K₀, O', hK₀n, hK₀, hK₀O', hO', hO'c, hO'O, η, hη, hsep⟩ :=
    config_compact_collar hO hx
  obtain ⟨a', ha', H⟩ := configCompactFamily_outer_P2 hd c C β hK₀O' hO' hO'c η hη hsep
  have hpre : LQGMetric.metricFunSpaceVal q.1 hq1.metric ⁻¹' K₀ ∈
      𝓝 (MetricFunSpace.pt q.1 hq1.metric x) :=
    (hq1.val_continuous.tendsto (MetricFunSpace.pt q.1 hq1.metric x)) hK₀n
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.1 hpre
  refine ⟨min (a' / 4) ρ, lt_min (by positivity) hρ, fun y _ hxy => ?_⟩
  have hyK : y ∈ K₀ := by
    have hmem : MetricFunSpace.pt q.1 hq1.metric y ∈
        Metric.ball (MetricFunSpace.pt q.1 hq1.metric x) ρ := by
      rw [Metric.mem_ball, MetricFunSpace.dist_pt, hq1.metric.symm]
      exact hxy.trans_le (min_le_right _ _)
    exact hball hmem
  have hxK : x ∈ K₀ := mem_of_mem_nhds hK₀n
  obtain ⟨Q, hQO, hQ0, hQ1, hQlen⟩ := H q hq x hxK y hyK (hxy.trans_le (min_le_left _ _))
  let Γ : Path (MetricFunSpace.pt q.1 hq1.metric x) (MetricFunSpace.pt q.1 hq1.metric y) :=
    { toFun := fun t => MetricFunSpace.pt q.1 hq1.metric (Q t)
      continuous_toFun := hq1.pt_continuous.comp Q.continuous
      source' := by simp only [hQ0]
      target' := by simp only [hQ1] }
  refine ⟨Γ, fun t => hO'O (hQO t), ?_⟩
  have hext : (⇑Γ.extend : ℝ → MetricFunSpace q.1 hq1.metric) =
      MetricFunSpace.pt q.1 hq1.metric ∘ Set.IccExtend zero_le_one Q := rfl
  unfold pathLength
  rw [hext, ← curveLengthWith_metricFunSpace hq1.metric, hQlen]
  exact ENNReal.ofReal_ne_top

/-- The stability properties (i)–(iii) of MA3 D-6.2 for the discount `f` at the outer coordinate
pair `(ζ, ζ̃)` (the conclusion of `lemma42_trap` on its neighbourhood). -/
def S6bStable (ξ : ℝ) (V : Set (Rd d)) (f : Rd d → ℝ) (ε₀ b c c' acol : ℝ)
    (ζ ζt : configOuter d × configOuter d → ℝ) : Prop :=
  (∀ x y : configOuter d, (x : Rd d) ∈ closure V → (y : Rd d) ∈ closure V →
    weylDistOnWith (fun u v => ENNReal.ofReal (ζ (u, v)))
      (fun z : configOuter d => Real.exp (-(ξ * f z))) {z : configOuter d | (z : Rd d) ∈ ann 0 1 3}
      x y < ENNReal.ofReal (3 * ε₀)) ∧
  (∀ Q : ℝ → configOuter d, ContinuousOn Q (Icc 0 1) → (Q 0 : Rd d) ∈ closure V →
    (Q 1 : Rd d) ∈ closure V →
    weightedLengthWith (fun u v => ENNReal.ofReal (ζ (u, v)))
        (fun z : configOuter d => Real.exp (-(ξ * f z))) Q 0 1 =
      weylDistOnWith (fun u v => ENNReal.ofReal (ζ (u, v)))
        (fun z : configOuter d => Real.exp (-(ξ * f z))) univ (Q 0) (Q 1) →
    b ≤ ζ (Q 0, Q 1) →
    ∃ u v, 0 ≤ u ∧ u ≤ v ∧ v ≤ 1 ∧
      ENNReal.ofReal c ≤ weightedLengthWith (fun u v => ENNReal.ofReal (ζ (u, v)))
        (fun z : configOuter d => Real.exp (-(ξ * f z))) Q u v ∧
      ∃ S : ℝ → configOuter d, ContinuousOn S (Icc 0 1) ∧ S 0 = Q u ∧ S 1 = Q v ∧
        MapsTo S (Icc 0 1) {z : configOuter d | (z : Rd d) ∈ ann 0 1 3} ∧
        weightedLengthWith (fun u v => ENNReal.ofReal (ζt (u, v)))
            (fun z : configOuter d => Real.exp (-(ξ * f z))) S 0 1 ≤
          ENNReal.ofReal c' * weightedLengthWith (fun u v => ENNReal.ofReal (ζ (u, v)))
            (fun z : configOuter d => Real.exp (-(ξ * f z))) Q u v) ∧
  (∀ x y : configOuter d, (x : Rd d) ∈ closure V → (y : Rd d) ∈ frontier (ann (0 : Rd d) 1 3) →
    2 * acol < ζ (x, y))

/-- `ε`-closeness of two configurations on `Ā_{1,3}` (outer coordinates). -/
def S6bClose (q κ : ConfigC d) (ε : ℝ) : Prop :=
  ∀ x y : configOuter d, (x : Rd d) ∈ annCl (0 : Rd d) 1 3 → (y : Rd d) ∈ annCl (0 : Rd d) 1 3 →
    |q.1 (x, y) - κ.1 (x, y)| < ε ∧ |q.2.1 (x, y) - κ.2.1 (x, y)| < ε

/-- The central box of a tree edge. -/
def s6bBox {δ : ℝ} {T : SimpleGraph (Topology.meshVertices δ (Metric.sphere (0 : Rd d) 2))}
    (e : T.edgeSet) : Set (Rd d) :=
  centralBox δ (Topology.latticePoint δ (lemma41_meshLeft e).1)
    (Topology.latticePoint δ (lemma41_meshRight e).1)

/-- **The trap at one configuration** (MA3 D-6.2, construction, for `κ ∈ 𝒢`). -/
theorem s6b_trap_at (hd : 3 ≤ d) {ξ : ℝ} (hξ : 0 < ξ) {cs Cs : ℝ} (hcs : 0 < cs) (hCs : 0 < Cs)
    {β : ConfigBounds d} {κ : ConfigC d}
    (hκ : κ ∈ configCompactFamily (by omega : 2 ≤ d) cs Cs β)
    {δ : ℝ} (hδ : 0 < δ) (hsmall : δ ≤ 1 / (4 * Real.sqrt d))
    {T : SimpleGraph (Topology.meshVertices δ (Metric.sphere (0 : Rd d) 2))}
    (hT : T ≤ Topology.meshGraph δ (Metric.sphere (0 : Rd d) 2)) (hTconn : T.Connected)
    {A a₁ c₂ c₃ c' : ℝ} (ha₁ : 0 < a₁) (hc₂ : 0 ≤ c₂) (hc₂₃ : c₂ < c₃) (hc₃c' : c₃ < c')
    (hwit : ∀ e : T.edgeSet, s6bWitness κ (s6bBox e) A a₁ c₂)
    {a b ε₀ : ℝ}
    (hcol : ∀ x y : configOuter d, (x : Rd d) ∈ closure (meshCollector d δ) →
      (y : Rd d) ∈ frontier (ann (0 : Rd d) 1 3) → 4 * a ≤ κ.1 (x, y))
    (hb : 0 < b) (hε₀ : 0 < ε₀) (hε₀b : ε₀ < Real.exp (-ξ) * b / 200) (hε₀col : ε₀ < a / 12)
    (hstar : ∀ v : Topology.meshVertices δ (Metric.sphere (0 : Rd d) 2),
      ∀ x y : configOuter d, (x : Rd d) ∈ meshStar δ v.1 → (y : Rd d) ∈ meshStar δ v.1 →
        κ.1 (x, y) < b / 8)
    (haccess : ∀ x : configOuter d, (x : Rd d) ∈ closure (meshCollector d δ) →
      ∃ P : ℝ → configOuter d, ContinuousOn P (Icc 0 1) ∧ P 0 = x ∧
        (∃ v : Topology.meshVertices δ (Metric.sphere (0 : Rd d) 2),
          P 1 = lemma41_outerPoint (by omega : 1 ≤ d) hδ hsmall v) ∧
        curveLengthWith (fun u v => ENNReal.ofReal (κ.1 (u, v))) P 0 1 ≤ ENNReal.ofReal ε₀) :
    ∃ f : Rd d → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f ∧ HasCompactSupport f ∧
      tsupport f ⊆ ann (0 : Rd d) 1 3 ∧ (∀ x, 0 ≤ f x) ∧
      (∀ x, 0 < f x ↔ x ∈ meshCollector d δ) ∧
      ∃ c ε : ℝ, 0 < c ∧ 0 < ε ∧
        ∀ q ∈ configCompactFamily (by omega : 2 ≤ d) cs Cs β, S6bClose q κ ε →
          S6bStable ξ (meshCollector d δ) f ε₀ b c c' a q.1 q.2.1 := by
  classical
  have hd2 : 2 ≤ d := by omega
  have hd1 : 1 ≤ d := by omega
  have : Fintype (Topology.meshVertices δ (Metric.sphere (0 : Rd d) 2)) :=
    (routingMesh_finite hδ).fintype
  set ζ : configOuter d × configOuter d → ℝ := ⇑κ.1 with hζ_def
  set ζt : configOuter d × configOuter d → ℝ := ⇑κ.2.1 with hζt_def
  have hζ : IsCoordinate ζ := (configCompactFamily_outer_P1 hd2 cs Cs β hκ).1
  have hζt : IsCoordinate ζt := (configCompactFamily_outer_tilde_P1 hd2 cs Cs β hκ).1
  have hcmp := (configCompactFamily_P3 hd2 hcs hCs β hκ).1
  -- simple favourable arcs in the central boxes
  choose γ hγc hγi hγB hγfin hγsep hγrat using fun e : T.edgeSet =>
    s6b_simpleArc_of_witness (q := κ) hζ hζt hcs (fun x y => (hcmp x y).1) ha₁ (hwit e)
  -- Lemma 4.1′
  obtain ⟨R⟩ := lemma41_outer_routing_coordinates hd hδ hsmall hT hTconn ζ hζ
    (s6b_hreal hd2 hκ hζ) ζt hζt γ hγc hγi (fun e r hr => hγB e r hr) hγfin ha₁ hc₂₃ hγsep
    hγrat
  have hc₃ : 0 ≤ c₃ := hc₂.trans hc₂₃.le
  -- Lemma 4.2′
  have hAU : annCl (0 : Rd d) 1 3 ⊆ configOuter d := trap_annCl_subset_ann_half_five
  have hdiam : ∀ v : Topology.meshVertices δ (Metric.sphere (0 : Rd d) 2),
      ∀ x ∈ lemma41_outerMeshStar ζ hζ v, ∀ y ∈ lemma41_outerMeshStar ζ hζ v,
        dist x y < b / 8 := by
    rintro v _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [MetricFunSpace.dist_pt]
    exact hstar v x y hx hy
  obtain ⟨f, hfs, hfc, hft, hf0, hfV, c, ĉ, ηs, hc, -, -, -, -, -, ε, hε, hstab⟩ :=
    lemma42_trap (U := configOuter d) (V := meshCollector d δ) hξ configOuter_isOpen hAU
      (isOpen_meshCollector d δ) (closure_meshCollector_subset_ann_one_three hδ hsmall)
      (s6bFam hd2 cs Cs β) (s6bFam_coord hd2 cs Cs β) (s6bFam_mod hd2 cs Cs β)
      (s6bFam_loc hd2 cs Cs β) hζ (s6b_mem_fam hd2 hκ) hCs (fun x y => (hcmp x y).2)
      hcol hb hε₀ hε₀b hε₀col R.K R.graph
      (fun q hq => by
        obtain ⟨x, hx, rfl⟩ := R.collector hq
        exact hx)
      R.σ R.σcontinuous (fun e t ht => R.σK e ⟨t, ht, rfl⟩) hc₃ hc₃c' (by positivity : 0 < a₁ / 2)
      (fun e => by
        have h := (R.σshort e).le
        refine h.trans_eq ?_
        rw [ENNReal.ofReal_mul hc₃, edist_dist])
      (fun e => (R.σseparated e).le)
      (fun Tl hTl p q hp hq hpq Q hQK hQ0 ℓ hℓ0 hℓT hQℓ hunit =>
        R.forcing_shortcut hb hdiam hTl p q hp hq hpq Q hQK hQ0 ℓ hℓ0 hℓT hQℓ hunit)
      (fun x hx => by
        obtain ⟨P, hPc, hP0, ⟨v, hP1⟩, hPlen⟩ := haccess x hx
        refine ⟨P, hPc, hP0, ?_, hPlen⟩
        rw [hP1]
        exact R.vertex v)
  refine ⟨f, hfs, hfc, hft, hf0, hfV, c, ε, hc, hε, fun q hq hclose => ?_⟩
  have h := hstab (⇑q.1, ⇑q.2.1) (s6b_mem_fam hd2 hq) hclose
  unfold S6bStable
  exact h

end HigherDimLQGMetric
