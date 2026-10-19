import HigherDimLFPP.Upper.BadRecordMean
import LQGDimension.LFPP.ChainUnionAux

/-!
# The chain union bound: HA3 D7 (Claim and Counting)

Source: `source/higher-dimensional-lfpp-limit.pdf`, §4.4, (4.20)–(4.23), as corrected by the
planning audit HA3 (`planning/audits/HA3-section-4.md`), Details D7 ("Claim", "Counting"), with
the fixes F1 (records carry the chord-length constraints) and F8 (no measurability of uncountable
suprema is needed: finite subfamilies, continuity from below, outer measures).

* **Separability** (`exists_dense_seq_config`, 2D `ChainUnion.exists_dense_seq_config` with `ℂ`
  replaced by `ℝ^d`): every family of configurations with nondegenerate polygons contains a
  sequence along which the record variables of every continuous field are dense; this uses the
  continuity of `c ↦ ∫ φ dν_{P}` in the vertices (`continuousAt_cfgVal_ofFn`).
* **One chain record** (`chain_bound_finite`, `chain_bound_family`): for finite product
  subfamilies, `max Σ = Σ max` (`ChainUnion.iSup_piFinset_sum`), the expected maxima are summed,
  and the white-noise Chernoff bound (`whiteNoise_measure_lt_iSup_le`) applies with the variance
  bound of the chain; then continuity from below over a dense sequence.
* **The Claim of D7** (`chainRecord_event_le`): with the weights
  `w_g(k) = exp(t(b + 1 - τk) + (π²/8) t² C_V √(k+1))` and
  `w_b = exp(t(C_bad - a₀/δ²) + (π²/8) t² C'_V/δ)`,
  `P(∃ c_i ∈ Φ(ρ_i): Σ_i (Y_i(c_i) - cost(ρ_i)) > T) ≤ e^{-tT} Π_i w(ρ_i)`, using
  `(1 - τ)(k + 1) - k ≤ 1 - τk`.
* **Counting** (`measure_chainUnion_le`): summing over the chain records of the finite record set
  of lengths `l ≤ M` (P-U2's `sum_chain_weight_le_recSet`), the exceptional event has outer
  probability `≤ e^{-tT₀} (1 + Z_g + Z_b)^M`; with `T₀ = (M/t)(log(1 + Z_g + Z_b) + 2)` this is
  `e^{-2M}` (`measure_exceptional_le`).

The simultaneity over all admissible paths and the target statement (packet P-U3 T3) are in
`HigherDimLFPP.Upper.ChainSimultaneity`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace

namespace HigherDimLFPP.Upper

attribute [local instance] isFiniteMeasure_polyMeasure

/-! ## Continuity of record variables in the vertices -/

section Continuity

variable {d : ℕ}

/-- Sum of a function over the edges of a vertex list. -/
def edgeSum (g : Rd d × Rd d → ℝ) (z : List (Rd d)) : ℝ := ((edges z).map g).sum

theorem edges_ofFn_succ {n : ℕ} (a : Fin (n + 1) → Rd d) :
    edges (List.ofFn a) = List.ofFn (fun i : Fin n => (a i.castSucc, a i.succ)) := by
  apply List.ext_getElem
  · simp [edges]
  · intro i h1 h2
    simp only [edges, List.getElem_zip, List.getElem_tail, List.getElem_ofFn]
    rfl

theorem continuous_edgeSum_ofFn {g : Rd d × Rd d → ℝ} (hg : Continuous g) (n : ℕ) :
    Continuous fun a : Fin n → Rd d => edgeSum g (List.ofFn a) := by
  cases n with
  | zero =>
    simp only [edgeSum, List.ofFn_zero, edges, List.tail_nil, List.zip_nil_left, List.map_nil,
      List.sum_nil]
    exact continuous_const
  | succ n =>
    simp only [edgeSum, edges_ofFn_succ, List.map_ofFn, List.sum_ofFn]
    refine continuous_finsetSum _ fun i _ => ?_
    exact hg.comp ((continuous_apply _).prodMk (continuous_apply _))

theorem continuous_segAvg_pair {φ : Rd d → ℝ} (hφ : Continuous φ) :
    Continuous fun p : Rd d × Rd d => segAvg φ p.1 p.2 := by
  unfold segAvg
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  exact hφ.comp (by fun_prop)

/-- Integrals against weighted list sums of segment measures. -/
theorem integral_listSum_segMeasure {φ : Rd d → ℝ} (hφ : Continuous φ) {S : ℝ} (hS : 0 ≤ S)
    (L : List (Rd d × Rd d)) :
    Integrable φ ((L.map fun e => ENNReal.ofReal (‖e.2 - e.1‖ / S) • segMeasure e.1 e.2).sum) ∧
    ∫ w, φ w ∂((L.map fun e => ENNReal.ofReal (‖e.2 - e.1‖ / S) • segMeasure e.1 e.2).sum) =
      (L.map fun e => ‖e.2 - e.1‖ / S * segAvg φ e.1 e.2).sum := by
  induction L with
  | nil => simp
  | cons e L ih =>
    simp only [List.map_cons, List.sum_cons]
    have h1 : Integrable φ (ENNReal.ofReal (‖e.2 - e.1‖ / S) • segMeasure e.1 e.2) :=
      (integrable_segMeasure hφ _ _).smul_measure ENNReal.ofReal_ne_top
    refine ⟨h1.add_measure ih.1, ?_⟩
    rw [integral_add_measure h1 ih.1, ih.2, integral_smul_measure, integral_segMeasure hφ,
      ENNReal.toReal_ofReal (by positivity), smul_eq_mul]

theorem polyLen_nonneg (z : List (Rd d)) : 0 ≤ polyLen z := by
  refine List.sum_nonneg fun x hx => ?_
  obtain ⟨e, -, rfl⟩ := List.mem_map.1 hx
  exact norm_nonneg _

/-- `⟨φ, ν_P⟩ = Σ_e |e| ⟨φ, ν_e⟩ / len P`. -/
theorem integral_polyMeasure_eq {φ : Rd d → ℝ} (hφ : Continuous φ) (z : List (Rd d)) :
    ∫ w, φ w ∂(polyMeasure z) =
      edgeSum (fun e => ‖e.2 - e.1‖ * segAvg φ e.1 e.2) z / polyLen z := by
  rw [polyMeasure, (integral_listSum_segMeasure hφ (polyLen_nonneg z) (edges z)).2, edgeSum,
    div_eq_mul_inv, ← List.sum_map_mul_right]
  congr 1
  apply List.map_congr_left
  intro e _
  ring

/-- `c ↦ ⟨φ, ν_P⟩` is continuous in the vertices at nondegenerate polygons. -/
theorem continuousAt_integral_polyMeasure_ofFn {φ : Rd d → ℝ} (hφ : Continuous φ) {n : ℕ}
    (a : Fin n → Rd d) (ha : 0 < polyLen (List.ofFn a)) :
    ContinuousAt (fun b : Fin n → Rd d => ∫ w, φ w ∂(polyMeasure (List.ofFn b))) a := by
  simp_rw [integral_polyMeasure_eq hφ]
  refine ContinuousAt.div ?_ ?_ ha.ne'
  · exact (continuous_edgeSum_ofFn ((continuous_norm.comp (continuous_snd.sub continuous_fst)).mul
      (continuous_segAvg_pair hφ)) n).continuousAt
  · exact (continuous_edgeSum_ofFn (continuous_norm.comp (continuous_snd.sub continuous_fst))
      n).continuousAt

theorem continuousAt_cfgVal_ofFn {φ : Rd d → ℝ} (hφ : Continuous φ) (δ : ℝ) {n₁ n₂ : ℕ}
    (p : (Fin n₁ → Rd d) × (Fin n₂ → Rd d)) (h₁ : 0 < polyLen (List.ofFn p.1))
    (h₂ : 0 < polyLen (List.ofFn p.2)) :
    ContinuousAt (fun q : (Fin n₁ → Rd d) × (Fin n₂ → Rd d) =>
      cfgVal δ φ (List.ofFn q.1, List.ofFn q.2)) p := by
  unfold cfgVal
  have c1 := (continuousAt_integral_polyMeasure_ofFn hφ p.1 h₁).comp continuous_fst.continuousAt
  have c2 := (continuousAt_integral_polyMeasure_ofFn hφ p.2 h₂).comp continuous_snd.continuousAt
  exact continuousAt_const.mul (c1.sub c2)

/-- **Separability of record families** (2D `ChainUnion.exists_dense_seq_config`): a family of
configurations with nondegenerate polygons contains a sequence which is dense for the values of
`cfgVal δ φ`, simultaneously for all continuous `φ` and all `δ`. -/
theorem exists_dense_seq_config (S : Set (Config d)) (hS : S.Nonempty)
    (hpos : ∀ c ∈ S, 0 < polyLen c.1 ∧ 0 < polyLen c.2) :
    ∃ e : ℕ → Config d, (∀ j, e j ∈ S) ∧ ∀ c ∈ S, ∀ φ : Rd d → ℝ, Continuous φ → ∀ δ : ℝ,
      ∀ η > 0, ∃ j, |cfgVal δ φ (e j) - cfgVal δ φ c| < η := by
  let T : ∀ n₁ n₂ : ℕ, Set ((Fin n₁ → Rd d) × (Fin n₂ → Rd d)) := fun n₁ n₂ =>
    {p | (List.ofFn p.1, List.ofFn p.2) ∈ S}
  have hsep : ∀ n₁ n₂, ∃ s : Set (T n₁ n₂), s.Countable ∧ Dense s := fun n₁ n₂ =>
    TopologicalSpace.exists_countable_dense (T n₁ n₂)
  choose s hsc hsd using hsep
  let emb : ∀ n₁ n₂, T n₁ n₂ → Config d := fun n₁ n₂ q => (List.ofFn q.1.1, List.ofFn q.1.2)
  let D : Set (Config d) := ⋃ n₁, ⋃ n₂, emb n₁ n₂ '' s n₁ n₂
  have hDS : D ⊆ S := by
    intro x hx
    simp only [D, mem_iUnion, mem_image] at hx
    obtain ⟨n₁, n₂, q, _, rfl⟩ := hx
    exact q.2
  have hDc : D.Countable :=
    countable_iUnion fun n₁ => countable_iUnion fun n₂ => (hsc n₁ n₂).image _
  have happrox : ∀ c ∈ S, ∀ φ : Rd d → ℝ, Continuous φ → ∀ δ : ℝ,
      ∀ η > 0, ∃ x ∈ D, |cfgVal δ φ x - cfgVal δ φ c| < η := by
    intro c hc φ hφ δ η hη
    set n₁ := c.1.length
    set n₂ := c.2.length
    obtain ⟨p, hpc⟩ : ∃ p : (Fin n₁ → Rd d) × (Fin n₂ → Rd d),
        (List.ofFn p.1, List.ofFn p.2) = c :=
      ⟨(c.1.get, c.2.get), by simp only [List.ofFn_get]⟩
    have hpT : p ∈ T n₁ n₂ := by
      show (List.ofFn p.1, List.ofFn p.2) ∈ S
      rw [hpc]; exact hc
    have hp1 : List.ofFn p.1 = c.1 := congrArg Prod.fst hpc
    have hp2 : List.ofFn p.2 = c.2 := congrArg Prod.snd hpc
    have h₁ : 0 < polyLen (List.ofFn p.1) := by rw [hp1]; exact (hpos c hc).1
    have h₂ : 0 < polyLen (List.ofFn p.2) := by rw [hp2]; exact (hpos c hc).2
    have hcont := continuousAt_cfgVal_ofFn hφ δ p h₁ h₂
    have hcont' : ContinuousAt (fun q : T n₁ n₂ =>
        cfgVal δ φ (List.ofFn q.1.1, List.ofFn q.1.2)) ⟨p, hpT⟩ :=
      ContinuousAt.comp (g := fun q : (Fin n₁ → Rd d) × (Fin n₂ → Rd d) =>
        cfgVal δ φ (List.ofFn q.1, List.ofFn q.2)) (f := fun q : T n₁ n₂ => q.1)
        (x := ⟨p, hpT⟩) hcont continuous_subtype_val.continuousAt
    have hU := hcont'.preimage_mem_nhds (Metric.ball_mem_nhds _ hη)
    have hcl : (⟨p, hpT⟩ : T n₁ n₂) ∈ closure (s n₁ n₂) := by
      rw [(hsd n₁ n₂).closure_eq]; exact mem_univ _
    obtain ⟨q, hqU, hqs⟩ := mem_closure_iff_nhds.1 hcl _ hU
    refine ⟨emb n₁ n₂ q, ?_, ?_⟩
    · simp only [D, mem_iUnion, mem_image]
      exact ⟨n₁, n₂, q, hqs, rfl⟩
    · have := hqU
      simp only [mem_preimage, Metric.mem_ball, Real.dist_eq] at this
      rw [hpc] at this
      exact this
  obtain ⟨c₀, hc₀⟩ := hS
  have hDne : D.Nonempty := by
    obtain ⟨x, hx, _⟩ := happrox c₀ hc₀ (fun _ => 0) continuous_const 1 1 one_pos
    exact ⟨x, hx⟩
  obtain ⟨e, he⟩ := hDc.exists_eq_range hDne
  refine ⟨e, fun j => hDS (he ▸ mem_range_self j), ?_⟩
  intro c hc φ hφ δ η hη
  obtain ⟨x, hx, hxη⟩ := happrox c hc φ hφ δ η hη
  rw [he] at hx
  obtain ⟨j, rfl⟩ := hx
  exact ⟨j, hxη⟩

end Continuity

/-! ## The Chernoff bound for one chain record -/

section Chain

variable {d : ℕ} {κ : Rd d → ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {W : WN d → Ω → ℝ}

/-- One chain record, finite subfamilies: the Chernoff bound for the maximum over the product
(2D `ChainUnion.chain_bound_finite`). -/
theorem chain_bound_finite (hκ : IsLFPPKernel κ) (hW : IsWhiteNoise P W) {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) {H : Rd d → Ω → ℝ} (hH : IsBandVersion P W κ a b H) (δ : ℝ) {l : ℕ}
    (G : Fin l → Finset (Config d)) (hGne : ∀ i, (G i).Nonempty) (m : Fin l → ℝ) (V : ℝ)
    (hmean : ∀ i, ∫ ω, (⨆ c : G i, cfgVal δ (fun z => H z ω) c) ∂P ≤ m i)
    (hvar : ∀ c : Fin l → Config d, (∀ i, c i ∈ G i) → ‖∑ i, cfgVec κ a b δ (c i)‖ ^ 2 ≤ V)
    (β t : ℝ) (ht : 0 ≤ t) :
    P {ω | β < ⨆ c : Fintype.piFinset G,
        ∑ i, cfgVal δ (fun z => H z ω) ((c : Fin l → Config d) i)} ≤
      ENNReal.ofReal (Real.exp (-t * β + t * ∑ i, m i + Real.pi ^ 2 / 8 * t ^ 2 * V)) := by
  have := hW.isProbabilityMeasure
  set F := Fintype.piFinset G with hF
  have hFne : F.Nonempty := Fintype.piFinset_nonempty.2 hGne
  set v : (Fin l → Config d) → WN d := fun c => ∑ i, cfgVec κ a b δ (c i) with hv
  have hall : ∀ᵐ ω ∂P, ∀ c : F,
      ∑ i, cfgVal δ (fun z => H z ω) ((c : Fin l → Config d) i) = W (v c) ω + 0 := by
    refine ae_all_iff.2 fun c => ?_
    filter_upwards [sum_cfgVal_ae_eq hκ hW ha hab hH δ (c : Fin l → Config d)] with ω hω
    rw [add_zero]
    exact hω
  have hset : P {ω | β < ⨆ c : F, ∑ i, cfgVal δ (fun z => H z ω) ((c : Fin l → Config d) i)} =
      P {ω | β < ⨆ c : F, W (v c) ω + 0} := by
    refine measure_congr ?_
    filter_upwards [hall] with ω hω
    simp only [hω]
  have hint : ∫ ω, (⨆ c : F, W (v c) ω + 0) ∂P =
      ∫ ω, (⨆ c : F, ∑ i, cfgVal δ (fun z => H z ω) ((c : Fin l → Config d) i)) ∂P :=
    integral_congr_ae (hall.mono fun ω hω => by simp only [hω])
  rw [hset]
  refine (whiteNoise_measure_lt_iSup_le hW hFne v (fun _ => 0) V
    (fun c hc => hvar c (Fintype.mem_piFinset.1 hc)) β t ht).trans ?_
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
  have hsup : ∀ ω, (⨆ c : F, ∑ i, cfgVal δ (fun z => H z ω) ((c : Fin l → Config d) i)) =
      ∑ i, ⨆ c : G i, cfgVal δ (fun z => H z ω) c := fun ω =>
    LQGDimension.ChainUnion.iSup_piFinset_sum G hGne (fun i c => cfgVal δ (fun z => H z ω) c)
  have hmean' : ∫ ω, (⨆ c : F, W (v c) ω + 0) ∂P ≤ ∑ i, m i := by
    rw [hint]
    simp_rw [hsup]
    rw [integral_finsetSum _ fun i _ => integrable_iSup_cfgVal hκ hW ha hab hH δ (hGne i)]
    exact Finset.sum_le_sum fun i _ => hmean i
  nlinarith [mul_le_mul_of_nonneg_left hmean' ht]

/-- One chain record, full (possibly infinite) families: separability through a dense sequence
and continuity from below of the outer measure (2D `ChainUnion.chain_bound_family`; HA3 F8). -/
theorem chain_bound_family (hκ : IsLFPPKernel κ) (hW : IsWhiteNoise P W) {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) {H : Rd d → Ω → ℝ} (hH : IsBandVersion P W κ a b H) (δ : ℝ) {l : ℕ}
    (S : Fin l → Set (Config d)) (hpos : ∀ i, ∀ c ∈ S i, 0 < polyLen c.1 ∧ 0 < polyLen c.2)
    (m : Fin l → ℝ) (V : ℝ)
    (hmean : ∀ i, ∀ F : Finset (Config d), F.Nonempty → ↑F ⊆ S i →
      ∫ ω, (⨆ c : F, cfgVal δ (fun z => H z ω) c) ∂P ≤ m i)
    (hvar : ∀ c : Fin l → Config d, (∀ i, c i ∈ S i) → ‖∑ i, cfgVec κ a b δ (c i)‖ ^ 2 ≤ V)
    (β t : ℝ) (ht : 0 ≤ t) :
    P {ω | ∃ c : Fin l → Config d, (∀ i, c i ∈ S i) ∧
        β < ∑ i, cfgVal δ (fun z => H z ω) (c i)} ≤
      ENNReal.ofReal (Real.exp (-t * β + t * ∑ i, m i + Real.pi ^ 2 / 8 * t ^ 2 * V)) := by
  by_cases hne : ∀ i, (S i).Nonempty
  swap
  · obtain ⟨i, hi⟩ := not_forall.1 hne
    refine le_trans (measure_mono (t := ∅) ?_) (by simp)
    rintro ω ⟨c, hc, -⟩
    exact hi ⟨c i, hc i⟩
  choose e he happ using fun i => exists_dense_seq_config (S i) (hne i) (hpos i)
  let G : ℕ → Fin l → Finset (Config d) := fun N i => (Finset.range (N + 1)).image (e i)
  have hGsub : ∀ N i, ↑(G N i) ⊆ S i := by
    intro N i x hx
    simp only [G, Finset.coe_image, mem_image, Finset.mem_coe] at hx
    obtain ⟨j, _, rfl⟩ := hx
    exact he i j
  have hGne : ∀ N i, (G N i).Nonempty := fun N i =>
    ⟨e i 0, Finset.mem_image_of_mem _ (by simp)⟩
  let A : ℕ → Set Ω := fun N => {ω | ∃ c : Fin l → Config d, (∀ i, c i ∈ G N i) ∧
    β < ∑ i, cfgVal δ (fun z => H z ω) (c i)}
  have hAmono : Monotone A := by
    intro N N' hNN' ω hω
    obtain ⟨c, hc, hlt⟩ := hω
    refine ⟨c, fun i => ?_, hlt⟩
    have := hc i
    simp only [G, Finset.mem_image, Finset.mem_range] at this ⊢
    obtain ⟨j, hj, hje⟩ := this
    exact ⟨j, by omega, hje⟩
  have hsub : {ω | ∃ c : Fin l → Config d, (∀ i, c i ∈ S i) ∧
      β < ∑ i, cfgVal δ (fun z => H z ω) (c i)} ⊆ ⋃ N, A N := by
    intro ω hω
    obtain ⟨c, hc, hlt⟩ := hω
    have hφ : Continuous fun z => H z ω := hH.continuous ω
    set gap := ∑ i, cfgVal δ (fun z => H z ω) (c i) - β with hgap
    have hgap0 : 0 < gap := sub_pos.2 hlt
    set η := gap / ((l : ℝ) + 1) with hη
    have hη0 : 0 < η := div_pos hgap0 (by positivity)
    have hj : ∀ i, ∃ j, |cfgVal δ (fun z => H z ω) (e i j) -
        cfgVal δ (fun z => H z ω) (c i)| < η :=
      fun i => happ i (c i) (hc i) _ hφ δ η hη0
    choose j hj using hj
    refine mem_iUnion.2 ⟨Finset.univ.sup j, ?_⟩
    refine ⟨fun i => e i (j i), fun i => ?_, ?_⟩
    · simp only [G, Finset.mem_image, Finset.mem_range]
      exact ⟨j i, Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ i)), rfl⟩
    · have hle : ∑ i, (cfgVal δ (fun z => H z ω) (c i) - η) ≤
          ∑ i, cfgVal δ (fun z => H z ω) (e i (j i)) :=
        Finset.sum_le_sum fun i _ => by linarith [(abs_lt.1 (hj i)).1]
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul] at hle
      show β < ∑ i, cfgVal δ (fun z => H z ω) (e i (j i))
      have hlη : (l : ℝ) * η < gap := by
        rw [hη, mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith
      linarith
  have hA : ∀ N, P (A N) ≤
      ENNReal.ofReal (Real.exp (-t * β + t * ∑ i, m i + Real.pi ^ 2 / 8 * t ^ 2 * V)) := by
    intro N
    refine le_trans (measure_mono ?_) (chain_bound_finite hκ hW ha hab hH δ (G N) (hGne N) m V
      (fun i => hmean i (G N i) (hGne N i) (hGsub N i))
      (fun c hc => hvar c fun i => hGsub N i (hc i)) β t ht)
    intro ω hω
    obtain ⟨c, hc, hlt⟩ := hω
    show β < ⨆ c' : Fintype.piFinset (G N),
      ∑ i, cfgVal δ (fun z => H z ω) ((c' : Fin l → Config d) i)
    exact lt_of_lt_of_le hlt (le_ciSup (f := fun c' : Fintype.piFinset (G N) =>
      ∑ i, cfgVal δ (fun z => H z ω) ((c' : Fin l → Config d) i))
      (Set.finite_range _).bddAbove ⟨c, Fintype.mem_piFinset.2 hc⟩)
  calc _ ≤ P (⋃ N, A N) := measure_mono hsub
    _ = ⨆ N, P (A N) := hAmono.measure_iUnion
    _ ≤ _ := iSup_le hA

end Chain

/-! ## The weights and the Claim of D7 -/

section Claim

variable {d : ℕ}

/-- The good-record weight `w_g(k) = exp(t(b + 1 - τk) + (π²/8) t² C_V √(k+1))` (HA3 D7). -/
def wGood (t τ bstar CV : ℝ) (k : ℕ) : ℝ :=
  Real.exp (t * (bstar + 1 - τ * k) + Real.pi ^ 2 / 8 * t ^ 2 * (CV * Real.sqrt ((k : ℝ) + 1)))

/-- The bad-record weight `w_b = exp(t(C_bad - a₀/δ²) + (π²/8) t² C'_V/δ)` (HA3 D7). -/
def wBad (n : ℕ) (t δ Cbad CV' : ℝ) : ℝ :=
  Real.exp (t * (Cbad - a0 n / δ ^ 2) + Real.pi ^ 2 / 8 * t ^ 2 * (CV' / δ))

/-- `Z_g + Z_b = Σ_k N_g(k) w_g(k) + N_b w_b` (HA3 D7). -/
def Zsum (d n : ℕ) (δ t τ bstar Cbad CV CV' : ℝ) : ℝ :=
  ∑' k, Ng d n k * wGood t τ bstar CV k + Nb d n δ * wBad n t δ Cbad CV'

/-- The mean bound of a record: `b + (1 - τ)(k + 1)` (good, bin `k`) and `C_bad` (bad). -/
def recMean (τ bstar Cbad : ℝ) : Record d → ℝ
  | .inl g => bstar + (1 - τ) * ((g.bin : ℝ) + 1)
  | .inr _ => Cbad

theorem wGood_pos (t τ bstar CV : ℝ) (k : ℕ) : 0 < wGood t τ bstar CV k := Real.exp_pos _

theorem wBad_pos (n : ℕ) (t δ Cbad CV' : ℝ) : 0 < wBad n t δ Cbad CV' := Real.exp_pos _

/-- The per-record exponent is bounded by the log-weight: for `t ≥ 0`, `τ ≥ 0`,
`t (mean - cost) + (π²/8) t² var ≤ log w(ρ)`. -/
theorem exponent_le_log_weight {n : ℕ} {δ t τ bstar Cbad CV CV' : ℝ} (ht : 0 ≤ t) (hτ : 0 ≤ τ)
    (ρ : Record d) :
    t * (recMean τ bstar Cbad ρ - ρ.cost n δ) + Real.pi ^ 2 / 8 * t ^ 2 * recVar CV CV' δ ρ ≤
      Real.log (recWeight (wGood t τ bstar CV) (wBad n t δ Cbad CV') ρ) := by
  rcases ρ with g | b
  · simp only [recWeight, wGood, Real.log_exp, recMean, Record.cost_inl, recVar]
    have : (1 - τ) * ((g.bin : ℝ) + 1) - g.bin ≤ 1 - τ * g.bin := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left this ht]
  · simp only [recWeight, wBad, Real.log_exp, recMean, Record.cost_inr, recVar]
    rfl

variable {κ : Rd d → ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ}

/-- **The Claim of HA3 D7**: for a chain record `ρ` of valid records,
`P(∃ c_i ∈ Φ(ρ_i): Σ_i (Y_i(c_i) - cost(ρ_i)) > T) ≤ e^{-tT} Π_i w(ρ_i)`, given the good-record
mean bound (D6 (iv)), the bad-record mean bound (D6 (ii)) and the variance bound (D6 (iii)). -/
theorem chainRecord_event_le (hκ : IsLFPPKernel κ) (hW : IsWhiteNoise P W) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) {H : Rd d → Ω → ℝ} (hH : IsBandVersion P W κ a b H) {n : ℕ}
    {δ : ℝ} {t τ bstar Cbad CV CV' : ℝ} (ht : 0 ≤ t) (hτ : 0 ≤ τ)
    (hgood : ∀ g : GoodRec d, RecValid n δ (Sum.inl g) → ∀ F : Finset (Config d),
      ↑F ⊆ goodFam n δ g → F.Nonempty →
        ∫ ω, (⨆ c : F, cfgVal δ (fun z => H z ω) c) ∂P ≤ bstar + (1 - τ) * ((g.bin : ℝ) + 1))
    (hbad : ∀ (br : BadRec d) (F : Finset (Config d)), ↑F ⊆ badFam n δ br →
      ∫ ω, (⨆ c : F, cfgVal δ (fun z => H z ω) c) ∂P ≤ Cbad)
    (hvar : ∀ {l : ℕ} (ρ : Fin l → Record d), IsChainRec δ ρ → (∀ i, RecValid n δ (ρ i)) →
      ∀ c : Fin l → Config d, (∀ i, c i ∈ family n δ (ρ i)) →
        ‖∑ i, cfgVec κ a b δ (c i)‖ ^ 2 ≤ ∑ i, recVar CV CV' δ (ρ i))
    {l : ℕ} (ρ : Fin l → Record d) (hch : IsChainRec δ ρ) (hv : ∀ i, RecValid n δ (ρ i))
    (T : ℝ) :
    P {ω | ∃ c : Fin l → Config d, (∀ i, c i ∈ family n δ (ρ i)) ∧
        T < ∑ i, (cfgVal δ (fun z => H z ω) (c i) - (ρ i).cost n δ)} ≤
      ENNReal.ofReal (Real.exp (-t * T) *
        ∏ i, recWeight (wGood t τ bstar CV) (wBad n t δ Cbad CV') (ρ i)) := by
  have hpos : ∀ i, ∀ c ∈ family n δ (ρ i), 0 < polyLen c.1 ∧ 0 < polyLen c.2 :=
    fun i c hc => polyLen_pos_of_mem_family hc
  have hmean : ∀ i, ∀ F : Finset (Config d), F.Nonempty → ↑F ⊆ family n δ (ρ i) →
      ∫ ω, (⨆ c : F, cfgVal δ (fun z => H z ω) c) ∂P ≤ recMean τ bstar Cbad (ρ i) := by
    intro i F hF hFS
    rcases hρ : ρ i with g | br
    · rw [hρ] at hFS
      have := hv i
      rw [hρ] at this
      exact hgood g this F hFS hF
    · rw [hρ] at hFS
      exact hbad br F hFS
  have hfam := chain_bound_family hκ hW ha hab hH δ (fun i => family n δ (ρ i)) hpos
    (fun i => recMean τ bstar Cbad (ρ i)) (∑ i, recVar CV CV' δ (ρ i)) hmean
    (fun c hc => hvar ρ hch hv c hc) (T + ∑ i, (ρ i).cost n δ) t ht
  refine le_trans (measure_mono fun ω hω => ?_) (hfam.trans (ENNReal.ofReal_le_ofReal ?_))
  · obtain ⟨c, hc, hlt⟩ := hω
    refine ⟨c, hc, ?_⟩
    rw [Finset.sum_sub_distrib] at hlt
    linarith
  · -- the exponent
    have hprod : Real.exp (-t * T) *
        ∏ i, recWeight (wGood t τ bstar CV) (wBad n t δ Cbad CV') (ρ i) =
        Real.exp (-t * T + ∑ i, Real.log
          (recWeight (wGood t τ bstar CV) (wBad n t δ Cbad CV') (ρ i))) := by
      rw [Real.exp_add, Real.exp_sum]
      congr 1
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [Real.exp_log]
      rcases ρ i with g | br
      · exact wGood_pos _ _ _ _ _
      · exact wBad_pos _ _ _ _ _
    rw [hprod]
    refine Real.exp_le_exp.2 ?_
    have hsum : ∑ i, (t * (recMean τ bstar Cbad (ρ i) - (ρ i).cost n δ) +
        Real.pi ^ 2 / 8 * t ^ 2 * recVar CV CV' δ (ρ i)) ≤
        ∑ i, Real.log (recWeight (wGood t τ bstar CV) (wBad n t δ Cbad CV') (ρ i)) :=
      Finset.sum_le_sum fun i _ => exponent_le_log_weight ht hτ (ρ i)
    have e : -t * (T + ∑ i, (ρ i).cost n δ) + t * ∑ i, recMean τ bstar Cbad (ρ i) +
        Real.pi ^ 2 / 8 * t ^ 2 * ∑ i, recVar CV CV' δ (ρ i) =
        -t * T + ∑ i, (t * (recMean τ bstar Cbad (ρ i) - (ρ i).cost n δ) +
          Real.pi ^ 2 / 8 * t ^ 2 * recVar CV CV' δ (ρ i)) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_sub_distrib]
      ring
    rw [e]
    linarith

end Claim

/-! ## Counting: the exceptional event -/

section Counting

variable {d : ℕ} {κ : Rd d → ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {W : WN d → Ω → ℝ}

/-- The exceptional event `𝒜` of HA3 D7: some chain record of the finite record set of the cutoff
`ε`, of length at most `M`, has `Σ_i (Y_i(c_i) - cost(ρ_i)) > T₀` for some `c_i ∈ Φ(ρ_i)`. -/
def excEvent (d n : ℕ) (δ ε : ℝ) (H : Rd d → Ω → ℝ) (M : ℕ) (T₀ : ℝ) : Set Ω :=
  ⋃ l ∈ Finset.range (M + 1), ⋃ ρ : Fin l → recSet d n δ ε,
    {ω | IsChainRec δ (fun i => (ρ i).1) ∧ ∃ c : Fin l → Config d,
      (∀ i, c i ∈ family n δ (ρ i).1) ∧
      T₀ < ∑ i, (cfgVal δ (fun z => H z ω) (c i) - (ρ i).1.cost n δ)}

/-- `Σ_k (k+1)^d r^k < ∞` for `0 < r < 1`. -/
theorem summable_succ_pow_mul_geometric (d : ℕ) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    Summable fun k : ℕ => ((k : ℝ) + 1) ^ d * r ^ k := by
  have hr1' : ‖r‖ < 1 := by rw [Real.norm_of_nonneg hr0.le]; exact hr1
  have h0 : Summable fun k : ℕ => (k : ℝ) ^ d * r ^ k :=
    summable_pow_mul_geometric_of_norm_lt_one d hr1'
  have h1 : Summable fun k : ℕ => ((k + 1 : ℕ) : ℝ) ^ d * r ^ (k + 1) :=
    (summable_nat_add_iff (f := fun k : ℕ => (k : ℝ) ^ d * r ^ k) 1).2 h0
  have h2 := h1.mul_left r⁻¹
  refine h2.congr fun k => ?_
  have hrne : r ≠ 0 := hr0.ne'
  rw [Nat.cast_succ, pow_succ, mul_comm (r ^ k) r, ← mul_assoc, ← mul_assoc,
    mul_comm r⁻¹, mul_assoc _ r⁻¹ r, inv_mul_cancel₀ hrne, mul_one]

/-- The good weights are summable against the counts: `Σ_k N_g(k) w_g(k) < ∞` for `t, τ > 0`. -/
theorem summable_Ng_wGood (d n : ℕ) {t τ : ℝ} (ht : 0 < t) (hτ : 0 < τ) (bstar CV : ℝ) :
    Summable fun k => Ng d n k * wGood t τ bstar CV k := by
  set c : ℝ := Real.pi ^ 2 / 8 * t ^ 2 * CV with hc
  set r : ℝ := Real.exp (-(t * τ) / 2) with hr
  -- `Ng(k) w_g(k) ≤ B (k+1)^d r^k`
  set B : ℝ := 3 * 2 ^ n * (cGood d * 2 ^ n) ^ (2 * d) *
    Real.exp (t * (bstar + 1) + t * τ / 2 + c ^ 2 / (2 * (t * τ))) with hB
  have hbound : ∀ k : ℕ, Ng d n k * wGood t τ bstar CV k ≤ B * (((k : ℝ) + 1) ^ d * r ^ k) := by
    intro k
    have hk : (0 : ℝ) ≤ (k : ℝ) + 1 := by positivity
    have hNg : Ng d n k = 3 * 2 ^ n * (cGood d * 2 ^ n) ^ (2 * d) * ((k : ℝ) + 1) ^ d := by
      rw [Ng, mul_pow, pow_mul (Real.sqrt ((k : ℝ) + 1)) 2 d, Real.sq_sqrt hk]
      ring
    have hamgm : c * Real.sqrt ((k : ℝ) + 1) ≤ t * τ / 2 * ((k : ℝ) + 1) + c ^ 2 / (2 * (t * τ)) := by
      have htt : 0 < t * τ := mul_pos ht hτ
      have hs := Real.sq_sqrt hk
      have hsq : 0 ≤ (t * τ * Real.sqrt ((k : ℝ) + 1) - c) ^ 2 := sq_nonneg _
      have e : 2 * (t * τ) * (t * τ / 2 * ((k : ℝ) + 1) + c ^ 2 / (2 * (t * τ))) =
          (t * τ) ^ 2 * ((k : ℝ) + 1) + c ^ 2 := by
        field_simp
      have key : 2 * (t * τ) * (c * Real.sqrt ((k : ℝ) + 1)) ≤
          2 * (t * τ) * (t * τ / 2 * ((k : ℝ) + 1) + c ^ 2 / (2 * (t * τ))) := by
        rw [e]
        nlinarith
      exact le_of_mul_le_mul_left key (by positivity)
    have hw : wGood t τ bstar CV k ≤
        Real.exp (t * (bstar + 1) + t * τ / 2 + c ^ 2 / (2 * (t * τ))) * r ^ k := by
      rw [wGood, hr, ← Real.exp_nat_mul, ← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      have e : Real.pi ^ 2 / 8 * t ^ 2 * (CV * Real.sqrt ((k : ℝ) + 1)) =
          c * Real.sqrt ((k : ℝ) + 1) := by rw [hc]; ring
      rw [e]
      nlinarith
    rw [hNg]
    have hNg0 : 0 ≤ 3 * 2 ^ n * (cGood d * 2 ^ n) ^ (2 * d) * ((k : ℝ) + 1) ^ d := by
      have := cGood_pos d
      positivity
    calc 3 * 2 ^ n * (cGood d * 2 ^ n) ^ (2 * d) * ((k : ℝ) + 1) ^ d * wGood t τ bstar CV k
        ≤ 3 * 2 ^ n * (cGood d * 2 ^ n) ^ (2 * d) * ((k : ℝ) + 1) ^ d *
          (Real.exp (t * (bstar + 1) + t * τ / 2 + c ^ 2 / (2 * (t * τ))) * r ^ k) :=
          mul_le_mul_of_nonneg_left hw hNg0
      _ = B * (((k : ℝ) + 1) ^ d * r ^ k) := by rw [hB]; ring
  have hsum1 : Summable fun k : ℕ => ((k : ℝ) + 1) ^ d * r ^ k :=
    summable_succ_pow_mul_geometric d (Real.exp_pos _) (by
      rw [hr, Real.exp_lt_one_iff]
      have := mul_pos ht hτ
      linarith)
  refine Summable.of_nonneg_of_le (fun k => mul_nonneg (Ng_nonneg d n k) (wGood_pos _ _ _ _ _).le)
    hbound (hsum1.mul_left B)

open scoped Classical in
/-- **Counting** (HA3 D7): the exceptional event has outer probability at most
`e^{-tT₀} (1 + Z_g + Z_b)^M`. -/
theorem measure_excEvent_le (hκ : IsLFPPKernel κ) (hW : IsWhiteNoise P W) {ε : ℝ}
    {H : Rd d → Ω → ℝ} (hH : IsBandVersion P W κ ε 1 H) (hε : ε ∈ Ioo (0 : ℝ) 1) {n : ℕ}
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {t τ bstar Cbad CV CV' : ℝ} (ht : 0 < t) (hτ : 0 < τ)
    (hgood : ∀ g : GoodRec d, RecValid n δ (Sum.inl g) → ∀ F : Finset (Config d),
      ↑F ⊆ goodFam n δ g → F.Nonempty →
        ∫ ω, (⨆ c : F, cfgVal δ (fun z => H z ω) c) ∂P ≤ bstar + (1 - τ) * ((g.bin : ℝ) + 1))
    (hbad : ∀ (br : BadRec d) (F : Finset (Config d)), ↑F ⊆ badFam n δ br →
      ∫ ω, (⨆ c : F, cfgVal δ (fun z => H z ω) c) ∂P ≤ Cbad)
    (hvar : ∀ {l : ℕ} (ρ : Fin l → Record d), IsChainRec δ ρ → (∀ i, RecValid n δ (ρ i)) →
      ∀ c : Fin l → Config d, (∀ i, c i ∈ family n δ (ρ i)) →
        ‖∑ i, cfgVec κ ε 1 δ (c i)‖ ^ 2 ≤ ∑ i, recVar CV CV' δ (ρ i))
    (M : ℕ) (T₀ : ℝ) :
    P (excEvent d n δ ε H M T₀) ≤
      ENNReal.ofReal (Real.exp (-t * T₀) * (1 + Zsum d n δ t τ bstar Cbad CV CV') ^ M) := by
  have hZ0 : 0 ≤ Zsum d n δ t τ bstar Cbad CV CV' :=
    add_nonneg (tsum_nonneg fun k => mul_nonneg (Ng_nonneg d n k) (wGood_pos _ _ _ _ _).le)
      (mul_nonneg (Nb_nonneg d n hδ) (wBad_pos _ _ _ _ _).le)
  set wg := wGood t τ bstar CV with hwg
  set wb := wBad n t δ Cbad CV' with hwb
  set Z := Zsum d n δ t τ bstar Cbad CV CV' with hZ
  -- one length
  have hl : ∀ l : ℕ, P (⋃ ρ : Fin l → recSet d n δ ε,
      {ω | IsChainRec δ (fun i => (ρ i).1) ∧ ∃ c : Fin l → Config d,
        (∀ i, c i ∈ family n δ (ρ i).1) ∧
        T₀ < ∑ i, (cfgVal δ (fun z => H z ω) (c i) - (ρ i).1.cost n δ)}) ≤
      ENNReal.ofReal (Real.exp (-t * T₀) * Z ^ l) := by
    intro l
    refine (measure_iUnion_fintype_le P _).trans ?_
    have hterm : ∀ ρ : Fin l → recSet d n δ ε,
        P {ω | IsChainRec δ (fun i => (ρ i).1) ∧ ∃ c : Fin l → Config d,
          (∀ i, c i ∈ family n δ (ρ i).1) ∧
          T₀ < ∑ i, (cfgVal δ (fun z => H z ω) (c i) - (ρ i).1.cost n δ)} ≤
        ENNReal.ofReal (Real.exp (-t * T₀) *
          (if IsChainRec δ (fun i => (ρ i).1) then ∏ i, recWeight wg wb (ρ i).1 else 0)) := by
      intro ρ
      by_cases hch : IsChainRec δ (fun i => (ρ i).1)
      · rw [ite_eq_left hch]
        refine le_trans (measure_mono fun ω hω => hω.2) ?_
        exact chainRecord_event_le hκ hW hε.1 hε.2.le hH ht.le hτ.le hgood hbad
          (fun ρ' hch' hv' c hc => hvar ρ' hch' hv' c hc) (fun i => (ρ i).1) hch
          (fun i => recValid_of_mem_recSet (ρ i).2) T₀
      · rw [ite_eq_right hch, mul_zero, ENNReal.ofReal_zero]
        refine le_of_eq (measure_eq_zero_iff_ae_notMem.2 ?_)
        exact Eventually.of_forall fun ω hω => hch hω.1
    refine (Finset.sum_le_sum fun ρ _ => hterm ρ).trans ?_
    rw [← ENNReal.ofReal_sum_of_nonneg (fun ρ _ => by
      split_ifs
      · exact mul_nonneg (Real.exp_pos _).le (Finset.prod_nonneg fun i _ =>
          recWeight_nonneg (fun k => (wGood_pos _ _ _ _ _).le) (wBad_pos _ _ _ _ _).le _)
      · simp)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
    exact sum_chain_weight_le_recSet hδ hδ1 ε (fun k => (wGood_pos _ _ _ _ _).le)
      (wBad_pos _ _ _ _ _).le (summable_Ng_wGood d n ht hτ bstar CV) l
  refine (measure_biUnion_finset_le _ _).trans ?_
  refine (Finset.sum_le_sum fun l _ => hl l).trans ?_
  rw [← ENNReal.ofReal_sum_of_nonneg (fun l _ => mul_nonneg (Real.exp_pos _).le
    (pow_nonneg hZ0 l))]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (sum_range_pow_le_one_add_pow hZ0 M) (Real.exp_pos _).le

/-- With `T₀ = (M/t)(log(1 + Z) + 2)`: `e^{-tT₀} (1 + Z)^M = e^{-2M}`. -/
theorem exp_mul_pow_eq {t Z : ℝ} (ht : 0 < t) (hZ : 0 ≤ Z) (M : ℕ) :
    Real.exp (-t * ((M : ℝ) / t * (Real.log (1 + Z) + 2))) * (1 + Z) ^ M =
      Real.exp (-2 * (M : ℝ)) := by
  have h1 : (0 : ℝ) < 1 + Z := by linarith
  have e : -t * ((M : ℝ) / t * (Real.log (1 + Z) + 2)) =
      -(M * Real.log (1 + Z)) + -2 * (M : ℝ) := by
    field_simp
    ring
  rw [e, Real.exp_add, Real.exp_neg, ← Real.log_pow, Real.exp_log (pow_pos h1 M)]
  field_simp

end Counting

end HigherDimLFPP.Upper
