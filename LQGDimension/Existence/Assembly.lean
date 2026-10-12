import LQGDimension.Existence.AssemblyAux1
import LQGDimension.Existence.AssemblyAux2
import LQGDimension.Existence.GffKernel
import LQGDimension.Existence.CountableGram
import LQGDimension.Existence.SeriesContinuity

/-!
# Assembly node: `Blueprint.Existence.GFFCircleAverageExists`

## Architecture

* **Probability space.** `Ω = ℕ → ℝ` with `stdP = infinitePi (gaussianReal 0 1)`
  (`AssemblyAux1`).
* **Index set.** `T₀ = {(q, a + b i) : q, a, b ∈ ℚ, q > 0}` is countable and dense in
  `(0, ∞) × ℂ` (`AssemblyAux2`).
* **Gram representation.** `CountableGramRep` on the subtype `T₀` with the kernel
  `gffCircleCov` (PSD by `gffCovPSD`, transported along `Finset.map`, `psd_T₀`) gives finitely
  supported `v₀ : T₀ → ℕ → ℝ`; it is extended by `0` off `T₀` to `v : ℝ × ℂ → ℕ → ℝ`.
* **Series.** `Xs v t ω = Σ' k, v t k * ω k` is a finite sum (`Xs_eq_sum`), hence measurable.
* **Continuity.** The increments `Σ_k (v s k - v t k)² = K(s,s) + K(t,t) - 2 K(s,t)`
  (`tsum_sq_sub_eq`) are bounded by `gffIncrementBound`, so `GaussianSeriesLocallyUnifCont`
  gives: a.s. `X` is uniformly continuous on every `T₀ ∩ box m`.  The exceptional set is put
  inside a measurable null set `B` (`exists_measurable_superset_of_null`); the good set is
  `G = Bᶜ`.  The data `(v, G)` is packaged as `GoodData v G`.
* **Field.** `hField v G ε z ω = 1_G(ω) · extendFrom T₀ (X · ω) (ε, z)`.  On `G` the extension
  is continuous on `{ε > 0}` and is the limit of `X` along every sequence of `T₀`
  (`AssemblyAux2`).  Measurability (`measurable_hField`): pointwise limit of `1_G · X_{s_n}`.
* **Laws.** `hasLaw_comb`: for finitely many points `p_i` with positive radii and coefficients
  `c_i`, `Σ c_i h(p_i)` has law `N(0, Σ c_i c_j K(p_i,p_j))`.  Proof: choose `s_i(n) ∈ T₀`,
  `s_i(n) → p_i`; `Σ c_i X_{s_i(n)} = Σ_{k<M_n} w_n(k) ω_k` has law `N(0, Σ_k w_n(k)²)`
  (`hasLaw_sum_mul`), `Σ_k w_n(k)² = Σ c_i c_j K(s_i(n), s_j(n)) → Σ c_i c_j K(p_i, p_j)`
  (`gffCovContinuous`), and the a.e. limit is Gaussian (`hasLaw_gaussianReal_of_tendsto`).
* **Conclusion.** Gaussian process: Cramér–Wold via `hasGaussianLaw_pi_of_forall_hasLaw`;
  mean zero: one point; covariance: polarisation with two points and symmetry of the kernel
  (`GffKernel.Kg_comm`, `GffKernel.Kg_eq`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace LQGDimension.ExistAsm

open Blueprint.Existence

/-! ### The Gaussian series and the field -/

/-- The Gaussian series `X_t(ω) = Σ_k v_t(k) ω_k`. -/
def Xs (v : ℝ × ℂ → ℕ → ℝ) (t : ℝ × ℂ) (ω : ℕ → ℝ) : ℝ := ∑' k, v t k * ω k

/-- The field: on the good set `G`, the continuous extension of `X` from `T₀`; `0` off `G`. -/
def hField (v : ℝ × ℂ → ℕ → ℝ) (G : Set (ℕ → ℝ)) (ε : ℝ) (z : ℂ) (ω : ℕ → ℝ) : ℝ :=
  G.indicator (fun ω => extendFrom T₀ (fun t => Xs v t ω) (ε, z)) ω

/-- The data produced by the two blueprint hypotheses. -/
structure GoodData (v : ℝ × ℂ → ℕ → ℝ) (G : Set (ℕ → ℝ)) : Prop where
  fin : ∀ t, ∃ N, ∀ k ≥ N, v t k = 0
  gram : ∀ s ∈ T₀, ∀ t ∈ T₀, ∑' k, v s k * v t k = gffCircleCov s.1 s.2 t.1 t.2
  meas : MeasurableSet G
  full : ∀ᵐ ω ∂stdP, ω ∈ G
  unif : ∀ ω ∈ G, ∀ m : ℕ, UniformContinuousOn (fun t => Xs v t ω) (T₀ ∩ box m)

theorem tsum_eq_sum_range_of_vanish {a : ℕ → ℝ} {N : ℕ} (h : ∀ k ≥ N, a k = 0) :
    ∑' k, a k = ∑ k ∈ Finset.range N, a k :=
  tsum_eq_sum fun k hk => h k (by simpa using hk)

theorem tsum_sq_sub_eq {a b : ℕ → ℝ} {N : ℕ} (ha : ∀ k ≥ N, a k = 0)
    (hb : ∀ k ≥ N, b k = 0) :
    ∑' k, (a k - b k) ^ 2 = ∑' k, a k * a k + ∑' k, b k * b k - 2 * ∑' k, a k * b k := by
  rw [tsum_eq_sum_range_of_vanish (a := fun k => (a k - b k) ^ 2) (N := N)
      (fun k hk => by simp [ha k hk, hb k hk]),
    tsum_eq_sum_range_of_vanish (a := fun k => a k * a k) (N := N)
      (fun k hk => by simp [ha k hk]),
    tsum_eq_sum_range_of_vanish (a := fun k => b k * b k) (N := N)
      (fun k hk => by simp [hb k hk]),
    tsum_eq_sum_range_of_vanish (a := fun k => a k * b k) (N := N)
      (fun k hk => by simp [ha k hk]),
    Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem Xs_eq_sum {v : ℝ × ℂ → ℕ → ℝ} {t : ℝ × ℂ} {N : ℕ} (hN : ∀ k ≥ N, v t k = 0)
    (ω : ℕ → ℝ) : Xs v t ω = ∑ k ∈ Finset.range N, v t k * ω k :=
  tsum_eq_sum_range_of_vanish fun k hk => by rw [hN k hk, zero_mul]

theorem measurable_Xs {v : ℝ × ℂ → ℕ → ℝ} {t : ℝ × ℂ} (hv : ∃ N, ∀ k ≥ N, v t k = 0) :
    Measurable (Xs v t) := by
  obtain ⟨N, hN⟩ := hv
  have e : Xs v t = fun ω => ∑ k ∈ Finset.range N, v t k * ω k := funext (Xs_eq_sum hN)
  rw [e]
  exact Finset.measurable_fun_sum _ fun k _ => (measurable_pi_apply k).const_mul _

/-! ### The covariance kernel -/

theorem gffCircleCov_symm {p q : ℝ × ℂ} (hp : 0 < p.1) (hq : 0 < q.1) :
    gffCircleCov p.1 p.2 q.1 q.2 = gffCircleCov q.1 q.2 p.1 p.2 := by
  rw [← GffKernel.Kg_eq p hq, ← GffKernel.Kg_eq q hp, GffKernel.Kg_comm]

theorem tendsto_gffCircleCov_seq {p q : ℝ × ℂ} (hp : 0 < p.1) (hq : 0 < q.1)
    {s t : ℕ → ℝ × ℂ} (hs0 : ∀ n, 0 < (s n).1) (ht0 : ∀ n, 0 < (t n).1)
    (hs : Tendsto s atTop (𝓝 p)) (ht : Tendsto t atTop (𝓝 q)) :
    Tendsto (fun n => gffCircleCov (s n).1 (s n).2 (t n).1 (t n).2) atTop
      (𝓝 (gffCircleCov p.1 p.2 q.1 q.2)) := by
  have h : ContinuousWithinAt
      (fun x : (ℝ × ℂ) × (ℝ × ℂ) => gffCircleCov x.1.1 x.1.2 x.2.1 x.2.2)
      {x | 0 < x.1.1 ∧ 0 < x.2.1} (p, q) := gffCovContinuous (p, q) ⟨hp, hq⟩
  have h2 : Tendsto (fun n => (s n, t n)) atTop
      (𝓝[{x : (ℝ × ℂ) × (ℝ × ℂ) | 0 < x.1.1 ∧ 0 < x.2.1}] (p, q)) :=
    tendsto_nhdsWithin_iff.2 ⟨hs.prodMk_nhds ht, Eventually.of_forall fun n => ⟨hs0 n, ht0 n⟩⟩
  have h3 := h.tendsto.comp h2
  simpa only [Function.comp_def] using h3

/-- `gffCircleCov` restricted to `T₀` is PSD on every finite subset. -/
theorem psd_T₀ (F : Finset T₀) :
    PSDOn F (fun s t : T₀ => gffCircleCov s.1.1 s.1.2 t.1.1 t.1.2) := by
  classical
  have h := gffCovPSD (F.map (Function.Embedding.subtype _)) (fun p hp => by
    obtain ⟨q, _, rfl⟩ := Finset.mem_map.1 hp
    exact q.2.1)
  unfold PSDOn at h ⊢
  convert h.submatrix (fun i : F => (⟨i.1.1, Finset.mem_map_of_mem _ i.2⟩ :
    (F.map (Function.Embedding.subtype _) : Finset (ℝ × ℂ)))) using 1
  ext i j
  rfl

/-! ### The field: measurability, continuity, finite-dimensional laws -/

section Field

variable {v : ℝ × ℂ → ℕ → ℝ} {G : Set (ℕ → ℝ)}

theorem measurable_hField (hD : GoodData v G) {ε : ℝ} (hε : 0 < ε) (z : ℂ) :
    Measurable (hField v G ε z) := by
  obtain ⟨s, hsT, hs⟩ := exists_seq_T₀ (x := (ε, z)) hε
  refine measurable_of_tendsto_metrizable (f := fun n => G.indicator (Xs v (s n)))
    (fun n => (measurable_Xs (hD.fin _)).indicator hD.meas) ?_
  rw [tendsto_pi_nhds]
  intro ω
  by_cases hω : ω ∈ G
  · simp only [hField, Set.indicator_of_mem hω]
    exact tendsto_extendFrom_T₀_seq (hD.unif ω hω) hε hsT hs
  · simp only [hField, Set.indicator_of_notMem hω]
    exact tendsto_const_nhds

theorem continuous_hField (hD : GoodData v G) {ε : ℝ} (hε : 0 < ε) (ω : ℕ → ℝ) :
    Continuous fun z => hField v G ε z ω := by
  by_cases hω : ω ∈ G
  · simp only [hField, Set.indicator_of_mem hω]
    exact continuous_extendFrom_T₀_slice (hD.unif ω hω) hε
  · simp only [hField, Set.indicator_of_notMem hω]
    exact continuous_const

/-- **Finite linear combinations of the field are centered Gaussians** with the covariance
`gffCircleCov`. -/
theorem hasLaw_comb (hD : GoodData v G) {ι : Type*} [Fintype ι] (p : ι → ℝ × ℂ)
    (hp : ∀ i, 0 < (p i).1) (c : ι → ℝ) :
    0 ≤ ∑ i, ∑ j, c i * c j * gffCircleCov (p i).1 (p i).2 (p j).1 (p j).2 ∧
    HasLaw (fun ω => ∑ i, c i * hField v G (p i).1 (p i).2 ω)
      (gaussianReal 0
        (∑ i, ∑ j, c i * c j * gffCircleCov (p i).1 (p i).2 (p j).1 (p j).2).toNNReal)
      stdP := by
  choose s hsT hs using fun i => exists_seq_T₀ (hp i)
  choose Nf hNf using hD.fin
  have hMex : ∀ n, ∃ M : ℕ, ∀ i, ∀ k ≥ M, v (s i n) k = 0 := fun n =>
    ⟨∑ i, Nf (s i n), fun i k hk => hNf _ k (le_trans
      (Finset.single_le_sum (f := fun j => Nf (s j n)) (fun j _ => Nat.zero_le _)
        (Finset.mem_univ i)) hk)⟩
  choose M hM using hMex
  have hgram : ∀ n i j, ∑ k ∈ Finset.range (M n), v (s i n) k * v (s j n) k =
      gffCircleCov (s i n).1 (s i n).2 (s j n).1 (s j n).2 := by
    intro n i j
    rw [← hD.gram _ (hsT i n) _ (hsT j n)]
    exact (tsum_eq_sum_range_of_vanish fun k hk => by rw [hM n i k hk, zero_mul]).symm
  have hYw : ∀ n, (fun ω : ℕ → ℝ => ∑ i, c i * Xs v (s i n) ω) =
      fun ω => ∑ k ∈ Finset.range (M n), (∑ i, c i * v (s i n) k) * ω k := by
    intro n
    funext ω
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Xs_eq_sum (hM n i), Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hQ : ∀ n, ∑ k ∈ Finset.range (M n), (∑ i, c i * v (s i n) k) ^ 2 =
      ∑ i, ∑ j, c i * c j * gffCircleCov (s i n).1 (s i n).2 (s j n).1 (s j n).2 := by
    intro n
    calc ∑ k ∈ Finset.range (M n), (∑ i, c i * v (s i n) k) ^ 2
        = ∑ k ∈ Finset.range (M n), ∑ i, ∑ j, c i * c j * (v (s i n) k * v (s j n) k) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          simp only [sq, Finset.sum_mul, Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
      _ = ∑ i, ∑ j, c i * c j * ∑ k ∈ Finset.range (M n), v (s i n) k * v (s j n) k := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun j _ => by rw [Finset.mul_sum]
      _ = _ := by simp only [hgram]
  have hlawY : ∀ n, HasLaw (fun ω : ℕ → ℝ => ∑ i, c i * Xs v (s i n) ω)
      (gaussianReal 0 (∑ i, ∑ j, c i * c j *
        gffCircleCov (s i n).1 (s i n).2 (s j n).1 (s j n).2).toNNReal) stdP := by
    intro n
    rw [hYw n, ← hQ n]
    exact hasLaw_sum_mul (fun k => ∑ i, c i * v (s i n) k) (M n)
  have hQlim : Tendsto (fun n => ∑ i, ∑ j, c i * c j *
      gffCircleCov (s i n).1 (s i n).2 (s j n).1 (s j n).2) atTop
      (𝓝 (∑ i, ∑ j, c i * c j * gffCircleCov (p i).1 (p i).2 (p j).1 (p j).2)) :=
    tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ =>
      (tendsto_gffCircleCov_seq (hp i) (hp j) (fun n => (hsT i n).1) (fun n => (hsT j n).1)
        (hs i) (hs j)).const_mul _
  have hlim : ∀ᵐ ω ∂stdP, Tendsto (fun n => ∑ i, c i * Xs v (s i n) ω) atTop
      (𝓝 (∑ i, c i * hField v G (p i).1 (p i).2 ω)) := by
    filter_upwards [hD.full] with ω hω
    refine tendsto_finsetSum _ fun i _ => Tendsto.const_mul (c i) ?_
    simp only [hField, Set.indicator_of_mem hω]
    exact tendsto_extendFrom_T₀_seq (hD.unif ω hω) (hp i) (hsT i) (hs i)
  refine ⟨ge_of_tendsto' hQlim fun n => ?_, hasLaw_gaussianReal_of_tendsto hlawY hlim hQlim⟩
  rw [← hQ n]
  exact Finset.sum_nonneg fun k _ => sq_nonneg _

theorem hasLaw_one (hD : GoodData v G) {ε : ℝ} (hε : 0 < ε) (z : ℂ) :
    0 ≤ gffCircleCov ε z ε z ∧
    HasLaw (hField v G ε z) (gaussianReal 0 (gffCircleCov ε z ε z).toNNReal) stdP := by
  have h := hasLaw_comb hD (fun _ : Unit => (ε, z)) (fun _ => hε) (fun _ => 1)
  simpa only [Fintype.sum_unique, one_mul, mul_one] using h

theorem hasLaw_two (hD : GoodData v G) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (z w : ℂ) :
    0 ≤ gffCircleCov ε z ε z + gffCircleCov ε z δ w +
      (gffCircleCov δ w ε z + gffCircleCov δ w δ w) ∧
    HasLaw (fun ω => hField v G ε z ω + hField v G δ w ω)
      (gaussianReal 0 (gffCircleCov ε z ε z + gffCircleCov ε z δ w +
        (gffCircleCov δ w ε z + gffCircleCov δ w δ w)).toNNReal) stdP := by
  have h := hasLaw_comb hD (![(ε, z), (δ, w)] : Fin 2 → ℝ × ℂ)
    (fun i => by fin_cases i <;> simp [hε, hδ]) (fun _ => 1)
  simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    one_mul, mul_one] using h

/-- **The field is a GFF circle-average process.** -/
theorem isGFFCircleAverage_hField (hD : GoodData v G) :
    IsGFFCircleAverage (hField v G) stdP := by
  have hGP : IsGaussianProcess (fun p : Ioi (0 : ℝ) × ℂ => hField v G p.1 p.2) stdP := by
    refine ⟨fun I => ?_⟩
    exact hasGaussianLaw_pi_of_forall_hasLaw (ι := I)
      (Y := fun i ω => hField v G i.1.1 i.1.2 ω)
      (fun i => (measurable_hField hD i.1.1.2 i.1.2).aemeasurable)
      (fun c => ⟨_, (hasLaw_comb hD (fun i : I => ((i.1.1 : ℝ), i.1.2)) (fun i => i.1.1.2) c).2⟩)
  refine ⟨inferInstance, hGP, ?_, ?_, fun ε hε ω => continuous_hField hD hε ω⟩
  · intro ε hε z
    rw [(hasLaw_one hD hε z).2.integral_eq, integral_id_gaussianReal]
  · intro ε hε δ hδ z w
    obtain ⟨hz0, hz⟩ := hasLaw_one hD hε z
    obtain ⟨hw0, hw⟩ := hasLaw_one hD hδ w
    obtain ⟨hzw0, hzw⟩ := hasLaw_two hD hε hδ z w
    have hsym := gffCircleCov_symm (p := (ε, z)) (q := (δ, w)) hε hδ
    simp only at hsym
    have e1 := variance_fun_add hz.hasGaussianLaw.memLp_two hw.hasGaussianLaw.memLp_two
    rw [hzw.variance_eq, hz.variance_eq, hw.variance_eq, variance_id_gaussianReal,
      variance_id_gaussianReal, variance_id_gaussianReal, Real.coe_toNNReal _ hzw0,
      Real.coe_toNNReal _ hz0, Real.coe_toNNReal _ hw0] at e1
    linarith

end Field

end LQGDimension.ExistAsm

/-! ### The assembly -/

namespace LQGDimension

open ExistAsm Blueprint.Existence

/-- **Node `GFFCircleAverageExists`**, from the two remaining existence-blueprint nodes. -/
theorem gffCircleAverageExists_of (hG : CountableGramRep) (hC : GaussianSeriesLocallyUnifCont) :
    GFFCircleAverageExists := by
  classical
  have : Countable T₀ := T₀_countable.to_subtype
  obtain ⟨v₀, hv₀fin, hv₀gram⟩ :=
    hG (↥T₀) (fun s t : T₀ => gffCircleCov s.1.1 s.1.2 t.1.1 t.1.2) psd_T₀
  let v : ℝ × ℂ → ℕ → ℝ := fun t => if ht : t ∈ T₀ then v₀ ⟨t, ht⟩ else 0
  have hv_mem : ∀ t (ht : t ∈ T₀), v t = v₀ ⟨t, ht⟩ := fun t ht => by simp [v, ht]
  have hfin : ∀ t, ∃ N, ∀ k ≥ N, v t k = 0 := by
    intro t
    by_cases ht : t ∈ T₀
    · obtain ⟨N, hN⟩ := hv₀fin ⟨t, ht⟩
      exact ⟨N, fun k hk => by rw [hv_mem t ht]; exact hN k hk⟩
    · exact ⟨0, fun k _ => by simp [v, ht]⟩
  have hgram : ∀ s ∈ T₀, ∀ t ∈ T₀, ∑' k, v s k * v t k = gffCircleCov s.1 s.2 t.1 t.2 := by
    intro s hs t ht
    rw [hv_mem s hs, hv_mem t ht]
    exact hv₀gram ⟨s, hs⟩ ⟨t, ht⟩
  have hinc : ∀ m : ℕ, ∃ L : ℝ, ∀ s ∈ T₀, ∀ t ∈ T₀, s ∈ box m → t ∈ box m →
      (∑' k, (v s k - v t k) ^ 2) ≤ L * ‖s - t‖ := by
    intro m
    obtain ⟨L, hL⟩ := gffIncrementBound m
    refine ⟨L, fun s hs t ht hsm htm => ?_⟩
    obtain ⟨N₁, hN₁⟩ := hfin s
    obtain ⟨N₂, hN₂⟩ := hfin t
    rw [tsum_sq_sub_eq (N := N₁ + N₂) (fun k hk => hN₁ k (by omega))
      (fun k hk => hN₂ k (by omega)), hgram s hs s hs, hgram t ht t ht, hgram s hs t ht]
    exact hL s hsm t htm
  have hae := hC T₀ T₀_countable v hfin hinc
  have hae' : stdP {ω | ¬ ∀ m : ℕ, UniformContinuousOn (fun t => Xs v t ω) (T₀ ∩ box m)} = 0 :=
    ae_iff.1 hae
  obtain ⟨B, hBsub, hBmeas, hB0⟩ := exists_measurable_superset_of_null hae'
  have hD : GoodData v Bᶜ :=
    { fin := hfin
      gram := hgram
      meas := hBmeas.compl
      full := ae_iff.2 (measure_mono_null (fun ω hω => by simpa using hω) hB0)
      unif := fun ω hω => by
        by_contra hcon
        exact hω (hBsub hcon) }
  exact ⟨ℕ → ℝ, inferInstance, stdP, hField v Bᶜ, isGFFCircleAverage_hField hD⟩

/-- **Non-vacuity of Theorem 1.1**: a GFF circle-average process exists. -/
theorem gffCircleAverageExists : GFFCircleAverageExists :=
  gffCircleAverageExists_of countableGramRep gaussianSeriesLocallyUnifCont

end LQGDimension
