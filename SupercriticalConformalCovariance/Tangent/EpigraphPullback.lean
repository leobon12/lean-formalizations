import SupercriticalConformalCovariance.Univalent.KoebeCore
import SupercriticalLQGUniqueness.Frozen.LSCTendsto

/-!
# Lemma 3.3, step 4: epigraph convergence is preserved by pullback

Paper l. 221–223: "Pullback by `ψ_n` preserves epigraph convergence because `ψ_n` and `ψ_n⁻¹`
converge uniformly on compact sets: the lower-bound condition is transported by forward convergence
of endpoints, and recovery endpoints are transported by the inverse maps."

* `lscTendsto_pullback`: the deterministic statement for general locally uniform limits `ψ_n → A`,
  `χ_n → B` with `B ∘ A = id`, `ψ_n ∘ χ_n = id` eventually on each compact set, and functions `E n`
  that agree with the pullbacks `G n (ψ_n ·, ψ_n ·)` eventually on each compact set (this is where
  the `+∞` extension outside `K_n × K_n` is absorbed).
* `lscTendsto_pullback_univalent`: the paper's setting (`U_n` exhausting `ℂ`, `ψ_n` univalent on
  `U_n`, `ψ_n(0) = 0`, `ψ_n'(0) → a ≠ 0`), with `χ_n = invFunOn ψ_n U_n` and the pullbacks
  extended by `+∞` outside `K_n × K_n` for closed disks `K_n = B̄_{R_n}`, `R_n → ∞`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric

namespace SupercriticalConformalCovariance.Tangent

open SupercriticalLQGUniqueness (LSCTendsto)

/-- Pairs converging to `q` lie eventually in the compact square `K × K`, `K` the union of the unit
closed disks about the two coordinates of `q`. -/
theorem eventually_mem_square {p : ℕ → ℂ × ℂ} {q : ℂ × ℂ} (hp : Tendsto p atTop (𝓝 q)) :
    ∀ᶠ n in atTop, (p n).1 ∈ closedBall q.1 1 ∪ closedBall q.2 1 ∧
      (p n).2 ∈ closedBall q.1 1 ∪ closedBall q.2 1 := by
  have h1 : Tendsto (fun n => (p n).1) atTop (𝓝 q.1) := (continuous_fst.tendsto q).comp hp
  have h2 : Tendsto (fun n => (p n).2) atTop (𝓝 q.2) := (continuous_snd.tendsto q).comp hp
  filter_upwards [h1 (closedBall_mem_nhds q.1 one_pos), h2 (closedBall_mem_nhds q.2 one_pos)]
    with n hn1 hn2
  exact ⟨Or.inl hn1, Or.inr hn2⟩

/-- **EpigraphPullback, deterministic core** (paper l. 221–223). If `G n → G₀` in the sense of DG
Definition 1.2, `ψ n → A` and `χ n → B` locally uniformly with `A`, `B` continuous and `B ∘ A = id`,
`ψ n ∘ χ n = id` eventually on every compact set, and `E n` agrees with `G n (ψ n ·, ψ n ·)`
eventually on every compact square, then `E n → G₀ (A ·, A ·)`. -/
theorem lscTendsto_pullback {G : ℕ → ℂ × ℂ → EReal} {G₀ : ℂ × ℂ → EReal}
    (hG : LSCTendsto G G₀) {ψ χ : ℕ → ℂ → ℂ} {A B : ℂ → ℂ}
    (hAc : Continuous A) (hBc : Continuous B) (hBA : ∀ x, B (A x) = x)
    (hψ : TendstoLocallyUniformly ψ A atTop) (hχ : TendstoLocallyUniformly χ B atTop)
    (hright : ∀ K : Set ℂ, IsCompact K → ∀ᶠ n in atTop, ∀ y ∈ K, ψ n (χ n y) = y)
    {E : ℕ → ℂ × ℂ → EReal}
    (hE : ∀ K : Set ℂ, IsCompact K → ∀ᶠ n in atTop, ∀ x ∈ K, ∀ y ∈ K,
      E n (x, y) = G n (ψ n x, ψ n y)) :
    LSCTendsto E (fun p => G₀ (A p.1, A p.2)) := by
  have hcomp : ∀ {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}, TendstoLocallyUniformly F f atTop → Continuous f →
      ∀ {u : ℕ → ℂ} {x : ℂ}, Tendsto u atTop (𝓝 x) →
        Tendsto (fun n => F n (u n)) atTop (𝓝 (f x)) :=
    fun hF hf _ _ hu => hF.tendsto_comp hf.continuousAt hu
  refine ⟨fun p q hp => ?_, fun q => ?_⟩
  · -- (i): the lower bound, transported by forward convergence of the endpoints
    have hK : IsCompact (closedBall q.1 1 ∪ closedBall q.2 1) :=
      (isCompact_closedBall _ _).union (isCompact_closedBall _ _)
    have h1 : Tendsto (fun n => (p n).1) atTop (𝓝 q.1) := (continuous_fst.tendsto q).comp hp
    have h2 : Tendsto (fun n => (p n).2) atTop (𝓝 q.2) := (continuous_snd.tendsto q).comp hp
    have hfw : Tendsto (fun n => (ψ n (p n).1, ψ n (p n).2)) atTop (𝓝 (A q.1, A q.2)) :=
      (hcomp hψ hAc h1).prodMk_nhds (hcomp hψ hAc h2)
    have heq : (fun n => E n (p n)) =ᶠ[atTop] fun n => G n (ψ n (p n).1, ψ n (p n).2) := by
      filter_upwards [hE _ hK, eventually_mem_square hp] with n hn hmem
      exact hn _ hmem.1 _ hmem.2
    rw [liminf_congr heq]
    exact hG.1 _ _ hfw
  · -- (ii): recovery sequences, transported by the inverse maps
    obtain ⟨r, hr, hGr⟩ := hG.2 (A q.1, A q.2)
    have hK : IsCompact (closedBall (A q.1) 1 ∪ closedBall (A q.2) 1) :=
      (isCompact_closedBall _ _).union (isCompact_closedBall _ _)
    have h1 : Tendsto (fun n => (r n).1) atTop (𝓝 (A q.1)) := (continuous_fst.tendsto _).comp hr
    have h2 : Tendsto (fun n => (r n).2) atTop (𝓝 (A q.2)) := (continuous_snd.tendsto _).comp hr
    have hp : Tendsto (fun n => (χ n (r n).1, χ n (r n).2)) atTop (𝓝 q) := by
      have := (hcomp hχ hBc h1).prodMk_nhds (hcomp hχ hBc h2)
      rwa [hBA, hBA] at this
    have hK' : IsCompact (closedBall q.1 1 ∪ closedBall q.2 1) :=
      (isCompact_closedBall _ _).union (isCompact_closedBall _ _)
    refine ⟨fun n => (χ n (r n).1, χ n (r n).2), hp, ?_⟩
    refine hGr.congr' ?_
    filter_upwards [hright _ hK, eventually_mem_square hr, hE _ hK', eventually_mem_square hp]
      with n hn hmem hEn hmem'
    rw [hEn _ hmem'.1 _ hmem'.2, hn _ hmem.1, hn _ hmem.2]

/-- Koebe covering for the paper's univalent sequence: every closed disk lies eventually in
`ψ_n(U_n)` (paper l. 225–227 uses this as "`ψ_n(K_n)` eventually contains every fixed target
disk"; here for the full domains). -/
theorem eventually_closedBall_subset_image {U : ℕ → Set ℂ} {ψ : ℕ → ℂ → ℂ} {a : ℂ}
    (hopen : ∀ n, IsOpen (U n)) (hzeroU : ∀ n, (0 : ℂ) ∈ U n)
    (hexhaust : ∀ K : Set ℂ, IsCompact K → ∀ᶠ n in atTop, K ⊆ U n)
    (hd : ∀ n, DifferentiableOn ℂ (ψ n) (U n)) (hinj : ∀ n, InjOn (ψ n) (U n))
    (hzero : ∀ n, ψ n 0 = 0) (ha0 : a ≠ 0)
    (ha : Tendsto (fun n => deriv (ψ n) 0) atTop (𝓝 a)) (ρ : ℝ) :
    ∀ᶠ n in atTop, closedBall (0 : ℂ) ρ ⊆ ψ n '' U n := by
  obtain ⟨r, hrpos, hrLarge, hrsub⟩ := SupercriticalConformalCovariance.Univalent.exhaustion_radii hopen hzeroU hexhaust
  set c : ℕ → ℝ := fun n => QuantumZipper.CA.Koebe.koebeCovConst * r n * ‖deriv (ψ n) 0‖
  have hnorm : Tendsto (fun n => ‖deriv (ψ n) 0‖) atTop (𝓝 ‖a‖) := ha.norm
  have hcLarge : Tendsto c atTop atTop :=
    (hrLarge.const_mul_atTop QuantumZipper.CA.Koebe.koebeCovConst_pos).atTop_mul_pos
      (norm_pos_iff.2 ha0) hnorm
  filter_upwards [hcLarge.eventually_gt_atTop ρ] with n hn y hy
  have hk := QuantumZipper.CA.Koebe.ball_subset_image_koebe ((hd n).mono (hrsub n))
    ((hinj n).mono (hrsub n))
  rw [hzero n] at hk
  have hy' : y ∈ ball (0 : ℂ) (c n) := mem_ball.2 ((mem_closedBall.1 hy).trans_lt hn)
  exact image_mono (hrsub n) (hk hy')

/-- Every compact set lies eventually in `ψ_n(U_n)`, where `invFunOn ψ_n U_n` is a right inverse. -/
theorem eventually_rightInverse_on_compact {U : ℕ → Set ℂ} {ψ : ℕ → ℂ → ℂ} {a : ℂ}
    (hopen : ∀ n, IsOpen (U n)) (hzeroU : ∀ n, (0 : ℂ) ∈ U n)
    (hexhaust : ∀ K : Set ℂ, IsCompact K → ∀ᶠ n in atTop, K ⊆ U n)
    (hd : ∀ n, DifferentiableOn ℂ (ψ n) (U n)) (hinj : ∀ n, InjOn (ψ n) (U n))
    (hzero : ∀ n, ψ n 0 = 0) (ha0 : a ≠ 0)
    (ha : Tendsto (fun n => deriv (ψ n) 0) atTop (𝓝 a)) (K : Set ℂ) (hK : IsCompact K) :
    ∀ᶠ n in atTop, ∀ y ∈ K, ψ n (Function.invFunOn (ψ n) (U n) y) = y := by
  obtain ⟨ρ, hρ⟩ := hK.isBounded.subset_closedBall 0
  filter_upwards [eventually_closedBall_subset_image hopen hzeroU hexhaust hd hinj hzero ha0 ha ρ]
    with n hn y hy
  exact Function.invFunOn_eq (hn (hρ hy))

/-- `+∞`-extension of a function outside `K × K` (paper l. 196). -/
def extendTop (K : Set ℂ) (G : ℂ × ℂ → EReal) (p : ℂ × ℂ) : EReal :=
  open Classical in if p.1 ∈ K ∧ p.2 ∈ K then G p else ⊤

/-- Closed disks of radii `→ ∞` eventually contain every compact set. -/
theorem eventually_subset_closedBall {R : ℕ → ℝ} (hR : Tendsto R atTop atTop) (K : Set ℂ)
    (hK : IsCompact K) : ∀ᶠ n in atTop, K ⊆ closedBall (0 : ℂ) (R n) := by
  obtain ⟨ρ, hρ⟩ := hK.isBounded.subset_closedBall 0
  filter_upwards [hR.eventually_ge_atTop ρ] with n hn
  exact hρ.trans (closedBall_subset_closedBall hn)

/-- **EpigraphPullback, paper form** (l. 194–196, 221–223). In the setting of Lemma 3.3 (`U_n`
exhausting `ℂ`, `ψ_n` univalent on `U_n`, `ψ_n(0) = 0`, `ψ_n'(0) → a ≠ 0`, closed disks
`K_n = B̄_{R_n}` with `R_n → ∞`): if `G n → G₀` in the sense of DG Definition 1.2, then the pullbacks
`ψ_n^* G_n`, extended by `+∞` outside `K_n × K_n`, converge to `(a·)^* G₀`. -/
theorem lscTendsto_pullback_univalent {U : ℕ → Set ℂ} {ψ : ℕ → ℂ → ℂ} {a : ℂ}
    (hopen : ∀ n, IsOpen (U n)) (hzeroU : ∀ n, (0 : ℂ) ∈ U n)
    (hexhaust : ∀ K : Set ℂ, IsCompact K → ∀ᶠ n in atTop, K ⊆ U n)
    (hd : ∀ n, DifferentiableOn ℂ (ψ n) (U n)) (hinj : ∀ n, InjOn (ψ n) (U n))
    (hzero : ∀ n, ψ n 0 = 0) (ha0 : a ≠ 0)
    (ha : Tendsto (fun n => deriv (ψ n) 0) atTop (𝓝 a))
    {R : ℕ → ℝ} (hR : Tendsto R atTop atTop)
    {G : ℕ → ℂ × ℂ → EReal} {G₀ : ℂ × ℂ → EReal} (hG : LSCTendsto G G₀) :
    LSCTendsto (fun n => extendTop (closedBall 0 (R n)) fun p => G n (ψ n p.1, ψ n p.2))
      (fun p => G₀ (a * p.1, a * p.2)) := by
  obtain ⟨hψ, -, hχ, -, -⟩ :=
    SupercriticalConformalCovariance.Univalent.exhausting_univalent_limits 0 hopen hzeroU hexhaust hd hinj hzero ha ha0
  rw [tendstoLocallyUniformlyOn_univ] at hψ hχ
  refine lscTendsto_pullback (A := fun z => a * z) (B := fun z => a⁻¹ * z) hG
    (continuous_const.mul continuous_id) (continuous_const.mul continuous_id)
    (fun x => by simp only [← mul_assoc, inv_mul_cancel₀ ha0, one_mul]) hψ hχ
    (eventually_rightInverse_on_compact hopen hzeroU hexhaust hd hinj hzero ha0 ha) ?_
  intro K hK
  filter_upwards [eventually_subset_closedBall hR K hK] with n hn x hx y hy
  simp only [extendTop, hn hx, hn hy, and_self, ite_true]

end SupercriticalConformalCovariance.Tangent
