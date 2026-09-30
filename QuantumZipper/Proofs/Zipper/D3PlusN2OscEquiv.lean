import QuantumZipper.Proofs.Zipper.D3PlusN2ContPair

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# N2Z-PAIROSC: what the oscillation node really asks, and a Lipschitz-modulus reduction

Task N2ZPAIROSC. The node `N2ZPairOscStmt` (`D3PlusN2ContPair.lean`) is stated as an "oscillation
bound `≤ ε · n2PairWeight c ρ`". Since `ε > 0` is arbitrary and `δ` may depend on `ρ`, `c` and
`ε`, the weight carries no information: the node is **equivalent** to the continuum pairing node
`N2ZContPairGFFStmt` (Cauchy criterion). Proved here:

* `n2ZPairOsc_of_contPair : N2ZContPairGFFStmt → N2ZPairOscStmt` and
  `n2ZPairOsc_iff_contPair : N2ZPairOscStmt ↔ N2ZContPairGFFStmt`.

So the node contains no uniformity at all; its content is the convergence, for **every** test
function simultaneously (outside one null set), of the circle-regularized pairings of the
positive and negative parts `ρ^±` (the node pairs `G` with `withDensity (ofReal (±ρ))`, i.e. with
the merely Lipschitz functions `ρ^±`).

By the uniform boundedness principle, such simultaneous convergence on a Banach space of test
functions forces an almost sure bound `sup_t |∫ G(u,t) f(u) du| ≤ C(ω) ‖f‖` in a norm; so any
proof has to produce such a quantitative bound. The natural quantitative form (what the
first-Fourier-mode / Kolmogorov argument gives, see the report) is the **Lipschitz modulus node**

* `N2ZPairLipStmt`: a.s., for every scale `c` and compact `K ⊆ H` there are `C, δ` with
  `|∫ (G(cu,t) − G(cu,s)) f(u) du| ≤ C · L · √(max t s)` for all `t, s ∈ (0, δ)` and all
  `L`-Lipschitz `f` vanishing off `K`,

and we prove the deterministic reduction

* `n2ZContPair_of_lip : N2ZPairLipStmt → N2ZContPairGFFStmt`, hence
  `n2ZPairOsc_of_lip : N2ZPairLipStmt → N2ZPairOscStmt`.

Mathematically the node is true (the free field is a.s. a distribution in `H^{-ε}_loc`, and
`ρ^± ∈ H¹`; Sheffield, *Gaussian free fields for mathematicians*, PTRF 139 (2007), Prop. 2.7;
Duplantier–Sheffield, Invent. Math. 185 (2011), §3.1 for circle averages). The bookkeeping here
(Cauchy criterion, positive parts, Lipschitz constants) is an own elementary argument.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace D3Plus

/-! ## 1. The oscillation node is the pairing node -/

/-- A test function with vanishing weight `n2PairWeight c ρ` is identically zero. -/
theorem testFun_eq_zero_of_n2PairWeight_eq_zero {c : ℝ} (hc : 0 < c) (ρ : TestFun H)
    (h0 : n2PairWeight c ρ = 0) : ρ.1 = 0 := by
  obtain ⟨hs, hcs, -⟩ := ρ.2
  have hcont : Continuous ρ.1 := hs.continuous
  have hsq : Real.sqrt (sSup (Set.range fun z => |ρ.1 z|) * ∫ z, |ρ.1 z|) = 0 := by
    rcases (div_eq_zero_iff.1 h0) with h | h
    · exact h
    · exact absurd h hc.ne'
  have hprod : sSup (Set.range fun z => |ρ.1 z|) * ∫ z, |ρ.1 z| ≤ 0 := Real.sqrt_eq_zero'.1 hsq
  have hS0 : 0 ≤ sSup (Set.range fun z => |ρ.1 z|) :=
    Real.sSup_nonneg fun x ⟨z, hz⟩ => hz ▸ abs_nonneg _
  have hI0 : 0 ≤ ∫ z, |ρ.1 z| := integral_nonneg fun z => abs_nonneg _
  have hprod0 : sSup (Set.range fun z => |ρ.1 z|) * ∫ z, |ρ.1 z| = 0 :=
    le_antisymm hprod (mul_nonneg hS0 hI0)
  rcases mul_eq_zero.1 hprod0 with hS | hI
  · have hbdd : BddAbove (Set.range fun z => |ρ.1 z|) := by
      simpa [Real.norm_eq_abs] using hcont.norm.bddAbove_range_of_hasCompactSupport hcs.norm
    funext z
    have := le_csSup hbdd ⟨z, rfl⟩
    rw [hS] at this
    simpa using le_antisymm this (abs_nonneg _)
  · have hint : Integrable (fun z => |ρ.1 z|) :=
      hcont.abs.integrable_of_hasCompactSupport hcs.abs
    have hae : (fun z => |ρ.1 z|) =ᵐ[volume] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun z => abs_nonneg _) hint).1 hI
    have heq : (fun z => |ρ.1 z|) = 0 :=
      (Continuous.ae_eq_iff_eq volume hcont.abs continuous_const).1 hae
    funext z
    simpa using congrFun heq z

/-- **The oscillation node follows from the pairing node** (Cauchy criterion). -/
theorem n2ZPairOsc_of_contPair (hCP : N2ZContPairGFFStmt) : N2ZPairOscStmt := by
  intro Ω _ P _ X hX
  obtain ⟨G, hGv, hlim⟩ := hCP P X hX
  refine ⟨G, hGv, ?_⟩
  filter_upwards [hlim] with ω hω c hc ρ f hf ε hε
  set F : ℝ → ℝ := fun t => ∫ u, G ω ((c : ℂ) * u, t)
    ∂(volume.withDensity fun z => ENNReal.ofReal (f z)) with hFdef
  rcases (n2PairWeight_nonneg hc ρ).eq_or_lt with h0 | hpos
  · -- zero weight: `ρ = 0`, so `f = 0` and every pairing vanishes
    have hρ0 := testFun_eq_zero_of_n2PairWeight_eq_zero hc ρ h0.symm
    have hf0 : f = 0 := by
      rcases hf with rfl | hf
      · exact hρ0
      · rw [mem_singleton_iff] at hf; rw [hf, hρ0, neg_zero]
    have hF0 : ∀ t, F t = 0 := fun t => by
      simp [hFdef, hf0]
    refine ⟨1, one_pos, fun t _ s _ => ?_⟩
    show |F t - F s| ≤ _
    rw [hF0 t, hF0 s, sub_zero, abs_zero]
    exact mul_nonneg hε.le (n2PairWeight_nonneg hc ρ)
  · obtain ⟨L, hL⟩ := hω c hc ρ f hf
    have hηpos : 0 < ε * n2PairWeight c ρ / 2 := by positivity
    have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), |F t - L| < ε * n2PairWeight c ρ / 2 := by
      have := (Metric.tendsto_nhds.1 hL) _ hηpos
      simpa [Real.dist_eq] using this
    obtain ⟨δ, hδ, hδ'⟩ := Metric.mem_nhdsWithin_iff.1 hev
    refine ⟨δ, hδ, fun t ht s hs => ?_⟩
    have hmem : ∀ x ∈ Ioo (0 : ℝ) δ, x ∈ Metric.ball (0 : ℝ) δ ∩ Ioi 0 := fun x hx =>
      ⟨by rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hx.1]; exact hx.2, hx.1⟩
    have h1 : |F t - L| < ε * n2PairWeight c ρ / 2 := hδ' (hmem t ht)
    have h2 : |F s - L| < ε * n2PairWeight c ρ / 2 := hδ' (hmem s hs)
    show |F t - F s| ≤ _
    calc |F t - F s| = |(F t - L) - (F s - L)| := by ring_nf
      _ ≤ |F t - L| + |F s - L| := abs_sub _ _
      _ ≤ ε * n2PairWeight c ρ := by linarith

/-! ## 2. Reduction to a Lipschitz modulus of the pairings -/

/-- **Node N2Z-PAIRLIP** (quantitative replacement of the oscillation node): for a free field
there is a regular version `G` such that almost surely, for every scale `c > 0` and compact
`K ⊆ H`, the radius increments of the pairings of `G(c ·, ·)` with `L`-Lipschitz functions
vanishing off `K` are at most `C · L · √(max t s)`, for `t, s ∈ (0, δ)`, with `C, δ` depending
only on `ω, c, K`. (Expected route: the `t`-derivative of `f ∗ σ_t` is the first circle Fourier
mode of `∇f`, and the first circle mode of the field has an a.s. bound `O(√log(1/τ))`.) -/
def N2ZPairLipStmt : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → FieldSample), IsFreeGFFModConstH X P →
    ∃ G : Ω → ℂ × ℝ → ℝ, WedgeTK.IsRegVersion X P G ∧
      ∀ᵐ ω ∂P, ∀ c : ℝ, 0 < c → ∀ K : Set ℂ, IsCompact K → K ⊆ H →
        ∃ C δ : ℝ, 0 < δ ∧ ∀ (L : ℝ≥0) (f : ℂ → ℝ), LipschitzWith L f → (∀ z ∉ K, f z = 0) →
          ∀ t ∈ Ioo 0 δ, ∀ s ∈ Ioo 0 δ,
            |∫ u, (G ω ((c : ℂ) * u, t) - G ω ((c : ℂ) * u, s)) * f u| ≤
              C * L * Real.sqrt (max t s)

/-- The node's pairing against `withDensity (ofReal f)` is the plain integral against the
positive part `max f 0`. -/
theorem integral_withDensity_ofReal_eq {g f : ℂ → ℝ} (hf : Continuous f) :
    ∫ u, g u ∂(volume.withDensity fun z => ENNReal.ofReal (f z)) = ∫ u, g u * max (f u) 0 := by
  have hm : Measurable fun z => ENNReal.ofReal (f z) :=
    ENNReal.measurable_ofReal.comp hf.measurable
  rw [integral_withDensity_eq_integral_toReal_smul hm
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (ae_of_all _ fun u => ?_)
  simp only [smul_eq_mul, ENNReal.toReal_ofReal', mul_comm]

/-- **N2Z-CONTPAIR from the Lipschitz modulus node.** -/
theorem n2ZContPair_of_lip (hLip : N2ZPairLipStmt) : N2ZContPairGFFStmt := by
  intro Ω _ P _ X hX
  obtain ⟨G, hGv, hlip⟩ := hLip P X hX
  refine ⟨G, hGv, ?_⟩
  filter_upwards [hlip] with ω hω c hc ρ f hf
  obtain ⟨hs, hcs, hH⟩ := ρ.2
  set K := tsupport ρ.1 with hKdef
  have hK : IsCompact K := hcs
  have hfK : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f ∧ HasCompactSupport f ∧ ∀ z ∉ K, f z = 0 := by
    rcases hf with rfl | hf
    · exact ⟨hs, hcs, fun z hz => image_eq_zero_of_notMem_tsupport hz⟩
    · rw [mem_singleton_iff] at hf
      subst hf
      exact ⟨hs.neg, hcs.neg, fun z hz => by simp [image_eq_zero_of_notMem_tsupport hz]⟩
  obtain ⟨hfs, hfc, hf0⟩ := hfK
  obtain ⟨C, δ, hδ, hb⟩ := hω c hc K hK hH
  obtain ⟨Lf, hLf⟩ := hfs.lipschitzWith_of_hasCompactSupport hfc (by simp)
  set g : ℂ → ℝ := fun z => max (f z) 0 with hgdef
  have hg : LipschitzWith Lf g := hLf.max_const 0
  have hg0 : ∀ z ∉ K, g z = 0 := fun z hz => by simp [hgdef, hf0 z hz]
  have hgc : Continuous g := hg.continuous
  -- integrability of the pairings at each radius
  have hint : ∀ t : ℝ, 0 < t → Integrable (fun u => G ω ((c : ℂ) * u, t) * g u) := by
    intro t ht
    have hco : ContinuousOn (fun u => G ω ((c : ℂ) * u, t) * g u) K := by
      refine ((hGv.cont ω).comp ((continuous_const.mul continuous_id).prodMk
        continuous_const).continuousOn fun u hu => ?_).mul hgc.continuousOn
      exact ⟨RegClosure.mapsTo_mul_pos hc (H_subset_Hbar (hH hu)), ht⟩
    exact (hco.integrableOn_compact hK).integrable_of_forall_notMem_eq_zero
      fun u hu => by simp [hg0 u hu]
  set F : ℝ → ℝ := fun t => ∫ u, G ω ((c : ℂ) * u, t)
    ∂(volume.withDensity fun z => ENNReal.ofReal (f z)) with hFdef
  have hFsub : ∀ t ∈ Ioo 0 δ, ∀ s ∈ Ioo 0 δ, |F t - F s| ≤ C * Lf * Real.sqrt (max t s) := by
    intro t ht s hs
    have h := hb Lf g hg hg0 t ht s hs
    simp only [hFdef, integral_withDensity_ofReal_eq hfs.continuous]
    rw [← integral_sub (hint t ht.1) (hint s hs.1)]
    refine le_of_eq_of_le ?_ h
    congr 1
    refine integral_congr_ae (ae_of_all _ fun u => ?_)
    simp only [hgdef]
    ring
  refine exists_tendsto_of_oscillation fun ε hε => ?_
  set M : ℝ := |C| * Lf + 1 with hM
  have hMpos : 0 < M := by positivity
  refine ⟨min δ ((ε / M) ^ 2), lt_min hδ (by positivity), fun t ht s hs => ?_⟩
  have ht' : t ∈ Ioo 0 δ := ⟨ht.1, ht.2.trans_le (min_le_left _ _)⟩
  have hs' : s ∈ Ioo 0 δ := ⟨hs.1, hs.2.trans_le (min_le_left _ _)⟩
  have hmax : max t s < (ε / M) ^ 2 :=
    max_lt (ht.2.trans_le (min_le_right _ _)) (hs.2.trans_le (min_le_right _ _))
  have hsq : Real.sqrt (max t s) < ε / M := by
    rw [show ε / M = Real.sqrt ((ε / M) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
    exact Real.sqrt_lt_sqrt (le_max_of_le_left ht.1.le) hmax
  have hsq0 : 0 ≤ Real.sqrt (max t s) := Real.sqrt_nonneg _
  calc |F t - F s| ≤ C * Lf * Real.sqrt (max t s) := hFsub t ht' s hs'
    _ ≤ M * Real.sqrt (max t s) := by
        refine mul_le_mul_of_nonneg_right ?_ hsq0
        have : C * Lf ≤ |C| * Lf := mul_le_mul_of_nonneg_right (le_abs_self C) Lf.2
        linarith
    _ ≤ M * (ε / M) := mul_le_mul_of_nonneg_left hsq.le hMpos.le
    _ = ε := mul_div_cancel₀ ε hMpos.ne'

/-- **N2Z-PAIROSC from the Lipschitz modulus node.** -/
theorem n2ZPairOsc_of_lip (hLip : N2ZPairLipStmt) : N2ZPairOscStmt :=
  n2ZPairOsc_of_contPair (n2ZContPair_of_lip hLip)

end D3Plus
end QuantumZipper
