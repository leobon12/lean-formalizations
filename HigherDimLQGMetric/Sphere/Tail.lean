import HigherDimLQGMetric.Sphere.Cont
import HigherDimLQGMetric.Sphere.Avg
import LQGMetric.Gaussian.FerniqueDZZ

/-!
# Gaussian tails of suprema of the recentred sphere-average process over compacts

Packet F3 (Phase A, block A1), complement to targets 3–4: blueprint Lemma `r1:lem:var` (c)
(proposed name `sphereAvg_block_tail`, assigned to packet F3 by BW2; MA5 A3 input (T)).

`exists_tail_iSup_sphereAvg_sub_le` (`d ≥ 2`): for every compact `L ⊆ (0, ∞) × ℝ^d` there are
`c_L, C_L > 0` such that for **every** LGF `h` and every `A ≥ 0`,

`P[sup_{(s,u) ∈ L} |h_s(u) - h_1(0)| ≥ A] ≤ C_L e^{-c_L A²}`.

Proof (blueprint: "centred Gaussian process with a continuous version and bounded variance on `L`;
Borell–TIS"). Modify `X(s,u) = h_s(u) - h_1(0)` on the null set where `(s, u) ↦ h_s(u)` fails to be
continuous (`IsWholeSpaceLGF.ae_continuousOn_sphereAvg`), so that every path is continuous on `L`.
Then `X` is a centred Gaussian process (`IsWholeSpaceLGF.isGaussianProcess_sphereAvg_sub`) with
`E(X_p - X_q)² ≤ C₀ (d + 1)/δ ‖(s,u) - (s',u')‖_∞` (transport bound; `δ = min_L s`) and
`Var X_p ≤ C₀ (2R + 1)/min(δ, 1)` (`R` a bound of `L`). LQGMetric's Dudley chaining
(`SupTail.integral_iSup_family_le`) and the dense-sequence reduction
(`SupTail.integrable_iSup_of_continuous`) bound `E sup_L X` and `E sup_L (-X)` uniformly, and the
Borell–TIS tail `SupTail.tail_iSup_abs_le_gaussian` gives the claim; all constants depend only on
`d` and `L`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ}

/-- Coordinates `(s, u₁, …, u_d)` of a point `(s, u)`. -/
def sphCoord (p : ℝ × Rd d) : Fin (d + 1) → ℝ := Fin.cons p.1 (WithLp.ofLp p.2)

theorem sphCoord_dist_le (p q : ℝ × Rd d) :
    ‖p.2 - q.2‖ + |p.1 - q.1| ≤ (d + 1) * ‖sphCoord p - sphCoord q‖ := by
  have h0 : |p.1 - q.1| ≤ ‖sphCoord p - sphCoord q‖ := by
    have := norm_le_pi_norm (sphCoord p - sphCoord q) 0
    rwa [Pi.sub_apply, Real.norm_eq_abs] at this
  have h1 : ‖WithLp.ofLp p.2 - WithLp.ofLp q.2‖ ≤ ‖sphCoord p - sphCoord q‖ :=
    (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => by
      have := norm_le_pi_norm (sphCoord p - sphCoord q) i.succ
      simpa only [Pi.sub_apply, sphCoord, Fin.cons_succ] using this
  have h2 : ‖p.2 - q.2‖ ≤ d * ‖sphCoord p - sphCoord q‖ := by
    have e : p.2 - q.2 = WithLp.toLp 2 (WithLp.ofLp p.2 - WithLp.ofLp q.2) := rfl
    rw [e]
    exact (norm_toLp_le _).trans (mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg d))
  linarith

theorem norm_sphCoord_le (p : ℝ × Rd d) : ‖sphCoord p‖ ≤ ‖p‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [sphCoord, Fin.cons_zero]
    exact norm_fst_le p
  · simp only [sphCoord, Fin.cons_succ]
    exact (PiLp.norm_apply_le p.2 j).trans (norm_snd_le p)

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistRd d}

/-- **Blueprint `r1:lem:var` (c)** (`d ≥ 2`): for every compact `L ⊆ (0, ∞) × ℝ^d` there are
`c, C > 0` such that for every LGF and every `A ≥ 0`,
`P[sup_{(s,u) ∈ L} |h_s(u) - h_1(0)| ≥ A] ≤ C e^{-c A²}`. -/
theorem exists_tail_iSup_sphereAvg_sub_le (hd : 2 ≤ d) {L : Set (ℝ × Rd d)} (hL : IsCompact L)
    (hL0 : ∀ p ∈ L, 0 < p.1) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
      {h : Ω → DistRd d}, IsWholeSpaceLGF h P → ∀ A : ℝ, 0 ≤ A →
        P {ω | A ≤ ⨆ p : L, |sphereAvg (h ω) p.1.1 p.1.2 - sphereAvg (h ω) 1 0|} ≤
          ENNReal.ofReal (C * Real.exp (-c * A ^ 2)) := by
  obtain ⟨C₀, hC₀0, hC₀⟩ := exists_integral_sq_sphIncProc_le hd
  -- a positive lower bound for the radii and a bound for `L`
  obtain ⟨δ, hδ0, hδ⟩ : ∃ δ > 0, ∀ p ∈ L, δ ≤ p.1 := by
    rcases L.eq_empty_or_nonempty with he | hne
    · exact ⟨1, one_pos, fun p hp => by simp [he] at hp⟩
    · obtain ⟨p₀, hp₀, hmin⟩ := hL.exists_isMinOn hne continuous_fst.continuousOn
      exact ⟨p₀.1, hL0 p₀ hp₀, fun p hp => hmin hp⟩
  obtain ⟨R₁, hR₁⟩ := (isBounded_iff_subset_closedBall 0).1 hL.isBounded
  set R := max R₁ 0 with hRdef
  have hR0 : 0 ≤ R := le_max_right _ _
  have hR : ∀ p ∈ L, ‖p‖ ≤ R := fun p hp => by
    have := hR₁ hp
    rw [mem_closedBall, dist_zero_right] at this
    exact this.trans (le_max_left _ _)
  -- the constants
  set V : ℝ := C₀ * (2 * R + 1) / min δ 1 + 1 with hV
  have hV0 : 0 < V := by have : 0 < min δ 1 := lt_min hδ0 one_pos; positivity
  set Lc : ℝ := Real.sqrt (C₀ * (d + 1) / δ) with hLc
  have hLc0 : 0 ≤ Lc := Real.sqrt_nonneg _
  have hLc2 : Lc ^ 2 = C₀ * (d + 1) / δ := Real.sq_sqrt (by positivity)
  set M : ℝ := 20 * Real.sqrt 5 * Lc * Real.sqrt (((d + 1 : ℕ) + 1) * (2 * R)) with hM
  refine ⟨1 / (2 * (2 * V)), 2 * Real.exp (M ^ 2 / (2 * V)), by positivity, by positivity,
    fun {Ω} _ {P} {h} hh A hA => ?_⟩
  have := hh.gaussian.isProbabilityMeasure
  rcases L.eq_empty_or_nonempty with he | hne
  · -- empty `L`: the supremum is `0`
    subst he
    have hsup : ∀ ω : Ω, (⨆ p : (∅ : Set (ℝ × Rd d)),
        |sphereAvg (h ω) p.1.1 p.1.2 - sphereAvg (h ω) 1 0|) = 0 := fun ω => by
      have : IsEmpty (∅ : Set (ℝ × Rd d)) := Set.isEmpty_coe_sort.2 rfl
      exact Real.iSup_of_isEmpty _
    simp only [hsup]
    rcases hA.eq_or_lt with h0 | hpos
    · subst h0
      simp only [le_refl, ofPred_true, measure_univ]
      rw [show (0 : ℝ) ^ 2 = 0 by norm_num, mul_zero, Real.exp_zero, mul_one]
      exact ENNReal.one_le_ofReal.2 (by
        have := Real.one_le_exp (by positivity : (0 : ℝ) ≤ M ^ 2 / (2 * V)); linarith)
    · have : {ω : Ω | A ≤ (0 : ℝ)} = ∅ := by
        ext ω; simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_le]; exact hpos
      rw [this, measure_empty]
      exact bot_le
  have : Nonempty L := hne.to_subtype
  have : CompactSpace L := isCompact_iff_compactSpace.1 hL
  -- the good set
  set S : Set Ω := {ω | ContinuousOn (fun p : ℝ × Rd d => sphereAvg (h ω) p.1 p.2)
    (Ioi 0 ×ˢ univ)} with hSdef
  have hS : ∀ᵐ ω ∂P, ω ∈ S := (hh.ae_continuousOn_sphereAvg hd).mono fun ω hω => hω.2
  set G : Set Ω := (toMeasurable P Sᶜ)ᶜ with hGdef
  have hGS : G ⊆ S := fun ω hω => by
    by_contra hc
    exact hω (subset_toMeasurable P Sᶜ hc)
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := by
    rw [ae_iff]
    have : {a | ¬a ∈ G} = toMeasurable P Sᶜ := by
      ext ω; simp only [hGdef, mem_compl_iff, not_not, mem_ofPred_eq]
    rw [this, measure_toMeasurable]
    exact ae_iff.1 hS
  -- the process and its modification
  set Y : L → Ω → ℝ := fun p ω => sphereAvg (h ω) p.1.1 p.1.2 - sphereAvg (h ω) 1 0 with hYdef
  set X : L → Ω → ℝ := fun p ω => G.indicator (Y p) ω with hXdef
  have hXY : ∀ p, X p =ᵐ[P] Y p := fun p => by
    filter_upwards [hGae] with ω hω
    simp only [hXdef, indicator_of_mem hω]
  have hYc : ∀ ω ∈ S, Continuous fun p : L => Y p ω := by
    intro ω hω
    have h1 : ContinuousOn (fun p : ℝ × Rd d => sphereAvg (h ω) p.1 p.2) L :=
      hω.mono fun p hp => ⟨hL0 p hp, mem_univ _⟩
    exact (continuousOn_iff_continuous_domRestrict.1 h1).sub continuous_const
  have hXc : ∀ ω, Continuous fun p : L => X p ω := by
    intro ω
    by_cases hω : ω ∈ G
    · simp only [hXdef, indicator_of_mem hω]; exact hYc ω (hGS hω)
    · simp only [hXdef, indicator_of_notMem hω]; exact continuous_const
  have hX'c : ∀ ω, Continuous fun p : L => -X p ω := fun ω => (hXc ω).neg
  -- Gaussianity
  set ι : L → SphPair d := fun p => ⟨((p.1.1, p.1.2), (1, 0)), hL0 p.1 p.2, one_pos⟩
  set ι' : L → SphPair d := fun p => ⟨((1, 0), (p.1.1, p.1.2)), one_pos, hL0 p.1 p.2⟩
  have hG0 := hh.isGaussianProcess_sphereAvg_sub hd
  have hYG : IsGaussianProcess Y P := hG0.comp_right (fun p => Sum.inl (ι p))
  have hXG : IsGaussianProcess X P := hYG.congr fun p => (hXY p).symm
  have hX'G : IsGaussianProcess (fun p ω => -X p ω) P := by
    have h1 : IsGaussianProcess (fun (p : L) ω => sphereAvg (h ω) 1 0 -
        sphereAvg (h ω) p.1.1 p.1.2) P := hG0.comp_right (fun p => Sum.inl (ι' p))
    refine h1.congr fun p => ?_
    filter_upwards [hXY p] with ω hω
    simp only [hω, hYdef, neg_sub]
  have hY0 : ∀ p : L, ∫ ω, Y p ω ∂P = 0 := fun p =>
    (hh.hasGaussianLaw_sphereAvg_sub hd (hL0 p.1 p.2) one_pos p.1.2 0).2
  have hX0 : ∀ p : L, ∫ ω, X p ω ∂P = 0 := fun p => by rw [integral_congr_ae (hXY p), hY0 p]
  have hX'0 : ∀ p : L, ∫ ω, -X p ω ∂P = 0 := fun p => by rw [integral_neg, hX0 p, neg_zero]
  -- the increment bound
  have hinc : ∀ p q : L, ∫ ω, (X p ω - X q ω) ^ 2 ∂P ≤ Lc ^ 2 * ‖sphCoord p.1 - sphCoord q.1‖ := by
    intro p q
    have e : (fun ω => (X p ω - X q ω) ^ 2) =ᵐ[P]
        fun ω => sphIncProc h
          (.inl (sphPt0 (hL0 p.1 p.2) p.1.2, sphPt0 (hL0 q.1 q.2) q.1.2)) ω ^ 2 := by
      filter_upwards [hXY p, hXY q] with ω h1 h2
      rw [h1, h2, sphIncProc_sphPt0]
      simp only [hYdef]
      ring
    rw [integral_congr_ae e]
    obtain ⟨-, -, hvar, hle⟩ := hC₀ hh (sphPt0 (hL0 p.1 p.2) p.1.2) (sphPt0 (hL0 q.1 q.2) q.1.2)
    rw [hvar]
    refine hle.trans ?_
    simp only [SphPt.dist, sphPt0, sub_self, abs_zero, add_zero]
    have hmin : δ ≤ min p.1.1 q.1.1 := le_min (hδ p.1 p.2) (hδ q.1 q.2)
    have hd' := sphCoord_dist_le p.1 q.1
    rw [hLc2]
    calc C₀ * (‖p.1.2 - q.1.2‖ + |p.1.1 - q.1.1|) / min p.1.1 q.1.1
        ≤ C₀ * ((d + 1) * ‖sphCoord p.1 - sphCoord q.1‖) / δ := by
          refine div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hd' hC₀0) hδ0 hmin
      _ = C₀ * (d + 1) / δ * ‖sphCoord p.1 - sphCoord q.1‖ := by ring
  have hinc' : ∀ p q : L, ∫ ω, (-X p ω - -X q ω) ^ 2 ∂P ≤
      Lc ^ 2 * ‖sphCoord p.1 - sphCoord q.1‖ := fun p q => by
    have e : (fun ω => (-X p ω - -X q ω) ^ 2) = fun ω => (X p ω - X q ω) ^ 2 := by
      funext ω; ring
    rw [e]; exact hinc p q
  have hdiam : ∀ p q : L, ‖sphCoord p.1 - sphCoord q.1‖ ≤ 2 * R := fun p q =>
    (norm_sub_le _ _).trans (by
      linarith [(norm_sphCoord_le p.1).trans (hR p.1 p.2),
        (norm_sphCoord_le q.1).trans (hR q.1 q.2)])
  -- chaining
  have hchain : ∀ (Z : L → Ω → ℝ), IsGaussianProcess Z P → (∀ p, ∫ ω, Z p ω ∂P = 0) →
      (∀ p q : L, ∫ ω, (Z p ω - Z q ω) ^ 2 ∂P ≤ Lc ^ 2 * ‖sphCoord p.1 - sphCoord q.1‖) →
      ∀ (n : ℕ) (t : Fin (n + 1) → L), ∫ ω, ⨆ i, Z (t i) ω ∂P ≤ M := by
    intro Z hZ hZ0 hZinc n t
    have := LQGMetric.SupTail.integral_iSup_family_le hZ hZ0 (Nat.succ_pos n) t
      (fun p : L => sphCoord p.1) hLc0 (fun i j => hdiam (t i) (t j))
      (fun i j => hZinc (t i) (t j))
    exact this
  obtain ⟨hint, hMb⟩ := LQGMetric.SupTail.integrable_iSup_of_continuous hXG hXc
    (hchain X hXG hX0 hinc)
  obtain ⟨hint', hMb'⟩ := LQGMetric.SupTail.integrable_iSup_of_continuous hX'G hX'c
    (hchain (fun p ω => -X p ω) hX'G hX'0 hinc')
  -- variance bound
  have hvar : ∀ p : L, Var[X p; P] ≤ Real.sqrt V ^ 2 := by
    intro p
    rw [Real.sq_sqrt hV0.le]
    have hp := hL0 p.1 p.2
    obtain ⟨hG', h0', hvar', hle'⟩ := hC₀ hh (sphPt0 hp p.1.2) (sphPt0 one_pos 0)
    have hVY : Var[X p; P] =
        ∫ ω, sphIncProc h (.inl (sphPt0 hp p.1.2, sphPt0 one_pos 0)) ω ^ 2 ∂P := by
      have e : X p =ᵐ[P] sphIncProc h (.inl (sphPt0 hp p.1.2, sphPt0 one_pos 0)) := by
        filter_upwards [hXY p] with ω hω
        rw [hω, sphIncProc_sphPt0]
      rw [variance_congr e, variance_eq_integral hG'.aemeasurable, h0']
      simp only [sub_zero]
    rw [hVY, hvar']
    refine hle'.trans ?_
    simp only [SphPt.dist, sphPt0, sub_zero, sub_self, abs_zero, add_zero]
    have hp1 : |p.1.1 - 1| ≤ R + 1 := by
      have := (abs_le.1 ((norm_fst_le p.1).trans (hR p.1 p.2) |>.trans' (by
        rw [Real.norm_eq_abs])))
      rw [abs_le]; constructor <;> linarith [this.1, this.2]
    have hp2 : ‖p.1.2‖ ≤ R := (norm_snd_le p.1).trans (hR p.1 p.2)
    have hmin : min δ 1 ≤ min p.1.1 1 := min_le_min (hδ p.1 p.2) le_rfl
    have hmin0 : 0 < min δ 1 := lt_min hδ0 one_pos
    calc C₀ * (‖p.1.2‖ + |p.1.1 - 1|) / min p.1.1 1 ≤ C₀ * (2 * R + 1) / min δ 1 :=
          div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left (by linarith) hC₀0) hmin0 hmin
      _ ≤ V := by rw [hV]; linarith
  have htail := LQGMetric.SupTail.tail_iSup_abs_le_gaussian hXG hX0 hXc hint hint' hMb hMb' hvar hA
  rw [Real.sq_sqrt hV0.le] at htail
  -- transfer to the original process
  have hset : {ω | A ≤ ⨆ p : L, |sphereAvg (h ω) p.1.1 p.1.2 - sphereAvg (h ω) 1 0|} =ᵐ[P]
      {ω | A ≤ ⨆ p : L, |X p ω|} := by
    filter_upwards [hGae] with ω hω
    have : (fun p : L => |X p ω|) = fun p : L => |sphereAvg (h ω) p.1.1 p.1.2 -
        sphereAvg (h ω) 1 0| := by
      funext p; simp only [hXdef, indicator_of_mem hω, hYdef]
    simp only [eq_iff_iff]
    rw [this]
  rw [show -A ^ 2 / (2 * (2 * V)) = -(1 / (2 * (2 * V))) * A ^ 2 by ring] at htail
  rw [measure_congr hset, ← ofReal_measureReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal htail

end HigherDimLQGMetric
