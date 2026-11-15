import InteractingSLE.Foundations.Loewner.YuanSimpleApproxStage
import InteractingSLE.Foundations.Loewner.YuanSimpleApproxDistort
import InteractingSLE.Spec.Sec6.DrivingCriterion
import InteractingSLE.Foundations.Loewner.YuanCorollary13Finite

/-!
# [Yua22] Theorem 1.1, (i) ⇒ (iii): uniform simple approximations of Loewner traces

Y. Yuan, *Topological characterisations of Loewner traces* (Indiana Univ. Math. J. 71 (2022),
arXiv:2003.05535v4), §4 (`source/external/Yua22/arxiv-latex/TraceTopology.tex` L467–L583): every
continuous Loewner trace is, on every compact time interval, a uniform limit of simple curves that
start at `0` and otherwise lie in `ℍ`. The conclusion is stated in the form of the specification's
non-crossing convention for Proposition 6.12 (`Sec6.HasSimpleApproxOn`).

## Main results

* `IsLoewnerTrace.hasSimpleApproxOn`: a continuous Loewner trace `η` of a continuous driver `W`
  (`W 0 = 0`) has the uniform simple approximations on every `[0, S]`;
* `IsLoewnerTraceLT.hasSimpleApproxOn`: the same on `[0, S]` for a trace before a horizon `T > S`.

## Proof

Fix `ε > 0`. Choose a dense sequence of cut times (`exists_isCutData`) and slit lengths `h n` with
`∑ h n` so small that `η` moves by less than `ε` within that time. The cut heights `c N` are
chosen inductively (`exists_height`): inserting the cut `N` moves the curve by at most a prescribed
amount (`exists_stageCurve_succ_repr` and uniform continuity), and changes distances on the earlier
cut segments after `t N` by a factor at least `1 − 2^{−(N+2)}` (`exists_le_norm_sub_add_I`).
Each new cut separates the curve before it from the curve after it by a positive distance
(`stageCurve_succ_ne`), and the later perturbations are summably smaller than that distance. The
uniform limit is therefore injective: two stretched times either have a cut between them, or lie on
one cut segment (`exists_mem_slit_of_origTime_eq`). A linear reparametrization to `[0, S]` gives
the approximant (`exists_simple_approx`).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Function

open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv)
open QuantumZipper.RS (shiftDrive)

namespace InteractingSLE

namespace YuanSimpleApprox

variable {W : ℝ → ℝ} {η : ℝ → ℂ}

/-! ### Cut data -/

/-- **Cut data exist**: a dense injective sequence of cut times in `[0, S)` starting at `0`, and
slit lengths of total length `hb`. -/
theorem exists_isCutData (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    {S hb : ℝ} (hS : 0 < S) (hhb : 0 < hb) :
    ∃ t h : ℕ → ℝ, IsCutData η S t h ∧ ∑' n, h n = hb ∧
      ∀ u u' : ℝ, 0 ≤ u → u < u' → u' ≤ S → ∃ n, u < t n ∧ t n < u' := by
  set C : Set ℝ := {u | u ∈ Ioo 0 S ∧ IsCutTime η u} with hC
  obtain ⟨D, hDC, hDc, hCD⟩ :=
    (TopologicalSpace.IsSeparable.of_separableSpace C).exists_countable_dense_subset
  -- every interval of `[0, S]` contains a point of `D`
  have hdense : ∀ u u' : ℝ, 0 ≤ u → u < u' → u' ≤ S → ∃ d ∈ D, u < d ∧ d < u' := by
    intro u u' hu huu' hu'S
    obtain ⟨v, hv, hvcut⟩ := exists_isCutTime_mem_Ioo hη hW hW0 hu huu'
    have hvC : v ∈ C := ⟨⟨hu.trans_lt hv.1, hv.2.trans_le hu'S⟩, hvcut⟩
    obtain ⟨d, hd, hdD⟩ := mem_closure_iff.1 (hCD hvC) (Ioo u u') isOpen_Ioo hv
    exact ⟨d, hdD, hd.1, hd.2⟩
  have hDinf : D.Infinite := by
    intro hfin
    obtain ⟨d, hdD, -⟩ := hdense 0 S le_rfl hS le_rfl
    -- a finite set has a point closest to `0` from the right; nothing of `D` lies below it
    obtain ⟨m, hmD, hmin⟩ := Set.exists_min_image D id hfin ⟨d, hdD⟩
    have hm0 : 0 < m := (hDC hmD).1.1
    obtain ⟨d', hd'D, -, hd'm⟩ := hdense 0 m le_rfl hm0 ((hDC hmD).1.2.le)
    exact absurd (hmin d' hd'D) (not_le.2 hd'm)
  have : Encodable D := hDc.toEncodable
  have : Infinite D := hDinf.to_subtype
  have : Denumerable D := Denumerable.ofEncodableOfInfinite D
  set e : ℕ ≃ D := (Denumerable.eqv D).symm with he
  set t : ℕ → ℝ := fun n => Nat.casesOn n 0 fun m => (e m : ℝ) with ht
  have ht0 : t 0 = 0 := rfl
  have htsucc : ∀ m, t (m + 1) = e m := fun m => rfl
  have heD : ∀ m, (e m : ℝ) ∈ C := fun m => hDC (e m).2
  refine ⟨t, fun n => hb / 2 / 2 ^ n, ⟨?_, ht0, ?_, ?_, ?_, ?_, ?_⟩, tsum_geometric_two' hb, ?_⟩
  · intro n n' hnn'
    cases n with
    | zero =>
      cases n' with
      | zero => rfl
      | succ m' =>
        exfalso
        rw [ht0, htsucc] at hnn'
        exact (heD m').1.1.ne hnn'
    | succ m =>
      cases n' with
      | zero =>
        exfalso
        rw [ht0, htsucc] at hnn'
        exact (heD m).1.1.ne' hnn'
      | succ m' =>
        rw [htsucc, htsucc] at hnn'
        exact congrArg (· + 1) (e.injective (Subtype.ext hnn'))
  · intro n hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    rw [htsucc]; exact (heD m).1.1
  · intro n
    cases n with
    | zero => rw [ht0]; exact hS
    | succ m => rw [htsucc]; exact (heD m).1.2
  · intro n hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    rw [htsucc]; exact (heD m).2
  · intro n; positivity
  · exact (summable_geometric_two' hb)
  · intro u u' hu huu' hu'S
    obtain ⟨d, hdD, hud, hdu'⟩ := hdense u u' hu huu' hu'S
    refine ⟨e.symm ⟨d, hdD⟩ + 1, ?_, ?_⟩ <;> rw [htsucc, Equiv.apply_symm_apply] <;> assumption

/-! ### Bookkeeping for the inductive choice of the heights -/

/-- `min (ε, f 0, …, f (N − 1))`. -/
def minUpTo (f : ℕ → ℝ) (ε : ℝ) : ℕ → ℝ
  | 0 => ε
  | N + 1 => min (minUpTo f ε N) (f N)

theorem minUpTo_pos {f : ℕ → ℝ} {ε : ℝ} (hε : 0 < ε) {N : ℕ} (hf : ∀ k < N, 0 < f k) :
    0 < minUpTo f ε N := by
  induction N with
  | zero => exact hε
  | succ N ih => exact lt_min (ih fun k hk => hf k (by omega)) (hf N (by omega))

theorem minUpTo_le_left (f : ℕ → ℝ) (ε : ℝ) (N : ℕ) : minUpTo f ε N ≤ ε := by
  induction N with
  | zero => exact le_rfl
  | succ N ih => exact (min_le_left _ _).trans ih

theorem minUpTo_le (f : ℕ → ℝ) (ε : ℝ) {k N : ℕ} (hk : k < N) : minUpTo f ε N ≤ f k := by
  induction N with
  | zero => omega
  | succ N ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with h' | h'
    · exact (min_le_left _ _).trans (ih h')
    · rw [h']; exact min_le_right _ _

theorem minUpTo_congr {f f' : ℕ → ℝ} (ε : ℝ) {N : ℕ} (hf : ∀ k < N, f k = f' k) :
    minUpTo f ε N = minUpTo f' ε N := by
  induction N with
  | zero => rfl
  | succ N ih => simp only [minUpTo, ih fun k hk => hf k (by omega), hf N (by omega)]

variable {t h : ℕ → ℝ} {S : ℝ}

/-- The **separation** of the stage-`(k+1)` curve by the cut `k`: the least distance between the
curve before the slit interval `I_k` and the curve after it (up to the end `L` of the stretched
time). -/
def sepDist (W : ℝ → ℝ) (t h c : ℕ → ℝ) (L : ℝ) (k : ℕ) : ℝ :=
  sInf ((fun p : ℝ × ℝ => ‖stageCurve W t h c (k + 1) p.1 - stageCurve W t h c (k + 1) p.2‖) ''
    (Icc 0 (slitStart t h k) ×ˢ Icc (slitStart t h k + h k) L))

theorem sepDist_congr {c c' : ℕ → ℝ} {L : ℝ} {k : ℕ} (hcc : ∀ m < k + 1, c m = c' m) :
    sepDist W t h c L k = sepDist W t h c' L k := by
  unfold sepDist
  congr 1
  refine image_congr fun p _ => ?_
  rw [stageCurve_congr hcc, stageCurve_congr hcc]

theorem sepDist_le {c : ℕ → ℝ} {L : ℝ} {k : ℕ} {s s' : ℝ} (hs : s ∈ Icc 0 (slitStart t h k))
    (hs' : s' ∈ Icc (slitStart t h k + h k) L) :
    sepDist W t h c L k ≤ ‖stageCurve W t h c (k + 1) s - stageCurve W t h c (k + 1) s'‖ :=
  csInf_le ⟨0, by rintro _ ⟨p, -, rfl⟩; exact norm_nonneg _⟩ ⟨(s, s'), ⟨hs, hs'⟩, rfl⟩

section Trace

variable (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
  (hd : IsCutData η S t h)
include hη hW hW0 hd

theorem sepDist_pos {c : ℕ → ℝ} (hc : ∀ n, 0 < c n) {L : ℝ}
    (hL : ∀ k, slitStart t h k + h k ≤ L) (k : ℕ) : 0 < sepDist W t h c L k := by
  set K := Icc 0 (slitStart t h k) ×ˢ Icc (slitStart t h k + h k) L with hK
  have hKc : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hKne : K.Nonempty :=
    ⟨(0, L), ⟨le_rfl, slitStart_nonneg hd.hpos hd.nonneg k⟩, hL k, le_rfl⟩
  have hcont := continuousOn_stageCurve hη hW hW0 hd hc (k + 1)
  have hfc : ContinuousOn
      (fun p : ℝ × ℝ => ‖stageCurve W t h c (k + 1) p.1 - stageCurve W t h c (k + 1) p.2‖) K := by
    refine continuous_norm.comp_continuousOn (ContinuousOn.sub ?_ ?_)
    · exact hcont.comp continuousOn_fst fun p hp => show (0 : ℝ) ≤ p.1 from hp.1.1
    · exact hcont.comp continuousOn_snd fun p hp =>
        show (0 : ℝ) ≤ p.2 from (slitStart_nonneg hd.hpos hd.nonneg k).trans
          ((le_add_of_nonneg_right (hd.hpos k).le).trans hp.2.1)
  obtain ⟨p, hpK, hpeq⟩ := (hKc.image_of_continuousOn hfc).sInf_mem (hKne.image _)
  unfold sepDist
  rw [← hpeq]
  refine norm_pos_iff.2 (sub_ne_zero.2 ?_)
  exact stageCurve_succ_ne hη hW hW0 hd hc k hpK.1.1 hpK.1.2 hpK.2.1

/-- Where the slit `N` has not started, inserting it changes nothing. -/
theorem stageCurve_succ_eq {c : ℕ → ℝ} (hc : ∀ n, 0 < c n) (N : ℕ) {s : ℝ} (hs : 0 ≤ s)
    (hfr : slitFrac t h N s = 0) : stageCurve W t h c (N + 1) s = stageCurve W t h c N s := by
  obtain ⟨_, _, -, -, -, -, -, -, -, -, -, -, hrep⟩ :=
    exists_stageCurve_succ_repr hη hW hW0 hd hc N
  have := (hrep (c N) (hc N) s hs).2 hfr
  rwa [update_eq_self] at this

/-- **One inductive step** (the choice of `h_n` in [Yua22] §4, L578–L583): the height `x` of the new
cut `N` can be chosen so small that the curve moves by at most `e`, and that distances on every
earlier cut segment after `t N` shrink by a factor at least `1 − 2^{−(N+2)}`. -/
theorem exists_height {c : ℕ → ℝ} (hc : ∀ n, 0 < c n) (N : ℕ) {L e : ℝ} (he : 0 < e) :
    ∃ x : ℝ, 0 < x ∧
      (∀ s ∈ Icc 0 L,
        ‖stageCurve W t h (update c N x) (N + 1) s - stageCurve W t h c N s‖ ≤ e) ∧
      ∀ k < N, t N < t k → ∀ s ∈ Icc (slitStart t h k) (slitStart t h k + h k),
        ∀ s' ∈ Icc (slitStart t h k) (slitStart t h k + h k),
        (1 - (1 / 2) ^ (N + 2)) * ‖stageCurve W t h c N s - stageCurve W t h c N s'‖ ≤
          ‖stageCurve W t h (update c N x) (N + 1) s -
            stageCurve W t h (update c N x) (N + 1) s'‖ := by
  obtain ⟨Φ, z, hΦc, -, hΦd, hΦi, -, hzc, hzH, hzcut, -, hrepN, hrep⟩ :=
    exists_stageCurve_succ_repr hη hW hW0 hd hc N
  set U : Set ℝ := {s | 0 ≤ s ∧ t N ≤ origTime t h s} with hU
  have hUc : IsClosed U := (isClosed_le continuous_const continuous_id).inter
    (isClosed_le continuous_const (continuous_origTime hd.hpos hd.summable))
  -- (1) the uniform continuity of `Φ` near the values of `z`
  set Z := z '' (U ∩ Icc 0 L) with hZ
  have hZc : IsCompact Z :=
    ((isCompact_Icc.inter_left hUc)).image_of_continuousOn (hzc.mono inter_subset_left)
  set K := (fun p : ℂ × ℝ => p.1 + (p.2 : ℂ) * I) '' (Z ×ˢ Icc (0 : ℝ) 1) with hK
  have hKc : IsCompact K := (hZc.prod isCompact_Icc).image (by fun_prop)
  have hKsub : K ⊆ Hbar := by
    rintro _ ⟨⟨w, θ⟩, ⟨⟨s, hs, rfl⟩, hθ⟩, rfl⟩
    show 0 ≤ (z s + (θ : ℂ) * I).im
    have : (0 : ℝ) ≤ (z s).im := hzH s hs.1.1 hs.1.2
    simp only [add_im, mul_im, ofReal_re, I_im, ofReal_im, I_re, mul_zero, add_zero]
    linarith [hθ.1]
  obtain ⟨δ, hδ, hδc⟩ := Metric.uniformContinuousOn_iff.1
    (hKc.uniformContinuousOn_of_continuous (hΦc.mono hKsub)) e he
  -- (2) the distortion on the earlier cut segments after `t N`
  have hdist : ∀ k, ∃ δk : ℝ, 0 < δk ∧ (k < N → t N < t k → ∀ θ ∈ Icc 0 δk,
      ∀ s ∈ Icc (slitStart t h k) (slitStart t h k + h k),
      ∀ s' ∈ Icc (slitStart t h k) (slitStart t h k + h k),
      (1 - (1 / 2) ^ (N + 2)) * ‖Φ (z s) - Φ (z s')‖ ≤
        ‖Φ (z s + θ * I) - Φ (z s' + θ * I)‖) := by
    intro k
    by_cases hk : k < N ∧ t N < t k
    · have hk0 : k ≠ 0 := fun hk0 => by
        rw [hk0, hd.zero] at hk; exact absurd hk.2 (not_lt.2 (hd.nonneg N))
      set Ik := Icc (slitStart t h k) (slitStart t h k + h k)
      have hIkU : Ik ⊆ U := fun s hs =>
        ⟨(slitStart_nonneg hd.hpos hd.nonneg k).trans hs.1,
          (origTime_eq_of_mem hd.hpos hd.summable hd.inj hs).symm ▸ hk.2.le⟩
      have hA : IsCompact (z '' Ik) := isCompact_Icc.image_of_continuousOn (hzc.mono hIkU)
      have hAH : z '' Ik ⊆ H := by
        rintro _ ⟨s, hs, rfl⟩
        exact hzcut s (hIkU hs).1 k hk0 hk.2 (origTime_eq_of_mem hd.hpos hd.summable hd.inj hs)
      obtain ⟨δk, hδk, hδkc⟩ := exists_le_norm_sub_add_I QuantumZipper.isOpen_H hΦd hΦi hA hAH
        (ε := (1 / 2) ^ (N + 2)) (by positivity)
      exact ⟨δk, hδk, fun _ _ θ hθ s hs s' hs' =>
        hδkc θ hθ _ ⟨s, hs, rfl⟩ _ ⟨s', hs', rfl⟩⟩
    · exact ⟨1, one_pos, fun h1 h2 => absurd ⟨h1, h2⟩ hk⟩
  choose δk hδk using hdist
  set x := min (min 1 (δ / 2)) (minUpTo δk 1 N) with hx
  have hx0 : 0 < x := lt_min (lt_min one_pos (by linarith)) (minUpTo_pos one_pos fun k _ =>
    (hδk k).1)
  have hx1 : x ≤ 1 := (min_le_left _ _).trans (min_le_left _ _)
  have hxδ : x ≤ δ / 2 := (min_le_left _ _).trans (min_le_right _ _)
  refine ⟨x, hx0, fun s hs => ?_, fun k hk hNk s hs s' hs' => ?_⟩
  · by_cases hfr : slitFrac t h N s = 0
    · rw [(hrep x hx0 s hs.1).2 hfr, sub_self, norm_zero]; exact he.le
    · have hτ : t N ≤ origTime t h s := origTime_ge_of_slitFrac_pos hd.hpos hd.summable hd.inj
        (lt_of_le_of_ne (slitFrac_nonneg N s) (Ne.symm hfr))
      rw [(hrep x hx0 s hs.1).1 hτ, hrepN s hs.1 hτ]
      have hθ0 : 0 ≤ x * slitFrac t h N s := mul_nonneg hx0.le (slitFrac_nonneg N s)
      have hθ1 : x * slitFrac t h N s ≤ x := mul_le_of_le_one_right hx0.le (slitFrac_le_one N s)
      have hzK : z s ∈ K := ⟨(z s, 0), ⟨⟨s, ⟨⟨hs.1, hτ⟩, hs⟩, rfl⟩, ⟨le_rfl, zero_le_one⟩⟩,
        by simp⟩
      have hzK' : ((x * slitFrac t h N s : ℝ) : ℂ) * I + z s ∈ K :=
        ⟨(z s, x * slitFrac t h N s), ⟨⟨s, ⟨⟨hs.1, hτ⟩, hs⟩, rfl⟩, ⟨hθ0, hθ1.trans hx1⟩⟩,
          by simp only; ring⟩
      have hdd : dist (((x * slitFrac t h N s : ℝ) : ℂ) * I + z s) (z s) < δ := by
        rw [dist_eq_norm, add_sub_cancel_right, norm_mul, Complex.norm_I, mul_one,
          Complex.norm_real, Real.norm_of_nonneg hθ0]
        linarith
      have := hδc _ hzK' _ hzK hdd
      rw [dist_eq_norm] at this
      exact this.le
  · have hτ := origTime_eq_of_mem hd.hpos hd.summable hd.inj hs
    have hτ' := origTime_eq_of_mem hd.hpos hd.summable hd.inj hs'
    have hs0 : 0 ≤ s := (slitStart_nonneg hd.hpos hd.nonneg k).trans hs.1
    have hs'0 : 0 ≤ s' := (slitStart_nonneg hd.hpos hd.nonneg k).trans hs'.1
    have hfr : slitFrac t h N s = 1 :=
      slitFrac_eq_one_of_lt_origTime hd.hpos hd.summable hd.inj (hτ ▸ hNk)
    have hfr' : slitFrac t h N s' = 1 :=
      slitFrac_eq_one_of_lt_origTime hd.hpos hd.summable hd.inj (hτ' ▸ hNk)
    rw [(hrep x hx0 s hs0).1 (hτ ▸ hNk.le), (hrep x hx0 s' hs'0).1 (hτ' ▸ hNk.le),
      hrepN s hs0 (hτ ▸ hNk.le), hrepN s' hs'0 (hτ' ▸ hNk.le), hfr, hfr', mul_one,
      add_comm _ (z s), add_comm _ (z s')]
    exact (hδk k).2 hk hNk x ⟨hx0.le, (min_le_right _ _).trans (minUpTo_le δk 1 hk)⟩ s hs s' hs'

end Trace

section Trace

variable (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
  (hd : IsCutData η S t h)
include hη hW hW0 hd

/-- **The inductive choice of all heights** ([Yua22] §4, L578–L583). Each step moves the curve by
at most `2^{−(N+3)}` times the minimum of `ε` and the earlier separations, and preserves the
distances on the earlier cut segments after `t N` up to the factor `1 − 2^{−(N+2)}`. -/
theorem exists_heights {L ε : ℝ} (hε : 0 < ε) (hL : ∀ k, slitStart t h k + h k ≤ L) :
    ∃ c : ℕ → ℝ, (∀ n, 0 < c n) ∧
      (∀ N, ∀ s ∈ Icc 0 L, ‖stageCurve W t h c (N + 1) s - stageCurve W t h c N s‖ ≤
        minUpTo (sepDist W t h c L) ε N / 2 ^ (N + 3)) ∧
      ∀ N, ∀ k < N, t N < t k → ∀ s ∈ Icc (slitStart t h k) (slitStart t h k + h k),
        ∀ s' ∈ Icc (slitStart t h k) (slitStart t h k + h k),
        (1 - (1 / 2) ^ (N + 2)) * ‖stageCurve W t h c N s - stageCurve W t h c N s'‖ ≤
          ‖stageCurve W t h c (N + 1) s - stageCurve W t h c (N + 1) s'‖ := by
  have hstep : ∀ (c : ℕ → ℝ) (N : ℕ), ∃ x : ℝ, (∀ n, 0 < c n) → 0 < x ∧
      (∀ s ∈ Icc 0 L, ‖stageCurve W t h (update c N x) (N + 1) s - stageCurve W t h c N s‖ ≤
        minUpTo (sepDist W t h c L) ε N / 2 ^ (N + 3)) ∧
      ∀ k < N, t N < t k → ∀ s ∈ Icc (slitStart t h k) (slitStart t h k + h k),
        ∀ s' ∈ Icc (slitStart t h k) (slitStart t h k + h k),
        (1 - (1 / 2) ^ (N + 2)) * ‖stageCurve W t h c N s - stageCurve W t h c N s'‖ ≤
          ‖stageCurve W t h (update c N x) (N + 1) s -
            stageCurve W t h (update c N x) (N + 1) s'‖ := by
    intro c N
    by_cases hc : ∀ n, 0 < c n
    · have he : 0 < minUpTo (sepDist W t h c L) ε N / 2 ^ (N + 3) :=
        div_pos (minUpTo_pos hε fun k _ => sepDist_pos hη hW hW0 hd hc hL k) (by positivity)
      obtain ⟨x, hx, h1, h2⟩ := exists_height hη hW hW0 hd hc N (L := L) he
      exact ⟨x, fun _ => ⟨hx, h1, h2⟩⟩
    · exact ⟨1, fun h' => absurd h' hc⟩
  choose g hg using hstep
  set F : ℕ → ℕ → ℝ := fun N => Nat.rec (fun _ => 1) (fun N FN => update FN N (g FN N)) N
    with hF
  have hFsucc : ∀ N, F (N + 1) = update (F N) N (g (F N) N) := fun N => rfl
  have hFpos : ∀ N n, 0 < F N n := by
    intro N
    induction N with
    | zero => intro n; exact one_pos
    | succ N ih =>
      intro n
      rw [hFsucc]
      by_cases hn : n = N
      · rw [hn, update_self]; exact (hg (F N) N ih).1
      · rw [update_of_ne hn]; exact ih n
  set c : ℕ → ℝ := fun N => F (N + 1) N with hc
  have hFc : ∀ M m, m < M → F M m = c m := by
    intro M
    induction M with
    | zero => intro m hm; omega
    | succ M ih =>
      intro m hm
      rcases Nat.lt_succ_iff_lt_or_eq.1 hm with h' | h'
      · rw [hFsucc, update_of_ne (Nat.ne_of_lt h'), ih m h']
      · rw [h']
  have hcpos : ∀ n, 0 < c n := fun n => hFpos (n + 1) n
  have hcN : ∀ N, update (F N) N (g (F N) N) = F (N + 1) := fun N => (hFsucc N).symm
  have hstage : ∀ M, stageCurve W t h c M = stageCurve W t h (F M) M := fun M => funext
    fun s => stageCurve_congr (fun m hm => (hFc M m hm).symm) s
  have hsep : ∀ N, minUpTo (sepDist W t h c L) ε N = minUpTo (sepDist W t h (F N) L) ε N :=
    fun N => minUpTo_congr ε fun k hk => sepDist_congr fun m hm =>
      (hFc N m (by omega)).symm
  refine ⟨c, hcpos, fun N s hs => ?_, fun N k hk hNk s hs s' hs' => ?_⟩
  · rw [hstage (N + 1), hstage N, hsep N, ← hcN N]
    exact (hg (F N) N (hFpos N)).2.1 s hs
  · rw [hstage (N + 1), hstage N, ← hcN N]
    exact (hg (F N) N (hFpos N)).2.2 k hk hNk s hs s' hs'

end Trace

/-! ### The limit curve -/

theorem norm_tsum_shift_le {f : ℕ → ℂ} {A : ℝ} {M : ℕ}
    (hf : ∀ n, M ≤ n → ‖f n‖ ≤ A / 2 ^ (n + 3)) : ‖∑' n, f (n + M)‖ ≤ A / 2 ^ (M + 2) := by
  refine tsum_of_norm_bounded (hasSum_geometric_two' (A / 2 ^ (M + 2))) fun n => ?_
  have := hf (n + M) (by omega)
  have e : A / 2 ^ (n + M + 3) = A / 2 ^ (M + 2) / 2 / 2 ^ n := by
    rw [div_div, div_div]; congr 1; ring
  rwa [e] at this

theorem tendsto_div_two_pow (ε : ℝ) : Tendsto (fun M : ℕ => ε / 2 ^ (M + 2)) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop ((tendsto_pow_atTop_atTop_of_one_lt one_lt_two).comp
    (tendsto_add_atTop_nat 2))

section Trace

variable (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
  (hd : IsCutData η S t h)
include hη hW hW0 hd

/-- **The limit of the stage curves** is a continuous injective curve on `[0, L]` starting at `0`,
in `ℍ` at positive times, within `ε / 4` of the halted trace ([Yua22] §4, L513–L521). -/
theorem exists_limit_curve {c : ℕ → ℝ} (hc : ∀ n, 0 < c n) {L ε : ℝ}
    (hL : ∀ k, slitStart t h k + h k ≤ L) (hLS : origTime t h L = S)
    (hdense : ∀ u u' : ℝ, 0 ≤ u → u < u' → u' ≤ S → ∃ n, u < t n ∧ t n < u')
    (hstep : ∀ N, ∀ s ∈ Icc 0 L, ‖stageCurve W t h c (N + 1) s - stageCurve W t h c N s‖ ≤
        minUpTo (sepDist W t h c L) ε N / 2 ^ (N + 3))
    (hdist : ∀ N, ∀ k < N, t N < t k → ∀ s ∈ Icc (slitStart t h k) (slitStart t h k + h k),
        ∀ s' ∈ Icc (slitStart t h k) (slitStart t h k + h k),
        (1 - (1 / 2) ^ (N + 2)) * ‖stageCurve W t h c N s - stageCurve W t h c N s'‖ ≤
          ‖stageCurve W t h c (N + 1) s - stageCurve W t h c (N + 1) s'‖) :
    ∃ G : ℝ → ℂ, ContinuousOn G (Icc 0 L) ∧ InjOn G (Icc 0 L) ∧ G 0 = 0 ∧
      MapsTo G (Ioc 0 L) H ∧ ∀ s ∈ Icc 0 L, ‖G s - η (origTime t h s)‖ ≤ ε / 4 := by
  set Γ := stageCurve W t h c with hΓ
  set f : ℕ → ℝ → ℂ := fun n s => Γ (n + 1) s - Γ n s with hf
  have hfb : ∀ n, ∀ s ∈ Icc 0 L, ‖f n s‖ ≤ ε / 2 ^ (n + 3) := fun n s hs =>
    (hstep n s hs).trans (div_le_div_of_nonneg_right (minUpTo_le_left _ _ _) (by positivity))
  have hfb' : ∀ k n, k < n → ∀ s ∈ Icc 0 L, ‖f n s‖ ≤ sepDist W t h c L k / 2 ^ (n + 3) :=
    fun k n hkn s hs =>
      (hstep n s hs).trans (div_le_div_of_nonneg_right (minUpTo_le _ _ hkn) (by positivity))
  have hgeom : Summable fun n : ℕ => ε / 2 ^ (n + 3) := by
    have := summable_geometric_two' (ε / 2 ^ 2)
    refine this.congr fun n => ?_
    rw [div_div, div_div]; congr 1; ring
  have hsumm : ∀ s ∈ Icc 0 L, Summable fun n => f n s := fun s hs =>
    Summable.of_norm_bounded hgeom fun n => hfb n s hs
  set G : ℝ → ℂ := fun s => Γ 0 s + ∑' n, f n s with hG
  have htail : ∀ M, ∀ s ∈ Icc 0 L, G s - Γ M s = ∑' n, f (n + M) s := by
    intro M s hs
    have h1 := (hsumm s hs).sum_add_tsum_nat_add M
    have h2 : ∑ i ∈ Finset.range M, f i s = Γ M s - Γ 0 s :=
      Finset.sum_range_sub (fun n => Γ n s) M
    rw [h2] at h1
    simp only [hG]
    rw [← h1]; ring
  have hclose : ∀ M, ∀ s ∈ Icc 0 L, ‖G s - Γ M s‖ ≤ ε / 2 ^ (M + 2) := fun M s hs => by
    rw [htail M s hs]; exact norm_tsum_shift_le fun n _ => hfb n s hs
  have hcloseSep : ∀ k, ∀ s ∈ Icc 0 L, ‖G s - Γ (k + 1) s‖ ≤ sepDist W t h c L k / 8 := by
    intro k s hs
    have hD : 0 ≤ sepDist W t h c L k := (sepDist_pos hη hW hW0 hd hc hL k).le
    rw [htail (k + 1) s hs]
    refine (norm_tsum_shift_le fun n hn => hfb' k n (by omega) s hs).trans ?_
    refine div_le_div_of_nonneg_left hD (by norm_num) ?_
    calc (8 : ℝ) = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (k + 1 + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hlim : ∀ s ∈ Icc 0 L, Tendsto (fun M => Γ M s) atTop (𝓝 (G s)) := by
    intro s hs
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (fun M => ?_) (tendsto_div_two_pow ε)
    rw [norm_sub_rev]; exact hclose M s hs
  have hcont : ∀ n, ContinuousOn (Γ n) (Icc 0 L) := fun n =>
    (continuousOn_stageCurve hη hW hW0 hd hc n).mono fun s hs => hs.1
  have hGc : ContinuousOn G (Icc 0 L) :=
    (hcont 0).add (continuousOn_tsum (fun n => (hcont (n + 1)).sub (hcont n)) hgeom
      fun n s hs => hfb n s hs)
  have hΓ0 : ∀ n, Γ n 0 = 0 := fun n => stageCurve_zero_time hW hd n
  have hG0 : G 0 = 0 := by
    simp only [hG, hf, hΓ0, sub_self, tsum_zero, add_zero]
  -- the curve before and after a cut
  have hsepG : ∀ n, ∀ s ∈ Icc 0 (slitStart t h n), ∀ s' ∈ Icc (slitStart t h n + h n) L,
      G s ≠ G s' := by
    intro n s hs s' hs' heq
    have hsL : s ∈ Icc 0 L := ⟨hs.1, hs.2.trans ((le_add_of_nonneg_right (hd.hpos n).le).trans
      (hL n))⟩
    have hs'L : s' ∈ Icc 0 L := ⟨(slitStart_nonneg hd.hpos hd.nonneg n).trans
      ((le_add_of_nonneg_right (hd.hpos n).le).trans hs'.1), hs'.2⟩
    have hD := sepDist_le (W := W) (c := c) hs hs'
    have hDpos := sepDist_pos hη hW hW0 hd hc hL n
    have e1 := hcloseSep n s hsL
    have e2 := hcloseSep n s' hs'L
    have : ‖Γ (n + 1) s - Γ (n + 1) s'‖ ≤ ‖G s - Γ (n + 1) s‖ + ‖G s' - Γ (n + 1) s'‖ := by
      calc ‖Γ (n + 1) s - Γ (n + 1) s'‖ = ‖(G s' - Γ (n + 1) s') - (G s - Γ (n + 1) s)‖ := by
            rw [heq]; congr 1; ring
        _ ≤ ‖G s' - Γ (n + 1) s'‖ + ‖G s - Γ (n + 1) s‖ := norm_sub_le _ _
        _ = _ := add_comm _ _
    linarith
  -- the curve on a cut segment
  have hslitG : ∀ n, ∀ s ∈ Icc (slitStart t h n) (slitStart t h n + h n),
      ∀ s' ∈ Icc (slitStart t h n) (slitStart t h n + h n), s ≠ s' → G s ≠ G s' := by
    intro n s hs s' hs' hne heq
    have hs0 : 0 ≤ s := (slitStart_nonneg hd.hpos hd.nonneg n).trans hs.1
    have hs'0 : 0 ≤ s' := (slitStart_nonneg hd.hpos hd.nonneg n).trans hs'.1
    have hsL : s ∈ Icc 0 L := ⟨hs0, hs.2.trans (hL n)⟩
    have hs'L : s' ∈ Icc 0 L := ⟨hs'0, hs'.2.trans (hL n)⟩
    set X₀ := ‖Γ (n + 1) s - Γ (n + 1) s'‖ with hX₀def
    have hX₀ : 0 < X₀ := norm_pos_iff.2 (sub_ne_zero.2 fun e =>
      hne (injOn_stageCurve_succ hη hW hW0 hd hc n hs hs' e))
    have hτ := origTime_eq_of_mem hd.hpos hd.summable hd.inj hs
    have hτ' := origTime_eq_of_mem hd.hpos hd.summable hd.inj hs'
    have hpers : ∀ j : ℕ, (1 / 2 + (1 / 2) ^ (j + 1)) * X₀ ≤
        ‖Γ (n + 1 + j) s - Γ (n + 1 + j) s'‖ := by
      intro j
      induction j with
      | zero =>
        rw [add_zero, zero_add, pow_one, show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num, one_mul]
      | succ j ih =>
        set N := n + 1 + j with hN
        have hstepN : (1 - (1 / 2) ^ (N + 2)) * ‖Γ N s - Γ N s'‖ ≤
            ‖Γ (N + 1) s - Γ (N + 1) s'‖ := by
          have hne' : t N ≠ t n := fun e => by have := hd.inj e; omega
          rcases lt_or_gt_of_ne hne' with hlt | hlt
          · exact hdist N n (by omega) hlt s hs s' hs'
          · have hfr : slitFrac t h N s = 0 :=
              slitFrac_eq_zero_of_origTime_lt hd.hpos hd.summable hd.inj (hτ ▸ hlt)
            have hfr' : slitFrac t h N s' = 0 :=
              slitFrac_eq_zero_of_origTime_lt hd.hpos hd.summable hd.inj (hτ' ▸ hlt)
            have e1 : Γ (N + 1) s = Γ N s := stageCurve_succ_eq hη hW hW0 hd hc N hs0 hfr
            have e2 : Γ (N + 1) s' = Γ N s' := stageCurve_succ_eq hη hW hW0 hd hc N hs'0 hfr'
            rw [e1, e2]
            have : (0 : ℝ) ≤ (1 / 2) ^ (N + 2) := by positivity
            nlinarith [norm_nonneg (Γ N s - Γ N s')]
        have hb : (1 / 2 : ℝ) ^ (N + 2) ≤ (1 / 2) ^ (j + 2) :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
        have hb2 : (1 / 2 : ℝ) ^ (j + 2) = (1 / 2) ^ (j + 1) / 2 := by rw [pow_succ]; ring
        have hb1 : (1 / 2 : ℝ) ^ (j + 1) ≤ 1 / 2 := by
          rw [pow_succ]; nlinarith [pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1 / 2)
            (by norm_num : (1 / 2 : ℝ) ≤ 1) (n := j)]
        have hb0 : (0 : ℝ) ≤ (1 / 2) ^ (j + 1) := by positivity
        have ha0 : (0 : ℝ) ≤ (1 / 2) ^ (N + 2) := by positivity
        rw [show n + 1 + (j + 1) = N + 1 by omega]
        refine le_trans ?_ hstepN
        have hfac : 0 ≤ 1 - (1 / 2 : ℝ) ^ (N + 2) := by
          have : (1 / 2 : ℝ) ^ (N + 2) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
          linarith
        calc (1 / 2 + (1 / 2) ^ (j + 1 + 1)) * X₀
            ≤ (1 - (1 / 2) ^ (N + 2)) * ((1 / 2 + (1 / 2) ^ (j + 1)) * X₀) := by
              rw [show j + 1 + 1 = j + 2 by ring, hb2]
              nlinarith [mul_nonneg hb0 hX₀.le, mul_nonneg ha0 hX₀.le,
                mul_nonneg (mul_nonneg ha0 hb0) hX₀.le]
          _ ≤ (1 - (1 / 2) ^ (N + 2)) * ‖Γ N s - Γ N s'‖ := mul_le_mul_of_nonneg_left ih hfac
    have hlimd : Tendsto (fun j : ℕ => ‖Γ (n + 1 + j) s - Γ (n + 1 + j) s'‖) atTop
        (𝓝 ‖G s - G s'‖) :=
      (((hlim s hsL).sub (hlim s' hs'L)).norm).comp (tendsto_atTop_atTop_of_monotone
        (fun a b hab => by omega) fun b => ⟨b, by omega⟩)
    have hge : X₀ / 2 ≤ ‖G s - G s'‖ := by
      refine ge_of_tendsto hlimd (Eventually.of_forall fun j => ?_)
      refine le_trans ?_ (hpers j)
      have : (0 : ℝ) ≤ (1 / 2) ^ (j + 1) := by positivity
      nlinarith
    rw [heq, sub_self, norm_zero] at hge
    linarith
  -- injectivity
  have hlt : ∀ s ∈ Icc 0 L, ∀ s' ∈ Icc 0 L, s < s' → G s ≠ G s' := by
    intro s hs s' hs' hss'
    have hmono := monotone_origTime hd.hpos hd.summable hd.inj hss'.le
    rcases hmono.lt_or_eq with hτlt | hτeq
    · have hτ'S : origTime t h s' ≤ S := hLS ▸ monotone_origTime hd.hpos hd.summable hd.inj hs'.2
      obtain ⟨n, h1, h2⟩ := hdense _ _ (hd.origTime_nonneg hs.1) hτlt hτ'S
      exact hsepG n s ⟨hs.1, (slitFrac_eq_zero_iff hd.hpos).1
          (slitFrac_eq_zero_of_origTime_lt hd.hpos hd.summable hd.inj h1)⟩ s'
        ⟨(slitFrac_eq_one_iff hd.hpos).1
          (slitFrac_eq_one_of_lt_origTime hd.hpos hd.summable hd.inj h2), hs'.2⟩
    · obtain ⟨n, hsn, hs'n⟩ := exists_mem_slit_of_origTime_eq hd.hpos hd.summable hd.inj hss' hτeq
      exact hslitG n s hsn s' hs'n hss'.ne
  refine ⟨G, hGc, fun s hs s' hs' heq => ?_, hG0, fun s hs => ?_, fun s hs => ?_⟩
  · by_contra hne
    rcases lt_or_gt_of_ne hne with h' | h'
    · exact hlt s hs s' hs' h' heq
    · exact hlt s' hs' s hs h' heq.symm
  · have hsL : s ∈ Icc 0 L := ⟨hs.1.le, hs.2⟩
    have hfrac : 0 < slitFrac t h 0 s := by
      rcases (slitFrac_nonneg (t := t) (h := h) 0 s).lt_or_eq with h' | h'
      · exact h'
      · have := (slitFrac_eq_zero_iff hd.hpos).1 h'.symm
        rw [hd.slitStart_zero] at this
        exact absurd hs.1 (not_lt.2 this)
    have hpos := mul_pos (hc 0) hfrac
    have him : Tendsto (fun M => (Γ M s).im) atTop (𝓝 (G s).im) :=
      (Complex.continuous_im.tendsto _).comp (hlim s hsL)
    have : c 0 * slitFrac t h 0 s ≤ (G s).im :=
      ge_of_tendsto him (eventually_atTop.2 ⟨1, fun M hM =>
        le_im_stageCurve hη hW hW0 hd hc hM hs.1.le⟩)
    exact lt_of_lt_of_le hpos this
  · have := hclose 0 s hs
    rw [hΓ, stageCurve_zero hη hW hW0 hd hs.1] at this
    calc _ ≤ ε / 2 ^ (0 + 2) := this
      _ = ε / 4 := by norm_num

end Trace

/-! ### The simple approximations -/

/-- **One simple approximant** ([Yua22] §4): for every `ε > 0` there is a continuous injective
curve on `[0, S]`, starting at `0`, in `ℍ` at positive times, within `2ε` of the trace. -/
theorem exists_simple_approx (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    {S ε : ℝ} (hS : 0 < S) (hε : 0 < ε) :
    ∃ γ : ℝ → ℂ, ContinuousOn γ (Icc 0 S) ∧ InjOn γ (Icc 0 S) ∧ γ 0 = 0 ∧
      MapsTo γ (Ioc 0 S) H ∧ ∀ u ∈ Icc 0 S, ‖γ u - η u‖ ≤ 2 * ε := by
  -- uniform continuity of the trace on `[0, S]`
  obtain ⟨δ, hδ, hδc⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous (hη.2.1.mono Icc_subset_Ici_self)) ε hε
  set hb := δ / 2 with hhb
  have hhb0 : 0 < hb := by rw [hhb]; linarith
  obtain ⟨t, h, hd, hsum, hdense⟩ := exists_isCutData hη hW hW0 hS hhb0
  set L := S + ∑' n, h n with hLdef
  have hL : ∀ k, slitStart t h k + h k ≤ L := slitStart_add_le_end hd.hpos hd.summable hd.lt
  have hLS : origTime t h L = S := origTime_end hd.hpos hd.summable hd.lt
  have hLeq : L = S + hb := by rw [hLdef, hsum]
  obtain ⟨c, hc, hstep, hdist⟩ := exists_heights hη hW hW0 hd hε hL
  obtain ⟨G, hGc, hGi, hG0, hGH, hGη⟩ :=
    exists_limit_curve hη hW hW0 hd hc hL hLS hdense hstep hdist
  -- reparametrize `[0, S]` onto `[0, L]`
  set r := L / S with hr
  have hr0 : 0 < r := div_pos (by rw [hLeq]; linarith) hS
  have hmaps : ∀ u ∈ Icc 0 S, u * r ∈ Icc 0 L := fun u hu => ⟨mul_nonneg hu.1 hr0.le, by
    have : u * r ≤ S * r := mul_le_mul_of_nonneg_right hu.2 hr0.le
    rwa [hr, mul_div_cancel₀ _ hS.ne'] at this⟩
  refine ⟨fun u => G (u * r), ?_, ?_, ?_, ?_, ?_⟩
  · exact hGc.comp (continuous_id.mul continuous_const).continuousOn hmaps
  · intro u hu u' hu' heq
    have := hGi (hmaps u hu) (hmaps u' hu') heq
    exact mul_right_cancel₀ hr0.ne' this
  · simp only [zero_mul]; exact hG0
  · intro u hu
    exact hGH ⟨mul_pos hu.1 hr0, (hmaps u ⟨hu.1.le, hu.2⟩).2⟩
  · intro u hu
    set s := u * r with hs
    have hsL := hmaps u hu
    have h1 := hGη s hsL
    -- the original time of `s` is within `hb` of `u`
    have hτ0 : 0 ≤ origTime t h s := hd.origTime_nonneg hsL.1
    have hτS : origTime t h s ≤ S := hLS ▸ monotone_origTime hd.hpos hd.summable hd.inj hsL.2
    have hus : u ≤ s := by
      have : 1 ≤ r := by rw [hr, le_div_iff₀ hS, one_mul, hLeq]; linarith
      nlinarith [hu.1]
    have hsu : s ≤ u + hb := by
      have : s = u + u * hb / S := by
        rw [hs, hr, hLeq]; field_simp
      rw [this]
      have : u * hb / S ≤ hb := by
        rw [div_le_iff₀ hS]; nlinarith [hu.2, hhb0.le]
      linarith
    have hτle := origTime_le hd.hpos (t := t) s
    have hτge := le_origTime hd.hpos hd.summable (t := t) s
    rw [hsum] at hτge
    have hdist' : dist (origTime t h s) u < δ := by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith
    have h2 := hδc (origTime t h s) ⟨hτ0, hτS⟩ u hu hdist'
    rw [dist_eq_norm] at h2
    calc ‖G s - η u‖ ≤ ‖G s - η (origTime t h s)‖ + ‖η (origTime t h s) - η u‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ ε / 4 + ε := add_le_add h1 h2.le
      _ ≤ 2 * ε := by linarith

end YuanSimpleApprox

/-! ### [Yua22] Theorem 1.1, (i) ⇒ (iii) -/

open YuanSimpleApprox in
/-- **[Yua22] Theorem 1.1, (i) ⇒ (iii)**: a continuous Loewner trace `η` of a continuous driver `W`
(`W 0 = 0`) is, on every compact interval `[0, S]`, a uniform limit of simple curves starting at
`0` and otherwise in `ℍ` (the specification's non-crossing convention, `Sec6.HasSimpleApproxOn`). -/
theorem IsLoewnerTrace.hasSimpleApproxOn {W : ℝ → ℝ} {η : ℝ → ℂ} (hη : IsLoewnerTrace W η)
    (hW : Continuous W) (hW0 : W 0 = 0) (S : ℝ) : Sec6.HasSimpleApproxOn η S := by
  rcases le_or_gt S 0 with hS | hS
  · -- a degenerate interval
    refine ⟨fun _ _ => 0, fun _ => ⟨continuousOn_const, ?_, rfl, ?_⟩, ?_⟩
    · intro u hu u' hu' _
      linarith [hu.1, hu.2, hu'.1, hu'.2]
    · intro u hu; exact absurd (hu.1.trans_le hu.2) (not_lt.2 hS)
    · refine Metric.tendstoUniformlyOn_iff.2 fun e he => Eventually.of_forall fun n u hu => ?_
      have hu0 : u = 0 := le_antisymm (hu.2.trans hS) hu.1
      rw [hu0, hη.1, dist_self]; exact he
  · have hex : ∀ n : ℕ, ∃ γ : ℝ → ℂ, ContinuousOn γ (Icc 0 S) ∧ InjOn γ (Icc 0 S) ∧ γ 0 = 0 ∧
        MapsTo γ (Ioc 0 S) H ∧ ∀ u ∈ Icc 0 S, ‖γ u - η u‖ ≤ 2 * (1 / (n + 1)) := fun n =>
      exists_simple_approx hη hW hW0 hS (by positivity)
    choose γ hγc hγi hγ0 hγH hγη using hex
    refine ⟨γ, fun n => ⟨hγc n, hγi n, hγ0 n, hγH n⟩, ?_⟩
    refine Metric.tendstoUniformlyOn_iff.2 fun e he => ?_
    obtain ⟨n₀, hn₀⟩ := exists_nat_gt (2 / e)
    refine eventually_atTop.2 ⟨n₀, fun n hn u hu => ?_⟩
    rw [dist_eq_norm, norm_sub_rev]
    refine lt_of_le_of_lt (hγη n u hu) ?_
    have hn1 : (2 / e : ℝ) < n + 1 := by
      have : (n₀ : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    rw [mul_one_div, div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ he] at hn1
    linarith

/-- **[Yua22] Theorem 1.1, (i) ⇒ (iii) before a horizon**: a continuous Loewner trace before the
horizon `T` has the uniform simple approximations on every `[0, S]` with `S < T`. -/
theorem IsLoewnerTraceLT.hasSimpleApproxOn {W : ℝ → ℝ} {η : ℝ → ℂ} {T : ℝ}
    (hη : IsLoewnerTraceLT W T η) (hW : Continuous W) (hW0 : W 0 = 0) {S : ℝ} (hST : S < T) :
    Sec6.HasSimpleApproxOn η S := by
  rcases lt_or_ge S 0 with hS | hS
  · refine ⟨fun _ _ => 0, fun _ => ⟨continuousOn_const, ?_, rfl, ?_⟩, ?_⟩
    · intro u hu; exact absurd (hu.1.trans hu.2) (not_le.2 hS)
    · intro u hu; exact absurd (hu.1.trans_le hu.2) (not_lt.2 hS.le)
    · refine Metric.tendstoUniformlyOn_iff.2 fun e he => Eventually.of_forall fun n u hu => ?_
      exact absurd (hu.1.trans hu.2) (not_le.2 hS)
  set T' := (S + T) / 2 with hT'
  have hT'0 : 0 ≤ T' := by rw [hT']; linarith
  have hT'T : T' < T := by rw [hT']; linarith
  have hST' : S ≤ T' := by rw [hT']; linarith
  have hext := hη.isLoewnerTrace_ext hW hW0 hT'0 hT'T
  obtain ⟨γ, hγ, hlim⟩ := hext.hasSimpleApproxOn
    (YuanCorollary13.continuous_extDrive hW) (YuanCorollary13.extDrive_zero hW0 hT'0) S
  refine ⟨γ, hγ, hlim.congr_right fun u hu => ?_⟩
  exact YuanCorollary13.extTrace_eq (hu.2.trans hST')

end InteractingSLE
