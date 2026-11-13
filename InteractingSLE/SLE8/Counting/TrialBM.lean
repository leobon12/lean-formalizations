import InteractingSLE.SLE8.Counting.Trial
import QuantumZipper.Proofs.Probability.StrongMarkov
import QuantumZipper.Proofs.Probability.Williams.Markov
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Group.Measure

/-!
# Many low-occupation trial intervals are unlikely for Brownian motion ((4.23))

SLE₈ note `source/sle8-continuity.pdf`, §4, Step 4, p. 10 (transcription
`source/sle8/sle8-continuity.md`, anchor `prop-4.1-proof`): "Lemma 3.3 and successive applications of
the strong Markov property give `ℚ(E_{k_*,T}) ≤ (C_tr/r)^{m_r}`" (4.23).

Here `J = 2β` for a standard Brownian motion `β` (variance rate `4`, started at `0`), with every path
continuous. The `j`-th trial interval is `[σ_j, σ_j + 2L]` with the entrance times `σ_j` of `Trial.lean`
(`c = 2r`, `L = r⁵`). Lemma 3.3 of the note (`Lemma33Statement`, proved by packet PROVE-S8-OCC) is a
hypothesis of the results below.

## Main results

* `Lemma33Statement`: Lemma 3.3 of the note, as stated.
* `measure_inter_occupation_restart_le`: Lemma 3.3 at a stopping time (strong Markov property): for an
  event `A ∈ 𝓕_ρ` on which the restart point `ξ` is in `[-2r, 2r]`,
  `Q(A ∩ {occupation after ρ ≤ r}) ≤ (C_tr/r) Q(A)`.
* `measure_trialFound_le`: `Q(the first m trials are found and each has occupation ≤ r) ≤ (C_tr/r)^m`.
-/

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal

namespace InteractingSLE.SLE8

/-- **Lemma 3.3** of the SLE₈ note (occupation during a long interval), as stated (p. 7): there is a
universal constant `C_tr < ∞` such that, for every `r ≥ 2`, a Brownian motion `J` of variance rate `4`
satisfies `sup_{|x| ≤ 2r} ℙ_x[∫_0^{2r⁵} 1{|J_u| ≤ 1} du ≤ r] ≤ C_tr / r`.

Here `J_u = x + 2 β_u` for a standard Brownian motion `β` (with every path continuous and measurable
coordinates) under any measure `Q` on the sample space `Ω`; the constant is chosen before `Q`, `β`,
`r` and `x`. -/
def Lemma33Statement (Ω : Type*) [MeasurableSpace Ω] : Prop :=
  ∃ C : ℝ, ∀ (Q : Measure Ω) (β : ℝ≥0 → Ω → ℝ), IsBrownianReal β Q →
    (∀ ω, Continuous fun t => β t ω) → (∀ t, Measurable (β t)) →
    ∀ r : ℝ, 2 ≤ r → ∀ x : ℝ, |x| ≤ 2 * r →
      Q {ω | volume {u : ℝ | u ∈ Icc 0 (2 * r ^ 5) ∧ |x + 2 * β u.toNNReal ω| ≤ 1} ≤
        ENNReal.ofReal r} ≤ ENNReal.ofReal (C / r)

/-! ## A measurable version of the occupation on path space -/

/-- The dyadic point `k / 2ⁿ`. -/
def dyadPt (n k : ℕ) : ℝ≥0 := (k : ℝ≥0) / 2 ^ n

theorem tendsto_dyadPt_ceil {v : ℝ} (hv : 0 ≤ v) :
    Tendsto (fun n : ℕ => dyadPt n ⌈(2 : ℝ) ^ n * v⌉₊) atTop (𝓝 v.toNNReal) := by
  rw [← NNReal.tendsto_coe, Real.coe_toNNReal v hv]
  have hlo : ∀ n : ℕ, v ≤ ((dyadPt n ⌈(2 : ℝ) ^ n * v⌉₊ : ℝ≥0) : ℝ) := by
    intro n
    simp only [dyadPt, NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_pow, NNReal.coe_ofNat]
    rw [le_div_iff₀ (by positivity), mul_comm]
    exact Nat.le_ceil _
  have hhi : ∀ n : ℕ, ((dyadPt n ⌈(2 : ℝ) ^ n * v⌉₊ : ℝ≥0) : ℝ) ≤ v + 1 / 2 ^ n := by
    intro n
    simp only [dyadPt, NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_pow, NNReal.coe_ofNat]
    rw [div_le_iff₀ (by positivity), add_mul, one_div, inv_mul_cancel₀ (by positivity), mul_comm]
    exact (Nat.ceil_lt_add_one (by positivity)).le
  have hlim : Tendsto (fun n : ℕ => v + 1 / (2 : ℝ) ^ n) atTop (𝓝 v) := by
    have h : Tendsto (fun n : ℕ => 1 / (2 : ℝ) ^ n) atTop (𝓝 0) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)).congr
        fun n => by rw [one_div_pow]
    simpa using h.const_add v
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim hlo hhi

/-- The measurable set `D` of triples `(x, w, v)` with `|x + 2 w(v)| ≤ 1` "along dyadic approximations";
for a continuous path `w` and `v ≥ 0` it is exactly `|x + 2 w(v)| ≤ 1` (`mem_occSet_iff`). -/
def occSet : Set ((ℝ × (ℝ≥0 → ℝ)) × ℝ) :=
  {p | ∀ k : ℕ, ∃ N : ℕ, ∀ n ≥ N,
    |p.1.1 + 2 * p.1.2 (dyadPt n ⌈(2 : ℝ) ^ n * p.2⌉₊)| < 1 + 1 / (k + 1)}

theorem measurableSet_occSet : MeasurableSet occSet := by
  have hev : ∀ n : ℕ, Measurable fun p : (ℝ × (ℝ≥0 → ℝ)) × ℝ =>
      p.1.1 + 2 * p.1.2 (dyadPt n ⌈(2 : ℝ) ^ n * p.2⌉₊) := by
    intro n
    have hΦ : Measurable fun q : (ℝ≥0 → ℝ) × ℕ => q.1 (dyadPt n q.2) :=
      measurable_from_prod_countable_left fun k => measurable_pi_apply (dyadPt n k)
    have hk : Measurable fun p : (ℝ × (ℝ≥0 → ℝ)) × ℝ => ⌈(2 : ℝ) ^ n * p.2⌉₊ :=
      Nat.measurable_ceil.comp (measurable_const.mul measurable_snd)
    exact (measurable_fst.comp measurable_fst).add
      (measurable_const.mul (hΦ.comp ((measurable_snd.comp measurable_fst).prodMk hk)))
  have heq : occSet = ⋂ k : ℕ, ⋃ N : ℕ, ⋂ n ≥ N,
      {p : (ℝ × (ℝ≥0 → ℝ)) × ℝ | |p.1.1 + 2 * p.1.2 (dyadPt n ⌈(2 : ℝ) ^ n * p.2⌉₊)| <
        1 + 1 / (k + 1)} := by
    ext p; simp [occSet]
  rw [heq]
  exact MeasurableSet.iInter fun k => MeasurableSet.iUnion fun N => MeasurableSet.iInter fun n =>
    MeasurableSet.iInter fun _ =>
      measurableSet_lt (continuous_abs.measurable.comp (hev n)) measurable_const

theorem mem_occSet_iff {x : ℝ} {w : ℝ≥0 → ℝ} (hw : Continuous w) {v : ℝ} (hv : 0 ≤ v) :
    ((x, w), v) ∈ occSet ↔ |x + 2 * w v.toNNReal| ≤ 1 := by
  have hlim : Tendsto (fun n : ℕ => |x + 2 * w (dyadPt n ⌈(2 : ℝ) ^ n * v⌉₊)|) atTop
      (𝓝 |x + 2 * w v.toNNReal|) :=
    ((continuous_abs.comp (continuous_const.add (continuous_const.mul hw))).tendsto _).comp
      (tendsto_dyadPt_ceil hv)
  constructor
  · intro h
    refine le_of_forall_pos_lt_add fun ε hε => ?_
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
    obtain ⟨N, hN⟩ := h k
    have hle : |x + 2 * w v.toNNReal| ≤ 1 + 1 / (k + 1) :=
      le_of_tendsto hlim (eventually_atTop.2 ⟨N, fun n hn => (hN n hn).le⟩)
    linarith
  · intro h k
    have hk : |x + 2 * w v.toNNReal| < 1 + 1 / (k + 1) := by
      have : (0 : ℝ) < 1 / (k + 1) := by positivity
      linarith
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hlim.eventually (gt_mem_nhds hk))
    exact ⟨N, hN⟩

/-- The occupation `∫_0^{2r⁵} 1{|x + 2 w(v)| ≤ 1} dv` of `[-1, 1]` by the path `x + 2w`. -/
def occRestart (r x : ℝ) (w : ℝ≥0 → ℝ) : ℝ≥0∞ :=
  volume {v : ℝ | v ∈ Icc 0 (2 * r ^ 5) ∧ |x + 2 * w v.toNNReal| ≤ 1}

/-- The measurable version of `occRestart` on `ℝ × (ℝ≥0 → ℝ)`. -/
def occMeas (r : ℝ) (q : ℝ × (ℝ≥0 → ℝ)) : ℝ≥0∞ :=
  volume (Prod.mk q ⁻¹' (occSet ∩ {p | p.2 ∈ Icc 0 (2 * r ^ 5)}))

theorem measurable_occMeas (r : ℝ) : Measurable (occMeas r) :=
  measurable_measure_prodMk_left (measurableSet_occSet.inter (measurableSet_Icc.preimage measurable_snd))

theorem occMeas_eq {r x : ℝ} {w : ℝ≥0 → ℝ} (hw : Continuous w) :
    occMeas r (x, w) = occRestart r x w := by
  unfold occMeas occRestart
  congr 1
  ext v
  simp only [mem_preimage, mem_inter_iff, mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h2, (mem_occSet_iff hw h2.1).1 h1⟩
  · rintro ⟨h2, h1⟩; exact ⟨(mem_occSet_iff hw h2.1).2 h1, h2⟩

section StrongMarkov

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {Q : Measure Ω} [IsProbabilityMeasure Q]
  {β : ℝ≥0 → Ω → ℝ}

/-- **Lemma 3.3 at a stopping time** (strong Markov property). Let `ρ` be a stopping time of the
natural filtration of the Brownian motion `β`, `A ∈ 𝓕_ρ`, and `ξ` an `𝓕_ρ`-measurable restart point
with `|ξ| ≤ 2r` on `A`. If Lemma 3.3 holds with constant `C` at this `r`, then the occupation of
`[-1, 1]` by `ξ + 2(β_{ρ+·} - β_ρ)` during `[0, 2r⁵]` is at most `r` on at most a `C/r` fraction of
`A`. -/
theorem measure_inter_occRestart_le {C r : ℝ}
    (hC : ∀ β' : ℝ≥0 → Ω → ℝ, IsBrownianReal β' Q → (∀ ω, Continuous fun t => β' t ω) →
      (∀ t, Measurable (β' t)) → ∀ x : ℝ, |x| ≤ 2 * r →
        Q {ω | occRestart r x (fun t => β' t ω) ≤ ENNReal.ofReal r} ≤ ENNReal.ofReal (C / r))
    (hβ : IsBrownianReal β Q) (hβc : ∀ ω, Continuous fun t => β t ω) (hβm : ∀ t, Measurable (β t))
    {ρ : Ω → ℝ≥0}
    (hρ : IsStoppingTime (QuantumZipper.Williams.pastFilt β hβm) fun ω => (ρ ω : WithTop ℝ≥0))
    {A : Set Ω} (hA : MeasurableSet[hρ.measurableSpace] A) {ξ : Ω → ℝ}
    (hξ : Measurable[hρ.measurableSpace] ξ) (hξA : ∀ ω ∈ A, |ξ ω| ≤ 2 * r) :
    Q (A ∩ {ω | occRestart r (ξ ω) (QuantumZipper.StrongMarkov.smPath β ρ ω) ≤ ENNReal.ofReal r}) ≤
      ENNReal.ofReal (C / r) * Q A := by
  set smP := QuantumZipper.StrongMarkov.smPath β ρ with hsmP
  have hind : ∀ t, Indep (QuantumZipper.Williams.pastFilt β hβm t)
      (MeasurableSpace.comap (QuantumZipper.StrongMarkov.smPath β (fun _ => t)) MeasurableSpace.pi)
      Q :=
    QuantumZipper.StrongMarkov.indep_shift_of_le_past hβ.toIsPreBrownianReal (fun t => le_rfl)
  set g : Ω → ℝ × ℝ := fun ω => (A.indicator (fun _ => (1 : ℝ)) ω, ξ ω) with hgdef
  have hg : Measurable[hρ.measurableSpace] g :=
    (measurable_const.indicator hA).prodMk hξ
  have hgm : Measurable g := hg.mono hρ.measurableSpace_le le_rfl
  have hsm : Measurable smP := QuantumZipper.StrongMarkov.measurable_smPath hβc hβm
    (QuantumZipper.StrongMarkov.measurable_of_isStoppingTime hρ)
  have hind' : IndepFun g smP Q :=
    QuantumZipper.StrongMarkov.indepFun_smPath hβ.toIsPreBrownianReal hβc hβm hind hρ hg
  have hmap := (indepFun_iff_map_prod_eq_prod_map_map hgm.aemeasurable hsm.aemeasurable).1 hind'
  set S : Set ((ℝ × ℝ) × (ℝ≥0 → ℝ)) :=
    {p | p.1.1 = 1 ∧ |p.1.2| ≤ 2 * r ∧ occMeas r (p.1.2, p.2) ≤ ENNReal.ofReal r} with hSdef
  have hS : MeasurableSet S := by
    refine (measurableSet_eq_fun (measurable_fst.comp measurable_fst) measurable_const).inter
      ((measurableSet_le (continuous_abs.measurable.comp (measurable_snd.comp measurable_fst))
        measurable_const).inter
      (measurableSet_le ((measurable_occMeas r).comp
        ((measurable_snd.comp measurable_fst).prodMk measurable_snd)) measurable_const))
  have hsmc : ∀ ω, Continuous (smP ω) := fun ω =>
    ((hβc ω).comp (continuous_const.add continuous_id)).sub continuous_const
  have hsub : A ∩ {ω | occRestart r (ξ ω) (smP ω) ≤ ENNReal.ofReal r} ⊆
      (fun ω => (g ω, smP ω)) ⁻¹' S := by
    rintro ω ⟨hωA, hocc⟩
    refine ⟨by simp [hgdef, hωA], hξA ω hωA, ?_⟩
    show occMeas r (ξ ω, smP ω) ≤ ENNReal.ofReal r
    rw [occMeas_eq (hsmc ω)]; exact hocc
  have hE1 : MeasurableSet {p : ℝ × ℝ | p.1 = 1} :=
    measurableSet_eq_fun measurable_fst measurable_const
  have hbound : ∀ p : ℝ × ℝ, (Q.map smP) (Prod.mk p ⁻¹' S) ≤
      {p : ℝ × ℝ | p.1 = 1}.indicator (fun _ => ENNReal.ofReal (C / r)) p := by
    intro p
    by_cases hp : p.1 = 1 ∧ |p.2| ≤ 2 * r
    · have hsec : Prod.mk p ⁻¹' S = {w | occMeas r (p.2, w) ≤ ENNReal.ofReal r} := by
        ext w; simp [hSdef, hp.1, hp.2]
      have hmeas : MeasurableSet {w : ℝ≥0 → ℝ | occMeas r (p.2, w) ≤ ENNReal.ofReal r} :=
        measurableSet_le ((measurable_occMeas r).comp (measurable_const.prodMk measurable_id))
          measurable_const
      rw [indicator_of_mem (show p ∈ {p : ℝ × ℝ | p.1 = 1} from hp.1), hsec,
        Measure.map_apply hsm hmeas]
      have heq : smP ⁻¹' {w | occMeas r (p.2, w) ≤ ENNReal.ofReal r} =
          {ω | occRestart r p.2 (fun t => QuantumZipper.StrongMarkov.smShift β ρ t ω) ≤
            ENNReal.ofReal r} := by
        ext ω
        simp only [mem_preimage, mem_ofPred_eq]
        rw [occMeas_eq (hsmc ω)]
        rfl
      rw [heq]
      refine hC _ (QuantumZipper.StrongMarkov.isBrownianReal_smShift hβ.toIsPreBrownianReal hβc hβm
        hind hρ) hsmc ?_ p.2 hp.2
      intro t
      exact QuantumZipper.StrongMarkov.measurable_smShift hβc hβm
        (QuantumZipper.StrongMarkov.measurable_of_isStoppingTime hρ) t
    · have hsec : Prod.mk p ⁻¹' S = ∅ := by
        ext w
        simp only [hSdef, mem_preimage, mem_ofPred_eq, mem_empty_iff_false, iff_false]
        rintro ⟨h1, h2, -⟩
        exact hp ⟨h1, h2⟩
      rw [hsec, measure_empty]
      exact bot_le
  calc Q (A ∩ {ω | occRestart r (ξ ω) (smP ω) ≤ ENNReal.ofReal r})
      ≤ Q ((fun ω => (g ω, smP ω)) ⁻¹' S) := measure_mono hsub
    _ = Q.map (fun ω => (g ω, smP ω)) S := (Measure.map_apply (hgm.prodMk hsm) hS).symm
    _ = ((Q.map g).prod (Q.map smP)) S := by rw [hmap]
    _ = ∫⁻ p, (Q.map smP) (Prod.mk p ⁻¹' S) ∂(Q.map g) := Measure.prod_apply hS
    _ ≤ ∫⁻ p, {p : ℝ × ℝ | p.1 = 1}.indicator (fun _ => ENNReal.ofReal (C / r)) p ∂(Q.map g) :=
        lintegral_mono hbound
    _ = ENNReal.ofReal (C / r) * (Q.map g) {p : ℝ × ℝ | p.1 = 1} := lintegral_indicator_const hE1 _
    _ = ENNReal.ofReal (C / r) * Q A := by
        rw [Measure.map_apply hgm hE1]
        congr 2
        ext ω
        by_cases hω : ω ∈ A <;> simp [hgdef, hω]

/-! ## The trials of a Brownian motion of variance rate 4 -/

/-- The path `u ↦ 2 β_u` (`J = 2β`, variance rate `4`), with `u < 0` sent to `2 β_0`. -/
def bmPath (β : ℝ≥0 → Ω → ℝ) (ω : Ω) : ℝ → ℝ := fun u => 2 * β u.toNNReal ω

omit [IsProbabilityMeasure Q] in
theorem continuous_bmPath (hβc : ∀ ω, Continuous fun t => β t ω) (ω : Ω) :
    Continuous (bmPath β ω) :=
  continuous_const.mul ((hβc ω).comp continuous_real_toNNReal)

omit [IsProbabilityMeasure Q] in
/-- The path stopped at time `t` is adapted to the natural filtration at `t`. -/
theorem measurable_bmPath_stopped (hβm : ∀ t, Measurable (β t)) (t : ℝ≥0) (u : ℝ) :
    Measurable[QuantumZipper.Williams.pastFilt β hβm t] fun ω => bmPath β ω (min u t) := by
  have hle : (min u (t : ℝ)).toNNReal ≤ t := by
    rw [Real.toNNReal_le_iff_le_coe]; exact min_le_right _ _
  have h1 : Measurable[MeasurableSpace.comap (fun ω (r : Set.Iic t) => β r ω) MeasurableSpace.pi]
      fun ω => β (min u (t : ℝ)).toNNReal ω :=
    (measurable_pi_apply (⟨(min u (t : ℝ)).toNNReal, hle⟩ : Set.Iic t)).comp
      (comap_measurable (fun ω (r : Set.Iic t) => β r ω))
  exact measurable_const.mul h1

omit [IsProbabilityMeasure Q] in
theorem measurable_bmPath_iSup (hβm : ∀ t, Measurable (β t)) (u : ℝ) :
    Measurable[⨆ t, QuantumZipper.Williams.pastFilt β hβm t] fun ω => bmPath β ω u := by
  have h := measurable_bmPath_stopped hβm u.toNNReal u
  have he : min u (u.toNNReal : ℝ) = u := min_eq_left (Real.le_coe_toNNReal u)
  simp only [he] at h
  exact h.mono (le_iSup (fun t => QuantumZipper.Williams.pastFilt β hβm t) u.toNNReal) le_rfl

omit [IsProbabilityMeasure Q] in
/-- The entrance times of `2β` are stopping times of the natural filtration. -/
theorem isStoppingTime_entrance (hβc : ∀ ω, Continuous fun t => β t ω)
    (hβm : ∀ t, Measurable (β t)) {c L K : ℝ} (hL : 0 ≤ L) (hK : 0 ≤ K) (m : ℕ) :
    IsStoppingTime (QuantumZipper.Williams.pastFilt β hβm)
      fun ω => ((entrance (bmPath β ω) c L K m).toNNReal : WithTop ℝ≥0) := by
  intro t
  set F : Ω → ℝ → ℝ := fun ω u => bmPath β ω (min u t) with hFdef
  have hFc : ∀ ω, Continuous (F ω) := fun ω =>
    (continuous_bmPath hβc ω).comp (continuous_id.min continuous_const)
  have hFm : ∀ u, Measurable[QuantumZipper.Williams.pastFilt β hβm t] fun ω => F ω u :=
    measurable_bmPath_stopped hβm t
  have hK' : 0 ≤ min (t : ℝ) K := le_min t.2 hK
  have hagree : ∀ ω, ∀ u ∈ Icc 0 (min (t : ℝ) K), bmPath β ω u = F ω u := fun ω u hu => by
    simp [hFdef, min_eq_left (hu.2.trans (min_le_left _ _))]
  have heq : {ω | ((entrance (bmPath β ω) c L K m).toNNReal : WithTop ℝ≥0) ≤ t} =
      {ω | entrance (F ω) c L K m ≤ min (t : ℝ) K} ∪ {_ω | K + 1 ≤ t} := by
    ext ω
    simp only [mem_ofPred_eq, mem_union, WithTop.coe_le_coe, Real.toNNReal_le_iff_le_coe]
    constructor
    · intro h
      rcases entrance_le_or_eq (continuous_bmPath hβc ω) hK m (c := c) (L := L) with h1 | h1
      · left
        have hle : entrance (bmPath β ω) c L K m ≤ min (t : ℝ) K := le_min h h1
        rw [entrance_congr_of_le (continuous_bmPath hβc ω) (hFc ω) hL hK' (min_le_right _ _)
          (min_le_right _ _) (hagree ω) m hle]
        exact hle
      · right; rw [← h1]; exact h
    · rintro (h | h)
      · rw [entrance_congr_of_le (hFc ω) (continuous_bmPath hβc ω) hL hK' (min_le_right _ _)
          (min_le_right _ _) (fun u hu => (hagree ω u hu).symm) m h]
        exact h.trans (min_le_left _ _)
      · exact (entrance_le_succ_horizon (continuous_bmPath hβc ω) hK m).trans h
  rw [heq]
  exact (measurableSet_le (measurable_entrance (m𝓖 := QuantumZipper.Williams.pastFilt β hβm t)
    hFc hFm c L K m) measurable_const).union (MeasurableSet.const _)

omit [IsProbabilityMeasure Q] in
/-- The event "the first `m` trials are found with occupation `≤ r` and `σ_m` is found" belongs to
`𝓕_{σ_m}`. -/
theorem measurableSet_trialFound_entrance (hβc : ∀ ω, Continuous fun t => β t ω)
    (hβm : ∀ t, Measurable (β t)) {c L K r : ℝ} (hL : 0 ≤ L) (hK : 0 ≤ K) (m : ℕ) :
    MeasurableSet[(isStoppingTime_entrance hβc hβm (c := c) hL hK m).measurableSpace]
      {ω | TrialFound (bmPath β ω) c L K r m ∧ entrance (bmPath β ω) c L K m ≤ K} := by
  refine ⟨?_, fun t => ?_⟩
  · have hm := measurable_bmPath_iSup hβm (β := β)
    exact (measurableSet_trialFound (m𝓖 := ⨆ t, QuantumZipper.Williams.pastFilt β hβm t)
      (continuous_bmPath hβc) hm c L K r m).inter
      (measurableSet_le (measurable_entrance (continuous_bmPath hβc) hm c L K m) measurable_const)
  · set F : Ω → ℝ → ℝ := fun ω u => bmPath β ω (min u t) with hFdef
    have hFc : ∀ ω, Continuous (F ω) := fun ω =>
      (continuous_bmPath hβc ω).comp (continuous_id.min continuous_const)
    have hFm : ∀ u, Measurable[QuantumZipper.Williams.pastFilt β hβm t] fun ω => F ω u :=
      measurable_bmPath_stopped hβm t
    have hK' : 0 ≤ min (t : ℝ) K := le_min t.2 hK
    have hagree : ∀ ω, ∀ u ∈ Icc 0 (min (t : ℝ) K), bmPath β ω u = F ω u := fun ω u hu => by
      simp [hFdef, min_eq_left (hu.2.trans (min_le_left _ _))]
    have heq : {ω | TrialFound (bmPath β ω) c L K r m ∧ entrance (bmPath β ω) c L K m ≤ K} ∩
        {ω | ((entrance (bmPath β ω) c L K m).toNNReal : WithTop ℝ≥0) ≤ t} =
        {ω | TrialFound (F ω) c L K r m ∧ entrance (F ω) c L K m ≤ min (t : ℝ) K} := by
      ext ω
      simp only [mem_inter_iff, mem_ofPred_eq, WithTop.coe_le_coe, Real.toNNReal_le_iff_le_coe]
      constructor
      · rintro ⟨⟨hT, hK1⟩, ht⟩
        have hle : entrance (bmPath β ω) c L K m ≤ min (t : ℝ) K := le_min ht hK1
        obtain ⟨hT', he⟩ := trialFound_congr (continuous_bmPath hβc ω) (hFc ω) hL hK'
          (min_le_right _ _) (hagree ω) hle hT
        exact ⟨hT', he ▸ hle⟩
      · rintro ⟨hT, hle⟩
        obtain ⟨hT', he⟩ := trialFound_congr (hFc ω) (continuous_bmPath hβc ω) hL hK'
          (min_le_right _ _) (fun u hu => (hagree ω u hu).symm) hle hT
        rw [he]
        exact ⟨⟨hT', hle.trans (min_le_right _ _)⟩, hle.trans (min_le_left _ _)⟩
    rw [heq]
    exact (measurableSet_trialFound (m𝓖 := QuantumZipper.Williams.pastFilt β hβm t) hFc hFm
      c L K r m).inter
      (measurableSet_le (measurable_entrance hFc hFm c L K m) measurable_const)

omit [IsProbabilityMeasure Q] in
/-- The occupation of a trial interval of `2β` is the occupation of the restarted path. -/
theorem occupation_bmPath_eq (r : ℝ) (ρ : Ω → ℝ≥0) (ω : Ω) :
    occupation (bmPath β ω) (ρ ω) (2 * r ^ 5) =
      occRestart r (2 * β (ρ ω) ω) (QuantumZipper.StrongMarkov.smPath β ρ ω) := by
  unfold occupation occRestart
  rw [← measure_preimage_add volume (ρ ω : ℝ)]
  congr 1
  ext v
  simp only [mem_preimage, mem_ofPred_eq, mem_Icc]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    have hv : 0 ≤ v := by linarith
    refine ⟨⟨hv, by linarith⟩, ?_⟩
    have hadd : (↑(ρ ω) + v).toNNReal = ρ ω + v.toNNReal := by
      rw [Real.toNNReal_add (ρ ω).coe_nonneg hv, Real.toNNReal_coe]
    simp only [bmPath, hadd] at h3
    simp only [QuantumZipper.StrongMarkov.smPath, QuantumZipper.StrongMarkov.smShift]
    convert h3 using 2; ring
  · rintro ⟨⟨hv, h2⟩, h3⟩
    refine ⟨⟨by linarith, by linarith⟩, ?_⟩
    have hadd : (↑(ρ ω) + v).toNNReal = ρ ω + v.toNNReal := by
      rw [Real.toNNReal_add (ρ ω).coe_nonneg hv, Real.toNNReal_coe]
    simp only [bmPath, hadd]
    simp only [QuantumZipper.StrongMarkov.smPath, QuantumZipper.StrongMarkov.smShift] at h3
    convert h3 using 2; ring

/-- **(4.23), Brownian form.** If Lemma 3.3 holds with constant `C` at `r ≥ 2`, then for a Brownian
motion `β` started at `0`, the probability that the first `m` trial intervals of `J = 2β` (level `2r`,
length `2L = 2r⁵`, horizon `K`) are found and each has occupation of `[-1, 1]` at most `r` is at most
`(C/r)^m`. -/
theorem measure_trialFound_le {C r K : ℝ}
    (hC : ∀ β' : ℝ≥0 → Ω → ℝ, IsBrownianReal β' Q → (∀ ω, Continuous fun t => β' t ω) →
      (∀ t, Measurable (β' t)) → ∀ x : ℝ, |x| ≤ 2 * r →
        Q {ω | occRestart r x (fun t => β' t ω) ≤ ENNReal.ofReal r} ≤ ENNReal.ofReal (C / r))
    (hβ : IsBrownianReal β Q) (hβc : ∀ ω, Continuous fun t => β t ω) (hβm : ∀ t, Measurable (β t))
    (hβ0 : ∀ ω, β 0 ω = 0) (hr : 2 ≤ r) (hK : 0 ≤ K) (m : ℕ) :
    Q {ω | TrialFound (bmPath β ω) (2 * r) (r ^ 5) K r m} ≤ ENNReal.ofReal (C / r) ^ m := by
  have hL : (0 : ℝ) ≤ r ^ 5 := by positivity
  induction m with
  | zero => simp [TrialFound]
  | succ m ih =>
    set A := {ω | TrialFound (bmPath β ω) (2 * r) (r ^ 5) K r m ∧
      entrance (bmPath β ω) (2 * r) (r ^ 5) K m ≤ K} with hAdef
    have hρ := isStoppingTime_entrance hβc hβm (c := 2 * r) hL hK m
    set ρ : Ω → ℝ≥0 := fun ω => (entrance (bmPath β ω) (2 * r) (r ^ 5) K m).toNNReal with hρdef
    have hA := measurableSet_trialFound_entrance hβc hβm (c := 2 * r) (r := r) hL hK m
    set ξ : Ω → ℝ := fun ω => 2 * β (ρ ω) ω with hξdef
    have hξ : Measurable[hρ.measurableSpace] ξ := by
      have hprog : IsStronglyProgressive (QuantumZipper.Williams.pastFilt β hβm)
          fun t ω => 2 * β t ω := by
        refine StronglyAdapted.isStronglyProgressive_of_continuous (fun t => ?_)
          fun ω => continuous_const.mul (hβc ω)
        have h1 : Measurable[MeasurableSpace.comap (fun ω (r : Set.Iic t) => β r ω)
            MeasurableSpace.pi] fun ω => β t ω :=
          (measurable_pi_apply (⟨t, Set.mem_Iic.2 le_rfl⟩ : Set.Iic t)).comp
            (comap_measurable (fun ω (r : Set.Iic t) => β r ω))
        exact (measurable_const.mul h1).stronglyMeasurable
      have := measurable_stoppedValue hprog hρ
      convert this using 1
      funext ω
      rfl
    have hξA : ∀ ω ∈ A, |ξ ω| ≤ 2 * r := by
      rintro ω ⟨-, hle⟩
      cases m with
      | zero =>
        simp [hξdef, hρdef, entrance_zero, hβ0]; linarith
      | succ j =>
        have h := abs_entrance_le (continuous_bmPath hβc ω) hle
        simpa [bmPath, hξdef, hρdef] using h
    have hsub : {ω | TrialFound (bmPath β ω) (2 * r) (r ^ 5) K r (m + 1)} ⊆
        A ∩ {ω | occRestart r (ξ ω) (QuantumZipper.StrongMarkov.smPath β ρ ω) ≤
          ENNReal.ofReal r} := by
      intro ω hω
      have hω' : TrialFound (bmPath β ω) (2 * r) (r ^ 5) K r (m + 1) := hω
      obtain ⟨hlast1, hlast2⟩ := hω' m (Nat.lt_succ_self m)
      refine ⟨⟨fun j hj => hω' j (Nat.lt_succ_of_lt hj), hlast1⟩, ?_⟩
      show occRestart r (2 * β (ρ ω) ω) (QuantumZipper.StrongMarkov.smPath β ρ ω) ≤ _
      have he : ((ρ ω : ℝ≥0) : ℝ) = entrance (bmPath β ω) (2 * r) (r ^ 5) K m :=
        Real.coe_toNNReal _ (entrance_nonneg (continuous_bmPath hβc ω) hL hK m)
      rw [← occupation_bmPath_eq r ρ ω, he, show 2 * r ^ 5 = 2 * (r ^ 5) by ring]
      exact hlast2
    have hAsub : A ⊆ {ω | TrialFound (bmPath β ω) (2 * r) (r ^ 5) K r m} := fun ω hω => hω.1
    calc Q {ω | TrialFound (bmPath β ω) (2 * r) (r ^ 5) K r (m + 1)}
        ≤ Q (A ∩ {ω | occRestart r (ξ ω) (QuantumZipper.StrongMarkov.smPath β ρ ω) ≤
            ENNReal.ofReal r}) := measure_mono hsub
      _ ≤ ENNReal.ofReal (C / r) * Q A :=
          measure_inter_occRestart_le hC hβ hβc hβm hρ hA hξ hξA
      _ ≤ ENNReal.ofReal (C / r) * ENNReal.ofReal (C / r) ^ m := by
          gcongr; exact (measure_mono hAsub).trans ih
      _ = ENNReal.ofReal (C / r) ^ (m + 1) := by rw [pow_succ']

end StrongMarkov

end InteractingSLE.SLE8
