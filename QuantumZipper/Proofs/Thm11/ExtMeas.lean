import QuantumZipper.Proofs.Thm11.AddendumAssemblyStmt
import QuantumZipper.Proofs.Thm11.ExtMeasTamed

/-!
# THM11-AD8: joint measurability of the extended field `𝔥^ext_T` (task EXT-MEAS), part 1

Sheffield, *Conformal weldings of random surfaces* (arXiv:1012.4797), Theorem 1.1 addendum
(`κ ∈ (4,8)`, p. 12): a point `z` swallowed before `T` receives the value
`𝔥^ext_T(z) := lim_{s ↑ τ(z)} 𝔥_s(z)`, `τ(z) = (swallowTime W z).toReal`
(`QuantumZipper.hTfwdExt` in `QuantumZipper/Statements/CouplingFields.lean`).

This file builds the *measurable candidate* for the extended field; `ExtMeas2.lean` proves that
it equals `hTfwdExt` pointwise and concludes `Thm11Asm.ExtMeasStmt`.

Route.  The `limUnder` over the point-dependent filter `𝓝[<] τ(z)` is not measurable by any
direct argument, so we replace the *filter* by an explicit countable device:

* `extFieldAt κ B s p` is the field value at the *fixed* time `s`, zero off `ℍ ∖ K_s`.  Its joint
  measurability in `(z, ω)` is `MeasTamed.measured_fieldAt_dom_at` (the time-`s` analogue of
  `measurable_fwdMap_dom`, via the tamed flow).
* `dfloor`/`dval` are the level-`j` dyadic floor of `τ(z)` and the field value there, written as
  finite sums over the grid `k/2^j` so that they are measurable; `dfloor j → τ(z)` from below.
* `guardAt p` is a countable Cauchy condition (oscillation of the field over the rational points
  of the windows `[τ - 1/(m+1), τ)`, expressed through the hull so that it is measurable).  By
  `MeasLimit.tendsto_iff_ratOsc` (continuity of `s ↦ 𝔥_s(z)` on `[0, τ(z))`,
  `MeasCont.continuousOn_fieldAt_Icc`), `guardAt p` holds iff the left limit exists.  Hence
  `candExt` — the `atTop`-limit of `dval` on the guard set, and the junk value
  `Classical.choice ‹Nonempty ℝ›` (what `limUnder` returns when no limit exists,
  `limUnder_of_not_tendsto`) elsewhere — is measurable and equals `hTfwdExt`.

Own argument (blueprint §9 AD-8, the "implicit measurability" node): the reduction of the
point-dependent `limUnder` to a countable guard is not in Sheffield; the analytic ingredients
(continuity below the swallowing time; the left limit exists iff the oscillation vanishes) are
elementary.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Complex Set Filter Classical
open scoped NNReal ENNReal Topology
open QuantumZipper.NonSwallow

namespace QuantumZipper
namespace Thm11Asm

section Defs

variable {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ}

/-- The field formula `h0fwd κ (f_s z) − χ arg f_s'(z)` (defined for every `s`; the field of the
coupling on `ℍ ∖ K_s`). -/
noncomputable def rawFieldAt (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (s : ℝ) (p : ℂ × Ω) : ℝ :=
  h0fwd κ (fwdMap (drive κ B p.2) s p.1)
    - chiC κ * (logDerivFwd (drive κ B p.2) s p.1).im

/-- The field value at the *fixed* time `s`: the formula on `z ∈ ℍ ∖ K_s`, and `0` off it (this
is exactly `hTfwd κ W s z`). -/
noncomputable def extFieldAt (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (s : ℝ) (p : ℂ × Ω) : ℝ :=
  ({p : ℂ × Ω | p.1 ∈ H \ fwdHull (drive κ B p.2) s}.indicator
    (fun p => h0fwd κ (fwdMap (drive κ B p.2) s p.1)
      - chiC κ * (logDerivFwd (drive κ B p.2) s p.1).im)) p

theorem extFieldAt_of_mem {κ : ℝ} {s : ℝ} {p : ℂ × Ω}
    (hp : p.1 ∈ H \ fwdHull (drive κ B p.2) s) : extFieldAt κ B s p = rawFieldAt κ B s p := by
  simp only [extFieldAt, rawFieldAt,
    Set.indicator_of_mem (show p ∈ {p : ℂ × Ω | p.1 ∈ H \ fwdHull (drive κ B p.2) s} from hp)]

theorem extFieldAt_of_notMem {κ : ℝ} {s : ℝ} {p : ℂ × Ω}
    (hp : p.1 ∉ H \ fwdHull (drive κ B p.2) s) : extFieldAt κ B s p = 0 := by
  simp only [extFieldAt,
    Set.indicator_of_notMem (show p ∉ {p : ℂ × Ω | p.1 ∈ H \ fwdHull (drive κ B p.2) s} from hp)]

/-- **Joint measurability of the field at a fixed time** in `(z, ω)`. -/
theorem measurable_extFieldAt (hBm : ∀ r : ℝ≥0, Measurable (B r))
    (hBc : ∀ ω, Continuous fun t => B t ω) (κ : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    Measurable (extFieldAt (Ω := Ω) κ B s) :=
  MeasTamed.measured_fieldAt_dom_at hBm hBc κ hs

/-- The level-`j` dyadic grid point `k / 2^j`. -/
noncomputable def dpt (j k : ℕ) : ℝ := (k : ℝ) / 2 ^ j

theorem dpt_nonneg (j k : ℕ) : 0 ≤ dpt j k := by
  unfold dpt; positivity

/-- The number of level-`j` grid points needed to cover `[0, T]`. -/
noncomputable def gridN (T : ℝ) (j : ℕ) : ℕ := Nat.ceil (2 ^ j * T) + 1

/-- The field value at the level-`j` dyadic floor of `τ(z)`. -/
noncomputable def dval (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (T : ℝ) (j : ℕ) (p : ℂ × Ω) : ℝ :=
  ∑ k ∈ Finset.range (gridN T j),
    if p.1 ∉ fwdHull (drive κ B p.2) (dpt j k) ∧
        p.1 ∈ fwdHull (drive κ B p.2) (dpt j (k + 1)) then extFieldAt κ B (dpt j k) p
      else 0

/-- The measurable set on which the level-`j` grid point `k` is the dyadic floor of `τ(z)`. -/
theorem measurableSet_dcell (hBm : ∀ r : ℝ≥0, Measurable (B r))
    (hBc : ∀ ω, Continuous fun t => B t ω) (κ : ℝ) (j k : ℕ) :
    MeasurableSet {p : ℂ × Ω | p.1 ∉ fwdHull (drive κ B p.2) (dpt j k) ∧
      p.1 ∈ fwdHull (drive κ B p.2) (dpt j (k + 1))} :=
  (measurableSet_fwdHull_prod hBm hBc κ (dpt_nonneg j k)).compl.inter
    (measurableSet_fwdHull_prod hBm hBc κ (dpt_nonneg j (k + 1)))

theorem measurable_dval (hBm : ∀ r : ℝ≥0, Measurable (B r))
    (hBc : ∀ ω, Continuous fun t => B t ω) (κ : ℝ) (T : ℝ) (j : ℕ) :
    Measurable (dval κ B T j) := by
  refine Finset.measurable_sum _ fun k _ => ?_
  exact Measurable.ite (measurableSet_dcell hBm hBc κ j k)
    (measurable_extFieldAt hBm hBc κ (dpt_nonneg j k)) measurable_const

/-- The window `[τ - 1/(m+1), τ)` of the guard, expressed through the hull: the rational `q` is
in the window iff `z ∉ K_q` (i.e. `q < τ`) and `z ∈ K_{q + 1/(m+1)}` (i.e. `q ≥ τ - 1/(m+1)`). -/
def win (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (m : ℕ) (q : {q : ℚ // (0 : ℝ) ≤ (q : ℝ)})
    (p : ℂ × Ω) : Prop :=
  p.1 ∉ fwdHull (drive κ B p.2) (q.1 : ℝ) ∧
    p.1 ∈ fwdHull (drive κ B p.2) ((q.1 : ℝ) + 1 / ((m : ℝ) + 1))

theorem measurableSet_win (hBm : ∀ r : ℝ≥0, Measurable (B r))
    (hBc : ∀ ω, Continuous fun t => B t ω) (κ : ℝ) (m : ℕ)
    (q : {q : ℚ // (0 : ℝ) ≤ (q : ℝ)}) :
    MeasurableSet {p : ℂ × Ω | win κ B m q p} :=
  (measurableSet_fwdHull_prod hBm hBc κ q.2).compl.inter
    (measurableSet_fwdHull_prod hBm hBc κ (by have h := q.2; positivity))

/-- The countable Cauchy condition at one level `n`: the field values at the rationals of the
window `[τ - 1/(m+1), τ)` differ by at most `1/(n+1)`. -/
noncomputable def ratOscAt (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (m n : ℕ) (p : ℂ × Ω) : Prop :=
  ∀ q q' : {q : ℚ // (0 : ℝ) ≤ (q : ℝ)},
    win κ B m q p → win κ B m q' p →
      |extFieldAt κ B (q.1 : ℝ) p - extFieldAt κ B (q'.1 : ℝ) p| ≤ 1 / ((n : ℝ) + 1)

theorem measurableSet_abs_sub_le {α : Type*} [MeasurableSpace α] {f g : α → ℝ}
    (hf : Measurable f) (hg : Measurable g) (r : ℝ) :
    MeasurableSet {a | |f a - g a| ≤ r} := by
  have h : {a | |f a - g a| ≤ r} = (fun a => f a - g a) ⁻¹' Set.Icc (-r) r := by
    ext a; simp [abs_le]
  rw [h]
  exact (hf.sub hg) measurableSet_Icc

/-- The guard: the left limit of the field at `τ(z)` exists (see `ExtMeas2`). -/
noncomputable def guardAt (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (p : ℂ × Ω) : Prop :=
  ∀ n : ℕ, ∃ m : ℕ, ratOscAt κ B m n p

theorem measurableSet_ratOscAt (hBm : ∀ r : ℝ≥0, Measurable (B r))
    (hBc : ∀ ω, Continuous fun t => B t ω) (κ : ℝ) (m n : ℕ) :
    MeasurableSet {p : ℂ × Ω | ratOscAt κ B m n p} := by
  have he : {p : ℂ × Ω | ratOscAt κ B m n p} =
      ⋂ q : {q : ℚ // (0 : ℝ) ≤ (q : ℝ)}, ⋂ q' : {q : ℚ // (0 : ℝ) ≤ (q : ℝ)},
        {p : ℂ × Ω | win κ B m q p → win κ B m q' p →
          |extFieldAt κ B (q.1 : ℝ) p - extFieldAt κ B (q'.1 : ℝ) p| ≤ 1 / ((n : ℝ) + 1)} := by
    ext p
    simp only [ratOscAt, Set.mem_iInter, Set.mem_setOf_eq]
  rw [he]
  refine MeasurableSet.iInter fun q => MeasurableSet.iInter fun q' => ?_
  have h3 : MeasurableSet {p : ℂ × Ω |
      |extFieldAt κ B (q.1 : ℝ) p - extFieldAt κ B (q'.1 : ℝ) p| ≤ 1 / ((n : ℝ) + 1)} :=
    measurableSet_abs_sub_le (measurable_extFieldAt hBm hBc κ q.2)
      (measurable_extFieldAt hBm hBc κ q'.2) _
  have hset : {p : ℂ × Ω | win κ B m q p → win κ B m q' p →
      |extFieldAt κ B (q.1 : ℝ) p - extFieldAt κ B (q'.1 : ℝ) p| ≤ 1 / ((n : ℝ) + 1)} =
      {p : ℂ × Ω | win κ B m q p}ᶜ ∪ ({p : ℂ × Ω | win κ B m q' p}ᶜ ∪ {p : ℂ × Ω |
        |extFieldAt κ B (q.1 : ℝ) p - extFieldAt κ B (q'.1 : ℝ) p| ≤ 1 / ((n : ℝ) + 1)}) := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_compl_iff]
    tauto
  rw [hset]
  exact ((measurableSet_win hBm hBc κ m q).compl.union
    ((measurableSet_win hBm hBc κ m q').compl.union h3))

theorem measurableSet_guardAt (hBm : ∀ r : ℝ≥0, Measurable (B r))
    (hBc : ∀ ω, Continuous fun t => B t ω) (κ : ℝ) :
    MeasurableSet {p : ℂ × Ω | guardAt κ B p} := by
  have he : {p : ℂ × Ω | guardAt κ B p} =
      ⋂ n : ℕ, ⋃ m : ℕ, {p : ℂ × Ω | ratOscAt κ B m n p} := by
    ext p
    simp only [guardAt, Set.mem_iInter, Set.mem_iUnion, Set.mem_setOf_eq]
  rw [he]
  exact MeasurableSet.iInter fun n =>
    MeasurableSet.iUnion fun m => measurableSet_ratOscAt hBm hBc κ m n

/-- The value `limUnder` returns at a filter along which the function has no limit
(`limUnder_of_not_tendsto`); it is a *constant*, which is what makes the junk values of the two
`limUnder`s below agree. -/
noncomputable def junkReal : ℝ := Classical.choice (inferInstance : Nonempty ℝ)

theorem limUnder_of_not_tendsto_eq_junkReal {α : Type*} {l : Filter α} {g : α → ℝ}
    (h : ¬ ∃ x, Tendsto g l (𝓝 x)) : limUnder l g = junkReal := by
  rw [limUnder_of_not_tendsto h, junkReal]

/-- **The measurable candidate for the extended field.**  On the hull: if the left limit exists
(the guard) it is the limit of the dyadic-floor values, otherwise the junk value of `limUnder`;
off the hull, the field `hTfwd` (which is `extFieldAt · T`). -/
noncomputable def candExt (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (T : ℝ) (p : ℂ × Ω) : ℝ :=
  if p.1 ∈ fwdHull (drive κ B p.2) T then
    (if guardAt κ B p then limUnder atTop (fun j => dval κ B T j p) else junkReal)
  else extFieldAt κ B T p

theorem measurable_candExt (hBm : ∀ r : ℝ≥0, Measurable (B r))
    (hBc : ∀ ω, Continuous fun t => B t ω) (κ : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    Measurable (candExt κ B T) := by
  have hlim : Measurable fun p : ℂ × Ω => limUnder atTop (fun j => dval κ B T j p) :=
    (StronglyMeasurable.limUnder (l := atTop) (f := fun j p => dval κ B T j p)
      fun j => (measurable_dval hBm hBc κ T j).stronglyMeasurable).measurable
  exact Measurable.ite (measurableSet_fwdHull_prod hBm hBc κ hT)
    (Measurable.ite (measurableSet_guardAt hBm hBc κ) hlim measurable_const)
    (measurable_extFieldAt hBm hBc κ hT)

end Defs

end Thm11Asm
end QuantumZipper
