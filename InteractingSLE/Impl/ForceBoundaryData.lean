import InteractingSLE.Foundations.Harmonic.StepData

/-!
# The bounded harmonic extension of the force-word boundary data

Packet PROVE-T11-COMP. Implementation proof of the companion theorem of Theorem 1.1
(Specification p. 9, and the convention on p. 2: "their harmonic extension means the bounded
harmonic extension in that specified chart"): for every state `(vL, vR)` of a force word the
boundary data `forceBoundaryData κ F vL vR` has a bounded harmonic extension in `ℍ`, unique on `ℍ`.

The definitions `ForceWord`, `forceBoundaryData`, `forceJumpSet` and `IsBoundedHarmonicExtension`
are verbatim copies of ARCH-2's audited candidate (`C2-v1.lean`), placed in the namespace
`InteractingSLE.Impl` so that they do not clash with the frozen versions; the orchestrator adds an
adapter once those land.

## Proof
Write `λ = π/√κ` and `𝟙_{≥b}(x) = 𝟙[b ≤ x]`. For every real `x`,
`forceBoundaryData κ F vL vR x = λ (−1 + 2·𝟙_{≥0}(x) − ∑ᵢ ρL i (1 − 𝟙_{≥ min 0 (vL i)}(x))
  + ∑ᵢ ρR i 𝟙_{≥ max 0 (vR i)}(x))`
(for `x < 0`: `𝟙[min 0 a ≤ x] = 𝟙[a ≤ x]` and `𝟙[max 0 b ≤ x] = 0`; for `x ≥ 0`:
`𝟙[min 0 a ≤ x] = 1`, `𝟙[max 0 b ≤ x] = 𝟙[b ≤ x]`). Each `𝟙_{≥b}` is the one-jump step data
`jumpStepData b`, whose bounded harmonic extension `jumpExt b` is given by
`InteractingSLE.StepData.harmonicExtH`; the same linear combination of the `jumpExt`s is
harmonic, bounded and has the right boundary values off `{0} ∪ range vL ∪ range vR`
(`min 0 a ∈ {0, a}`, `max 0 b ∈ {0, b}`). Uniqueness is Lindelöf's maximum principle with a
finite exceptional set, `InteractingSLE.eqOn_of_tendsto_sub_H`.

## Main statements
* `InteractingSLE.Impl.isBoundedHarmonicExtension_forceExt`: existence (explicit extension);
* `InteractingSLE.Impl.eqOn_of_isBoundedHarmonicExtension`: uniqueness on `ℍ`;
* `InteractingSLE.Impl.existsUnique_isBoundedHarmonicExtension_forceBoundaryData`: the
  companion statement, exactly as in `C2-v1.lean`.
-/

set_option autoImplicit false

noncomputable section

open Filter Set Topology

namespace InteractingSLE

namespace Impl

/-! ## Verbatim copies of the candidate's definitions (ARCH-1/ARCH-2, `C2-v1.lean`) -/

/-- An ordered finite force word (Specification p. 3, "Ordered force words and integrated
evolution"; Definition 2.1, p. 20): `nL` left marks at `x_{nL,L} ≤ ⋯ ≤ x_{1,L} ≤ 0` and `nR`
right marks at `0 ≤ x_{1,R} ≤ ⋯ ≤ x_{nR,R}`, with real weights `ρ = (ρ_L; ρ_R)`. The Lean index
`i : Fin n` is the source index `i + 1`. The side label is the list a mark belongs to, so a left
mark at `0` is `0⁻` and a right mark at `0` is `0⁺`. Coincident marks are kept as separate
entries; the evolution and the threshold below sum their weights automatically. -/
structure ForceWord where
  /-- Number of left marks `k`. -/
  nL : ℕ
  /-- Number of right marks `ℓ`. -/
  nR : ℕ
  /-- Left positions `x_{i+1,L}`. -/
  xL : Fin nL → ℝ
  /-- Right positions `x_{i+1,R}`. -/
  xR : Fin nR → ℝ
  /-- Left weights `ρ^{i+1,L}`. -/
  ρL : Fin nL → ℝ
  /-- Right weights `ρ^{i+1,R}`. -/
  ρR : Fin nR → ℝ
  /-- `x_{k,L} ≤ ⋯ ≤ x_{1,L}`. -/
  antitone_xL : Antitone xL
  /-- `x_{1,L} ≤ 0`. -/
  xL_nonpos : ∀ i, xL i ≤ 0
  /-- `x_{1,R} ≤ ⋯ ≤ x_{ℓ,R}`. -/
  monotone_xR : Monotone xR
  /-- `0 ≤ x_{1,R}`. -/
  xR_nonneg : ∀ i, 0 ≤ xR i

/-- The force-word boundary data of Theorem 1.1 (p. 9) at a state whose centred force-point
positions are `vL i = V̂^{i+1,L}`, `vR i = V̂^{i+1,R}`: with `λ = π/√κ`,
`−λ (1 + ∑_{i=0}^{j} ρ^{i,L})` on `[V̂^{j+1,L}, V̂^{j,L})` and `λ (1 + ∑_{i=0}^{j} ρ^{i,R})` on
`[V̂^{j,R}, V̂^{j+1,R})` (`V̂^{0,q} = 0`, `V̂^{k+1,L} = −∞`, `V̂^{ℓ+1,R} = ∞`, `ρ^{0,q} = 0`).
For `x < 0` the left marks strictly to the right of `x` are exactly the marks `1, …, j` of the
interval containing `x`; for `x ≥ 0` the right marks at or to the left of `x` are the marks
`1, …, j`. Intervals of zero length contribute no point. -/
def forceBoundaryData (κ : ℝ) (F : ForceWord) (vL : Fin F.nL → ℝ) (vR : Fin F.nR → ℝ)
    (x : ℝ) : ℝ :=
  if x < 0 then
    -(Real.pi / Real.sqrt κ) * (1 + ∑ i ∈ Finset.univ.filter (fun i => x < vL i), F.ρL i)
  else
    (Real.pi / Real.sqrt κ) * (1 + ∑ i ∈ Finset.univ.filter (fun i => vR i ≤ x), F.ρR i)

/-- The finite set of possible jump points of `forceBoundaryData`: `0` and the force points. -/
def forceJumpSet (F : ForceWord) (vL : Fin F.nL → ℝ) (vR : Fin F.nR → ℝ) : Set ℝ :=
  insert 0 (Set.range vL ∪ Set.range vR)

/-- `u` is a bounded harmonic extension in `ℍ` of the boundary data `g` off the exceptional set
`S` (Specification p. 2: "their harmonic extension means the bounded harmonic extension in that
specified chart"; Theorem 1.1, p. 9): `u` is harmonic on `ℍ`, bounded on `ℍ`, and tends to
`g x` at every real boundary point `x ∉ S`. Only the values of `u` on `ℍ` are constrained. -/
def IsBoundedHarmonicExtension (g : ℝ → ℝ) (S : Set ℝ) (u : ℂ → ℝ) : Prop :=
  InnerProductSpace.HarmonicOnNhd u QuantumZipper.H ∧
    (∃ C : ℝ, ∀ z ∈ QuantumZipper.H, |u z| ≤ C) ∧
    ∀ x : ℝ, x ∉ S → Tendsto u (𝓝[QuantumZipper.H] (x : ℂ)) (𝓝 (g x))

/-! ## Algebra of harmonic functions -/

theorem harmonicOnNhd_const_mul {f : ℂ → ℝ} {U : Set ℂ} (c : ℝ)
    (hf : InnerProductSpace.HarmonicOnNhd f U) :
    InnerProductSpace.HarmonicOnNhd (fun z => c * f z) U := by
  have := hf.const_smul (c := c)
  simpa only [Pi.smul_def, smul_eq_mul] using this

theorem harmonicOnNhd_finsetSum {ι : Type*} (s : Finset ι) {f : ι → ℂ → ℝ} {U : Set ℂ}
    (hf : ∀ i ∈ s, InnerProductSpace.HarmonicOnNhd (f i) U) :
    InnerProductSpace.HarmonicOnNhd (fun z => ∑ i ∈ s, f i z) U := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

/-! ## One jump -/

/-- The one-jump step data `𝟙[b ≤ x]`: breakpoint `b`, value `0` before and `1` after. -/
def jumpStepData (b : ℝ) : StepData where
  n := 1
  x := ![b]
  monotone_x := fun i j _ => by rw [Subsingleton.elim i j]
  v := ![0, 1]

/-- The bounded harmonic extension of `𝟙[b ≤ x]`: `1 − arg (z − b)/π`. -/
def jumpExt (b : ℝ) (z : ℂ) : ℝ :=
  (jumpStepData b).harmonicExtH z

theorem jumpExt_eq (b : ℝ) (z : ℂ) : jumpExt b z = 1 - Complex.arg (z - b) / Real.pi := by
  show stepHarmonicH 1 ![b] ![0, 1] z = _
  simp [stepHarmonicH]
  ring

theorem harmonicOnNhd_jumpExt (b : ℝ) :
    InnerProductSpace.HarmonicOnNhd (jumpExt b) QuantumZipper.H :=
  (jumpStepData b).harmonicOnNhd_harmonicExtH

theorem jumpExt_mem_Icc (b : ℝ) {z : ℂ} (hz : z ∈ QuantumZipper.H) :
    jumpExt b z ∈ Icc (0 : ℝ) 1 := by
  rw [jumpExt_eq]
  have h0 : 0 ≤ Complex.arg (z - b) :=
    Complex.arg_nonneg_iff.2 (sub_ofReal_mem_H hz b).le
  have h1 : Complex.arg (z - b) ≤ Real.pi := Complex.arg_le_pi _
  have hπ := Real.pi_pos
  constructor
  · rw [sub_nonneg, div_le_one hπ]; exact h1
  · have : 0 ≤ Complex.arg (z - b) / Real.pi := div_nonneg h0 hπ.le
    linarith

theorem abs_jumpExt_le (b : ℝ) {z : ℂ} (hz : z ∈ QuantumZipper.H) : |jumpExt b z| ≤ 1 := by
  obtain ⟨h0, h1⟩ := jumpExt_mem_Icc b hz
  rw [abs_le]; constructor <;> linarith

theorem jumpStepData_bdry {b t : ℝ} :
    (jumpStepData b).bdry t = if b ≤ t then 1 else 0 := by
  have hx : ∀ j : Fin (jumpStepData b).n, (jumpStepData b).x j = b := fun ⟨j, hj⟩ => by
    have h1 : j < 1 := hj
    obtain rfl : j = 0 := by omega
    rfl
  by_cases hb : b ≤ t
  · rw [ite_eq_left hb, (jumpStepData b).bdry_eq_of_forall_le_iff (k := 1) le_rfl
      fun j => by rw [hx j]; exact iff_of_true hb j.isLt]
    rfl
  · rw [ite_eq_right hb, (jumpStepData b).bdry_eq_of_forall_le_iff (k := 0) (Nat.zero_le _)
      fun j => by rw [hx j]; exact iff_of_false hb (Nat.not_lt_zero _)]
    rfl

theorem tendsto_jumpExt {b t : ℝ} (hbt : b ≠ t) :
    Tendsto (jumpExt b) (𝓝[QuantumZipper.H] (t : ℂ)) (𝓝 (if b ≤ t then 1 else 0)) := by
  have hx : ∀ j : Fin (jumpStepData b).n, (jumpStepData b).x j ≠ t := fun ⟨j, hj⟩ => by
    have h1 : j < 1 := hj
    obtain rfl : j = 0 := by omega
    exact hbt
  rw [← jumpStepData_bdry]
  exact (jumpStepData b).tendsto_harmonicExtH hx

/-! ## The extension of the force-word data -/

/-- The explicit bounded harmonic extension of `forceBoundaryData κ F vL vR`. -/
def forceExt (κ : ℝ) (F : ForceWord) (vL : Fin F.nL → ℝ) (vR : Fin F.nR → ℝ) (z : ℂ) : ℝ :=
  Real.pi / Real.sqrt κ * (-1 + 2 * jumpExt 0 z
    - ∑ i, F.ρL i * (1 - jumpExt (min 0 (vL i)) z)
    + ∑ i, F.ρR i * jumpExt (max 0 (vR i)) z)

theorem harmonicOnNhd_forceExt (κ : ℝ) (F : ForceWord) (vL : Fin F.nL → ℝ)
    (vR : Fin F.nR → ℝ) :
    InnerProductSpace.HarmonicOnNhd (forceExt κ F vL vR) QuantumZipper.H := by
  refine harmonicOnNhd_const_mul _ ?_
  refine (((InnerProductSpace.harmonicOnNhd_const (-1 : ℝ)).add
    (harmonicOnNhd_const_mul 2 (harmonicOnNhd_jumpExt 0))).sub ?_).add ?_
  · refine harmonicOnNhd_finsetSum _ fun i _ => harmonicOnNhd_const_mul _ ?_
    exact (InnerProductSpace.harmonicOnNhd_const (1 : ℝ)).sub (harmonicOnNhd_jumpExt _)
  · exact harmonicOnNhd_finsetSum _ fun i _ => harmonicOnNhd_const_mul _
      (harmonicOnNhd_jumpExt _)

theorem abs_forceExt_le (κ : ℝ) (F : ForceWord) (vL : Fin F.nL → ℝ) (vR : Fin F.nR → ℝ)
    {z : ℂ} (hz : z ∈ QuantumZipper.H) :
    |forceExt κ F vL vR z| ≤
      |Real.pi / Real.sqrt κ| * (3 + 2 * ∑ i, |F.ρL i| + ∑ i, |F.ρR i|) := by
  unfold forceExt
  rw [abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  have hJ0 := abs_jumpExt_le 0 hz
  have hL : |∑ i, F.ρL i * (1 - jumpExt (min 0 (vL i)) z)| ≤ 2 * ∑ i, |F.ρL i| := by
    rw [Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [abs_mul, mul_comm]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    have := abs_jumpExt_le (min 0 (vL i)) hz
    calc |1 - jumpExt (min 0 (vL i)) z| ≤ |(1 : ℝ)| + |jumpExt (min 0 (vL i)) z| :=
          abs_sub _ _
      _ ≤ 2 := by rw [abs_one]; linarith
  have hR : |∑ i, F.ρR i * jumpExt (max 0 (vR i)) z| ≤ ∑ i, |F.ρR i| := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [abs_mul]
    calc |F.ρR i| * |jumpExt (max 0 (vR i)) z| ≤ |F.ρR i| * 1 :=
          mul_le_mul_of_nonneg_left (abs_jumpExt_le _ hz) (abs_nonneg _)
      _ = |F.ρR i| := mul_one _
  have h2 : |2 * jumpExt 0 z| ≤ 2 := by
    rw [abs_mul, abs_two]; linarith
  calc |-1 + 2 * jumpExt 0 z - ∑ i, F.ρL i * (1 - jumpExt (min 0 (vL i)) z)
        + ∑ i, F.ρR i * jumpExt (max 0 (vR i)) z|
      ≤ |-1 + 2 * jumpExt 0 z - ∑ i, F.ρL i * (1 - jumpExt (min 0 (vL i)) z)|
        + |∑ i, F.ρR i * jumpExt (max 0 (vR i)) z| := abs_add_le _ _
    _ ≤ |-1 + 2 * jumpExt 0 z| + |∑ i, F.ρL i * (1 - jumpExt (min 0 (vL i)) z)|
        + |∑ i, F.ρR i * jumpExt (max 0 (vR i)) z| := by
          gcongr; exact abs_sub _ _
    _ ≤ (|(-1 : ℝ)| + |2 * jumpExt 0 z|) + 2 * ∑ i, |F.ρL i| + ∑ i, |F.ρR i| := by
          gcongr; exact abs_add_le _ _
    _ ≤ 3 + 2 * ∑ i, |F.ρL i| + ∑ i, |F.ρR i| := by
          rw [abs_neg, abs_one]; linarith

/-- The boundary value of `forceExt` at `x` off the jump points, as a combination of
indicators. -/
theorem tendsto_forceExt (κ : ℝ) (F : ForceWord) (vL : Fin F.nL → ℝ) (vR : Fin F.nR → ℝ)
    {x : ℝ} (hx : x ∉ forceJumpSet F vL vR) :
    Tendsto (forceExt κ F vL vR) (𝓝[QuantumZipper.H] (x : ℂ))
      (𝓝 (Real.pi / Real.sqrt κ * (-1 + 2 * (if (0 : ℝ) ≤ x then 1 else 0)
        - ∑ i, F.ρL i * (1 - if min 0 (vL i) ≤ x then 1 else 0)
        + ∑ i, F.ρR i * (if max 0 (vR i) ≤ x then 1 else 0)))) := by
  simp only [forceJumpSet, mem_insert_iff, mem_union, mem_range, not_or, not_exists] at hx
  obtain ⟨hx0, hxL, hxR⟩ := hx
  have hL : ∀ i, min 0 (vL i) ≠ x := fun i => by
    rcases min_choice 0 (vL i) with h | h <;> rw [h]
    · exact fun e => hx0 e.symm
    · exact hxL i
  have hR : ∀ i, max 0 (vR i) ≠ x := fun i => by
    rcases max_choice 0 (vR i) with h | h <;> rw [h]
    · exact fun e => hx0 e.symm
    · exact hxR i
  refine tendsto_const_nhds.mul ?_
  refine ((tendsto_const_nhds.add (tendsto_const_nhds.mul
    (tendsto_jumpExt (fun e => hx0 e.symm)))).sub ?_).add ?_
  · exact tendsto_finsetSum _ fun i _ =>
      tendsto_const_nhds.mul (tendsto_const_nhds.sub (tendsto_jumpExt (hL i)))
  · exact tendsto_finsetSum _ fun i _ => tendsto_const_nhds.mul (tendsto_jumpExt (hR i))

/-- Off `0`, the indicator combination is the force-word boundary data. -/
theorem forceBoundaryData_eq_indicators (κ : ℝ) (F : ForceWord) (vL : Fin F.nL → ℝ)
    (vR : Fin F.nR → ℝ) {x : ℝ} (hx0 : x ≠ 0) :
    forceBoundaryData κ F vL vR x =
      Real.pi / Real.sqrt κ * (-1 + 2 * (if (0 : ℝ) ≤ x then 1 else 0)
        - ∑ i, F.ρL i * (1 - if min 0 (vL i) ≤ x then 1 else 0)
        + ∑ i, F.ρR i * (if max 0 (vR i) ≤ x then 1 else 0)) := by
  unfold forceBoundaryData
  rcases lt_or_gt_of_ne hx0 with hneg | hpos
  · rw [ite_eq_left hneg, ite_eq_right (not_le.2 hneg)]
    have hL : ∀ i, F.ρL i * (1 - if min 0 (vL i) ≤ x then (1 : ℝ) else 0) =
        if x < vL i then F.ρL i else 0 := fun i => by
      by_cases h : x < vL i
      · rw [ite_eq_right (not_le.2 (lt_min hneg h)), ite_eq_left h]; ring
      · rw [ite_eq_left (min_le_of_right_le (not_lt.1 h)), ite_eq_right h]; ring
    have hR : ∀ i, F.ρR i * (if max 0 (vR i) ≤ x then (1 : ℝ) else 0) = 0 := fun i => by
      rw [ite_eq_right (not_le.2 (hneg.trans_le (le_max_left _ _)))]; ring
    simp only [hL, hR, Finset.sum_const_zero, ← Finset.sum_filter]
    ring
  · rw [ite_eq_right (not_lt.2 hpos.le), ite_eq_left hpos.le]
    have hL : ∀ i, F.ρL i * (1 - if min 0 (vL i) ≤ x then (1 : ℝ) else 0) = 0 := fun i => by
      rw [ite_eq_left ((min_le_left _ _).trans hpos.le)]; ring
    have hR : ∀ i, F.ρR i * (if max 0 (vR i) ≤ x then (1 : ℝ) else 0) =
        if vR i ≤ x then F.ρR i else 0 := fun i => by
      by_cases h : vR i ≤ x
      · rw [ite_eq_left (max_le hpos.le h), ite_eq_left h]; ring
      · rw [ite_eq_right (fun e => h ((le_max_right _ _).trans e)), ite_eq_right h]; ring
    simp only [hL, hR, Finset.sum_const_zero, ← Finset.sum_filter]
    ring

/-- **Existence**: `forceExt` is a bounded harmonic extension of the force-word data. -/
theorem isBoundedHarmonicExtension_forceExt (κ : ℝ) (F : ForceWord) (vL : Fin F.nL → ℝ)
    (vR : Fin F.nR → ℝ) :
    IsBoundedHarmonicExtension (forceBoundaryData κ F vL vR) (forceJumpSet F vL vR)
      (forceExt κ F vL vR) := by
  refine ⟨harmonicOnNhd_forceExt κ F vL vR, ⟨_, fun z hz => abs_forceExt_le κ F vL vR hz⟩,
    fun x hx => ?_⟩
  have hx0 : x ≠ 0 := fun e => hx (e ▸ mem_insert 0 _)
  rw [forceBoundaryData_eq_indicators κ F vL vR hx0]
  exact tendsto_forceExt κ F vL vR hx

/-- **Uniqueness**: two bounded harmonic extensions of the same data off a finite set agree
on `ℍ`. -/
theorem eqOn_of_isBoundedHarmonicExtension {g : ℝ → ℝ} {S : Set ℝ} (hS : S.Finite)
    {u v : ℂ → ℝ} (hu : IsBoundedHarmonicExtension g S u)
    (hv : IsBoundedHarmonicExtension g S v) : EqOn v u QuantumZipper.H := by
  obtain ⟨hvh, ⟨Cv, hCv⟩, hvl⟩ := hv
  obtain ⟨huh, ⟨Cu, hCu⟩, hul⟩ := hu
  have hb : ∀ {w : ℂ → ℝ} {C : ℝ}, (∀ z ∈ QuantumZipper.H, |w z| ≤ C) →
      Bornology.IsBounded (w '' QuantumZipper.H) := fun {w C} hC =>
    isBounded_iff_forall_norm_le.2 ⟨C, by
      rintro _ ⟨z, hz, rfl⟩
      exact (Real.norm_eq_abs _).trans_le (hC z hz)⟩
  refine eqOn_of_tendsto_sub_H hS.toFinset hvh huh (hb hCv) (hb hCu) fun t ht => ?_
  have ht' : t ∉ S := fun h => ht (hS.mem_toFinset.2 h)
  simpa using (hvl t ht').sub (hul t ht')

theorem forceJumpSet_finite (F : ForceWord) (vL : Fin F.nL → ℝ) (vR : Fin F.nR → ℝ) :
    (forceJumpSet F vL vR).Finite :=
  ((Set.finite_range vL).union (Set.finite_range vR)).insert 0

/-- **Well-definedness of the bounded harmonic extension of force-word data** (companion of
Theorem 1.1, p. 9, and of the convention on p. 2), exactly the statement of
`existsUnique_isBoundedHarmonicExtension_forceBoundaryData` in ARCH-2's candidate. -/
theorem existsUnique_isBoundedHarmonicExtension_forceBoundaryData (κ : ℝ) (F : ForceWord)
    (vL : Fin F.nL → ℝ) (vR : Fin F.nR → ℝ) :
    ∃ u : ℂ → ℝ, IsBoundedHarmonicExtension (forceBoundaryData κ F vL vR)
        (forceJumpSet F vL vR) u ∧
      ∀ v : ℂ → ℝ, IsBoundedHarmonicExtension (forceBoundaryData κ F vL vR)
        (forceJumpSet F vL vR) v → EqOn v u QuantumZipper.H :=
  ⟨forceExt κ F vL vR, isBoundedHarmonicExtension_forceExt κ F vL vR, fun _ hv =>
    eqOn_of_isBoundedHarmonicExtension (forceJumpSet_finite F vL vR)
      (isBoundedHarmonicExtension_forceExt κ F vL vR) hv⟩

end Impl

end InteractingSLE
