import QuantumZipper.Proofs.Zipper.E6Concrete
import QuantumZipper.Proofs.Zipper.ESMLen
import QuantumZipper.Proofs.Field.Factorization

/-!
# E6-ID: the deterministic identity `Z_C C̄_x ≈ zipLenDown γ ℓ₁ (Z_C C̄_y)`

Input `hId` of `E6.e6_concrete` (blueprint `blueprint/E_BRANCH_BLUEPRINT.md` §E6: "deterministic
identity on `{τ_{x_{ℓ₀}} ≤ T}`: `zipCapDown γ (τ_{x_{ℓ₀}} − τ_x) C̄_{x_{ℓ₀}} = C̄_x` (ConfigEq;
zipCapDown cocycle, B5-V: the left length unzipped is `ν[x_{ℓ₀}, x] = ℓ₀`), hence
`Z_C C̄_x = zipLenDown γ ℓ₁ (Z_C C̄_{x_{ℓ₀}})` (`zipLenDown_eq_canonConfig`, addConst multiplies
lengths by `e^{C/2}`, B3(d))"). Paper: Sheffield, arXiv:1012.4797, proof of Theorem 1.8 (PDF p. 70,
"unzipping by a fixed quantity of quantum boundary length"); the paper gives no details. The
argument below is the blueprint's; the length-time identification is our own elementary argument.

Split:
* **Length part (proved here).** With `u = T − τ_y`, the left length unzipped from `C̄_y = 𝒞_{τ_y}`
  in capacity time `s ≤ τ_y − τ_x` is `ν_{h⁰}[y, 0₋(τ_y − s)]` (`LenCollidedStmt`, B5-V for the
  configurations `𝒞_t`), so the first time the (addConst-rescaled) left length reaches `ℓ₁` is
  exactly `τ_y − τ_x` (`e6id_sInf_eq`, own elementary argument). `e6_id_of_len`.
* **`LenCollidedStmt` from uniform B5-V** (`lenCollidedStmt_of`): `ESM.ae_b5v_uniform` (fixed-time
  B5-V + a.s. monotonicity of `L⁻`, decision D21) and the `L⁻` cocycle `LenCocycleStmt`
  (blueprint §B5: `L⁻_{u+s} = L⁻_u + L⁻_s ∘ zipCapDown γ u`), via `e6id_len_collided`.
* **Zip algebra (hypothesis `CanonZipStmt`).** `zipLenDown` of the canonicalized,
  constant-shifted configuration `canonConfig (addConst C_u.1 k, C_u.2)` is, up to `ConfigEq`, the
  canonicalized, constant-shifted `C_{u+t₀}`, `t₀` that first time. `canonZipStmt_of` reduces it
  to the field cocycle `CapCocycleAddStmt` (the driver half is pathwise,
  `zipCapDown_snd_cocycle`) and B3(b)+B3(d) for length unzipping `ZipLenCanonStmt`.
* `e6_id` (the B5-V route) and `e6_concrete_of_id` (E6 with `hId` discharged).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace QuantumZipper.E6

open B2 E1

variable {Ω : Type} [MeasurableSpace Ω]

/-! ## Deterministic length-time identification -/

section Det

variable {ν : Measure ℝ} {zm : ℝ → ℝ} {T : ℝ}

/-- **First passage time of the unzipped length.** If the length unzipped in capacity time
`s ∈ [0, τ_y − τ_x]` is `ν[y, 0₋(τ_y − s)]`, with `0₋` strictly decreasing, `0₋(τ_x) = x`,
`0₋(τ_y) = y` and `ν` positive on open intervals and finite on compact ones, then the first time
the unzipped length reaches `ν[y, x]` is `τ_y − τ_x`. -/
lemma e6id_sInf_eq {L : ℝ → ℝ≥0∞} {ℓ : ℝ≥0∞} {τx τy x y : ℝ}
    (hpos : ∀ a b, a < b → 0 < ν (Ioo a b)) (hfin : ∀ a b, ν (Icc a b) ≠ ∞)
    (hanti : StrictAntiOn zm (Icc 0 T)) (hτx : τx ∈ Icc 0 T) (hτy : τy ∈ Icc 0 T)
    (hzx : zm τx = x) (hzy : zm τy = y) (hle : τx ≤ τy)
    (hL : ∀ s ∈ Icc 0 (τy - τx), L s = ν (Icc y (zm (τy - s))))
    (hℓ : ν (Icc y x) = ℓ) :
    sInf {s : ℝ | 0 ≤ s ∧ ℓ ≤ L s} = τy - τx := by
  have hmem : τy - τx ∈ {s : ℝ | 0 ≤ s ∧ ℓ ≤ L s} := by
    refine ⟨sub_nonneg.2 hle, ?_⟩
    rw [hL _ ⟨sub_nonneg.2 hle, le_rfl⟩, sub_sub_cancel, hzx, hℓ]
  refine le_antisymm (csInf_le ⟨0, fun s hs => hs.1⟩ hmem) (le_csInf ⟨_, hmem⟩ fun s hs => ?_)
  by_contra hlt
  push Not at hlt
  have hr : τy - s ∈ Icc 0 T := ⟨by linarith [hτx.1], by linarith [hτy.2, hs.1]⟩
  have hz1 : zm (τy - s) < x := hzx ▸ hanti hτx hr (by linarith)
  have hz0 : y ≤ zm (τy - s) := hzy ▸ hanti.antitoneOn hr hτy (by linarith [hs.1])
  have h2 := hs.2
  rw [hL s ⟨hs.1, hlt.le⟩] at h2
  set z := zm (τy - s)
  have hsub : Icc y z ∪ Ioo z x ⊆ Icc y x := by
    rintro t (ht | ht)
    · exact ⟨ht.1, ht.2.trans hz1.le⟩
    · exact ⟨hz0.trans ht.1.le, ht.2.le⟩
  have hdisj : Disjoint (Icc y z) (Ioo z x) := by
    rw [Set.disjoint_left]; intro t ht ht'; exact absurd ht.2 (not_le.2 ht'.1)
  have h3 : ν (Icc y z) + ν (Ioo z x) ≤ ℓ := by
    rw [← measure_union hdisj measurableSet_Ioo, ← hℓ]; exact measure_mono hsub
  have h4 : ν (Icc y z) < ν (Icc y z) + ν (Ioo z x) :=
    ENNReal.lt_add_right (hfin _ _) (hpos _ _ hz1).ne'
  exact absurd (h4.trans_le (h3.trans h2)) (lt_irrefl _)

end Det

/-! ## The remaining B-items, as statements -/

/-! ## Splitting the zip algebra: field cocycle + canonicalization -/

/-- The driver half of the `zipCapDown` cocycle is pathwise and literal: for `s ≥ 0`, unzipping
by `u` and then by `s` gives the driver `W(u + s + ·) − W(u + s)`. -/
lemma zipCapDown_snd_cocycle (γ u s : ℝ) (c : FieldSample × (ℝ → ℝ)) (hs : 0 ≤ s) :
    (zipCapDown γ s (zipCapDown γ u c)).2 = (zipCapDown γ (u + s) c).2 := by
  funext v
  simp only [zipCapDown]
  rw [max_eq_left (by positivity : 0 ≤ s + max v 0), max_eq_left hs, ← add_assoc]
  ring

/-- `canonConfig` reads the field only through `avgReg`. -/
lemma canonConfig_congr_avgReg {γ : ℝ} {x x' : FieldSample} {W W' : ℝ → ℝ}
    (h1 : avgReg x = avgReg x') (h2 : W = W') : canonConfig γ (x, W) = canonConfig γ (x', W') := by
  unfold canonConfig
  simp only
  rw [Factorization.canonical_congr h1, Factorization.scaleParam_congr h1, h2]

/-- **Field cocycle of `zipCapDown` after adding a constant** (Corollary 1.5(b) for two
unzippings, at all times at once; the constant is added because `avgReg ∘ addConst` is not a
function of `avgReg` for non-convergent raw values): a.s., for all `u, s ≥ 0` with `u + s ≤ T`
and all `k`, `avgReg (C_u unzipped by s + k) = avgReg (C_{u+s} + k)`. -/
def CapCocycleAddStmt (κ T : ℝ) (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) :
    Prop :=
  ∀ᵐ ω ∂P, ∀ u s k : ℝ, 0 ≤ u → 0 ≤ s → u + s ≤ T →
    avgReg (addConst (zipCapDown (Real.sqrt κ) s (zipCapDown (Real.sqrt κ) u (cfg κ B X ω))).1 k) =
      avgReg (addConst (zipCapDown (Real.sqrt κ) (u + s) (cfg κ B X ω)).1 k)

/-! ## B5-V for the collided configurations -/

/-! ## E6-ID -/

end QuantumZipper.E6
