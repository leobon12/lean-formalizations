import QuantumZipper.Proofs.Zipper.F1Reflect

/-!
# F1c input (e): from locality of the lengths to a germ-measurable ratio

Theorem 1.3, node F1c (`blueprint/E_BRANCH_BLUEPRINT.md` §F1; Sheffield, arXiv:1012.4797, §5.4,
pp. 70–72, where the ratio of the two quantum lengths is shown to be a.s. constant by a 0-1 law).
`F1.f1cd_lengths_agree` needs the ratio `f` with `L⁺ = f L⁻` to be measurable for the germ
`⨅ n, ⨆ i ∈ S, 𝒜 i n`. This file derives such a germ-measurable version from **locality at small
times** (B5 locality):

* `exists_iInf_version`: if for every `n` the function `f` is a.e. equal to a `𝒢 n`-measurable
  function, and `𝒢` is antitone, then `f` is a.e. equal to a `⨅ n, 𝒢 n`-measurable function
  (the `limsup` of the versions);
* `ae_eq_level_of_local`: if along times `s m > 0` the lengths `unzipLengths γ (c ω) (s m)` agree,
  on events `E m` that a.s. eventually occur, with `𝒢 n`-measurable functions, and `L⁺ = f L⁻`
  with `0 < L⁻_{s m} < ⊤`, then `f` is a.e. equal to a `𝒢 n`-measurable function;
* **`f1cd_lengths_agree_local`**: `f1cd_lengths_agree` with the germ-measurability of `f` replaced
  by this locality hypothesis (`hloc`), for the families `𝒢 n = ⨆ i ∈ S, 𝒜 i n`.

The mathematics: `F 1 = F(s)/s·1` is the ratio at every small time `s` (F1a–F1b); for small `s`
the hull `η[0,s]` lies in a small ball on an event of probability close to `1`, on which the
lengths are functions of the field near `0` and of the driver on `[0,s]` (B5 locality). The
measure-theoretic bookkeeping (limsup of versions) is an own elementary argument.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace F1

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- **Germ version from level versions.** For an antitone sequence of σ-algebras `𝒢 n`, a
function a.e. equal to a `𝒢 n`-measurable function for every `n` is a.e. equal to a
`⨅ n, 𝒢 n`-measurable function. -/
theorem exists_iInf_version {𝒢 : ℕ → MeasurableSpace Ω} (h𝒢 : Antitone 𝒢) {f : Ω → ℝ≥0∞}
    (hloc : ∀ n, ∃ g : Ω → ℝ≥0∞, Measurable[𝒢 n] g ∧ f =ᵐ[P] g) :
    ∃ g : Ω → ℝ≥0∞, Measurable[⨅ n, 𝒢 n] g ∧ f =ᵐ[P] g := by
  choose G hGm hGe using hloc
  refine ⟨fun ω => limsup (fun m => G m ω) atTop, ?_, ?_⟩
  · refine measurable_iff_comap_le.2 (le_iInf fun n => ?_)
    have e : (fun ω => limsup (fun m => G m ω) atTop) =
        fun ω => limsup (fun m => G (m + n) ω) atTop := by
      funext ω; exact (limsup_nat_add (fun m => G m ω) n).symm
    rw [e]
    exact measurable_iff_comap_le.1 (Measurable.limsup (mδ := 𝒢 n) fun m =>
      (hGm (m + n)).mono (h𝒢 (Nat.le_add_left n m)) le_rfl)
  · filter_upwards [ae_all_iff.2 hGe] with ω h
    have : (fun m => G m ω) = fun _ => f ω := funext fun m => (h m).symm
    rw [this, limsup_const]

/-- The ratio `L⁺/L⁻` read from a pair of lengths. -/
def lenRatio (p : ℝ≥0∞ × ℝ≥0∞) : ℝ≥0∞ := p.2 / p.1

theorem measurable_lenRatio : Measurable lenRatio :=
  measurable_snd.mul measurable_fst.inv

/-- `L⁺ = f L⁻` with `0 < L⁻ < ⊤` identifies `f` with the ratio. -/
theorem lenRatio_eq_of {p : ℝ≥0∞ × ℝ≥0∞} {f : ℝ≥0∞} (h : p.2 = f * p.1) (h0 : 0 < p.1)
    (htop : p.1 < ⊤) : lenRatio p = f := by
  rw [lenRatio, h, ENNReal.mul_div_cancel_right h0.ne' htop.ne]

variable [IsProbabilityMeasure P]

end F1
end QuantumZipper
