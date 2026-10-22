import HigherDimLQGMetric.LogEnergy.DecayKernel
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

set_option autoImplicit false
noncomputable section
open HigherDimLFPP (Rd)
namespace HigherDimLQGMetric

def decayOuterBump {d : ℕ} {b : ℝ} (hb : 0 < b) : ContDiffBump (0 : Rd d) :=
  ⟨b, 2*b, hb, by linarith⟩

def decayInnerBump {d : ℕ} {a : ℝ} (ha : 0 < a) : ContDiffBump (0 : Rd d) :=
  ⟨a/2, a, by positivity, by linarith⟩

def decayOuterCutoff {d : ℕ} {b : ℝ} (hb : 0 < b) : Rd d → ℝ :=
  decayOuterBump hb

def decayAnnCutoff {d : ℕ} {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : Rd d → ℝ :=
  fun x => decayOuterBump hb x * (1 - decayInnerBump ha x)

theorem decayOuterCutoff_contDiff {d : ℕ} {b : ℝ} (hb : 0 < b) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (decayOuterCutoff (d:=d) hb) := by
  change ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (decayOuterBump hb : Rd d → ℝ)
  exact (decayOuterBump hb).contDiff

theorem decayAnnCutoff_contDiff {d : ℕ} {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (decayAnnCutoff (d:=d) ha hb) := by
  change ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
    (fun x : Rd d => decayOuterBump hb x * (1 - decayInnerBump ha x))
  exact (decayOuterBump hb).contDiff.mul
    (contDiff_const.sub (decayInnerBump ha).contDiff)

theorem decayOuterCutoff_eq_one {d : ℕ} {b : ℝ} (hb : 0 < b) (x : Rd d)
    (hx : ‖x‖ ≤ b) : decayOuterCutoff hb x = 1 := by
  exact (decayOuterBump hb).one_of_mem_closedBall
    (by simpa [decayOuterBump, Metric.mem_closedBall] using hx)

theorem decayAnnCutoff_eq_one {d : ℕ} {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (x : Rd d) (hxa : a ≤ ‖x‖) (hxb : ‖x‖ ≤ b) :
    decayAnnCutoff ha hb x = 1 := by
  dsimp [decayAnnCutoff]
  rw [(decayOuterBump hb).one_of_mem_closedBall
      (by simpa [decayOuterBump, Metric.mem_closedBall] using hxb),
    (decayInnerBump ha).zero_of_le_dist
      (by simpa [decayInnerBump, dist_eq_norm] using hxa)]
  ring

theorem decayOuterCutoff_tsupport_subset {d : ℕ} {b : ℝ} (hb : 0 < b) :
    tsupport (decayOuterCutoff (d:=d) hb) ⊆ Metric.closedBall 0 (2*b) := by
  rw [decayOuterCutoff, (decayOuterBump (d:=d) hb).tsupport_eq]
  rfl

theorem decayAnnCutoff_tsupport_subset {d : ℕ} {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) :
    tsupport (decayAnnCutoff (d:=d) ha hb) ⊆ annCl 0 (a/2) (2*b) := by
  have hsupp : Function.support (decayAnnCutoff (d:=d) ha hb) ⊆
      annCl 0 (a/2) (2*b) := by
    intro x hx
    have hne : decayAnnCutoff ha hb x ≠ 0 := hx
    change a/2 ≤ ‖x - 0‖ ∧ ‖x - 0‖ ≤ 2*b
    constructor
    · by_contra hlt
      have hi : decayInnerBump ha x = 1 :=
        (decayInnerBump ha).one_of_mem_closedBall (by
          simpa [decayInnerBump, Metric.mem_closedBall, dist_eq_norm] using
            le_of_not_ge hlt)
      exact hne (by simp [decayAnnCutoff, hi])
    · by_contra hlt
      have ho : decayOuterBump hb x = 0 :=
        (decayOuterBump hb).zero_of_le_dist (by
          simpa [decayOuterBump, dist_eq_norm] using le_of_not_ge hlt)
      exact hne (by simp [decayAnnCutoff, ho])
  exact closure_minimal hsupp (isClosed_annCl 0 (a/2) (2*b))

theorem decayOuterCutoff_hasCompactSupport {d : ℕ} {b : ℝ} (hb : 0 < b) :
    HasCompactSupport (decayOuterCutoff (d:=d) hb) :=
  (decayOuterBump hb).hasCompactSupport

theorem decayAnnCutoff_hasCompactSupport {d : ℕ} {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) :
    HasCompactSupport (decayAnnCutoff (d:=d) ha hb) := by
  exact (decayOuterBump hb).hasCompactSupport.mul_right

end HigherDimLQGMetric
