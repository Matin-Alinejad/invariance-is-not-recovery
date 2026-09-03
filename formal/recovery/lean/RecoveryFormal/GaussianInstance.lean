import Mathlib
import RecoveryFormal.PairFamilyAchievability

/-!
# pair-family achievability (instantiation) — the explicit independent-pair Gaussian family

`PairFamilyAchievability.lean` proves an exact-recovery upper bound for an abstract
independent-pair model whose noise is assumed sub-Gaussian.  This file certifies that the
model is genuinely the **explicit independent-pair Gaussian family** by instantiating it with
iid `N(0, v)` coordinates:

* `gaussianPairLaw m v` is the law of `m · ∞` iid real Gaussians `N(0, v)`, one per
  `(pair, sample)`;
* `gaussian_hindep` / `gaussian_hsub` verify the independence and sub-Gaussian (noise)
  hypotheses of the abstract theorem for this law;
* `exact_recovery_gaussian` states the achievability bound directly for that Gaussian
  sequence family.

This module does not define the observational Gaussian pair-DAG SEM and does not prove a
minimax converse.  It is an achievability instantiation only.
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

namespace RecoveryFormal
namespace PairFamily

/-- The law of the independent Gaussian sequence family: an iid family of centred real
Gaussians `N(0, v)`, indexed by `(pair, sample) ∈ Fin m × ℕ`. -/
noncomputable def gaussianPairLaw (m : ℕ) (v : ℝ≥0) : Measure ((Fin m × ℕ) → ℝ) :=
  MeasureTheory.Measure.infinitePi (fun _ : (Fin m × ℕ) => gaussianReal 0 v)

instance (m : ℕ) (v : ℝ≥0) : IsProbabilityMeasure (gaussianPairLaw m v) := by
  unfold gaussianPairLaw; infer_instance

/-- The coordinate noise of the explicit Gaussian family. -/
def gaussianNoise (m : ℕ) : Fin m → ℕ → ((Fin m × ℕ) → ℝ) → ℝ :=
  fun k i ω => ω (k, i)

/-- **Independence hypothesis, verified for the Gaussian family.** For each pair, the noise
samples are independent under `gaussianPairLaw`. -/
lemma gaussian_hindep (m : ℕ) (v : ℝ≥0) (k : Fin m) :
    iIndepFun (fun i => gaussianNoise m k i) (gaussianPairLaw m v) := by
  show iIndepFun (fun i => fun ω : (Fin m × ℕ) → ℝ => ω (k, i)) (gaussianPairLaw m v)
  have hfull : iIndepFun (fun (p : Fin m × ℕ) => fun ω : (Fin m × ℕ) → ℝ => ω p)
      (gaussianPairLaw m v) := by
    unfold gaussianPairLaw
    exact iIndepFun_infinitePi (X := fun _ => id) (fun _ => measurable_id)
  have hinj : Function.Injective (fun i : ℕ => (k, i)) := by
    intro a b h; simpa using h
  exact hfull.precomp hinj

/-- **Noise (sub-Gaussian) hypothesis, verified for the Gaussian family.** Each coordinate is
a centred Gaussian `N(0, v)`, hence sub-Gaussian with variance proxy `v`. -/
lemma gaussian_hsub (m : ℕ) (v : ℝ≥0) (k : Fin m) (i : ℕ) :
    HasSubgaussianMGF (gaussianNoise m k i) v (gaussianPairLaw m v) := by
  show HasSubgaussianMGF (fun ω : (Fin m × ℕ) → ℝ => ω (k, i)) v (gaussianPairLaw m v)
  have hmap : (gaussianPairLaw m v).map (fun ω => ω (k, i)) = gaussianReal 0 v := by
    unfold gaussianPairLaw; exact Measure.infinitePi_map_eval _ (k, i)
  rw [← HasSubgaussianMGF.id_map_iff (measurable_pi_apply _).aemeasurable, hmap]
  exact gaussian_hasSubgaussianMGF v

/-- **Exact-recovery achievability bound for the independent Gaussian sequence family.**

With iid `N(0, v)` observations, signal margin `b > 0`, and `n ≥ 8 v log(m/δ) / b²` samples,
the coordinatewise threshold estimator recovers all `m` bits simultaneously with
probability at least `1 - δ`.  This is an upper bound of logarithmic order in the number
of bits; it is not a converse or an observational causal-DAG recovery theorem. -/
theorem exact_recovery_gaussian {m n : ℕ} (hn : 0 < n) (θ : Fin m → Bool)
    (b : ℝ) (hb : 0 < b) (v : ℝ≥0) (hv : 0 < v)
    (δ : ℝ) (hδ : 0 < δ)
    (hrate : (8 * (v : ℝ) * Real.log ((m : ℝ) / δ)) / b ^ 2 ≤ (n : ℝ)) :
    1 - δ ≤ (gaussianPairLaw m v).real
      {ω | ∀ k, estimator θ b (gaussianNoise m) n k ω = θ k} :=
  exact_recovery_upper_bound hn θ b hb v hv (gaussianNoise m)
    (gaussian_hindep m v) (gaussian_hsub m v) δ hδ hrate

end PairFamily
end RecoveryFormal
