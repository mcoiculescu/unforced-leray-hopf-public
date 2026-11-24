/-
Cauchy--Schwarz proof adapted from OpenAI's NavierStokesAndEuler,
Euler/WholeSpaceGaussian.lean at f9e8bc5b38b6e212696e8a30e3e91517af887bbd,
Apache-2.0. Changes: imports, namespace, general L² norm identification,
standard heat scaling and the ordinary x-y convolution convention.
-/
import UnforcedLeray.Analysis.Heat.KernelNorm
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Group.Integral

/-! Actual pointwise convergence and L²-to-uniform heat smoothing on R³. -/
noncomputable section
namespace UnforcedLeray.Heat
open MeasureTheory Filter
open scoped ENNReal
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Cauchy--Schwarz for scalar multiplication, in a form that retains the
ordinary L² norm of a Banach-valued field. -/
theorem norm_integral_smul_le (k : Space → ℝ) (f : Space → V)
    (hk : MemLp k 2 volume) (hf : MemLp f 2 volume) :
    ‖∫ x : Space, k x • f x‖ ≤
      Real.sqrt (∫ x : Space, ‖k x‖^2) * (eLpNorm f 2 volume).toReal := by
  have hp : (2:ℝ).HolderConjugate 2 := by norm_num [Real.holderConjugate_iff]
  have hk' : MemLp (fun x => ‖k x‖) (ENNReal.ofReal (2:ℝ)) volume := by simpa using hk.norm
  have hf' : MemLp (fun x => ‖f x‖) (ENNReal.ofReal (2:ℝ)) volume := by simpa using hf.norm
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg hp
    (Eventually.of_forall (fun x => norm_nonneg (k x)))
    (Eventually.of_forall (fun x => norm_nonneg (f x))) hk' hf'
  have hnorm : (∫ x : Space, ‖k x‖*‖f x‖) ≤
      Real.sqrt (∫ x : Space, ‖k x‖^2) * Real.sqrt (∫ x : Space, ‖f x‖^2) := by
    simpa only [Real.rpow_two, Real.sqrt_eq_rpow] using h
  have he : Real.sqrt (∫ x : Space, ‖f x‖^2) = (eLpNorm f 2 volume).toReal := by
    exact (Gaussian.eLpNorm_two_toReal_eq_sqrt hf).symm
  rw [he] at hnorm
  exact (norm_integral_le_integral_norm _).trans (by simpa only [norm_smul] using hnorm)


/-- The actual Bochner heat integral, using the standard viscosity-one kernel. -/
def average (t : ℝ) (f : Space → V) (x : Space) : V :=
  ∫ y : Space, kernel t y • f (x-y)

/-- Every pointwise heat integral converges for an L² input at positive time. -/
theorem average_integrable {t : ℝ} (ht : 0 < t) {f : Space → V}
    (hf : MemLp f 2 volume) (x : Space) :
    Integrable (fun y : Space => kernel t y • f (x-y)) := by
  have hs := hf.comp_measurePreserving (Measure.measurePreserving_sub_left (volume : Measure Space) x)
  have hm : MemLp (fun y : Space => kernel t y • f (x-y)) 1 volume :=
    hs.smul (kernel_memLp_two ht)
  exact memLp_one_iff_integrable.mp hm

/-- The exact Gaussian factor in whole-space L²-to-pointwise smoothing. -/
theorem average_norm_le_L2 {t : ℝ} (ht : 0 < t) (f : Space → V)
    (hf : MemLp f 2 volume) (x : Space) :
    ‖average t f x‖ ≤ (8 * Real.pi * t) ^ (-(3 : ℝ) / 4) *
      (eLpNorm f 2 volume).toReal := by
  have hmp := Measure.measurePreserving_sub_left (volume : Measure Space) x
  have hs : MemLp (fun y : Space => f (x-y)) 2 volume := hf.comp_measurePreserving hmp
  have he : eLpNorm (fun y : Space => f (x-y)) 2 volume = eLpNorm f 2 volume :=
    eLpNorm_comp_measurePreserving hf.aestronglyMeasurable hmp
  have h := norm_integral_smul_le (kernel t) (fun y : Space => f (x-y))
    (kernel_memLp_two ht) hs
  rw [he, ← Gaussian.eLpNorm_two_toReal_eq_sqrt (kernel_memLp_two ht),
    eLpNorm_kernel_toReal ht] at h
  exact h

/-- Null-set changes of an input give equal heat averages at every spatial point. -/
theorem average_congr_ae {f g : Space → V} (hfg : f =ᵐ[volume] g) (t : ℝ) :
    average t f = average t g := by
  funext x
  apply integral_congr_ae
  have he := (Measure.measurePreserving_sub_left (volume : Measure Space) x).quasiMeasurePreserving.ae_eq_comp hfg
  filter_upwards [he] with y hy
  exact congrArg (fun v : V => kernel t y • v) hy

/-- Actual additivity follows from pointwise integrability, not from totalized defaults. -/
theorem average_add {t : ℝ} (ht : 0 < t) {f g : Space → V}
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    average t (f + g) = average t f + average t g := by
  funext x
  simp only [average, Pi.add_apply, smul_add]
  exact integral_add (average_integrable ht hf x) (average_integrable ht hg x)

theorem average_smul (t a : ℝ) (f : Space → V) :
    average t (a • f) = a • average t f := by
  funext x
  simp only [average, Pi.smul_apply, smul_comm (kernel t _) a]
  exact integral_smul a _

end UnforcedLeray.Heat
