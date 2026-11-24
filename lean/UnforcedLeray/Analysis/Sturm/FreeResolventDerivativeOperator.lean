import UnforcedLeray.Analysis.Sturm.FreeResolventEnergy
import UnforcedLeray.Analysis.Sturm.CompactL2
import Mathlib.Analysis.Normed.Operator.Extend

/-!
# The actual first-derivative Green operator on L²

The derivative of convolution with `exp(-L|x|)/(2L)` is first constructed on
the dense submodule of compactly supported L² inputs. The actual Green-kernel
energy identity gives its support-independent norm bound. Its unique bounded
extension retains the exact dense-domain formula. Identifying its values as
weak derivatives for arbitrary L² inputs is a separate closed-graph argument.
-/

noncomputable section
open MeasureTheory Set Filter
namespace UnforcedLeray.Sturm
open NonUniqueEuler.Sob NonUniqueEuler.Sob.EnergyAux

/-- The explicit derivative convolution is independent of representatives. -/
theorem freeResolventDeriv_congr_ae (L : ℝ) {f g : ℝ → ℂ}
    (h : f =ᵐ[volume] g) : freeResolventDeriv L f = freeResolventDeriv L g := by
  funext x
  unfold freeResolventDeriv psi1
  congr 1
  apply integral_congr_ae
  exact h.mono fun y hy => by simp only [hy]

theorem freeResolventDeriv_add {L : ℝ} (hL : 0 < L) {f g : ℝ → ℂ}
    (hf : Integrable f) (hg : Integrable g) :
    freeResolventDeriv L (f + g) = freeResolventDeriv L f + freeResolventDeriv L g := by
  have hint (k : ℝ → ℂ) (hk : Integrable k) (x : ℝ) :
      Integrable (fun y => (k1 L (x - y) : ℂ) * k y) :=
    integrable_ofReal_mul ((measurable_k1 L).comp (measurable_const.sub measurable_id))
      (fun _ => abs_k1_le_one hL.le _) hk
  funext x
  simp only [freeResolventDeriv, psi1, Pi.add_apply, mul_add]
  rw [integral_add (hint f hf x) (hint g hg x)]
  ring

theorem freeResolventDeriv_smul (L : ℝ) (c : ℂ) (f : ℝ → ℂ) :
    freeResolventDeriv L (c • f) = c • freeResolventDeriv L f := by
  funext x
  simp only [freeResolventDeriv, psi1, Pi.smul_apply, smul_eq_mul]
  have h : (fun y => (k1 L (x - y) : ℂ) * (c * f y)) =
      fun y => c * ((k1 L (x - y) : ℂ) * f y) := by
    funext y
    ring
  rw [h, integral_const_mul]
  ring

section Energy
variable {L : ℝ} (hL : 0 < L) {f : ℝ → ℂ} (hf2 : MemLp f 2 volume)
  {a b : ℝ} (hfab : ∀ᵐ x, x ∉ Icc a b → f x = 0)
include hL hf2 hfab

/-- The derivative estimate follows from the actual elliptic energy identity. -/
theorem freeResolventDeriv_integral_sq_bound :
    L ^ 2 * (∫ x, ‖freeResolventDeriv L f x‖ ^ 2) ≤ ∫ x, ‖f x‖ ^ 2 := by
  rw [freeResolvent_energy_integral hL hf2 hfab]
  have hu : 0 ≤ ∫ x, ‖freeResolvent L f x‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hd : 0 ≤ ∫ x, ‖freeResolventDeriv L f x‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hs : 0 ≤ ∫ x, ‖freeResolventSecond L f x‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hdu : 0 ≤ L ^ 2 * (∫ x, ‖freeResolventDeriv L f x‖ ^ 2) :=
    mul_nonneg (sq_nonneg _) hd
  have huu : 0 ≤ L ^ 4 * (∫ x, ‖freeResolvent L f x‖ ^ 2) :=
    mul_nonneg (by positivity) hu
  linarith

/-- A support-independent bound on the actual first derivative of the Green convolution. -/
theorem l2_freeResolventDeriv_le : l2 (freeResolventDeriv L f) ≤ L⁻¹ * l2 f := by
  have hf := integrable_of_memLp_two hf2 hfab
  have hd := memLp_freeResolventDeriv hL hf hfab
  have hbound := freeResolventDeriv_integral_sq_bound hL hf2 hfab
  rw [← l2_sq_eq_integral hd, ← l2_sq_eq_integral hf2] at hbound
  have hfn : 0 ≤ l2 f := ENNReal.toReal_nonneg
  have hdn : 0 ≤ l2 (freeResolventDeriv L f) := ENNReal.toReal_nonneg
  have hs : L * l2 (freeResolventDeriv L f) ≤ l2 f := by
    nlinarith [sq_nonneg (L * l2 (freeResolventDeriv L f) + l2 f)]
  exact (le_inv_mul_iff₀ hL).mpr hs

end Energy

variable {L : ℝ} (hL : 0 < L)
include hL

theorem freeResolventDeriv_memLp_compact (f : compactL2) :
    MemLp (freeResolventDeriv L (f : ComplexL2)) 2 volume := by
  obtain ⟨a, b, hab⟩ := CompactL2.exists_interval f
  exact memLp_freeResolventDeriv hL (CompactL2.integrable f) hab

def freeResolventDerivCompact (f : compactL2) : ComplexL2 :=
  (freeResolventDeriv_memLp_compact hL f).toLp (freeResolventDeriv L (f : ComplexL2))

theorem coeFn_freeResolventDerivCompact (f : compactL2) :
    freeResolventDerivCompact hL f =ᵐ[volume] freeResolventDeriv L (f : ComplexL2) :=
  (freeResolventDeriv_memLp_compact hL f).coeFn_toLp

/-- The derivative convolution on the actual dense compact-support domain. -/
def freeResolventDerivCompactLinear : compactL2 →ₗ[ℂ] ComplexL2 where
  toFun := freeResolventDerivCompact hL
  map_add' f g := by
    apply Lp.ext
    have hraw := freeResolventDeriv_congr_ae L (Lp.coeFn_add (f : ComplexL2) (g : ComplexL2))
    rw [freeResolventDeriv_add hL (CompactL2.integrable f) (CompactL2.integrable g)] at hraw
    filter_upwards [coeFn_freeResolventDerivCompact hL (f + g),
      coeFn_freeResolventDerivCompact hL f, coeFn_freeResolventDerivCompact hL g,
      Lp.coeFn_add (freeResolventDerivCompact hL f) (freeResolventDerivCompact hL g)]
      with x hfg hf hg hsum
    simp only [Submodule.coe_add] at hfg
    rw [hfg, congrFun hraw x, hsum]
    simp only [Pi.add_apply, hf, hg]
  map_smul' c f := by
    apply Lp.ext
    have hraw := freeResolventDeriv_congr_ae L (Lp.coeFn_smul c (f : ComplexL2))
    rw [freeResolventDeriv_smul] at hraw
    filter_upwards [coeFn_freeResolventDerivCompact hL (c • f),
      coeFn_freeResolventDerivCompact hL f, Lp.coeFn_smul c (freeResolventDerivCompact hL f)]
      with x hcf hf hout
    simp only [RingHom.id_apply]
    simp only [Submodule.coe_smul] at hcf
    rw [hcf, congrFun hraw x, hout]
    simp only [Pi.smul_apply, hf]

theorem norm_freeResolventDerivCompact_le (f : compactL2) :
    ‖freeResolventDerivCompact hL f‖ ≤ L⁻¹ * ‖(f : ComplexL2)‖ := by
  obtain ⟨a, b, hab⟩ := CompactL2.exists_interval f
  have h := l2_freeResolventDeriv_le hL (Lp.memLp (f : ComplexL2)) hab
  unfold freeResolventDerivCompact
  rw [Lp.norm_toLp, Lp.norm_def]
  exact h

/-- The bounded extension of the actual first derivative of the free Green resolvent. -/
def freeResolventDerivativeOperator : ComplexL2 →L[ℂ] ComplexL2 :=
  (freeResolventDerivCompactLinear hL).extendOfNorm compactL2.subtype

theorem freeResolventDerivativeOperator_on_compact (f : compactL2) :
    freeResolventDerivativeOperator hL (f : ComplexL2) = freeResolventDerivCompact hL f :=
  LinearMap.extendOfNorm_eq denseRange_compactL2_subtypeL
    ⟨L⁻¹, norm_freeResolventDerivCompact_le hL⟩ f

theorem coeFn_freeResolventDerivativeOperator_on_compact (f : compactL2) :
    freeResolventDerivativeOperator hL (f : ComplexL2) =ᵐ[volume]
      freeResolventDeriv L (f : ComplexL2) := by
  rw [freeResolventDerivativeOperator_on_compact]
  exact coeFn_freeResolventDerivCompact hL f

theorem norm_freeResolventDerivativeOperator_apply_le (f : ComplexL2) :
    ‖freeResolventDerivativeOperator hL f‖ ≤ L⁻¹ * ‖f‖ :=
  LinearMap.norm_extendOfNorm_apply_le denseRange_compactL2_subtypeL _
    (norm_freeResolventDerivCompact_le hL) f

theorem norm_freeResolventDerivativeOperator_le : ‖freeResolventDerivativeOperator hL‖ ≤ L⁻¹ :=
  (freeResolventDerivativeOperator hL).opNorm_le_bound (by positivity)
    (norm_freeResolventDerivativeOperator_apply_le hL)

end UnforcedLeray.Sturm
