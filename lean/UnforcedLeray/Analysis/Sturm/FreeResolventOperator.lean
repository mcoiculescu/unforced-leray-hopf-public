import UnforcedLeray.Analysis.Sturm.FreeResolventEnergy
import UnforcedLeray.Analysis.Sturm.FreeResolventSymmetry
import UnforcedLeray.Analysis.Sturm.CompactL2
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# The free Green resolvent as an actual bounded L² operator

The operator is the unique continuous extension from the dense submodule of
compactly supported L² data of the explicit exponential-kernel convolution.
Its norm estimate is proved from that convolution's actual energy identity.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ComplexConjugate InnerProductSpace
namespace UnforcedLeray.Sturm
open NonUniqueEuler.Sob

variable {L : ℝ} (hL : 0 < L)
include hL

theorem freeResolvent_memLp_compact (f : compactL2) :
    MemLp (freeResolvent L (f : ComplexL2)) 2 volume := by
  obtain ⟨a, b, hab⟩ := CompactL2.exists_interval f
  exact memLp_freeResolvent hL (CompactL2.integrable f) hab

def freeResolventCompact (f : compactL2) : ComplexL2 :=
  (freeResolvent_memLp_compact hL f).toLp (freeResolvent L (f : ComplexL2))

theorem coeFn_freeResolventCompact (f : compactL2) :
    freeResolventCompact hL f =ᵐ[volume] freeResolvent L (f : ComplexL2) :=
  (freeResolvent_memLp_compact hL f).coeFn_toLp

/-- The actual exponential-kernel convolution on a dense linear domain. -/
def freeResolventCompactLinear : compactL2 →ₗ[ℂ] ComplexL2 where
  toFun := freeResolventCompact hL
  map_add' f g := by
    apply Lp.ext
    have hraw := freeResolvent_congr_ae L (Lp.coeFn_add (f : ComplexL2) (g : ComplexL2))
    rw [freeResolvent_add hL (CompactL2.integrable f) (CompactL2.integrable g)] at hraw
    filter_upwards [coeFn_freeResolventCompact hL (f + g),
      coeFn_freeResolventCompact hL f, coeFn_freeResolventCompact hL g,
      Lp.coeFn_add (freeResolventCompact hL f) (freeResolventCompact hL g)] with x hfg hf hg hsum
    rw [hfg]
    change freeResolvent L (⇑((f : ComplexL2) + (g : ComplexL2))) x = _
    rw [congrFun hraw x, hsum]
    simp only [Pi.add_apply, hf, hg]
  map_smul' c f := by
    apply Lp.ext
    have hraw := freeResolvent_congr_ae L (Lp.coeFn_smul c (f : ComplexL2))
    rw [freeResolvent_smul] at hraw
    filter_upwards [coeFn_freeResolventCompact hL (c • f),
      coeFn_freeResolventCompact hL f, Lp.coeFn_smul c (freeResolventCompact hL f)] with x hcf hf hout
    simp only [RingHom.id_apply]
    rw [hcf]
    change freeResolvent L (⇑(c • (f : ComplexL2))) x = _
    rw [congrFun hraw x, hout]
    simp only [Pi.smul_apply, hf]

theorem norm_freeResolventCompact_le (f : compactL2) :
    ‖freeResolventCompact hL f‖ ≤ (L ^ 2)⁻¹ * ‖(f : ComplexL2)‖ := by
  obtain ⟨a, b, hab⟩ := CompactL2.exists_interval f
  have h := l2_freeResolvent_le hL (Lp.memLp (f : ComplexL2)) hab
  unfold freeResolventCompact
  rw [Lp.norm_toLp, Lp.norm_def]
  exact h

/-- The bounded extension of the actual positive free Green resolvent. -/
def freeResolventOperator : ComplexL2 →L[ℂ] ComplexL2 :=
  (freeResolventCompactLinear hL).extendOfNorm compactL2.subtype

theorem freeResolventOperator_on_compact (f : compactL2) :
    freeResolventOperator hL (f : ComplexL2) = freeResolventCompact hL f :=
  LinearMap.extendOfNorm_eq denseRange_compactL2_subtypeL
    ⟨(L ^ 2)⁻¹, norm_freeResolventCompact_le hL⟩ f

theorem coeFn_freeResolventOperator_on_compact (f : compactL2) :
    freeResolventOperator hL (f : ComplexL2) =ᵐ[volume] freeResolvent L (f : ComplexL2) := by
  rw [freeResolventOperator_on_compact]
  exact coeFn_freeResolventCompact hL f

theorem norm_freeResolventOperator_apply_le (f : ComplexL2) :
    ‖freeResolventOperator hL f‖ ≤ (L ^ 2)⁻¹ * ‖f‖ :=
  LinearMap.norm_extendOfNorm_apply_le denseRange_compactL2_subtypeL _
    (norm_freeResolventCompact_le hL) f

theorem norm_freeResolventOperator_le : ‖freeResolventOperator hL‖ ≤ (L ^ 2)⁻¹ :=
  (freeResolventOperator hL).opNorm_le_bound (by positivity)
    (norm_freeResolventOperator_apply_le hL)

end UnforcedLeray.Sturm
