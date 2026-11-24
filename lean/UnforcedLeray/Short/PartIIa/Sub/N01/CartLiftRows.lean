import UnforcedLeray.Short.PartIIa.Sub.N01.Defs
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.Proofs.CartLiftIsTest

/-!
# `PartII-a:N01/5`: the rows of the tensor lift (source lines 1647-1650)

`cartRowsC (cartLift ε⁻¹ c m) i` is a smooth `P`-periodic phase test (from `CartLiftIsTest`),
and the lifted tensor is symmetric because `nsSym` is symmetric and the frame conjugation
`F B Fᵀ` preserves symmetry.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa.N01

open UnforcedLeray.PhaseSpace
open UnforcedLeray.Short.PartIIIb.Concrete (Chart Ten3)
open UnforcedLeray.Short.PartIIIb.NearInst (tv4 cartLift nsSym cylFrame symRZ)

/-- `nsSym` is a symmetric matrix. -/
theorem nsSym_transpose (X : Ten3) : (nsSym X).transpose = nsSym X := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [nsSym, symRZ, Matrix.transpose_apply]

/-- The Cartesian lift is a symmetric matrix at every point. -/
theorem cartLift_transpose (R c : ℝ) (m : Chart → Ten3) (τ : ℝ) (z : UnforcedLeray.Space) :
    (cartLift R c m τ z).transpose = cartLift R c m τ z := by
  unfold cartLift
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.transpose_smul, nsSym_transpose, ← Matrix.mul_assoc]

theorem cartLiftRows : CartLiftRows := by
  intro ε c P hε hc hP m hm
  have hT := UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.cartLiftIsTest
    ε c P hε hc hP m hm
  have hsym : ∀ (τ : ℝ) (z : UnforcedLeray.Space),
      (cartLift ε⁻¹ c m τ z).transpose = cartLift ε⁻¹ c m τ z :=
    fun τ z => cartLift_transpose ε⁻¹ c m τ z
  generalize cartLift ε⁻¹ c m = T at hT hsym
  have hphase : ∀ i, IsPhaseTest P (cartRowsC T i) := by
    intro i
    refine ⟨?_, ?_, ?_⟩
    · apply PiLp.contDiff_toLp.comp
      apply contDiff_pi.2
      intro j
      have hf : ContDiff ℝ ∞ (fun x : ℝ × UnforcedLeray.Space => T x.1 x.2 i j) :=
        (hT.smooth i j).comp (contDiff_snd.prodMk contDiff_fst)
      exact Complex.ofRealCLM.contDiff.comp hf
    · intro τ y
      simp only [cartRowsC]
      rw [hT.periodic]
    · obtain ⟨r, hr⟩ := hT.bounded
      refine ⟨r, fun τ y hy => ?_⟩
      have h0 : T τ y = 0 := by
        by_contra hne
        exact absurd (hr τ y hne) (not_le.mpr hy)
      simp [cartRowsC, h0]
      rfl
  refine ⟨hphase, ?_⟩
  rintro i j ⟨τ, y⟩
  have hs := congrFun (congrFun (hsym τ y) i) j
  simp only [Matrix.transpose_apply] at hs
  simp only [cartRowsC, PiLp.toLp_apply]
  rw [hs]

end UnforcedLeray.Short.PartIIa.N01
