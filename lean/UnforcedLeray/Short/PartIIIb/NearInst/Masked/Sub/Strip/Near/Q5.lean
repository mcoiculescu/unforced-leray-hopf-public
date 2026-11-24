import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.Strip.Near.Q5a
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.Strip.Near.Q5b

/-!
# `PartIII-b:C/near/masked/22/2/5`: `NearYoung` from `sep:young` (source 4000-4003)

Route. Take the constant `C` of `nearYoungLtau` (Q5a). The receiver restriction to
`{R/√r < hRad y}` is harmless because `nearM` vanishes off that set. Then `ltauLq_two_eq`
(Q5b) converts both `L²_τ L²_y` integrals into `P`-multiples of squared `ltauLq`, and the
Q5a bound `ltauLq P 2 nearM ≤ C (√r/R) ltauLq P 2 srcNorm` squares to
`C² (r/R²) ∫∫ srcNorm²`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Short.PartIIIb.NearInst.Delta
  UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Blueprint.Planar

theorem nearYoung_holds : NearYoung := by
  intro hY Kset hKc hKs δ hδ
  obtain ⟨C, hC0, hC⟩ := nearYoungLtau hY Kset hKc hKs δ hδ
  refine ⟨C, hC0, ?_⟩
  intro R c ν μ l r g hR hc hν hμ hl hlr hrl hg hsupp
  have hr : 0 < r := hl.trans hlr
  have hP : 0 < 2 * c / R := by positivity
  have hQ := hC R c ν μ l r g hR hc hν hμ hl hlr hrl hg hsupp
  -- nearM vanishes off the receiver set, so the restricted integral is the full one
  have hinner : ∀ τ : ℝ,
      ∫⁻ y in {y : UnforcedLeray.Space | R / Real.sqrt r < hRad y},
          nearM ν μ R c r g τ y ^ (2 : ℝ) =
        ∫⁻ y : UnforcedLeray.Space, nearM ν μ R c r g τ y ^ (2 : ℝ) := by
    intro τ
    apply setLIntegral_eq_of_support_subset
    intro y hy
    rw [Function.mem_support] at hy
    by_contra hn
    have hn' : ¬ (R / Real.sqrt r < hRad y) := hn
    apply hy
    have h0 : nearM ν μ R c r g τ y = 0 := by
      unfold nearM
      rw [if_neg hn']
    rw [h0]
    exact ENNReal.zero_rpow_of_pos (by norm_num)
  simp only [hinner]
  have hQb : ENNReal.ofReal (2 * c / R) *
      UnforcedLeray.Short.IIIa.ltauLq (2 * c / R) 2 (nearM ν μ R c r g) ^ (2 : ℝ) =
      ∫⁻ τ in Ico (0 : ℝ) (2 * c / R),
        ∫⁻ y : UnforcedLeray.Space, nearM ν μ R c r g τ y ^ (2 : ℝ) :=
    ltauLq_two_eq _ hP _
  have hQs : ENNReal.ofReal (2 * c / R) *
      UnforcedLeray.Short.IIIa.ltauLq (2 * c / R) 2
        (UnforcedLeray.Short.IIIa.srcNorm (NearInst.cartLift R c g)) ^ (2 : ℝ) =
      ∫⁻ τ in Ico (0 : ℝ) (2 * c / R),
        ∫⁻ z : UnforcedLeray.Space,
          UnforcedLeray.Short.IIIa.srcNorm (NearInst.cartLift R c g) τ z ^ (2 : ℝ) :=
    ltauLq_two_eq _ hP _
  have hA0 : 0 ≤ C * (Real.sqrt r / R) :=
    mul_nonneg hC0 (div_nonneg (Real.sqrt_nonneg _) hR.le)
  have hA : ENNReal.ofReal (C * (Real.sqrt r / R)) ^ (2 : ℝ) =
      ENNReal.ofReal (C ^ 2 * (r / R ^ 2)) := by
    rw [ENNReal.ofReal_rpow_of_nonneg hA0 (by norm_num), Real.rpow_two]
    congr 1
    rw [mul_pow, div_pow, Real.sq_sqrt hr.le]
  rw [← hQb, ← hQs]
  calc ENNReal.ofReal (2 * c / R) *
          UnforcedLeray.Short.IIIa.ltauLq (2 * c / R) 2 (nearM ν μ R c r g) ^ (2 : ℝ)
      ≤ ENNReal.ofReal (2 * c / R) *
          (ENNReal.ofReal (C * (Real.sqrt r / R)) *
            UnforcedLeray.Short.IIIa.ltauLq (2 * c / R) 2
              (UnforcedLeray.Short.IIIa.srcNorm (NearInst.cartLift R c g))) ^ (2 : ℝ) :=
        mul_le_mul_of_nonneg_left (ENNReal.rpow_le_rpow hQ (by norm_num)) (by positivity)
    _ = ENNReal.ofReal (C ^ 2 * (r / R ^ 2)) *
          (ENNReal.ofReal (2 * c / R) *
            UnforcedLeray.Short.IIIa.ltauLq (2 * c / R) 2
              (UnforcedLeray.Short.IIIa.srcNorm (NearInst.cartLift R c g)) ^ (2 : ℝ)) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2), ← hA]
        ring

end UnforcedLeray.Short.PartIIIb.NearInst.Masked
