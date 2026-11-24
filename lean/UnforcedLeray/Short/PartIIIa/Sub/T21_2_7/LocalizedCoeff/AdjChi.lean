import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_1_7_4
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.LocalizedCoeff.WeakMeas
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.LocalizedCoeff.FieldBound
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.KernelAdjoint

/-!
# `PartIII-a:T21/2/7/1/7/4/3`: the kernel adjoint of `w ∇E(r)` (`locAdjChi`)

Source: `the November 2 reference manuscript` lines 3052-3058.
`KernelAdjointBound` applied to `F_j = w ∂_jE(r)` (`locFieldBound`, which needs `8 < m`, so
`1 < m` for the kernel bound) gives `χ` with `h1Norm ≤ C_K ∑_j (‖F_j‖₁ + ‖F_j‖₂)`. Then
`xNorm ≤ h1Norm` puts `χ` in `L²(cellMeasure)` (measurability from `locWeakMeas`), and the
identity transfers from `χ` to its `Lp` representative by `ae` equality.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

namespace AdjChiAux

theorem xNorm_le_h1Norm (c m : ℝ) (φ : ℝ × ℝ → ℂ) (g : Fin 2 → ℝ × ℝ → ℂ) :
    xNorm c (-m) φ ≤ h1Norm c m φ g := by
  unfold h1Norm
  calc xNorm c (-m) φ = (xNorm c (-m) φ ^ 2) ^ (1 / 2 : ℝ) := by
        rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num
    _ ≤ _ := ENNReal.rpow_le_rpow (le_self_add) (by norm_num)

end AdjChiAux

open AdjChiAux in
/-- **(L2') Kernel adjoint of `w ∇E(r)`** (SP 3052-3058): the kernel adjoint is an element of
`X_{-m,c}` with norm bounded by `β₀ ‖w‖`, characterised by the cylinder/kernel identity. -/
theorem locAdjChi (m : ℝ) (hm : 8 < m) : LocAdjChi m := by
  intro ν hν hν1 tr T C hT hb
  have hc1 : 1 ≤ (ν ^ (-2 : ℝ)) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hν hν1 (by norm_num)
  obtain ⟨C', hC', hF⟩ := locFieldBound m hm ν hν hν1 tr T C hT hb
  obtain ⟨CK, hCK, hK⟩ := kernelAdjointBound m (by linarith)
  refine ⟨2 * CK * C', by positivity, ?_⟩
  intro r hr w
  -- the fields `F_j = w ∂_jE(r)`
  have hint : ∀ j : Fin 2, IntegrableOn (fun x => w x * ((B0579.pd j (UnforcedLeray.B0238.Ec tr r) x : ℝ) : ℂ))
      (B0579.cell (ν ^ (-2 : ℝ))) ∧
      MemLp (fun x => w x * ((B0579.pd j (UnforcedLeray.B0238.Ec tr r) x : ℝ) : ℂ)) 2
        (volume.restrict (B0579.cell (ν ^ (-2 : ℝ)))) :=
    fun j => ⟨(hF r hr w j).1, (hF r hr w j).2.1⟩
  obtain ⟨χ, gχ, hweak, hh1, hid⟩ := hK (ν ^ (-2 : ℝ)) hc1
    (fun j x => w x * ((B0579.pd j (UnforcedLeray.B0238.Ec tr r) x : ℝ) : ℂ)) hint
  -- the `L²` bound of `χ`
  have hβ : ENNReal.ofReal (2 * CK * C') = ENNReal.ofReal CK * (2 * ENNReal.ofReal C') := by
    rw [show (2 : ℝ) * CK * C' = CK * (2 * C') by ring, ENNReal.ofReal_mul hCK,
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
  have hsum : ∑ j : Fin 2, (eLpNorm (fun x => w x * ((B0579.pd j (UnforcedLeray.B0238.Ec tr r) x : ℝ) : ℂ)) 1
        (volume.restrict (B0579.cell (ν ^ (-2 : ℝ)))) +
      eLpNorm (fun x => w x * ((B0579.pd j (UnforcedLeray.B0238.Ec tr r) x : ℝ) : ℂ)) 2
        (volume.restrict (B0579.cell (ν ^ (-2 : ℝ))))) ≤
      2 * (ENNReal.ofReal C' * ‖w‖ₑ) := by
    rw [Fin.sum_univ_two, two_mul]
    exact add_le_add (hF r hr w 0).2.2 (hF r hr w 1).2.2
  have hwn : ‖w‖ₑ = eLpNorm w 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) := Lp.enorm_def w
  have hmainE : eLpNorm χ 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) ≤
      ENNReal.ofReal (2 * CK * C') * ‖w‖ₑ := by
    calc eLpNorm χ 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m))
        = xNorm (ν ^ (-2 : ℝ)) (-m) χ := rfl
      _ ≤ h1Norm (ν ^ (-2 : ℝ)) m χ gχ := AdjChiAux.xNorm_le_h1Norm _ _ _ _
      _ ≤ ENNReal.ofReal CK * ∑ j : Fin 2, (eLpNorm (fun x => w x * ((B0579.pd j (UnforcedLeray.B0238.Ec tr r) x : ℝ) : ℂ)) 1
            (volume.restrict (B0579.cell (ν ^ (-2 : ℝ)))) +
          eLpNorm (fun x => w x * ((B0579.pd j (UnforcedLeray.B0238.Ec tr r) x : ℝ) : ℂ)) 2
            (volume.restrict (B0579.cell (ν ^ (-2 : ℝ))))) := hh1
      _ ≤ ENNReal.ofReal CK * (2 * (ENNReal.ofReal C' * ‖w‖ₑ)) := by gcongr
      _ = ENNReal.ofReal (2 * CK * C') * ‖w‖ₑ := by rw [hβ]; ring
  -- measurability and membership in `X_{-m,c}`
  have hmeas0 : AEStronglyMeasurable χ (volume.restrict (B0579.cell (ν ^ (-2 : ℝ)))) :=
    locWeakMeas (ν ^ (-2 : ℝ)) hc1 0 χ (gχ 0) (hweak 0)
  have hmeas : AEStronglyMeasurable χ (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) :=
    hmeas0.mono_ac (B0579.cellMeasure_ac (ν ^ (-2 : ℝ)) (-m))
  have hwtop : ‖w‖ₑ ≠ ⊤ := by
    rw [hwn]; exact (Lp.memLp w).eLpNorm_lt_top.ne
  have hfin : eLpNorm χ 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) < ⊤ :=
    lt_of_le_of_lt hmainE (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (lt_top_iff_ne_top.2 hwtop))
  have hmem : MemLp χ 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) := ⟨hmeas, hfin⟩
  have hae : ∀ᵐ x ∂(volume.restrict (B0579.cell (ν ^ (-2 : ℝ)))),
      (hmem.toLp χ : ℝ × ℝ → ℂ) x = χ x :=
    (B0579.ac_cellMeasure (ν ^ (-2 : ℝ)) (-m)).ae_le (MemLp.coeFn_toLp hmem)
  refine ⟨hmem.toLp χ, ?_, ?_⟩
  · -- the norm bound
    have hrhs : ENNReal.ofReal (2 * CK * C') * ‖w‖ₑ ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hwtop
    have h1 := ENNReal.toReal_mono hrhs hmainE
    rw [Lp.norm_toLp χ hmem]
    calc (eLpNorm χ 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m))).toReal
        ≤ (ENNReal.ofReal (2 * CK * C') * ‖w‖ₑ).toReal := h1
      _ = 2 * CK * C' * ‖w‖ := by
          rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), hwn, Lp.norm_def w]
  · intro ψ uψ hψ hu
    calc ∫ x in B0579.cell (ν ^ (-2 : ℝ)), (hmem.toLp χ : ℝ × ℝ → ℂ) x * (ψ x : ℂ)
        = ∫ x in B0579.cell (ν ^ (-2 : ℝ)), χ x * (ψ x : ℂ) :=
          integral_congr_ae (hae.mono fun x hx => by simp only [hx])
      _ = ∫ y in B0579.cell (ν ^ (-2 : ℝ)), ∑ j : Fin 2,
            (w y * ((B0579.pd j (UnforcedLeray.B0238.Ec tr r) y : ℝ) : ℂ)) * ((uψ y j : ℝ) : ℂ) :=
          hid ψ uψ hψ hu
      _ = ∫ x in B0579.cell (ν ^ (-2 : ℝ)), w x *
            ((uψ x 0 * B0579.pd 0 (UnforcedLeray.B0238.Ec tr r) x +
              uψ x 1 * B0579.pd 1 (UnforcedLeray.B0238.Ec tr r) x : ℝ) : ℂ) := by
          congr 1
          funext x
          simp only [Fin.sum_univ_two]
          push_cast
          ring

end UnforcedLeray.Short.IIIa
