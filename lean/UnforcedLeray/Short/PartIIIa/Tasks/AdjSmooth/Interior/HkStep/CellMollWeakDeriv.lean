import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.HkStep.Shared
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.CellConvDeriv
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.CellPeriodize

/-!
# `PartIII-a:T21/2/7/2/1/1/5/12`: mollification commutes with periodic weak derivatives

Source of record: `the November 2 reference manuscript` (SP), lines 3060-3061.
For `g = ∂_j f` weakly on the cylinder, `∂_j (ρ_n ⋆ f) = ρ_n ⋆ g` everywhere. Proof at `x`: with
the centred kernel `K_x(z) = ρ_n(x - z)`, the derivative falls on the kernel, the kernel is moved
to `z` by the substitution `y = x - z`, `∂_j K_x = -(∂_j ρ_n)(x - ·)`, the plane pairing with
`∂_j K_x` is the cell pairing with the periodization `∂_j (perKer c K_x)` (`CellPeriodize`), the
weak derivative identity is applied to that cylinder test, and the pairing with `K_x` is returned
by `CellPeriodize` once more.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- The mollifier `ρ_n` is smooth. -/
theorem molKer_contDiff_cmw (n : ℕ) : ContDiff ℝ ∞ (molKer n) :=
  (molBump n).contDiff_normed

/-- The mollifier `ρ_n` has compact support. -/
theorem molKer_hasCompactSupport_cmw (n : ℕ) : HasCompactSupport (molKer n) :=
  (molBump n).hasCompactSupport_normed

/-- Substitution `y = x - z` in the convolution: `(K ⋆ h)(x) = ∫ K(x - z) h(z) dz`. -/
theorem cellConv_eq_sub_cmw (K : ℝ × ℝ → ℝ) (h : ℝ × ℝ → ℂ) (x : ℝ × ℝ) :
    cellConv K h x = ∫ z, K (x - z) • h z := by
  unfold cellConv
  have := integral_sub_left_eq_self (fun y : ℝ × ℝ => K y • h (x - y)) volume x
  simp only [sub_sub_cancel] at this
  exact this.symm

/-- The partial derivative of the reflected kernel: `∂_j (w ↦ K(x - w))(z) = -(∂_j K)(x - z)`. -/
theorem pd_neg_comp_sub_cmw (K : ℝ × ℝ → ℝ) (hK : Differentiable ℝ K) (j : Fin 2) (x z : ℝ × ℝ) :
    B0579.pd j (fun w => K (x - w)) z = -(B0579.pd j K (x - z)) := by
  have h1 : HasFDerivAt (fun w : ℝ × ℝ => x - w) (-(ContinuousLinearMap.id ℝ (ℝ × ℝ))) z :=
    (hasFDerivAt_id z).const_sub x
  have h2 : HasFDerivAt (fun w => K (x - w))
      ((fderiv ℝ K (x - z)).comp (-(ContinuousLinearMap.id ℝ (ℝ × ℝ)))) z :=
    (hK (x - z)).hasFDerivAt.comp z h1
  unfold B0579.pd
  rw [h2.fderiv]
  simp

/-- The pairing step: for a smooth compactly supported real kernel `K`, a periodic `f` whose
weak cell derivative is `g`, the derivative of `K`-pairing of `f` is minus the `K`-pairing of `g`. -/
theorem cellMollWeakDeriv_pair (c m : ℝ) (j : Fin 2) (f g : ℝ × ℝ → ℂ) (K : ℝ × ℝ → ℝ)
    (hc : 0 < c) (hK : ContDiff ℝ ∞ K) (hKc : HasCompactSupport K)
    (hfper : ∀ x : ℝ × ℝ, f (x.1 + c, x.2) = f x)
    (hgper : ∀ x : ℝ × ℝ, g (x.1 + c, x.2) = g x)
    (hf : MemLp f 2 (B0579.cellMeasure c (-m)))
    (hg : MemLp g 2 (B0579.cellMeasure c (-m)))
    (hw2 : ∀ ψ : ℝ × ℝ → ℝ, B0579.IsCylTest c ψ →
      ∫ x in B0579.cell c, f x * (B0579.pd j ψ x : ℂ) =
        -∫ x in B0579.cell c, g x * (ψ x : ℂ)) :
    -∫ z, B0579.pd j K z • f z = ∫ z, K z • g z := by
  obtain ⟨hψ, hψd, hpK⟩ := cellPeriodize c m K hc hK hKc
  have hpdS : ContDiff ℝ ∞ (B0579.pd j K) := pd_contDiff_cellConvDeriv hK
  have hpdC : HasCompactSupport (B0579.pd j K) := pd_hasCompactSupport_cellConvDeriv hKc
  obtain ⟨-, -, hpD⟩ := cellPeriodize c m (B0579.pd j K) hc hpdS hpdC
  have hA : ∫ z, B0579.pd j K z • f z =
      ∫ z in B0579.cell c, B0579.pd j (perKer c K) z • f z := by
    rw [(hpD f hfper hf).2, hψd j]
  have hB : ∫ z in B0579.cell c, B0579.pd j (perKer c K) z • f z =
      ∫ z in B0579.cell c, f z * (B0579.pd j (perKer c K) z : ℂ) := by
    congr 1
    funext z
    rw [Complex.real_smul, mul_comm]
  have hC : ∫ z, K z • g z = ∫ z in B0579.cell c, g z * (perKer c K z : ℂ) := by
    rw [(hpK g hgper hg).2]
    congr 1
    funext z
    rw [Complex.real_smul, mul_comm]
  rw [hA, hB, hw2 (perKer c K) hψ, neg_neg, hC]

theorem cellMollWeakDeriv : UnforcedLeray.Short.IIIa.CellMollWeakDeriv := by
  intro c m j f g hc hfper hgper hf hg hw n
  funext x
  have hK : ContDiff ℝ ∞ (molKer n) := molKer_contDiff_cmw n
  have hKc : HasCompactSupport (molKer n) := molKer_hasCompactSupport_cmw n
  -- the derivative falls on the kernel (`CellConvDeriv` with `w = [j]`)
  have hD : pdCx j (cellMoll n f) = cellConv (B0579.pd j (molKer n)) f :=
    (cellConvDeriv c m (molKer n) f hc hK hKc hfper hf).2.2 [j]
  have hw2 : ∀ ψ : ℝ × ℝ → ℝ, B0579.IsCylTest c ψ →
      ∫ x in B0579.cell c, f x * (B0579.pd j ψ x : ℂ) =
        -∫ x in B0579.cell c, g x * (ψ x : ℂ) := by
    unfold HasWeakCellDerivC at hw
    exact hw.2
  -- the centred kernel `z ↦ ρ_n(x - z)`
  have hKxS : ContDiff ℝ ∞ (fun z : ℝ × ℝ => molKer n (x - z)) :=
    hK.comp (contDiff_const.sub contDiff_id)
  have hKxC : HasCompactSupport (fun z : ℝ × ℝ => molKer n (x - z)) :=
    hKc.comp_homeomorph (Homeomorph.subLeft x)
  have hP : -∫ z, B0579.pd j (fun w => molKer n (x - w)) z • f z =
      ∫ z, molKer n (x - z) • g z :=
    cellMollWeakDeriv_pair c m j f g (fun w => molKer n (x - w)) hc hKxS hKxC hfper hgper hf hg hw2
  have hL : cellConv (B0579.pd j (molKer n)) f x =
      -∫ z, B0579.pd j (fun w => molKer n (x - w)) z • f z := by
    rw [cellConv_eq_sub_cmw, ← integral_neg]
    congr 1
    funext z
    rw [pd_neg_comp_sub_cmw (molKer n) (hK.differentiable (by simp)) j x z, neg_smul, neg_neg]
  rw [congrFun hD x, hL, hP]
  exact (cellConv_eq_sub_cmw (molKer n) g x).symm

end UnforcedLeray.Short.IIIa
