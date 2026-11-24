import UnforcedLeray.Short.PartIIIa.Sub.T18_3_1_3_2_2.Props
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Existence.NiceForceSolution.LerayProjectSlices.P0DivFreeC
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.LionsMagenesCyl.MollLimit.AeGood

/-!
# Part III-a, `PartIII-a:T18/3/1/3/2/2/org`: `LMDerivRepAEH1` from the leaves

Source of record: `the November 2 reference manuscript` lines 3427-3440, 3541-3552.
Statements in `Sub/T18_3_1_3_2_2/Props.lean`. Here the weak derivative
`u'(s) = -(μ/s) u_k(s) + Yt(s)`, `Yt(s) = 𝒫₀ Z(s)` a.e., is assembled.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- `⟨w, f⟩ = ⟨χ, J_k f⟩` for `w = J_k 𝒫₀ χ` and `f` weakly divergence free (SP 3427-3440). -/
theorem lmSliceScalar (hA : LMP0CAdj) (hF : LMP0CFix) (hD : LMJWeakDiv)
    {c : ℝ} (hc : 0 < c) {J : ℕ → LMSpField → LMSpField} (hJ : IsLMMollifier c J)
    (hX : LMMollH1 c J) (k : ℕ) {χ f : LMSpField} (hχ : LMCellL2 c χ) (hf : LMCellL2 c f)
    (hfd : LMWeakDivFree c f) :
    LMIp c (J k (P0C c χ)) f = LMIp c χ (J k f) := by
  have h1 : LMIp c (J k (P0C c χ)) f = LMIp c (P0C c χ) (J k f) :=
    hJ.selfAdj k (P0C c χ) f (lmP0C_cellL2 c χ) hf
  rw [h1, hA c hc χ (J k f) hχ (hJ.memL2 k f hf)]
  exact lmIp_congr_right (hF c hc (J k f) (hJ.memL2 k f hf) (hD c hc J hJ hX k f hf hfd))

/-- **Assembly**: `LMDerivRepAEH1` from the leaves. -/
theorem lmDerivRepAEH1_of (hA : LMP0CAdj) (hF : LMP0CFix) (hD : LMJWeakDiv) (hT : LMH1Test)
    (hST : LMSliceTested) (hMR : LMDivJMeasRep) (hP : LMP0Rep) (hU : LMUkL2Loc)
    (hY : LMYtL2Loc) (hUD : LMUDerL2Loc) (hW : LMIpWeightedInt) (hPS : LMPairingSlice)
    (hSl : LMSliceTensor) : LMDerivRepAEH1 := by
  intro c ν μ F b G hS J hJ hX hE k
  have hc : 0 < c := hS.pos_c
  have hTm : ∀ i j, Measurable fun p => lmTens ν F G p i j := fun i j =>
    (measurable_const.mul (hS.sol.gradMeasurable i j)).add (hS.meas i j)
  obtain ⟨Y, hYm, hYe⟩ := hMR c hc J hJ k (lmTens ν F G) hTm
  obtain ⟨Yt, hYtm, hYte⟩ := hP c hc Y hYm
  have hgood : ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))), LMGoodSlice c F G b s :=
    lmAeGoodSlice c ν μ F b G hS
  -- the identification of `Yt(s)` with `𝒫₀ Z(s)` on good slices
  have hYg : ∀ s, LMGoodSlice c F G b s → ∀ᵐ x ∂(volume.restrict (B0579.cell c)), ∀ i : Fin 2,
      Yt (s, x) i = P0C c (lmDivJ J k (fun y => lmTens ν F G (s, y))) x i := by
    intro s hs
    have e : (fun y => Y (s, y)) = lmDivJ J k (fun y => lmTens ν F G (s, y)) := by
      funext x i
      exact hYe s (fun j => lmTens_col_cellL2 hs j) x i
    rw [← e]
    exact hYte s
  have hYae : ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))), ∀ᵐ x ∂(volume.restrict (B0579.cell c)),
      ∀ i : Fin 2, Yt (s, x) i = P0C c (lmDivJ J k (fun y => lmTens ν F G (s, y))) x i := by
    filter_upwards [hgood] with s hs using hYg s hs
  -- the two space-time fields and their local `L²` bounds
  set u : ℝ → LMSpField := LMMollU J b k with hu
  have hum : ∀ i, Measurable fun p : ℝ × (ℝ × ℝ) => u p.1 p.2 i := fun i =>
    hJ.measurable k b hS.sol.measurable i
  have huL := hU c ν μ F b G hS J hJ k
  have hYL := hY c ν μ F b G hS J hJ hX k Yt hYtm hYae
  have hu'm : ∀ i, Measurable fun p : ℝ × (ℝ × ℝ) => lmUDer μ u Yt p.1 p.2 i := fun i =>
    (((measurable_const.div (Complex.measurable_ofReal.comp measurable_fst)).neg).mul
      (hum i)).add (hYtm i)
  have hu'L : ∀ s₁ s₂ : ℝ, 0 < s₁ → s₁ < s₂ → ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c,
      ENNReal.ofReal (vnorm2 (fun i => lmUDer μ u Yt p.1 p.2 i) ^ 2) < ⊤ := fun s₁ s₂ h1 h2 =>
    hUD c μ u Yt hum hYtm s₁ s₂ h1 h2 (huL s₁ s₂ h1 h2) (hYL s₁ s₂ h1 h2)
  -- slices of `u`, `Yt`, and the pairing with `u'`
  have huc : ∀ s, LMGoodSlice c F G b s → LMCellL2 c (u s) := fun s hs =>
    hJ.memL2 k _ hs.1
  have hZc : ∀ s, LMGoodSlice c F G b s →
      LMCellL2 c (P0C c (lmDivJ J k (fun y => lmTens ν F G (s, y)))) := fun s _ =>
    lmP0C_cellL2 c _
  have hYc : ∀ s, LMGoodSlice c F G b s → LMCellL2 c (fun x i => Yt (s, x) i) := by
    intro s hs i
    refine (hZc s hs i).ae_eq ?_
    filter_upwards [hYg s hs] with x hx
    exact (hx i).symm
  refine ⟨lmUDer μ u Yt, ⟨hum, hu'm, huL, hu'L, ?_⟩, ?_⟩
  · -- the tested identity
    intro ψ hψ hcs hts χ hχ
    have hP0χ : LMWeakDivFree c (P0C c χ) := fun ψ' hψ' =>
      p0DivFreeC c hc χ ψ' hψ'
    obtain ⟨hre, him⟩ := hT c hc J hJ hX k (P0C c χ) (lmP0C_cellL2 c χ) hP0χ
    have H0 := hST c ν μ F b G hS hE ψ hψ hcs hts (J k (P0C c χ)) hre him
    have hdψ : Continuous (deriv ψ) := hψ.continuous_deriv (by simp)
    have hsdψ : tsupport (deriv ψ) ⊆ Ioi (0 : ℝ) :=
      (tsupport_deriv_subset (𝕜 := ℝ)).trans hts
    have hI1 := hW c χ u (deriv ψ) hχ hum huL hdψ hcs.deriv hsdψ
    have hI2 := hW c χ (lmUDer μ u Yt) ψ hχ hu'm hu'L hψ.continuous hcs hts
    have hae : ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))),
        (-(((deriv ψ s : ℝ) : ℂ) * LMIp c (J k (P0C c χ)) (fun y => b (s, y))) +
          ((ψ s : ℝ) : ℂ) * ((μ / (s : ℂ)) * LMIp c (J k (P0C c χ)) (fun y => b (s, y))) +
          ((ψ s : ℝ) : ℂ) * ∑ i : Fin 2, ∑ j : Fin 2, ∫ x in B0579.cell c,
            starRingEnd ℂ (LMPd j (fun y => J k (P0C c χ) y i) x) * lmTens ν F G (s, x) i j) =
        -(((deriv ψ s : ℝ) : ℂ) * LMIp c χ (u s)) -
          ((ψ s : ℝ) : ℂ) * LMIp c χ (lmUDer μ u Yt s) := by
      filter_upwards [hgood, ae_restrict_mem measurableSet_Ioi] with s hs hs0
      have hs0' : (0 : ℝ) < s := hs0
      have hP1 : LMIp c (J k (P0C c χ)) (fun y => b (s, y)) = LMIp c χ (u s) :=
        lmSliceScalar hA hF hD hc hJ hX k hχ hs.1 (fun ψ' hψ' => hS.sol.divFree s hs0' ψ' hψ')
      have hQ := hSl c hc J hJ hX k χ (fun y => lmTens ν F G (s, y)) hχ
        (fun j => lmTens_col_cellL2 hs j)
      have hYp : LMIp c χ (P0C c (lmDivJ J k (fun y => lmTens ν F G (s, y)))) =
          LMIp c χ (fun x i => Yt (s, x) i) :=
        lmIp_congr_right (by
          filter_upwards [hYg s hs] with x hx i
          exact (hx i).symm)
      have hsplit : LMIp c χ (lmUDer μ u Yt s) =
          -(μ / (s : ℂ)) * LMIp c χ (u s) + LMIp c χ (fun x i => Yt (s, x) i) := by
        have h1 : lmUDer μ u Yt s = fun x i => -(μ / (s : ℂ)) * u s x i + Yt (s, x) i := rfl
        have hsm : LMCellL2 c (fun x i => -(μ / (s : ℂ)) * u s x i) := fun i =>
          (huc s hs i).const_mul _
        rw [h1, lmIp_add_right hχ hsm (hYc s hs), lmIp_smul_right]
      rw [hP1, hQ, hYp, hsplit]
      ring
    rw [integral_congr_ae hae, integral_sub hI1.fun_neg hI2, integral_neg] at H0
    have H1 : ∫ s in Ioi (0 : ℝ), ((deriv ψ s : ℝ) : ℂ) * LMIp c χ (u s) =
        -∫ s in Ioi (0 : ℝ), ((ψ s : ℝ) : ℂ) * LMIp c χ (lmUDer μ u Yt s) := by
      linear_combination -H0
    exact H1
  · -- the pairing identity
    filter_upwards [hgood, ae_restrict_mem measurableSet_Ioi] with s hs hs0
    have hs0' : (0 : ℝ) < s := hs0
    have hsne : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hs0'.ne'
    have hP := hPS c ν μ F b G hS J hJ hX k s hs0' hs
    have hYp : LMIp c (fun x i => Yt (s, x) i) (u s) =
        LMIp c (P0C c (lmDivJ J k (fun y => lmTens ν F G (s, y)))) (u s) :=
      lmIp_congr_left (hYg s hs)
    have hsm : LMCellL2 c (fun x i => -(μ / (s : ℂ)) * u s x i) := fun i =>
      (huc s hs i).const_mul _
    have hsplit : LMIp c (lmUDer μ u Yt s) (u s) =
        starRingEnd ℂ (-(μ / (s : ℂ))) * LMIp c (u s) (u s) +
          LMIp c (P0C c (lmDivJ J k (fun y => lmTens ν F G (s, y)))) (u s) := by
      have h1 : lmUDer μ u Yt s = fun x i => -(μ / (s : ℂ)) * u s x i + Yt (s, x) i := rfl
      rw [h1, lmIp_add_left hsm (hYc s hs) (huc s hs), lmIp_smul_left, hYp]
    have hE' : LMIp c (u s) (u s) = ((LMMollE c J b k s : ℝ) : ℂ) := lmIp_self c (u s)
    rw [hsplit, hE', Complex.add_re, hP]
    have hre : (starRingEnd ℂ (-(μ / (s : ℂ))) * ((LMMollE c J b k s : ℝ) : ℂ)).re =
        -(μ.re / s) * LMMollE c J b k s := by
      rw [Complex.re_mul_ofReal, Complex.conj_re, Complex.neg_re, Complex.div_ofReal_re]
    rw [hre]
    ring

end UnforcedLeray.Short.IIIa
