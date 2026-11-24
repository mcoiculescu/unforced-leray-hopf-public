import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_8.Split.BrkSecondClosed
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_8.Split.VjSecondClosed
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_8.Split.MgradPsiAjClosed

/-!
# `PartIII-b:C/asrc/ra/8/1/org` : `RPerSplit` from the open leaves

Source of record: `the November 2 reference manuscript` (73 pages), 5022-5027,
4963-4978, 2040-2051.

The closed-form leaves (L1) `brkClosed`, (L2) `brkFDerivClosed`, (L3) `brkSecondClosed`,
(L5) `vjSecondClosed`, (L6) `mgradPsiAjClosed` are proved; `rPerSplit_of_leaves` reduces `RPerSplit`
to the remaining leaves: (L4) `BrkDerivSClosed`, (G1) `LatticeFDerivSum`, (B1)-(B4) the Gaussian
bounds, (T3) `HpASumS` and (D) `TsumBilinSplit`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The single-center identity, from the proved closed forms and (L4). -/
theorem brkIdentity_of_derivS (h4 : BrkDerivSClosed) : BrkIdentity :=
  brkIdentity_of brkClosed brkFDerivClosed brkSecondClosed h4 vjSecondClosed mgradPsiAjClosed

/-- **`RPerSplit` from the open leaves** (source 5022-5027). -/
theorem rPerSplit_of_leaves (as : ℝ) (χf : ℝ → ℝ) (h4 : BrkDerivSClosed)
    (hG : LatticeFDerivSum) (hB1 : BrkGaussBound1) (hB2 : BrkGaussBound2) (hB3 : VjGaussBound)
    (hB4 : PsiAjGaussBound) (hS : HpASumS as χf) (hD : TsumBilinSplit) : RPerSplit as χf :=
  rPerSplit_of as χf (brkIdentity_of_derivS h4) hS
    (hpASumX_of hG hB1 brkFDerivClosed)
    (hpASumLap_of hG (hpASumX_of hG hB1 brkFDerivClosed) hB1 hB2 brkSecondClosed)
    (vsumSum_of hG hB3) (psiASum_of hG hB4 mgradPsiAjClosed) hD

end UnforcedLeray.Short.PartIIIb.Concrete
