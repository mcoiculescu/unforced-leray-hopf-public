import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1_org
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst
import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Proofs.BroadMult

/-!
# `PartIII-b:C/rep/8/swirl/1`: the multiplier `M_U w` is swirl free

Source of record: `the November 2 reference manuscript`, line 5376 (`T = M_U w`),
5141-5142 (`w`, `U` swirl free), 4772-4774 (zero azimuthal row and column).

The thin component of `multOp w` is a.e. a positive scalar multiple of the gain-conjugate of the
thin component of `nearMU (gainH w)`, which is a.e. `ten3Of (symOuter a b)` for meridional `a, b`;
such a tensor has zero entries in every row or column with index `1` (the azimuthal index).
-/

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

open UnforcedLeray.Short.PartIIIb.NearInst
open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- A `3×3` tensor pattern: zero in every row and column with azimuthal index `1`. -/
theorem pat_ten3Of (a b : Merid) :
    ∀ i j : Fin 3, (i = 1 ∨ j = 1) → NearInst.ten3Of (UnforcedLeray.Short.IIIa.symOuter a b) (i, j) = 0 := by
  intro i j hij
  rcases hij with rfl | rfl <;>
    simp [NearInst.ten3Of, UnforcedLeray.Short.IIIa.symOuter, UnforcedLeray.Short.IIIa.embedMerid]

theorem aux_X {c mZ ρb γ ν : ℝ} (hν : 0 < ν) (M : Hsp c →L[ℝ] Zsp c mZ ρb) (u : Hsp c)
    (hM : ∀ᵐ p ∂(z1Measure c mZ), ∀ i j : Fin 3, (i = 1 ∨ j = 1) →
      ((M u).fst : Chart → Ten3) p (i, j) = 0) :
    ∀ᵐ p ∂(gainZ1Measure c mZ γ ν), ∀ i j : Fin 3, (i = 1 ∨ j = 1) →
      (((strIso c mZ ρb γ ν).symm ((gainEquiv c mZ ρb γ hν).symm (M u))).fst : Chart → Ten3) p
        (i, j) = 0 := by
  have h1 := NearInst.coeFn_strIso_symm_fst (γ := γ) (ν := ν)
    ((gainEquiv c mZ ρb γ hν).symm (M u))
  have h2 : ∀ᵐ p ∂(gainZ1Measure c mZ γ ν),
      (((gainEquiv c mZ ρb γ hν).symm (M u)).fst : Chart → Ten3) p
        = gainInvFun γ ν p • ((M u).fst : Chart → Ten3) p := by
    rw [NearInst.ae_gainZ1Measure]
    exact NearInst.Delta.gainEquiv_symm_fst c mZ ρb γ hν (M u)
  have h3 : ∀ᵐ p ∂(gainZ1Measure c mZ γ ν), ∀ i j : Fin 3, (i = 1 ∨ j = 1) →
      ((M u).fst : Chart → Ten3) p (i, j) = 0 := by
    rw [NearInst.ae_gainZ1Measure]
    exact hM
  filter_upwards [h1, h2, h3] with p hp1 hp2 hp3
  intro i j hij
  rw [hp1, hp2]
  simp [hp3 i j hij]

theorem aux_main {c mZ ρb γ ν : ℝ} (hν : 0 < ν) (M : Hsp c →L[ℝ] Zsp c mZ ρb) (u : Hsp c)
    (hM : ∀ᵐ p ∂(z1Measure c mZ), ∀ i j : Fin 3, (i = 1 ∨ j = 1) →
      ((M u).fst : Chart → Ten3) p (i, j) = 0) (c0 : ℝ) :
    ∀ᵐ p ∂(ageμ c (-1 / 2)), ∀ i j : Fin 3, (i = 1 ∨ j = 1) →
      thinRep (c0 • (strIso c mZ ρb γ ν).symm ((gainEquiv c mZ ρb γ hν).symm (M u))) p i j = 0 := by
  rw [← NearInst.ae_z1Measure c mZ]
  rw [← NearInst.ae_gainZ1Measure c mZ γ ν]
  have hX := aux_X (γ := γ) hν M u hM
  have hs := Lp.coeFn_smul c0
    (((strIso c mZ ρb γ ν).symm ((gainEquiv c mZ ρb γ hν).symm (M u))).fst)
  set Y := (strIso c mZ ρb γ ν).symm ((gainEquiv c mZ ρb γ hν).symm (M u)) with hY
  filter_upwards [hX, hs] with p hX' hs'
  intro i j hij
  show ((c0 • Y).fst : Chart → Ten3) p (i, j) = 0
  rw [show (c0 • Y).fst = c0 • Y.fst from rfl, hs', Pi.smul_apply, PiLp.smul_apply, hX' i j hij,
    smul_zero]

theorem multOp_thinAziZero (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel)
    (hsplit : ∃ M : Hsp (cOf L.ν) →L[ℝ] Zsp (cOf L.ν) K.mZ (L.ρb Pl K),
      NearInst.IsSplitMult M (L.params Pl).R L.V L.rb)
    (w : LVel Pl L) : ThinAziZero Pl K L (multOp Pl K L w) := by
  have hM := nearMU_spec hsplit
  set u := gainH (cOf L.ν) (gRate Pl) L.ν_pos (velIso (cOf L.ν) (gRate Pl) L.ν w) with hu
  have hMu : ∀ᵐ p ∂(z1Measure (cOf L.ν) K.mZ), ∀ i j : Fin 3, (i = 1 ∨ j = 1) →
      ((nearMU Pl K L u).fst : Chart → Ten3) p (i, j) = 0 := by
    filter_upwards [(hM u).1] with p hp
    intro i j hij
    rw [hp]
    exact pat_ten3Of _ _ i j hij
  unfold ThinAziZero
  exact aux_main (γ := gRate Pl) (ν := L.ν) L.ν_pos (nearMU Pl K L) u hMu ((Real.sqrt Real.pi)⁻¹)

end UnforcedLeray.Short.PartIIIb.Concrete
