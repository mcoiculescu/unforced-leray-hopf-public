import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.XmtSmooth
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.N0

/-!
# Part III-b, task `PartIII-b:C/srcL/10` (`sourceLSmooth`)

`𝓛T` is `C^6` on `(0,∞)`: `𝓛T(s) = D_y X^mt(R/√s, 0, 0)` (`Lpt`, SourceL.lean), and `X^mt` is `C^7`
(`xmtSmooth`) for the thin representative of a stress with finite `N₀` (`sourceLN0`).  Source
4797-4800 of `the November 2 reference manuscript`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The receiver path `s ↦ (ε⁻¹/√s, 0, 0)` is `C^6` on `(0,∞)`. -/
theorem contDiffOn_recvPt (ε : ℝ) :
    ContDiffOn ℝ 6 (fun s : ℝ => (![ε⁻¹ / Real.sqrt s, 0, 0] : Vec3)) (Ioi 0) := by
  have hfun : (fun s : ℝ => (![ε⁻¹ / Real.sqrt s, 0, 0] : Vec3)) =
      fun s : ℝ => (ε⁻¹ / Real.sqrt s) • (![1, 0, 0] : Vec3) := by
    funext s
    ext k
    fin_cases k <;> simp
  rw [hfun]
  have hsq : ContDiffOn ℝ 6 (fun s : ℝ => Real.sqrt s) (Ioi 0) :=
    contDiffOn_id.sqrt (fun x hx => (Set.mem_Ioi.1 hx).ne')
  exact ContDiffOn.smul (contDiffOn_const.div hsq
    (fun x hx => (Real.sqrt_pos.2 (Set.mem_Ioi.1 hx)).ne')) contDiffOn_const

/-- `𝓛T` is `C^6` on `(0,∞)` for a stress with finite `N₀` thin component. -/
theorem sourceLSmooth (c mZ ρb γ ν ε μ : ℝ) (χo χy : ℝ → ℝ) :
    SourceLSmooth c mZ ρb γ ν ε μ χo χy := by
  intro h hmZ hγ T
  obtain ⟨C, k, hC⟩ := sourceLN0 mZ γ hmZ hγ
  have hfin : OldThinFinite c ν (thinRep T) := (hC c ν ρb h.c_pos h.nu_pos h.nu_le T).1
  have hX : ContDiff ℝ 7 (Xmt c ν ε μ χo χy (thinRep T)) :=
    xmtSmooth c ν ε μ χo χy h (thinRep T) hfin
  have hD : ContDiff ℝ 6 (fderiv ℝ (Xmt c ν ε μ χo χy (thinRep T))) :=
    hX.fderiv_right (by norm_num)
  have hDy : ContDiffOn ℝ 6
      (fun s : ℝ => fderiv ℝ (Xmt c ν ε μ χo χy (thinRep T)) ![ε⁻¹ / Real.sqrt s, 0, 0])
      (Ioi 0) :=
    hD.contDiffOn.comp (contDiffOn_recvPt ε) (mapsTo_univ _ _)
  have hcol : ∀ j : Fin 3, ContDiffOn ℝ 6
      (fun s : ℝ => fderiv ℝ (Xmt c ν ε μ χo χy (thinRep T)) ![ε⁻¹ / Real.sqrt s, 0, 0]
        (Pi.single j 1)) (Ioi 0) :=
    fun j => hDy.clm_apply contDiffOn_const
  have hmat : ContDiffOn ℝ 6
      (fun s : ℝ => (fun i j => fderiv ℝ (Xmt c ν ε μ χo χy (thinRep T))
        ![ε⁻¹ / Real.sqrt s, 0, 0] (Pi.single j 1) i : Mat3)) (Ioi 0) :=
    contDiffOn_pi.2 fun i => contDiffOn_pi.2 fun j => contDiffOn_pi.1 (hcol j) i
  refine hmat.congr ?_
  intro s hs
  show Lpt c ν ε μ χo χy (thinRep T) s = _
  unfold Lpt
  rw [if_pos (Set.mem_Ioi.1 hs)]

end UnforcedLeray.Short.PartIIIb.Concrete
