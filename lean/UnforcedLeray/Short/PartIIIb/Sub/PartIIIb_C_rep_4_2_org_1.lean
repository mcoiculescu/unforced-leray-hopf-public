import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.Org.YThinTrans

/-!
# Decomposition of `sepYoungThin` (`PartIII-b:C/rep/4/2/org/1`; source 3611-3621, 4161-4171, 5148-5157)

`SepYoungAt` says that the coefficient of `Sop (oldThin T)` is `-coefOf (wardW …)` at a.e. young
chart point.  `Sop` is only pinned as *a* weak stress inverse (`Classical.epsilon` of
`IsWeakStressInverse`, existence from `RegimePins.stress`).  The analytic content is therefore the
**weak representation** `SepWeakRepresentation`: every `Y_2` weakly solenoidal distributional
solution `w` of `D_μ w = ℙ div 𝒩_T(oldThin T)` is, at a.e. young chart point `νs ≤ 1`, the
negative separated-kernel response `-W_μ` (`sep:resolvent`, 3611-3621: `W_μ = -S_μ(χ_oT)`; the old
source is supported in `s ≥ 1.2/ν`, i.e. in the radial disk `r ≤ R√(ν/1.2)`, separated from the
young receiver `r ≥ R√ν`, where the kernel integral converges absolutely by
`IIIa.sepKernelBounds`, `|∇K| ≤ C|x|^{-4}`, 5573-5576).  Here this is proved to imply
`SepYoungAt` / `SepYoungThin` (`sepYoungAt_of`, `sepYoungThin_of`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

section
variable (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)

/-- **Weak representation of the old thin response by the separated kernel** (source 3611-3621
`sep:resolvent`, 4163-4171, 5153-5157; free weak uniqueness 1571; absolute convergence of the
kernel integral on the young region by `IIIa.sepKernelBounds` and the finite old mass, 5573-5576).
For the old thin source `oldThin T` with chart representatives `g₁ g₂` of its two components, every
body velocity `w` whose lift is a weakly solenoidal distributional solution of
`D_μ w = ℙ div 𝒩_T(oldThin T)` (the clauses of `IsWeakStressInverse`) has, at `bodyMeasure`-a.e.
young chart point `νs ≤ 1`, the coefficient `-coefOf (wardW …(g₁+g₂))`. -/
def SepWeakRepresentation : Prop :=
  ∀ (T : LStr Pl K L) (g₁ g₂ : Chart → Ten3), IsRep Pl K L (oldThin Pl K L T) g₁ g₂ →
    ∀ w : LVel Pl L,
      IsWeakDmu L.ν μ (2 * L.ε * cOf L.ν) (velPhys L.ε⁻¹ (cOf L.ν) w)
        (fun Φ => -stressPair (2 * L.ε * cOf L.ν)
          (strPhys L.ε⁻¹ (cOf L.ν) (strSum (oldThin Pl K L T))) Φ) →
      ∀ᵐ p ∂(bodyMeasure (cOf L.ν) (gRate Pl) L.ν), L.ν * p.1 ≤ 1 →
        (w : Chart → Merid) p =
          -coefOf L.ε⁻¹ (wardW L.ν μ L.ε⁻¹ (cOf L.ν) (g₁ + g₂)) p

/-- The pinned stress inverse `Sop` is a weak stress inverse as soon as one exists. -/
theorem sop_isWeakStressInverse (hpins : RegimePins Pl K L μ) :
    IsWeakStressInverse (Sop Pl K L μ) L.ε μ :=
  Classical.epsilon_spec hpins.stress

/-- `SepYoungAt` at a regime from the weak representation and the existence of the stress inverse. -/
theorem sepYoungAt_of (hpins : RegimePins Pl K L μ) (h : SepWeakRepresentation Pl K L μ) :
    SepYoungAt Pl K L μ := by
  intro T g₁ g₂ hg
  exact h T g₁ g₂ hg (Sop Pl K L μ (oldThin Pl K L T))
    (sop_isWeakStressInverse Pl K L μ hpins (oldThin Pl K L T))

end

/-- The weak representation along the sequence (large `n`, all `z ∈ [-1,1]`). -/
def SepWeakRepresentationThin (dm dp : ℝ) : Prop :=
  ∀ D : SeqData, D.RepairStanding dm dp → ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    SepWeakRepresentation D.Pl D.K (D.level n) (D.mu n z)

/-- `SepYoungThin` from the weak representation. -/
theorem sepYoungThin_of (dm dp : ℝ) (h : SepWeakRepresentationThin dm dp) : SepYoungThin dm dp := by
  intro D hst
  filter_upwards [h D hst, hst.pins] with n hn hp z hz
  exact sepYoungAt_of D.Pl D.K (D.level n) (D.mu n z) (hp z hz) (hn z hz)

end UnforcedLeray.Short.PartIIIb.Concrete
