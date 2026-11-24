import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_4_2_org_1

/-!
# `PartIII-b:C/rep/4/2/org/1/1`: weak representation = existence of one kernel solution + uniqueness

Source `the November 2 reference manuscript` 3596-3621 (`sep:kernel`,
`sep:resolvent`: `W_μ = -S_μT`), 4155-4171, 1556-1583 (`free:weak-stress`, free weak uniqueness),
5573-5576.

`SepWeakRepresentation` quantifies over *every* weak solution `w`.  By free weak uniqueness
(`FreeWeakUniqueness`, 1571, 1580-1583) it is enough to exhibit **one** body velocity `w'` with the
same weak right-hand side whose coefficient is `-W_μ` at a.e. young chart point
(`SepWeakExistence`: the separated-kernel integral of `sep:resolvent`, absolutely convergent on
the young region `r ≥ R√ν` by `IIIa.sepKernelBounds` and the finite old mass 5573-5576, is the
restriction of a global `Y_2` weak solution).  Here `sepWeakRepresentationThin_of` is proved.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

section
variable (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)

/-- **Existence of a global weak solution with the separated-kernel values on the young region**
(source 3611-3621, 4155-4171, 5573-5576): for the old thin source `oldThin T` with chart
representatives `g₁ g₂`, there is a body velocity `w'` whose lift is a weakly solenoidal
distributional solution of `D_μ w = ℙ div 𝒩_T(oldThin T)` and whose coefficient is `-W_μ` at
`bodyMeasure`-a.e. young chart point `νs ≤ 1`. -/
def SepWeakExistence : Prop :=
  ∀ (T : LStr Pl K L) (g₁ g₂ : Chart → Ten3), IsRep Pl K L (oldThin Pl K L T) g₁ g₂ →
    ∃ w' : LVel Pl L,
      IsWeakDmu L.ν μ (2 * L.ε * cOf L.ν) (velPhys L.ε⁻¹ (cOf L.ν) w')
        (fun Φ => -stressPair (2 * L.ε * cOf L.ν)
          (strPhys L.ε⁻¹ (cOf L.ν) (strSum (oldThin Pl K L T))) Φ) ∧
      ∀ᵐ p ∂(bodyMeasure (cOf L.ν) (gRate Pl) L.ν), L.ν * p.1 ≤ 1 →
        (w' : Chart → Merid) p =
          -coefOf L.ε⁻¹ (wardW L.ν μ L.ε⁻¹ (cOf L.ν) (g₁ + g₂)) p

/-- Weak representation from existence and free weak uniqueness. -/
theorem sepWeakRepresentation_of (hU : FreeWeakUniqueness (cOf L.ν) (gRate Pl) L.ν L.ε μ)
    (hE : SepWeakExistence Pl K L μ) : SepWeakRepresentation Pl K L μ := by
  intro T g₁ g₂ hg w hw
  obtain ⟨w', hw', hae⟩ := hE T g₁ g₂ hg
  have : w = w' := hU w w' _ hw hw'
  subst this
  exact hae

end

/-- Existence along the sequence (large `n`, all `z ∈ [-1,1]`). -/
def SepWeakExistenceThin (dm dp : ℝ) : Prop :=
  ∀ D : SeqData, D.RepairStanding dm dp → ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    SepWeakExistence D.Pl D.K (D.level n) (D.mu n z)

/-- Free weak uniqueness along the sequence (source 1571, 1580-1583). -/
def FreeWeakUniquenessThin (dm dp : ℝ) : Prop :=
  ∀ D : SeqData, D.RepairStanding dm dp → ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    FreeWeakUniqueness (cOf (D.level n).ν) (gRate D.Pl) (D.level n).ν (D.level n).ε (D.mu n z)

/-- **`sepWeakRepresentationThin` from existence and uniqueness.** -/
theorem sepWeakRepresentationThin_of {dm dp : ℝ} (hU : FreeWeakUniquenessThin dm dp)
    (hE : SepWeakExistenceThin dm dp) : SepWeakRepresentationThin dm dp := by
  intro D hst
  filter_upwards [hU D hst, hE D hst] with n h1 h2 z hz
  exact sepWeakRepresentation_of D.Pl D.K (D.level n) (D.mu n z) (h1 z hz) (h2 z hz)

end UnforcedLeray.Short.PartIIIb.Concrete
