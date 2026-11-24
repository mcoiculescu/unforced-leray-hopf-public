import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.Trans
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_1.PeriodSmall
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_1.HU
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.Window

/-!
# `PartIII-b:C/rep/4/4/1/org/1`: `sepYoungRep` from the separated-kernel response

Source `the November 2 reference manuscript` 3611-3621 (`sep:resolvent`, `S_μT = -W_μ`
by the separated kernel `IIIa.sepW`), 4163-4174 (`W_μ = -S_μ(χ_oT)`), 4187-4194, 5153-5157,
5169-5176.

The weak stress inverse `Sop` is pinned only by `IsWeakStressInverse`.  The identification with the
separated kernel therefore goes through free weak uniqueness (closed: `freeWeakUniquenessAll`):
if a body velocity `B` has the coefficient `-coefOf (wardW ..)` and its lift is a weakly
solenoidal solution of the same weak equation as `Sop (oldRep w)`, then `Sop (oldRep w) = B`.

Two lemmas remain, both about the explicit separated-kernel field `W_μ` of the old repair source:
`SepRepBody` (the field `-coefOf (wardW ..)` is a body velocity in the gain class) and
`SepRepWeak` (its lift solves the weak equation).
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace UnforcedLeray.Short.PartIIIb.Concrete

section One

variable (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)

/-- **Lemma A (body velocity).**  Source 3611-3621, 4163-4174, 4187-4194 (separated-kernel
convergence for the repair `L²_τL^{22/19}` source, 5169-5176): for representatives `g₁, g₂` of the
components of `χ_o(0,(M_Uw)₂)`, the field `p ↦ -coefOf ε⁻¹ (wardW ν μ ε⁻¹ c (g₁+g₂)) p`
(`W_μ`, the separated kernel `IIIa.sepW` of the separated representative) is, almost everywhere
for the body measure, a body velocity `B ∈ VelG` (finite gain norm). -/
def SepRepBodyAt : Prop :=
  ∀ (w : LVel Pl L) (g₁ g₂ : Chart → Ten3), IsRep Pl K L (oldRep Pl K L w) g₁ g₂ →
    ∃ B : LVel Pl L, (B : Chart → Merid) =ᵐ[bodyMeasure (cOf L.ν) (gRate Pl) L.ν]
      fun p => -coefOf L.ε⁻¹ (wardW L.ν μ L.ε⁻¹ (cOf L.ν) (g₁ + g₂)) p

/-- **Lemma B (weak equation).**  Source 3611-3621 (`sep:resolvent`: `S_μT = -W_μ`), 4163-4174: any
body velocity whose coefficient is a.e. `-coefOf (wardW ..)` has a lift that is a weakly solenoidal
distributional solution of `D_μ w = ℙ div 𝒩_T(T₁ + T₂)` for `T = χ_o(0,(M_Uw)₂)`, i.e. of the same
equation that pins `Sop T` (`IsWeakStressInverse`). -/
def SepRepWeakAt : Prop :=
  ∀ (w : LVel Pl L) (g₁ g₂ : Chart → Ten3), IsRep Pl K L (oldRep Pl K L w) g₁ g₂ →
    ∀ B : LVel Pl L, (B : Chart → Merid) =ᵐ[bodyMeasure (cOf L.ν) (gRate Pl) L.ν]
        (fun p => -coefOf L.ε⁻¹ (wardW L.ν μ L.ε⁻¹ (cOf L.ν) (g₁ + g₂)) p) →
      IsWeakDmu L.ν μ (2 * L.ε * cOf L.ν) (velPhys L.ε⁻¹ (cOf L.ν) B)
        (fun Φ => -stressPair (2 * L.ε * cOf L.ν)
          (strPhys L.ε⁻¹ (cOf L.ν) (strSum (oldRep Pl K L w))) Φ)

variable {Pl K L μ}

/-- At one regime: Lemmas A, B, free weak uniqueness and the existence of the weak stress inverse
give `SepYoungRepAt` (in fact the identity holds at a.e. point of the whole body measure). -/
theorem sepYoungRepAt_of
    (hU : FreeWeakUniqueness (cOf L.ν) (gRate Pl) L.ν L.ε μ)
    (hS : ∃ S : LStr Pl K L →L[ℝ] LVel Pl L, IsWeakStressInverse S L.ε μ)
    (hA : SepRepBodyAt Pl K L μ) (hB : SepRepWeakAt Pl K L μ) :
    SepYoungRepAt Pl K L μ := by
  intro w g₁ g₂ hg
  obtain ⟨B, hB1⟩ := hA w g₁ g₂ hg
  have hw := hB w g₁ g₂ hg B hB1
  have hSs : IsWeakStressInverse (Sop Pl K L μ) L.ε μ := Classical.epsilon_spec hS
  have hEq : Sop Pl K L μ (oldRep Pl K L w) = B := hU _ _ _ (hSs _) hw
  rw [hEq]
  filter_upwards [hB1] with p hp _
  exact hp

end One

/-- **Lemma A along the sequence.** -/
def SepRepBody (dm dp : ℝ) : Prop :=
  ∀ D : SeqData, D.RepairStanding dm dp → ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    SepRepBodyAt D.Pl D.K (D.level n) (D.mu n z)

/-- **Lemma B along the sequence.** -/
def SepRepWeak (dm dp : ℝ) : Prop :=
  ∀ D : SeqData, D.RepairStanding dm dp → ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    SepRepWeakAt D.Pl D.K (D.level n) (D.mu n z)

/-- `SepYoungRep` from Lemmas A and B. -/
theorem sepYoungRep_of (dm dp : ℝ) (hA : SepRepBody dm dp) (hB : SepRepWeak dm dp) :
    SepYoungRep dm dp := by
  intro D hst
  filter_upwards [hA D hst, hB D hst, periodSmall D hst, muWin_gt_quarter D hst, hst.pins]
    with n h1 h2 h3 h4 h5 z hz
  exact sepYoungRepAt_of
    (freeWeakUniquenessAll _ _ _ _ _ (cOf_pos (D.level n).ν_pos) (D.level n).ν_pos
      (D.level n).ε_pos h3 (by linarith [h4 z hz]))
    (h5 z hz).stress (h1 z hz) (h2 z hz)

end UnforcedLeray.Short.PartIIIb.Concrete
