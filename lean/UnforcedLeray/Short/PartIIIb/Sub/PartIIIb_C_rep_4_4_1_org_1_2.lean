import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_4_4_1_org_1

/-!
# `PartIII-b:C/rep/4/4/1/org/1/2`: `sepRepWeak` (Lemma B of `sepYoungRep`), decomposed

Source `the November 2 reference manuscript`
3604-3621 (`sep:resolvent`, `sep:kernel`: `S_μT = -W_μ`), 4163-4174, 5153-5157.

`SepRepWeakAt` follows from four facts about the explicit field `W_μ = wardW` of the old repair
source `g₁ + g₂`:

* `SepRepLift`: the physical lift of a body velocity with coefficient `-coefOf (wardW ..)` is a.e.
  the physical field `-W_μ` (axisymmetry, no swirl: `Nv` of the meridional coefficient);
* `SepRepStressAE`: the physical stress of `T₁ + T₂` of the old representative is a.e.
  `oldPhys (g₁ + g₂)` (`IsRep`);
* `SepNegSolenoidal`: `-W_μ` is weakly solenoidal (the heat-Leray kernel is divergence free);
* `SepNegEquation`: `-W_μ` solves `⟨D_μᵗΦ, w⟩ = -⟨T, ∇Φ⟩` against solenoidal tests
  (Duhamel/Fubini, `sep:resolvent`).

The a.e.-congruence of `IsWeakDmu` is proved here.
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open scoped ENNReal
open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest)

theorem phaseInt_congr_ae' (P : ℝ) {f g : ℝ × UnforcedLeray.Space → ℂ}
    (h : f =ᵐ[volume] g) : phaseInt P f = phaseInt P g := by
  unfold phaseInt
  congr 1
  rw [Measure.volume_eq_prod] at h
  have h2 := Measure.ae_ae_of_ae_prod h
  apply setIntegral_congr_ae measurableSet_Ioc
  filter_upwards [h2] with t ht _
  exact integral_congr_ae ht

theorem pairF_congr_ae' (P : ℝ) (Φ : ℝ × UnforcedLeray.Space → CVec3) {u u' : ℝ × UnforcedLeray.Space → CVec3}
    (h : u =ᵐ[volume] u') : pairF P Φ u = pairF P Φ u' := by
  unfold pairF
  apply phaseInt_congr_ae'
  filter_upwards [h] with x hx
  simp [hx]

theorem stressPair_congr_ae' (P : ℝ) {T T' : ℝ × UnforcedLeray.Space → Matrix (Fin 3) (Fin 3) ℝ}
    (h : T =ᵐ[volume] T') (Φ : ℝ × UnforcedLeray.Space → CVec3) :
    stressPair P T Φ = stressPair P T' Φ := by
  unfold stressPair
  apply phaseInt_congr_ae'
  filter_upwards [h] with x hx
  simp [hx]

/-- `IsWeakDmu` is invariant under a.e. change of the field and pointwise change of the right side. -/
theorem isWeakDmu_congr_ae (ν μ P : ℝ) {w w' : ℝ × UnforcedLeray.Space → CVec3}
    {rhs rhs' : (ℝ × UnforcedLeray.Space → CVec3) → ℂ} (h : w =ᵐ[volume] w')
    (hr : ∀ Φ, IsSolTest P Φ → rhs Φ = rhs' Φ) (hw : IsWeakDmu ν μ P w' rhs') :
    IsWeakDmu ν μ P w rhs := by
  refine ⟨fun φ hφ => ?_, fun Φ hΦ => ?_⟩
  · rw [pairF_congr_ae' P _ h]; exact hw.solenoidal φ hφ
  · rw [pairF_congr_ae' P _ h, hr Φ hΦ]; exact hw.equation Φ hΦ

section One

/-- The physical field `-W_μ`, `W_μ = wardW` of the old repair source `g` (source 4163-4174). -/
def negW (L : ReturnLevel) (μ : ℝ) (g : Chart → Ten3) : ℝ × UnforcedLeray.Space → CVec3 :=
  fun x => UnforcedLeray.B0412.realC (-(wardW L.ν μ L.ε⁻¹ (cOf L.ν) g x.1 x.2))

/-- **Lift** (source 4171-4178, 2666-2668, 2683): a body velocity whose coefficient is a.e.
`-coefOf ε⁻¹ (wardW ..)` has physical lift a.e. equal to `-W_μ` (axisymmetric, swirl-free field
recovered from its meridional coefficient). -/
def SepRepLiftAt (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ) : Prop :=
  ∀ (w : LVel Pl L) (g₁ g₂ : Chart → Ten3), IsRep Pl K L (oldRep Pl K L w) g₁ g₂ →
    ∀ B : LVel Pl L, (B : Chart → Merid) =ᵐ[bodyMeasure (cOf L.ν) (gRate Pl) L.ν]
        (fun p => -coefOf L.ε⁻¹ (wardW L.ν μ L.ε⁻¹ (cOf L.ν) (g₁ + g₂)) p) →
      velPhys L.ε⁻¹ (cOf L.ν) B =ᵐ[volume] negW L μ (g₁ + g₂)

/-- **Stress** (source 4171-4174): the physical stress of `T₁ + T₂` of the old representative is
a.e. the physical old source `oldPhys (g₁ + g₂)`. -/
def SepRepStressAt (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) : Prop :=
  ∀ (w : LVel Pl L) (g₁ g₂ : Chart → Ten3), IsRep Pl K L (oldRep Pl K L w) g₁ g₂ →
    strPhys L.ε⁻¹ (cOf L.ν) (strSum (oldRep Pl K L w)) =ᵐ[volume]
      fun x => oldPhys L.ε⁻¹ (cOf L.ν) (g₁ + g₂) x.1 x.2

/-- **Solenoidal** (source 3604-3610: the heat-Leray kernel is divergence free in its first index,
`sep:kernel`): `-W_μ` is weakly solenoidal. -/
def SepNegSolenoidalAt (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ) : Prop :=
  ∀ (w : LVel Pl L) (g₁ g₂ : Chart → Ten3), IsRep Pl K L (oldRep Pl K L w) g₁ g₂ →
    IsWeakSolenoidal (2 * L.ε * cOf L.ν) (negW L μ (g₁ + g₂))

/-- **Equation** (source 3611-3621, `sep:resolvent`, `S_μT = -W_μ`; Duhamel/Fubini of the
heat-Leray kernel against solenoidal tests): `⟨D_μᵗΦ, -W_μ⟩ = -⟨oldPhys, ∇Φ⟩` for solenoidal
phase tests `Φ`, `P = 2εc`. -/
def SepNegEquationAt (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ) : Prop :=
  ∀ (w : LVel Pl L) (g₁ g₂ : Chart → Ten3), IsRep Pl K L (oldRep Pl K L w) g₁ g₂ →
    ∀ Φ, IsSolTest (2 * L.ε * cOf L.ν) Φ →
      pairF (2 * L.ε * cOf L.ν) (fun x => L0T L.ν Φ x + (μ : ℂ) • Φ x) (negW L μ (g₁ + g₂)) =
        -stressPair (2 * L.ε * cOf L.ν)
          (fun x => oldPhys L.ε⁻¹ (cOf L.ν) (g₁ + g₂) x.1 x.2) Φ

variable {Pl : PlanarData} {K : ReturnConsts} {L : ReturnLevel} {μ : ℝ}

/-- `SepRepWeakAt` from the four facts. -/
theorem sepRepWeakAt_of (hL : SepRepLiftAt Pl K L μ) (hS : SepRepStressAt Pl K L)
    (h1 : SepNegSolenoidalAt Pl K L μ) (h2 : SepNegEquationAt Pl K L μ) :
    SepRepWeakAt Pl K L μ := by
  intro w g₁ g₂ hg B hB
  refine isWeakDmu_congr_ae L.ν μ _ (hL w g₁ g₂ hg B hB) (fun Φ _ => ?_)
    ⟨h1 w g₁ g₂ hg, h2 w g₁ g₂ hg⟩
  rw [stressPair_congr_ae' _ (hS w g₁ g₂ hg)]

end One

/-- `SepRepLiftAt` along the sequence. -/
def SepRepLift (dm dp : ℝ) : Prop :=
  ∀ D : SeqData, D.RepairStanding dm dp → ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    SepRepLiftAt D.Pl D.K (D.level n) (D.mu n z)

/-- `SepRepStressAt` along the sequence. -/
def SepRepStress (dm dp : ℝ) : Prop :=
  ∀ D : SeqData, D.RepairStanding dm dp → ∀ᶠ n : ℕ in atTop, SepRepStressAt D.Pl D.K (D.level n)

/-- `SepNegSolenoidalAt` along the sequence. -/
def SepNegSolenoidal (dm dp : ℝ) : Prop :=
  ∀ D : SeqData, D.RepairStanding dm dp → ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    SepNegSolenoidalAt D.Pl D.K (D.level n) (D.mu n z)

/-- `SepNegEquationAt` along the sequence. -/
def SepNegEquation (dm dp : ℝ) : Prop :=
  ∀ D : SeqData, D.RepairStanding dm dp → ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    SepNegEquationAt D.Pl D.K (D.level n) (D.mu n z)

/-- **`sepRepWeak`** from the four sequence-level facts. -/
theorem sepRepWeak_of (dm dp : ℝ) (hL : SepRepLift dm dp) (hS : SepRepStress dm dp)
    (h1 : SepNegSolenoidal dm dp) (h2 : SepNegEquation dm dp) : SepRepWeak dm dp := by
  intro D hst
  filter_upwards [hL D hst, hS D hst, h1 D hst, h2 D hst] with n a b c d z hz
  exact sepRepWeakAt_of (a z hz) b (c z hz) (d z hz)

end UnforcedLeray.Short.PartIIIb.Concrete
end
