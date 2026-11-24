import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G4Org

/-!
# `PartIII-b:IIIb-D3/2/G4/4`: integrability of the two `I_T` pieces

Source `the November 2 reference manuscript`: `I_T` 4584-4592; split at
`u_o = ν^{-3/2}` 4668-4690 ("full forward gain estimate" 4686-4688); absolute moments 4637-4693.
The integrability is reduced to three source facts: measurability in `s` of the two pieces and
an integrable majorant of each (a pointwise-in-`s` bound of `cellInt |M_B|`, as `momentC` is only
a Bochner integral).
-/

set_option autoImplicit false

noncomputable section

open Filter Topology Set MeasureTheory

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G4

open ConcreteYF

/-- Upper piece of `I_T` integrand (`s ≥ ν^{-3/2}`), 4668-4686. -/
def upperPiece (D : SeqData) (S : ℕ → FlatSetting) (n : ℕ) (z : ℝ) (B : ℝ → Matrix (Fin 3) (Fin 3) ℝ)
    (s : ℝ) : ℝ :=
  (S n).ITdens (fun s => if nu D n ^ (-(3 / 2 : ℝ)) ≤ s then
        (S n).Mcell s ((S n).xi (D.mu n z : ℂ) B s) else fun _ => 0) s

/-- Lower piece of `I_T` integrand (`s < ν^{-3/2}`), 4686-4688. -/
def lowerPiece (D : SeqData) (S : ℕ → FlatSetting) (n : ℕ) (z : ℝ) (B : ℝ → Matrix (Fin 3) (Fin 3) ℝ)
    (s : ℝ) : ℝ :=
  (S n).ITdens (fun s => if s < nu D n ^ (-(3 / 2 : ℝ)) then
        (S n).Mcell s ((S n).xi (D.mu n z : ℂ) B s) else fun _ => 0) s

/-- Source fact (4584-4592, continuity of `ξ_B` in `s` and L² control of the readout on the cell):
both pieces are a.e.-strongly measurable in `s`. -/
def PieceMeas (D : SeqData) : Prop :=
  ForActual D fun S => ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1, ∀ B,
      IsBclass D.K.as (nu D n) B →
    AEStronglyMeasurable (upperPiece D S n z B) (volume.restrict (Ioi (0 : ℝ))) ∧
    AEStronglyMeasurable (lowerPiece D S n z B) (volume.restrict (Ioi (0 : ℝ)))

/-- Source fact (4637-4693, absolute moment `k = 0` pointwise in `s`): the upper piece has an
integrable majorant on `Ioi 0` (`χ_o` vanishes for `s ≤ 1.2/ν`; decay for `s ≥ 1.2/ν`). -/
def UpperMaj (D : SeqData) : Prop :=
  ForActual D fun S => ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1, ∀ B,
      IsBclass D.K.as (nu D n) B →
    ∃ G : ℝ → ℝ, Integrable G (volume.restrict (Ioi (0 : ℝ))) ∧
      ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))), ‖upperPiece D S n z B s‖ ≤ G s

/-- Source fact (4686-4688, full forward gain estimate on the bounded interval
`(1.2/ν, ν^{-3/2})`): the lower piece has an integrable majorant on `Ioi 0`. -/
def LowerMaj (D : SeqData) : Prop :=
  ForActual D fun S => ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1, ∀ B,
      IsBclass D.K.as (nu D n) B →
    ∃ G : ℝ → ℝ, Integrable G (volume.restrict (Ioi (0 : ℝ))) ∧
      ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))), ‖lowerPiece D S n z B s‖ ≤ G s

theorem IntConj_of (D : SeqData) (h1 : PieceMeas D) (h2 : UpperMaj D) (h3 : LowerMaj D) :
    IntConj D := by
  intro dm dp hst κ hκ m _ hm S hS
  filter_upwards [h1 dm dp hst κ hκ m hm S hS, h2 dm dp hst κ hκ m hm S hS,
    h3 dm dp hst κ hκ m hm S hS] with n a b c
  intro z hz B hB
  obtain ⟨m1, m2⟩ := a z hz B hB
  obtain ⟨G, hG, hle⟩ := b z hz B hB
  obtain ⟨G', hG', hle'⟩ := c z hz B hB
  exact ⟨hG.mono' m1 hle, hG'.mono' m2 hle'⟩

end UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G4
