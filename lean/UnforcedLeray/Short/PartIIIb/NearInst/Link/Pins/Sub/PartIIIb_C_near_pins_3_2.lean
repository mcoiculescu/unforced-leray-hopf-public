import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Sub.PartIIIb_C_near_pins_3
import UnforcedLeray.Units.B0226

/-!
# `PepsSolenoidal` decomposed (task `PartIII-b:C/near/pins/3/2`)

Source `the November 2 reference manuscript` 1675-1677 (`P_ε` is the conjugated
Cartesian Leray projection), 1339-1362, 4139-4146.

`P_ε z` lies in `solenoidalHC` and has a real chart form `wk`; its real part `b ∈ H` lies in the
real solenoidal subspace `B0226.solenoidalH` (leaf `PepsRealMember`), whose lift `J_ε b` is
divergence free on `ℝ³ × period` (`B0226.J_mem_of_solenoidalH`, proved in the library); and the
physical pairing against a complex phase test is a fixed multiple of the `L²` pairings of `J_ε b`
with the gradients of the real and imaginary parts (leaf `PairWithLift`, the `liftVec`/`velPhys`
dictionary: `Axi.Nv`, `Axi.perExt`, `B0223.coeFn_liftVec`, `Axi.liftFun_congr_ae`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst

open UnforcedLeray.Short.PartIIIb.Concrete UnforcedLeray.Cons.C03.Concrete
  UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.B0220 (HSpace measureH Profile)
open UnforcedLeray.B0223 (MeridC)

/-- **The real part of `P_ε z` is solenoidal in `H`** (source 1675-1677; `PartIIa.solenoidalHC`
is the orthogonal complement of the complexified chart gradients `cgrad ε Φ`, and for a real
chart form `wk` the complex pairing `⟪cgrad ε Φ, merC ∘ wk ∘ cellPt⟫` is the real pairing, so
`b = wk ∘ cellPt` is orthogonal to the real gradients `profileGradH ε c Φ`): there is a real
`b ∈ HSpace c Merid`, `b ∈ B0226.solenoidalH ε c`, with `b = wk ∘ cellPt` a.e. -/
def PepsRealMember : Prop :=
  ∀ (p : Params) (z : HSpace p.c MeridC) (wk : Chart → Merid),
    ChartRep p.c (UnforcedLeray.Short.PartIIa.PepsC p.ε p.c z) wk →
      ∃ b : HSpace p.c Merid, b ∈ UnforcedLeray.B0226.solenoidalH p.ε p.c ∧
        (b : Profile → Merid) =ᵐ[measureH p.c] fun q => wk (cellPt p.c q)

/-- **The physical pairing with the lift** (the `liftVec` ↔ `velPhys` dictionary, source
1339-1362, 4139-4146; `τ = 2εq + log s`, `y = (R/√s, 0, η/√s)`, `R = ε⁻¹`): if the real
`b ∈ H` is the chart coefficient of `wk` (a.e.), then there is a constant `κ` such that for every
complex phase test `φ` the pairing `⟨∇φ, velPhys wk⟩` is `κ(⟪J_ε b, ∇ₓφ₁⟫ + i⟪J_ε b, ∇ₓφ₂⟫)`
for suitable real physical tests `φ₁, φ₂` (the real and imaginary parts of `φ`, with the
arguments `(τ, y)` swapped to `(y, τ)`). -/
def PairWithLift : Prop :=
  ∀ (p : Params) (wk : Chart → Merid) (b : HSpace p.c Merid),
    (b : Profile → Merid) =ᵐ[measureH p.c] (fun q => wk (cellPt p.c q)) →
    ∃ κ : ℂ, ∀ φ : ℝ × Space → ℂ, IsPhaseTest (2 * p.ε * p.c) φ →
      ∃ φ₁ φ₂ : UnforcedLeray.B0226.PhysTest p.ε p.c,
        pairF (2 * p.ε * p.c) (gradT φ) (velPhys p.ε⁻¹ p.c wk) =
          κ * (((inner ℝ (UnforcedLeray.B0220.J p.ε_pos p.c_pos b)
                  (UnforcedLeray.B0226.physGrad p.ε p.c φ₁) : ℝ) : ℂ) +
            Complex.I * ((inner ℝ (UnforcedLeray.B0220.J p.ε_pos p.c_pos b)
                  (UnforcedLeray.B0226.physGrad p.ε p.c φ₂) : ℝ) : ℂ))

theorem pepsSolenoidal_of (h1 : PepsRealMember) (h2 : PairWithLift) : PepsSolenoidal := by
  intro p z wk hwk φ hφ
  obtain ⟨b, hb, hbwk⟩ := h1 p z wk hwk
  obtain ⟨κ, hκ⟩ := h2 p wk b hbwk
  obtain ⟨φ₁, φ₂, hpair⟩ := hκ φ hφ
  have hJ := UnforcedLeray.B0226.J_mem_of_solenoidalH p.ε_pos p.c_pos hb
  have e1 := (UnforcedLeray.B0226.mem_orthogonal_span_range _ _).1 hJ φ₁
  have e2 := (UnforcedLeray.B0226.mem_orthogonal_span_range _ _).1 hJ φ₂
  rw [hpair, e1, e2]
  simp

end UnforcedLeray.Short.PartIIIb.NearInst
