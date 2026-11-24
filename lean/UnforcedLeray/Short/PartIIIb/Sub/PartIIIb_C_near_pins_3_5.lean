import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Sub.PartIIIb_C_near_pins_3

/-!
# `RepsVecSolenoidal` decomposed (task `PartIII-b:C/near/pins/3/5`)

Source `the November 2 reference manuscript`:
1675-1677 (`R_ε^vec(μ) = (μ - A_ε)⁻¹`), 2666-2668 and 2683 (the chart `s = R²/ρ²`,
`q = R log(ρ/R) + Rτ/2`, `η = Rz/ρ` of the similarity variable `y`, `R = ε⁻¹`, and the lift
`𝒩_v b = √s b`), 1339-1362 (the free Cartesian operator acts componentwise and commutes with `∇`),
4139-4146.

Plan.  Work in the periodic `L²` space `X = L²(dx dτ; ℂ³)` of `B0223`, where the lift `J = liftVec`
lives and the outer semigroup `S_ε(t)` acts.  Its spatial variable is the unit-ring variable
`x = εy` (`B0220` chart `s = |x'|⁻²`, `q = ε⁻¹ log|x'| + τ/(2ε)`, `η = x₃/(ε|x'|)`), while
`velPhys` (`𝒩_v`) and the weak formulation `IsWeakSolenoidal` live in the similarity variable `y`.
A field `F ∈ X` is *weakly solenoidal* (`XSol`) if `⟨∇φ, F⟩ = 0` for all phase tests `φ` (`pairX`).
Then
* (`DictVel`) `velPhys ε⁻¹ c f` at `(τ, y)` is a fixed nonzero multiple of the representative of
  `J g` at `(τ, εy)` (`ChartRep g f`);
* (`XSolDil`) `XSol F` iff the dilated representative `(τ, y) ↦ F(εy, τ)` is weakly solenoidal, so
  `IsWeakSolenoidal (velPhys f) ↔ XSol (J g)`;
* (`J_RepsVec`, proved in `B0223`) `J R_ε^vec(μ) = physRes μ J`;
* (`PhysResSol`) `physRes μ = ∫ e^{-μt} S(t) dt` preserves `XSol`.  It follows from
  `PairXCont` (`F ↦ ⟨∇φ, F⟩` is a bounded functional on `X`, so commutes with the Bochner integral)
  and `XSolSemigroup` (`S(t)` preserves `XSol`), the latter from
  `SemigroupAdjointGrad` (`⟨∇φ, S(t)F⟩ = ⟨∇χ, F⟩`, `χ` a rescaled heat-smoothing of `φ`, in
  `L²` with `∇χ ∈ L²`; source 1339-1362 and the formula `S_formula` of `B0223`) and `XSolExtend`
  (weak solenoidality extends from compactly supported tests to `H¹`-type tests by cutoff).

Proved here: `pairF_congr_ae`, `pairF_smul`, `xSolSemigroup_of`, `physResSol_of`,
`repsVecSolenoidal_of`.  Leaves: `DictVel`, `PairXCont`, `XSolExtend`, `SemigroupAdjointGrad`,
`XSolDil`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.NearInst

open UnforcedLeray.Short.PartIIIb.Concrete UnforcedLeray.Cons.C03.Concrete
  UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.B0220 (HSpace measureH Profile)
open UnforcedLeray.B0223 (MeridC SpaceC X PSpace outerS physRes liftVec)

/-- The function on `ℝ × ℝ³` (periodically extended in the phase) represented by `F ∈ X`. -/
def repX (P : ℝ) [Fact (0 < P)] (F : X SpaceC P) : ℝ × Space → CVec3 :=
  fun x => (F : PSpace P → SpaceC) (x.2, (x.1 : AddCircle P))

/-- The pairing `⟨Φ, F⟩ = P⁻¹∫₀ᴾ∫ Φ · F` of a test with an element of `X`. -/
def pairX (P : ℝ) [Fact (0 < P)] (Φ : ℝ × Space → CVec3) (F : X SpaceC P) : ℂ :=
  pairF P Φ (repX P F)

/-- `F ∈ X` is weakly solenoidal: `⟨∇φ, F⟩ = 0` for every scalar phase test `φ`. -/
def XSol (P : ℝ) [Fact (0 < P)] (F : X SpaceC P) : Prop :=
  ∀ φ : ℝ × Space → ℂ, IsPhaseTest P φ → pairX P (gradT φ) F = 0

/-- Smooth `P`-periodic scalar functions with `χ, ∇χ ∈ L²(dy dτ)` over one period. -/
def IsL2Test (P : ℝ) (χ : ℝ × Space → ℂ) : Prop :=
  ContDiff ℝ ∞ χ ∧ (∀ τ y, χ (τ + P, y) = χ (τ, y)) ∧
    IntegrableOn (fun x : ℝ × Space => ‖χ x‖ ^ 2 + ‖gradT χ x‖ ^ 2) (Ioc (0 : ℝ) P ×ˢ univ)

/-- **Leaf 1 (dictionary)** (source 2666-2668, 2683, 1640-1641, 1675-1677; `Axi.Nv`,
`B0223.coeFn_liftVec`): for the real chart field `f` of `g ∈ H`, the physical velocity
`velPhys ε⁻¹ c f` at `(τ, y)` is a fixed nonzero real multiple `κ = κ(p)` of the (periodically
extended) representative of the lift `J_ε g ∈ X` at `(τ, εy)`, almost everywhere on `ℝ × ℝ³`.
The lift lives in the unit-ring variable `x = εy`:
`J_ε b (x, τ) = (√(2π) ε)⁻¹ |x'|⁻¹ (b_r e_r + b_z e_z)` at the `B0220` chart point
`(|x'|⁻², ε⁻¹ log|x'| + τ/(2ε), x₃/(ε|x'|))`.  At `x = εy` this is the chart point
`(R²/ρ², R log(ρ/R) + Rτ/2, Rz/ρ)` of `y` (2666-2668; `q` mod `c`, which `periodize` and
`perExt` both see, and `ChartRep` recentres by `cellPt`), and `|x'|⁻¹ = R/ρ = √s`, against
`𝒩_v b = √s (b_r e_r + b_z e_z)` (2683), `R = ε⁻¹`.  So `κ = √(2π) ε`. -/
def DictVel : Prop :=
  ∀ p : Params, ∃ κ : ℝ, κ ≠ 0 ∧
    ∀ (g : HSpace p.c MeridC) (f : Chart → Merid), ChartRep p.c g f →
      velPhys p.ε⁻¹ p.c f =ᵐ[volume]
        fun x => (κ : ℂ) • repX p.period (liftVec (P := p.period) p.ε_pos p.c_pos rfl g)
          (x.1, p.ε • x.2)

/-- **Leaf 2 (bounded functional)** (source 1339-1362): for a phase test `φ` (smooth, periodic,
compact in `y`) the pairing `F ↦ ⟨∇φ, F⟩` is a bounded linear functional on `X`
(Cauchy-Schwarz on one period; `∇φ` is bounded with bounded support). -/
def PairXCont : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (φ : ℝ × Space → ℂ), IsPhaseTest P φ →
    ∃ ℓ : X SpaceC P →L[ℂ] ℂ, ∀ F : X SpaceC P, ℓ F = pairX P (gradT φ) F

/-- **Leaf 3 (cutoff extension)**: weak solenoidality, tested against compactly supported phase
tests, extends to tests `χ` with `χ, ∇χ ∈ L²` (`θ_R(y) = θ(y/R)`, `φ_R = θ_R χ`,
`∇φ_R = θ_R ∇χ + χ ∇θ_R → ∇χ` in `L²`, `F ∈ L²`). -/
def XSolExtend : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (F : X SpaceC P), XSol P F →
    ∀ χ : ℝ × Space → ℂ, IsL2Test P χ → pairX P (gradT χ) F = 0

/-- **Leaf 4 (adjoint of the outer semigroup on gradient tests)** (source 1339-1362; `B0223.S_formula`:
`S_ε(t)F(x,τ) = e^{t/2}[e^{νε²(e^t-1)Δ}F(·,τ-t)](e^{t/2}x)`): for a phase test `φ` and `t ≥ 0`
there is `χ ∈ IsL2Test` (`χ = e^{-t/2} G_{νε²(e^t-1)} * φ(e^{-t/2}·, · + t)`, a Gaussian
smoothing of a compactly supported test) with `⟨∇φ, S(t)F⟩ = ⟨∇χ, F⟩` for all `F ∈ X`
(change of variables `y = e^{t/2}x` and Fubini; the heat kernel is even and acts componentwise, so
commutes with `∇`). -/
def SemigroupAdjointGrad : Prop :=
  ∀ (ν ε : ℝ) (hν : 0 < ν), 0 < ε → ∀ (P : ℝ) [Fact (0 < P)] (t : ℝ), 0 ≤ t →
    ∀ φ : ℝ × Space → ℂ, IsPhaseTest P φ →
      ∃ χ : ℝ × Space → ℂ, IsL2Test P χ ∧ ∀ F : X SpaceC P,
        pairX P (gradT φ) ((outerS (E := SpaceC) (P := P) hν ε).T t F) = pairX P (gradT χ) F

/-- **Leaf 5 (dilation `x = εy`)** (source 2666-2668, 1675-1677: the outer space `X` of the lift
uses the unit-ring variable `x = εy`, the weak formulation the similarity variable `y`): for
`ε > 0`, `F ∈ X` is weakly solenoidal iff its dilated representative `(τ, y) ↦ F(εy, τ)` is.
Phase tests correspond by `φ(τ, y) = ψ(τ, εy)` (smooth, `P`-periodic, bounded support in `y`),
`∇φ(τ, y) = ε (∇ψ)(τ, εy)`, and `∫ h(εy) dy = ε⁻³ ∫ h(x) dx`, so
`⟨∇φ, F(·, ε·)⟩ = ε⁻² ⟨∇ψ, F⟩`. -/
def XSolDil : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (ε : ℝ), 0 < ε → ∀ F : X SpaceC P,
    (XSol P F ↔ IsWeakSolenoidal P (fun x => repX P F (x.1, ε • x.2)))

/-- The outer semigroup preserves weak solenoidality. -/
def XSolSemigroup : Prop :=
  ∀ (ν ε : ℝ) (hν : 0 < ν), 0 < ε → ∀ (P : ℝ) [Fact (0 < P)] (t : ℝ), 0 ≤ t →
    ∀ F : X SpaceC P, XSol P F → XSol P ((outerS (E := SpaceC) (P := P) hν ε).T t F)

/-- The physical resolvent preserves weak solenoidality. -/
def PhysResSol : Prop :=
  ∀ (ν ε : ℝ) (hν : 0 < ν), 0 < ε → ∀ (P : ℝ) [Fact (0 < P)] (μ : ℂ), 0 < μ.re + 1 / 4 →
    ∀ F : X SpaceC P, XSol P F → XSol P (physRes (E := SpaceC) (P := P) hν ε μ F)

theorem pairF_congr_ae {P : ℝ} {Φ u v : ℝ × Space → CVec3} (h : u =ᵐ[volume] v) :
    pairF P Φ u = pairF P Φ v := by
  unfold pairF phaseInt
  congr 1
  have h1 : ∀ᵐ x : ℝ × Space ∂(volume : Measure (ℝ × Space)), dotL (Φ x) (u x) = dotL (Φ x) (v x) :=
    h.mono fun x hx => by rw [hx]
  have h2 := Measure.ae_ae_of_ae_prod h1
  refine integral_congr_ae ?_
  exact ae_restrict_of_ae (h2.mono fun t ht => integral_congr_ae ht)

theorem pairF_smul {P : ℝ} (k : ℂ) (Φ u : ℝ × Space → CVec3) :
    pairF P Φ (fun x => k • u x) = k * pairF P Φ u := by
  unfold pairF phaseInt
  simp only [map_smul, smul_eq_mul, integral_const_mul]
  rw [mul_smul_comm]

theorem xSolSemigroup_of (hE : XSolExtend) (hA : SemigroupAdjointGrad) : XSolSemigroup := by
  intro ν ε hν hε P _ t ht F hF φ hφ
  obtain ⟨χ, hχ, hχF⟩ := hA ν ε hν hε P t ht φ hφ
  rw [hχF F]
  exact hE P F hF χ hχ

theorem physResSol_of (hC : PairXCont) (hS : XSolSemigroup) : PhysResSol := by
  intro ν ε hν hε P _ μ hμ F hF φ hφ
  obtain ⟨ℓ, hℓ⟩ := hC P φ hφ
  have hω := UnforcedLeray.B0223.omega_lt (E := SpaceC) (P := P) hμ hν ε
  rw [← hℓ]
  unfold physRes
  have hint : Integrable (fun t : ℝ => Complex.exp (-(μ * t)) •
      (outerS (E := SpaceC) (P := P) hν ε).T t F) (volume.restrict (Ioi (0 : ℝ))) :=
    (outerS (E := SpaceC) (P := P) hν ε).integrableOn_lapInt hω F
  rw [(outerS (E := SpaceC) (P := P) hν ε).laplace_apply hω]
  refine (ContinuousLinearMap.integral_comp_comm ℓ hint).symm.trans ?_
  refine setIntegral_eq_zero_of_forall_eq_zero fun t ht => ?_
  have ht' : (0 : ℝ) ≤ t := le_of_lt ht
  have h0 := hS ν ε hν hε P t ht' F hF φ hφ
  rw [map_smul, hℓ, h0, smul_zero]

/-- The pairing of a gradient test with `velPhys f` is `κ` times its pairing with the dilated
representative of the lift (`DictVel`, `pairF_congr_ae`, `pairF_smul`). -/
theorem pairF_velPhys_of_dict {p : Params} {κ : ℝ}
    (hdict : ∀ (g : HSpace p.c MeridC) (f : Chart → Merid), ChartRep p.c g f →
      velPhys p.ε⁻¹ p.c f =ᵐ[volume]
        fun x => (κ : ℂ) • repX p.period (liftVec (P := p.period) p.ε_pos p.c_pos rfl g)
          (x.1, p.ε • x.2))
    (g : HSpace p.c MeridC) (f : Chart → Merid) (hgf : ChartRep p.c g f) (φ : ℝ × Space → ℂ) :
    pairF (2 * p.ε * p.c) (gradT φ) (velPhys p.ε⁻¹ p.c f) =
      (κ : ℂ) * pairF p.period (gradT φ)
        (fun x => repX p.period (liftVec (P := p.period) p.ε_pos p.c_pos rfl g) (x.1, p.ε • x.2)) := by
  rw [pairF_congr_ae (hdict g f hgf), pairF_smul]
  rfl

theorem repsVecSolenoidal_of (hD : DictVel) (hR : PhysResSol) (hX : XSolDil) :
    RepsVecSolenoidal := by
  intro p μ hP hμ γ z wz w hz hw hsol
  obtain ⟨κ, hκ, hdict⟩ := hD p
  have hκc : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ
  have hγ : 0 < ((μ : ℂ)).re + 1 / 4 := by simp; linarith
  have hWz : IsWeakSolenoidal p.period
      (fun x => repX p.period (liftVec (P := p.period) p.ε_pos p.c_pos rfl z) (x.1, p.ε • x.2)) := by
    intro φ hφ
    have h3 := hsol φ hφ
    rw [pairF_velPhys_of_dict hdict z wz hz φ] at h3
    exact (mul_eq_zero.1 h3).resolve_left hκc
  have hXz : XSol p.period (liftVec (P := p.period) p.ε_pos p.c_pos rfl z) :=
    (hX p.period p.ε p.ε_pos _).2 hWz
  have hXw : XSol p.period (liftVec (P := p.period) p.ε_pos p.c_pos rfl
      (UnforcedLeray.B0223.RepsVec (P := p.period) p.ν_pos p.ε_pos p.c_pos rfl (μ : ℂ) z)) := by
    rw [UnforcedLeray.B0223.J_RepsVec (P := p.period) p.ν_pos p.ε_pos p.c_pos rfl hγ z]
    exact hR p.ν p.ε p.ν_pos p.ε_pos p.period (μ : ℂ) hγ _ hXz
  have hWw := (hX p.period p.ε p.ε_pos _).1 hXw
  intro φ hφ
  rw [pairF_velPhys_of_dict hdict _ (w : Chart → Merid) hw φ, hWw φ hφ, mul_zero]

end UnforcedLeray.Short.PartIIIb.NearInst
