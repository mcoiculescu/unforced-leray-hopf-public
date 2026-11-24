import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.RADefs

/-!
# `PartIII-b:C/asrc/ra/6` : `RAPhysAxi` from equivariance and periodicity leaves

Source of record: `the November 2 reference manuscript` (73 pages), 121-124
(axisymmetry without swirl = invariance under the linear isometries fixing `e₃`), 2666-2668,
4995-4997.

`RAPhysAxi` is reduced to:

* `RALiftsEquiv` : `ĥ_A`, `F_A+E_A` (lifts) are `g`-equivariant and `sΨ_A` is `g`-invariant for every
  linear isometry `g` fixing `e₃` (the ring lift `Nv` of a meridional coefficient; source 4979-4981);
* `PhysDmuEquiv`, `PhysDivSymEquiv`, `PhysGradEquiv` : the operators `D_μ`, `div(a⊗b+b⊗a)`, `∇`
  commute with `g` on fields of the stated smoothness (chain rule for linear isometries);
* `AxiNoSwirlOfEquiv` : a field equivariant under every `g` fixing `e₃` is `AxiNoSwirl`
  (rotation taking `meridPt y` to `y`; source 121-124, 4161);
* `RALiftsPer` : `ĥ_A`, `F_A+E_A`, `sΨ_A` are `2c/R`-periodic in the phase (`nvPerExt_periodic`,
  `chart_add_period`, reindexing `j ↦ j-1` of the lattice sums).

The `τ`-periodicity of `D_μ`, `div`, `∇` of periodic fields is proved here.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest Params)

/-- Source 4979-4981, 5024: the lifts `ĥ_A`, `F_A + E_A` of meridional coefficients are
equivariant, and `sΨ_A` invariant, under every linear isometry `g` of `ℝ³` fixing `e₃`
(`age`, the chart variables are `g`-invariant, `eR (g y) = g (eR y)`, `e_z` fixed). -/
def RALiftsEquiv (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  IsSourceCutoffC χf → ∀ (ν μ ε : ℝ), 0 < ν → 0 < ε → ∀ A : ℝ → Mat3, IsAffElem as A →
    ∀ g : Space ≃ₗᵢ[ℝ] Space, UnforcedLeray.FixesAxis g →
      (∀ τ y, hLift ν ε (cOf ν) χf A τ (g y) = g (hLift ν ε (cOf ν) χf A τ y)) ∧
      (∀ τ y, feLift ν μ ε (cOf ν) χf A τ (g y) = g (feLift ν μ ε (cOf ν) χf A τ y)) ∧
      (∀ τ y, psiLift ν ε χf A τ (g y) = psiLift ν ε χf A τ y)

/-- `D_μ` commutes with a linear isometry on jointly `C²` equivariant fields (source 4140-4141). -/
def PhysDmuEquiv : Prop :=
  ∀ (ν μ : ℝ) (g : Space ≃ₗᵢ[ℝ] Space) (X : ℝ → Space → Space),
    ContDiff ℝ 2 (fun x : ℝ × Space => X x.1 x.2) → (∀ τ y, X τ (g y) = g (X τ y)) →
      ∀ τ y, physDmu ν μ X τ (g y) = g (physDmu ν μ X τ y)

/-- `div(a⊗b + b⊗a)` commutes with a linear isometry on `C¹` equivariant fields. -/
def PhysDivSymEquiv : Prop :=
  ∀ (g : Space ≃ₗᵢ[ℝ] Space) (a b : Space → Space), ContDiff ℝ 1 a → ContDiff ℝ 1 b →
    (∀ y, a (g y) = g (a y)) → (∀ y, b (g y) = g (b y)) →
      ∀ y, physDivSym a b (g y) = g (physDivSym a b y)

/-- `∇q` commutes with a linear isometry for `g`-invariant scalars. -/
def PhysGradEquiv : Prop :=
  ∀ (g : Space ≃ₗᵢ[ℝ] Space) (q : Space → ℝ), (∀ y, q (g y) = q y) →
    ∀ y, physGrad q (g y) = g (physGrad q y)

/-- A phase-dependent field equivariant under every linear isometry fixing `e₃` is axisymmetric
without swirl in the sense `AxiNoSwirl` (source 121-124, 4161): the rotation about `e₃` taking
`meridPt y` to `y` gives `F τ y = frameL y (F τ (meridPt y))`, and the reflection `y₁ ↦ -y₁` fixes
`meridPt y` so the azimuthal component of `F τ (meridPt y)` vanishes. -/
def AxiNoSwirlOfEquiv : Prop :=
  ∀ F : ℝ → Space → Space,
    (∀ g : Space ≃ₗᵢ[ℝ] Space, UnforcedLeray.FixesAxis g → ∀ τ y, F τ (g y) = g (F τ y)) →
      AxiNoSwirl F

/-- Source 4995-4997, 2666-2668: `ĥ_A`, `F_A+E_A`, `sΨ_A` are `2c/R`-periodic in the phase
(`nvPerExt_periodic`, `chart_add_period`; `sΨ_A` by the `c`-periodicity of `Ψ_A` in `q`). -/
def RALiftsPer (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  IsSourceCutoffC χf → ∀ (ν μ ε : ℝ), 0 < ν → 0 < ε → ∀ A : ℝ → Mat3, IsAffElem as A →
    (∀ τ y, hLift ν ε (cOf ν) χf A (τ + 2 * cOf ν / ε⁻¹) y = hLift ν ε (cOf ν) χf A τ y) ∧
    (∀ τ y, feLift ν μ ε (cOf ν) χf A (τ + 2 * cOf ν / ε⁻¹) y = feLift ν μ ε (cOf ν) χf A τ y) ∧
    (∀ τ y, psiLift ν ε χf A (τ + 2 * cOf ν / ε⁻¹) y = psiLift ν ε χf A τ y)

theorem deriv_shift_of_periodic {f : ℝ → Space} {P : ℝ} (hf : ∀ t, f (t + P) = f t) (τ : ℝ) :
    deriv f (τ + P) = deriv f τ := by
  have h : (fun t => f (t + P)) = f := funext hf
  have := deriv_comp_add_const (f := f) (a := P) (x := τ)
  rw [h] at this
  exact this.symm

theorem contDiff_slice {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {n : WithTop ℕ∞} (f : ℝ → E → F)
    (h : ContDiff ℝ n (fun x : ℝ × E => f x.1 x.2)) (τ : ℝ) : ContDiff ℝ n (f τ) :=
  h.comp (contDiff_const.prodMk contDiff_id)

theorem raPhysAxi_of (as : ℝ) (χf : ℝ → ℝ) (h0 : AffineLiftReg as χf)
    (hL : RALiftsEquiv as χf) (hD : PhysDmuEquiv) (hS : PhysDivSymEquiv) (hG : PhysGradEquiv)
    (hA : AxiNoSwirlOfEquiv) (hP : RALiftsPer as χf) : RAPhysAxi as χf := by
  intro hχ ν μ ε hν hε U hUax hU1 hUper A hAe
  obtain ⟨hh2, hpsi1, hfe⟩ := h0 hχ ν μ ε hν hε A hAe
  have hh2' : ∀ τ, ContDiff ℝ 2 (hLift ν ε (cOf ν) χf A τ) := contDiff_slice _ hh2
  have hpsi' : ∀ τ, ContDiff ℝ 1 (psiLift ν ε χf A τ) := contDiff_slice _ hpsi1
  have hU' : ∀ τ, ContDiff ℝ 1 (U τ) := contDiff_slice _ hU1
  have hper : 2 * cOf ν / ε⁻¹ = 2 * ε * cOf ν := by rw [div_inv_eq_mul]; ring
  have heq : ∀ τ y, rAPhys ν μ ε (cOf ν) χf U A τ y =
      physDmu ν μ (hLift ν ε (cOf ν) χf A) τ y + physDivSym (U τ) (hLift ν ε (cOf ν) χf A τ) y -
        feLift ν μ ε (cOf ν) χf A τ y - physGrad (psiLift ν ε χf A τ) y := fun _ _ => rfl
  constructor
  · apply hA
    intro g hg τ y
    obtain ⟨e1, e2, e3⟩ := hL hχ ν μ ε hν hε A hAe g hg
    have eU : ∀ y, U τ (g y) = g (U τ y) := by
      intro y
      have := hUax τ g hg (g y)
      simpa using this.symm
    rw [heq, heq, map_sub, map_sub, map_add,
      hD ν μ g _ hh2 e1 τ y, hS g _ _ (hU' τ) ((hh2' τ).of_le (by norm_num)) eU (e1 τ) y, e2 τ y,
      hG g _ (e3 τ) y]
  · intro τ y
    obtain ⟨p1, p2, p3⟩ := hP hχ ν μ ε hν hε A hAe
    rw [heq, heq]
    have hUp : U (τ + 2 * cOf ν / ε⁻¹) = U τ := by
      funext z; rw [hper]; exact hUper τ z
    have hp1 : hLift ν ε (cOf ν) χf A (τ + 2 * cOf ν / ε⁻¹) = hLift ν ε (cOf ν) χf A τ :=
      funext (p1 τ)
    have hp3 : psiLift ν ε χf A (τ + 2 * cOf ν / ε⁻¹) = psiLift ν ε χf A τ := funext (p3 τ)
    have hDm : physDmu ν μ (hLift ν ε (cOf ν) χf A) (τ + 2 * cOf ν / ε⁻¹) y =
        physDmu ν μ (hLift ν ε (cOf ν) χf A) τ y := by
      unfold physDmu
      rw [hp1, deriv_shift_of_periodic (f := fun t => hLift ν ε (cOf ν) χf A t y)
        (fun t => p1 t y) τ]
    rw [hDm, hUp, hp1, p2 τ y, hp3]
end UnforcedLeray.Short.PartIIIb.Concrete
