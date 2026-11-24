import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Defs

/-!
# The six identities behind `WardPointwiseIdentity` (source 4225-4258)

Source: `the November 2 reference manuscript`.
Product rule (4228-4231), convection cancellation (4232-4236), pressure identity (4237-4240),
and the divergence bookkeeping (`div` of symmetrized products, solenoidality of `[U,X]` and of
`D_μX`) used to turn `u·∇h + h·∇u` into `div(u⊗h + h⊗u)` (4258).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Product rule (source 4228-4231): `D_μ[U,X] = [D₀U, X] + [U, D_{μ+1}X] - 2νC_diff`
for jointly smooth `U, X`. -/
def PwProduct (ν μ : ℝ) : Prop :=
  ∀ U X : ℝ → Space → Space,
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ × Space => U x.1 x.2) →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ × Space => X x.1 x.2) →
    ∀ τ y,
      physDmu ν μ (fun τ' y' => physBracket (U τ') (X τ') y') τ y =
        physBracket (physDmu ν 0 U τ) (X τ) y +
          physBracket (U τ) (physDmu ν (μ + 1) X τ) y - (2 * ν) • physCdiff (U τ) (X τ) y

/-- Convection cancellation (source 4232-4236): with `N = u·∇u`, `h = [u, X]`,
`-[N, X] + u·∇h + h·∇u = (u⊗u):D²X`. -/
def PwConvection : Prop :=
  ∀ u X : Space → Space,
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) X →
    ∀ y, -(physBracket (fun y' => fderiv ℝ u y' (u y')) X y) +
        fderiv ℝ (physBracket u X) y (u y) + fderiv ℝ u y (physBracket u X y) =
      physUUD2 u X y

/-- Pressure identity (source 4237-4240): `-[∇q, X] = ∇(X·∇q) - (DX + DXᵀ)∇q`. -/
def PwPressure : Prop :=
  ∀ (X : Space → Space) (q : Space → ℝ),
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) X → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) q →
    ∀ y, -(physBracket (physGrad q) X y) =
      physGrad (fun y' => ∑ j : Fin 3, X y' j * physGrad q y' j) y - physDXp X q y

/-- Divergence of the symmetrized product of two solenoidal fields (source 4258):
`div(a⊗b + b⊗a) = a·∇b + b·∇a`. -/
def PwDivSym : Prop :=
  ∀ a b : Space → Space,
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) a → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) b →
    (∀ y, ∑ j : Fin 3, physPd a j y j = 0) → (∀ y, ∑ j : Fin 3, physPd b j y j = 0) →
    ∀ y, physDivSym a b y = fderiv ℝ b y (a y) + fderiv ℝ a y (b y)

/-- The bracket of solenoidal fields is solenoidal (source 4258). -/
def PwBracketDivFree : Prop :=
  ∀ a b : Space → Space,
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) a → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) b →
    (∀ y, ∑ j : Fin 3, physPd a j y j = 0) → (∀ y, ∑ j : Fin 3, physPd b j y j = 0) →
    ∀ y, ∑ j : Fin 3, physPd (physBracket a b) j y j = 0

/-- `D_μ` preserves solenoidality (it commutes with `div` up to the Euler term
`y·∇ div X + div X`). -/
def PwDmuDivFree (ν μ : ℝ) : Prop :=
  ∀ X : ℝ → Space → Space,
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ × Space => X x.1 x.2) →
    (∀ τ y, ∑ j : Fin 3, physPd (X τ) j y j = 0) →
    ∀ τ y, ∑ j : Fin 3, physPd (physDmu ν μ X τ) j y j = 0

end UnforcedLeray.Short.PartIIIb.Concrete
