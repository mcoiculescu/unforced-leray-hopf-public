import UnforcedLeray.Short.PartIIIa.Sub.T18_3_1

/-!
# Part III-a, task `PartIII-a:T18/3/1/3` (`LionsMagenesCyl`): the split

Status: BLOCKED (SIZE XL). This file does NOT prove `LionsMagenesCyl`. It states the three finer
Props of the split and proves the reduction `LionsMagenesCyl ⇐ (a) ∧ (b) ∧ (c)`:

* (a) `HasLMMollifier`: for every period `c > 0` there is a family `J k` of mollifiers on the
  vector fields on the cylinder with the properties of `IsLMMollifier` (smooth periodic output,
  linearity on `L²(cell)`, self-adjointness and contraction on `L²(cell)`, commutation with the
  weak `∂_q, ∂_η`, preservation of smooth `c`-periodic divergence-free fields, strong convergence
  `J_k f → f`,
  boundedness `L²(cell) → L²(cell)`, joint measurability in a parameter `s`, `L²`-boundedness of
  `∂ⱼ J_k` for each `k` (`gradL2`) and `J_k` of a weakly divergence-free field is divergence free
  (`divFreeWeak`); both by Young's inequality, `y ↦ K_k(x-y)` being a test function).
  Mathematics: a periodic convolution with an even nonnegative smooth kernel of unit mass and
  support shrinking to `0`, acting componentwise.
* (b) `MollifiedEnergyIdentity`: for every standing datum and every mollifier family, the energy
  identity holds for the mollified energies `E_k(s) = ∫_cell |J_k b(s)|²`,
  `N_k(s) = ∫_cell |∇J_k b(s)|²`, `R_k(s) = ∫_cell Re⟨F(s), ∇J_k² b(s)⟩`:
  `∫ w' E_k = ∫ w (2 Re μ s⁻¹ E_k + 2ν N_k + 2R_k)`. Mathematics: `u_k(s) = J_k b(s)` has the
  `H`-valued weak time derivative `-(μ/s) u_k + νΔu_k + J_k 𝒫₀ div F` (test `ExtWeakH1` with
  `φ = J_k φ₀`, self-adjointness, commutation with `∂`); `HasWeakDerivTime.weighted_norm_sq_sub`
  (`Lib/BochnerTime/Energy.lean`) with compact support of `w` in `(0,∞)`; the pairings
  `⟨Δu_k, u_k⟩ = -‖∇u_k‖²` and `⟨J_k 𝒫₀ div F, u_k⟩ = -⟨F, ∇J_k² b⟩`.
* (c) `MollifiedEnergyLimit`: for every `w` with compact support in `(0,∞)` the two integrals in
  (b) converge, as `k → ∞`, to the corresponding integrals of `CoreIdentity` (`energyE`, `energyN`,
  `energyR`). Mathematics: strong convergence `J_k b(s) → b(s)` and `J_k ∇b(s) → ∇b(s)` in
  `L²(cell)` for every `s > 0` (`∇b(s)` is the weak gradient `G(s)` of `weakGrad`), contraction
  bounds `E_k ≤ E`, `N_k ≤ N` and dominated convergence in `s` on `supp w` (Tonelli for `E`, `N`,
  `energyLoc`, `L2locTensor` for `F`).

The reduction is the uniqueness of limits: the sequence of left-hand sides of (b) converges to
`∫ w' E` by (c), the sequence of right-hand sides converges to `∫ w (2Re μ s⁻¹ E + 2ν N + 2R)`, and
they agree termwise by (b), so the two limits coincide. Source of record:
`the November 2 reference manuscript`, lines 3541-3552 (the energy identity) and
3427-3440.

Finer than (a)-(c): (b) is itself the composition of the `H`-valued weak derivative (not yet
formalised: `u_k` lives in `Lp` of the cell, not in the raw function space used here), the
pairings, and the generic energy identity `HasWeakDerivTime.weighted_norm_sq_sub`; (c) is the
dominated convergence. The Lean names of these pieces are listed in the report.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- A complex spatial field on the plane, with values in `ℂ²`. -/
abbrev LMSpField := ℝ × ℝ → Fin 2 → ℂ

/-- `f ∈ L²(cell)` componentwise. -/
def LMCellL2 (c : ℝ) (f : LMSpField) : Prop :=
  ∀ i : Fin 2, MemLp (fun x => f x i) 2 (volume.restrict (B0579.cell c))

/-- Partial derivative of a complex function on the plane, through the real and imaginary parts of
`B0579.pd`. -/
def LMPd (j : Fin 2) (f : ℝ × ℝ → ℂ) (x : ℝ × ℝ) : ℂ :=
  ((B0579.pd j (fun y => (f y).re) x : ℝ) : ℂ) +
    Complex.I * ((B0579.pd j (fun y => (f y).im) x : ℝ) : ℂ)

/-- `g` is the weak `j`-th derivative of `f` on the cylinder: both are in `L²(cell)`, and
`∫_cell f ∂_j φ = -∫_cell g φ` for every smooth real `φ`, `c`-periodic in `q`, with compact
support in `η`. -/
def LMWeakPd (c : ℝ) (j : Fin 2) (f g : ℝ × ℝ → ℂ) : Prop :=
  MemLp f 2 (volume.restrict (B0579.cell c)) ∧ MemLp g 2 (volume.restrict (B0579.cell c)) ∧
    ∀ φ : ℝ × ℝ → ℝ, ContDiff ℝ ∞ φ → (∀ x : ℝ × ℝ, φ (x.1 + c, x.2) = φ x) →
      (∃ R : ℝ, ∀ x : ℝ × ℝ, R < |x.2| → φ x = 0) →
      ∫ x in B0579.cell c, f x * (B0579.pd j φ x : ℂ) = -∫ x in B0579.cell c, g x * (φ x : ℂ)

/-- **Classical derivatives of smooth periodic fields are weak derivatives** (integration by parts
on the cell `[-c/2, c/2) × ℝ`; source `the November 2 reference manuscript`
3427-3440, the energy class with `∇b ∈ L²`, used for the mollified fields `J_k b(s)` of the energy
identity, 3541-3552): if `f` is smooth and `c`-periodic in `q`, and `f` and its classical partial
derivative `LMPd j f` lie in `L²(cell)`, then `LMPd j f` is the weak `j`-th derivative of `f` in
the sense of `LMWeakPd`. Against a smooth test `φ`, `c`-periodic in `q` and vanishing for `|η|`
large, the boundary terms vanish: at `q = ±c/2` by periodicity of `f φ`, at `|η| → ∞` by the
`η`-support of `φ`. -/
def LMSmoothWeakPd : Prop :=
  ∀ c : ℝ, 0 < c → ∀ (j : Fin 2) (f : ℝ × ℝ → ℂ), ContDiff ℝ ∞ f →
    (∀ x : ℝ × ℝ, f (x.1 + c, x.2) = f x) →
    MemLp f 2 (volume.restrict (B0579.cell c)) →
    MemLp (LMPd j f) 2 (volume.restrict (B0579.cell c)) →
    LMWeakPd c j f (LMPd j f)

/-- **Mollifier family on the cylinder** (part (a) of the split of `PartIII-a:T18/3/1/3`). The family
`J k` acts on vector fields; the listed clauses are: smooth periodic output (`smooth`, `periodic`),
linearity on `L²(cell)` (`add`, `smul`), self-adjointness and contraction on `L²(cell)` (`selfAdj`,
`contr`), commutation with the weak derivatives (`commute`), preservation of smooth `c`-periodic
divergence free fields (`divFree`; periodicity in `q` is part of the hypothesis, as for the slices
`b(s)` of the energy class on the cylinder, lines 3427-3440: without it the periodized convolution
picks up the seam term at `q = ±c/2`), strong convergence `J_k f → f` in `L²(cell)` (`tendsto`), boundedness on
`L²(cell)` (`memL2`: the output of an `L²` field is again in `L²(cell)`, so that `contr`,
`selfAdj` and `tendsto` are statements about genuine `L²` integrals and not about the junk value `0`
of a non-integrable Bochner integral), and joint measurability in a parameter (`measurable`: for a
jointly measurable `f(s, y)` the mollified field `(s, x) ↦ J_k f(s, ·)(x)` is jointly measurable,
which makes `s ↦ E_k(s), N_k(s), R_k(s)` measurable). A periodic convolution
`J_k f(x) = ∫_cell K_k(x - y) f(y) dy` with an even nonnegative smooth kernel of unit mass whose
support shrinks to `0` satisfies all of them (`memL2` by Young's inequality, `measurable` by
`MeasureTheory.StronglyMeasurable.integral_prod_right`). Source:
`the November 2 reference manuscript` 3427-3440, 3541-3552. -/
structure IsLMMollifier (c : ℝ) (J : ℕ → LMSpField → LMSpField) : Prop where
  smooth : ∀ (k : ℕ) (f : LMSpField), LMCellL2 c f → ∀ i : Fin 2, ContDiff ℝ ∞ (fun x => J k f x i)
  periodic : ∀ (k : ℕ) (f : LMSpField), LMCellL2 c f → ∀ (x : ℝ × ℝ) (i : Fin 2),
    J k f (x.1 + c, x.2) i = J k f x i
  add : ∀ (k : ℕ) (f g : LMSpField), LMCellL2 c f → LMCellL2 c g →
    J k (fun x i => f x i + g x i) = fun x i => J k f x i + J k g x i
  smul : ∀ (k : ℕ) (a : ℂ) (f : LMSpField), LMCellL2 c f →
    J k (fun x i => a * f x i) = fun x i => a * J k f x i
  selfAdj : ∀ (k : ℕ) (f g : LMSpField), LMCellL2 c f → LMCellL2 c g →
    ∫ x in B0579.cell c, ∑ i : Fin 2, starRingEnd ℂ (J k f x i) * g x i =
      ∫ x in B0579.cell c, ∑ i : Fin 2, starRingEnd ℂ (f x i) * J k g x i
  contr : ∀ (k : ℕ) (f : LMSpField), LMCellL2 c f →
    ∫ x in B0579.cell c, ∑ i : Fin 2, ‖J k f x i‖ ^ 2 ≤ ∫ x in B0579.cell c, ∑ i : Fin 2, ‖f x i‖ ^ 2
  commute : ∀ (k : ℕ) (f g : LMSpField) (j : Fin 2), LMCellL2 c f → LMCellL2 c g →
    (∀ i : Fin 2, LMWeakPd c j (fun x => f x i) (fun x => g x i)) →
    ∀ (i : Fin 2) (x : ℝ × ℝ), LMPd j (fun y => J k f y i) x = J k g x i
  divFree : ∀ (k : ℕ) (f : LMSpField), (∀ i : Fin 2, ContDiff ℝ ∞ (fun x => f x i)) →
    (∀ (x : ℝ × ℝ) (i : Fin 2), f (x.1 + c, x.2) i = f x i) →
    LMCellL2 c f → (∀ x : ℝ × ℝ, LMPd 0 (fun y => f y 0) x + LMPd 1 (fun y => f y 1) x = 0) →
    ∀ x : ℝ × ℝ, LMPd 0 (fun y => J k f y 0) x + LMPd 1 (fun y => J k f y 1) x = 0
  tendsto : ∀ (f : LMSpField), LMCellL2 c f →
    Tendsto (fun k : ℕ => ∫ x in B0579.cell c, ∑ i : Fin 2, ‖J k f x i - f x i‖ ^ 2) atTop (𝓝 0)
  memL2 : ∀ (k : ℕ) (f : LMSpField), LMCellL2 c f → LMCellL2 c (J k f)
  measurable : ∀ (k : ℕ) (f : ℝ × (ℝ × ℝ) → Fin 2 → ℂ), (∀ i : Fin 2, Measurable fun p => f p i) →
    ∀ i : Fin 2, Measurable fun p : ℝ × (ℝ × ℝ) => J k (fun y => f (p.1, y)) p.2 i
  gradL2 : ∀ k : ℕ, ∃ C : ℝ, ∀ f : LMSpField, LMCellL2 c f → ∀ i j : Fin 2,
    MemLp (LMPd j (fun y => J k f y i)) 2 (volume.restrict (B0579.cell c)) ∧
      ∫ x in B0579.cell c, ‖LMPd j (fun y => J k f y i) x‖ ^ 2 ≤
        C * ∫ x in B0579.cell c, ∑ l : Fin 2, ‖f x l‖ ^ 2
  divFreeWeak : ∀ (k : ℕ) (f : LMSpField), LMCellL2 c f →
    (∀ ψ : ℝ × ℝ → ℝ, B0579.IsCylTest c ψ →
      ∫ x in B0579.cell c, (f x 0 * (B0579.pd 0 ψ x : ℂ) + f x 1 * (B0579.pd 1 ψ x : ℂ)) = 0) →
    ∀ x : ℝ × ℝ, LMPd 0 (fun y => J k f y 0) x + LMPd 1 (fun y => J k f y 1) x = 0

/-- Mollified field `u_k(s) = J_k b(s)`. -/
def LMMollU (J : ℕ → LMSpField → LMSpField) (b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ) (k : ℕ) (s : ℝ) :
    LMSpField :=
  J k (fun y => b (s, y))

/-- `E_k(s) = ∫_cell |J_k b(s)|²`. -/
def LMMollE (c : ℝ) (J : ℕ → LMSpField → LMSpField) (b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ) (k : ℕ)
    (s : ℝ) : ℝ :=
  ∫ x in B0579.cell c, vnorm2 (LMMollU J b k s x) ^ 2

/-- `N_k(s) = ∫_cell |∇ J_k b(s)|²`. -/
def LMMollN (c : ℝ) (J : ℕ → LMSpField → LMSpField) (b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ) (k : ℕ)
    (s : ℝ) : ℝ :=
  ∫ x in B0579.cell c, tnorm2 (fun i j => LMPd j (fun y => LMMollU J b k s y i) x) ^ 2

/-- `R_k(s) = ∫_cell Re ∑ᵢⱼ Fᵢⱼ conj(∂ⱼ (J_k² b)ᵢ)` (the real part of the pairing `⟨F, ∇J_k² b⟩`). -/
def LMMollR (c : ℝ) (J : ℕ → LMSpField → LMSpField) (F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ)
    (b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ) (k : ℕ) (s : ℝ) : ℝ :=
  ∫ x in B0579.cell c, ∑ i : Fin 2, ∑ j : Fin 2,
    ((F (s, x) i j).re * (LMPd j (fun y => J k (LMMollU J b k s) y i) x).re +
      (F (s, x) i j).im * (LMPd j (fun y => J k (LMMollU J b k s) y i) x).im)

/-- Part (a): mollifier families exist for every period. -/
def HasLMMollifier : Prop :=
  ∀ c : ℝ, 0 < c → ∃ J : ℕ → LMSpField → LMSpField, IsLMMollifier c J

/-- Part (b): the energy identity for the mollified energies, for every standing datum and every
mollifier family. The right-hand side is the integrand of `CoreIdentity` with `E, N, R` replaced by
`E_k, N_k, R_k`. -/
def MollifiedEnergyIdentity : Prop :=
  ∀ (c ν : ℝ) (μ : ℂ) (F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) (b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ)
    (G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ),
    FreeSolData c ν μ F b G → ∀ J : ℕ → LMSpField → LMSpField, IsLMMollifier c J →
    ExtWeakH1 c ν μ F b G →
    ∀ w : ℝ → ℝ, ContDiff ℝ ∞ w → HasCompactSupport w → tsupport w ⊆ Ioi (0 : ℝ) →
    ∀ k : ℕ,
      ∫ s in Ioi (0 : ℝ), deriv w s * LMMollE c J b k s =
        ∫ s in Ioi (0 : ℝ), w s * (2 * μ.re / s * LMMollE c J b k s +
          2 * ν * LMMollN c J b k s + 2 * LMMollR c J F b k s)

/-- Part (c): the `ε → 0` limit of the two integrals of (b) against a weight `w`. -/
def MollifiedEnergyLimit : Prop :=
  ∀ (c ν : ℝ) (μ : ℂ) (F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) (b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ)
    (G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ),
    FreeSolData c ν μ F b G → ∀ J : ℕ → LMSpField → LMSpField, IsLMMollifier c J →
    ∀ w : ℝ → ℝ, ContDiff ℝ ∞ w → HasCompactSupport w → tsupport w ⊆ Ioi (0 : ℝ) →
    Tendsto (fun k : ℕ => ∫ s in Ioi (0 : ℝ), deriv w s * LMMollE c J b k s) atTop
        (𝓝 (∫ s in Ioi (0 : ℝ), deriv w s * energyE c b s)) ∧
    Tendsto (fun k : ℕ => ∫ s in Ioi (0 : ℝ), w s * (2 * μ.re / s * LMMollE c J b k s +
        2 * ν * LMMollN c J b k s + 2 * LMMollR c J F b k s)) atTop
        (𝓝 (∫ s in Ioi (0 : ℝ), w s * (2 * μ.re / s * energyE c b s +
          2 * ν * energyN c G s + 2 * energyR c F G s)))

/-- **The split of `LionsMagenesCyl`**: the mollifier, the mollified energy identity and its limit
give the energy identity `CoreIdentity` for every standing datum, hence `LionsMagenesCyl`.
Proof: for a datum and a weight `w`, pick a mollifier `J` by (a); the mollified identity (b) says
that the two sequences in (c) agree termwise, so their limits coincide. -/
theorem lionsMagenesCyl_of_split (hA : HasLMMollifier) (hB : MollifiedEnergyIdentity)
    (hC : MollifiedEnergyLimit) : LionsMagenesCyl := by
  intro hW c ν μ F b G hD w hw hcs hts
  obtain ⟨J, hJ⟩ := hA c hD.pos_c
  obtain ⟨h1, h2⟩ := hC c ν μ F b G hD J hJ w hw hcs hts
  exact tendsto_nhds_unique
    (h1.congr (fun k => hB c ν μ F b G hD J hJ (hW c ν μ F b G hD) w hw hcs hts k)) h2

end UnforcedLeray.Short.IIIa
