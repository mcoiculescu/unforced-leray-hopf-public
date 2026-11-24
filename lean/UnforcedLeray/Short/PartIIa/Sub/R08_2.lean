import UnforcedLeray.Short.PartIIa.StatementsRing
import UnforcedLeray.Short.PartIIa.Sub.R08

/-!
# Part II-a, task `PartII-a:R08/2`: the raw inlet is smooth on `{x ≠ 0}` (conditional)

Source of record: `the November 2 reference manuscript`, lines 1330-1334 ("Each
derivative costs `C/r`; all powers of `|x|/r` are absorbed by the Gaussian decay in `η = Rz/r`";
"including smoothness at nonzero axis points").

Target (`InletSmoothExt`, `Sub/R08.lean`): the witness is `a := inletRaw c R` itself. It is `0` on
the axis (`ϱ = 0` gives `ϱ⁻¹ = 0` and `eR = 0`), `C^∞` off the axis, and flat at the axis points
`z ≠ 0`: with `D = trainDatum c q η = e^{-η²/4} θ(q)`, `θ(q) = -2 Σₙ e^{-(q-nc)²/4}` smooth and
`c`-periodic, `q = R log(ϱ/R)`, `η = R z/ϱ`, the stream formulas give, off the axis,

* `u_r = (R² z / (2ϱ²)) e^{-R²z²/(4ϱ²)} θ(q)`,
* `u_z = ϱ⁻¹ e^{-R²z²/(4ϱ²)} [ (1 + R²z²/(2ϱ²)) θ(q) + R θ'(q) ]`,

`inletRaw = u_r e_R + u_z e_z` (`inletClosed`). Every derivative costs powers of `ϱ⁻¹`, and
`e^{-R²z²/(4ϱ²)} ≤ e^{-κ/ϱ²}` for `|z| ≥ δ`, so away from `z = 0` all `D^n inletRaw` are
`O(ϱ^{-N} e^{-κ/ϱ²})`. The flat extension lemma `Axi.contDiff_flat_extension`
(`Lib/AxisymmetricB/FlatExtension.lean`) then gives smoothness at the axis points `z ≠ 0`.

The decomposition (all leaf Props below; the assembly `inletSmoothExt_of` is proved here):

* `AxisFlatSmooth` : a field `f`, `C^∞` off the axis, `0` on the axis and flat
  (`FlatOn (flatRegion δ M) κ f` for some `κ > 0`, every `δ > 0`, `M`) is `C^∞` at every axis point
  with `z ≠ 0` (cutoff in `z` and `Axi.contDiff_flat_extension`);
* `InletRawFlat` : `inletRaw c R` is `FlatOn (flatRegion δ M) (R²δ²/4)`; proved from the closed form
  `InletRawClosedForm`, the regularity `ThetaRegular` of `θ`, and the calculus of the class
  `FlatOn` (`FlatSmul`, `FlatAddCongr`, `TameInvRho`, `TameCoord`, `TameLog`, `TameCompBdd`,
  `FlatExpOfTame`).

`FlatOn W κ f` says: `f` is `C^∞` off the axis and `‖D^n f(y)‖ ≤ C ϱ(y)^{-N} e^{-κ/ϱ(y)²}` on `W`
(`κ = 0`: polynomial growth in `ϱ⁻¹`, "tame"). The calculus lemmas are the same ones needed for
`PartII-a:R06` (`RingAxisSmooth`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa

/-- The periodic Gaussian profile `θ_c(q) = -2 Σ_{n∈ℤ} e^{-(q-nc)²/4}`, so that
`trainDatum c q η = e^{-η²/4} θ_c(q)`. -/
def inletTheta (c q : ℝ) : ℝ := ∑' n : ℤ, -2 * Real.exp (-((q - (n : ℝ) * c) ^ 2 / 4))

/-- The region near the axis, with `|z|` between `δ` and `M`:
`{y ∉ axis, ϱ y < 1, δ ≤ |y 2| ≤ M}`. -/
def flatRegion (δ M : ℝ) : Set Space :=
  {y : Space | y ∉ Axi.axis ∧ Axi.ϱ y < 1 ∧ δ ≤ |y 2| ∧ |y 2| ≤ M}

/-- **Flatness class.** `f` is `C^∞` off the axis and, on `W ⊆ axisᶜ`, every derivative satisfies
`‖D^n f(y)‖ ≤ C ϱ(y)^{-N} e^{-κ/ϱ(y)²}` (with constants `C, N` depending on `n`). For `κ = 0`
this is polynomial growth in `ϱ⁻¹` ("tame"). -/
def FlatOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (W : Set Space) (κ : ℝ)
    (f : Space → E) : Prop :=
  ContDiffOn ℝ ∞ f Axi.axisᶜ ∧
    ∀ n : ℕ, ∃ (C : ℝ) (N : ℕ), ∀ y ∈ W,
      ‖iteratedFDeriv ℝ n f y‖ ≤ C / Axi.ϱ y ^ N * Real.exp (-κ / Axi.ϱ y ^ 2)

/-- The closed form of the raw inlet off the axis (`I = ϱ⁻¹`, `q = R log(ϱ/R)`,
`E = e^{-(R²/4) z² I²}`):
`inletClosed = (R²/2) z I² E θ(q) • eR + I E [(1 + (R²/2) z² I²) θ(q) + R θ'(q)] • e₃`. -/
def inletClosed (c R : ℝ) (y : Space) : Space :=
  ((R ^ 2 / 2 * y 2 * (Axi.ϱ y)⁻¹ ^ 2 * Real.exp (-(R ^ 2 / 4) * y 2 ^ 2 * (Axi.ϱ y)⁻¹ ^ 2) *
      inletTheta c (R * Real.log (Axi.ϱ y / R))) • Axi.eR y) +
    (((Axi.ϱ y)⁻¹ * Real.exp (-(R ^ 2 / 4) * y 2 ^ 2 * (Axi.ϱ y)⁻¹ ^ 2) *
      ((1 + R ^ 2 / 2 * y 2 ^ 2 * (Axi.ϱ y)⁻¹ ^ 2) * inletTheta c (R * Real.log (Axi.ϱ y / R)) +
        R * deriv (inletTheta c) (R * Real.log (Axi.ϱ y / R)))) • Axi.e3)

/-! ### Leaf Props: the profile `θ` and the closed form -/

/-- **Regularity of `θ_c`** (task `PartII-a:R08/2/1`): for `c > 0`, `θ_c` is `C^∞` and `θ_c`, `θ_c'`
have bounded iterated derivatives of every order (`θ_c` is smooth and `c`-periodic; each iterated
derivative is continuous and `c`-periodic, hence bounded on `[0, c]`). -/
def ThetaRegular : Prop :=
  ∀ c : ℝ, 0 < c → ContDiff ℝ ∞ (inletTheta c) ∧
    (∀ j : ℕ, ∃ B : ℝ, ∀ t : ℝ, ‖iteratedFDeriv ℝ j (inletTheta c) t‖ ≤ B) ∧
    (∀ j : ℕ, ∃ B : ℝ, ∀ t : ℝ, ‖iteratedFDeriv ℝ j (deriv (inletTheta c)) t‖ ≤ B)

/-- **Closed form of the raw inlet** (task `PartII-a:R08/2/2`, source line 1210 stream form): off the
axis, `inletRaw c R y = inletClosed c R y` (differentiate `𝒫(r, z) = r e^{-(Rz/r)²/4} θ(R log(r/R))`
in `z` and in `r`). -/
def InletRawClosedForm : Prop :=
  ∀ c R : ℝ, 0 < c → 0 < R → ∀ y : Space, y ∉ Axi.axis → inletRaw c R y = inletClosed c R y

/-! ### Leaf Props: the calculus of the class `FlatOn` -/

/-- **Leibniz** (task `PartII-a:R08/2/3`): scalar times vector, exponents add. -/
def FlatSmul : Prop :=
  ∀ (δ M κ₁ κ₂ : ℝ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Space → ℝ) (g : Space → E),
    FlatOn (flatRegion δ M) κ₁ f → FlatOn (flatRegion δ M) κ₂ g →
      FlatOn (flatRegion δ M) (κ₁ + κ₂) (fun y => f y • g y)

/-- **Sums and congruence** (task `PartII-a:R08/2/4`): `FlatOn` is closed under sums, and depends
only on the values off the axis. -/
def FlatAddCongr : Prop :=
  ∀ (δ M κ : ℝ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (f g : Space → E),
    (FlatOn (flatRegion δ M) κ f → FlatOn (flatRegion δ M) κ g →
        FlatOn (flatRegion δ M) κ (fun y => f y + g y)) ∧
      ((∀ y : Space, y ∉ Axi.axis → f y = g y) → FlatOn (flatRegion δ M) κ f →
        FlatOn (flatRegion δ M) κ g)

/-- **`ϱ⁻¹` is tame** (task `PartII-a:R08/2/5`): `ϱ⁻¹ = s^{-1/2}`, `s = y₀² + y₁²`; the derivatives of
`s ↦ s^{-1/2}` are `c_j s^{-1/2-j}` (`Real.iter_deriv_rpow_const`), and those of `s` are bounded;
Faà di Bruno (`norm_iteratedFDerivWithin_comp_le` on the open set `axisᶜ`). -/
def TameInvRho : Prop :=
  ∀ δ M : ℝ, FlatOn (flatRegion δ M) 0 (fun y : Space => (Axi.ϱ y)⁻¹)

/-- **Coordinates are tame** (task `PartII-a:R08/2/6`): on `|y 2| ≤ M` the coordinate `y 2`, the
horizontal part `Axi.hor` (`‖hor y‖ = ϱ y < 1`) and the constants (in any normed space). -/
def TameCoord : Prop :=
  ∀ δ M : ℝ, FlatOn (flatRegion δ M) 0 (fun y : Space => y 2) ∧
    FlatOn (flatRegion δ M) 0 Axi.hor ∧
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (v : E),
      FlatOn (flatRegion δ M) 0 (fun _ : Space => v)

/-- **The logarithmic coordinate `q = R log(ϱ/R)` is tame** (task `PartII-a:R08/2/7`):
`q = (R/2) log(s/R²)`; `|log ϱ| ≤ ϱ⁻¹` for `ϱ < 1`; `log^{(j)}(s) = (-1)^{j-1}(j-1)!/s^j`
and Faà di Bruno as in `TameInvRho`. -/
def TameLog : Prop :=
  ∀ (δ M R : ℝ), 0 < R →
    FlatOn (flatRegion δ M) 0 (fun y : Space => R * Real.log (Axi.ϱ y / R))

/-- **Composition with a function with bounded derivatives** (task `PartII-a:R08/2/8`): if `θ` is
`C^∞` with every iterated derivative bounded and `q` is tame, then `θ ∘ q` is tame
(Faà di Bruno `norm_iteratedFDerivWithin_comp_le` with `C = ` the bound of `θ^{(j)}`,
`D = max 1 (bounds of ‖D^j q‖)`). -/
def TameCompBdd : Prop :=
  ∀ (δ M : ℝ) (θ : ℝ → ℝ), ContDiff ℝ ∞ θ →
    (∀ j : ℕ, ∃ B : ℝ, ∀ t : ℝ, ‖iteratedFDeriv ℝ j θ t‖ ≤ B) →
    ∀ q : Space → ℝ, FlatOn (flatRegion δ M) 0 q → FlatOn (flatRegion δ M) 0 (fun y => θ (q y))

/-- **The exponential of a tame function bounded by `-κ/ϱ²` is flat** (task `PartII-a:R08/2/9`):
Faà di Bruno with the outer function `exp`, whose derivatives at `g y` all have norm `e^{g y}
≤ e^{-κ/ϱ²}`. -/
def FlatExpOfTame : Prop :=
  ∀ (δ M κ : ℝ) (g : Space → ℝ), FlatOn (flatRegion δ M) 0 g →
    (∀ y ∈ flatRegion δ M, g y ≤ -κ / Axi.ϱ y ^ 2) →
      FlatOn (flatRegion δ M) κ (fun y => Real.exp (g y))

/-! ### Leaf Props: the assembly of the flat bound and the extension across the axis -/

/-- **The raw inlet is flat away from `z = 0`** (task `PartII-a:R08/2/11`, from the closed form and
the calculus Props above): for `c > 0`, `R ≥ 2`, `δ > 0` and every `M`,
`inletRaw c R` is `FlatOn (flatRegion δ M) (R²δ²/4)`. The Gaussian factor is
`exp(g)`, `g = -(R²/4) z² ϱ⁻² ≤ -(R²δ²/4)/ϱ²` on `|z| ≥ δ`. -/
def InletRawFlat : Prop :=
  ∀ c R : ℝ, 0 < c → 2 ≤ R → ∀ δ M : ℝ, 0 < δ →
    FlatOn (flatRegion δ M) (R ^ 2 * δ ^ 2 / 4) (inletRaw c R)

/-- **Smoothness at the nonzero axis points from flatness** (task `PartII-a:R08/2/10`,
`Axi.contDiff_flat_extension`): a field `f`, `C^∞` off the axis, vanishing on the axis, and flat
on every `flatRegion δ M` (`δ > 0`) with some `κ > 0`, is `C^∞` at every axis point with `z ≠ 0`.
Proof: for `z₀ = x₀ 2 ≠ 0` take a smooth cutoff `χ` with `χ = 1` near `z₀` and
`supp χ ⊂ {|z₀|/2 ≤ |z| ≤ 2|z₀|}`; by Leibniz `χ(y 2) • f` satisfies the hypotheses of
`Axi.contDiff_flat_extension` for every finite order, its extension by zero is itself (it vanishes
on the axis), and it agrees with `f` near `x₀`; pass from finite `k` to `∞` by `contDiffAt_infty`. -/
def AxisFlatSmooth : Prop :=
  ∀ f : Space → Space, ContDiffOn ℝ ∞ f Axi.axisᶜ → (∀ y ∈ Axi.axis, f y = 0) →
    (∀ δ M : ℝ, 0 < δ → ∃ κ : ℝ, 0 < κ ∧ FlatOn (flatRegion δ M) κ f) →
      ∀ x₀ ∈ Axi.axis, x₀ 2 ≠ 0 → ContDiffAt ℝ ∞ f x₀

/-- `inletRaw` vanishes on the axis (`ϱ = 0` makes `ϱ⁻¹`, `1/ϱ` and `eR` vanish). -/
theorem inletRaw_eq_zero_of_mem_axis (c R : ℝ) {y : Space} (hy : y ∈ Axi.axis) :
    inletRaw c R y = 0 := by
  have hρ : Axi.ϱ y = 0 := (Axi.mem_axis_iff y).1 hy
  simp [inletRaw, Axi.eR, hρ]

/-- A point of the axis with `z = 0` is the origin. -/
theorem eq_zero_of_mem_axis_of_snd_eq_zero {x : Space} (hx : x ∈ Axi.axis) (hz : x 2 = 0) :
    x = 0 := by
  obtain ⟨h0, h1⟩ := hx
  ext i
  fin_cases i
  · simpa using h0
  · simpa using h1
  · simpa using hz

/-- **`PartII-a:R08/2`, conditional**: `InletSmoothExt`, with the witness `a = inletRaw c R`. -/
theorem inletSmoothExt_of (hflat : InletRawFlat) (hax : AxisFlatSmooth) : InletSmoothExt := by
  intro c R hc hR
  refine ⟨inletRaw c R, ?_, fun x _ => rfl⟩
  have hsm : ContDiffOn ℝ ∞ (inletRaw c R) Axi.axisᶜ := (hflat c R hc hR 1 1 one_pos).1
  have hat : ∀ x₀ ∈ Axi.axis, x₀ 2 ≠ 0 → ContDiffAt ℝ ∞ (inletRaw c R) x₀ :=
    hax _ hsm (fun y hy => inletRaw_eq_zero_of_mem_axis c R hy)
      (fun δ M hδ => ⟨R ^ 2 * δ ^ 2 / 4, by positivity, hflat c R hc hR δ M hδ⟩)
  intro x hx
  by_cases hxa : x ∈ Axi.axis
  · have hz : x 2 ≠ 0 := fun h => hx (eq_zero_of_mem_axis_of_snd_eq_zero hxa h)
    exact (hat x hxa hz).contDiffWithinAt
  · exact (hsm.contDiffAt (Axi.isOpen_compl_axis.mem_nhds hxa)).contDiffWithinAt

/-! ### The flat bound for `inletRaw` from the calculus Props (proved here) -/

/-- Products of scalar functions in the class `FlatOn`. -/
theorem flatOn_mul_of (hS : FlatSmul) {δ M κ₁ κ₂ κ : ℝ} (hκ : κ₁ + κ₂ = κ) {f g : Space → ℝ}
    (hf : FlatOn (flatRegion δ M) κ₁ f) (hg : FlatOn (flatRegion δ M) κ₂ g) :
    FlatOn (flatRegion δ M) κ (fun y => f y * g y) := by
  subst hκ
  exact hS δ M κ₁ κ₂ ℝ f g hf hg

/-- Scalar times vector in the class `FlatOn`, with the exponents added. -/
theorem flatOn_smul_of (hS : FlatSmul) {δ M κ₁ κ₂ κ : ℝ} (hκ : κ₁ + κ₂ = κ) {f : Space → ℝ}
    {g : Space → Space} (hf : FlatOn (flatRegion δ M) κ₁ f) (hg : FlatOn (flatRegion δ M) κ₂ g) :
    FlatOn (flatRegion δ M) κ (fun y => f y • g y) := by
  subst hκ
  exact hS δ M κ₁ κ₂ Space f g hf hg

/-- Congruence for `FlatOn` (the functions agree everywhere). -/
theorem flatOn_congr_of (hA : FlatAddCongr) {δ M κ : ℝ} {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f g : Space → E} (h : ∀ y, f y = g y)
    (hf : FlatOn (flatRegion δ M) κ f) : FlatOn (flatRegion δ M) κ g :=
  ((hA δ M κ E f g).2 (fun y _ => h y)) hf

/-- **The flat bound for the raw inlet from the calculus of `FlatOn`** (assembly of `InletRawFlat`):
`inletClosed` is a sum of two products of tame factors (`z`, `ϱ⁻¹`, `θ(q)`, `θ'(q)`, the
constants, `eR = ϱ⁻¹ hor`, `e₃`) and the flat Gaussian `exp(-(R²/4) z² ϱ⁻²)`. -/
theorem inletRawFlat_of_calculus (hθ : ThetaRegular) (hcf : InletRawClosedForm)
    (hS : FlatSmul) (hA : FlatAddCongr) (hI : TameInvRho) (hC : TameCoord) (hL : TameLog)
    (hB : TameCompBdd) (hE : FlatExpOfTame) : InletRawFlat := by
  intro c R hc hR δ M hδ
  have hR0 : 0 < R := by linarith
  generalize hκ : R ^ 2 * δ ^ 2 / 4 = κ
  obtain ⟨hsm, hb0, hb1⟩ := hθ c hc
  have hz : FlatOn (flatRegion δ M) 0 (fun y : Space => y 2) := (hC δ M).1
  have hhor : FlatOn (flatRegion δ M) 0 Axi.hor := (hC δ M).2.1
  have hcst : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (v : E),
      FlatOn (flatRegion δ M) 0 (fun _ : Space => v) := (hC δ M).2.2
  have hi : FlatOn (flatRegion δ M) 0 (fun y : Space => (Axi.ϱ y)⁻¹) := hI δ M
  have hq := hL δ M R hR0
  have hT0 : FlatOn (flatRegion δ M) 0
      (fun y : Space => inletTheta c (R * Real.log (Axi.ϱ y / R))) :=
    hB δ M (inletTheta c) hsm hb0 _ hq
  have hsm' : ContDiff ℝ ∞ (deriv (inletTheta c)) := (contDiff_infty_iff_deriv.1 hsm).2
  have hT1 : FlatOn (flatRegion δ M) 0
      (fun y : Space => deriv (inletTheta c) (R * Real.log (Axi.ϱ y / R))) :=
    hB δ M (deriv (inletTheta c)) hsm' hb1 _ hq
  have mul : ∀ {κ₁ κ₂ κ : ℝ}, κ₁ + κ₂ = κ → ∀ {f g : Space → ℝ},
      FlatOn (flatRegion δ M) κ₁ f → FlatOn (flatRegion δ M) κ₂ g →
        FlatOn (flatRegion δ M) κ (fun y => f y * g y) :=
    fun {_ _ _} hk {_ _} hf hg => flatOn_mul_of hS hk hf hg
  have add' : ∀ {κ : ℝ} {f g : Space → ℝ}, FlatOn (flatRegion δ M) κ f →
      FlatOn (flatRegion δ M) κ g → FlatOn (flatRegion δ M) κ (fun y => f y + g y) :=
    fun {_ _ _} hf hg => ((hA δ M _ ℝ _ _).1 hf hg)
  have h00 : (0 : ℝ) + 0 = 0 := add_zero 0
  have h0κ : (0 : ℝ) + κ = κ := zero_add κ
  have hκ0 : κ + 0 = κ := add_zero κ
  have hi2 : FlatOn (flatRegion δ M) 0 (fun y : Space => (Axi.ϱ y)⁻¹ ^ 2) :=
    flatOn_congr_of hA (fun y => by ring) (mul h00 hi hi)
  have hz2 : FlatOn (flatRegion δ M) 0 (fun y : Space => y 2 ^ 2) :=
    flatOn_congr_of hA (fun y => by ring) (mul h00 hz hz)
  -- the exponent `g = -(R²/4) z² ϱ⁻²` and the Gaussian
  have hg : FlatOn (flatRegion δ M) 0
      (fun y : Space => -(R ^ 2 / 4) * y 2 ^ 2 * (Axi.ϱ y)⁻¹ ^ 2) :=
    mul h00 (mul h00 (hcst ℝ (-(R ^ 2 / 4))) hz2) hi2
  have hexp : FlatOn (flatRegion δ M) κ
      (fun y : Space => Real.exp (-(R ^ 2 / 4) * y 2 ^ 2 * (Axi.ϱ y)⁻¹ ^ 2)) := by
    refine hE δ M κ _ hg ?_
    intro y hy
    obtain ⟨hya, hy1, hyδ, hyM⟩ := hy
    have hρ : 0 < Axi.ϱ y := Axi.ϱ_pos hya
    have hsq : δ ^ 2 ≤ y 2 ^ 2 := by
      have := pow_le_pow_left₀ hδ.le hyδ 2
      rwa [sq_abs] at this
    have e1 : -(R ^ 2 / 4) * y 2 ^ 2 * (Axi.ϱ y)⁻¹ ^ 2 = -(R ^ 2 / 4 * y 2 ^ 2) / Axi.ϱ y ^ 2 := by
      field_simp
    rw [e1, ← hκ, div_le_div_iff_of_pos_right (by positivity)]
    nlinarith [sq_nonneg R]
  -- the coefficient of `eR`
  have hA1 : FlatOn (flatRegion δ M) 0 (fun y : Space => R ^ 2 / 2 * y 2) :=
    mul h00 (hcst ℝ (R ^ 2 / 2)) hz
  have hA2 : FlatOn (flatRegion δ M) 0
      (fun y : Space => R ^ 2 / 2 * y 2 * (Axi.ϱ y)⁻¹ ^ 2) := mul h00 hA1 hi2
  have hA3 : FlatOn (flatRegion δ M) κ
      (fun y : Space => R ^ 2 / 2 * y 2 * (Axi.ϱ y)⁻¹ ^ 2 *
        Real.exp (-(R ^ 2 / 4) * y 2 ^ 2 * (Axi.ϱ y)⁻¹ ^ 2)) := mul h0κ hA2 hexp
  have hA4 : FlatOn (flatRegion δ M) κ
      (fun y : Space => R ^ 2 / 2 * y 2 * (Axi.ϱ y)⁻¹ ^ 2 *
        Real.exp (-(R ^ 2 / 4) * y 2 ^ 2 * (Axi.ϱ y)⁻¹ ^ 2) *
          inletTheta c (R * Real.log (Axi.ϱ y / R))) := mul hκ0 hA3 hT0
  -- the coefficient of `e₃`
  have hB1 : FlatOn (flatRegion δ M) κ
      (fun y : Space => (Axi.ϱ y)⁻¹ *
        Real.exp (-(R ^ 2 / 4) * y 2 ^ 2 * (Axi.ϱ y)⁻¹ ^ 2)) := mul h0κ hi hexp
  have hB2 : FlatOn (flatRegion δ M) 0
      (fun y : Space => 1 + R ^ 2 / 2 * y 2 ^ 2 * (Axi.ϱ y)⁻¹ ^ 2) :=
    add' (hcst ℝ 1) (mul h00 (mul h00 (hcst ℝ (R ^ 2 / 2)) hz2) hi2)
  have hB3 : FlatOn (flatRegion δ M) 0
      (fun y : Space => (1 + R ^ 2 / 2 * y 2 ^ 2 * (Axi.ϱ y)⁻¹ ^ 2) *
        inletTheta c (R * Real.log (Axi.ϱ y / R)) +
          R * deriv (inletTheta c) (R * Real.log (Axi.ϱ y / R))) :=
    add' (mul h00 hB2 hT0) (mul h00 (hcst ℝ R) hT1)
  have hB4 : FlatOn (flatRegion δ M) κ
      (fun y : Space => (Axi.ϱ y)⁻¹ * Real.exp (-(R ^ 2 / 4) * y 2 ^ 2 * (Axi.ϱ y)⁻¹ ^ 2) *
        ((1 + R ^ 2 / 2 * y 2 ^ 2 * (Axi.ϱ y)⁻¹ ^ 2) *
          inletTheta c (R * Real.log (Axi.ϱ y / R)) +
            R * deriv (inletTheta c) (R * Real.log (Axi.ϱ y / R)))) := mul hκ0 hB1 hB3
  -- the frame vectors
  have heR : FlatOn (flatRegion δ M) 0 Axi.eR := flatOn_smul_of hS h00 hi hhor
  have hF1 := flatOn_smul_of hS hκ0 hA4 heR
  have hF2 := flatOn_smul_of hS hκ0 hB4 (hcst Space Axi.e3)
  have hF := (hA δ M κ Space _ _).1 hF1 hF2
  exact (hA δ M κ Space _ (inletRaw c R)).2 (fun y hy => (hcf c R hc hR0 y hy).symm) hF

/-- **`PartII-a:R08/2`, conditional on the ten leaf Props**: `InletSmoothExt`. -/
theorem inletSmoothExt_of_sub (hθ : ThetaRegular) (hcf : InletRawClosedForm)
    (hS : FlatSmul) (hA : FlatAddCongr) (hI : TameInvRho) (hC : TameCoord) (hL : TameLog)
    (hB : TameCompBdd) (hE : FlatExpOfTame) (hax : AxisFlatSmooth) : InletSmoothExt :=
  inletSmoothExt_of (inletRawFlat_of_calculus hθ hcf hS hA hI hC hL hB hE) hax

end UnforcedLeray.Short.PartIIa
