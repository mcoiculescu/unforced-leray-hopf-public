import UnforcedLeray.Short.PartIIb.Sub.T12_1
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.CellStream.Partition
import UnforcedLeray.Lib.CylinderB.Liouville1D

/-!
# Part II-b, task `PartII-b:T12/1/5` (`CylOfPlaneProps`): planar to cylinder Helmholtz pairs
(conditional assembly and sub-leaves)

Source of record: `the November 2 reference manuscript`: line 1670 ("`P_0` the
ordinary planar cylinder projection") and the zero-frequency remark at lines 1727-1731 (the radial
component is solenoidal, the axial component a gradient); `P_0` is used in the causal formula at
lines 1923-1926. The target is `CylOfPlaneProps` of `Sub/T12_1.lean`: for `c`-periodic
`F, G ∈ L^r(dq/c dη)`, `IsPlaneHelmholtz F G → IsCylHelmholtz c r F G`.

## Why the target splits this way

Let `D = F - G` and let `θ ∈ C_c^∞(ℝ)` with `Σ_n θ(q - n c) = 1`, `Σ_n θ^{(k)}(q - n c) = 0`
(`CellPart.exists_partition_of_derivs`).

* **Weak divergence** (`IsCylHelmholtz`, second clause). For a cylinder test `φ`, `θ(q) φ` is a planar
  test, and the planar weak solenoidality `∫ G·∇(θφ) = 0` reads `∫ θ (G·∇φ) + ∫ θ' G₀ φ = 0`.
  Unfolding the periodic integrands (`CylUnfold`) turns this into `∫_cell G·∇φ = 0`.
* **Orthogonality to solenoidal tests** (third clause). A cylinder solenoidal test `Ψ` has a constant
  flux `m = ∫ Ψ₀ dη` (`CylFluxConst`), hence `Ψ = ∇^⊥Φ + m (χ(η), 0)` with `χ ∈ C_c^∞(ℝ)`, `∫ χ = 1`,
  and a periodic stream function `Φ` that is smooth and compactly supported in `η`
  (`CylStreamDecomp`, via the smooth primitive `SmoothPrimEta`). The field `∇^⊥(θ Φ)` is a planar
  solenoidal test (`CylCutoffTests`), so planar orthogonality gives `∫_cell D·∇^⊥Φ = 0` after
  unfolding. For the zero mode, `∇^⊥(θ(q) ζ(η)) = (θ ζ', -θ' ζ)` gives `∫ e ζ' = 0` for all
  `ζ ∈ C_c^∞(ℝ)`, where `e(η) = ∫_{cell} D₀(q, η) dq ∈ L^r(ℝ)` (`CylCellAverage`); a distribution
  with zero derivative in `L^r(ℝ)` (`r < ∞`) vanishes (`OneDDerivZeroLr`), so `∫_cell D₀ χ = 0`.
* Integrability and a.e. measurability on the plane of the periodic fields: `CylLpAEMeas`,
  `CylPairingIntegrableOn`.

Proved here: `cylOfPlaneProps_of : CylUnfold → CylLpAEMeas → CylPairingIntegrableOn →
CylCutoffTests → CylStreamDecomp → CylCellAverage → OneDDerivZeroLr → CylOfPlaneProps`, no sorry.
The leaves `SmoothPrimEta` and `CylFluxConst` are the two inputs of `CylStreamDecomp`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-! ## Statements of the leaves -/

/-- A `ℂ`-valued function on the plane that is `c`-periodic in `q` (everywhere), a.e.-strongly
measurable for Lebesgue measure, and integrable on one cell `[-c/2, c/2) × ℝ`. -/
def CylGood (c : ℝ) (h : ℝ × ℝ → ℂ) : Prop :=
  (∀ z : ℝ × ℝ, h (z.1 + c, z.2) = h z) ∧ AEStronglyMeasurable h volume ∧
    IntegrableOn h (UnforcedLeray.Cyl.cell c) volume

/-- **Leaf `PartII-b:T12/1/5/1`** (unfolding against a compactly supported weight; the
`Lib/CylinderB/Periodize.lean` device, SP 1670). If `w ∈ C_c(ℝ)` has `Σ_n w(q - n c) = s` for all
`q` and `h` is `c`-periodic, a.e.-measurable and integrable on one cell, then `w(q) h` is integrable
on the plane and `∫_{ℝ²} w(q) h = s ∫_{cell} h`. Proof: `w(q)` is supported in finitely many
translates `n c + [-c/2, c/2)`, `h(· + n c e_q) = h`, so by `integral_eq_tsum_cell` (unfolding along
the lattice) `∫ w h = Σ_n ∫_cell w(q + n c) h`, a finite sum that equals `∫_cell (Σ_n w(q + n c)) h
= s ∫_cell h` (reindex `n ↦ -n` in the `HasSum`). -/
def CylUnfold : Prop :=
  ∀ (c : ℝ) (w : ℝ → ℝ) (s : ℝ), 0 < c → Continuous w → HasCompactSupport w →
    (∀ q : ℝ, HasSum (fun n : ℤ => w (q - n * c)) s) →
    ∀ h : ℝ × ℝ → ℂ, CylGood c h →
      Integrable (fun z : ℝ × ℝ => (w z.1 : ℂ) * h z) volume ∧
        ∫ z, (w z.1 : ℂ) * h z = (s : ℂ) * ∫ z in UnforcedLeray.Cyl.cell c, h z

/-- **Leaf `PartII-b:T12/1/5/2`**: a `c`-periodic field of `L^r(Cyl.avgμ c)` is a.e.-strongly
measurable for Lebesgue measure on the plane. Proof: `avgμ c` is a positive multiple of Lebesgue
measure restricted to the cell, so `F` is a.e.-strongly measurable on the cell; on the translate
`cell + n c e_q` use `F(z) = F(z - n c e_q)` and the measure preserving translation; the countable
union `⋃_n (cell + n c e_q)` is the plane (`aestronglyMeasurable_iUnion_iff`). -/
def CylLpAEMeas : Prop :=
  ∀ (c r : ℝ) (F : ℝ × ℝ → CMerid), 0 < c → CylLp c r F → AEStronglyMeasurable F volume

/-- **Leaf `PartII-b:T12/1/5/3`** (Hoelder on the cell): for `F ∈ L^r(Cyl.avgμ c)`, `r ≥ 1`, and a
continuous real `w` vanishing for `|η| > L`, each `F_i w` is integrable on the cell. Proof: the set
`cell ∩ {|η| ≤ L}` has finite measure, `F ∈ L^r ⊂ L^1` there (`MemLp.mono_exponent` on the restricted
measure), `w` is bounded on the compact box `[-c/2, c/2] × [-L, L]` and `F_i w = 0` off that box. -/
def CylPairingIntegrableOn : Prop :=
  ∀ (c r : ℝ) (F : ℝ × ℝ → CMerid), 0 < c → 1 ≤ r → CylLp c r F → ∀ (i : Fin 2) (w : ℝ × ℝ → ℝ),
    Continuous w → (∃ L : ℝ, ∀ z : ℝ × ℝ, L < |z.2| → w z = 0) →
      IntegrableOn (fun z : ℝ × ℝ => F z i * (w z : ℂ)) (UnforcedLeray.Cyl.cell c) volume

/-- **Leaf `PartII-b:T12/1/5/4`** (planar tests built from a cylinder test and a cutoff in `q`):
for `θ ∈ C_c^∞(ℝ)` and a cylinder test `φ`, `θ(q) φ` is a planar test with the product-rule
derivatives, and `∇^⊥(θ φ) = (θ ∂_ηφ, -θ' φ - θ ∂_qφ)` is a planar solenoidal test. Proof: all
components are smooth (`ContDiff.fderiv_right`, `clm_apply`); the support lies in
`tsupport θ × [-L, L]`, which is compact (`φ` and its derivatives vanish for `|η| > L`, as `φ = 0`
on the open set `{|η| > L}`, `Filter.EventuallyEq.fderiv_eq`); the divergence is
`θ'∂_ηφ + θ ∂_q∂_ηφ - θ'∂_ηφ - θ ∂_η∂_qφ = 0` by symmetry of the second derivative
(`ContDiffAt.isSymmSndFDerivAt`; compare `planarTest_div_free` in
`Tasks/FlatUnique/CellStream/PlanarTest.lean`). -/
def CylCutoffTests : Prop :=
  ∀ (c : ℝ) (θ : ℝ → ℝ), ContDiff ℝ ∞ θ → HasCompactSupport θ → ∀ φ : ℝ × ℝ → ℝ, CylTest c φ →
    PlaneTest (fun z : ℝ × ℝ => θ z.1 * φ z) ∧
    (∀ z : ℝ × ℝ, fderiv ℝ (fun y : ℝ × ℝ => θ y.1 * φ y) z (1, 0) =
        deriv θ z.1 * φ z + θ z.1 * fderiv ℝ φ z (1, 0)) ∧
    (∀ z : ℝ × ℝ, fderiv ℝ (fun y : ℝ × ℝ => θ y.1 * φ y) z (0, 1) =
        θ z.1 * fderiv ℝ φ z (0, 1)) ∧
    PlaneSolTest (fun z : ℝ × ℝ =>
      ![θ z.1 * fderiv ℝ φ z (0, 1), -(deriv θ z.1 * φ z + θ z.1 * fderiv ℝ φ z (1, 0))])

/-- **Leaf `PartII-b:T12/1/5/5`** (smooth primitive in the last variable with parameters). If `g`
is smooth on the plane and vanishes for `|η| > L`, then `P(q, η) = ∫_{-L}^{η} g(q, s) ds` is smooth,
`∂_ηP = g`, and `∂_qP(q, η) = ∫_{-L}^{η} ∂_q g(q, s) ds`. Proof: `∂_ηP = g` is the fundamental
theorem of calculus (`Continuous.integral_hasStrictDerivAt`); for the `q`-derivative use
`hasFDerivAt_integral_of_dominated_loc_of_deriv_le` (or the substitution
`P = (η + L) ∫_0^1 g(q, -L + t(η + L)) dt`) with the dominating bound from the compact support in
`η`; smoothness follows by induction on the order, since `∂_qP` and `∂_ηP` are again of the same
form with `g` replaced by `∂_q g` and `g`. -/
def SmoothPrimEta : Prop :=
  ∀ (g : ℝ × ℝ → ℝ) (L : ℝ), ContDiff ℝ ∞ g → (∀ z : ℝ × ℝ, L < |z.2| → g z = 0) →
    ContDiff ℝ ∞ (fun z : ℝ × ℝ => ∫ s in (-L)..z.2, g (z.1, s)) ∧
    (∀ z : ℝ × ℝ, fderiv ℝ (fun y : ℝ × ℝ => ∫ s in (-L)..y.2, g (y.1, s)) z (0, 1) = g z) ∧
    (∀ z : ℝ × ℝ, fderiv ℝ (fun y : ℝ × ℝ => ∫ s in (-L)..y.2, g (y.1, s)) z (1, 0) =
        ∫ s in (-L)..z.2, fderiv ℝ g (z.1, s) (1, 0))

/-- **Leaf `PartII-b:T12/1/5/6`** (constant flux). For a cylinder solenoidal test `Ψ`, the flux
`∫ Ψ₀(q, s) ds` does not depend on `q`. Proof: take `L` with `Ψ = 0` for `|η| > L`; by
`SmoothPrimEta` applied to `g = Ψ₀` the function `T(q) = ∫_{-L}^{L} Ψ₀(q, s) ds` is differentiable
with `T'(q) = ∫_{-L}^{L} ∂_qΨ₀(q, s) ds = -∫_{-L}^{L} ∂_ηΨ₁(q, s) ds = -(Ψ₁(q, L) - Ψ₁(q, -L)) = 0`
(`div_free`, FTC), so `T` is constant (`is_const_of_deriv_eq_zero`); `∫ Ψ₀(q, ·) = T(q)` because
`Ψ₀(q, ·)` vanishes outside `[-L, L]`. -/
def CylFluxConst : Prop :=
  ∀ (c : ℝ) (Ψ : ℝ × ℝ → Fin 2 → ℝ), CylSolTest c Ψ → ∀ q : ℝ,
    ∫ s, Ψ (q, s) 0 = ∫ s, Ψ (0, s) 0

/-- **Leaf `PartII-b:T12/1/5/7`** (stream function of a periodic solenoidal test; uses
`SmoothPrimEta`, `CylFluxConst`; SP 1727-1731). For a cylinder solenoidal test `Ψ` and any
`χ ∈ C_c^∞(ℝ)` with `∫ χ = 1` there are a cylinder test `Φ` and a number `m` with
`Ψ₀ = ∂_ηΦ + m χ(η)` and `Ψ₁ = -∂_qΦ`. Proof: put `m = ∫ Ψ₀(0, s) ds`, `g(q, η) = Ψ₀(q, η) - m χ(η)`,
`L'` a common support radius of `Ψ` and `χ`, and `Φ = ∫_{-L'}^{η} g(q, s) ds` (`SmoothPrimEta`).
Then `Φ` is smooth, `c`-periodic (as `g` is), `∂_ηΦ = g`, and
`∂_qΦ(q, η) = ∫_{-L'}^{η} ∂_qΨ₀ = -∫_{-L'}^{η} ∂_sΨ₁ = -Ψ₁(q, η)` (`div_free`, FTC); `Φ = 0` for
`η < -L'` trivially and for `η > L'` because `∫_{-L'}^{L'} g = ∫Ψ₀(q, ·) - m = 0` by `CylFluxConst`. -/
def CylStreamDecomp : Prop :=
  ∀ (c : ℝ) (Ψ : ℝ × ℝ → Fin 2 → ℝ), CylSolTest c Ψ →
    ∀ χ : ℝ → ℝ, UnforcedLeray.Cyl.OneD.Test χ → ∫ s, χ s = 1 →
      ∃ (Φ : ℝ × ℝ → ℝ) (m : ℝ), CylTest c Φ ∧
        (∀ z : ℝ × ℝ, Ψ z 0 = fderiv ℝ Φ z (0, 1) + m * χ z.2) ∧
        (∀ z : ℝ × ℝ, Ψ z 1 = -fderiv ℝ Φ z (1, 0))

/-- **Leaf `PartII-b:T12/1/5/8`** (the `q`-average of an `L^r` field; Hoelder and Fubini): for
`f ∈ L^r(Cyl.avgμ c)`, `r ≥ 1`, there is `e ∈ L^r(ℝ)` such that `∫_{cell} f(q, η) χ(η) = ∫ e χ` for
every test `χ`. Proof: `e(η) = ∫_{-c/2}^{c/2} f(q, η) dq` (the junk value `0` where `f(·, η)` is not
integrable). `e` is a.e.-strongly measurable (`AEStronglyMeasurable.integral_prod_right'`), and
`‖e(η)‖^r ≤ c^{r-1} ∫ ‖f(q, η)‖^r dq` (Jensen / Hoelder on the interval of length `c`), so
`∫ ‖e‖^r ≤ c^{r-1} ∫_{cell} ‖f‖^r < ∞`. The identity is Fubini (`integral_prod`), valid because
`f χ` is integrable on the cell (finite measure of `cell ∩ {|η| ≤ R}` and `f ∈ L^r ⊂ L^1` there). -/
def CylCellAverage : Prop :=
  ∀ (c r : ℝ), 0 < c → 1 ≤ r → ∀ f : ℝ × ℝ → ℂ,
    MemLp f (ENNReal.ofReal r) (UnforcedLeray.Cyl.avgμ c) →
      ∃ e : ℝ → ℂ, MemLp e (ENNReal.ofReal r) volume ∧
        ∀ χ : ℝ → ℝ, UnforcedLeray.Cyl.OneD.Test χ →
          ∫ z in UnforcedLeray.Cyl.cell c, f z * ((χ z.2 : ℝ) : ℂ) = ∫ η, e η * ((χ η : ℝ) : ℂ)

/-- **Leaf `PartII-b:T12/1/5/9`** (du Bois-Reymond in `L^r(ℝ)`, the `L^r` analogue of
`UnforcedLeray.Cyl.OneD.eq_zero_of_deriv` in `Lib/CylinderB/Liouville1D.lean`): if `e ∈ L^r(ℝ; ℂ)`,
`1 < r < ∞`, and `∫ e ζ' = 0` for every test `ζ`, then `∫ e χ = 0` for every test `χ` (i.e.
`e = 0` a.e.). Proof: copy `eq_zero_of_deriv` with `L²` replaced by `L^r` and Hoelder's exponent
pair `(r, r/(r-1))`: for a bump `β₀` with `∫ β₀ = 1`, `χ - (∫ χ) β₀` has integral `0`, hence is
`ζ'` with `ζ` a test (`exists_primitive`), so `∫ e χ = (∫ χ) ∫ e β₀`; replacing `β₀` by the dilates
`R⁻¹ β₀(·/R)` shows `|∫ e β₀| ≤ ‖e‖_r R^{-1/r} ‖β₀‖_{r'} → 0`. Real and imaginary parts handle the
complex values. -/
def OneDDerivZeroLr : Prop :=
  ∀ r : ℝ, 1 < r → ∀ e : ℝ → ℂ, MemLp e (ENNReal.ofReal r) volume →
    (∀ ζ : ℝ → ℝ, UnforcedLeray.Cyl.OneD.Test ζ → ∫ η, e η * ((deriv ζ η : ℝ) : ℂ) = 0) →
      ∀ χ : ℝ → ℝ, UnforcedLeray.Cyl.OneD.Test χ → ∫ η, e η * ((χ η : ℝ) : ℂ) = 0


/-! ## Assembly: conversions between `avgμ` and the cell -/

theorem cyl_integrable_avg_iff {c : ℝ} (hc : 0 < c) {f : ℝ × ℝ → ℂ} :
    Integrable f (UnforcedLeray.Cyl.avgμ c) ↔
      IntegrableOn f (UnforcedLeray.Cyl.cell c) volume := by
  unfold UnforcedLeray.Cyl.avgμ UnforcedLeray.Cyl.cellμ
  rw [integrable_smul_measure (ENNReal.ofReal_pos.2 (inv_pos.2 hc)).ne' ENNReal.ofReal_ne_top]
  rfl

theorem cyl_integral_avg {c : ℝ} (hc : 0 < c) (f : ℝ × ℝ → ℂ) :
    ∫ z, f z ∂(UnforcedLeray.Cyl.avgμ c) = (c : ℂ)⁻¹ * ∫ z in UnforcedLeray.Cyl.cell c, f z := by
  unfold UnforcedLeray.Cyl.avgμ UnforcedLeray.Cyl.cellμ
  rw [integral_smul_measure, ENNReal.toReal_ofReal (inv_nonneg.2 hc.le), Complex.real_smul]
  simp

/-! ## Assembly: `CylGood` closure -/

theorem cylGood_add {c : ℝ} {h₁ h₂ : ℝ × ℝ → ℂ} (a : CylGood c h₁) (b : CylGood c h₂) :
    CylGood c (fun z => h₁ z + h₂ z) :=
  ⟨fun z => by beta_reduce; rw [a.1, b.1], a.2.1.add b.2.1, a.2.2.add b.2.2⟩

theorem cylGood_sub {c : ℝ} {h₁ h₂ : ℝ × ℝ → ℂ} (a : CylGood c h₁) (b : CylGood c h₂) :
    CylGood c (fun z => h₁ z - h₂ z) :=
  ⟨fun z => by beta_reduce; rw [a.1, b.1], a.2.1.sub b.2.1, a.2.2.sub b.2.2⟩

theorem cylGood_neg {c : ℝ} {h : ℝ × ℝ → ℂ} (a : CylGood c h) : CylGood c (fun z => -h z) :=
  ⟨fun z => by beta_reduce; rw [a.1], a.2.1.neg, a.2.2.neg⟩

theorem cylGood_const_mul {c : ℝ} {h : ℝ × ℝ → ℂ} (m : ℂ) (a : CylGood c h) :
    CylGood c (fun z => m * h z) :=
  ⟨fun z => by beta_reduce; rw [a.1], a.2.1.const_mul m, a.2.2.const_mul m⟩

/-! ## Assembly: facts about cylinder tests -/

theorem cylTest_fderiv_contDiff {c : ℝ} {φ : ℝ × ℝ → ℝ} (hφ : CylTest c φ) (v : ℝ × ℝ) :
    ContDiff ℝ ∞ (fun z : ℝ × ℝ => fderiv ℝ φ z v) :=
  (ContDiff.fderiv_right (m := ∞) hφ.smooth (by simp)).clm_apply contDiff_const

theorem cylTest_fderiv_periodic {c : ℝ} {φ : ℝ × ℝ → ℝ} (hφ : CylTest c φ) (v z : ℝ × ℝ) :
    fderiv ℝ φ (z.1 + c, z.2) v = fderiv ℝ φ z v := by
  have hfun : (fun y : ℝ × ℝ => φ (y + ((c : ℝ), (0 : ℝ)))) = φ := by
    funext y
    have h := hφ.periodic y
    have e : y + ((c : ℝ), (0 : ℝ)) = (y.1 + c, y.2) := by ext <;> simp
    rw [e]
    exact h
  have hd : fderiv ℝ φ (z + ((c : ℝ), (0 : ℝ))) = fderiv ℝ φ z := by
    have h : fderiv ℝ (fun y : ℝ × ℝ => φ (y + ((c : ℝ), (0 : ℝ)))) z =
        fderiv ℝ φ (z + ((c : ℝ), (0 : ℝ))) := fderiv_comp_add_right _
    rw [hfun] at h
    exact h.symm
  have e : z + ((c : ℝ), (0 : ℝ)) = (z.1 + c, z.2) := by ext <;> simp
  rw [← e, hd]

theorem cylTest_fderiv_vanish {c : ℝ} {φ : ℝ × ℝ → ℝ} (hφ : CylTest c φ) (v : ℝ × ℝ) :
    ∃ L : ℝ, ∀ z : ℝ × ℝ, L < |z.2| → fderiv ℝ φ z v = 0 := by
  obtain ⟨L, hL⟩ := hφ.bounded
  refine ⟨L, fun z hz => ?_⟩
  have hU : IsOpen {y : ℝ × ℝ | L < |y.2|} :=
    isOpen_lt continuous_const (by fun_prop)
  have hev : φ =ᶠ[𝓝 z] (fun _ : ℝ × ℝ => (0 : ℝ)) := by
    filter_upwards [hU.mem_nhds hz] with y hy
    exact hL y hy
  rw [hev.fderiv_eq, fderiv_const_apply]
  simp

/-- The pairing of a `CylLp` field with a continuous, periodic, `η`-compactly supported weight is
`CylGood` (`CylLpAEMeas`, `CylPairingIntegrableOn`). -/
theorem cylGood_pair (hA : CylLpAEMeas) (hI : CylPairingIntegrableOn) {c r : ℝ} (hc : 0 < c)
    (hr : 1 ≤ r) {F : ℝ × ℝ → CMerid} (hF : CylLp c r F) (i : Fin 2) {w : ℝ × ℝ → ℝ}
    (hw : Continuous w) (hper : ∀ z : ℝ × ℝ, w (z.1 + c, z.2) = w z)
    (hsupp : ∃ L : ℝ, ∀ z : ℝ × ℝ, L < |z.2| → w z = 0) :
    CylGood c (fun z => F z i * (w z : ℂ)) := by
  refine ⟨fun z => ?_, ?_, hI c r F hc hr hF i w hw hsupp⟩
  · beta_reduce
    rw [hF.1 z, hper z]
  · have hm := hA c r F hc hF
    exact ((EuclideanSpace.proj i : CMerid →L[ℂ] ℂ).continuous.comp_aestronglyMeasurable hm).mul
      (Complex.continuous_ofReal.comp hw).aestronglyMeasurable

theorem cylTest_good {c : ℝ} {φ : ℝ × ℝ → ℝ} (hφ : CylTest c φ) :
    Continuous φ ∧ (∀ z : ℝ × ℝ, φ (z.1 + c, z.2) = φ z) ∧
      ∃ L : ℝ, ∀ z : ℝ × ℝ, L < |z.2| → φ z = 0 :=
  ⟨hφ.smooth.continuous, hφ.periodic, hφ.bounded⟩


/-! ## Assembly: unfolding the cutoff identities -/

/-- `∫ (θ h + θ' h₂) = ∫_cell h` for the periodic partition of unity `θ` (`Σ θ(· - n c) = 1`,
`Σ θ'(· - n c) = 0`) and `c`-periodic `h, h₂`. -/
theorem cyl_split_unfold (hU : CylUnfold) {c : ℝ} (hc : 0 < c) {θ : ℝ → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hθc : HasCompactSupport θ)
    (hθ1 : ∀ q : ℝ, HasSum (fun n : ℤ => θ (q - n * c)) 1)
    (hθ0 : ∀ q : ℝ, HasSum (fun n : ℤ => deriv θ (q - n * c)) 0)
    {h h₂ : ℝ × ℝ → ℂ} (a : CylGood c h) (b : CylGood c h₂) :
    Integrable (fun z : ℝ × ℝ => (θ z.1 : ℂ) * h z + ((deriv θ z.1 : ℝ) : ℂ) * h₂ z) volume ∧
      ∫ z, ((θ z.1 : ℂ) * h z + ((deriv θ z.1 : ℝ) : ℂ) * h₂ z) =
        ∫ z in UnforcedLeray.Cyl.cell c, h z := by
  have hd : Continuous (deriv θ) := hθ.continuous_deriv (by simp)
  obtain ⟨i1, e1⟩ := hU c θ 1 hc hθ.continuous hθc hθ1 h a
  obtain ⟨i2, e2⟩ := hU c (deriv θ) 0 hc hd hθc.deriv hθ0 h₂ b
  refine ⟨i1.add i2, ?_⟩
  rw [integral_add i1 i2, e1, e2]
  simp

/-- The partition of unity of `CellPart`, in the form used here. -/
theorem cyl_partition {c : ℝ} (hc : 0 < c) :
    ∃ θ : ℝ → ℝ, ContDiff ℝ ∞ θ ∧ HasCompactSupport θ ∧
      (∀ q : ℝ, HasSum (fun n : ℤ => θ (q - n * c)) 1) ∧
      (∀ q : ℝ, HasSum (fun n : ℤ => deriv θ (q - n * c)) 0) := by
  obtain ⟨θ, hθ, hθc, -, hθ1, hθk⟩ := CellPart.exists_partition_of_derivs hc
  refine ⟨θ, hθ, hθc, hθ1, fun q => ?_⟩
  have h := hθk 0 q
  simpa [iteratedDeriv_one] using h

/-! ## Assembly: weak divergence on the cylinder -/

theorem cyl_weak_div (hU : CylUnfold) (hA : CylLpAEMeas) (hI : CylPairingIntegrableOn)
    (hT : CylCutoffTests) {c r : ℝ} (hc : 0 < c) (hr : 1 ≤ r) {G : ℝ × ℝ → CMerid}
    (hG : CylLp c r G)
    (hP1 : ∀ φ : ℝ × ℝ → ℝ, PlaneTest φ →
      Integrable (fun z => G z 0 * (fderiv ℝ φ z (1, 0) : ℂ) + G z 1 * (fderiv ℝ φ z (0, 1) : ℂ)) ∧
        ∫ z, (G z 0 * (fderiv ℝ φ z (1, 0) : ℂ) + G z 1 * (fderiv ℝ φ z (0, 1) : ℂ)) = 0)
    {φ : ℝ × ℝ → ℝ} (hφ : CylTest c φ) :
    CylGood c (fun z => G z 0 * (fderiv ℝ φ z (1, 0) : ℂ) + G z 1 * (fderiv ℝ φ z (0, 1) : ℂ)) ∧
      ∫ z in UnforcedLeray.Cyl.cell c,
        (G z 0 * (fderiv ℝ φ z (1, 0) : ℂ) + G z 1 * (fderiv ℝ φ z (0, 1) : ℂ)) = 0 := by
  obtain ⟨θ, hθ, hθc, hθ1, hθ0⟩ := cyl_partition hc
  obtain ⟨hPT, hf1, hf2, -⟩ := hT c θ hθ hθc φ hφ
  have g1 : CylGood c (fun z => G z 0 * (fderiv ℝ φ z (1, 0) : ℂ)) := by
    obtain ⟨c1, c2, c3⟩ := cylTest_fderiv_contDiff hφ (1, 0) |>.continuous,
      cylTest_fderiv_periodic hφ (1, 0), cylTest_fderiv_vanish hφ (1, 0)
    exact cylGood_pair hA hI hc hr hG 0 c1 c2 c3
  have g2 : CylGood c (fun z => G z 1 * (fderiv ℝ φ z (0, 1) : ℂ)) := by
    obtain ⟨c1, c2, c3⟩ := cylTest_fderiv_contDiff hφ (0, 1) |>.continuous,
      cylTest_fderiv_periodic hφ (0, 1), cylTest_fderiv_vanish hφ (0, 1)
    exact cylGood_pair hA hI hc hr hG 1 c1 c2 c3
  have g3 : CylGood c (fun z => G z 0 * (φ z : ℂ)) := by
    obtain ⟨c1, c2, c3⟩ := cylTest_good hφ
    exact cylGood_pair hA hI hc hr hG 0 c1 c2 c3
  have g12 := cylGood_add g1 g2
  have key := cyl_split_unfold hU hc hθ hθc hθ1 hθ0 g12 g3
  have h0 := (hP1 _ hPT).2
  have hfun : (fun z : ℝ × ℝ => G z 0 * (fderiv ℝ (fun y : ℝ × ℝ => θ y.1 * φ y) z (1, 0) : ℂ) +
        G z 1 * (fderiv ℝ (fun y : ℝ × ℝ => θ y.1 * φ y) z (0, 1) : ℂ)) =
      fun z => (θ z.1 : ℂ) * (G z 0 * (fderiv ℝ φ z (1, 0) : ℂ) + G z 1 * (fderiv ℝ φ z (0, 1) : ℂ)) +
        ((deriv θ z.1 : ℝ) : ℂ) * (G z 0 * (φ z : ℂ)) := by
    funext z
    rw [hf1 z, hf2 z]
    push_cast
    ring
  rw [hfun] at h0
  refine ⟨g12, ?_⟩
  rw [← key.2]
  exact h0


/-! ## Assembly: orthogonality to the stream fields of a cylinder test -/

/-- For a `c`-periodic `D ∈ L^r` orthogonal to every planar solenoidal test, `∫_cell D·∇^⊥Φ = 0` for
every cylinder test `Φ` (test `∇^⊥(θΦ)` and unfold). -/
theorem cyl_orth_stream (hU : CylUnfold) (hA : CylLpAEMeas) (hI : CylPairingIntegrableOn)
    (hT : CylCutoffTests) {c r : ℝ} (hc : 0 < c) (hr : 1 ≤ r) {D : ℝ × ℝ → CMerid}
    (hD : CylLp c r D)
    (hP2 : ∀ Ψ : ℝ × ℝ → Fin 2 → ℝ, PlaneSolTest Ψ →
      ∫ z, ∑ i : Fin 2, D z i * (Ψ z i : ℂ) = 0)
    {Φ : ℝ × ℝ → ℝ} (hΦ : CylTest c Φ) :
    CylGood c (fun z => D z 0 * (fderiv ℝ Φ z (0, 1) : ℂ) - D z 1 * (fderiv ℝ Φ z (1, 0) : ℂ)) ∧
      ∫ z in UnforcedLeray.Cyl.cell c,
        (D z 0 * (fderiv ℝ Φ z (0, 1) : ℂ) - D z 1 * (fderiv ℝ Φ z (1, 0) : ℂ)) = 0 := by
  obtain ⟨θ, hθ, hθc, hθ1, hθ0⟩ := cyl_partition hc
  obtain ⟨-, -, -, hSol⟩ := hT c θ hθ hθc Φ hΦ
  have g1 : CylGood c (fun z => D z 0 * (fderiv ℝ Φ z (0, 1) : ℂ)) := by
    obtain ⟨c1, c2, c3⟩ := cylTest_fderiv_contDiff hΦ (0, 1) |>.continuous,
      cylTest_fderiv_periodic hΦ (0, 1), cylTest_fderiv_vanish hΦ (0, 1)
    exact cylGood_pair hA hI hc hr hD 0 c1 c2 c3
  have g2 : CylGood c (fun z => D z 1 * (fderiv ℝ Φ z (1, 0) : ℂ)) := by
    obtain ⟨c1, c2, c3⟩ := cylTest_fderiv_contDiff hΦ (1, 0) |>.continuous,
      cylTest_fderiv_periodic hΦ (1, 0), cylTest_fderiv_vanish hΦ (1, 0)
    exact cylGood_pair hA hI hc hr hD 1 c1 c2 c3
  have g3 : CylGood c (fun z => D z 1 * (Φ z : ℂ)) := by
    obtain ⟨c1, c2, c3⟩ := cylTest_good hΦ
    exact cylGood_pair hA hI hc hr hD 1 c1 c2 c3
  have gk := cylGood_sub g1 g2
  have gn := cylGood_neg g3
  have key := cyl_split_unfold hU hc hθ hθc hθ1 hθ0 gk gn
  have h0 : ∫ z : ℝ × ℝ, ((θ z.1 : ℂ) *
        (D z 0 * (fderiv ℝ Φ z (0, 1) : ℂ) - D z 1 * (fderiv ℝ Φ z (1, 0) : ℂ)) +
      ((deriv θ z.1 : ℝ) : ℂ) * (-(D z 1 * (Φ z : ℂ)))) = 0 := by
    refine Eq.trans ?_ (hP2 _ hSol)
    congr 1
    funext z
    simp [Fin.sum_univ_two]
    ring
  refine ⟨gk, ?_⟩
  rw [← key.2]
  exact h0

/-! ## Assembly: the zero mode -/

theorem cyl_zero_mode (hC : CylCellAverage) (hZ : OneDDerivZeroLr) {c r : ℝ} (hc : 0 < c)
    (hr : 1 < r) {D : ℝ × ℝ → CMerid} (hD : CylLp c r D)
    (hk : ∀ Φ : ℝ × ℝ → ℝ, CylTest c Φ →
      ∫ z in UnforcedLeray.Cyl.cell c,
        (D z 0 * (fderiv ℝ Φ z (0, 1) : ℂ) - D z 1 * (fderiv ℝ Φ z (1, 0) : ℂ)) = 0)
    {χ : ℝ → ℝ} (hχ : UnforcedLeray.Cyl.OneD.Test χ) :
    ∫ z in UnforcedLeray.Cyl.cell c, D z 0 * ((χ z.2 : ℝ) : ℂ) = 0 := by
  have hm : MemLp (fun z : ℝ × ℝ => D z 0) (ENNReal.ofReal r) (UnforcedLeray.Cyl.avgμ c) := by
    refine hD.2.of_le ?_ (Filter.Eventually.of_forall fun z => ?_)
    · exact (EuclideanSpace.proj 0 : CMerid →L[ℂ] ℂ).continuous.comp_aestronglyMeasurable
        hD.2.aestronglyMeasurable
    · exact PiLp.norm_apply_le (D z) 0
  obtain ⟨e, he, hee⟩ := hC c r hc hr.le (fun z => D z 0) hm
  have hder : ∀ ζ : ℝ → ℝ, UnforcedLeray.Cyl.OneD.Test ζ →
      ∫ η, e η * ((deriv ζ η : ℝ) : ℂ) = 0 := by
    intro ζ hζ
    have hΦ : CylTest c (fun z : ℝ × ℝ => ζ z.2) := by
      refine ⟨hζ.smooth.comp contDiff_snd, fun z => rfl, ?_⟩
      obtain ⟨M, -, hM⟩ := hζ.exists_bound
      exact ⟨M, fun z hz => hM z.2 hz.le⟩
    have hfd : ∀ z : ℝ × ℝ, fderiv ℝ (fun y : ℝ × ℝ => ζ y.2) z =
        (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (deriv ζ z.2)).comp
          (ContinuousLinearMap.snd ℝ ℝ ℝ) := fun z =>
      ((hζ.hasDerivAt z.2).hasFDerivAt.comp z (hasFDerivAt_snd)).fderiv
    have e1 : ∀ z : ℝ × ℝ, fderiv ℝ (fun y : ℝ × ℝ => ζ y.2) z (0, 1) = deriv ζ z.2 := by
      intro z; rw [hfd z]; simp
    have e2 : ∀ z : ℝ × ℝ, fderiv ℝ (fun y : ℝ × ℝ => ζ y.2) z (1, 0) = 0 := by
      intro z; rw [hfd z]; simp
    have h := hk _ hΦ
    have hfun : (fun z : ℝ × ℝ =>
        D z 0 * (fderiv ℝ (fun y : ℝ × ℝ => ζ y.2) z (0, 1) : ℂ) -
          D z 1 * (fderiv ℝ (fun y : ℝ × ℝ => ζ y.2) z (1, 0) : ℂ)) =
        fun z => D z 0 * ((deriv ζ z.2 : ℝ) : ℂ) := by
      funext z
      rw [e1 z, e2 z]
      simp
    rw [hfun] at h
    rw [← hee (deriv ζ) hζ.deriv]
    exact h
  have h := hZ r hr e he hder χ hχ
  rw [hee χ hχ]
  exact h


/-! ## The conditional theorem -/

/-- **`CylOfPlaneProps` from the leaves** (`PartII-b:T12/1/5`): a planar Helmholtz pair of
`c`-periodic fields in `L^r(dq/c dη)` is a cylinder Helmholtz pair. -/
theorem cylOfPlaneProps_of (hU : CylUnfold) (hA : CylLpAEMeas) (hI : CylPairingIntegrableOn)
    (hT : CylCutoffTests) (hS : CylStreamDecomp) (hC : CylCellAverage) (hZ : OneDDerivZeroLr) :
    CylOfPlaneProps := by
  intro c r hc hr F G hF hG hH
  obtain ⟨hP1, hP2⟩ := hH
  refine ⟨hG, fun φ hφ => ?_, fun Ψ hΨ => ?_⟩
  · -- weak divergence
    have hg := cyl_weak_div hU hA hI hT hc hr.le hG hP1 hφ
    refine ⟨(cyl_integrable_avg_iff hc).2 hg.1.2.2, ?_⟩
    rw [cyl_integral_avg hc, hg.2, mul_zero]
  · -- orthogonality to solenoidal tests
    have hD : CylLp c r (F - G) := cylLp_sub hF hG
    have hP2' : ∀ Ψ' : ℝ × ℝ → Fin 2 → ℝ, PlaneSolTest Ψ' →
        ∫ z, ∑ i : Fin 2, (F - G) z i * (Ψ' z i : ℂ) = 0 :=
      fun Ψ' h => (hP2 Ψ' h).2
    have hk := fun (Φ : ℝ × ℝ → ℝ) (hΦ : CylTest c Φ) =>
      cyl_orth_stream hU hA hI hT hc hr.le hD hP2' hΦ
    have pa : ∀ i : Fin 2, CylGood c (fun z => (F - G) z i * (Ψ z i : ℂ)) := fun i => by
      obtain ⟨c1, c2, c3⟩ := cylTest_good (hΨ.comp i)
      exact cylGood_pair hA hI hc hr.le hD i c1 c2 c3
    have hsum0 : (fun z : ℝ × ℝ => ∑ i : Fin 2, (F z i - G z i) * (Ψ z i : ℂ)) =
        fun z => (F - G) z 0 * (Ψ z 0 : ℂ) + (F - G) z 1 * (Ψ z 1 : ℂ) := by
      funext z
      simp [Fin.sum_univ_two]
    refine ⟨?_, ?_⟩
    · rw [hsum0, cyl_integrable_avg_iff hc]
      exact (cylGood_add (pa 0) (pa 1)).2.2
    · obtain ⟨Φ, m, hΦ, e0, e1⟩ := hS c Ψ hΨ UnforcedLeray.Cyl.OneD.bump0
        UnforcedLeray.Cyl.OneD.test_bump0 UnforcedLeray.Cyl.OneD.integral_bump0
      have hkΦ := hk Φ hΦ
      have hz := cyl_zero_mode hC hZ hc hr hD (fun Φ' hΦ' => (hk Φ' hΦ').2)
        UnforcedLeray.Cyl.OneD.test_bump0
      have gχ : CylGood c (fun z => (F - G) z 0 * ((UnforcedLeray.Cyl.OneD.bump0 z.2 : ℝ) : ℂ)) := by
        refine cylGood_pair hA hI hc hr.le hD 0
          (UnforcedLeray.Cyl.OneD.test_bump0.continuous.comp continuous_snd)
          (fun z => rfl) ?_
        obtain ⟨M, -, hM⟩ := UnforcedLeray.Cyl.OneD.test_bump0.exists_bound
        exact ⟨M, fun z hz => hM z.2 hz.le⟩
      have hsum : (fun z : ℝ × ℝ => ∑ i : Fin 2, (F z i - G z i) * (Ψ z i : ℂ)) =
          fun z => ((F - G) z 0 * (fderiv ℝ Φ z (0, 1) : ℂ) -
              (F - G) z 1 * (fderiv ℝ Φ z (1, 0) : ℂ)) +
            (m : ℂ) * ((F - G) z 0 * ((UnforcedLeray.Cyl.OneD.bump0 z.2 : ℝ) : ℂ)) := by
        funext z
        simp only [Fin.sum_univ_two, e0 z, e1 z]
        simp
        ring
      rw [hsum, cyl_integral_avg hc, integral_add hkΦ.1.2.2 (gχ.2.2.const_mul (m : ℂ)),
        hkΦ.2, integral_const_mul, hz]
      simp

end UnforcedLeray.Short.IIb

end
