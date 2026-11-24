import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Leaves
import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Setting
import UnforcedLeray.Units.B0610

/-!
# `FlatForceCurl` from four source facts (decomposition of `PartIII-b:C/flatset/col/1`)

Source of record `the November 2 reference manuscript`: 4594-4608 (`f_B`, its
vorticity `g_B = -½(d-ie)H - ½(d+ie)H̄ - βR`), 4963-4976 (the lattice sums), 4988 (Gaussian decay,
"the sums and their required derivatives converge").

`f_A = -(∑'_j fTerm)` (`merOf`, components `0, 1`) is a smooth `cOf ν`-periodic planar field
(`FlatForceSmooth`, `FlatForcePeriodic`), whose pointwise curl is `-∑'_j curlTermProf`
(`FlatForceCurlTsum`, from `flatCurlTerm` termwise), which is `g_B` (`FlatForceGB`).  The tested form
is integration by parts for smooth periodic functions against cylinder tests
(`B0610.hasWeakCellDeriv_of_smooth`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ComplexConjugate ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- The meridional component `i` (`0 = q`, `1 = η`) of the affine force `f_A` at age `s`. -/
def fMer (ν μ : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (i : Fin 2) (x : ℝ × ℝ) : ℝ :=
  merOf (fA ν μ χ A s x) i

/-- **(1) Smoothness of `f_A` in the plane** (source 4594-4596, 4988: "the sums and their required
derivatives converge by Gaussian decay"): `fMer` is `C^∞`.  Route: `fMer ... i x = -∑' j, (fTerm ν s B
j x).i` (unfold `fA`, `Concrete.emb`, `mv`, `merOf`; coordinate projections commute with `tsum` by
summability, Gaussian lattice bounds as in `Concrete/SummableProof.lean`); each term is `C^∞`
(`Vj` is a Gaussian times `Jrot x_j`; `fderiv` of it is `C^∞`); termwise differentiation of all
orders with locally uniform Gaussian bounds (`contDiff_tsum`, or `hasFDerivAt_tsum` inductively). -/
def FlatForceSmooth : Prop :=
  ∀ (ν μ : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ), 0 < ν → 0 < s → ∀ i : Fin 2,
    ContDiff ℝ ∞ (fMer ν μ χ A s i)

/-- **(2) Periodicity of `f_A` in `q`** (source 4594: the lattice sum over `j ∈ ℤ` with
`x_j = (q - jc, η)`): `fMer ... i (q + c, η) = fMer ... i (q, η)` for `c = cOf ν`.  Route:
`xj ν j (q + c, η) = xj ν (j - 1) (q, η)`, so `fTerm ν s B j (q + c, η) = fTerm ν s B (j-1) (q, η)`
(`Vj`, `fderiv` of a translate), and reindex the `tsum` by `Equiv.subRight 1` (`Equiv.tsum_eq`);
or directly for `fA`. -/
def FlatForcePeriodic : Prop :=
  ∀ (ν μ : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ), 0 < ν → 0 < s → ∀ (i : Fin 2) (x : ℝ × ℝ),
    fMer ν μ χ A s i (x.1 + cOf ν, x.2) = fMer ν μ χ A s i x

/-- **(3) The pointwise curl of `f_A` is the lattice sum of the term curls** (source 4597-4608,
4963-4976; `flatCurlTerm`, `Proofs/FlatCurlTerm.lean`): `∂_q f_η - ∂_η f_q = -∑'_j
curlTermProf (ageA ν s) B (xj ν j x)`, `B = Bmat ν μ χ A s`.  Route: as in (1), `fMer ... i = -∑'_j
(fTerm ..).i`; `hasFDerivAt_tsum` (or `hasDerivAt_tsum`) in each of the lines `q ↦ (q, η)`,
`η ↦ (q, η)` with locally uniform Gaussian bounds for the derivatives of the terms, so the
derivatives of the sum are the sums of the derivatives; then `∑'` of
`flatCurlTerm` (`B0579.pd` is `fderiv` along `dir j`, `B0579.hasDerivAt_fst` converts to `deriv`);
summability of the term curls by the Gaussian bound `|curlTermProf a B y| ≤ C(1+|y|²)e^{-|y|²/(4a)}`. -/
def FlatForceCurlTsum : Prop :=
  ∀ (ν μ : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ), 0 < ν → 0 < s → ∀ x : ℝ × ℝ,
    B0579.pd 0 (fMer ν μ χ A s 1) x - B0579.pd 1 (fMer ν μ χ A s 0) x =
      -∑' j : ℤ, curlTermProf (ageA ν s) (Bmat ν μ χ A s) (xj ν j x)

/-- **(4) The lattice sum of the term curls is `g_B`** (source 4597-4608: "the vorticity source is
`g_B = -½(d-ie)H_{s,c} - ½(d+ie)H̄_{s,c} - βR_{s,c}`"): for `c = cOf ν`, `s > 0`, `B = Bmat ν μ χ A s`,
`gBProf ν (cOf ν) s B x = ((-∑'_j curlTermProf (ageA ν s) B (xj ν j x) : ℝ) : ℂ)`.  Route:
`HProf ν c s x = IIIa.periodizeC c (hMode a) x = ∑' n, hMode a (x.1 - n c, x.2) = ∑' j, hMode a (xj ν j x)`
(`srcA ν s = ageA ν s` for `s > 0`; same for `RProf`, `rMode`); summability of the three lattice
sums by the Gaussian bound (`Concrete/SummableProof.lean`); `conj` commutes with `tsum`
(`Complex.conj_tsum`); per-term algebra `-(1/2)(d-ie)·hMode a y - (1/2)(d+ie)·conj(hMode a y) -
β·rMode a y = -(curlTermProf a B y : ℂ)` with `hMode a y = (gaussRdE a |y| : ℂ)·IIIa.angTwo y`,
`IIIa.angTwo y = (y.1+y.2 i)²/(y.1²+y.2²)`, `rMode a y = gaussRdE + 2 gaussE`, and `Bd, Be, Bbeta`
of `ConcreteYF` (at `y = 0` both sides are `-2βE(0)`: `gaussRdE a 0 = 0`, `angTwo 0` is a junk value
multiplied by `0`); then `tsum` linearity. -/
def FlatForceGB : Prop :=
  ∀ (ν μ : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ), 0 < ν → 0 < s → ∀ x : ℝ × ℝ,
    gBProf ν (cOf ν) s (Bmat ν μ χ A s) x =
      ((-∑' j : ℤ, curlTermProf (ageA ν s) (Bmat ν μ χ A s) (xj ν j x) : ℝ) : ℂ)

/-- A continuous function on the plane vanishing for `|η| > R` is integrable on the cell. -/
theorem integrableOn_cell_of_band {c R : ℝ} {g : ℝ × ℝ → ℝ} (hg : Continuous g)
    (hv : ∀ x : ℝ × ℝ, R < |x.2| → g x = 0) : IntegrableOn g (B0579.cell c) :=
  B0579.integrableOn_cell_of_continuous hg (B0579.isCompact_box c R) fun x hx hxK =>
    hv x (by
      by_contra h
      exact hxK (B0579.mem_box_of_mem_cell hx (not_lt.1 h)))

/-- **`FlatForceCurl`** from smoothness, periodicity, the termwise curl and the identification with
`g_B`. -/
theorem flatForceCurl_of (h1 : FlatForceSmooth) (h2 : FlatForcePeriodic)
    (h3 : FlatForceCurlTsum) (h4 : FlatForceGB) : FlatForceCurl := by
  intro ν μ χ A s hν hs ψ hψ
  set f0 := fMer ν μ χ A s 0 with hf0
  set f1 := fMer ν μ χ A s 1 with hf1
  have s0 : ContDiff ℝ ∞ f0 := h1 ν μ χ A s hν hs 0
  have s1 : ContDiff ℝ ∞ f1 := h1 ν μ χ A s hν hs 1
  have p0 : ∀ x : ℝ × ℝ, f0 (x.1 + cOf ν, x.2) = f0 x := h2 ν μ χ A s hν hs 0
  have p1 : ∀ x : ℝ × ℝ, f1 (x.1 + cOf ν, x.2) = f1 x := h2 ν μ χ A s hν hs 1
  -- bands of the test derivatives
  obtain ⟨R0, hR0⟩ := hψ.exists_band_pd 0
  obtain ⟨R1, hR1⟩ := hψ.exists_band_pd 1
  have hd0 : ∀ x : ℝ × ℝ, max R0 R1 < |x.2| → B0579.pd 0 ψ x = 0 := fun x hx =>
    (hR0 x (lt_of_le_of_lt (le_max_left _ _) hx)).2
  have hd1 : ∀ x : ℝ × ℝ, max R0 R1 < |x.2| → B0579.pd 1 ψ x = 0 := fun x hx =>
    (hR1 x (lt_of_le_of_lt (le_max_right _ _) hx)).2
  have c0 : Continuous (B0579.pd 0 ψ) := (B0579.contDiff_pd hψ.smooth 0).continuous
  have c1 : Continuous (B0579.pd 1 ψ) := (B0579.contDiff_pd hψ.smooth 1).continuous
  have i0 : IntegrableOn (fun x => f0 x * B0579.pd 1 ψ x) (B0579.cell (cOf ν)) :=
    integrableOn_cell_of_band (R := max R0 R1) (s0.continuous.mul c1) fun x hx => by
      simp [hd1 x hx]
  have i1 : IntegrableOn (fun x => f1 x * B0579.pd 0 ψ x) (B0579.cell (cOf ν)) :=
    integrableOn_cell_of_band (R := max R0 R1) (s1.continuous.mul c0) fun x hx => by
      simp [hd0 x hx]
  refine ⟨i0.sub i1, ?_⟩
  -- weak derivatives of the smooth periodic components
  have w0 := B0610.hasWeakCellDeriv_of_smooth s0 p0 1 ψ hψ
  have w1 := B0610.hasWeakCellDeriv_of_smooth s1 p1 0 ψ hψ
  -- the real identity
  have hreal : ∫ x in B0579.cell (cOf ν), (f0 x * B0579.pd 1 ψ x - f1 x * B0579.pd 0 ψ x) =
      ∫ x in B0579.cell (cOf ν),
        (B0579.pd 0 f1 x - B0579.pd 1 f0 x) * ψ x := by
    have j0 : IntegrableOn (fun x => B0579.pd 1 f0 x * ψ x) (B0579.cell (cOf ν)) := by
      obtain ⟨R, hR⟩ := hψ.band
      exact integrableOn_cell_of_band (R := R)
        (((B0579.contDiff_pd s0 1).continuous).mul hψ.continuous) fun x hx => by simp [hR x hx]
    have j1 : IntegrableOn (fun x => B0579.pd 0 f1 x * ψ x) (B0579.cell (cOf ν)) := by
      obtain ⟨R, hR⟩ := hψ.band
      exact integrableOn_cell_of_band (R := R)
        (((B0579.contDiff_pd s1 0).continuous).mul hψ.continuous) fun x hx => by simp [hR x hx]
    rw [integral_sub i0 i1]
    simp only [sub_mul]
    rw [integral_sub j1 j0]
    have e0 : ∫ x in B0579.cell (cOf ν), f0 x * B0579.pd 1 ψ x =
        -∫ x in B0579.cell (cOf ν), B0579.pd 1 f0 x * ψ x := w0
    have e1 : ∫ x in B0579.cell (cOf ν), f1 x * B0579.pd 0 ψ x =
        -∫ x in B0579.cell (cOf ν), B0579.pd 0 f1 x * ψ x := w1
    rw [e0, e1]
    ring
  -- pointwise identification of the source
  have hpt : ∀ x : ℝ × ℝ, gBProf ν (cOf ν) s (Bmat ν μ χ A s) x =
      ((B0579.pd 0 f1 x - B0579.pd 1 f0 x : ℝ) : ℂ) := fun x => by
    rw [h4 ν μ χ A s hν hs x, h3 ν μ χ A s hν hs x]
  have hc : ∫ x in B0579.cell (cOf ν), gBProf ν (cOf ν) s (Bmat ν μ χ A s) x * (ψ x : ℂ) =
      ((∫ x in B0579.cell (cOf ν), (B0579.pd 0 f1 x - B0579.pd 1 f0 x) * ψ x : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [hpt x]
    push_cast
    ring
  rw [hc]
  exact congrArg (fun r : ℝ => (r : ℂ)) hreal

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
