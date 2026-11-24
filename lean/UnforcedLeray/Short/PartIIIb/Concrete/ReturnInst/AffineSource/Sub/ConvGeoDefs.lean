import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_9_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4

/-!
# The convection chart remainder `G` and the decomposition of `GeoConvL2`
# (`PartIII-b:C/asrc/ra/9/2/2`, source 5040-5044, 5034-5039, 2075-2077, 4963-4980)

Source of record: `the November 2 reference manuscript` (73 pages).

## The chart rules (source 5034-5044)

With `s = R²/ϱ²`, `q = Rτ/2 - (R/2) log s`, `η = R z/ϱ`, `ε = R⁻¹`, `𝒦 = η∂_η + 2s∂_s`:
`∂_r = √s(∂_q - ε𝒦)`, `∂_z = √s ∂_η` (`radial_chain`, `axial_chain` of `Lib/Axisymmetric/RingChart`),
hence on a field `√s α` (meridional, no swirl): `∂_r(√s α) = s(∂_q - ε(𝒦+1))α`,
`∂_z(√s α) = s ∂_η α`, `div(√s α) = s(div_{q,η}α - ε𝒦α_r)` (the term `α_r/r = ε s α_r` cancels
the `-ε s α_r` of `∂_r √s`).  For `a = √s α`, `b = √s β` the identity
`div(a⊗b+b⊗a) = (a·∇)b + (b·∇)a + (div a)b + (div b)a` gives the coefficient
`s^{-1/2}·(div(a⊗b+b⊗a))_{r,z} = s·cBil ε α β` with
`cBil ε α β = cB0 α β + ε cB1 α β`,
* `cB0 α β = (α·∇)β + (β·∇)α + (div α)β + (div β)α` (planar, in `(q,η)`),
* `cB1 α β = -[α_r(𝒦+1)β + β_r(𝒦+1)α + (𝒦α_r)β + (𝒦β_r)α]`.

## The remainder `G` (source 5040-5044)

`U_raw = √s[v₁e_r + (v₂ + εH)e_z]` (profile `α = v + εHe_z`, `H = (1-𝒦)ψ`, source 2075-2077) and
`ĥ_A = √s[(h^p)_r e_r + ((h^p)_z + εk)e_z]` (profile `β = h^p + εke_z`, `k = (1-𝒦)ψ^p_A`, source
4980).  Since `div v = 0 = div h^p` (planar, `h^p = J∇ψ^p`), expanding `cB0` bilinearly,
`cBil ε α β - [(v·∇)h^p + (h^p·∇)v] = ε G` with
`G = cB0(He,h^p) + cB0(v,ke) + ε cB0(He,ke) + cB1(α,β)`  (`convG`),
a finite Gaussian-lattice sum of products of `(s∂_s)^i A^y`, Gaussian polynomials and the train
(`H`, `v` and their first `x`-derivatives and `𝒦`).  Thus `geoConvPiece = ε s G` (`ConvChartEq`),
and the cell `L²` norm of `sG` is `≤ P_ν M(A)(s^{5/2}+s^{7/2})` (`ConvGL2`: pointwise lattice
envelope `ConvGEnvelope` from the train band `TrainBand` and the lattice envelope `HpPsiEnv`, then
the uniform cell `L²` bound `GradLatticeL2` of the Gaussian lattice sum).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest Params)

/-! ## 1. Planar chart calculus on profiles `F(s, x)`, `x = (q, η)` -/

/-- `(F·∇)G = DG · F`, planar, at fixed `s`. -/
def cAdv (F G : ℝ → ℝ × ℝ → ℝ × ℝ) (s : ℝ) (x : ℝ × ℝ) : ℝ × ℝ :=
  fderiv ℝ (G s) x (F s x)

/-- `div_{q,η} F = ∂_q F_r + ∂_η F_z`. -/
def cDiv (F : ℝ → ℝ × ℝ → ℝ × ℝ) (s : ℝ) (x : ℝ × ℝ) : ℝ :=
  (fderiv ℝ (F s) x (ei 0)).1 + (fderiv ℝ (F s) x (ei 1)).2

/-- `𝒦 F = η∂_η F + 2s∂_s F`, componentwise. -/
def cK (F : ℝ → ℝ × ℝ → ℝ × ℝ) (s : ℝ) (x : ℝ × ℝ) : ℝ × ℝ :=
  (Kop (fun s' y => (F s' y).1) s x, Kop (fun s' y => (F s' y).2) s x)

/-- Planar part: `(F·∇)G + (G·∇)F + (div F)G + (div G)F`. -/
def cB0 (F G : ℝ → ℝ × ℝ → ℝ × ℝ) (s : ℝ) (x : ℝ × ℝ) : ℝ × ℝ :=
  cAdv F G s x + cAdv G F s x + cDiv F s x • G s x + cDiv G s x • F s x

/-- The `ε`-part: `-[F_r(𝒦+1)G + G_r(𝒦+1)F + (𝒦F_r)G + (𝒦G_r)F]`. -/
def cB1 (F G : ℝ → ℝ × ℝ → ℝ × ℝ) (s : ℝ) (x : ℝ × ℝ) : ℝ × ℝ :=
  -((F s x).1 • (cK G s x + G s x) + (G s x).1 • (cK F s x + F s x) +
    (cK F s x).1 • G s x + (cK G s x).1 • F s x)

/-- The chart bilinear form `cB0 + ε cB1`: the profile of `s^{-1/2}·div(a⊗b+b⊗a)/s`. -/
def cBil (ε : ℝ) (F G : ℝ → ℝ × ℝ → ℝ × ℝ) (s : ℝ) (x : ℝ × ℝ) : ℝ × ℝ :=
  cB0 F G s x + ε • cB1 F G s x

/-- A meridional profile `α : Chart → Merid` as a planar profile `(s, x) ↦ (α_r, α_z)`. -/
def plOf (α : Chart → Merid) : ℝ → ℝ × ℝ → ℝ × ℝ :=
  fun s x => (α (s, x) 0, α (s, x) 1)

/-! ## 2. The data of the level -/

/-- The raw profile `b_raw = (v₁, v₂ + εH)` as a planar profile (source 2075-2077). -/
def rawPl (p : Params) : ℝ → ℝ × ℝ → ℝ × ℝ :=
  plOf (UnforcedLeray.Cons.C03.rawProfile p.ε p.train.v p.train.ψ)

/-- The planar train `v(s, x)` (source 5022). -/
def trPl (p : Params) : ℝ → ℝ × ℝ → ℝ × ℝ := trainPl p.train

/-- `H = (1 - 𝒦)ψ` of the train stream, `H = ψ - η∂_ηψ - 2s∂_sψ` (source 2076). -/
def trH (p : Params) (s : ℝ) (x : ℝ × ℝ) : ℝ :=
  UnforcedLeray.Cons.C03.raisedStream p.train.ψ s x.1 x.2

/-- `H e_z` as a planar profile. -/
def trHe (p : Params) : ℝ → ℝ × ℝ → ℝ × ℝ := fun s x => (0, trH p s x)

/-- `ĥ_A / √s` as a planar profile `(hAcoef)` (source 4980). -/
def hatPl (p : Params) (χf : ℝ → ℝ) (A : ℝ → Mat3) : ℝ → ℝ × ℝ → ℝ × ℝ :=
  plOf (hAcoef p.ν p.ε χf A)

/-- `h^p_A` as a planar profile (source 4973). -/
def hpPl (p : Params) (χf : ℝ → ℝ) (A : ℝ → Mat3) : ℝ → ℝ × ℝ → ℝ × ℝ :=
  hpA p.ν χf A

/-- `k = (1 - 𝒦)ψ^p_A = ψ^p_A - η∂_ηψ^p_A - 2s∂_sψ^p_A` (source 4980). -/
def kOf (ν : ℝ) (χf : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (x : ℝ × ℝ) : ℝ :=
  psipA ν χf A s x - Kop (fun s' y => psipA ν χf A s' y) s x

/-- `k` at the level `p`. -/
def kPl (p : Params) (χf : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (x : ℝ × ℝ) : ℝ :=
  kOf p.ν χf A s x

/-- `k e_z` as a planar profile. -/
def kEz (p : Params) (χf : ℝ → ℝ) (A : ℝ → Mat3) : ℝ → ℝ × ℝ → ℝ × ℝ :=
  fun s x => (0, kPl p χf A s x)

/-- **The remainder `G`** (source 5040-5044): `geoConvPiece = ε s G`,
`G = cB0(He,h^p) + cB0(v,ke) + ε cB0(He,ke) + cB1(α,β)`, `α = rawPl`, `β = hatPl`. -/
def convG (p : Params) (χf : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (x : ℝ × ℝ) : ℝ × ℝ :=
  cB0 (trHe p) (hpPl p χf A) s x + cB0 (trPl p) (kEz p χf A) s x +
    p.ε • cB0 (trHe p) (kEz p χf A) s x + cB1 (rawPl p) (hatPl p χf A) s x

/-! ## 3. The two statements -/

/-- **The exact chart identity** (source 5034-5044, 2075-2077, 4980): for `s > 0`,
`geoConvPiece = ε s · G`. -/
def ConvChartEq (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  IsSourceCutoffC χf → ∀ dm dp : ℝ, 0 < dm →
    ∃ ν₀ : ℝ, 0 < ν₀ ∧
      ∀ (p : Params) (d : ℝ), UnforcedLeray.Short.IIb.BgRegime p d dm dp → p.ν ≤ ν₀ →
      ∀ μ : ℝ, ∀ A : ℝ → Mat3, IsAffElem as A → ∀ s : ℝ, 0 < s → ∀ x : ℝ × ℝ,
        geoConvPiece p μ χf A (s, x) = (p.ε * s) • toMer (convG p χf A s x)

/-- **Gaussian-summation cell `L²` bound of `sG`** (source 5040-5044): independent of `ε`. -/
def ConvGL2 (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  IsSourceCutoffC χf → ∀ dm dp : ℝ, 0 < dm →
    ∃ (C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < ν₀ ∧
      ∀ (p : Params) (d : ℝ), UnforcedLeray.Short.IIb.BgRegime p d dm dp → p.ν ≤ ν₀ →
      ∀ A : ℝ → Mat3, IsAffElem as A → ∀ s : ℝ, 0 < s → s ≤ (11 / 10) / p.ν →
        ∫⁻ x, ENNReal.ofReal (‖s • toMer (convG p χf A s x)‖ ^ 2) ∂(UnforcedLeray.Cyl.avgμ p.c)
          ≤ ENNReal.ofReal ((C * p.ν⁻¹ ^ k * affM p.ν χf A *
              (s ^ (5 / 2 : ℝ) + s ^ (7 / 2 : ℝ))) ^ 2)

/-- `GeoConvL2` from the chart identity and the bound for `sG`. -/
theorem geoConvL2_of (as : ℝ) (χf : ℝ → ℝ) (h1 : ConvChartEq as χf) (h2 : ConvGL2 as χf) :
    GeoConvL2 as χf := by
  intro hχ K _ _ dm dp hdm
  obtain ⟨ν₁, h1pos, H1⟩ := h1 hχ dm dp hdm
  obtain ⟨C, k, ν₂, h2pos, H2⟩ := h2 hχ dm dp hdm
  refine ⟨C, k, min ν₁ ν₂, lt_min h1pos h2pos, fun p d hreg hν μ _ A hA s hs hsT => ?_⟩
  have hν1 : p.ν ≤ ν₁ := hν.trans (min_le_left _ _)
  have hν2 : p.ν ≤ ν₂ := hν.trans (min_le_right _ _)
  have hε : 0 < p.ε := p.ε_pos
  have hpt : ∀ x : ℝ × ℝ, ENNReal.ofReal (‖geoConvPiece p μ χf A (s, x)‖ ^ 2) =
      ENNReal.ofReal (p.ε ^ 2) * ENNReal.ofReal (‖s • toMer (convG p χf A s x)‖ ^ 2) := by
    intro x
    rw [H1 p d hreg hν1 μ A hA s hs x, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [show (p.ε * s) • toMer (convG p χf A s x) = p.ε • (s • toMer (convG p χf A s x)) by
      rw [smul_smul], norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  simp only [hpt]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hb := H2 p d hreg hν2 A hA s hs hsT
  calc ENNReal.ofReal (p.ε ^ 2) * ∫⁻ x, ENNReal.ofReal (‖s • toMer (convG p χf A s x)‖ ^ 2)
          ∂(UnforcedLeray.Cyl.avgμ p.c)
      ≤ ENNReal.ofReal (p.ε ^ 2) * ENNReal.ofReal ((C * p.ν⁻¹ ^ k * affM p.ν χf A *
              (s ^ (5 / 2 : ℝ) + s ^ (7 / 2 : ℝ))) ^ 2) := by gcongr
    _ = ENNReal.ofReal ((C * p.ν⁻¹ ^ k * p.ε * affM p.ν χf A *
              (s ^ (5 / 2 : ℝ) + s ^ (7 / 2 : ℝ))) ^ 2) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring

end UnforcedLeray.Short.PartIIIb.Concrete
