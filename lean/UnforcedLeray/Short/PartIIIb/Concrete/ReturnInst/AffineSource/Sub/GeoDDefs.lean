import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_9_1
import UnforcedLeray.Lib.Axisymmetric.RingChart

/-!
# `PartIII-b:C/asrc/ra/9/1/2` : the remainder `G` of `D_μ ĥ_A` and its ring-chart identity

Source of record: `the November 2 reference manuscript` (73 pages), lines 5034-5039
(ring-chart rules, second order), 4979-4980 (`ĥ_A`), 5063-5079 (Gaussian cell norms, derivative
budget).

With `b = s^{-1/2} ĥ_A = h^p_A + ε(0, (1-𝒦)ψ^p_A)` (`hbM`), the rules
`(∂_τ - y·∇/2 - 1/2)(√s b) = s^{3/2}∂_s b` and
`Δ(√s b) = s^{3/2}{[Δ_{q,η} - 2ε(𝒦+1)∂_q + ε²(𝒦+1)²] b - ε² b_r e_r}` give the chart coefficient

`coefOf R (D_μ (𝒩_v b)) = s (∂_s + μ/s - νΔ_{q,η}) b + ε s · ν[2(𝒦+1)∂_q b - ε(𝒦+1)² b + ε b_r e_r]`.

Subtracting `s (∂_s + μ/s - νΔ)h^p_A` (the planar bracket of `r_per`) leaves exactly `ε s G`,
`G = (∂_s + μ/s - νΔ)Θ + ringRem b`, `Θ = (0, (1-𝒦)ψ^p_A)`.

* `Kc`, `K1`, `Dc`, `ringRem` : the chart operators on `Chart → E`;
* `geoDG` : the remainder `G`;
* `GeoDChartId` : the exact identity `geoDPiece = ε s G` (second-order ring-chart rules);
* `GeoGCellL2` : the Gaussian-summation cell `L²` bound of `G`;
* `geoDL2_of` : `GeoDL2` from the two (algebra).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest Params)

/-! ## 1. Chart operators (source 5034-5039) -/

section Ops

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `𝒦 F = η∂_η F + 2s∂_s F` (source 4979). -/
def Kc (F : Chart → E) : Chart → E := fun p => (2 * p.1) • UnforcedLeray.Axi.dS F p + p.2.2 • UnforcedLeray.Axi.dEta F p

/-- `(𝒦 + 1) F`. -/
def K1 (F : Chart → E) : Chart → E := fun p => Kc F p + F p

/-- `Δ_{q,η} F = ∂_q² F + ∂_η² F`. -/
def lapQE (F : Chart → E) : Chart → E := fun p => UnforcedLeray.Axi.dQ (UnforcedLeray.Axi.dQ F) p + UnforcedLeray.Axi.dEta (UnforcedLeray.Axi.dEta F) p

/-- `(∂_s + μ/s - νΔ_{q,η}) F` (source 5022-5023). -/
def Dc (ν μ : ℝ) (F : Chart → E) : Chart → E :=
  fun p => UnforcedLeray.Axi.dS F p + (μ / p.1) • F p - ν • lapQE F p

end Ops

/-- `b_r e_r` for a meridional vector `b = (b_r, b_z)`. -/
def erProj (v : Merid) : Merid := !₂[v 0, 0]

/-- The second-order ring-chart remainder (source 5034-5036):
`ν[2(𝒦+1)∂_q b - ε(𝒦+1)² b + ε b_r e_r]`, the part of
`s^{-3/2}·(-νΔ)(√s b)` beyond `-νΔ_{q,η} b`, divided by `ε`. -/
def ringRem (ν ε : ℝ) (F : Chart → Merid) : Chart → Merid :=
  fun p => ν • ((2 : ℝ) • K1 (UnforcedLeray.Axi.dQ F) p - ε • K1 (K1 F) p + ε • erProj (F p))

/-! ## 2. The affine fields on the chart -/

/-- `h^p_A` as a chart function `Chart → Merid`. -/
def hpM (ν : ℝ) (χf : ℝ → ℝ) (A : ℝ → Mat3) : Chart → Merid :=
  fun p => toMer (hpA ν χf A p.1 p.2)

/-- `ψ^p_A` as a chart function. -/
def psiM (ν : ℝ) (χf : ℝ → ℝ) (A : ℝ → Mat3) : Chart → ℝ :=
  fun p => psipA ν χf A p.1 p.2

/-- The stream completion `Θ = (0, (1 - 𝒦)ψ^p_A)` (source 4979-4980). -/
def thetaM (ν : ℝ) (χf : ℝ → ℝ) (A : ℝ → Mat3) : Chart → Merid :=
  fun p => toMer (0, psipA ν χf A p.1 p.2 - Kop (fun s' y => psipA ν χf A s' y) p.1 p.2)

/-- `b = s^{-1/2} ĥ_A = h^p_A + ε Θ` (source 4979-4980). -/
def hbM (ν ε : ℝ) (χf : ℝ → ℝ) (A : ℝ → Mat3) : Chart → Merid :=
  hpM ν χf A + ε • thetaM ν χf A

/-- **The remainder `G`** (source 5034-5039): `geoDPiece = ε s G`,
`G = (∂_s + μ/s - νΔ_{q,η})Θ + ν[2(𝒦+1)∂_q b - ε(𝒦+1)²b + εb_re_r]`, `b = hbM`. -/
def geoDG (ν μ ε : ℝ) (χf : ℝ → ℝ) (A : ℝ → Mat3) : Chart → Merid :=
  fun p => Dc ν μ (thetaM ν χf A) p + ringRem ν ε (hbM ν ε χf A) p

/-! ## 3. The two statements -/

/-- **Chart identity** (source 5034-5039): on `s > 0`, `geoDPiece = ε s G`; this is the second-order
ring-chart rule extending `radial_chain`/`axial_chain` of `Lib/Axisymmetric/RingChart.lean`, the
vector Laplacian `vecLap_liftMer`, and the stream completion of `ĥ_A`. -/
def GeoDChartId (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  IsSourceCutoffC χf → ∀ (p : Params), p.c = cOf p.ν → ∀ (μ : ℝ) (A : ℝ → Mat3),
    IsAffElem as A → ∀ q : Chart, 0 < q.1 →
      geoDPiece p μ χf A q = (p.ε * q.1) • geoDG p.ν μ p.ε χf A q

/-- **Gaussian-summation cell bound** (source 5039-5041, 5063-5079): the cell `L²` norm of `G` is
`≤ P_ν M(A)(s^{3/2} + s^{5/2})`, uniformly in the background regime, `μ ∈ K ⋐ (0,1/4)`. -/
def GeoGCellL2 (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  IsSourceCutoffC χf → ∀ K : Set ℝ, IsCompact K → K ⊆ Ioo 0 (1 / 4) → ∀ dm dp : ℝ, 0 < dm →
    ∃ (C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < ν₀ ∧
      ∀ (p : Params) (d : ℝ), UnforcedLeray.Short.IIb.BgRegime p d dm dp → p.ν ≤ ν₀ →
      ∀ μ ∈ K, ∀ A : ℝ → Mat3, IsAffElem as A →
        ∀ s : ℝ, 0 < s → s ≤ (11 / 10) / p.ν →
          ∫⁻ x, ENNReal.ofReal (‖geoDG p.ν μ p.ε χf A (s, x)‖ ^ 2) ∂(UnforcedLeray.Cyl.avgμ p.c)
            ≤ ENNReal.ofReal ((C * p.ν⁻¹ ^ k * affM p.ν χf A *
                (s ^ (3 / 2 : ℝ) + s ^ (5 / 2 : ℝ))) ^ 2)

/-- `GeoDL2` from the chart identity and the cell bound of `G` (algebra: the factor `ε s` turns
`s^{3/2} + s^{5/2}` into `ε(s^{5/2} + s^{7/2})`). -/
theorem geoDL2_of (as : ℝ) (χf : ℝ → ℝ) (h1 : GeoDChartId as χf) (h2 : GeoGCellL2 as χf) :
    GeoDL2 as χf := by
  intro hχ K hK hKs dm dp hdm
  obtain ⟨C, k, ν₀, hν₀, H⟩ := h2 hχ K hK hKs dm dp hdm
  refine ⟨C, k, ν₀, hν₀, fun p d hreg hν μ hμ A hA s hs hs1 => ?_⟩
  have hc : p.c = cOf p.ν := hreg.c_eq
  have hε : 0 < p.ε := p.ε_pos
  have hid : ∀ x : ℝ × ℝ, geoDPiece p μ χf A (s, x) =
      (p.ε * s) • geoDG p.ν μ p.ε χf A (s, x) := fun x => h1 hχ p hc μ A hA (s, x) hs
  have hsum : s ^ (5 / 2 : ℝ) + s ^ (7 / 2 : ℝ) = s * (s ^ (3 / 2 : ℝ) + s ^ (5 / 2 : ℝ)) := by
    have e1 : s ^ (5 / 2 : ℝ) = s * s ^ (3 / 2 : ℝ) := by
      rw [show (5 / 2 : ℝ) = 1 + 3 / 2 by norm_num, Real.rpow_add hs, Real.rpow_one]
    have e2 : s ^ (7 / 2 : ℝ) = s * s ^ (5 / 2 : ℝ) := by
      rw [show (7 / 2 : ℝ) = 1 + 5 / 2 by norm_num, Real.rpow_add hs, Real.rpow_one]
    rw [e2, e1]; ring
  have hH := H p d hreg hν μ hμ A hA s hs hs1
  have hεs : 0 ≤ p.ε * s := by positivity
  calc ∫⁻ x, ENNReal.ofReal (‖geoDPiece p μ χf A (s, x)‖ ^ 2) ∂(UnforcedLeray.Cyl.avgμ p.c)
      = ∫⁻ x, ENNReal.ofReal ((p.ε * s) ^ 2) *
          ENNReal.ofReal (‖geoDG p.ν μ p.ε χf A (s, x)‖ ^ 2) ∂(UnforcedLeray.Cyl.avgμ p.c) := by
        refine lintegral_congr fun x => ?_
        rw [hid x, norm_smul, Real.norm_of_nonneg hεs, mul_pow,
          ENNReal.ofReal_mul (by positivity)]
    _ = ENNReal.ofReal ((p.ε * s) ^ 2) *
          ∫⁻ x, ENNReal.ofReal (‖geoDG p.ν μ p.ε χf A (s, x)‖ ^ 2)
            ∂(UnforcedLeray.Cyl.avgμ p.c) := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal ((p.ε * s) ^ 2) *
          ENNReal.ofReal ((C * p.ν⁻¹ ^ k * affM p.ν χf A *
            (s ^ (3 / 2 : ℝ) + s ^ (5 / 2 : ℝ))) ^ 2) := by gcongr
    _ = ENNReal.ofReal ((C * p.ν⁻¹ ^ k * p.ε * affM p.ν χf A *
            (s ^ (5 / 2 : ℝ) + s ^ (7 / 2 : ℝ))) ^ 2) := by
        rw [← ENNReal.ofReal_mul (by positivity), hsum]
        congr 1
        ring

end UnforcedLeray.Short.PartIIIb.Concrete
