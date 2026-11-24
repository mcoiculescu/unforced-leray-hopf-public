import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_of
import UnforcedLeray.Units.B0224.PlaneHeat
import UnforcedLeray.Units.B0225
import UnforcedLeray.Short.PartIIa.StatementsNear

/-!
# Duhamel representation of `R₀ g` for a smooth force (design for `PartIII-b:C/flatset/col/7/1/1/2/1`)

Source `the November 2 reference manuscript` 1650-1656, 1684-1689.

Key facts (found while designing, see the ledger of the organizer):

* `IsBodyTransport R0 (T0flat hc ν μ)` with `T0flat = R₀ ∘ P₀` (`PartII-a/StatementsNear.lean:121-123`,
  source 1655-1656 `T₀ = (μ - A₀)⁻¹ P₀`).  So `velC (R0 g)` is the Duhamel integral of the Leray
  projection `P₀ g`, not of `g`.
* `B0225.R0_Ms_ae_causalHeat` is the Duhamel formula for `R₀ (M_s G)`, `M_s G = s • G` (`H_g → H`).
  Hence for `P₀ g = M_s G` the density in `H_g` is `G = (P₀ g)/s`, and
  `velC (R0 g) = ∫₀^s (σ/s)^μ e^{ν(s-σ)Δ} G(σ) dσ` with *no* extra `1/σ`.
  `PepsRep c g G` records exactly `P₀ g = s • G` (a.e. on the cell), `IsDriving` the regularity of `G`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.Short.IIIa (vnorm2)

/-- The Duhamel integral `∫₀^s (σ/s)^μ e^{ν(s-σ)Δ_{q,η}} G(σ) dσ` of a `q`-periodic field `G`
(source 1650-1656, `B0225.causalHeat`); `planeHeat` is the planar Gaussian average
(`B0224.planeHeat`, exact for `q`-periodic data, so no periodization is needed). -/
def duhamel (ν μ : ℝ) (G : Chart → Fin 2 → ℝ) (p : Chart) (i : Fin 2) : ℂ :=
  ∫ σ in (0 : ℝ)..p.1, (((σ / p.1 : ℝ) : ℂ) ^ (μ : ℂ)) •
    UnforcedLeray.B0224.planeHeat (ν * (p.1 - σ)) (fun z => ((G (σ, z) i : ℝ) : ℂ)) p.2

/-- The regularity class of the `H_g`-density `G` of the Leray-projected smooth force
`P₀ g = s • G` (source 1650-1656, 1684-1689): smooth, `q`-periodic, supported in `s ∈ [s₀, s₁]`
with `0 < s₀` (the force is supported away from `s = 0`), all derivatives bounded. -/
def IsDriving (c : ℝ) (G : Chart → Fin 2 → ℝ) : Prop :=
  (∀ i, ContDiff ℝ ∞ fun p => G p i) ∧
  (∀ s q η, G (s, (q + c, η)) = G (s, (q, η))) ∧
  (∃ s0 s1 : ℝ, 0 < s0 ∧ ∀ p, G p ≠ 0 → p.1 ∈ Icc s0 s1) ∧
  ∀ (i : Fin 2) (n : ℕ), ∃ C : ℝ, ∀ p, ‖iteratedFDeriv ℝ n (fun p : Chart => G p i) p‖ ≤ C

/-- `G` represents the flat Leray projection of the smooth force `g` as an `H_g`-density:
for every `H`-representative `f'` of `g` (complexified, on the `PartII-a` cell), `P₀ f' = s • G`
a.e. on the cell (`PepsC` is the orthogonal projection onto `solenoidalHC 0 c`,
`PartII-a/StatementsNear.lean:112`; source 1655-1656, 1676). -/
def PepsRep (c : ℝ) (g : Hsp c) (G : Chart → Fin 2 → ℝ) : Prop :=
  ∀ f' : UnforcedLeray.B0220.HSpace c UnforcedLeray.B0223.MeridC,
    (f' : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC)
        =ᵐ[UnforcedLeray.B0220.measureH c] (fun p => NearInst.merC (g (NearInst.cellPt c p))) →
      ((UnforcedLeray.Short.PartIIa.PepsC 0 c f' : UnforcedLeray.B0220.HSpace c
          UnforcedLeray.B0223.MeridC) : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC)
        =ᵐ[UnforcedLeray.B0220.measureH c]
        fun p => WithLp.toLp 2 (fun i : Fin 2 => ((p.1 * G (NearInst.cellPt c p) i : ℝ) : ℂ))

/-- **Bridge** `IsBodyTransport` → Duhamel (source 1650-1656, `R0_Ms_ae_causalHeat`). -/
def DuhamelBridge : Prop :=
  ∀ (c ν μ : ℝ) (hc : 0 < c) (R0 : Hsp c →L[ℝ] Hsp c) (g : Hsp c) (G : Chart → Fin 2 → ℝ),
    ClassicalCtx c ν μ hc R0 g → IsDriving c G → PepsRep c g G →
      NearInst.velC (R0 g) =ᵐ[ageμ c (-3 / 2)] fun p i => duhamel ν μ G p i

/-- **Smoothness** of the Duhamel integral for `s > 0` (source 1684-1689). -/
def DuhamelSmooth : Prop :=
  ∀ (c ν μ : ℝ) (G : Chart → Fin 2 → ℝ), IsDriving c G → 0 < ν → ∀ i : Fin 2,
    ContDiffOn ℝ ∞ (fun p => duhamel ν μ G p i) (Ioi (0 : ℝ) ×ˢ univ)

/-- **Periodicity** of the Duhamel integral for `s > 0`. -/
def DuhamelPeriodic : Prop :=
  ∀ (c ν μ : ℝ) (G : Chart → Fin 2 → ℝ), IsDriving c G → ∀ s q η : ℝ, 0 < s →
    duhamel ν μ G (s, (q + c, η)) = duhamel ν μ G (s, (q, η))

/-- **Slice bounds** of the Duhamel integral and its cell gradient (source 1684-1689). -/
def DuhamelSliceBound : Prop :=
  ∀ (c ν μ : ℝ) (G : Chart → Fin 2 → ℝ), IsDriving c G → 0 < ν → ∀ s : ℝ, 0 < s →
    ∃ C : ℝ, ∀ x : ℝ × ℝ, vnorm2 (duhamel ν μ G (s, x)) ≤ C ∧
      ∀ i j, ‖cellGrad (duhamel ν μ G) (s, x) i j‖ ≤ C

/-- **Leray representative** (source 1655-1656, 1676): the flat Leray projection of a smooth force
has an `H_g`-density in the class `IsDriving`. -/
def LerayDriving : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ g : Hsp c, IsSmoothForce c g → ∃ G : Chart → Fin 2 → ℝ,
    IsDriving c G ∧ PepsRep c g G

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
