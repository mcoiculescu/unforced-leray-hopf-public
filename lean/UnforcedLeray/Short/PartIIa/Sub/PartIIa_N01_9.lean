import UnforcedLeray.Short.PartIIa.Sub.N01.FlatReduction
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_2
import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Proofs.CompactWindow.Comparison.FlatStress.FlatStressFree.TensorDivIBP

/-!
# `PartII-a:N01/9` (decomposition): `FlatColumnC` from the complex-`μ` body column

Source of record `the November 2 reference manuscript`:
1650-1658 (`A₀ = -S + νsΔ`), 1669-1674 (`T₀ = (μ - A₀)⁻¹P₀`), 1661-1664 at `ε = 0`,
1684-1689 (flat equation `(∂_s + μ/s - νΔ)b = P₀ div₀ M`, pairing with `s^{-1/2} b̄`),
3420-3440 (causal zero-entrance energy class), 3541-3552 (energy identity).

The real-`μ`, real-tensor route (`FlatSettingInst.BodyColumnFlat`) uses a real form of `T0flat`;
for complex `μ` the column is therefore stated directly for `velF c (T0flat hc ν μ G)`.  Two analytic
leaves (energy class, weak equation); the null-set redefinition (`energyNullModification`) and the
tensor integration by parts (`tensorDivIBP`) are accepted.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIa.N01

open UnforcedLeray.B0220 (Profile HSpace measureH)
open UnforcedLeray.B0223 (MeridC)
open UnforcedLeray.Short.PartIIIb.Concrete (Chart)
open UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
  (IsEnergyFieldAE IsEnergyField IsForcedColumn forcedIntegrand)
open UnforcedLeray.Short.PartIIIb.NearInst.Delta (velF tblkF tvBlk)
open UnforcedLeray.Short.IIIa (IsCausalEnergySolution flatIntegrand IsFlatTest flatGrad)

/-- **Leaf `N01/9/1` — the complex-`μ` body column lies in the energy class** (lines 1684-1689:
pairing with `s^{-1/2} b̄` gives `(Re μ + 1/4)‖b‖²_𝓗 + ν‖∇b‖²_𝒯 ≤ ‖h‖_𝓗‖b‖_𝓗`; 3426-3430;
`B0225.R0_Ms_ae`: `R₀(μ)M_s g(s) = ∫₀^s (σ/s)^μ e^{ν(s-σ)Δ} g(σ)dσ` holds for complex `μ`).
For smooth tensor tests `M` and `G = s div₀ M` a.e., `velF c (T0flat hc ν μ G)` has a weak gradient
`Gr` in the energy class (`divFree`, `weakGrad` for a.e. age). -/
def BodyColumnEnergyC : Prop :=
  ∀ (c ν : ℝ) (hc : 0 < c), 0 < ν → ∀ μ : ℂ, 0 < μ.re + 1 / 4 →
    ∀ M : Profile → TensorVal, IsTensorTest c M → ∀ G : HSpace c MeridC,
      (G : Profile → MeridC) =ᵐ[measureH c] (fun p => (p.1 : ℂ) • divEps 0 M p) →
      ∃ (b : Chart → Fin 2 → ℂ) (Gr : Chart → Fin 2 → Fin 2 → ℂ),
        b =ᵐ[ageμ c (-3 / 2)] velF c (T0flat hc ν μ G) ∧ IsEnergyFieldAE c b Gr

/-- **Leaf `N01/9/2` — the weak equation of the complex-`μ` body column** (lines 1650-1658,
1669-1674, 1684-1689; `B0225.R0_apply`, `R0_ae_eq`; `T0flat = R0 ∘ PepsC 0 c`; `PepsC 0 c` is the
orthogonal projection onto `solenoidalHC 0 c`, so `⟨P₀ h, ζ⟩ = ⟨h, ζ⟩` for divergence-free `ζ`; the
Laplace transform of `d/dt ⟨T₀(t)f, ζ⟩ = ⟨T₀(t)f, A₀*ζ⟩`): for a flat test `Φ`,
`∬ forcedIntegrand ν μ 0 (div₀ M) (velF c (T0flat G)) Φ = 0` with the integrand integrable. -/
def BodyColumnWeakC : Prop :=
  ∀ (c ν : ℝ) (hc : 0 < c), 0 < ν → ∀ μ : ℂ, 0 < μ.re + 1 / 4 →
    ∀ M : Profile → TensorVal, IsTensorTest c M → ∀ G : HSpace c MeridC,
      (G : Profile → MeridC) =ᵐ[measureH c] (fun p => (p.1 : ℂ) • divEps 0 M p) →
      ∀ Φ, IsFlatTest c Φ →
        IntegrableOn (forcedIntegrand ν μ (fun _ _ _ => 0) (fun x i => divEps 0 M x i)
            (velF c (T0flat hc ν μ G)) Φ) (Ioi (0 : ℝ) ×ˢ B0579.cell c) ∧
          ∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c,
            forcedIntegrand ν μ (fun _ _ _ => 0) (fun x i => divEps 0 M x i)
              (velF c (T0flat hc ν μ G)) Φ p = 0

theorem n01_forcedIntegrand_congr_ae {c ν : ℝ} (hc : 0 < c) {μ : ℂ}
    {f b b' : Chart → Fin 2 → ℂ} (Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ)
    (h : b =ᵐ[ageμ c (-3 / 2)] b') :
    forcedIntegrand ν μ (fun _ _ _ => 0) f b Φ =ᵐ[(volume : Measure (ℝ × (ℝ × ℝ))).restrict
      (Ioi (0 : ℝ) ×ˢ B0579.cell c)] forcedIntegrand ν μ (fun _ _ _ => 0) f b' Φ := by
  have h' := (UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.volCyl_ac_ageμ hc
    (-3 / 2)).ae_le h
  filter_upwards [h'] with p hp
  unfold forcedIntegrand flatIntegrand
  rw [hp]

/-- **`FlatColumnC` from the two leaves** (copy of `bodyColumnFlat_of` and `smoothStressColumn_of`
with complex `μ` and complex `M`; no realness is used). -/
theorem flatColumnC_of (hE : BodyColumnEnergyC) (hW : BodyColumnWeakC) : FlatColumnC := by
  intro c ν hc hν μ hμ M hM G hG
  obtain ⟨b₁, G₁, hb₁, hE₁⟩ := hE c ν hc hν μ hμ M hM G hG
  obtain ⟨b, Gr, hb', hEF⟩ :=
    UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.energyNullModification c hc b₁ G₁ hE₁
  have hbb : b =ᵐ[ageμ c (-3 / 2)] velF c (T0flat hc ν μ G) := hb'.trans hb₁
  refine ⟨b, Gr, hbb, ?_⟩
  have h2 := UnforcedLeray.Short.PartIIIb.NearInst.Delta.tensorDivIBP
  have hper : ∀ x : Chart, M (UnforcedLeray.Short.PartIIIb.NearInst.Masked.cellPtInv c x) = M x :=
    fun x => UnforcedLeray.Short.PartIIIb.NearInst.Delta.fsf_cellPtInv_periodic hM.periodic x
  have hcol : ∀ Φ, IsFlatTest c Φ →
      IntegrableOn (forcedIntegrand ν μ (fun _ _ _ => 0) (fun x i => divEps 0 M x i) b Φ)
        (Ioi (0 : ℝ) ×ˢ B0579.cell c) ∧
      ∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c,
        forcedIntegrand ν μ (fun _ _ _ => 0) (fun x i => divEps 0 M x i) b Φ p = 0 := by
    intro Φ hΦ
    have := hW c ν hc hν μ hμ M hM G hG Φ hΦ
    refine ⟨this.1.congr (n01_forcedIntegrand_congr_ae hc Φ hbb.symm), ?_⟩
    rw [← this.2]
    exact integral_congr_ae (n01_forcedIntegrand_congr_ae hc Φ hbb)
  have key : ∀ Φ p, flatIntegrand ν μ (fun _ _ _ => 0) (tblkF c M) b Φ p =
      forcedIntegrand ν μ (fun _ _ _ => 0) (fun x i => divEps 0 M x i) b Φ p +
        ∑ i : Fin 2, (divEps 0 M p i * (Φ p.1 p.2 i : ℂ) +
          ∑ j : Fin 2, tvBlk (M p) i j * (flatGrad Φ p.1 p.2 i j : ℂ)) := by
    intro Φ p
    simp only [forcedIntegrand, flatIntegrand, tblkF, hper p, Fin.sum_univ_two,
      Complex.ofReal_zero, zero_mul, mul_zero, add_zero, sub_zero]
    ring
  refine
    { measurable := hEF.measurable
      gradMeasurable := hEF.gradMeasurable
      energyLoc := hEF.energyLoc
      zeroEntrance := hEF.zeroEntrance
      divFree := hEF.divFree
      weakGrad := hEF.weakGrad
      integrable := fun Φ hΦ => ?_
      weak := fun Φ hΦ => ?_ }
  · refine ((hcol Φ hΦ).1.add (h2 c hc M hM Φ hΦ).1).congr
      (Eventually.of_forall fun p => ?_)
    simp only [Pi.add_apply]
    exact (key Φ p).symm
  · simp_rw [key Φ]
    rw [integral_add (hcol Φ hΦ).1 (h2 c hc M hM Φ hΦ).1, (hcol Φ hΦ).2,
      (h2 c hc M hM Φ hΦ).2, add_zero]

end UnforcedLeray.Short.PartIIa.N01
