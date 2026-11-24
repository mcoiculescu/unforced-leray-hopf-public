import UnforcedLeray.Units.B0061
import UnforcedLeray.Lib.PlanarSectorsB.BiotSavartSector

/-!
# Part I, task `PartI:S11`: the Euler generator is the sector-decomposed operator (conditional)

Source of record: `the November 2 reference manuscript`, lines 841-889
(transfer of the spectral and semigroup results of the sector operators `𝓛_n` to the weak-derivative
generator `𝓛 = -Ω∂_ϑ - (K·)·∇E₀`, `B0009.generator`, on `H^0_M`).

The generator is `𝓛f = -Ω∂_ϑ f - A_E f`, where `Ω∂_ϑ f` is the weak transport
(`B0009.HasWeakTransport`, domain `B0009.transportDomain`) and `A_E f = (Kf)·∇E₀` is the bounded
operator `B0061.AEj`. On the sector `w(r)e^{inϑ}` one has

* `Ω∂_ϑ` acts as `i n Ω = -transportSec M n` (`Planar.transportSec M n = -(i n)Ω`),
* `A_E` acts as `-couplingSec hM n` (`Planar.couplingSec hM n` is the kernel `i n k Δ_{|n|}⁻¹` of
  `-(Kf)·∇E₀`, see the header of `Lib/PlanarSectorsB/BiotSavartSector.lean`),

so `𝓛` acts as `Lsec hM n = transportSec M n + couplingSec hM n`. Three precise Props isolate what
is not yet in the library; `generator_sector_bridge_of` and `generator_sector_bridge_converse_of`
are the two halves of the bridge, proved from them. The unconditional bridge is the task
`PartI:S11` (`Short/PartI/Tasks/EulerSectorBridge.lean`).

Well-formed reading of the original target: "`xValue`-element of `F`" is
`((F : B0008.XjM 0 M) : B0008.HjM 0 M).value`, the `L²_M` element of `F`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Real

namespace UnforcedLeray.Short.PartI

open UnforcedLeray

/-- **Sector form of `A_E`** (analytic half of target P8; source lines 841-889, with
`K = ∇^⊥Δ⁻¹` and `∇E₀(y) = k(|y|)y`, lines 662-670): the sector-`n` profile of
`A_E f = (Kf)·∇E₀` is `-couplingSec hM n` applied to the sector-`n` profile of `f`, for every
`f ∈ H^0_M`, `M > 1`. The sign is fixed by the header of `Lib/PlanarSectorsB/BiotSavartSector.lean`
(`-(Kf)·∇E₀ = i n k Δ_{|n|}⁻¹ f_n e^{inϑ}`, the kernel of `couplingSec`); compare with
`Planar.coeFn_couplingSec` before proving. -/
def SecProfAE : Prop :=
  ∀ {M : ℝ} (hM : 1 < M) (n : ℤ) (f : B0008.HjM 0 M),
    Planar.secProf M n (B0061.AEj 0 hM f).value =
      -Planar.couplingSec hM n (Planar.secProf M n f.value)

/-- **Sector form of the weak transport** (source lines 841-889): if `f ∈ H^0_M` has weak
`Ω∂_ϑ f ∈ H^0_M`, then the sector-`n` profile of `Ω∂_ϑ f` is `i n Ω f_n = -transportSec M n f_n`
(`Planar.transportSec M n = -(i n)Ω`). Proof: test the weak identity
`∫ f · Ω∂_ϑφ = -∫ (Ω∂_ϑ f) φ` against test functions `φ = ψ(r) e^{imϑ}`; `Ω` is radial and the
sector projections commute with it. -/
def SecProfTransport : Prop :=
  ∀ {M : ℝ} (n : ℤ) (F : B0009.transportDomain 0 M),
    Planar.secProf M n (B0009.transport F).value =
      -Planar.transportSec M n (Planar.secProf M n (F : B0008.HjM 0 M).value)

/-- **Sector-sum criterion for the weak transport** (source lines 841-889): if the sector profiles
`f_n` of `f ∈ H^0_M` satisfy `Σ_n ‖n Ω f_n‖² < ∞`, i.e.
`Σ_n ‖transportSec M n f_n‖² < ∞`, then `Ω∂_ϑ f` exists weakly in `H^0_M` and has the sector
profiles `i n Ω f_n = -transportSec M n f_n`. Proof: the family `secEmb M n (-transportSec M n f_n)`
is orthogonal with summable squared norms, so it sums to some `g ∈ L²_M`
(`Planar.hasSum_secEmb_secProf`, `Planar.orthogonalFamily_secEmb`); then
`∫ f · Ω∂_ϑφ = -∫ g φ` for test functions `φ` by Parseval on the sectors of `φ`
(`Planar.norm_sq_eq_tsum`, `Planar.hasSum_norm_sq_secProf`), since `Ω∂_ϑ φ` has sector profiles
`i n Ω φ_n`. -/
def SectorTransportCriterion : Prop :=
  ∀ {M : ℝ}, 1 < M → ∀ u : B0008.HjM 0 M,
    (Summable fun n : ℤ => ‖Planar.transportSec M n (Planar.secProf M n u.value)‖ ^ 2) →
      ∃ G : B0008.HjM 0 M,
        B0009.HasWeakTransport (u.value : ℂ → ℂ) (G.value : ℂ → ℂ) ∧
          ∀ n : ℤ, Planar.secProf M n G.value =
            -Planar.transportSec M n (Planar.secProf M n u.value)

/-- `B0008.L2w M` and `Planar.L2w M` are the same type (`Planar.wMeasure_eq_B0008`); this
wrapper only changes the elaborated type. -/
def toP {M : ℝ} (f : B0008.L2w M) : Planar.L2w M := f

theorem coeFn_toP {M : ℝ} (f : B0008.L2w M) (y : ℂ) :
    (toP f : ℂ → ℂ) y = (f : ℂ → ℂ) y := rfl

theorem coeFn_neg_sub_ae {M : ℝ} (g a : Planar.L2w M) :
    ⇑(-g - a) =ᵐ[volume] fun y => -(g : ℂ → ℂ) y - (a : ℂ → ℂ) y := by
  refine (Planar.volume_ac M).ae_le ?_
  filter_upwards [Lp.coeFn_sub (-g) a, Lp.coeFn_neg g] with y hy1 hy2
  rw [hy1, Pi.sub_apply, hy2, Pi.neg_apply]

/-- **Forward half of the bridge** (conditional): for `F` in the domain of the weak-derivative
generator there is `u ∈ L²_M` with `u = 𝓛F` almost everywhere whose sector profiles are
`Lsec hM n (F_n)`. -/
theorem generator_sector_bridge_of (hAE : SecProfAE) (hT : SecProfTransport)
    {M : ℝ} (hM : 1 < M) (F : (B0009.generator 0 hM).domain) :
    ∃ u : Planar.L2w M, ⇑u =ᵐ[volume] ⇑(B0009.generator 0 hM F) ∧
      ∀ n : ℤ, Planar.secProf M n u =
        Planar.Lsec hM n (Planar.secProf M n (((F : B0008.XjM 0 M) : B0008.HjM 0 M).value)) := by
  have hG := B0009.hasWeakTransport_transport (B0009.domainIncl (j := 0) (M := M) F)
  refine ⟨-toP (B0009.transport (B0009.domainIncl (j := 0) (M := M) F)).value -
    toP (B0061.AEj 0 hM ((F : B0008.XjM 0 M) : B0008.HjM 0 M)).value, ?_, ?_⟩
  · have h1 := B0009.generator_apply hM F hG
    have h2 := B0061.AEj_value_ae hM ((F : B0008.XjM 0 M) : B0008.HjM 0 M)
    have h3 := coeFn_neg_sub_ae
      (toP (B0009.transport (B0009.domainIncl (j := 0) (M := M) F)).value)
      (toP (B0061.AEj 0 hM ((F : B0008.XjM 0 M) : B0008.HjM 0 M)).value)
    filter_upwards [h1, h2, h3] with y hy1 hy2 hy3
    rw [hy3, coeFn_toP, coeFn_toP]
    refine Eq.trans ?_ hy1.symm
    rw [hy2]
    try rfl
  · intro n
    have hs : Planar.secProf M n (toP (B0009.transport (B0009.domainIncl (j := 0) (M := M) F)).value)
        = -Planar.transportSec M n
            (Planar.secProf M n (((F : B0008.XjM 0 M) : B0008.HjM 0 M).value)) :=
      hT n (B0009.domainIncl (j := 0) (M := M) F)
    have ha : Planar.secProf M n (toP (B0061.AEj 0 hM ((F : B0008.XjM 0 M) : B0008.HjM 0 M)).value)
        = -Planar.couplingSec hM n
            (Planar.secProf M n (((F : B0008.XjM 0 M) : B0008.HjM 0 M).value)) :=
      hAE hM n _
    rw [map_sub, map_neg, hs, ha, neg_neg, sub_neg_eq_add, Planar.Lsec]
    rfl

/-- **Converse half of the bridge** (conditional): if `u ∈ X_{0,M}` and `w ∈ L²_M` satisfy
`w_n = Lsec hM n u_n` sectorwise and `Σ_n ‖transportSec M n u_n‖² < ∞`, then `u` is in the
domain of the weak-derivative generator and `w = 𝓛u` almost everywhere. -/
theorem generator_sector_bridge_converse_of (hAE : SecProfAE) (hC : SectorTransportCriterion)
    {M : ℝ} (hM : 1 < M) (u : B0008.XjM 0 M) (w : Planar.L2w M)
    (hw : ∀ n : ℤ, Planar.secProf M n w =
      Planar.Lsec hM n (Planar.secProf M n (((u : B0008.XjM 0 M) : B0008.HjM 0 M).value)))
    (hsum : Summable fun n : ℤ => ‖Planar.transportSec M n
      (Planar.secProf M n (((u : B0008.XjM 0 M) : B0008.HjM 0 M).value))‖ ^ 2) :
    ∃ hu : u ∈ (B0009.generator 0 hM).domain,
      ⇑w =ᵐ[volume] ⇑(B0009.generator 0 hM ⟨u, hu⟩) := by
  obtain ⟨G, hG, hGsec⟩ := hC hM ((u : B0008.XjM 0 M) : B0008.HjM 0 M) hsum
  have hu : u ∈ (B0009.generator 0 hM).domain := (B0009.mem_domain_iff u).2 ⟨G, hG⟩
  refine ⟨hu, ?_⟩
  have h1 := B0009.generator_apply hM (⟨u, hu⟩ : B0009.domain 0 M) hG
  have h2 := B0061.AEj_value_ae hM ((u : B0008.XjM 0 M) : B0008.HjM 0 M)
  have hv : w = -toP G.value - toP (B0061.AEj 0 hM ((u : B0008.XjM 0 M) : B0008.HjM 0 M)).value := by
    apply Planar.eq_of_secProf
    intro n
    have hG' : Planar.secProf M n (toP G.value) =
        -Planar.transportSec M n
          (Planar.secProf M n (((u : B0008.XjM 0 M) : B0008.HjM 0 M).value)) := hGsec n
    have ha : Planar.secProf M n
        (toP (B0061.AEj 0 hM ((u : B0008.XjM 0 M) : B0008.HjM 0 M)).value)
        = -Planar.couplingSec hM n
            (Planar.secProf M n (((u : B0008.XjM 0 M) : B0008.HjM 0 M).value)) :=
      hAE hM n _
    rw [hw n, map_sub, map_neg, hG', ha, neg_neg, sub_neg_eq_add, Planar.Lsec]
    rfl
  have h3 := coeFn_neg_sub_ae (toP G.value)
    (toP (B0061.AEj 0 hM ((u : B0008.XjM 0 M) : B0008.HjM 0 M)).value)
  rw [hv]
  filter_upwards [h1, h2, h3] with y hy1 hy2 hy3
  rw [hy3, coeFn_toP, coeFn_toP]
  refine Eq.trans ?_ hy1.symm
  rw [hy2]
  try rfl

end UnforcedLeray.Short.PartI
