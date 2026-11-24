import UnforcedLeray.Short.PartIIb.Sub.FlatInverseDesign
import UnforcedLeray.Short.PartIIb.Tasks.HardyL1
import UnforcedLeray.Units.B0583
import UnforcedLeray.Short.PartIIIa.T20_4_VelocityIsBiotSavart

/-!
# Part II-b, task `PartII-b:F6`: early meridional correction bound (`EarlyBound`, SP 2254–2268)

Source of record: `the November 2 reference manuscript`
(SP), lines 2254–2268, display `short-bg:early` at line 2263:

  "The zero-circulation cylinder Biot–Savart map sends `X_m` to `H¹` with polynomial `c` cost.
  On nonzero horizontal modes use the gap `2π/c`; on the mean mode use
  `|ω̂(0, ξ)| ≤ |ξ| ∫ |η ω̄(η)| dη` before dividing by `ξ`. Thus `(short-bg:green-bound)` and
  `(short-bg:source)` give
  `sup_{[0, T]} ‖z(s)‖_{H¹} + |α| ≤ 𝒫_ν e^{a'T} ‖F‖_{H_p}`,
  where `α ∈ ℝ²` is the entrance coefficient of the Green-selected correction."

## Proved here (zero `sorry`)

1. `hasWeakCellDerivC_of_hasWeakVelDeriv` and `eLpNorm_vel_coord_le`: bridge between the `Lp Vel 2`
   weak cylinder gradient `B0583.HasWeakVelDeriv` and componentwise `IIIa.HasWeakCellDerivC` /
   componentwise `L²(cell)` norms;
2. `cylinderBiotSavartH1_proof : CylinderBiotSavartH1`: full proof of the zero-circulation cylinder
   Biot–Savart `X_{m,c} → H¹(C_c)` bound with polynomial `c` cost (`C_bs = 12`, `N_bs = 1`),
   combining `Short.IIIa.CTE.velocityIsBiotSavart` and `B0583.velocity` / `velGradQ` / `velGradEta`;
3. `rpow_one_div_22_div_le` and `curl_L1_le_of_sLpNorm`: application of `hardyL1_proof` (`PartII-b:T01`)
   at `p = 11/4`, `b = 13/8` (`b/p = 13/22 < 3/4`) on `(0, T]` (`T = Σ/ν`, `0 < ν ≤ 1`) to bound
   `∫⁻ s in Ioc 0 (Σ/ν), ‖curl g(s)‖_{X_{m,c}} ds` by
   `14^{7/11} Σ^{1/22} ν⁻¹ ‖curl g‖_{L^p((0, Σ/ν), s^{13/8} ds; X_{m,c})}`;
4. `c_pow_eq_inv_nu_pow` and `one_le_c_of_nu_le_one`: conversion of polynomial `p.c ^ N` factors
   under `BgRegime` (`p.c = ν⁻²`) to `(p.ν ^ (2 * N))⁻¹`;
5. `earlyBound_of_leaves`: conditional assembly of `EarlyBound` from `LinearBodySourceMap`
   (`PartII-b:F6/1`), `GreenVorticityUncurl` (`PartII-b:F6/2`), `MixedGreenSelector` (`F4`),
   `BodySourceBound` (`F5`), and `cylinderBiotSavartH1_proof`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete

/-! ## 1. Proof of `CylinderBiotSavartH1` (SP 2258–2261) -/

/-- Bridge from `B0583.HasWeakVelDeriv` on `Lp B0581.Vel 2 (B0581.cellVol c)` to componentwise
`IIIa.HasWeakCellDerivC` on `B0579.cell c`. -/
theorem hasWeakCellDerivC_of_hasWeakVelDeriv {c : ℝ} {k j : Fin 2}
    {u g : Lp B0581.Vel 2 (B0581.cellVol c)}
    (h : B0583.HasWeakVelDeriv c k u g) :
    IIIa.HasWeakCellDerivC c k
      (fun x => (u : B0579.Plane → B0581.Vel) x j)
      (fun x => (g : B0579.Plane → B0581.Vel) x j) := by
  refine ⟨fun ψ hψ => ⟨?_, ?_⟩, fun ψ hψ => ?_⟩
  · have hI := B0583.integrable_testLp_mul c (hψ.pd k) j u
    exact hI.congr (Eventually.of_forall fun x => mul_comm _ _)
  · have hI := B0583.integrable_testLp_mul c hψ j g
    exact hI.congr (Eventually.of_forall fun x => mul_comm _ _)
  · have hEq := h ψ hψ j
    have hL : (∫ x in B0579.cell c,
        (u : B0579.Plane → B0581.Vel) x j * (B0579.pd k ψ x : ℂ)) =
        ∫ x, (B0579.pd k ψ x : ℂ) * (u x : B0581.Vel) j ∂B0581.cellVol c := by
      refine integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)
    have hR : (∫ x in B0579.cell c,
        (g : B0579.Plane → B0581.Vel) x j * (ψ x : ℂ)) =
        ∫ x, (ψ x : ℂ) * (g x : B0581.Vel) j ∂B0581.cellVol c := by
      refine integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)
    rw [hL, hR, hEq]

/-- Each coordinate of `v : Lp B0581.Vel 2 (B0581.cellVol c)` has `L²(cell)` `eLpNorm` bounded by
`ENNReal.ofReal ‖v‖`. -/
theorem eLpNorm_vel_coord_le (c : ℝ) (v : Lp B0581.Vel 2 (B0581.cellVol c)) (j : Fin 2) :
    eLpNorm (fun x => (v : B0579.Plane → B0581.Vel) x j) 2 (volume.restrict (B0579.cell c)) ≤
      ENNReal.ofReal ‖v‖ := by
  have hle : eLpNorm (fun x => (v : B0579.Plane → B0581.Vel) x j) 2 (B0581.cellVol c) ≤
      eLpNorm (v : B0579.Plane → B0581.Vel) 2 (B0581.cellVol c) := by
    refine eLpNorm_mono_enorm fun x => ?_
    simp only [enorm_eq_nnnorm, ENNReal.coe_le_coe, ← norm_toNNReal]
    exact Real.toNNReal_le_toNNReal (PiLp.norm_apply_le (v x) j)
  calc eLpNorm (fun x => (v : B0579.Plane → B0581.Vel) x j) 2 (volume.restrict (B0579.cell c))
      ≤ eLpNorm (v : B0579.Plane → B0581.Vel) 2 (B0581.cellVol c) := hle
    _ = ENNReal.ofReal ‖v‖ := by
      rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top v)]

/-- **Proof of `CylinderBiotSavartH1`** (SP 2258–2261): the zero-circulation cylinder Biot–Savart
map `B0583.velocity` sends `X_{m,c}` (`m > 8`, `c ≥ 1`) to `H¹(C_c)` with polynomial `c` cost
(`C_bs = 12`, `N_bs = 1`). -/
theorem cylinderBiotSavartH1_proof : CylinderBiotSavartH1 := by
  intro m hm
  refine ⟨12, 1, by norm_num, ?_⟩
  intro c hc1 w hw
  have hc0 : 0 < c := by linarith
  have : Fact (0 < c) := ⟨hc0⟩
  have hm1 : (1 : ℝ) ≤ m := by linarith
  have hm1' : (1 : ℝ) < m := by linarith
  have hcirc : ∫ x in B0579.cell c, w x = 0 := hw.2
  set uLp : Lp B0581.Vel 2 (B0581.cellVol c) := B0583.velocity c hm1 w hcirc
  set uqLp : Lp B0581.Vel 2 (B0581.cellVol c) := B0583.velGradQ c hm1 w
  set uηLp : Lp B0581.Vel 2 (B0581.cellVol c) := B0583.velGradEta c hm1 w hcirc
  refine ⟨fun x j => (uLp : B0579.Plane → B0581.Vel) x j,
    fun x j => (uqLp : B0579.Plane → B0581.Vel) x j,
    fun x j => (uηLp : B0579.Plane → B0581.Vel) x j,
    Short.IIIa.CTE.velocityIsBiotSavart c m hm1' w hcirc,
    fun j => ⟨hasWeakCellDerivC_of_hasWeakVelDeriv (B0583.hasWeakVelDeriv_velocity_q c hm1 w hcirc),
      hasWeakCellDerivC_of_hasWeakVelDeriv (B0583.hasWeakVelDeriv_velocity_eta c hm1 w hcirc)⟩,
    ?_⟩
  have hpi : (1 : ℝ) ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
  have hc_div : c / (2 * Real.pi) ≤ c := div_le_self hc0.le hpi
  have hu_norm : ‖uLp‖ ≤ 3 * c * ‖w‖ := by
    calc ‖uLp‖ ≤ (c / (2 * Real.pi) + 2) * ‖w‖ := B0583.norm_velocity_le c hm1 w hcirc
      _ ≤ (c + 2 * c) * ‖w‖ := by
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg w)
          linarith
      _ = 3 * c * ‖w‖ := by ring
  have huq_norm : ‖uqLp‖ ≤ c * ‖w‖ := by
    calc ‖uqLp‖ ≤ 1 * ‖w‖ := by rw [one_mul]; exact B0583.norm_velGradQ_le c hm1 w
      _ ≤ c * ‖w‖ := mul_le_mul_of_nonneg_right hc1 (norm_nonneg w)
  have huη_norm : ‖uηLp‖ ≤ 2 * c * ‖w‖ := by
    calc ‖uηLp‖ ≤ 2 * ‖w‖ := B0583.norm_velGradEta_le c hm1 w hcirc
      _ ≤ (2 * c) * ‖w‖ := by
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg w)
          linarith
  have hcomp : ∀ j : Fin 2,
      eLpNorm (fun x => (uLp : B0579.Plane → B0581.Vel) x j) 2 (volume.restrict (B0579.cell c)) +
        eLpNorm (fun x => (uqLp : B0579.Plane → B0581.Vel) x j) 2 (volume.restrict (B0579.cell c)) +
        eLpNorm (fun x => (uηLp : B0579.Plane → B0581.Vel) x j) 2 (volume.restrict (B0579.cell c)) ≤
      ENNReal.ofReal (6 * c * ‖w‖) := by
    intro j
    calc eLpNorm (fun x => (uLp : B0579.Plane → B0581.Vel) x j) 2 (volume.restrict (B0579.cell c)) +
          eLpNorm (fun x => (uqLp : B0579.Plane → B0581.Vel) x j) 2 (volume.restrict (B0579.cell c)) +
          eLpNorm (fun x => (uηLp : B0579.Plane → B0581.Vel) x j) 2 (volume.restrict (B0579.cell c))
        ≤ ENNReal.ofReal ‖uLp‖ + ENNReal.ofReal ‖uqLp‖ + ENNReal.ofReal ‖uηLp‖ := by
          gcongr
          · exact eLpNorm_vel_coord_le c uLp j
          · exact eLpNorm_vel_coord_le c uqLp j
          · exact eLpNorm_vel_coord_le c uηLp j
      _ ≤ ENNReal.ofReal (3 * c * ‖w‖) + ENNReal.ofReal (c * ‖w‖) +
            ENNReal.ofReal (2 * c * ‖w‖) := by
          gcongr
      _ = ENNReal.ofReal (6 * c * ‖w‖) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          ring
  rw [Fin.sum_univ_two]
  calc (eLpNorm (fun x => (uLp : B0579.Plane → B0581.Vel) x 0) 2 (volume.restrict (B0579.cell c)) +
        eLpNorm (fun x => (uqLp : B0579.Plane → B0581.Vel) x 0) 2 (volume.restrict (B0579.cell c)) +
        eLpNorm (fun x => (uηLp : B0579.Plane → B0581.Vel) x 0) 2 (volume.restrict (B0579.cell c))) +
      (eLpNorm (fun x => (uLp : B0579.Plane → B0581.Vel) x 1) 2 (volume.restrict (B0579.cell c)) +
        eLpNorm (fun x => (uqLp : B0579.Plane → B0581.Vel) x 1) 2 (volume.restrict (B0579.cell c)) +
        eLpNorm (fun x => (uηLp : B0579.Plane → B0581.Vel) x 1) 2 (volume.restrict (B0579.cell c)))
      ≤ ENNReal.ofReal (6 * c * ‖w‖) + ENNReal.ofReal (6 * c * ‖w‖) :=
        add_le_add (hcomp 0) (hcomp 1)
    _ = ENNReal.ofReal (12 * c ^ 1 * ‖w‖) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

/-! ## 2. Hardy `L¹` bound for the curl source and `BgRegime` polynomial-in-`ν⁻¹` algebra -/

/-- For `Sig > 0` and `0 < ν ≤ 1`, `(Sig / ν)^{1/22} ≤ Sig^{1/22} ν⁻¹`. -/
theorem rpow_one_div_22_div_le {Sig ν : ℝ} (hSig : 0 < Sig) (hν0 : 0 < ν) (hν1 : ν ≤ 1) :
    (Sig / ν) ^ (1 / 22 : ℝ) ≤ Sig ^ (1 / 22 : ℝ) * ν⁻¹ := by
  rw [Real.div_rpow hSig.le hν0.le, div_eq_mul_inv, ← Real.rpow_neg hν0.le]
  refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hSig.le _)
  rw [← Real.rpow_neg_one ν]
  exact Real.rpow_le_rpow_of_exponent_ge hν0 hν1 (by norm_num)

/-- Applying `hardyL1_proof` (`PartII-b:T01`) on `(0, Sig/ν]` (`0 < ν ≤ 1`) bounds the `L¹` integral
of a measurable slice norm `N` by `14^{7/11} Sig^{1/22} ν⁻¹ · sLpNorm (13/8) (Sig/ν) N`. -/
theorem curl_L1_le_of_sLpNorm {Sig ν : ℝ} (hSig : 0 < Sig) (hν0 : 0 < ν) (hν1 : ν ≤ 1)
    {N : ℝ → ℝ≥0∞} (hN : Measurable N) :
    ∫⁻ s in Ioc 0 (Sig / ν), N s ≤
      ENNReal.ofReal (14 ^ (7 / 11 : ℝ) * Sig ^ (1 / 22 : ℝ) * ν⁻¹) *
        sLpNorm (13 / 8) (Sig / ν) N := by
  have hT : 0 < Sig / ν := div_pos hSig hν0
  have h1 := hardyL1_proof (Sig / ν) hT N hN
  change ∫⁻ s in Ioc 0 (Sig / ν), N s ≤
    ENNReal.ofReal (14 ^ (7 / 11 : ℝ) * (Sig / ν) ^ (1 / 22 : ℝ)) *
      sLpNorm (13 / 8) (Sig / ν) N at h1
  refine h1.trans (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) zero_le)
  have h2 := rpow_one_div_22_div_le hSig hν0 hν1
  calc 14 ^ (7 / 11 : ℝ) * (Sig / ν) ^ (1 / 22 : ℝ)
      ≤ 14 ^ (7 / 11 : ℝ) * (Sig ^ (1 / 22 : ℝ) * ν⁻¹) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = 14 ^ (7 / 11 : ℝ) * Sig ^ (1 / 22 : ℝ) * ν⁻¹ := by ring

/-- Under `BgRegime p d dm dp`, `p.c = (p.ν ^ 2)⁻¹`, so `p.c ^ N = (p.ν ^ (2 * N))⁻¹` and `1 ≤ p.c`
whenever `p.ν ≤ 1`. -/
theorem c_pow_eq_inv_nu_pow {p : Params} {d dm dp : ℝ} (hreg : BgRegime p d dm dp) (N : ℕ) :
    p.c ^ N = (p.ν ^ (2 * N))⁻¹ := by
  rw [hreg.c_eq, inv_pow, ← pow_mul]

theorem one_le_c_of_nu_le_one {p : Params} {d dm dp : ℝ} (hreg : BgRegime p d dm dp)
    (hν1 : p.ν ≤ 1) : 1 ≤ p.c := by
  have hν : 0 < p.ν := p.ν_pos
  rw [hreg.c_eq, one_le_inv₀ (pow_pos hν 2)]
  exact pow_le_one₀ hν.le hν1

/-! ## 3. Leaf propositions (`PartII-b:F6/1`, `PartII-b:F6/2`) and conditional assembly -/

/-- **Leaf 1 (`PartII-b:F6/1`, `LinearBodySourceMap`, SP 2213–2239, 2265–2267)**:
from `BodySourceBound` (`PartII-b:F5`), `profileGraphFlat_bgp` (`PartII-b:T14`), and the proved
Hardy `L¹` bound `curl_L1_le_of_sLpNorm` (`PartII-b:T01`), at every `BgRegime` parameter point `p`
with `p.ν ≤ ν_s`, `p.ν ≤ 1`, `p.ageCut = Sig`, `p.mode = q`, the flat response `b_0 = T_0 F`, its
weak derivatives `b0q, b0η`, the projected body source `g = -P_0(v·∇b_0 + b_0·∇v)` and its weak
derivatives `gq, gη`, and the Bochner-integrable zero-circulation vorticity source
`s ↦ curl g(s) ∈ X_{m,c}` on `(0, p.H]` can be packaged as `ℝ`-linear maps
`b0Of, b0qOf, b0ηOf, gOf, gqOf, gηOf : HpR p.c →ₗ[ℝ] CProf` and
`curlSourceOf : HpR p.c →ₗ[ℝ] (ℝ → Xmc p.c m)` satisfying the `sLpNorm (13 / 8)` bound on `g` and
the `L¹(0, p.H; X_{m,c})` bound on `curlSourceOf F`. -/
def LinearBodySourceMap : Prop :=
  BodySourceBound →
  ∀ m : ℝ, 8 < m →
  ∀ (Sig : ℝ) (lam : ℂ) (q : Blueprint.Planar.Profile), 0 < Sig →
    Blueprint.Planar.IsGrowingEigenpair lam q →
  ∀ dm dp : ℝ, 0 < dm →
    ∃ (C_src : ℝ) (k_src : ℕ) (ν_s : ℝ), 0 < C_src ∧ 0 < ν_s ∧
      ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν_s → p.ν ≤ 1 →
        p.ageCut = Sig → p.mode = q →
        ∃ (b0Of b0qOf b0ηOf gOf gqOf gηOf : HpR p.c →ₗ[ℝ] CProf)
          (curlSourceOf : HpR p.c →ₗ[ℝ] (ℝ → Xmc p.c m)),
          ∀ F : HpR p.c,
            InFlatClass p.c bgp (b0Of F) ∧
            IsFlatResponse p.ν 0 (toProf p.c F) (b0Of F) ∧
            HasWeakVec vQ0 dZero (b0Of F) (b0qOf F) ∧
            HasWeakVec vEta dZero (b0Of F) (b0ηOf F) ∧
            QPeriodic p.c (gOf F) ∧
            HasWeakVec vQ0 dZero (gOf F) (gqOf F) ∧
            HasWeakVec vEta dZero (gOf F) (gηOf F) ∧
            IsBodySource p.train (b0Of F) (b0qOf F) (b0ηOf F) (gOf F) ∧
            Measurable (sliceH1Norm p.c (gOf F) (gqOf F) (gηOf F)) ∧
            sLpNorm (13 / 8) p.H (sliceH1Norm p.c (gOf F) (gqOf F) (gηOf F)) ≤
              ENNReal.ofReal (C_src * (p.ν ^ k_src)⁻¹ * ‖F‖) ∧
            IntegrableOn (curlSourceOf F) (Ioc 0 p.H) volume ∧
            (∀ᵐ t ∂volume, t ∈ Ioc 0 p.H → HasZeroCirculationR p.c (curlSourceOf F t)) ∧
            (∀ᵐ s ∂volume, s ∈ Ioc 0 p.H →
              ∀ᵐ x ∂volume, x ∈ B0579.cell p.c →
                ((curlSourceOf F s x : ℝ) : ℂ) = profCurl (gqOf F) (gηOf F) (s, x)) ∧
            ∫ t in Ioc 0 p.H, ‖curlSourceOf F t‖ ≤
              (14 ^ (7 / 11 : ℝ) * Sig ^ (1 / 22 : ℝ) * p.ν⁻¹) *
                (C_src * (p.ν ^ k_src)⁻¹) * ‖F‖

/-- **Leaf 2 (`PartII-b:F6/2`, `GreenVorticityUncurl`, SP 2219–2222, 2254–2268)**:
given `CylinderBiotSavartH1`, the Green selector operators `(U, P_term, Piu, Pic, G_c, G_u, Γ_α)`
from `MixedGreenSelector` (`PartII-b:F4`), and the linear body-source/curl-source maps
`(b0Of, b0qOf, b0ηOf, gOf, gqOf, gηOf, curlSourceOf)` from `LinearBodySourceMap` (`PartII-b:F6/1`),
feeding `f = curlSourceOf F` into the Green selector
`ω(s) = ∫_{0}^s G_c s t (f t) dt - ∫_s^{p.H} G_u s t (f t) dt` and
`αMap F = ∫_0^{p.H} Γ_α t (f t) dt` and uncurling `ω(s)` on `(0, p.H]` via the zero-circulation
cylinder Biot–Savart operators (`B0583.velocity`, `B0583.velGradQ`, `B0583.velGradEta`) yields the
continuous linear entrance functional `αMap : HpR p.c →L[ℝ] E2` and linear profile maps
`zOf, zqOf, zηOf : HpR p.c →ₗ[ℝ] CProf` solving
`IsMeridionalCorrectionOn p p.H (gOf F) (zOf F) (zqOf F) (zηOf F) (αMap F)` with slice `H¹` norm
bounded by `(C_bs * p.c ^ N_bs + 1) * C_green * e^{a' p.H} * C_L1 * ‖F‖`. -/
def GreenVorticityUncurl : Prop :=
  ∀ m : ℝ, 8 < m →
  ∀ (C_bs : ℝ) (N_bs : ℕ), 0 < C_bs →
    (∀ c : ℝ, 1 ≤ c → ∀ w : Xmc c m, HasZeroCirculationR c w →
      ∃ u uq uη : B0579.Plane → Fin 2 → ℂ,
        IIIa.IsBiotSavart c (fun x => ((w x : ℝ) : ℂ)) u ∧
        (∀ j : Fin 2, IIIa.HasWeakCellDerivC c 0 (fun x => u x j) (fun x => uq x j) ∧
          IIIa.HasWeakCellDerivC c 1 (fun x => u x j) (fun x => uη x j)) ∧
        (∑ j : Fin 2,
          (eLpNorm (fun x => u x j) 2 (volume.restrict (B0579.cell c)) +
            eLpNorm (fun x => uq x j) 2 (volume.restrict (B0579.cell c)) +
            eLpNorm (fun x => uη x j) 2 (volume.restrict (B0579.cell c)))) ≤
          ENNReal.ofReal (C_bs * c ^ N_bs * ‖w‖)) →
  ∀ (Sig : ℝ) (lam : ℂ) (q : Blueprint.Planar.Profile), 0 < Sig →
    Blueprint.Planar.IsGrowingEigenpair lam q →
  ∀ (a' b' C_green C_src C_L1 : ℝ) (k_src : ℕ),
    0 < a' → a' < b' → b' < lam.re / (1 + Sig) ^ 2 → 0 < C_green → 0 < C_src → 0 ≤ C_L1 →
  ∀ (dm dp : ℝ), 0 < dm →
  ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → 1 ≤ p.c → p.ν ≤ 1 →
    p.ageCut = Sig → p.mode = q →
    (∃ (U : ℝ → ℝ → (Xmc p.c m →L[ℝ] Xmc p.c m))
      (P_term : Xmc p.c m →L[ℝ] E2)
      (Piu Pic : ℝ → (Xmc p.c m →L[ℝ] Xmc p.c m))
      (G_c G_u : ℝ → ℝ → (Xmc p.c m →L[ℝ] Xmc p.c m))
      (Γ_α : ℝ → (Xmc p.c m →L[ℝ] E2)),
      IsCoupledPropagator m p U ∧
      (∀ t ∈ Icc 0 p.H,
        (Piu t).comp (Piu t) = Piu t ∧
        Pic t = ContinuousLinearMap.id ℝ (Xmc p.c m) - Piu t ∧
        ‖Piu t‖ ≤ C_green ∧ ‖Pic t‖ ≤ C_green ∧
        ‖Γ_α t‖ ≤ C_green * Real.exp (-b' * t)) ∧
      (∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ p.H →
        (U t s).comp (Piu s) = (Piu t).comp (U t s) ∧
        (U t s).comp (Pic s) = (Pic t).comp (U t s) ∧
        G_c t s = (U t s).comp (Pic s) ∧
        (U t s).comp (G_u s t) = Piu t ∧
        ‖G_c t s‖ ≤ C_green * Real.exp (a' * (t - s)) ∧
        ‖G_u s t‖ ≤ C_green * Real.exp (-b' * (t - s))) ∧
      ∀ f : ℝ → Xmc p.c m, IntegrableOn f (Ioc 0 p.H) volume →
        (∀ᵐ t ∂volume, t ∈ Ioc 0 p.H → HasZeroCirculationR p.c (f t)) →
        let ω : ℝ → Xmc p.c m := fun s =>
          (∫ t in Ioc 0 s, G_c s t (f t)) - (∫ t in Ioc s p.H, G_u s t (f t))
        let α : E2 := ∫ t in Ioc 0 p.H, Γ_α t (f t)
        ((ω 0 : B0579.Plane → ℝ) =ᵐ[B0579.cellMeasure p.c m] entranceVorticityComb p α) ∧
        P_term (ω p.H) = 0 ∧
        (∀ s ∈ Icc 0 p.H, HasZeroCirculationR p.c (ω s)) ∧
        (∀ φ : B0579.Plane → ℝ, B0579.IsCylTest p.c φ → ∀ s ∈ Icc 0 p.H,
          ∫ x in B0579.cell p.c, ω s x * φ x =
            (∫ x in B0579.cell p.c, ω 0 x * φ x) +
              ∫ r in (0 : ℝ)..s, ∫ x in B0579.cell p.c,
                (cylCoupledIntegrand p.train (ω r) r φ x + f r x * φ x)) ∧
        (∀ s ∈ Icc 0 p.H,
          ‖ω s‖ + ‖α‖ ≤ C_green * Real.exp (a' * p.H) * ∫ t in Ioc 0 p.H, ‖f t‖)) →
    ∀ (b0Of b0qOf b0ηOf gOf gqOf gηOf : HpR p.c →ₗ[ℝ] CProf)
      (curlSourceOf : HpR p.c →ₗ[ℝ] (ℝ → Xmc p.c m)),
      (∀ F : HpR p.c,
        InFlatClass p.c bgp (b0Of F) ∧
        IsFlatResponse p.ν 0 (toProf p.c F) (b0Of F) ∧
        HasWeakVec vQ0 dZero (b0Of F) (b0qOf F) ∧
        HasWeakVec vEta dZero (b0Of F) (b0ηOf F) ∧
        QPeriodic p.c (gOf F) ∧
        HasWeakVec vQ0 dZero (gOf F) (gqOf F) ∧
        HasWeakVec vEta dZero (gOf F) (gηOf F) ∧
        IsBodySource p.train (b0Of F) (b0qOf F) (b0ηOf F) (gOf F) ∧
        Measurable (sliceH1Norm p.c (gOf F) (gqOf F) (gηOf F)) ∧
        sLpNorm (13 / 8) p.H (sliceH1Norm p.c (gOf F) (gqOf F) (gηOf F)) ≤
          ENNReal.ofReal (C_src * (p.ν ^ k_src)⁻¹ * ‖F‖) ∧
        IntegrableOn (curlSourceOf F) (Ioc 0 p.H) volume ∧
        (∀ᵐ t ∂volume, t ∈ Ioc 0 p.H → HasZeroCirculationR p.c (curlSourceOf F t)) ∧
        (∀ᵐ s ∂volume, s ∈ Ioc 0 p.H →
          ∀ᵐ x ∂volume, x ∈ B0579.cell p.c →
            ((curlSourceOf F s x : ℝ) : ℂ) = profCurl (gqOf F) (gηOf F) (s, x)) ∧
        ∫ t in Ioc 0 p.H, ‖curlSourceOf F t‖ ≤ C_L1 * ‖F‖) →
      ∃ (αMap : HpR p.c →L[ℝ] E2)
        (zOf zqOf zηOf : HpR p.c →ₗ[ℝ] CProf),
        ∀ F : HpR p.c,
          IsMeridionalCorrectionOn p p.H (gOf F) (zOf F) (zqOf F) (zηOf F) (αMap F) ∧
          Measurable (sliceH1Norm p.c (zOf F) (zqOf F) (zηOf F)) ∧
          ∀ s ∈ Ioc 0 p.H,
            sliceH1Norm p.c (zOf F) (zqOf F) (zηOf F) s + ENNReal.ofReal ‖αMap F‖ ≤
              ENNReal.ofReal
                ((C_bs * p.c ^ N_bs + 1) * C_green * Real.exp (a' * p.H) * C_L1 * ‖F‖)

/-- **Conditional assembly of `EarlyBound` (`PartII-b:F6`)** from `LinearBodySourceMap`
(`PartII-b:F6/1`), `GreenVorticityUncurl` (`PartII-b:F6/2`), `MixedGreenSelector` (`F4`),
`BodySourceBound` (`F5`), and the proved `cylinderBiotSavartH1_proof`. -/
theorem earlyBound_of_leaves
    (hSrc : LinearBodySourceMap)
    (hUncurl : GreenVorticityUncurl)
    (hGS : UnforcedLeray.Short.IIb.MixedGreenSelector)
    (hBS : UnforcedLeray.Short.IIb.BodySourceBound) :
    UnforcedLeray.Short.IIb.EarlyBound := by
  refine ⟨cylinderBiotSavartH1_proof, ?_⟩
  intro m hm Sig lam q hSig hEig a' ha'0 ha'lam dm dp hdm
  obtain ⟨C_bs, N_bs, hC_bs, hbs⟩ := cylinderBiotSavartH1_proof m hm
  set b' : ℝ := (a' + lam.re / (1 + Sig) ^ 2) / 2
  have hb'1 : a' < b' := by dsimp [b']; linarith
  have hb'2 : b' < lam.re / (1 + Sig) ^ 2 := by dsimp [b']; linarith
  obtain ⟨C_green, ν_g, hC_green, hν_g, hGS_p⟩ :=
    hGS m hm Sig lam q hSig hEig a' b' ha'0 hb'1 hb'2 dm dp hdm
  obtain ⟨C_src, k_src, ν_s, hC_src, hν_s, hSrc_p⟩ :=
    hSrc hBS m hm Sig lam q hSig hEig dm dp hdm
  set C_early : ℝ :=
    C_src + (C_bs + 1) * C_green * (14 ^ (7 / 11 : ℝ) * Sig ^ (1 / 22 : ℝ)) * C_src
  have hC_early : 0 < C_early := by positivity
  set k_early : ℕ := k_src + 1 + 2 * N_bs
  set ν₀ : ℝ := min (min ν_g ν_s) 1
  have hν₀ : 0 < ν₀ := lt_min (lt_min hν_g hν_s) one_pos
  refine ⟨C_early, k_early, ν₀, hC_early, hν₀, ?_⟩
  intro p d hreg hν hSig_p hmode_p
  have hν_g' : p.ν ≤ ν_g := hν.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hν_s' : p.ν ≤ ν_s := hν.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hν1 : p.ν ≤ 1 := hν.trans (min_le_right _ _)
  have hν0 : 0 < p.ν := p.ν_pos
  have hc1 : 1 ≤ p.c := one_le_c_of_nu_le_one hreg hν1
  obtain ⟨b0Of, b0qOf, b0ηOf, gOf, gqOf, gηOf, curlSourceOf, hSrc_F⟩ :=
    hSrc_p p d hreg hν_s' hν1 hSig_p hmode_p
  set C_L1 : ℝ :=
    (14 ^ (7 / 11 : ℝ) * Sig ^ (1 / 22 : ℝ) * p.ν⁻¹) * (C_src * (p.ν ^ k_src)⁻¹)
  have hC_L1 : 0 ≤ C_L1 := by dsimp [C_L1]; positivity
  obtain ⟨αMap, zOf, zqOf, zηOf, hUnc_F⟩ :=
    hUncurl m hm C_bs N_bs hC_bs hbs Sig lam q hSig hEig a' b' C_green C_src C_L1 k_src
      ha'0 hb'1 hb'2 hC_green hC_src hC_L1 dm dp hdm p d hreg hc1 hν1 hSig_p hmode_p
      (hGS_p p d hreg hν_g' hSig_p hmode_p)
      b0Of b0qOf b0ηOf gOf gqOf gηOf curlSourceOf hSrc_F
  refine ⟨αMap, b0Of, b0qOf, b0ηOf, gOf, gqOf, gηOf, zOf, zqOf, zηOf, fun F => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h10, hg_lp, _, _, _, _⟩ := hSrc_F F
  obtain ⟨h9, h11, hz_sup⟩ := hUnc_F F
  have hpow_le : ∀ a b : ℕ, a ≤ b → (p.ν ^ a)⁻¹ ≤ (p.ν ^ b)⁻¹ := by
    intro a b hab
    exact inv_anti₀ (pow_pos hν0 b) (pow_le_pow_of_le_one hν0.le hν1 hab)
  have hC_src_le : C_src ≤ C_early := by
    dsimp [C_early]
    have : 0 ≤ (C_bs + 1) * C_green * (14 ^ (7 / 11 : ℝ) * Sig ^ (1 / 22 : ℝ)) * C_src := by
      positivity
    linarith
  have hg_lp' : sLpNorm (13 / 8) p.H (sliceH1Norm p.c (gOf F) (gqOf F) (gηOf F)) ≤
      ENNReal.ofReal (C_early * (p.ν ^ k_early)⁻¹ * ‖F‖) := by
    refine hg_lp.trans (ENNReal.ofReal_le_ofReal ?_)
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg F)
    exact mul_le_mul hC_src_le (hpow_le k_src k_early (by omega)) (by positivity) hC_early.le
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, hg_lp', fun s hs => ?_⟩
  refine (hz_sup s hs).trans (ENNReal.ofReal_le_ofReal ?_)
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg F)
  have hc_pow : C_bs * p.c ^ N_bs + 1 ≤ (C_bs + 1) * (p.ν ^ (2 * N_bs))⁻¹ := by
    rw [c_pow_eq_inv_nu_pow hreg N_bs]
    have h1_le : (1 : ℝ) ≤ (p.ν ^ (2 * N_bs))⁻¹ := by
      simpa using hpow_le 0 (2 * N_bs) (Nat.zero_le _)
    nlinarith [hC_bs]
  have hcoef_le : (C_bs + 1) * C_green * (14 ^ (7 / 11 : ℝ) * Sig ^ (1 / 22 : ℝ)) * C_src ≤
      C_early := by
    dsimp [C_early]
    linarith
  have hnu_prod :
      (p.ν ^ (2 * N_bs))⁻¹ * p.ν⁻¹ * (p.ν ^ k_src)⁻¹ = (p.ν ^ k_early)⁻¹ := by
    dsimp [k_early]
    rw [pow_add, pow_add, pow_one, mul_inv, mul_inv]
    ring
  calc (C_bs * p.c ^ N_bs + 1) * C_green * Real.exp (a' * p.H) * C_L1
      = (C_bs * p.c ^ N_bs + 1) * C_green * Real.exp (a' * p.H) *
          (14 ^ (7 / 11 : ℝ) * Sig ^ (1 / 22 : ℝ) * p.ν⁻¹) * (C_src * (p.ν ^ k_src)⁻¹) := by
        dsimp [C_L1]; ring
    _ ≤ ((C_bs + 1) * (p.ν ^ (2 * N_bs))⁻¹) * C_green * Real.exp (a' * p.H) *
          (14 ^ (7 / 11 : ℝ) * Sig ^ (1 / 22 : ℝ) * p.ν⁻¹) * (C_src * (p.ν ^ k_src)⁻¹) := by
        gcongr
    _ = ((C_bs + 1) * C_green * (14 ^ (7 / 11 : ℝ) * Sig ^ (1 / 22 : ℝ)) * C_src) *
          ((p.ν ^ (2 * N_bs))⁻¹ * p.ν⁻¹ * (p.ν ^ k_src)⁻¹) * Real.exp (a' * p.H) := by
        ring
    _ = ((C_bs + 1) * C_green * (14 ^ (7 / 11 : ℝ) * Sig ^ (1 / 22 : ℝ)) * C_src) *
          (p.ν ^ k_early)⁻¹ * Real.exp (a' * p.H) := by
        rw [hnu_prod]
    _ ≤ C_early * (p.ν ^ k_early)⁻¹ * Real.exp (a' * p.H) := by
        gcongr

end UnforcedLeray.Short.IIb

end
