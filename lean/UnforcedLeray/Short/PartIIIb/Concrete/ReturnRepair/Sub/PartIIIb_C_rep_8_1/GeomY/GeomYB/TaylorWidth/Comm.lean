import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomY.GeomYB
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomX.PhasePrimitive
import UnforcedLeray.Short.PartIIIa.T17_SepMeanComparison.MomentSplit

/-!
# The commutator `[D_{μ+1}, 𝒞_y]` of a separated-kernel field (shared by `GeomYB.TaylorWidth`
and `GeomYB.PhasePrimitive`, tasks `PartIII-b:C/rep/8/1/1/2/5/{1,2}`)

Source `the November 2 reference manuscript`
lines 4171 (`X₀ = W_μ - W_{μ+1}`), 4195-4215 (`ward:cutoff-source`,
`Y = 𝒞_yW_μ + [D_{μ+1},𝒞_y]X₀`), 5383-5387 (the same commutator formula for `Y^mt`, the uncut
Newton fields), 5427-5432 ("apply the spatial kernel comparison to these terms separately"),
SP 3611-3621 (`sep:resolvent`), 3746-3757 (`thinSource`, `F̄`, `V_{μ,0}`).

* `srcX0 ν μ src = Re(W_μ(src) - W_{μ+1}(src))` for a thin source `src` (as `wardX0`);
* `newtonX0 ε μ G = ε² Re(V_{μ,0}(G) - V_{μ+1,0}(G))(ε·)`, the zero-width Newton field of a
  phase-free planar source `G` (`W^mt = ε²V(ε·)`, source 4784);
* `comm ν μ R χ_y Z = D_{μ+1}(𝒞_yZ) - 𝒞_y(D_{μ+1}Z)` (`physDmu`, `wardStreamCut`).

Bridges (proved): `actYB T = comm (zAct0 T)`, `actYBMid T = comm (zMid T)` (definitional);
`zAct0 T = srcX0 (thinSource ε F)` for the cut planar lift `F = liftSrc T` (`PhasePrim.sepW_cut`),
`zMid T = srcX0 (thinSource ε (meanLift Ḡ))` for its phase mean `Ḡ = meanSrc T`
(`PhasePrim.sepW_mean`), and `N₁(meanLift Ḡ) ≤ N₁(F) ≤ πN` (`PhasePrim.thinMoment_cutLift_le`,
`IIIa.sepMomentSplit`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace YBComm

open PhasePrim

/-- `X₀ = W_μ - W_{μ+1}` of a thin source `src` in its separated-kernel realization, real
Cartesian components (source 4171, SP 3611-3621; as `wardX0` with `src` in place of `oldPhys`). -/
def srcX0 (ν μ : ℝ) (src : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) : ℝ → Space → Space :=
  fun τ y => WithLp.toLp 2 fun i =>
    (IIIa.sepW ν (μ : ℂ) src y τ i - IIIa.sepW ν ((μ : ℂ) + 1) src y τ i).re

/-- The zero-width Newton field `ε² Re(V_{μ,0}(G) - V_{μ+1,0}(G))(εy)` of a phase-free planar
source `G` (source 4776-4791: `W^mt_μ(y) = ε²V_{μ,M}(εy)`; SP 3753-3757: `V_{μ,0}`), phase free. -/
def newtonX0 (ε μ : ℝ) (G : ℝ × ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ) : ℝ → Space → Space :=
  fun _ y => (ε ^ 2) • reMap (IIIa.sepVmu0 (μ : ℂ) G (ε • y) - IIIa.sepVmu0 ((μ : ℂ) + 1) G (ε • y))

/-- The commutator `[D_{μ+1}, 𝒞_y]Z = D_{μ+1}(𝒞_yZ) - 𝒞_y(D_{μ+1}Z)` (source 4195-4200,
5383-5387), `𝒞_y` the solenoidal stream cutoff `wardStreamCut` at `R`. -/
def comm (ν μ R : ℝ) (χy : ℝ → ℝ) (Z : ℝ → Space → Space) : ℝ → Space → Space := fun τ y =>
  physDmu ν (μ + 1) (wardStreamCut ν R χy Z) τ y - wardStreamCut ν R χy (physDmu ν (μ + 1) Z) τ y

section Regime

variable (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)

/-- The cut planar lift `F = cutLift c √(5ν/6) g` of the old thin source `g = thinG T`
(`oldPhys ε⁻¹ c g` and `thinSource ε F` have the same responses, `PhasePrim.sepW_cut`). -/
def liftSrc (T : LStr Pl K L) : ℝ × ℝ → ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ :=
  cutLift (cOf L.ν) (Real.sqrt (5 * L.ν / 6)) (thinG Pl K L T)

/-- Its phase mean `Ḡ = c⁻¹∫₀^c F dq` (SP 3753-3757 `F̄`; source 4764-4770). -/
def meanSrc (T : LStr Pl K L) : ℝ × ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ :=
  IIIa.phaseMean (cOf L.ν) (liftSrc Pl K L T)

theorem actYB_eq_comm (T : LStr Pl K L) :
    actYB Pl K L μ T = comm L.ν μ L.ε⁻¹ K.χy (zAct0 Pl K L μ T) := rfl

theorem actYBMid_eq_comm (T : LStr Pl K L) :
    actYBMid Pl K L μ T = comm L.ν μ L.ε⁻¹ K.χy (zMid Pl K L μ T) := rfl

theorem thinG_meas (T : LStr Pl K L) : Measurable (thinG Pl K L T) := by
  unfold thinG
  exact (Lp.stronglyMeasurable _).measurable.add (Lp.stronglyMeasurable _).measurable

theorem thinG_young (hC0 : 0 < K.C0) (T : LStr Pl K L) :
    ∀ᵐ p ∂(ageμ (cOf L.ν) (-1 / 2)), L.ν * p.1 ≤ 6 / 5 → thinG Pl K L T p = 0 :=
  ZRegAux.strSum_zero_young _ _ _ _ _ K.hχo (ZRegAux.rho_b_pos' Pl K L hC0) _

/-- **`X₀` of the actual old source is `srcX0` of the cut planar lift** (source 4171; SP 3746-3751). -/
theorem zAct0_eq_srcX0 (hC0 : 0 < K.C0) (T : LStr Pl K L) :
    zAct0 Pl K L μ T = srcX0 L.ν μ (IIIa.thinSource L.ε (liftSrc Pl K L T)) := by
  have hν : 0 < L.ν := L.ν_pos
  have hε : 0 < L.ε := L.ε_pos
  have hc : 0 < cOf L.ν := cOf_pos hν
  have hz := thinG_young Pl K L hC0 T
  funext τ y
  unfold zAct0 wardX0 srcX0 liftSrc
  rw [sepW_cut (cOf L.ν) L.ν L.ε _ hc hν hε _ hz y τ,
    sepW_cut (cOf L.ν) L.ν L.ε _ hc hν hε _ hz y τ]

/-- **`X₀` of the phase-mean chart tensor is `srcX0` of the phase-mean planar source** (source
4764-4770; SP 3753-3757). -/
theorem zMid_eq_srcX0 (hC0 : 0 < K.C0) (hmZ : 3 / 2 < K.mZ) (T : LStr Pl K L) :
    zMid Pl K L μ T = srcX0 L.ν μ (IIIa.thinSource L.ε (IIIa.meanLift (meanSrc Pl K L T))) := by
  have hν : 0 < L.ν := L.ν_pos
  have hε : 0 < L.ε := L.ε_pos
  have hc : 0 < cOf L.ν := cOf_pos hν
  have hρb : 0 < L.ρb Pl K := ZRegAux.rho_b_pos' Pl K L hC0
  have hgm := thinG_meas Pl K L T
  have hmom : ∫⁻ p, ‖thinG Pl K L T p‖ₑ ^ 2 ∂(ageμ (cOf L.ν) (-1 / 2)) < ⊤ :=
    strChartL2 (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν hρb (by linarith) hν _
  have hz' := ZRegAux.mean_ae_zero (cOf L.ν) (-1 / 2) L.ν hc _ hgm (thinG_young Pl K L hC0 T)
  funext τ y
  unfold zMid wardX0 srcX0 meanSrc liftSrc
  rw [sepW_mean (cOf L.ν) L.ν L.ε _ hc hν hε _ hgm hmom hz' y τ,
    sepW_mean (cOf L.ν) L.ν L.ε _ hc hν hε _ hgm hmom hz' y τ]

/-- `N₁(F) ≤ πN`, `N = oldN1 T` (SP 2790-2795, source 5400). -/
theorem thinMoment_liftSrc_le (hC0 : 0 < K.C0) (T : LStr Pl K L) :
    IIIa.thinMoment (cOf L.ν) (liftSrc Pl K L T) ≤ ENNReal.ofReal Real.pi * oldN1 Pl K L T := by
  have hc : 0 < cOf L.ν := cOf_pos L.ν_pos
  have h2 := thinMoment_cutLift_le (cOf L.ν) (Real.sqrt (5 * L.ν / 6)) hc _ (thinG_meas Pl K L T)
  rw [firstMoment_thinG Pl K L hC0 T] at h2
  exact h2

/-- `N₁(meanLift Ḡ) ≤ N₁(F) ≤ πN` (Jensen in `q`, `IIIa.sepMomentSplit`). -/
theorem thinMoment_meanSrc_le (hC0 : 0 < K.C0) (T : LStr Pl K L) :
    IIIa.thinMoment (cOf L.ν) (IIIa.meanLift (meanSrc Pl K L T)) ≤
      ENNReal.ofReal Real.pi * oldN1 Pl K L T := by
  have hc : 0 < cOf L.ν := cOf_pos L.ν_pos
  have h1 := (IIIa.sepMomentSplit (cOf L.ν) hc (liftSrc Pl K L T)
    (cutLift_measurable _ _ _ (thinG_meas Pl K L T))).1
  exact h1.trans (thinMoment_liftSrc_le Pl K L hC0 T)

theorem liftSrc_measurable (T : LStr Pl K L) (i j : Fin 3) :
    Measurable fun w : (ℝ × ℝ) × ℝ × ℝ => liftSrc Pl K L T w.1 w.2.1 w.2.2 i j :=
  cutLift_measurable _ _ _ (thinG_meas Pl K L T) i j

theorem liftSrc_periodic (T : LStr Pl K L) (x' : ℝ × ℝ) (Y q : ℝ) :
    liftSrc Pl K L T x' Y (q + cOf L.ν) = liftSrc Pl K L T x' Y q :=
  cutLift_periodic _ _ (cOf_pos L.ν_pos).ne' _ x' Y q

theorem liftSrc_support (T : LStr Pl K L) (x' : ℝ × ℝ) (Y q : ℝ)
    (h : Real.sqrt (5 * L.ν / 6) < Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2)) :
    liftSrc Pl K L T x' Y q = 0 :=
  cutLift_support _ _ _ x' Y q h

theorem meanSrc_measurable (T : LStr Pl K L) (i j : Fin 3) :
    Measurable fun w : (ℝ × ℝ) × ℝ => meanSrc Pl K L T w.1 w.2 i j :=
  IIIa.phaseMean_measurable _ _ (cutLift_measurable _ _ _ (thinG_meas Pl K L T)) i j

theorem meanSrc_support (T : LStr Pl K L) (x' : ℝ × ℝ) (Y : ℝ)
    (h : Real.sqrt (5 * L.ν / 6) < Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2)) :
    meanSrc Pl K L T x' Y = 0 := by
  have hz : ∀ q, liftSrc Pl K L T x' Y q = 0 := fun q => liftSrc_support Pl K L T x' Y q h
  funext i j
  unfold meanSrc IIIa.phaseMean
  simp only [hz]
  simp

end Regime

/-! ### The young receiver and the constants -/

/-- The young receiver `y = chartY ε⁻¹ (s, q, η) = ε⁻¹x_obs`: `|x_obs'| = s^{-1/2}`, so
`ν ≤ |x_obs'|²` for `s ≤ 1/ν` and `|x_obs'|^{-5} = s^{5/2}`. -/
theorem receiver (ν ε s q η : ℝ) (hν : 0 < ν) (hε : 0 < ε) (hs : s ∈ Ioc (0 : ℝ) (1 / ν)) :
    ε⁻¹ • (ε • NearInst.chartY ε⁻¹ (s, (q, η))) = NearInst.chartY ε⁻¹ (s, (q, η)) ∧
      ν ≤ (ε • NearInst.chartY ε⁻¹ (s, (q, η))) 0 ^ 2 +
        (ε • NearInst.chartY ε⁻¹ (s, (q, η))) 1 ^ 2 ∧
      Real.sqrt ((ε • NearInst.chartY ε⁻¹ (s, (q, η))) 0 ^ 2 +
        (ε • NearInst.chartY ε⁻¹ (s, (q, η))) 1 ^ 2) ^ (-5 : ℝ) = s ^ (5 / 2 : ℝ) := by
  have hs0 : 0 < s := hs.1
  have hss : 0 < Real.sqrt s := Real.sqrt_pos.2 hs0
  set y := NearInst.chartY ε⁻¹ (s, (q, η)) with hy
  have h0 : (ε • y) 0 = (Real.sqrt s)⁻¹ := by
    rw [hy, GeomXAsm.chartY_eq_hpt]
    show ε * (ε⁻¹ / Real.sqrt s) = _
    field_simp
  have h1 : (ε • y) 1 = 0 := by
    rw [hy, GeomXAsm.chartY_eq_hpt]
    show ε * 0 = _
    ring
  have hxr : Real.sqrt ((ε • y) 0 ^ 2 + (ε • y) 1 ^ 2) = (Real.sqrt s)⁻¹ := by
    rw [h0, h1, show (0 : ℝ) ^ 2 = 0 by norm_num, add_zero, Real.sqrt_sq (by positivity)]
  refine ⟨by rw [smul_smul, inv_mul_cancel₀ hε.ne', one_smul], ?_, ?_⟩
  · rw [h0, h1, inv_pow, Real.sq_sqrt hs0.le]
    have hs2 := hs.2
    rw [le_div_iff₀ hν] at hs2
    rw [show (0 : ℝ) ^ 2 = 0 by norm_num, add_zero, le_inv_comm₀ hν hs0, ← one_div,
      le_div_iff₀ hν]
    exact hs2
  · rw [hxr, rpow_neg_five s hs0]

/-- `1 + ν⁻¹ + c ≤ 3ν⁻²` for `c = cOf ν`, `0 < ν ≤ 1`. -/
theorem poly3 (ν : ℝ) (hν : 0 < ν) (hν1 : ν ≤ 1) : 1 + ν⁻¹ + cOf ν ≤ 3 * ν⁻¹ ^ 2 := by
  have hνi : 1 ≤ ν⁻¹ := one_le_inv_iff₀.2 ⟨hν, hν1⟩
  have hc : cOf ν = ν⁻¹ ^ 2 := by unfold cOf; rw [inv_pow]
  rw [hc]
  nlinarith

end YBComm

end UnforcedLeray.Short.PartIIIb.Concrete
