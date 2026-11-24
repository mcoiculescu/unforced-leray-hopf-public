import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_3
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.Assembly
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.L5_WardGradXPhase
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.L7_WardGradYPhase
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.L8_RepairSepBridge
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.HessianBound.ZActJet

/-!
# Audit decomposition of `PartIII-b:C/rep/3/3` (`RepJet`)

Source of record: `the November 2 reference manuscript` (73 pages), lines
5212-5223 (`repair:phase-gradient`), 5259-5268 (`D²X` in `Y_{22/3}` with an additional curvature
power `(R√ν)⁻¹ ≤ ν⁻¹`), and 2681-2689 (chart-to-physical lift identity).

`RepJetAt Pl K L μ C k` bounds the `Y_{22/3}` chart norm (`ringPhysμ L.ε⁻¹ (cOf L.ν)`) of
`ringRead L.ε⁻¹ (fun τ => meanJetDens (repX Pl K L μ w τ) (repY Pl K L μ w τ))`, where
`meanJetDens X Y y = ‖fderiv ℝ Y y‖ + gradSize X y + hessSize X y`, together with its
`AEStronglyMeasurable` property.

Since `ringRead R f p` evaluates `f (chartTau R p)` at the meridian point
`chartY R p = !₂[R / √p.1, 0, p.2.2 / √p.1] = !₂[ϱ z, 0, z 2]`, the decomposition splits into three
independent leaves:
* `RepJetChartTransfer` (`PartIII-b:C/rep/3/3/1`): chart measurability of
  `ringRead L.ε⁻¹ (fun τ => meanJetDens (repX ...) (repY ...))` on `ringPhysμ L.ε⁻¹ (cOf L.ν)`, and
  the lift transfer `eLpNorm ... (22/3) (ringPhysμ ...) ≤ B` from a uniform slice bound
  `∀ τ : ℝ, lqNorm (22/3) (fun y => ENNReal.ofReal (meanJetDens (repX ... τ) (repY ... τ) !₂[ϱ y, 0, y 2])) ≤ B`.
* `SepWXHessMeridPointwise` (`PartIII-b:C/rep/3/3/2`): pointwise meridian bound on
  `hessSize (sepWX ν μ R χy T τ) !₂[ϱ y, 0, y 2]` for `0 < ϱ y` in terms of `wgxJet j` (`j = 0, 1, 2`)
  and `wgxPsi` at `!₂[ϱ y, 0, y 2]` (from `streamCutHess` on the cutoff annulus and vanishing /
  identity outside).
* `SepJetMeridEq` (`PartIII-b:C/rep/3/3/3`): rotation invariance of `wgxJet j`, `wgyWJet j`,
  `wgxPsi`, `wgyWPsi` at `!₂[ϱ y, 0, y 2]` for `0 < ϱ y` (from orthogonal equivariance of `sepX0`
  and `sepWre`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

/-- **Leaf 1 (`PartIII-b:C/rep/3/3/1`): chart measurability and lift transfer for `meanJetDens`**
(source 2681-2689, 5259-5268).  Off the axis `repX` is `C²` and `repY` is `C¹` (`WardEMeasAux.wemOff`),
so `ringRead L.ε⁻¹ (fun τ => meanJetDens (repX ...) (repY ...))` is a.e. strongly measurable for
`ringPhysμ L.ε⁻¹ (cOf L.ν)`; by `chartPhaseLIntegral`, `chartTauOf_proved`, `chartYOf_proved` and
time periodicity of `repX, repY`, a uniform slice bound on `lqNorm (22/3)` of the meridian reading
`y ↦ meanJetDens (repX ... τ) (repY ... τ) !₂[ϱ y, 0, y 2]` bounds the `L^{22/3}(ringPhysμ)` norm. -/
def RepJetChartTransfer : Prop :=
  ∀ (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ),
    IsStreamCutoff K.χy → -(1 / 4 : ℝ) < μ → 0 < K.C0 → 0 ≤ K.mZ →
    ∀ (w : LVel Pl L),
      AEStronglyMeasurable (ringRead L.ε⁻¹ fun τ =>
          meanJetDens (repX Pl K L μ w τ) (repY Pl K L μ w τ))
        (ringPhysμ L.ε⁻¹ (cOf L.ν)) ∧
      ∀ (B : ℝ≥0∞),
        (∀ τ : ℝ, lqNorm (22 / 3) (fun y : Space =>
            ENNReal.ofReal
              (meanJetDens (repX Pl K L μ w τ) (repY Pl K L μ w τ) !₂[ϱ y, 0, y 2])) ≤ B) →
        eLpNorm (ringRead L.ε⁻¹ fun τ =>
            meanJetDens (repX Pl K L μ w τ) (repY Pl K L μ w τ))
          (22 / 3) (ringPhysμ L.ε⁻¹ (cOf L.ν)) ≤ B

/-- **Leaf 2 (`PartIII-b:C/rep/3/3/2`): pointwise meridian Hessian bound for `sepWX`**
(source 4181-4192, 5259-5268).  At every meridian point `!₂[ϱ y, 0, y 2]` with `0 < ϱ y`,
`hessSize (sepWX ν μ R χy T τ) !₂[ϱ y, 0, y 2]` is bounded by the 2-jet of `sepX0` and the outward
primitive `wgxPsi` with powers of `L⁻¹ = (R√ν)⁻¹` (`streamCutHess` on `[L, R√(5ν/4)]`, vanishing for
`ϱ y < L`, and `sepWX = sepX0` for `ϱ y > R√(5ν/4)`). -/
def SepWXHessMeridPointwise : Prop :=
  ∀ (σ₁ σ₂ : ℝ), -(1 / 4 : ℝ) < σ₁ → ∀ (χy : ℝ → ℝ), IsStreamCutoff χy →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (ν μ R P : ℝ), 0 < ν → ν ≤ 1 → 1 ≤ R → 0 < P → P ≤ 1 → μ ∈ Icc σ₁ σ₂ →
        ∀ T, IIIa.IsSepSource P (R * Real.sqrt (5 * ν / 6)) T → SepMoment P T → IsAxiSource T →
          ∀ (τ : ℝ) (y : Space), 0 < ϱ y →
            ENNReal.ofReal (hessSize (sepWX ν μ R χy T τ) !₂[ϱ y, 0, y 2]) ≤
              ENNReal.ofReal C *
                (wgxJet 2 ν μ (R * Real.sqrt ν) T τ !₂[ϱ y, 0, y 2] +
                  ENNReal.ofReal (R * Real.sqrt ν)⁻¹ *
                    wgxJet 1 ν μ (R * Real.sqrt ν) T τ !₂[ϱ y, 0, y 2] +
                  ENNReal.ofReal ((R * Real.sqrt ν)⁻¹ ^ 2) *
                    wgxJet 0 ν μ (R * Real.sqrt ν) T τ !₂[ϱ y, 0, y 2] +
                  ENNReal.ofReal ((R * Real.sqrt ν)⁻¹ ^ 3) *
                    wgxPsi ν μ R T τ !₂[ϱ y, 0, y 2])

/-- **Leaf 3 (`PartIII-b:C/rep/3/3/3`): rotation invariance of the separated jet densities**
(source 2681-2689, 3603-3629).  For an axisymmetric separated source `T`, `sepX0` and `sepWre` are
equivariant under horizontal rotations `rotM co si`, so the norms of their `j`-jets (`wgxJet j`,
`wgyWJet j`) and outward primitives (`wgxPsi`, `wgyWPsi`) at `!₂[ϱ y, 0, y 2]` equal their values
at `y` whenever `0 < ϱ y`. -/
def SepJetMeridEq : Prop :=
  ∀ (ν μ R P : ℝ), 0 < ν → 0 < R → 0 < P → -(1 / 4 : ℝ) < μ →
    ∀ T, IIIa.IsSepSource P (R * Real.sqrt (5 * ν / 6)) T → SepMoment P T → IsAxiSource T →
      ∀ (τ : ℝ) (y : Space), 0 < ϱ y →
        (∀ j : ℕ, wgxJet j ν μ (R * Real.sqrt ν) T τ !₂[ϱ y, 0, y 2] =
          wgxJet j ν μ (R * Real.sqrt ν) T τ y) ∧
        (∀ j : ℕ, wgyWJet j ν μ (R * Real.sqrt ν) T τ !₂[ϱ y, 0, y 2] =
          wgyWJet j ν μ (R * Real.sqrt ν) T τ y) ∧
        wgxPsi ν μ R T τ !₂[ϱ y, 0, y 2] = wgxPsi ν μ R T τ y ∧
        wgyWPsi ν μ R T τ !₂[ϱ y, 0, y 2] = wgyWPsi ν μ R T τ y

private lemma rj_varrho_merid (y : Space) : ϱ !₂[ϱ y, 0, y 2] = ϱ y := by
  have : !₂[ϱ y, 0, y 2] = meridPt y := rfl
  rw [this, varrho_meridPt]

private lemma rj_gradSize_le_three_fderiv (f : Space → Space) (y : Space) :
    ENNReal.ofReal (gradSize f y) ≤ ENNReal.ofReal 3 * ENNReal.ofReal ‖fderiv ℝ f y‖ := by
  rw [← ENNReal.ofReal_mul (by norm_num)]
  refine ENNReal.ofReal_le_ofReal ?_
  have h := ZActJetAux.gradSize_le_iteratedFDeriv f y
  rwa [norm_iteratedFDeriv_one] at h

private lemma rj_L_inv_le_nu_inv {ν R : ℝ} (hν : 0 < ν) (hν1 : ν ≤ 1) (hR1 : 1 ≤ R) :
    (R * Real.sqrt ν)⁻¹ ≤ ν⁻¹ := by
  refine inv_anti₀ hν ?_
  have h1 : ν ≤ Real.sqrt ν := by
    have hs : 0 ≤ Real.sqrt ν := Real.sqrt_nonneg ν
    nlinarith [Real.sq_sqrt hν.le, Real.sqrt_le_one.2 hν1]
  nlinarith [Real.sqrt_pos.2 hν]

private lemma rj_sum3 (C m1 m2 m3 Y : ℝ) (F : ℝ≥0∞) (hC : 0 ≤ C) (h1 : 0 ≤ m1) (h2 : 0 ≤ m2)
    (h3 : 0 ≤ m3) (hY : 0 ≤ Y) :
    ENNReal.ofReal C * (ENNReal.ofReal (m1 * Y) * F + ENNReal.ofReal (m2 * Y) * F +
        ENNReal.ofReal (m3 * Y) * F) =
      ENNReal.ofReal ((C * (m1 + m2 + m3)) * Y) * F := by
  have e : (C * (m1 + m2 + m3)) * Y = C * (m1 * Y + m2 * Y + m3 * Y) := by ring
  rw [e, ENNReal.ofReal_mul hC, ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_add (by positivity) (by positivity)]
  simp only [add_mul, mul_add, mul_assoc]

private lemma rj_sum4 (C m1 m2 m3 m4 Y : ℝ) (F : ℝ≥0∞) (hC : 0 ≤ C) (h1 : 0 ≤ m1) (h2 : 0 ≤ m2)
    (h3 : 0 ≤ m3) (h4 : 0 ≤ m4) (hY : 0 ≤ Y) :
    ENNReal.ofReal C * (ENNReal.ofReal (m1 * Y) * F + ENNReal.ofReal (m2 * Y) * F +
        ENNReal.ofReal (m3 * Y) * F + ENNReal.ofReal (m4 * Y) * F) =
      ENNReal.ofReal ((C * (m1 + m2 + m3 + m4)) * Y) * F := by
  have e : (C * (m1 + m2 + m3 + m4)) * Y = C * (m1 * Y + m2 * Y + m3 * Y + m4 * Y) := by ring
  rw [e, ENNReal.ofReal_mul hC, ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_add (by positivity) (by positivity)]
  simp only [add_mul, mul_add, mul_assoc]

private lemma rj_sum_final (MY MX MH ν L Y : ℝ) (F : ℝ≥0∞)
    (hMY : 0 ≤ MY) (hMX : 0 ≤ MX) (hMH : 0 ≤ MH) (hY0 : 0 ≤ Y)
    (hY : Y = ν⁻¹ * L ^ (-(46 / 11 : ℝ))) :
    (ENNReal.ofReal (MY * Y) * F + ENNReal.ofReal (MX * Y) * F) +
        ENNReal.ofReal (MH * Y) * F =
      ENNReal.ofReal ((MY + MX + MH) * ν⁻¹ * L ^ (-(46 / 11 : ℝ))) * F := by
  have h1 : 0 ≤ MY * Y := mul_nonneg hMY hY0
  have h2 : 0 ≤ MX * Y := mul_nonneg hMX hY0
  have h3 : 0 ≤ MH * Y := mul_nonneg hMH hY0
  have e : (MY + MX + MH) * ν⁻¹ * L ^ (-(46 / 11 : ℝ)) =
      (MY * Y + MX * Y) + MH * Y := by rw [hY]; ring
  rw [e, ENNReal.ofReal_add (add_nonneg h1 h2) h3, ENNReal.ofReal_add h1 h2]
  simp only [add_mul]

set_option maxHeartbeats 800000 in
/-- Slice `L^{22/3}` bound on `y ↦ meanJetDens (sepWX ...) (sepWY ...) !₂[ϱ y, 0, y 2]`. -/
theorem sepJetMeridSlice_of (hH : SepWXHessMeridPointwise) (hEq : SepJetMeridEq)
    (σ₁ σ₂ : ℝ) (hσ : -(1 / 4 : ℝ) < σ₁) (χy : ℝ → ℝ) (hχ : IsStreamCutoff χy) :
    ∃ (C : ℝ), 0 ≤ C ∧
      ∀ (ν μ R P : ℝ), 0 < ν → ν ≤ 1 → 1 ≤ R → 0 < P → P ≤ 1 → μ ∈ Icc σ₁ σ₂ →
        ∀ T, IIIa.IsSepSource P (R * Real.sqrt (5 * ν / 6)) T → SepMoment P T → IsAxiSource T →
          ∀ τ : ℝ,
            lqNorm (22 / 3) (fun y : Space =>
                ENNReal.ofReal
                  (meanJetDens (sepWX ν μ R χy T τ) (sepWY ν μ R χy T τ) !₂[ϱ y, 0, y 2])) ≤
              ENNReal.ofReal (C * ν⁻¹ * (R * Real.sqrt ν) ^ (-(46 / 11 : ℝ))) *
                IIIa.ltauLq P (22 / 19) (IIIa.srcNorm T) := by
  obtain ⟨Cx, hCx, hPtX⟩ := wgxPointwise σ₁ σ₂ hσ χy hχ
  obtain ⟨Cy1, Cy2, hCy1, hCy2, hPtY⟩ := wgyPointwise σ₁ σ₂ hσ χy hχ
  obtain ⟨Ch, hCh, hPtH⟩ := hH σ₁ σ₂ hσ χy hχ
  obtain ⟨CW0, hCW0, HW0⟩ := wgy_jet_phase σ₁ σ₂ hσ 0 (by norm_num)
  obtain ⟨CW1, hCW1, HW1⟩ := wgy_jet_phase σ₁ σ₂ hσ 1 (by norm_num)
  obtain ⟨D0, hD0, H0⟩ := sepX0PhaseBound σ₁ σ₂ hσ 0 (by norm_num)
  obtain ⟨D1, hD1, H1⟩ := sepX0PhaseBound σ₁ σ₂ hσ 1 (by norm_num)
  obtain ⟨D2, hD2, H2⟩ := sepX0PhaseBound σ₁ σ₂ hσ 2 (by norm_num)
  obtain ⟨Co, hCo, Ho⟩ := outPrimPhaseBound σ₁ σ₂ hσ
  set c0 : ℝ := 1 - Real.sqrt (5 / 6) with hc0
  have hs56 : Real.sqrt (5 / 6) < 1 := by rw [Real.sqrt_lt' one_pos]; norm_num
  have hc0pos : 0 < c0 := by rw [hc0]; linarith
  have hc0n : 0 ≤ c0 := hc0pos.le
  set e0 : ℝ := -4 - ((0 : ℕ) : ℝ) + 9 / 11 with he0
  set e1 : ℝ := -4 - ((1 : ℕ) : ℝ) + 9 / 11 with he1
  set e2 : ℝ := -4 - ((2 : ℕ) : ℝ) + 9 / 11 with he2
  set MY : ℝ := (1 * (CW1 * c0 ^ e1)) + (Cy1 * (CW0 * c0 ^ e0)) + (Cy1 * Co) +
      Cy2 * ((1 * (D0 * c0 ^ e0)) + (1 * (D1 * c0 ^ e1)) + (1 * (D2 * c0 ^ e2)) +
        (1 * (D1 * c0 ^ e1)) + (1 * Co))
  set MX : ℝ := 3 * ((1 * (D1 * c0 ^ e1)) + (Cx * (D0 * c0 ^ e0)) + (Cx * Co))
  set MH : ℝ := Ch * ((1 * (D2 * c0 ^ e2)) + (1 * (D1 * c0 ^ e1)) +
      (1 * (D0 * c0 ^ e0)) + (1 * Co))
  refine ⟨MY + MX + MH, by positivity, ?_⟩
  intro ν μ R P hν hν1 hR1 hP0 hP1 hμ T hT hSM hAx τ
  have hR : 0 < R := by linarith
  have hμ' : -(1 / 4 : ℝ) < μ := lt_of_lt_of_le hσ hμ.1
  set L : ℝ := R * Real.sqrt ν with hL
  have hLpos : 0 < L := by rw [hL]; positivity
  set F : ℝ≥0∞ := IIIa.ltauLq P (22 / 19) (IIIa.srcNorm T) with hF
  have hLsq : ν * R ^ 2 = L ^ 2 := by rw [hL, mul_pow, Real.sq_sqrt hν.le]; ring
  have hrO : R * Real.sqrt (5 * ν / 6) = Real.sqrt (5 / 6) * L := by
    rw [hL, show 5 * ν / 6 = 5 / 6 * ν by ring, Real.sqrt_mul (by norm_num)]; ring
  have hD : L - R * Real.sqrt (5 * ν / 6) = c0 * L := by rw [hrO, hc0]; ring
  have hrOnn : 0 ≤ R * Real.sqrt (5 * ν / 6) := by positivity
  have hlt : R * Real.sqrt (5 * ν / 6) < L := by
    have : 0 < c0 * L := mul_pos hc0pos hLpos
    linarith
  set X : ℝ := L ^ (-(46 / 11 : ℝ)) with hX
  set Y : ℝ := ν⁻¹ * X with hY
  have hX0 : 0 ≤ X := Real.rpow_nonneg hLpos.le _
  have hν1' : 1 ≤ ν⁻¹ := (one_le_inv₀ hν).2 hν1
  have hY0 : 0 ≤ Y := by positivity
  have hY1 : X ≤ Y := by
    calc X = 1 * X := (one_mul X).symm
      _ ≤ ν⁻¹ * X := mul_le_mul_of_nonneg_right hν1' hX0
  have hLinv_le : L⁻¹ ≤ ν⁻¹ := rj_L_inv_le_nu_inv hν hν1 hR1
  have hY57 : L ^ (-(57 / 11 : ℝ)) ≤ Y := by
    have h1 : L ^ (-(57 / 11 : ℝ)) = L⁻¹ * X := by
      rw [hX, ← Real.rpow_neg_one L, ← Real.rpow_add hLpos]; congr 1; norm_num
    rw [h1]
    exact mul_le_mul_of_nonneg_right hLinv_le hX0
  have hY2 : L ^ (-(68 / 11 : ℝ)) ≤ Y := by
    have h2 : L ^ (-(68 / 11 : ℝ)) = L ^ (-2 : ℝ) * X := by
      rw [hX, ← Real.rpow_add hLpos]; congr 1; norm_num
    have h3 : L ^ (-2 : ℝ) ≤ ν⁻¹ := by
      have : L ^ (-2 : ℝ) = (L ^ 2)⁻¹ := by
        rw [Real.rpow_neg hLpos.le]; norm_cast
      rw [this, ← hLsq]
      refine inv_anti₀ hν ?_
      nlinarith [mul_pos hν (pow_pos hR 2), sq_nonneg R, mul_nonneg hν.le (sq_nonneg (R - 1)),
        mul_nonneg hν.le (sq_nonneg R)]
    rw [h2]
    exact mul_le_mul_of_nonneg_right h3 hX0
  have hLinv : L⁻¹ = L ^ (-1 : ℝ) := (Real.rpow_neg_one L).symm
  have hLinv2 : L⁻¹ ^ 2 = L ^ (-2 : ℝ) := by
    rw [Real.rpow_neg hLpos.le, inv_pow]; norm_cast
  have hLinv3 : L⁻¹ ^ 3 = L ^ (-3 : ℝ) := by
    rw [Real.rpow_neg hLpos.le, inv_pow]; norm_cast
  have hmul : ∀ a b c : ℝ, a + b = c → L ^ a * L ^ b = L ^ c := fun a b c h => by
    rw [← Real.rpow_add hLpos, h]
  obtain ⟨m1, m0, mP⟩ := wgxMeas ν μ R P hν hR hP0 T hT hSM τ
  obtain ⟨w1, w0, wP⟩ := wgyMeas_W ν μ R P T hT τ
  have m2 := wgyMeas_X2 ν μ L T τ
  have hq : (1 : ℝ) ≤ 22 / 3 := by norm_num
  have hq0 : (0 : ℝ) < 22 / 3 := by norm_num
  have haxis : ∀ᵐ y : Space, 0 < ϱ y := by
    have : ∀ᵐ y : Space, y ∉ {y : Space | ϱ y = 0} :=
      measure_eq_zero_iff_ae_notMem.1 wgxAxisNull
    filter_upwards [this] with y hy
    exact lt_of_le_of_ne (Real.sqrt_nonneg _) (fun h => hy h.symm)
  have eW1 := HW1 ν μ (R * Real.sqrt (5 * ν / 6)) L P hν hμ hrOnn hlt hP0 hP1 T hT hSM τ
  have eW0 := HW0 ν μ (R * Real.sqrt (5 * ν / 6)) L P hν hμ hrOnn hlt hP0 hP1 T hT hSM τ
  have hE1 := H1 ν μ (R * Real.sqrt (5 * ν / 6)) L P hν hμ hrOnn hlt hP0 hP1 T hT hSM τ
  have hE0 := H0 ν μ (R * Real.sqrt (5 * ν / 6)) L P hν hμ hrOnn hlt hP0 hP1 T hT hSM τ
  have hE2 := H2 ν μ (R * Real.sqrt (5 * ν / 6)) L P hν hμ hrOnn hlt hP0 hP1 T hT hSM τ
  obtain ⟨eoW, eoX⟩ := Ho ν μ R P hν hR hP0 hP1 hμ T hT hSM τ
  rw [hD] at eW1 eW0 hE1 hE0 hE2
  have x1 : L ^ e1 = X := by rw [hX, he1]; congr 1; norm_num
  have x0 : L ^ (-1 : ℝ) * L ^ e0 = X := by
    rw [hmul _ _ (-(46 / 11)) (by rw [he0]; norm_num)]
  have x2 : L⁻¹ * L ^ e2 = L ^ (-(68 / 11 : ℝ)) := by
    rw [hLinv, hmul _ _ (-(68 / 11)) (by rw [he2]; norm_num)]
  have x4 : L ^ (-2 : ℝ) * L ^ e1 = L ^ (-(68 / 11 : ℝ)) := by
    rw [hmul _ _ (-(68 / 11)) (by rw [he1]; norm_num)]
  have x3 : L ^ (-3 : ℝ) * L ^ (-(13 / 11 : ℝ)) = X := by
    rw [hX, hmul _ _ (-(46 / 11)) (by norm_num)]
  have xH2 : L ^ e2 = L ^ (-(57 / 11 : ℝ)) := by rw [he2]; congr 1; norm_num
  have xH1 : L⁻¹ * L ^ e1 = L ^ (-(57 / 11 : ℝ)) := by
    rw [hLinv, hmul _ _ (-(57 / 11)) (by rw [he1]; norm_num)]
  have xH0 : L ^ (-2 : ℝ) * L ^ e0 = L ^ (-(57 / 11 : ℝ)) := by
    rw [hmul _ _ (-(57 / 11)) (by rw [he0]; norm_num)]
  -- DY terms
  have t1 : lqNorm (22 / 3) (wgyWJet 1 ν μ L T τ) ≤
      ENNReal.ofReal ((1 * (CW1 * c0 ^ e1)) * Y) * F := by
    simpa using wgy_term 1 (CW1 * (c0 * L) ^ e1) (1 * (CW1 * c0 ^ e1)) Y F
      (g := wgyWJet 1 ν μ L T τ) zero_le_one
      (mul_nonneg hCW1 (Real.rpow_nonneg (mul_nonneg hc0n hLpos.le) _))
      (wgy_k 1 CW1 c0 L e1 Y 1 hCW1 hc0n hLpos.le zero_le_one
        (by rw [x1, one_mul, one_mul]; exact hY1)) eW1
  have t2 : lqNorm (22 / 3) (fun y => ENNReal.ofReal (Cy1 * L ^ (-1 : ℝ)) * wgyWJet 0 ν μ L T τ y) ≤
      ENNReal.ofReal ((Cy1 * (CW0 * c0 ^ e0)) * Y) * F :=
    wgy_term (Cy1 * L ^ (-1 : ℝ)) (CW0 * (c0 * L) ^ e0) (Cy1 * (CW0 * c0 ^ e0)) Y F
      (by positivity) (mul_nonneg hCW0 (Real.rpow_nonneg (mul_nonneg hc0n hLpos.le) _))
      (wgy_k _ CW0 c0 L e0 Y Cy1 hCW0 hc0n hLpos.le (by positivity) (by
        rw [mul_assoc, x0]; exact mul_le_mul_of_nonneg_left hY1 hCy1)) eW0
  have t3 : lqNorm (22 / 3) (fun y => ENNReal.ofReal (Cy1 * L ^ (-3 : ℝ)) * wgyWPsi ν μ R T τ y) ≤
      ENNReal.ofReal ((Cy1 * Co) * Y) * F :=
    wgy_term (Cy1 * L ^ (-3 : ℝ)) (Co * L ^ (-(13 / 11 : ℝ))) (Cy1 * Co) Y F
      (by positivity) (by positivity)
      (by
        calc Cy1 * L ^ (-3 : ℝ) * (Co * L ^ (-(13 / 11 : ℝ))) =
            (Cy1 * Co) * (L ^ (-3 : ℝ) * L ^ (-(13 / 11 : ℝ))) := by ring
          _ ≤ (Cy1 * Co) * Y := by rw [x3]; exact mul_le_mul_of_nonneg_left hY1 (by positivity))
      eoW
  have q1 : lqNorm (22 / 3) (fun y => ENNReal.ofReal L⁻¹ * wgxJet 0 ν μ L T τ y) ≤
      ENNReal.ofReal ((1 * (D0 * c0 ^ e0)) * Y) * F :=
    wgy_term L⁻¹ (D0 * (c0 * L) ^ e0) (1 * (D0 * c0 ^ e0)) Y F (inv_nonneg.2 hLpos.le)
      (mul_nonneg hD0 (Real.rpow_nonneg (mul_nonneg hc0n hLpos.le) _))
      (wgy_k _ D0 c0 L e0 Y 1 hD0 hc0n hLpos.le (inv_nonneg.2 hLpos.le) (by
        rw [hLinv, x0, one_mul]; exact hY1)) hE0
  have q2 : lqNorm (22 / 3) (wgxJet 1 ν μ L T τ) ≤
      ENNReal.ofReal ((1 * (D1 * c0 ^ e1)) * Y) * F := by
    simpa using wgy_term 1 (D1 * (c0 * L) ^ e1) (1 * (D1 * c0 ^ e1)) Y F
      (g := wgxJet 1 ν μ L T τ) zero_le_one
      (mul_nonneg hD1 (Real.rpow_nonneg (mul_nonneg hc0n hLpos.le) _))
      (wgy_k 1 D1 c0 L e1 Y 1 hD1 hc0n hLpos.le zero_le_one
        (by rw [x1, one_mul, one_mul]; exact hY1)) hE1
  have q3 : lqNorm (22 / 3) (fun y => ENNReal.ofReal L⁻¹ * wgxJet 2 ν μ L T τ y) ≤
      ENNReal.ofReal ((1 * (D2 * c0 ^ e2)) * Y) * F :=
    wgy_term L⁻¹ (D2 * (c0 * L) ^ e2) (1 * (D2 * c0 ^ e2)) Y F (inv_nonneg.2 hLpos.le)
      (mul_nonneg hD2 (Real.rpow_nonneg (mul_nonneg hc0n hLpos.le) _))
      (wgy_k _ D2 c0 L e2 Y 1 hD2 hc0n hLpos.le (inv_nonneg.2 hLpos.le) (by
        rw [x2, one_mul]; exact hY2)) hE2
  have q4 : lqNorm (22 / 3) (fun y => ENNReal.ofReal (L⁻¹ ^ 2) * wgxJet 1 ν μ L T τ y) ≤
      ENNReal.ofReal ((1 * (D1 * c0 ^ e1)) * Y) * F :=
    wgy_term (L⁻¹ ^ 2) (D1 * (c0 * L) ^ e1) (1 * (D1 * c0 ^ e1)) Y F (by positivity)
      (mul_nonneg hD1 (Real.rpow_nonneg (mul_nonneg hc0n hLpos.le) _))
      (wgy_k _ D1 c0 L e1 Y 1 hD1 hc0n hLpos.le (by positivity) (by
        rw [hLinv2, x4, one_mul]; exact hY2)) hE1
  have q5 : lqNorm (22 / 3) (fun y => ENNReal.ofReal (L⁻¹ ^ 3) * wgxPsi ν μ R T τ y) ≤
      ENNReal.ofReal ((1 * Co) * Y) * F :=
    wgy_term (L⁻¹ ^ 3) (Co * L ^ (-(13 / 11 : ℝ))) (1 * Co) Y F (by positivity) (by positivity)
      (by
        rw [hLinv3]
        calc L ^ (-3 : ℝ) * (Co * L ^ (-(13 / 11 : ℝ))) =
            Co * (L ^ (-3 : ℝ) * L ^ (-(13 / 11 : ℝ))) := by ring
          _ ≤ (1 * Co) * Y := by
              rw [x3, one_mul]
              exact mul_le_mul_of_nonneg_left hY1 hCo)
      eoX
  -- DX extra terms
  have gx0 : lqNorm (22 / 3) (fun y => ENNReal.ofReal (Cx * L ^ (-1 : ℝ)) * wgxJet 0 ν μ L T τ y) ≤
      ENNReal.ofReal ((Cx * (D0 * c0 ^ e0)) * Y) * F :=
    wgy_term (Cx * L ^ (-1 : ℝ)) (D0 * (c0 * L) ^ e0) (Cx * (D0 * c0 ^ e0)) Y F
      (by positivity) (mul_nonneg hD0 (Real.rpow_nonneg (mul_nonneg hc0n hLpos.le) _))
      (wgy_k _ D0 c0 L e0 Y Cx hD0 hc0n hLpos.le (by positivity) (by
        rw [mul_assoc, x0]; exact mul_le_mul_of_nonneg_left hY1 hCx)) hE0
  have gxP : lqNorm (22 / 3) (fun y => ENNReal.ofReal (Cx * L ^ (-3 : ℝ)) * wgxPsi ν μ R T τ y) ≤
      ENNReal.ofReal ((Cx * Co) * Y) * F :=
    wgy_term (Cx * L ^ (-3 : ℝ)) (Co * L ^ (-(13 / 11 : ℝ))) (Cx * Co) Y F
      (by positivity) (by positivity)
      (by
        calc Cx * L ^ (-3 : ℝ) * (Co * L ^ (-(13 / 11 : ℝ))) =
            (Cx * Co) * (L ^ (-3 : ℝ) * L ^ (-(13 / 11 : ℝ))) := by ring
          _ ≤ (Cx * Co) * Y := by rw [x3]; exact mul_le_mul_of_nonneg_left hY1 (by positivity))
      eoX
  -- D²X extra terms
  have h2_bd : lqNorm (22 / 3) (wgxJet 2 ν μ L T τ) ≤
      ENNReal.ofReal ((1 * (D2 * c0 ^ e2)) * Y) * F := by
    simpa using wgy_term 1 (D2 * (c0 * L) ^ e2) (1 * (D2 * c0 ^ e2)) Y F
      (g := wgxJet 2 ν μ L T τ) zero_le_one
      (mul_nonneg hD2 (Real.rpow_nonneg (mul_nonneg hc0n hLpos.le) _))
      (wgy_k 1 D2 c0 L e2 Y 1 hD2 hc0n hLpos.le zero_le_one
        (by rw [xH2, one_mul, one_mul]; exact hY57)) hE2
  have h1_bd : lqNorm (22 / 3) (fun y => ENNReal.ofReal L⁻¹ * wgxJet 1 ν μ L T τ y) ≤
      ENNReal.ofReal ((1 * (D1 * c0 ^ e1)) * Y) * F :=
    wgy_term L⁻¹ (D1 * (c0 * L) ^ e1) (1 * (D1 * c0 ^ e1)) Y F (inv_nonneg.2 hLpos.le)
      (mul_nonneg hD1 (Real.rpow_nonneg (mul_nonneg hc0n hLpos.le) _))
      (wgy_k _ D1 c0 L e1 Y 1 hD1 hc0n hLpos.le (inv_nonneg.2 hLpos.le) (by
        rw [xH1, one_mul]; exact hY57)) hE1
  have h0_bd : lqNorm (22 / 3) (fun y => ENNReal.ofReal (L⁻¹ ^ 2) * wgxJet 0 ν μ L T τ y) ≤
      ENNReal.ofReal ((1 * (D0 * c0 ^ e0)) * Y) * F :=
    wgy_term (L⁻¹ ^ 2) (D0 * (c0 * L) ^ e0) (1 * (D0 * c0 ^ e0)) Y F (by positivity)
      (mul_nonneg hD0 (Real.rpow_nonneg (mul_nonneg hc0n hLpos.le) _))
      (wgy_k _ D0 c0 L e0 Y 1 hD0 hc0n hLpos.le (by positivity) (by
        rw [hLinv2, xH0, one_mul]; exact hY57)) hE0
  -- Measurability of summands
  have mA2 : AEMeasurable (fun y => ENNReal.ofReal (Cy1 * L ^ (-1 : ℝ)) * wgyWJet 0 ν μ L T τ y)
      volume := w0.const_mul _
  have mA3 : AEMeasurable (fun y => ENNReal.ofReal (Cy1 * L ^ (-3 : ℝ)) * wgyWPsi ν μ R T τ y)
      volume := wP.const_mul _
  have mB1 : AEMeasurable (fun y => ENNReal.ofReal L⁻¹ * wgxJet 0 ν μ L T τ y) volume :=
    m0.const_mul _
  have mB3 : AEMeasurable (fun y => ENNReal.ofReal L⁻¹ * wgxJet 2 ν μ L T τ y) volume :=
    m2.const_mul _
  have mB4 : AEMeasurable (fun y => ENNReal.ofReal (L⁻¹ ^ 2) * wgxJet 1 ν μ L T τ y) volume :=
    m1.const_mul _
  have mB5 : AEMeasurable (fun y => ENNReal.ofReal (L⁻¹ ^ 3) * wgxPsi ν μ R T τ y) volume :=
    mP.const_mul _
  have mX2 : AEMeasurable (fun y => ENNReal.ofReal (Cx * L ^ (-1 : ℝ)) * wgxJet 0 ν μ L T τ y)
      volume := m0.const_mul _
  have mX3 : AEMeasurable (fun y => ENNReal.ofReal (Cx * L ^ (-3 : ℝ)) * wgxPsi ν μ R T τ y)
      volume := mP.const_mul _
  have mH1 : AEMeasurable (fun y => ENNReal.ofReal L⁻¹ * wgxJet 1 ν μ L T τ y) volume :=
    m1.const_mul _
  have mH0 : AEMeasurable (fun y => ENNReal.ofReal (L⁻¹ ^ 2) * wgxJet 0 ν μ L T τ y) volume :=
    m0.const_mul _
  set fY : Space → ℝ≥0∞ := fun y =>
    (wgyWJet 1 ν μ L T τ y + ENNReal.ofReal (Cy1 * L ^ (-1 : ℝ)) * wgyWJet 0 ν μ L T τ y +
      ENNReal.ofReal (Cy1 * L ^ (-3 : ℝ)) * wgyWPsi ν μ R T τ y) +
    ENNReal.ofReal Cy2 *
      (ENNReal.ofReal L⁻¹ * wgxJet 0 ν μ L T τ y + wgxJet 1 ν μ L T τ y +
        ENNReal.ofReal L⁻¹ * wgxJet 2 ν μ L T τ y +
        ENNReal.ofReal (L⁻¹ ^ 2) * wgxJet 1 ν μ L T τ y +
        ENNReal.ofReal (L⁻¹ ^ 3) * wgxPsi ν μ R T τ y)
  set fX : Space → ℝ≥0∞ := fun y =>
    ENNReal.ofReal 3 *
      (wgxJet 1 ν μ L T τ y + ENNReal.ofReal (Cx * L ^ (-1 : ℝ)) * wgxJet 0 ν μ L T τ y +
        ENNReal.ofReal (Cx * L ^ (-3 : ℝ)) * wgxPsi ν μ R T τ y)
  set fH : Space → ℝ≥0∞ := fun y =>
    ENNReal.ofReal Ch *
      (wgxJet 2 ν μ L T τ y + ENNReal.ofReal L⁻¹ * wgxJet 1 ν μ L T τ y +
        ENNReal.ofReal (L⁻¹ ^ 2) * wgxJet 0 ν μ L T τ y +
        ENNReal.ofReal (L⁻¹ ^ 3) * wgxPsi ν μ R T τ y)
  have mfY : AEMeasurable fY volume :=
    ((w1.add mA2).add mA3).add
      ((((((mB1.add m1).add mB3).add mB4).add mB5)).const_mul (ENNReal.ofReal Cy2))
  have mfX : AEMeasurable fX volume :=
    ((m1.add mX2).add mX3).const_mul (ENNReal.ofReal 3)
  have mfH : AEMeasurable fH volume :=
    (((m2.add mH1).add mH0).add mB5).const_mul (ENNReal.ofReal Ch)
  have bA := wgy_lq_add (w1.add mA2) mA3 (wgy_lq_add w1 mA2 t1 t2) t3
  have bB := wgy_lq_add (((mB1.add m1).add mB3).add mB4) mB5
    (wgy_lq_add ((mB1.add m1).add mB3) mB4
      (wgy_lq_add (mB1.add m1) mB3 (wgy_lq_add mB1 m1 q1 q2) q3) q4) q5
  have bfY : lqNorm (22 / 3) fY ≤ ENNReal.ofReal (MY * Y) * F := by
    calc lqNorm (22 / 3) fY
        ≤ lqNorm (22 / 3) (fun y => wgyWJet 1 ν μ L T τ y +
              ENNReal.ofReal (Cy1 * L ^ (-1 : ℝ)) * wgyWJet 0 ν μ L T τ y +
              ENNReal.ofReal (Cy1 * L ^ (-3 : ℝ)) * wgyWPsi ν μ R T τ y) +
          lqNorm (22 / 3) (fun y => ENNReal.ofReal Cy2 *
              (ENNReal.ofReal L⁻¹ * wgxJet 0 ν μ L T τ y + wgxJet 1 ν μ L T τ y +
                ENNReal.ofReal L⁻¹ * wgxJet 2 ν μ L T τ y +
                ENNReal.ofReal (L⁻¹ ^ 2) * wgxJet 1 ν μ L T τ y +
                ENNReal.ofReal (L⁻¹ ^ 3) * wgxPsi ν μ R T τ y)) :=
          lqNorm_add_le hq ((w1.add mA2).add mA3)
            (((((mB1.add m1).add mB3).add mB4).add mB5).const_mul (ENNReal.ofReal Cy2))
      _ ≤ (ENNReal.ofReal ((1 * (CW1 * c0 ^ e1)) * Y) * F +
            ENNReal.ofReal ((Cy1 * (CW0 * c0 ^ e0)) * Y) * F +
            ENNReal.ofReal ((Cy1 * Co) * Y) * F) +
          ENNReal.ofReal Cy2 * (ENNReal.ofReal ((1 * (D0 * c0 ^ e0)) * Y) * F +
            ENNReal.ofReal ((1 * (D1 * c0 ^ e1)) * Y) * F +
            ENNReal.ofReal ((1 * (D2 * c0 ^ e2)) * Y) * F +
            ENNReal.ofReal ((1 * (D1 * c0 ^ e1)) * Y) * F +
            ENNReal.ofReal ((1 * Co) * Y) * F) := by
          refine add_le_add bA ?_
          rw [lqNorm_const_mul hq0 _ ENNReal.ofReal_ne_top]
          exact mul_le_mul_of_nonneg_left bB zero_le
      _ = ENNReal.ofReal (MY * Y) * F :=
          wgy_sum _ _ _ _ _ _ _ _ _ Y F (by positivity) (by positivity) (by positivity) hCy2
            (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) hY0
  have bX_in := wgy_lq_add (m1.add mX2) mX3 (wgy_lq_add m1 mX2 q2 gx0) gxP
  have bfX : lqNorm (22 / 3) fX ≤ ENNReal.ofReal (MX * Y) * F := by
    unfold fX
    rw [lqNorm_const_mul hq0 _ ENNReal.ofReal_ne_top]
    exact (mul_le_mul_of_nonneg_left bX_in zero_le).trans
      (rj_sum3 3 _ _ _ Y F (by norm_num) (by positivity) (by positivity) (by positivity) hY0).le
  have bH_in := wgy_lq_add ((m2.add mH1).add mH0) mB5
    (wgy_lq_add (m2.add mH1) mH0 (wgy_lq_add m2 mH1 h2_bd h1_bd) h0_bd) q5
  have bfH : lqNorm (22 / 3) fH ≤ ENNReal.ofReal (MH * Y) * F := by
    unfold fH
    rw [lqNorm_const_mul hq0 _ ENNReal.ofReal_ne_top]
    exact (mul_le_mul_of_nonneg_left bH_in zero_le).trans
      (rj_sum4 Ch _ _ _ _ Y F hCh (by positivity) (by positivity) (by positivity)
        (by positivity) hY0).le
  have mfYX : AEMeasurable (fun y => fY y + fX y) volume := mfY.add mfX
  have bfYX : lqNorm (22 / 3) (fun y => fY y + fX y) ≤
      ENNReal.ofReal (MY * Y) * F + ENNReal.ofReal (MX * Y) * F :=
    wgy_lq_add mfY mfX bfY bfX
  have bfYXH : lqNorm (22 / 3) (fun y => (fY y + fX y) + fH y) ≤
      (ENNReal.ofReal (MY * Y) * F + ENNReal.ofReal (MX * Y) * F) +
        ENNReal.ofReal (MH * Y) * F :=
    wgy_lq_add mfYX mfH bfYX bfH
  calc lqNorm (22 / 3) (fun y : Space =>
          ENNReal.ofReal
            (meanJetDens (sepWX ν μ R χy T τ) (sepWY ν μ R χy T τ) !₂[ϱ y, 0, y 2]))
      ≤ lqNorm (22 / 3) (fun y => (fY y + fX y) + fH y) := by
        refine lqNorm_mono_ae hq0 ?_
        filter_upwards [haxis] with y hy
        set y₀ : Space := !₂[ϱ y, 0, y 2]
        have hy₀ : 0 < ϱ y₀ := by rw [rj_varrho_merid]; exact hy
        obtain ⟨eqX, eqW, eqPsiX, eqPsiW⟩ := hEq ν μ R P hν hR hP0 hμ' T hT hSM hAx τ y hy
        have pY := hPtY ν μ R P hν hν1 hR1 hP0 hP1 hμ T hT hSM hAx τ y₀ hy₀
        have pX := hPtX ν μ R P hν hν1 hR1 hP0 hP1 hμ T hT hSM hAx τ y₀ hy₀
        have pH := hPtH ν μ R P hν hν1 hR1 hP0 hP1 hμ T hT hSM hAx τ y hy
        rw [eqW 1, eqW 0, eqPsiW, eqX 0, eqX 1, eqX 2, eqPsiX] at pY
        rw [eqX 1, eqX 0, eqPsiX] at pX
        rw [eqX 2, eqX 1, eqX 0, eqPsiX] at pH
        have pX' : ENNReal.ofReal (gradSize (sepWX ν μ R χy T τ) y₀) ≤ fX y :=
          (rj_gradSize_le_three_fderiv _ _).trans (mul_le_mul_of_nonneg_left pX zero_le)
        have hsum : ENNReal.ofReal (meanJetDens (sepWX ν μ R χy T τ) (sepWY ν μ R χy T τ) y₀) =
            ENNReal.ofReal ‖fderiv ℝ (sepWY ν μ R χy T τ) y₀‖ +
              ENNReal.ofReal (gradSize (sepWX ν μ R χy T τ) y₀) +
              ENNReal.ofReal (hessSize (sepWX ν μ R χy T τ) y₀) := by
          change ENNReal.ofReal (‖fderiv ℝ (sepWY ν μ R χy T τ) y₀‖ +
              gradSize (sepWX ν μ R χy T τ) y₀ + hessSize (sepWX ν μ R χy T τ) y₀) = _
          have h1 : 0 ≤ ‖fderiv ℝ (sepWY ν μ R χy T τ) y₀‖ := norm_nonneg _
          have h2 : 0 ≤ gradSize (sepWX ν μ R χy T τ) y₀ :=
            Finset.sum_nonneg fun _ _ => norm_nonneg _
          have h3 : 0 ≤ hessSize (sepWX ν μ R χy T τ) y₀ :=
            Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
          rw [ENNReal.ofReal_add (add_nonneg h1 h2) h3, ENNReal.ofReal_add h1 h2]
        rw [hsum]
        exact add_le_add (add_le_add pY pX') pH
    _ ≤ (ENNReal.ofReal (MY * Y) * F + ENNReal.ofReal (MX * Y) * F) +
          ENNReal.ofReal (MH * Y) * F := bfYXH
    _ = ENNReal.ofReal ((MY + MX + MH) * ν⁻¹ * L ^ (-(46 / 11 : ℝ))) * F :=
        rj_sum_final MY MX MH ν L Y F (by unfold MY; positivity) (by unfold MX; positivity)
          (by unfold MH; positivity) hY0 hY

/-- `RepJetAt` at one regime from the three leaves and `RepairSepBridge`. -/
theorem repJetAt_of (hB : RepairSepBridge) (hTr : RepJetChartTransfer)
    (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)
    {σ₁ σ₂ C : ℝ} (hσ : -(1 / 4 : ℝ) < σ₁) (hC : 0 ≤ C) (hχy : IsStreamCutoff K.χy)
    (hSl : ∀ (ν μ R P : ℝ), 0 < ν → ν ≤ 1 → 1 ≤ R → 0 < P → P ≤ 1 → μ ∈ Icc σ₁ σ₂ →
      ∀ T, IIIa.IsSepSource P (R * Real.sqrt (5 * ν / 6)) T → SepMoment P T → IsAxiSource T →
        ∀ τ : ℝ,
          lqNorm (22 / 3) (fun y : Space =>
              ENNReal.ofReal
                (meanJetDens (sepWX ν μ R K.χy T τ) (sepWY ν μ R K.χy T τ) !₂[ϱ y, 0, y 2])) ≤
            ENNReal.ofReal (C * ν⁻¹ * (R * Real.sqrt ν) ^ (-(46 / 11 : ℝ))) *
              IIIa.ltauLq P (22 / 19) (IIIa.srcNorm T))
    (hμ : μ ∈ Icc σ₁ σ₂) (hν1 : L.ν ≤ 1) (hε1 : L.ε ≤ 1) (hP : 2 * L.ε * cOf L.ν ≤ 1)
    (hC0 : 0 < K.C0) (hmZ : 0 ≤ K.mZ) :
    RepJetAt Pl K L μ C 4 := by
  intro w
  have hν := L.ν_pos
  have hε := L.ε_pos
  have hc := cOf_pos hν
  have hμ' : -(1 / 4 : ℝ) < μ := lt_of_lt_of_le hσ hμ.1
  have hρ : 0 < L.ρb Pl K := by
    unfold ReturnLevel.ρb UnforcedLeray.Short.IIb.rhoB
    have h1 := (L.params Pl).ν_pos
    have h2 := (L.params Pl).ε_pos
    positivity
  obtain ⟨T, hS, hM, hA, hW, hN⟩ := hB (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν L.ε K.χo K.hχo
    hc hρ hmZ hν hε (multOp Pl K L w)
  have hX0 : wardX0 L.ν μ L.ε⁻¹ (cOf L.ν) (repSrcTen Pl K L w) = sepX0 L.ν μ T := by
    rw [wardX0_eq_sepX0]; exact sepX0_congr hW
  have hX : repX Pl K L μ w = sepWX L.ν μ L.ε⁻¹ K.χy T := by
    show wardStreamCut L.ν L.ε⁻¹ K.χy (wardX0 L.ν μ L.ε⁻¹ (cOf L.ν) (repSrcTen Pl K L w)) = _
    rw [hX0]; rfl
  have hY : repY Pl K L μ w = sepWY L.ν μ L.ε⁻¹ K.χy T := by
    show physDmu L.ν (μ + 1) (repX Pl K L μ w) = _
    rw [hX]; rfl
  obtain ⟨hm, htr⟩ := hTr Pl K L μ hχy hμ' hC0 hmZ w
  refine ⟨hm, ?_⟩
  have hR1 : 1 ≤ L.ε⁻¹ := (one_le_inv₀ hε).2 hε1
  have hP0 : 0 < 2 * L.ε * cOf L.ν := by positivity
  refine (htr (ENNReal.ofReal (C * L.ν⁻¹ * (L.ε⁻¹ * Real.sqrt L.ν) ^ (-(46 / 11 : ℝ))) *
      IIIa.ltauLq (2 * L.ε * cOf L.ν) (22 / 19) (IIIa.srcNorm T)) (fun τ => ?_)).trans ?_
  · rw [hX, hY]
    exact hSl L.ν μ L.ε⁻¹ _ hν hν1 hR1 hP0 hP hμ T hS hM hA τ
  · have hscale : C * L.ν⁻¹ * (L.ε⁻¹ * Real.sqrt L.ν) ^ (-(46 / 11 : ℝ)) ≤
        C * L.ν⁻¹ ^ 4 * L.ε ^ (46 / 11 : ℝ) := by
      have h := pg_scale_le hν hν1 hε
      calc C * L.ν⁻¹ * (L.ε⁻¹ * Real.sqrt L.ν) ^ (-(46 / 11 : ℝ))
          ≤ C * L.ν⁻¹ * (L.ν⁻¹ ^ 3 * L.ε ^ (46 / 11 : ℝ)) :=
            mul_le_mul_of_nonneg_left h (by positivity)
        _ = C * L.ν⁻¹ ^ 4 * L.ε ^ (46 / 11 : ℝ) := by ring
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal hscale) hN

/-- **`RepJet` along the concrete sequence from the three leaves** (source 5212-5223, 5259-5268). -/
theorem repJet_of (hTr : RepJetChartTransfer) (hPtH : SepWXHessMeridPointwise)
    (hEq : SepJetMeridEq) (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp)
    (_hPG : D.PhaseGradient) : RepJet D := by
  have hσ : -(1 / 4 : ℝ) < D.σ₀ / 2 := by linarith [hst.sigma_pos]
  obtain ⟨C, hC, hSl⟩ := sepJetMeridSlice_of hPtH hEq (D.σ₀ / 2) ((D.σ₀ + 1 / 4) / 2) hσ
    D.K.χy hst.chiY
  refine ⟨C, 4, ?_⟩
  have hev1 := mu_eventually_mem D hst.omega_ne hst.sigma_pos hst.sigma_lt
  have hev2 := retNu_retEps_eventually_le_one hst.omega_ne hst.gamma_pos D.coeff_ne
  have hev3 : ∀ᶠ n : ℕ in atTop, retNu D.Pl D.σ₀ n ≤ dm ^ 3 / 12 :=
    (retNu_tendsto D.σ₀ hst.omega_ne).eventually_le_const (by have := hst.dm_pos; positivity)
  filter_upwards [hev1, hev2, hev3, hst.actual] with n h1 h2 h3 h4 z hz
  have hP : 2 * (D.level n).ε * cOf (D.level n).ν ≤ 1 :=
    UnforcedLeray.Short.IIIa.period_le_one_of_small h4.regime h3
  exact repJetAt_of repairSepBridge hTr D.Pl D.K (D.level n) (D.mu n z) hσ hC hst.chiY
    hSl (h1 z hz) h2.1 h2.2 hP hst.C0_pos (by linarith [hst.mZ_gt])

end UnforcedLeray.Short.PartIIIb.Concrete

end
