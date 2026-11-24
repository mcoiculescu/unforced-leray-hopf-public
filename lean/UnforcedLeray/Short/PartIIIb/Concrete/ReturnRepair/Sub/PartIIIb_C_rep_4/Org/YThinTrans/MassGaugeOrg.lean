import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.Org.YThinTrans.TableOrg
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.Org.YThinTrans.Margin
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.ThinMoment

/-!
# `PartIII-b:C/rep/4/2/org/3/2`: the old mass in gain form (`OldMassGauge`)

Source `the November 2 reference manuscript` 5527 (`N ≤ P_ν|N_ν|‖g⁻¹T‖_Z`),
5573-5576 (the mass `N_0`), 5118 (`N_ν = e^{λ/ν}ν^{-κ}`), 5162-5167 (thin moment).

The proof is the chain
`N_0 ≤ N₁ ≤ P_ν e^{γ/ν}‖T‖ = P_ν |N_ν| ν^{Re κ}‖T‖ ≤ P_ν |N_ν|‖T‖`:

* `oldMassAt_le_firstMoment`: the mass `N_0(a)` is the first moment `𝒩₁(1_{s>a}·)` without the
  weight `1 + |η|/√s ≥ 1`, so `oldMass ≤ oldN1` (same old source `χ_o(T₁,0)`, same cell);
* `thinMoment` (`ThinMoment.lean`, accepted `PartIII-b:C/rep/10`): `N₁ ≤ C ν^{-k}e^{γ/ν}‖T‖`;
* `am_gaugeN` (`Margin.lean`): `|N_ν| = e^{γ/ν}ν^{-Re κ}`, hence `e^{γ/ν} = |N_ν|ν^{Re κ}` and
  `ν^{Re κ} ≤ ν^{-⌈-Re κ⌉₊}` for `ν ≤ 1` (eventually along the sequence, `retNu → 0`).

`oldMassGauge_proof : OldMassGauge dm dp` (no hypotheses beyond the arguments).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi Topology
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete.MassGaugeOrg

open UnforcedLeray.Blueprint.Planar (PlanarData)
open UnforcedLeray.Short.PartIIIb.Concrete

/-- `N_0(a) ≤ 𝒩₁(1_{s>a}T)`: the weight `1 + |η|/√s` of the first moment is at least `1`
(source 5573-5576 against SP 2747-2752). -/
theorem oldMassAt_le_firstMoment (c a : ℝ) (T : Chart → Matrix (Fin 3) (Fin 3) ℝ) :
    oldMassAt c a T ≤ UnforcedLeray.Short.IIIa.firstMoment c a T := by
  unfold oldMassAt UnforcedLeray.Short.IIIa.firstMoment
  refine setLIntegral_mono' measurableSet_Ioi fun s _ => ?_
  refine mul_le_mul_of_nonneg_left (lintegral_mono fun η => ?_) bot_le
  refine le_mul_of_one_le_left' (ENNReal.one_le_ofReal.2 ?_)
  have : 0 ≤ |η| / Real.sqrt s := div_nonneg (abs_nonneg η) (Real.sqrt_nonneg s)
  linarith

/-- `oldMass ≤ oldN1`: the mass of the old thin source `χ_o(T₁, 0)` is at most its first
moment `N = N₁(χ_oT₁)` (source 5400, 5573-5576). -/
theorem oldMass_le_oldN1 (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel)
    (T : LStr Pl K L) : oldMass Pl K L T ≤ oldN1 Pl K L T :=
  oldMassAt_le_firstMoment _ _ _

/-- `e^{γ/ν} ≤ ν^{-j}|N_ν|` for `0 < ν ≤ 1` and `j ≥ -Re κ` (source 5118, `am_gaugeN`). -/
theorem exp_le_gaugeN (Pl : PlanarData) (L : ReturnLevel) (hν1 : L.ν ≤ 1) :
    Real.exp (gRate Pl / L.ν) ≤ L.ν⁻¹ ^ ⌈-Pl.kappa.re⌉₊ * gaugeN Pl L := by
  have hν := L.ν_pos
  have hg : Real.exp (gRate Pl / L.ν) = gaugeN Pl L * L.ν ^ Pl.kappa.re := by
    rw [am_gaugeN, mul_assoc, ← Real.rpow_add hν, neg_add_cancel, Real.rpow_zero, mul_one]
  have hpow : L.ν ^ Pl.kappa.re ≤ L.ν⁻¹ ^ ⌈-Pl.kappa.re⌉₊ := by
    calc L.ν ^ Pl.kappa.re ≤ L.ν ^ (-(⌈-Pl.kappa.re⌉₊ : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_ge hν hν1 (by linarith [Nat.le_ceil (-Pl.kappa.re)])
      _ = L.ν⁻¹ ^ ⌈-Pl.kappa.re⌉₊ := by
          rw [Real.rpow_neg hν.le, Real.rpow_natCast, inv_pow]
  rw [hg, mul_comm (L.ν⁻¹ ^ _)]
  exact mul_le_mul_of_nonneg_left hpow (norm_nonneg _)

/-- One level: `ThinMomentAt C k` and `ν ≤ 1` give `MassGaugeAt (max C 0) (k + ⌈-Re κ⌉₊)`. -/
theorem massGaugeAt_of_thinMomentAt (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel)
    (hν1 : L.ν ≤ 1) {C : ℝ} {k : ℕ} (h : ThinMomentAt Pl K L C k) :
    MassGaugeAt Pl K L (max C 0) (k + ⌈-Pl.kappa.re⌉₊) := by
  intro T
  have hν := L.ν_pos
  refine (oldMass_le_oldN1 Pl K L T).trans ((h T).trans (ENNReal.ofReal_le_ofReal ?_))
  have hT : 0 ≤ ‖T‖ := norm_nonneg _
  have hp : 0 ≤ L.ν⁻¹ ^ k := pow_nonneg (inv_nonneg.2 hν.le) k
  have hE := exp_le_gaugeN Pl L hν1
  calc C * L.ν⁻¹ ^ k * Real.exp (gRate Pl / L.ν) * ‖T‖
      ≤ max C 0 * L.ν⁻¹ ^ k * Real.exp (gRate Pl / L.ν) * ‖T‖ := by
        gcongr
        exact le_max_left _ _
    _ ≤ max C 0 * L.ν⁻¹ ^ k * (L.ν⁻¹ ^ ⌈-Pl.kappa.re⌉₊ * gaugeN Pl L) * ‖T‖ := by
        gcongr
    _ = max C 0 * L.ν⁻¹ ^ (k + ⌈-Pl.kappa.re⌉₊) * gaugeN Pl L * ‖T‖ := by
        rw [pow_add]; ring

/-- **`OldMassGauge`** (source 5527: `N ≤ P_ν|N_ν|‖g⁻¹T‖_Z`, here for the mass `N_0 ≤ N`). -/
theorem oldMassGauge_proof (dm dp : ℝ) : OldMassGauge dm dp := by
  intro D hst
  obtain ⟨C, k, hC⟩ := thinMoment D hst
  refine ⟨max C 0, k + ⌈-D.Pl.kappa.re⌉₊, le_max_right _ _, ?_⟩
  have hν : ∀ᶠ n : ℕ in atTop, retNu D.Pl D.σ₀ n ≤ 1 :=
    ((retNu_tendsto D.σ₀ hst.omega_ne).eventually_lt_const (by norm_num : (0 : ℝ) < 1)).mono
      fun n h => h.le
  filter_upwards [hC, hν] with n hn hn1
  exact massGaugeAt_of_thinMomentAt D.Pl D.K (D.level n) hn1 hn

end UnforcedLeray.Short.PartIIIb.Concrete.MassGaugeOrg
