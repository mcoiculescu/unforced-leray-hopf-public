import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.Org.YThinTrans.Annulus.Defs
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.Org.YThinTrans.Annulus.ThinGlobal
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.Org.YThinTrans.Annulus.Compact
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.Sub.T8_1

/-!
# `PartIII-b:C/rep/4/2/org/3/3`: `AnnulusFields` from the leaves

Source `the November 2 reference manuscript` 3669-3674 (`sep:thin-global` with
`c₀ = 1 - √(5/6)`, `R = ε⁻¹ ≥ 1`, receiver `r_i = R√ν`), 3730 and 5571-5576 (the physical mass
of the old thin source is `πR²N₀`), 4163-4168 (source disk `r ≤ R√(ν/1.2) ≤ R√(5ν/6)`,
receiver `r ≥ R√ν`), 5342-5355, 5928-5950.

`annulusFields_of`: for large `n` the window lies in a fixed compact `K ⊂ {Re μ > -1/4}`,
`ν ≤ 1`, `R ≥ 1` (`annulus_window`); one constant serves the six pairs `j ≤ 2`, `q ∈ {2, 22/3}`
(`thinGlobal_uniform`, from `annulus_sepThinGlobal`); the physical mass of
`oldPhys R c (g₁ + g₂)` is at most `R²·πN₀` (`physMass_le`, from `TwoPeriodLtau`,
`ChartMassLe`, `OldThinPhysAE`); a source radius `r_o < 0` is replaced by `max r_o 0`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi Topology
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace AnnulusRed

theorem rhoB_pos' (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (hC0 : 0 < K.C0) :
    0 < L.ρb Pl K := by
  unfold ReturnLevel.ρb UnforcedLeray.Short.IIb.rhoB
  have h1 : 0 < ((L.params Pl).ν ^ K.k0)⁻¹ := inv_pos.2 (pow_pos (L.params Pl).ν_pos _)
  have h2 : 0 < (L.params Pl).ε ^ (3 / 11 : ℝ) := Real.rpow_pos_of_pos (L.params Pl).ε_pos _
  have h3 := Real.exp_pos (K.m0 / (L.params Pl).ν)
  positivity

theorem floor_shift (X c : ℝ) (hc : 0 < c) :
    X + c - c * ⌊(X + c) / c + 1 / 2⌋ = X - c * ⌊X / c + 1 / 2⌋ := by
  have hc' : c ≠ 0 := hc.ne'
  rw [show (X + c) / c + 1 / 2 = X / c + 1 / 2 + 1 by field_simp; ring, Int.floor_add_one]
  push_cast
  ring

theorem cartLift_period (R c : ℝ) (hR : 0 < R) (hc : 0 < c) (f : Chart → Ten3) (τ : ℝ)
    (z : Space) :
    NearInst.cartLift R c f (τ + 2 * c / R) z = NearInst.cartLift R c f τ z := by
  have hR' : R ≠ 0 := hR.ne'
  have hX : R * Real.log (NearInst.hRad z / R) + R * (τ + 2 * c / R) / 2 =
      (R * Real.log (NearInst.hRad z / R) + R * τ / 2) + c := by
    field_simp
    ring
  have hch : NearInst.chartOf R c z (τ + 2 * c / R) = NearInst.chartOf R c z τ := by
    unfold NearInst.chartOf
    rw [hX, floor_shift _ c hc]
  unfold NearInst.cartLift
  rw [hch]

theorem srcNorm_meas {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ}
    (hT : ∀ i j, Measurable fun p : ℝ × Space => T p.1 p.2 i j) (z : Space) :
    Measurable fun τ => UnforcedLeray.Short.IIIa.srcNorm T τ z := by
  have h : ∀ i j, Measurable fun τ : ℝ => T τ z i j := fun i j =>
    (hT i j).comp (measurable_id.prodMk measurable_const)
  unfold UnforcedLeray.Short.IIIa.srcNorm UnforcedLeray.Short.IIIa.tensorNorm
  refine ENNReal.measurable_ofReal.comp (Measurable.sqrt ?_)
  exact Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => (h i j).pow_const 2

/-- **The physical mass of the old source is at most `πR²N₀`** (source 3730, 5571-5576):
for representatives `g₁, g₂` of `χ_o(T₁, 0)` whose lift is a `P`-periodic separated source. -/
theorem physMass_le (h1 : TwoPeriodLtau) (h2 : ChartMassLe) (h3 : OldThinPhysAE)
    {Pl : PlanarData} {K : ReturnConsts} {L : ReturnLevel} (hρ : 0 < L.ρb Pl K)
    (T : LStr Pl K L) (g₁ g₂ : Chart → Ten3) (hg : IsRep Pl K L (oldThin Pl K L T) g₁ g₂)
    {P rOut : ℝ} (hP : 0 < P)
    (hsrc : UnforcedLeray.Short.IIIa.IsSepSource P rOut (oldPhys L.ε⁻¹ (cOf L.ν) (g₁ + g₂))) :
    ∫⁻ z : Space, UnforcedLeray.Short.IIIa.ltauAt P
        (fun τ => UnforcedLeray.Short.IIIa.srcNorm (oldPhys L.ε⁻¹ (cOf L.ν) (g₁ + g₂)) τ z) ≤
      ENNReal.ofReal (Real.pi * L.ε⁻¹ ^ 2) * oldMass Pl K L T := by
  have hR : 0 < L.ε⁻¹ := inv_pos.2 L.ε_pos
  have hc : 0 < cOf L.ν := cOf_pos L.ν_pos
  have hF := measurable_oldThinTen Pl K L T
  have hk : ∀ z : Space, Measurable fun τ => UnforcedLeray.Short.IIIa.srcNorm
      (NearInst.cartLift L.ε⁻¹ (cOf L.ν) (oldThinTen Pl K L T)) τ z := fun z =>
    srcNorm_meas (fun i j => T8_1.measurable_cartLift_entry _ _ _ hF i j) z
  calc ∫⁻ z : Space, UnforcedLeray.Short.IIIa.ltauAt P
        (fun τ => UnforcedLeray.Short.IIIa.srcNorm (oldPhys L.ε⁻¹ (cOf L.ν) (g₁ + g₂)) τ z)
      = ∫⁻ z : Space, UnforcedLeray.Short.IIIa.ltauAt (2 * cOf L.ν / L.ε⁻¹)
        (fun τ => UnforcedLeray.Short.IIIa.srcNorm
          (NearInst.cartLift L.ε⁻¹ (cOf L.ν) (oldThinTen Pl K L T)) τ z) := by
        refine lintegral_congr_ae ?_
        filter_upwards [h3 Pl K L hρ T g₁ g₂ hg] with z hz
        refine h1 P _ hP (by positivity) _ _ (srcNorm_meas hsrc.measurable z) (hk z)
          (fun τ => ?_) (fun τ => ?_) hz
        · simp only [UnforcedLeray.Short.IIIa.srcNorm]
          rw [hsrc.periodic]
        · simp only [UnforcedLeray.Short.IIIa.srcNorm]
          rw [cartLift_period _ _ hR hc]
    _ ≤ ENNReal.ofReal (Real.pi * L.ε⁻¹ ^ 2) *
          oldMassAt (cOf L.ν) 0 (fun p => Ten3.toMatrix (oldThinTen Pl K L T p)) :=
        h2 _ _ hR hc _ hF
    _ = ENNReal.ofReal (Real.pi * L.ε⁻¹ ^ 2) * oldMass Pl K L T := by rw [oldMass_eq]

theorem c0_pos : 0 < 1 - Real.sqrt (5 / 6) := by
  have : Real.sqrt (5 / 6) < 1 := by
    rw [Real.sqrt_lt' one_pos]
    norm_num
  linarith

/-- Raising the constant and the `ν⁻¹`-power keeps the bound (`ν ≤ 1`, `R ≥ 1`... only
`R > 0` is used). -/
theorem coef_mono {Ci C : ℝ} {ki k : ℕ} (hCi : 0 ≤ Ci) (hC : Ci ≤ C) (hk : ki ≤ k) {ν : ℝ}
    (hν : 0 < ν) (hν1 : ν ≤ 1) {R N₀ e : ℝ} (hR : 1 ≤ R) (hN : 0 ≤ N₀) :
    ENNReal.ofReal (Ci * ν⁻¹ ^ ki * R ^ e * N₀) ≤ ENNReal.ofReal (C * ν⁻¹ ^ k * R ^ e * N₀) := by
  apply ENNReal.ofReal_le_ofReal
  have h1 : 1 ≤ ν⁻¹ := (one_le_inv₀ hν).2 hν1
  have h2 : ν⁻¹ ^ ki ≤ ν⁻¹ ^ k := pow_le_pow_right₀ h1 hk
  have h3 : 0 ≤ R ^ e * N₀ := mul_nonneg (Real.rpow_nonneg (by linarith) _) hN
  have h4 : 0 ≤ ν⁻¹ ^ ki := by positivity
  calc Ci * ν⁻¹ ^ ki * R ^ e * N₀ = Ci * ν⁻¹ ^ ki * (R ^ e * N₀) := by ring
    _ ≤ C * ν⁻¹ ^ k * (R ^ e * N₀) :=
        mul_le_mul_of_nonneg_right (mul_le_mul hC h2 h4 (by linarith)) h3
    _ = C * ν⁻¹ ^ k * R ^ e * N₀ := by ring

/-- **One constant for the six table exponents** (source 3669-3674, 5329-5331): `sep:thin-global`
at `j ≤ 2`, `q ∈ {2, 22/3}`, `c₀ = 1 - √(5/6)`, with a common `C > 0` and `k`. -/
theorem thinGlobal_uniform (Kc : Set ℂ) (hKc : IsCompact Kc) (hKre : ∀ μ ∈ Kc, -(1 / 4) < μ.re) :
    ∃ (C : ℝ) (k : ℕ), 0 < C ∧ ∀ j : ℕ, j ≤ 2 → ∀ q : ℝ, (q = 2 ∨ q = 22 / 3) →
      ∀ ν : ℝ, 0 < ν → ν ≤ 1 → ∀ μ ∈ Kc, ∀ R N₀ rOut rIn P : ℝ, 1 ≤ R → 0 ≤ N₀ → 0 ≤ rOut →
        rOut < rIn → 0 < P → (1 - Real.sqrt (5 / 6)) * R * Real.sqrt ν ≤ rIn - rOut →
        ∀ T, UnforcedLeray.Short.IIIa.IsSepSource P rOut T →
          ∫⁻ z : Space, UnforcedLeray.Short.IIIa.ltauAt P
              (fun τ => UnforcedLeray.Short.IIIa.srcNorm T τ z) ≤ ENNReal.ofReal (R ^ 2 * N₀) →
          UnforcedLeray.Short.IIIa.ltauLq P q (UnforcedLeray.Short.IIIa.youngDerivNorm ν μ T j rIn) ≤
            ENNReal.ofReal (C * (ν⁻¹) ^ k * R ^ (-2 - (j : ℝ) + 3 / q) * N₀) := by
  have G := annulus_sepThinGlobal Kc hKc hKre
  have hc0 := c0_pos
  obtain ⟨C0, k0, hC0, H0⟩ := G 0 2 _ (by norm_num) hc0
  obtain ⟨C1, k1, hC1, H1⟩ := G 1 2 _ (by norm_num) hc0
  obtain ⟨C2, k2, hC2, H2⟩ := G 2 2 _ (by norm_num) hc0
  obtain ⟨C3, k3, hC3, H3⟩ := G 0 (22 / 3) _ (by norm_num) hc0
  obtain ⟨C4, k4, hC4, H4⟩ := G 1 (22 / 3) _ (by norm_num) hc0
  obtain ⟨C5, k5, hC5, H5⟩ := G 2 (22 / 3) _ (by norm_num) hc0
  refine ⟨C0 + C1 + C2 + C3 + C4 + C5 + 1, k0 + k1 + k2 + k3 + k4 + k5, by positivity, ?_⟩
  intro j hj q hq ν hν hν1 μ hμ R N₀ rOut rIn P hR hN hrO hrr hP hgap T hT hmass
  interval_cases j <;> rcases hq with rfl | rfl
  · exact (H0 ν hν hν1 μ hμ R N₀ rOut rIn P hR hN hrO hrr hP hgap T hT hmass).trans
      (coef_mono hC0 (by linarith) (by omega) hν hν1 hR hN)
  · exact (H3 ν hν hν1 μ hμ R N₀ rOut rIn P hR hN hrO hrr hP hgap T hT hmass).trans
      (coef_mono hC3 (by linarith) (by omega) hν hν1 hR hN)
  · exact (H1 ν hν hν1 μ hμ R N₀ rOut rIn P hR hN hrO hrr hP hgap T hT hmass).trans
      (coef_mono hC1 (by linarith) (by omega) hν hν1 hR hN)
  · exact (H4 ν hν hν1 μ hμ R N₀ rOut rIn P hR hN hrO hrr hP hgap T hT hmass).trans
      (coef_mono hC4 (by linarith) (by omega) hν hν1 hR hN)
  · exact (H2 ν hν hν1 μ hμ R N₀ rOut rIn P hR hN hrO hrr hP hgap T hT hmass).trans
      (coef_mono hC2 (by linarith) (by omega) hν hν1 hR hN)
  · exact (H5 ν hν hν1 μ hμ R N₀ rOut rIn P hR hN hrO hrr hP hgap T hT hmass).trans
      (coef_mono hC5 (by linarith) (by omega) hν hν1 hR hN)

end AnnulusRed

open AnnulusRed in
/-- **`AnnulusFields` from the leaves** (source 3669-3674, 3730, 4163-4168, 5342-5355,
5571-5576, 5928-5950). -/
theorem annulusFields_of (h1 : TwoPeriodLtau) (h2 : ChartMassLe) (h3 : OldThinPhysAE)
    (dm dp : ℝ) : AnnulusFields dm dp := by
  intro D hst
  obtain ⟨Kc, hKc, hKre, hev⟩ := annulus_window D hst
  obtain ⟨C, k, hC, H⟩ := thinGlobal_uniform Kc hKc hKre
  refine ⟨Real.pi * C, k, ?_⟩
  filter_upwards [hev] with n hn z hz T g₁ g₂ hg
  obtain ⟨hν1, hε1, hμ⟩ := hn
  intro P rOut hP hrOut hsrc j hj q hq
  have hν := (D.level n).ν_pos
  have hε := (D.level n).ε_pos
  have hR1 : 1 ≤ (D.level n).ε⁻¹ := (one_le_inv₀ hε).2 hε1
  have hρ : 0 < (D.level n).ρb D.Pl D.K := rhoB_pos' D.Pl D.K (D.level n) hst.C0_pos
  have hmass := physMass_le h1 h2 h3 hρ T g₁ g₂ hg hP hsrc
  have hcoef : 0 < Real.pi * C * (D.level n).ν⁻¹ ^ k *
      (D.level n).ε⁻¹ ^ (-2 - (j : ℝ) + 3 / q) := by
    have := Real.pi_pos
    have : 0 < (D.level n).ε⁻¹ ^ (-2 - (j : ℝ) + 3 / q) := Real.rpow_pos_of_pos (by positivity) _
    positivity
  by_cases htop : oldMass D.Pl D.K (D.level n) T = ⊤
  · rw [htop, ENNReal.mul_top (ENNReal.ofReal_pos.2 hcoef).ne']
    exact le_top
  set m := (oldMass D.Pl D.K (D.level n) T).toReal with hm
  have hm0 : 0 ≤ m := ENNReal.toReal_nonneg
  set R := (D.level n).ε⁻¹ with hRdef
  set ν := (D.level n).ν with hνdef
  have hsq : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν
  have hs56 : Real.sqrt (5 / 6) < 1 := by
    rw [Real.sqrt_lt' one_pos]
    norm_num
  have hs56' : 0 ≤ Real.sqrt (5 / 6) := Real.sqrt_nonneg _
  have hRpos : 0 < R := by linarith
  have hRs : 0 < R * Real.sqrt ν := mul_pos hRpos hsq
  set rO := max rOut 0 with hrO
  have hrO_le : rO ≤ R * Real.sqrt ν * Real.sqrt (5 / 6) :=
    max_le hrOut (by positivity)
  have hsrc' : UnforcedLeray.Short.IIIa.IsSepSource P rO (oldPhys R (cOf ν) (g₁ + g₂)) :=
    ⟨hsrc.measurable, hsrc.periodic,
      fun τ z' h => hsrc.support τ z' (lt_of_le_of_lt (le_max_left _ _) h)⟩
  have hlt : rO < R * Real.sqrt ν := by
    have : R * Real.sqrt ν * Real.sqrt (5 / 6) < R * Real.sqrt ν * 1 :=
      mul_lt_mul_of_pos_left hs56 hRs
    linarith
  have hgap : (1 - Real.sqrt (5 / 6)) * R * Real.sqrt ν ≤ R * Real.sqrt ν - rO := by
    nlinarith
  have hM : ∫⁻ z' : Space, UnforcedLeray.Short.IIIa.ltauAt P
      (fun τ => UnforcedLeray.Short.IIIa.srcNorm (oldPhys R (cOf ν) (g₁ + g₂)) τ z') ≤
      ENNReal.ofReal (R ^ 2 * (Real.pi * m)) := by
    refine hmass.trans (le_of_eq ?_)
    rw [← ENNReal.ofReal_toReal htop, ← hm,
      ← ENNReal.ofReal_mul (by have := Real.pi_pos; positivity)]
    congr 1
    ring
  have hb := H j hj q hq ν hν hν1 _ (hμ z hz) R (Real.pi * m) rO (R * Real.sqrt ν) P hR1
    (by have := Real.pi_pos; positivity) (le_max_right _ _) hlt hP hgap _ hsrc' hM
  refine hb.trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_toReal htop, ← hm, ← ENNReal.ofReal_mul hcoef.le]
  congr 1
  ring

end UnforcedLeray.Short.PartIIIb.Concrete
