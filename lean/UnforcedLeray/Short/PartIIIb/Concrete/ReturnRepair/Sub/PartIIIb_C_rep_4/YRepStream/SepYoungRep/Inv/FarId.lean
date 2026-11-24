import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.SepYoungRep.Inv.FarOf
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_1.L1
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_1.L2
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Agree
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Inverses.Level
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# `SepFarId` (PartIII-b:C/rep/4/4/1/org/1/1/inv/far/2, source 3611-3621, 3905-3912, 4163-4174)

Pointwise identity `farOut (strSum F) = -coefOf (wardW (g₁ + g₂))` at a.e. young chart point with
`ν s ≤ 1`. Steps: (1) `cartLift (strSum F) = cartLift (g₁ + g₂)` a.e. in `(τ, z)`
(`strSum_lift_ae`, the copy of `stressSum_ae_of_isRep` for an arbitrary `F`); (2) the masked
source equals `T` a.e. (`mask_eq_ae`: the mask is inactive on the old disk, `T` vanishes outside
it, and the axis `z₀ = z₁ = 0` is null); (3) `sepWCongrAE`; (4) `wardW = sepWre T` from `SepRepOf`.
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open scoped ENNReal Topology
open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Step (1): the lift of the measurable representative `strSum F` agrees with the lift of
`g₁ + g₂` a.e. in `(τ, z)`. -/
theorem strSum_lift_ae (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel)
    (hC0 : 0 < K.C0) (F : LStr Pl K L) (g₁ g₂ : Chart → Ten3)
    (hg : IsRep Pl K L F g₁ g₂) :
    ∀ᵐ x : ℝ × Space ∂volume,
      NearInst.cartLift L.ε⁻¹ (cOf L.ν) (strSum F) x.1 x.2
        = NearInst.cartLift L.ε⁻¹ (cOf L.ν) (g₁ + g₂) x.1 x.2 := by
  have hc : 0 < cOf L.ν := cOf_pos L.ν_pos
  have hR : 0 < L.ε⁻¹ := inv_pos.2 L.ε_pos
  have hρ : 0 < L.ρb Pl K := inv_rhoB_pos hC0
  have h1 : (F.fst : Chart → Ten3) =ᵐ[ageμ (cOf L.ν) (-1 / 2)] g₁ := by
    have h := hg.1
    rw [NearInst.ae_gainZ1Measure, NearInst.ae_z1Measure] at h
    exact h
  have h2 : (F.snd : Chart → Ten3) =ᵐ[ageμ (cOf L.ν) (-1 / 2)] g₂ := by
    have h := hg.2
    rw [NearInst.ae_gainHTMeasure, NearInst.ae_htRhoMeasure hρ] at h
    exact h
  have hN0 : ageμ (cOf L.ν) (-1 / 2)
      {p : Chart | strSum F p ≠ (g₁ + g₂) p} = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [h1, h2] with p e1 e2
    simp only [not_not, strSum, Pi.add_apply]
    rw [e1, e2]
  have hpt := chartOfNullPullback L.ε⁻¹ (cOf L.ν) hR hc _ hN0
  filter_upwards [hpt] with x hx
  have heq : strSum F (NearInst.chartOf L.ε⁻¹ (cOf L.ν) x.2 x.1)
      = (g₁ + g₂) (NearInst.chartOf L.ε⁻¹ (cOf L.ν) x.2 x.1) := by
    by_contra hne
    exact hx hne
  simp only [NearInst.cartLift, heq]

/-- The axis `z₀² + z₁² = 0` is null in `ℝ × Space`. -/
theorem axis_ae_ne : ∀ᵐ x : ℝ × Space ∂(volume : Measure (ℝ × Space)),
    x.2 0 ^ 2 + x.2 1 ^ 2 ≠ 0 := by
  let f : Space →ₗ[ℝ] ℝ := (EuclideanSpace.proj (0 : Fin 3) : Space →L[ℝ] ℝ).toLinearMap
  let K : Submodule ℝ Space := LinearMap.ker f
  have hK : K ≠ ⊤ := by
    intro h
    have hmem : (EuclideanSpace.single (0 : Fin 3) (1 : ℝ) : Space) ∈ K := by
      rw [h]; trivial
    simp [K, f, LinearMap.mem_ker] at hmem
  have hA : (volume : Measure Space) {z : Space | z 0 ^ 2 + z 1 ^ 2 = 0} = 0 := by
    apply measure_mono_null _ (Measure.addHaar_submodule (volume : Measure Space) K hK)
    intro z hz
    have hz' : z 0 ^ 2 + z 1 ^ 2 = 0 := hz
    have h0 : z 0 = 0 := by
      have : z 0 ^ 2 = 0 := by nlinarith [sq_nonneg (z 0), sq_nonneg (z 1)]
      exact pow_eq_zero_iff (two_ne_zero) |>.1 this
    simp [K, f, LinearMap.mem_ker, h0]
  have hP : (volume : Measure (ℝ × Space)) (univ ×ˢ {z : Space | z 0 ^ 2 + z 1 ^ 2 = 0}) = 0 := by
    rw [Measure.volume_eq_prod, Measure.prod_prod]
    simp [hA]
  have hn := MeasureTheory.measure_eq_zero_iff_ae_notMem.1 hP
  filter_upwards [hn] with x hx
  intro h
  exact hx ⟨trivial, h⟩

/-- Step (2): the masked source equals `T` a.e. in `(τ, z)`, for every `s` with `ν s ≤ 1`. -/
theorem mask_eq_ae (R ν δ s rOut : ℝ) (hν : 0 < ν) (hδ : Real.exp δ < 6 / 5)
    (hs : ν * s ≤ 1) (hr0 : 0 ≤ rOut) (hr2 : rOut ^ 2 = R ^ 2 * (5 * ν / 6))
    (hR : 0 < R)
    (T G : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ)
    (hsupp : ∀ τ z, rOut < Real.sqrt (z 0 ^ 2 + z 1 ^ 2) → T τ z = 0)
    (hG : ∀ᵐ x : ℝ × Space ∂volume, G x.1 x.2 = T x.1 x.2) :
    ∀ᵐ x : ℝ × Space ∂volume,
      (if Real.exp δ * s < R ^ 2 / (x.2 0 ^ 2 + x.2 1 ^ 2) then G x.1 x.2 else 0)
        = T x.1 x.2 := by
  filter_upwards [hG, axis_ae_ne] with x hp hax
  by_cases hm : Real.exp δ * s < R ^ 2 / (x.2 0 ^ 2 + x.2 1 ^ 2)
  · rw [if_pos hm]; exact hp
  · rw [if_neg hm]
    symm
    apply hsupp
    by_contra hle
    push_neg at hle
    have hq0 : 0 < x.2 0 ^ 2 + x.2 1 ^ 2 :=
      lt_of_le_of_ne (by positivity) (Ne.symm hax)
    have hqle : x.2 0 ^ 2 + x.2 1 ^ 2 ≤ rOut ^ 2 := by
      have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ x.2 0 ^ 2 + x.2 1 ^ 2 by positivity)
      have := pow_le_pow_left₀ (Real.sqrt_nonneg _) hle 2
      rw [hsq] at this
      exact this
    have hRpos2 : 0 < R ^ 2 := by positivity
    have hbound : R ^ 2 / rOut ^ 2 ≤ R ^ 2 / (x.2 0 ^ 2 + x.2 1 ^ 2) :=
      div_le_div_of_nonneg_left hRpos2.le hq0 hqle
    have hr2pos : 0 < rOut ^ 2 := by rw [hr2]; positivity
    have hval : R ^ 2 / rOut ^ 2 = 6 / (5 * ν) := by
      rw [hr2]
      field_simp
    have hexp : Real.exp δ * s < 6 / (5 * ν) := by
      rw [lt_div_iff₀ (by positivity)]
      have hpos : 0 < Real.exp δ := Real.exp_pos δ
      nlinarith [mul_le_mul_of_nonneg_left hs hpos.le]
    linarith

/-- The pointwise identity at a fixed young chart point (step 5 with `sepWCongrAE`). -/
theorem sepFarId (dm dp : ℝ) : SepFarId dm dp := by
  intro D hst
  have hdm : 0 < dm := hst.dm_pos
  have hapos : 0 < D.K.b * dm := mul_pos hst.b_pos hdm
  have hsmall : ∀ᶠ n : ℕ in atTop, retNu D.Pl D.σ₀ n ≤ (D.K.b * dm) ^ 2 / 2 :=
    Filter.Tendsto.eventually_le_const (div_pos (pow_pos hapos 2) two_pos)
      (retNu_tendsto D.σ₀ hst.omega_ne)
  filter_upwards [hst.actual, hsmall] with n hact hs
  intro z hz F g₁ g₂ T hg hT
  have hreg := hact.regime
  have hνa : (D.level n).ν ≤ (D.K.b * dm) ^ 2 / 2 := hs
  have hS : 1 / (D.level n).ν ≤ (D.level n).Scut D.K :=
    scut_ge_inv D.Pl D.K (D.level n) hst.b_pos hreg hνa
  have hν : 0 < (D.level n).ν := (D.level n).ν_pos
  have hc : 0 < cOf (D.level n).ν := cOf_pos hν
  have hR : 0 < (D.level n).ε⁻¹ := inv_pos.2 (D.level n).ε_pos
  obtain ⟨hsrc, hTeq, hward, _⟩ := hT
  have hG := strSum_lift_ae D.Pl D.K (D.level n) hst.C0_pos F g₁ g₂ hg
  have hGT : ∀ᵐ x : ℝ × Space ∂volume,
      NearInst.cartLift (D.level n).ε⁻¹ (cOf (D.level n).ν) (strSum F) x.1 x.2 = T x.1 x.2 := by
    filter_upwards [hG, hTeq] with x h1 h2
    rw [h1, h2]
    rfl
  have hexp : Real.exp D.K.δ < 6 / 5 := by
    have h12 : Real.exp D.K.δ < 12 / 11 := by
      rw [← Real.exp_log (by norm_num : (0 : ℝ) < 12 / 11)]
      exact Real.exp_lt_exp.2 hst.δ_lt
    linarith
  have hrO0 : 0 ≤ (D.level n).ε⁻¹ * Real.sqrt (5 * (D.level n).ν / 6) :=
    mul_nonneg hR.le (Real.sqrt_nonneg _)
  have hrO2 : ((D.level n).ε⁻¹ * Real.sqrt (5 * (D.level n).ν / 6)) ^ 2
      = (D.level n).ε⁻¹ ^ 2 * (5 * (D.level n).ν / 6) := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
  filter_upwards [ageμ_fst_eq_null (cOf (D.level n).ν) (-3 / 2) (1 / (D.level n).ν)] with x hne
  intro hle
  have hlt : x.1 < 1 / (D.level n).ν :=
    lt_of_le_of_ne (by rw [le_div_iff₀ hν, mul_comm]; exact hle) hne
  have hxS : x.1 < (D.level n).Scut D.K := lt_of_lt_of_le hlt hS
  have hmask := mask_eq_ae ((D.level n).ε⁻¹) (D.level n).ν D.K.δ x.1 _ hν hexp hle
    hrO0 hrO2 hR T
    (fun τ z => NearInst.cartLift (D.level n).ε⁻¹ (cOf (D.level n).ν) (strSum F) τ z)
    hsrc.support hGT
  have hsep : NearInst.sepWfar (D.level n).ν (D.mu n z : ℂ) (D.level n).ε⁻¹ D.K.δ x.1
      (NearInst.cartLift (D.level n).ε⁻¹ (cOf (D.level n).ν) (strSum F))
      (NearInst.chartY (D.level n).ε⁻¹ x) (NearInst.chartTau (D.level n).ε⁻¹ x)
      = UnforcedLeray.Short.IIIa.sepW (D.level n).ν (D.mu n z : ℂ) T
        (NearInst.chartY (D.level n).ε⁻¹ x) (NearInst.chartTau (D.level n).ε⁻¹ x) :=
    sepWCongrAE (D.level n).ν (D.mu n z : ℂ)
      (fun τ z => if Real.exp D.K.δ * x.1 < (D.level n).ε⁻¹ ^ 2 / (z 0 ^ 2 + z 1 ^ 2)
        then NearInst.cartLift (D.level n).ε⁻¹ (cOf (D.level n).ν) (strSum F) τ z else 0)
      T hmask _ _
  have hwR : ∀ i : Fin 3,
      wardW (D.level n).ν (D.mu n z) (D.level n).ε⁻¹ (cOf (D.level n).ν) (g₁ + g₂)
        (NearInst.chartTau (D.level n).ε⁻¹ x) (NearInst.chartY (D.level n).ε⁻¹ x) i
        = (UnforcedLeray.Short.IIIa.sepW (D.level n).ν (D.mu n z : ℂ) T
            (NearInst.chartY (D.level n).ε⁻¹ x) (NearInst.chartTau (D.level n).ε⁻¹ x) i).re := by
    intro i
    rw [hward]
    simp [sepWre]
  unfold NearInst.Masked.farOut
  rw [if_pos hxS, hsep]
  unfold coefOf
  ext i
  fin_cases i <;> simp [NearInst.merRe, hwR]

end UnforcedLeray.Short.PartIIIb.Concrete
