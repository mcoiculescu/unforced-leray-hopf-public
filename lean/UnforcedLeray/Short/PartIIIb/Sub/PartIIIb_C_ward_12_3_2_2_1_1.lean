import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_2_2_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_1.AgeJet
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_1.ChartLift
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_1.EFar
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_1.SliceBridge
import UnforcedLeray.Short.PartIIa.Tasks.R03ResidualChart
import UnforcedLeray.Short.PartIIa.Sub.R01
import UnforcedLeray.Short.PartIIa.Tasks.R01.EarlyCalculus
import UnforcedLeray.Short.PartIIa.Tasks.R01.EarlyStreamProfile
import UnforcedLeray.Short.PartIIa.Tasks.R01.EarlyPressureProfile
import UnforcedLeray.Short.PartIIa.Tasks.R02.ProfileSmooth

/-!
# `PartIII-b:C/ward/12/3/2/2/1/1`: `RawResidualD2FarDecay`

Source of record:
`the November 2 reference manuscript`,
lines 2542-2548 at `k = 2`, 1255-1305: in the large-radius region `ϱ > R₀` the similarity
residual `F_R = s^{3/2} (r_r e_r + r_z e_z) = s N_v r` (`PartIIa.ringResidual_eq_chart`) has
homogeneity `-3`, so its second spatial derivatives have homogeneity `-5` and satisfy
`|D² F_R(τ, y)| ≤ C ϱ^{-5} (1 + |y₃|/ϱ)^{-2} ≤ C ϱ^{-3} (1 + |y₃|/ϱ)^{-2}` once the chart
residual profile `r = (r_r, r_z)` has zero-age second-jet decay `(1 + |η|)^{-4}` on `0 < s ≤ s₀`
(`ResProfileFarJet`).

This file proves:
1. the off-axis chart representation `ringResidual = Axi.age p.R • Axi.Nv p.R (resChartProfile p)`
   (`ringResidual_eq_age_smul_Nv`);
2. the joint off-axis smoothness and Leibniz/Faà di Bruno far-field second-jet bound for
   `s N_v b` (`age_smul_nv_far_jet2`);
3. the complete reduction `rawResidualD2FarDecay_of : ResProfileFarJet → RawResidualD2FarDecay`.
-/

set_option autoImplicit false

noncomputable section

open UnforcedLeray.PhaseSpace MeasureTheory Set Filter Topology
open scoped ContDiff ENNReal
open UnforcedLeray.Cons.C03.Concrete (Params)
open UnforcedLeray.Short.IIb (trainStream trainPressure rawResidualC)
open UnforcedLeray.B0184 UnforcedLeray.B0185 UnforcedLeray.B0187 UnforcedLeray.B0188
  UnforcedLeray.B0190 UnforcedLeray.Short.PartIIa

namespace UnforcedLeray.Short.PartIIIb.Concrete

namespace FarDecaySub

/-- Coordinate permutation `(s, (ξ, η)) ↦ (ξ, (η, s))` from `Axi.chart` order to
`ProfilePoint` order. -/
def chartSwap (m : ℝ × (ℝ × ℝ)) : ProfilePoint :=
  (m.2.1, (m.2.2, m.1))

theorem chartSwap_chart (R τ : ℝ) (y : UnforcedLeray.Space) :
    chartSwap (Axi.chart R τ y) = chartPtR03 R τ y :=
  rfl

/-- The meridional chart residual profile `r = (r_r, r_z)` in `Axi.chart` coordinates
`m = (s, (ξ, η))` (`the November 2 reference manuscript`, lines 1255-1269). -/
def resChartProfile (p : Params) (m : ℝ × (ℝ × ℝ)) : Axi.Merid :=
  !₂[chartRadialResidual p.R p.ν
        (streamV1 (trainStream p))
        (axialProfile p.R (trainStream p))
        (trainPressure p) (chartSwap m),
      chartAxialResidual p.R p.ν
        (streamV1 (trainStream p))
        (axialProfile p.R (trainStream p))
        (trainPressure p) (chartSwap m)]

end FarDecaySub

open FarDecaySub

/-- **Zero-age chart jets of the ring residual profile** (`the November 2 reference manuscript`,
lines 1270-1305, 2542-2548): on `0 < s ≤ s₀` the derivatives of order `l ≤ 2` of the chart
residual profile `resChartProfile p` decay like `C (1 + |η|)^{-4}`. -/
def ResProfileFarJet : Prop :=
  ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ p : Params, UnforcedLeray.Short.PartI.IsBUCTrain p.train → p.ν < ν₀ →
    p.c = (p.ν ^ 2)⁻¹ → 2 ≤ p.R → p.period ≤ 1 →
      ∃ C s0 : ℝ, 0 < s0 ∧ ∀ m : ℝ × (ℝ × ℝ), 0 < m.1 → m.1 ≤ s0 → ∀ l ≤ 2,
        ‖iteratedFDeriv ℝ l (resChartProfile p) m‖ ≤ C * (1 + |m.2.2|) ^ (-4 : ℝ)

namespace FarDecaySub

theorem earlyBdd_of_eq {ρ : ℝ} {X Y : ProfFam} (e : X = Y) (h : EarlyBdd ρ X) :
    EarlyBdd ρ Y := by
  subst e
  exact h

/-- `EarlyBdd ρ` for `coeffA₁` from `EarlyStreamProfile` and `EarlyPressureProfile`. -/
theorem earlyBdd_coeffA1 (hψ : EarlyStreamProfile) (hp : EarlyPressureProfile)
    {ρ : ℝ} (hρ : 1 / 2 < ρ) : EarlyBdd ρ (fun ν ψ p => coeffA₁ ν ψ p) := by
  have hC : EarlyCalculus := earlyCalculus
  have hS : LateProfileSmooth := lateProfileSmooth_of UnforcedLeray.Short.PartI.trainStreamSmooth
  have hPsi : EarlyBdd ρ (fun _ ψ _ => ψ) := earlyBdd_stream hS hψ hρ
  have hPr : EarlyBdd ρ (fun _ _ p => p) := earlyBdd_pressure hS hp hρ
  have hV : EarlyBdd ρ (fun _ ψ _ => streamV1 ψ) :=
    hC.neg ρ (fun _ ψ _ => partialEta ψ) hρ (hC.dEta ρ (fun _ ψ _ => ψ) hρ hPsi)
  have hH : EarlyBdd ρ (fun _ ψ _ => ageDefect ψ) :=
    hC.sub ρ (fun _ ψ _ => ψ) (fun _ ψ _ => ageOperator ψ) hρ hPsi
      (hC.scaling ρ (fun _ ψ _ => ψ) hρ hPsi)
  have hKV := hC.scaling ρ (fun _ ψ _ => streamV1 ψ) hρ hV
  have hdEtaV := hC.dEta ρ (fun _ ψ _ => streamV1 ψ) hρ hV
  have hdQV := hC.dQ ρ (fun _ ψ _ => streamV1 ψ) hρ hV
  have hsh1 := hC.shift ρ 1 (fun _ ψ _ => partialQ (streamV1 ψ)) hρ hdQV
  have hsh2 := hC.shift ρ 2 (fun _ _ p => p) hρ hPr
  have hMA := hC.mul ρ _ _ hρ hV hKV
  have hMB := hC.mul ρ _ _ hρ hH hdEtaV
  have hMC := hC.mul ρ _ _ hρ hV hV
  have hNU := hC.nuMul ρ _ hρ (hC.constMul ρ 2 _ hρ hsh1)
  have hX1 := hC.neg ρ _ hρ hMA
  have hX2 := hC.add ρ _ _ hρ hX1 hMB
  have hX3 := hC.sub ρ _ _ hρ hX2 hMC
  have hX4 := hC.add ρ _ _ hρ hX3 hNU
  have hX5 := hC.sub ρ _ _ hρ hX4 hsh2
  refine earlyBdd_of_eq ?_ hX5
  funext ν ψ p x
  simp only [coeffA₁, ageDefect, ageShift, streamV1, Pi.add_apply, Pi.sub_apply,
    Pi.mul_apply, Pi.neg_apply]
  ring

/-- `EarlyBdd ρ` for `coeffA₂` from `EarlyStreamProfile`. -/
theorem earlyBdd_coeffA2 (hψ : EarlyStreamProfile) {ρ : ℝ} (hρ : 1 / 2 < ρ) :
    EarlyBdd ρ (fun ν ψ _ => coeffA₂ ν ψ) := by
  have hC : EarlyCalculus := earlyCalculus
  have hS : LateProfileSmooth := lateProfileSmooth_of UnforcedLeray.Short.PartI.trainStreamSmooth
  have hPsi : EarlyBdd ρ (fun _ ψ _ => ψ) := earlyBdd_stream hS hψ hρ
  have hH : EarlyBdd ρ (fun _ ψ _ => ageDefect ψ) :=
    hC.sub ρ (fun _ ψ _ => ψ) (fun _ ψ _ => ageOperator ψ) hρ hPsi
      (hC.scaling ρ (fun _ ψ _ => ψ) hρ hPsi)
  have hv1 : EarlyBdd ρ (fun _ ψ _ => streamV1 ψ) :=
    hC.neg ρ (fun _ ψ _ => partialEta ψ) hρ (hC.dEta ρ (fun _ ψ _ => ψ) hρ hPsi)
  have hv2 : EarlyBdd ρ (fun _ ψ _ => streamV2 ψ) :=
    hC.dQ ρ (fun _ ψ _ => ψ) hρ hPsi
  have dA := hC.dAge ρ _ hρ hH
  have dQH := hC.dQ ρ _ hρ hH
  have dEH := hC.dEta ρ _ hρ hH
  have lap := hC.add ρ _ _ hρ (hC.dQ ρ _ hρ dQH) (hC.dEta ρ _ hρ dEH)
  have TD := hC.sub ρ _ _ hρ
    (hC.add ρ _ _ hρ (hC.add ρ _ _ hρ dA (hC.mul ρ _ _ hρ hv1 dQH)) (hC.mul ρ _ _ hρ hv2 dEH))
    (hC.nuMul ρ _ hρ lap)
  have dEv2 := hC.dEta ρ _ hρ hv2
  have sh1v2 := hC.shift ρ 1 _ hρ hv2
  have sh1dQv2 := hC.shift ρ 1 _ hρ (hC.dQ ρ _ hρ hv2)
  have W := hC.add ρ _ _ hρ
    (hC.sub ρ _ _ hρ (hC.add ρ _ _ hρ TD (hC.mul ρ _ _ hρ hH dEv2)) (hC.mul ρ _ _ hρ hv1 sh1v2))
    (hC.nuMul ρ _ hρ (hC.constMul ρ 2 _ hρ sh1dQv2))
  refine earlyBdd_of_eq ?_ W
  funext ν ψ p x
  simp only [coeffA₂, transportDiffusion, profileLap, streamV1, streamV2, ageDefect, ageShift,
    Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
  ring

/-- `EarlyBdd ρ` for `coeffB₁` from `EarlyStreamProfile`. -/
theorem earlyBdd_coeffB1 (hψ : EarlyStreamProfile) {ρ : ℝ} (hρ : 1 / 2 < ρ) :
    EarlyBdd ρ (fun ν ψ _ => coeffB₁ ν ψ) := by
  have hC : EarlyCalculus := earlyCalculus
  have hS : LateProfileSmooth := lateProfileSmooth_of UnforcedLeray.Short.PartI.trainStreamSmooth
  have hPsi : EarlyBdd ρ (fun _ ψ _ => ψ) := earlyBdd_stream hS hψ hρ
  have hV : EarlyBdd ρ (fun _ ψ _ => streamV1 ψ) :=
    hC.neg ρ (fun _ ψ _ => partialEta ψ) hρ (hC.dEta ρ (fun _ ψ _ => ψ) hρ hPsi)
  have hS2 := hC.shift ρ 2 (fun _ ψ _ => streamV1 ψ) hρ hV
  have hK := hC.scaling ρ (fun _ ψ _ => ageShift 2 (streamV1 ψ)) hρ hS2
  have hN := hC.nuMul ρ (fun _ ψ _ => ageOperator (ageShift 2 (streamV1 ψ))) hρ hK
  have hM := hC.constMul ρ (-1) _ hρ hN
  refine earlyBdd_of_eq ?_ hM
  funext ν ψ p x
  show (-1 : ℝ) * (ν * ageOperator (ageShift 2 (streamV1 ψ)) x) =
    -ν * ageOperator (ageShift 2 (streamV1 ψ)) x
  ring

/-- `EarlyBdd ρ` for `coeffB₂` from `EarlyStreamProfile`. -/
theorem earlyBdd_coeffB2 (hψ : EarlyStreamProfile) {ρ : ℝ} (hρ : 1 / 2 < ρ) :
    EarlyBdd ρ (fun ν ψ _ => coeffB₂ ν ψ) := by
  have hC : EarlyCalculus := earlyCalculus
  have hS : LateProfileSmooth := lateProfileSmooth_of UnforcedLeray.Short.PartI.trainStreamSmooth
  have hPsi : EarlyBdd ρ (fun _ ψ _ => ψ) := earlyBdd_stream hS hψ hρ
  have hH : EarlyBdd ρ (fun _ ψ _ => ageDefect ψ) :=
    hC.sub ρ (fun _ ψ _ => ψ) (fun _ ψ _ => ageOperator ψ) hρ hPsi
      (hC.scaling ρ (fun _ ψ _ => ψ) hρ hPsi)
  have hv1 : EarlyBdd ρ (fun _ ψ _ => streamV1 ψ) :=
    hC.neg ρ (fun _ ψ _ => partialEta ψ) hρ (hC.dEta ρ (fun _ ψ _ => ψ) hρ hPsi)
  have hv2 : EarlyBdd ρ (fun _ ψ _ => streamV2 ψ) :=
    hC.dQ ρ (fun _ ψ _ => ψ) hρ hPsi
  have sh1H := hC.shift ρ 1 _ hρ hH
  have t1 := hC.neg ρ _ hρ (hC.mul ρ _ _ hρ hv1 sh1H)
  have dEH := hC.dEta ρ _ hρ hH
  have t2 := hC.mul ρ _ _ hρ hH dEH
  have dQH := hC.dQ ρ _ hρ hH
  have t3 := hC.nuMul ρ _ hρ (hC.constMul ρ 2 _ hρ (hC.shift ρ 1 _ hρ dQH))
  have t4 := hC.nuMul ρ _ hρ (hC.shift ρ 1 _ hρ (hC.shift ρ 1 _ hρ hv2))
  have W := hC.sub ρ _ _ hρ (hC.add ρ _ _ hρ (hC.add ρ _ _ hρ t1 t2) t3) t4
  refine earlyBdd_of_eq ?_ W
  funext ν ψ p x
  simp only [coeffB₂, streamV1, streamV2, ageDefect, ageShift,
    Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.neg_apply]
  ring

/-- `EarlyBdd ρ` for `coeffB₃` from `EarlyStreamProfile`. -/
theorem earlyBdd_coeffB3 (hψ : EarlyStreamProfile) {ρ : ℝ} (hρ : 1 / 2 < ρ) :
    EarlyBdd ρ (fun ν ψ _ => coeffB₃ ν ψ) := by
  have hC : EarlyCalculus := earlyCalculus
  have hS : LateProfileSmooth := lateProfileSmooth_of UnforcedLeray.Short.PartI.trainStreamSmooth
  have hΨ : EarlyBdd ρ (fun _ ψ _ => ψ) := earlyBdd_stream hS hψ hρ
  have hO := hC.scaling ρ (fun _ ψ _ => ψ) hρ hΨ
  have hD := hC.sub ρ (fun _ ψ _ => ψ) (fun _ ψ _ => ageOperator ψ) hρ hΨ hO
  have hS1 := hC.shift ρ 1 (fun _ ψ _ => ageDefect ψ) hρ hD
  have hS2 := hC.shift ρ 1 (fun _ ψ _ => ageShift 1 (ageDefect ψ)) hρ hS1
  have hN := hC.nuMul ρ (fun _ ψ _ => ageShift 1 (ageShift 1 (ageDefect ψ))) hρ hS2
  have hM := hC.constMul ρ (-1) _ hρ hN
  refine earlyBdd_of_eq ?_ hM
  funext ν ψ p x
  simp only [coeffB₃]
  ring

theorem isOpen_ageDomain : IsOpen ageDomain :=
  isOpen_lt continuous_const (continuous_snd.comp continuous_snd)

theorem contDiffOn_fderiv_dir {f : ProfilePoint → ℝ} (hf : ContDiffOn ℝ ∞ f ageDomain)
    (v : ProfilePoint) : ContDiffOn ℝ ∞ (fun x => fderiv ℝ f x v) ageDomain :=
  (hf.fderiv_of_isOpen isOpen_ageDomain (by simp)).clm_apply contDiffOn_const

theorem contDiffOn_ageOperator {f : ProfilePoint → ℝ} (hf : ContDiffOn ℝ ∞ f ageDomain) :
    ContDiffOn ℝ ∞ (ageOperator f) ageDomain := by
  have hE := contDiffOn_fderiv_dir hf eηDir
  have hA := contDiffOn_fderiv_dir hf esDir
  have hc1 : ContDiffOn ℝ ∞ (fun x : ProfilePoint => x.2.1) ageDomain :=
    (show ContDiff ℝ ∞ (fun x : ProfilePoint => x.2.1) by fun_prop).contDiffOn
  have hc2 : ContDiffOn ℝ ∞ (fun x : ProfilePoint => 2 * x.2.2) ageDomain :=
    (show ContDiff ℝ ∞ (fun x : ProfilePoint => 2 * x.2.2) by fun_prop).contDiffOn
  unfold ageOperator partialEta partialAge
  exact (hc1.mul hE).add (hc2.mul hA)

theorem contDiffOn_ringD (R : ℝ) {f : ProfilePoint → ℝ} (hf : ContDiffOn ℝ ∞ f ageDomain) :
    ContDiffOn ℝ ∞ (ringD R f) ageDomain := by
  have hQ : ContDiffOn ℝ ∞ (partialQ f) ageDomain := contDiffOn_fderiv_dir hf eqDir
  exact hQ.sub (contDiffOn_const.mul (contDiffOn_ageOperator hf))

theorem contDiffOn_chartRadialResidual (R ν : ℝ) {f h pres : ProfilePoint → ℝ}
    (hf : ContDiffOn ℝ ∞ f ageDomain) (hh : ContDiffOn ℝ ∞ h ageDomain)
    (hp : ContDiffOn ℝ ∞ pres ageDomain) :
    ContDiffOn ℝ ∞ (chartRadialResidual R ν f h pres) ageDomain := by
  have hdf := contDiffOn_ringD R hf
  have hddf := contDiffOn_ringD R hdf
  have hetaf : ContDiffOn ℝ ∞ (partialEta f) ageDomain := contDiffOn_fderiv_dir hf eηDir
  have heta2f : ContDiffOn ℝ ∞ (partialEta (partialEta f)) ageDomain :=
    contDiffOn_fderiv_dir hetaf eηDir
  have hagef : ContDiffOn ℝ ∞ (partialAge f) ageDomain := contDiffOn_fderiv_dir hf esDir
  have hdp := contDiffOn_ringD R hp
  have hdiff : ContDiffOn ℝ ∞ (ringDiffusionRadial R f) ageDomain :=
    (hddf.sub (contDiffOn_const.mul hdf)).add heta2f
  unfold chartRadialResidual
  exact ((((hagef.add (hf.mul hdf)).add (hh.mul hetaf)).sub
    (contDiffOn_const.mul (hf.pow 2))).sub (contDiffOn_const.mul hdiff)).add
      (hdp.sub (contDiffOn_const.mul hp))

theorem contDiffOn_chartAxialResidual (R ν : ℝ) {f h pres : ProfilePoint → ℝ}
    (hf : ContDiffOn ℝ ∞ f ageDomain) (hh : ContDiffOn ℝ ∞ h ageDomain)
    (hp : ContDiffOn ℝ ∞ pres ageDomain) :
    ContDiffOn ℝ ∞ (chartAxialResidual R ν f h pres) ageDomain := by
  have hdh := contDiffOn_ringD R hh
  have hddh := contDiffOn_ringD R hdh
  have hetah : ContDiffOn ℝ ∞ (partialEta h) ageDomain := contDiffOn_fderiv_dir hh eηDir
  have heta2h : ContDiffOn ℝ ∞ (partialEta (partialEta h)) ageDomain :=
    contDiffOn_fderiv_dir hetah eηDir
  have hageh : ContDiffOn ℝ ∞ (partialAge h) ageDomain := contDiffOn_fderiv_dir hh esDir
  have hetap : ContDiffOn ℝ ∞ (partialEta pres) ageDomain := contDiffOn_fderiv_dir hp eηDir
  have hdiff : ContDiffOn ℝ ∞ (ringDiffusionAxial R h) ageDomain :=
    ((hddh.sub (contDiffOn_const.mul hdh)).add (contDiffOn_const.mul hh)).add heta2h
  unfold chartAxialResidual
  exact ((((hageh.add (hf.mul hdh)).add (hh.mul hetah)).sub
    ((contDiffOn_const.mul hf).mul hh)).sub (contDiffOn_const.mul hdiff)).add hetap

/-- For any BUC train, `resChartProfile p` is `C^∞` on `{m | 0 < m.1}`. -/
theorem resChartProfile_contDiffOn (p : Params)
    (htr : UnforcedLeray.Short.PartI.IsBUCTrain p.train) :
    ContDiffOn ℝ ∞ (resChartProfile p) {m : ℝ × (ℝ × ℝ) | 0 < m.1} := by
  have hψ : ContDiffOn ℝ ∞ (trainStream p) ageDomain :=
    UnforcedLeray.Short.IIb.trainStreamSmoothBUC_of
      UnforcedLeray.Short.PartI.trainStreamSmooth p.ν p.c p.ν_pos p.c_pos p.train htr
  have hp : ContDiffOn ℝ ∞ (trainPressure p) ageDomain :=
    UnforcedLeray.Short.IIb.trainPressureSmooth p.ν p.c p.train
  have hv1 : ContDiffOn ℝ ∞ (streamV1 (trainStream p)) ageDomain :=
    (contDiffOn_fderiv_dir hψ eηDir).neg
  have hv2 : ContDiffOn ℝ ∞ (axialProfile p.R (trainStream p)) ageDomain := by
    have hs2 : ContDiffOn ℝ ∞ (streamV2 (trainStream p)) ageDomain :=
      contDiffOn_fderiv_dir hψ eqDir
    have had : ContDiffOn ℝ ∞ (ageDefect (trainStream p)) ageDomain :=
      hψ.sub (contDiffOn_ageOperator hψ)
    exact hs2.add (contDiffOn_const.mul had)
  have hsw : ContDiff ℝ ∞ chartSwap := by
    unfold chartSwap
    fun_prop
  have hmaps : MapsTo chartSwap {m : ℝ × (ℝ × ℝ) | 0 < m.1} ageDomain :=
    fun _ hm => hm
  have hr0 : ContDiffOn ℝ ∞
      (fun m => chartRadialResidual p.R p.ν (streamV1 (trainStream p))
        (axialProfile p.R (trainStream p)) (trainPressure p) (chartSwap m))
      {m : ℝ × (ℝ × ℝ) | 0 < m.1} :=
    (contDiffOn_chartRadialResidual p.R p.ν hv1 hv2 hp).comp hsw.contDiffOn hmaps
  have hr1 : ContDiffOn ℝ ∞
      (fun m => chartAxialResidual p.R p.ν (streamV1 (trainStream p))
        (axialProfile p.R (trainStream p)) (trainPressure p) (chartSwap m))
      {m : ℝ × (ℝ × ℝ) | 0 < m.1} :=
    (contDiffOn_chartAxialResidual p.R p.ν hv1 hv2 hp).comp hsw.contDiffOn hmaps
  have hEq : resChartProfile p = fun m =>
      chartRadialResidual p.R p.ν (streamV1 (trainStream p))
          (axialProfile p.R (trainStream p)) (trainPressure p) (chartSwap m) •
        (!₂[(1 : ℝ), 0] : Axi.Merid) +
      chartAxialResidual p.R p.ν (streamV1 (trainStream p))
          (axialProfile p.R (trainStream p)) (trainPressure p) (chartSwap m) •
        (!₂[(0 : ℝ), 1] : Axi.Merid) := by
    ext m i
    fin_cases i <;> simp [resChartProfile]
  rw [hEq]
  exact (hr0.smul contDiffOn_const).add (hr1.smul contDiffOn_const)

theorem age_rpow_three_halves {s : ℝ} (hs : 0 < s) : s ^ (3 / 2 : ℝ) = s * √s := by
  rw [Real.sqrt_eq_rpow, show (3 / 2 : ℝ) = 1 + 1 / 2 by ring, Real.rpow_add hs, Real.rpow_one]

/-- Off the axis, the similarity ring residual equals `s • N_v (resChartProfile p)`
(`F_R = s^{3/2} r = s (√s r)`, source line 1263). -/
theorem ringResidual_eq_age_smul_Nv (p : Params)
    (htr : UnforcedLeray.Short.PartI.IsBUCTrain p.train) (hR : 2 ≤ p.R)
    (τ : ℝ) (y : UnforcedLeray.Space) (hy : Axi.ϱ y ≠ 0) :
    ringResidual p.R p.ν (trainStream p) (trainPressure p) τ y =
      Axi.age p.R y • Axi.Nv p.R (resChartProfile p) τ y := by
  have hRpos : 0 < p.R := by linarith
  have hyax : y ∉ Axi.axis := mt (Axi.mem_axis_iff y).mp hy
  have hspos : 0 < Axi.age p.R y := Axi.age_pos hRpos.ne' hyax
  have hopen : IsOpen ageDomain := isOpen_ageDomain
  have hmem : chartPtR03 p.R τ y ∈ ageDomain := hspos
  have hψon : ContDiffOn ℝ ∞ (trainStream p) ageDomain :=
    UnforcedLeray.Short.IIb.trainStreamSmoothBUC_of
      UnforcedLeray.Short.PartI.trainStreamSmooth p.ν p.c p.ν_pos p.c_pos p.train htr
  have hpon : ContDiffOn ℝ ∞ (trainPressure p) ageDomain :=
    UnforcedLeray.Short.IIb.trainPressureSmooth p.ν p.c p.train
  have hψ3 : ContDiffAt ℝ 3 (trainStream p) (chartPtR03 p.R τ y) :=
    (hψon.contDiffAt (hopen.mem_nhds hmem)).of_le (by norm_num)
  have hp1 : ContDiffAt ℝ 1 (trainPressure p) (chartPtR03 p.R τ y) :=
    (hpon.contDiffAt (hopen.mem_nhds hmem)).of_le (by norm_num)
  rw [ringResidual_eq_chart p.R p.ν hR (trainStream p)
    (trainPressure p) τ y hy hψ3 hp1]
  rw [age_rpow_three_halves hspos, mul_smul]
  congr 1

/-- Off the axis, `rawResidualC p` agrees with the complexified lift `s • N_v (resChartProfile p)`. -/
theorem rawResidualC_eq_off_axis (p : Params)
    (htr : UnforcedLeray.Short.PartI.IsBUCTrain p.train) (hR : 2 ≤ p.R)
    (z : ℝ × UnforcedLeray.Space) (hz : z.2 ∉ Axi.axis) :
    rawResidualC p z =
      efarRealCLI (Axi.age p.R z.2 • Axi.Nv p.R (resChartProfile p) z.1 z.2) := by
  have hy : Axi.ϱ z.2 ≠ 0 := Axi.ϱ_ne_zero hz
  change UnforcedLeray.B0412.realC
    (ringResidual p.R p.ν (trainStream p) (trainPressure p) z.1 z.2) = _
  rw [ringResidual_eq_age_smul_Nv p htr hR z.1 z.2 hy]
  rfl

/-- Joint smoothness of `(τ, y) ↦ Axi.chart R τ y` off the axis. -/
theorem chart_joint_contDiffOn (R : ℝ) (hR : 0 < R) :
    ContDiffOn ℝ ∞ (fun z : ℝ × UnforcedLeray.Space => Axi.chart R z.1 z.2)
      {z : ℝ × UnforcedLeray.Space | z.2 ∉ Axi.axis} := by
  have hϱ : ContDiffOn ℝ ∞ (fun z : ℝ × UnforcedLeray.Space => Axi.ϱ z.2)
      {z : ℝ × UnforcedLeray.Space | z.2 ∉ Axi.axis} :=
    Axi.contDiffOn_ϱ.comp contDiff_snd.contDiffOn (fun _ hz => hz)
  have hAge : ContDiffOn ℝ ∞ (fun z : ℝ × UnforcedLeray.Space => Axi.age R z.2)
      {z : ℝ × UnforcedLeray.Space | z.2 ∉ Axi.axis} :=
    contDiffOn_const.div (hϱ.pow 2) (fun _ hz => pow_ne_zero 2 (Axi.ϱ_ne_zero hz))
  have hLog : ContDiffOn ℝ ∞ (fun z : ℝ × UnforcedLeray.Space => Real.log (Axi.age R z.2))
      {z : ℝ × UnforcedLeray.Space | z.2 ∉ Axi.axis} :=
    ContDiffOn.log hAge (fun _ hz => (Axi.age_pos hR.ne' hz).ne')
  have hPhase : ContDiffOn ℝ ∞ (fun z : ℝ × UnforcedLeray.Space => Axi.phase R z.1 z.2)
      {z : ℝ × UnforcedLeray.Space | z.2 ∉ Axi.axis} := by
    have h1 : ContDiffOn ℝ ∞ (fun z : ℝ × UnforcedLeray.Space => R * z.1 / 2)
        {z : ℝ × UnforcedLeray.Space | z.2 ∉ Axi.axis} :=
      (show ContDiff ℝ ∞ (fun z : ℝ × UnforcedLeray.Space => R * z.1 / 2) by fun_prop).contDiffOn
    exact h1.sub (contDiffOn_const.mul hLog)
  have hTrans : ContDiffOn ℝ ∞ (fun z : ℝ × UnforcedLeray.Space => Axi.trans R z.2)
      {z : ℝ × UnforcedLeray.Space | z.2 ∉ Axi.axis} := by
    have h2 : ContDiffOn ℝ ∞ (fun z : ℝ × UnforcedLeray.Space => R * z.2 2)
        {z : ℝ × UnforcedLeray.Space | z.2 ∉ Axi.axis} :=
      (show ContDiff ℝ ∞ (fun z : ℝ × UnforcedLeray.Space => R * z.2 2) by fun_prop).contDiffOn
    exact h2.div hϱ (fun _ hz => Axi.ϱ_ne_zero hz)
  exact hAge.prodMk (hPhase.prodMk hTrans)

/-- Joint smoothness of `(τ, y) ↦ efarRealCLI (Axi.age R y • Axi.Nv R b τ y)` off the axis. -/
theorem age_smul_Nv_joint_contDiffOn (R : ℝ) (hR : 0 < R) (b : ℝ × (ℝ × ℝ) → Axi.Merid)
    (hb : ContDiffOn ℝ ∞ b {m : ℝ × (ℝ × ℝ) | 0 < m.1}) :
    ContDiffOn ℝ ∞
      (fun z : ℝ × UnforcedLeray.Space => efarRealCLI (Axi.age R z.2 • Axi.Nv R b z.1 z.2))
      {z : ℝ × UnforcedLeray.Space | z.2 ∉ Axi.axis} := by
  have hAge : ContDiffOn ℝ ∞ (fun z : ℝ × UnforcedLeray.Space => Axi.age R z.2)
      {z : ℝ × UnforcedLeray.Space | z.2 ∉ Axi.axis} := by
    have hA : ContDiffOn ℝ ∞ (Axi.age R) Axi.axisᶜ :=
      contDiffOn_const.div (Axi.contDiffOn_ϱ.pow 2)
        (fun y hy => pow_ne_zero 2 (Axi.ϱ_ne_zero hy))
    exact hA.comp contDiff_snd.contDiffOn (fun _ hz => hz)
  have hLF : ContDiffOn ℝ ∞ (fun z : ℝ × UnforcedLeray.Space => liftFactor R z.2)
      {z : ℝ × UnforcedLeray.Space | z.2 ∉ Axi.axis} :=
    (clf_lift_contDiffOn R hR).comp contDiff_snd.contDiffOn (fun _ hz => hz)
  have hCh : ContDiffOn ℝ ∞ (fun z : ℝ × UnforcedLeray.Space => b (Axi.chart R z.1 z.2))
      {z : ℝ × UnforcedLeray.Space | z.2 ∉ Axi.axis} :=
    hb.comp (chart_joint_contDiffOn R hR) (fun _ hz => Axi.age_pos hR.ne' hz)
  have hNv : ContDiffOn ℝ ∞ (fun z : ℝ × UnforcedLeray.Space => Axi.Nv R b z.1 z.2)
      {z : ℝ × UnforcedLeray.Space | z.2 ∉ Axi.axis} := by
    have hEq : (fun z : ℝ × UnforcedLeray.Space => Axi.Nv R b z.1 z.2) =
        fun z => liftFactor R z.2 (b (Axi.chart R z.1 z.2)) :=
      funext fun z => Nv_eq_liftFactor R b z.1 z.2
    rw [hEq]
    exact hLF.clm_apply hCh
  exact efarRealCLI.toContinuousLinearMap.contDiff.comp_contDiffOn (hAge.smul hNv)

/-- Uniform bound on the `0, 1, 2` spatial derivatives of `Axi.age R` off the axis. -/
theorem age_jet_le_two (R : ℝ) (hR : 0 < R) :
    ∃ Ca : ℝ, 0 ≤ Ca ∧ ∀ y : UnforcedLeray.Space, y ∉ Axi.axis → ∀ i : ℕ, i ≤ 2 →
      ‖iteratedFDeriv ℝ i (Axi.age R) y‖ ≤ Ca * Axi.ϱ y ^ (-(2 + (i : ℝ))) := by
  obtain ⟨C1, hC1, hb1⟩ := ageJet R hR 1 (by omega)
  obtain ⟨C2, hC2, hb2⟩ := ageJet R hR 2 (by omega)
  refine ⟨R ^ 2 + C1 + C2, by positivity, fun y hy i hi => ?_⟩
  have hρ : 0 < Axi.ϱ y := Axi.ϱ_pos hy
  have hrp : 0 ≤ Axi.ϱ y ^ (-(2 + (i : ℝ))) := Real.rpow_nonneg hρ.le _
  interval_cases i
  · rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs,
      abs_of_pos (Axi.age_pos hR.ne' hy)]
    have h0 : Axi.age R y = R ^ 2 * Axi.ϱ y ^ (-(2 + ((0 : ℕ) : ℝ))) := by
      unfold Axi.age
      rw [show -(2 + ((0 : ℕ) : ℝ)) = -((2 : ℕ) : ℝ) by norm_num,
        Real.rpow_neg hρ.le, Real.rpow_natCast, div_eq_mul_inv]
    rw [h0]
    exact mul_le_mul_of_nonneg_right (by linarith [sq_nonneg R]) hrp
  · exact (hb1 y hy).trans (mul_le_mul_of_nonneg_right (by linarith [sq_nonneg R]) hrp)
  · exact (hb2 y hy).trans (mul_le_mul_of_nonneg_right (by linarith [sq_nonneg R]) hrp)

/-- If `max R (R / √s0) < ϱ y`, then `R ≤ ϱ y` and `Axi.age R y ≤ s0`. -/
theorem age_le_of_radius_gt {R s0 : ℝ} (hR : 0 < R) (hs0 : 0 < s0) {y : UnforcedLeray.Space}
    (hy : max R (R / Real.sqrt s0) < Axi.ϱ y) :
    R ≤ Axi.ϱ y ∧ Axi.age R y ≤ s0 := by
  have h1 : R < Axi.ϱ y := lt_of_le_of_lt (le_max_left _ _) hy
  have h2 : R / Real.sqrt s0 < Axi.ϱ y := lt_of_le_of_lt (le_max_right _ _) hy
  have hρ : 0 < Axi.ϱ y := hR.trans h1
  have hsq : 0 < Real.sqrt s0 := Real.sqrt_pos.2 hs0
  have h3 : R < Axi.ϱ y * Real.sqrt s0 := (div_lt_iff₀ hsq).1 h2
  have h4 : R ^ 2 ≤ (Axi.ϱ y * Real.sqrt s0) ^ 2 :=
    pow_le_pow_left₀ hR.le h3.le 2
  rw [mul_pow, Real.sq_sqrt hs0.le] at h4
  refine ⟨h1.le, ?_⟩
  unfold Axi.age
  exact (div_le_iff₀ (pow_pos hρ 2)).2 (by linarith)

/-- Far-field spatial jets (orders `j ≤ 2`) of `Axi.Nv R b τ` when `b` has `(1 + |η|)^{-4}` decay
for `0 < s ≤ s0`. -/
theorem nv_far_jet_of_resProfile {R s0 Cb K : ℝ} (hR1 : 1 ≤ R) (hs0 : 0 < s0) (hK0 : 0 < K)
    (hKb : ∀ (b : ℝ × (ℝ × ℝ) → Axi.Merid), ContDiffOn ℝ ∞ b {m : ℝ × (ℝ × ℝ) | 0 < m.1} →
      ∀ (τ : ℝ) (y : UnforcedLeray.Space), R ≤ Axi.ϱ y → ∀ k : ℕ, k ≤ 3 →
        ‖iteratedFDeriv ℝ k (Axi.Nv R b τ) y‖ ≤
          K * Axi.ϱ y ^ (-(1 + (k : ℝ))) * (1 + |y 2| / Axi.ϱ y) ^ k *
            ∑ l ∈ Finset.range (k + 1), ‖iteratedFDeriv ℝ l b (Axi.chart R τ y)‖)
    {b : ℝ × (ℝ × ℝ) → Axi.Merid} (hb : ContDiffOn ℝ ∞ b {m : ℝ × (ℝ × ℝ) | 0 < m.1})
    (hbd : ∀ m : ℝ × (ℝ × ℝ), 0 < m.1 → m.1 ≤ s0 → ∀ l ≤ 2,
      ‖iteratedFDeriv ℝ l b m‖ ≤ Cb * (1 + |m.2.2|) ^ (-4 : ℝ))
    (τ : ℝ) {y : UnforcedLeray.Space} (hy : max R (R / Real.sqrt s0) < Axi.ϱ y)
    {j : ℕ} (hj : j ≤ 2) :
    ‖iteratedFDeriv ℝ j (Axi.Nv R b τ) y‖ ≤
      (3 * K * max Cb 0) * Axi.ϱ y ^ (-(1 + (j : ℝ))) *
        (1 + |y 2| / Axi.ϱ y) ^ (-2 : ℝ) := by
  have hRpos : 0 < R := lt_of_lt_of_le one_pos hR1
  obtain ⟨hRy, hage⟩ := age_le_of_radius_gt hRpos hs0 hy
  have hρ : 0 < Axi.ϱ y := lt_of_lt_of_le hRpos hRy
  have hyax : y ∉ Axi.axis := by
    intro h
    rw [Axi.mem_axis_iff] at h
    linarith
  have hspos : 0 < (Axi.chart R τ y).1 := Axi.age_pos hRpos.ne' hyax
  have ht0 : 0 ≤ |y 2| / Axi.ϱ y := div_nonneg (abs_nonneg _) hρ.le
  have h1t : 1 ≤ 1 + |y 2| / Axi.ϱ y := by linarith
  have h1t_pos : 0 < 1 + |y 2| / Axi.ϱ y := by linarith
  have hη : 1 + |y 2| / Axi.ϱ y ≤ 1 + |(Axi.chart R τ y).2.2| := by
    have : |y 2| / Axi.ϱ y ≤ |(Axi.chart R τ y).2.2| := by
      show |y 2| / Axi.ϱ y ≤ |Axi.trans R y|
      rw [Axi.trans, abs_div, abs_mul, abs_of_pos hRpos, abs_of_pos hρ]
      exact div_le_div_of_nonneg_right (le_mul_of_one_le_left (abs_nonneg _) hR1) hρ.le
    linarith
  have hpow4 : (1 + |(Axi.chart R τ y).2.2|) ^ (-4 : ℝ) ≤
      (1 + |y 2| / Axi.ϱ y) ^ (-4 : ℝ) :=
    Real.rpow_le_rpow_of_nonpos h1t_pos hη (by norm_num)
  have hterm : ∀ l ∈ Finset.range (j + 1),
      ‖iteratedFDeriv ℝ l b (Axi.chart R τ y)‖ ≤
        max Cb 0 * (1 + |y 2| / Axi.ϱ y) ^ (-4 : ℝ) := by
    intro l hl
    have hlj : l ≤ 2 := by have := Finset.mem_range.1 hl; omega
    have h1 := hbd (Axi.chart R τ y) hspos hage l hlj
    have h2 : Cb ≤ max Cb 0 := le_max_left _ _
    have h3 : 0 ≤ (1 + |(Axi.chart R τ y).2.2|) ^ (-4 : ℝ) :=
      Real.rpow_nonneg (by positivity) _
    exact h1.trans ((mul_le_mul_of_nonneg_right h2 h3).trans
      (mul_le_mul_of_nonneg_left hpow4 (le_max_right _ _)))
  have hsum : ∑ l ∈ Finset.range (j + 1), ‖iteratedFDeriv ℝ l b (Axi.chart R τ y)‖ ≤
      3 * (max Cb 0 * (1 + |y 2| / Axi.ϱ y) ^ (-4 : ℝ)) := by
    have hj3 : ((j + 1 : ℕ) : ℝ) ≤ 3 := by exact_mod_cast (show j + 1 ≤ 3 by omega)
    have hnonneg : 0 ≤ max Cb 0 * (1 + |y 2| / Axi.ϱ y) ^ (-4 : ℝ) :=
      mul_nonneg (le_max_right _ _) (Real.rpow_nonneg h1t_pos.le _)
    calc ∑ l ∈ Finset.range (j + 1), ‖iteratedFDeriv ℝ l b (Axi.chart R τ y)‖
        ≤ ∑ _ ∈ Finset.range (j + 1), max Cb 0 * (1 + |y 2| / Axi.ϱ y) ^ (-4 : ℝ) :=
          Finset.sum_le_sum hterm
      _ = ((j + 1 : ℕ) : ℝ) * (max Cb 0 * (1 + |y 2| / Axi.ϱ y) ^ (-4 : ℝ)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ 3 * (max Cb 0 * (1 + |y 2| / Axi.ϱ y) ^ (-4 : ℝ)) :=
          mul_le_mul_of_nonneg_right hj3 hnonneg
  have hjt : (1 + |y 2| / Axi.ϱ y) ^ j * (1 + |y 2| / Axi.ϱ y) ^ (-4 : ℝ) ≤
      (1 + |y 2| / Axi.ϱ y) ^ (-2 : ℝ) := by
    rw [← Real.rpow_natCast (1 + |y 2| / Axi.ϱ y) j, ← Real.rpow_add h1t_pos]
    apply Real.rpow_le_rpow_of_exponent_le h1t
    have : (j : ℝ) ≤ 2 := by exact_mod_cast hj
    linarith
  have hKstep := hKb b hb τ y hRy j (by omega)
  have hpref0 : 0 ≤ K * Axi.ϱ y ^ (-(1 + (j : ℝ))) * (1 + |y 2| / Axi.ϱ y) ^ j :=
    mul_nonneg (mul_nonneg hK0.le (Real.rpow_nonneg hρ.le _)) (pow_nonneg h1t_pos.le _)
  calc ‖iteratedFDeriv ℝ j (Axi.Nv R b τ) y‖
      ≤ K * Axi.ϱ y ^ (-(1 + (j : ℝ))) * (1 + |y 2| / Axi.ϱ y) ^ j *
          (3 * (max Cb 0 * (1 + |y 2| / Axi.ϱ y) ^ (-4 : ℝ))) :=
        hKstep.trans (mul_le_mul_of_nonneg_left hsum hpref0)
    _ = (3 * K * max Cb 0 * Axi.ϱ y ^ (-(1 + (j : ℝ)))) *
          ((1 + |y 2| / Axi.ϱ y) ^ j * (1 + |y 2| / Axi.ϱ y) ^ (-4 : ℝ)) := by ring
    _ ≤ (3 * K * max Cb 0 * Axi.ϱ y ^ (-(1 + (j : ℝ)))) *
          (1 + |y 2| / Axi.ϱ y) ^ (-2 : ℝ) :=
        mul_le_mul_of_nonneg_left hjt
          (mul_nonneg (mul_nonneg (by linarith) (le_max_right _ _)) (Real.rpow_nonneg hρ.le _))
    _ = (3 * K * max Cb 0) * Axi.ϱ y ^ (-(1 + (j : ℝ))) *
          (1 + |y 2| / Axi.ϱ y) ^ (-2 : ℝ) := by ring

/-- Order-2 far-field spatial jet bound for `s • N_v b`. -/
theorem age_smul_nv_far_jet2 {R s0 Cb : ℝ} (hR : 2 ≤ R) (hs0 : 0 < s0)
    {b : ℝ × (ℝ × ℝ) → Axi.Merid} (hb : ContDiffOn ℝ ∞ b {m : ℝ × (ℝ × ℝ) | 0 < m.1})
    (hbd : ∀ m : ℝ × (ℝ × ℝ), 0 < m.1 → m.1 ≤ s0 → ∀ l ≤ 2,
      ‖iteratedFDeriv ℝ l b m‖ ≤ Cb * (1 + |m.2.2|) ^ (-4 : ℝ)) :
    ∃ C R0 : ℝ, 0 < R0 ∧ ∀ (τ : ℝ) (y : UnforcedLeray.Space), R0 < Axi.ϱ y →
      ‖iteratedFDeriv ℝ 2 (fun w => Axi.age R w • Axi.Nv R b τ w) y‖ ≤
        C * (Axi.ϱ y ^ (-3 : ℝ) * (1 + |y 2| / Axi.ϱ y) ^ (-2 : ℝ)) := by
  have hR1 : 1 ≤ R := by linarith
  have hRpos : 0 < R := by linarith
  obtain ⟨Ca, hCa0, hCa⟩ := age_jet_le_two R hRpos
  obtain ⟨K, hK0, hKb⟩ := chartLiftJets R hRpos
  set CN : ℝ := 3 * K * max Cb 0
  have hCN0 : 0 ≤ CN := mul_nonneg (by positivity) (le_max_right _ _)
  set R0 : ℝ := max R (R / Real.sqrt s0)
  have hR0pos : 0 < R0 := lt_of_lt_of_le hRpos (le_max_left _ _)
  refine ⟨6 * Ca * CN, R0, hR0pos, fun τ y hy => ?_⟩
  have hRy : R ≤ Axi.ϱ y := (age_le_of_radius_gt hRpos hs0 hy).1
  have hρ1 : 1 ≤ Axi.ϱ y := hR1.trans hRy
  have hρ : 0 < Axi.ϱ y := lt_of_lt_of_le one_pos hρ1
  have hyax : y ∉ Axi.axis := by
    intro h
    rw [Axi.mem_axis_iff] at h
    linarith
  have hyS : y ∈ (Axi.axisᶜ : Set UnforcedLeray.Space) := hyax
  have hAgeS : ContDiffOn ℝ ∞ (Axi.age R) Axi.axisᶜ :=
    contDiffOn_const.div (Axi.contDiffOn_ϱ.pow 2)
      (fun z hz => pow_ne_zero 2 (Axi.ϱ_ne_zero hz))
  have hgS : ContDiffOn ℝ ∞ (fun z => b (Axi.chart R τ z)) Axi.axisᶜ :=
    hb.comp (clf_chart_contDiffOn R τ hRpos) (clf_chart_mapsTo R τ hRpos)
  have hNvS : ContDiffOn ℝ ∞ (Axi.Nv R b τ) Axi.axisᶜ := by
    have hEq : Axi.Nv R b τ = fun z => liftFactor R z (b (Axi.chart R τ z)) :=
      funext fun z => Nv_eq_liftFactor R b τ z
    rw [hEq]
    exact (clf_lift_contDiffOn R hRpos).clm_apply hgS
  have hleib : ‖iteratedFDeriv ℝ 2 (fun w => Axi.age R w • Axi.Nv R b τ w) y‖ ≤
      ∑ i ∈ Finset.range 3, (Nat.choose 2 i : ℝ) *
        ‖iteratedFDerivWithin ℝ i (Axi.age R) Axi.axisᶜ y‖ *
        ‖iteratedFDerivWithin ℝ (2 - i) (Axi.Nv R b τ) Axi.axisᶜ y‖ := by
    rw [← iteratedFDerivWithin_of_isOpen (𝕜 := ℝ)
      (f := fun w => Axi.age R w • Axi.Nv R b τ w) 2 Axi.isOpen_compl_axis hyS]
    exact norm_iteratedFDerivWithin_smul_le hAgeS hNvS
      Axi.isOpen_compl_axis.uniqueDiffOn hyS (n := 2) (hjLe 2)
  have ht0 : 0 < 1 + |y 2| / Axi.ϱ y := by
    have : 0 ≤ |y 2| / Axi.ϱ y := div_nonneg (abs_nonneg _) hρ.le
    linarith
  have hterm : ∀ i ∈ Finset.range 3,
      (Nat.choose 2 i : ℝ) * ‖iteratedFDerivWithin ℝ i (Axi.age R) Axi.axisᶜ y‖ *
        ‖iteratedFDerivWithin ℝ (2 - i) (Axi.Nv R b τ) Axi.axisᶜ y‖ ≤
        2 * Ca * CN * (Axi.ϱ y ^ (-3 : ℝ) * (1 + |y 2| / Axi.ϱ y) ^ (-2 : ℝ)) := by
    intro i hi
    have hi2 : i ≤ 2 := by have := Finset.mem_range.1 hi; omega
    rw [iteratedFDerivWithin_of_isOpen i Axi.isOpen_compl_axis hyS,
      iteratedFDerivWithin_of_isOpen (2 - i) Axi.isOpen_compl_axis hyS]
    have h1 := hCa y hyax i hi2
    have h2 := nv_far_jet_of_resProfile hR1 hs0 hK0 hKb hb hbd τ hy (show 2 - i ≤ 2 by omega)
    have hch : (Nat.choose 2 i : ℝ) ≤ 2 := by
      interval_cases i <;> norm_num [Nat.choose]
    have hch0 : (0 : ℝ) ≤ (Nat.choose 2 i : ℝ) := Nat.cast_nonneg _
    have hr1 : 0 ≤ Ca * Axi.ϱ y ^ (-(2 + (i : ℝ))) :=
      mul_nonneg hCa0 (Real.rpow_nonneg hρ.le _)
    have hrp_eq : Axi.ϱ y ^ (-(2 + (i : ℝ))) * Axi.ϱ y ^ (-(1 + ((2 - i : ℕ) : ℝ))) =
        Axi.ϱ y ^ (-5 : ℝ) := by
      rw [← Real.rpow_add hρ]
      congr 1
      have : ((2 - i : ℕ) : ℝ) = 2 - (i : ℝ) := Nat.cast_sub hi2
      linarith
    have hrp_le : Axi.ϱ y ^ (-5 : ℝ) ≤ Axi.ϱ y ^ (-3 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hρ1 (by norm_num)
    calc (Nat.choose 2 i : ℝ) * ‖iteratedFDeriv ℝ i (Axi.age R) y‖ *
          ‖iteratedFDeriv ℝ (2 - i) (Axi.Nv R b τ) y‖
        ≤ 2 * (Ca * Axi.ϱ y ^ (-(2 + (i : ℝ)))) *
            (CN * Axi.ϱ y ^ (-(1 + ((2 - i : ℕ) : ℝ))) * (1 + |y 2| / Axi.ϱ y) ^ (-2 : ℝ)) :=
          mul_le_mul (mul_le_mul hch h1 (norm_nonneg _) (by norm_num)) h2 (norm_nonneg _)
            (mul_nonneg (by norm_num) hr1)
      _ = 2 * Ca * CN * ((Axi.ϱ y ^ (-(2 + (i : ℝ))) * Axi.ϱ y ^ (-(1 + ((2 - i : ℕ) : ℝ)))) *
            (1 + |y 2| / Axi.ϱ y) ^ (-2 : ℝ)) := by ring
      _ = 2 * Ca * CN * (Axi.ϱ y ^ (-5 : ℝ) * (1 + |y 2| / Axi.ϱ y) ^ (-2 : ℝ)) := by
          rw [hrp_eq]
      _ ≤ 2 * Ca * CN * (Axi.ϱ y ^ (-3 : ℝ) * (1 + |y 2| / Axi.ϱ y) ^ (-2 : ℝ)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hrp_le (Real.rpow_nonneg ht0.le _))
            (mul_nonneg (mul_nonneg (by norm_num) hCa0) hCN0)
  calc ‖iteratedFDeriv ℝ 2 (fun w => Axi.age R w • Axi.Nv R b τ w) y‖
      ≤ ∑ i ∈ Finset.range 3, (Nat.choose 2 i : ℝ) *
          ‖iteratedFDerivWithin ℝ i (Axi.age R) Axi.axisᶜ y‖ *
          ‖iteratedFDerivWithin ℝ (2 - i) (Axi.Nv R b τ) Axi.axisᶜ y‖ := hleib
    _ ≤ ∑ _ ∈ Finset.range 3,
          2 * Ca * CN * (Axi.ϱ y ^ (-3 : ℝ) * (1 + |y 2| / Axi.ϱ y) ^ (-2 : ℝ)) :=
        Finset.sum_le_sum hterm
    _ = 6 * Ca * CN * (Axi.ϱ y ^ (-3 : ℝ) * (1 + |y 2| / Axi.ϱ y) ^ (-2 : ℝ)) := by
        rw [Finset.sum_const, Finset.card_range]
        ring

end FarDecaySub

open FarDecaySub

/-- **`RawResidualD2FarDecay` from `ResProfileFarJet`** (source lines 2542-2548 at `k = 2`,
1287-1305). -/
theorem rawResidualD2FarDecay_of (h : ResProfileFarJet) : RawResidualD2FarDecay := by
  obtain ⟨ν₀, hν₀, H⟩ := h
  refine ⟨ν₀, hν₀, fun p htr hν hc hR hP j l => ?_⟩
  have hsm := resChartProfile_contDiffOn p htr
  obtain ⟨Cb, s0, hs0, hbd⟩ := H p htr hν hc hR hP
  obtain ⟨C, R0, hR0, hjet⟩ := age_smul_nv_far_jet2 hR hs0 hsm hbd
  refine ⟨C, R0, hR0, fun τ _ y hy => ?_⟩
  have hy' : R0 < Axi.ϱ y := hy
  have hρ : 0 < Axi.ϱ y := hR0.trans hy'
  have hyax : y ∉ Axi.axis := by
    intro hax
    rw [Axi.mem_axis_iff] at hax
    linarith
  have hU : IsOpen {z : ℝ × UnforcedLeray.Space | z.2 ∉ Axi.axis} :=
    Axi.isOpen_compl_axis.preimage continuous_snd
  have hRpos : 0 < p.R := by linarith
  have hGsm : ContDiffOn ℝ ∞ (rawResidualC p)
      {z : ℝ × UnforcedLeray.Space | z.2 ∉ Axi.axis} :=
    (age_smul_Nv_joint_contDiffOn p.R hRpos (resChartProfile p) hsm).congr
      (fun z hz => rawResidualC_eq_off_axis p htr hR z hz)
  have hsb := (sliceBridge CVec3 (rawResidualC p)
    {z : ℝ × UnforcedLeray.Space | z.2 ∉ Axi.axis} hU hGsm (τ, y) hyax j l j).2.1
  have hslice_eq : iteratedFDeriv ℝ 2 (fun w => rawResidualC p (τ, w)) y =
      iteratedFDeriv ℝ 2
        (fun w => efarRealCLI (Axi.age p.R w • Axi.Nv p.R (resChartProfile p) τ w)) y := by
    have hev : (fun w => rawResidualC p (τ, w)) =ᶠ[𝓝 y]
        (fun w => efarRealCLI (Axi.age p.R w • Axi.Nv p.R (resChartProfile p) τ w)) :=
      Filter.eventuallyEq_of_mem (Axi.isOpen_compl_axis.mem_nhds hyax)
        (fun w hw => rawResidualC_eq_off_axis p htr hR (τ, w) hw)
    exact (hev.iteratedFDeriv ℝ 2).eq_of_nhds
  have hrealS : ContDiffOn ℝ ∞
      (fun w => Axi.age p.R w • Axi.Nv p.R (resChartProfile p) τ w) Axi.axisᶜ := by
    have hAgeS : ContDiffOn ℝ ∞ (Axi.age p.R) Axi.axisᶜ :=
      contDiffOn_const.div (Axi.contDiffOn_ϱ.pow 2)
        (fun z hz => pow_ne_zero 2 (Axi.ϱ_ne_zero hz))
    have hgS : ContDiffOn ℝ ∞ (fun z => resChartProfile p (Axi.chart p.R τ z)) Axi.axisᶜ :=
      hsm.comp (clf_chart_contDiffOn p.R τ hRpos) (clf_chart_mapsTo p.R τ hRpos)
    have hNvS : ContDiffOn ℝ ∞ (Axi.Nv p.R (resChartProfile p) τ) Axi.axisᶜ := by
      have hEq : Axi.Nv p.R (resChartProfile p) τ =
          fun z => liftFactor p.R z (resChartProfile p (Axi.chart p.R τ z)) :=
        funext fun z => Nv_eq_liftFactor p.R (resChartProfile p) τ z
      rw [hEq]
      exact (clf_lift_contDiffOn p.R hRpos).clm_apply hgS
    exact hAgeS.smul hNvS
  have hiso := efar_realC_norm
    (fun w => Axi.age p.R w • Axi.Nv p.R (resChartProfile p) τ w) hrealS hyax 2
  calc ‖dy j (dy l (rawResidualC p)) (τ, y)‖
      ≤ ‖iteratedFDeriv ℝ 2 (fun w => rawResidualC p (τ, w)) y‖ := hsb
    _ = ‖iteratedFDeriv ℝ 2
          (fun w => Axi.age p.R w • Axi.Nv p.R (resChartProfile p) τ w) y‖ := by
        rw [hslice_eq, hiso]
    _ ≤ C * (Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ^ (-3 : ℝ) *
          (1 + |y 2| / Real.sqrt (y 0 ^ 2 + y 1 ^ 2)) ^ (-2 : ℝ)) := hjet τ y hy'

end UnforcedLeray.Short.PartIIIb.Concrete
