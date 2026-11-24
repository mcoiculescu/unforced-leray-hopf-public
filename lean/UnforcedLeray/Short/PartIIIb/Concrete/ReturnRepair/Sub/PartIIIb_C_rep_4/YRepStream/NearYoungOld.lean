import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.LateEarly
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.Window
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AsymNuEps
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.MaskedSupport
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.BoxDenseZ
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.StressKernelRealization
import UnforcedLeray.Short.PartIIIb.NearInst.Proofs.NearSolver
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Agree
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnOps.ChiOStrApply

/-!
# `PartIII-b:C/rep/4/4/1/org/4`: the young-old rectangle lies in the far mask

Source `the November 2 reference manuscript` 5303-5306, 3902-3920 (`S_N = S_ε -
S_far`, far mask `s < S`, `t > e^δ s`), 4163-4166 (`χ_o = 0` for `s ≤ 1.2/ν`, `χ_y = 0` for
`s ≥ 1/ν`).  For large `n` one has `1/ν ≤ S = ε^{-b}`, `ρ_b ≤ 1`, `e^δ/ν < 1.2/ν`; the stress `χ_oT`
is supported in `s ≥ e^δ/ν`, and by the masked support bound the near output vanishes on
`s < 1/ν`, where alone `χ_y` is nonzero.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Short.PartIIIb.NearInst.Delta
  UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Blueprint.Planar

/-- `maskedSupport_of` (source 3905-3912) under the window hypothesis `μ > -1/4` of the stress kernel
realization instead of `μ > 0` (the only use of `μ` is `hK`). -/
theorem maskedSupport_quarter (hK : StressKernelRealization) (hD : BoxDenseZ)
    (p : Params) (mZ ρb μ δ S T : ℝ) (hmZ : 0 ≤ mZ) (hρ : 0 < ρb) (hρ1 : ρb ≤ 1)
    (hμ : -(1 / 4) < μ) (hδ : 0 < δ) (hT : 0 < T) (hTS : T ≤ S)
    (Seps Sf : Zsp p.c mZ ρb →L[ℝ] Hsp p.c) (hpair : IsMaskedPair p μ δ S Seps Sf) :
    outRestr p.c (ageBelow T) ∘L (Seps - Sf) ∘L
          inRestr p.c mZ ρb (ageAbove (Real.exp δ * T)) = 0 := by
  obtain ⟨⟨Seps', hstress, htrans⟩, hfar⟩ := hpair
  have hX : ‖outRestr p.c (ageBelow T) ∘L (Seps - Sf) ∘L
      inRestr p.c mZ ρb (ageAbove (Real.exp δ * T))‖ ≤ 0 := by
    refine opNorm_le_of_box hD p.c_pos hmZ hρ hρ1 _ le_rfl ?_
    intro F f hf hFf
    have hA : MeasurableSet (ageAbove (Real.exp δ * T)) :=
      measurableSet_le measurable_const measurable_fst
    have hfA : IsBoxTensor ((ageAbove (Real.exp δ * T)).indicator f) :=
      UnforcedLeray.Short.PartIIIb.NearInst.Masked.IsBoxTensor.indicator hf hA
    have hGz : zsum (inRestr p.c mZ ρb (ageAbove (Real.exp δ * T)) F) =ᵐ[ageμ p.c (-1 / 2)]
        (ageAbove (Real.exp δ * T)).indicator f := by
      filter_upwards [zsum_inRestr_ae hmZ hρ (ageAbove (Real.exp δ * T)) hA F, hFf] with x h1 h2
      rw [h1, h2]
      by_cases hx : x ∈ ageAbove (Real.exp δ * T)
      · simp [ind, Set.indicator_of_mem hx]
      · simp [ind, Set.indicator_of_notMem hx]
    have hSeps := hK p.ν p.ε p.c p.period p.ν_pos p.ε_pos p.c_pos rfl μ
      hμ mZ ρb Seps' Seps hstress htrans _ _ hfA hGz
    have hSf := (isFarMask_iff p.R p.ν μ δ S Sf).1 hfar _ _ hfA hGz
    have hBelow : MeasurableSet (ageBelow T) := measurableSet_lt measurable_fst measurable_const
    have hf' : ∀ q : Chart, q.1 < Real.exp δ * T →
        (ageAbove (Real.exp δ * T)).indicator f q = 0 := by
      intro q hq
      exact Set.indicator_of_notMem (show q ∉ ageAbove (Real.exp δ * T) from fun h => not_le.2 hq h) f
    have hres : (outRestr p.c (ageBelow T) ((Seps - Sf) (inRestr p.c mZ ρb
        (ageAbove (Real.exp δ * T)) F)) : Chart → Merid) =ᵐ[ageμ p.c (-3 / 2)]
        (ageBelow T).indicator (fun _ => (1 : ℝ)) • ((Seps - Sf) (inRestr p.c mZ ρb
          (ageAbove (Real.exp δ * T)) F) : Chart → Merid) :=
      restrLp_ae hBelow _
    have hzero : ((outRestr p.c (ageBelow T) ∘L (Seps - Sf) ∘L
        inRestr p.c mZ ρb (ageAbove (Real.exp δ * T))) F : Chart → Merid) =ᵐ[ageμ p.c (-3 / 2)]
        (0 : Chart → Merid) := by
      simp only [ContinuousLinearMap.comp_apply]
      filter_upwards [hres, hSeps, hSf, Lp.coeFn_sub
        (Seps (inRestr p.c mZ ρb (ageAbove (Real.exp δ * T)) F))
        (Sf (inRestr p.c mZ ρb (ageAbove (Real.exp δ * T)) F))] with x h1 h2 h3 h4
      rw [h1]
      simp only [Pi.zero_apply]
      change (ageBelow T).indicator (fun _ => (1 : ℝ)) x • ((Seps - Sf) (inRestr p.c mZ ρb
          (ageAbove (Real.exp δ * T)) F) : Chart → Merid) x = 0
      by_cases hx : x ∈ ageBelow T
      · have hxT : x.1 < T := hx
        rw [Set.indicator_of_mem hx, one_smul, ContinuousLinearMap.sub_apply, h4, Pi.sub_apply,
          h2, h3, farOut_eq_fullOut_of_lt (R := p.R) hδ hTS _ hf' x hxT]
        exact sub_eq_zero.mpr rfl
      · rw [Set.indicator_of_notMem hx, zero_smul]
    rw [eLpNorm_congr_ae hzero, eLpNorm_zero]
    simp
  exact norm_le_zero_iff.1 hX


end UnforcedLeray.Short.PartIIIb.NearInst.Masked

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Short.PartIIIb.NearInst.Delta
open UnforcedLeray.Blueprint.Planar (PlanarData)

/-- `χ_oT` is supported in `s ≥ t₀` as an element of `Z` whenever `ν s ≤ 6/5` for `s < t₀`
(source 4163-4166): `1_{s ≥ t₀}` acts as the identity on `g⁻¹ χ_oT`. -/
theorem inRestr_chiO {c mZ ρb γ ν : ℝ} {χ : ℝ → ℝ} (hχ : IsOutwardCutoff χ) (hρ : 0 < ρb)
    (hν : 0 < ν) (t₀ : ℝ) (hs : ∀ p : Chart, p.1 < t₀ → ν * p.1 ≤ 6 / 5)
    (T : StrG c mZ ρb γ ν) :
    inRestr c mZ ρb (ageAbove t₀)
        (gainEquiv c mZ ρb γ hν (strIso c mZ ρb γ ν (chiOStr c mZ ρb γ ν hχ T))) =
      gainEquiv c mZ ρb γ hν (strIso c mZ ρb γ ν (chiOStr c mZ ρb γ ν hχ T)) := by
  set X := chiOStr c mZ ρb γ ν hχ T with hX
  set F := gainEquiv c mZ ρb γ hν (strIso c mZ ρb γ ν X) with hF
  have hA : MeasurableSet (ageAbove t₀) := measurableSet_le measurable_const measurable_fst
  have happ := chiOStrApply c mZ ρb γ ν χ hχ T
  have a1 := happ.1
  have a2 := happ.2
  have b1 := coeFn_zOfStr_fst (c := c) (mZ := mZ) (ρb := ρb) γ hν X
  have b2 := coeFn_zOfStr_snd (c := c) (mZ := mZ) (ρb := ρb) γ hν X
  rw [NearInst.ae_gainZ1Measure] at a1
  rw [NearInst.ae_gainHTMeasure] at a2
  have hz : ∀ p : Chart, p ∉ ageAbove t₀ → cutFun χ ν p = 0 := fun p hp =>
    hχ.zero _ (hs p (not_le.1 hp))
  apply (zEquiv c mZ ρb).injective
  rw [zEquiv_inRestr]
  refine Prod.ext ?_ ?_
  · apply Lp.ext
    show (restrLp (z1Measure c mZ) Ten3 (ageAbove t₀) F.fst : Chart → Ten3) =ᵐ[z1Measure c mZ] F.fst
    filter_upwards [restrLp_ae hA F.fst, b1, a1] with p e1 e2 e3
    rw [e1]
    show ind (ageAbove t₀) p • (F.fst : Chart → Ten3) p = (F.fst : Chart → Ten3) p
    by_cases hp : p ∈ ageAbove t₀
    · simp [ind, Set.indicator_of_mem hp]
    · have h0 := hz p hp
      have : (F.fst : Chart → Ten3) p = 0 := by rw [e2, e3]; simp [h0]
      simp [this]
  · apply Lp.ext
    show (restrLp (htRhoMeasure c ρb) Ten3 (ageAbove t₀) F.snd : Chart → Ten3)
      =ᵐ[htRhoMeasure c ρb] F.snd
    filter_upwards [restrLp_ae hA F.snd, b2, a2] with p e1 e2 e3
    rw [e1]
    show ind (ageAbove t₀) p • (F.snd : Chart → Ten3) p = (F.snd : Chart → Ten3) p
    by_cases hp : p ∈ ageAbove t₀
    · simp [ind, Set.indicator_of_mem hp]
    · have h0 := hz p hp
      have : (F.snd : Chart → Ten3) p = 0 := by rw [e2, e3]; simp [h0]
      simp [this]

/-- `1/ν ≤ e^{a/ν}` for `ν ≤ a²/2`, `a = b d₋` (the output cut `S = ε^{-b}` exceeds `1/ν`). -/
theorem inv_le_exp_of_small {ν a : ℝ} (hν : 0 < ν) (ha : 0 < a) (h : ν ≤ a ^ 2 / 2) :
    1 / ν ≤ Real.exp (a / ν) := by
  have hx : 0 ≤ a / ν := by positivity
  have h1 := Real.quadratic_le_exp_of_nonneg hx
  have h2 : 1 / ν ≤ (a / ν) ^ 2 / 2 := by
    rw [div_pow, div_div, div_le_div_iff₀ hν (by positivity)]
    nlinarith [sq_nonneg ν]
  linarith [sq_nonneg (a / ν)]

/-- The output cut is at least `1/ν` on an actual level of small viscosity. -/
theorem scut_ge_inv (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) {dm dp : ℝ}
    (hb : 0 < K.b)
    (hreg : UnforcedLeray.Short.IIb.BgRegime (L.params Pl) (-L.ν * Real.log L.ε) dm dp)
    (hν : L.ν ≤ (K.b * dm) ^ 2 / 2) : 1 / L.ν ≤ L.Scut K := by
  have hν0 : 0 < L.ν := L.ν_pos
  have hdm : 0 < dm := hreg.dm_pos
  have hdle := hreg.dm_le
  have hε : L.ε = Real.exp (-(-L.ν * Real.log L.ε) / L.ν) := hreg.eps_eq
  set d := -L.ν * Real.log L.ε with hd
  have hS : L.Scut K = Real.exp (K.b * d / L.ν) := by
    unfold ReturnLevel.Scut
    rw [Real.rpow_def_of_pos L.ε_pos]
    have : Real.log L.ε = -d / L.ν := by
      conv_lhs => rw [hε]
      rw [Real.log_exp]
    rw [this]
    congr 1
    ring
  rw [hS]
  refine (inv_le_exp_of_small hν0 (mul_pos hb hdm) hν).trans (Real.exp_le_exp.2 ?_)
  have : K.b * dm / L.ν ≤ K.b * d / L.ν :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hdle hb.le) hν0.le
  exact this

/-- **The young-old rectangle lies in the far mask at one regime** (source 5303-5306). -/
theorem nyo_core (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)
    (hχy : IsStreamCutoff K.χy) (hμ : -(1 / 4) < μ) (hmZ : 0 ≤ K.mZ) (hρ : 0 < L.ρb Pl K)
    (hρ1 : L.ρb Pl K ≤ 1) (hδ : 0 < K.δ) (hδ2 : K.δ < Real.log (12 / 11))
    (hS : 1 / L.ν ≤ L.Scut K)
    (hnear : ∃ o : NearInst.NearOps (cOf L.ν) K.mZ (L.ρb Pl K),
      NearInst.IsActualNear (L.params Pl) L.V L.rb μ K.δ (L.Scut K) o) :
    NearYoungOldAt Pl K L μ hχy := by
  intro T
  have hν : 0 < L.ν := L.ν_pos
  obtain ⟨ho, -⟩ := nearOpsAt_spec hnear
  set o := nearOpsAt Pl K L μ with hodef
  obtain ⟨Seps, Sf, Seps', hstress, htrans, hfar, hSN⟩ := ho.near
  have hpair : NearInst.Masked.IsMaskedPair (L.params Pl) μ K.δ (L.Scut K) Seps Sf :=
    ⟨⟨Seps', hstress, htrans⟩, hfar⟩
  have hT0 : 0 < 1 / L.ν := by positivity
  have hms := NearInst.Masked.maskedSupport_quarter NearInst.Masked.stressKernelRealization
    NearInst.Masked.boxDenseZ (L.params Pl) K.mZ (L.ρb Pl K) μ K.δ (L.Scut K) (1 / L.ν) hmZ hρ hρ1
    hμ hδ hT0 hS Seps Sf hpair
  set X := chiOStr (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν K.hχo T with hX
  set F := gainEquiv (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) hν
    (strIso (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν X) with hF
  have hexp : Real.exp K.δ < 12 / 11 := by
    have := Real.exp_lt_exp.2 hδ2
    rwa [Real.exp_log (by norm_num)] at this
  have hin : NearInst.Delta.inRestr (cOf L.ν) K.mZ (L.ρb Pl K)
      (NearInst.Delta.ageAbove (Real.exp K.δ * (1 / L.ν))) F = F := by
    refine inRestr_chiO K.hχo hρ hν _ ?_ T
    intro p hp
    have h1 : L.ν * p.1 < L.ν * (Real.exp K.δ * (1 / L.ν)) := mul_lt_mul_of_pos_left hp hν
    have h2 : L.ν * (Real.exp K.δ * (1 / L.ν)) = Real.exp K.δ := by field_simp
    rw [h2] at h1
    linarith
  have hout : NearInst.Delta.outRestr (cOf L.ν) (NearInst.Delta.ageBelow (1 / L.ν)) (o.SN F) = 0 := by
    have h : NearInst.Delta.outRestr (cOf L.ν) (NearInst.Delta.ageBelow (1 / L.ν))
        ((Seps - Sf) (NearInst.Delta.inRestr (cOf L.ν) K.mZ (L.ρb Pl K)
          (NearInst.Delta.ageAbove (Real.exp K.δ * (1 / L.ν))) F)) = 0 := DFunLike.congr_fun hms F
    rw [hin] at h
    rw [hSN]
    exact h
  have hBelow : MeasurableSet (NearInst.Delta.ageBelow (1 / L.ν)) :=
    NearInst.Delta.measurableSet_ageBelow _
  have hres : (NearInst.Delta.outRestr (cOf L.ν) (NearInst.Delta.ageBelow (1 / L.ν)) (o.SN F) :
      Chart → Merid) =ᵐ[ageμ (cOf L.ν) (-3 / 2)]
      NearInst.Delta.ind (NearInst.Delta.ageBelow (1 / L.ν)) • (o.SN F : Chart → Merid) :=
    NearInst.Delta.restrLp_ae hBelow _
  rw [hout] at hres
  have hsn : (SNop Pl K L μ X : Chart → Merid) =ᵐ[ageμ (cOf L.ν) (-3 / 2)]
      (o.SN F : Chart → Merid) := NearInst.coeFn_SNG o (gRate Pl) hν X
  have hym := youngMul_ae hχy (SNop Pl K L μ X)
  rw [NearInst.ae_bodyMeasure] at hym
  apply Lp.ext
  have e4 := Lp.coeFn_zero (E := Merid) 2 (bodyMeasure (cOf L.ν) (gRate Pl) L.ν)
  rw [NearInst.ae_bodyMeasure] at e4
  rw [NearInst.ae_bodyMeasure]
  filter_upwards [hym, hsn, hres, e4, Lp.coeFn_zero (E := Merid) 2 (ageμ (cOf L.ν) (-3 / 2))]
    with p e1 e2 e3 e5 e6
  show (youngMul hχy (SNop Pl K L μ X) : Chart → Merid) p = (0 : LVel Pl L) p
  rw [e1, e5]
  simp only [Pi.zero_apply, Pi.smul_apply]
  by_cases hp : p.1 < 1 / L.ν
  · have hz : (o.SN F : Chart → Merid) p = 0 := by
      have hi : NearInst.Delta.ind (NearInst.Delta.ageBelow (1 / L.ν)) p = 1 := by
        unfold NearInst.Delta.ind
        exact Set.indicator_of_mem (show p ∈ NearInst.Delta.ageBelow (1 / L.ν) from hp) _
      have h4 := e6.symm.trans e3
      rw [Pi.smul_apply', hi, one_smul] at h4
      exact h4.symm
    rw [e2, hz, smul_zero]
  · have h1 : 1 ≤ L.ν * p.1 := by
      rw [not_lt, div_le_iff₀ hν] at hp
      linarith
    have : cutFun K.χy L.ν p = 0 := hχy.zero _ h1
    rw [this, zero_smul]

/-- **`NearYoungOld`** (source 5303-5306): for large `n` and `z ∈ [-1,1]` the young-old rectangle
`χ_yS_Nχ_o` vanishes. -/
theorem nearYoungOld (dm dp : ℝ) : NearYoungOld dm dp := by
  intro D hst
  obtain ⟨ν₂, hν₂, hrho⟩ :=
    NearInst.ns_rhoB_le D.K.m0 D.K.C0 dm dp D.K.k0 hst.C0_pos hst.m0_lt
  have hdm : 0 < dm := hst.dm_pos
  have hapos : 0 < D.K.b * dm := mul_pos hst.b_pos hdm
  have hlim : 0 < min ν₂ ((D.K.b * dm) ^ 2 / 2) := lt_min hν₂ (by positivity)
  have hsmall : ∀ᶠ n : ℕ in atTop, retNu D.Pl D.σ₀ n ≤ min ν₂ ((D.K.b * dm) ^ 2 / 2) :=
    Filter.Tendsto.eventually_le_const hlim (retNu_tendsto D.σ₀ hst.omega_ne)
  filter_upwards [hst.actual, hst.pins, muWin_gt_quarter D hst, hsmall] with n hact hpins hmu hs
  intro z hz
  have hreg := hact.regime
  have hνn : (D.level n).ν ≤ ν₂ := hs.trans (min_le_left _ _)
  have hνa : (D.level n).ν ≤ (D.K.b * dm) ^ 2 / 2 := hs.trans (min_le_right _ _)
  exact nyo_core D.Pl D.K (D.level n) (D.mu n z) hst.chiY (hmu z hz)
    (by linarith [hst.mZ_gt])
    (NearInst.ns_rhoB_pos ((D.level n).params D.Pl) D.K.m0 D.K.C0 D.K.k0 hst.C0_pos)
    (hrho _ _ hreg hνn) hst.δ_pos hst.δ_lt (scut_ge_inv D.Pl D.K (D.level n) hst.b_pos hreg hνa)
    (hpins z hz).near

end UnforcedLeray.Short.PartIIIb.Concrete
