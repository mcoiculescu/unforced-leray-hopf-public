import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.LateRepThinOrg.Props
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.EarlyRepThin.Kernel.ThinRecv
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AsymMu
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AsymNuEps

/-!
# `PartIII-b:C/rep/4/4/1/org/5/1/org` (b): far-mask outputs on the ungained thin receiver

Source `the November 2 reference manuscript` 5337-5338 ("the repair-to-thin entry
uses the pointwise exponent `79/22`, followed by `ρR`"), 3631-3647 (`sep:young`, pointwise version
`q = ∞`, `b = p'`; `p = 22/19`, `j = 0`: `D^{-4+9/22} = D^{-79/22}`), 3611-3621 (`sep:resolvent`),
3902-3912 (far mask `s < S`, `t > e^δs`: gap `(1-e^{-δ/2})R/√s` at output age `s`), 2713-2721
(`stress-short:coefficients`, `‖Wv(s)‖_{L²_ηL^∞_q} ≤ P_ν[(1+s)^{-3/4}+ε(1+s)^{-1/4}]`), 2758-2772
(`(M_Ub)₁ = v⊗b+b⊗v`), 2697 (`Z₁ = L²(W²s^{-1/2}dς)`), 5345-5352 ("after the normalized velocity
lift and thin multiplication, the square root of the output stress age density is bounded by
`P_ν … V_m(s) …`; its square is integrable at zero, and the integral up to `S` is polynomial in
`S`").

`FarThinRecvUng`: for a far-kernel output `v = farOut f` at a standing level,
`‖(M_Uv)₁‖_{Z₁} ≤ P_νS^{k₀}ε^{79/22}‖𝒩_Tf‖_{L²_τL^{22/19}}` in the **ungained** `Z₁` norm, on all
output ages (no cutoff `χ_y`, no gain `g⁻¹`).  Proved here (`farThinRecvUng_of`) from the generic
leaves of `PartIII-b:C/rep/4/4/1/org/7/1/org` (`EarlyRepThin/Kernel/ThinRecv.lean`):

* the thin multiplier on all ages (`frk_thinMultUng_level`, proved here from the exact-multiplier
  pin `concreteBase_isExactMultiplier`): `‖(M_Uv)₁‖²_{Z₁} = ∫W²|(M_Uv)₁|²s^{-1/2}dς` and a.e.
  `W²|(M_Uv)₁|² ≤ 4W²|v_V|²|v|²`;
* `FarOutChartQ` (Tonelli, `L^∞_q × L²_q`, one cell is one phase period), `FarOutPointwise`
  (`sep:young` pointwise on the masked source), `EtaQSupSeq` (the coefficient bound of 2717),
  `FarRecvIntegral` (`∫_0^S s^{23/11}ds ≤ S^{34/11}`).

Then `K = (1-e^{-δ/2})ε⁻¹`: `K^{-79/22} = (1-e^{-δ/2})^{-79/22}ε^{79/22}` and
`S^{17/11} = ε^{-17b/11} ≤ ε^{-2b}` (`k₀ = 2`, `ε ≤ 1`).

`FarThinRecvUng` is stronger than the gained young-output receiver `FarThinRecv` of
`EarlyRepThin/Kernel/ThinRecv.lean` (`farThinRecv_of_ung`, proved here: `χ_y` commutes with `M_U`
and `|χ_y| ≤ 1`, `g⁻¹ ≤ 1`).
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open UnforcedLeray.Blueprint.Planar (PlanarData)
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-! ## 1. The thin multiplier on all output ages -/

theorem frk_measurable_transWeight (mZ : ℝ) :
    Measurable (UnforcedLeray.Short.IIIa.transWeight mZ) := by
  unfold UnforcedLeray.Short.IIIa.transWeight
  fun_prop

theorem frk_enorm_sq {E : Type*} [SeminormedAddCommGroup E] (x : E) :
    ‖x‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (‖x‖ ^ 2) := by
  rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num),
    Real.rpow_two]

/-- **The thin multiplier, ungained, on all ages** (source 2758-2772, 4147, 5779-5782: `(M_Uu)₁ =
v⊗u + u⊗v`, `v = s^{-1/2}V`; 2697 `Z₁ = L²(W²s^{-1/2}dς)`): at a level with the near operators and
the split multiplier, for every velocity `v`, `‖(M_Uv)₁‖_{Z₁} = (∫W²|(M_Uv)₁|²s^{-1/2}dς)^{1/2}`
and a.e. `W²|(M_Uv)₁|² ≤ 4W²|v_V|²|v|²`. -/
theorem frk_thinMultUng_level (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)
    (hnear : NearAt Pl K L μ)
    (hs : ∃ M : Hsp (cOf L.ν) →L[ℝ] Zsp (cOf L.ν) K.mZ (L.ρb Pl K),
      NearInst.IsSplitMult M (L.params Pl).R L.V L.rb) (v : LVel Pl L) :
    z1Ung (cOf L.ν) K.mZ ((multOp Pl K L v).fst : Chart → Ten3) =
        (∫⁻ p, ENNReal.ofReal (UnforcedLeray.Short.IIIa.transWeight K.mZ p ^ 2) *
          ‖((multOp Pl K L v).fst : Chart → Ten3) p‖ₑ ^ (2 : ℝ) ∂(ageμ (cOf L.ν) (-1 / 2))) ^
          (1 / 2 : ℝ) ∧
      ∀ᵐ p ∂(ageμ (cOf L.ν) (-1 / 2)),
        ENNReal.ofReal (UnforcedLeray.Short.IIIa.transWeight K.mZ p ^ 2) *
            ‖((multOp Pl K L v).fst : Chart → Ten3) p‖ₑ ^ (2 : ℝ) ≤
          4 * (ENNReal.ofReal (UnforcedLeray.Short.IIIa.transWeight K.mZ p ^ 2 *
            ‖UnforcedLeray.Short.IIIa.chartCoeff L.ε⁻¹ L.V p‖ ^ 2) *
              ‖(v : Chart → Merid) p‖ₑ ^ (2 : ℝ)) := by
  refine ⟨?_, ?_⟩
  · unfold z1Ung z1Measure
    rw [lintegral_withDensity_eq_lintegral_mul _
      ((frk_measurable_transWeight K.mZ).pow_const 2).ennreal_ofReal
      ((Lp.stronglyMeasurable _).measurable.enorm.pow_const _)]
    rfl
  · have hEx : IsExactMultiplier (concreteBase Pl K L μ hnear) L.ε⁻¹ L.V L.rb :=
      concreteBase_isExactMultiplier (h := hnear) NearInst.multPinOfLink hs
    have h1 : ((multOp Pl K L v).fst : Chart → Ten3) =ᵐ[gainZ1Measure (cOf L.ν) K.mZ
        (gRate Pl) L.ν] fun p => NearInst.ten3Of (UnforcedLeray.Short.IIIa.symOuter
          (UnforcedLeray.Short.IIIa.chartCoeff L.ε⁻¹ L.V p) ((v : Chart → Merid) p)) :=
      (hEx v).1
    rw [Filter.EventuallyEq, NearInst.ae_gainZ1Measure, NearInst.ae_z1Measure] at h1
    filter_upwards [h1] with p hp
    rw [hp]
    set W := UnforcedLeray.Short.IIIa.transWeight K.mZ p
    set a := UnforcedLeray.Short.IIIa.chartCoeff L.ε⁻¹ L.V p
    set b := (v : Chart → Merid) p
    have key : W ^ 2 * ‖NearInst.ten3Of (UnforcedLeray.Short.IIIa.symOuter a b)‖ ^ 2 ≤
        4 * (W ^ 2 * ‖a‖ ^ 2 * ‖b‖ ^ 2) := by
      rw [NearInst.CoeffMult.norm_sq_ten3Of]
      calc W ^ 2 * UnforcedLeray.Short.IIIa.frobSq (UnforcedLeray.Short.IIIa.symOuter a b)
          ≤ W ^ 2 * (4 * ‖a‖ ^ 2 * ‖b‖ ^ 2) :=
            mul_le_mul_of_nonneg_left (NearInst.CoeffMult.frobSq_symOuter_le' a b) (sq_nonneg _)
        _ = 4 * (W ^ 2 * ‖a‖ ^ 2 * ‖b‖ ^ 2) := by ring
    calc ENNReal.ofReal (W ^ 2) *
          ‖NearInst.ten3Of (UnforcedLeray.Short.IIIa.symOuter a b)‖ₑ ^ (2 : ℝ)
        = ENNReal.ofReal (W ^ 2 *
            ‖NearInst.ten3Of (UnforcedLeray.Short.IIIa.symOuter a b)‖ ^ 2) := by
          rw [frk_enorm_sq, ENNReal.ofReal_mul (sq_nonneg _)]
      _ ≤ ENNReal.ofReal (4 * (W ^ 2 * ‖a‖ ^ 2 * ‖b‖ ^ 2)) := ENNReal.ofReal_le_ofReal key
      _ = 4 * (ENNReal.ofReal (W ^ 2 * ‖a‖ ^ 2) * ‖b‖ₑ ^ (2 : ℝ)) := by
          rw [frk_enorm_sq, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by positivity)]
          norm_num

/-! ## 2. Norm and arithmetic bookkeeping -/

/-- The mixed norm of `sep:young` on the lifted source is the phase norm `phaseL2Lr`. -/
theorem frk_ltauLq_eq (P q R c : ℝ) (hP : 0 < P) (f : Chart → Ten3) :
    UnforcedLeray.Short.IIIa.ltauLq P q
        (UnforcedLeray.Short.IIIa.srcNorm (NearInst.cartLift R c f)) =
      phaseL2Lr P q (strPhys R c f) := by
  unfold UnforcedLeray.Short.IIIa.ltauLq phaseL2Lr
  rw [ENNReal.ofReal_inv_of_pos hP]
  rfl

/-- `I ≤ 2·4·X·F²` gives `I^{1/2} ≤ √(8X)·F`. -/
theorem frk_sqrt_bound {I F : ℝ≥0∞} {X : ℝ} (hX : 0 ≤ X)
    (h : I ≤ 2 * 4 * (ENNReal.ofReal X * F ^ (2 : ℝ))) :
    I ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal (Real.sqrt (8 * X)) * F := by
  have e : 2 * 4 * (ENNReal.ofReal X * F ^ (2 : ℝ)) =
      (ENNReal.ofReal (Real.sqrt (8 * X)) * F) ^ (2 : ℝ) := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
      ENNReal.ofReal_rpow_of_nonneg (Real.sqrt_nonneg _) (by norm_num), Real.rpow_two,
      Real.sq_sqrt (by positivity), ENNReal.ofReal_mul (by norm_num)]
    have h8 : ENNReal.ofReal 8 = 2 * 4 := by
      rw [show (8 : ℝ) = 2 * 4 by norm_num, ENNReal.ofReal_mul (by norm_num)]
      norm_num
    rw [h8]; ring
  calc I ^ (1 / 2 : ℝ) ≤ ((ENNReal.ofReal (Real.sqrt (8 * X)) * F) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow (h.trans e.le) (by norm_num)
    _ = ENNReal.ofReal (Real.sqrt (8 * X)) * F := by
        rw [← ENNReal.rpow_mul]; norm_num

/-- `√(8E²C²K^{-79/11}S^{34/11}) = √8·E·C·K^{-79/22}S^{17/11}`. -/
theorem frk_sqrt_eq {E C K S : ℝ} (hE : 0 ≤ E) (hC : 0 ≤ C) (hK : 0 < K) (hS : 0 < S) :
    Real.sqrt (8 * (E ^ 2 * C ^ 2 * K ^ (-(79 / 11 : ℝ)) * S ^ (34 / 11 : ℝ))) =
      Real.sqrt 8 * E * C * K ^ (-(79 / 22 : ℝ)) * S ^ (17 / 11 : ℝ) := by
  have eK : K ^ (-(79 / 11 : ℝ)) = (K ^ (-(79 / 22 : ℝ))) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hK.le]; norm_num
  have eS : S ^ (34 / 11 : ℝ) = (S ^ (17 / 11 : ℝ)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hS.le]; norm_num
  have e8 : (8 : ℝ) = Real.sqrt 8 ^ 2 := (Real.sq_sqrt (by norm_num)).symm
  rw [eK, eS]
  nth_rewrite 1 [e8]
  have h0 : 0 ≤ Real.sqrt 8 * E * C * K ^ (-(79 / 22 : ℝ)) * S ^ (17 / 11 : ℝ) := by positivity
  rw [← Real.sqrt_sq h0]
  congr 1
  ring

/-- `√8·(Cν^{-k})·C'·((κε⁻¹)^{-79/22})·(ε^{-b})^{17/11} ≤ (√8CC'κ^{-79/22})ν^{-k}ε^{-2b}ε^{79/22}`
for `0 < ε ≤ 1`, `b ≥ 0`. -/
theorem frk_const_le {CE CP κ ε ν b : ℝ} {kE : ℕ} (hCE : 0 ≤ CE) (hCP : 0 ≤ CP) (hκ : 0 < κ)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hν : 0 < ν) (hb : 0 ≤ b) :
    Real.sqrt 8 * (CE * ν⁻¹ ^ kE) * CP * (κ * ε⁻¹) ^ (-(79 / 22 : ℝ)) *
        (ε ^ (-b)) ^ (17 / 11 : ℝ) ≤
      Real.sqrt 8 * CE * CP * κ ^ (-(79 / 22 : ℝ)) * ν⁻¹ ^ kE *
        ε ^ (-(((2 : ℕ) : ℝ) * b)) * ε ^ (79 / 22 : ℝ) := by
  rw [Real.mul_rpow hκ.le (inv_nonneg.2 hε.le), Real.inv_rpow hε.le, Real.rpow_neg hε.le,
    inv_inv, ← Real.rpow_mul hε.le]
  have hA : 0 ≤ Real.sqrt 8 * CE * CP * κ ^ (-(79 / 22 : ℝ)) * ν⁻¹ ^ kE *
      ε ^ (79 / 22 : ℝ) := by positivity
  have hle : ε ^ (-b * (17 / 11 : ℝ)) ≤ ε ^ (-(((2 : ℕ) : ℝ) * b)) :=
    Real.rpow_le_rpow_of_exponent_ge hε hε1 (by push_cast; nlinarith)
  calc Real.sqrt 8 * (CE * ν⁻¹ ^ kE) * CP * (κ ^ (-(79 / 22 : ℝ)) * ε ^ (79 / 22 : ℝ)) *
        ε ^ (-b * (17 / 11 : ℝ))
      = (Real.sqrt 8 * CE * CP * κ ^ (-(79 / 22 : ℝ)) * ν⁻¹ ^ kE * ε ^ (79 / 22 : ℝ)) *
          ε ^ (-b * (17 / 11 : ℝ)) := by ring
    _ ≤ (Real.sqrt 8 * CE * CP * κ ^ (-(79 / 22 : ℝ)) * ν⁻¹ ^ kE * ε ^ (79 / 22 : ℝ)) *
          ε ^ (-(((2 : ℕ) : ℝ) * b)) := mul_le_mul_of_nonneg_left hle hA
    _ = _ := by ring

/-! ## 3. The ungained receiver bound -/

/-- **Far-mask outputs on the ungained thin receiver** (source 5337-5338, 3647, 2713-2721,
5345-5352, 3902-3912, 2697): with the S-degree `k₀` chosen before `D` (before `b`), for a
standing sequence there are `C ≥ 0`, `k` with, for large `n`, `z ∈ [-1,1]`, every velocity `v` and
measurable chart tensor `f` with `v = farOut f` a.e. (the far kernel of level `n`: `R = ε⁻¹`,
`c = ν⁻²`, gap `δ`, cut `S = ε^{-b}`),
`‖(M_Uv)₁‖_{Z₁} ≤ Cν^{-k}ε^{-k₀b}ε^{79/22}‖𝒩_Tf‖_{L²_τL^{22/19}}` (ungained `Z₁`, all output ages,
period `2εc`). -/
def FarThinRecvUng (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) : Prop :=
  ∃ k₀ : ℕ, ∀ D : SeqData, D.Pl = Pl → D.σ₀ = σ₀ → D.K.mZ = mZ →
    ∀ _hst : D.RepairStanding dm dp, ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧
      ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1, ∀ (v : LVel D.Pl (D.level n)) (f : Chart → Ten3),
        Measurable f →
        (v : Chart → Merid) =ᵐ[ageμ (cOf (D.level n).ν) (-3 / 2)]
          NearInst.Masked.farOut (D.level n).ε⁻¹ (cOf (D.level n).ν) (D.level n).ν (D.mu n z)
            D.K.δ ((D.level n).Scut D.K) f →
        z1Ung (cOf (D.level n).ν) D.K.mZ
            ((multOp D.Pl D.K (D.level n) v).fst : Chart → Ten3) ≤
          ENNReal.ofReal (C * (D.level n).ν⁻¹ ^ k * (D.level n).ε ^ (-((k₀ : ℝ) * D.K.b)) *
              (D.level n).ε ^ (79 / 22 : ℝ)) *
            phaseL2Lr (2 * (D.level n).ε * cOf (D.level n).ν) (22 / 19)
              (strPhys (D.level n).ε⁻¹ (cOf (D.level n).ν) f)

/-- **(b) from the generic receiver leaves** (source 5337-5338, 5345-5352, 2713-2721, 3631-3647):
`k₀ = 2`, `C = √8·C_E·C_P·(1-e^{-δ/2})^{-79/22}`, `k = k_E`. -/
theorem farThinRecvUng_of (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) (hQ : FarOutChartQ)
    (hP : FarOutPointwise) (hE : EtaQSupSeq dm dp) (hI : FarRecvIntegral) :
    FarThinRecvUng Pl σ₀ mZ dm dp := by
  obtain ⟨CP, hCP0, hCP⟩ := hP 0 (1 / 4) (by norm_num)
  refine ⟨2, fun D _ _ _ hst => ?_⟩
  obtain ⟨CE, kE, hCE0, hEev⟩ := hE D hst
  have hκ0 : 0 < 1 - Real.exp (-(D.K.δ / 2)) := by
    rw [sub_pos]; exact Real.exp_lt_one_iff.mpr (by linarith [hst.δ_pos])
  refine ⟨Real.sqrt 8 * CE * CP * (1 - Real.exp (-(D.K.δ / 2))) ^ (-(79 / 22 : ℝ)), kE,
    by positivity, ?_⟩
  filter_upwards [hEev, hst.near, hst.pins,
    mu_eventually_mem D hst.omega_ne hst.sigma_pos hst.sigma_lt,
    retNu_retEps_eventually_le_one hst.omega_ne hst.gamma_pos D.coeff_ne] with
    n hEn hnear hpins hmu hle1 z hz v f hf hv
  have hε : 0 < (D.level n).ε := (D.level n).ε_pos
  have hν : 0 < (D.level n).ν := (D.level n).ν_pos
  have hε1 : (D.level n).ε ≤ 1 := hle1.2
  have hc : 0 < cOf (D.level n).ν := cOf_pos hν
  have hR : 0 < (D.level n).ε⁻¹ := inv_pos.2 hε
  have hS : 0 < (D.level n).Scut D.K := Real.rpow_pos_of_pos hε _
  have hμ : D.mu n z ∈ Icc (0 : ℝ) (1 / 4) := by
    obtain ⟨h1, h2⟩ := hmu z hz
    exact ⟨by linarith [hst.sigma_pos], by linarith [hst.sigma_lt]⟩
  obtain ⟨hz1, hz2⟩ := frk_thinMultUng_level D.Pl D.K (D.level n) (D.mu n z) (hnear z hz)
    (hpins z hz).split v
  set F := UnforcedLeray.Short.IIIa.ltauLq (2 * cOf (D.level n).ν / (D.level n).ε⁻¹) (22 / 19)
    (UnforcedLeray.Short.IIIa.srcNorm
      (NearInst.cartLift (D.level n).ε⁻¹ (cOf (D.level n).ν) f)) with hF
  set E := CE * (D.level n).ν⁻¹ ^ kE with hEdef
  have hE0 : 0 ≤ E := by positivity
  have hKR : 0 < (1 - Real.exp (-(D.K.δ / 2))) * (D.level n).ε⁻¹ := mul_pos hκ0 hR
  have hHm : Measurable fun p : Chart =>
      ENNReal.ofReal (UnforcedLeray.Short.IIIa.transWeight D.K.mZ p ^ 2) *
        ‖((multOp D.Pl D.K (D.level n) v).fst : Chart → Ten3) p‖ₑ ^ (2 : ℝ) :=
    (((frk_measurable_transWeight D.K.mZ).pow_const 2).ennreal_ofReal).mul
      ((Lp.stronglyMeasurable _).measurable.enorm.pow_const _)
  have hQ' := hQ (D.level n).ε⁻¹ (cOf (D.level n).ν) (D.level n).ν (D.mu n z) D.K.δ
    ((D.level n).Scut D.K) D.K.mZ hR hc hS
    (UnforcedLeray.Short.IIIa.chartCoeff (D.level n).ε⁻¹ (D.level n).V) (v : Chart → Merid) f
    _ 4 ENNReal.ofNat_ne_top (fun s => ENNReal.ofReal (CP * ((1 - Real.exp (-(D.K.δ / 2))) * (D.level n).ε⁻¹ /
      Real.sqrt s) ^ (-(79 / 22 : ℝ))) * F)
    hHm (Lp.stronglyMeasurable v).measurable hz2 hv
    (fun p hp0 _ => hCP (D.level n).ν (D.mu n z) (D.level n).ε⁻¹ (cOf (D.level n).ν) D.K.δ hν
      hμ hR hc hst.δ_pos f hf p hp0)
  have hmono : ∫⁻ s in Ioo 0 ((D.level n).Scut D.K), ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) *
        UnforcedLeray.Short.IIIa.etaL2QSup (cOf (D.level n).ν) D.K.mZ
          (UnforcedLeray.Short.IIIa.chartCoeff (D.level n).ε⁻¹ (D.level n).V) s ^ (2 : ℝ) *
        (ENNReal.ofReal (CP * ((1 - Real.exp (-(D.K.δ / 2))) * (D.level n).ε⁻¹ /
          Real.sqrt s) ^ (-(79 / 22 : ℝ))) * F) ^ (2 : ℝ) ≤
      ∫⁻ s in Ioo 0 ((D.level n).Scut D.K), ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) *
        ENNReal.ofReal E ^ (2 : ℝ) *
        (ENNReal.ofReal (CP * ((1 - Real.exp (-(D.K.δ / 2))) * (D.level n).ε⁻¹ /
          Real.sqrt s) ^ (-(79 / 22 : ℝ))) * F) ^ (2 : ℝ) := by
    refine lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioo).2
      (Eventually.of_forall fun s hs => ?_))
    gcongr
    exact hEn s hs.1
  have hI' := hI ((D.level n).Scut D.K) E CP ((1 - Real.exp (-(D.K.δ / 2))) * (D.level n).ε⁻¹)
    F hS hE0 hCP0 hKR
  have htot : ∫⁻ p, ENNReal.ofReal (UnforcedLeray.Short.IIIa.transWeight D.K.mZ p ^ 2) *
        ‖((multOp D.Pl D.K (D.level n) v).fst : Chart → Ten3) p‖ₑ ^ (2 : ℝ)
          ∂(ageμ (cOf (D.level n).ν) (-1 / 2)) ≤
      2 * 4 * (ENNReal.ofReal (E ^ 2 * CP ^ 2 *
        ((1 - Real.exp (-(D.K.δ / 2))) * (D.level n).ε⁻¹) ^ (-(79 / 11 : ℝ)) *
          ((D.level n).Scut D.K) ^ (34 / 11 : ℝ)) * F ^ (2 : ℝ)) :=
    hQ'.trans (mul_le_mul_of_nonneg_left (hmono.trans hI') zero_le)
  have hfin := frk_sqrt_bound (by positivity) htot
  rw [← hz1, frk_sqrt_eq hE0 hCP0 hKR hS] at hfin
  have hP2 : 2 * cOf (D.level n).ν / (D.level n).ε⁻¹ = 2 * (D.level n).ε * cOf (D.level n).ν := by
    rw [div_inv_eq_mul]; ring
  have hF' : F = phaseL2Lr (2 * (D.level n).ε * cOf (D.level n).ν) (22 / 19)
      (strPhys (D.level n).ε⁻¹ (cOf (D.level n).ν) f) := by
    rw [hF, hP2]
    exact frk_ltauLq_eq _ _ _ _ (by positivity) f
  rw [hF'] at hfin
  refine hfin.trans (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) zero_le)
  have hSc : (D.level n).Scut D.K = (D.level n).ε ^ (-D.K.b) := rfl
  rw [hSc, hEdef]
  exact frk_const_le hCE0 hCP0 hκ0 hε hε1 hν hst.b_pos.le

/-! ## 4. The gained young-output receiver follows -/

/-- On young output the gained thin receiver is below the ungained one: `χ_y` commutes with `M_U`,
`|χ_y| ≤ 1`, and `g⁻¹ ≤ 1` (source 4164, 5318-5319, 2697-2700). -/
theorem frk_young_le (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel)
    (hχ : IsStreamCutoff K.χy) (hγ : 0 ≤ gRate Pl)
    (hM : ∀ v : LVel Pl L,
      ((multOp Pl K L (youngMul hχ v)).fst : Chart → Ten3) =ᵐ[gainZ1Measure
          (cOf L.ν) K.mZ (gRate Pl) L.ν]
        (fun p => cutFun K.χy L.ν p • ((multOp Pl K L v).fst : Chart → Ten3) p))
    (v : LVel Pl L) :
    ENNReal.ofReal ‖thinPart (multOp Pl K L (youngMul hχ v))‖ ≤
      z1Ung (cOf L.ν) K.mZ ((multOp Pl K L v).fst : Chart → Ten3) := by
  rw [lrt_norm_thinPart]
  refine (lrt_gainZ1_le_glob zero_le_one (fun p => ginv_le_one hγ L.ν_pos.le p) _).trans ?_
  rw [ENNReal.ofReal_one, one_mul]
  refine lrt_z1Ung_mono ?_
  have h := hM v
  rw [Filter.EventuallyEq, NearInst.ae_gainZ1Measure] at h
  filter_upwards [h] with p hp
  rw [hp, norm_smul, Real.norm_eq_abs]
  have h0 := hχ.range (L.ν * p.1)
  have hab : |cutFun K.χy L.ν p| ≤ 1 := by
    unfold cutFun
    rw [abs_of_nonneg h0.1]; exact h0.2
  calc |cutFun K.χy L.ν p| * ‖((multOp Pl K L v).fst : Chart → Ten3) p‖
      ≤ 1 * ‖((multOp Pl K L v).fst : Chart → Ten3) p‖ :=
        mul_le_mul_of_nonneg_right hab (norm_nonneg _)
    _ = _ := one_mul _

/-- **The gained young-output receiver `FarThinRecv` (`EarlyRepThin/Kernel/ThinRecv.lean`) from the
ungained one** (source 4164, 5318-5319): the same `k₀`, `C`, `k`. -/
theorem farThinRecv_of_ung (Pl : PlanarData) (σ₀ mZ dm dp : ℝ)
    (h : FarThinRecvUng Pl σ₀ mZ dm dp) : FarThinRecv Pl σ₀ mZ dm dp := by
  obtain ⟨k₀, hk⟩ := h
  refine ⟨k₀, fun D hP hσ hZ hst => ?_⟩
  obtain ⟨C, k, hC, e⟩ := hk D hP hσ hZ hst
  refine ⟨C, k, hC, ?_⟩
  filter_upwards [e, multYoung dm dp D hst] with n a m z hz v f hf hv
  exact (frk_young_le D.Pl D.K (D.level n) hst.chiY hst.gamma_pos.le (fun v => (m v).1) v).trans
    (a z hz v f hf hv)

end UnforcedLeray.Short.PartIIIb.Concrete
