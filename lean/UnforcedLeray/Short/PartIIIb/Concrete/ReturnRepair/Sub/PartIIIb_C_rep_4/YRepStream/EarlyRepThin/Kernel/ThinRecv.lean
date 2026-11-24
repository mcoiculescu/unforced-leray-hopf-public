import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.EarlyRepThin.Props
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Defs
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AsymMu
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AsymNuEps

/-!
# `PartIII-b:C/rep/4/4/1/org/7/1/org` (b): far-mask outputs on the thin receiver

Source `the November 2 reference manuscript` 5337-5338 ("the repair-to-thin entry
uses the pointwise exponent `79/22`, followed by `ρR`"), 3631-3647 (`sep:young`; "the pointwise
version has `q = ∞`, `b = p'`": with `p = 22/19`, `b = 22/3`, `j = 0` the receiver power is
`D^{-4+9/22} = D^{-79/22}`), 3611-3621 (`sep:resolvent`, radial gap `|y-λz| ≥ |y'| - λ|z'|`),
3902-3912 (far mask `s < S`, `t > e^δs`: at output age `s` the masked sources lie in the disk
`|z'| ≤ Re^{-δ/2}/√s`, the receiver at `|y'| = R/√s`, gap `(1-e^{-δ/2})R/√s`), 2713-2721
(`stress-short:coefficients`: `‖Wv(s)‖_{L²_ηL^∞_q} ≤ P_ν[(1+s)^{-3/4}+ε(1+s)^{-1/4}]`,
`v = s^{-1/2}V`), 2758-2772 (`M_U b = (v⊗b+b⊗v, …)`), 2666-2689 (the chart, `τ = 2q/R + log s`,
the cell `|q| < c/2` of length `c = ν⁻²` is one phase period `P = 2εc`), 5345-5352 ("after the
normalized velocity lift and thin multiplication").

`FarThinRecv`: for a far-kernel output `v = farOut f` (any measurable chart tensor `f`) at a
standing level, `‖(M_Uχ_yv)₁‖ ≤ P_νS^{k₀}ε^{79/22}‖𝒩_Tf‖_{L²_τL^{22/19}}`.  Route
(`farThinRecv_of`, task):

* `ThinMultPin` — the thin multiplier `(M_Uu)₁ = v⊗u + u⊗v`, `|χ_y| ≤ 1`, `g⁻¹ ≤ 1`:
  `‖(M_Uχ_yv)₁‖² ≤ ∫W²|(M_Uχ_yv)₁|²s^{-1/2}dς` and `W²|(M_Uχ_yv)₁|² ≤ 4W²|v_V|²|v|²` a.e.;
* `FarOutCellPhase` — one cell in `q` is one phase period: `∫_{|q|<c/2}|farOut f|²dq/c ≤
  2s⁻¹ farPt²`, `farPt` the phase `L²` norm of the masked separated velocity at the receiver;
* `FarOutChartQ` — Tonelli in `(s, η, q)`, `L^∞_q` of the coefficient against `L²_q` of `v`:
  `∫H ≤ 2κ₀∫_0^S s^{-3/2}‖Wv_V(s)‖²_{L²_ηL^∞_q}Φ(s)²` when `H ≤ κ₀W²|v_V|²|v|²` and
  `farPt ≤ Φ(s)`;
* `FarOutPointwise` — `sep:young` pointwise (`IIIa.sepYoungPointwise_of`) on the masked source:
  `farPt ≤ C((1-e^{-δ/2})R/√s)^{-79/22}‖𝒩_Tf‖_{L²_τL^{22/19}}`;
* `EtaQSupSeq` — the coefficient bound of 2717 along the sequence, `≤ P_ν`;
* `FarRecvIntegral` — `∫_0^S s^{-3/2}E²(C(K/√s)^{-79/22}F)²ds ≤ E²C²K^{-79/11}S^{34/11}F²`
  (`-3/2 + 79/22 = 23/11`).

Then `K = (1-e^{-δ/2})R`, `R = ε⁻¹`: `K^{-79/22} = (1-e^{-δ/2})^{-79/22}ε^{79/22}`,
`S^{17/11} ≤ ε^{-2b}` (`k₀ = 2`).
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open UnforcedLeray.Blueprint.Planar (PlanarData)
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **The pointwise separated velocity at a chart receiver** (source 3611-3621, 3647, 3905-3912):
the normalized phase `L²` norm (period `P = 2c/R`) of the masked response
`W_μ[1_{t>e^δs}𝒩_Tf]` at the receiver `y = chartY R p = (R/√s, 0, η/√s)` of the chart point `p`
of age `s = p.1` (independent of the phase coordinate `q`). -/
def farPt (R c ν μ δ : ℝ) (f : Chart → Ten3) (p : Chart) : ℝ≥0∞ :=
  UnforcedLeray.Short.IIIa.ltauAt (2 * c / R)
    (fun τ => ‖NearInst.sepWfar ν (μ : ℂ) R δ p.1 (NearInst.cartLift R c f) (NearInst.chartY R p)
      τ‖ₑ)

/-! ## 1. Leaves -/

/-- **The thin multiplier on young output** (source 2758-2772, 4147, 5779-5782: `(M_Uu)₁ =
v⊗u + u⊗v`, `v = s^{-1/2}V` the chart coefficient of the thin background; 4164 `|χ_y| ≤ 1`;
3875, 5117 `g⁻¹ ≤ 1` for `γ ≥ 0`; 2697 `Z₁ = L²(W²s^{-1/2}dς)`): at a level with the near
operators and the split multiplier, for every velocity `v`,
`‖(M_Uχ_yv)₁‖² ≤ ∫W²|(M_Uχ_yv)₁|² s^{-1/2}dς` and a.e.
`W²|(M_Uχ_yv)₁|² ≤ 4W²|v_V|²|v|²`. -/
def ThinMultPin : Prop :=
  ∀ (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ) (hχ : IsStreamCutoff K.χy),
    0 < K.C0 → NearAt Pl K L μ →
    (∃ M : Hsp (cOf L.ν) →L[ℝ] Zsp (cOf L.ν) K.mZ (L.ρb Pl K),
      NearInst.IsSplitMult M (L.params Pl).R L.V L.rb) → 0 ≤ gRate Pl → ∀ v : LVel Pl L,
      ENNReal.ofReal ‖thinPart (multOp Pl K L (youngMul hχ v))‖ ^ (2 : ℝ) ≤
          ∫⁻ p, ENNReal.ofReal (UnforcedLeray.Short.IIIa.transWeight K.mZ p ^ 2) *
            ‖((multOp Pl K L (youngMul hχ v)).fst : Chart → Ten3) p‖ₑ ^ (2 : ℝ)
              ∂(ageμ (cOf L.ν) (-1 / 2)) ∧
        ∀ᵐ p ∂(ageμ (cOf L.ν) (-1 / 2)),
          ENNReal.ofReal (UnforcedLeray.Short.IIIa.transWeight K.mZ p ^ 2) *
              ‖((multOp Pl K L (youngMul hχ v)).fst : Chart → Ten3) p‖ₑ ^ (2 : ℝ) ≤
            4 * (ENNReal.ofReal (UnforcedLeray.Short.IIIa.transWeight K.mZ p ^ 2 *
              ‖UnforcedLeray.Short.IIIa.chartCoeff L.ε⁻¹ L.V p‖ ^ 2) *
                ‖(v : Chart → Merid) p‖ₑ ^ (2 : ℝ))

/-- **One cell is one phase period** (source 2666-2689: `τ = 2q/R + log s`, `dq/c = dτ/P`,
`P = 2c/R`; the masked source `1_{t>e^δs}𝒩_Tf` is `P`-periodic in `τ`, hence so is its response;
`|merRe w| ≤ √2|w|`): for `s > 0` and every `η`,
`∫_{-c/2}^{c/2}|farOut f(s,q,η)|²dq/c ≤ 1_{s<S}·2s⁻¹·farPt(s,0,η)²`. -/
def FarOutCellPhase : Prop :=
  ∀ (R c ν μ δ S : ℝ), 0 < R → 0 < c → ∀ (f : Chart → Ten3) (s η : ℝ), 0 < s →
    ∫⁻ q in Ico (-(c / 2)) (c / 2), ENNReal.ofReal c⁻¹ *
        ‖NearInst.Masked.farOut R c ν μ δ S f (s, (q, η))‖ₑ ^ (2 : ℝ) ≤
      if s < S then ENNReal.ofReal (2 * s⁻¹) * farPt R c ν μ δ f (s, (0, η)) ^ (2 : ℝ) else 0

/-- **The thin receiver integral by `L^∞_q × L²_q`** (source 2713-2721, 2666-2689, 5345-5352): for
`R, c, S > 0`, a finite constant `κ₀ < ∞` (in the source a numerical constant; the one consumer
`farThinRecv_of` takes `κ₀ = 4`), a measurable `H ≥ 0` with `H ≤ κ₀W²|a|²|v|²` a.e., where
`v = farOut f` a.e. and `farPt ≤ Φ(s)` at every receiver of age `0 < s < S`,
`∫H s^{-1/2}dς ≤ 2κ₀∫_0^S s^{-3/2}‖Wa(s)‖²_{L²_ηL^∞_q}Φ(s)²ds` (`lintegral_ageμ`, Tonelli,
`W|a| ≤ essSup_q` a.e. in `q`, `FarOutCellPhase`; `farOut = 0` for `s ≥ S`).  The finiteness
`κ₀ ≠ ⊤` is what lets `κ₀` leave the `η`-integral of `κ₀·(essSup_q W|a|)²`
(`lintegral_const_mul'`): the `essSup_q` need not be measurable in `η` for an arbitrary `a`. -/
def FarOutChartQ : Prop :=
  ∀ (R c ν μ δ S mZ : ℝ), 0 < R → 0 < c → 0 < S →
    ∀ (a v : Chart → Merid) (f : Chart → Ten3) (H : Chart → ℝ≥0∞) (κ₀ : ℝ≥0∞), κ₀ ≠ ⊤ →
      ∀ (Φ : ℝ → ℝ≥0∞), Measurable H → Measurable v →
      (∀ᵐ p ∂(ageμ c (-1 / 2)), H p ≤ κ₀ * (ENNReal.ofReal
        (UnforcedLeray.Short.IIIa.transWeight mZ p ^ 2 * ‖a p‖ ^ 2) * ‖v p‖ₑ ^ (2 : ℝ))) →
      v =ᵐ[ageμ c (-3 / 2)] NearInst.Masked.farOut R c ν μ δ S f →
      (∀ p : Chart, 0 < p.1 → p.1 < S → farPt R c ν μ δ f p ≤ Φ p.1) →
      ∫⁻ p, H p ∂(ageμ c (-1 / 2)) ≤
        2 * κ₀ * ∫⁻ s in Ioo 0 S, ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) *
          UnforcedLeray.Short.IIIa.etaL2QSup c mZ a s ^ (2 : ℝ) * Φ s ^ (2 : ℝ)

/-- **`sep:young`, pointwise version, on the masked source** (source 3631-3647 with `p = 22/19`,
`b = 22/3`, `j = 0`: `D^{-4+9/22} = D^{-79/22}`; 3611-3621; 3905-3912: the masked source
`1_{e^δs < R²/|z'|²}𝒩_Tf` is a separated source in the disk `|z'| ≤ Re^{-δ/2}/√s`, the receiver
`chartY R p` has `|y'| = R/√s`): for a window `[σ₁, σ₂]`, `σ₁ > -1/4`, there is `C` with, for
`ν, R, c, δ > 0`, real `μ ∈ [σ₁, σ₂]`, measurable `f` and `p.1 > 0`,
`farPt ≤ C((1-e^{-δ/2})R/√s)^{-79/22}‖𝒩_Tf‖_{L²_τL^{22/19}}` (period `2c/R`). -/
def FarOutPointwise : Prop :=
  ∀ σ₁ σ₂ : ℝ, -(1 / 4) < σ₁ → ∃ C : ℝ, 0 ≤ C ∧
    ∀ (ν μ R c δ : ℝ), 0 < ν → μ ∈ Icc σ₁ σ₂ → 0 < R → 0 < c → 0 < δ →
      ∀ f : Chart → Ten3, Measurable f → ∀ p : Chart, 0 < p.1 →
        farPt R c ν μ δ f p ≤
          ENNReal.ofReal (C * ((1 - Real.exp (-(δ / 2))) * R / Real.sqrt p.1) ^ (-(79 / 22 : ℝ))) *
            UnforcedLeray.Short.IIIa.ltauLq (2 * c / R) (22 / 19)
              (UnforcedLeray.Short.IIIa.srcNorm (NearInst.cartLift R c f))

/-- **The coefficient bound of `stress-short:coefficients` along the sequence** (source 2713-2721,
fourth line, `‖Wv(s)‖_{L²_ηL^∞_q} ≤ P_ν[(1+s)^{-3/4}+ε(1+s)^{-1/4}] ≤ 2P_ν` for `ε ≤ 1`;
`IIIa.StressCoefficients` at the actual levels, as in `seq_splitMult`). -/
def EtaQSupSeq (dm dp : ℝ) : Prop :=
  ∀ D : SeqData, D.RepairStanding dm dp → ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop,
    ∀ s : ℝ, 0 < s → UnforcedLeray.Short.IIIa.etaL2QSup (cOf (D.level n).ν) D.K.mZ
      (UnforcedLeray.Short.IIIa.chartCoeff (D.level n).ε⁻¹ (D.level n).V) s ≤
        ENNReal.ofReal (C * (D.level n).ν⁻¹ ^ k)

/-- **The age integral** (source 5345-5352: "its square is integrable at zero, and the integral up
to `S` is polynomial in `S`"): `s^{-3/2}((K/√s)^{-79/22})² = K^{-79/11}s^{23/11}` and
`∫_0^S s^{23/11}ds = (11/34)S^{34/11} ≤ S^{34/11}`. -/
def FarRecvIntegral : Prop :=
  ∀ (S E C K : ℝ) (F : ℝ≥0∞), 0 < S → 0 ≤ E → 0 ≤ C → 0 < K →
    ∫⁻ s in Ioo 0 S, ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) * ENNReal.ofReal E ^ (2 : ℝ) *
        (ENNReal.ofReal (C * (K / Real.sqrt s) ^ (-(79 / 22 : ℝ))) * F) ^ (2 : ℝ) ≤
      ENNReal.ofReal (E ^ 2 * C ^ 2 * K ^ (-(79 / 11 : ℝ)) * S ^ (34 / 11 : ℝ)) * F ^ (2 : ℝ)

/-! ## 2. The thin receiver bound -/

/-- **Far-mask outputs on the thin receiver** (source 5337-5338, 3647, 2713-2721, 5345-5352,
3902-3912): with the S-degree `k₀` chosen before `D` (before `b`), for a standing sequence there
are `C ≥ 0`, `k` with, for large `n`, `z ∈ [-1,1]`, every velocity `v` and measurable chart tensor
`f` with `v = farOut f` a.e. (the far kernel of level `n`: `R = ε⁻¹`, `c = ν⁻²`, gap `δ`, cut
`S = ε^{-b}`),
`‖(M_Uχ_yv)₁‖ ≤ Cν^{-k}S^{k₀}ε^{79/22}‖𝒩_Tf‖_{L²_τL^{22/19}}` (period `2εc`). -/
def FarThinRecv (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) : Prop :=
  ∃ k₀ : ℕ, ∀ D : SeqData, D.Pl = Pl → D.σ₀ = σ₀ → D.K.mZ = mZ →
    ∀ hst : D.RepairStanding dm dp, ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧
      ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1, ∀ (v : LVel D.Pl (D.level n)) (f : Chart → Ten3),
        Measurable f →
        (v : Chart → Merid) =ᵐ[ageμ (cOf (D.level n).ν) (-3 / 2)]
          NearInst.Masked.farOut (D.level n).ε⁻¹ (cOf (D.level n).ν) (D.level n).ν (D.mu n z)
            D.K.δ ((D.level n).Scut D.K) f →
        ENNReal.ofReal ‖thinPart (multOp D.Pl D.K (D.level n) (youngMul hst.chiY v))‖ ≤
          ENNReal.ofReal (C * (D.level n).ν⁻¹ ^ k * (D.level n).ε ^ (-((k₀ : ℝ) * D.K.b)) *
              (D.level n).ε ^ (79 / 22 : ℝ)) *
            phaseL2Lr (2 * (D.level n).ε * cOf (D.level n).ν) (22 / 19)
              (strPhys (D.level n).ε⁻¹ (cOf (D.level n).ν) f)

/-! ## 3. The thin receiver bound from the leaves -/

theorem ftr_ltauLq_eq (ε c : ℝ) (hε : 0 < ε) (hc : 0 < c) (f : Chart → Ten3) :
    UnforcedLeray.Short.IIIa.ltauLq (2 * c / ε⁻¹) (22 / 19)
        (UnforcedLeray.Short.IIIa.srcNorm (NearInst.cartLift ε⁻¹ c f)) =
      phaseL2Lr (2 * ε * c) (22 / 19) (strPhys ε⁻¹ c f) := by
  have hP : 2 * c / ε⁻¹ = 2 * ε * c := by rw [div_inv_eq_mul]; ring
  have hPpos : 0 < 2 * ε * c := by positivity
  rw [hP]
  unfold UnforcedLeray.Short.IIIa.ltauLq phaseL2Lr UnforcedLeray.Short.IIIa.srcNorm strPhys
  rw [ENNReal.ofReal_inv_of_pos hPpos]

theorem ftr_measurable_transWeight (mZ : ℝ) :
    Measurable (UnforcedLeray.Short.IIIa.transWeight mZ) := by
  unfold UnforcedLeray.Short.IIIa.transWeight
  fun_prop

/-- The real exponent bookkeeping of `farThinRecv_of`: `K = κε⁻¹`, `S = ε^{-b}`,
`8E²C²K^{-79/11}S^{34/11} ≤ (√8·CE·C·κ^{-79/22}ν^{-k}ε^{-2b}ε^{79/22})²` for `ε ≤ 1`, `b > 0`. -/
theorem ftr_exponents {CE CP κ ε b νi : ℝ} (kE : ℕ) (_hCE : 0 ≤ CE) (_hCP : 0 ≤ CP) (hκ : 0 < κ)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hb : 0 < b) (_hνi : 0 ≤ νi) :
    8 * ((CE * νi ^ kE) ^ 2 * CP ^ 2 * (κ * ε⁻¹) ^ (-(79 / 11 : ℝ)) *
        (ε ^ (-b)) ^ (34 / 11 : ℝ)) ≤
      (Real.sqrt 8 * CE * CP * κ ^ (-(79 / 22 : ℝ)) * νi ^ kE *
        ε ^ (-(((2 : ℕ) : ℝ) * b)) * ε ^ (79 / 22 : ℝ)) ^ 2 := by
  have h1 : (κ * ε⁻¹) ^ (-(79 / 22 : ℝ)) = κ ^ (-(79 / 22 : ℝ)) * ε ^ (79 / 22 : ℝ) := by
    rw [Real.mul_rpow hκ.le (inv_nonneg.2 hε.le), Real.inv_rpow hε.le, Real.rpow_neg hε.le,
      inv_inv]
  have h2 : (κ * ε⁻¹) ^ (-(79 / 11 : ℝ)) = ((κ * ε⁻¹) ^ (-(79 / 22 : ℝ))) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  have h3 : (ε ^ (-b)) ^ (34 / 11 : ℝ) ≤ (ε ^ (-(((2 : ℕ) : ℝ) * b))) ^ 2 := by
    rw [← Real.rpow_mul hε.le, ← Real.rpow_natCast, ← Real.rpow_mul hε.le]
    refine Real.rpow_le_rpow_of_exponent_ge hε hε1 ?_
    push_cast
    nlinarith
  have hS0 : 0 ≤ (ε ^ (-b)) ^ (34 / 11 : ℝ) := by positivity
  have hA : 0 ≤ (CE * νi ^ kE) ^ 2 * CP ^ 2 * (κ ^ (-(79 / 22 : ℝ)) * ε ^ (79 / 22 : ℝ)) ^ 2 := by
    positivity
  rw [h2, h1]
  calc 8 * ((CE * νi ^ kE) ^ 2 * CP ^ 2 * (κ ^ (-(79 / 22 : ℝ)) * ε ^ (79 / 22 : ℝ)) ^ 2 *
          (ε ^ (-b)) ^ (34 / 11 : ℝ))
      ≤ 8 * ((CE * νi ^ kE) ^ 2 * CP ^ 2 * (κ ^ (-(79 / 22 : ℝ)) * ε ^ (79 / 22 : ℝ)) ^ 2 *
          (ε ^ (-(((2 : ℕ) : ℝ) * b))) ^ 2) := by gcongr
    _ = _ := by
        rw [show Real.sqrt 8 * CE * CP * κ ^ (-(79 / 22 : ℝ)) * νi ^ kE *
            ε ^ (-(((2 : ℕ) : ℝ) * b)) * ε ^ (79 / 22 : ℝ) = Real.sqrt 8 * (CE * νi ^ kE * CP *
              (κ ^ (-(79 / 22 : ℝ)) * ε ^ (79 / 22 : ℝ)) * ε ^ (-(((2 : ℕ) : ℝ) * b))) by ring,
          mul_pow (Real.sqrt 8), Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 8)]
        ring

/-- **(b) from its leaves** (source 5337-5338, 3647, 2713-2721, 5345-5352), with `k₀ = 2`. -/
theorem farThinRecv_of (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) (h1 : ThinMultPin)
    (h2 : FarOutChartQ) (h3 : FarOutPointwise) (h4 : EtaQSupSeq dm dp)
    (h5 : FarRecvIntegral) : FarThinRecv Pl σ₀ mZ dm dp := by
  refine ⟨2, fun D hPl hσ hmZ hst => ?_⟩
  obtain ⟨CP, hCP, hP⟩ := h3 (D.σ₀ / 2) ((D.σ₀ + 1 / 4) / 2) (by linarith [hst.sigma_pos])
  obtain ⟨CE, kE, hCE, hE⟩ := h4 D hst
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = 1 - Real.exp (-(D.K.δ / 2)) := ⟨_, rfl⟩
  have hκ0 : 0 < κ := by
    have : Real.exp (-(D.K.δ / 2)) < 1 := by
      have := Real.exp_lt_exp.mpr (show -(D.K.δ / 2) < 0 by linarith [hst.δ_pos])
      simpa using this
    rw [hκ]; linarith
  refine ⟨Real.sqrt 8 * CE * CP * κ ^ (-(79 / 22 : ℝ)), kE, by positivity, ?_⟩
  filter_upwards [hE, hst.near, hst.pins,
    mu_eventually_mem D hst.omega_ne hst.sigma_pos hst.sigma_lt,
    retNu_retEps_eventually_le_one hst.omega_ne hst.gamma_pos D.coeff_ne] with
    n hEn hnear hpins hmu hle z hz v f hf hv
  have hν : 0 < (D.level n).ν := (D.level n).ν_pos
  have hε : 0 < (D.level n).ε := (D.level n).ε_pos
  have hε1 : (D.level n).ε ≤ 1 := hle.2
  have hc : 0 < cOf (D.level n).ν := cOf_pos hν
  have hR : 0 < (D.level n).ε⁻¹ := inv_pos.2 hε
  have hS : 0 < (D.level n).Scut D.K := Real.rpow_pos_of_pos hε _
  have hνi : 0 ≤ (D.level n).ν⁻¹ := inv_nonneg.2 hν.le
  have hE0 : 0 ≤ CE * (D.level n).ν⁻¹ ^ kE := by positivity
  -- the pointwise separated velocity at every receiver of age `0 < s < S`
  have hpt : ∀ p : Chart, 0 < p.1 → p.1 < (D.level n).Scut D.K →
      farPt (D.level n).ε⁻¹ (cOf (D.level n).ν) (D.level n).ν (D.mu n z) D.K.δ f p ≤
        ENNReal.ofReal (CP * (κ * (D.level n).ε⁻¹ / Real.sqrt p.1) ^ (-(79 / 22 : ℝ))) *
          phaseL2Lr (2 * (D.level n).ε * cOf (D.level n).ν) (22 / 19)
            (strPhys (D.level n).ε⁻¹ (cOf (D.level n).ν) f) := by
    intro p hp _
    have h := hP (D.level n).ν (D.mu n z) (D.level n).ε⁻¹ (cOf (D.level n).ν) D.K.δ hν
      (hmu z hz) hR hc hst.δ_pos f hf p hp
    rw [ftr_ltauLq_eq _ _ hε hc, ← hκ] at h
    exact h
  -- the thin multiplier
  obtain ⟨hn1, hn2⟩ := h1 D.Pl D.K (D.level n) (D.mu n z) hst.chiY hst.C0_pos (hnear z hz)
    (hpins z hz).split hst.gamma_pos.le v
  have hHm : Measurable fun p : Chart =>
      ENNReal.ofReal (UnforcedLeray.Short.IIIa.transWeight D.K.mZ p ^ 2) *
        ‖((multOp D.Pl D.K (D.level n) (youngMul hst.chiY v)).fst : Chart → Ten3) p‖ₑ ^ (2 : ℝ) :=
    (ENNReal.measurable_ofReal.comp ((ftr_measurable_transWeight D.K.mZ).pow_const 2)).mul
      ((Lp.stronglyMeasurable _).measurable.enorm.pow_const _)
  have hC := h2 (D.level n).ε⁻¹ (cOf (D.level n).ν) (D.level n).ν (D.mu n z) D.K.δ
    ((D.level n).Scut D.K) D.K.mZ hR hc hS
    (UnforcedLeray.Short.IIIa.chartCoeff (D.level n).ε⁻¹ (D.level n).V) (v : Chart → Merid) f _ 4
    ENNReal.ofNat_ne_top (fun s => ENNReal.ofReal (CP * (κ * (D.level n).ε⁻¹ / Real.sqrt s) ^ (-(79 / 22 : ℝ))) *
      phaseL2Lr (2 * (D.level n).ε * cOf (D.level n).ν) (22 / 19)
        (strPhys (D.level n).ε⁻¹ (cOf (D.level n).ν) f))
    hHm (Lp.stronglyMeasurable v).measurable hn2 hv hpt
  -- the age integral
  have hD : ∫⁻ s in Ioo 0 ((D.level n).Scut D.K), ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) *
        UnforcedLeray.Short.IIIa.etaL2QSup (cOf (D.level n).ν) D.K.mZ
          (UnforcedLeray.Short.IIIa.chartCoeff (D.level n).ε⁻¹ (D.level n).V) s ^ (2 : ℝ) *
        (ENNReal.ofReal (CP * (κ * (D.level n).ε⁻¹ / Real.sqrt s) ^ (-(79 / 22 : ℝ))) *
          phaseL2Lr (2 * (D.level n).ε * cOf (D.level n).ν) (22 / 19)
            (strPhys (D.level n).ε⁻¹ (cOf (D.level n).ν) f)) ^ (2 : ℝ) ≤
      ∫⁻ s in Ioo 0 ((D.level n).Scut D.K), ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) *
        ENNReal.ofReal (CE * (D.level n).ν⁻¹ ^ kE) ^ (2 : ℝ) *
        (ENNReal.ofReal (CP * (κ * (D.level n).ε⁻¹ / Real.sqrt s) ^ (-(79 / 22 : ℝ))) *
          phaseL2Lr (2 * (D.level n).ε * cOf (D.level n).ν) (22 / 19)
            (strPhys (D.level n).ε⁻¹ (cOf (D.level n).ν) f)) ^ (2 : ℝ) := by
    refine lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioo).2
      (Eventually.of_forall fun s hs => ?_))
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (ENNReal.rpow_le_rpow (hEn s hs.1) (by norm_num)) zero_le) zero_le
  have hI := h5 ((D.level n).Scut D.K) (CE * (D.level n).ν⁻¹ ^ kE) CP (κ * (D.level n).ε⁻¹)
    (phaseL2Lr (2 * (D.level n).ε * cOf (D.level n).ν) (22 / 19)
      (strPhys (D.level n).ε⁻¹ (cOf (D.level n).ν) f)) hS hE0 hCP (mul_pos hκ0 hR)
  have hX := ftr_exponents kE hCE hCP hκ0 hε hε1 hst.b_pos hνi
  have hB0 : 0 ≤ Real.sqrt 8 * CE * CP * κ ^ (-(79 / 22 : ℝ)) * (D.level n).ν⁻¹ ^ kE *
      (D.level n).ε ^ (-(((2 : ℕ) : ℝ) * D.K.b)) * (D.level n).ε ^ (79 / 22 : ℝ) := by positivity
  rw [← ENNReal.rpow_le_rpow_iff (by norm_num : (0 : ℝ) < 2)]
  calc ENNReal.ofReal ‖thinPart (multOp D.Pl D.K (D.level n) (youngMul hst.chiY v))‖ ^ (2 : ℝ)
      ≤ 2 * 4 * (ENNReal.ofReal ((CE * (D.level n).ν⁻¹ ^ kE) ^ 2 * CP ^ 2 *
          (κ * (D.level n).ε⁻¹) ^ (-(79 / 11 : ℝ)) * (D.level n).Scut D.K ^ (34 / 11 : ℝ)) *
          phaseL2Lr (2 * (D.level n).ε * cOf (D.level n).ν) (22 / 19)
            (strPhys (D.level n).ε⁻¹ (cOf (D.level n).ν) f) ^ (2 : ℝ)) :=
        hn1.trans (hC.trans (mul_le_mul_of_nonneg_left (hD.trans hI) zero_le))
    _ = ENNReal.ofReal (8 * ((CE * (D.level n).ν⁻¹ ^ kE) ^ 2 * CP ^ 2 *
          (κ * (D.level n).ε⁻¹) ^ (-(79 / 11 : ℝ)) * (D.level n).Scut D.K ^ (34 / 11 : ℝ))) *
          phaseL2Lr (2 * (D.level n).ε * cOf (D.level n).ν) (22 / 19)
            (strPhys (D.level n).ε⁻¹ (cOf (D.level n).ν) f) ^ (2 : ℝ) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 8), ENNReal.ofReal_ofNat]
        ring
    _ ≤ ENNReal.ofReal ((Real.sqrt 8 * CE * CP * κ ^ (-(79 / 22 : ℝ)) * (D.level n).ν⁻¹ ^ kE *
          (D.level n).ε ^ (-(((2 : ℕ) : ℝ) * D.K.b)) * (D.level n).ε ^ (79 / 22 : ℝ)) ^ 2) *
          phaseL2Lr (2 * (D.level n).ε * cOf (D.level n).ν) (22 / 19)
            (strPhys (D.level n).ε⁻¹ (cOf (D.level n).ν) f) ^ (2 : ℝ) :=
        mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hX) zero_le
    _ = _ := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
          ENNReal.ofReal_rpow_of_nonneg hB0 (by norm_num), Real.rpow_two]

end UnforcedLeray.Short.PartIIIb.Concrete
