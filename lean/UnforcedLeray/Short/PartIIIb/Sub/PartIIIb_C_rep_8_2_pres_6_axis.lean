import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_6
import UnforcedLeray.Short.PartI.StatementsTrain
import UnforcedLeray.Short.PartIIIa.Sub.T23_1_org

/-!
# The axis value of the raw lift (task `PartIII-b:C/rep/8/2/pres/6/axis/org`)

Source `the November 2 reference manuscript`:
Proposition `sct:lift` (1205-1235): the lift `u_r = (R/r)v₁`, `u_z = (R/r)(v₂ + εH)` is "smooth
through the axis for positive time"; its proof (1310-1323): "Smoothness at the axis follows term by
term from the full heat expansion `r a_{2j}∂_η^{2j}G_{νs} = …`; fluctuations are flat because
`e^{-κνR²t/(c²r²)}` dominates", and "the leading mean is `(-ϱR⁻¹∂_{z_y}(a₀G_ν), 2R⁻¹a₀G_ν)`".

The all-age decay this uses is Lemma `sct:heat` (437-467) of Part I, stated for the BUC train in
`PartI.TrainFluctuationDecay` (`sct:fluctuation`, 439-446) and `PartI.TrainMeanExpansion`
(`sct:expansion`, 447-459), with the mean equations `PartI.TrainMeanEquations` (`sct:mean`,
397-404).  No new field of `SeqData` or `IsActualLevel` is needed: the trains of the sequence are
BUC (`SeqData.train_buc`) and `ν_n → 0` (`retNu_tendsto`), so Part I applies for large `n`.

In the chart `s = R²/ϱ²`, `η = Ry₃/ϱ = √s·y₃`, `U_raw = √s(b₀e_r + b₁e₃)` with
`b = (v₁, v₂ + εH)`, `H = (1-K)ψ`.  At late age
* `√s v = √s(\bar v + \tilde v) = O(s^{-1/2})` (`IIIa.LateMeanVel`, `IIIa.LateFluctVel`);
* `εH = ε(1-K)\tilde ψ + ε(1-K)S` (`IIIa.RaisedStreamSplit`), `(1-K)\tilde ψ = O(e^{-κνs/c²})`
  (`AxisEvFluctSharp`), and `(1-K)S = 2a₀G_{νs}(η) + O(s^{-3/2})` (`AxisEvMeanAsymp`: the heat
  identity `(1-K)G_{νs} = 2G_{νs}` and the remainder of `sct:expansion` at `N = 0`);
* `√s·G_{νs}(√s x) = G_ν(x)`, so `√s b₁ → 2εa₀G_ν(y₃)`: the axis value is `2εa₀G_ν(y₃)e₃`
  (source 1321-1322).

## Contents

* `AxisEvDecay b g`: the uniform late-age decay of a chart profile `b` with axial limit profile `g`;
* leaf statements `AxisEvNvLimit` (geometry of the ring lift at the axis), `AxisEvTrainDecay`
  (the train's raw profile has the decay), `AxisEvFluctSharp`, `AxisEvMeanAsymp` (Part I readings);
* proved: the elementary helpers `AxisEvOrg.heatKernel1_scale`, `hasDerivAt_heatKernel1_eta`,
  `hasDerivAt_heatKernel1_age`, `heatKernel1_completion`, `continuous_heatKernel1`,
  `transWeight_zero`, `late_small`, `sqrt_mul_inv_one_add_le`, `sqrt_mul_rpow_le` (for the leaves),
  `AxisEvOrg.rawAxisContinuous_of_decay`, and the reduction `axisEv_of`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

/-- **Uniform late-age axis decay** of a chart profile `b(s, ξ, η)` with axial limit profile `g`
(source 1310-1323): `g` is continuous, `√s|b₀| → 0` uniformly in `(ξ, η)` as `s → ∞`, and
`√s b₁(s, ξ, √s x) → g(x)` uniformly in `(ξ, x)` (the chart regime `η = √s·y₃` near the axis). -/
def AxisEvDecay (b : ℝ × (ℝ × ℝ) → Merid) (g : ℝ → ℝ) : Prop :=
  Continuous g ∧
  (∀ e : ℝ, 0 < e → ∃ S : ℝ, ∀ s : ℝ, S ≤ s → ∀ ξ η : ℝ, Real.sqrt s * |b (s, (ξ, η)) 0| ≤ e) ∧
  (∀ e : ℝ, 0 < e → ∃ S : ℝ, ∀ s : ℝ, S ≤ s → ∀ ξ x : ℝ,
    |Real.sqrt s * b (s, (ξ, Real.sqrt s * x)) 1 - g x| ≤ e)

/-- **The ring lift has a limit at the axis** (geometry; source 1310-1323): for `R > 0` and a profile
with uniform late-age axis decay, `N_v b(τ, y') = √s(b₀e_r + b₁e₃)` at the chart point of `y'`
tends to `g(y₃)e₃` as `y' → y ∈ axis` off the axis (`s = R²/ϱ² → ∞`, `η = √s·y'₃`,
`|e_r| = 1`). -/
def AxisEvNvLimit : Prop :=
  ∀ (R : ℝ) (b : ℝ × (ℝ × ℝ) → Merid) (g : ℝ → ℝ), 0 < R → AxisEvDecay b g →
    ∀ (τ : ℝ) (y : Space), y ∈ axis → Tendsto (Nv R b τ) (𝓝[axisᶜ] y) (𝓝 (g (y 2) • e3))

/-- **The raw profile of the BUC train has the axis decay** (source 1310-1323 from `sct:heat`,
437-467): for small `ν`, every BUC train at `c = ν⁻²` and every `ε`, the profile
`b_raw = (v₁, v₂ + εH)` has uniform late-age axis decay with axial limit `2εa₀G_ν`
(`a₀ = PartI.meanCoeff tr 0`, `G_ν = PartI.heatKernel1 ν`; the leading mean of source 1321-1322). -/
def AxisEvTrainDecay : Prop :=
  ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
    ∀ tr : UnforcedLeray.B0140.TrainSol ν (cOf ν), UnforcedLeray.Short.PartI.IsBUCTrain tr →
      ∀ ε : ℝ, AxisEvDecay (UnforcedLeray.Cons.C03.rawProfile ε tr.v tr.ψ)
        (fun x => ε * (2 * UnforcedLeray.Short.PartI.meanCoeff tr 0 *
          UnforcedLeray.Short.PartI.heatKernel1 ν x))

/-- **The stream completion of the fluctuation decays like `(1+s)⁻¹`** (source 1317-1318
"fluctuations are flat", from `sct:fluctuation` 439-446 for `\tilde ψ`, `∂_η\tilde ψ`, `∂_s\tilde ψ`
with weight `m = 1`; `(1+s)²e^{-κνs/c²}` is bounded polynomially in `ν⁻¹` at `c = ν⁻²`): for
`s ≥ 1`, `|(1 - η∂_η - 2s∂_s)\tilde ψ(s, q, η)| ≤ Cν^{-k}(1+s)⁻¹`. -/
def AxisEvFluctSharp : Prop :=
  ∃ (C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < ν₀ ∧ ∀ ν ∈ Ioc 0 ν₀,
    ∀ c : ℝ, c = (ν ^ 2)⁻¹ → ∀ tr : UnforcedLeray.B0140.TrainSol ν c,
      UnforcedLeray.Short.PartI.IsBUCTrain tr → ∀ s : ℝ, 1 ≤ s → ∀ q η : ℝ,
        |UnforcedLeray.Cons.C03.raisedStream (UnforcedLeray.Short.IIIa.fluctStream tr) s q η| ≤
          C * ν⁻¹ ^ k * (1 + s)⁻¹

/-- **The stream completion of the mean is the leading heat mode up to `s^{-3/2}`** (source
1268-1269 "`K∂_η^jG_{νs} = -(j+1)∂_η^jG_{νs}`", 1310-1322, and `sct:expansion` 447-459 at `N = 0`,
`p = ∞`): with `S = a₀G_{νs} + R₀`, `(1-K)G_{νs} = 2G_{νs}` and
`|R₀| + |η∂_ηR₀| + |s∂_sR₀| ≤ P s^{-3/2}`, so for `s ≥ 1`,
`|(1 - η∂_η - 2s∂_s)S(s, η) - 2a₀G_{νs}(η)| ≤ Cν^{-k}s^{-3/2}`. -/
def AxisEvMeanAsymp : Prop :=
  ∃ (C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < ν₀ ∧ ∀ ν ∈ Ioc 0 ν₀,
    ∀ c : ℝ, c = (ν ^ 2)⁻¹ → ∀ tr : UnforcedLeray.B0140.TrainSol ν c,
      UnforcedLeray.Short.PartI.IsBUCTrain tr → ∀ s : ℝ, 1 ≤ s → ∀ η : ℝ,
        |UnforcedLeray.Short.IIIa.meanCompletion tr s η -
            2 * UnforcedLeray.Short.PartI.meanCoeff tr 0 *
              UnforcedLeray.Short.PartI.heatKernel1 (ν * s) η| ≤
          C * ν⁻¹ ^ k * s ^ (-(3 / 2 : ℝ))

namespace AxisEvOrg

/-! ### Helpers for the leaves (elementary) -/

/-- The heat-kernel scaling of the leading mean (source 1321-1322):
`√s·G_{νs}(√s x) = G_ν(x)` for `ν, s > 0`. -/
theorem heatKernel1_scale {ν s : ℝ} (hν : 0 < ν) (hs : 0 < s) (x : ℝ) :
    Real.sqrt s * UnforcedLeray.Short.PartI.heatKernel1 (ν * s) (Real.sqrt s * x) =
      UnforcedLeray.Short.PartI.heatKernel1 ν x := by
  unfold UnforcedLeray.Short.PartI.heatKernel1
  have hq : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
  have h1 : Real.sqrt (4 * Real.pi * (ν * s)) = Real.sqrt (4 * Real.pi * ν) * Real.sqrt s := by
    rw [← Real.sqrt_mul (by positivity)]
    ring_nf
  have h2 : -((Real.sqrt s * x) ^ 2) / (4 * (ν * s)) = -(x ^ 2) / (4 * ν) := by
    rw [mul_pow, Real.sq_sqrt hs.le]
    field_simp
  rw [h1, h2, mul_inv]
  field_simp

/-- `∂_η G_t(η) = G_t(η)·(-η/(2t))` for `t > 0`. -/
theorem hasDerivAt_heatKernel1_eta {t : ℝ} (ht : 0 < t) (η : ℝ) :
    HasDerivAt (fun e => UnforcedLeray.Short.PartI.heatKernel1 t e)
      (UnforcedLeray.Short.PartI.heatKernel1 t η * (-η / (2 * t))) η := by
  unfold UnforcedLeray.Short.PartI.heatKernel1
  have h0 : HasDerivAt (fun e : ℝ => e ^ 2) (2 * η) η := by
    simpa using hasDerivAt_pow 2 η
  have h1 : HasDerivAt (fun e : ℝ => -(e ^ 2) / (4 * t)) (-(2 * η) / (4 * t)) η :=
    h0.neg.div_const (4 * t)
  have e : -(2 * η) / (4 * t) = -η / (2 * t) := by
    rw [div_eq_div_iff (by positivity) (by positivity)]
    ring
  rw [e] at h1
  have h2 := (h1.exp).const_mul (Real.sqrt (4 * Real.pi * t))⁻¹
  refine h2.congr_deriv ?_
  ring

/-- `∂_r[G_{νr}(η)] = G_{νr}(η)·(η²/(4νr²) - 1/(2r))` for `ν, r > 0`. -/
theorem hasDerivAt_heatKernel1_age {ν r : ℝ} (hν : 0 < ν) (hr : 0 < r) (η : ℝ) :
    HasDerivAt (fun r' => UnforcedLeray.Short.PartI.heatKernel1 (ν * r') η)
      (UnforcedLeray.Short.PartI.heatKernel1 (ν * r) η * (η ^ 2 / (4 * ν * r ^ 2) - 1 / (2 * r)))
      r := by
  unfold UnforcedLeray.Short.PartI.heatKernel1
  have hX : 0 < 4 * Real.pi * (ν * r) := by positivity
  have harg : HasDerivAt (fun r' : ℝ => 4 * Real.pi * (ν * r')) (4 * Real.pi * (ν * 1)) r :=
    ((hasDerivAt_id r).const_mul ν).const_mul (4 * Real.pi)
  have hsqrt := (Real.hasDerivAt_sqrt hX.ne').comp r harg
  set q := Real.sqrt (4 * Real.pi * (ν * r)) with hqdef
  have hq0 : 0 < q := Real.sqrt_pos.2 hX
  have hinv := hsqrt.inv hq0.ne'
  have hsq : q * q = 4 * Real.pi * (ν * r) := Real.mul_self_sqrt hX.le
  have hden : HasDerivAt (fun r' : ℝ => 4 * (ν * r')) (4 * (ν * 1)) r :=
    ((hasDerivAt_id r).const_mul ν).const_mul 4
  have hexpArg : HasDerivAt (fun r' : ℝ => -(η ^ 2) / (4 * (ν * r'))) (η ^ 2 / (4 * ν * r ^ 2)) r := by
    refine ((hasDerivAt_const r (-(η ^ 2))).div hden (by positivity)).congr_deriv ?_
    field_simp
    ring
  have hprod := hinv.mul hexpArg.exp
  refine hprod.congr_deriv ?_
  have hπ : 0 < Real.pi := Real.pi_pos
  have e1 : 1 / (2 * q) * (4 * Real.pi * (ν * 1)) / q ^ 2 = q⁻¹ * (1 / (2 * r)) := by
    rw [sq, hsq]
    field_simp
  simp only [Function.comp_apply, Pi.inv_apply]
  rw [← hqdef, neg_div, e1]
  ring

/-- **The heat identity `(1-K)G_{νr} = 2G_{νr}`** (source 1268-1269, `K∂_η^jG = -(j+1)∂_η^jG` at
`j = 0`), with `K = η∂_η + 2r∂_r`. -/
theorem heatKernel1_completion {ν r : ℝ} (hν : 0 < ν) (hr : 0 < r) (η : ℝ) :
    UnforcedLeray.Short.PartI.heatKernel1 (ν * r) η -
        (η * deriv (fun e => UnforcedLeray.Short.PartI.heatKernel1 (ν * r) e) η +
          2 * r * deriv (fun r' => UnforcedLeray.Short.PartI.heatKernel1 (ν * r') η) r) =
      2 * UnforcedLeray.Short.PartI.heatKernel1 (ν * r) η := by
  rw [(hasDerivAt_heatKernel1_eta (mul_pos hν hr) η).deriv,
    (hasDerivAt_heatKernel1_age hν hr η).deriv]
  field_simp
  ring

/-- `G_t` is continuous in the transverse variable. -/
theorem continuous_heatKernel1 (t : ℝ) :
    Continuous (UnforcedLeray.Short.PartI.heatKernel1 t) := by
  unfold UnforcedLeray.Short.PartI.heatKernel1
  exact continuous_const.mul (Real.continuous_exp.comp ((continuous_pow 2).neg.div_const _))

/-- The transverse weight with exponent `0` is `1`. -/
theorem transWeight_zero (p : ℝ × (ℝ × ℝ)) : UnforcedLeray.Short.IIIa.transWeight 0 p = 1 := by
  simp [UnforcedLeray.Short.IIIa.transWeight]

/-- `K/√s ≤ e` for all large `s`. -/
theorem late_small (K e : ℝ) (he : 0 < e) :
    ∃ S : ℝ, 1 ≤ S ∧ ∀ s : ℝ, S ≤ s → K * (Real.sqrt s)⁻¹ ≤ e := by
  refine ⟨max 1 ((K / e) ^ 2), le_max_left _ _, fun s hs => ?_⟩
  have hs1 : 1 ≤ s := (le_max_left _ _).trans hs
  have hq : 0 < Real.sqrt s := Real.sqrt_pos.2 (by linarith)
  have hK : K / e ≤ Real.sqrt s := by
    calc K / e ≤ |K / e| := le_abs_self _
      _ = Real.sqrt ((K / e) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt s := Real.sqrt_le_sqrt ((le_max_right _ _).trans hs)
  rw [← div_eq_mul_inv, div_le_iff₀ hq]
  rw [div_le_iff₀ he] at hK
  linarith

/-- `√s (1+s)⁻¹ ≤ (√s)⁻¹` for `s > 0`. -/
theorem sqrt_mul_inv_one_add_le {s : ℝ} (hs : 0 < s) :
    Real.sqrt s * (1 + s)⁻¹ ≤ (Real.sqrt s)⁻¹ := by
  have hq : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
  rw [← div_eq_mul_inv, div_le_iff₀ (by linarith), inv_mul_eq_div, le_div_iff₀ hq,
    Real.mul_self_sqrt hs.le]
  linarith

/-- `√s s^{-3/2} ≤ (√s)⁻¹` for `s ≥ 1`. -/
theorem sqrt_mul_rpow_le {s : ℝ} (hs : 1 ≤ s) :
    Real.sqrt s * s ^ (-(3 / 2 : ℝ)) ≤ (Real.sqrt s)⁻¹ := by
  have hs0 : 0 < s := by linarith
  have e : Real.sqrt s * s ^ (-(3 / 2 : ℝ)) = s⁻¹ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hs0, show (1 / 2 : ℝ) + -(3 / 2) = -1 by norm_num,
      Real.rpow_neg_one]
  rw [e]
  apply inv_anti₀ (Real.sqrt_pos.2 hs0)
  calc Real.sqrt s ≤ Real.sqrt s * Real.sqrt s :=
        le_mul_of_one_le_right (Real.sqrt_nonneg _) (Real.one_le_sqrt.2 hs)
    _ = s := Real.mul_self_sqrt hs0.le

/-- The test points `y + (n+1)⁻¹e₀` of `RawAxisContinuous` leave the axis. -/
theorem shift_not_mem_axis (y : Space) (hy : y ∈ axis) (n : ℕ) :
    y + (((n : ℝ) + 1)⁻¹) • coordinateVector 0 ∉ axis := by
  intro h
  have h0 : (y + (((n : ℝ) + 1)⁻¹) • coordinateVector 0) 0 = 0 := h.1
  have hy0 : y 0 = 0 := hy.1
  have hne : (n : ℝ) + 1 ≠ 0 := (by positivity : (0 : ℝ) < (n : ℝ) + 1).ne'
  simp [coordinateVector, hy0] at h0
  exact hne h0

/-- The test points tend to `y` off the axis. -/
theorem tendsto_shift (y : Space) (hy : y ∈ axis) :
    Tendsto (fun n : ℕ => y + (((n : ℝ) + 1)⁻¹) • coordinateVector 0) atTop (𝓝[axisᶜ] y) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => shift_not_mem_axis y hy n⟩
  have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
    simpa only [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have h2 := (tendsto_const_nhds (x := y)).add (h1.smul_const (coordinateVector 0 : Space))
  rwa [zero_smul, add_zero] at h2

/-- **`RawAxisContinuous` from the axis decay of the raw profile** (source 1205-1235, 1310-1323):
the axis value `axisExt = limUnder` is the limit from off the axis given by `AxisEvNvLimit`. -/
theorem rawAxisContinuous_of_decay (hN : AxisEvNvLimit) (Pl : PlanarData) (L : ReturnLevel)
    (g : ℝ → ℝ) (hd : AxisEvDecay (UnforcedLeray.Cons.C03.rawProfile L.ε L.train.v L.train.ψ) g) :
    RawAxisContinuous Pl L := by
  intro τ y hy
  set f : Space → Space :=
    Nv L.ε⁻¹ (UnforcedLeray.Cons.C03.rawProfile L.ε L.train.v L.train.ψ) τ with hf
  have hlim : Tendsto f (𝓝[axisᶜ] y) (𝓝 (g (y 2) • e3)) :=
    hN _ _ g (inv_pos.2 L.ε_pos) hd τ y hy
  have hseq := tendsto_shift y hy
  have : (𝓝[axisᶜ] y).NeBot := hseq.neBot
  have hraw : rawU Pl L τ = UnforcedLeray.Cons.C03.Concrete.axisExt f := rfl
  have hval : rawU Pl L τ y = g (y 2) • e3 := by
    rw [hraw]
    simp only [UnforcedLeray.Cons.C03.Concrete.axisExt, hy, ↓reduceIte]
    exact hlim.limUnder_eq
  rw [hval]
  refine (hlim.comp hseq).congr fun n => ?_
  rw [hraw]
  exact (UnforcedLeray.Cons.C03.Concrete.axisExt_of_not_mem (shift_not_mem_axis y hy n)).symm

end AxisEvOrg

/-- **`AxisEv` from the two source facts** (source 1205-1235, 1310-1323): `ν_n → 0`
(`retNu_tendsto`, `ω ≠ 0` from the standing hypotheses), so for large `n` the BUC train of level
`n` is in the range of `AxisEvTrainDecay`, and `AxisEvNvLimit` gives the continuous extension. -/
theorem axisEv_of (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp)
    (hN : AxisEvNvLimit) (hT : AxisEvTrainDecay) : AxisEv D dm dp := by
  obtain ⟨ν₀, hν₀, hT⟩ := hT
  have hev : ∀ᶠ n : ℕ in atTop, retNu D.Pl D.σ₀ n < ν₀ :=
    (retNu_tendsto D.σ₀ hst.omega_ne).eventually (gt_mem_nhds hν₀)
  filter_upwards [hev] with n hn _
  exact AxisEvOrg.rawAxisContinuous_of_decay hN D.Pl (D.level n) _
    (hT (retNu D.Pl D.σ₀ n) (retNu_pos _ _ _) hn.le (D.train n) (D.train_buc n)
      (retEps D.Pl D.σ₀ n))

end UnforcedLeray.Short.PartIIIb.Concrete
