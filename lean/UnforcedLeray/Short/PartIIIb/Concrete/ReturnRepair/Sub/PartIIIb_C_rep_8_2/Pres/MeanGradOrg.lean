import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.PresCoef
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_7.L1
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_7.L3
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_9_5
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.N0
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AsymMu

/-!
# The mean-field gradient estimate `MeanGrad` (`PartIII-b:C/rep/8/2/pres/5/org`)

Source of record: `the November 2 reference manuscript`
(73 pages).

`MeanGradAt` (`Sub/PartIII-b_C_rep_8_2/PresCoef.lean`) is the general thin-source estimate
"`‖DX‖_{L^∞_τL^{22/3}} ≤ P_ν ε^{57/22}N₁`" (source 5282-5284) for the phase-mean zero-width
Newton field `X^mt, Y^mt = D_{μ+1}X^mt` with the stream cutoff (5380-5387), together with `DY`
(the pair of `repair:phase-gradient`, 5214-5217) and `D²X` ("an additional curvature power",
5267-5268).  The source argument has two steps:

* **pointwise kernel bound** (5400-5413 and 5203-5205): "the gradient Newton kernel has degree
  `-5`, and the ratio of the old source radius to the young receiver radius is at most
  `1/√1.2 < 1`"; "the outward stream primitive has the same degree"; "fixed conormal derivatives
  of `χ̂_y(νs)` are bounded".  At the chart point `y = (R/√s, 0, η/√s)`, `R = ε⁻¹`, the scaled
  point is `w = εy = (s^{-1/2}, 0, εη/√s)`, `|w|² = (1 + ε²η²)/s`, and the degree `-5` kernel
  gives `|DX^mt| + |DY^mt| + |D²X^mt| ≤ P_ν ε³ s^{5/2}(1 + ε²η²)^{-1/2} N` on the young range
  `s ≤ 1/ν` (`ε³` from `W^mt(y) = ε²V(εy)`, 4784); the stream cutoff vanishes for `s ≥ 1/ν`
  (4161-4166).  (`MeanJetKernelPt`.)  The decay `(1 + ε²η²)^{-1/2}` is the weakest one among the
  terms: on the cutoff transition `ν ≤ r² ≤ 5ν/4` the stream term `(χ_y'/r)Ψ_Z e_z` has
  `Ψ_Z = O(N|w|^{-2})` only, and `y·∇` costs a factor `|w|` in `DY`.
* **the `(s, η)` integration** (5203-5217: "the pointwise gradient kernel has `L^{22/3}` norm
  `CD^{-101/22}`"; the physical Jacobian `πR²s^{-5/2}ds dη` and normalized phase `dq/c`,
  2681-2688): `‖ε³s^{5/2}(1+ε²η²)^{-1/2}1_{s≤1/ν}‖_{L^{22/3}(πR²s^{-5/2}ds dq/c dη)}
  = (π ε^{19} ∫_0^{1/ν}s^{95/6}ds ∫(1+t²)^{-11/3}dt)^{3/22} ≤ P_ν ε^{57/22}`
  (`19·3/22 = 57/22`).  (`YoungJetWeightInt`.)

**The pointwise bound is decomposed** (`meanJetKernelPt` is an assembly):
* `SCPsiBoundOff` — the outward primitive off the ray: `‖∂^mΨ_Z(y)‖ ≤ C₁ B r^{-m}|y|^{-2}`
  (`m ≤ 3`, `ν ≤ r²`), the off-ray form of `SCPsiBound` (`r^{-2-m}`, no decay in the height);
* `SCXJetOff` — the stream-cut field off the ray: `‖∂^m𝒞_yZ(y)‖ ≤ C₄ B r^{-2-m}|y|^{-2}`
  (Leibniz, as `scXJet_of_parts`);
* `XmtJetOff` — the same for `X^mt` at `ε = 1` with `B = P·N₀^χ(M)` (**proved here**,
  `xmtJetOff_of`, from `newtonVCutBound` as in `clockEps1_of`);
* `MeanJetScaleBound` — calculus: the jet density of `(ε²X(ε·), D_{μ+1}(ε²X(ε·)))` at `y` is
  `≤ 100 ε³(|DX(w)| + (1+|w|)|D²X(w)| + ν|D³X(w)|)`, `w = εy`.

**Proved here:** `meanJetDens_measurable` (any `X, Y`: `measurable_fderiv`), `xmtJetOff_of`,
`meanGradAt_of`, `meanGrad_of : MeanJetKernelPt χo χy → YoungJetWeightInt → D.MeanGrad`
(with `n0cutLeN1 : N₀^χ ≤ N₁(χ_oM)`, source 5400).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

/-! ## 1. The weight and the two source Props -/

/-- The young chart weight `ε³ s^{5/2} (1 + ε²η²)^{-1/2} 1_{0<s≤1/ν}` at `p = (s, (q, η))`
(source 5400-5413: degree `-5` at `|w|² = (1+ε²η²)/s`, `W^mt = ε²V(ε·)`, 4784; young support
`s ≤ 1/ν` of the stream cutoff, 4161-4166). -/
def youngJetWeight (ν ε : ℝ) (p : Chart) : ℝ :=
  if 0 < p.1 ∧ p.1 ≤ 1 / ν then
    ε ^ 3 * p.1 ^ (5 / 2 : ℝ) * (1 + (ε * p.2.2) ^ 2) ^ (-(1 / 2 : ℝ))
  else 0

/-- **The pointwise kernel bound for the mean field** (source 5380-5387, 5400-5413, 5203-5205,
5267-5268; `X^mt = 𝒞_y(W^mt_μ - W^mt_{μ+1})`, `W^mt(y) = ε²V(εy)`, 4776-4791, `Y^mt = D_{μ+1}X^mt`,
5455): at every chart point `y = (R/√s, 0, η/√s)`, `R = ε⁻¹`, the jet density
`|DY^mt| + Σ|∂_jX^mt| + Σ|∂_j∂_lX^mt|` is at most `P_ν ε³s^{5/2}(1+ε²η²)^{-1/2}N₀^χ(M)` for
`s ≤ 1/ν` and vanishes for `s > 1/ν`, with `N₀^χ` the cut old moment (`oldN0cut`, 4924-4927,
5400).  Uniform in `c, ν ≤ 1, ε ≤ 1, μ ∈ (0, 1/4)`. -/
def MeanJetKernelPt (χo χy : ℝ → ℝ) : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ (c ν ε μ : ℝ), LHyp c ν ε μ χo χy → ε ≤ 1 →
    ∀ M : Chart → Mat3, OldThinFinite c ν M → ∀ (τ : ℝ) (p : Chart), 0 < p.1 →
      meanJetDens (Xmean c ν ε μ χo χy M τ) (Ymean c ν ε μ χo χy M τ)
          (NearInst.chartY ε⁻¹ p) ≤
        C * ν⁻¹ ^ k * youngJetWeight ν ε p * oldN0cut c ν χo M

/-- **The `(s, η)` integration** (source 5203-5217 with the chart measure 2681-2688): the
`L^{22/3}` norm of the young weight for `πR²s^{-5/2}ds dq/c dη`, `R = ε⁻¹`, is
`≤ P_ν ε^{57/22}` (`π ε^{20}·ε⁻¹·∫_0^{1/ν}s^{-5/2+55/3}ds·∫(1+t²)^{-11/3}dt`, `19·3/22 = 57/22`;
`5282-5284`). -/
def YoungJetWeightInt : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ (ν ε c : ℝ), 0 < ν → ν ≤ 1 → 0 < ε → 0 < c →
    eLpNorm (youngJetWeight ν ε) (22 / 3) (ringPhysμ ε⁻¹ c) ≤
      ENNReal.ofReal (C * ν⁻¹ ^ k * ε ^ (57 / 22 : ℝ))

/-! ## 2. The decomposition of the pointwise bound -/

/-- **The outward primitive off the ray** (source 4180-4182, 5400-5413: "the outward stream
primitive has the same degree"): `Ψ_Z(y) = -∫_r^∞ ρZ_z(ρ, z)dρ` with `|∂^mZ(w)| ≤ B|w|^{-4-m}`
has `|∂^mΨ_Z(y)| ≤ C₁Br^{-m}|y|^{-2}` for `m ≤ 3`, `ν ≤ r²` (`∫_r^∞ ρ^{1+a}(ρ²+z²)^{-2-a/2}dρ ≤
|y|^{-2}/2`; the Cartesian derivatives of `r` cost `r^{-1}`).  Off-ray form of `SCPsiBound`. -/
def SCPsiBoundOff : Prop :=
  ∃ C1 : ℝ, ∀ (ν B : ℝ) (Z : Vec3 → Vec3), 0 < ν → 0 ≤ B → SCZHyp ν B Z →
    ∀ m : ℕ, m ≤ 3 → ∀ y : Vec3, ν ≤ cylR y ^ 2 →
      ‖iteratedFDeriv ℝ m (streamPsi Z) y‖ ≤ C1 * B * cylR y ^ (-(m : ℝ)) * (eucSq y)⁻¹

/-- **The stream-cut field off the ray** (source 4178-4186, 5400-5413: `𝒞_yZ = χ_yZ +
(χ_y'/r)Ψ_Ze_z`, fixed conormal derivatives of `χ̂_y(νs)` bounded): `|∂^m𝒞_yZ(y)| ≤
C₄Br^{-2-m}|y|^{-2}` for `m ≤ 3`, `ν ≤ r²` (`|y|^{-4-k} ≤ r^{-2-k}|y|^{-2}`). -/
def SCXJetOff (χy : ℝ → ℝ) : Prop :=
  ∃ C4 : ℝ, ∀ (ν B : ℝ), 0 < ν → 0 ≤ B → ∀ Z : Vec3 → Vec3, SCZHyp ν B Z → IsStreamCutoff χy →
    ∀ y : Vec3, ν ≤ cylR y ^ 2 → ∀ m : ℕ, m ≤ 3 →
      ‖iteratedFDeriv ℝ m (streamCut ν 1 χy Z) y‖ ≤
        C4 * B * cylR y ^ (-(2 : ℝ) - m) * (eucSq y)⁻¹

/-- **The mean field off the ray at `ε = 1`** (source 4776-4791, 4870-4900, 5400-5413):
`|∂^mX^mt_1(w)| ≤ C r^{-2-m}|w|^{-2}N₀^χ(M)`, `m ≤ 3`, `ν ≤ r²`. -/
def XmtJetOff (χo χy : ℝ → ℝ) : Prop :=
  ∃ C : ℝ, ∀ (c ν μ : ℝ), LHyp c ν 1 μ χo χy → ∀ M : Chart → Mat3, OldThinFinite c ν M →
    ∀ w : Vec3, ν ≤ cylR w ^ 2 → ∀ m : ℕ, m ≤ 3 →
      ‖iteratedFDeriv ℝ m (Xmt c ν 1 μ χo χy M) w‖ ≤
        C * cylR w ^ (-(2 : ℝ) - m) * (eucSq w)⁻¹ * oldN0cut c ν χo M

/-- **The jet density under the scaling `X ↦ ε²X(ε·)`** (calculus; source 4784, 5455:
`X^mt_ε(y) = ε²X^mt_1(εy)` (`Scale.Xmt_smul`), `Y^mt = (-½y·∇ - νΔ + μ + ½)X^mt`): with
`w = εy`, `|DX_ε(y)| = ε³|DX(w)|`, `|D²X_ε(y)| = ε⁴|D²X(w)|`, `|y||D²X_ε(y)| = ε³|w||D²X(w)|`,
`|DΔX_ε(y)| ≤ 3ε⁵|D³X(w)|`; the Euclidean/sup norm changes cost `√3`. -/
def MeanJetScaleBound : Prop :=
  ∀ (X : Vec3 → Vec3) (ε ν μ : ℝ), ContDiff ℝ 3 X → 0 < ε → ε ≤ 1 → 0 ≤ ν → 0 ≤ μ →
    μ ≤ 1 / 4 → ∀ y : Space,
      meanJetDens (fun y' : Space => WithLp.toLp 2 (JetClockCore.Xsc X ε (WithLp.ofLp y')))
          (fun y' : Space =>
            WithLp.toLp 2 (JetClockCore.Yf (JetClockCore.Xsc X ε) ν μ (WithLp.ofLp y'))) y ≤
        100 * ε ^ 3 * (‖iteratedFDeriv ℝ 1 X (ε • WithLp.ofLp y)‖ +
          (1 + Real.sqrt (eucSq (ε • WithLp.ofLp y))) *
            ‖iteratedFDeriv ℝ 2 X (ε • WithLp.ofLp y)‖ +
          ν * ‖iteratedFDeriv ℝ 3 X (ε • WithLp.ofLp y)‖)

/-! ## 3. Elementary facts -/

theorem youngJetWeight_nonneg (ν : ℝ) {ε : ℝ} (hε : 0 ≤ ε) (p : Chart) :
    0 ≤ youngJetWeight ν ε p := by
  unfold youngJetWeight
  split_ifs with h
  · exact mul_nonneg (mul_nonneg (pow_nonneg hε 3) (Real.rpow_nonneg h.1.le _))
      (Real.rpow_nonneg (by positivity) _)
  · exact le_rfl

/-- The jet density of any pair of fields is Borel measurable (`measurable_fderiv` needs no
regularity). -/
theorem meanJetDens_measurable (X Y : Space → Space) : Measurable (meanJetDens X Y) := by
  have h1 : Measurable fun y => ‖fderiv ℝ Y y‖ := (measurable_fderiv ℝ Y).norm
  have h2 : ∀ j : Fin 3, Measurable fun y => ‖physPd X j y‖ := fun j =>
    (measurable_fderiv_apply_const ℝ X (coordinateVector j)).norm
  have h3 : ∀ j l : Fin 3, Measurable fun y => ‖physPd2 X j l y‖ := fun j l =>
    (measurable_fderiv_apply_const ℝ (fun y' => physPd X l y') (coordinateVector j)).norm
  have h2s : Measurable fun y => ∑ j : Fin 3, ‖physPd X j y‖ :=
    Finset.measurable_fun_sum _ fun j _ => h2 j
  have h3s : Measurable fun y => ∑ j : Fin 3, ∑ l : Fin 3, ‖physPd2 X j l y‖ :=
    Finset.measurable_fun_sum _ fun j _ => Finset.measurable_fun_sum _ fun l _ => h3 j l
  exact (h1.add h2s).add h3s

theorem mg_measurable_chartY (R : ℝ) : Measurable (NearInst.chartY R) := by
  unfold NearInst.chartY
  have : Measurable fun p : Chart =>
      (![R / Real.sqrt p.1, 0, p.2.2 / Real.sqrt p.1] : Fin 3 → ℝ) := by
    refine measurable_pi_lambda _ fun i => ?_
    fin_cases i <;> simp <;> fun_prop
  exact (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).measurable.comp this

/-! ## 4. `XmtJetOff` from the stream-cut bound and the Newton kernel -/

/-- **`xmtJetOff_of`**: `X^mt_1 = 𝒞_y(V_μ - V_{μ+1})` and `V_μ, V_{μ+1}` satisfy the receiver
bounds `|∂^mV(w)| ≤ C_mN₀^χ|w|^{-4-m}` (`NewtonVCutBound`, source 4776-4782, 4870-4900). -/
theorem xmtJetOff_of {χo χy : ℝ → ℝ} (hV : NewtonVCutBound χo) (hS : SCXJetOff χy) :
    XmtJetOff χo χy := by
  obtain ⟨C, hC⟩ := hV
  obtain ⟨C4, hC4⟩ := hS
  set S : ℝ := ∑ m ∈ Finset.range 8, (|C m| + |C m|) with hSdef
  have hSnn : 0 ≤ S := Finset.sum_nonneg fun m _ => by positivity
  refine ⟨|C4| * S, ?_⟩
  intro c ν μ h M hM w hw m hm
  have hN0 := oldN0cut_nonneg c ν h.nu_pos h.chiO M
  have hmu0 : 0 ≤ μ := h.mu_pos.le
  have hmu1 : 0 ≤ μ + 1 := by linarith
  obtain ⟨h1, h1b⟩ := hC c ν μ h.c_pos h.nu_pos h.chiO hmu0 M hM
  obtain ⟨h2, h2b⟩ := hC c ν (μ + 1) h.c_pos h.nu_pos h.chiO hmu1 M hM
  have hY : ∀ μ' : ℝ, youngW c ν 1 μ' χo M = newtonV c ν μ' χo M := by
    intro μ'; funext y; simp [youngW]
  set Z : Vec3 → Vec3 := newtonV c ν μ χo M - newtonV c ν (μ + 1) χo M with hZ
  have hopen : IsOpen {w : Vec3 | ν * (11 / 12) < eucSq w} := by
    unfold eucSq
    exact isOpen_lt continuous_const (by fun_prop)
  have hZs : ContDiffOn ℝ 7 Z {w | ν * (11 / 12) < eucSq w} := h1.sub h2
  have hZb : ∀ m : ℕ, m ≤ 7 → ∀ w : Vec3, ν * (11 / 12) < eucSq w →
      ‖iteratedFDeriv ℝ m Z w‖ ≤
        (S * oldN0cut c ν χo M) * (Real.sqrt (eucSq w)) ^ (-(4 : ℝ) - m) := by
    intro m hm w hw
    have hat1 : ContDiffAt ℝ 7 (newtonV c ν μ χo M) w := h1.contDiffAt (hopen.mem_nhds hw)
    have hat2 : ContDiffAt ℝ 7 (newtonV c ν (μ + 1) χo M) w :=
      h2.contDiffAt (hopen.mem_nhds hw)
    have hmle : (m : WithTop ℕ∞) ≤ 7 := by exact_mod_cast hm
    rw [hZ, iteratedFDeriv_sub_apply (hat1.of_le hmle) (hat2.of_le hmle)]
    have hp : 0 ≤ (Real.sqrt (eucSq w)) ^ (-(4 : ℝ) - m) :=
      Real.rpow_nonneg (Real.sqrt_nonneg _) _
    have hb1 := h1b m hm w hw
    have hb2 := h2b m hm w hw
    have hSm : |C m| + |C m| ≤ S :=
      Finset.single_le_sum (f := fun m => |C m| + |C m|) (fun m _ => by positivity)
        (Finset.mem_range.2 (by omega))
    have hCm : C m + C m ≤ S := le_trans (add_le_add (le_abs_self _) (le_abs_self _)) hSm
    calc ‖iteratedFDeriv ℝ m (newtonV c ν μ χo M) w -
            iteratedFDeriv ℝ m (newtonV c ν (μ + 1) χo M) w‖
        ≤ ‖iteratedFDeriv ℝ m (newtonV c ν μ χo M) w‖ +
            ‖iteratedFDeriv ℝ m (newtonV c ν (μ + 1) χo M) w‖ := norm_sub_le _ _
      _ ≤ C m * oldN0cut c ν χo M * (Real.sqrt (eucSq w)) ^ (-(4 : ℝ) - m) +
          C m * oldN0cut c ν χo M * (Real.sqrt (eucSq w)) ^ (-(4 : ℝ) - m) :=
          add_le_add hb1 hb2
      _ = (C m + C m) * (oldN0cut c ν χo M * (Real.sqrt (eucSq w)) ^ (-(4 : ℝ) - m)) := by
          ring
      _ ≤ S * (oldN0cut c ν χo M * (Real.sqrt (eucSq w)) ^ (-(4 : ℝ) - m)) :=
          mul_le_mul_of_nonneg_right hCm (mul_nonneg hN0 hp)
      _ = (S * oldN0cut c ν χo M) * (Real.sqrt (eucSq w)) ^ (-(4 : ℝ) - m) := by ring
  have hL : Xmt c ν 1 μ χo χy M = streamCut ν 1 χy Z := by
    funext y'
    simp only [Xmt, hY, hZ]
  rw [hL]
  have key := hC4 ν (S * oldN0cut c ν χo M) h.nu_pos (mul_nonneg hSnn hN0) Z ⟨hZs, hZb⟩
    h.chiY w hw m hm
  have hr : 0 ≤ cylR w ^ (-(2 : ℝ) - m) := Real.rpow_nonneg (Real.sqrt_nonneg _) _
  have he : 0 ≤ (eucSq w)⁻¹ := inv_nonneg.2 (Finset.sum_nonneg fun i _ => sq_nonneg (w i))
  have hX : 0 ≤ S * oldN0cut c ν χo M * cylR w ^ (-(2 : ℝ) - m) * (eucSq w)⁻¹ :=
    mul_nonneg (mul_nonneg (mul_nonneg hSnn hN0) hr) he
  calc ‖iteratedFDeriv ℝ m (streamCut ν 1 χy Z) w‖
      ≤ C4 * (S * oldN0cut c ν χo M) * cylR w ^ (-(2 : ℝ) - m) * (eucSq w)⁻¹ := key
    _ = C4 * (S * oldN0cut c ν χo M * cylR w ^ (-(2 : ℝ) - m) * (eucSq w)⁻¹) := by ring
    _ ≤ |C4| * (S * oldN0cut c ν χo M * cylR w ^ (-(2 : ℝ) - m) * (eucSq w)⁻¹) :=
        mul_le_mul_of_nonneg_right (le_abs_self _) hX
    _ = |C4| * S * cylR w ^ (-(2 : ℝ) - m) * (eucSq w)⁻¹ * oldN0cut c ν χo M := by ring

/-! ## 5. `MeanGrad` from the pointwise bound and the integration -/

section Regime

variable (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)

/-- **`meanGradAt_of`** (one regime): Hölder-free, `‖f‖_{L^{22/3}} ≤ P_ν N₀^χ‖w_young‖_{L^{22/3}}`
with `N₀^χ ≤ N₁(χ_oT₁)` (`n0cutLeN1`, source 5400). -/
theorem meanGradAt_of (hν1 : L.ν ≤ 1) (hε1 : L.ε ≤ 1) (hμ0 : 0 < μ) (hμ1 : μ < 1 / 4)
    (hmZ : 3 / 2 < K.mZ) (hγ : 0 < gRate Pl) (hχy : IsStreamCutoff K.χy)
    {C1 : ℝ} {k1 : ℕ}
    (h1 : ∀ (c ν ε μ : ℝ), LHyp c ν ε μ K.χo K.χy → ε ≤ 1 →
      ∀ M : Chart → Mat3, OldThinFinite c ν M → ∀ (τ : ℝ) (p : Chart), 0 < p.1 →
        meanJetDens (Xmean c ν ε μ K.χo K.χy M τ) (Ymean c ν ε μ K.χo K.χy M τ)
            (NearInst.chartY ε⁻¹ p) ≤
          C1 * ν⁻¹ ^ k1 * youngJetWeight ν ε p * oldN0cut c ν K.χo M)
    {C2 : ℝ} {k2 : ℕ}
    (h2 : ∀ (ν ε c : ℝ), 0 < ν → ν ≤ 1 → 0 < ε → 0 < c →
      eLpNorm (youngJetWeight ν ε) (22 / 3) (ringPhysμ ε⁻¹ c) ≤
        ENNReal.ofReal (C2 * ν⁻¹ ^ k2 * ε ^ (57 / 22 : ℝ))) :
    MeanGradAt Pl K L μ (|C1| * |C2|) (k1 + k2) := by
  intro T
  have hν := L.ν_pos
  have hε := L.ε_pos
  have hc : 0 < cOf L.ν := cOf_pos hν
  obtain ⟨CN, kN, hCN⟩ := sourceLN0 K.mZ (gRate Pl) hmZ hγ
  have hfin : OldThinFinite (cOf L.ν) L.ν (thinRep T) :=
    (hCN (cOf L.ν) L.ν (L.ρb Pl K) hc hν hν1 T).1
  have hL : LHyp (cOf L.ν) L.ν L.ε μ K.χo K.χy :=
    ⟨hc, hν, hν1, hε, hμ0, hμ1, K.hχo, hχy⟩
  set Xm := Xmean (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T) with hXm
  set Ym := Ymean (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T) with hYm
  set f : Chart → ℝ := ringRead L.ε⁻¹ fun τ => meanJetDens (Xm τ) (Ym τ) with hf
  set N0 : ℝ := oldN0cut (cOf L.ν) L.ν K.χo (thinRep T) with hN0def
  have hN0 : 0 ≤ N0 := oldN0cut_nonneg _ _ hν K.hχo _
  have hP1 : 0 ≤ L.ν⁻¹ ^ k1 := by positivity
  have hP2 : 0 ≤ L.ν⁻¹ ^ k2 := by positivity
  set A : ℝ := |C1| * L.ν⁻¹ ^ k1 * N0 with hAdef
  have hA0 : 0 ≤ A := by positivity
  set μp := ringPhysμ L.ε⁻¹ (cOf L.ν) with hμp
  -- measurability: `Xm`, `Ym` do not depend on the phase
  have hfm : Measurable f := by
    have e : f = fun p => meanJetDens (Xm 0) (Ym 0) (NearInst.chartY L.ε⁻¹ p) := rfl
    rw [e]
    exact (meanJetDens_measurable _ _).comp (mg_measurable_chartY _)
  refine ⟨hfm.aestronglyMeasurable, ?_⟩
  -- the pointwise bound, a.e. (`0 < s` a.e.)
  have hae : ∀ᵐ p ∂μp, 0 < p.1 := by
    rw [hμp]
    unfold ringPhysμ
    exact Measure.ae_smul_measure (ae_ageμ_fst_pos _ _) _
  have hpt : ∀ᵐ p ∂μp, ‖f p‖ ≤ (A • youngJetWeight L.ν L.ε) p := by
    filter_upwards [hae] with p hp
    have e1 := h1 (cOf L.ν) L.ν L.ε μ hL hε1 (thinRep T) hfin (NearInst.chartTau L.ε⁻¹ p) p hp
    have hd : 0 ≤ f p := meanJetDens_nonneg _ _ _
    have hw : 0 ≤ youngJetWeight L.ν L.ε p := youngJetWeight_nonneg _ hε.le p
    rw [Real.norm_of_nonneg hd, Pi.smul_apply, smul_eq_mul]
    calc f p ≤ C1 * L.ν⁻¹ ^ k1 * youngJetWeight L.ν L.ε p * N0 := e1
      _ ≤ |C1| * L.ν⁻¹ ^ k1 * youngJetWeight L.ν L.ε p * N0 := by
          gcongr
          exact le_abs_self _
      _ = A * youngJetWeight L.ν L.ε p := by rw [hAdef]; ring
  have hN1 : ENNReal.ofReal N0 ≤ oldN1 Pl K L T :=
    n0cutLeN1 (cOf L.ν) L.ν K.χo hc hν K.hχo (thinRep T) hfin
  have hint := h2 L.ν L.ε (cOf L.ν) hν hν1 hε hc
  have hC2 : C2 * L.ν⁻¹ ^ k2 * L.ε ^ (57 / 22 : ℝ) ≤ |C2| * L.ν⁻¹ ^ k2 * L.ε ^ (57 / 22 : ℝ) := by
    have : 0 ≤ L.ν⁻¹ ^ k2 * L.ε ^ (57 / 22 : ℝ) := by positivity
    nlinarith [le_abs_self C2]
  calc eLpNorm f (22 / 3) μp ≤ eLpNorm (A • youngJetWeight L.ν L.ε) (22 / 3) μp :=
        eLpNorm_mono_ae_real hpt
    _ = ENNReal.ofReal A * eLpNorm (youngJetWeight L.ν L.ε) (22 / 3) μp := by
        rw [eLpNorm_const_smul, Real.enorm_eq_ofReal hA0]
    _ ≤ ENNReal.ofReal A * ENNReal.ofReal (|C2| * L.ν⁻¹ ^ k2 * L.ε ^ (57 / 22 : ℝ)) := by
        gcongr
        exact hint.trans (ENNReal.ofReal_le_ofReal hC2)
    _ = ENNReal.ofReal (|C1| * |C2| * L.ν⁻¹ ^ (k1 + k2) * L.ε ^ (57 / 22 : ℝ)) *
          ENNReal.ofReal N0 := by
        rw [← ENNReal.ofReal_mul hA0, ← ENNReal.ofReal_mul (by positivity), hAdef, pow_add]
        congr 1
        ring
    _ ≤ ENNReal.ofReal (|C1| * |C2| * L.ν⁻¹ ^ (k1 + k2) * L.ε ^ (57 / 22 : ℝ)) *
          oldN1 Pl K L T := by
        gcongr

end Regime

/-- **`meanGrad_of`**: `MeanGrad` along the sequence from the pointwise kernel bound and the
`(s, η)` integration (source 5282-5284 with 5203-5217, 5380-5387, 5400-5413). -/
theorem meanGrad_of (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp)
    (h1 : MeanJetKernelPt D.K.χo D.K.χy) (h2 : YoungJetWeightInt) : D.MeanGrad := by
  obtain ⟨C1, k1, hC1⟩ := h1
  obtain ⟨C2, k2, hC2⟩ := h2
  refine ⟨|C1| * |C2|, k1 + k2, ?_⟩
  filter_upwards [retNu_retEps_eventually_le_one hst.omega_ne hst.gamma_pos D.coeff_ne,
    mu_eventually_mem D hst.omega_ne hst.sigma_pos hst.sigma_lt] with n hle hmu z hz
  have hmz := hmu z hz
  have hs := hst.sigma_pos
  have hs1 := hst.sigma_lt
  exact meanGradAt_of D.Pl D.K (D.level n) (D.mu n z) hle.1 hle.2
    (by linarith [hmz.1]) (by linarith [hmz.2]) hst.mZ_gt hst.gamma_pos hst.chiY hC1 hC2

end UnforcedLeray.Short.PartIIIb.Concrete
