import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.rawSmoothBdd_Sub.Sub.RingLiftDerivSource
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_4_1_1_2_org
import UnforcedLeray.Short.PartIIb.Sub.R1_5
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.InletSourcePtw.Fields.RawJointSmooth.RawParityForm.HeatTermParity
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.InletSourcePtw.Fields.RawJointSmooth.RawParityForm.RawStreamProfile
import UnforcedLeray.Short.PartI.Tasks.TrainMeanEquations.StreamSmooth

/-!
# Organizer `PartIII-b:C/ward/12/3/1/2/6/1/3/1/org/1/org/1`: `RingLiftOffAxisDerivBdd`

Source of record: `the November 2 reference manuscript`
(SP), lines 1305-1325 (proof of Proposition `sct:lift`: "Smoothness at the axis follows term by
term from the full heat expansion `r a_{2j} ∂_η^{2j} G_{νs} = a_{2j} r^{2j+2} R^{-(2j+1)}
∂_z^{2j} G_{νt}(z)`. After `a` radial derivatives the remainder after order `N` is `O(r^{2N+4-a})`
...; fluctuations are flat ... The same argument with the finite needed expansion order proves
`‖U_R‖_{W^{k,∞}} ≤ P_k`"), with SP 438-467 (Lemma `sct:heat`: `sct:fluctuation` with the weights
`⟨η⟩^m`, `sct:expansion` with the weights `η^m`, `sct:transverse`) and SP 427-435 (all orders at fixed
parameters, one smallness threshold).

## The argument

Off the axis `U_R(τ) = N_v b(τ, ·)` with `b = ringStreamProfile R Ψ`, `Ψ(s,(q,η)) = ψ(s,(q,η))` the
train stream (`B0190.simProfile_liftVelocity_eq_Nv`, `rawProfile_eq_merProfile_of_smooth`,
`rawStreamProfile`).  Each Cartesian derivative of `N_v b` costs one profile derivative, powers of
`1 + s` and one factor `1 + |η|` (`∂_ϱ η = -η/ϱ`): `RingLiftPtJet` (pointwise form of the proved
`RingLiftOffAxis`), and `‖D^l b‖ ≲ (1 + s + |η|) ∑_{i ≤ l+1} ‖D^i Ψ‖` (`RingProfileMeridJet`, from the
proved `RingProfileJet`).  So (`nv_jet_le`)
`‖D^k N_v(ringStreamProfile R Φ)(τ, y)‖ ≤ C (1+s)^{K+1} (1+|η|)^{k+1} ∑_{i ≤ k+1} ‖D^i Φ(chart y)‖`.

* (iii) far from the axis, `s = age ≤ 4`: the transverse weights of the train at bounded ages
  (`TrainStreamWtdBdd`, SP 439-467) bound the right side.
* near the axis, `s > 4` (`ϱ² < R²`): split `Ψ = ∑_{j ≤ N} a_{2j} ∂_η^{2j} G_{νs} + Φ_N`
  (`heatRemainder`). (i) The `j`-th heat term lifts to the explicit field `heatField ν R j` (parity
  coefficients `heatParG`, `heatParH`, polynomial in `w = ϱ²`, Gaussian in `z`; `HeatTermParity`,
  SP 1310-1313), whose Cartesian derivatives are bounded on `ϱ² ≤ W` (`HeatFieldJet`).
  (ii) The remainder: the weighted heat expansion (`TrainHeatRemWtd`, SP 439-458, fluctuation flat
  `e^{-κνs/c²}`, mean remainder `s^{-N-3/2}` with weights `(η/√s)^m`) gives
  `(1+|η|)^{k+1}‖D^iΦ_N‖ ≤ C s^{(k+1)/2-N-3/2}`, and with the finite order `N = K + k + 2` the factor
  `(1+s)^{K+1}` is absorbed.

The transverse weights are necessary: without them `∂_ϱ` of the lift at large `|y₃|` is not
controlled (`∂_ϱ η = -η/ϱ`, cf. `not_chartJets` in `Short/PartII-b/Sub/PartII-b_G4_5_2_1_2.lean`).

## Contents

Definitions: `heatField`, `heatSum` (explicit heat-term fields).
Leaf Props: `TrainHeatRemWtd`, `TrainStreamWtdBdd` (Part I source facts at fixed parameters),
`CompChartPtJet`, `RingLiftPtJet`, `RingProfileMeridJet`, `ProfileDerivBdd`, `HeatFieldJet` (calculus).
Proved here: `contDiff_heatField`, `contDiff_heatSum`, `heatSum_jet_le`, `age_pos_of`,
`parity_heat_decomp`, `Nv_heat_decomp`, `nv_jet_le`, and
`ringLiftOffAxisDerivBdd_of (hN : TrainHeatRemWtd) (hF : TrainStreamWtdBdd) (hJ : RingLiftPtJet)
(hP : RingProfileMeridJet) (hH : HeatFieldJet) : RingLiftOffAxisDerivBdd`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

open Set Filter Topology
open scoped ContDiff
open UnforcedLeray UnforcedLeray.Short.IIb

/-! ## The heat-term fields -/

/-- **The lift of the `j`-th heat term** (SP 1310-1313: `r a_{2j}∂_η^{2j}G_{νs} =
a_{2j} r^{2j+2} R^{-(2j+1)} ∂_z^{2j}G_{νt}(z)`), in Cartesian similarity variables:
`heatParG ν R j • hor y + heatParH ν R j • e₃` at `(w, z) = (y₀² + y₁², y₃)`, i.e.
`-R^{-(2j+1)} w^j g_ν^{(2j+1)}(y₃) (y₀, y₁, 0) + (2j+2) R^{-(2j+1)} w^j g_ν^{(2j)}(y₃) e₃`
(`g_ν = B0191.profile ν`).  Off the axis it is `N_v` of the ring stream profile of the heat term
(`Nv_heat_decomp`); it does not depend on the phase `τ`. -/
def heatField (ν R : ℝ) (j : ℕ) (y : Space) : Space :=
  heatParG ν R j (0, (y 0 ^ 2 + y 1 ^ 2, y 2)) • Axi.hor y +
    heatParH ν R j (0, (y 0 ^ 2 + y 1 ^ 2, y 2)) • Axi.e3

/-- The lift of the first `N + 1` heat terms with coefficients `a` (`a_{2j} = PartI.meanCoeff`). -/
def heatSum (ν R : ℝ) (a : ℕ → ℝ) (N : ℕ) (y : Space) : Space :=
  ∑ j ∈ Finset.range (N + 1), a j • heatField ν R j y

/-! ## Leaf Props: the train (Part I source facts at fixed parameters) -/

/-- **Weighted heat remainder of the train stream, at fixed parameters** (source fact; SP 439-458,
Lemma `sct:heat`, at fixed parameters as SP 427-435).

For `ρ > 1/2` there is one threshold `ν₀` such that for every BUC train with `c = ν^{-ρ}`,
`ν ≤ ν₀`, and all orders `N, m, i`: the stream minus its first `N + 1` heat terms,
`Φ_N = ψ − ∑_{j≤N} a_{2j}∂_η^{2j}G_{νs} = ψ̃ + R_N` (`heatRemainder`, `a = PartI.meanCoeff`), has
`(1 + |η|)^m ‖D^i Φ_N(s, q, η)‖ ≤ C s^{m/2 − N − 3/2}` for `s ≥ 1`, all `q, η` (`D^i` the full
`i`-th derivative in `(s, q, η)`).  Source: `sct:fluctuation` (SP 440-445, weight `⟨η⟩^m`, every
mixed age/spatial derivative of `ψ̃` is `≤ P e^{-κνs/c²}`, which is `O(s^{-N-3/2})` at fixed
parameters) and `sct:expansion` (SP 455-458, `‖η^m ∂_η^b ∂_s^ℓ R_N(s)‖_∞ ≤ P s^{(m−b−2N−3)/2−ℓ}`,
`s ≥ 1`, with `s^{-b/2-ℓ} ≤ 1`; `(1+|η|)^m ≤ 2^m (1 + |η|^m)`).  The unweighted case `m = 0` is
`IIb.TrainHeatExpansion`. -/
def TrainHeatRemWtd : Prop :=
  ∀ ρ : ℝ, 1 / 2 < ρ → ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ ν c : ℝ, 0 < ν → ν ≤ ν₀ →
    c = Short.PartI.trainPeriod ρ ν →
    ∀ tr : B0140.TrainSol ν c, Short.PartI.IsBUCTrain tr →
      ∀ N m i : ℕ, ∃ C : ℝ, ∀ y : ℝ × (ℝ × ℝ), 1 ≤ y.1 →
        (1 + |y.2.2|) ^ m *
            ‖iteratedFDeriv ℝ i
              (heatRemainder ν (Short.PartI.meanCoeff tr) N (fun y => tr.ψ y.1 y.2)) y‖ ≤
          C * y.1 ^ ((m : ℝ) / 2 - N - 3 / 2)

/-- **Transverse weights of the train stream at bounded ages, at fixed parameters** (source fact;
SP 439-467 at fixed parameters as SP 427-435).

For `ρ > 1/2` there is one threshold `ν₀` such that for every BUC train with `c = ν^{-ρ}`,
`ν ≤ ν₀`, all orders `m, i` and every age bound `S`: `(1 + |η|)^m ‖D^i ψ(s, q, η)‖ ≤ C` for
`0 < s ≤ S` (`D^i` the full derivative in `(s, q, η)`).  Source: `ψ = S + ψ̃`; `sct:fluctuation`
(SP 440-445: `⟨η⟩^m ∂_s^ℓ D^j ψ̃ ≤ P e^{-κνs/c²}` at every age) and the bound of the mean stream
`S` itself (SP 456-457: `‖η^m ∂_η^b ∂_s^ℓ S(s)‖_∞ ≤ P (1+s)^{(m−b−1)/2−ℓ}`, all `s ≥ 0`); equivalently
`sct:transverse` (SP 460-467: on `0 ≤ s ≤ S_*` all fields and fixed derivatives have Gaussian /
exponential transverse tails) with the bounded jets inside the band. -/
def TrainStreamWtdBdd : Prop :=
  ∀ ρ : ℝ, 1 / 2 < ρ → ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ ν c : ℝ, 0 < ν → ν ≤ ν₀ →
    c = Short.PartI.trainPeriod ρ ν →
    ∀ tr : B0140.TrainSol ν c, Short.PartI.IsBUCTrain tr →
      ∀ (m i : ℕ) (S : ℝ), ∃ C : ℝ, ∀ y : ℝ × (ℝ × ℝ), 0 < y.1 → y.1 ≤ S →
        (1 + |y.2.2|) ^ m * ‖iteratedFDeriv ℝ i (fun y : ℝ × (ℝ × ℝ) => tr.ψ y.1 y.2) y‖ ≤ C

/-! ## Leaf Props: calculus of the ring lift -/

/-- **Pointwise jets of a profile through the ring chart** (Faà di Bruno; the pointwise form of
`IIb.CompChartJets`, `Short/PartII-b/Sub/PartII-b_G4_5_2_1_2_org.lean`, SP 2346-2366): for a
profile `b` that is `C^∞` on `s > 0`, at every point off the axis the derivatives of order `≤ j`
of `z ↦ b(chart R τ z)` are bounded by `C (1+s)^k (1+|η|)^j ∑_{l ≤ j} ‖D^l b(chart R τ y)‖`,
`s = age R y`, `η = trans R y`, uniformly in `R ≥ 1`, `τ`, `b`. (`IIb.ChartJets` at level
`S = s + 1`: `‖D^i chart‖ ≤ C (1+S)^k (1+|η|)`, `i ≥ 1`.) -/
def CompChartPtJet : Prop :=
  ∀ j : ℕ, ∃ (C : ℝ) (k : ℕ), 0 < C ∧
    ∀ (R τ : ℝ) (b : ℝ × (ℝ × ℝ) → Axi.Merid), 1 ≤ R → ContDiffOn ℝ ∞ b (Ioi 0 ×ˢ univ) →
      ∀ y : Space, y ∉ Axi.axis → ∀ n ≤ j,
        ‖iteratedFDeriv ℝ n (fun z => b (Axi.chart R τ z)) y‖ ≤
          C * (1 + Axi.age R y) ^ k * (1 + |Axi.trans R y|) ^ j *
            ∑ l ∈ Finset.range (j + 1), ‖iteratedFDeriv ℝ l b (Axi.chart R τ y)‖

/-- **Pointwise Cartesian jets of a ring lift** (the pointwise form of `IIb.RingLiftOffAxis`,
SP 2360-2366, 2386-2387, used at every age for SP 1322-1325): for `b` `C^∞` on `s > 0`, `N_v b(τ,·)`
is `C^∞` off the axis and
`‖D^j N_v b(τ, y)‖ ≤ C (1+s)^k (1+|η|)^j ∑_{l ≤ j} ‖D^l b(chart R τ y)‖` at every `y` off the axis,
uniformly in `R ≥ 1`, `τ`, `b` (Leibniz with `IIb.SqrtFrameJets` at level `s + 1`). -/
def RingLiftPtJet : Prop :=
  ∀ j : ℕ, ∃ (C : ℝ) (k : ℕ), 0 < C ∧
    ∀ (R τ : ℝ) (b : ℝ × (ℝ × ℝ) → Axi.Merid), 1 ≤ R → ContDiffOn ℝ ∞ b (Ioi 0 ×ˢ univ) →
      ContDiffOn ℝ ∞ (Axi.Nv R b τ) Axi.axisᶜ ∧
      ∀ y : Space, y ∉ Axi.axis →
        ‖iteratedFDeriv ℝ j (Axi.Nv R b τ) y‖ ≤
          C * (1 + Axi.age R y) ^ k * (1 + |Axi.trans R y|) ^ j *
            ∑ l ∈ Finset.range (j + 1), ‖iteratedFDeriv ℝ l b (Axi.chart R τ y)‖

/-- **Jets of the ring stream profile as a meridional vector** (SP 1207-1212: `b = (−Ψ_η,
Ψ_q + R⁻¹(Ψ − 2sΨ_s − ηΨ_η))`; the vector form of the proved `IIb.RingProfileJet`): for `Φ` `C^∞`
on `s > 0`, `ringStreamProfile R Φ` is `C^∞` on `s > 0` with
`‖D^i b(y)‖ ≤ C (1 + |s| + |η|) ∑_{l ≤ i+1} ‖D^l Φ(y)‖`. -/
def RingProfileMeridJet : Prop :=
  ∀ (R : ℝ) (Φ : ℝ × (ℝ × ℝ) → ℝ), ContDiffOn ℝ ∞ Φ (Ioi 0 ×ˢ univ) →
    ContDiffOn ℝ ∞ (Axi.ringStreamProfile R Φ) (Ioi 0 ×ˢ univ) ∧
    ∀ i : ℕ, ∃ C : ℝ, ∀ y : ℝ × (ℝ × ℝ), 0 < y.1 →
      ‖iteratedFDeriv ℝ i (Axi.ringStreamProfile R Φ) y‖ ≤
        C * (1 + |y.1| + |y.2.2|) * ∑ l ∈ Finset.range (i + 2), ‖iteratedFDeriv ℝ l Φ y‖

/-- **The derivatives of the unit-age heat kernel are bounded** (`g_ν^{(n)} = H_n · g_ν`, a
polynomial times the Gaussian `g_ν(z) = (4πν)^{-1/2} e^{-z²/(4ν)}`, SP 1311-1313 "Gaussian in `z`"). -/
def ProfileDerivBdd : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ n : ℕ, ∃ C : ℝ, ∀ z : ℝ, |B0191.profileDeriv ν n z| ≤ C

/-- **Bounded Cartesian jets of the heat-term fields near the axis** (SP 1310-1313, 1323-1325: the
heat terms are polynomials in `w = ϱ²` times Gaussian derivatives in `y₃`; "its Cartesian second
derivatives have no spurious axis singularity"): on every region `ϱ² ≤ W`, all derivatives of
`heatField ν R j` are bounded. -/
def HeatFieldJet : Prop :=
  ∀ ν R : ℝ, 0 < ν → ∀ (j k : ℕ) (W : ℝ), ∃ C : ℝ, ∀ y : Space, Axi.ϱ y ^ 2 ≤ W →
    ‖iteratedFDeriv ℝ k (heatField ν R j) y‖ ≤ C

/-! ## Proofs -/

theorem contDiff_heatField (ν R : ℝ) (j : ℕ) : ContDiff ℝ ∞ (heatField ν R j) := by
  have h1 : ContDiff ℝ ∞ (fun y : Space => y 0 ^ 2 + y 1 ^ 2) := by fun_prop
  have h2 : ContDiff ℝ ∞ (fun y : Space => y 2) := by fun_prop
  have hπ : ContDiff ℝ ∞ (fun y : Space => ((0 : ℝ), (y 0 ^ 2 + y 1 ^ 2, y 2))) :=
    contDiff_const.prodMk (h1.prodMk h2)
  unfold heatField
  exact (((contDiff_heatParG ν R j).comp hπ).smul Axi.contDiff_hor).add
    (((contDiff_heatParH ν R j).comp hπ).smul contDiff_const)

theorem contDiff_heatSum (ν R : ℝ) (a : ℕ → ℝ) (N : ℕ) : ContDiff ℝ ∞ (heatSum ν R a N) := by
  unfold heatSum
  exact ContDiff.sum fun j _ => (contDiff_heatField ν R j).const_smul (a j)

/-- The heat sum has bounded jets on `ϱ² ≤ W` (from `HeatFieldJet`). -/
theorem heatSum_jet_le (hH : HeatFieldJet) {ν : ℝ} (hν : 0 < ν) (R : ℝ) (a : ℕ → ℝ) (N k : ℕ)
    (W : ℝ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ y : Space, Axi.ϱ y ^ 2 ≤ W →
      ‖iteratedFDeriv ℝ k (heatSum ν R a N) y‖ ≤ C := by
  choose CH hCH using fun j => hH ν R hν j k W
  refine ⟨∑ j ∈ Finset.range (N + 1), |a j| * |CH j|,
    Finset.sum_nonneg fun j _ => mul_nonneg (abs_nonneg _) (abs_nonneg _), fun y hy => ?_⟩
  have hsm : ∀ j ∈ Finset.range (N + 1), ContDiff ℝ k (fun y => a j • heatField ν R j y) :=
    fun j _ => ((contDiff_heatField ν R j).const_smul (a j)).of_le (m := (k : WithTop ℕ∞))
      (by exact_mod_cast le_top)
  have e : iteratedFDeriv ℝ k (heatSum ν R a N) y =
      ∑ j ∈ Finset.range (N + 1), iteratedFDeriv ℝ k (fun y => a j • heatField ν R j y) y := by
    have h := iteratedFDeriv_sum (𝕜 := ℝ) (i := k) hsm
    have h' := congrFun h y
    rw [Finset.sum_apply] at h'
    exact h'
  rw [e]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [iteratedFDeriv_const_smul_apply'
      (((contDiff_heatField ν R j).contDiffAt (x := y)).of_le (m := (k : WithTop ℕ∞))
        (by exact_mod_cast le_top)),
    norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left ((hCH j y hy).trans (le_abs_self _)) (abs_nonneg _)

theorem age_pos_of {R : ℝ} (hR : 0 < R) {y : Space} (hy : y ∉ Axi.axis) : 0 < Axi.age R y := by
  unfold Axi.age
  exact div_pos (pow_pos hR 2) (pow_pos (Axi.ϱ_pos hy) 2)

/-- The parity coefficients of the ring stream profile split into the heat terms and the
remainder (as `hdec` in `IIb.parityOfExpansion_of`). -/
theorem parity_heat_decomp {ν R : ℝ} (hν : 0 < ν) (hR0 : 0 < R) (a : ℕ → ℝ) (N : ℕ)
    {Ψ : ℝ × (ℝ × ℝ) → ℝ} (hΨ : ContDiffOn ℝ ∞ Ψ (Ioi 0 ×ˢ univ)) (x : ℝ × (ℝ × ℝ))
    (hx : 0 < x.2.1) :
    parG R (Axi.ringStreamProfile R Ψ) x =
        ∑ j ∈ Finset.range (N + 1), a j * heatParG ν R j x +
          parG R (Axi.ringStreamProfile R (heatRemainder ν a N Ψ)) x ∧
      parH R (Axi.ringStreamProfile R Ψ) x =
        ∑ j ∈ Finset.range (N + 1), a j * heatParH ν R j x +
          parH R (Axi.ringStreamProfile R (heatRemainder ν a N Ψ)) x := by
  have hy := parChart_fst_pos hR0 hx
  have hΨd : DifferentiableAt ℝ Ψ (parChart R x) := differentiableAt_of_contDiffOn_pos hΨ hy
  have hTd : ∀ j, DifferentiableAt ℝ (heatTerm ν j) (parChart R x) := fun j =>
    differentiableAt_of_contDiffOn_pos (heatTermSmooth ν hν j) hy
  have hG : ∀ j ∈ Finset.range (N + 1), a j * heatParG ν R j x =
      R / x.2.1 * (a j * Axi.ringStreamProfile R (heatTerm ν j) (parChart R x) 0) :=
    fun j _ => by rw [← (heatTermParity ν R hν hR0 j x hx).1, parG]; ring
  have hH : ∀ j ∈ Finset.range (N + 1), a j * heatParH ν R j x =
      R / Real.sqrt x.2.1 * (a j * Axi.ringStreamProfile R (heatTerm ν j) (parChart R x) 1) :=
    fun j _ => by rw [← (heatTermParity ν R hν hR0 j x hx).2, parH]; ring
  refine ⟨?_, ?_⟩
  · rw [Finset.sum_congr rfl hG, ← Finset.mul_sum]
    simp only [parG]
    rw [ringStreamProfile_heatRemainder R ν a N hΨd hTd 0]
    ring
  · rw [Finset.sum_congr rfl hH, ← Finset.mul_sum]
    simp only [parH]
    rw [ringStreamProfile_heatRemainder R ν a N hΨd hTd 1]
    ring

/-- **The lift splits into the heat fields and the lift of the remainder** off the axis
(SP 1310-1318). -/
theorem Nv_heat_decomp {ν R : ℝ} (hν : 0 < ν) (hR : 0 < R) (a : ℕ → ℝ) (N : ℕ)
    {Ψ : ℝ × (ℝ × ℝ) → ℝ} (hΨ : ContDiffOn ℝ ∞ Ψ (Ioi 0 ×ˢ univ)) (τ : ℝ) {z : Space}
    (hz : z ∉ Axi.axis) :
    Axi.Nv R (Axi.ringStreamProfile R Ψ) τ z =
      heatSum ν R a N z + Axi.Nv R (Axi.ringStreamProfile R (heatRemainder ν a N Ψ)) τ z := by
  have hw : 0 < ((τ, (z 0 ^ 2 + z 1 ^ 2, z 2)) : ℝ × (ℝ × ℝ)).2.1 := by
    show 0 < z 0 ^ 2 + z 1 ^ 2
    rw [← Axi.ϱ_sq]
    exact pow_pos (Axi.ϱ_pos hz) 2
  obtain ⟨hG, hH⟩ := parity_heat_decomp hν hR a N hΨ _ hw
  have hF : heatSum ν R a N z =
      (∑ j ∈ Finset.range (N + 1), a j * heatParG ν R j (τ, (z 0 ^ 2 + z 1 ^ 2, z 2))) •
          Axi.hor z +
        (∑ j ∈ Finset.range (N + 1), a j * heatParH ν R j (τ, (z 0 ^ 2 + z 1 ^ 2, z 2))) •
          Axi.e3 := by
    simp only [heatSum, heatField, smul_add, smul_smul, Finset.sum_add_distrib, Finset.sum_smul]
    rfl
  rw [Nv_eq_parity hR (Axi.ringStreamProfile R Ψ) τ hz,
    Nv_eq_parity hR (Axi.ringStreamProfile R (heatRemainder ν a N Ψ)) τ hz, hG, hH, hF,
    add_smul, add_smul]
  abel

/-- **Cartesian jets of the lift of a stream profile** (from `RingLiftPtJet` and
`RingProfileMeridJet`): `‖D^k N_v(ringStreamProfile R Φ)(τ, y)‖ ≤
C (1+s)^{K+1} (1+|η|)^{k+1} ∑_{i ≤ k+1} ‖D^i Φ(chart R τ y)‖`, with `K` independent of `R`, `Φ`. -/
theorem nv_jet_le (hJ : RingLiftPtJet) (hP : RingProfileMeridJet) (k : ℕ) :
    ∃ K : ℕ, ∀ (R : ℝ) (Φ : ℝ × (ℝ × ℝ) → ℝ), 1 ≤ R → ContDiffOn ℝ ∞ Φ (Ioi 0 ×ˢ univ) →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (τ : ℝ) (y : Space), y ∉ Axi.axis →
        ‖iteratedFDeriv ℝ k (Axi.Nv R (Axi.ringStreamProfile R Φ) τ) y‖ ≤
          C * (1 + Axi.age R y) ^ (K + 1) * ((1 + |Axi.trans R y|) ^ (k + 1) *
            ∑ i ∈ Finset.range (k + 2), ‖iteratedFDeriv ℝ i Φ (Axi.chart R τ y)‖) := by
  obtain ⟨CJ, K, hCJ, HJ⟩ := hJ k
  refine ⟨K, fun R Φ hR hΦ => ?_⟩
  obtain ⟨hBs, hBj⟩ := hP R Φ hΦ
  choose CP hCP using hBj
  have hCP0 : 0 ≤ ∑ l ∈ Finset.range (k + 1), |CP l| :=
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨CJ * ∑ l ∈ Finset.range (k + 1), |CP l|, mul_nonneg hCJ.le hCP0, fun τ y hy => ?_⟩
  have hR0 : 0 < R := by linarith
  have hs : 0 < Axi.age R y := age_pos_of hR0 hy
  have h1 := (HJ R τ _ hR hBs).2 y hy
  have hA0 : 0 ≤ ∑ i ∈ Finset.range (k + 2), ‖iteratedFDeriv ℝ i Φ (Axi.chart R τ y)‖ :=
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hfac : 1 + |(Axi.chart R τ y).1| + |(Axi.chart R τ y).2.2| ≤
      (1 + Axi.age R y) * (1 + |Axi.trans R y|) := by
    show 1 + |Axi.age R y| + |Axi.trans R y| ≤ (1 + Axi.age R y) * (1 + |Axi.trans R y|)
    rw [abs_of_pos hs]
    nlinarith [abs_nonneg (Axi.trans R y)]
  have hl : ∀ l ∈ Finset.range (k + 1),
      ‖iteratedFDeriv ℝ l (Axi.ringStreamProfile R Φ) (Axi.chart R τ y)‖ ≤
        |CP l| * ((1 + Axi.age R y) * (1 + |Axi.trans R y|)) *
          ∑ i ∈ Finset.range (k + 2), ‖iteratedFDeriv ℝ i Φ (Axi.chart R τ y)‖ := by
    intro l hl
    have hl' : l + 2 ≤ k + 2 := by have := Finset.mem_range.1 hl; omega
    have h2 := hCP l (Axi.chart R τ y) hs
    have hsub : ∑ i ∈ Finset.range (l + 2), ‖iteratedFDeriv ℝ i Φ (Axi.chart R τ y)‖ ≤
        ∑ i ∈ Finset.range (k + 2), ‖iteratedFDeriv ℝ i Φ (Axi.chart R τ y)‖ :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hl')
        (fun _ _ _ => norm_nonneg _)
    have hsum0 : 0 ≤ ∑ i ∈ Finset.range (l + 2), ‖iteratedFDeriv ℝ i Φ (Axi.chart R τ y)‖ :=
      Finset.sum_nonneg fun _ _ => norm_nonneg _
    refine h2.trans (mul_le_mul ?_ hsub hsum0 (by positivity))
    exact (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)).trans
      (mul_le_mul_of_nonneg_left hfac (abs_nonneg _))
  have hsumB : ∑ l ∈ Finset.range (k + 1),
      ‖iteratedFDeriv ℝ l (Axi.ringStreamProfile R Φ) (Axi.chart R τ y)‖ ≤
        (∑ l ∈ Finset.range (k + 1), |CP l|) * ((1 + Axi.age R y) * (1 + |Axi.trans R y|)) *
          ∑ i ∈ Finset.range (k + 2), ‖iteratedFDeriv ℝ i Φ (Axi.chart R τ y)‖ := by
    rw [Finset.sum_mul, Finset.sum_mul]
    exact Finset.sum_le_sum hl
  have h1s : 0 ≤ 1 + Axi.age R y := by linarith
  have hpos1 : 0 ≤ CJ * (1 + Axi.age R y) ^ K * (1 + |Axi.trans R y|) ^ k :=
    mul_nonneg (mul_nonneg hCJ.le (pow_nonneg h1s _)) (pow_nonneg (by positivity) _)
  calc ‖iteratedFDeriv ℝ k (Axi.Nv R (Axi.ringStreamProfile R Φ) τ) y‖
      ≤ CJ * (1 + Axi.age R y) ^ K * (1 + |Axi.trans R y|) ^ k *
          ∑ l ∈ Finset.range (k + 1),
            ‖iteratedFDeriv ℝ l (Axi.ringStreamProfile R Φ) (Axi.chart R τ y)‖ := h1
    _ ≤ CJ * (1 + Axi.age R y) ^ K * (1 + |Axi.trans R y|) ^ k *
          ((∑ l ∈ Finset.range (k + 1), |CP l|) * ((1 + Axi.age R y) * (1 + |Axi.trans R y|)) *
            ∑ i ∈ Finset.range (k + 2), ‖iteratedFDeriv ℝ i Φ (Axi.chart R τ y)‖) :=
        mul_le_mul_of_nonneg_left hsumB hpos1
    _ = CJ * (∑ l ∈ Finset.range (k + 1), |CP l|) * (1 + Axi.age R y) ^ (K + 1) *
          ((1 + |Axi.trans R y|) ^ (k + 1) *
            ∑ i ∈ Finset.range (k + 2), ‖iteratedFDeriv ℝ i Φ (Axi.chart R τ y)‖) := by
        ring

/-- **`RingLiftOffAxisDerivBdd` from the leaf Props** (SP 1305-1325). -/
theorem ringLiftOffAxisDerivBdd_of (hN : TrainHeatRemWtd) (hF : TrainStreamWtdBdd)
    (hJ : RingLiftPtJet) (hP : RingProfileMeridJet) (hH : HeatFieldJet) :
    RingLiftOffAxisDerivBdd := by
  obtain ⟨ν₁, hν₁, HN⟩ := hN 2 (by norm_num)
  obtain ⟨ν₂, hν₂, HF⟩ := hF 2 (by norm_num)
  refine ⟨min ν₁ ν₂, lt_min hν₁ hν₂, fun ν hν ψ pr hpr R hR k => ?_⟩
  obtain ⟨T, hT, hψ, -⟩ := hpr
  subst hψ
  have hν0 : 0 < ν := hν.1
  have hνle1 : ν ≤ ν₁ := (le_of_lt hν.2).trans (min_le_left _ _)
  have hνle2 : ν ≤ ν₂ := (le_of_lt hν.2).trans (min_le_right _ _)
  have hc : ν ^ (-(2 : ℝ)) = Short.PartI.trainPeriod 2 ν := rfl
  have hc0 : 0 < ν ^ (-(2 : ℝ)) := Real.rpow_pos_of_pos hν0 _
  have hR0 : 0 < R := by linarith
  have hR1 : 1 ≤ R := by linarith
  have hΨ : ContDiffOn ℝ ∞ (fun x : ℝ × (ℝ × ℝ) => T.ψ x.1 x.2) (Ioi 0 ×ˢ univ) :=
    Short.PartI.trainStreamSmooth ν _ hν0 hc0 T hT
  -- off the axis the lift is the ring lift of the stream profile
  have hmer : ∀ x : ℝ × (ℝ × ℝ), 0 < x.1 →
      B0190.merProfile R (B0190.trainProfile T.ψ) x =
        Axi.ringStreamProfile R (fun x : ℝ × (ℝ × ℝ) => T.ψ x.1 x.2) x := by
    intro x hx
    rw [← rawProfile_eq_merProfile_of_smooth Short.PartI.trainStreamSmooth hν0 hc0 T hT
      (R := R) rfl hx]
    exact rawStreamProfile ν _ R T hR0 hΨ x hx
  have hU : ∀ (τ : ℝ) (y : Space), y ∉ Axi.axis →
      iteratedFDeriv ℝ k
          (B0190.simProfile 1 (B0185.liftVelocity R (B0190.trainProfile T.ψ)) τ) y =
        iteratedFDeriv ℝ k
          (Axi.Nv R (Axi.ringStreamProfile R (fun x : ℝ × (ℝ × ℝ) => T.ψ x.1 x.2)) τ) y := by
    intro τ y hy
    have hev : B0190.simProfile 1 (B0185.liftVelocity R (B0190.trainProfile T.ψ)) τ =ᶠ[𝓝 y]
        Axi.Nv R (Axi.ringStreamProfile R (fun x : ℝ × (ℝ × ℝ) => T.ψ x.1 x.2)) τ := by
      filter_upwards [Axi.isOpen_compl_axis.mem_nhds hy] with z hz
      rw [B0190.simProfile_liftVelocity_eq_Nv hR0 _ τ hz]
      simp only [Axi.Nv]
      rw [hmer (Axi.chart R τ z) (age_pos_of hR0 hz)]
    exact (hev.iteratedFDeriv ℝ k).eq_of_nhds
  -- constants
  obtain ⟨K, HK⟩ := nv_jet_le hJ hP k
  obtain ⟨CJ, KJ, hCJ, HJ⟩ := hJ k
  obtain ⟨Cf, hCf0, Hf⟩ := HK R _ hR1 hΨ
  choose CF hCF using fun i => HF ν _ hν0 hνle2 hc T hT (k + 1) i 4
  obtain ⟨N, hNdef⟩ : ∃ N : ℕ, N = K + k + 2 := ⟨_, rfl⟩
  have hΦN : ContDiffOn ℝ ∞ (heatRemainder ν (Short.PartI.meanCoeff T) N
      (fun x : ℝ × (ℝ × ℝ) => T.ψ x.1 x.2)) (Ioi 0 ×ˢ univ) :=
    hΨ.sub (ContDiffOn.sum fun j _ => contDiffOn_const.mul (heatTermSmooth ν hν0 j))
  obtain ⟨Cn, hCn0, Hn⟩ := HK R _ hR1 hΦN
  choose CN hCN using fun i => HN ν _ hν0 hνle1 hc T hT N (k + 1) i
  obtain ⟨Ch, hCh0, Hh⟩ := heatSum_jet_le hH hν0 R (Short.PartI.meanCoeff T) N k (R ^ 2)
  have hBNs := (hP R _ hΦN).1
  have hCF0 : 0 ≤ ∑ i ∈ Finset.range (k + 2), |CF i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hCN0 : 0 ≤ ∑ i ∈ Finset.range (k + 2), |CN i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hfar0 : 0 ≤ Cf * 5 ^ (K + 1) * ∑ i ∈ Finset.range (k + 2), |CF i| :=
    mul_nonneg (mul_nonneg hCf0 (by positivity)) hCF0
  have hnear0 : 0 ≤ Ch + Cn * 2 ^ (K + 1) * ∑ i ∈ Finset.range (k + 2), |CN i| :=
    add_nonneg hCh0 (mul_nonneg (mul_nonneg hCn0 (by positivity)) hCN0)
  refine ⟨Cf * 5 ^ (K + 1) * ∑ i ∈ Finset.range (k + 2), |CF i| +
      (Ch + Cn * 2 ^ (K + 1) * ∑ i ∈ Finset.range (k + 2), |CN i|), fun τ y hy0 => ?_⟩
  have hy : y ∉ Axi.axis := varrho_ne_zero_iff.1 hy0
  rw [hU τ y hy]
  have hs : 0 < Axi.age R y := age_pos_of hR0 hy
  by_cases hfar : Axi.age R y ≤ 4
  · -- (iii) far from the axis: bounded ages
    have h := Hf τ y hy
    have hw : (1 + |Axi.trans R y|) ^ (k + 1) * ∑ i ∈ Finset.range (k + 2),
        ‖iteratedFDeriv ℝ i (fun x : ℝ × (ℝ × ℝ) => T.ψ x.1 x.2) (Axi.chart R τ y)‖ ≤
        ∑ i ∈ Finset.range (k + 2), |CF i| := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ =>
        (hCF i (Axi.chart R τ y) hs hfar).trans (le_abs_self _)
    have h5 : (1 + Axi.age R y) ^ (K + 1) ≤ 5 ^ (K + 1) :=
      pow_le_pow_left₀ (by linarith) (by linarith) _
    calc _ ≤ Cf * (1 + Axi.age R y) ^ (K + 1) * ((1 + |Axi.trans R y|) ^ (k + 1) *
            ∑ i ∈ Finset.range (k + 2),
              ‖iteratedFDeriv ℝ i (fun x : ℝ × (ℝ × ℝ) => T.ψ x.1 x.2) (Axi.chart R τ y)‖) := h
      _ ≤ Cf * 5 ^ (K + 1) * ∑ i ∈ Finset.range (k + 2), |CF i| :=
          mul_le_mul (mul_le_mul_of_nonneg_left h5 hCf0) hw (by positivity)
            (mul_nonneg hCf0 (by positivity))
      _ ≤ _ := le_add_of_nonneg_right hnear0
  · -- near the axis: heat terms (i) plus the remainder (ii)
    push Not at hfar
    have hs1 : 1 ≤ Axi.age R y := by linarith
    have hϱ : Axi.ϱ y ^ 2 ≤ R ^ 2 := by
      have hϱ0 : 0 < Axi.ϱ y ^ 2 := pow_pos (Axi.ϱ_pos hy) 2
      have h4 : 4 < R ^ 2 / Axi.ϱ y ^ 2 := hfar
      rw [lt_div_iff₀ hϱ0] at h4
      nlinarith
    have hev : Axi.Nv R (Axi.ringStreamProfile R (fun x : ℝ × (ℝ × ℝ) => T.ψ x.1 x.2)) τ
        =ᶠ[𝓝 y] heatSum ν R (Short.PartI.meanCoeff T) N +
          Axi.Nv R (Axi.ringStreamProfile R (heatRemainder ν (Short.PartI.meanCoeff T) N
            (fun x : ℝ × (ℝ × ℝ) => T.ψ x.1 x.2))) τ := by
      filter_upwards [Axi.isOpen_compl_axis.mem_nhds hy] with z hz
      exact Nv_heat_decomp hν0 hR0 _ N hΨ τ hz
    have hNvc : ContDiffAt ℝ k (Axi.Nv R (Axi.ringStreamProfile R (heatRemainder ν
        (Short.PartI.meanCoeff T) N (fun x : ℝ × (ℝ × ℝ) => T.ψ x.1 x.2))) τ) y :=
      (((HJ R τ _ hR1 hBNs).1).contDiffAt (Axi.isOpen_compl_axis.mem_nhds hy)).of_le
        (by exact_mod_cast le_top)
    have hHc : ContDiffAt ℝ k (heatSum ν R (Short.PartI.meanCoeff T) N) y :=
      (contDiff_heatSum ν R _ N).contDiffAt.of_le (by exact_mod_cast le_top)
    rw [(hev.iteratedFDeriv ℝ k).eq_of_nhds, iteratedFDeriv_add_apply hHc hNvc]
    refine (norm_add_le _ _).trans ?_
    have h1 := Hh y hϱ
    have h2 := Hn τ y hy
    have he : ((k + 1 : ℕ) : ℝ) / 2 - (N : ℝ) - 3 / 2 ≤ -((K + 1 : ℕ) : ℝ) := by
      rw [hNdef]; push_cast; linarith
    have hw : (1 + |Axi.trans R y|) ^ (k + 1) * ∑ i ∈ Finset.range (k + 2),
        ‖iteratedFDeriv ℝ i (heatRemainder ν (Short.PartI.meanCoeff T) N
          (fun x : ℝ × (ℝ × ℝ) => T.ψ x.1 x.2)) (Axi.chart R τ y)‖ ≤
        (∑ i ∈ Finset.range (k + 2), |CN i|) *
          Axi.age R y ^ (((k + 1 : ℕ) : ℝ) / 2 - (N : ℝ) - 3 / 2) := by
      rw [Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_le_sum fun i _ => (hCN i (Axi.chart R τ y) hs1).trans
        (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg hs.le _))
    have hpow : (1 + Axi.age R y) ^ (K + 1) *
        Axi.age R y ^ (((k + 1 : ℕ) : ℝ) / 2 - (N : ℝ) - 3 / 2) ≤ 2 ^ (K + 1) := by
      have h2s : (1 + Axi.age R y) ^ (K + 1) ≤ 2 ^ (K + 1) * Axi.age R y ^ (K + 1) := by
        rw [← mul_pow]
        exact pow_le_pow_left₀ (by linarith) (by linarith) _
      have hle1 : Axi.age R y ^ (K + 1) *
          Axi.age R y ^ (((k + 1 : ℕ) : ℝ) / 2 - (N : ℝ) - 3 / 2) ≤ 1 := by
        rw [← Real.rpow_natCast, ← Real.rpow_add hs]
        exact Real.rpow_le_one_of_one_le_of_nonpos hs1 (by push_cast at he ⊢; linarith)
      calc _ ≤ 2 ^ (K + 1) * Axi.age R y ^ (K + 1) *
            Axi.age R y ^ (((k + 1 : ℕ) : ℝ) / 2 - (N : ℝ) - 3 / 2) :=
            mul_le_mul_of_nonneg_right h2s (Real.rpow_nonneg hs.le _)
        _ = 2 ^ (K + 1) * (Axi.age R y ^ (K + 1) *
            Axi.age R y ^ (((k + 1 : ℕ) : ℝ) / 2 - (N : ℝ) - 3 / 2)) := by ring
        _ ≤ 2 ^ (K + 1) * 1 := mul_le_mul_of_nonneg_left hle1 (by positivity)
        _ = _ := mul_one _
    have hCnA : 0 ≤ Cn * (1 + Axi.age R y) ^ (K + 1) :=
      mul_nonneg hCn0 (pow_nonneg (by linarith) _)
    calc _ ≤ Ch + Cn * (1 + Axi.age R y) ^ (K + 1) * ((1 + |Axi.trans R y|) ^ (k + 1) *
            ∑ i ∈ Finset.range (k + 2),
              ‖iteratedFDeriv ℝ i (heatRemainder ν (Short.PartI.meanCoeff T) N
                (fun x : ℝ × (ℝ × ℝ) => T.ψ x.1 x.2)) (Axi.chart R τ y)‖) := add_le_add h1 h2
      _ ≤ Ch + Cn * (1 + Axi.age R y) ^ (K + 1) * ((∑ i ∈ Finset.range (k + 2), |CN i|) *
            Axi.age R y ^ (((k + 1 : ℕ) : ℝ) / 2 - (N : ℝ) - 3 / 2)) :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left hw hCnA)
      _ = Ch + Cn * (∑ i ∈ Finset.range (k + 2), |CN i|) * ((1 + Axi.age R y) ^ (K + 1) *
            Axi.age R y ^ (((k + 1 : ℕ) : ℝ) / 2 - (N : ℝ) - 3 / 2)) := by ring
      _ ≤ Ch + Cn * (∑ i ∈ Finset.range (k + 2), |CN i|) * 2 ^ (K + 1) :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left hpow (mul_nonneg hCn0 hCN0))
      _ = Ch + Cn * 2 ^ (K + 1) * ∑ i ∈ Finset.range (k + 2), |CN i| := by ring
      _ ≤ _ := le_add_of_nonneg_left hfar0

end UnforcedLeray.Short.PartIIIb.Concrete

#print axioms UnforcedLeray.Short.PartIIIb.Concrete.ringLiftOffAxisDerivBdd_of
