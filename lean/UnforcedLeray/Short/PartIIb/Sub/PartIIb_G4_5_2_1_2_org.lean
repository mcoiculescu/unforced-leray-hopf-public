import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_5_2_1

/-!
# Part II-b, organize task `PartII-b:G4/5/2/1/2/org`: chart and composite jets of the ring lift

Source of record: `the November 2 reference manuscript` (SP) lines 2346-2366
(the exact stream lift `E_ε = N_v e_ε`, `e_ε` with exponential transverse decay), 2386-2387
(`‖E_εα‖_{W^{j,∞}} ≤ 𝒫_{ν,j}|α|`).  Chart: `s = R²/ϱ²`, `ξ = Rτ/2 - (R/2) log s`, `η = R y₃/ϱ`
(`Lib/Axisymmetric/RingChart.lean`).

`ChartJets` (restated with the factor `1+|η|`) splits into its three components, each a pure
off-axis calculus bound in powers of `t = ϱ⁻¹` (`AgeJets`, `PhaseJets`, `TransJets`);
`chartJets_of` assembles them: the Cartesian derivative of `y ↦ (s, (ξ, η))` is the product of the
component derivatives (`iteratedFDeriv_prodMk`), whose norm is the maximum
(`ContinuousMultilinearMap.opNorm_prod`), and on `{age R y < S}`, `R ≥ 1`, one has
`t ≤ R t = √s < 1 + S`, so `R² t^{j+2} = s t^j`, `R t^j = √s t^{j-1}` and `|η| t^j` are bounded by
`(1+S)^{j+2}(1+|η|)`.

`CompChartJets` is the Faà di Bruno step of `RingLiftOffAxis`: the composite `b ∘ chart` has
`‖D^n (b ∘ chart)(y)‖ ≤ C (1+S)^k M` for `n ≤ j` if `(1+|η|)^j ‖D^l b‖ ≤ M` for `l ≤ j`
(`norm_iteratedFDerivWithin_comp_le` on `axisᶜ` with `D = A (1+S)^K (1+|η(y)|)`: the factor
`(1+|η|)^n ≤ (1+|η|)^j` it produces is absorbed by the weight).

The smoothness facts the leaves need are proved here (`ChartJetsAux`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIb

/-- **Age jets** (SP 2346-2366; `s = R²/ϱ² = R² ϱ⁻¹ ϱ⁻¹`): off the axis
`‖D^j s(y)‖ ≤ C_j R² ϱ(y)^{-(j+2)}` for every `j` and `R`.  (Leibniz
`norm_iteratedFDerivWithin_mul_le` on the open set `axisᶜ` with the jets of `ϱ⁻¹`,
`SqrtFrameJetsAux.varrho_inv_jet`: `‖D^i ϱ⁻¹‖ ≤ C_i ϱ^{-(i+1)}`.) -/
def AgeJets : Prop :=
  ∀ j : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ (R : ℝ) (y : Space), y ∉ Axi.axis →
    ‖iteratedFDeriv ℝ j (Axi.age R) y‖ ≤ C * R ^ 2 * (Axi.ϱ y)⁻¹ ^ (j + 2)

/-- **Phase jets** (SP 2346-2366; `ξ = Rτ/2 - (R/2) log s`): for `j ≥ 1` and `R > 0`, off the axis
`‖D^j ξ(y)‖ ≤ C_j R ϱ(y)^{-j}`.  (`Dξ(z) = phaseD R z = (R/ϱ) ϱD z = R ϱ(z)⁻² (z₀ dz₀ + z₁ dz₁)`,
`Axi.hasFDerivAt_phase`; so `‖D^j ξ‖ = ‖D^{j-1}(Dξ)‖` (`norm_iteratedFDeriv_fderiv`), and Leibniz
for the scalar `R ϱ⁻¹ϱ⁻¹` (jets `≲ R ϱ^{-(i+2)}`) times the linear map `z ↦ z₀ dz₀ + z₁ dz₁`
(norm `≤ ϱ(z)` at order 0, `≤ 1` at order 1, `0` at order `≥ 2`).) -/
def PhaseJets : Prop :=
  ∀ j : ℕ, 1 ≤ j → ∃ C : ℝ, 0 < C ∧ ∀ (R τ : ℝ) (y : Space), 0 < R → y ∉ Axi.axis →
    ‖iteratedFDeriv ℝ j (Axi.phase R τ) y‖ ≤ C * R * (Axi.ϱ y)⁻¹ ^ j

/-- **Transverse jets** (SP 2346-2366; `η = R y₃ ϱ⁻¹`): for `j ≥ 1` and `R > 0`, off the axis
`‖D^j η(y)‖ ≤ C_j (|η(y)| + R) ϱ(y)^{-j}`.  (Leibniz for `y₃ · ϱ⁻¹`:
`‖D^j η‖ ≤ R|y₃| ‖D^j ϱ⁻¹‖ + j R ‖D^{j-1} ϱ⁻¹‖ ≲ R|y₃| ϱ^{-(j+1)} + R ϱ^{-j}` and
`R|y₃|ϱ⁻¹ = |η|`.  The factor `|η|` is genuine: `∂_ϱ η = -η/ϱ`.) -/
def TransJets : Prop :=
  ∀ j : ℕ, 1 ≤ j → ∃ C : ℝ, 0 < C ∧ ∀ (R : ℝ) (y : Space), 0 < R → y ∉ Axi.axis →
    ‖iteratedFDeriv ℝ j (Axi.trans R) y‖ ≤ C * (|Axi.trans R y| + R) * (Axi.ϱ y)⁻¹ ^ j

/-- **Composite jets** (Faà di Bruno step of `RingLiftOffAxis`, SP 2360-2366): if the profile jets of
order `≤ j` satisfy `(1+|η|)^j ‖D^l b‖ ≤ M`, then on `{y ∉ axis, age R y < S}` the composite
`z ↦ b (chart R τ z)` has `‖D^n (b ∘ chart)(y)‖ ≤ C_j (1+S)^{k_j} M` for all `n ≤ j`. -/
def CompChartJets : Prop :=
  ∀ j : ℕ, ∃ (C : ℝ) (k : ℕ), 0 < C ∧
    ∀ (S R τ M : ℝ) (b : ℝ × (ℝ × ℝ) → Axi.Merid), 0 < S → 1 ≤ R → 0 ≤ M →
      ContDiff ℝ ∞ b →
      (∀ l ≤ j, ∀ x : ℝ × (ℝ × ℝ), (1 + |x.2.2|) ^ j * ‖iteratedFDeriv ℝ l b x‖ ≤ M) →
      ∀ y : Space, y ∉ Axi.axis → Axi.age R y < S → ∀ n ≤ j,
        ‖iteratedFDeriv ℝ n (fun z => b (Axi.chart R τ z)) y‖ ≤ C * (1 + S) ^ k * M

namespace ChartJetsAux

open UnforcedLeray

theorem contDiffOn_age (R : ℝ) : ContDiffOn ℝ ∞ (Axi.age R) Axi.axisᶜ := by
  unfold Axi.age
  exact contDiffOn_const.div (Axi.contDiffOn_ϱ.pow 2) fun z hz => pow_ne_zero 2 (Axi.ϱ_ne_zero hz)

theorem contDiffOn_phase {R : ℝ} (hR : R ≠ 0) (τ : ℝ) :
    ContDiffOn ℝ ∞ (Axi.phase R τ) Axi.axisᶜ := by
  have hpos : ∀ z ∈ Axi.axisᶜ, Axi.age R z ≠ 0 := fun z hz => (Axi.age_pos hR hz).ne'
  unfold Axi.phase
  exact contDiffOn_const.sub (contDiffOn_const.mul ((contDiffOn_age R).log hpos))

theorem contDiffOn_trans (R : ℝ) : ContDiffOn ℝ ∞ (Axi.trans R) Axi.axisᶜ := by
  unfold Axi.trans
  have h2 : ContDiff ℝ ∞ (fun z : Space => z 2) :=
    (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).contDiff
  exact (contDiffOn_const.mul h2.contDiffOn).div Axi.contDiffOn_ϱ fun z hz => Axi.ϱ_ne_zero hz

/-- The chart is `C^∞` off the axis. -/
theorem contDiffOn_chart {R : ℝ} (hR : R ≠ 0) (τ : ℝ) :
    ContDiffOn ℝ ∞ (Axi.chart R τ) Axi.axisᶜ :=
  (contDiffOn_age R).prodMk ((contDiffOn_phase hR τ).prodMk (contDiffOn_trans R))

/-- A smooth profile composed with the chart is `C^∞` off the axis. -/
theorem contDiffOn_comp_chart {b : ℝ × (ℝ × ℝ) → Axi.Merid} (hb : ContDiff ℝ ∞ b) {R : ℝ}
    (hR : R ≠ 0) (τ : ℝ) : ContDiffOn ℝ ∞ (fun z => b (Axi.chart R τ z)) Axi.axisᶜ :=
  hb.comp_contDiffOn (contDiffOn_chart hR τ)

/-- The amplitude `√s = √(age R ·)` is `C^∞` off the axis. -/
theorem contDiffOn_sqrt_age {R : ℝ} (hR : R ≠ 0) :
    ContDiffOn ℝ ∞ (fun z => √(Axi.age R z)) Axi.axisᶜ :=
  (contDiffOn_age R).sqrt fun _ hz => (Axi.age_pos hR hz).ne'

/-- The frame `frameL` is `C^∞` off the axis. -/
theorem contDiffOn_frameL : ContDiffOn ℝ ∞ Axi.frameL Axi.axisᶜ := by
  set L : Space →L[ℝ] (Axi.Merid →L[ℝ] Space) :=
    ContinuousLinearMap.smulRightL ℝ Axi.Merid Space
      (EuclideanSpace.proj (0 : Fin 2) : Axi.Merid →L[ℝ] ℝ) with hL
  have h : Axi.frameL = fun y => L (Axi.eR y) +
      (EuclideanSpace.proj (1 : Fin 2) : Axi.Merid →L[ℝ] ℝ).smulRight Axi.e3 := by
    funext y
    ext v : 1
    simp [hL, Axi.frameL_apply]
  rw [h]
  exact (L.contDiff.comp_contDiffOn Axi.contDiffOn_eR).add contDiffOn_const

/-- The ring lift as an explicit product: `N_v b(τ, z) = √(age R z) • frameL z (b (chart R τ z))`. -/
theorem Nv_eq_fun (R : ℝ) (b : ℝ × (ℝ × ℝ) → Axi.Merid) (τ : ℝ) :
    Axi.Nv R b τ = fun z => √(Axi.age R z) • (Axi.frameL z) (b (Axi.chart R τ z)) := rfl

end ChartJetsAux

open ChartJetsAux in
/-- **`ChartJets` from its components** (`R ≥ 1`, `age R y < S`: `t = ϱ⁻¹ ≤ Rt = √s < 1 + S`). -/
theorem chartJets_of (hA : AgeJets) (hP : PhaseJets) (hT : TransJets) : ChartJets := by
  intro j hj
  obtain ⟨CA, hCA, hA'⟩ := hA j
  obtain ⟨CP, hCP, hP'⟩ := hP j hj
  obtain ⟨CT, hCT, hT'⟩ := hT j hj
  refine ⟨CA + CP + CT, j + 2, by positivity, ?_⟩
  intro S R τ hS hR y hy hage
  have hR0 : 0 < R := lt_of_lt_of_le one_pos hR
  have hU : Axi.axisᶜ ∈ 𝓝 y := Axi.isOpen_compl_axis.mem_nhds hy
  have cA : ContDiffAt ℝ ∞ (Axi.age R) y := (contDiffOn_age R).contDiffAt hU
  have cP : ContDiffAt ℝ ∞ (Axi.phase R τ) y := (contDiffOn_phase hR0.ne' τ).contDiffAt hU
  have cT : ContDiffAt ℝ ∞ (Axi.trans R) y := (contDiffOn_trans R).contDiffAt hU
  have hj' : ((j : ℕ) : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  have hD : iteratedFDeriv ℝ j (Axi.chart R τ) y =
      (iteratedFDeriv ℝ j (Axi.age R) y).prod
        ((iteratedFDeriv ℝ j (Axi.phase R τ) y).prod (iteratedFDeriv ℝ j (Axi.trans R) y)) := by
    rw [show Axi.chart R τ = fun x => (Axi.age R x, (Axi.phase R τ x, Axi.trans R x)) from rfl,
      iteratedFDeriv_prodMk cA (cP.prodMk cT) hj', iteratedFDeriv_prodMk cP cT hj']
  rw [hD, ContinuousMultilinearMap.opNorm_prod, ContinuousMultilinearMap.opNorm_prod]
  -- the scales `t = ϱ⁻¹ ≤ u = R t = √s < 1 + S`
  have hϱ : 0 < Axi.ϱ y := Axi.ϱ_pos hy
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = (Axi.ϱ y)⁻¹ := ⟨_, rfl⟩
  have ht0 : 0 < t := by rw [ht]; exact inv_pos.2 hϱ
  have hage' : Axi.age R y = (R * t) ^ 2 := by
    rw [Axi.age, ht, mul_pow, inv_pow, div_eq_mul_inv]
  have hu0 : 0 < R * t := mul_pos hR0 ht0
  have hu2 : (R * t) ^ 2 < S := hage' ▸ hage
  have hu1 : R * t ≤ 1 + S := by nlinarith
  have htu : t ≤ R * t := by nlinarith
  have ht1 : t ≤ 1 + S := htu.trans hu1
  have hS1 : (1 : ℝ) ≤ 1 + S := by linarith
  have tpow : ∀ n : ℕ, t ^ n ≤ (1 + S) ^ n := fun n => pow_le_pow_left₀ ht0.le ht1 n
  have upow : (R * t) ^ 2 ≤ (1 + S) ^ 2 := pow_le_pow_left₀ hu0.le hu1 2
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  have hP1 : (1 + S) ^ (m + 1) ≤ (1 + S) ^ (m + 1 + 2) := pow_le_pow_right₀ hS1 (by omega)
  have hη : (1 : ℝ) ≤ 1 + |Axi.trans R y| := by linarith [abs_nonneg (Axi.trans R y)]
  have hη0 : 0 ≤ |Axi.trans R y| := abs_nonneg _
  have hPp : 0 ≤ (1 + S) ^ (m + 1 + 2) := by positivity
  have hpm : 0 ≤ (1 + S) ^ m := by positivity
  have htm : 0 ≤ t ^ m := pow_nonneg ht0.le m
  have bA : ‖iteratedFDeriv ℝ (m + 1) (Axi.age R) y‖ ≤ CA * (1 + S) ^ (m + 1 + 2) := by
    have h := hA' R y hy
    rw [← ht] at h
    have e : CA * R ^ 2 * t ^ (m + 1 + 2) = CA * ((R * t) ^ 2 * t ^ (m + 1)) := by ring
    have e' : CA * (1 + S) ^ (m + 1 + 2) = CA * ((1 + S) ^ 2 * (1 + S) ^ (m + 1)) := by ring
    rw [e] at h
    rw [e']
    refine h.trans (mul_le_mul_of_nonneg_left ?_ hCA.le)
    exact mul_le_mul upow (tpow _) (pow_nonneg ht0.le _) (by positivity)
  have bP : ‖iteratedFDeriv ℝ (m + 1) (Axi.phase R τ) y‖ ≤ CP * (1 + S) ^ (m + 1 + 2) := by
    have h := hP' R τ y hR0 hy
    rw [← ht] at h
    have e : CP * R * t ^ (m + 1) = CP * ((R * t) * t ^ m) := by ring
    rw [e] at h
    refine h.trans (mul_le_mul_of_nonneg_left ?_ hCP.le)
    calc (R * t) * t ^ m ≤ (1 + S) * (1 + S) ^ m := mul_le_mul hu1 (tpow m) htm (by positivity)
      _ = (1 + S) ^ (m + 1) := by ring
      _ ≤ _ := hP1
  have bT : ‖iteratedFDeriv ℝ (m + 1) (Axi.trans R) y‖ ≤
      CT * (1 + S) ^ (m + 1 + 2) * (1 + |Axi.trans R y|) := by
    have h := hT' R y hR0 hy
    rw [← ht] at h
    have e : CT * (|Axi.trans R y| + R) * t ^ (m + 1) =
        CT * (|Axi.trans R y| * t ^ (m + 1) + (R * t) * t ^ m) := by ring
    rw [e] at h
    refine h.trans ?_
    have h1 : |Axi.trans R y| * t ^ (m + 1) ≤ |Axi.trans R y| * (1 + S) ^ (m + 1 + 2) :=
      mul_le_mul_of_nonneg_left ((tpow _).trans hP1) hη0
    have h2 : (R * t) * t ^ m ≤ (1 + S) ^ (m + 1 + 2) := by
      calc (R * t) * t ^ m ≤ (1 + S) * (1 + S) ^ m := mul_le_mul hu1 (tpow m) htm (by positivity)
        _ = (1 + S) ^ (m + 1) := by ring
        _ ≤ _ := hP1
    have e2 : CT * (1 + S) ^ (m + 1 + 2) * (1 + |Axi.trans R y|) =
        CT * (|Axi.trans R y| * (1 + S) ^ (m + 1 + 2) + (1 + S) ^ (m + 1 + 2)) := by ring
    rw [e2]
    exact mul_le_mul_of_nonneg_left (add_le_add h1 h2) hCT.le
  have hsum : 0 ≤ CA + CP + CT := by positivity
  refine max_le ?_ (max_le ?_ ?_)
  · calc _ ≤ CA * (1 + S) ^ (m + 1 + 2) := bA
      _ ≤ (CA + CP + CT) * (1 + S) ^ (m + 1 + 2) :=
          mul_le_mul_of_nonneg_right (by linarith) hPp
      _ ≤ (CA + CP + CT) * (1 + S) ^ (m + 1 + 2) * (1 + |Axi.trans R y|) :=
          le_mul_of_one_le_right (mul_nonneg hsum hPp) hη
  · calc _ ≤ CP * (1 + S) ^ (m + 1 + 2) := bP
      _ ≤ (CA + CP + CT) * (1 + S) ^ (m + 1 + 2) :=
          mul_le_mul_of_nonneg_right (by linarith) hPp
      _ ≤ (CA + CP + CT) * (1 + S) ^ (m + 1 + 2) * (1 + |Axi.trans R y|) :=
          le_mul_of_one_le_right (mul_nonneg hsum hPp) hη
  · calc _ ≤ CT * (1 + S) ^ (m + 1 + 2) * (1 + |Axi.trans R y|) := bT
      _ ≤ (CA + CP + CT) * (1 + S) ^ (m + 1 + 2) * (1 + |Axi.trans R y|) := by
          have : CT * (1 + S) ^ (m + 1 + 2) ≤ (CA + CP + CT) * (1 + S) ^ (m + 1 + 2) :=
            mul_le_mul_of_nonneg_right (by linarith) hPp
          exact mul_le_mul_of_nonneg_right this (by linarith)

end UnforcedLeray.Short.IIb
