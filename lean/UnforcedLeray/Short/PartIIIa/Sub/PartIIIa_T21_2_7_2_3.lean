import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2_2
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.AdjWeakSmooth

/-!
# `PartIII-a:T21/2/7/2/3`: `φ ∈ C([t, s); H^1_{-m,c})`, the differentiated energy, decomposed

Source: `the November 2 reference manuscript` (SP) lines 3060-3071
(`E_1' + β_min E_2 ≤ C_b(E_1 + E_0)`, "the transport and compact terms have coefficient `C_b`"),
3044-3049 (the weight), 3052-3058 (the localized term).

The energy is the physical one, `E(ρ) = Σ_k ‖∂_kφ(ρ)‖²_{X_{-m,c}}` (`gradE`), with transverse cutoffs
`χ_R = ladCut R`. The weight `⟨x⟩^{-2m}` of `X_{-m,c}` is not smooth on the periodic cylinder, but it
takes equal values at `q = ±c/2`, so one integration by parts has no seam term.

For a jointly smooth `c`-periodic `φ` and `R ≥ 1`, `ρ ∈ (t, s)`:

* (`CutE1Deriv`, calculus) `d/dρ Σ_k ∫ χ_R²⟨x⟩^{-2m}|∂_kφ|² = cutRate`, the rate after the integration
  by parts in `x_k`;
* (`CutRateBound`, Young) with `∂_ρφ = χ - νΔφ - v·∇φ`, `|v| ≤ C_V`, `‖χ‖_{X_{-m}} ≤ M`:
  `νY_R - K(1 + E_{2R}) ≤ cutRate ≤ 3νY_R + K(1 + E_{2R})`, `Y_R = ∫ χ_R²⟨x⟩^{-2m}|Δφ|²`. The transport
  term is integrated by parts onto `Δφ`, so only `sup|v|` enters (SP 3068).

The assembly of these inequalities is abstract (`CutEnergySqueeze`): the lower bound gives
`∫_t^r Y_R ≤ B` uniformly in `R`, so `Y = sup_R Y_R` is integrable, and then
`|E(r₂) - E(r₁)| ≤ ∫_{r₁}^{r₂} (3νY + K(1 + E))`: `E` is continuous on `[t, s)`. Since `∂_kφ(r') → ∂_kφ(r)`
pointwise, continuity of the energy upgrades to strong convergence in `X_{-m,c}`
(`L2StrongOfEnergy`, the Riesz-Scheffé lemma).

`adjointWeakH1Cont_of` proves `AdjointWeakH1Cont m` from these and from `AdjointIntegratedH1 m`,
`AdjWeakChiBound m`. Joint regularity of the slice derivatives is proved here (`jointSmooth_pdCx`).

The lower bound also gives `AdjointH1Gronwall` without a time weight: pick `r' > r` with `E(r') < ∞`
(the time integral is finite); then `E_R(r) ≤ E_R(r') + K∫_r^{r'}(1 + E_{2R})` uniformly in `R`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff Interval

namespace UnforcedLeray.Short.IIIa

/-! ## Joint regularity of the slices -/

section Joint

variable {t s : ℝ} {ψ : ℝ → ℝ × ℝ → ℂ}

theorem adjStrip_uniqueDiff (t s : ℝ) : UniqueDiffOn ℝ (Ico t s ×ˢ (univ : Set (ℝ × ℝ))) :=
  (uniqueDiffOn_Ico t s).prod uniqueDiffOn_univ

/-- The slice derivative is a component of the derivative within the strip. -/
theorem hasFDerivAt_slice
    (hj : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => ψ p.1 p.2) (Ico t s ×ˢ univ)) {r : ℝ}
    (hr : r ∈ Ico t s) (x : ℝ × ℝ) :
    HasFDerivAt (ψ r)
      ((fderivWithin ℝ (fun p : ℝ × (ℝ × ℝ) => ψ p.1 p.2) (Ico t s ×ˢ univ) (r, x)).comp
        (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ))) x := by
  have hmem : ((r, x) : ℝ × (ℝ × ℝ)) ∈ Ico t s ×ˢ (univ : Set (ℝ × ℝ)) := ⟨hr, mem_univ _⟩
  have h1 : HasFDerivWithinAt (fun p : ℝ × (ℝ × ℝ) => ψ p.1 p.2)
      (fderivWithin ℝ (fun p : ℝ × (ℝ × ℝ) => ψ p.1 p.2) (Ico t s ×ˢ univ) (r, x))
      (Ico t s ×ˢ univ) (r, x) :=
    ((hj _ hmem).differentiableWithinAt (by simp)).hasFDerivWithinAt
  have hι : HasFDerivAt (fun y : ℝ × ℝ => ((r, y) : ℝ × (ℝ × ℝ)))
      (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)) x :=
    (hasFDerivAt_const r x).prodMk (hasFDerivAt_id x)
  have hmaps : MapsTo (fun y : ℝ × ℝ => ((r, y) : ℝ × (ℝ × ℝ))) univ
      (Ico t s ×ˢ (univ : Set (ℝ × ℝ))) := fun y _ => ⟨hr, mem_univ y⟩
  have h2 := h1.comp x hι.hasFDerivWithinAt hmaps
  rw [hasFDerivWithinAt_univ] at h2
  exact h2

theorem pdCx_eq_fderivWithin
    (hj : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => ψ p.1 p.2) (Ico t s ×ˢ univ)) {r : ℝ}
    (hr : r ∈ Ico t s) (k : Fin 2) (x : ℝ × ℝ) :
    pdCx k (ψ r) x =
      fderivWithin ℝ (fun p : ℝ × (ℝ × ℝ) => ψ p.1 p.2) (Ico t s ×ˢ univ) (r, x)
        ((0 : ℝ), B0579.dir k) := by
  unfold pdCx
  rw [(hasFDerivAt_slice hj hr x).fderiv]
  simp

/-- **The slice derivative of a jointly smooth field is jointly smooth.** -/
theorem jointSmooth_pdCx
    (hj : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => ψ p.1 p.2) (Ico t s ×ˢ univ)) (k : Fin 2) :
    ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => pdCx k (ψ p.1) p.2) (Ico t s ×ˢ univ) := by
  have h : ContDiffOn ℝ ∞
      (fderivWithin ℝ (fun p : ℝ × (ℝ × ℝ) => ψ p.1 p.2) (Ico t s ×ˢ univ))
      (Ico t s ×ˢ univ) :=
    hj.fderivWithin (adjStrip_uniqueDiff t s) (by simp)
  have h2 : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) =>
      fderivWithin ℝ (fun p : ℝ × (ℝ × ℝ) => ψ p.1 p.2) (Ico t s ×ˢ univ) p
        ((0 : ℝ), B0579.dir k)) (Ico t s ×ˢ univ) :=
    h.clm_apply contDiffOn_const
  refine h2.congr fun p hp => ?_
  exact pdCx_eq_fderivWithin hj hp.1 k p.2

/-- The slice Laplacian of a jointly smooth field is jointly smooth. -/
theorem jointSmooth_ladLapCx
    (hj : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => ψ p.1 p.2) (Ico t s ×ˢ univ)) :
    ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => ladLapCx (ψ p.1) p.2) (Ico t s ×ˢ univ) := by
  unfold ladLapCx
  have h0 := jointSmooth_pdCx (ψ := fun r => pdCx 0 (ψ r)) (jointSmooth_pdCx hj 0) 0
  have h1 := jointSmooth_pdCx (ψ := fun r => pdCx 1 (ψ r)) (jointSmooth_pdCx hj 1) 1
  exact h0.add h1

/-- The time derivative at an interior age is the time component of the derivative in the strip. -/
theorem ladDt_eq_fderivWithin
    (hj : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => ψ p.1 p.2) (Ico t s ×ˢ univ)) {ρ : ℝ}
    (hρ : ρ ∈ Ioo t s) (x : ℝ × ℝ) :
    ladDt ψ ρ x =
      fderivWithin ℝ (fun p : ℝ × (ℝ × ℝ) => ψ p.1 p.2) (Ico t s ×ˢ univ) (ρ, x)
        ((1 : ℝ), (0 : ℝ × ℝ)) := by
  have hmem : ((ρ, x) : ℝ × (ℝ × ℝ)) ∈ Ico t s ×ˢ (univ : Set (ℝ × ℝ)) :=
    ⟨Ioo_subset_Ico_self hρ, mem_univ _⟩
  have hnhds : Ico t s ×ˢ (univ : Set (ℝ × ℝ)) ∈ 𝓝 ((ρ, x) : ℝ × (ℝ × ℝ)) :=
    prod_mem_nhds (Ico_mem_nhds hρ.1 hρ.2) univ_mem
  have h1 : HasFDerivAt (fun p : ℝ × (ℝ × ℝ) => ψ p.1 p.2)
      (fderivWithin ℝ (fun p : ℝ × (ℝ × ℝ) => ψ p.1 p.2) (Ico t s ×ˢ univ) (ρ, x)) (ρ, x) :=
    (((hj _ hmem).differentiableWithinAt (by simp)).hasFDerivWithinAt).hasFDerivAt hnhds
  have hι : HasDerivAt (fun r : ℝ => ((r, x) : ℝ × (ℝ × ℝ))) ((1 : ℝ), (0 : ℝ × ℝ)) ρ :=
    (hasDerivAt_id ρ).prodMk (hasDerivAt_const ρ x)
  have h2 := h1.comp_hasDerivAt ρ hι
  exact ladDt_eq_of_hasDerivAt h2

/-- `∂_ρψ(ρ)` is continuous in `x` at an interior age. -/
theorem continuous_ladDt
    (hj : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => ψ p.1 p.2) (Ico t s ×ˢ univ)) {ρ : ℝ}
    (hρ : ρ ∈ Ioo t s) : Continuous (ladDt ψ ρ) := by
  have h : ContinuousOn (fun p : ℝ × (ℝ × ℝ) =>
      fderivWithin ℝ (fun p : ℝ × (ℝ × ℝ) => ψ p.1 p.2) (Ico t s ×ˢ univ) p
        ((1 : ℝ), (0 : ℝ × ℝ))) (Ico t s ×ˢ univ) :=
    (hj.fderivWithin (adjStrip_uniqueDiff t s) (m := ∞) (by simp)).continuousOn.clm_apply
      continuousOn_const
  have hc : Continuous fun x : ℝ × ℝ => fderivWithin ℝ (fun p : ℝ × (ℝ × ℝ) => ψ p.1 p.2)
      (Ico t s ×ˢ univ) (ρ, x) ((1 : ℝ), (0 : ℝ × ℝ)) :=
    h.comp_continuous (continuous_const.prodMk continuous_id)
      fun x => ⟨Ioo_subset_Ico_self hρ, mem_univ x⟩
  have e : ladDt ψ ρ = fun x : ℝ × ℝ => fderivWithin ℝ (fun p : ℝ × (ℝ × ℝ) => ψ p.1 p.2)
      (Ico t s ×ˢ univ) (ρ, x) ((1 : ℝ), (0 : ℝ × ℝ)) :=
    funext fun x => ladDt_eq_fderivWithin hj hρ x
  rw [e]
  exact hc

/-- Pointwise convergence of the slice derivatives along the strip. -/
theorem tendsto_pdCx_slice
    (hj : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => ψ p.1 p.2) (Ico t s ×ˢ univ)) {r : ℝ}
    (hr : r ∈ Ico t s) (k : Fin 2) (x : ℝ × ℝ) :
    Tendsto (fun r' => pdCx k (ψ r') x) (𝓝[Ico t s] r) (𝓝 (pdCx k (ψ r) x)) := by
  have hmem : ((r, x) : ℝ × (ℝ × ℝ)) ∈ Ico t s ×ˢ (univ : Set (ℝ × ℝ)) := ⟨hr, mem_univ _⟩
  have h : ContinuousWithinAt (fun p : ℝ × (ℝ × ℝ) => pdCx k (ψ p.1) p.2)
      (Ico t s ×ˢ univ) (r, x) := (jointSmooth_pdCx hj k).continuousOn _ hmem
  have hι : ContinuousWithinAt (fun r' : ℝ => ((r', x) : ℝ × (ℝ × ℝ))) (Ico t s) r :=
    (continuous_id.prodMk continuous_const).continuousWithinAt
  exact ContinuousWithinAt.comp (g := fun p : ℝ × (ℝ × ℝ) => pdCx k (ψ p.1) p.2)
    (f := fun r' : ℝ => ((r', x) : ℝ × (ℝ × ℝ))) (t := Ico t s ×ˢ univ) h hι
    fun r' hr' => ⟨hr', mem_univ x⟩

end Joint

/-- `∫ u dμ = ∫_{C_c} ⟨x⟩^{-2m} u` for the measure of `X_{-m,c}`. -/
theorem integral_cellMeasure_eq (c m : ℝ) (u : ℝ × ℝ → ℝ) :
    ∫ x, u x ∂(B0579.cellMeasure c (-m)) = ∫ x in B0579.cell c, B0579.jb x ^ (-m) * u x := by
  unfold B0579.cellMeasure
  rw [integral_withDensity_eq_integral_smul (B0579.measurable_density (-m))]
  simp only [NNReal.smul_def, B0579.coe_density, smul_eq_mul]

/-! ## The energies of a slice -/

/-- The cut gradient energy `Σ_k ∫_{C_c} χ_R² ⟨x⟩^{-2m} |∂_kΦ|²`. -/
def cutE1 (c m R : ℝ) (Φ : ℝ × ℝ → ℂ) : ℝ :=
  ∑ k : Fin 2, ∫ x in B0579.cell c, ladCut R x ^ 2 * (B0579.jb x ^ (-m) * ‖pdCx k Φ x‖ ^ 2)

/-- The cut Laplacian energy `∫_{C_c} χ_R² ⟨x⟩^{-2m} |ΔΦ|²`. -/
def cutLap (c m R : ℝ) (Φ : ℝ × ℝ → ℂ) : ℝ :=
  ∫ x in B0579.cell c, ladCut R x ^ 2 * (B0579.jb x ^ (-m) * ‖ladLapCx Φ x‖ ^ 2)

/-- The gradient energy `Σ_k ‖∂_kΦ‖²_{X_{-m,c}}`. -/
def gradE (c m : ℝ) (Φ : ℝ × ℝ → ℂ) : ℝ :=
  ∑ k : Fin 2, ∫ x, ‖pdCx k Φ x‖ ^ 2 ∂(B0579.cellMeasure c (-m))

/-- The rate of `cutE1` along `∂_ρΦ = F`, after the integration by parts in `x_k`:
`-2∫ χ_R²⟨x⟩^{-2m} Re(conj(ΔΦ) F) - 2Σ_k ∫ ∂_k(χ_R²⟨x⟩^{-2m}) Re(conj(∂_kΦ) F)`. -/
def cutRate (c m R : ℝ) (Φ F : ℝ × ℝ → ℂ) : ℝ :=
  -(2 * ∫ x in B0579.cell c, ladCut R x ^ 2 *
      (B0579.jb x ^ (-m) * ((starRingEnd ℂ) (ladLapCx Φ x) * F x).re)) -
    2 * ∑ k : Fin 2, ∫ x in B0579.cell c,
      B0579.pd k (fun y => ladCut R y ^ 2 * B0579.jb y ^ (-m)) x *
        ((starRingEnd ℂ) (pdCx k Φ x) * F x).re

/-! ## The leaves -/

/-- **Leaf 1: the derivative of the cut energy** (SP 3060-3067; calculus). For `ψ` jointly smooth on
`[t, s) × ℝ²` and `c`-periodic, `ρ ∈ (t, s)`: differentiate under the integral on the compact band
`supp χ_R`, `∂_ρ∂_kψ = ∂_k∂_ρψ`, and integrate by parts in `x_k`. In `q` the boundary terms cancel:
`∂_kψ`, `∂_ρψ` are `c`-periodic, `χ_R` depends on `η` only and `⟨(±c/2, η)⟩` takes one value. In `η`
the band is compact. Valid for every real `m`. -/
def CutE1Deriv : Prop :=
  ∀ (c m R t s : ℝ) (ψ : ℝ → ℝ × ℝ → ℂ), 0 < c → 0 < R →
    ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => ψ p.1 p.2) (Ico t s ×ˢ univ) →
    (∀ r ∈ Ico t s, ∀ x : ℝ × ℝ, ψ r (x.1 + c, x.2) = ψ r x) →
    ∀ ρ ∈ Ioo t s, HasDerivAt (fun r => cutE1 c m R (ψ r)) (cutRate c m R (ψ ρ) (ladDt ψ ρ)) ρ

/-- **Leaf 2: the bound of the rate** (SP 3062-3071: "the diffusion-weight errors have coefficient
`C_m β` and the transport and compact terms have coefficient `C_b`"). With
`F = χ - νΔΦ - V·∇Φ`, `|V| ≤ C_V` on the cell and `‖χ‖_{X_{-m,c}} ≤ M`, for `R ≥ 1`:
`νY_R - K(1 + E_{2R}) ≤ cutRate ≤ 3νY_R + K(1 + E_{2R})`, `K = K(m, ν, C_V, M)`. Proof: pointwise on
the cell, Young's inequality, `|∂_k(χ_R²⟨x⟩^{-2m})| ≤ K₂χ_R⟨x⟩^{-2m}` (`LadCutProps`, `AdjWeightGrad`,
`R ≥ 1`) and `χ_{2R} = 1` on `supp χ_R`; then integrate on the band. No derivative of `V` enters. -/
def CutRateBound : Prop :=
  ∀ (m ν CV M : ℝ), 0 < ν → ∃ K : ℝ, 0 ≤ K ∧
    ∀ (c R : ℝ) (Φ χ F : ℝ × ℝ → ℂ) (V : ℝ × ℝ → Fin 2 → ℝ), 0 < c → 1 ≤ R →
      ContDiff ℝ ∞ Φ → Continuous χ → Continuous F →
      (∀ x ∈ B0579.cell c, ∀ j : Fin 2, |V x j| ≤ CV) →
      (∀ x : ℝ × ℝ, F x = χ x - (ν : ℂ) * ladLapCx Φ x -
        ((V x 0 : ℂ) * pdCx 0 Φ x + (V x 1 : ℂ) * pdCx 1 Φ x)) →
      MemLp χ 2 (B0579.cellMeasure c (-m)) →
      eLpNorm χ 2 (B0579.cellMeasure c (-m)) ≤ ENNReal.ofReal M →
      ν * cutLap c m R Φ - K * (1 + cutE1 c m (2 * R) Φ) ≤ cutRate c m R Φ F ∧
        cutRate c m R Φ F ≤ 3 * ν * cutLap c m R Φ + K * (1 + cutE1 c m (2 * R) Φ)

/-- **Leaf 3: the cut energies are continuous in the age** on `[t, s)` (the integrands are jointly
continuous by `jointSmooth_pdCx`, `jointSmooth_ladLapCx`, and vanish off a compact band). -/
def CutE1TimeCont : Prop :=
  ∀ (c m R t s : ℝ) (ψ : ℝ → ℝ × ℝ → ℂ), 0 < c → 0 < R →
    ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => ψ p.1 p.2) (Ico t s ×ˢ univ) →
    ContinuousOn (fun r => cutE1 c m R (ψ r)) (Ico t s) ∧
      ContinuousOn (fun r => cutLap c m R (ψ r)) (Ico t s)

/-- **Leaf 4: the cut energies of a slice** (`0 ≤ χ_R ≤ 1`, `χ_R` increases with `R` and tends to
`1`; dominated convergence). -/
def CutSliceProps : Prop :=
  ∀ (c m : ℝ) (Φ : ℝ × ℝ → ℂ), 0 < c → ContDiff ℝ ∞ Φ →
    (∀ R : ℝ, 0 < R → 0 ≤ cutE1 c m R Φ ∧ 0 ≤ cutLap c m R Φ) ∧
    (∀ R R' : ℝ, 0 < R → R ≤ R' → cutLap c m R Φ ≤ cutLap c m R' Φ) ∧
    ((∀ k : Fin 2, MemLp (pdCx k Φ) 2 (B0579.cellMeasure c (-m))) →
      (∀ R : ℝ, 0 < R → cutE1 c m R Φ ≤ gradE c m Φ) ∧
      Tendsto (fun n : ℕ => cutE1 c m ((n : ℝ) + 1) Φ) atTop (𝓝 (gradE c m Φ)))

/-- **Leaf 5: the energy squeeze** (SP 3072-3073; real analysis, no equation). Let `P n` be
continuous on `[t, s)` with `P n → E` pointwise, `Y n ≥ 0` continuous and increasing in `n`, `E` integrable
on `[t, r]` for `r < s`, and `νY_n - K(1 + E) ≤ (P n)' ≤ 3νY_n + K(1 + E)` on `(t, s)`. Then `E` is continuous
on `[t, s)`. Proof: integrating the lower bound over `[t, r]` (`P n ≥ 0`) bounds `∫_t^r Y_n` uniformly in `n`
(`intervalIntegral.integral_le_sub_of_hasDeriv_right_of_le`); by monotone convergence
`Ȳ = sup_n Y_n` is integrable on `[t, r]`; integrating both bounds over `[r₁, r₂]`
(`intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le`) and letting `n → ∞` gives
`|E(r₂) - E(r₁)| ≤ ∫_{r₁}^{r₂} (3νȲ + K(1 + E))`. -/
def CutEnergySqueeze : Prop :=
  ∀ (t s ν K : ℝ) (P Y : ℕ → ℝ → ℝ) (E : ℝ → ℝ), t < s → 0 < ν → 0 ≤ K →
    (∀ n, ContinuousOn (P n) (Ico t s)) → (∀ n, ContinuousOn (Y n) (Ico t s)) →
    (∀ n, ∀ ρ ∈ Ico t s, 0 ≤ P n ρ) → (∀ n, ∀ ρ ∈ Ico t s, 0 ≤ Y n ρ) →
    (∀ ρ ∈ Ico t s, Monotone fun n => Y n ρ) →
    (∀ ρ ∈ Ico t s, Tendsto (fun n => P n ρ) atTop (𝓝 (E ρ))) →
    (∀ r ∈ Ico t s, IntervalIntegrable E volume t r) →
    (∀ n, ∀ ρ ∈ Ioo t s, ∃ D : ℝ, HasDerivAt (P n) D ρ ∧
      ν * Y n ρ - K * (1 + E ρ) ≤ D ∧ D ≤ 3 * ν * Y n ρ + K * (1 + E ρ)) →
    ContinuousOn E (Ico t s)

/-- **Leaf 6: pointwise convergence and convergence of the energy give strong convergence** (the
Riesz-Scheffé lemma for two components): apply Fatou (`lintegral_liminf_le'`) along sequences to
`2Σ_k(|F_k|² + |F₀_k|²) - Σ_k|F_k - F₀_k|² ≥ 0`. -/
def L2StrongOfEnergy : Prop :=
  ∀ (μ : Measure (ℝ × ℝ)) (l : Filter ℝ) [l.IsCountablyGenerated] (F : ℝ → Fin 2 → ℝ × ℝ → ℂ)
    (F₀ : Fin 2 → ℝ × ℝ → ℂ),
    (∀ᶠ r in l, ∀ k, MemLp (F r k) 2 μ) → (∀ k, MemLp (F₀ k) 2 μ) →
    (∀ k x, Tendsto (fun r => F r k x) l (𝓝 (F₀ k x))) →
    Tendsto (fun r => ∑ k, ∫ x, ‖F r k x‖ ^ 2 ∂μ) l (𝓝 (∑ k, ∫ x, ‖F₀ k x‖ ^ 2 ∂μ)) →
    ∀ k, Tendsto (fun r => eLpNorm (F r k - F₀ k) 2 μ) l (𝓝 0)

/-- **Leaf 7: the energy is integrable in the age** (measurability: `gradE ∘ ψ` is the pointwise
limit of the continuous cut energies; finiteness: `∫⁻` of `AdjointIntegratedH1`, with `memH1` to pass
from `∫⁻` to `∫`). -/
def GradEIntegrable : Prop :=
  ∀ (c m t s : ℝ) (ψ : ℝ → ℝ × ℝ → ℂ), 0 < c → t < s →
    ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => ψ p.1 p.2) (Ico t s ×ˢ univ) →
    (∀ r ∈ Ico t s, ∀ k : Fin 2, MemLp (pdCx k (ψ r)) 2 (B0579.cellMeasure c (-m))) →
    (∀ k : Fin 2, ∫⁻ ρ in Ioc t s, (∫⁻ x, ‖pdCx k (ψ ρ) x‖ₑ ^ (2 : ℝ)
      ∂(B0579.cellMeasure c (-m))) < ⊤) →
    ∀ r ∈ Ico t s, IntervalIntegrable (fun ρ => gradE c m (ψ ρ)) volume t r

/-! ## The assembly -/

/-- `χ(ρ) = ∂_ρφ + νΔφ + v·∇φ` is continuous in `x`, at an interior age. -/
theorem continuous_ladChi {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) {t s ρ : ℝ}
    {φ : ℝ → ℝ × ℝ → ℂ} (ht : 0 ≤ t)
    (hj : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (Ico t s ×ˢ univ))
    (hρ : ρ ∈ Ioo t s) : Continuous (ladChi tr φ ρ) := by
  have hslice : ContDiff ℝ ∞ (φ ρ) := adjContDiff_slice hj (Ioo_subset_Ico_self hρ)
  have hpd : ∀ (Φ : ℝ × ℝ → ℂ) (k : Fin 2), ContDiff ℝ ∞ Φ → ContDiff ℝ ∞ (pdCx k Φ) := by
    intro Φ k hΦ
    exact (hΦ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hv : ∀ j : Fin 2, Continuous fun x => ((tr.v ρ x j : ℝ) : ℂ) := by
    intro j
    have h : ContDiff ℝ ∞ (fun w => tr.v ρ w j) :=
      (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp
        (UnforcedLeray.B0238.contDiff_Vc tr (ht.trans hρ.1.le))
    exact Complex.continuous_ofReal.comp h.continuous
  have hlap : Continuous (ladLapCx (φ ρ)) := by
    unfold ladLapCx
    exact (hpd _ 0 (hpd _ 0 hslice)).continuous.add (hpd _ 1 (hpd _ 1 hslice)).continuous
  have htr : Continuous (ladTransport tr ρ (φ ρ)) := by
    unfold ladTransport
    exact ((hv 0).mul (hpd _ 0 hslice).continuous).add ((hv 1).mul (hpd _ 1 hslice).continuous)
  have e : ladChi tr φ ρ = fun x => ladDt φ ρ x + (ν : ℂ) * ladLapCx (φ ρ) x +
      ladTransport tr ρ (φ ρ) x := rfl
  rw [e]
  exact ((continuous_ladDt hj hρ).add (continuous_const.mul hlap)).add htr

/-- **`AdjointWeakH1Cont` from the leaves** (SP 3060-3071). -/
theorem adjointWeakH1Cont_of (m : ℝ) (hI : AdjointIntegratedH1 m) (hChi : AdjWeakChiBound m)
    (hD : CutE1Deriv) (hB : CutRateBound) (hC : CutE1TimeCont) (hS : CutSliceProps)
    (hSq : CutEnergySqueeze) (hL : L2StrongOfEnergy) (hE : GradEIntegrable) :
    AdjointWeakH1Cont m := by
  intro ν hν hν1 tr hb t s ht hts G hG φ hφ hj hm r hr k
  have hc0 : (0 : ℝ) < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hν _
  have hc1 : (1 : ℝ) ≤ ν ^ (-2 : ℝ) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hν hν1 (by norm_num)
  have hper := hφ.periodic
  obtain ⟨M, hM⟩ := hChi ν _ tr t s _ φ hc1 ⟨hν, hc0, ht, hts, hb, hφ, hj⟩
  obtain ⟨CV, hCV⟩ := hb s (ht.trans hts.le)
  obtain ⟨K, hK0, hK⟩ := hB m ν CV M hν
  have hslice : ∀ ρ ∈ Ico t s, ContDiff ℝ ∞ (φ ρ) := fun ρ hρ => adjContDiff_slice hj hρ
  have hn1 : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1 := fun n => by positivity
  -- the continuity of the energy
  have hEc : ContinuousOn (fun ρ => gradE (ν ^ (-2 : ℝ)) m (φ ρ)) (Ico t s) := by
    refine hSq t s ν K (fun n ρ => cutE1 (ν ^ (-2 : ℝ)) m ((n : ℝ) + 1) (φ ρ))
      (fun n ρ => cutLap (ν ^ (-2 : ℝ)) m ((n : ℝ) + 1) (φ ρ)) _ hts hν hK0
      (fun n => (hC _ m _ t s φ hc0 (hn1 n) hj).1) (fun n => (hC _ m _ t s φ hc0 (hn1 n) hj).2)
      (fun n ρ hρ => ((hS _ m _ hc0 (hslice ρ hρ)).1 _ (hn1 n)).1)
      (fun n ρ hρ => ((hS _ m _ hc0 (hslice ρ hρ)).1 _ (hn1 n)).2)
      (fun ρ hρ n n' hnn => (hS _ m _ hc0 (hslice ρ hρ)).2.1 _ _ (hn1 n) (by
        have : (n : ℝ) ≤ n' := by exact_mod_cast hnn
        linarith))
      (fun ρ hρ => ((hS _ m _ hc0 (hslice ρ hρ)).2.2 (hm ρ hρ)).2)
      (hE _ m t s φ hc0 hts hj hm
        (fun k => hI ν hν hν1 tr hb t s ht hts G hG φ hφ hj t ⟨le_rfl, hts⟩ k))
      ?_
    intro n ρ hρ
    have hρ' : ρ ∈ Ico t s := Ioo_subset_Ico_self hρ
    have hρS : ρ ∈ Icc (0 : ℝ) s := ⟨ht.trans hρ.1.le, hρ.2.le⟩
    have hR : (1 : ℝ) ≤ (n : ℝ) + 1 := by
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    obtain ⟨h1, h2⟩ := hK _ ((n : ℝ) + 1) (φ ρ) (ladChi tr φ ρ) (ladDt φ ρ)
      (fun x j => tr.v ρ x j) hc0 hR (hslice ρ hρ') (continuous_ladChi tr ht hj hρ)
      (continuous_ladDt hj hρ) (fun x hx j => (hCV ρ hρS x hx).1 j)
      (fun x => by
        have e : ladChi tr φ ρ x = ladDt φ ρ x + (ν : ℂ) * ladLapCx (φ ρ) x +
            ladTransport tr ρ (φ ρ) x := rfl
        rw [e]
        unfold ladTransport
        ring)
      (hM ρ hρ).1 (hM ρ hρ).2
    have hle : cutE1 (ν ^ (-2 : ℝ)) m (2 * ((n : ℝ) + 1)) (φ ρ) ≤
        gradE (ν ^ (-2 : ℝ)) m (φ ρ) :=
      ((hS _ m _ hc0 (hslice ρ hρ')).2.2 (hm ρ hρ')).1 _ (by positivity)
    have hle2 : K * (1 + cutE1 (ν ^ (-2 : ℝ)) m (2 * ((n : ℝ) + 1)) (φ ρ)) ≤
        K * (1 + gradE (ν ^ (-2 : ℝ)) m (φ ρ)) :=
      mul_le_mul_of_nonneg_left (by linarith) hK0
    exact ⟨_, hD _ m _ t s φ hc0 (hn1 n) hj hper ρ hρ, by linarith, by linarith⟩
  -- strong convergence
  have hcw : Tendsto (fun ρ => gradE (ν ^ (-2 : ℝ)) m (φ ρ)) (𝓝[Ico t s] r)
      (𝓝 (gradE (ν ^ (-2 : ℝ)) m (φ r))) := hEc r hr
  exact hL (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) (𝓝[Ico t s] r) (fun r' k => pdCx k (φ r'))
    (fun k => pdCx k (φ r))
    (by filter_upwards [self_mem_nhdsWithin] with r' hr' k using hm r' hr' k)
    (fun k => hm r hr k) (fun k x => tendsto_pdCx_slice hj hr k x) hcw k

end UnforcedLeray.Short.IIIa
