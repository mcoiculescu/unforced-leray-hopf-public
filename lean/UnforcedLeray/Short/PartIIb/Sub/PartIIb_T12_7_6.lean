import UnforcedLeray.Short.PartIIb.Sub.T12_7

/-!
# Part II-b, leaf `PartII-b:T12/7/6` (`DeqSliceIdentity`): decomposition

Source: `the November 2 reference manuscript`
lines 1923-1927 (`T_0 F(s) = ∫_0^s (t/s)^μ e^{ν(s-t)Δ} P_0 F(t) dt/t`).

`φ(s) = s^{1-μ} Σ_i Φ_i(s)`, `Φ_i(s) = ∫ g_i U_i(s,·)`.  Given the algebraic splitting of `deqPair`
(`DeqPairSplit`, from `DeqHeatSymm`), the derivative `DeqPairDeriv`, the boundary value
`DeqHeatPair`, vanishing for large `s`, integrability of `s^{-μ} deqPair` and local
integrability of `g_i ψ`, the identity is the fundamental theorem of calculus on `(t, ∞)`
(proved here: `deqSliceIdentity_of`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- Leaf `T12/7/6/1` (algebraic splitting; SP 1923-1927).  For `s > t`,
`deqPair ν μ g Ψ t s = Σ_i [(μ-1) Φ_i(s) - s D_i(s)]`, `Φ_i(s) = ∫ g_i deqSmooth_i`,
`D_i(s) = ∫ g_i deqSmoothD_i`.  Proof: `flatTranspose ν μ Ψ (s,z) i = (μ-1) Ψ_i(s,z) - s ψ_i(s,z)`
with `ψ_i = ∂_sΨ_i + ν(∂_q²+∂_η²)Ψ_i`; split the `z`-integral using integrability of
`(flatHeat θ g)_i ψ` (from `deqhsAbsInt`, `HeatSymm/Leaf/DeqhsAbsInt.lean`) and apply `deqHeatSymm`
(`θ = ν(s-t)`) to the continuous compactly supported slices `Ψ_i(s,·)` and `ψ_i(s,·)`
(`deqT_cpd_contDiff`, `HasCompactSupport.fderiv`). -/
def DeqPairSplit : Prop :=
  ∀ (ν : ℝ) (μ : ℂ) (c r t : ℝ), 0 < ν → 0 < t → 0 < c → 1 < r →
    ∀ g : ℝ × ℝ → CMerid, DeqSliceGood c r g →
      ∀ Ψ : Coord → Fin 2 → ℝ, IsPlanarSolTest Ψ → ∀ s : ℝ, t < s →
        deqPair ν μ g Ψ t s = ∑ i : Fin 2,
          ((μ - 1) * (∫ z : ℝ × ℝ, g z i * (deqSmooth ν Ψ i t s z : ℂ)) -
            (s : ℂ) * (∫ z : ℝ × ℝ, g z i * (deqSmoothD ν Ψ i t s z : ℂ)))

/-- Leaf `T12/7/6/2` (integrability on `(t,∞)`; SP 1923-1927).  `s ↦ s^{-μ} deqPair ν μ g Ψ t s`
is integrable on `(t, ∞)`: it vanishes for `s ≥ H` (`flatTranspose Ψ (s,·) = 0` there,
`deqTransposeTest`), is measurable in `s` (e.g. as `-φ'` via `measurable_deriv`, or Fubini), and is
bounded on `(t, H]` by the heat contraction (`Tasks/FlatCausal/FlatHeatContraction.lean`, uniform in
the age) and Hölder over the finitely many periodic cells meeting the compact support of
`flatTranspose Ψ`. -/
def DeqPairIntegrableIoi : Prop :=
  ∀ (ν : ℝ) (μ : ℂ) (c r t : ℝ), 0 < ν → 0 < t → 0 < c → 1 < r →
    ∀ g : ℝ × ℝ → CMerid, DeqSliceGood c r g →
      ∀ Ψ : Coord → Fin 2 → ℝ, IsPlanarSolTest Ψ →
        IntegrableOn (fun s : ℝ => ((s : ℂ) ^ (-μ)) * deqPair ν μ g Ψ t s) (Ioi t)

/-- Leaf `T12/7/6/3` (vanishing for large age; SP 1923-1927).  `Ψ` has compact support, so
`Ψ(s,·) = 0` for `s ≥ H`, hence `deqSmooth ν Ψ i t s = 0` and `Φ_i(s) = 0`. -/
def DeqPhiVanish : Prop :=
  ∀ (ν c r t : ℝ), 0 < ν → 0 < t → 0 < c → 1 < r →
    ∀ g : ℝ × ℝ → CMerid, DeqSliceGood c r g →
      ∀ Ψ : Coord → Fin 2 → ℝ, IsPlanarSolTest Ψ →
        ∃ H : ℝ, ∀ s : ℝ, H ≤ s → ∀ i : Fin 2,
          ∫ z : ℝ × ℝ, g z i * (deqSmooth ν Ψ i t s z : ℂ) = 0

/-- Leaf `T12/7/6/4` (local integrability of a periodic `L^r` slice against a planar test slice).
For a `DeqSliceGood` slice `g` and a planar solenoidal test `Ψ`, `z ↦ g_i(z) Ψ_i(t,z)` is integrable
on the plane: `z ↦ Ψ_i(t,z)` is continuous with compact support (`IsCoordTest`; compose with the
closed embedding `z ↦ (t,z)`), and `g` is `q`-periodic with finite cell `L^r` norm, hence in
`L^r_loc` (finitely many cells cover the support; compare `Tasks/FlatUnique/CellStream/HrBox.lean`
and `Cyl.eLpNorm_planarConv_periodic_le`), so Hölder against a bounded function on a compact set. -/
def DeqSliceLocInt : Prop :=
  ∀ (c r t : ℝ) (g : ℝ × ℝ → CMerid), 0 < c → 1 < r → DeqSliceGood c r g →
    ∀ Ψ : Coord → Fin 2 → ℝ, IsPlanarSolTest Ψ → ∀ i : Fin 2,
      Integrable (fun z : ℝ × ℝ => g z i * (Ψ (t, z) i : ℂ))

private lemma cpow_hasDerivAt (a : ℂ) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (fun y : ℝ => (y : ℂ) ^ a) (a * (s : ℂ) ^ (a - 1)) s := by
  have h1 : HasDerivAt (fun y : ℂ => y ^ a) (a * (s : ℂ) ^ (a - 1) * 1) (s : ℂ) :=
    (hasDerivAt_id (s : ℂ)).cpow_const (Complex.ofReal_mem_slitPlane.2 hs)
  simpa using h1.comp_ofReal

/-- `DeqSliceIdentity` from the four leaves, `DeqHeatPair`, `DeqPairDeriv` (fundamental theorem of
calculus on `(t, ∞)`). -/
theorem deqSliceIdentity_of (h1 : DeqPairSplit) (h2 : DeqPairIntegrableIoi) (h3 : DeqPhiVanish)
    (h4 : DeqSliceLocInt) (hHP : DeqHeatPair) (hPD : DeqPairDeriv) : DeqSliceIdentity := by
  intro ν μ c r t hν ht hc hr g hg Ψ hΨ
  set Φ : Fin 2 → ℝ → ℂ := fun i s => ∫ z : ℝ × ℝ, g z i * (deqSmooth ν Ψ i t s z : ℂ) with hΦ
  set D : Fin 2 → ℝ → ℂ := fun i s => ∫ z : ℝ × ℝ, g z i * (deqSmoothD ν Ψ i t s z : ℂ) with hD
  set S : ℂ := ∑ i : Fin 2, ∫ z : ℝ × ℝ, g z i * (Ψ (t, z) i : ℂ) with hS
  set φ : ℝ → ℂ := fun s => (s : ℂ) ^ (1 - μ) * ∑ i : Fin 2, Φ i s with hφ
  set f' : ℝ → ℂ := fun s => -((s : ℂ) ^ (-μ) * deqPair ν μ g Ψ t s) with hf'
  have hsplit := h1 ν μ c r t hν ht hc hr g hg Ψ hΨ
  -- derivative of φ
  have hderiv : ∀ s ∈ Ioi t, HasDerivAt φ (f' s) s := by
    intro s hs
    have hs' : t < s := hs
    have hs0 : 0 < s := ht.trans hs'
    have hd : ∀ i, HasDerivAt (Φ i) (D i s) s := fun i => hPD ν c r t hν ht hc hr g hg Ψ hΨ i s hs'
    have hsum : HasDerivAt (fun s => ∑ i : Fin 2, Φ i s) (∑ i : Fin 2, D i s) s :=
      HasDerivAt.fun_sum (fun i _ => hd i)
    have hp := (cpow_hasDerivAt (1 - μ) hs0).mul hsum
    have hne : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hs0.ne'
    have hpow : (s : ℂ) ^ (1 - μ) = (s : ℂ) ^ (-μ) * (s : ℂ) := by
      rw [sub_eq_add_neg, add_comm, Complex.cpow_add _ _ hne, Complex.cpow_one]
    have hpow' : (s : ℂ) ^ (1 - μ - 1) = (s : ℂ) ^ (-μ) := by ring_nf
    have hsp : deqPair ν μ g Ψ t s = ∑ i : Fin 2, ((μ - 1) * Φ i s - (s : ℂ) * D i s) :=
      hsplit s hs'
    have hsum2 : ∑ i : Fin 2, ((μ - 1) * Φ i s - (s : ℂ) * D i s) =
        (μ - 1) * ∑ i : Fin 2, Φ i s - (s : ℂ) * ∑ i : Fin 2, D i s := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have e : f' s = -((s : ℂ) ^ (-μ) * ((μ - 1) * ∑ i : Fin 2, Φ i s - (s : ℂ) * ∑ i : Fin 2, D i s)) := by
      simp only [hf']; rw [hsp, hsum2]
    refine hp.congr_deriv ?_
    rw [e, hpow', hpow]
    ring
  have hint : IntegrableOn f' (Ioi t) :=
    (h2 ν μ c r t hν ht hc hr g hg Ψ hΨ).neg
  obtain ⟨H, hH⟩ := h3 ν c r t hν ht hc hr g hg Ψ hΨ
  have hvan : ∀ s : ℝ, H ≤ s → φ s = 0 := by
    intro s hs
    simp only [hφ, hΦ]
    simp [hH s hs]
  have hlimtop : Tendsto φ atTop (𝓝 0) :=
    tendsto_const_nhds.congr' (by
      filter_upwards [eventually_ge_atTop H] with s hs using (hvan s hs).symm)
  set L : ℂ := (t : ℂ) ^ (1 - μ) * S with hL
  have hlimt : Tendsto φ (𝓝[>] t) (𝓝 L) := by
    have hc1 : Tendsto (fun s : ℝ => (s : ℂ) ^ (1 - μ)) (𝓝[>] t) (𝓝 ((t : ℂ) ^ (1 - μ))) :=
      ((cpow_hasDerivAt (1 - μ) ht).continuousAt.tendsto).mono_left nhdsWithin_le_nhds
    have hc2 : Tendsto (fun s : ℝ => ∑ i : Fin 2, Φ i s) (𝓝[>] t) (𝓝 S) :=
      tendsto_finset_sum _ (fun i _ => hHP ν c r t hν ht hc hr g hg Ψ hΨ i)
    exact hc1.mul hc2
  set φ' : ℝ → ℂ := Function.update φ t L with hφ'
  have hcont : ContinuousWithinAt φ' (Ici t) t := by
    rw [← continuousWithinAt_Ioi_iff_Ici]
    show Tendsto φ' (𝓝[>] t) (𝓝 (φ' t))
    have : φ' t = L := by simp [hφ']
    rw [this]
    refine hlimt.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    have : y ≠ t := ne_of_gt hy
    simp [hφ', Function.update_of_ne this]
  have hder' : ∀ x ∈ Ioi t, HasDerivAt φ' (f' x) x := by
    intro x hx
    refine (hderiv x hx).congr_of_eventuallyEq ?_
    filter_upwards [isOpen_ne.mem_nhds (ne_of_gt (show t < x from hx))] with y hy
    simp [hφ', Function.update_of_ne hy]
  have hlim' : Tendsto φ' atTop (𝓝 0) := by
    refine hlimtop.congr' ?_
    filter_upwards [eventually_gt_atTop t] with y hy
    simp [hφ', Function.update_of_ne (ne_of_gt hy)]
  have hftc := integral_Ioi_of_hasDerivAt_of_tendsto hcont hder' hint hlim'
  have hφt : φ' t = L := by simp [hφ']
  rw [hφt] at hftc
  -- RHS
  have hS' : ∫ z : ℝ × ℝ, ∑ i : Fin 2, g z i * (Ψ (t, z) i : ℂ) = S := by
    rw [hS]
    exact integral_finset_sum _ (fun i _ => h4 c r t g hc hr hg Ψ hΨ i)
  rw [hS']
  have hcp : ∀ s ∈ Ioi t, (((t / s : ℝ) : ℂ) ^ μ) * deqPair ν μ g Ψ t s =
      (t : ℂ) ^ μ * (-(f' s)) := by
    intro s hs
    have hs0 : 0 < s := ht.trans hs
    have h1 : (((t / s : ℝ) : ℂ) ^ μ) = (t : ℂ) ^ μ * (s : ℂ) ^ (-μ) := by
      rw [div_eq_mul_inv, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg ht.le
        (inv_nonneg.2 hs0.le), Complex.ofReal_inv, Complex.inv_cpow, Complex.cpow_neg]
      rw [Complex.arg_ofReal_of_nonneg hs0.le]
      exact Real.pi_pos.ne
    rw [h1]; simp only [hf']; ring
  rw [setIntegral_congr_fun measurableSet_Ioi hcp, integral_const_mul, integral_neg, hftc]
  have htne : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ht.ne'
  rw [hL]
  have : (t : ℂ) ^ μ * (t : ℂ) ^ (1 - μ) = (t : ℂ) := by
    rw [← Complex.cpow_add _ _ htne]; simp
  calc (t : ℂ) ^ μ * -(0 - (t : ℂ) ^ (1 - μ) * S) = ((t : ℂ) ^ μ * (t : ℂ) ^ (1 - μ)) * S := by ring
    _ = (t : ℂ) * S := by rw [this]

end UnforcedLeray.Short.IIb
