import UnforcedLeray.Short.PartIIIa.SeparatedKernels

/-!
# T16 decomposition: `SepYoung` and `SepYoungPointwise` (SP 3611-3647)

The target is split into (A) a pointwise domination of `|D^j W_μ|` by the scalar dilation
integral of the gap-truncated kernel majorant (`sep:resolvent` with `sep:kernel` and the radial gap
`|y - λz| ≥ D`, SP 3611-3623), and (B) the mixed-norm estimates for that scalar dilation integral
(Young with dilation `λ^{-3+3/p}`, Minkowski in `λ`, phase-translation invariance; SP 3624-3646).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

/-- The gap-truncated kernel majorant `1_{|x| ≥ D}|x|^{-4-j}` (SP 3629-3630). -/
def sepKd (j : ℕ) (D : ℝ) (x : Space) : ℝ≥0∞ :=
  if D ≤ ‖x‖ then ENNReal.ofReal (‖x‖ ^ (-4 - (j : ℝ))) else 0

/-- The scalar dilation integral
`∫_0^1 λ^a ∫ 1_{|y-λz|≥D}|y-λz|^{-4-j} g(τ + 2 log λ, z) dz dλ` (SP 3611-3617, 3631-3646). -/
def sepDom (a : ℝ) (j : ℕ) (D : ℝ) (g : ℝ → Space → ℝ≥0∞) (τ : ℝ) (y : Space) : ℝ≥0∞ :=
  ∫⁻ l in Ioo (0 : ℝ) 1, ENNReal.ofReal (l ^ a) *
    ∫⁻ z : Space, sepKd j D (y - l • z) * g (τ + 2 * Real.log l) z

/-- **(A) Pointwise domination** (SP 3604-3623): from `sep:kernel` (`SepKernelBounds`), `sep:resolvent`
(differentiate under the `(λ,z)` integral; `∇K` is a convolution against a source supported in
`|z'| ≤ r_o`) and the gap `|y - λz| ≥ |y'| - λ|z'| ≥ r_i - r_o = D`: for receivers `|y'| ≥ r_i`
at which the order-`0` majorant `∫_0^1 λ^{2Re μ+2} ∫ 1_{≥D}|y-λz|^{-4}|T(z,τ+2log λ)| dz dλ` is
finite, `|D^jW_μ(y,τ)| ≤ C_j ∫_0^1 λ^{2Re μ+2} ∫ 1_{≥D}|y-λz|^{-4-j}|T(z,τ+2log λ)| dz dλ`.
The finiteness hypothesis is the Lean form of "we begin with smooth tensors and then complete in
the norms appearing below" (SP 3594-3595): `sepW` is a Bochner integral, which is `0` by
convention where its integrand is not integrable, so at a receiver with infinite order-`0`
majorant `D^jW_μ` is not controlled by the order-`j` majorant (the signed integrand can still be
integrable there: an isotropic part `aI` of `T` contributes `∑_k ∂_kK_{ik} = 0`).  The consumers
obtain the finiteness for a.e. phase/receiver from `sep:young` at `j = 0` (`SepDomYoung`,
`SepDomPointwise`; see `sepYoung_of`, `sepYoungPointwise_of`). -/
def SepWDominated : Prop :=
  SepKernelBounds → ∀ j : ℕ, ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ ν : ℝ, 0 < ν → ∀ μ : ℂ, -(1 / 4) < μ.re →
    ∀ rOut rIn P : ℝ, 0 ≤ rOut → rOut < rIn → 0 < P →
      ∀ T, IsSepSource P rOut T → ∀ (τ : ℝ) (y : Space), rIn ≤ Real.sqrt (y 0 ^ 2 + y 1 ^ 2) →
        sepDom (2 * μ.re + 2) 0 (rIn - rOut) (srcNorm T) τ y < ⊤ →
        wDerivNorm ν μ T j τ y ≤
          ENNReal.ofReal C0 * sepDom (2 * μ.re + 2) j (rIn - rOut) (srcNorm T) τ y

/-- **(B1) Young with dilation, Minkowski in `λ`, phase invariance** (SP 3624-3646): for `1 ≤ p,b,q`,
`1 + 1/q = 1/p + 1/b`, `δ ≤ a - 2 + 3/p`, `a ≥ 0`: for `P`-periodic jointly measurable `g`,
`‖sepDom a j D g‖_{L²_τL^q_y} ≤ C D^{-4-j+3/b}‖g‖_{L²_τL^p_y}`, `C = C(j,p,q,b,δ)`.
(`‖1_{>D}|x|^{-4-j}‖_{L^b} = C D^{-4-j+3/b}` for `(4+j)b > 3`, Young in `y`, dilation
`λ^{-3+3/p}`, `λ^{a-3+3/p}` integrable on `(0,1)`, Minkowski in `λ`, `τ ↦ τ+2log λ`
preserves the normalised `L²_τ` norm on the period.) -/
def SepDomYoung : Prop :=
  ∀ (j : ℕ) (p q b δ : ℝ), 1 ≤ p → 1 ≤ b → 1 ≤ q → 1 + 1 / q = 1 / p + 1 / b → 0 < δ →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ℝ, 0 ≤ a → δ ≤ a - 2 + 3 / p → ∀ D P : ℝ, 0 < D → 0 < P →
      ∀ g : ℝ → Space → ℝ≥0∞, Measurable (Function.uncurry g) → (∀ τ z, g (τ + P) z = g τ z) →
        ltauLq P q (sepDom a j D g) ≤
          ENNReal.ofReal (C * D ^ (-4 - (j : ℝ) + 3 / b)) * ltauLq P p g

/-- **(B2) Pointwise version** (SP 3647): `q = ∞`, `1/p + 1/b = 1`, Hölder in `z`, then
Minkowski in `λ` and phase invariance: `‖sepDom a j D g (·,y)‖_{L²_τ} ≤ C D^{-4-j+3/b}‖g‖_{L²_τL^p}`. -/
def SepDomPointwise : Prop :=
  ∀ (j : ℕ) (p b δ : ℝ), 1 ≤ p → 1 ≤ b → 1 / p + 1 / b = 1 → 0 < δ →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ℝ, 0 ≤ a → δ ≤ a - 2 + 3 / p → ∀ D P : ℝ, 0 < D → 0 < P →
      ∀ g : ℝ → Space → ℝ≥0∞, Measurable (Function.uncurry g) → (∀ τ z, g (τ + P) z = g τ z) →
        ∀ y : Space, ltauAt P (fun τ => sepDom a j D g τ y) ≤
          ENNReal.ofReal (C * D ^ (-4 - (j : ℝ) + 3 / b)) * ltauLq P p g

/-! ## Homogeneity and monotonicity of the phase norms -/

theorem ltauLq_mono (P q : ℝ) (hq : 0 < q) {f f' : ℝ → Space → ℝ≥0∞}
    (h : ∀ τ y, f τ y ≤ f' τ y) : ltauLq P q f ≤ ltauLq P q f' := by
  unfold ltauLq
  have hq2 : 0 ≤ 2 / q := by positivity
  gcongr with τ y
  exact h τ y

theorem ltauLq_const_mul (P q : ℝ) (hq : 0 < q) (c : ℝ≥0∞) (hc : c ≠ ∞)
    (f : ℝ → Space → ℝ≥0∞) :
    ltauLq P q (fun τ y => c * f τ y) = c * ltauLq P q f := by
  unfold ltauLq
  have h1 : ∀ τ, (∫⁻ y, (c * f τ y) ^ q) ^ (2 / q) = c ^ (2 : ℝ) * (∫⁻ y, f τ y ^ q) ^ (2 / q) := by
    intro τ
    have : ∫⁻ y, (c * f τ y) ^ q = c ^ q * ∫⁻ y, f τ y ^ q := by
      simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hq.le]
      exact lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hq.le hc)
    rw [this, ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul]
    congr 2
    field_simp
  simp_rw [h1]
  rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hc)]
  rw [← mul_assoc, mul_comm _ (c ^ (2 : ℝ)), mul_assoc,
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul]
  norm_num

theorem ltauAt_mono (P : ℝ) {g g' : ℝ → ℝ≥0∞} (h : ∀ τ, g τ ≤ g' τ) :
    ltauAt P g ≤ ltauAt P g' := by
  unfold ltauAt
  gcongr with τ
  exact h τ

theorem ltauAt_const_mul (P : ℝ) (c : ℝ≥0∞) (hc : c ≠ ∞) (g : ℝ → ℝ≥0∞) :
    ltauAt P (fun τ => c * g τ) = c * ltauAt P g := by
  unfold ltauAt
  simp_rw [ENNReal.mul_rpow_of_nonneg _ _ (show (0:ℝ) ≤ 2 by norm_num)]
  rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hc)]
  rw [← mul_assoc, mul_comm _ (c ^ (2 : ℝ)), mul_assoc,
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul]
  norm_num

/-! ## Almost-everywhere finiteness of the order-`0` majorant

`SepWDominated` needs the order-`0` majorant to be finite at the receiver.  When
`‖T‖_{L²_τL^p} < ∞`, `sep:young` at `j = 0` (same `p`, `q`, `b`) makes it finite for a.e. phase and
a.e. receiver (mixed norm) or for a.e. phase (pointwise form); when `‖T‖_{L²_τL^p} = ∞` the
asserted bounds are trivial. -/

theorem sepAE_measurable_srcNorm {P rOut : ℝ} {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ}
    (hT : IsSepSource P rOut T) : Measurable (Function.uncurry (srcNorm T)) := by
  have hTn : Measurable fun p : ℝ × Space => tensorNorm (T p.1 p.2) := by
    unfold tensorNorm
    refine Measurable.sqrt ?_
    refine Finset.measurable_sum _ fun i _ => ?_
    refine Finset.measurable_sum _ fun j _ => ?_
    exact (hT.measurable i j).pow_const 2
  exact ENNReal.measurable_ofReal.comp hTn

/-- Joint measurability of `sepDom a j D g` in `(τ, y)`. -/
theorem sepAE_measurable_sepDom (a : ℝ) (j : ℕ) (D : ℝ) {g : ℝ → Space → ℝ≥0∞}
    (hg : Measurable (Function.uncurry g)) : Measurable (Function.uncurry (sepDom a j D g)) := by
  have hin : Measurable (fun r : ((ℝ × Space) × ℝ) × Space =>
      sepKd j D (r.1.1.2 - r.1.2 • r.2) * g (r.1.1.1 + 2 * Real.log r.1.2) r.2) := by
    refine Measurable.mul ?_ ?_
    · have hk : Measurable (sepKd j D) := by
        unfold sepKd
        refine Measurable.ite ?_ (ENNReal.measurable_ofReal.comp (measurable_norm.pow_const _))
          measurable_const
        exact measurableSet_le measurable_const measurable_norm
      refine hk.comp ?_
      exact (measurable_snd.comp (measurable_fst.comp measurable_fst)).sub
        ((measurable_snd.comp measurable_fst).smul measurable_snd)
    · have : Measurable (fun r : ((ℝ × Space) × ℝ) × Space =>
          (r.1.1.1 + 2 * Real.log r.1.2, r.2)) :=
        ((measurable_fst.comp (measurable_fst.comp measurable_fst)).add (measurable_const.mul
          (Real.measurable_log.comp (measurable_snd.comp measurable_fst)))).prodMk measurable_snd
      exact hg.comp this
  have h1 : Measurable (fun q : (ℝ × Space) × ℝ => ∫⁻ z : Space,
      sepKd j D (q.1.2 - q.2 • z) * g (q.1.1 + 2 * Real.log q.2) z) :=
    Measurable.lintegral_prod_right (f := fun (q : (ℝ × Space) × ℝ) (z : Space) =>
      sepKd j D (q.1.2 - q.2 • z) * g (q.1.1 + 2 * Real.log q.2) z) hin
  have h2 : Measurable (fun q : (ℝ × Space) × ℝ => ENNReal.ofReal (q.2 ^ a) * ∫⁻ z : Space,
      sepKd j D (q.1.2 - q.2 • z) * g (q.1.1 + 2 * Real.log q.2) z) :=
    (ENNReal.measurable_ofReal.comp (measurable_snd.pow_const a)).mul h1
  exact Measurable.lintegral_prod_right (ν := volume.restrict (Ioo (0 : ℝ) 1))
    (f := fun (q : ℝ × Space) (l : ℝ) => ENNReal.ofReal (l ^ a) * ∫⁻ z : Space,
      sepKd j D (q.2 - l • z) * g (q.1 + 2 * Real.log l) z) h2

/-- Monotonicity of `ltauLq` under an a.e. (phase, then receiver) inequality. -/
theorem sepAE_ltauLq_mono (P q : ℝ) (hq : 0 < q) {f f' : ℝ → Space → ℝ≥0∞}
    (h : ∀ᵐ τ ∂(volume.restrict (Ioc 0 P)), ∀ᵐ y, f τ y ≤ f' τ y) :
    ltauLq P q f ≤ ltauLq P q f' := by
  unfold ltauLq
  have hint : ∫⁻ τ in Ioc 0 P, (∫⁻ y, f τ y ^ q) ^ (2 / q) ≤
      ∫⁻ τ in Ioc 0 P, (∫⁻ y, f' τ y ^ q) ^ (2 / q) := by
    refine lintegral_mono_ae ?_
    filter_upwards [h] with τ hτ
    refine ENNReal.rpow_le_rpow (lintegral_mono_ae ?_) (by positivity)
    filter_upwards [hτ] with y hy
    exact ENNReal.rpow_le_rpow hy hq.le
  gcongr

/-- A finite mixed norm forces a.e. finiteness (a.e. phase in `(0,P]`, then a.e. receiver). -/
theorem sepAE_lt_top_of_ltauLq (P q : ℝ) (hq : 0 < q) {f : ℝ → Space → ℝ≥0∞}
    (hf : Measurable (Function.uncurry f)) (h : ltauLq P q f < ⊤) :
    ∀ᵐ τ ∂(volume.restrict (Ioc 0 P)), ∀ᵐ y, f τ y < ⊤ := by
  unfold ltauLq at h
  rw [ENNReal.rpow_lt_top_iff_of_pos (by norm_num)] at h
  have hP' : (ENNReal.ofReal P)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 ENNReal.ofReal_ne_top
  have hI : ∫⁻ τ in Ioc 0 P, (∫⁻ y, f τ y ^ q) ^ (2 / q) ≠ ⊤ := by
    intro htop
    rw [htop, ENNReal.mul_top hP'] at h
    exact lt_irrefl _ h
  have hmq : Measurable (fun τ => ∫⁻ y, f τ y ^ q) :=
    Measurable.lintegral_prod_right (f := fun (τ : ℝ) (y : Space) => f τ y ^ q) (hf.pow_const q)
  filter_upwards [ae_lt_top' (hmq.pow_const (2 / q)).aemeasurable hI] with τ hτ
  rw [ENNReal.rpow_lt_top_iff_of_pos (by positivity)] at hτ
  have hmy : Measurable (fun y => f τ y ^ q) :=
    (hf.comp (measurable_prodMk_left (x := τ))).pow_const q
  filter_upwards [ae_lt_top' hmy.aemeasurable hτ.ne] with y hy
  exact (ENNReal.rpow_lt_top_iff_of_pos hq).1 hy

/-- Monotonicity of `ltauAt` under an a.e. inequality in the phase. -/
theorem sepAE_ltauAt_mono (P : ℝ) {g g' : ℝ → ℝ≥0∞}
    (h : ∀ᵐ τ ∂(volume.restrict (Ioc 0 P)), g τ ≤ g' τ) : ltauAt P g ≤ ltauAt P g' := by
  unfold ltauAt
  have : ∫⁻ τ in Ioc 0 P, g τ ^ (2 : ℝ) ≤ ∫⁻ τ in Ioc 0 P, g' τ ^ (2 : ℝ) :=
    lintegral_mono_ae (by filter_upwards [h] with τ hτ using ENNReal.rpow_le_rpow hτ (by norm_num))
  gcongr

/-- A finite phase norm forces a.e. finiteness in the phase. -/
theorem sepAE_lt_top_of_ltauAt (P : ℝ) {g : ℝ → ℝ≥0∞} (hg : Measurable g) (h : ltauAt P g < ⊤) :
    ∀ᵐ τ ∂(volume.restrict (Ioc 0 P)), g τ < ⊤ := by
  unfold ltauAt at h
  rw [ENNReal.rpow_lt_top_iff_of_pos (by norm_num)] at h
  have hP' : (ENNReal.ofReal P)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 ENNReal.ofReal_ne_top
  have hI : ∫⁻ τ in Ioc 0 P, g τ ^ (2 : ℝ) ≠ ⊤ := by
    intro htop
    rw [htop, ENNReal.mul_top hP'] at h
    exact lt_irrefl _ h
  filter_upwards [ae_lt_top' (hg.pow_const (2 : ℝ)).aemeasurable hI] with τ hτ
  exact (ENNReal.rpow_lt_top_iff_of_pos (by norm_num)).1 hτ

/-- **(A) at order `0` without the finiteness hypothesis**: where the order-`0` majorant is
infinite the bound is trivial (the constant is taken positive). -/
theorem sepWDominated_zero (hA : SepWDominated) (hK : SepKernelBounds) :
    ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ ν : ℝ, 0 < ν → ∀ μ : ℂ, -(1 / 4) < μ.re →
      ∀ rOut rIn P : ℝ, 0 ≤ rOut → rOut < rIn → 0 < P →
        ∀ T, IsSepSource P rOut T → ∀ (τ : ℝ) (y : Space), rIn ≤ Real.sqrt (y 0 ^ 2 + y 1 ^ 2) →
          wDerivNorm ν μ T 0 τ y ≤
            ENNReal.ofReal C0 * sepDom (2 * μ.re + 2) 0 (rIn - rOut) (srcNorm T) τ y := by
  obtain ⟨C0, hC0, hA'⟩ := hA hK 0
  refine ⟨C0 + 1, by linarith, ?_⟩
  intro ν hν μ hμ rOut rIn P hrO hrr hP T hT τ y hy
  by_cases hfin : sepDom (2 * μ.re + 2) 0 (rIn - rOut) (srcNorm T) τ y < ⊤
  · refine (hA' ν hν μ hμ rOut rIn P hrO hrr hP T hT τ y hy hfin).trans ?_
    gcongr
    linarith
  · rw [not_lt_top_iff.1 hfin, ENNReal.mul_top (by simp; linarith)]
    exact le_top

/-- **(A) on a phase slice, a.e. in the receiver**: at a phase `τ` where the order-`0` majorant
has finite `L^q_y` integral (`q > 0`), the domination holds for a.e. receiver (for phase-by-phase
consumers, which obtain the finiteness from a slice form of `sep:young` at order `0`). -/
theorem sepWDominated_slice_ae (hA : SepWDominated) (hK : SepKernelBounds) (j : ℕ) :
    ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ ν : ℝ, 0 < ν → ∀ μ : ℂ, -(1 / 4) < μ.re →
      ∀ rOut rIn P : ℝ, 0 ≤ rOut → rOut < rIn → 0 < P →
        ∀ T, IsSepSource P rOut T → ∀ (τ q : ℝ), 0 < q →
          (∫⁻ y, sepDom (2 * μ.re + 2) 0 (rIn - rOut) (srcNorm T) τ y ^ q) ≠ ⊤ →
          ∀ᵐ y, youngDerivNorm ν μ T j rIn τ y ≤
            ENNReal.ofReal C0 * sepDom (2 * μ.re + 2) j (rIn - rOut) (srcNorm T) τ y := by
  obtain ⟨C0, hC0, hA'⟩ := hA hK j
  refine ⟨C0, hC0, ?_⟩
  intro ν hν μ hμ rOut rIn P hrO hrr hP T hT τ q hq hI
  have hm : Measurable (fun y => sepDom (2 * μ.re + 2) 0 (rIn - rOut) (srcNorm T) τ y ^ q) :=
    ((sepAE_measurable_sepDom (2 * μ.re + 2) 0 (rIn - rOut)
      (sepAE_measurable_srcNorm hT)).of_uncurry_left).pow_const q
  filter_upwards [ae_lt_top' hm.aemeasurable hI] with y hy
  unfold youngDerivNorm
  split_ifs with h
  · exact hA' ν hν μ hμ rOut rIn P hrO hrr hP T hT τ y h
      ((ENNReal.rpow_lt_top_iff_of_pos hq).1 hy)
  · exact bot_le

/-- `SepYoung` from (A) and (B1) (B1 is used at order `j` and, for the finiteness of the
order-`0` majorant, at order `0`). -/
theorem sepYoung_of (hA : SepWDominated) (hK : SepKernelBounds) (hB : SepDomYoung) : SepYoung := by
  intro K hKc hKre j p q b hp hb hq hrel hδ
  obtain ⟨δ, hδ0, hδK⟩ := hδ
  obtain ⟨C0, hC0, hA'⟩ := hA hK j
  obtain ⟨Cb, hCb, hB'⟩ := hB j p q b δ hp hb hq hrel hδ0
  obtain ⟨Cz, hCz, hBz⟩ := hB 0 p q b δ hp hb hq hrel hδ0
  refine ⟨C0 * Cb + 1, by positivity, ?_⟩
  intro ν hν μ hμ rOut rIn P hrO hrr hP T hT
  have hμre := hKre μ hμ
  have hD : 0 < rIn - rOut := by linarith
  have ha : 0 ≤ 2 * μ.re + 2 := by linarith
  have hδ' : δ ≤ (2 * μ.re + 2) - 2 + 3 / p := by have := hδK μ hμ; linarith
  have hgm : Measurable (Function.uncurry (srcNorm T)) := sepAE_measurable_srcNorm hT
  have hper : ∀ τ z, srcNorm T (τ + P) z = srcNorm T τ z := by
    intro τ z; unfold srcNorm; rw [hT.periodic]
  have hq0 : 0 < q := by linarith
  have hDr : 0 ≤ (rIn - rOut) ^ (-4 - (j : ℝ) + 3 / b) := Real.rpow_nonneg hD.le _
  have hpos : 0 < (C0 * Cb + 1) * (rIn - rOut) ^ (-4 - (j : ℝ) + 3 / b) :=
    mul_pos (by positivity) (Real.rpow_pos_of_pos hD _)
  by_cases htop : ltauLq P p (srcNorm T) = ⊤
  · rw [htop, ENNReal.mul_top (ENNReal.ofReal_pos.2 hpos).ne']
    exact le_top
  have h0 : ltauLq P q (sepDom (2 * μ.re + 2) 0 (rIn - rOut) (srcNorm T)) < ⊤ :=
    (hBz _ ha hδ' _ P hD hP _ hgm hper).trans_lt
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_top_iff_ne_top.2 htop))
  have hae := sepAE_lt_top_of_ltauLq P q hq0 (sepAE_measurable_sepDom _ 0 _ hgm) h0
  calc ltauLq P q (youngDerivNorm ν μ T j rIn)
      ≤ ltauLq P q (fun τ y => ENNReal.ofReal C0 *
          sepDom (2 * μ.re + 2) j (rIn - rOut) (srcNorm T) τ y) := by
        refine sepAE_ltauLq_mono P q hq0 ?_
        filter_upwards [hae] with τ hτ
        filter_upwards [hτ] with y hy
        unfold youngDerivNorm
        split_ifs with h
        · exact hA' ν hν μ hμre rOut rIn P hrO hrr hP T hT τ y h hy
        · exact bot_le
    _ = ENNReal.ofReal C0 * ltauLq P q (sepDom (2 * μ.re + 2) j (rIn - rOut) (srcNorm T)) :=
        ltauLq_const_mul P q hq0 _ ENNReal.ofReal_ne_top _
    _ ≤ ENNReal.ofReal C0 * (ENNReal.ofReal (Cb * (rIn - rOut) ^ (-4 - (j : ℝ) + 3 / b)) *
          ltauLq P p (srcNorm T)) := by
        gcongr
        exact hB' _ ha hδ' _ P hD hP _ hgm hper
    _ = ENNReal.ofReal (C0 * Cb * (rIn - rOut) ^ (-4 - (j : ℝ) + 3 / b)) *
          ltauLq P p (srcNorm T) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hC0, mul_assoc]
    _ ≤ ENNReal.ofReal ((C0 * Cb + 1) * (rIn - rOut) ^ (-4 - (j : ℝ) + 3 / b)) *
          ltauLq P p (srcNorm T) := by
        gcongr
        linarith

/-- `SepYoungPointwise` from (A) and (B2) (B2 is used at order `j` and, for the finiteness of the
order-`0` majorant, at order `0`). -/
theorem sepYoungPointwise_of (hA : SepWDominated) (hK : SepKernelBounds) (hB : SepDomPointwise) :
    SepYoungPointwise := by
  intro K hKc hKre j p b hp hb hrel hδ
  obtain ⟨δ, hδ0, hδK⟩ := hδ
  obtain ⟨C0, hC0, hA'⟩ := hA hK j
  obtain ⟨Cb, hCb, hB'⟩ := hB j p b δ hp hb hrel hδ0
  obtain ⟨Cz, hCz, hBz⟩ := hB 0 p b δ hp hb hrel hδ0
  refine ⟨C0 * Cb + 1, by positivity, ?_⟩
  intro ν hν μ hμ rOut rIn P hrO hrr hP T hT y hy
  have hμre := hKre μ hμ
  have hD : 0 < rIn - rOut := by linarith
  have ha : 0 ≤ 2 * μ.re + 2 := by linarith
  have hδ' : δ ≤ (2 * μ.re + 2) - 2 + 3 / p := by have := hδK μ hμ; linarith
  have hgm : Measurable (Function.uncurry (srcNorm T)) := sepAE_measurable_srcNorm hT
  have hper : ∀ τ z, srcNorm T (τ + P) z = srcNorm T τ z := by
    intro τ z; unfold srcNorm; rw [hT.periodic]
  have hDr : 0 ≤ (rIn - rOut) ^ (-4 - (j : ℝ) + 3 / b) := Real.rpow_nonneg hD.le _
  have hpos : 0 < (C0 * Cb + 1) * (rIn - rOut) ^ (-4 - (j : ℝ) + 3 / b) :=
    mul_pos (by positivity) (Real.rpow_pos_of_pos hD _)
  by_cases htop : ltauLq P p (srcNorm T) = ⊤
  · rw [htop, ENNReal.mul_top (ENNReal.ofReal_pos.2 hpos).ne']
    exact le_top
  have h0 : ltauAt P (fun τ => sepDom (2 * μ.re + 2) 0 (rIn - rOut) (srcNorm T) τ y) < ⊤ :=
    (hBz _ ha hδ' _ P hD hP _ hgm hper y).trans_lt
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_top_iff_ne_top.2 htop))
  have hmτ : Measurable (fun τ => sepDom (2 * μ.re + 2) 0 (rIn - rOut) (srcNorm T) τ y) :=
    (sepAE_measurable_sepDom (2 * μ.re + 2) 0 (rIn - rOut) hgm).of_uncurry_right
  have hae := sepAE_lt_top_of_ltauAt P hmτ h0
  calc ltauAt P (fun τ => wDerivNorm ν μ T j τ y)
      ≤ ltauAt P (fun τ => ENNReal.ofReal C0 *
          sepDom (2 * μ.re + 2) j (rIn - rOut) (srcNorm T) τ y) := by
        refine sepAE_ltauAt_mono P ?_
        filter_upwards [hae] with τ hτ
        exact hA' ν hν μ hμre rOut rIn P hrO hrr hP T hT τ y hy hτ
    _ = ENNReal.ofReal C0 * ltauAt P (fun τ => sepDom (2 * μ.re + 2) j (rIn - rOut) (srcNorm T) τ y) :=
        ltauAt_const_mul P _ ENNReal.ofReal_ne_top _
    _ ≤ ENNReal.ofReal C0 * (ENNReal.ofReal (Cb * (rIn - rOut) ^ (-4 - (j : ℝ) + 3 / b)) *
          ltauLq P p (srcNorm T)) := by
        gcongr
        exact hB' _ ha hδ' _ P hD hP _ hgm hper y
    _ = ENNReal.ofReal (C0 * Cb * (rIn - rOut) ^ (-4 - (j : ℝ) + 3 / b)) *
          ltauLq P p (srcNorm T) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hC0, mul_assoc]
    _ ≤ ENNReal.ofReal ((C0 * Cb + 1) * (rIn - rOut) ^ (-4 - (j : ℝ) + 3 / b)) *
          ltauLq P p (srcNorm T) := by
        gcongr
        linarith

end UnforcedLeray.Short.IIIa

end
