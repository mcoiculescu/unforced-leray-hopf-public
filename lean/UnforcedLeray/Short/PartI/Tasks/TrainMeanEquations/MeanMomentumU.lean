import UnforcedLeray.Short.PartI.Sub.T01

/-!
# Part I, task `PartI:T01`, leaf `TrainMeanMomentumU`: the averaged first momentum equation

Source of record: `the November 2 reference manuscript`, lines 397-404 (average the
first component of the momentum equation over one period in `q`).

Proof. For `s > 0` the first component of `∂_s v + v·∇v - νΔv + ∇p = 0` at `(q, η)` reads
`∂_s v₁ + v₁∂_q v₁ + v₂∂_η v₁ - ν(∂_q²v₁ + ∂_η²v₁) + ∂_q p = 0`. Using `div v = 0` the advection
term equals `∂_q(v₁²) + ∂_η(v₁v₂)` minus `v₁ div v`. Averaging over `q ∈ (-c/2, c/2]`: the
`∂_q`-terms integrate to zero by periodicity (fundamental theorem of calculus), and the averages of
`∂_s v₁`, `∂_η(v₁v₂)`, `∂_η²v₁` are the derivatives of the averages (differentiation under the
integral sign over the compact interval).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane partialQ partialEta)

/-! ### Partial derivatives as Fréchet derivatives -/

theorem mm_hasDerivAt_fst {G : Plane → ℝ} {x q : ℝ} (hG : DifferentiableAt ℝ G (x, q)) :
    HasDerivAt (fun y => G (y, q)) (fderiv ℝ G (x, q) (1, 0)) x := by
  have hpath : HasDerivAt (fun y : ℝ => ((y, q) : Plane)) ((1, 0) : ℝ × ℝ) x :=
    (hasDerivAt_id x).prodMk (hasDerivAt_const x q)
  exact hG.hasFDerivAt.comp_hasDerivAt x hpath

theorem mm_hasDerivAt_snd {G : Plane → ℝ} {x q : ℝ} (hG : DifferentiableAt ℝ G (x, q)) :
    HasDerivAt (fun y => G (x, y)) (fderiv ℝ G (x, q) (0, 1)) q := by
  have hpath : HasDerivAt (fun y : ℝ => ((x, y) : Plane)) ((0, 1) : ℝ × ℝ) q :=
    (hasDerivAt_const q x).prodMk (hasDerivAt_id q)
  exact hG.hasFDerivAt.comp_hasDerivAt q hpath

theorem mm_partialQ_eq {g : Plane → ℝ} {z : Plane} (hg : DifferentiableAt ℝ g z) :
    partialQ g z = fderiv ℝ g z (1, 0) := by
  obtain ⟨x, q⟩ := z
  exact (mm_hasDerivAt_fst hg).deriv

theorem mm_partialEta_eq {g : Plane → ℝ} {z : Plane} (hg : DifferentiableAt ℝ g z) :
    partialEta g z = fderiv ℝ g z (0, 1) := by
  obtain ⟨x, q⟩ := z
  exact (mm_hasDerivAt_snd hg).deriv

theorem mm_diff_snd {G : Plane → ℝ} (hG : Differentiable ℝ G) (q y : ℝ) :
    DifferentiableAt ℝ (fun y' => G (q, y')) y :=
  (hG (q, y)).comp y ((differentiableAt_const q).prodMk differentiableAt_id)

theorem mm_partialQ_contDiff {g : Plane → ℝ} (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (partialQ g) := by
  have hd : Differentiable ℝ g := hg.differentiable (by simp)
  have heq : partialQ g = fun z => fderiv ℝ g z (1, 0) :=
    funext fun z => mm_partialQ_eq (hd z)
  rw [heq]
  exact (hg.fderiv_right (by simp)).clm_apply contDiff_const

theorem mm_cont_partialQ_slice {g : Plane → ℝ} (hg : ContDiff ℝ ∞ g) (η : ℝ) :
    Continuous (fun q : ℝ => partialQ g (q, η)) :=
  (mm_partialQ_contDiff hg).continuous.comp (continuous_id.prodMk continuous_const)

/-- The slice `z ↦ F (s, z)` of a function that is `C^∞` on `(0, ∞) × ℝ²` is `C^∞`. -/
theorem mm_slice {F : ℝ → Plane → ℝ} {s : ℝ}
    (hF : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => F x.1 x.2) (Ioi 0 ×ˢ univ)) (hs : 0 < s) :
    ContDiff ℝ ∞ (fun z : Plane => F s z) := by
  have hc : ContDiff ℝ ∞ (fun z : Plane => ((s, z) : ℝ × Plane)) :=
    contDiff_const.prodMk contDiff_id
  have hmaps : MapsTo (fun z : Plane => ((s, z) : ℝ × Plane)) univ (Ioi 0 ×ˢ univ) :=
    fun z _ => ⟨hs, mem_univ z⟩
  exact contDiffOn_univ.1 (hF.comp hc.contDiffOn hmaps)

theorem mm_partialQ_mul {f g : Plane → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (z : Plane) :
    partialQ (fun w => f w * g w) z = f z * partialQ g z + partialQ f z * g z := by
  obtain ⟨x, η⟩ := z
  have hf' : DifferentiableAt ℝ (fun y => f (y, η)) x :=
    (hf (x, η)).comp x ((differentiableAt_id).prodMk (differentiableAt_const η))
  have hg' : DifferentiableAt ℝ (fun y => g (y, η)) x :=
    (hg (x, η)).comp x ((differentiableAt_id).prodMk (differentiableAt_const η))
  show deriv (fun y => f (y, η) * g (y, η)) x
      = f (x, η) * deriv (fun y => g (y, η)) x + deriv (fun y => f (y, η)) x * g (x, η)
  rw [deriv_fun_mul hf' hg']
  ring

theorem mm_partialEta_mul {f g : Plane → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (z : Plane) :
    partialEta (fun w => f w * g w) z = f z * partialEta g z + partialEta f z * g z := by
  obtain ⟨x, η⟩ := z
  have hf' : DifferentiableAt ℝ (fun y => f (x, y)) η := mm_diff_snd hf x η
  have hg' : DifferentiableAt ℝ (fun y => g (x, y)) η := mm_diff_snd hg x η
  show deriv (fun y => f (x, y) * g (x, y)) η
      = f (x, η) * deriv (fun y => g (x, y)) η + deriv (fun y => f (x, y)) η * g (x, η)
  rw [deriv_fun_mul hf' hg']
  ring

theorem mm_deriv_proj (f : ℝ → EuclideanSpace ℝ (Fin 2)) (s : ℝ) (hf : DifferentiableAt ℝ f s) :
    deriv (fun t => f t 0) s = deriv f s 0 := by
  have h := ((EuclideanSpace.proj (0 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).hasFDerivAt).comp_hasDerivAt
    s hf.hasDerivAt
  exact h.deriv

/-! ### Periodic `q`-averages vanish -/

/-- The `q`-average over one period of `∂_q g` vanishes for a `c`-periodic `C^∞` function `g`. -/
theorem mm_integral_partialQ_zero {c : ℝ} {g : Plane → ℝ} (hc : 0 < c) (hg : ContDiff ℝ ∞ g)
    (hper : UnforcedLeray.Cyl.IsPeriodic c g) (η : ℝ) :
    ∫ q in Ioc (-c / 2) (c / 2), partialQ g (q, η) = 0 := by
  have hd : Differentiable ℝ g := hg.differentiable (by simp)
  have hftc : ∫ q in (-c / 2)..(c / 2), partialQ g (q, η) = g (c / 2, η) - g (-c / 2, η) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun q => g (q, η))
    · intro x _
      exact (mm_hasDerivAt_fst (hd (x, η))).congr_deriv (mm_partialQ_eq (hd (x, η))).symm
    · exact (mm_cont_partialQ_slice hg η).intervalIntegrable _ _
  rw [intervalIntegral.integral_of_le (show -c / 2 ≤ c / 2 by linarith)] at hftc
  rw [hftc, hper.neg_half η, sub_self]

/-! ### Differentiation under the `q`-average -/

/-- Differentiation under the `q`-average over `Ioc a b` of a function `H (x, q)` that is `C^∞`
on the open strip `Ioo l r × ℝ` in the parameter `x`. The integrability of the derivative is also
returned. -/
theorem mm_hasDerivAt_avg {H : ℝ × ℝ → ℝ} {l r : ℝ} (a b x0 : ℝ)
    (hH : ContDiffOn ℝ ∞ H (Ioo l r ×ˢ (univ : Set ℝ))) (hx0 : x0 ∈ Ioo l r) :
    IntegrableOn (fun q => deriv (fun y => H (y, q)) x0) (Ioc a b) ∧
      HasDerivAt (fun x => ∫ q in Ioc a b, H (x, q))
        (∫ q in Ioc a b, deriv (fun y => H (y, q)) x0) x0 := by
  have hUo : IsOpen (Ioo l r ×ˢ (univ : Set ℝ)) := isOpen_Ioo.prod isOpen_univ
  have hdiff : ∀ x ∈ Ioo l r, ∀ q : ℝ, DifferentiableAt ℝ H (x, q) := fun x hx q =>
    (hH.contDiffAt (hUo.mem_nhds ⟨hx, mem_univ q⟩)).differentiableAt (by simp)
  have hfd : ContinuousOn (fderiv ℝ H) (Ioo l r ×ˢ (univ : Set ℝ)) :=
    hH.continuousOn_fderiv_of_isOpen hUo (by simp)
  have hφ : ContinuousOn (fun p : ℝ × ℝ => fderiv ℝ H p (1, 0)) (Ioo l r ×ˢ (univ : Set ℝ)) :=
    (ContinuousLinearMap.apply ℝ ℝ ((1, 0) : ℝ × ℝ)).continuous.comp_continuousOn hfd
  have hcontq : ∀ x ∈ Ioo l r, Continuous (fun q => H (x, q)) := by
    intro x hx
    have h1 : ContinuousOn (fun q : ℝ => (x, q)) univ :=
      (continuous_const.prodMk continuous_id).continuousOn
    have h2 : MapsTo (fun q : ℝ => (x, q)) univ (Ioo l r ×ˢ (univ : Set ℝ)) :=
      fun q _ => ⟨hx, mem_univ q⟩
    exact continuousOn_univ.1 (hH.continuousOn.comp h1 h2)
  have hcontF : ∀ x ∈ Ioo l r, Continuous (fun q => fderiv ℝ H (x, q) (1, 0)) := by
    intro x hx
    have h1 : ContinuousOn (fun q : ℝ => (x, q)) univ :=
      (continuous_const.prodMk continuous_id).continuousOn
    have h2 : MapsTo (fun q : ℝ => (x, q)) univ (Ioo l r ×ˢ (univ : Set ℝ)) :=
      fun q _ => ⟨hx, mem_univ q⟩
    exact continuousOn_univ.1 (hφ.comp h1 h2)
  obtain ⟨δ, hδpos, hδl, hδr⟩ : ∃ δ : ℝ, 0 < δ ∧ l < x0 - δ ∧ x0 + δ < r := by
    have h1 := min_le_left (x0 - l) (r - x0)
    have h2 := min_le_right (x0 - l) (r - x0)
    have h3 : 0 < min (x0 - l) (r - x0) := lt_min (by linarith [hx0.1]) (by linarith [hx0.2])
    exact ⟨min (x0 - l) (r - x0) / 2, by linarith, by linarith, by linarith⟩
  have hKc : IsCompact (Icc (x0 - δ) (x0 + δ) ×ˢ Icc a b) := isCompact_Icc.prod isCompact_Icc
  have hKU : Icc (x0 - δ) (x0 + δ) ×ˢ Icc a b ⊆ Ioo l r ×ˢ (univ : Set ℝ) := by
    intro p hp
    exact ⟨⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩, mem_univ _⟩
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn (hφ.mono hKU)
  have hnhds : Ioo (x0 - δ) (x0 + δ) ∈ 𝓝 x0 := Ioo_mem_nhds (by linarith) (by linarith)
  have hmeas : ∀ᶠ x in 𝓝 x0, AEStronglyMeasurable (fun q => H (x, q))
      (volume.restrict (Ioc a b)) :=
    Filter.eventually_of_mem (Ioo_mem_nhds hx0.1 hx0.2) fun x hx =>
      (hcontq x hx).aestronglyMeasurable
  have hint : Integrable (fun q => H (x0, q)) (volume.restrict (Ioc a b)) :=
    ((hcontq x0 hx0).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hF'meas : AEStronglyMeasurable (fun q => fderiv ℝ H (x0, q) (1, 0))
      (volume.restrict (Ioc a b)) :=
    (hcontF x0 hx0).aestronglyMeasurable
  have hbound : ∀ᵐ q ∂(volume.restrict (Ioc a b)), ∀ x ∈ Ioo (x0 - δ) (x0 + δ),
      ‖fderiv ℝ H (x, q) (1, 0)‖ ≤ (fun _ : ℝ => C) q := by
    refine (ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun q hq x hx => ?_)
    exact hC (x, q) ⟨⟨hx.1.le, hx.2.le⟩, Ioc_subset_Icc_self hq⟩
  have hbint : Integrable (fun _ : ℝ => C) (volume.restrict (Ioc a b)) := integrable_const C
  have hdiffs : ∀ᵐ q ∂(volume.restrict (Ioc a b)), ∀ x ∈ Ioo (x0 - δ) (x0 + δ),
      HasDerivAt (fun y => H (y, q)) (fderiv ℝ H (x, q) (1, 0)) x := by
    refine (ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun q _ x hx => ?_)
    exact mm_hasDerivAt_fst (hdiff x ⟨by linarith [hx.1], by linarith [hx.2]⟩ q)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioc a b))
    (F := fun x q => H (x, q)) (F' := fun x q => fderiv ℝ H (x, q) (1, 0))
    (bound := fun _ : ℝ => C) hnhds hmeas hint hF'meas hbound hbint hdiffs
  have hderEq : (fun q => deriv (fun y => H (y, q)) x0) = fun q => fderiv ℝ H (x0, q) (1, 0) :=
    funext fun q => (mm_hasDerivAt_fst (hdiff x0 hx0 q)).deriv
  rw [hderEq]
  exact ⟨key.1, key.2⟩

/-! ### The core averaged identity -/

/-- The averaged first momentum equation for a smooth `c`-periodic solution with divergence
free velocity, at a fixed age `s > 0`. -/
theorem mm_core {ν c : ℝ} (hc : 0 < c) (v1 v2 p : ℝ → Plane → ℝ)
    (hv1 : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => v1 x.1 x.2) (Ioi 0 ×ˢ univ))
    (hv2 : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => v2 x.1 x.2) (Ioi 0 ×ˢ univ))
    (hp : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => p x.1 x.2) (Ioi 0 ×ˢ univ))
    (hperv : ∀ s : ℝ, 0 < s → UnforcedLeray.Cyl.IsPeriodic c (v1 s))
    (hperp : ∀ s : ℝ, 0 < s → UnforcedLeray.Cyl.IsPeriodic c (p s))
    (hdiv : ∀ s : ℝ, 0 < s → ∀ z : Plane, partialQ (v1 s) z + partialEta (v2 s) z = 0)
    (hmom : ∀ s : ℝ, 0 < s → ∀ z : Plane,
      deriv (fun t => v1 t z) s + (v1 s z * partialQ (v1 s) z + v2 s z * partialEta (v1 s) z)
        - ν * (partialQ (partialQ (v1 s)) z + partialEta (partialEta (v1 s)) z)
        + partialQ (p s) z = 0)
    {s : ℝ} (hs : 0 < s) (η : ℝ) :
    deriv (fun r => hmean c (v1 r) η) s + deriv (fun e => hmean c (fun z => v1 s z * v2 s z) e) η
      = ν * deriv (deriv (fun e => hmean c (v1 s) e)) η := by
  -- smoothness of the slices at the fixed age `s`
  have hS1 : ContDiff ℝ ∞ (fun z : Plane => v1 s z) := mm_slice (F := v1) hv1 hs
  have hS2 : ContDiff ℝ ∞ (fun z : Plane => v2 s z) := mm_slice (F := v2) hv2 hs
  have hSP : ContDiff ℝ ∞ (fun z : Plane => p s z) := mm_slice (F := p) hp hs
  have hD1 : Differentiable ℝ (v1 s) := hS1.differentiable (by simp)
  have hD2 : Differentiable ℝ (v2 s) := hS2.differentiable (by simp)
  have hS1Q : ContDiff ℝ ∞ (partialQ (v1 s)) := mm_partialQ_contDiff hS1
  have hSsq : ContDiff ℝ ∞ (fun w : Plane => v1 s w * v1 s w) := hS1.mul hS1
  -- periodicity
  have hper1 : UnforcedLeray.Cyl.IsPeriodic c (v1 s) := hperv s hs
  have hpsq : UnforcedLeray.Cyl.IsPeriodic c (fun w : Plane => v1 s w * v1 s w) :=
    fun z => by
      show v1 s (z.1 + c, z.2) * v1 s (z.1 + c, z.2) = v1 s z * v1 s z
      rw [hper1 z]
  have hpd1 : UnforcedLeray.Cyl.IsPeriodic c (partialQ (v1 s)) := hper1.partialQ
  -- the `q`-averages of the `∂_q`-terms vanish
  have hX : ∫ q in Ioc (-c / 2) (c / 2), partialQ (fun w : Plane => v1 s w * v1 s w) (q, η) = 0 :=
    mm_integral_partialQ_zero hc hSsq hpsq η
  have hP : ∫ q in Ioc (-c / 2) (c / 2), partialQ (p s) (q, η) = 0 :=
    mm_integral_partialQ_zero hc hSP (hperp s hs) η
  have hD : ∫ q in Ioc (-c / 2) (c / 2), partialQ (partialQ (v1 s)) (q, η) = 0 :=
    mm_integral_partialQ_zero hc hS1Q hpd1 η
  have iX : IntegrableOn (fun q => partialQ (fun w : Plane => v1 s w * v1 s w) (q, η))
      (Ioc (-c / 2) (c / 2)) :=
    ((mm_cont_partialQ_slice hSsq η).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have iP : IntegrableOn (fun q => partialQ (p s) (q, η)) (Ioc (-c / 2) (c / 2)) :=
    ((mm_cont_partialQ_slice hSP η).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have iD : IntegrableOn (fun q => partialQ (partialQ (v1 s)) (q, η)) (Ioc (-c / 2) (c / 2)) :=
    ((mm_cont_partialQ_slice hS1Q η).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  -- the `s`-derivative of the first average
  have hK1 : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => v1 x.1 (x.2, η))
      (Ioo 0 (s + 1) ×ˢ (univ : Set ℝ)) := by
    have hφ : ContDiff ℝ ∞ (fun x : ℝ × ℝ => ((x.1, (x.2, η)) : ℝ × Plane)) :=
      contDiff_fst.prodMk (contDiff_snd.prodMk contDiff_const)
    have hmaps : MapsTo (fun x : ℝ × ℝ => ((x.1, (x.2, η)) : ℝ × Plane))
        (Ioo 0 (s + 1) ×ˢ (univ : Set ℝ)) (Ioi 0 ×ˢ (univ : Set Plane)) :=
      fun x hx => ⟨hx.1.1, mem_univ _⟩
    exact hv1.comp hφ.contDiffOn hmaps
  obtain ⟨iA, hA⟩ := mm_hasDerivAt_avg (-c / 2) (c / 2) s hK1 ⟨hs, by linarith⟩
  have iA' : IntegrableOn (fun q => deriv (fun y => v1 y (q, η)) s) (Ioc (-c / 2) (c / 2)) := iA
  have hA' : HasDerivAt (fun r => hmean c (v1 r) η)
      (c⁻¹ • ∫ q in Ioc (-c / 2) (c / 2), deriv (fun y => v1 y (q, η)) s) s := hA.const_smul c⁻¹
  -- the `η`-derivative of the mean stress
  have hK2 : ContDiff ℝ ∞ (fun x : ℝ × ℝ => v1 s (x.2, x.1) * v2 s (x.2, x.1)) :=
    (hS1.mul hS2).comp (contDiff_snd.prodMk contDiff_fst)
  obtain ⟨iB, hB⟩ := mm_hasDerivAt_avg (l := η - 1) (r := η + 1) (-c / 2) (c / 2) η
    hK2.contDiffOn ⟨by linarith, by linarith⟩
  have iB' : IntegrableOn (fun q => deriv (fun y => v1 s (q, y) * v2 s (q, y)) η)
      (Ioc (-c / 2) (c / 2)) := iB
  have hB' : HasDerivAt (fun e => hmean c (fun z => v1 s z * v2 s z) e)
      (c⁻¹ • ∫ q in Ioc (-c / 2) (c / 2), deriv (fun y => v1 s (q, y) * v2 s (q, y)) η) η :=
    hB.const_smul c⁻¹
  -- the `η`-derivative of the mean, and its second derivative
  have hK3 : ContDiff ℝ ∞ (fun x : ℝ × ℝ => v1 s (x.2, x.1)) :=
    hS1.comp (contDiff_snd.prodMk contDiff_fst)
  have hF : ∀ e : ℝ, HasDerivAt (fun e' => hmean c (v1 s) e')
      (c⁻¹ • ∫ q in Ioc (-c / 2) (c / 2), deriv (fun y => v1 s (q, y)) e) e := by
    intro e
    obtain ⟨_, h⟩ := mm_hasDerivAt_avg (l := e - 1) (r := e + 1) (-c / 2) (c / 2) e
      hK3.contDiffOn ⟨by linarith, by linarith⟩
    exact h.const_smul c⁻¹
  have hfun : deriv (fun e' => hmean c (v1 s) e') =
      fun e => c⁻¹ • ∫ q in Ioc (-c / 2) (c / 2), deriv (fun y => v1 s (q, y)) e :=
    funext fun e => (hF e).deriv
  have hK4 : ContDiff ℝ ∞ (fun x : ℝ × ℝ => deriv (fun y => v1 s (x.2, y)) x.1) := by
    have heq : (fun x : ℝ × ℝ => deriv (fun y => v1 s (x.2, y)) x.1) =
        fun x : ℝ × ℝ => fderiv ℝ (v1 s) (x.2, x.1) (0, 1) :=
      funext fun x => (mm_hasDerivAt_snd (hD1 (x.2, x.1))).deriv
    rw [heq]
    exact ((hS1.fderiv_right (by simp)).comp (contDiff_snd.prodMk contDiff_fst)).clm_apply
      contDiff_const
  obtain ⟨iC, hC'⟩ := mm_hasDerivAt_avg (l := η - 1) (r := η + 1) (-c / 2) (c / 2) η
    hK4.contDiffOn ⟨by linarith, by linarith⟩
  have iC' : IntegrableOn (fun q => deriv (fun y => deriv (fun y' => v1 s (q, y')) y) η)
      (Ioc (-c / 2) (c / 2)) := iC
  have hT3 : deriv (deriv (fun e => hmean c (v1 s) e)) η
      = c⁻¹ • ∫ q in Ioc (-c / 2) (c / 2), deriv (fun y => deriv (fun y' => v1 s (q, y')) y) η := by
    rw [hfun]
    exact (hC'.const_smul c⁻¹).deriv
  -- the pointwise identity, with `div v = 0` and the momentum equation
  have hpt : ∀ q : ℝ,
      deriv (fun y => v1 y (q, η)) s + deriv (fun y => v1 s (q, y) * v2 s (q, y)) η
        - ν * deriv (fun y => deriv (fun y' => v1 s (q, y')) y) η
      = -(partialQ (fun w : Plane => v1 s w * v1 s w) (q, η)) - partialQ (p s) (q, η)
        + ν * partialQ (partialQ (v1 s)) (q, η) := by
    intro q
    have hmq := hmom s hs (q, η)
    have hdq := hdiv s hs (q, η)
    have hB0 : deriv (fun y => v1 s (q, y) * v2 s (q, y)) η
        = v1 s (q, η) * partialEta (v2 s) (q, η) + partialEta (v1 s) (q, η) * v2 s (q, η) :=
      mm_partialEta_mul (f := v1 s) (g := v2 s) hD1 hD2 (q, η)
    have hX0 : partialQ (fun w : Plane => v1 s w * v1 s w) (q, η)
        = v1 s (q, η) * partialQ (v1 s) (q, η) + partialQ (v1 s) (q, η) * v1 s (q, η) :=
      mm_partialQ_mul (f := v1 s) (g := v1 s) hD1 hD1 (q, η)
    have hC0 : deriv (fun y => deriv (fun y' => v1 s (q, y')) y) η
        = partialEta (partialEta (v1 s)) (q, η) := rfl
    linear_combination hmq - ν * hC0 + hB0 + hX0 + (v1 s (q, η)) * hdq
  -- integrate the pointwise identity over one period
  have hAB : Integrable (fun q => deriv (fun y => v1 y (q, η)) s
      + deriv (fun y => v1 s (q, y) * v2 s (q, y)) η) (volume.restrict (Ioc (-c / 2) (c / 2))) :=
    iA'.add iB'
  have hCν : Integrable (fun q => ν * deriv (fun y => deriv (fun y' => v1 s (q, y')) y) η)
      (volume.restrict (Ioc (-c / 2) (c / 2))) :=
    iC'.const_mul ν
  have hXPD : Integrable (fun q => -(partialQ (fun w : Plane => v1 s w * v1 s w) (q, η))
      - partialQ (p s) (q, η)) (volume.restrict (Ioc (-c / 2) (c / 2))) :=
    iX.neg.sub iP
  have hνD : Integrable (fun q => ν * partialQ (partialQ (v1 s)) (q, η))
      (volume.restrict (Ioc (-c / 2) (c / 2))) :=
    iD.const_mul ν
  have hsum : (∫ q in Ioc (-c / 2) (c / 2), deriv (fun y => v1 y (q, η)) s)
      + (∫ q in Ioc (-c / 2) (c / 2), deriv (fun y => v1 s (q, y) * v2 s (q, y)) η)
      - ν * (∫ q in Ioc (-c / 2) (c / 2),
          deriv (fun y => deriv (fun y' => v1 s (q, y')) y) η) = 0 := by
    have e1 : (∫ q in Ioc (-c / 2) (c / 2),
        (deriv (fun y => v1 y (q, η)) s + deriv (fun y => v1 s (q, y) * v2 s (q, y)) η
          - ν * deriv (fun y => deriv (fun y' => v1 s (q, y')) y) η))
        = ∫ q in Ioc (-c / 2) (c / 2),
          (-(partialQ (fun w : Plane => v1 s w * v1 s w) (q, η)) - partialQ (p s) (q, η)
            + ν * partialQ (partialQ (v1 s)) (q, η)) :=
      setIntegral_congr_fun measurableSet_Ioc (fun q _ => hpt q)
    have eL : (∫ q in Ioc (-c / 2) (c / 2),
        (deriv (fun y => v1 y (q, η)) s + deriv (fun y => v1 s (q, y) * v2 s (q, y)) η
          - ν * deriv (fun y => deriv (fun y' => v1 s (q, y')) y) η))
        = (∫ q in Ioc (-c / 2) (c / 2), deriv (fun y => v1 y (q, η)) s)
          + (∫ q in Ioc (-c / 2) (c / 2), deriv (fun y => v1 s (q, y) * v2 s (q, y)) η)
          - ν * (∫ q in Ioc (-c / 2) (c / 2),
              deriv (fun y => deriv (fun y' => v1 s (q, y')) y) η) := by
      rw [integral_sub hAB hCν, integral_add iA' iB', integral_const_mul]
    have iXn : Integrable (fun q => -(partialQ (fun w : Plane => v1 s w * v1 s w) (q, η)))
        (volume.restrict (Ioc (-c / 2) (c / 2))) := iX.neg
    have eR : (∫ q in Ioc (-c / 2) (c / 2),
        (-(partialQ (fun w : Plane => v1 s w * v1 s w) (q, η)) - partialQ (p s) (q, η)
          + ν * partialQ (partialQ (v1 s)) (q, η))) = 0 := by
      rw [integral_add hXPD hνD, integral_sub iXn iP, integral_neg, integral_const_mul,
        hX, hP, hD]
      ring
    linarith [e1, eL, eR]
  -- assemble
  rw [hA'.deriv, hB'.deriv, hT3]
  simp only [smul_eq_mul]
  linear_combination c⁻¹ * hsum

/-! ### The leaf statement `TrainMeanMomentumU` -/

/-- **`PartI:T01/leaf`: the averaged first momentum equation** (source lines 397-404). The
mean `u = \bar v₁` of the first velocity component satisfies `u_s + g_η = ν u_ηη` for `s > 0`,
with `g = \overline{v₁v₂}`. -/
theorem trainMeanMomentumU : TrainMeanMomentumU := by
  intro ν c hν hc tr s hs η
  have hv1 : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => tr.v x.1 x.2 0) (Ioi 0 ×ˢ univ) :=
    (EuclideanSpace.proj (0 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp_contDiffOn
      (tr.isTrain.smooth_v.mono (prod_mono Ioi_subset_Ici_self (subset_refl _)))
  have hv2 : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => tr.v x.1 x.2 1) (Ioi 0 ×ˢ univ) :=
    (EuclideanSpace.proj (1 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp_contDiffOn
      (tr.isTrain.smooth_v.mono (prod_mono Ioi_subset_Ici_self (subset_refl _)))
  have hp : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => tr.p x.1 x.2) (Ioi 0 ×ˢ univ) :=
    tr.isTrain.smooth_p.mono (prod_mono Ioi_subset_Ici_self (subset_refl _))
  have hdiffv : ∀ s' : ℝ, 0 < s' → ∀ z : Plane, DifferentiableAt ℝ (fun t => tr.v t z) s' :=
    fun s' hs' z => by
      have hU : (Ioi 0 ×ˢ (univ : Set Plane)) ∈ 𝓝 (s', z) :=
        (isOpen_Ioi.prod isOpen_univ).mem_nhds ⟨hs', mem_univ z⟩
      have hC : ContDiffAt ℝ ∞ (fun x : ℝ × Plane => tr.v x.1 x.2) (s', z) :=
        (tr.isTrain.smooth_v.mono (prod_mono Ioi_subset_Ici_self (subset_refl _))).contDiffAt hU
      have hpath : DifferentiableAt ℝ (fun t : ℝ => ((t, z) : ℝ × Plane)) s' :=
        differentiableAt_id.prodMk (differentiableAt_const z)
      exact (hC.differentiableAt (by simp)).comp s' hpath
  have hperv : ∀ s' : ℝ, 0 < s' → UnforcedLeray.Cyl.IsPeriodic c (fun z => tr.v s' z 0) :=
    fun s' hs' => (tr.isTrain.periodic_v s' hs'.le).comp (fun y => y 0)
  have hperp : ∀ s' : ℝ, 0 < s' → UnforcedLeray.Cyl.IsPeriodic c (tr.p s') :=
    fun s' hs' => tr.isTrain.periodic_p s' hs'.le
  have hdiv : ∀ s' : ℝ, 0 < s' → ∀ z : Plane,
      partialQ (fun z => tr.v s' z 0) z + partialEta (fun z => tr.v s' z 1) z = 0 :=
    fun s' hs' z => tr.isTrain.solenoidal s' hs'.le z
  have hmom : ∀ s' : ℝ, 0 < s' → ∀ z : Plane,
      deriv (fun t => tr.v t z 0) s' + (tr.v s' z 0 * partialQ (fun w => tr.v s' w 0) z
        + tr.v s' z 1 * partialEta (fun w => tr.v s' w 0) z)
        - ν * (partialQ (partialQ (fun w => tr.v s' w 0)) z
          + partialEta (partialEta (fun w => tr.v s' w 0)) z)
        + partialQ (tr.p s') z = 0 := by
    intro s' hs' z
    have h0 := congrArg (fun y : EuclideanSpace ℝ (Fin 2) => y 0)
      (tr.isTrain.momentum s' hs' z)
    have hd := mm_deriv_proj (fun t => tr.v t z) s' (hdiffv s' hs' z)
    simp only [UnforcedLeray.Train.momentumResidual, UnforcedLeray.Train.advection,
      UnforcedLeray.Train.vecLaplacian, UnforcedLeray.Train.gradS, UnforcedLeray.Train.lapS,
      UnforcedLeray.Train.toVec_zero, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
      smul_eq_mul, PiLp.zero_apply] at h0
    rw [hd]
    linear_combination h0
  exact mm_core hc (fun r z => tr.v r z 0) (fun r z => tr.v r z 1) tr.p hv1 hv2 hp hperv hperp
    hdiv hmom hs η

end UnforcedLeray.Short.PartI
