import UnforcedLeray.Short.PartI.Sub.T02_2
import UnforcedLeray.Short.PartI.Tasks.TrainMeanEquations.MeanMomentumU

/-!
# Part I, task `PartI:T02/2`, leaf `PressureMeanIdentity`

Source of record: `the November 2 reference manuscript`, lines 397-404 (mean
equations, `\bar v₂ = 0`) and line 447 (the decaying pressure gauge).

Statement: `p̄ + \overline{v₂²}` does not depend on `η`, where `p̄ = hmean c (p s)`.

Proof outline.

1. For `s ∈ [0,T]`, `\bar v₂(s,·) ≡ 0`: its `η`-derivative is `\overline{∂_η v₂} = -\overline{∂_q v₁}`
   (divergence), which vanishes by `q`-periodicity; the function tends to `0` as `|η| → ∞`.
2. For `s ∈ (0,T)`: `∫_q ∂_s v₂ = 0` (differentiate `r ↦ \bar v₂(r,η)`, which vanishes on `[0,T]`),
   and `∫_q ∂_η² v₂ = 0` (differentiate `η ↦ \overline{∂_η v₂} ≡ 0`).
3. Pointwise, using `div v = 0`, the second momentum component reads
   `∂_η p + ∂_η(v₂²) = -∂_s v₂ - ∂_q(v₁v₂) + ν(∂_q²v₂ + ∂_η²v₂)`; averaging over `q` gives
   `∂_η(p̄ + \overline{v₂²}) = 0`, so the identity holds on `(0,T)`.
4. The identity extends to `[0,T]` by continuity in `s` of the two averages over the compact cell.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec)
open UnforcedLeray.Cyl (Plane)

/-! ### Calculus helpers -/

/-- The `η`-derivative of a horizontal average of a smooth function, under the `q`-integral. -/
theorem pmi_hasDerivAt_hmean_eta {c : ℝ} {G : Plane → ℝ} (hG : ContDiff ℝ ∞ G) (e : ℝ) :
    HasDerivAt (fun e' => hmean c G e') (hmean c (fun z => Cyl.partialEta G z) e) e := by
  have hH : ContDiffOn ℝ ∞ (fun y : ℝ × ℝ => G (y.2, y.1))
      (Ioo (e - 1) (e + 1) ×ˢ (univ : Set ℝ)) :=
    (hG.comp (contDiff_snd.prodMk contDiff_fst)).contDiffOn
  obtain ⟨_, key⟩ := mm_hasDerivAt_avg (-c / 2) (c / 2) e hH ⟨by linarith, by linarith⟩
  exact key.const_smul c⁻¹

theorem pmi_partialEta_contDiff {g : Plane → ℝ} (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (fun z => Cyl.partialEta g z) := by
  have hd : Differentiable ℝ g := hg.differentiable (by simp)
  have heq : (fun z => Cyl.partialEta g z) = fun z => fderiv ℝ g z (0, 1) :=
    funext fun z => mm_partialEta_eq (hd z)
  rw [heq]
  exact (hg.fderiv_right (by simp)).clm_apply contDiff_const

theorem pmi_cont_partialEta_slice {g : Plane → ℝ} (hg : ContDiff ℝ ∞ g) (e : ℝ) :
    Continuous (fun q : ℝ => Cyl.partialEta g (q, e)) :=
  (pmi_partialEta_contDiff hg).continuous.comp (continuous_id.prodMk continuous_const)

/-- The second coordinate of the derivative of a `Vec`-valued function. -/
theorem pmi_deriv_comp1 {f : ℝ → Vec} {s : ℝ} (hf : DifferentiableAt ℝ f s) :
    deriv f s 1 = deriv (fun t => f t 1) s := by
  have h := ((EuclideanSpace.proj (1 : Fin 2) : Vec →L[ℝ] ℝ).hasFDerivAt).comp_hasDerivAt s
    hf.hasDerivAt
  exact h.deriv.symm

/-- A vanishing horizontal average has a vanishing `q`-integral. -/
theorem pmi_integral_of_hmean {c : ℝ} (hc : 0 < c) {G : Plane → ℝ} {e : ℝ}
    (h : hmean c G e = 0) : ∫ q in Ioc (-c / 2) (c / 2), G (q, e) = 0 := by
  unfold hmean at h
  rcases smul_eq_zero.1 h with h' | h'
  · exact absurd h' (inv_ne_zero hc.ne')
  · exact h'

/-- Age derivative of the `q`-integral of the second velocity component, at `s ∈ (0,T)`. -/
theorem pmi_hasDerivAt_s {c T : ℝ} {v : ℝ → Plane → Vec}
    (hv : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => v x.1 x.2) (Icc 0 T ×ˢ univ))
    {s : ℝ} (hs : s ∈ Ioo 0 T) (e : ℝ) :
    IntegrableOn (fun q => deriv (fun t => v t (q, e) 1) s) (Ioc (-c / 2) (c / 2)) ∧
      HasDerivAt (fun r => ∫ q in Ioc (-c / 2) (c / 2), v r (q, e) 1)
        (∫ q in Ioc (-c / 2) (c / 2), deriv (fun t => v t (q, e) 1) s) s := by
  have hv' : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => v x.1 x.2) (Ioo 0 T ×ˢ univ) :=
    hv.mono (prod_mono Ioo_subset_Icc_self subset_rfl)
  have h1 : ContDiffOn ℝ ∞ (fun y : ℝ × ℝ => v y.1 (y.2, e)) (Ioo 0 T ×ˢ (univ : Set ℝ)) :=
    hv'.comp (contDiff_fst.prodMk (contDiff_snd.prodMk contDiff_const)).contDiffOn
      (fun y hy => ⟨hy.1, mem_univ _⟩)
  have hw : ContDiff ℝ ∞ (fun w : Vec => w 1) :=
    (EuclideanSpace.proj (1 : Fin 2) : Vec →L[ℝ] ℝ).contDiff
  have hH : ContDiffOn ℝ ∞ (fun y : ℝ × ℝ => v y.1 (y.2, e) 1) (Ioo 0 T ×ˢ (univ : Set ℝ)) :=
    hw.comp_contDiffOn h1
  obtain ⟨hI, hD⟩ := mm_hasDerivAt_avg (-c / 2) (c / 2) s hH ⟨hs.1, hs.2⟩
  exact ⟨hI, hD⟩

/-! ### The mean of the second velocity component vanishes -/

/-- The `q`-average of `∂_η v₂` vanishes at a fixed age `s ∈ [0,T]` (divergence and periodicity). -/
theorem pmi_L0 {ν c T : ℝ} {v : ℝ → Plane → Vec} {p : ℝ → Plane → ℝ}
    (hG : GaugeHyp ν c T v p) {s : ℝ} (hs : s ∈ Icc 0 T) (e : ℝ) :
    hmean c (fun z => Cyl.partialEta (fun w => v s w 1) z) e = 0 := by
  have hc : 0 < c := zero_lt_one.trans_le hG.one_le
  have hg0 : ContDiff ℝ ∞ (fun z => v s z 0) := (gg_component hG hs 0).1
  have hper0 : Cyl.IsPeriodic c (fun z => v s z 0) :=
    fun z => congrArg (fun x : Vec => x 0) (hG.classical.periodic_v s hs z)
  have hdiv : ∀ z : Plane,
      Cyl.partialEta (fun w => v s w 1) z = -Cyl.partialQ (fun w => v s w 0) z := by
    intro z
    have h := hG.classical.solenoidal s hs z
    unfold Cyl.divergence at h
    linarith
  have hfun : (fun q : ℝ => Cyl.partialEta (fun w => v s w 1) (q, e)) =
      fun q => -Cyl.partialQ (fun w => v s w 0) (q, e) :=
    funext fun q => hdiv (q, e)
  unfold hmean
  rw [hfun, integral_neg, mm_integral_partialQ_zero hc hg0 hper0 e, neg_zero, smul_zero]

/-- `\bar v₂ ≡ 0` at a fixed age `s ∈ [0,T]`. -/
theorem pmi_M1 {ν c T : ℝ} {v : ℝ → Plane → Vec} {p : ℝ → Plane → ℝ}
    (hG : GaugeHyp ν c T v p) {s : ℝ} (hs : s ∈ Icc 0 T) (η : ℝ) :
    hmean c (fun z => v s z 1) η = 0 := by
  have hc : 0 < c := zero_lt_one.trans_le hG.one_le
  have hg1 : ContDiff ℝ ∞ (fun z => v s z 1) := (gg_component hG hs 1).1
  have hdec1 := (gg_component hG hs 1).2.2
  have hderiv : ∀ x : ℝ, HasDerivAt (fun e' => hmean c (fun z => v s z 1) e') 0 x := by
    intro x
    have h := pmi_hasDerivAt_hmean_eta (c := c) hg1 x
    rw [pmi_L0 hG hs x] at h
    exact h
  have hconst : ∀ e, hmean c (fun z => v s z 1) e = hmean c (fun z => v s z 1) 0 :=
    fun e => is_const_of_deriv_eq_zero (fun x => (hderiv x).differentiableAt)
      (fun x => (hderiv x).deriv) e 0
  have hk : Tendsto (fun e : ℝ => ((0 : ℝ), e) : ℝ → Plane)
      (comap (fun e : ℝ => |e|) atTop) (comap (fun z : Plane => |z.2|) atTop) :=
    tendsto_comap_iff.2 tendsto_comap
  have hlim : Tendsto (fun e => hmean c (fun z => v s z 1) e)
      (comap (fun e : ℝ => |e|) atTop) (𝓝 0) :=
    (gg_hmean_tendsto hc hdec1).comp hk
  have hK : (fun e => hmean c (fun z => v s z 1) e) = fun _ => hmean c (fun z => v s z 1) 0 :=
    funext hconst
  rw [hK] at hlim
  have : NeBot (comap (fun e : ℝ => |e|) atTop) := by
    rw [comap_abs_atTop]
    infer_instance
  have hval : hmean c (fun z => v s z 1) 0 = 0 := tendsto_nhds_unique tendsto_const_nhds hlim
  rw [hconst η, hval]

/-- `∫_q ∂_η² v₂ = 0` at a fixed age `s ∈ [0,T]`. -/
theorem pmi_M3 {ν c T : ℝ} {v : ℝ → Plane → Vec} {p : ℝ → Plane → ℝ}
    (hG : GaugeHyp ν c T v p) {s : ℝ} (hs : s ∈ Icc 0 T) (e : ℝ) :
    hmean c (fun z => Cyl.partialEta (fun w => Cyl.partialEta (fun z => v s z 1) w) z) e = 0 := by
  have hg1 : ContDiff ℝ ∞ (fun z => v s z 1) := (gg_component hG hs 1).1
  have hG1 : ContDiff ℝ ∞ (fun w => Cyl.partialEta (fun z => v s z 1) w) :=
    pmi_partialEta_contDiff hg1
  have h := pmi_hasDerivAt_hmean_eta (c := c) hG1 e
  have hev : (fun e' => hmean c (fun w => Cyl.partialEta (fun z => v s z 1) w) e') =ᶠ[𝓝 e]
      (fun _ => (0 : ℝ)) :=
    Filter.Eventually.of_forall fun e' => pmi_L0 hG hs e'
  have h0 := (hasDerivAt_const e (0 : ℝ)).congr_of_eventuallyEq hev
  exact h.unique h0

/-- The `q`-integral of `∂_s v₂` vanishes on `(0,T)`: the age derivative of `\bar v₂` is zero, since
`\bar v₂ ≡ 0` on `[0,T]`. -/
theorem pmi_M2 {ν c T : ℝ} {v : ℝ → Plane → Vec} {p : ℝ → Plane → ℝ}
    (hG : GaugeHyp ν c T v p) {s : ℝ} (hs : s ∈ Ioo 0 T) (e : ℝ) :
    ∫ q in Ioc (-c / 2) (c / 2), deriv (fun t => v t (q, e) 1) s = 0 := by
  have hc : 0 < c := zero_lt_one.trans_le hG.one_le
  obtain ⟨_, hD⟩ := pmi_hasDerivAt_s hG.classical.smooth_v hs e
  have hev : (fun r => ∫ q in Ioc (-c / 2) (c / 2), v r (q, e) 1) =ᶠ[𝓝 s]
      fun _ => (0 : ℝ) := by
    filter_upwards [Ioo_mem_nhds hs.1 hs.2] with r hr
    exact pmi_integral_of_hmean hc (pmi_M1 hG (Ioo_subset_Icc_self hr) e)
  have hz : HasDerivAt (fun r => ∫ q in Ioc (-c / 2) (c / 2), v r (q, e) 1) 0 s :=
    (hasDerivAt_const s (0 : ℝ)).congr_of_eventuallyEq hev
  exact hD.unique hz

/-! ### The second momentum component, pointwise -/

/-- The second component of the momentum equation, rewritten with `div v = 0`: the advection term
`v₁∂_q v₂ + v₂∂_η v₂` equals `∂_q(v₁v₂) + ∂_η(v₂²)`. -/
theorem pmi_momentum1 {ν c T : ℝ} {v : ℝ → Plane → Vec} {p : ℝ → Plane → ℝ}
    (hG : GaugeHyp ν c T v p) {s : ℝ} (hs : s ∈ Ioo 0 T) (z : Plane) :
    Cyl.partialEta (p s) z + Cyl.partialEta (fun w => v s w 1 * v s w 1) z =
      -(deriv (fun t => v t z 1) s) - Cyl.partialQ (fun w => v s w 0 * v s w 1) z
        + ν * Train.lapS (fun w => v s w 1) z := by
  have hsIcc : s ∈ Icc 0 T := Ioo_subset_Icc_self hs
  have hcl := hG.classical
  have hv' : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => v x.1 x.2) (Ioo 0 T ×ˢ univ) :=
    hcl.smooth_v.mono (prod_mono Ioo_subset_Icc_self subset_rfl)
  have hca : ContDiffAt ℝ ∞ (fun x : ℝ × Plane => v x.1 x.2) (s, z) :=
    hv'.contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨hs, mem_univ z⟩)
  have hpath : DifferentiableAt ℝ (fun t : ℝ => ((t, z) : ℝ × Plane)) s :=
    differentiableAt_id.prodMk (differentiableAt_const z)
  have hgz : DifferentiableAt ℝ (fun x : ℝ × Plane => v x.1 x.2) (s, z) :=
    hca.differentiableAt (by simp)
  have hcomp := hgz.comp s hpath
  have hdiff : DifferentiableAt ℝ (fun t => v t z) s := hcomp
  have hD0 : Differentiable ℝ (fun w => v s w 0) :=
    ((gg_component hG hsIcc 0).1).differentiable (by simp)
  have hD1 : Differentiable ℝ (fun w => v s w 1) :=
    ((gg_component hG hsIcc 1).1).differentiable (by simp)
  have hmom := hcl.momentum s hs z
  unfold Train.momentumResidual at hmom
  have h1 := congrArg (fun x : Vec => x 1) hmom
  simp only [Train.advection, Train.vecLaplacian, Train.gradS, PiLp.add_apply, PiLp.sub_apply,
    PiLp.smul_apply, smul_eq_mul, Train.toVec_one, PiLp.zero_apply] at h1
  rw [pmi_deriv_comp1 hdiff] at h1
  have hE := mm_partialQ_mul hD0 hD1 z
  have hSq := mm_partialEta_mul hD1 hD1 z
  have hdv : Cyl.partialQ (fun w => v s w 0) z + Cyl.partialEta (fun w => v s w 1) z = 0 := by
    have h := hcl.solenoidal s hsIcc z
    unfold Cyl.divergence at h
    exact h
  linear_combination h1 + hSq + hE + (v s z 1) * hdv

/-- The `q`-average of the second momentum component: `∫_q (∂_η p + ∂_η v₂²) = 0`, at a fixed
age `s ∈ (0,T)` and any `η`. -/
theorem pmi_K1 {ν c T : ℝ} {v : ℝ → Plane → Vec} {p : ℝ → Plane → ℝ}
    (hG : GaugeHyp ν c T v p) {s : ℝ} (hs : s ∈ Ioo 0 T) (e : ℝ) :
    hmean c (fun z => Cyl.partialEta (p s) z) e +
      hmean c (fun z => Cyl.partialEta (fun w => v s w 1 ^ 2) z) e = 0 := by
  have hc : 0 < c := zero_lt_one.trans_le hG.one_le
  have hsIcc : s ∈ Icc 0 T := Ioo_subset_Icc_self hs
  have hsq : (fun w : Plane => v s w 1 ^ 2) = fun w => v s w 1 * v s w 1 :=
    funext fun w => sq _
  rw [hsq]
  have hP : ContDiff ℝ ∞ (p s) := gg_slice_contDiff hsIcc hG.classical.smooth_p
  have hg0 : ContDiff ℝ ∞ (fun z => v s z 0) := (gg_component hG hsIcc 0).1
  have hg1 : ContDiff ℝ ∞ (fun z => v s z 1) := (gg_component hG hsIcc 1).1
  have hE : ContDiff ℝ ∞ (fun w : Plane => v s w 0 * v s w 1) := hg0.mul hg1
  have hSq : ContDiff ℝ ∞ (fun w : Plane => v s w 1 * v s w 1) := hg1.mul hg1
  have hperE : Cyl.IsPeriodic c (fun w : Plane => v s w 0 * v s w 1) := fun z => by
    simp only [hG.classical.periodic_v s hsIcc z]
  have hper1 : Cyl.IsPeriodic c (fun z => v s z 1) :=
    fun z => congrArg (fun x : Vec => x 1) (hG.classical.periodic_v s hsIcc z)
  have hIP : IntegrableOn (fun q => Cyl.partialEta (p s) (q, e)) (Ioc (-c / 2) (c / 2)) :=
    ((pmi_cont_partialEta_slice hP e).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hISq : IntegrableOn (fun q => Cyl.partialEta (fun w => v s w 1 * v s w 1) (q, e))
      (Ioc (-c / 2) (c / 2)) :=
    ((pmi_cont_partialEta_slice hSq e).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have iA : IntegrableOn (fun q => deriv (fun t => v t (q, e) 1) s) (Ioc (-c / 2) (c / 2)) :=
    (pmi_hasDerivAt_s hG.classical.smooth_v hs e).1
  have iE : IntegrableOn (fun q => Cyl.partialQ (fun w => v s w 0 * v s w 1) (q, e))
      (Ioc (-c / 2) (c / 2)) :=
    ((mm_cont_partialQ_slice hE e).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hLc : Continuous (fun q : ℝ => Train.lapS (fun w => v s w 1) (q, e)) :=
    (mm_cont_partialQ_slice (mm_partialQ_contDiff hg1) e).add
      (pmi_cont_partialEta_slice (pmi_partialEta_contDiff hg1) e)
  have iL : IntegrableOn (fun q => Train.lapS (fun w => v s w 1) (q, e))
      (Ioc (-c / 2) (c / 2)) :=
    (hLc.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have zA : ∫ q in Ioc (-c / 2) (c / 2), deriv (fun t => v t (q, e) 1) s = 0 :=
    pmi_M2 hG hs e
  have zE : ∫ q in Ioc (-c / 2) (c / 2), Cyl.partialQ (fun w => v s w 0 * v s w 1) (q, e) = 0 :=
    mm_integral_partialQ_zero hc hE hperE e
  have zL : ∫ q in Ioc (-c / 2) (c / 2), Train.lapS (fun w => v s w 1) (q, e) = 0 := by
    have hiQ : IntegrableOn (fun q => Cyl.partialQ (Cyl.partialQ (fun z => v s z 1)) (q, e))
        (Ioc (-c / 2) (c / 2)) :=
      ((mm_cont_partialQ_slice (mm_partialQ_contDiff hg1) e).integrableOn_Icc).mono_set
        Ioc_subset_Icc_self
    have hiH : IntegrableOn
        (fun q => Cyl.partialEta (Cyl.partialEta (fun z => v s z 1)) (q, e))
        (Ioc (-c / 2) (c / 2)) :=
      ((pmi_cont_partialEta_slice (pmi_partialEta_contDiff hg1) e).integrableOn_Icc).mono_set
        Ioc_subset_Icc_self
    have zL1 : ∫ q in Ioc (-c / 2) (c / 2), Cyl.partialQ (Cyl.partialQ (fun z => v s z 1)) (q, e)
        = 0 :=
      mm_integral_partialQ_zero hc (mm_partialQ_contDiff hg1) hper1.partialQ e
    have zL2 : ∫ q in Ioc (-c / 2) (c / 2),
        Cyl.partialEta (Cyl.partialEta (fun z => v s z 1)) (q, e) = 0 :=
      pmi_integral_of_hmean hc (pmi_M3 hG hsIcc e)
    unfold Train.lapS
    rw [integral_add hiQ hiH, zL1, zL2, add_zero]
  have i1 : IntegrableOn (fun q => -(deriv (fun t => v t (q, e) 1) s)
      - Cyl.partialQ (fun w => v s w 0 * v s w 1) (q, e)) (Ioc (-c / 2) (c / 2)) :=
    Integrable.sub (Integrable.neg iA) iE
  have i2 : IntegrableOn (fun q => ν * Train.lapS (fun w => v s w 1) (q, e))
      (Ioc (-c / 2) (c / 2)) :=
    Integrable.const_mul iL ν
  have i3 : IntegrableOn (fun q => -(deriv (fun t => v t (q, e) 1) s)) (Ioc (-c / 2) (c / 2)) :=
    Integrable.neg iA
  have hR : ∫ q in Ioc (-c / 2) (c / 2),
      (-(deriv (fun t => v t (q, e) 1) s) - Cyl.partialQ (fun w => v s w 0 * v s w 1) (q, e)
        + ν * Train.lapS (fun w => v s w 1) (q, e)) = 0 := by
    rw [integral_add i1 i2, integral_sub i3 iE, integral_neg, integral_const_mul, zA, zE, zL]
    ring
  have hIPS : IntegrableOn
      (fun q => Cyl.partialEta (p s) (q, e) + Cyl.partialEta (fun w => v s w 1 * v s w 1) (q, e))
      (Ioc (-c / 2) (c / 2)) := Integrable.add hIP hISq
  have hcongr : ∫ q in Ioc (-c / 2) (c / 2),
      (Cyl.partialEta (p s) (q, e) + Cyl.partialEta (fun w => v s w 1 * v s w 1) (q, e)) =
      ∫ q in Ioc (-c / 2) (c / 2),
      (-(deriv (fun t => v t (q, e) 1) s) - Cyl.partialQ (fun w => v s w 0 * v s w 1) (q, e)
        + ν * Train.lapS (fun w => v s w 1) (q, e)) :=
    setIntegral_congr_fun measurableSet_Ioc (fun q _ => pmi_momentum1 hG hs (q, e))
  unfold hmean
  rw [← smul_add, ← integral_add hIP hISq, hcongr, hR, smul_zero]

/-- The interior identity: for `s ∈ (0,T)` the `η`-derivative of `p̄ + \overline{v₂²}` vanishes. -/
theorem pmi_interior {ν c T : ℝ} {v : ℝ → Plane → Vec} {p : ℝ → Plane → ℝ}
    (hG : GaugeHyp ν c T v p) {s : ℝ} (hs : s ∈ Ioo 0 T) (η : ℝ) :
    hmean c (p s) η + hmean c (fun z => v s z 1 ^ 2) η =
      hmean c (p s) 0 + hmean c (fun z => v s z 1 ^ 2) 0 := by
  have hsIcc : s ∈ Icc 0 T := Ioo_subset_Icc_self hs
  have hP : ContDiff ℝ ∞ (p s) := gg_slice_contDiff hsIcc hG.classical.smooth_p
  have hg1 : ContDiff ℝ ∞ (fun z => v s z 1) := (gg_component hG hsIcc 1).1
  have hSq : ContDiff ℝ ∞ (fun z : Plane => v s z 1 ^ 2) := hg1.pow 2
  have hderiv : ∀ x : ℝ,
      HasDerivAt (fun e' => hmean c (p s) e' + hmean c (fun z => v s z 1 ^ 2) e') 0 x := by
    intro x
    exact ((pmi_hasDerivAt_hmean_eta (c := c) hP x).add
      (pmi_hasDerivAt_hmean_eta (c := c) hSq x)).congr_deriv (pmi_K1 hG hs x)
  exact is_const_of_deriv_eq_zero (f := fun e' => hmean c (p s) e' + hmean c (fun z => v s z 1 ^ 2) e')
    (fun x => (hderiv x).differentiableAt) (fun x => (hderiv x).deriv) η 0

/-! ### Continuity in the age, and the extension to `[0,T]` -/

/-- Continuity in `r ∈ [0,T]` of the horizontal average of `G r` at a fixed `η`. -/
theorem pmi_hmean_contOn {c T : ℝ} (_hc : 0 < c) {G : ℝ → Plane → ℝ}
    (hG : ContinuousOn (fun x : ℝ × Plane => G x.1 x.2) (Icc 0 T ×ˢ univ)) (η : ℝ) :
    ContinuousOn (fun r => hmean c (G r) η) (Icc 0 T) := by
  have hK : ContinuousOn (fun x : ℝ × ℝ => G x.1 (x.2, η))
      (Icc 0 T ×ˢ Icc (-c / 2) (c / 2)) := by
    refine hG.comp (f := fun x : ℝ × ℝ => (x.1, (x.2, η))) ?_ ?_
    · exact (continuous_fst.prodMk (continuous_snd.prodMk continuous_const)).continuousOn
    · intro x hx
      exact ⟨hx.1, mem_univ _⟩
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hK
  have hqcont : ∀ r ∈ Icc 0 T, Continuous (fun q : ℝ => G r (q, η)) := by
    intro r hr
    exact hG.comp_continuous (f := fun q : ℝ => (r, (q, η)))
      (continuous_const.prodMk (continuous_id.prodMk continuous_const))
      (fun q => ⟨hr, mem_univ _⟩)
  have hrcont : ∀ q : ℝ, ContinuousOn (fun r => G r (q, η)) (Icc 0 T) := by
    intro q
    exact hG.comp (f := fun r : ℝ => (r, (q, η)))
      (continuous_id.prodMk continuous_const).continuousOn (fun r hr => ⟨hr, mem_univ _⟩)
  unfold hmean
  refine ContinuousOn.const_smul ?_ c⁻¹
  refine continuousOn_of_dominated (bound := fun _ => C)
    (fun r hr => (hqcont r hr).aestronglyMeasurable) ?_ (integrable_const C) (ae_of_all _ hrcont)
  intro r hr
  refine (ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun q hq => ?_)
  exact hC (r, q) ⟨hr, Ioc_subset_Icc_self hq⟩

/-- A function continuous on `[a,b]` and zero on `(a,b)` is zero on `[a,b]`. -/
theorem pmi_eq_zero_of_contOn {a b : ℝ} (hab : a < b) {Φ : ℝ → ℝ}
    (hc : ContinuousOn Φ (Icc a b)) (h0 : ∀ r ∈ Ioo a b, Φ r = 0) :
    ∀ s ∈ Icc a b, Φ s = 0 := by
  intro s hs
  have hcl : s ∈ closure (Ioo a b) := by
    rw [closure_Ioo hab.ne]
    exact hs
  have : NeBot (𝓝[Ioo a b] s) := mem_closure_iff_nhdsWithin_neBot.1 hcl
  have h1 : Tendsto Φ (𝓝[Ioo a b] s) (𝓝 (Φ s)) :=
    (hc s hs).tendsto.mono_left (nhdsWithin_mono s Ioo_subset_Icc_self)
  have hev : (fun _ : ℝ => (0 : ℝ)) =ᶠ[𝓝[Ioo a b] s] Φ :=
    Filter.Eventually.mono eventually_mem_nhdsWithin (fun r hr => (h0 r hr).symm)
  have h2 : Tendsto Φ (𝓝[Ioo a b] s) (𝓝 0) := tendsto_const_nhds.congr' hev
  exact tendsto_nhds_unique h1 h2

/-! ### The theorem -/

/-- **`PressureMeanIdentity`** (source lines 397-404, 447): `p̄ + \overline{v₂²}` does not depend
on `η`, for every `s ∈ [0,T]`. -/
theorem pressureMeanIdentity : PressureMeanIdentity := by
  unfold PressureMeanIdentity
  intro ν c T v p hG s hs η
  have hc : 0 < c := zero_lt_one.trans_le hG.one_le
  have hT : 0 < T := hG.T_pos
  have hpC : ContinuousOn (fun x : ℝ × Plane => p x.1 x.2) (Icc 0 T ×ˢ univ) :=
    hG.classical.smooth_p.continuousOn
  have hvC : ContinuousOn (fun x : ℝ × Plane => v x.1 x.2 1 ^ 2) (Icc 0 T ×ˢ univ) :=
    ((EuclideanSpace.proj (1 : Fin 2) : Vec →L[ℝ] ℝ).continuous.comp_continuousOn
      hG.classical.smooth_v.continuousOn).pow 2
  have hcont : ContinuousOn (fun r => (hmean c (p r) η + hmean c (fun z => v r z 1 ^ 2) η) -
      (hmean c (p r) 0 + hmean c (fun z => v r z 1 ^ 2) 0)) (Icc 0 T) :=
    ((pmi_hmean_contOn hc hpC η).add
        (pmi_hmean_contOn (G := fun r z => v r z 1 ^ 2) hc hvC η)).sub
      ((pmi_hmean_contOn hc hpC 0).add
        (pmi_hmean_contOn (G := fun r z => v r z 1 ^ 2) hc hvC 0))
  have h0 : ∀ r ∈ Ioo 0 T, (hmean c (p r) η + hmean c (fun z => v r z 1 ^ 2) η) -
      (hmean c (p r) 0 + hmean c (fun z => v r z 1 ^ 2) 0) = 0 :=
    fun r hr => sub_eq_zero.2 (pmi_interior hG hr η)
  exact sub_eq_zero.1 (pmi_eq_zero_of_contOn hT hcont h0 s hs)

end UnforcedLeray.Short.PartI
