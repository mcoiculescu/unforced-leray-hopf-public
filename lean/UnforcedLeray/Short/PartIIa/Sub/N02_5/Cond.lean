import UnforcedLeray.Short.PartIIa.Sub.N02_5

/-!
# Part II-a, task `PartII-a:N02/5` (`NearLerayModeSplit`): conditional reductions


four leaves `AvgSmooth`, `AvgOpS`, `AvgQCauchySchwarz`, `AvgSliceMono` of `Sub/N02_5.lean`:

* `avgJensen_of`: Jensen in `q` (`AvgQCauchySchwarz`) plus Fubini on `measureH c` (`AvgSliceMono`) give
  `∫ w ‖avgQ c g‖² d(measureH c) ≤ ∫ w ‖g‖² d(measureH c)` for continuous band-supported `g`;
* `avgSqZero_of`: termwise `nzSq c a j (avgQ c f) ≤ nzSq c a j f` for `a, j ∈ {0, 1}`
  (`opS` commutes with the average: `AvgOpS`);
* `avgMomentZero_of_sq`, `avgMomentOne_of`: the moment sums (`‖a - b‖² ≤ 2‖a‖² + 2‖b‖²`);
* `nearLerayModeSplit_of_leaves`: the conditional theorem for the target.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226

/-! ### Continuity, band support and integrability -/

theorem avgQ_continuous {c : ℝ} {g : Profile → MeridC} (hg : Continuous g) :
    Continuous (avgQ c g) := by
  unfold avgQ
  have hf : Continuous (Function.uncurry fun (p : Profile) (q : ℝ) => g (p.1, q, p.2.2)) := by
    show Continuous fun z : Profile × ℝ => g (z.1.1, z.2, z.1.2.2)
    fun_prop
  exact Continuous.const_smul (M := ℝ)
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (μ := volume) hf 0 c) _

theorem avgOpS_eq_zero_of_notBand {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : Profile → E} {s0 s1 L : ℝ}
    (hb : ∀ p : Profile, g p ≠ 0 → p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L) (p : Profile)
    (hp : ¬(p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L)) : opS g p = 0 := by
  have hclosed : IsClosed {q : Profile | q.1 ∈ Icc s0 s1 ∧ |q.2.2| ≤ L} :=
    (isClosed_Icc.preimage continuous_fst).inter
      (isClosed_le (continuous_abs.comp (continuous_snd.comp continuous_snd)) continuous_const)
  have hev : g =ᶠ[𝓝 p] fun _ => (0 : E) := by
    filter_upwards [hclosed.isOpen_compl.mem_nhds hp] with q hq
    by_contra h
    exact hq (hb q h)
  have hz : fderiv ℝ g p = 0 := by
    rw [hev.fderiv_eq]
    exact fderiv_const_apply _
  simp [opS, pdS, hz]

theorem avgOpS_band {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : Profile → E} {s0 s1 L : ℝ}
    (hb : ∀ p : Profile, g p ≠ 0 → p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L) (p : Profile)
    (hp : opS g p ≠ 0) : p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L := by
  by_contra h
  exact hp (avgOpS_eq_zero_of_notBand hb p h)

theorem avgOpS_continuous {g : Profile → MeridC} (hg : ContDiff ℝ ∞ g) : Continuous (opS g) := by
  have h1 : Continuous fun p => fderiv ℝ g p := hg.continuous_fderiv (by simp)
  unfold opS pdS
  exact continuous_fst.smul (h1.clm_apply continuous_const)

theorem avgIntegrable_of_band {c s0 s1 L : ℝ} (hs0 : 0 < s0) {Φ : Profile → ℝ}
    (hΦ : Continuous Φ) (hz : ∀ p : Profile, Φ p ≠ 0 → p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L) :
    Integrable Φ (measureH c) := by
  have hm : MemLp Φ 1 (measureH c) := by
    refine memLp_of_continuous_of_ae_vanish hΦ
      (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)) (measureH_band_ne_top c hs0 s1 L) ?_ 1
    filter_upwards [ae_cell_measureH c] with p hp hpA
    by_contra hne
    obtain ⟨h1, h2⟩ := hz p hne
    exact hpA ⟨h1, Ioc_subset_Icc_self hp.2.1, abs_le.1 h2⟩
  exact memLp_one_iff_integrable.1 hm

theorem avgIntegrable_wnorm {c s0 s1 L : ℝ} (hs0 : 0 < s0) (j : ℕ) {E : Type*}
    [NormedAddCommGroup E] {g : Profile → E} (hg : Continuous g)
    (hb : ∀ p : Profile, g p ≠ 0 → p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L) :
    Integrable (fun p : Profile => (|p.2.2| ^ j) ^ 2 * ‖g p‖ ^ 2) (measureH c) :=
  avgIntegrable_of_band hs0 (by fun_prop) fun p hp => hb p (by intro h; apply hp; simp [h])

/-! ### Jensen for the weighted integrals -/

/-- Weighted `L²` contraction of the `q`-average on continuous band-supported profiles. -/
def AvgJensen : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ (g : Profile → MeridC) (j : ℕ), Continuous g →
    (∃ s0 s1 L : ℝ, 0 < s0 ∧ ∀ p : Profile, g p ≠ 0 → p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L) →
    ∫ p, (|p.2.2| ^ j) ^ 2 * ‖avgQ c g p‖ ^ 2 ∂(measureH c) ≤
      ∫ p, (|p.2.2| ^ j) ^ 2 * ‖g p‖ ^ 2 ∂(measureH c)

theorem avgJensen_of (hCS : AvgQCauchySchwarz) (hSM : AvgSliceMono) : AvgJensen := by
  intro c hc g j hg ⟨s0, s1, L, hs0, hb⟩
  have hav : Continuous (avgQ c g) := avgQ_continuous hg
  have hA : Continuous fun p : Profile => (|p.2.2| ^ j) ^ 2 * ‖avgQ c g p‖ ^ 2 := by fun_prop
  have hB : Continuous fun p : Profile => (|p.2.2| ^ j) ^ 2 * ‖g p‖ ^ 2 := by fun_prop
  refine hSM c hc _ _ hA hB ⟨s0, s1, L, hs0, ?_⟩ ?_
  · intro p hp
    rcases hp with hp | hp
    · have h : avgQ c g p ≠ 0 := by
        intro h
        apply hp
        simp [h]
      exact avgQ_band (c := c) hb p h
    · have h : g p ≠ 0 := by
        intro h
        apply hp
        simp [h]
      exact hb p h
  · intro s η hs
    have hgc : Continuous fun q : ℝ => g (s, q, η) := hg.comp (by fun_prop)
    have hcs := hCS c hc _ hgc
    have hint : IntervalIntegrable (fun q => ‖g (s, q, η)‖ ^ 2) volume 0 c :=
      (hgc.norm.pow 2).intervalIntegrable 0 c
    have hconst : ∀ q : ℝ, avgQ c g (s, q, η) = avgQ c g (s, 0, η) := fun q => rfl
    have h1 : ∫ q in (0 : ℝ)..c, (|η| ^ j) ^ 2 * ‖avgQ c g (s, q, η)‖ ^ 2 =
        c * ((|η| ^ j) ^ 2 * ‖avgQ c g (s, 0, η)‖ ^ 2) := by
      simp only [hconst, intervalIntegral.integral_const, smul_eq_mul, sub_zero]
    have h2 : ∫ q in (0 : ℝ)..c, (|η| ^ j) ^ 2 * ‖g (s, q, η)‖ ^ 2 =
        (|η| ^ j) ^ 2 * ∫ q in (0 : ℝ)..c, ‖g (s, q, η)‖ ^ 2 :=
      intervalIntegral.integral_const_mul _ _
    show ∫ q in (0 : ℝ)..c, (|η| ^ j) ^ 2 * ‖avgQ c g (s, q, η)‖ ^ 2 ≤
      ∫ q in (0 : ℝ)..c, (|η| ^ j) ^ 2 * ‖g (s, q, η)‖ ^ 2
    rw [h1, h2]
    set J := ∫ q in (0 : ℝ)..c, g (s, q, η) with hJ
    set I := ∫ q in (0 : ℝ)..c, ‖g (s, q, η)‖ ^ 2 with hI
    have ha : ‖avgQ c g (s, 0, η)‖ ^ 2 = (c⁻¹) ^ 2 * ‖J‖ ^ 2 := by
      show ‖(c⁻¹ : ℝ) • J‖ ^ 2 = _
      rw [norm_smul, mul_pow, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hc)]
    have hkey : c * ‖avgQ c g (s, 0, η)‖ ^ 2 ≤ I := by
      rw [ha]
      calc c * ((c⁻¹) ^ 2 * ‖J‖ ^ 2) = c⁻¹ * ‖J‖ ^ 2 := by field_simp
        _ ≤ c⁻¹ * (c * I) := by gcongr
        _ = I := by field_simp
    have hw : 0 ≤ (|η| ^ j) ^ 2 := by positivity
    calc c * ((|η| ^ j) ^ 2 * ‖avgQ c g (s, 0, η)‖ ^ 2)
        = (|η| ^ j) ^ 2 * (c * ‖avgQ c g (s, 0, η)‖ ^ 2) := by ring
      _ ≤ (|η| ^ j) ^ 2 * I := mul_le_mul_of_nonneg_left hkey hw

/-! ### Termwise comparison and the moment sums -/

/-- Termwise zero-frequency comparison `nzSq c a j (avgQ c f) ≤ nzSq c a j f`, `a, j ∈ {0, 1}`. -/
def AvgSqZero : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ f : Profile → MeridC, IsMeridTest c f →
    ∀ a ∈ Finset.range 2, ∀ j ∈ Finset.range 2, nzSq c a j (avgQ c f) ≤ nzSq c a j f

theorem avgSqZero_of (hOp : AvgOpS) (hJ : AvgJensen) : AvgSqZero := by
  intro c hc f hf a ha j _
  obtain ⟨s0, s1, L, hs0, hb⟩ := hf.band
  have hcont := hf.smooth.continuous
  have ha2 : a = 0 ∨ a = 1 := by
    have := Finset.mem_range.1 ha
    omega
  rcases ha2 with rfl | rfl
  · simp only [nzSq, Function.iterate_zero, id_eq]
    exact hJ c hc f j hcont ⟨s0, s1, L, hs0, hb⟩
  · simp only [nzSq, Function.iterate_one]
    rw [hOp c hc f hf]
    exact hJ c hc (opS f) j (avgOpS_continuous hf.smooth)
      ⟨s0, s1, L, hs0, fun p hp => avgOpS_band hb p hp⟩

theorem avgMomentZero_of_sq (h : AvgSqZero) : AvgMomentZero := by
  intro c hc f hf
  unfold nzMomSum
  refine Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun j hj => ?_
  refine Real.rpow_le_rpow ?_ (h c hc f hf a ha j hj) (by norm_num)
  unfold nzSq
  exact integral_nonneg fun p => by positivity

/-! ### The comparison for the remainder `f - avgQ c f` -/

theorem avgIter_continuous {g : Profile → MeridC} (hg : ContDiff ℝ ∞ g) {a : ℕ} (ha : a < 2) :
    Continuous (opS^[a] g) := by
  have h : a = 0 ∨ a = 1 := by omega
  rcases h with rfl | rfl
  · simpa using hg.continuous
  · simpa using avgOpS_continuous hg

theorem avgIter_band {g : Profile → MeridC} {s0 s1 L : ℝ}
    (hb : ∀ p : Profile, g p ≠ 0 → p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L) {a : ℕ} (ha : a < 2) :
    ∀ p : Profile, (opS^[a] g) p ≠ 0 → p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L := by
  have h : a = 0 ∨ a = 1 := by omega
  rcases h with rfl | rfl
  · simpa using hb
  · intro p hp
    exact avgOpS_band hb p (by simpa using hp)

theorem avgIter_sub {u v : Profile → MeridC} (hu : Differentiable ℝ u) (hv : Differentiable ℝ v)
    {a : ℕ} (ha : a < 2) :
    opS^[a] (fun p => u p - v p) = fun p => (opS^[a] u) p - (opS^[a] v) p := by
  have h : a = 0 ∨ a = 1 := by omega
  rcases h with rfl | rfl
  · rfl
  · funext p
    simp only [Function.iterate_one, opS, pdS]
    have e : fderiv ℝ (fun p => u p - v p) p = fderiv ℝ u p - fderiv ℝ v p :=
      fderiv_sub (hu p) (hv p)
    rw [e]
    simp [smul_sub]

theorem avgSqOne_le {c : ℝ} (hc : 0 < c) {f : Profile → MeridC} (hf : IsMeridTest c f)
    (hsm : AvgSmooth) (h0 : AvgSqZero) {a : ℕ} (ha : a ∈ Finset.range 2) {j : ℕ}
    (hj : j ∈ Finset.range 2) :
    nzSq c a j (fun p => f p - avgQ c f p) ≤ 4 * nzSq c a j f := by
  obtain ⟨s0, s1, L, hs0, hb⟩ := hf.band
  have hsmooth := hsm c hc f hf
  have haL := Finset.mem_range.1 ha
  have hx : Continuous (opS^[a] f) := avgIter_continuous hf.smooth haL
  have hxb := avgIter_band hb haL
  have hy : Continuous (opS^[a] (avgQ c f)) := avgIter_continuous hsmooth haL
  have hyb := avgIter_band (g := avgQ c f) (fun p hp => avgQ_band hb p hp) haL
  have hsub := avgIter_sub (u := f) (v := avgQ c f) (hf.smooth.differentiable (by simp))
    (hsmooth.differentiable (by simp)) haL
  have hIx := avgIntegrable_wnorm (c := c) hs0 j hx hxb
  have hIy := avgIntegrable_wnorm (c := c) hs0 j hy hyb
  have hband : ∀ p : Profile, (opS^[a] f) p - (opS^[a] (avgQ c f)) p ≠ 0 →
      p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L := by
    intro p hp
    by_cases hxp : (opS^[a] f) p = 0
    · refine hyb p fun hyp => hp ?_
      rw [hxp, hyp, sub_zero]
    · exact hxb p hxp
  have hIs := avgIntegrable_wnorm (c := c) hs0 j (hx.sub hy) hband
  have hz := h0 c hc f hf a ha j hj
  unfold nzSq at hz ⊢
  rw [hsub]
  calc ∫ p, (|p.2.2| ^ j) ^ 2 * ‖(opS^[a] f) p - (opS^[a] (avgQ c f)) p‖ ^ 2 ∂(measureH c)
      ≤ ∫ p, (2 * ((|p.2.2| ^ j) ^ 2 * ‖(opS^[a] f) p‖ ^ 2) +
          2 * ((|p.2.2| ^ j) ^ 2 * ‖(opS^[a] (avgQ c f)) p‖ ^ 2)) ∂(measureH c) := by
        refine integral_mono hIs ((hIx.const_mul 2).add (hIy.const_mul 2)) fun p => ?_
        have hn : ‖(opS^[a] f) p - (opS^[a] (avgQ c f)) p‖ ≤
            ‖(opS^[a] f) p‖ + ‖(opS^[a] (avgQ c f)) p‖ := norm_sub_le _ _
        have hsq : ‖(opS^[a] f) p - (opS^[a] (avgQ c f)) p‖ ^ 2 ≤
            2 * ‖(opS^[a] f) p‖ ^ 2 + 2 * ‖(opS^[a] (avgQ c f)) p‖ ^ 2 := by
          nlinarith [norm_nonneg ((opS^[a] f) p), norm_nonneg ((opS^[a] (avgQ c f)) p),
            norm_nonneg ((opS^[a] f) p - (opS^[a] (avgQ c f)) p),
            sq_nonneg (‖(opS^[a] f) p‖ - ‖(opS^[a] (avgQ c f)) p‖)]
        have hw : 0 ≤ (|p.2.2| ^ j) ^ 2 := by positivity
        calc (|p.2.2| ^ j) ^ 2 * ‖(opS^[a] f) p - (opS^[a] (avgQ c f)) p‖ ^ 2
            ≤ (|p.2.2| ^ j) ^ 2 * (2 * ‖(opS^[a] f) p‖ ^ 2 + 2 * ‖(opS^[a] (avgQ c f)) p‖ ^ 2) :=
              mul_le_mul_of_nonneg_left hsq hw
          _ = _ := by ring
    _ = 2 * ∫ p, (|p.2.2| ^ j) ^ 2 * ‖(opS^[a] f) p‖ ^ 2 ∂(measureH c) +
          2 * ∫ p, (|p.2.2| ^ j) ^ 2 * ‖(opS^[a] (avgQ c f)) p‖ ^ 2 ∂(measureH c) := by
        rw [integral_add (hIx.const_mul 2) (hIy.const_mul 2), integral_const_mul,
          integral_const_mul]
    _ ≤ 4 * ∫ p, (|p.2.2| ^ j) ^ 2 * ‖(opS^[a] f) p‖ ^ 2 ∂(measureH c) := by linarith

theorem avgMomentOne_of (hsm : AvgSmooth) (h0 : AvgSqZero) : AvgMomentOne := by
  intro c hc f hf
  unfold nzMomSum
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun a ha => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j hj => ?_
  have h4 := avgSqOne_le hc hf hsm h0 ha hj
  have hnn : 0 ≤ nzSq c a j f := by
    unfold nzSq
    exact integral_nonneg fun p => by positivity
  have hnn' : 0 ≤ nzSq c a j (fun p => f p - avgQ c f p) := by
    unfold nzSq
    exact integral_nonneg fun p => by positivity
  have h2 : (4 : ℝ) ^ (1 / 2 : ℝ) = 2 := by
    rw [← Real.sqrt_eq_rpow, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  calc (nzSq c a j (fun p => f p - avgQ c f p)) ^ (1 / 2 : ℝ)
      ≤ (4 * nzSq c a j f) ^ (1 / 2 : ℝ) := Real.rpow_le_rpow hnn' h4 (by norm_num)
    _ = 2 * (nzSq c a j f) ^ (1 / 2 : ℝ) := by rw [Real.mul_rpow (by norm_num) hnn, h2]

/-- **`NearLerayModeSplit` from the four leaves (proved).** -/
theorem nearLerayModeSplit_of_leaves (hsm : AvgSmooth) (hOp : AvgOpS)
    (hCS : AvgQCauchySchwarz) (hSM : AvgSliceMono) : NearLerayModeSplit :=
  nearLerayModeSplit_of hsm (avgMomentZero_of_sq (avgSqZero_of hOp (avgJensen_of hCS hSM)))
    (avgMomentOne_of hsm (avgSqZero_of hOp (avgJensen_of hCS hSM)))

/-! ### `AvgSmooth` and `AvgOpS` from `IntervalParamSmooth` -/

/-- The linear map `((s, q, η), q') ↦ (s, q', η)`. -/
def avgEmb : Profile × ℝ →L[ℝ] Profile :=
  ((ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).comp (ContinuousLinearMap.fst ℝ Profile ℝ)).prod
    ((ContinuousLinearMap.snd ℝ Profile ℝ).prod
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp
        ((ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)).comp (ContinuousLinearMap.fst ℝ Profile ℝ))))

theorem avgEmb_apply (z : Profile × ℝ) : avgEmb z = (z.1.1, z.2, z.1.2.2) := rfl

theorem avgSmooth_of (h : IntervalParamSmooth) : AvgSmooth := by
  intro c hc f hf
  have hH : ContDiff ℝ ∞ (fun z : Profile × ℝ => f (avgEmb z)) :=
    hf.smooth.comp avgEmb.contDiff
  have := (h Profile MeridC 0 c _ hH).1
  unfold avgQ
  exact this.const_smul _

theorem avgOpS_of (h : IntervalParamSmooth) : AvgOpS := by
  intro c hc f hf
  funext p
  have hH : ContDiff ℝ ∞ (fun z : Profile × ℝ => f (avgEmb z)) :=
    hf.smooth.comp avgEmb.contDiff
  obtain ⟨hs, hd⟩ := h Profile MeridC 0 c _ hH
  have hdf : DifferentiableAt ℝ f p := hf.smooth.differentiable (by simp) p
  have hchain : ∀ q : ℝ,
      fderiv ℝ (fun z : Profile × ℝ => f (avgEmb z)) (p, q) ((1, 0, 0), 0) =
        fderiv ℝ f (p.1, q, p.2.2) (1, 0, 0) := by
    intro q
    have h1 : HasFDerivAt (fun z : Profile × ℝ => f (avgEmb z))
        ((fderiv ℝ f (avgEmb (p, q))).comp avgEmb) (p, q) :=
      (hf.smooth.differentiable (by simp) (avgEmb (p, q))).hasFDerivAt.comp (p, q)
        avgEmb.hasFDerivAt
    rw [h1.fderiv]
    rfl
  have hI : DifferentiableAt ℝ (fun x : Profile => ∫ q in (0 : ℝ)..c, f (avgEmb (x, q))) p :=
    hs.differentiable (by simp) p
  have e1 : fderiv ℝ (avgQ c f) p (1, 0, 0) =
      (c⁻¹ : ℝ) • ∫ q in (0 : ℝ)..c, fderiv ℝ f (p.1, q, p.2.2) (1, 0, 0) := by
    have : avgQ c f = fun x : Profile => (c⁻¹ : ℝ) • ∫ q in (0 : ℝ)..c, f (avgEmb (x, q)) := rfl
    rw [this, fderiv_fun_const_smul hI, smul_apply, hd p (1, 0, 0)]
    simp only [hchain]
  show p.1 • fderiv ℝ (avgQ c f) p (1, 0, 0) =
    (c⁻¹ : ℝ) • ∫ q in (0 : ℝ)..c, p.1 • fderiv ℝ f (p.1, q, p.2.2) (1, 0, 0)
  rw [e1, intervalIntegral.integral_smul, smul_comm]

/-- **`NearLerayModeSplit` from the three leaves (proved).** -/
theorem nearLerayModeSplit_of_leaves' (hI : IntervalParamSmooth)
    (hCS : AvgQCauchySchwarz) (hSM : AvgSliceMono) : NearLerayModeSplit :=
  nearLerayModeSplit_of_leaves (avgSmooth_of hI) (avgOpS_of hI) hCS hSM

end UnforcedLeray.Short.PartIIa
