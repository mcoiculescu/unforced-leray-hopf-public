import UnforcedLeray.Short.PartIIa.Sub.N02_3
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.ZeroMode.PrimBound

/-!


Source of record: `the November 2 reference manuscript`, lines 1731-1733.
Prop: `ZeroWindowBound` (`Sub/N02_3.lean`). Constant: `C = 2 √π`.

Plan. Fibrewise `ZeroPrimBound` gives `‖zPrimC g‖² ≤ 2π (a + b)(s,q)` with
`a = ∫ ‖g‖²dt`, `b = ∫ t²‖g‖²dt`. Using `measureH` as the cell integral with weight `s^{-3/2}`,
the `η`-window `|η| ≤ R` has length `2R`, and the cell Fubini (`η` innermost) gives
`X ≤ 2π · 2R · ∫_cell s^{-3/2}(‖g‖² + η²‖g‖²) = 4πR (M0 + M1)`, where `M0 = ∫‖g‖²dH`,
`M1 = ∫η²‖g‖²dH`. Taking square roots and using `M0 + M1 ≤ (√M0 + √M1)²` finishes.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226

namespace ZeroWindowBoundAux

/-- Fibre integral `a(s,q) = ∫ ‖g(s,q,t)‖² dt`. -/
def aF (g : Profile → ℂ) (x : ℝ × ℝ) : ℝ := ∫ t : ℝ, ‖g (x.1, x.2, t)‖ ^ 2

/-- Fibre integral `b(s,q) = ∫ t² ‖g(s,q,t)‖² dt`. -/
def bF (g : Profile → ℂ) (x : ℝ × ℝ) : ℝ := ∫ t : ℝ, t ^ 2 * ‖g (x.1, x.2, t)‖ ^ 2

/-- The window function `s^{-3/2} (a + b)(s,q)` evaluated at `p`. -/
def Psi (g : Profile → ℂ) (p : Profile) : ℝ :=
  p.1 ^ (-(3 / 2 : ℝ)) * (aF g (p.1, p.2.1) + bF g (p.1, p.2.1))

/-- The cell integrand `s^{-3/2} (‖g‖² + η²‖g‖²)`. -/
def Uf (g : Profile → ℂ) (p : Profile) : ℝ :=
  p.1 ^ (-(3 / 2 : ℝ)) * (‖g p‖ ^ 2 + p.2.2 ^ 2 * ‖g p‖ ^ 2)

lemma cont_fiber {F : (ℝ × ℝ) × ℝ → ℝ} (hF : Continuous F) {L : ℝ}
    (hz : ∀ (x : ℝ × ℝ) (t : ℝ), L < |t| → F (x, t) = 0) :
    Continuous fun x : ℝ × ℝ => ∫ t : ℝ, F (x, t) := by
  have h1 : Continuous fun x : ℝ × ℝ => ∫ t in Icc (-L) L, F (x, t) :=
    continuous_parametric_integral_of_continuous (μ := volume) (f := fun x t => F (x, t)) hF
      isCompact_Icc
  have e : (fun x : ℝ × ℝ => ∫ t in Icc (-L) L, F (x, t))
      = fun x : ℝ × ℝ => ∫ t : ℝ, F (x, t) := by
    funext x
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro t ht
    apply hz x t
    exact not_le.1 (fun h => ht (abs_le.1 h))
  rw [e] at h1
  exact h1

lemma aF_continuous {g : Profile → ℂ} (hg : Continuous g) {L : ℝ}
    (hL : ∀ p : Profile, L < |p.2.2| → g p = 0) : Continuous (aF g) := by
  have hc : Continuous (fun z : (ℝ × ℝ) × ℝ => g (z.1.1, z.1.2, z.2)) :=
    hg.comp (f := fun z : (ℝ × ℝ) × ℝ => (z.1.1, z.1.2, z.2)) (by fun_prop)
  have hF : Continuous (fun z : (ℝ × ℝ) × ℝ => ‖g (z.1.1, z.1.2, z.2)‖ ^ 2) :=
    hc.norm.pow 2
  exact cont_fiber (L := L) hF fun x t ht => by
    show ‖g (x.1, x.2, t)‖ ^ 2 = 0
    rw [hL (x.1, x.2, t) ht]
    simp

lemma bF_continuous {g : Profile → ℂ} (hg : Continuous g) {L : ℝ}
    (hL : ∀ p : Profile, L < |p.2.2| → g p = 0) : Continuous (bF g) := by
  have hc : Continuous (fun z : (ℝ × ℝ) × ℝ => g (z.1.1, z.1.2, z.2)) :=
    hg.comp (f := fun z : (ℝ × ℝ) × ℝ => (z.1.1, z.1.2, z.2)) (by fun_prop)
  have hF : Continuous (fun z : (ℝ × ℝ) × ℝ => z.2 ^ 2 * ‖g (z.1.1, z.1.2, z.2)‖ ^ 2) :=
    (continuous_snd.pow 2).mul (hc.norm.pow 2)
  exact cont_fiber (L := L) hF fun x t ht => by
    show t ^ 2 * ‖g (x.1, x.2, t)‖ ^ 2 = 0
    rw [hL (x.1, x.2, t) ht]
    simp

lemma aF_zero_of {g : Profile → ℂ} {s0 s1 L : ℝ}
    (hsup : ∀ p : Profile, g p ≠ 0 → p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L)
    {x : ℝ × ℝ} (hx : x.1 ∉ Icc s0 s1) : aF g x = 0 := by
  have h0 : ∀ t : ℝ, g (x.1, x.2, t) = 0 := fun t => by
    by_contra h
    exact hx (hsup _ h).1
  simp [aF, h0]

lemma bF_zero_of {g : Profile → ℂ} {s0 s1 L : ℝ}
    (hsup : ∀ p : Profile, g p ≠ 0 → p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L)
    {x : ℝ × ℝ} (hx : x.1 ∉ Icc s0 s1) : bF g x = 0 := by
  have h0 : ∀ t : ℝ, g (x.1, x.2, t) = 0 := fun t => by
    by_contra h
    exact hx (hsup _ h).1
  simp [bF, h0]

lemma fiber_props {g : Profile → ℂ} (hgc : Continuous g) {L : ℝ}
    (hL : ∀ p : Profile, L < |p.2.2| → g p = 0) (s q : ℝ) :
    Integrable (fun t : ℝ => ‖g (s, q, t)‖ ^ 2) ∧
      Integrable (fun t : ℝ => t ^ 2 * ‖g (s, q, t)‖ ^ 2) := by
  obtain ⟨-, h1, h2⟩ := ZeroPrimBoundAux.fiber_integrable (fun t : ℝ => g (s, q, t))
    (hgc.comp (f := fun t : ℝ => ((s, q, t) : Profile)) (by fun_prop)) L
    (fun t ht => hL (s, q, t) ht)
  exact ⟨h1, h2⟩

lemma psi_contOn {g : Profile → ℂ} (hgc : Continuous g) {L s0 : ℝ} (hs0 : 0 < s0)
    (hL : ∀ p : Profile, L < |p.2.2| → g p = 0) (K : Set Profile)
    (hK : ∀ p ∈ K, s0 ≤ p.1) : ContinuousOn (Psi g) K := by
  have hpair : Continuous fun p : Profile => (p.1, p.2.1) := by fun_prop
  have ha : Continuous fun p : Profile => aF g (p.1, p.2.1) :=
    (aF_continuous hgc hL).comp hpair
  have hb : Continuous fun p : Profile => bF g (p.1, p.2.1) :=
    (bF_continuous hgc hL).comp hpair
  have hw : ContinuousOn (fun p : Profile => p.1 ^ (-(3 / 2 : ℝ))) K :=
    ContinuousOn.rpow_const continuous_fst.continuousOn
      (fun p hp => Or.inl (lt_of_lt_of_le hs0 (hK p hp)).ne')
  unfold Psi
  exact hw.mul (ha.add hb).continuousOn

lemma uf_contOn {g : Profile → ℂ} (hgc : Continuous g) {s0 : ℝ} (hs0 : 0 < s0)
    (K : Set Profile) (hK : ∀ p ∈ K, s0 ≤ p.1) : ContinuousOn (Uf g) K := by
  have hw : ContinuousOn (fun p : Profile => p.1 ^ (-(3 / 2 : ℝ))) K :=
    ContinuousOn.rpow_const continuous_fst.continuousOn
      (fun p hp => Or.inl (lt_of_lt_of_le hs0 (hK p hp)).ne')
  have hg2 : Continuous fun p : Profile => ‖g p‖ ^ 2 + p.2.2 ^ 2 * ‖g p‖ ^ 2 := by fun_prop
  unfold Uf
  exact hw.mul hg2.continuousOn

lemma aF_nonneg (g : Profile → ℂ) (x : ℝ × ℝ) : 0 ≤ aF g x := by
  simp only [aF]
  exact integral_nonneg fun t => sq_nonneg _

lemma bF_nonneg (g : Profile → ℂ) (x : ℝ × ℝ) : 0 ≤ bF g x := by
  simp only [bF]
  exact integral_nonneg fun t => by positivity

/-- Fibrewise bound: `‖zPrimC g p‖² ≤ 2π (a + b)(s,q)`. -/
lemma pointwise_bound {g : Profile → ℂ} (hg : ContDiff ℝ ∞ g)
    (hband : ∃ s0 s1 L : ℝ, 0 < s0 ∧ ∀ p : Profile, g p ≠ 0 → p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L)
    (p : Profile) :
    ‖zPrimC g p‖ ^ 2 ≤ 2 * Real.pi * (aF g (p.1, p.2.1) + bF g (p.1, p.2.1)) := by
  have h0 := zeroPrimBound g hg hband p
  simp only [← Real.sqrt_eq_rpow] at h0
  show ‖zPrimC g p‖ ^ 2 ≤ 2 * Real.pi *
    ((∫ t : ℝ, ‖g (p.1, p.2.1, t)‖ ^ 2) + (∫ t : ℝ, t ^ 2 * ‖g (p.1, p.2.1, t)‖ ^ 2))
  have hα : 0 ≤ ∫ t : ℝ, ‖g (p.1, p.2.1, t)‖ ^ 2 := integral_nonneg fun t => sq_nonneg _
  have hβ : 0 ≤ ∫ t : ℝ, t ^ 2 * ‖g (p.1, p.2.1, t)‖ ^ 2 :=
    integral_nonneg fun t => by positivity
  set α := ∫ t : ℝ, ‖g (p.1, p.2.1, t)‖ ^ 2 with hαd
  set β := ∫ t : ℝ, t ^ 2 * ‖g (p.1, p.2.1, t)‖ ^ 2 with hβd
  have hpi : 0 ≤ Real.pi := Real.pi_pos.le
  have h2 : ‖zPrimC g p‖ ^ 2 ≤ (Real.sqrt Real.pi * (Real.sqrt α + Real.sqrt β)) ^ 2 := by
    gcongr
  have h3 : (Real.sqrt Real.pi * (Real.sqrt α + Real.sqrt β)) ^ 2
      = Real.pi * (Real.sqrt α + Real.sqrt β) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hpi]
  have h5 : Real.pi * α = Real.pi * Real.sqrt α ^ 2 := by rw [Real.sq_sqrt hα]
  have h6 : Real.pi * β = Real.pi * Real.sqrt β ^ 2 := by rw [Real.sq_sqrt hβ]
  have h4 : Real.pi * (Real.sqrt α + Real.sqrt β) ^ 2 ≤ 2 * Real.pi * (α + β) := by
    nlinarith [mul_nonneg hpi (sq_nonneg (Real.sqrt α - Real.sqrt β)), h5, h6]
  linarith [h2, h3, h4]

lemma measureH_integral_real (c : ℝ) (G : Profile → ℝ) :
    ∫ p, G p ∂(measureH c) = ∫ p in cell c, (p.1 ^ (-(3 / 2 : ℝ)) : ℝ) * G p := by
  rw [measureH, integral_withDensity_eq_integral_toReal_smul measurable_weightH
    (ae_weightH_lt_top c), cellMeasure]
  refine setIntegral_congr_fun (measurableSet_cell c) fun p hp => ?_
  have hp1 : 0 < p.1 := hp.1
  simp only [weightH, ENNReal.toReal_ofReal (Real.rpow_nonneg hp1.le _), smul_eq_mul]

lemma cellFubiniR (c : ℝ) (G : Profile → ℝ) (hG : IntegrableOn G (cell c)) :
    ∫ p in cell c, G p =
      ∫ s in Ioi (0 : ℝ), ∫ q in Ioc (0 : ℝ) c, ∫ η : ℝ, G (s, q, η) := by
  have hvol : (volume : Measure Profile) =
      (volume : Measure ℝ).prod ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
    rw [Measure.volume_eq_prod ℝ (ℝ × ℝ), Measure.volume_eq_prod ℝ ℝ]
  have hcell : cell c = Ioi (0 : ℝ) ×ˢ (Ioc (0 : ℝ) c ×ˢ (univ : Set ℝ)) := rfl
  rw [hvol, hcell] at hG
  rw [hvol, hcell]
  have hG2 : Integrable G (((volume : Measure ℝ).restrict (Ioi (0 : ℝ))).prod
      (((volume : Measure ℝ).prod (volume : Measure ℝ)).restrict
        (Ioc (0 : ℝ) c ×ˢ (univ : Set ℝ)))) := by
    rw [Measure.prod_restrict]
    exact hG
  have hae := hG2.prod_right_ae
  rw [setIntegral_prod G hG]
  refine integral_congr_ae ?_
  filter_upwards [hae] with s hs
  rw [setIntegral_prod (fun y : ℝ × ℝ => G (s, y)) hs, Measure.restrict_univ]

lemma integrableOn_cell_of_zero (c : ℝ) {K : Set Profile} {F : Profile → ℝ}
    (hF : IntegrableOn F K) (hz : ∀ p ∈ cell c, p ∉ K → F p = 0) :
    IntegrableOn F (cell c) :=
  IntegrableOn.of_forall_sdiff_eq_zero hF (measurableSet_cell c) fun x hx => hz x hx.1 hx.2

/-- The `η`-integral of the window part of `Psi`: the window has length `2R`. -/
lemma phi_inner {g : Profile → ℂ} {R : ℝ} (hR : 0 ≤ R) (s q : ℝ) :
    ∫ η : ℝ, {p : Profile | |p.2.2| ≤ R}.indicator (Psi g) (s, q, η)
      = 2 * R * (s ^ (-(3 / 2 : ℝ)) * (aF g (s, q) + bF g (s, q))) := by
  have e : ∀ η : ℝ, {p : Profile | |p.2.2| ≤ R}.indicator (Psi g) (s, q, η)
      = (Icc (-R) R).indicator
          (fun _ : ℝ => s ^ (-(3 / 2 : ℝ)) * (aF g (s, q) + bF g (s, q))) η := by
    intro η
    simp [Set.indicator_apply, Psi, abs_le]
  simp only [e]
  rw [integral_indicator_const _ measurableSet_Icc, Real.volume_real_Icc_of_le (by linarith),
    smul_eq_mul]
  ring

/-- The `η`-integral of the cell integrand `Uf`. -/
lemma uf_inner {g : Profile → ℂ} (hgc : Continuous g) {L : ℝ}
    (hL : ∀ p : Profile, L < |p.2.2| → g p = 0) (s q : ℝ) :
    ∫ η : ℝ, Uf g (s, q, η) = s ^ (-(3 / 2 : ℝ)) * (aF g (s, q) + bF g (s, q)) := by
  obtain ⟨h1, h2⟩ := fiber_props hgc hL s q
  have e : ∀ η : ℝ, Uf g (s, q, η)
      = s ^ (-(3 / 2 : ℝ)) * (‖g (s, q, η)‖ ^ 2 + η ^ 2 * ‖g (s, q, η)‖ ^ 2) :=
    fun η => rfl
  simp only [e]
  rw [integral_const_mul, integral_add h1 h2]
  rfl

end ZeroWindowBoundAux

open ZeroWindowBoundAux in
/-- **Window bound (`ZeroWindowBound`, task `PartII-a:N02/3/5`).** -/
theorem zeroWindowBound : ZeroWindowBound := by
  unfold ZeroWindowBound
  refine ⟨2 * Real.sqrt Real.pi, by positivity, ?_⟩
  intro c R g hc hR hg hband
  obtain ⟨s0, s1, L, hs0, hsup⟩ := hband
  have hgc : Continuous g := hg.continuous
  have hL : ∀ p : Profile, L < |p.2.2| → g p = 0 := fun p hp => by
    by_contra h
    exact absurd (hsup p h).2 (not_le.2 hp)
  have hband' : ∃ s0 s1 L : ℝ, 0 < s0 ∧
      ∀ p : Profile, g p ≠ 0 → p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L :=
    ⟨s0, s1, L, hs0, hsup⟩
  -- compact boxes
  have hKR : IsCompact (Icc s0 s1 ×ˢ (Icc 0 c ×ˢ Icc (-R) R)) :=
    isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hKL : IsCompact (Icc s0 s1 ×ˢ (Icc 0 c ×ˢ Icc (-L) L)) :=
    isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hmeas : MeasurableSet {p : Profile | |p.2.2| ≤ R} :=
    measurableSet_le (by fun_prop) measurable_const
  -- `g` vanishes on the cell outside the band box
  have gzeroL : ∀ p ∈ cell c, p ∉ (Icc s0 s1 ×ˢ (Icc 0 c ×ˢ Icc (-L) L)) → g p = 0 := by
    intro p hp hpK
    by_contra h
    obtain ⟨h1, h2⟩ := hsup p h
    exact hpK ⟨h1, Ioc_subset_Icc_self hp.2.1, abs_le.1 h2⟩
  -- integrability of the window part
  have hPsiK : ContinuousOn (Psi g) (Icc s0 s1 ×ˢ (Icc 0 c ×ˢ Icc (-R) R)) :=
    psi_contOn hgc hs0 hL _ (fun p hp => hp.1.1)
  have hPhiI : IntegrableOn ({p : Profile | |p.2.2| ≤ R}.indicator (Psi g))
      (Icc s0 s1 ×ˢ (Icc 0 c ×ˢ Icc (-R) R)) :=
    (hPsiK.integrableOn_compact hKR).indicator hmeas
  have hPhiZ : ∀ p ∈ cell c, p ∉ (Icc s0 s1 ×ˢ (Icc 0 c ×ˢ Icc (-R) R)) →
      {p : Profile | |p.2.2| ≤ R}.indicator (Psi g) p = 0 := by
    intro p hp hpK
    by_cases h1 : p.1 ∈ Icc s0 s1
    · have h2 : ¬ |p.2.2| ≤ R := fun h => hpK ⟨h1, Ioc_subset_Icc_self hp.2.1, abs_le.1 h⟩
      simp [Set.indicator_apply, h2]
    · have h0 : Psi g p = 0 := by
        simp only [Psi, aF_zero_of (x := (p.1, p.2.1)) hsup h1,
          bF_zero_of (x := (p.1, p.2.1)) hsup h1, add_zero, mul_zero]
      simp [Set.indicator_apply, h0]
  have hPhiInt : IntegrableOn ({p : Profile | |p.2.2| ≤ R}.indicator (Psi g)) (cell c) :=
    integrableOn_cell_of_zero c hPhiI hPhiZ
  -- integrability of the cell integrands `Uf`, `‖g‖²`, `η²‖g‖²`
  have hwL : ContinuousOn (fun p : Profile => p.1 ^ (-(3 / 2 : ℝ)))
      (Icc s0 s1 ×ˢ (Icc 0 c ×ˢ Icc (-L) L)) :=
    ContinuousOn.rpow_const continuous_fst.continuousOn
      (fun p hp => Or.inl (lt_of_lt_of_le hs0 hp.1.1).ne')
  have hUint : IntegrableOn (Uf g) (cell c) :=
    integrableOn_cell_of_zero c
      ((uf_contOn hgc hs0 _ (fun p hp => hp.1.1)).integrableOn_compact hKL)
      (fun p hp hpK => by
        unfold Uf
        rw [gzeroL p hp hpK]
        simp)
  have hAc : IntegrableOn (fun p : Profile => p.1 ^ (-(3 / 2 : ℝ)) * ‖g p‖ ^ 2) (cell c) :=
    integrableOn_cell_of_zero c
      ((hwL.mul (by fun_prop : Continuous fun p : Profile => ‖g p‖ ^ 2).continuousOn).integrableOn_compact hKL)
      (fun p hp hpK => by
        rw [gzeroL p hp hpK]
        simp)
  have hBc : IntegrableOn (fun p : Profile => p.1 ^ (-(3 / 2 : ℝ)) * (p.2.2 ^ 2 * ‖g p‖ ^ 2))
      (cell c) :=
    integrableOn_cell_of_zero c
      ((hwL.mul (by fun_prop : Continuous fun p : Profile => p.2.2 ^ 2 * ‖g p‖ ^ 2).continuousOn).integrableOn_compact hKL)
      (fun p hp hpK => by
        rw [gzeroL p hp hpK]
        simp)
  -- splitting of the cell integral of `Uf`
  have hUsplit : ∫ p in cell c, Uf g p
      = (∫ p, ‖g p‖ ^ 2 ∂(measureH c)) + (∫ p, p.2.2 ^ 2 * ‖g p‖ ^ 2 ∂(measureH c)) := by
    have e0 : ∫ p, ‖g p‖ ^ 2 ∂(measureH c)
        = ∫ p in cell c, p.1 ^ (-(3 / 2 : ℝ)) * ‖g p‖ ^ 2 :=
      measureH_integral_real c (fun p => ‖g p‖ ^ 2)
    have e1 : ∫ p, p.2.2 ^ 2 * ‖g p‖ ^ 2 ∂(measureH c)
        = ∫ p in cell c, p.1 ^ (-(3 / 2 : ℝ)) * (p.2.2 ^ 2 * ‖g p‖ ^ 2) :=
      measureH_integral_real c (fun p => p.2.2 ^ 2 * ‖g p‖ ^ 2)
    rw [e0, e1, ← integral_add hAc hBc]
    congr 1
    funext p
    unfold Uf
    ring
  -- the cell Fubini computation
  have hPhiEq : ∫ p in cell c, {p : Profile | |p.2.2| ≤ R}.indicator (Psi g) p
      = 2 * R * ∫ p in cell c, Uf g p := by
    rw [cellFubiniR c _ hPhiInt, cellFubiniR c _ hUint]
    simp only [phi_inner hR.le, uf_inner hgc hL]
    simp only [integral_const_mul]
  -- pointwise comparison on the cell
  have step2 : ∫ p in cell c, p.1 ^ (-(3 / 2 : ℝ))
        * {p : Profile | |p.2.2| ≤ R}.indicator (fun p => ‖zPrimC g p‖ ^ 2) p
      ≤ ∫ p in cell c, 2 * Real.pi * {p : Profile | |p.2.2| ≤ R}.indicator (Psi g) p := by
    apply integral_mono_of_nonneg
    · filter_upwards [ae_restrict_mem (measurableSet_cell c)] with p hp
      have hw : 0 ≤ p.1 ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg hp.1.le _
      have hI : 0 ≤ {p : Profile | |p.2.2| ≤ R}.indicator (fun p => ‖zPrimC g p‖ ^ 2) p := by
        by_cases h : |p.2.2| ≤ R
        · rw [Set.indicator_of_mem (show p ∈ {p : Profile | |p.2.2| ≤ R} from h)]
          positivity
        · simp [h]
      exact mul_nonneg hw hI
    · exact Integrable.const_mul hPhiInt _
    · filter_upwards [ae_restrict_mem (measurableSet_cell c)] with p hp
      by_cases h : |p.2.2| ≤ R
      · have hk := pointwise_bound hg hband' p
        have hw : 0 ≤ p.1 ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg hp.1.le _
        rw [Set.indicator_of_mem (show p ∈ {p : Profile | |p.2.2| ≤ R} from h),
          Set.indicator_of_mem (show p ∈ {p : Profile | |p.2.2| ≤ R} from h)]
        unfold Psi
        calc p.1 ^ (-(3 / 2 : ℝ)) * ‖zPrimC g p‖ ^ 2
            ≤ p.1 ^ (-(3 / 2 : ℝ)) * (2 * Real.pi * (aF g (p.1, p.2.1) + bF g (p.1, p.2.1))) :=
              mul_le_mul_of_nonneg_left hk hw
          _ = 2 * Real.pi * (p.1 ^ (-(3 / 2 : ℝ)) * (aF g (p.1, p.2.1) + bF g (p.1, p.2.1))) := by
              ring
      · simp [h]
  -- assemble the main inequality
  have hMain : ∫ p, {p : Profile | |p.2.2| ≤ R}.indicator (fun p => ‖zPrimC g p‖ ^ 2) p
        ∂(measureH c)
      ≤ 2 * Real.pi * (2 * R * ((∫ p, ‖g p‖ ^ 2 ∂(measureH c))
          + (∫ p, p.2.2 ^ 2 * ‖g p‖ ^ 2 ∂(measureH c)))) := by
    have hI : ∫ p, {p : Profile | |p.2.2| ≤ R}.indicator (fun p => ‖zPrimC g p‖ ^ 2) p
        ∂(measureH c)
        = ∫ p in cell c, p.1 ^ (-(3 / 2 : ℝ))
          * {p : Profile | |p.2.2| ≤ R}.indicator (fun p => ‖zPrimC g p‖ ^ 2) p :=
      measureH_integral_real c _
    rw [hI, ← hUsplit]
    calc _ ≤ _ := step2
      _ = 2 * Real.pi * ∫ p in cell c, {p : Profile | |p.2.2| ≤ R}.indicator (Psi g) p :=
          integral_const_mul _ _
      _ = 2 * Real.pi * (2 * R * ∫ p in cell c, Uf g p) := by rw [hPhiEq]
  -- final square-root estimate
  simp only [← Real.sqrt_eq_rpow]
  set X := ∫ p, {p : Profile | |p.2.2| ≤ R}.indicator (fun p => ‖zPrimC g p‖ ^ 2) p
    ∂(measureH c) with hXd
  set M0 := ∫ p, ‖g p‖ ^ 2 ∂(measureH c) with hM0d
  set M1 := ∫ p, p.2.2 ^ 2 * ‖g p‖ ^ 2 ∂(measureH c) with hM1d
  have hM0 : 0 ≤ M0 := integral_nonneg fun p => sq_nonneg _
  have hM1 : 0 ≤ M1 := integral_nonneg fun p => by positivity
  have hR0 : 0 ≤ R := hR.le
  have hpi0 : 0 ≤ Real.pi := Real.pi_pos.le
  have e : (2 * Real.sqrt Real.pi * Real.sqrt R * (Real.sqrt M0 + Real.sqrt M1)) ^ 2
      = 4 * Real.pi * R * (Real.sqrt M0 + Real.sqrt M1) ^ 2 := by
    simp only [mul_pow, Real.sq_sqrt hpi0, Real.sq_sqrt hR0]
    ring
  have h2 : M0 + M1 ≤ (Real.sqrt M0 + Real.sqrt M1) ^ 2 := by
    nlinarith [Real.sq_sqrt hM0, Real.sq_sqrt hM1,
      mul_nonneg (Real.sqrt_nonneg M0) (Real.sqrt_nonneg M1)]
  have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 4 * Real.pi * R)
  have key : X ≤ (2 * Real.sqrt Real.pi * Real.sqrt R * (Real.sqrt M0 + Real.sqrt M1)) ^ 2 := by
    rw [e]
    nlinarith [h3, hMain]
  calc Real.sqrt X ≤ Real.sqrt ((2 * Real.sqrt Real.pi * Real.sqrt R
          * (Real.sqrt M0 + Real.sqrt M1)) ^ 2) := Real.sqrt_le_sqrt key
    _ = 2 * Real.sqrt Real.pi * Real.sqrt R * (Real.sqrt M0 + Real.sqrt M1) :=
          Real.sqrt_sq (by positivity)

end UnforcedLeray.Short.PartIIa
