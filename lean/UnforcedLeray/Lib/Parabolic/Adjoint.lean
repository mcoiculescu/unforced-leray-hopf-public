import UnforcedLeray.Lib.Parabolic.L2Op
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# The transpose of `∂_i∂_j (∂_t - νΔ)^{-1}`: time reversal (INF02 T6/T7)


step 7 ("duality gives `2 ≤ q < ∞`; the adjoint kernel `K(-X)` satisfies the same estimates by
`t ↦ -t`"). Manuscript: eq:free-stress-11 (`paper/main.tex` lines 7447–7477, blueprint unit
B0423).

* `trev (t, x) = (-t, x)`, a measure-preserving linear involution of `ℝ × ℝ^d`.
* `sD2_comm`: `∂_i∂_j f = ∂_j∂_i f` for tests; `integral_mul_sD2`: two spatial integrations by
  parts, `∫ φ ∂_i∂_j ψ = ∫ (∂_i∂_j φ) ψ`.
* `backTest ν i j g = (∂_i∂_j H_ν ⋆ (g ∘ trev)) ∘ trev`, the backward operator on tests.
* `integral_mul_secondDerivTest_eq` (**transposition on tests**):
  `∫ g · ∂_i∂_j(H_ν ⋆ f) = ∫ f · backTest ν i j g`.
* `reflL2`, `backOp = reflL2 ∘ secondDerivOp ∘ reflL2`, `backOp_toLp`, and
  `integral_secondDerivOp_mul` (**transposition on `L²`**):
  `∫ (T F) G = ∫ F (backOp G)` for all `F, G ∈ L²`.
-/

noncomputable section

set_option autoImplicit false

namespace UnforcedLeray.Parabolic

open MeasureTheory Real Set Filter
open scoped ENNReal NNReal ContDiff Topology RealInnerProductSpace

open UnforcedLeray.Gaussian (Euc gaussKernel)

variable {d : ℕ}

section TimeReversal

/-- Time reversal `(t, x) ↦ (-t, x)` as a continuous linear map. -/
def trevCLM (d : ℕ) : PS d →L[ℝ] PS d :=
  (-(ContinuousLinearMap.fst ℝ ℝ (Euc d))).prod (ContinuousLinearMap.snd ℝ ℝ (Euc d))

/-- Time reversal `(t, x) ↦ (-t, x)`. -/
def trev (X : PS d) : PS d := (-X.1, X.2)

theorem trev_eq_clm : (trev : PS d → PS d) = trevCLM d := by
  funext X; rfl

@[simp] theorem trev_trev (X : PS d) : trev (trev X) = X := by
  simp [trev]

theorem trev_sub (X Y : PS d) : trev (X - Y) = trev X - trev Y := by
  simp only [trev, Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk, neg_sub, sub_neg_eq_add]
  ext <;> simp; ring

theorem measurePreserving_trev : MeasurePreserving (trev : PS d → PS d) volume volume := by
  have h := (Measure.measurePreserving_neg (volume : Measure ℝ)).prod
    (MeasurePreserving.id (volume : Measure (Euc d)))
  exact h

theorem continuous_trev : Continuous (trev : PS d → PS d) := by
  rw [trev_eq_clm]; exact (trevCLM d).continuous

theorem IsSTTest.comp_trev {g : PS d → ℝ} (hg : IsSTTest g) : IsSTTest (g ∘ trev) := by
  refine ⟨?_, ?_⟩
  · rw [trev_eq_clm]; exact hg.1.comp (trevCLM d).contDiff
  · have : g ∘ trev = g ∘ (Homeomorph.mk ⟨trev, trev, trev_trev, trev_trev⟩ continuous_trev
      continuous_trev) := rfl
    rw [this]
    exact hg.2.comp_homeomorph _

theorem dirD_comp_trev {g : PS d → ℝ} (hg : Differentiable ℝ g) (i : Fin d) :
    sD i (g ∘ trev) = (sD i g) ∘ trev := by
  funext X
  simp only [sD, dirD, Function.comp_apply]
  have h : HasFDerivAt (g ∘ trev) ((fderiv ℝ g (trev X)).comp (trevCLM d)) X := by
    rw [trev_eq_clm]; exact (hg (trevCLM d X)).hasFDerivAt.comp X (trevCLM d).hasFDerivAt
  rw [h.fderiv]
  simp [trevCLM]

theorem sD2_comp_trev {g : PS d → ℝ} (hg : IsSTTest g) (i j : Fin d) :
    sD2 i j (g ∘ trev) = (sD2 i j g) ∘ trev := by
  unfold sD2
  rw [dirD_comp_trev hg.differentiable j, dirD_comp_trev (hg.dirD _).differentiable i]

/-- `(s, y) ↦ (s, -y)`, a measure-preserving involution. -/
def sflip (d : ℕ) : PS d ≃ᵐ PS d :=
  MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) (MeasurableEquiv.neg (Euc d))

theorem sflip_apply (Y : PS d) : sflip d Y = (Y.1, -Y.2) := rfl

theorem measurePreserving_sflip : MeasurePreserving (sflip d) volume volume :=
  (MeasurePreserving.id (volume : Measure ℝ)).prod (Measure.measurePreserving_neg _)

theorem causalHeat_sflip (ν : ℝ) (Y : PS d) : causalHeat ν (sflip d Y) = causalHeat ν Y := by
  unfold causalHeat
  rw [sflip_apply]
  simp [Gaussian.gaussKernel_neg]

end TimeReversal

section Symmetry

theorem dirD_dirD_eq {f : PS d → ℝ} (hf : IsSTTest f) (u w : PS d) (X : PS d) :
    dirD u (dirD w f) X = fderiv ℝ (fderiv ℝ f) X u w := by
  have hd : Differentiable ℝ (fderiv ℝ f) :=
    (hf.1.fderiv_right (m := 1) (by simp)).differentiable (by simp)
  show fderiv ℝ (fun y => fderiv ℝ f y w) X u = _
  rw [fderiv_clm_apply (hd X) (differentiableAt_const w)]
  simp

/-- Symmetry of second spatial derivatives of tests. -/
theorem sD2_comm {f : PS d → ℝ} (hf : IsSTTest f) (i j : Fin d) : sD2 i j f = sD2 j i f := by
  funext X
  unfold sD2 sD
  rw [dirD_dirD_eq hf, dirD_dirD_eq hf]
  exact (hf.1.contDiffAt.isSymmSndFDerivAt (by simp)) _ _

/-- Spatial integration by parts for tests: `∫ φ ∂_v ψ = -∫ (∂_v φ) ψ`. -/
theorem integral_mul_dirD {φ ψ : PS d → ℝ} (hφ : IsSTTest φ) (hψ : IsSTTest ψ) (v : PS d) :
    ∫ X, φ X * dirD v ψ X = -∫ X, dirD v φ X * ψ X := by
  have h1 : Integrable (fun X => fderiv ℝ φ X v * ψ X) volume :=
    ((hφ.dirD v).continuous.mul hψ.continuous).integrable_of_hasCompactSupport hψ.2.mul_left
  have h2 : Integrable (fun X => φ X * fderiv ℝ ψ X v) volume :=
    (hφ.continuous.mul (hψ.dirD v).continuous).integrable_of_hasCompactSupport hφ.2.mul_right
  have h3 : Integrable (fun X => φ X * ψ X) volume :=
    (hφ.continuous.mul hψ.continuous).integrable_of_hasCompactSupport hφ.2.mul_right
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable h1 h2 h3
    (fun X _ => hφ.differentiable X) (fun X _ => hψ.differentiable X)

/-- Two spatial integrations by parts: `∫ φ ∂_i∂_j ψ = ∫ (∂_i∂_j φ) ψ`. -/
theorem integral_mul_sD2 {φ ψ : PS d → ℝ} (hφ : IsSTTest φ) (hψ : IsSTTest ψ) (i j : Fin d) :
    ∫ X, φ X * sD2 i j ψ X = ∫ X, sD2 i j φ X * ψ X := by
  unfold sD2 sD
  rw [integral_mul_dirD hφ (hψ.dirD _), ← integral_neg]
  have h2 := integral_mul_dirD (hφ.dirD (sdir i)) hψ (sdir j)
  have e : ∀ X, -(dirD (sdir i) φ X * dirD (sdir j) ψ X) =
      -(dirD (sdir i) φ X * dirD (sdir j) ψ X) := fun X => rfl
  calc ∫ X, -(dirD (sdir i) φ X * dirD (sdir j) ψ X)
      = -∫ X, dirD (sdir i) φ X * dirD (sdir j) ψ X := integral_neg _
    _ = ∫ X, dirD (sdir j) (dirD (sdir i) φ) X * ψ X := by rw [h2, neg_neg]
    _ = ∫ X, dirD (sdir i) (dirD (sdir j) φ) X * ψ X := by
        have := sD2_comm hφ j i
        unfold sD2 sD at this
        rw [this]

end Symmetry

section Transpose

variable {ν : ℝ}

/-- The backward operator on tests, `g ↦ (∂_i∂_j H_ν ⋆ (g ∘ trev)) ∘ trev`. -/
def backTest (ν : ℝ) (i j : Fin d) (g : PS d → ℝ) : PS d → ℝ :=
  secondDerivTest ν i j (g ∘ trev) ∘ trev

theorem backTest_eq (hν : 0 < ν) {g : PS d → ℝ} (hg : IsSTTest g) (i j : Fin d) (Z : PS d) :
    backTest ν i j g Z = ∫ Y, causalHeat ν Y * sD2 i j g (Z + Y) := by
  unfold backTest secondDerivTest duhamel
  simp only [Function.comp, sD2_comp_trev hg i j]
  have h := (measurePreserving_sflip (d := d)).integral_comp'
    (fun W => causalHeat ν W * sD2 i j g (trev (trev Z - W)))
  rw [← h]
  congr 1; funext Y
  rw [causalHeat_sflip]
  congr 2
  rw [sflip_apply]
  ext <;> simp [trev, add_comm]

theorem integrable_heat_far (hν : 0 < ν) {T : ℝ} :
    Integrable ((Icc (-T) T ×ˢ (univ : Set (Euc d))).indicator (causalHeat ν)) volume :=
  (integrable_indicator_iff (measurableSet_Icc.prod MeasurableSet.univ)).2
    (integrableOn_causalHeat hν T)

/-- **Transposition on tests.** `∫ g · ∂_i∂_j(H_ν ⋆ f) = ∫ f · backTest ν i j g`. -/
theorem integral_mul_secondDerivTest_eq (hν : 0 < ν) {f g : PS d → ℝ} (hf : IsSTTest f)
    (hg : IsSTTest g) (i j : Fin d) :
    ∫ X, g X * secondDerivTest ν i j f X = ∫ Z, f Z * backTest ν i j g Z := by
  set A := sD2 i j f with hAdef
  set B := sD2 i j g with hBdef
  have hA : IsSTTest A := hf.sD2 i j
  have hB : IsSTTest B := hg.sD2 i j
  obtain ⟨Ma, -, hMa⟩ := hA.bounded
  obtain ⟨Mb, -, hMb⟩ := hB.bounded
  obtain ⟨Ra, -, hRa⟩ := hA.timeBound
  obtain ⟨Rb, -, hRb⟩ := hB.timeBound
  obtain ⟨Rg, -, hRg⟩ := hg.timeBound
  obtain ⟨Rf, -, hRf⟩ := hf.timeBound
  have hHm := measurable_causalHeat (d := d) ν
  have hMa0 : 0 ≤ Ma := (abs_nonneg _).trans (hMa 0)
  have hMb0 : 0 ≤ Mb := (abs_nonneg _).trans (hMb 0)
  have hind0 : ∀ {T : ℝ} (Y : PS d),
      0 ≤ (Icc (-T) T ×ˢ (univ : Set (Euc d))).indicator (causalHeat ν) Y :=
    fun Y => indicator_nonneg (fun Y _ => causalHeat_nonneg hν Y) Y
  -- first swap
  have hint1 : Integrable (Function.uncurry fun X Y : PS d => g X * (causalHeat ν Y * A (X - Y)))
      (volume.prod volume) := by
    refine (hg.integrable.norm.mul_prod
      ((integrable_heat_far (d := d) hν (T := Rg + Ra)).const_mul Ma)).mono' ?_
      (Eventually.of_forall fun p => ?_)
    · exact (hg.continuous.measurable.comp measurable_fst |>.mul
        ((hHm.comp measurable_snd).mul (hA.continuous.measurable.comp
          (measurable_fst.sub measurable_snd)))).aestronglyMeasurable
    · simp only [Function.uncurry, norm_mul, Real.norm_eq_abs]
      by_cases h0 : g p.1 = 0 ∨ A (p.1 - p.2) = 0
      · have hl : |g p.1| * (|causalHeat ν p.2| * |A (p.1 - p.2)|) = 0 := by
          rcases h0 with h0 | h0 <;> simp [h0]
        rw [hl]
        exact mul_nonneg (abs_nonneg _) (mul_nonneg hMa0 (hind0 _))
      push Not at h0
      have h1 := hRg _ h0.1
      have h2 := hRa _ h0.2
      simp only [Prod.fst_sub] at h2
      have hY : p.2 ∈ Icc (-(Rg + Ra)) (Rg + Ra) ×ˢ (univ : Set (Euc d)) := by
        refine ⟨⟨?_, ?_⟩, mem_univ _⟩ <;>
        · cases abs_le.1 h1; cases abs_le.1 h2; linarith
      rw [indicator_of_mem hY, abs_of_nonneg (causalHeat_nonneg hν _)]
      have := hMa (p.1 - p.2)
      calc |g p.1| * (causalHeat ν p.2 * |A (p.1 - p.2)|)
          ≤ |g p.1| * (causalHeat ν p.2 * Ma) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left this (causalHeat_nonneg hν _))
              (abs_nonneg _)
        _ = |g p.1| * (Ma * causalHeat ν p.2) := by ring
  have L1 : ∫ X, g X * secondDerivTest ν i j f X =
      ∫ Y, causalHeat ν Y * ∫ X, g X * A (X - Y) := by
    unfold secondDerivTest duhamel
    simp_rw [← integral_const_mul]
    rw [integral_integral_swap hint1]
    congr 1; funext Y; congr 1; funext X; ring
  -- translation and integration by parts
  have L2 : ∀ Y, ∫ X, g X * A (X - Y) = ∫ Z, B (Z + Y) * f Z := by
    intro Y
    rw [← integral_add_right_eq_self (fun X => g X * A (X - Y)) Y]
    simp only [add_sub_cancel_right]
    have hgY : IsSTTest (fun Z => g (Z + Y)) := by
      refine ⟨hg.1.comp (contDiff_id.add contDiff_const), ?_⟩
      exact hg.2.comp_homeomorph (Homeomorph.addRight Y)
    rw [integral_mul_sD2 hgY hf i j]
    congr 1; funext Z
    congr 1
    have hd : ∀ (φ : PS d → ℝ) (v : PS d), Differentiable ℝ φ →
        dirD v (fun Z => φ (Z + Y)) = fun Z => dirD v φ (Z + Y) := by
      intro φ v hφ
      funext Z
      simp only [dirD]
      rw [fderiv_comp_add_right]
    unfold sD2 sD
    rw [hd g _ hg.differentiable, hd _ _ (hg.dirD _).differentiable]
  -- second swap
  have hint2 : Integrable (Function.uncurry fun Y Z : PS d => causalHeat ν Y * (B (Z + Y) * f Z))
      (volume.prod volume) := by
    have hb : Integrable (fun p : PS d × PS d =>
        (Ma + Mb) * (Icc (-(Rb + Rf)) (Rb + Rf) ×ˢ (univ : Set (Euc d))).indicator
          (causalHeat ν) p.1 * ‖f p.2‖) (volume.prod volume) := by
      have := ((integrable_heat_far (d := d) hν (T := Rb + Rf)).const_mul (Ma + Mb)).mul_prod
        hf.integrable.norm
      exact this
    refine (hb.mono' ?_ (Eventually.of_forall fun p => ?_))
    · exact ((hHm.comp measurable_fst).mul ((hB.continuous.measurable.comp
        (measurable_snd.add measurable_fst)).mul
        (hf.continuous.measurable.comp measurable_snd))).aestronglyMeasurable
    · simp only [Function.uncurry, norm_mul, Real.norm_eq_abs]
      by_cases h0 : B (p.2 + p.1) = 0 ∨ f p.2 = 0
      · have hl : |causalHeat ν p.1| * (|B (p.2 + p.1)| * |f p.2|) = 0 := by
          rcases h0 with h0 | h0 <;> simp [h0]
        rw [hl]
        exact mul_nonneg (mul_nonneg (by linarith) (hind0 _)) (abs_nonneg _)
      push Not at h0
      have h1 := hRb _ h0.1
      have h2 := hRf _ h0.2
      simp only [Prod.fst_add] at h1
      have hY : p.1 ∈ Icc (-(Rb + Rf)) (Rb + Rf) ×ˢ (univ : Set (Euc d)) := by
        refine ⟨⟨?_, ?_⟩, mem_univ _⟩ <;>
        · cases abs_le.1 h1; cases abs_le.1 h2; linarith
      rw [indicator_of_mem hY, abs_of_nonneg (causalHeat_nonneg hν _)]
      have hb' := hMb (p.2 + p.1)
      calc causalHeat ν p.1 * (|B (p.2 + p.1)| * |f p.2|)
          ≤ causalHeat ν p.1 * ((Ma + Mb) * |f p.2|) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _))
              (causalHeat_nonneg hν _)
        _ = (Ma + Mb) * causalHeat ν p.1 * |f p.2| := by ring
  rw [L1]
  simp_rw [L2]
  calc ∫ Y, causalHeat ν Y * ∫ Z, B (Z + Y) * f Z
      = ∫ Y, ∫ Z, causalHeat ν Y * (B (Z + Y) * f Z) := by simp_rw [integral_const_mul]
    _ = ∫ Z, ∫ Y, causalHeat ν Y * (B (Z + Y) * f Z) := integral_integral_swap hint2
    _ = ∫ Z, f Z * backTest ν i j g Z := by
        congr 1; funext Z
        rw [backTest_eq hν hg i j Z, ← integral_const_mul]
        congr 1; funext Y; ring

end Transpose

section L2Transpose

variable {ν : ℝ}

/-- Time reversal on `L²`. -/
def reflL2 (d : ℕ) : Lp ℝ 2 (volume : Measure (PS d)) →L[ℝ] Lp ℝ 2 (volume : Measure (PS d)) :=
  (Lp.compMeasurePreservingₗᵢ ℝ trev measurePreserving_trev).toContinuousLinearMap

theorem coeFn_reflL2 (F : Lp ℝ 2 (volume : Measure (PS d))) :
    ⇑(reflL2 d F) =ᵐ[volume] ⇑F ∘ trev :=
  Lp.coeFn_compMeasurePreserving F measurePreserving_trev

theorem reflL2_toLp {g : PS d → ℝ} (hg : MemLp g 2 volume) :
    reflL2 d (hg.toLp g) = (hg.comp_measurePreserving measurePreserving_trev).toLp (g ∘ trev) := by
  refine Lp.ext ?_
  filter_upwards [coeFn_reflL2 (hg.toLp g),
    measurePreserving_trev.quasiMeasurePreserving.ae_eq_comp hg.coeFn_toLp,
    (hg.comp_measurePreserving measurePreserving_trev).coeFn_toLp] with X h1 h2 h3
  rw [h1, h3, Function.comp_apply, Function.comp_apply]
  exact h2

/-- **The transpose on `L²`**: `backOp = reflL2 ∘ secondDerivOp ∘ reflL2`. -/
def backOp (hν : 0 < ν) (i j : Fin d) :
    Lp ℝ 2 (volume : Measure (PS d)) →L[ℝ] Lp ℝ 2 (volume : Measure (PS d)) :=
  (reflL2 d).comp ((secondDerivOp hν i j).comp (reflL2 d))

theorem memLp_backTest (hν : 0 < ν) {g : PS d → ℝ} (hg : IsSTTest g) (i j : Fin d) :
    MemLp (backTest ν i j g) 2 volume :=
  (memLp_secondDerivTest hν hg.comp_trev i j).comp_measurePreserving measurePreserving_trev

theorem backOp_toLp (hν : 0 < ν) {g : PS d → ℝ} (hg : IsSTTest g) (i j : Fin d) :
    backOp hν i j ((hg.memLp 2).toLp g) = (memLp_backTest hν hg i j).toLp _ := by
  simp only [backOp, ContinuousLinearMap.comp_apply]
  rw [reflL2_toLp, show ((hg.memLp 2).comp_measurePreserving measurePreserving_trev) =
    (hg.comp_trev.memLp 2) from rfl, secondDerivOp_toLp hν i j hg.comp_trev, reflL2_toLp]
  rfl

theorem inner_eq_integral (F G : Lp ℝ 2 (volume : Measure (PS d))) :
    ⟪F, G⟫ = ∫ X, F X * G X := by
  rw [L2.inner_def]
  congr 1; funext X
  rw [Real.inner_apply, mul_comm]

theorem inner_secondDerivOp_tests (hν : 0 < ν) (i j : Fin d) (f g : testSpace d) :
    ⟪secondDerivOp hν i j (toL2 d f), toL2 d g⟫ = ⟪toL2 d f, backOp hν i j (toL2 d g)⟫ := by
  rw [inner_eq_integral, inner_eq_integral, secondDerivOp_toL2]
  have hb := backOp_toLp hν g.2 i j
  change _ = ∫ X, (toL2 d f) X * (backOp hν i j ((g.2.memLp 2).toLp (g : PS d → ℝ))) X
  rw [hb]
  have e1 : ∫ X, ((memLp_secondDerivTest hν f.2 i j).toLp _ : Lp ℝ 2 volume) X * (toL2 d g) X =
      ∫ X, (g : PS d → ℝ) X * secondDerivTest ν i j f X := by
    refine integral_congr_ae ?_
    filter_upwards [(memLp_secondDerivTest hν f.2 i j).coeFn_toLp, coeFn_toL2 g] with X h1 h2
    rw [h1, h2, mul_comm]
  have e2 : ∫ X, (toL2 d f) X * ((memLp_backTest hν g.2 i j).toLp _ : Lp ℝ 2 volume) X =
      ∫ X, (f : PS d → ℝ) X * backTest ν i j g X := by
    refine integral_congr_ae ?_
    filter_upwards [(memLp_backTest hν g.2 i j).coeFn_toLp, coeFn_toL2 f] with X h1 h2
    rw [h1, h2]
  rw [e1, e2]
  exact integral_mul_secondDerivTest_eq hν f.2 g.2 i j

/-- **Transposition on `L²`.** `⟪T F, G⟫ = ⟪F, backOp G⟫`. -/
theorem inner_secondDerivOp (hν : 0 < ν) (i j : Fin d) (F G : Lp ℝ 2 (volume : Measure (PS d))) :
    ⟪secondDerivOp hν i j F, G⟫ = ⟪F, backOp hν i j G⟫ := by
  have hd := denseRange_toL2 (d := d)
  -- first `F`, with `G` a test
  have step1 : ∀ g : testSpace d, ∀ F : Lp ℝ 2 (volume : Measure (PS d)),
      ⟪secondDerivOp hν i j F, toL2 d g⟫ = ⟪F, backOp hν i j (toL2 d g)⟫ := by
    intro g
    have := hd.equalizer (g := fun F => ⟪secondDerivOp hν i j F, toL2 d g⟫)
      (h := fun F => ⟪F, backOp hν i j (toL2 d g)⟫)
      ((secondDerivOp hν i j).continuous.inner continuous_const)
      (continuous_id.inner continuous_const)
      (funext fun f => inner_secondDerivOp_tests hν i j f g)
    exact fun F => congrFun this F
  have := hd.equalizer (g := fun G => ⟪secondDerivOp hν i j F, G⟫)
    (h := fun G => ⟪F, backOp hν i j G⟫) (continuous_const.inner continuous_id)
    (continuous_const.inner (backOp hν i j).continuous)
    (funext fun g => step1 g F)
  exact congrFun this G

/-- **Transposition on `L²`, integral form** (the hypothesis `hadj` of the CZ core). -/
theorem integral_secondDerivOp_mul (hν : 0 < ν) (i j : Fin d)
    (F G : Lp ℝ 2 (volume : Measure (PS d))) :
    ∫ X, secondDerivOp hν i j F X * G X = ∫ X, F X * backOp hν i j G X := by
  rw [← inner_eq_integral, ← inner_eq_integral]
  exact inner_secondDerivOp hν i j F G

end L2Transpose

end UnforcedLeray.Parabolic
