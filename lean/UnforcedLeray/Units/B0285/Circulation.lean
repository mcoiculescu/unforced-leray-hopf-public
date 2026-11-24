import UnforcedLeray.Units.B0285.Holder

/-!
# B0285, zero circulation of the source

Unit B0285 of `paper/main.tex` (tex lines 4675–4677): "The source has zero circulation: it is
the curl of a spatially localized integrable vector. There is no first-moment restriction."
Blueprint unit B0285; infrastructure INF13 (CY05 `integral_cell_curl_eq_zero` is the classical
form; here the field `b₀` is only weakly twice differentiable, so the weak form is proved).

* `IsWeakCurl c W ω`: `ω` is the curl of `W` against the periodic tests of `Sob.cylinder c`,
  `∫ φ ω = ∫ (∂_η φ) W₁ - ∫ (∂_q φ) W₂` (pairings on the centred cell `[-c/2,c/2) × ℝ`).
* `isWeakCurl_curlSource`: with weak jets `Db k = ∂_k b`, `D2b j k = ∂_j (Db k)` (periodic weak
  derivatives, as produced by B0289) and a smooth periodic coefficient `V`, the formula
  `curlSource V b Db D2b` is the weak curl of `B_V b = bvField V b Db` (the Leibniz rule with a
  smooth coefficient, tested against `V_k φ` and `∂_k V_i φ`).
* `integral_eq_zero_of_isWeakCurl`: the weak curl of a vector with integrable first component
  has zero cell integral, if it is itself integrable (cutoffs `χ(η/(n+1))` in `η` only; the
  periodic direction needs no cutoff).
* `integral_curlSource_eq_zero`: the source `curl(B_V b)` has zero circulation whenever
  `b, Db, D2b ∈ L^p`, `V` is smooth periodic with finite localized coefficient norm, and
  `m > 1` (the weight of `X_c` makes both `B_V b` and its curl integrable on the cell).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Real Topology
open scoped NNReal ENNReal ContDiff

namespace UnforcedLeray.B0285

open UnforcedLeray.GaussianVortex (Plane)

/-! ## 1. Preliminaries -/

theorem cylinder_μ_eq (c : ℝ) : (Sob.cylinder c).μ = Cyl.cellμ c := by
  rw [Sob.cylinder_μ]
  unfold Cyl.cellμ
  congr 1
  simp only [Sob.cylCell, Cyl.cell, neg_div]

@[simp] theorem cylDir_zero : Sob.cylDir 0 = ((1 : ℝ), (0 : ℝ)) := rfl

@[simp] theorem cylDir_one : Sob.cylDir 1 = ((0 : ℝ), (1 : ℝ)) := rfl

theorem add_shift (c : ℝ) (x : Plane) : x + (c, 0) = (x.1 + c, x.2) := Prod.ext rfl (add_zero _)

instance isLocallyFiniteMeasure_cellμ (c : ℝ) : IsLocallyFiniteMeasure (Cyl.cellμ c) := by
  unfold Cyl.cellμ; infer_instance

theorem locInt_cmpL {μ : Measure Plane} {f : Plane → Plane}
    (hf : LocallyIntegrable f μ) (i : Fin 2) : LocallyIntegrable (fun z => cmpL i (f z)) μ :=
  hf.mono ((cmpL i).continuous.comp_aestronglyMeasurable hf.aestronglyMeasurable)
    (Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs]; exact abs_cmpL_le i (f z))

theorem fderiv_cmpL {F : Plane → Plane} (hF : Differentiable ℝ F) (i : Fin 2) (z v : Plane) :
    fderiv ℝ (fun w => cmpL i (F w)) z v = cmpL i (fderiv ℝ F z v) := by
  have h : HasFDerivAt (fun w => cmpL i (F w)) ((cmpL i).comp (fderiv ℝ F z)) z :=
    (cmpL i).hasFDerivAt.comp z (hF z).hasFDerivAt
  rw [h.fderiv]
  rfl

theorem fderiv_periodic {F : Plane → Plane} {c : ℝ} (hF : ∀ x : Plane, F (x + (c, 0)) = F x)
    (x : Plane) : fderiv ℝ F (x + (c, 0)) = fderiv ℝ F x := by
  rw [← fderiv_comp_add_right (f := F) (x := x) ((c, 0) : Plane)]
  congr 1
  funext y
  exact hF y

/-- A continuous function with bounded `η`-support times a locally integrable function is
integrable on the cell. -/
theorem integrable_mul_of_bounded {c : ℝ} {ψ u : Plane → ℝ} (hψ : Continuous ψ)
    (hψR : ∃ R : ℝ, ∀ z : Plane, R < |z.2| → ψ z = 0)
    (hu : LocallyIntegrable u (Cyl.cellμ c)) :
    Integrable (fun z => ψ z * u z) (Cyl.cellμ c) := by
  obtain ⟨R, hR⟩ := hψR
  set K : Set Plane := Icc (-c / 2) (c / 2) ×ˢ Icc (-R) R
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hint : IntegrableOn (fun z => ψ z * u z) K (Cyl.cellμ c) :=
    IntegrableOn.continuousOn_mul hψ.continuousOn (hu.integrableOn_isCompact hK) hK
  refine hint.integrable_of_ae_notMem_eq_zero ?_
  have hmem : ∀ᵐ z ∂(Cyl.cellμ c), z ∈ Cyl.cell c := ae_restrict_mem (Cyl.measurableSet_cell c)
  filter_upwards [hmem] with z hz hzK
  rw [Cyl.mem_cell] at hz
  have h2 : R < |z.2| := by
    by_contra hle
    push Not at hle
    exact hzK ⟨⟨hz.1, hz.2.le⟩, abs_le.mp hle⟩
  rw [hR z h2, zero_mul]

/-! ## 2. The Leibniz rule with a smooth periodic coefficient -/

/-- `∫ F = -∫ G` with both integrands integrable on the cell. -/
def WeakPair (c : ℝ) (F G : Plane → ℝ) : Prop :=
  Integrable F (Cyl.cellμ c) ∧ Integrable G (Cyl.cellμ c) ∧
    ∫ z, F z ∂(Cyl.cellμ c) = -∫ z, G z ∂(Cyl.cellμ c)

theorem WeakPair.add {c : ℝ} {F₁ G₁ F₂ G₂ : Plane → ℝ} (h₁ : WeakPair c F₁ G₁)
    (h₂ : WeakPair c F₂ G₂) : WeakPair c (fun z => F₁ z + F₂ z) (fun z => G₁ z + G₂ z) :=
  ⟨h₁.1.add h₂.1, h₁.2.1.add h₂.2.1, by
    rw [integral_add h₁.1 h₂.1, integral_add h₁.2.1 h₂.2.1, h₁.2.2, h₂.2.2, neg_add]⟩

theorem WeakPair.congr {c : ℝ} {F G F' G' : Plane → ℝ} (h : WeakPair c F G)
    (hF : ∀ z, F z = F' z) (hG : ∀ z, G z = G' z) : WeakPair c F' G' := by
  have e1 : F = F' := funext hF
  have e2 : G = G' := funext hG
  subst e1 e2
  exact h

/-- **Weak Leibniz rule** on the cylinder: if `u' = ∂_j u` weakly and `a` is smooth and
periodic with `∂_j a = da`, then `∂_j (a u) = da u + a u'` weakly:
`∫ φ (da u + a u') = -∫ (∂_j φ) a u` for every cylinder test `φ`. -/
theorem leibniz_weak {c : ℝ} (j : Fin 2) {a da u u' : Plane → ℝ}
    (ha : ContDiff ℝ ∞ a) (haper : ∀ x : Plane, a (x + (c, 0)) = a x)
    (hda : ∀ z, fderiv ℝ a z (Sob.cylDir j) = da z)
    (hu : LocallyIntegrable u (Cyl.cellμ c)) (hu' : LocallyIntegrable u' (Cyl.cellμ c))
    (hw : Sob.HasWeakDeriv (Sob.cylinder c) [Sob.cylDir j] u u')
    {φ : Plane → ℝ} (hφ : Sob.IsCylTest c φ) :
    WeakPair c (fun z => φ z * (da z * u z + a z * u' z))
      (fun z => fderiv ℝ φ z (Sob.cylDir j) * (a z * u z)) := by
  set μ := Cyl.cellμ c with hμ
  obtain ⟨R, hR⟩ := hφ.bounded
  have hdφt : Sob.IsCylTest c (fun x => fderiv ℝ φ x (Sob.cylDir j)) := hφ.dirDeriv _
  obtain ⟨R', hR'⟩ := hdφt.bounded
  have hcda : Continuous da := by
    have : da = fun z => fderiv ℝ a z (Sob.cylDir j) := funext fun z => (hda z).symm
    rw [this]; exact (Sob.contDiff_dirDeriv ha _).continuous
  have hψ : Sob.IsCylTest c (fun z => a z * φ z) :=
    ⟨ha.mul hφ.smooth, fun x => by simp only [haper x, hφ.periodic x],
      ⟨R, fun x hx => by simp only [hR x hx, mul_zero]⟩⟩
  have hdiffa : Differentiable ℝ a := ha.differentiable (by simp)
  have hdiffφ : Differentiable ℝ φ := hφ.smooth.differentiable (by simp)
  have hder : ∀ z, fderiv ℝ (fun y => a y * φ y) z (Sob.cylDir j) =
      a z * fderiv ℝ φ z (Sob.cylDir j) + φ z * da z := by
    intro z
    rw [fderiv_fun_mul (hdiffa z) (hdiffφ z)]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, hda]
  have I1 : Integrable (fun z => (a z * fderiv ℝ φ z (Sob.cylDir j)) * u z) μ :=
    integrable_mul_of_bounded (ha.continuous.mul hdφt.smooth.continuous)
      ⟨R', fun z hz => by simp only [hR' z hz, mul_zero]⟩ hu
  have I2 : Integrable (fun z => (φ z * da z) * u z) μ :=
    integrable_mul_of_bounded (hφ.smooth.continuous.mul hcda)
      ⟨R, fun z hz => by simp only [hR z hz, zero_mul]⟩ hu
  have I3 : Integrable (fun z => (a z * φ z) * u' z) μ :=
    integrable_mul_of_bounded hψ.smooth.continuous
      ⟨R, fun z hz => by simp only [hR z hz, mul_zero]⟩ hu'
  have hid := hw.identity _ hψ
  rw [cylinder_μ_eq] at hid
  simp only [Sob.iterDirDeriv_singleton, smul_eq_mul, List.length_singleton, pow_one,
    neg_mul, one_mul] at hid
  have e3 : ∫ x, fderiv ℝ (fun y => a y * φ y) x (Sob.cylDir j) * u x ∂μ =
      ∫ x, (a x * fderiv ℝ φ x (Sob.cylDir j)) * u x ∂μ + ∫ x, (φ x * da x) * u x ∂μ := by
    rw [← integral_add I1 I2]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [hder x]
    ring
  have e1 : ∫ z, φ z * (da z * u z + a z * u' z) ∂μ =
      ∫ x, (φ x * da x) * u x ∂μ + ∫ x, (a x * φ x) * u' x ∂μ := by
    rw [← integral_add I2 I3]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    ring
  have e4 : ∫ z, fderiv ℝ φ z (Sob.cylDir j) * (a z * u z) ∂μ =
      ∫ x, (a x * fderiv ℝ φ x (Sob.cylDir j)) * u x ∂μ := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    ring
  refine ⟨(I2.add I3).congr (Eventually.of_forall fun z => ?_),
    I1.congr (Eventually.of_forall fun z => ?_), ?_⟩
  · simp only [Pi.add_apply]; ring
  · simp only; ring
  · rw [e1, e4]
    linarith [hid, e3]

/-! ## 3. The source is the weak curl of `B_V b` -/

/-- `ω` is the weak curl of `W` on the cylinder:
`∫ φ ω = ∫ (∂_η φ) W₁ - ∫ (∂_q φ) W₂` for every cylinder test `φ` (pairings on the cell). -/
def IsWeakCurl (c : ℝ) (W : Plane → Plane) (om : Plane → ℝ) : Prop :=
  ∀ φ : Plane → ℝ, Sob.IsCylTest c φ →
    ∫ z, φ z * om z ∂(Cyl.cellμ c) =
      ∫ z, fderiv ℝ φ z (Sob.cylDir 1) * (W z).1 ∂(Cyl.cellμ c) -
        ∫ z, fderiv ℝ φ z (Sob.cylDir 0) * (W z).2 ∂(Cyl.cellμ c)

theorem cmpL_smul (i : Fin 2) (x : ℝ) (w : Plane) : cmpL i (x • w) = x * cmpL i w := by
  rw [map_smul, smul_eq_mul]

/-- **`curl(B_V b)` is the weak curl of `B_V b`** (tex line 4676), for a smooth periodic
coefficient `V` and periodic weak jets `Db k = ∂_k b`, `D2b j k = ∂_j (Db k)` of a locally
integrable `b`. -/
theorem isWeakCurl_curlSource {c : ℝ} {V b : Plane → Plane} {Db : Fin 2 → Plane → Plane}
    {D2b : Fin 2 → Fin 2 → Plane → Plane}
    (hV : ContDiff ℝ ∞ V) (hVper : B0284.IsQPeriodic c V)
    (hb : LocallyIntegrable b (Cyl.cellμ c))
    (hDb : ∀ k, LocallyIntegrable (Db k) (Cyl.cellμ c))
    (hD2b : ∀ j k, LocallyIntegrable (D2b j k) (Cyl.cellμ c))
    (hw1 : ∀ k, Sob.HasWeakDeriv (Sob.cylinder c) [Sob.cylDir k] b (Db k))
    (hw2 : ∀ j k, Sob.HasWeakDeriv (Sob.cylinder c) [Sob.cylDir j] (Db k) (D2b j k)) :
    IsWeakCurl c (bvField V b Db) (curlSource V b Db D2b) := by
  have hV' : ∀ x : Plane, V (x + (c, 0)) = V x := fun x => by rw [add_shift]; exact hVper x
  have hdV : ∀ k, ContDiff ℝ ∞ (dV V k) := fun k =>
    (ContDiff.fderiv_right (m := ∞) hV (by simp)).clm_apply contDiff_const
  have hdVper : ∀ k (x : Plane), dV V k (x + (c, 0)) = dV V k x := fun k x => by
    simp only [dV, fderiv_periodic hV' x]
  intro φ hφ
  -- the weak identity for `∂_j (B_V b)_i`
  have key : ∀ j i : Fin 2, WeakPair c (fun z => φ z * cmpL i (bvDeriv V b Db D2b j z))
      (fun z => fderiv ℝ φ z (Sob.cylDir j) * cmpL i (bvField V b Db z)) := by
    intro j i
    have A : ∀ k : Fin 2, WeakPair c
        (fun z => φ z * (cmpL k (dV V j z) * cmpL i (Db k z) + cmpL k (V z) * cmpL i (D2b j k z)))
        (fun z => fderiv ℝ φ z (Sob.cylDir j) * (cmpL k (V z) * cmpL i (Db k z))) := fun k =>
      leibniz_weak j ((cmpL k).contDiff.comp hV)
        (fun x => by show cmpL k (V (x + (c, 0))) = cmpL k (V x); rw [hV' x])
        (fun z => fderiv_cmpL (hV.differentiable (by simp)) k z _)
        (locInt_cmpL (hDb k) i) (locInt_cmpL (hD2b j k) i) ((hw2 j k).map_clm (cmpL i)) hφ
    have B : ∀ k : Fin 2, WeakPair c
        (fun z => φ z * (cmpL i (d2V V j k z) * cmpL k (b z) + cmpL i (dV V k z) * cmpL k (Db j z)))
        (fun z => fderiv ℝ φ z (Sob.cylDir j) * (cmpL i (dV V k z) * cmpL k (b z))) := fun k =>
      leibniz_weak j ((cmpL i).contDiff.comp (hdV k))
        (fun x => by show cmpL i (dV V k (x + (c, 0))) = cmpL i (dV V k x); rw [hdVper k x])
        (fun z => fderiv_cmpL ((hdV k).differentiable (by simp)) i z _)
        (locInt_cmpL hb k) (locInt_cmpL (hDb j) k) ((hw1 j).map_clm (cmpL k)) hφ
    refine (((A 0).add (B 0)).add ((A 1).add (B 1))).congr (fun z => ?_) (fun z => ?_)
    · simp only [bvDeriv, Fin.sum_univ_two, map_add, cmpL_smul]
      ring
    · simp only [bvField, Fin.sum_univ_two, map_add, cmpL_smul]
      ring
  have h01 := key 0 1
  have h10 := key 1 0
  have hsrc : ∀ z, φ z * curlSource V b Db D2b z =
      φ z * cmpL 1 (bvDeriv V b Db D2b 0 z) - φ z * cmpL 0 (bvDeriv V b Db D2b 1 z) := by
    intro z; simp only [curlSource, cmpL_zero, cmpL_one]; ring
  simp only [hsrc]
  rw [integral_sub h01.1 h10.1, h01.2.2, h10.2.2]
  simp only [cmpL_zero, cmpL_one]
  ring

/-! ## 4. Zero circulation of a weak curl -/

/-- The cutoff profile: `1` on `[-1, 1]`, `0` outside `(-2, 2)`. -/
def chi0 : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩

/-- The cylinder test `φ_n(q, η) = χ(η/(n+1))`. -/
def cutT (n : ℕ) (z : Plane) : ℝ := chi0 (((n : ℝ) + 1)⁻¹ * z.2)

theorem cutT_test (c : ℝ) (n : ℕ) : Sob.IsCylTest c (cutT n) := by
  have hn : (0 : ℝ) < n + 1 := by positivity
  refine ⟨?_, fun x => ?_, ⟨2 * ((n : ℝ) + 1), fun x hx => ?_⟩⟩
  · exact chi0.contDiff.comp (contDiff_const.mul contDiff_snd)
  · simp only [cutT, Prod.snd_add, add_zero]
  · unfold cutT
    apply chi0.zero_of_le_dist
    rw [Real.dist_eq, sub_zero, abs_mul, abs_inv, abs_of_pos hn]
    show (2 : ℝ) ≤ ((n : ℝ) + 1)⁻¹ * |x.2|
    calc (2 : ℝ) = ((n : ℝ) + 1)⁻¹ * (2 * ((n : ℝ) + 1)) := by field_simp
      _ ≤ ((n : ℝ) + 1)⁻¹ * |x.2| := by gcongr

theorem hasFDerivAt_cutT (n : ℕ) (z : Plane) :
    HasFDerivAt (cutT n) (deriv chi0 (((n : ℝ) + 1)⁻¹ * z.2) •
      (((n : ℝ) + 1)⁻¹ • ContinuousLinearMap.snd ℝ ℝ ℝ)) z := by
  have h1 : HasFDerivAt (fun z : Plane => ((n : ℝ) + 1)⁻¹ * z.2)
      (((n : ℝ) + 1)⁻¹ • ContinuousLinearMap.snd ℝ ℝ ℝ) z :=
    (hasFDerivAt_snd).const_mul _
  have h2 : HasDerivAt chi0 (deriv chi0 (((n : ℝ) + 1)⁻¹ * z.2)) (((n : ℝ) + 1)⁻¹ * z.2) :=
    ((chi0.contDiff (n := 1)).differentiable one_ne_zero _).hasDerivAt
  exact h2.comp_hasFDerivAt z h1

theorem fderiv_cutT_zero (n : ℕ) (z : Plane) : fderiv ℝ (cutT n) z (Sob.cylDir 0) = 0 := by
  rw [(hasFDerivAt_cutT n z).fderiv]
  simp

theorem fderiv_cutT_one (n : ℕ) (z : Plane) :
    fderiv ℝ (cutT n) z (Sob.cylDir 1) =
      deriv chi0 (((n : ℝ) + 1)⁻¹ * z.2) * ((n : ℝ) + 1)⁻¹ := by
  rw [(hasFDerivAt_cutT n z).fderiv]
  simp

theorem abs_cutT_le (n : ℕ) (z : Plane) : |cutT n z| ≤ 1 := by
  unfold cutT
  rw [abs_of_nonneg chi0.nonneg]
  exact chi0.le_one

theorem eventually_cutT_eq_one (z : Plane) : ∀ᶠ n : ℕ in atTop, cutT n z = 1 := by
  refine (eventually_ge_atTop ⌈|z.2|⌉₊).mono fun n hn => ?_
  unfold cutT
  apply chi0.one_of_mem_closedBall
  have hn' : |z.2| ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hn)
  have hpos : (0 : ℝ) < n + 1 := by positivity
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_mul, abs_inv, abs_of_pos hpos]
  show ((n : ℝ) + 1)⁻¹ * |z.2| ≤ 1
  rw [inv_mul_le_iff₀ hpos]
  linarith

/-- **Zero circulation of a weak curl** (tex lines 4675–4677): if `ω` is the weak curl of a
vector `W` whose first component is integrable on the cell, and `ω` is integrable, then
`∫_cell ω = 0`. -/
theorem integral_eq_zero_of_isWeakCurl {c : ℝ} {W : Plane → Plane} {om : Plane → ℝ}
    (hW : Integrable (fun z => (W z).1) (Cyl.cellμ c)) (hom : Integrable om (Cyl.cellμ c))
    (hcurl : IsWeakCurl c W om) : ∫ z, om z ∂(Cyl.cellμ c) = 0 := by
  set μ := Cyl.cellμ c with hμ
  obtain ⟨M, hM⟩ := ((chi0.contDiff (n := 1)).continuous_deriv le_rfl).bounded_above_of_compact_support
    chi0.hasCompactSupport.deriv
  set I := ∫ z, ‖(W z).1‖ ∂μ
  have hid : ∀ n : ℕ, ∫ z, cutT n z * om z ∂μ =
      ∫ z, (deriv chi0 (((n : ℝ) + 1)⁻¹ * z.2) * ((n : ℝ) + 1)⁻¹) * (W z).1 ∂μ := by
    intro n
    rw [hcurl _ (cutT_test c n)]
    simp only [fderiv_cutT_zero, fderiv_cutT_one, zero_mul, integral_zero, sub_zero]
    rfl
  have hbound : ∀ n : ℕ, ‖∫ z, cutT n z * om z ∂μ‖ ≤ M * I * (1 / ((n : ℝ) + 1)) := by
    intro n
    have hpos : (0 : ℝ) < n + 1 := by positivity
    rw [hid n]
    refine (norm_integral_le_integral_norm _).trans ?_
    have e : ∫ z, M * ‖(W z).1‖ * (1 / ((n : ℝ) + 1)) ∂μ = M * I * (1 / ((n : ℝ) + 1)) := by
      rw [integral_mul_const, integral_const_mul]
    rw [← e]
    refine integral_mono_of_nonneg (Eventually.of_forall fun z => norm_nonneg _)
      ((hW.norm.const_mul M).mul_const _) (Eventually.of_forall fun z => ?_)
    simp only
    rw [norm_mul, norm_mul, Real.norm_of_nonneg (inv_nonneg.2 hpos.le)]
    calc ‖deriv chi0 (((n : ℝ) + 1)⁻¹ * z.2)‖ * ((n : ℝ) + 1)⁻¹ * ‖(W z).1‖
        ≤ M * ((n : ℝ) + 1)⁻¹ * ‖(W z).1‖ := by
          gcongr
          exact hM _
      _ = M * ‖(W z).1‖ * (1 / ((n : ℝ) + 1)) := by ring
  have hT1 : Tendsto (fun n : ℕ => ∫ z, cutT n z * om z ∂μ) atTop (𝓝 (∫ z, om z ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence (fun z => ‖om z‖)
      (fun n => ((cutT_test c n).smooth.continuous.aestronglyMeasurable).mul
        hom.aestronglyMeasurable) hom.norm (fun n => Eventually.of_forall fun z => ?_)
      (Eventually.of_forall fun z => ?_)
    · rw [norm_mul, Real.norm_eq_abs]
      calc |cutT n z| * ‖om z‖ ≤ 1 * ‖om z‖ := by gcongr; exact abs_cutT_le n z
        _ = ‖om z‖ := one_mul _
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_cutT_eq_one z] with n hn
      rw [hn, one_mul]
  have hT2 : Tendsto (fun n : ℕ => ∫ z, cutT n z * om z ∂μ) atTop (𝓝 0) := by
    have hlim : Tendsto (fun n : ℕ => M * I * (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
      have := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (M * I)
      simpa only [mul_zero] using this
    exact squeeze_zero_norm hbound hlim
  exact tendsto_nhds_unique hT1 hT2

/-! ## 5. Integrability through the weight of `X_c` -/

/-- For `m > 1`, a measurable `ω` with `‖ω‖_{X_c} < ∞` is integrable on the cell
(weighted Cauchy–Schwarz, `Cyl.eLpNorm_one_cell_le`). -/
theorem integrable_of_XcNorm {c m : ℝ} (hc : 0 < c) (hm : 1 < m) {om : Plane → ℝ}
    (hmeas : AEStronglyMeasurable om (Cyl.cellμ c)) (hfin : XcNorm c m om < ⊤) :
    Integrable om (Cyl.cellμ c) := by
  obtain ⟨C, _, hC⟩ := Cyl.eLpNorm_one_cell_le hm
  have hmc : AEStronglyMeasurable (fun z => (om z : ℂ)) (Cyl.cellμ c) :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable hmeas
  have h1 := hC c hc _ hmc
  have h2 := Cyl.eLpNorm_wμ_le_wμc hc (by linarith : (0 : ℝ) ≤ m) (fun z => (om z : ℂ))
  refine memLp_one_iff_integrable.1 ⟨hmeas, ?_⟩
  have e : eLpNorm om 1 (Cyl.cellμ c) = eLpNorm (fun z => (om z : ℂ)) 1 (Cyl.cellμ c) :=
    eLpNorm_congr_norm_ae (Eventually.of_forall fun z => (Complex.norm_real _).symm)
  rw [e]
  exact h1.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (h2.trans_lt hfin))

theorem aestronglyMeasurable_bvField {μ : Measure Plane} {V b : Plane → Plane}
    {Db : Fin 2 → Plane → Plane} (hV : ContDiff ℝ 2 V) (hb : AEStronglyMeasurable b μ)
    (hDb : ∀ k, AEStronglyMeasurable (Db k) μ) : AEStronglyMeasurable (bvField V b Db) μ := by
  unfold bvField
  refine Finset.aestronglyMeasurable_fun_sum _ fun k _ => ?_
  exact (((cmpL k).continuous.comp hV.continuous).aestronglyMeasurable.smul (hDb k)).add
    (((cmpL k).continuous.comp_aestronglyMeasurable hb).smul
      (continuous_dV hV k).aestronglyMeasurable)

theorem aestronglyMeasurable_bvDeriv {μ : Measure Plane} {V b : Plane → Plane}
    {Db : Fin 2 → Plane → Plane} {D2b : Fin 2 → Fin 2 → Plane → Plane} (hV : ContDiff ℝ 2 V)
    (hb : AEStronglyMeasurable b μ) (hDb : ∀ k, AEStronglyMeasurable (Db k) μ)
    (hD2b : ∀ j k, AEStronglyMeasurable (D2b j k) μ) (j : Fin 2) :
    AEStronglyMeasurable (bvDeriv V b Db D2b j) μ := by
  unfold bvDeriv
  refine Finset.aestronglyMeasurable_fun_sum _ fun k _ => ?_
  have hc : ∀ (i : Fin 2) {f : Plane → Plane}, AEStronglyMeasurable f μ →
      AEStronglyMeasurable (fun z => cmpL i (f z)) μ := fun i f hf =>
    (cmpL i).continuous.comp_aestronglyMeasurable hf
  have hV0 : AEStronglyMeasurable V μ := hV.continuous.aestronglyMeasurable
  have hV1 : ∀ k, AEStronglyMeasurable (dV V k) μ := fun k =>
    (continuous_dV hV k).aestronglyMeasurable
  have hV2 : ∀ j k, AEStronglyMeasurable (d2V V j k) μ := fun j k =>
    (continuous_d2V hV j k).aestronglyMeasurable
  exact ((((hc k (hV1 j)).smul (hDb k)).add ((hc k hV0).smul (hD2b j k))).add
    ((hc k (hDb j)).smul (hV1 k))).add ((hc k hb).smul (hV2 j k))

theorem aestronglyMeasurable_curlSource {μ : Measure Plane} {V b : Plane → Plane}
    {Db : Fin 2 → Plane → Plane} {D2b : Fin 2 → Fin 2 → Plane → Plane} (hV : ContDiff ℝ 2 V)
    (hb : AEStronglyMeasurable b μ) (hDb : ∀ k, AEStronglyMeasurable (Db k) μ)
    (hD2b : ∀ j k, AEStronglyMeasurable (D2b j k) μ) :
    AEStronglyMeasurable (curlSource V b Db D2b) μ :=
  (continuous_snd.comp_aestronglyMeasurable (aestronglyMeasurable_bvDeriv hV hb hDb hD2b 0)).sub
    (continuous_fst.comp_aestronglyMeasurable (aestronglyMeasurable_bvDeriv hV hb hDb hD2b 1))

/-- The localized vector `B_V b` lies in the weighted space:
`‖(B_V b)₁‖_{X_c} ≤ P (‖Db‖_p + ‖b‖_p)`. -/
theorem XcNorm_bvField_fst_le {c m : ℝ} (hc : 0 < c) {V b : Plane → Plane}
    {Db : Fin 2 → Plane → Plane} (hV : ContDiff ℝ 2 V)
    (hbper : B0284.IsQPeriodic c b) (hDbper : ∀ j, B0284.IsQPeriodic c (Db j))
    (hbm : AEStronglyMeasurable b (Cyl.cellμ c))
    (hDbm : ∀ j, AEStronglyMeasurable (Db j) (Cyl.cellμ c)) :
    XcNorm c m (fun z => (bvField V b Db z).1) ≤
      srcConst c (coeffNorm c m V) * (spNorm1 c Db + spNorm c b) := by
  set μ := Cyl.cellμ c
  set R := ENNReal.ofReal rB
  have hV0 : AEStronglyMeasurable (fun z => ‖V z‖) μ := hV.continuous.norm.aestronglyMeasurable
  have hV1 : AEStronglyMeasurable (jet1 (dV V)) μ :=
    aestronglyMeasurable_jet1 fun k => (continuous_dV hV k).aestronglyMeasurable
  have hb0 : AEStronglyMeasurable (fun z => ‖b z‖) μ := hbm.norm
  have hb1 : AEStronglyMeasurable (jet1 Db) μ := aestronglyMeasurable_jet1 hDbm
  have hw := (continuous_wt m).aestronglyMeasurable (μ := μ)
  set f1 : Plane → ℝ := fun z => wt m z * ‖V z‖ * jet1 Db z
  set f2 : Plane → ℝ := fun z => wt m z * jet1 (dV V) z * ‖b z‖
  have hf1 : AEStronglyMeasurable f1 μ := (hw.mul hV0).mul hb1
  have hf2 : AEStronglyMeasurable f2 μ := (hw.mul hV1).mul hb0
  have hdom : ∀ z, ‖wt m z * (bvField V b Db z).1‖ ≤ ‖(f1 + f2) z‖ := by
    intro z
    have h := norm_bvField_le V b Db z
    have h' : |(bvField V b Db z).1| ≤ ‖bvField V b Db z‖ := by
      rw [← Real.norm_eq_abs]; exact norm_fst_le _
    have hw0 := wt_nonneg m z
    have hnn : 0 ≤ f1 z + f2 z := by
      simp only [f1, f2]
      have := jet1_nonneg (dV V) z
      have := jet1_nonneg Db z
      positivity
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_nonneg hw0, Pi.add_apply,
      abs_of_nonneg hnn]
    calc wt m z * |(bvField V b Db z).1|
        ≤ wt m z * (‖V z‖ * jet1 Db z + jet1 (dV V) z * ‖b z‖) :=
          mul_le_mul_of_nonneg_left (h'.trans h) hw0
      _ = f1 z + f2 z := by simp only [f1, f2]; ring
  have hp1 : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have hstep : XcNorm c m (fun z => (bvField V b Db z).1) ≤ eLpNorm f1 2 μ + eLpNorm f2 2 μ := by
    rw [XcNorm_eq]
    exact (eLpNorm_mono hdom).trans (eLpNorm_add_le hf1 hf2 hp1)
  have h1 : eLpNorm f1 2 μ ≤ eLpNorm (fun z => wt m z * ‖V z‖) R μ *
      (ENNReal.ofReal (c ^ (1 / pB)) * spNorm1 c Db) :=
    (eLpNorm_wt_mul_le hV0 hb1).trans (mul_le_mul_right (eLpNorm_jet1_le hc hDbper hDbm) _)
  have h2 : eLpNorm f2 2 μ ≤ eLpNorm (fun z => wt m z * jet1 (dV V) z) R μ *
      (ENNReal.ofReal (c ^ (1 / pB)) * spNorm c b) :=
    (eLpNorm_wt_mul_le hV1 hb0).trans
      (mul_le_mul_right (le_of_eq (eLpNorm_norm_cellμ_le hc hbper)) _)
  set A0 := eLpNorm (fun z => wt m z * ‖V z‖) R μ
  set A1 := eLpNorm (fun z => wt m z * jet1 (dV V) z) R μ
  set A2 := eLpNorm (fun z => wt m z * jet2 (d2V V) z) R μ
  set C := ENNReal.ofReal (c ^ (1 / pB))
  have hK : coeffNorm c m V = A0 + A1 + A2 := rfl
  have hA0 : A0 ≤ 2 * (A0 + A1 + A2) :=
    (le_self_add.trans le_self_add).trans (le_two_mul_self _)
  have hA1 : A1 ≤ 2 * (A0 + A1 + A2) :=
    (le_self_add.trans' le_add_self).trans (le_two_mul_self _)
  calc XcNorm c m (fun z => (bvField V b Db z).1)
      ≤ A0 * (C * spNorm1 c Db) + A1 * (C * spNorm c b) := hstep.trans (add_le_add h1 h2)
    _ ≤ (2 * (A0 + A1 + A2)) * (C * spNorm1 c Db) + (2 * (A0 + A1 + A2)) * (C * spNorm c b) := by
        gcongr
    _ = srcConst c (coeffNorm c m V) * (spNorm1 c Db + spNorm c b) := by
        rw [hK, srcConst]; ring

/-! ## 6. Zero circulation of the source -/

theorem memLp_of_spNorm {c : ℝ} (hc : 0 < c) {f : Plane → Plane} (hper : B0284.IsQPeriodic c f)
    (hm : AEStronglyMeasurable f (Cyl.cellμ c)) (hfin : spNorm c f < ⊤) :
    MemLp f (ENNReal.ofReal pB) (Cyl.cellμ c) :=
  ⟨hm, by
    rw [eLpNorm_cellμ_eq hc hper pB_pos]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin⟩

theorem locallyIntegrable_of_spNorm {c : ℝ} (hc : 0 < c) {f : Plane → Plane}
    (hper : B0284.IsQPeriodic c f) (hm : AEStronglyMeasurable f (Cyl.cellμ c))
    (hfin : spNorm c f < ⊤) : LocallyIntegrable f (Cyl.cellμ c) :=
  (memLp_of_spNorm hc hper hm hfin).locallyIntegrable (ENNReal.one_le_ofReal.2 one_lt_pB.le)

/-- **Zero circulation of the source** (tex lines 4675–4677): for a smooth periodic coefficient
`V` with finite localized coefficient norm, and a periodic `b ∈ W^{2,p}` (periodic weak jets
`Db k = ∂_k b`, `D2b j k = ∂_j (Db k)`, all in `L^p`), and `m > 1`,
`∫_cell curl(B_V b) dq dη = 0`. -/
theorem integral_curlSource_eq_zero {c m : ℝ} (hc : 0 < c) (hm : 1 < m)
    {V b : Plane → Plane} {Db : Fin 2 → Plane → Plane} {D2b : Fin 2 → Fin 2 → Plane → Plane}
    (hV : ContDiff ℝ ∞ V) (hVper : B0284.IsQPeriodic c V) (hK : coeffNorm c m V < ⊤)
    (hbper : B0284.IsQPeriodic c b) (hDbper : ∀ j, B0284.IsQPeriodic c (Db j))
    (hD2bper : ∀ j k, B0284.IsQPeriodic c (D2b j k))
    (hbm : AEStronglyMeasurable b (Cyl.cellμ c))
    (hDbm : ∀ j, AEStronglyMeasurable (Db j) (Cyl.cellμ c))
    (hD2bm : ∀ j k, AEStronglyMeasurable (D2b j k) (Cyl.cellμ c))
    (hbfin : spNorm c b < ⊤) (hDbfin : ∀ j, spNorm c (Db j) < ⊤)
    (hD2bfin : ∀ j k, spNorm c (D2b j k) < ⊤)
    (hw1 : ∀ k, Sob.HasWeakDeriv (Sob.cylinder c) [Sob.cylDir k] b (Db k))
    (hw2 : ∀ j k, Sob.HasWeakDeriv (Sob.cylinder c) [Sob.cylDir j] (Db k) (D2b j k)) :
    ∫ z in Cyl.cell c, curlSource V b Db D2b z = 0 := by
  have hV2 : ContDiff ℝ 2 V := by simpa using contDiff_infty.1 hV 2
  have hP : srcConst c (coeffNorm c m V) < ⊤ := srcConst_lt_top c hK
  have hS1 : spNorm1 c Db < ⊤ := by
    unfold spNorm1; simp only [Fin.sum_univ_two]
    exact ENNReal.add_lt_top.2 ⟨hDbfin 0, hDbfin 1⟩
  have hS2 : spNorm2 c D2b < ⊤ := by
    unfold spNorm2; simp only [Fin.sum_univ_two]
    exact ENNReal.add_lt_top.2 ⟨ENNReal.add_lt_top.2 ⟨hD2bfin 0 0, hD2bfin 0 1⟩,
      ENNReal.add_lt_top.2 ⟨hD2bfin 1 0, hD2bfin 1 1⟩⟩
  have hW : Integrable (fun z => (bvField V b Db z).1) (Cyl.cellμ c) := by
    refine integrable_of_XcNorm hc hm
      (continuous_fst.comp_aestronglyMeasurable (aestronglyMeasurable_bvField hV2 hbm hDbm)) ?_
    exact (XcNorm_bvField_fst_le hc hV2 hbper hDbper hbm hDbm).trans_lt
      (ENNReal.mul_lt_top hP (ENNReal.add_lt_top.2 ⟨hS1, hbfin⟩))
  have hom : Integrable (curlSource V b Db D2b) (Cyl.cellμ c) := by
    refine integrable_of_XcNorm hc hm (aestronglyMeasurable_curlSource hV2 hbm hDbm hD2bm) ?_
    exact (XcNorm_curlSource_le hc hV2 hbper hDbper hD2bper hbm hDbm hD2bm).trans_lt
      (ENNReal.mul_lt_top hP (ENNReal.add_lt_top.2 ⟨ENNReal.add_lt_top.2 ⟨hS2, hS1⟩, hbfin⟩))
  exact integral_eq_zero_of_isWeakCurl hW hom
    (isWeakCurl_curlSource hV hVper (locallyIntegrable_of_spNorm hc hbper hbm hbfin)
      (fun k => locallyIntegrable_of_spNorm hc (hDbper k) (hDbm k) (hDbfin k))
      (fun j k => locallyIntegrable_of_spNorm hc (hD2bper j k) (hD2bm j k) (hD2bfin j k))
      hw1 hw2)

end UnforcedLeray.B0285
